-- Prove2me | solution 1 for OnDemandCoord.platform_identity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:53:08.05799+00:00
-- url     : https://prove2.me/submissions/8382fe31-d19a-4bf8-ac2b-9bea4b2756ac

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

set_option autoImplicit false

open MeasureTheory ProbabilityTheory OnDemandCoord

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Q : Fin n → ℝ) (_hQ : 0 ≤ Q) (η : ℝ) (K : Contract n) (hβ : ∀ i, 0 < K.β i)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (hκ : IsPolicy κ) :
    M.platformProfit K η κ Q ≤
        -M.C Q η + M.p * ∑ i, (1 - K.m i) * M.mean Q i + M.c * ∑ i, Q i + ∑ i, K.r i ∧
      (IsNoWaste κ → M.platformProfit K η κ Q =
        -M.C Q η + M.p * ∑ i, (1 - K.m i) * M.mean Q i + M.c * ∑ i, Q i + ∑ i, K.r i) := by
  have : IsProbabilityMeasure P := M.isProb
  have : IsMarkovKernel κ := hκ.1
  have hp_pos : 0 < M.p := lt_trans M.c_pos M.c_lt_p
  have hG_nn : 0 ≤ M.G η := by
    rcases le_total η M.τl with hle | hge
    · rw [M.G_of_le η hle]
    · rw [← M.G_of_le M.τl le_rfl]
      exact M.monotone_G hge
  have hS_nn : 0 ≤ M.S η := mul_nonneg M.N_pos.le hG_nn
  have hvac_nn : ∀ ω : Ω, 0 ≤ M.vacVec Q ω := fun _ _ => le_max_right _ _
  have hvac_meas : ∀ i : Fin n, Measurable (M.vac Q i) :=
    fun i => ((M.measurable_X i).sub_const (Q i)).max measurable_const
  have hvac_int : ∀ i : Fin n, Integrable (M.vac Q i) P := by
    intro i
    refine Integrable.mono' ((M.integrable_X i).sub (integrable_const (Q i))).norm
      (hvac_meas i).aestronglyMeasurable (ae_of_all P fun ω => ?_)
    simp only [Model.vac, Real.norm_eq_abs]
    rcases le_total (M.X i ω - Q i) 0 with hle | hge
    · rw [max_eq_right hle, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left hge]; exact le_rfl
  have hV_meas : Measurable (fun ω : Ω => ∑ i, M.vac Q i ω) :=
    Finset.measurable_sum Finset.univ fun i _ => hvac_meas i
  have hV_int : Integrable (fun ω : Ω => ∑ i, M.vac Q i ω) P :=
    integrable_finsetSum Finset.univ fun i _ => hvac_int i
  have hmax_int : Integrable (fun ω : Ω => max (∑ i, M.vac Q i ω - M.S η) 0) P := by
    refine Integrable.mono' (hV_int.sub (integrable_const (M.S η))).norm
      ((hV_meas.sub_const (M.S η)).max measurable_const).aestronglyMeasurable
      (ae_of_all P fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rcases le_total (∑ i, M.vac Q i ω - M.S η) 0 with hle | hge
    · rw [max_eq_right hle, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left hge]; exact le_rfl
  have hmin_int : Integrable (fun ω : Ω => min (M.S η) (∑ i, M.vac Q i ω)) P :=
    (integrable_const (M.S η)).inf hV_int
  have hai_int : ∀ (ω : Ω) (i : Fin n),
      Integrable (fun a : Fin n → ℝ => a i) (κ (M.vacVec Q ω, M.S η)) := by
    intro ω i
    refine Integrable.mono' (integrable_const (M.vac Q i ω))
      (measurable_pi_apply i).aestronglyMeasurable ?_
    filter_upwards [hκ.2 (M.vacVec Q ω) (M.S η) (hvac_nn ω) hS_nn] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (ha.1 i).1]
    exact (ha.1 i).2
  have hexpA_int : ∀ i : Fin n,
      Integrable (fun ω : Ω => ∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) P := by
    intro i
    have hpi : Measurable (fun a : Fin n → ℝ => a i) := measurable_pi_apply i
    have hsm : StronglyMeasurable (fun ω : Ω => ∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) :=
      (hpi.stronglyMeasurable.integral_kernel (κ := κ)).comp_measurable
        ((M.measurable_vacVec Q).prodMk (measurable_const (a := M.S η)))
    refine Integrable.mono' (hvac_int i) hsm.aestronglyMeasurable (ae_of_all P fun ω => ?_)
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbound : ∫ a, ‖a i‖ ∂κ (M.vacVec Q ω, M.S η) ≤
        ∫ _, M.vac Q i ω ∂κ (M.vacVec Q ω, M.S η) := by
      refine integral_mono_ae (hai_int ω i).norm (integrable_const _) ?_
      filter_upwards [hκ.2 (M.vacVec Q ω) (M.S η) (hvac_nn ω) hS_nn] with a ha
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.1 i).1]
      exact (ha.1 i).2
    simpa [integral_const, probReal_univ] using hbound
  have hpay_eq : ∀ (i : Fin n) (a x : Fin n → ℝ),
      M.payment K i a x = (K.r i - M.p * K.m i * x i) + M.p * a i := by
    intro i a x
    unfold Model.payment Model.fixedRate Model.contingentPayment
    have hβi : K.β i ≠ 0 := (hβ i).ne'
    field_simp
    ring
  have hinner_i : ∀ (ω : Ω) (i : Fin n),
      (∫ a, M.payment K i a (M.vacVec Q ω) ∂κ (M.vacVec Q ω, M.S η)) =
        (K.r i - M.p * K.m i * M.vac Q i ω) +
          M.p * ∫ a, a i ∂κ (M.vacVec Q ω, M.S η) := by
    intro ω i
    simp_rw [hpay_eq i _ (M.vacVec Q ω)]
    rw [integral_add (integrable_const _) ((hai_int ω i).const_mul M.p),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    rfl
  have hprof_eq : M.platformProfit K η κ Q =
      (∑ i, K.r i) - M.p * (∑ i, K.m i * M.mean Q i) +
        M.p * (∫ ω, (∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η)) ∂P) - η * M.S η := by
    unfold Model.platformProfit
    have houter_i : ∀ i : Fin n,
        (∫ ω, ∫ a, M.payment K i a (M.vacVec Q ω) ∂κ (M.vacVec Q ω, M.S η) ∂P) =
          K.r i - M.p * K.m i * M.mean Q i +
            M.p * ∫ ω, (∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) ∂P := by
      intro i
      simp_rw [hinner_i _ i]
      have hint1 : Integrable (fun ω : Ω => K.r i - M.p * K.m i * M.vac Q i ω) P :=
        (integrable_const _).sub ((hvac_int i).const_mul _)
      rw [integral_add hint1 ((hexpA_int i).const_mul M.p),
        integral_sub (integrable_const _) ((hvac_int i).const_mul _),
        integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]
      rfl
    simp_rw [houter_i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← integral_finset_sum Finset.univ fun i _ => hexpA_int i]
    have hsum_in : ∀ ω : Ω,
        (∑ i, ∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) =
          ∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η) :=
      fun ω => (integral_finset_sum Finset.univ fun i _ => hai_int ω i).symm
    simp_rw [hsum_in]
    have hmul_sum : (∑ i : Fin n, M.p * K.m i * M.mean Q i) =
        M.p * ∑ i : Fin n, K.m i * M.mean Q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hmul_sum]
  have hRHS_eq :
      -M.C Q η + M.p * ∑ i, (1 - K.m i) * M.mean Q i + M.c * ∑ i, Q i + ∑ i, K.r i =
        (∑ i, K.r i) - M.p * (∑ i, K.m i * M.mean Q i) +
          M.p * (∫ ω, min (M.S η) (∑ i, M.vac Q i ω) ∂P) - η * M.S η := by
    have hmin_pt : ∀ ω : Ω,
        min (M.S η) (∑ i, M.vac Q i ω) =
          (∑ i, M.vac Q i ω) - max (∑ i, M.vac Q i ω - M.S η) 0 := by
      intro ω
      rcases le_total (M.S η) (∑ i, M.vac Q i ω) with hle | hge
      · rw [min_eq_left hle, max_eq_left (by linarith)]; ring
      · rw [min_eq_right hge, max_eq_right (by linarith)]; ring
    have hmin_int_eq : (∫ ω, min (M.S η) (∑ i, M.vac Q i ω) ∂P) =
        (∑ i, M.mean Q i) - ∫ ω, max (∑ i, M.vac Q i ω - M.S η) 0 ∂P := by
      simp_rw [hmin_pt]
      rw [integral_sub hV_int hmax_int, integral_finset_sum Finset.univ fun i _ => hvac_int i]
      rfl
    unfold Model.C
    rw [hmin_int_eq]
    have hsplit_m : ∑ i, (1 - K.m i) * M.mean Q i =
        (∑ i, M.mean Q i) - ∑ i, K.m i * M.mean Q i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit_m]
    ring
  have hsumA_int : Integrable (fun ω : Ω => ∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η)) P := by
    have heq : (fun ω : Ω => ∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η)) =
        fun ω : Ω => ∑ i, ∫ a, a i ∂κ (M.vacVec Q ω, M.S η) := by
      ext ω
      exact integral_finset_sum Finset.univ fun i _ => hai_int ω i
    rw [heq]
    exact integrable_finset_sum Finset.univ fun i _ => hexpA_int i
  rw [hprof_eq, hRHS_eq]
  constructor
  · have hint_le : (∫ ω, (∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η)) ∂P) ≤
        ∫ ω, min (M.S η) (∑ i, M.vac Q i ω) ∂P := by
      refine integral_mono_ae hsumA_int hmin_int (ae_of_all P fun ω => ?_)
      have h1 : (∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η)) ≤
          ∫ _, min (M.S η) (∑ i, M.vac Q i ω) ∂κ (M.vacVec Q ω, M.S η) := by
        refine integral_mono_ae (integrable_finset_sum Finset.univ fun i _ => hai_int ω i)
          (integrable_const _) ?_
        filter_upwards [hκ.2 (M.vacVec Q ω) (M.S η) (hvac_nn ω) hS_nn] with a ha
        exact le_min ha.2 (Finset.sum_le_sum fun i _ => (ha.1 i).2)
      simpa [integral_const, probReal_univ] using h1
    have := mul_le_mul_of_nonneg_left hint_le hp_pos.le
    linarith
  · intro hnw
    have hint_eq : (∫ ω, (∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η)) ∂P) =
        ∫ ω, min (M.S η) (∑ i, M.vac Q i ω) ∂P := by
      refine integral_congr_ae (ae_of_all P fun ω => ?_)
      have h1 : (∫ a, (∑ i, a i) ∂κ (M.vacVec Q ω, M.S η)) =
          ∫ _, min (M.S η) (∑ i, M.vac Q i ω) ∂κ (M.vacVec Q ω, M.S η) := by
        simpa [Model.vacVec] using integral_congr_ae (hnw (M.vacVec Q ω) (M.S η) (hvac_nn ω) hS_nn)
      simpa [integral_const, probReal_univ] using h1
    rw [hint_eq]
