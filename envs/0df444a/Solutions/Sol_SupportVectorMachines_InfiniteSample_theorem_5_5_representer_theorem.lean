-- Prove2me | solution 1 for SupportVectorMachines.InfiniteSample.theorem_5_5_representer_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:58:47.54392+00:00
-- url     : https://prove2.me/submissions/e916368a-db17-4600-aa09-0d7410550577

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory


namespace SupportVectorMachines.InfiniteSample

theorem rep_core {X : Type*} {n : ℕ} (hn : 0 < n)
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (D : Fin n → X × ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃! f : H,
      (∀ g : H, lam * ‖f‖ ^ 2 + empiricalRisk n L D (toFun f) ≤
        lam * ‖g‖ ^ 2 + empiricalRisk n L D (toFun g)) ∧
      ∃ α : Fin n → ℝ, ∀ x : X, toFun f x = ∑ i, α i * k x (D i).1 := by
  obtain ⟨_hinj, kAt, hk, hrep⟩ := hRKHS
  set J : H → ℝ := fun f => lam * ‖f‖ ^ 2 + empiricalRisk n L D (toFun f) with hJ
  have hRnn : ∀ f : H, 0 ≤ empiricalRisk n L D (toFun f) := by
    intro f
    unfold empiricalRisk
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => hLnn _ _ _)
  have hRcont : Continuous (fun f : H => empiricalRisk n L D (toFun f)) := by
    unfold empiricalRisk
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro i _
    have h1 : (fun f : H => L (D i).1 (D i).2 (toFun f (D i).1)) =
        fun f : H => L (D i).1 (D i).2 (inner (𝕜 := ℝ) f (kAt (D i).1)) := by
      funext f; rw [hrep]
    rw [h1]
    exact ((hL _ _).locallyLipschitz.continuous).comp (continuous_id.inner continuous_const)
  have hJcont : Continuous J := by
    simp only [hJ]
    exact (continuous_const.mul (continuous_norm.pow 2)).add hRcont
  set V : Submodule ℝ H := Submodule.span ℝ (Set.range fun i => kAt (D i).1) with hV
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  -- projection does not increase J
  have hproj : ∀ g : H, J (V.starProjection g) ≤ J g := by
    intro g
    have hR : empiricalRisk n L D (toFun (V.starProjection g)) = empiricalRisk n L D (toFun g) := by
      unfold empiricalRisk
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hrep, hrep g]
      have h0 := V.starProjection_inner_eq_zero g (kAt (D i).1)
        (Submodule.subset_span ⟨i, rfl⟩)
      rw [inner_sub_left] at h0
      rw [show inner ℝ (V.starProjection g) (kAt (D i).1) = inner ℝ g (kAt (D i).1) by linarith]
    simp only [hJ, hR]
    have := V.norm_starProjection_apply_le g
    have h2 : ‖V.starProjection g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith
  -- existence of minimizer
  set r : ℝ := J 0 / lam + 1 with hr
  have hJ0 : 0 ≤ J 0 := by simp only [hJ]; have := hRnn 0; positivity
  have hr1 : 1 ≤ r := by have : 0 ≤ J 0 / lam := div_nonneg hJ0 hlam.le; linarith
  obtain ⟨v0, hv0K, hv0min⟩ := (isCompact_closedBall (0 : V) r).exists_isMinOn
    (Metric.nonempty_closedBall.mpr (by linarith))
    ((hJcont.comp continuous_subtype_val).continuousOn)
  have hmin : ∀ g : H, J (v0 : H) ≤ J g := by
    intro g
    have hpm : V.starProjection g ∈ V := V.starProjection_apply_mem g
    let p : V := ⟨V.starProjection g, hpm⟩
    refine le_trans ?_ (hproj g)
    by_cases hp : ‖V.starProjection g‖ ≤ r
    · have : p ∈ Metric.closedBall (0 : V) r := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact hp
      exact hv0min this
    · push_neg at hp
      have h0 : (0 : V) ∈ Metric.closedBall (0 : V) r := by
        simp only [Metric.mem_closedBall, dist_self]; linarith
      have h1 : J ((0 : V) : H) ≥ J (v0 : H) := hv0min h0
      simp only [ZeroMemClass.coe_zero] at h1
      have h2 : r ^ 2 < ‖V.starProjection g‖ ^ 2 := by
        have := sq_lt_sq' (by linarith) hp
        exact this
      have h3 : J 0 / lam * lam = J 0 := div_mul_cancel₀ _ hlam.ne'
      have h4 : J 0 < lam * ‖V.starProjection g‖ ^ 2 := by nlinarith
      have h5 := hRnn (V.starProjection g)
      simp only [hJ] at h1 h4 ⊢
      linarith
  refine ⟨(v0 : H), ⟨hmin, ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp v0.2
    refine ⟨c, fun x => ?_⟩
    rw [← hc, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hk x, hrep, hrep, real_inner_comm]
  · rintro f ⟨hf, -⟩
    by_contra hne
    set f1 : H := (v0 : H)
    have e1 : J f ≤ J f1 := hf f1
    have e2 : J f1 ≤ J f := hmin f
    set m : H := (1/2 : ℝ) • (f + f1)
    have hm1 : J f ≤ J m := hf m
    have hRm : empiricalRisk n L D (toFun m) ≤
        (empiricalRisk n L D (toFun f) + empiricalRisk n L D (toFun f1)) / 2 := by
      unfold empiricalRisk
      have : ∑ i, L (D i).1 (D i).2 (toFun m (D i).1) ≤
          ∑ i, ((1/2 : ℝ) * L (D i).1 (D i).2 (toFun f (D i).1) +
            (1/2 : ℝ) * L (D i).1 (D i).2 (toFun f1 (D i).1)) := by
        apply Finset.sum_le_sum
        intro i _
        have hc := (hL (D i).1 (D i).2).2 (Set.mem_univ (toFun f (D i).1))
          (Set.mem_univ (toFun f1 (D i).1)) (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        simp only [smul_eq_mul] at hc
        have : toFun m (D i).1 = 1/2 * toFun f (D i).1 + 1/2 * toFun f1 (D i).1 := by
          simp only [m, map_smul, map_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
        rw [this]; exact hc
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
      have hn' : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hn']
    have hsub : f - f1 ≠ 0 := sub_ne_zero.mpr hne
    have hpos : 0 < ‖f - f1‖ ^ 2 := by positivity
    have hnm : ‖m‖ ^ 2 = (‖f‖ ^ 2 + ‖f1‖ ^ 2) / 2 - ‖f - f1‖ ^ 2 / 4 := by
      simp only [m, norm_smul]
      have a1 := norm_add_sq_real f f1
      have a2 := norm_sub_sq_real f f1
      rw [mul_pow]
      norm_num
      nlinarith
    simp only [hJ] at e1 e2 hm1
    nlinarith

end SupportVectorMachines.InfiniteSample

open SupportVectorMachines.InfiniteSample


theorem solution {X : Type*} {n : ℕ} (hn : 0 < n)
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (D : Fin n → X × ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃! f : H,
      (∀ g : H, lam * ‖f‖ ^ 2 + empiricalRisk n L D (toFun f) ≤
        lam * ‖g‖ ^ 2 + empiricalRisk n L D (toFun g)) ∧
      ∃ α : Fin n → ℝ, ∀ x : X, toFun f x = ∑ i, α i * k x (D i).1 := by
  exact rep_core hn L hL hLnn D H toFun k hRKHS lam hlam
