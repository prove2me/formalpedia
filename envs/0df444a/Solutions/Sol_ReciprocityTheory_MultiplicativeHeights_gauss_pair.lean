-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:08.905071+00:00
-- url     : https://prove2.me/submissions/74ea2ad9-6d7e-4ee3-8740-fdfce84d2511

import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_gaussLogC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_gaussOneC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (hn : 0 < n) (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    ∃ s : ℝ, 0 < s ∧
      Integrable (fun x : EuclideanSpace ℂ (Fin n) ↦
        log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2)) ∧
      ∫ x : EuclideanSpace ℂ (Fin n), log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ *
        exp (-‖x‖ ^ 2) = s * (gaussLogC ‖c‖ * gaussOneC ^ (n - 1)) ∧
      ∫ x : EuclideanSpace ℂ (Fin n), exp (-‖x‖ ^ 2) = s * gaussOneC ^ n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set v : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 (fun i => star (WithLp.ofLp c i)) with hvdef
  have hvx : ∀ x : EuclideanSpace ℂ (Fin (m + 1)),
      inner ℂ v x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hvdef, RCLike.inner_apply] <;> ring
  have hvn : ‖v‖ = ‖c‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [hvdef]
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set u0 : EuclideanSpace ℂ (Fin (m + 1)) := ((‖c‖⁻¹ : ℝ) : ℂ) • v with hu0
  have hu0n : ‖u0‖ = 1 := by
    rw [hu0, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0, hvn,
      inv_mul_cancel₀ hc0.ne']
  have hon : Orthonormal ℂ (Set.restrict ({0} : Set (Fin (m + 1))) (fun _ => u0)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j :=
      Subtype.ext (by rw [Set.mem_singleton_iff.mp i.2, Set.mem_singleton_iff.mp j.2])
    subst hij
    simp only [Set.restrict_apply, if_true]
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖u0‖ : ℝ) : ℂ) ^ 2 = 1
    rw [hu0n]; simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (by rw [finrank_euclideanSpace]) hon
  have hb0 : b 0 = u0 := hb 0 (Set.mem_singleton 0)
  let M : EuclideanSpace ℂ (Fin (m + 1)) ≃L[ℂ] (Fin (m + 1) → ℂ) :=
    b.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin (m + 1)) ℂ)
  have hMr : ∀ x i, M x i = b.repr x i := fun x i => rfl
  have hnorm1 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ = ‖c‖ * ‖M x 0‖ := by
    intro x
    rw [hMr, OrthonormalBasis.repr_apply_apply, hb0, hu0, inner_smul_left, hvx, norm_mul,
      Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
      ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  have hnorm2 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), ‖x‖ ^ 2 = ∑ i, ‖M x i‖ ^ 2 := by
    intro x
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
    rfl
  let f : Fin (m + 1) → ℂ → ℝ := fun i z =>
    if i = 0 then log (‖c‖ * ‖z‖) * exp (-‖z‖ ^ 2) else exp (-‖z‖ ^ 2)
  let g : Fin (m + 1) → ℂ → ℝ := fun _ z => exp (-‖z‖ ^ 2)
  have hexp : ∀ y : Fin (m + 1) → ℂ, exp (-∑ i, ‖y i‖ ^ 2) = ∏ i, exp (-‖y i‖ ^ 2) := by
    intro y; rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have hf : ∀ y : Fin (m + 1) → ℂ,
      ∏ i, f i (y i) = log (‖c‖ * ‖y 0‖) * ∏ i, exp (-‖y i‖ ^ 2) := by
    intro y
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun i => exp (-‖y i‖ ^ 2))]
    simp only [f, if_pos rfl, Fin.succ_ne_zero, if_false]
    ring
  have hF1 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)),
      log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2) = ∏ i, f i (M x i) := by
    intro x
    rw [hf (M x), hnorm1, hnorm2, hexp]
  have hF2 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), exp (-‖x‖ ^ 2) = ∏ i, g i (M x i) := by
    intro x
    rw [hnorm2, hexp]
  set μ := (volume : Measure (EuclideanSpace ℂ (Fin (m + 1)))) with hμ
  let Me := M.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map Me).IsAddHaarMeasure := by
    have h := M.isAddHaarMeasure_map μ
    exact h
  set k := (μ.map Me).addHaarScalarFactor (volume : Measure (Fin (m + 1) → ℂ))
  have hν : μ.map Me = k • (volume : Measure (Fin (m + 1) → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hk : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hint : ∀ H : (Fin (m + 1) → ℂ) → ℝ, ∫ x, H (M x) ∂μ = (k : ℝ) * ∫ y, H y := by
    intro H
    calc ∫ x, H (M x) ∂μ = ∫ x, H (Me x) ∂μ := rfl
      _ = ∫ y, H y ∂(μ.map Me) := (Me.measurableEmbedding.integral_map H).symm
      _ = (k : ℝ) * ∫ y, H y := by
        rw [hν, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hintg : ∀ H : (Fin (m + 1) → ℂ) → ℝ, Integrable H → Integrable (fun x => H (M x)) μ := by
    intro H hH
    have h1 : Integrable H (μ.map Me) := by rw [hν]; exact hH.smul_measure_nnreal
    exact Me.measurableEmbedding.integrable_map_iff.mp h1
  have hP1 : ∫ y : Fin (m + 1) → ℂ, ∏ i, f i (y i) = gaussLogC ‖c‖ * gaussOneC ^ m := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := f), Fin.prod_univ_succ]
    simp only [f, if_pos rfl, Fin.succ_ne_zero, if_false, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, gaussLogC, gaussOneC]
  have hP2 : ∫ y : Fin (m + 1) → ℂ, ∏ i, g i (y i) = gaussOneC ^ (m + 1) := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := g)]
    simp only [g, Finset.prod_const, Finset.card_univ, Fintype.card_fin, gaussOneC]
  have hI1 : Integrable (fun y : Fin (m + 1) → ℂ => ∏ i, f i (y i)) := by
    rw [volume_pi]
    refine Integrable.fintype_prod (f := f) fun i => ?_
    by_cases hi : i = 0
    · subst hi; simpa [f] using integrable_gaussLogC hc0
    · simpa [f, hi] using integrable_gaussOneC
  refine ⟨(k : ℝ), NNReal.coe_pos.mpr hk, ?_, ?_, ?_⟩
  · exact (hintg _ hI1).congr (Filter.Eventually.of_forall fun x => (hF1 x).symm)
  · rw [show (fun x : EuclideanSpace ℂ (Fin (m + 1)) =>
        log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2)) =
        fun x => ∏ i, f i (M x i) from funext hF1]
    rw [hint (fun y => ∏ i, f i (y i)), hP1]
  · rw [show (fun x : EuclideanSpace ℂ (Fin (m + 1)) => exp (-‖x‖ ^ 2)) =
        fun x => ∏ i, g i (M x i) from funext hF2]
    rw [hint (fun y => ∏ i, g i (y i)), hP2]
end ReciprocityTheory.MultiplicativeHeights
