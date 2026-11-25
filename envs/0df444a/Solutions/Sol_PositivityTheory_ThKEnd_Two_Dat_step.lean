-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Dat.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:53.715673+00:00
-- url     : https://prove2.me/submissions/5b15d22e-228e-4f21-b19a-3e7f299c9acf

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Dat_gr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]
namespace PositivityTheory.ThKEnd.Two
namespace Dat
theorem _root_.solution (hC : Cusp Γ n a) (hn : Continuous n) (h : Dat Γ n a lam l φ c) (hl : ‖l‖ < 1) {m : ℕ} (hm : Gr a (m + 1) φ)
    (hV : V ∈ 𝓝 (1 : G)) : ∃ η, Bump V η ∧ Gr a m (Two.conv μ η φ) := by
  obtain ⟨η, hη, h2⟩ := hC.lip V hV
  refine ⟨η, hη, fun Ω hΩ => ?_⟩
  have h' := h.conv μ hC hn hη
  obtain ⟨D, Ω', h3, h4⟩ := h2 Ω hΩ
  obtain ⟨C₀, hC₀⟩ := h'.gr hl Ω hΩ
  have hK : IsCompact (Ω' * (Ω * tsupport η) ∪ Ω * tsupport η) := (h3.mul (hΩ.mul hη.cpt)).union (hΩ.mul hη.cpt)
  obtain ⟨C, hCC⟩ := hm _ hK
  set K := Ω' * (Ω * tsupport η) ∪ Ω * tsupport η
  refine ⟨C₀ + C * D * μ.real K, fun k κ hκ => ?_⟩
  have key : ∀ x, ‖Two.conv μ η φ (a ^ k * κ) - Two.conv μ η φ (n x * (a ^ k * κ))‖ ≤ C * D * μ.real K * (2 ^ k) ^ m := fun x => by
    obtain ⟨γ, h5, u, h6, h7, h8⟩ := h4 x k
    have e : ∀ z, Two.conv μ η φ (a ^ k * z) = ∫ y, φ (a ^ k * y) * η (z⁻¹ * y) ∂μ := fun z => by
      rw [Two.conv, ← integral_mul_left_eq_self _ z⁻¹]
      simp only [mul_assoc, mul_inv_cancel_left]
    have i : ∀ z, Integrable (fun y => φ (a ^ k * y) * η (z⁻¹ * y)) μ := fun z => by
      simpa only [mul_assoc, mul_inv_cancel_left] using (hη.int μ h.cont (a ^ k * z)).comp_mul_left z⁻¹
    rw [← h'.inv γ h5 (n x * _), ← mul_assoc γ, ← mul_assoc _ _ κ, h7, mul_assoc _ u, e, e, ← integral_sub (i _) (i _),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun y hy => ?_]
    · refine (norm_setIntegral_le_of_norm_le_const (C := C * D * (2 ^ k) ^ m) hK.measure_lt_top fun y hy => ?_).trans_eq (by ring)
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, mul_inv_rev, mul_assoc κ⁻¹]
      refine (mul_le_mul (hCC k y hy) (h8 κ hκ y) (abs_nonneg _) ((norm_nonneg _).trans (hCC k y hy))).trans_eq ?_
      field_simp
      ring
    · have z1 : η (κ⁻¹ * y) = 0 := image_eq_zero_of_notMem_tsupport fun hh => hy (Or.inr ⟨κ, hκ, _, hh, by simp⟩)
      have z2 : η ((u * κ)⁻¹ * y) = 0 := image_eq_zero_of_notMem_tsupport fun hh =>
        hy (Or.inl ⟨u, h6, _, ⟨κ, hκ, _, hh, rfl⟩, by simp [mul_assoc]⟩)
      rw [z1, z2, sub_self]
  obtain ⟨M, hM⟩ := h'.bound hC (isCompact_singleton (x := a ^ k * κ))
  have := h'.cont
  have hi : Integrable (fun x => Two.conv μ η φ (n x * (a ^ k * κ))) lam :=
    .of_bound (Continuous.aestronglyMeasurable (by fun_prop)) M (.of_forall fun x => hM x _ rfl)
  have e : Two.conv μ η φ (a ^ k * κ) = Two.conv μ η c (a ^ k * κ) +
      ∫ x, (Two.conv μ η φ (a ^ k * κ) - Two.conv μ η φ (n x * (a ^ k * κ))) ∂lam := by
    rw [integral_sub (integrable_const _) hi, ← h'.av]; simp
  have h9 := hC₀ k κ hκ
  rw [pow_zero, mul_one] at h9
  have h10 : (1 : ℝ) ≤ (2 ^ k) ^ m := one_le_pow₀ (one_le_pow₀ one_le_two)
  rw [e, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (h9.trans (le_mul_of_one_le_right ((norm_nonneg _).trans h9) h10)) ?_)
  simpa using norm_integral_le_of_norm_le_const (μ := lam) (.of_forall key)
end Dat
end PositivityTheory.ThKEnd.Two
