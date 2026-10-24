-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P50.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:47:06.76185+00:00
-- url     : https://prove2.me/submissions/8e37b56a-0a9a-4286-8616-b48bf0001224

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50


/-! X6: operator Hölder continuity of `a ↦ a ^ p` (`0 ≤ p ≤ 1`) in a C*-algebra. -/

open scoped NNReal
set_option linter.unusedSectionVars false
noncomputable section
namespace X6HO

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_le_sa {x : A} (hx : IsSelfAdjoint x) {c : ℝ} (hc : 0 ≤ c)
    (h1 : x ≤ algebraMap ℝ A c) (h2 : -x ≤ algebraMap ℝ A c) : ‖x‖ ≤ c := by
  obtain (h | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim x 0, hc]
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with h | h
  · exact ((le_algebraMap_iff_spectrum_le hx).1 h1) _ h
  · have : ‖x‖ ∈ spectrum ℝ (-x) := by
      rw [← spectrum.neg_eq]; simpa using h
    exact ((le_algebraMap_iff_spectrum_le hx.neg).1 h2) _ this

lemma rpow_add_le {b : A} (hb : 0 ≤ b) {δ : ℝ} (hδ : 0 ≤ δ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (b + algebraMap ℝ A δ) ^ p ≤ b ^ p + algebraMap ℝ A (δ ^ p) := by
  have hbd : 0 ≤ b + algebraMap ℝ A δ :=
    add_nonneg hb (by rw [Algebra.algebraMap_eq_smul_one]; exact smul_nonneg hδ zero_le_one)
  have e1 : b + algebraMap ℝ A δ = cfc (fun x : ℝ => x + δ) b := by
    rw [cfc_add .., cfc_id' .., cfc_const ..]
  rw [CFC.rpow_eq_cfc_real hbd, CFC.rpow_eq_cfc_real hb, e1, ← cfc_comp' (fun x : ℝ => x ^ p)
    (fun x : ℝ => x + δ) b, ← cfc_const (δ ^ p) b, ← cfc_add ..]
  refine cfc_mono fun x hx => ?_
  have hx0 : 0 ≤ x := by
    have := spectrum_nonneg_of_nonneg hb hx
    exact this
  exact Real.rpow_add_le_add_rpow hx0 hδ hp0 hp1

lemma holder {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖a ^ p - b ^ p‖ ≤ ‖a - b‖ ^ p := by
  have one_side : ∀ {a b : A}, 0 ≤ a → 0 ≤ b → a ^ p - b ^ p ≤ algebraMap ℝ A (‖a - b‖ ^ p) := by
    intro a b ha hb
    have hsa : IsSelfAdjoint (a - b) := (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
    have h1 : a ≤ b + algebraMap ℝ A ‖a - b‖ := by
      have := hsa.le_algebraMap_norm_self
      rw [sub_le_iff_le_add'] at this; exact this
    have h2 : a ^ p ≤ (b + algebraMap ℝ A ‖a - b‖) ^ p := CFC.rpow_le_rpow ⟨hp0, hp1⟩ h1
    have h3 := rpow_add_le hb (norm_nonneg (a - b)) hp0 hp1
    rw [sub_le_iff_le_add']
    exact h2.trans h3
  refine norm_le_sa ?_ (Real.rpow_nonneg (norm_nonneg _) _) (one_side ha hb) ?_
  · exact (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).sub (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg)
  · rw [neg_sub, norm_sub_rev]; exact one_side hb ha

lemma rpow_norm_le_one {a : A} (ha : 0 ≤ a) (ha1 : a ≤ 1) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖a ^ p‖ ≤ 1 := by
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ CFC.rpow_nonneg]
  calc a ^ p ≤ (1 : A) ^ p := CFC.rpow_le_rpow ⟨hp0, hp1⟩ ha1
    _ = 1 := CFC.one_rpow

theorem main {E F : A} (hE : 0 ≤ E) (hE1 : E ≤ 1) (hF : 0 ≤ F) (hF1 : F ≤ 1) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ‖E ^ α * (1 - E) ^ (1 - α) - F ^ α * (1 - F) ^ (1 - α)‖ ≤
      ‖E - F‖ ^ α + ‖E - F‖ ^ (1 - α) := by
  have hE' : 0 ≤ 1 - E := sub_nonneg.2 hE1
  have hF' : 0 ≤ 1 - F := sub_nonneg.2 hF1
  have hE'1 : 1 - E ≤ 1 := sub_le_self _ hE
  have e : E ^ α * (1 - E) ^ (1 - α) - F ^ α * (1 - F) ^ (1 - α) =
      (E ^ α - F ^ α) * (1 - E) ^ (1 - α) + F ^ α * ((1 - E) ^ (1 - α) - (1 - F) ^ (1 - α)) := by
    noncomm_ring
  rw [e]
  have k1 : ‖(1 - E) ^ (1 - α)‖ ≤ 1 := rpow_norm_le_one hE' hE'1 (by linarith) (by linarith)
  have k2 : ‖F ^ α‖ ≤ 1 := rpow_norm_le_one hF hF1 hα.le hα1.le
  have k3 := holder hE hF hα.le hα1.le
  have k4 := holder hE' hF' (p := 1 - α) (by linarith) (by linarith)
  have e2 : (1 - E) - (1 - F) = -(E - F) := by abel
  rw [e2, norm_neg] at k4
  calc _ ≤ ‖(E ^ α - F ^ α) * (1 - E) ^ (1 - α)‖ + ‖F ^ α * ((1 - E) ^ (1 - α) - (1 - F) ^ (1 - α))‖ :=
        norm_add_le _ _
    _ ≤ ‖E ^ α - F ^ α‖ * ‖(1 - E) ^ (1 - α)‖ + ‖F ^ α‖ * ‖(1 - E) ^ (1 - α) - (1 - F) ^ (1 - α)‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖E - F‖ ^ α * 1 + 1 * ‖E - F‖ ^ (1 - α) := by
        gcongr
    _ = _ := by ring

end X6HO


open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace X6HO
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50

section
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma key {n : ℕ} (G : M n) (hG : 0 ≤ G) (hG1 : G ≤ 1) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    cfc (hAlpha α) G = G ^ α * (1 - G) ^ (1 - α) := by
  have hc1 : Continuous fun t : ℝ => t ^ α := Real.continuous_rpow_const hα.le
  have hc2 : Continuous fun t : ℝ => t ^ (1 - α) := Real.continuous_rpow_const (by linarith)
  have e0 : hAlpha α = fun t => t ^ α * (1 - t) ^ (1 - α) := by
    funext t; rfl
  have h2 : cfc (fun t : ℝ => (1 - t) ^ (1 - α)) G = (1 - G) ^ (1 - α) := by
    have e1 : (1 : M n) - G = cfc (fun t : ℝ => 1 - t) G := by
      rw [cfc_sub .., cfc_const_one .., cfc_id' ..]
    rw [CFC.rpow_eq_cfc_real (sub_nonneg.2 hG1), e1]
    exact cfc_comp' (fun t : ℝ => t ^ (1 - α)) (fun t : ℝ => 1 - t) G hc2.continuousOn
  rw [e0, cfc_mul (fun t : ℝ => t ^ α) (fun t : ℝ => (1 - t) ^ (1 - α)) G hc1.continuousOn
    (hc2.comp (by fun_prop)).continuousOn, h2, ← CFC.rpow_eq_cfc_real hG]

theorem sol {n : ℕ} (E F : M n) (hE : IsEffect E) (hF : IsEffect F)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    specNorm (cfc (hAlpha alpha) E - cfc (hAlpha alpha) F) ≤
      Real.rpow (specNorm (E - F)) alpha + Real.rpow (specNorm (E - F)) (1 - alpha) := by
  have hE0 : (0 : M n) ≤ E := Matrix.nonneg_iff_posSemidef.2 hE.1
  have hE1 : E ≤ 1 := Matrix.le_iff.2 hE.2
  have hF0 : (0 : M n) ≤ F := Matrix.nonneg_iff_posSemidef.2 hF.1
  have hF1 : F ≤ 1 := Matrix.le_iff.2 hF.2
  rw [key E hE0 hE1 halpha halpha1, key F hF0 hF1 halpha halpha1]
  exact main hE0 hE1 hF0 hF1 halpha halpha1

end
end X6HO

section
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50

theorem solution {n : ℕ} (E F : M n) (hE : IsEffect E) (hF : IsEffect F)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    specNorm (cfc (hAlpha alpha) E - cfc (hAlpha alpha) F) ≤
      Real.rpow (specNorm (E - F)) alpha + Real.rpow (specNorm (E - F)) (1 - alpha) :=
  X6HO.sol E F hE hF alpha halpha halpha1

end
