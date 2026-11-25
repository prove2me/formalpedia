-- Prove2me | solution 1 for PI.FJMS.blkHyp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:34.63417+00:00
-- url     : https://prove2.me/submissions/2bfc486b-1ee0-4573-800f-57f78a6af50c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_PI_FJMS_gR_neg_block
import Theorems.Thm_PI_FJMS_sw_neg_block
import Theorems.Thm_P2M_PI_FJMS_bRow_apply__fa8f98d64b0d
import Theorems.Thm_P2M_PI_FJMS_bCol_apply__63c2c4b09970
import Theorems.Thm_PI_FJMS_pure_of
import Theorems.Thm_PI_FJMP_exists_mem_support
import Theorems.Thm_PI_FJMP_ker_of_hw
import Theorems.Thm_PI_FJMP_leftRootOperator_eq_signedPolarization
import Theorems.Thm_PI_FJMP_mem_leftHighestWeight_of_isMinimalJointVector
import Theorems.Thm_PI_FJMP_mem_rightHighestWeight_of_isMinimalJointVector
import Theorems.Thm_PI_FJMP_monomialLeftWeight_eq_weight_sub
import Theorems.Thm_PI_FJMP_monomialRightWeight_eq_weight_sub
import Theorems.Thm_PI_FJMP_ne_of_posC
import Theorems.Thm_PI_FJMP_rightRootOperator_eq_signedPolarization
import Theorems.Thm_PI_FJM_leftDiagonalActionFormula
import Theorems.Thm_PI_FJM_leftOffDiagonalActionFormula
import Theorems.Thm_PI_FJM_rightDiagonalActionFormula
import Theorems.Thm_PI_FJM_rightOffDiagonalActionFormula
import Theorems.Thm_PI_WFJM_leftDiagonalActionFormula
import Theorems.Thm_PI_WFJM_leftOffDiagonalActionFormula
import Theorems.Thm_PI_WFJM_ne_of_posC
import Theorems.Thm_PI_WFJM_rightDiagonalActionFormula
import Theorems.Thm_PI_WFJM_rightOffDiagonalActionFormula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
variable {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
namespace PI.FJMS
theorem _root_.solution (hM : MinHyp p q r s μ μ' P) {m n : ℕ} (iX : Fin m → Ix p q) (jX : Fin n → Ix r s)
    (hi : Function.Injective iX) (hj : Function.Injective jX)
    (hmi : ∀ a b : Fin m, a < b → posC (iX b) (iX a)) (hmj : ∀ c d : Fin n, c < d → posC (jX d) (jX c))
    (hs1 : ∀ (a b : Fin m) (c : Ix r s), linePos ((iX b, c) : Ln p q r s) = linePos ((iX a, c) : Ln p q r s))
    (hs2 : ∀ (c d : Fin n) (a : Ix p q), linePos ((a, jX d) : Ln p q r s) = linePos ((a, jX c) : Ln p q r s))
    (hlp : ∀ i k, linePos ((iX i, jX k) : Ln p q r s) = false)
    (hcol : ∀ (i : Fin m) (c : Ix r s), linePos ((iX i, c) : Ln p q r s) = false → nu2 p q r s μ' c < 0 →
      c ∈ Set.range jX)
    (hrow : ∀ (k : Fin n) (a : Ix p q), linePos ((a, jX k) : Ln p q r s) = false → nu1 p q r s μ a < 0 →
      a ∈ Set.range iX)
    (hnu1 : ∀ i, nu1 p q r s μ (iX i) < 0) (hnu2 : ∀ k, nu2 p q r s μ' (jX k) < 0)
    (α : Fin m → ℕ) (β : Fin n → ℕ) (hα : ∀ i, α i = ⌊-nu1 p q r s μ (iX i)⌋₊)
    (hβ : ∀ k, β k = ⌊-nu2 p q r s μ' (jX k)⌋₊) :
    IsBlockHighestWeight (fun x : Fin m × Fin n => ((iX x.1, jX x.2) : Ln p q r s)) α β P := by
  have hw1 := mem_leftHighestWeight_of_isMinimalJointVector hM
  have hw2 := mem_rightHighestWeight_of_isMinimalJointVector hM
  have hP0 : P ≠ 0 := hM.2.1
  have lpf : ∀ l : Ln p q r s, (linePos l = true ↔ 0 < nu1 p q r s μ l.1) → nu1 p q r s μ l.1 < 0 →
      linePos l = false := by
    intro l h h'
    cases hl : linePos l
    · rfl
    · rw [hl] at h; linarith [h.1 rfl]
  have urow : ∀ i c, c ∉ Set.range jX → NoVar P ((iX i, c) : Ln p q r s) := by
    intro i c hc e he
    by_contra hne
    obtain ⟨-, h2, h3, h4⟩ := pure_of hM he hne
    have hf : linePos ((iX i, c) : Ln p q r s) = false := lpf _ h3 (hnu1 i)
    have hneg : nu2 p q r s μ' c < 0 := by
      rw [hf] at h4
      rcases lt_or_gt_of_ne h2 with h | h
      · exact h
      · exact absurd (h4.2 h) Bool.false_ne_true
    exact hc (hcol i c hf hneg)
  have ucol : ∀ k a, a ∉ Set.range iX → NoVar P ((a, jX k) : Ln p q r s) := by
    intro k a ha e he
    by_contra hne
    obtain ⟨h1, -, h3, h4⟩ := pure_of hM he hne
    have hf : linePos ((a, jX k) : Ln p q r s) = false := by
      cases hl : linePos ((a, jX k) : Ln p q r s)
      · rfl
      · rw [hl] at h4; linarith [h4.1 rfl, hnu2 k]
    have hneg : nu1 p q r s μ a < 0 := by
      rw [hf] at h3
      rcases lt_or_gt_of_ne h1 with h | h
      · exact h
      · exact absurd (h3.2 h) Bool.false_ne_true
    exact ha (hrow k a hf hneg)
  have rowv : ∀ e ∈ P.support, ∀ i, -nu1 p q r s μ (iX i) = ((∑ k, e ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by
    intro e he i
    rw [← monomialLeftWeight_eq_weight_sub leftDiagonalActionFormula hw1 e he (iX i)]
    have h := sw_neg_block e (fun c : Ix r s => ((iX i, c) : Ln p q r s)) (fun c => linePos ((iX i, c) : Ln p q r s))
      jX hj (fun c hc => urow i c hc e he) (fun k => hlp i k)
    rw [show wt1 e (iX i) = sw e (fun c : Ix r s => ((iX i, c) : Ln p q r s))
      (fun c => linePos ((iX i, c) : Ln p q r s)) from rfl, h]
    push_cast; ring
  have colv : ∀ e ∈ P.support, ∀ k, -nu2 p q r s μ' (jX k) = ((∑ i, e ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by
    intro e he k
    rw [← monomialRightWeight_eq_weight_sub rightDiagonalActionFormula hw2 e he (jX k)]
    have h := sw_neg_block e (fun a : Ix p q => ((a, jX k) : Ln p q r s)) (fun a => linePos ((a, jX k) : Ln p q r s))
      iX hi (fun a ha => ucol k a ha e he) (fun i => hlp i k)
    rw [show wt2 e (jX k) = sw e (fun a : Ix p q => ((a, jX k) : Ln p q r s))
      (fun a => linePos ((a, jX k) : Ln p q r s)) from rfl, h]
    push_cast; ring
  obtain ⟨e0, he0⟩ := exists_mem_support hP0
  refine ⟨fun a b hab => ?_, fun c d hcd => ?_, fun e he => ⟨fun i => ?_, fun k => ?_⟩, fun i => ?_, fun k => ?_⟩
  · have hne := ne_of_posC (hmi a b hab)
    have hR := ker_of_hw hw1 (iX b) (iX a) (hmi a b hab)
    rw [leftOffDiagonalActionFormula p q r s _ _ hne, leftRootOperator_eq_signedPolarization _ _ hne (hs1 b a) P,
      gR_neg_block _ _ _ jX hj P (fun c hc => urow b c hc) (fun c hc => urow a c hc) (fun k => hlp b k),
      neg_eq_zero] at hR
    rw [bRow_apply']
    exact hR
  · have hne := ne_of_posC (hmj c d hcd)
    have hR := ker_of_hw hw2 (jX d) (jX c) (hmj c d hcd)
    rw [rightOffDiagonalActionFormula p q r s _ _ hne, rightRootOperator_eq_signedPolarization _ _ hne (hs2 d c) P,
      gR_neg_block _ _ _ iX hi P (fun a ha => ucol d a ha) (fun a ha => ucol c a ha) (fun i => hlp i d),
      neg_eq_zero] at hR
    rw [bCol_apply']
    exact hR
  · rw [hα i, rowv e he i, Nat.floor_natCast]
  · rw [hβ k, colv e he k, Nat.floor_natCast]
  · rw [hα i, Nat.floor_pos]
    have h := hnu1 i
    have h2 := rowv e0 he0 i
    rw [h2]
    have h' : 0 < ∑ k, e0 ((iX i, jX k) : Ln p q r s) := by
      have : (0 : ℚ) < ((∑ k, e0 ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by rw [← h2]; linarith
      exact_mod_cast this
    exact_mod_cast h'
  · rw [hβ k, Nat.floor_pos]
    have h := hnu2 k
    have h2 := colv e0 he0 k
    rw [h2]
    have h' : 0 < ∑ i, e0 ((iX i, jX k) : Ln p q r s) := by
      have : (0 : ℚ) < ((∑ i, e0 ((iX i, jX k) : Ln p q r s) : ℕ) : ℚ) := by rw [← h2]; linarith
      exact_mod_cast this
    exact_mod_cast h'
end PI.FJMS
