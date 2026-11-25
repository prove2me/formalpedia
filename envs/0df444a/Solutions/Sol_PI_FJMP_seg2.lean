-- Prove2me | solution 1 for PI.FJMP.seg2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:28.38749+00:00
-- url     : https://prove2.me/submissions/60a8c328-09b5-46fd-adf4-264c8e9ac3f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_seg_pos_gen
import Theorems.Thm_PI_FJMP_seg_neg_gen
import Theorems.Thm_PI_FJMP_monomialRightWeight_eq_weight_sub
import Theorems.Thm_PI_FJMP_mem_rightHighestWeight_of_isMinimalJointVector
import Theorems.Thm_PI_FJMP_pureJ_of
import Theorems.Thm_PI_FJMP_rightRootOperator_eq_signedPolarization
import Theorems.Thm_PI_FJMP_ker_of_hw
import Theorems.Thm_PI_FJMP_ne_of_posC

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
open PI PI.FJMP
open PI.FJM
namespace PI.FJMP
theorem _root_.solution (hW1 : FormWt1) (hW2 : FormWt2) (hR2 : FormRaise2) {p q r s : ℕ} {μ : Ix p q → ℚ}
    {μ' : Ix r s → ℚ} {P : Pol p q r s} (hM : MinHyp p q r s μ μ' P) (c d : Ix r s) (hcd : posC c d)
    (hsame : ∀ a : Ix p q, linePos ((a, d) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) :
    (0 < nu2 p q r s μ' d → 0 < nu2 p q r s μ' c) ∧ (nu2 p q r s μ' c < 0 → nu2 p q r s μ' d < 0) := by
  have hP2 := mem_rightHighestWeight_of_isMinimalJointVector hM
  have hne := ne_of_posC hcd
  have hR : gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d))
      (fun a => linePos ((a, c) : Ln p q r s)) P = 0 := by
    rw [← rightRootOperator_eq_signedPolarization c d hne hsame P, ← hR2 p q r s c d hne]
    exact ker_of_hw hP2 c d hcd
  have hu : Function.Injective (fun a : Ix p q => ((a, c) : Ln p q r s)) := fun a a' h => (Prod.ext_iff.mp h).1
  have hv : Function.Injective (fun a : Ix p q => ((a, d) : Ln p q r s)) := fun a a' h => (Prod.ext_iff.mp h).1
  have huv : ∀ a a' : Ix p q, ((a, c) : Ln p q r s) ≠ (a', d) := fun a a' h => hne (Prod.ext_iff.mp h).2
  have hM' := hM
  unfold MinHyp at hM'
  have hPJ := pureJ_of hW1 hW2 p q r s μ μ' P hM
  have hswA : ∀ e ∈ P.support, (sw e (fun a : Ix p q => ((a, c) : Ln p q r s))
      (fun a => linePos ((a, c) : Ln p q r s)) : ℚ) = nu2 p q r s μ' c := by
    intro e he
    rw [← monomialRightWeight_eq_weight_sub hW2 hP2 e he c]
    rfl
  have hswB : ∀ e ∈ P.support, (sw e (fun a : Ix p q => ((a, d) : Ln p q r s))
      (fun a => linePos ((a, c) : Ln p q r s)) : ℚ) = nu2 p q r s μ' d := by
    intro e he
    rw [← monomialRightWeight_eq_weight_sub hW2 hP2 e he d]
    congr 1
    unfold sw wt2
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsame a]
  refine ⟨fun hd => seg_pos_gen _ _ _ hu huv P hR hM'.2.1 _ _ hswB ?_ hd,
    fun hc => seg_neg_gen _ _ _ hv huv P hR hM'.2.1 _ _ hswA ?_ hc⟩
  · intro e he a ha
    obtain ⟨-, h2, -, h4⟩ := hPJ e he (a, c) ha
    exact ⟨h2, h4⟩
  · intro e he a ha
    obtain ⟨-, h2, -, h4⟩ := hPJ e he (a, d) ha
    refine ⟨h2, ?_⟩
    show linePos ((a, c) : Ln p q r s) = true ↔ _
    rw [← hsame a]
    exact h4
end PI.FJMP
