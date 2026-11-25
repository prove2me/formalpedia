-- Prove2me | solution 1 for PI.FJMP.seg1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:23.322532+00:00
-- url     : https://prove2.me/submissions/c02c05ca-1340-440f-85e0-e19597a9d4a4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_seg_pos_gen
import Theorems.Thm_PI_FJMP_seg_neg_gen
import Theorems.Thm_PI_FJMP_monomialLeftWeight_eq_weight_sub
import Theorems.Thm_PI_FJMP_mem_leftHighestWeight_of_isMinimalJointVector
import Theorems.Thm_PI_FJMP_pureJ_of
import Theorems.Thm_PI_FJMP_leftRootOperator_eq_signedPolarization
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
theorem _root_.solution (hW1 : FormWt1) (hW2 : FormWt2) (hR1 : FormRaise1) {p q r s : ℕ} {μ : Ix p q → ℚ}
    {μ' : Ix r s → ℚ} {P : Pol p q r s} (hM : MinHyp p q r s μ μ' P) (a b : Ix p q) (hab : posC a b)
    (hsame : ∀ c : Ix r s, linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) :
    (0 < nu1 p q r s μ b → 0 < nu1 p q r s μ a) ∧ (nu1 p q r s μ a < 0 → nu1 p q r s μ b < 0) := by
  have hP1 := mem_leftHighestWeight_of_isMinimalJointVector hM
  have hne := ne_of_posC hab
  have hR : gR (fun c : Ix r s => ((a, c) : Ln p q r s)) (fun c => (b, c))
      (fun c => linePos ((a, c) : Ln p q r s)) P = 0 := by
    rw [← leftRootOperator_eq_signedPolarization a b hne hsame P, ← hR1 p q r s a b hne]
    exact ker_of_hw hP1 a b hab
  have hu : Function.Injective (fun c : Ix r s => ((a, c) : Ln p q r s)) := fun c c' h => (Prod.ext_iff.mp h).2
  have hv : Function.Injective (fun c : Ix r s => ((b, c) : Ln p q r s)) := fun c c' h => (Prod.ext_iff.mp h).2
  have huv : ∀ c c' : Ix r s, ((a, c) : Ln p q r s) ≠ (b, c') := fun c c' h => hne (Prod.ext_iff.mp h).1
  have hM' := hM
  unfold MinHyp at hM'
  have hPJ := pureJ_of hW1 hW2 p q r s μ μ' P hM
  have hswA : ∀ e ∈ P.support, (sw e (fun c : Ix r s => ((a, c) : Ln p q r s))
      (fun c => linePos ((a, c) : Ln p q r s)) : ℚ) = nu1 p q r s μ a := by
    intro e he
    rw [← monomialLeftWeight_eq_weight_sub hW1 hP1 e he a]
    rfl
  have hswB : ∀ e ∈ P.support, (sw e (fun c : Ix r s => ((b, c) : Ln p q r s))
      (fun c => linePos ((a, c) : Ln p q r s)) : ℚ) = nu1 p q r s μ b := by
    intro e he
    rw [← monomialLeftWeight_eq_weight_sub hW1 hP1 e he b]
    congr 1
    unfold sw wt1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsame c]
  refine ⟨fun hb => seg_pos_gen _ _ _ hu huv P hR hM'.2.1 _ _ hswB ?_ hb,
    fun ha => seg_neg_gen _ _ _ hv huv P hR hM'.2.1 _ _ hswA ?_ ha⟩
  · intro e he c hc
    obtain ⟨h1, -, h3, -⟩ := hPJ e he (a, c) hc
    exact ⟨h1, h3⟩
  · intro e he c hc
    obtain ⟨h1, -, h3, -⟩ := hPJ e he (b, c) hc
    refine ⟨h1, ?_⟩
    show linePos ((a, c) : Ln p q r s) = true ↔ _
    rw [← hsame c]
    exact h3
end PI.FJMP
