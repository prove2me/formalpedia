-- Prove2me | solution 1 for PI.OpWords.polarizationBihomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:35.18161+00:00
-- url     : https://prove2.me/submissions/24d1c778-5148-4971-8c44-f593eac3e5ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Theorems.Thm_PI_OpWords_rop_apply_eq
import Theorems.Thm_PI_OpWords_iwh_X_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution : RBihom := by
  intro K _ _ k d a b f hf
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  show Rop K k a b f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  rw [rop_apply_eq]
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ ?_ ?_, Submodule.sub_mem _ ?_ ?_⟩ <;>
    rw [mem_weightedHomogeneousSubmodule]
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2
end PI.OpWords
