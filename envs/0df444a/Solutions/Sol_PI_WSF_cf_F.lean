-- Prove2me | solution 1 for PI.WSF.cf_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:54.585686+00:00
-- url     : https://prove2.me/submissions/6f8271f8-29c0-4c08-b880-e67edea1a474

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CfEqSumOfSubset
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial
namespace PI.WSF
theorem _root_.solution {N : ℕ} (lam : DomWeight N) :
    (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 ∧
      0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re := by
  have hne : extremal ℂ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW
  obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.fockPos _ _ hne
  exact ⟨h2, h1⟩
end PI.WSF
