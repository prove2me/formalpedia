-- Prove2me | solution 1 for PI.LocJacOrd.W.Ar.alp_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:00.721449+00:00
-- url     : https://prove2.me/submissions/6943277c-17e0-4515-8232-a7d4faca17b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Theorems.Thm_PI_LocJacOrd_W_Ar_dV_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocJacOrd.W.Ar
theorem _root_.solution (r : ℕ) (i : Fin (r + 1)) : alp v r i ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero
end PI.LocJacOrd.W.Ar
