-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.char_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:27.455741+00:00
-- url     : https://prove2.me/submissions/3c6a62cd-01bc-499f-bf33-9424ca822871

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace PositivityTheory.Mirab.Irr
theorem _root_.solution (ψ₀ : AddChar k ℂ) (u : uniSub k n) :
    genericChar n ψ₀ (u⁻¹) * genericChar n ψ₀ u = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]
end PositivityTheory.Mirab.Irr
