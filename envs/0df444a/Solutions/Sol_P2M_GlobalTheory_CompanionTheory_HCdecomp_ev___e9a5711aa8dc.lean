-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_HCdecomp_ev___e9a5711aa8dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:55.856423+00:00
-- url     : https://prove2.me/submissions/0860dd6f-5b89-496f-9229-30e995279406

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.HCdecomp
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (p : Fin n × Fin n) :
    ev E (FreeAlgebra.ι ℂ p) = E p.1 p.2 := by
  simp [ev]
end GlobalTheory.CompanionTheory.HCdecomp
