-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.lattice_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:43.680799+00:00
-- url     : https://prove2.me/submissions/0a5ddaf9-bad8-41fd-ad11-6e290a938d41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_LatIs_latSet_eq
import Theorems.Thm_Formalism_UG_P_global_lattice_isLattice_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct
open PI.LatSizeCont
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC
namespace PI.UnitaryGroupMassFormula.LSC
theorem _root_.solution : LatIs := by
  intro I x
  have hL := Formalism.UG.P.global_lattice_isLattice_holds I.F I.E (Fin I.n) I.L (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
  exact ⟨_, hL.fg, hL.span_eq_top, LatIs.latSet_eq I x⟩
end PI.UnitaryGroupMassFormula.LSC
