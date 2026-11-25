-- Prove2me | solution 1 for PI.ScRefExists.WB.WA_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:57.862863+00:00
-- url     : https://prove2.me/submissions/01c5abb3-8c0b-4751-a38e-1d61e39e404b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WeilBasisExistence
import Theorems.Thm_PI_ScRefExists_WB_mem_WA
import Theorems.Thm_PI_ScRefExists_WB_LA_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WB
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WB
theorem _root_.solution {p r : ℕ} (e f : Fin r → Fin I.n → I.E) [IsPrincipalIdealRing (Ap I p)] :
    Module.Finite (Ap I p) (WA I p r e f) := by
  have hle : WA I p r e f ≤ LA I p := fun x hx => (mem_WA I).mp hx |>.1
  haveI : IsNoetherian (Ap I p) (LA I p) := isNoetherian_of_fg_of_noetherian _ (LA_fg I p)
  have hfg : ((WA I p r e f).comap (LA I p).subtype).FG := IsNoetherian.noetherian _
  have hmap : ((WA I p r e f).comap (LA I p).subtype).map (LA I p).subtype = WA I p r e f := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  rw [Module.Finite.iff_fg, ← hmap]
  exact hfg.map _
end PI.ScRefExists.WB
