-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IAT.locv_incl_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:25.392868+00:00
-- url     : https://prove2.me/submissions/2f82eca8-abf9-42ec-9d97-7952fde7e39a

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralityAtPrimeLattices_AwayLoc
import Theorems.Thm_Formalism_UG_P_levelv_tmul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IAT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.IAT
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (e : E) (he : IsIntegral ℤ e) :
    Formalism.UG.inclE (F := F) (v.adicCompletion F) e ∈ Formalism.L2.Geo.Def.PC.SV E v := by
  have he' : e ∈ intOE E := ⟨⟨e, he⟩, rfl⟩
  exact levelv_tmul_mem v e he' 1 (one_mem _)
end PI.UnitaryGroupMassFormula.IAT
