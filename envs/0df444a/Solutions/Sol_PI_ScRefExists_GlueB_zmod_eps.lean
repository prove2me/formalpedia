-- Prove2me | solution 1 for PI.ScRefExists.GlueB.zmod_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:56.947321+00:00
-- url     : https://prove2.me/submissions/0049068f-d62f-486b-a7c3-f813658ab890

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight
import Theorems.Thm_PI_ScRefExists_GlueB_zmod_of_GE
import Theorems.Thm_PI_ScRefExists_GlueB_zmod_add
import Theorems.Thm_PI_ScRefExists_GlueB_zmod_mul_int
import Theorems.Thm_P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed


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
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueB
open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)
namespace PI.ScRefExists.GlueB
theorem _root_.solution {ε : I.E ⊗[I.F] Af I.F} {θ : I.E}
    (hε : ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) θ)) {x : I.E}
    (hx : x ∈ (algebraMap (𝓞 I.E) I.E).range) (h : GE I g (θ * x)) :
    ZMod' I g (ε * Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨s, rfl⟩ := hx
  have h1 := zmod_mul_int I g hε (inclE_mem' I s)
  have h2 := zmod_add I g h1 (zmod_of_GE I g h)
  convert h2 using 1
  rw [map_mul]
  have e : algebraMap (𝓞 I.E) I.E s = (s : I.E) := rfl
  rw [e]
  ring
end PI.ScRefExists.GlueB
