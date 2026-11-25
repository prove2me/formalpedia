-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.incl_mem_Lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:25.729695+00:00
-- url     : https://prove2.me/submissions/1246561c-bbfa-431c-b8c1-d4fad09148c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (l : Fin I.n → I.E) (hl : l ∈ I.L) :
    (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ I.Lf :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
end PI.UnitaryGroupMassFormula.ScXuExists
