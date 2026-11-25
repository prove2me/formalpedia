-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.Gl.mem_mL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:40.858455+00:00
-- url     : https://prove2.me/submissions/feea8781-bd70-4237-b18e-e7dc67940274

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl
theorem _root_.solution (I : AutInst) (m : ℕ) {W : Fin I.n → I.E ⊗[I.F] Af I.F} (hW : W ∈ I.Lf) :
    (m : I.E ⊗[I.F] Af I.F) • W ∈ mL I m :=
  Submodule.subset_span ⟨W, hW, rfl⟩
end PI.UnitaryGroupMassFormula.ScXuExists.Gl
