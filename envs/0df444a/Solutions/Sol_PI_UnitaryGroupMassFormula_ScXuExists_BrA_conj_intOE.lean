-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.conj_intOE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:05.139847+00:00
-- url     : https://prove2.me/submissions/131d1220-6ac0-4a76-bac3-8965ffe96008

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
theorem _root_.solution (I : AutInst) (x : I.E) (hx : x ∈ Formalism.UG.intOE I.E) :
    starRingEnd I.E x ∈ Formalism.UG.intOE I.E := by
  obtain ⟨o, rfl⟩ := hx
  have h : IsIntegral ℤ (starRingEnd I.E (algebraMap (𝓞 I.E) I.E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
