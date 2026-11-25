-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.pr_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:58.575917+00:00
-- url     : https://prove2.me/submissions/1f2ef624-ff64-4129-930f-17d5c6f42dcd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_pr_vec
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_hl_ratV
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_ScXuExists_BrA_vecV_incl__c4acc129ac4b

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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) (x y : Fin I.n → I.E) :
    pr (Pm I v p1) (vec2 p1 (PI.FinKW.vecV I v (incl I x))) (vec1 p1 (PI.FinKW.vecV I v (incl I y))) =
      p1 (inclV I v (Formalism.UG.hform (starRingEnd I.E) I.J x y)) := by
  rw [pr_vec, vecV_incl', vecV_incl', hl_ratV]
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
