-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.hl_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:18.66739+00:00
-- url     : https://prove2.me/submissions/379149d4-c09a-465b-886b-263418c238ef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_pr_vec
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_pr_int

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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (X Y : Fin I.n → RV I v)
    (hX : X ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (hY : Y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) : p1 (hl I v X Y) ∈ OV I v := by
  rw [← pr_vec]
  exact pr_int I v ε p1 hp _ (Submodule.subset_span ⟨X, hX, rfl⟩) _ (Submodule.subset_span ⟨Y, hY, rfl⟩)
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
