-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.first_coordinate_vector_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:49.741578+00:00
-- url     : https://prove2.me/submissions/aecc5f86-a98e-4f30-a7f0-ddfc7ff56c2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_first_coordinate_vector_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_first_coordinate_vector_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_first_coordinate_vector_zero

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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (hp : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) (X : Fin I.n → RV I v)
    (hX : X ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    vec1 p1 X ∈ Submodule.span (OV I v)
      ((fun l => vec1 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)) '' (I.L : Set _)) := by
  induction hX using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero => rw [first_coordinate_vector_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [first_coordinate_vector_add]; exact add_mem ha hb
  | smul c a _ ha => rw [first_coordinate_vector_smul I v p1 hp]; exact Submodule.smul_mem _ c ha
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
