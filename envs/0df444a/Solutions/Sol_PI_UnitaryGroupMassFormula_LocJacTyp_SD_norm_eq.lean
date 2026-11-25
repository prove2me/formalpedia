-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.SD.norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:10.532855+00:00
-- url     : https://prove2.me/submissions/12b0ebb1-12aa-4935-8ec3-e855592ad2ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_p_e
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_p_f
import Theorems.Thm_PI_LocDualGen_EpS_pr_apply
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
open PI.UnitaryGroupMassFormula.LocJacTyp.SD
variable {σ v} (D : SD σ v)
namespace PI.UnitaryGroupMassFormula.LocJacTyp.SD
theorem _root_.solution (z : Fv F v ⊗[F] E) : Algebra.norm (Fv F v) z = D.p 0 z * D.p 1 z := by
  rw [Algebra.norm_eq_matrix_det (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1) z, Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    PI.LocDualGen.EpS.bas0, PI.LocDualGen.EpS.bas1]
  have h0 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h1 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h2 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  have h3 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  rw [h0, h1, h2, h3]
  simp only [(PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).1,
    (PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).2]
  have pe := D.p_e
  have pf := D.p_f
  simp only [p, PI.LocDualGen.EpS.pr_apply] at pe pf
  rw [pe.1, pe.2, pf.1, pf.2]
  simp only [p, PI.LocDualGen.EpS.pr_apply]
  ring
end PI.UnitaryGroupMassFormula.LocJacTyp.SD
