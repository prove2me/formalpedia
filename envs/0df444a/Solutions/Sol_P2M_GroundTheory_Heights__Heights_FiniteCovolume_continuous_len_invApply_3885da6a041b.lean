-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_invApply_3885da6a041b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:19.692603+00:00
-- url     : https://prove2.me/submissions/0cb6ea0e-72b9-4353-b0ff-3a200da81694

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArithmeticCovolumeFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (invApply g y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => invApply g y w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_)
  exact (hw w).star.dotProduct (continuous_const.matrix_mulVec (hw w))
end GroundTheory.Heights₂.Heights.FiniteCovolume
