-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_repr_sum_de623f64b805
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:53.611004+00:00
-- url     : https://prove2.me/submissions/5fdf62f4-864c-4dbd-a223-18405906ed88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
variable {K : Type} [Field K] [NumberField K]
open Classical
namespace GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
theorem _root_.solution (τ σ : K →+* ℂ) :
    ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single τ 1) m * σ (integralBasis K m) =
      if σ = τ then 1 else 0 := by
  have h := congrFun ((canonicalEmbedding.latticeBasis K).sum_repr (Pi.single τ 1)) σ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, canonicalEmbedding.latticeBasis_apply,
    canonicalEmbedding.apply_at, Pi.single_apply] at h
  exact h
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
