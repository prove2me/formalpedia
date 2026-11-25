-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_charZero_5d26261f436b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:13.545184+00:00
-- url     : https://prove2.me/submissions/a79f8ed1-5b69-4a38-8aca-c772145332e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.FibreCurve
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.FibreCurve
theorem _root_.solution [CharZero Ω] (u : Ω) : CharZero (gen u).Φ' := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (C (n : ℤ) : MRing B2) ∈ mCoordIdeal (pt u) := by
    rw [← (gen u).genericFibre_ker_target, RingHom.mem_ker]
    simpa using hn
  simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
  simpa using hmem
end GroundTheory.Heights₂.Heights.Targets.FibreCurve
