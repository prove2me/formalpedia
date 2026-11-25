-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_ker_aeval_F_7dc16d4c0989
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:42.761731+00:00
-- url     : https://prove2.me/submissions/915f5372-835a-4cc4-8dd7-85734c60515e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AevalMemAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_red_da59eedff835
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_mem_map_red_iff_50299f2085c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_red_surjective_25202236fa05


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.FibreTranscendence
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.Inter.FibreTranscendence
theorem _root_.solution {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] (y : (Σ k, ι k) → L)
    {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) :
    RingHom.ker (aeval y : MRingOver (ZMod p) ι →ₐ[ZMod p] L) = J.map (PointVertical.red (ι := ι) p) := by
  ext f
  obtain ⟨g, rfl⟩ := PointVertical.red_surjective (ι := ι) p f
  rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, ← hJ, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = 0) (aeval_red p y g))
end GroundTheory.Heights₂.Heights.Inter.FibreTranscendence
