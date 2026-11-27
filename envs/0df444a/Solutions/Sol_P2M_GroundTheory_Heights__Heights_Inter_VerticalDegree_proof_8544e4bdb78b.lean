-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_VerticalDegree_proof_8544e4bdb78b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:01:36.622164+00:00
-- url     : https://prove2.me/submissions/710eef75-c644-45c6-bfc2-6eb5f6f13bde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImageVarIdBotTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsRest

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
namespace GroundTheory.Heights₂.Heights.Inter
namespace VerticalDegree
theorem _root_.solution (h₁ : FibreDimensionZero.Statement) (h₂ : ChartRankAdjoin.Statement)
    (h₃ : VerticalDegreeAfterAdjoining.Statement) : VerticalDegree.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n i' hv hp hW hV hch G' J' hJ
  have hfib := h₁ K ι K' ι' κ v p W' n hv hp hW hV G'
  have hz : ∀ k : FibreBlock κ, G'.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hch k.1
    have hX : (X ⟨k.1, i' k.1⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h0
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  have hj : IsChart (fibreIdeal κ G') (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  rw [hJ.1 _ Fin.elim0 _ hfib hj, h₃ K ι K' ι' κ v p W' n i' hv hp hW hV hch G']
  congr 1
  exact (h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ' (fun q => G'.x' ⟨q.1.1, q.2⟩) (fun k => i' k.1) hz
    hfib.1.2.1).symm
end VerticalDegree
end GroundTheory.Heights₂.Heights.Inter
