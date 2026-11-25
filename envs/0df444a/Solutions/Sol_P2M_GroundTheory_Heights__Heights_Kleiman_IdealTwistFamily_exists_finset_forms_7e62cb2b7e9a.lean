-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_finset_forms_7e62cb2b7e9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:22:03.327364+00:00
-- url     : https://prove2.me/submissions/c1761e51-5fe5-4328-b03e-73482a742893

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_isHomogeneous_totalDegree_ce023b502360

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {R : Type u} [CommRing R] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
theorem _root_.solution [IsNoetherianRing R] (J : Ideal (Poly R N))
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) :
    ∃ H : Finset (Poly R N), (↑H : Set (Poly R N)) ⊆ J ∧ Ideal.span (↑H : Set (Poly R N)) = J ∧
      ∀ g ∈ (↑H : Set (Poly R N)), g.IsHomogeneous g.totalDegree := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian J : J.FG)
  have hsub : (↑(G.biUnion fun g => (Finset.range (g.totalDegree + 1)).image
      fun i => homogeneousComponent i g) : Set (Poly R N)) ⊆ J := by
    intro h hh
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe] at hh
    obtain ⟨g, hg, i, -, rfl⟩ := hh
    exact hJ g (hG ▸ Ideal.subset_span hg) i
  refine ⟨G.biUnion fun g => (Finset.range (g.totalDegree + 1)).image
      fun i => homogeneousComponent i g, hsub, le_antisymm (Ideal.span_le.mpr hsub) ?_, ?_⟩
  · rw [← hG]
    refine Submodule.span_le.mpr fun g hg => ?_
    have hsum := sum_homogeneousComponent g
    rw [SetLike.mem_coe, ← hsum]
    refine Ideal.sum_mem _ fun i hi => Ideal.subset_span ?_
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
    exact ⟨g, hg, i, hi, rfl⟩
  · intro h hh
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe] at hh
    obtain ⟨g, -, i, -, rfl⟩ := hh
    exact isHomogeneous_totalDegree (homogeneousComponent_isHomogeneous i g)
end GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
