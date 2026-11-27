-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicIsolatedFibreOpen_proof_07ba1654a2d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:02.49746+00:00
-- url     : https://prove2.me/submissions/3b8abde0-53da-42ee-9bb2-babc4ffdeb26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperHolomorphicSurjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicIsolatedFibreOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace HolomorphicIsolatedFibreOpen
theorem _root_.solution (hPS : ProperHolomorphicSurjective.Statement) :
    HolomorphicIsolatedFibreOpen.Statement := by
  intro k U g u hU hu hg ⟨W, hW, hiso⟩ V hV
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall u r ⊆ U ∩ W ∩ V :=
    nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hu) hW) hV)
  have hgc : ContinuousOn g (closedBall u r) := hg.continuousOn.mono fun x hx => (hrsub hx).1.1

  have hSc : IsCompact (g '' sphere u r) :=
    (isCompact_sphere u r).image_of_continuousOn (hgc.mono sphere_subset_closedBall)
  have hnot : g u ∉ g '' sphere u r := by
    rintro ⟨s, hs, hgs⟩
    have hsK := hrsub (sphere_subset_closedBall hs)
    have := hiso s hsK.1.2 hsK.1.1 hgs
    subst this
    rw [mem_sphere, dist_self] at hs
    exact hr.ne' hs.symm
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hSc.isClosed.isOpen_compl (g u) hnot

  have key : ∀ v ∈ closedBall u r, g v ∈ ball (g u) ε → v ∈ ball u r := by
    intro v hv hgv
    rcases (mem_closedBall.1 hv).lt_or_eq with h | h
    · exact h
    · exact (hεsub hgv ⟨v, mem_sphere.2 h, rfl⟩).elim
  have hΩ : IsOpen (ball u r ∩ g ⁻¹' ball (g u) ε) :=
    (hgc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hproper : ∀ L ⊆ ball (g u) ε, IsCompact L →
      IsCompact ((ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L) := by
    intro L hLD hL
    have heq : (ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L = closedBall u r ∩ g ⁻¹' L := by
      ext v
      constructor
      · rintro ⟨⟨hv, _⟩, hvL⟩
        exact ⟨ball_subset_closedBall hv, hvL⟩
      · rintro ⟨hv, hvL⟩
        exact ⟨⟨key v hv (hLD hvL), hLD hvL⟩, hvL⟩
    rw [heq]
    exact (isCompact_closedBall u r).of_isClosed_subset
      (hgc.preimage_isClosed_of_isClosed isClosed_closedBall hL.isClosed) Set.inter_subset_left
  have hsurj := hPS k _ _ g hΩ ⟨u, mem_ball_self hr, mem_ball_self hε⟩ isOpen_ball
    (convex_ball _ _).isPreconnected (hg.mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).1.1)
    (fun x hx => hx.2) hproper
  refine Filter.mem_of_superset (ball_mem_nhds _ hε) ?_
  rw [← hsurj]
  exact Set.image_mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).2
end HolomorphicIsolatedFibreOpen
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
