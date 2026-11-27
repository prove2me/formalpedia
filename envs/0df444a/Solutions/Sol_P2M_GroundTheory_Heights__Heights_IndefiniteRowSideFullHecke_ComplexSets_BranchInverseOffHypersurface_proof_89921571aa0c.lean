-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BranchInverseOffHypersurface_proof_89921571aa0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:39.928038+00:00
-- url     : https://prove2.me/submissions/3729fe55-bf18-4a44-a6d2-b2e66174cdb7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionInjectiveOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchInverseOffHypersurface

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace BranchInverseOffHypersurface
theorem _root_.solution (hinv : InjectiveHolomorphicInverse.Statement)
    (hproj : ProjectionInjectiveOffHypersurface.Statement) :
    BranchInverseOffHypersurface.Statement := by
  intro σ _ I k hI hk
  obtain ⟨h', hh', hloc⟩ := hproj σ I k hI hk
  refine ⟨h', hh', fun U φ ψ hU hφd hφi hφZ hψ => ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
  obtain ⟨W, hWo, hzW, A, hA⟩ := hloc (φ t) (hφZ ht) hz
  have hU'o : IsOpen (U ∩ φ ⁻¹' W) := hφd.continuousOn.isOpen_inter_preimage hU hWo
  have hfd : DifferentiableOn ℂ (fun s => A (φ s)) (U ∩ φ ⁻¹' W) :=
    A.differentiable.differentiableOn.comp (hφd.mono Set.inter_subset_left) (Set.mapsTo_univ _ _)
  have hfi : Set.InjOn (fun s => A (φ s)) (U ∩ φ ⁻¹' W) := fun s hs s' hs' hss' =>
    hφi hs.1 hs'.1 (hA ⟨hφZ hs.1, hs.2⟩ ⟨hφZ hs'.1, hs'.2⟩ hss')
  obtain ⟨hOo, g, hgd, hgf⟩ := hinv k _ _ hU'o hfd hfi
  refine ⟨W ∩ A ⁻¹' ((fun s => A (φ s)) '' (U ∩ φ ⁻¹' W)), hWo.inter (hOo.preimage A.continuous),
    ⟨hzW, t, ⟨ht, hzW⟩, rfl⟩, fun y => g (A y), ?_, ?_⟩
  · exact hgd.comp A.differentiable.differentiableOn fun y hy => hy.2
  · rintro _ ⟨⟨⟨s, hs, rfl⟩, -⟩, hsW, -⟩
    show ψ (φ s) = g (A (φ s))
    rw [hψ s hs, hgf s ⟨hs, hsW⟩]
end BranchInverseOffHypersurface
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
