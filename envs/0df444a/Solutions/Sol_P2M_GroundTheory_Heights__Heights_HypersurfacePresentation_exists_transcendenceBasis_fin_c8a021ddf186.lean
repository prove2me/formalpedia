-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_transcendenceBasis_fin_c8a021ddf186
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:51.514413+00:00
-- url     : https://prove2.me/submissions/41154b43-29d2-4f81-bf9f-c09e422445d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
namespace GroundTheory.Heights₂.Heights.HypersurfacePresentation
theorem _root_.solution {S A : Type} [CommRing S] [CommRing A] [IsDomain A] [Algebra S A]
    [FaithfulSMul S A] {ι : Type} [Finite ι] (x : ι → A) (hx : Algebra.adjoin S (Set.range x) = ⊤) :
    ∃ (d : ℕ) (y : Fin d → A), IsTranscendenceBasis S y := by
  have : Algebra.IsAlgebraic (Algebra.adjoin S (Set.range x)) A := ⟨fun a => by
    have ha : a ∈ Algebra.adjoin S (Set.range x) := hx ▸ Algebra.mem_top
    exact isAlgebraic_algebraMap (R := Algebra.adjoin S (Set.range x)) (A := A) ⟨a, ha⟩⟩
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := S) (Set.range x)
  have : Finite t := ((Set.finite_range x).subset ht).to_subtype
  exact ⟨_, _, hb.comp_equiv (Finite.equivFin t).symm⟩
end GroundTheory.Heights₂.Heights.HypersurfacePresentation
