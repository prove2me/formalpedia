-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_AdjoinTrdegAdd_trdeg_adjoin_eq_of_family_7abcbe3c35c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:09.859378+00:00
-- url     : https://prove2.me/submissions/06daf73a-455c-44d8-ae03-61a946f84274

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open Algebra Cardinal Set
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace AdjoinTrdegAdd
theorem _root_.solution {R L κ : Type} [CommRing R] [CommRing L] [IsDomain L]
    [Algebra R L] (u : Set L) (w : κ → L) (hwu : range w ⊆ u) (hw : AlgebraicIndependent R w)
    (halg : ∀ a ∈ u, IsAlgebraic (adjoin R (range w)) a) :
    trdeg R (adjoin R u) = #κ := by
  have := (algebraMap R L).domain_nontrivial
  let v : κ → adjoin R u := fun i => ⟨w i, subset_adjoin (hwu ⟨i, rfl⟩)⟩
  have hv : AlgebraicIndependent R v := AlgebraicIndependent.of_comp (adjoin R u).val hw
  have heq : (adjoin R (range v)).map (adjoin R u).val = adjoin R (range w) := by
    rw [AlgHom.map_adjoin, ← range_comp]
    rfl
  let e := ((adjoin R (range v)).equivMapOfInjective (adjoin R u).val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ heq)
  have hval : Algebra.IsAlgebraic (adjoin R (range v)) (adjoin R u) := by
    refine ⟨fun a => ?_⟩
    have h0 : IsAlgebraic (adjoin R u) (a : L) := isAlgebraic_algebraMap a
    have h1 : IsAlgebraic (adjoin R (range w)) ((adjoin R u).val a) :=
      h0.adjoin_of_forall_isAlgebraic fun y hy => halg y hy.1
    exact (isAlgebraic_ringHom_iff_of_comp_eq e (adjoin R u).val Subtype.val_injective
      (by ext; rfl)).mp h1
  exact ((isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hv, hval⟩).cardinalMk_eq_trdeg).symm
end AdjoinTrdegAdd
end GroundTheory.Heights₂.Heights.NumbersDVR
