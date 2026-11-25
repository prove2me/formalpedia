-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_derivation_mem_of_mem_sq_cb7946785f2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:58.644253+00:00
-- url     : https://prove2.me/submissions/899d6ebe-07ed-4c74-bdb9-9abc22f9b407

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationCotangentIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDerivationCotangentIndependent

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
open IsLocalRing Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {T : Type} [CommRing T] (P : Ideal T) (D : Derivation ℤ T T)
    {x : T} (hx : x ∈ P ^ 2) : D x ∈ P := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)
  · rw [map_add]; exact P.add_mem ha hb
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
