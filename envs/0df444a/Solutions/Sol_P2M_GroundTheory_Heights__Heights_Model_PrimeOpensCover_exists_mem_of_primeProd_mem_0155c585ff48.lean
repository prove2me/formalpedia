-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_exists_mem_of_primeProd_mem_0155c585ff48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:09.251789+00:00
-- url     : https://prove2.me/submissions/814539eb-57ef-4c13-bff4-10861de2308b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPrimeOpensCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open AlgebraicGeometry TopologicalSpace
open GroundTheory.Heights₂.Heights.Model.PrimeOpensCover
namespace GroundTheory.Heights₂.Heights.Model.PrimeOpensCover
theorem _root_.solution {P : Ideal ℤ} [P.IsPrime] {S : Finset Nat.Primes}
    (h : primeProd S ∈ P) : ∃ r ∈ S, ((r : ℕ) : ℤ) ∈ P :=
  Ideal.IsPrime.prod_mem_iff.mp h
end GroundTheory.Heights₂.Heights.Model.PrimeOpensCover
