-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sqZeroFrobeniusLift_mk_9f7e8c1b72b5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:41.284382+00:00
-- url     : https://prove2.me/submissions/461868fe-41b5-48b8-a340-f9a6e321b974

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift

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
variable {C : Type*} [CommRing C] {N : Ideal C} {p : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) (c : C) :
    sqZeroFrobeniusLift N hp hpC hN (Ideal.Quotient.mk N c) = c ^ p :=
  pow_prime_eq_of_mk_eq hp hpC hN (Ideal.Quotient.mk_surjective _).choose_spec
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
