-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_not_dvd_prod_erase_35fbca75cdeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:50.2874+00:00
-- url     : https://prove2.me/submissions/355eff44-08fe-4658-b808-a290ec31c7c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles

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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (S : Finset Nat.Primes) (p : Nat.Primes) :
    ¬ (p : ℕ) ∣ ∏ q ∈ S.erase p, (q : ℕ) := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff p.2.prime _).1 h
  have : p = q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).1 hpq)
  subst this
  exact Finset.notMem_erase _ _ hq
end GroundTheory.Heights₂.Heights.Model
