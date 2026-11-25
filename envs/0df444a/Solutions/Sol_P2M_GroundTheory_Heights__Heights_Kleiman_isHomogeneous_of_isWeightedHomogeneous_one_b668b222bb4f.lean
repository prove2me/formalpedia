-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isHomogeneous_of_isWeightedHomogeneous_one_b668b222bb4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:48.609118+00:00
-- url     : https://prove2.me/submissions/c853299a-4db7-4441-91ed-ae6cf50edfe5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded

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
open MvPolynomial DirectSum
noncomputable section
universe u
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {f : Poly S N} {n : ℕ}
    (hf : IsWeightedHomogeneous (fun _ => (1 : ℤ)) f (n : ℤ)) : f.IsHomogeneous n := by
  intro d hd
  have h1 := hf hd
  rw [weight_one_int] at h1
  have h2 : Finsupp.weight (1 : Fin (N + 1) → ℕ) d = d.degree := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [h2]
  exact_mod_cast h1
end GroundTheory.Heights₂.Heights.Kleiman
