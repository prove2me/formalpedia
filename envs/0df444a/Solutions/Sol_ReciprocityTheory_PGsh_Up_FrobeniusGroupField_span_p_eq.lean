-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.span_p_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:19.375805+00:00
-- url     : https://prove2.me/submissions/d6e5bba4-c4a0-4307-9b46-baa0186430d7

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (S : Type) [CommRing S] [Algebra ℤ_[p] S] :
    (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S) = Ideal.span {(p : S)} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
