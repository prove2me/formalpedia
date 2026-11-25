-- Prove2me | solution 1 for ReciprocityTheory.Cheb.smooth_insert_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:03.413921+00:00
-- url     : https://prove2.me/submissions/8a41c64b-bae0-4b57-af7b-d50cb49d523f

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
import Theorems.Thm_ReciprocityTheory_Cheb_prm_eq_of_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} {b : Ideal (𝓞 E)}
    (q : Prm E) (k : ℕ) (hb : Smooth S b) : Smooth (insert q S) (q.asIdeal ^ k * b) := by
  intro p hp
  rcases p.prime.dvd_or_dvd hp with h | h
  · exact Finset.mem_insert.2 (Or.inl (prm_eq_of_dvd (p.prime.dvd_of_dvd_pow h)))
  · exact Finset.mem_insert_of_mem (hb p h)
end ReciprocityTheory.Cheb
