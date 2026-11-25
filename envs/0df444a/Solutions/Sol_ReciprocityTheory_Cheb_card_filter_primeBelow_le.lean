-- Prove2me | solution 1 for ReciprocityTheory.Cheb.card_filter_primeBelow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:08.754184+00:00
-- url     : https://prove2.me/submissions/321b7815-de84-4ce2-a99b-58477c13b7e8

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Theorems.Thm_ReciprocityTheory_Cheb_mem_primesOverFinset_primeBelow
import Theorems.Thm_ReciprocityTheory_Cheb_card_primesOverFinset_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (u : Finset (Prm E)) (p : ℕ) (hp : p.Prime) :
    (u.filter fun x => primeBelow x = p).card ≤ Module.finrank ℚ E := by
  classical
  refine le_trans ?_ (card_primesOverFinset_le (E := E) p hp)
  refine Finset.card_le_card_of_injOn (fun x => x.asIdeal) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter] at hx
    have := mem_primesOverFinset_primeBelow x
    rw [hx.2] at this
    exact this
  · intro x _ y _ hxy
    exact HeightOneSpectrum.ext hxy
end ReciprocityTheory.Cheb
