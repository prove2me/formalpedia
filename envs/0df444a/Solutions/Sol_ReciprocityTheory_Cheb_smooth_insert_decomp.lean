-- Prove2me | solution 1 for ReciprocityTheory.Cheb.smooth_insert_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:33.450276+00:00
-- url     : https://prove2.me/submissions/61796ff8-787b-456b-b8b8-809c9d3adbf8

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} (q : Prm E)
    {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) (hs : Smooth (insert q S) a) :
    ∃ (k : ℕ) (b : Ideal (𝓞 E)), b ≠ ⊥ ∧ Smooth S b ∧ a = q.asIdeal ^ k * b := by
  obtain ⟨k, b, hqb, hab⟩ := WfDvdMonoid.max_power_factor (a₀ := a) ha q.irreducible
  refine ⟨k, b, ?_, ?_, hab⟩
  · rintro rfl
    exact ha (by rw [hab, Ideal.mul_bot])
  · intro p hp
    have hpa : p.asIdeal ∣ a := hab ▸ dvd_mul_of_dvd_right hp _
    rcases Finset.mem_insert.1 (hs p hpa) with h | h
    · exact absurd (h ▸ hp) hqb
    · exact h
end ReciprocityTheory.Cheb
