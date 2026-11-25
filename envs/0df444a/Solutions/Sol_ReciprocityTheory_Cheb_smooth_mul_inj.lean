-- Prove2me | solution 1 for ReciprocityTheory.Cheb.smooth_mul_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:38.157262+00:00
-- url     : https://prove2.me/submissions/dc37742b-21d1-47c7-8d9e-95fd8c337d16

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] {S : Finset (Prm E)} {q : Prm E} (hq : q ∉ S)
    {b b' : Ideal (𝓞 E)} (hb : Smooth S b) (hb' : Smooth S b') {k k' : ℕ}
    (h : q.asIdeal ^ k * b = q.asIdeal ^ k' * b') : k = k' ∧ b = b' := by
  have hq0 : q.asIdeal ≠ 0 := q.ne_bot
  have key : ∀ {c c' : Ideal (𝓞 E)} {m m' : ℕ}, Smooth S c → m < m' →
      q.asIdeal ^ m * c ≠ q.asIdeal ^ m' * c' := by
    intro c c' m m' hc hlt he
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [show q.asIdeal ^ (m + n + 1) * c' = q.asIdeal ^ m * (q.asIdeal ^ (n + 1) * c') by
      rw [← mul_assoc, ← pow_add, add_assoc]] at he
    have hc' := mul_left_cancel₀ (pow_ne_zero m hq0) he
    exact hq (hc q (hc' ▸ dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero n)) _))
  rcases lt_trichotomy k k' with hlt | rfl | hlt
  · exact absurd h (key hb hlt)
  · exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k hq0) h⟩
  · exact absurd h.symm (key hb' hlt)
end ReciprocityTheory.Cheb
