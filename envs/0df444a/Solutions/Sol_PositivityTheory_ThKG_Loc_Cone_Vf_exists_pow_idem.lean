-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.exists_pow_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:49.704555+00:00
-- url     : https://prove2.me/submissions/5b34ccad-b7b6-4071-bfa3-8278eb925866

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}
namespace PositivityTheory.ThKG.Loc.Cone.Vf
theorem _root_.solution {M : Type} [Monoid M] [Finite M] (x : M) : ∃ N, 0 < N ∧ x ^ N * x ^ N = x ^ N := by
  obtain ⟨a, b, hab, e⟩ : ∃ a b : ℕ, a < b ∧ x ^ a = x ^ b := by
    obtain ⟨a, b, hne, e⟩ := Finite.exists_ne_map_eq_of_infinite fun i : ℕ => x ^ i
    rcases lt_or_gt_of_ne hne with h | h
    exacts [⟨a, b, h, e⟩, ⟨b, a, h, e.symm⟩]
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have h1 : ∀ j, x ^ (a + j * (p + 1)) = x ^ a := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show a + (j + 1) * (p + 1) = (a + p + 1) + j * (p + 1) by ring, pow_add, ← e, ← pow_add, ih]
  refine ⟨(a + 1) * (p + 1), by positivity, ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, (a + 1) * (p + 1) = a + r := Nat.exists_eq_add_of_le (by nlinarith)
  rw [← pow_add, show (a + 1) * (p + 1) + (a + 1) * (p + 1) = (a + (a + 1) * (p + 1)) + r by omega, pow_add, h1, ← pow_add, hr]
end PositivityTheory.ThKG.Loc.Cone.Vf
