-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_card_eq_pow_of_length_eq_89617ad0f5d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:33:50.513888+00:00
-- url     : https://prove2.me/submissions/0a8e9c84-57cd-42f7-9c8d-18f99efab223

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_of_isSimpleModule_83467b0fb3cd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open IsLocalRing
universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (n : ℕ) : ∀ (M : Type v) [AddCommGroup M] [Module R M],
    Module.length R M = n → Nat.card M = Nat.card (ResidueField R) ^ n := by
  induction n with
  | zero =>
    intro M _ _ h
    have : Subsingleton M := Module.length_eq_zero_iff.mp (by exact_mod_cast h)
    rw [pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨0⟩⟩
  | succ n ih =>
    intro M _ _ h
    have hfin : IsFiniteLength R M := Module.length_ne_top_iff.mp (by rw [h]; exact ENat.natCast_ne_top _)
    obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
    have hnt : Nontrivial M := Module.length_pos_iff.mp (by rw [h]; exact_mod_cast Nat.succ_pos n)
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
    have hs : IsSimpleModule R N := (isSimpleModule_iff_isAtom).mpr hN
    have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    rw [h, Module.length_eq_one] at hlen
    have hq : Module.length R (M ⧸ N) = n := by
      have hne : Module.length R (M ⧸ N) ≠ ⊤ := by
        intro ht
        rw [ht] at hlen
        exact ENat.natCast_ne_top _ (hlen.trans (add_top _))
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hm] at hlen ⊢
      have : n + 1 = 1 + m := by exact_mod_cast hlen
      congr 1
      omega
    rw [Submodule.card_eq_card_quotient_mul_card N, card_eq_card_residueField_of_isSimpleModule (R := R) N, ih (M ⧸ N) hq,
      pow_succ, mul_comm]
end GroundTheory.Heights₂.Heights.Inter
