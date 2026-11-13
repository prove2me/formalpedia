-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.G0Finset_cyclicClosed
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:54:30.391504+00:00
-- url     : https://prove2.me/submissions/c5deb5cf-e2cc-4cee-924f-513676840d69

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- Membership in the generic set `G₀`, unfolded: nonidentity and in neither saturation. -/
theorem Hypothesis.mem_G0_iff (hyp : Hypothesis (G := G)) (x : G) :
    x ∈ hyp.G0 ↔ x ≠ 1 ∧ x ∉ conjClassSet (sharpSubgroup hyp.H)
      ∧ x ∉ conjClassSet (sharpSubgroup hyp.Q) := by
  change x ∈ sharpSubgroup (⊤ : Subgroup G) \ _ ↔ _
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_union, not_or]

/-- **`G₀` is cyclic-closed**: closed under `x ↦ x^k` for `k` coprime to `|G|` — the hypothesis
shape of the Galois integrality `exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed` (and of
[Is] Lemma 3.14) that makes the (13.10) atoms `slam`/`seta` rational.  The coprime power is
undone by a further coprime power (Euler), so `x^k = 1` forces `x = 1`, and a conjugate of
`H^#`/`Q^#` hitting `x^k` pulls back to one hitting `x` (subgroups are power-closed). -/
theorem _root_.solution [Finite G] (hyp : Hypothesis (G := G)) :
    ∀ x ∈ hyp.G0Finset, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ hyp.G0Finset := by
  intro x hx k hk
  rw [Hypothesis.G0Finset, Set.Finite.mem_toFinset] at hx ⊢
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hx
  -- Euler round-trip: `(x^k)^(k^(φ(|G|)−1)) = x`.
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  set t := (Nat.card G).totient with htdef
  have ht1 : 1 ≤ t := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  set m : ℕ := k ^ (t - 1) with hmdef
  have hround : (x ^ k) ^ m = x := by
    rw [hmdef, ← pow_mul]
    have hkt : k * k ^ (t - 1) = k ^ t := by rw [← pow_succ']; congr 1; omega
    rw [hkt]
    have hord : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
    have hmod : k ^ t ≡ 1 [MOD orderOf x] := (Nat.ModEq.pow_totient hk).of_dvd hord
    rw [pow_eq_pow_iff_modEq.mpr hmod, pow_one]
  -- Conjugates of `K^#` hitting `x^k` pull back to `x`.
  have hpull : ∀ K : Subgroup G, x ^ k ∈ conjClassSet (sharpSubgroup K) →
      x ∈ conjClassSet (sharpSubgroup K) := by
    intro K hmem
    obtain ⟨a, ⟨haK, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hmem
    refine mem_conjClassSet.mpr ⟨a ^ m, ⟨?_, ?_⟩, g, ?_⟩
    · exact SetLike.mem_coe.mpr (pow_mem (SetLike.mem_coe.mp haK) m)
    · intro h1
      rw [Set.mem_singleton_iff] at h1
      refine hx1 ?_
      rw [← hround, ← hg, conj_pow, h1, mul_one, mul_inv_cancel]
    · rw [← conj_pow, hg, hround]
  refine (hyp.mem_G0_iff _).mpr ⟨?_, fun h => hxH (hpull _ h), fun h => hxQ (hpull _ h)⟩
  intro h1
  refine hx1 ?_
  rw [← hround, h1, one_pow]

end CountingLayer

end OddOrder.Peterfalvi.S15
