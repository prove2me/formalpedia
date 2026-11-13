-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.one_le_norm_eta_grid_signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:27:24.1922+00:00
-- url     : https://prove2.me/submissions/85452de8-3b4b-4ab4-8535-7b0ffac225aa

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Parity core of Peterfalvi (3.9)/(14.11.3)**: a `±1`-signed sum of an integer-valued grid
that pairs under a conjugation involution has complex norm `≥ 1`.

Concretely, let `n : ι → ℤ` be constant on the orbits of an involution `ρ` whose *unique* fixed
point `i₀` carries the principal value `n i₀ = 1`, and let `ε : ι → ℤ` take values in `{±1}`.  Then
the signed sum `∑ ε_i n_i` is an **odd** integer — the `ρ`-paired off-principal terms contribute an
even total (`n` is `ρ`-invariant, so each pair sums to `2 n_i`), while the fixed point contributes
`±1` — so its image in `ℂ` has norm `≥ 1`.

This is the arithmetic heart of (14.11.3): on a generic element `g`, the η-grid values `η_ij(g)`
are rational integers (3.9.c) that pair under the conjugation `(i,j) ↦ (−i,−j)` with the single
principal value `η₀₀(g) = 1` (3.9.a); combined with the (14.11.2) expansion
`ψ^{τ₁}(g) = ±∑ ε_ij η_ij(g)` (valid on `G_0`, where `β_M^τ(g) = 0`) this forces
`|ψ^{τ₁}(g)| ≥ 1`.  Stated generically over a `Fintype` so it serves both the (14.11.3) bound and
the dual (14.16) parity contradiction. -/
theorem one_le_norm_signed_paired_sum {ι : Type*} [Fintype ι]
    (n ε : ι → ℤ) (ρ : Equiv.Perm ι) (i₀ : ι)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hρ : Function.Involutive ρ)
    (hfix : ∀ i, ρ i = i ↔ i = i₀)
    (hpair : ∀ i, n (ρ i) = n i)
    (hn0 : n i₀ = 1) :
    1 ≤ ‖(∑ i, (ε i : ℂ) * (n i : ℂ))‖ := by
  classical
  have hcast : (∑ i, (ε i : ℂ) * (n i : ℂ)) = ((∑ i, ε i * n i : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_intCast]
  -- Off-principal terms sum to an even integer (fixed-point-free involution on `univ ∖ {i₀}`).
  have heven_erase : (2 : ℤ) ∣ ∑ i ∈ Finset.univ.erase i₀, n i := by
    have hz : ((∑ i ∈ Finset.univ.erase i₀, n i : ℤ) : ZMod 2) = 0 := by
      push_cast
      refine Finset.sum_involution (fun a _ => ρ a) ?_ ?_ ?_ ?_
      · intro a _
        rw [hpair a]; exact CharTwo.add_self_eq_zero _
      · intro a ha _ hcontra
        exact (Finset.mem_erase.mp ha).1 ((hfix a).mp hcontra)
      · intro a ha
        rw [Finset.mem_erase] at ha ⊢
        refine ⟨fun hcontra => ha.1 ?_, Finset.mem_univ _⟩
        change ρ a = i₀ at hcontra
        calc a = ρ (ρ a) := (hρ a).symm
          _ = ρ i₀ := by rw [hcontra]
          _ = i₀ := (hfix i₀).mpr rfl
      · intro a _; exact hρ a
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  -- Each sign satisfies `ε_i ≡ 1 (mod 2)`, so `∑ ε_i n_i ≡ ∑ n_i (mod 2)`.
  have hdiff : (2 : ℤ) ∣ (∑ i, ε i * n i) - (∑ i, n i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum (fun i _ => ?_)
    have hrw : ε i * n i - n i = (ε i - 1) * n i := by ring
    rw [hrw]
    exact Dvd.dvd.mul_right (by rcases hε i with h | h <;> rw [h] <;> norm_num) (n i)
  have hsum_n : ∑ i, n i = (∑ i ∈ Finset.univ.erase i₀, n i) + n i₀ :=
    (Finset.sum_erase_add Finset.univ n (Finset.mem_univ i₀)).symm
  have hodd_n : Odd (∑ i, n i) := by
    rw [hsum_n, hn0]
    rcases heven_erase with ⟨c, hc⟩
    exact ⟨c, by rw [hc]⟩
  have hodd : Odd (∑ i, ε i * n i) := by
    rcases hdiff with ⟨d, hd⟩
    rcases hodd_n with ⟨m, hm⟩
    refine ⟨d + m, ?_⟩
    have hA : ∑ i, ε i * n i = (∑ i, n i) + 2 * d := by omega
    rw [hA, hm]; ring
  rcases hodd with ⟨m, hm⟩
  rw [hm, ← Int.cast_abs]
  have hh : (1 : ℤ) ≤ |2 * m + 1| := by
    rcases abs_cases (2 * m + 1 : ℤ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
  exact_mod_cast hh

theorem finNeg_involutive {n : ℕ} (hn : 0 < n) : Function.Involutive (finNeg hn) := by
  intro i
  apply Fin.ext
  rw [finNeg_val, finNeg_val]
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · have hlt : i.val < n := i.isLt
    have h1 : (n - i.val) % n = n - i.val := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : n - (n - i.val) = i.val := by omega
    rw [h2, Nat.mod_eq_of_lt hlt]

theorem finNeg_eq_self_iff {n : ℕ} (hn : 0 < n) (hodd : Odd n) (i : Fin n) :
    finNeg hn i = i ↔ i = ⟨0, hn⟩ := by
  rw [Fin.ext_iff, Fin.ext_iff, finNeg_val]
  change (n - i.val) % n = i.val ↔ i.val = 0
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · exact h0
    · have hlt : i.val < n := i.isLt
      have h1 : (n - i.val) % n = n - i.val := Nat.mod_eq_of_lt (by omega)
      rw [h1] at h
      rcases hodd with ⟨k, hk⟩
      omega
  · intro h
    rw [h, Nat.sub_zero, Nat.mod_self]

/-- **Arithmetic core of Peterfalvi (14.11.3), specialised to the `η`-grid.**  An integer-valued
`q × p` grid `n` that pairs under the conjugation `(i,j) ↦ (−i,−j)` (`finNeg`) with principal value
`n₀₀ = 1`, summed against a `±1`-sign grid `ε`, has complex norm `≥ 1`.

This packages the conjugation involution `(i,j) ↦ (−i,−j)` on `Fin q × Fin p` (whose unique fixed
point is `(0,0)`, since `q`, `p` are odd) and feeds it to `one_le_norm_signed_paired_sum`.  It is
the
exact arithmetic consumed by `generic_character_bound` (14.11.3) and the dual (14.16) parity
contradiction once the `(3.9)` integrality/pairing facts of the `η`-grid are supplied. -/
theorem _root_.solution {q p : ℕ} (hq : 0 < q) (hp : 0 < p)
    (hqodd : Odd q) (hpodd : Odd p) (n ε : Fin q → Fin p → ℤ)
    (hε : ∀ i j, ε i j = 1 ∨ ε i j = -1)
    (hpair : ∀ i j, n (finNeg hq i) (finNeg hp j) = n i j)
    (h00 : n ⟨0, hq⟩ ⟨0, hp⟩ = 1) :
    1 ≤ ‖(∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (n i j : ℂ))‖ := by
  classical
  have hinv : Function.Involutive
      (fun x : Fin q × Fin p => (finNeg hq x.1, finNeg hp x.2)) := by
    intro x
    change (finNeg hq (finNeg hq x.1), finNeg hp (finNeg hp x.2)) = x
    rw [finNeg_involutive hq x.1, finNeg_involutive hp x.2]
  have key := one_le_norm_signed_paired_sum
    (fun x : Fin q × Fin p => n x.1 x.2) (fun x => ε x.1 x.2)
    hinv.toPerm (⟨0, hq⟩, ⟨0, hp⟩) (fun x => hε x.1 x.2)
    (by rw [Function.Involutive.coe_toPerm]; exact hinv)
    (by
      intro x
      rw [Function.Involutive.coe_toPerm]
      constructor
      · intro h
        have h1 : finNeg hq x.1 = x.1 := (Prod.ext_iff.mp h).1
        have h2 : finNeg hp x.2 = x.2 := (Prod.ext_iff.mp h).2
        exact Prod.ext ((finNeg_eq_self_iff hq hqodd x.1).mp h1)
          ((finNeg_eq_self_iff hp hpodd x.2).mp h2)
      · intro h
        rw [h]
        exact Prod.ext ((finNeg_eq_self_iff hq hqodd _).mpr rfl)
          ((finNeg_eq_self_iff hp hpodd _).mpr rfl))
    (by intro x; rw [Function.Involutive.coe_toPerm]; exact hpair x.1 x.2)
    h00
  have hsum : (∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (n i j : ℂ))
      = ∑ x : Fin q × Fin p, (ε x.1 x.2 : ℂ) * (n x.1 x.2 : ℂ) := by
    rw [Fintype.sum_prod_type]
  rw [hsum]
  exact key

end OddOrder.Peterfalvi.S16
