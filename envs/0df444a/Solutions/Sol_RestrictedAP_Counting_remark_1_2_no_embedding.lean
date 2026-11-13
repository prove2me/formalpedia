-- Prove2me | solution 1 for RestrictedAP.Counting.remark_1_2_no_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:02:50.67958+00:00
-- url     : https://prove2.me/submissions/05efab80-c681-424c-b42d-7f684241625b

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_MuP

section
namespace RestrictedAP.Counting.Dev.R12

theorem mem_supp (p : ℕ) [NeZero p] (x : ZMod p) (a : Fin 3) :
    (x, x + ((a : ℕ) : ZMod p), x + 2 * ((a : ℕ) : ZMod p)) ∈ supp (muP p) := by
  unfold supp muP
  simp only [Set.mem_setOf_eq, ne_eq, div_eq_zero_iff, not_or]
  refine ⟨?_, ?_⟩
  · have : 0 < (Finset.univ.filter (fun xa : ZMod p × Fin 3 =>
        (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p)) =
          (x, x + ((a : ℕ) : ZMod p), x + 2 * ((a : ℕ) : ZMod p)))).card :=
      Finset.card_pos.mpr ⟨(x, a), by simp⟩
    exact_mod_cast this.ne'
  · have : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    positivity

/-- a function on `ZMod p` (p odd prime) whose differences at distance 1 agree at `y` and `y+2`
 is constant in `ℤ`. -/
theorem const_of_diff (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (φ : ZMod p → ℤ)
    (h : ∀ y, φ (y + 1) - φ y = φ (y + 2 + 1) - φ (y + 2)) : ∀ y z, φ y = φ z := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- all differences equal d
  have hk : ∀ k : ℕ, ∀ y, φ (y + 2 * (k : ZMod p) + 1) - φ (y + 2 * (k : ZMod p)) =
      φ (y + 1) - φ y := by
    intro k; induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      have := h (y + 2 * (k : ZMod p))
      push_cast
      have e : y + 2 * ((k : ZMod p) + 1) = y + 2 * (k : ZMod p) + 2 := by ring
      rw [e, ← ih y, this]
  have hall : ∀ y, φ (y + 1) - φ y = φ 1 - φ 0 := by
    intro y
    obtain ⟨k, hk'⟩ : ∃ k : ℕ, (0 : ZMod p) + 2 * (k : ZMod p) = y := by
      refine ⟨((y / 2 : ZMod p)).val, ?_⟩
      rw [ZMod.natCast_zmod_val]; field_simp; simp
    have := hk k 0
    rw [hk'] at this
    simpa using this
  set d := φ 1 - φ 0 with hd
  have hnat : ∀ k : ℕ, φ (k : ZMod p) = φ 0 + k * d := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      have := hall (k : ZMod p)
      push_cast; linarith [ih, this]
  have hd0 : d = 0 := by
    have := hnat p
    rw [ZMod.natCast_self] at this
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
    have : (p : ℤ) * d = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hp0
    · exact h
  have hc : ∀ y, φ y = φ 0 := by
    intro y
    have := hnat y.val
    rw [ZMod.natCast_zmod_val] at this
    rw [this, hd0]; simp
  intro y z; rw [hc y, hc z]

theorem remark_1_2 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : ¬ DistHasEmbedding ℤ (muP p) := by
  rintro ⟨σ, γ, φ, hnc, hall⟩
  have E : ∀ (a : Fin 3) (x : ZMod p), σ x + γ (x + ((a : ℕ) : ZMod p)) +
      φ (x + 2 * ((a : ℕ) : ZMod p)) = 0 := fun a x => hall _ (mem_supp p x a)
  have E0 : ∀ x, σ x + γ x + φ x = 0 := by
    intro x; have := E 0 x; simpa using this
  have E1 : ∀ x, σ x + γ (x + 1) + φ (x + 2) = 0 := by
    intro x; have := E 1 x; simpa using this
  have E2 : ∀ x, σ x + γ (x + 2) + φ (x + 4) = 0 := by
    intro x; have := E 2 x
    have e1 : x + ((((2 : Fin 3) : ℕ)) : ZMod p) = x + 2 := by simp
    have e2 : x + 2 * ((((2 : Fin 3) : ℕ)) : ZMod p) = x + 4 := by simp; ring
    rw [e1, e2] at this; exact this
  have key : ∀ y, φ (y + 2) - φ (y + 1) = φ (y + 4) - φ (y + 3) := by
    intro y
    have c1 := E1 y; have c2 := E0 (y + 1); have c3 := E1 (y + 1); have c4 := E2 y
    have q1 : y + 1 + 2 = y + 3 := by ring
    have q2 : y + 1 + 1 = y + 2 := by ring
    rw [q1, q2] at c3
    linarith
  have hφ : ∀ y, φ (y + 1) - φ y = φ (y + 2 + 1) - φ (y + 2) := by
    intro y
    have := key (y - 1)
    rw [show y - 1 + 2 = y + 1 by ring, show y - 1 + 1 = y by ring,
      show y - 1 + 4 = y + 3 by ring, show y - 1 + 3 = y + 2 by ring] at this
    rw [show y + 2 + 1 = y + 3 by ring]
    linarith
  have hφc := const_of_diff p hp φ hφ
  have hγ : ∀ y, γ (y + 1) = γ y := by
    intro y
    have := E1 y; have := E0 y
    have e := hφc (y + 2) y
    linarith
  have hγc : ∀ y z, γ y = γ z := by
    have hc : ∀ y, γ y = γ 0 := by
      intro y
      have hnat : ∀ k : ℕ, γ (k : ZMod p) = γ 0 := by
        intro k; induction k with
        | zero => simp
        | succ k ih => push_cast; rw [hγ, ih]
      have := hnat y.val
      rwa [ZMod.natCast_zmod_val] at this
    intro y z; rw [hc y, hc z]
  have hσc : ∀ y z, σ y = σ z := by
    intro y z
    have := E0 y; have := E0 z
    have := hγc y z; have := hφc y z
    linarith
  exact hnc ⟨hσc, hγc, hφc⟩

end RestrictedAP.Counting.Dev.R12
end
theorem solution : type_of% @RestrictedAP.Counting.Dev.R12.remark_1_2 := @RestrictedAP.Counting.Dev.R12.remark_1_2
