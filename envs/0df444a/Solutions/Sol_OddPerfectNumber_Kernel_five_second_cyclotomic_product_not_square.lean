-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_second_cyclotomic_product_not_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T10:35:30.558982+00:00
-- url     : https://prove2.me/submissions/fa61a108-1403-47e7-a49e-8aec9b9e951c

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- Route K for `five_second_cyclotomic_product_not_square` (62a8c541).
--
-- A deliberately different route from route J (candidate 4967).  Route J builds the
-- `gcd = 3` branch by hand from `Nat.dvd_gcd`, `dvd_antisymm` and an explicit
-- cancellation of `9`.  This route instead consumes `Nat.gcd_mul_left` directly,
-- which factors the gcd of a common factor straight out:
--
--   Nat.gcd_mul_left (a b c : Nat) : Nat.gcd (a * b) (a * c) = a * Nat.gcd b c
--   (`Mathlib/Algebra/GCDMonoid/Basic.lean:490`, `[StrongNormalizedGCDMonoid Nat]`)
--
-- With `A = (p + 1) / 2` and `B = p ^ 2 - p + 1` and `Nat.gcd A B = 3`, we have
-- `B = 3 * B1` and `Nat.gcd (3 * A1) (3 * B1) = 3 * Nat.gcd A1 B1 = 3`, so
-- `Nat.gcd A1 B1 = 1` immediately by `Nat.mul_left_cancel`.  The square `A * B` then
-- divides `9 * (A1 * B1)`, so `A1 * B1` is a square, `B1` is a square by
-- `coprime_sq_factor_right`, and `B = 3 * z ^ 2` contradicts `quad_not_three_mul_sq`.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_second_block_gcd_cases
import Theorems.Thm_OddPerfectNumber_Kernel_quad_not_three_mul_sq
import Theorems.Thm_OddPerfectNumber_Kernel_coprime_sq_factor_right
import Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_factors_ne_square

namespace OddPerfectNumber.Kernel
namespace FiveVK

theorem solution_aux (p : Nat) (hp : p.Prime) (hp4 : p % 4 = 1) :
    ¬ ∃ y : Nat, ((p + 1) / 2) * (p ^ 2 - p + 1) = y ^ 2 := by
  rintro ⟨y, hsq⟩
  have hp2lt : 2 < p := by
    have htwo : 2 ≤ p := hp.two_le
    by_contra hc
    have htwoeq : p = 2 := by omega
    rw [htwoeq] at hp4
    norm_num at hp4
  have hneB : ¬ ∃ b, b ^ 2 = p ^ 2 - p + 1 :=
    OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square p hp2lt |>.2
  have hA0 : (p + 1) / 2 ≠ 0 := Nat.ne_of_gt (Nat.div_pos (by omega) (by norm_num))
  have hB0 : p ^ 2 - p + 1 ≠ 0 := by
    obtain ⟨n, hn⟩ : ∃ n : Nat, p = n + 1 := ⟨p - 1, by omega⟩
    rw [hn]
    have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [hexp]
    exact Nat.ne_of_gt (by omega)
  obtain hd | hd := OddPerfectNumber.Kernel.second_block_gcd_cases p hp4
  · obtain ⟨z, hz⟩ := OddPerfectNumber.Kernel.coprime_sq_factor_right hA0 hB0
        (Nat.coprime_iff_gcd_eq_one.mpr hd) ⟨y, hsq.symm⟩
    exact hneB ⟨z, hz⟩
  · -- `gcd A B = 3`: both blocks carry a factor of `3`.
    have h3dA : 3 ∣ (p + 1) / 2 := by
      rw [← hd]
      exact Nat.gcd_dvd_left _ _
    have h3dB : 3 ∣ p ^ 2 - p + 1 := by
      rw [← hd]
      exact Nat.gcd_dvd_right _ _
    -- REPAIR (candidate 5009, remote a9a049b5, CE at line 67).  Two earlier
    -- repairs were wrong in opposite directions and the remote context is the
    -- authority on the orientation.  The goal reported verbatim was
    --   `3 * A1.gcd B1 | (p + 1) / 2  context: ... hA1 : (p + 1) / 2 = 3 * A1`,
    -- so `obtain ⟨A1, hA1⟩ := h3dA` with `h3dA : 3 ∣ (p + 1) / 2` yields the
    -- witness equation with the **block on the left** and `3 * A1` on the right,
    -- and every rewrite below must run *forwards*.  Two faults followed:
    --   * writing `obtain ⟨A1, hA1⟩ := h3dA` *consumes* `h3dA`, so the later
    --     `dvd_mul_of_dvd_left h3dA _` reported `Unknown identifier h3dA`;
    --   * the attempted repair `obtain ⟨A1, hA1⟩ := Dvd.elim h3dA` is not a
    --     witness equation at all — `Dvd.elim` is a *function*
    --     `(∀ c, 3 * c = _ → β) → β`, so `rcases` reported
    --     "`(∀ c : ℕ, (p + 1) / 2 = 3 * c → ?m) → ?m` is not an inductive datatype".
    -- The correct repair inverts the order: obtain the witness equations first,
    -- and *rebuild* the divisibility from them, so nothing is consumed twice.
    obtain ⟨A1, hA1⟩ := h3dA
    obtain ⟨B1, hB1⟩ := h3dB
    -- The only later use of the divisibility is the one line
    -- `dvd_trans (dvd_mul_of_dvd_left h3dA _) hsq` below, and it is discharged
    -- directly from the witness equation instead, so the name consumed by
    -- `obtain` is never needed again.
    -- ROUTE K's core step: `Nat.gcd_mul_left` factors the shared `3` straight out,
    -- so `Nat.gcd A1 B1 = 1` needs no `Nat.dvd_gcd` and no `dvd_antisymm`.
    have hgcd3 : 3 * Nat.gcd A1 B1 = 3 := by
      -- `Nat.gcd_mul_left (a b c : Nat) : Nat.gcd (a * b) (a * c) = a * Nat.gcd b c`,
      -- so `Nat.gcd_mul_left 3 A1 B1` reads `3 * Nat.gcd A1 B1` directly, and the
      -- two block equations rewrite *towards* the `3 *` products.  The remote
      -- diagnostic `Did not find an occurrence of the pattern (p + 1) / 2 in the
      -- target expression (3 * A1).gcd (3 * B1) = 3 * A1.gcd B1` came from applying
      -- `rw` to the goal, which already displayed `3 * A1` on both sides; `calc`
      -- keeps each rewrite attached to a goal of its own.
      calc 3 * Nat.gcd A1 B1 = Nat.gcd (3 * A1) (3 * B1) :=
            (Nat.gcd_mul_left (3 : Nat) A1 B1).symm
        _ = ((p + 1) / 2).gcd (p ^ 2 - p + 1) := by rw [hA1, hB1]
        _ = 3 := hd
    have hcop : Nat.Coprime A1 B1 := by
      rw [Nat.coprime_iff_gcd_eq_one]
      exact mul_left_cancel₀ (by norm_num) hgcd3
    have hA10 : A1 ≠ 0 := by
      intro hc
      rw [hA1, hc, Nat.mul_zero] at hA0
      exact hA0 rfl
    have hB10 : B1 ≠ 0 := by
      intro hc
      rw [hB1, hc, Nat.mul_zero] at hB0
      exact hB0 rfl
    -- `3` divides the square `A * B`, so it divides `y`; cancelling the `9` leaves
    -- `A1 * B1` a square.
    have h3dY2 : 3 ∣ y ^ 2 := by
      -- REPAIR (30 September 2026 session H), replacing both earlier attempts.
      -- Those two shared one root fault: they tried to *rewrite the shared
      -- hypothesis* `hsq` so that it would look like the divisibility they
      -- wanted.  That (a) mutated `hsq`, which the later `h9` step still needs
      -- in its original `(p + 1) / 2 * ...` form, and (b) never actually
      -- produced a `3 ∣ y ^ 2` goal at all.
      --
      -- Two names those repairs invented do not exist in the pinned revision:
      -- `Nat.dvd_of_dvd_mul_left` is absent from Lean core
      -- `Init/Data/Nat/Dvd.lean` and from Mathlib `Algebra/GroupWithZero/`, and
      -- `Nat.dvd_of_mul_eq_mul_left` is likewise absent.
      --
      -- The honest route uses only core lemmas read out of
      -- `Init/Data/Nat/Dvd.lean` in this session:
      --   Nat.dvd_mul_left_of_dvd {a b} (h : a ∣ b) (c : ℕ) : a ∣ c * b   (line 31)
      --   Nat.dvd_trans {a b c} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c        (line 26)
      --
      -- REPAIR (30 September 2026 session H, remote 773e337d).  Both of this
      -- session's first attempts at this step were wrong about the *orientation*
      -- of `Nat.∣`.  The remote error is verbatim:
      --
      --   line 126: The argument `Eq.symm hA1` has type `3 * A1 = (p + 1) / 2`
      --              but is expected to have type `(p + 1) / 2 = 3 * A1`
      --              in the application `Exists.intro A1 (Eq.symm hA1)`
      --
      -- so in this revision `a ∣ b` unfolds to `∃ c, b = c * a`, **not**
      -- `∃ c, b = a * c`.  The witness equation `hA1` is therefore already in the
      -- required form and must be passed *without* `.symm`.
      --
      -- The second error (`hsq` has type `(p + 1) / 2 * (p ^ 2 - p + 1) = y ^ 2`
      -- but a `∣` was expected) says the second leg of `Nat.dvd_trans` must be a
      -- divisibility, so the square equation has to be turned into one with the
      -- same orientation: `b ∣ c` means `∃ k, c = k * b`, i.e. `y ^ 2 = y ^ 2 * k`.
      have h3dA' : 3 ∣ (p + 1) / 2 := ⟨A1, hA1⟩
      have hdvd : 3 ∣ (p ^ 2 - p + 1) * ((p + 1) / 2) :=
        Nat.dvd_mul_left_of_dvd h3dA' (p ^ 2 - p + 1)
      -- `hdvd` has the factors in the opposite order from `hsq`, so commute the
      -- factor in the divisibility rather than rewriting `hsq`.
      have hcom : (p ^ 2 - p + 1) * ((p + 1) / 2) = (p + 1) / 2 * (p ^ 2 - p + 1) :=
        Nat.mul_comm _ _
      rw [hcom] at hdvd
      refine Nat.dvd_trans hdvd ?_
      -- (a) line 148 "No goals to be solved".  The remaining goal is
      --     `(p + 1) / 2 * (p ^ 2 - p + 1) ∣ y ^ 2`.  Rewriting with `hsq`
      --     turns it into `y ^ 2 ∣ y ^ 2`, and the `dvd` instance then closes
      --     it by `Nat.dvd_refl` inside `rw`, so the following `exact` is
      --     surplus.  `simpa only [Nat.dvd_refl]` is written as a single term so
      --     the block cannot both close and then be handed another tactic.
      simpa only [hsq, Nat.dvd_refl]
    -- REPAIR (30 September 2026 session I, remote ca850669).  The `∣`
    -- orientation repair above worked, and the `mul_left_cancel₀` and `hcontra`
    -- rewrites now elaborate.  Two residual faults remain, both trivial.
    --
    -- (a) line 148 "No goals to be solved": the `refine Nat.dvd_trans hdvd ?_`
    --     block above is closed by its own `exact ⟨y ^ 2, rfl⟩`, so the `have`
    --     for `h3dY` that follows must be *dedented out of* that block rather
    --     than left inside it.  The blank-comment block separating the two was
    --     still indented to the `?_` goal's depth, so the parser treated the
    --     whole remaining proof as tactics for an already-closed goal.
    --
    -- (b) line 164, goal `⊢ ¬ ?m.975 = 0`.  `mul_left_cancel₀ (ha : a ≠ 0)
    --     (h : a * b = a * c) : b = c` needs the *cancelling factor* to be
    --     nonzero, and the factor here is the literal `9`.  Written as
    --     `(by norm_num)` the expected type is the bare proposition
    --     `¬ ?m = 0` for an unconstrained metavariable, which `norm_num` cannot
    --     close.  Naming the factor as `(9 : Nat)` pins the metavariable and
    --     leaves the ordinary goal `¬ (9 : Nat) = 0`.
    have h3dY : 3 ∣ y := by
      -- `3 ∣ y ^ 2` with `3` prime gives `3 ∣ y`. `Nat.Prime.dvd_of_dvd_pow`
      -- is stated for `Prime p`, so it needs the instance at `3` rather than
      -- the ambient `hp : Nat.Prime p`.
      exact Nat.prime_three.dvd_of_dvd_pow h3dY2
    obtain ⟨y1, hy1⟩ := h3dY
    have h9a : 9 * (A1 * B1) = ((p + 1) / 2) * (p ^ 2 - p + 1) := by
      rw [hA1, hB1]
      ring
    have h9 : 9 * (A1 * B1) = 9 * y1 ^ 2 := by
      calc 9 * (A1 * B1) = y ^ 2 := h9a.trans hsq
        _ = (3 * y1) ^ 2 := by rw [hy1]
        _ = 9 * y1 ^ 2 := by ring
    -- (c) line 178.  `mul_left_cancel₀` concludes `b = c` from `a * b = a * c`,
    -- so it needs the equality with the *cancelling factor on the left of each
    -- side's product*, i.e. exactly the shape of `h9`.  The remote reported the
    -- opposite expectation, which means in this revision the lemma is stated as
    -- `mul_left_cancel₀ : a * c = a * b → b = c`, i.e. the equation is consumed
    -- up to its own symmetry.  Passing `h9.symm` therefore matches the reported
    -- expected type `9 * y1 ^ 2 = 9 * (A1 * B1)`.
    have h9symm : 9 * y1 ^ 2 = 9 * (A1 * B1) := h9.symm
    obtain ⟨z, hz⟩ := OddPerfectNumber.Kernel.coprime_sq_factor_right hA10 hB10 hcop
      ⟨y1, mul_left_cancel₀ (by norm_num : ¬ (9 : Nat) = 0) h9symm⟩
    have hcontra : p ^ 2 - p + 1 = 3 * z ^ 2 := by
      -- (d) line 180.  `rw [hB1]` rewrites the goal `3 * B1 = 3 * z ^ 2` to
      -- `3 * B1 = 3 * B1`, and then `Nat.mul_assoc` has no pattern left to
      -- fire on, so it errors with "No goals to be solved"-adjacent reporting.
      -- `hz : z ^ 2 = B1` must be consumed *before* `hB1` rewrites the goal.
      calc p ^ 2 - p + 1 = 3 * B1 := hB1
        _ = 3 * z ^ 2 := by rw [hz]
    -- (e) line 194.  `quad_not_three_mul_sq` concludes the *existence* statement
    --     `¬ ∃ z, p ^ 2 - p + 1 = 3 * z ^ 2`, so the single-value equation
    --     `hcontra` has to be repackaged as an existential witness.  Passing
    --     `hcontra` directly reports the mismatch seen in remote `ca850669`.
    exact OddPerfectNumber.Kernel.quad_not_three_mul_sq p hp4 ⟨z, hcontra⟩

end FiveVK
end OddPerfectNumber.Kernel

theorem solution (p : Nat) (hp : p.Prime) (hp4 : p % 4 = 1) :
    ¬ ∃ y : Nat, ((p + 1) / 2) * (p ^ 2 - p + 1) = y ^ 2 :=
  OddPerfectNumber.Kernel.FiveVK.solution_aux p hp hp4
