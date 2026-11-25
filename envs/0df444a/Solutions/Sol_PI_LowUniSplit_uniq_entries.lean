-- Prove2me | solution 1 for PI.LowUniSplit.uniq_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:37.35633+00:00
-- url     : https://prove2.me/submissions/0960e5d5-ab7b-4ded-a613-f480c235b853

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Theorems.Thm_PI_LowUniSplit_mul_below
import Theorems.Thm_PI_LowUniSplit_xs_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)
namespace PI.LowUniSplit
theorem _root_.solution {a b : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    (hsa : ∀ i j, j < i → ¬ S i j → a i j = 0) (hsb : ∀ i j, j < i → S i j → b i j = 0)
    (hab : l = a * b) :
    ∀ n : ℕ, ∀ i j : Fin m, (i : ℕ) - j = n → j < i →
      a i j = (if S i j then xs S l i j else 0) ∧ b i j = (if S i j then 0 else xs S l i j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j hn hji
  have hsum : a i j + b i j = xs S l i j := by
    rw [xs_eq, hab, mul_below ha hb hji, ← hab]
    have e : ∀ k : Btw i j, a i k.1 * b k.1 j =
        (if S i k.1 then xs S l i k.1 else 0) * (if S k.1 j then 0 else xs S l k.1 j) := by
      intro k
      have h1 := k.2.1
      have h2 := k.2.2
      rw [(ih ((i : ℕ) - k.1) (by simp only [Fin.lt_def] at h1 h2; omega) i k.1 rfl h2).1,
        (ih ((k.1 : ℕ) - j) (by simp only [Fin.lt_def] at h1 h2; omega) k.1 j rfl h1).2]
    rw [Finset.sum_congr rfl (fun k _ => e k)]
    ring
  by_cases hs : S i j
  · have := hsb i j hji hs
    simp only [hs, if_true]
    constructor
    · rw [← hsum, this, add_zero]
    · exact this
  · have := hsa i j hji hs
    simp only [hs, if_false]
    constructor
    · exact this
    · rw [← hsum, this, zero_add]
end PI.LowUniSplit
