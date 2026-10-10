-- Prove2me | solution 1 for SymPolyOpt.PowerSumUB.theorem_6_7
-- status  : ACCEPTED   (disprove)
-- author  : @carlok
-- created : 2026-10-10T06:15:13.92114+00:00
-- url     : https://prove2.me/submissions/8201548b-b363-4fa3-9117-8711c3c05b66

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

/-!
# Disproof of `SymPolyOpt.PowerSumUB.theorem_6_7` as encoded

Target: theorem id `4606d7a2-19ba-4a59-bc00-e915f4f80a8d`, environment
`0df444a360eaa60ab8c11dca51a86af692955474` (`leanprover/lean4:v4.33.1`).
Submitted with `proof_type=disprove`.

The encoded hypothesis `q ≤ 2 * m - 2` is subtraction on `ℕ`, which truncates:
at `m = 0` it reads `q ≤ 0`, so `(n, m, q) = (1, 0, 0)` is admissible. The
constraint list of (6.4) is then empty, so every point is feasible and
`minP 1 0 0 γ = 1`; the only monic polynomial of degree `0` is `p = 1`, whose
root multiset is empty, so `valU 0 0 γ = 0`. The first conjunct of the
conclusion claims `1 ≤ 0`.

The paper is not at fault: over `ℤ` the hypothesis at `m = 0` is `q ≤ -2`,
unsatisfiable for `q ∈ ℕ`, so the intended statement presumably assumes `2 ≤ m`.
-/

open Polynomial
open SymPolyOpt.PowerSumLB

theorem solution :
    ¬ (∀ (n m q : ℕ) (γ : ℕ → ℝ), m ≤ n → m ≤ q → q ≤ 2 * m - 2 →
        SymPolyOpt.PowerSumLB.minP n m q γ ≤ SymPolyOpt.PowerSumUB.valU m q γ ∧
          ((∃ x ∈ SymPolyOpt.PowerSumLB.feasP n m γ,
                ((SymPolyOpt.PowerSumLB.powerSum x q : ℝ) : EReal) =
                  SymPolyOpt.PowerSumLB.minP n m q γ ∧
                (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ m) →
              SymPolyOpt.PowerSumLB.minP n m q γ =
                SymPolyOpt.PowerSumUB.valU m q γ)) := by
  intro h
  let γ₀ : ℕ → ℝ := fun _ => 0
  -- the counterexample: `n = 1`, `m = 0`, `q = 0`, any `γ`
  -- (the third hypothesis is `0 ≤ 2 * 0 - 2`, i.e. `0 ≤ 0` after truncation)
  obtain ⟨hmain, _⟩ := h 1 0 0 γ₀ (by omega) (by omega) (by omega)
  -- `minP 1 0 0 γ₀ = 1`
  have hmin : SymPolyOpt.PowerSumLB.minP 1 0 0 γ₀ = ((1 : ℝ) : EReal) := by
    rw [show SymPolyOpt.PowerSumLB.minP 1 0 0 γ₀
          = ⨅ x : Fin 1 → ℝ, ⨅ (_ : x ∈ SymPolyOpt.PowerSumLB.feasP 1 0 γ₀),
              ((SymPolyOpt.PowerSumLB.powerSum x 0 : ℝ) : EReal) from rfl]
    refine le_antisymm ?_ ?_
    · -- one feasible point attains the value, and `s_0 x = ∑_i x_i^0 = 1`
      have hx : (fun _ : Fin 1 => (0 : ℝ)) ∈ SymPolyOpt.PowerSumLB.feasP 1 0 γ₀ := by
        intro j hj hj'
        exfalso
        omega
      have hp : SymPolyOpt.PowerSumLB.powerSum (fun _ : Fin 1 => (0 : ℝ)) 0 = (1 : ℝ) := by
        simp [SymPolyOpt.PowerSumLB.powerSum]
      calc (⨅ x : Fin 1 → ℝ, ⨅ (_ : x ∈ SymPolyOpt.PowerSumLB.feasP 1 0 γ₀),
              ((SymPolyOpt.PowerSumLB.powerSum x 0 : ℝ) : EReal))
          ≤ ((SymPolyOpt.PowerSumLB.powerSum (fun _ : Fin 1 => (0 : ℝ)) 0 : ℝ) : EReal) :=
            iInf₂_le (fun _ : Fin 1 => (0 : ℝ)) hx
        _ = ((1 : ℝ) : EReal) := by simp only [hp]
    · -- every feasible point has the same value
      refine le_iInf₂ fun x _ => ?_
      have hp : SymPolyOpt.PowerSumLB.powerSum x 0 = (1 : ℝ) := by
        simp [SymPolyOpt.PowerSumLB.powerSum]
      simpa only [hp] using le_rfl
  -- `valU 0 0 γ₀ = 0`: the only monic polynomial of degree `0` is `p = 1`
  have hval : SymPolyOpt.PowerSumUB.valU 0 0 γ₀ ≤ ((0 : ℝ) : EReal) := by
    rw [show SymPolyOpt.PowerSumUB.valU 0 0 γ₀
          = ⨅ p : ℝ[X], ⨅ (_ : p ∈ SymPolyOpt.PowerSumUB.feasU 0 γ₀),
              ((SymPolyOpt.PowerSumUB.newtonSum p 0 : ℝ) : EReal) from rfl]
    have hmem : (1 : ℝ[X]) ∈ SymPolyOpt.PowerSumUB.feasU 0 γ₀ := by
      refine ⟨Polynomial.monic_one, Polynomial.natDegree_one, ?_, ?_⟩
      · intro j hj hj'
        exfalso
        omega
      · -- `hankel 0 _` is a `0 × 0` matrix: `IsSymm` and the quadratic form are vacuous
        -- (`PosSemidef` here is `IsSymm ∧ ∀ x : m →₀ ℝ, 0 ≤ x.sum ...`, and `x` is `0`)
        constructor
        · first | exact Subsingleton.elim _ _ | exact Matrix.ext fun i j => Fin.elim0 i
        · intro x
          have hx : x = 0 := Finsupp.ext fun i => Fin.elim0 i
          rw [hx]
          simp [Finsupp.sum]
    have hn : SymPolyOpt.PowerSumUB.newtonSum (1 : ℝ[X]) 0 = 0 := by
      simp [SymPolyOpt.PowerSumUB.newtonSum]
    calc (⨅ p : ℝ[X], ⨅ (_ : p ∈ SymPolyOpt.PowerSumUB.feasU 0 γ₀),
            ((SymPolyOpt.PowerSumUB.newtonSum p 0 : ℝ) : EReal))
        ≤ ((SymPolyOpt.PowerSumUB.newtonSum (1 : ℝ[X]) 0 : ℝ) : EReal) :=
          iInf₂_le (1 : ℝ[X]) hmem
      _ = ((0 : ℝ) : EReal) := by simp only [hn]
  -- `1 ≤ valU 0 0 γ₀ ≤ 0`
  rw [hmin] at hmain
  exact absurd (le_trans hmain hval)
    (not_le_of_gt (EReal.coe_lt_coe_iff.mpr (by norm_num)))
