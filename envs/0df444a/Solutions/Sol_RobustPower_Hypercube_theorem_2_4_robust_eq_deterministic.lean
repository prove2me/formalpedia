-- Prove2me | solution 1 for RobustPower.Hypercube.theorem_2_4_robust_eq_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:55:59.233545+00:00
-- url     : https://prove2.me/submissions/50528654-ff46-47aa-8701-879ee3d09e43

import Definitions.Def_RobustPower_Hypercube_RhsProblems

open RobustPower.Hypercube

theorem solution
    {m n₁ n₂ : ℕ} {Ω : Type*} [Nonempty Ω]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (I₁ : Set (Fin n₁))
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : ∀ ω, 0 ≤ b ω)
    (hbdd : BddAbove (Set.range b)) :
    (∀ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ),
      robFeasibleRhs A B b I₁ ∅ x y ↔ detFeasible A B (worstRhs b) I₁ ∅ x y) ∧
    zRobRhs A B b I₁ ∅ c d = zDet A B (worstRhs b) I₁ ∅ c d := by
  have hbdd_coord (j : Fin m) : BddAbove (Set.range fun ω => b ω j) := by
    rcases hbdd with ⟨u, hu⟩
    refine ⟨u j, ?_⟩
    rintro _ ⟨ω, rfl⟩
    exact hu ⟨ω, rfl⟩ j
  have hfeas (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
      robFeasibleRhs A B b I₁ ∅ x y ↔ detFeasible A B (worstRhs b) I₁ ∅ x y := by
    constructor
    · rintro ⟨hx, hy, hxy⟩
      refine ⟨hx, hy, ?_⟩
      intro j
      exact ciSup_le fun ω => hxy ω j
    · rintro ⟨hx, hy, hxy⟩
      refine ⟨hx, hy, ?_⟩
      intro ω j
      exact (le_ciSup (hbdd_coord j) ω).trans (hxy j)
  refine ⟨hfeas, ?_⟩
  simp only [zRobRhs, zDet, hfeas]
