-- Prove2me | solution 1 for VanderbeiLP.Simplex.lexicographic_rule_terminates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-03T20:16:45.229589+00:00
-- url     : https://prove2.me/submissions/d8ce17b9-000f-4ed3-8246-3d5bc60254a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_VanderbeiLP_Simplex_lex_pivot_preserves_positive_rows
import Theorems.Thm_VanderbeiLP_Simplex_lex_pivot_increases_perturbed_objective

open VanderbeiLP.Simplex
open Module

private theorem initial_positive {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (D₀ : Dictionary A) (b : Fin m → ℝ) (h0 : D₀.IsFeasible b) :
    ∀ i ∈ D₀.B, toLex (0 : Fin (m + 1) → ℝ) <
      toLex (Dictionary.lexRow D₀ D₀ b i) := by
  classical
  intro i hi
  have hcol (j : D₀.B) : D₀.colBasis j = augCol A j := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j
  have ha (p : Fin m) : D₀.abar i (D₀.epsVar p) =
      if i = D₀.epsVar p then 1 else 0 := by
    have hp : D₀.epsVar p ∈ D₀.B := Finset.orderEmbOfFin_mem _ _ _
    rw [Dictionary.abar, dif_pos hi, ← hcol ⟨D₀.epsVar p, hp⟩]
    simp [Basis.repr_self, Finsupp.single_apply, eq_comm]
  obtain ⟨p, hp⟩ : ∃ p : Fin m, D₀.epsVar p = i := by
    have hr := Finset.range_orderEmbOfFin D₀.B D₀.card_B
    have : i ∈ Set.range (D₀.B.orderEmbOfFin D₀.card_B) := by
      rw [hr]
      exact hi
    exact this
  apply Pi.toLex_strictMono
  apply lt_of_le_of_ne
  · intro q
    refine Fin.cases ?_ (fun p => ?_) q
    · exact h0 i hi
    · simp only [Dictionary.lexRow, Fin.cons_succ]
      rw [ha]
      split <;> norm_num
  · intro heq
    have he := congrFun heq p.succ
    simp [Dictionary.lexRow, ha, hp] at he

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (D₀ : Dictionary A) (h0 : D₀.IsFeasible b) :
    ¬ ∃ D : ℕ → Dictionary A, D 0 = D₀ ∧
      ∀ t, Dictionary.IsLexPivot D₀ b c (D t) (D (t + 1)) := by
  classical
  rintro ⟨D, hstart, hstep⟩
  have hpos (t : ℕ) : ∀ i ∈ (D t).B,
      toLex (0 : Fin (m + 1) → ℝ) < toLex (Dictionary.lexRow D₀ (D t) b i) := by
    induction t with
    | zero => simpa only [hstart] using initial_positive D₀ b h0
    | succ t ih =>
      exact lex_pivot_preserves_positive_rows D₀ (D t) (D (t + 1)) b c ih (hstep t)
  let objective (E : Dictionary A) :=
    toLex (∑ i ∈ E.B, extCost c i • Dictionary.lexRow D₀ E b i)
  have hstrict : StrictMono (fun t => objective (D t)) := by
    apply strictMono_nat_of_lt_succ
    intro t
    exact lex_pivot_increases_perturbed_objective D₀ (D t) (D (t + 1)) b c
      (hpos t) (hstep t)
  have hext (E F : Dictionary A) (h : E.B = F.B) : E = F := by
    cases E
    cases F
    cases h
    rfl
  have hinj : Function.Injective (fun t => (D t).B) := by
    intro s t h
    apply hstrict.injective
    exact congrArg objective (hext (D s) (D t) h)
  exact not_injective_infinite_finite (fun t => (D t).B) hinj
