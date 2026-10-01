-- Prove2me | solution 1 for RobustMDP.FiniteHorizon.bellman_maps_monotone
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:35:53.662231+00:00
-- url     : https://prove2.me/submissions/35462906-b400-4543-953a-79a46c6fedeb

import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_FiniteHorizon_Model
import Mathlib.Tactic
open RobustMDP RobustMDP.FiniteHorizon

private theorem support_bdd {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : S ⊆ stdSimplex ℝ (Fin n)) (v : Fin n → ℝ) :
    BddAbove ((fun p : Fin n → ℝ => ∑ j, p j*v j) '' S) := by
  refine ⟨∑ j, |v j|,?_⟩
  rintro z ⟨p,hp,rfl⟩
  apply Finset.sum_le_sum
  intro j _
  have hpj := mem_Icc_of_mem_stdSimplex (hS hp) j
  calc
    p j*v j ≤ p j*|v j| := mul_le_mul_of_nonneg_left (le_abs_self _) hpj.1
    _ ≤ |v j| := by nlinarith [hpj.2,abs_nonneg (v j)]

private theorem support_mono {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : S ⊆ stdSimplex ℝ (Fin n)) (hne : S.Nonempty) : Monotone (Shared.supportFunction S) := by
  intro v w hvw
  apply csSup_le (hne.image _) 
  rintro z ⟨p,hp,rfl⟩
  apply le_trans (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hvw j) ((hS hp).1 j)))
  exact le_csSup (support_bdd S hS w) ⟨p,hp,rfl⟩

theorem solution {n N : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n N A) (t : Fin N) :
    Monotone (fun (v : Fin n → ℝ) (i : Fin n) =>
      ⨅ a : A, (M.cost t i a + Shared.supportFunction (M.rows a i) v)) ∧
    ∀ π : ControlPolicy n N A,
      Monotone (fun (v : Fin n → ℝ) (i : Fin n) =>
        M.cost t i (π t i) + Shared.supportFunction (M.rows (π t i) i) v) := by
  have hs := fun a i => support_mono (M.rows a i) (M.rows_subset_simplex a i) (M.rows_nonempty a i)
  constructor
  · intro v w hvw i
    apply ciInf_mono (Set.finite_range _).bddBelow
    intro a
    exact add_le_add_right (hs a i hvw) _
  · intro π v w hvw i
    exact add_le_add_right (hs (π t i) i hvw) _

