-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.exists_expanding_full_finpartition_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/9842181f-ab97-4c51-97bb-76e8f4425eb8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_expanding_full_finpartition

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    (ι : Type*) [Fintype ι]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)]
    [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (B : (n : ℕ) → Finset (V n))
    (γ : ℝ) (hγ : 0 < γ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hαzero : Tendsto α atTop (nhds 0))
    (hbad : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (himprove : ∀ n (T : Finset (V n)),
      T ⊆ Finset.univ \ B n →
      (SoficGroups.boundary (σ n) T : ℝ) <
        γ * (T.card : ℝ) →
      ∃ U : Finset (V n), 3 * (U ∆ T).card < T.card ∧
        (SoficGroups.boundary (σ n) U : ℝ) ≤
          α n * (U.card : ℝ)) :
    ∃ P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)),
      0 < γ ∧
      (∀ n, ∀ C ∈ (P n).parts, ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤
            (SoficGroups.boundary (σ n) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (P n).parts,
            (SoficGroups.boundary (σ n) C : ℝ)) /
              Fintype.card (V n))
        atTop (nhds 0) := by
  classical
  have hchoose (n : ℕ) :=
    exists_expanding_full_finpartition
      (σ n) (B n) γ (α n) (hα n) (himprove n)
  let P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)) :=
    fun n => (hchoose n).choose
  have hexpand (n : ℕ) :
      ∀ C ∈ (P n).parts, ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤
            (SoficGroups.boundary (σ n) E : ℝ) :=
    (hchoose n).choose_spec.1
  have hbudget (n : ℕ) :
      (∑ C ∈ (P n).parts,
        (SoficGroups.boundary (σ n) C : ℝ)) ≤
        2 * (Fintype.card ι : ℝ) * ((B n).card : ℝ) +
          4 * α n * (Fintype.card (V n) : ℝ) :=
    (hchoose n).choose_spec.2
  have hpositive (n : ℕ) :
      (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hupper (n : ℕ) :
      (∑ C ∈ (P n).parts,
        (SoficGroups.boundary (σ n) C : ℝ)) /
          Fintype.card (V n) ≤
        (2 * (Fintype.card ι : ℝ)) *
          (((B n).card : ℝ) / Fintype.card (V n)) +
            4 * α n := by
    calc
      (∑ C ∈ (P n).parts,
        (SoficGroups.boundary (σ n) C : ℝ)) /
          Fintype.card (V n) ≤
        (2 * (Fintype.card ι : ℝ) * ((B n).card : ℝ) +
          4 * α n * (Fintype.card (V n) : ℝ)) /
            Fintype.card (V n) :=
              div_le_div_of_nonneg_right (hbudget n)
                (hpositive n).le
      _ = (2 * (Fintype.card ι : ℝ)) *
            (((B n).card : ℝ) / Fintype.card (V n)) +
          4 * α n := by
            field_simp [(hpositive n).ne']
  have hlimit : Tendsto
      (fun n =>
        (2 * (Fintype.card ι : ℝ)) *
          (((B n).card : ℝ) / Fintype.card (V n)) +
            4 * α n)
      atTop (nhds 0) := by
    simpa using
      (hbad.const_mul (2 * (Fintype.card ι : ℝ))).add
        (hαzero.const_mul 4)
  refine ⟨P, hγ, hexpand, ?_⟩
  exact squeeze_zero
    (fun n => div_nonneg
      (Finset.sum_nonneg fun C _ => Nat.cast_nonneg _)
      (hpositive n).le)
    hupper hlimit
end SoficGroups.KunResidualExpanderDecomposition
