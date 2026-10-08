-- Prove2me | solution 1 for SubstOverbooking.Structure.lemma2_V0_concave
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:22:14.095291+00:00
-- url     : https://prove2.me/submissions/e6901e77-0c8d-4ace-a2f6-2c0f39f2f55b

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

open SubstOverbooking.Structure
open scoped BigOperators

private theorem feasible_nonempty {n m : ℕ} (c : Fin (m + 1) → ℝ)
    (z : Fin n → ℝ) (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (hz : ∀ i, 0 ≤ z i) :
    Set.Nonempty {y | IsTPFeasible c z y} := by
  classical
  refine ⟨fun i j => if j = 0 then z i else 0, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    dsimp
    split_ifs <;> simp [hz]
  · intro i
    simp
  · intro j hj
    simpa [hj] using hc j hj

private theorem feasible_compact {n m : ℕ} (c : Fin (m + 1) → ℝ)
    (z : Fin n → ℝ) : IsCompact {y | IsTPFeasible c z y} := by
  have hclosed : IsClosed {y | IsTPFeasible c z y} := by
    unfold IsTPFeasible
    simp only [Set.setOf_and, Set.setOf_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (show Continuous (fun y : Fin n → Fin (m + 1) → ℝ => y i j) by fun_prop)).inter
      ((isClosed_iInter fun i => isClosed_eq
        (show Continuous (fun y : Fin n → Fin (m + 1) → ℝ => ∑ j, y i j) by fun_prop) continuous_const).inter
        (isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_le (show Continuous (fun y : Fin n → Fin (m + 1) → ℝ => ∑ i, y i j) by fun_prop) continuous_const))
  apply (isCompact_Icc (a := (0 : Fin n → Fin (m + 1) → ℝ))
    (b := fun i _ => z i)).of_isClosed_subset hclosed
  intro y hy
  refine ⟨hy.1, ?_⟩
  intro i j
  have := Finset.single_le_sum (fun k _ => hy.1 i k) (Finset.mem_univ j)
  simpa [hy.2.1 i] using this

private theorem objective_continuous {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) :
    Continuous (tpObjective a) := by
  unfold tpObjective
  fun_prop

private theorem optimum {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (hz : ∀ i, 0 ≤ z i) :
    ∃ y, IsTPFeasible c z y ∧ tpObjective a y = V0 a c z := by
  obtain ⟨y, hy, he⟩ := (feasible_compact c z).exists_sSup_image_eq
    (feasible_nonempty c z hc hz) (objective_continuous a).continuousOn
  exact ⟨y, hy, he.symm⟩

private theorem objective_le_value {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ)
    (y : Fin n → Fin (m + 1) → ℝ) (hy : IsTPFeasible c z y) :
    tpObjective a y ≤ V0 a c z := by
  exact le_csSup ((feasible_compact c z).bddAbove_image
    (objective_continuous a).continuousOn) ⟨y, hy, rfl⟩

private theorem combine_feasible {n m : ℕ}
    (c d : Fin (m + 1) → ℝ) (z w : Fin n → ℝ)
    (y v : Fin n → Fin (m + 1) → ℝ)
    (hy : IsTPFeasible c z y) (hv : IsTPFeasible d w v)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    IsTPFeasible (α • c + β • d) (α • z + β • w) (α • y + β • v) := by
  refine ⟨fun i j => add_nonneg (mul_nonneg hα (hy.1 i j))
    (mul_nonneg hβ (hv.1 i j)), ?_, ?_⟩
  · intro i
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hy.2.1 i, hv.2.1 i]
  · intro j hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left (hy.2.2 j hj) hα)
      (mul_le_mul_of_nonneg_left (hv.2.2 j hj) hβ)

private theorem combine_objective {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (y v : Fin n → Fin (m + 1) → ℝ) (α β : ℝ) :
    tpObjective a (α • y + β • v) = α * tpObjective a y + β * tpObjective a v := by
  simp only [tpObjective, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  simp_rw [mul_left_comm (a _ _) α, mul_left_comm (a _ _) β]
  simp_rw [← Finset.mul_sum]

open SubstOverbooking.Structure

theorem solution {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) :
    (∀ c : Fin (m + 1) → ℝ, (∀ j, j ≠ 0 → 0 ≤ c j) →
      ConcaveOn ℝ {z : Fin n → ℝ | ∀ i, 0 ≤ z i} (fun z => V0 a c z)) ∧
    (∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) →
      ConcaveOn ℝ {c : Fin (m + 1) → ℝ | ∀ j, j ≠ 0 → 0 ≤ c j} (fun c => V0 a c z)) := by
  constructor
  · intro c hc
    refine ⟨?_, ?_⟩
    · intro z hz w hw α β hα hβ hab i
      exact add_nonneg (mul_nonneg hα (hz i)) (mul_nonneg hβ (hw i))
    · intro z hz w hw α β hα hβ hab
      obtain ⟨y, hy, ey⟩ := optimum a c z hc hz
      obtain ⟨v, hv, ev⟩ := optimum a c w hc hw
      have hf := combine_feasible c c z w y v hy hv α β hα hβ
      rw [← add_smul, hab, one_smul] at hf
      have h := objective_le_value a c _ _ hf
      simpa [combine_objective, ey, ev, smul_eq_mul] using h
  · intro z hz
    refine ⟨?_, ?_⟩
    · intro c hc d hd α β hα hβ hab j hj
      exact add_nonneg (mul_nonneg hα (hc j hj)) (mul_nonneg hβ (hd j hj))
    · intro c hc d hd α β hα hβ hab
      obtain ⟨y, hy, ey⟩ := optimum a c z hc hz
      obtain ⟨v, hv, ev⟩ := optimum a d z hd hz
      have hf := combine_feasible c d z z y v hy hv α β hα hβ
      rw [← add_smul, hab, one_smul] at hf
      have h := objective_le_value a _ z _ hf
      simpa [combine_objective, ey, ev, smul_eq_mul] using h

#print axioms solution
