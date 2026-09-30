-- Prove2me | solution 1 for TranscendenceTheory.sparse_inconsistency_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T17:04:51.698572+00:00
-- url     : https://prove2.me/submissions/b28e8216-e998-4011-a248-4b67114df1df

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Choose

open scoped BigOperators

theorem solution
    (K ι α : Type*) [Field K] [Fintype ι]
    (A : α → ι → K) (B : α → K) :
    (¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a) ↔
      ∃ r : ℕ, r ≤ Fintype.card ι + 1 ∧
        ∃ a : Fin r → α, ∃ c : Fin r → K,
          (∀ i, ∑ j, c j * A (a j) i = 0) ∧
          ∑ j, c j * B (a j) = 1 := by
  classical
  let row : α → (ι → K) × K := fun a => (A a, B a)
  let S := Submodule.span K (Set.range row)
  let e : (ι → K) × K := (0, 1)
  constructor
  · intro hno
    have he : e ∈ S := by
      by_contra hnot
      obtain ⟨f, hfe, hS⟩ := S.exists_dual_map_eq_bot_of_notMem hnot inferInstance
      have hfrow (a : α) : f (row a) = 0 := by
        apply (Submodule.mem_bot K).mp
        rw [← hS]
        exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, rfl⟩)
      let v : ι → (ι → K) × K := fun i => (Pi.single i 1, 0)
      have hrow (a : α) : row a = (∑ i, A a i • v i) + B a • e := by
        ext i <;> simp [row, v, e, Prod.fst_sum, Prod.snd_sum,
          Finset.sum_apply, Pi.single_apply]
      have hsum (a : α) : (∑ i, A a i * f (v i)) = -(B a * f e) := by
        have h := hfrow a
        rw [hrow, map_add, map_sum] at h
        simp only [map_smul, smul_eq_mul] at h
        exact eq_neg_of_add_eq_zero_left h
      apply hno
      refine ⟨fun i => -(f e)⁻¹ * f (v i), ?_⟩
      intro a
      calc
        ∑ i, A a i * (-(f e)⁻¹ * f (v i)) =
            -(f e)⁻¹ * ∑ i, A a i * f (v i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = B a := by rw [hsum]; field_simp
    obtain ⟨v, hv, hspan, hli⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq K (Set.range row)
    have he' : e ∈ Submodule.span K (Set.range v) := by
      rw [hspan]
      exact he
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp he'
    choose a ha using hv
    refine ⟨Module.finrank K S, ?_, a, c, ?_, ?_⟩
    · have h := Submodule.finrank_le S
      simpa only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
        Module.finrank_self] using h
    · intro i
      have h := congrArg (fun x : (ι → K) × K => x.1 i) hc
      simpa [← ha, row, e, Prod.fst_sum, Finset.sum_apply] using h
    · have h := congrArg (fun x : (ι → K) × K => x.2) hc
      simpa [← ha, row, e, Prod.snd_sum] using h
  · rintro ⟨r, hr, a, c, hzero, hone⟩ ⟨u, hu⟩
    have h : (1 : K) = 0 := by
      calc
        1 = ∑ j, c j * B (a j) := hone.symm
        _ = ∑ j, c j * (∑ i, A (a j) i * u i) := by simp only [hu]
        _ = ∑ i, (∑ j, c j * A (a j) i) * u i := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          simp_rw [← mul_assoc, Finset.sum_mul]
        _ = 0 := by simp only [hzero, zero_mul, Finset.sum_const_zero]
    exact one_ne_zero h
