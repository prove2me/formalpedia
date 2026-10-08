-- Prove2me | solution 1 for OceanicGames.Interior.theorem_6_efficiency
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:16:37.952242+00:00
-- url     : https://prove2.me/submissions/5aede76f-efcc-4b22-a43c-657b78c7da88

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic

open OceanicGames.Interior Finset

private noncomputable def mass {X : Type*} [DecidableEq X] (p q : X → ℝ)
    (A S : Finset X) : ℝ := (∏ j ∈ S, p j) * ∏ j ∈ A \ S, q j

private theorem pointed_sum {X : Type*} [DecidableEq X] (A : Finset X) (i : X)
    (hi : i ∈ A) (F : Finset X → ℝ) :
    ∑ S ∈ (A.erase i).powerset, F (insert i S) =
      ∑ T ∈ A.powerset, if i ∈ T then F T else 0 := by
  rw [← sum_filter]
  apply sum_bij (fun S _ => insert i S)
  · intro S hS
    have hsub := mem_powerset.mp hS
    exact mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hi (hsub.trans (erase_subset _ _))), mem_insert_self _ _⟩
  · intro S hS T hT heq
    have hiS : i ∉ S := notMem_mono (mem_powerset.mp hS) (notMem_erase _ _)
    have hiT : i ∉ T := notMem_mono (mem_powerset.mp hT) (notMem_erase _ _)
    simpa [erase_insert hiS, erase_insert hiT] using congrArg (fun U => U.erase i) heq
  · intro T hT
    have ht := mem_filter.mp hT
    refine ⟨T.erase i, mem_powerset.mpr ?_, insert_erase ht.2⟩
    exact erase_subset_erase i (mem_powerset.mp ht.1)
  · intro S hS
    rfl

private theorem mass_insert {X : Type*} [DecidableEq X] (p q : X → ℝ)
    (A S : Finset X) (i : X) (hi : i ∈ A) (hS : S ⊆ A.erase i) :
    p i * mass p q (A.erase i) S = mass p q A (insert i S) := by
  have hn : i ∉ S := notMem_mono hS (notMem_erase _ _)
  have hd : A \ insert i S = A.erase i \ S := by ext j; simp; tauto
  simp only [mass, prod_insert hn, hd]
  ring

theorem solution {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : α ≠ 0) :
    ∑ i, w i / α * ∑ S ∈ (Finset.univ.erase i).powerset, (coeff S.card : ℝ) * piProdErase α w i S
      = 1 - ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (coeff S.card : ℝ) * piProd α w S := by
  classical
  let A : Finset (Fin m) := univ
  let p : Fin m → ℝ := fun j => w j / α
  let q : Fin m → ℝ := fun j => (α - w j) / α
  have hpq (j : Fin m) : p j + q j = 1 := by dsimp [p, q]; field_simp; ring
  have hmass : ∑ T ∈ A.powerset, mass p q A T = 1 := by
    rw [show (∑ T ∈ A.powerset, mass p q A T) = ∏ j ∈ A, (p j + q j) from (prod_add _ _ _).symm]
    simp [hpq]
  have hcoeff (T : Finset (Fin m)) :
      (coeff T.card : ℝ) + (T.card : ℝ) * (coeff (T.card - 1) : ℝ) = 1 := by
    cases hh : T.card with
    | zero => simp [coeff]
    | succ k => simp [coeff]
  have hinner (i : Fin m) :
      p i * ∑ S ∈ (A.erase i).powerset, (coeff S.card : ℝ) * mass p q (A.erase i) S =
        ∑ T ∈ A.powerset, if i ∈ T then (coeff (T.card - 1) : ℝ) * mass p q A T else 0 := by
    rw [mul_sum, ← pointed_sum A i (mem_univ _) (fun T => (coeff (T.card - 1) : ℝ) * mass p q A T)]
    apply sum_congr rfl
    intro S hS
    have hn : i ∉ S := notMem_mono (mem_powerset.mp hS) (notMem_erase _ _)
    rw [card_insert_of_notMem hn, Nat.add_sub_cancel, ← mass_insert p q A S i (mem_univ _) (mem_powerset.mp hS)]
    ring
  change (∑ i, p i * ∑ S ∈ (A.erase i).powerset, (coeff S.card : ℝ) * mass p q (A.erase i) S) =
    1 - ∑ S ∈ A.powerset, (coeff S.card : ℝ) * mass p q A S
  simp_rw [hinner]
  rw [sum_comm]
  have hs (T : Finset (Fin m)) :
      (∑ i : Fin m, if i ∈ T then (coeff (T.card - 1) : ℝ) * mass p q A T else 0) =
        (T.card : ℝ) * (coeff (T.card - 1) : ℝ) * mass p q A T := by
    rw [← sum_filter]
    have hf : (univ.filter fun i => i ∈ T) = T := by ext i; simp
    rw [hf]
    simp [mul_assoc]
  simp_rw [hs]
  have hadd : (∑ T ∈ A.powerset, (T.card : ℝ) * (coeff (T.card - 1) : ℝ) * mass p q A T) +
      (∑ T ∈ A.powerset, (coeff T.card : ℝ) * mass p q A T) = 1 := by
    rw [← sum_add_distrib, ← hmass]
    apply sum_congr rfl
    intro T hT
    calc
      _ = ((coeff T.card : ℝ) + (T.card : ℝ) * (coeff (T.card - 1) : ℝ)) * mass p q A T := by ring
      _ = mass p q A T := by rw [hcoeff T, one_mul]
  linarith

#print axioms solution
