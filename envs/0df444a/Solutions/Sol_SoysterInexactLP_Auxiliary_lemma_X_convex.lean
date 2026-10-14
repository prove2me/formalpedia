-- Prove2me | solution 1 for SoysterInexactLP.Auxiliary.lemma_X_convex
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:55:35.411206+00:00
-- url     : https://prove2.me/submissions/7aab2163-25fc-420e-8011-f64685b145e5

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix
open SoysterInexactLP.Auxiliary

private theorem choice_iff {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (R : Set (Fin m → ℝ)) (x : Fin n → ℝ) :
    FeasibleI K R x ↔ (∀ j, 0 ≤ x j) ∧
      ∀ a : Fin n → Fin m → ℝ, (∀ j, a j ∈ K j) → ∑ j, x j • a j ∈ R := by
  classical
  constructor
  · rintro ⟨hx, hR⟩
    refine ⟨hx, fun a ha => hR ?_⟩
    exact (Set.mem_fintype_sum _ _).mpr
      ⟨fun j => x j • a j, fun j => Set.smul_mem_smul_set (ha j), rfl⟩
  · rintro ⟨hx, hR⟩
    refine ⟨hx, fun y hy => ?_⟩
    obtain ⟨z, hz, rfl⟩ := (Set.mem_fintype_sum _ _).mp hy
    choose a ha heq using fun j => Set.mem_smul_set.mp (hz j)
    have hfun : z = fun j => x j • a j := by
      funext j
      exact (heq j).symm
    rw [hfun]
    exact hR a ha

private theorem coordinate_support {m : ℕ} (K : Set (Fin m → ℝ)) (i : Fin m) :
    supportFun K (Pi.single i 1) = ⨆ a ∈ K, (a i : EReal) := by
  simp [supportFun, dotProduct, Pi.single_apply]

private theorem coordinate_le {m : ℕ} (K : Set (Fin m → ℝ))
    (i : Fin m) {a : Fin m → ℝ} (ha : a ∈ K) :
    (a i : EReal) ≤ supportFun K (Pi.single i 1) := by
  rw [coordinate_support]
  exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)

private theorem support_not_bot {m : ℕ} (K : Set (Fin m → ℝ))
    (hne : K.Nonempty) (i : Fin m) : supportFun K (Pi.single i 1) ≠ ⊥ := by
  obtain ⟨a, ha⟩ := hne
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (coordinate_le K i ha)

private theorem entry_le {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤)
    (i : Fin m) (j : Fin n) {a : Fin m → ℝ} (ha : a ∈ K j) : a i ≤ Abar K i j := by
  have h := EReal.toReal_le_toReal (coordinate_le (K j) i ha)
    (EReal.coe_ne_bot _) (ne_of_lt (hfin i j))
  simpa [Abar] using h
private theorem matrix_iff {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    FeasibleIb K b x ↔ (∀ A ∈ MSet K, A *ᵥ x ≤ b) ∧ 0 ≤ x := by
  classical
  change FeasibleI K (Kb b) x ↔ _
  rw [choice_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨?_, hx⟩
    intro A hA i
    have hi := h (fun j i => A i j) hA
    simpa [Kb, Finset.sum_apply, Pi.smul_apply, mulVec, dotProduct, mul_comm] using hi i
  · rintro ⟨h, hx⟩
    refine ⟨hx, fun a ha => ?_⟩
    have hi := h (fun i j => a j i) ha
    intro i
    simpa [Finset.sum_apply, Pi.smul_apply, mulVec, dotProduct, mul_comm] using hi i

theorem solution {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (R : Set (Fin m → ℝ)) (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hRne : R.Nonempty) (hRconv : Convex ℝ R) :
    Convex ℝ (X K R) := by
  classical
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hxR⟩ := (choice_iff K R x).mp hx
  obtain ⟨hy0, hyR⟩ := (choice_iff K R y).mp hy
  apply (choice_iff K R (a • x + b • y)).mpr
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx0 j)) (mul_nonneg hb (hy0 j))
  · intro z hz
    have hmem := hRconv (hxR z hz) (hyR z hz) ha hb hab
    convert hmem using 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
