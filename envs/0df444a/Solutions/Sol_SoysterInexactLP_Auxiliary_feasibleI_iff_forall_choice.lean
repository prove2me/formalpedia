-- Prove2me | solution 1 for SoysterInexactLP.Auxiliary.feasibleI_iff_forall_choice
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:55:32.231981+00:00
-- url     : https://prove2.me/submissions/81132cd0-1872-4492-abac-a484acb66294

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

theorem solution {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (R : Set (Fin m → ℝ)) (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hRne : R.Nonempty) (hRconv : Convex ℝ R) (x : Fin n → ℝ) :
    FeasibleI K R x ↔
      (∀ j, 0 ≤ x j) ∧ ∀ a : Fin n → Fin m → ℝ, (∀ j, a j ∈ K j) → ∑ j, x j • a j ∈ R := by
  exact choice_iff K R x
