-- Prove2me | solution 1 for QuantumMaxCutEnergy.integral_support_is_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:55:47.417428+00:00
-- url     : https://prove2.me/submissions/c1b0b6cb-7343-43ea-bc77-a9b519e1eda4

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- The support of an integral edge weight whose loads are at most `1` is a matching. -/
theorem solution {n : ℕ} (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hint : ∀ e, x e = 0 ∨ x e = 1) :
    ∀ e ∈ Finset.univ.filter (fun e : Edge n => x e = 1),
      ∀ e' ∈ Finset.univ.filter (fun e : Edge n => x e = 1), e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2 := by
  classical
  intro e he e' he' hne
  have he1 : x e = 1 := (Finset.mem_filter.mp he).2
  have he'1 : x e' = 1 := (Finset.mem_filter.mp he').2
  -- the load at a shared vertex would be at least `2`
  have key : ∀ v : Fin n, ¬ ((v = e.val.1 ∨ v = e.val.2) ∧ (v = e'.val.1 ∨ v = e'.val.2)) := by
    intro v hv
    have hsum : x e + x e' ≤ loadAt x v := by
      rw [loadAt]
      have hmem : ∀ f : Edge n, (if v = f.val.1 ∨ v = f.val.2 then x f else 0) = 0 ∨
          (if v = f.val.1 ∨ v = f.val.2 then x f else 0) = x f := by
        intro f
        by_cases h : v = f.val.1 ∨ v = f.val.2
        · exact Or.inr (if_pos h)
        · exact Or.inl (if_neg h)
      have h1 : ∀ f : Edge n, 0 ≤ (if v = f.val.1 ∨ v = f.val.2 then x f else 0) := by
        intro f; by_cases h : v = f.val.1 ∨ v = f.val.2 <;> simp [h, hx f]
      calc x e + x e' = (if v = e.val.1 ∨ v = e.val.2 then x e else 0)
              + (if v = e'.val.1 ∨ v = e'.val.2 then x e' else 0) := by
            rw [if_pos hv.1, if_pos hv.2]
        _ ≤ ∑ f : Edge n, (if v = f.val.1 ∨ v = f.val.2 then x f else 0) := by
            have hle : ∑ f : Edge n, (if v = f.val.1 ∨ v = f.val.2 then x f else 0)
                = (if v = e.val.1 ∨ v = e.val.2 then x e else 0)
                  + ∑ f ∈ Finset.univ.erase e, (if v = f.val.1 ∨ v = f.val.2 then x f else 0) :=
              (Finset.add_sum_erase _ _ (Finset.mem_univ e)).symm
            rw [hle]
            have h2 : 0 ≤ ∑ f ∈ Finset.univ.erase e, (if v = f.val.1 ∨ v = f.val.2 then x f else 0) :=
              Finset.sum_nonneg (fun f _ => h1 f)
            have h3 : (if v = e'.val.1 ∨ v = e'.val.2 then x e' else 0)
                ≤ ∑ f ∈ Finset.univ.erase e, (if v = f.val.1 ∨ v = f.val.2 then x f else 0) := by
              have : e' ∈ Finset.univ.erase e := Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩
              exact Finset.single_le_sum (f := fun f => (if v = f.val.1 ∨ v = f.val.2 then x f else 0))
                (fun f _ => h1 f) this
            linarith
    rw [he1, he'1] at hsum
    have := hload v
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; exact key e.val.1 ⟨Or.inl rfl, Or.inl h⟩
  · intro h; exact key e.val.1 ⟨Or.inl rfl, Or.inr h⟩
  · intro h; exact key e.val.2 ⟨Or.inr rfl, Or.inl h⟩
  · intro h; exact key e.val.2 ⟨Or.inr rfl, Or.inr h⟩

#print axioms solution
