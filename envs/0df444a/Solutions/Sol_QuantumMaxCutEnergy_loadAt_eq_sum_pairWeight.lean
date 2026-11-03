-- Prove2me | solution 1 for QuantumMaxCutEnergy.loadAt_eq_sum_pairWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T02:20:21.262003+00:00
-- url     : https://prove2.me/submissions/f6e66ca5-08d5-41bb-8420-d1dac9db4447

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- Summing the pair weights over the other endpoint recovers the vertex load. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (a : Fin n) :
    loadAt x a = ∑ b, pairWeight x a b := by
  classical
  set s : Finset (Edge n) :=
    Finset.univ.filter (fun e => a = e.val.1 ∨ a = e.val.2) with hsdef
  have h1 : loadAt x a = ∑ e ∈ s, x e := by
    rw [hsdef, loadAt, ← Finset.sum_filter]
  have hmem_other : ∀ e ∈ s, (if e.val.1 = a then e.val.2 else e.val.1) ≠ a := by
    intro e he
    have hep := e.property
    split <;> omega
  have h2 : ∑ e ∈ s, x e = ∑ j ∈ Finset.univ.erase a, pairWeight x a j := by
    refine Finset.sum_bij (fun e _ => if e.val.1 = a then e.val.2 else e.val.1)
      (fun e he => Finset.mem_erase.mpr ⟨hmem_other e he, Finset.mem_univ _⟩) ?_ ?_ ?_
    · -- injectivity
      intro a1 ha b1 hb hab
      have hap := a1.property
      have hbp := b1.property
      by_cases ha₁ : a1.val.1 = a
      · by_cases hb₁ : b1.val.1 = a
        · simp only [if_pos ha₁, if_pos hb₁] at hab
          refine Subtype.ext ?_
          show (a1.val.1, a1.val.2) = (b1.val.1, b1.val.2)
          rw [ha₁, hb₁, hab]
        · simp only [if_pos ha₁, if_neg hb₁] at hab
          have hb₂ : b1.val.2 = a := by
            rcases (Finset.mem_filter.mp hb).2 with h | h
            · exact absurd h.symm hb₁
            · exact h.symm
          omega
      · by_cases hb₁ : b1.val.1 = a
        · simp only [if_neg ha₁, if_pos hb₁] at hab
          have ha₂ : a1.val.2 = a := by
            rcases (Finset.mem_filter.mp ha).2 with h | h
            · exact absurd h.symm ha₁
            · exact h.symm
          omega
        · simp only [if_neg ha₁, if_neg hb₁] at hab
          have ha₂ : a1.val.2 = a := by
            rcases (Finset.mem_filter.mp ha).2 with h | h
            · exact absurd h.symm ha₁
            · exact h.symm
          have hb₂ : b1.val.2 = a := by
            rcases (Finset.mem_filter.mp hb).2 with h | h
            · exact absurd h.symm hb₁
            · exact h.symm
          refine Subtype.ext ?_
          show (a1.val.1, a1.val.2) = (b1.val.1, b1.val.2)
          rw [ha₂, hb₂, hab]
    · -- surjectivity
      intro j hj
      have hja : j ≠ a := (Finset.mem_erase.mp hj).1
      rcases lt_or_gt_of_ne (Ne.symm hja) with hlt | hlt
      · refine ⟨⟨(a, j), hlt⟩, ?_, ?_⟩
        · rw [hsdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, Or.inl rfl⟩
        · show (if (⟨(a, j), hlt⟩ : Edge n).val.1 = a then (⟨(a, j), hlt⟩ : Edge n).val.2
              else (⟨(a, j), hlt⟩ : Edge n).val.1) = j
          rw [if_pos rfl]
      · refine ⟨⟨(j, a), hlt⟩, ?_, ?_⟩
        · rw [hsdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, Or.inr rfl⟩
        · show (if (⟨(j, a), hlt⟩ : Edge n).val.1 = a then (⟨(j, a), hlt⟩ : Edge n).val.2
              else (⟨(j, a), hlt⟩ : Edge n).val.1) = j
          rw [if_neg (Fin.ne_of_lt hlt)]
    · -- agreement
      intro e he
      by_cases hc : e.val.1 = a
      · have hlt : a < e.val.2 := hc ▸ e.property
        rw [if_pos hc, pairWeight, dif_pos hlt]
        congr 1
        refine Subtype.ext ?_
        show (e.val.1, e.val.2) = (a, e.val.2)
        rw [hc]
      · have heq : e.val.2 = a := by
          rcases (Finset.mem_filter.mp he).2 with h | h
          · exact absurd h.symm hc
          · exact h.symm
        have hlt : e.val.1 < a := heq ▸ e.property
        rw [if_neg hc, pairWeight, dif_neg (by omega), dif_pos (by omega)]
        congr 1
        refine Subtype.ext ?_
        show (e.val.1, e.val.2) = (e.val.1, a)
        rw [heq]
  -- fold the erased vertex back in
  have h3 := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
    (h := Finset.mem_univ a) (f := fun j : Fin n => pairWeight x a j)
  rw [h1, h2, ← h3, pairWeight_self, add_zero]


#print axioms solution
