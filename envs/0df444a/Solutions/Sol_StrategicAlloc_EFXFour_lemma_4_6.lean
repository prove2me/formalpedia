-- Prove2me | solution 1 for StrategicAlloc.EFXFour.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:53:53.911491+00:00
-- url     : https://prove2.me/submissions/9a19b810-2b77-4f36-8a84-7ce388ae87a4

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

set_option autoImplicit false
open StrategicAlloc.EFXFour

theorem key1a (w : Fin 4 → ℝ) (h01 : w 1 ≤ w 0) (h12 : w 2 ≤ w 1) (h23 : w 3 ≤ w 2)
    (h3 : 0 < w 3) (x : Fin 4 → Fin 2) :
    ∃ j : Fin 2, (∑ i, if x i = j then w i else 0) ≤ w 0 + w 3 := by
  simp only [Fin.sum_univ_four]
  generalize x 0 = x0
  generalize x 1 = x1
  generalize x 2 = x2
  generalize x 3 = x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    first
    | (refine ⟨0, ?_⟩; simp <;> linarith)
    | (refine ⟨1, ?_⟩; simp <;> linarith)

theorem key1b (w : Fin 4 → ℝ) (h01 : w 1 ≤ w 0) (h12 : w 2 ≤ w 1) (h23 : w 3 ≤ w 2)
    (h3 : 0 < w 3) (x : Fin 4 → Fin 2) :
    ∃ j : Fin 2, ((∑ i, if x i = j then w i else 0) ≤ w 0 ∨
      (∑ i, if x i = j then w i else 0) ≤ w 1 + w 2) := by
  simp only [Fin.sum_univ_four]
  generalize x 0 = x0
  generalize x 1 = x1
  generalize x 2 = x2
  generalize x 3 = x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    first
    | (refine ⟨0, Or.inl ?_⟩; simp <;> linarith)
    | (refine ⟨0, Or.inr ?_⟩; simp <;> linarith)
    | (refine ⟨1, Or.inl ?_⟩; simp <;> linarith)
    | (refine ⟨1, Or.inr ?_⟩; simp <;> linarith)

theorem solution (v : Fin 2 → Fin 4 → ℝ) (hv : ∀ i g, 0 ≤ v i g) (h : Fin 4 ≃ Fin 4)
    (h01 : v 0 (h 1) ≤ v 0 (h 0)) (h12 : v 0 (h 2) ≤ v 0 (h 1)) (h23 : v 0 (h 3) ≤ v 0 (h 2))
    (h3pos : 0 < v 0 (h 3)) :
    mu v 0 ≤ StrategicAlloc.RRFair.val v 0 {h 0, h 3} ∧ mu v 0 ≤ max (StrategicAlloc.RRFair.val v 0 {h 0}) (StrategicAlloc.RRFair.val v 0 {h 1, h 2}) := by
  have hF : ∀ (f : Fin 4 → Fin 2) (j : Fin 2),
      StrategicAlloc.RRFair.val v 0 (Finset.univ.filter fun g => f g = j) =
        ∑ i, if f (h i) = j then v 0 (h i) else 0 := by
    intro f j
    unfold StrategicAlloc.RRFair.val
    rw [Finset.sum_filter]
    exact (Equiv.sum_comp h (fun g => if f g = j then v 0 g else 0)).symm
  have hbdd : ∀ (f : Fin 4 → Fin 2),
      BddBelow (Set.range fun j : Fin 2 => StrategicAlloc.RRFair.val v 0 (Finset.univ.filter fun g => f g = j)) :=
    fun f => (Set.finite_range _).bddBelow
  have hmu : ∀ X : ℝ, (∀ f : Fin 4 → Fin 2, ∃ j : Fin 2,
      StrategicAlloc.RRFair.val v 0 (Finset.univ.filter fun g => f g = j) ≤ X) → mu v 0 ≤ X := by
    intro X hX
    unfold mu LittleCharity.MMS.mms
    apply ciSup_le
    intro f
    obtain ⟨j, hj⟩ := hX f
    exact (ciInf_le (hbdd f) j).trans hj
  have hne : ∀ a b : Fin 4, a ≠ b → h a ≠ h b := fun a b hab => h.injective.ne hab
  have e03 : StrategicAlloc.RRFair.val v 0 {h 0, h 3} = v 0 (h 0) + v 0 (h 3) := by
    unfold StrategicAlloc.RRFair.val
    rw [Finset.sum_pair (hne 0 3 (by decide))]
  have e0 : StrategicAlloc.RRFair.val v 0 {h 0} = v 0 (h 0) := by
    unfold StrategicAlloc.RRFair.val
    rw [Finset.sum_singleton]
  have e12 : StrategicAlloc.RRFair.val v 0 {h 1, h 2} = v 0 (h 1) + v 0 (h 2) := by
    unfold StrategicAlloc.RRFair.val
    rw [Finset.sum_pair (hne 1 2 (by decide))]
  constructor
  · rw [e03]
    apply hmu
    intro f
    obtain ⟨j, hj⟩ := key1a (fun i => v 0 (h i)) h01 h12 h23 h3pos (fun i => f (h i))
    exact ⟨j, by rw [hF]; exact hj⟩
  · rw [e0, e12]
    apply hmu
    intro f
    obtain ⟨j, hj⟩ := key1b (fun i => v 0 (h i)) h01 h12 h23 h3pos (fun i => f (h i))
    refine ⟨j, ?_⟩
    rw [hF]
    rcases hj with H | H
    · exact le_trans H (le_max_left _ _)
    · exact le_trans H (le_max_right _ _)
