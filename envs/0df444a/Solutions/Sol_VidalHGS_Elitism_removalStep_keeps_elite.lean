-- Prove2me | solution 1 for VidalHGS.Elitism.removalStep_keeps_elite
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-07T22:35:10.255283+00:00
-- url     : https://prove2.me/submissions/9863b4c9-e3cd-491f-96ec-f3be6841b683

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection
import Theorems.Thm_VidalHGS_Elitism_worst_biasedFitness_ge_one
import Theorems.Thm_VidalHGS_Elitism_elite_biasedFitness_lt_one

open VidalHGS.Elitism

theorem solution {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P Q : Finset α) (J : α)
    (hstep : RemovalStep c δ Δ nbElit best P Q) (hsize : nbElit + 1 ≤ P.card)
    (hJ : J ∈ P) (hJX : J ∉ cloneSet c δ best P) (helite : IsElite c nbElit P J) :
    J ∈ Q := by
  obtain ⟨I, hI, hQ, hne, hemp⟩ := hstep
  rw [hQ, Finset.mem_erase]
  refine ⟨?_, hJ⟩
  intro hJI
  rcases (cloneSet c δ best P).eq_empty_or_nonempty with hX | hX
  · -- X = ∅: the removed individual I maximizes BF over P, so BF(I) ≥ BF(W) ≥ 1 > BF(J)
    have hmax := hemp hX
    have hElit1 : 1 ≤ nbElit := by
      unfold IsElite at helite
      omega
    have hcard : 2 ≤ P.card := by omega
    obtain ⟨W, hW, hWmax⟩ := Finset.exists_max_image P c ⟨J, hJ⟩
    have hWBF := (worst_biasedFitness_ge_one c δ Δ nbElit best P W hX hcard hsize hW hWmax).2
    have hJBF := (elite_biasedFitness_lt_one c Δ nbElit P J hsize hJ helite).2
    have hWI := hmax W hW
    rw [hJI] at hJBF
    linarith
  · -- X ≠ ∅: the removed individual lies in X, and J does not
    have hIX := (hne hX).1
    rw [hJI] at hJX
    exact hJX hIX
