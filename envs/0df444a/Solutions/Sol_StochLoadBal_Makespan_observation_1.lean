-- Prove2me | solution 1 for StochLoadBal.Makespan.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T18:49:07.468927+00:00
-- url     : https://prove2.me/submissions/0942f04f-a199-4567-91f8-c6a7c57c7496

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

namespace MachineClassResearch

variable {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
variable (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (b : ℝ)
variable (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)

include hy

lemma removable (L : Finset (Fin m)) (hL : L.Nonempty) :
    (L.filter (fun i => zLoad P X y i L.card ≤ b)).Nonempty := by
  classical
  by_contra h
  have hn : ∀ i ∈ L, b < zLoad P X y i L.card := by
    intro i hi
    by_contra hh
    exact h ⟨i, Finset.mem_filter.mpr ⟨hi, le_of_not_gt hh⟩⟩
  have hs := Finset.sum_lt_sum_of_nonempty hL hn
  have hu := hy.2.2.2.2 L hL
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  nlinarith

lemma loop_invariant (fuel : ℕ) (L : Finset (Fin m)) (cls : Fin m → ℕ)
    (hsize : L.card ≤ fuel) :
    (∀ i ∉ L, classLoop P X b y fuel L cls i = cls i) ∧
    (∀ i ∈ L, 1 ≤ classLoop P X b y fuel L cls i ∧
      classLoop P X b y fuel L cls i ≤ L.card) ∧
    ∀ ℓ : ℕ, (L.filter (fun i => classLoop P X b y fuel L cls i ≤ ℓ)).card ≤ ℓ := by
  classical
  induction fuel generalizing L cls with
  | zero =>
    have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [hL, classLoop]
  | succ fuel ih =>
    by_cases hL : L = ∅
    · simp [hL, classLoop]
    have hLpos : 0 < L.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hL)
    let F := L.filter (fun i => zLoad P X y i L.card ≤ b)
    have hF : F.Nonempty := removable P X b y hy L (Finset.nonempty_iff_ne_empty.mpr hL)
    have hFn : F ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hF
    have hFL : F ⊆ L := Finset.filter_subset _ _
    let S := L \ F
    have hSL : S ⊆ L := Finset.sdiff_subset
    have hScard : S.card ≤ fuel := by
      have heq := Finset.card_sdiff_add_card_eq_card hFL
      have hp := Finset.card_pos.mpr hF
      dsimp [S]
      omega
    let upd : Fin m → ℕ := fun i => if i ∈ F then L.card else cls i
    have hrec := ih S upd hScard
    have heq : classLoop P X b y (fuel+1) L cls =
        classLoop P X b y fuel S upd := by
      simp only [classLoop, if_neg hL]
      change (if F = ∅ then cls else classLoop P X b y fuel S upd) = _
      rw [if_neg hFn]
    rw [heq]
    have hfixed (i : Fin m) (hi : i ∈ F) :
        classLoop P X b y fuel S upd i = L.card := by
      have hn : i ∉ S := by simp [S, hi]
      simpa [upd, hi] using hrec.1 i hn
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hnS : i ∉ S := fun h => hi (hSL h)
      have hnF : i ∉ F := fun h => hi (hFL h)
      simpa [upd, hnF] using hrec.1 i hnS
    · intro i hi
      by_cases hiF : i ∈ F
      · rw [hfixed i hiF]
        exact ⟨hLpos, le_rfl⟩
      · have hiS : i ∈ S := Finset.mem_sdiff.mpr ⟨hi, hiF⟩
        exact ⟨(hrec.2.1 i hiS).1,
          (hrec.2.1 i hiS).2.trans (Finset.card_le_card hSL)⟩
    · intro ℓ
      by_cases hℓ : L.card ≤ ℓ
      · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hℓ
      · have hsub :
            L.filter (fun i => classLoop P X b y fuel S upd i ≤ ℓ) ⊆
            S.filter (fun i => classLoop P X b y fuel S upd i ≤ ℓ) := by
          intro i hi
          obtain ⟨hiL, hiℓ⟩ := Finset.mem_filter.mp hi
          have hiF : i ∉ F := by
            intro hiF
            rw [hfixed i hiF] at hiℓ
            exact hℓ hiℓ
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiL, hiF⟩, hiℓ⟩
        exact (Finset.card_le_card hsub).trans (hrec.2.2 ℓ)

end MachineClassResearch

theorem solution {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin m → Fin n → Ω → ℝ) (b : ℝ) (y : Fin m → Fin n → ℝ)
    (hy : LPFeasible P X b y) :
    (∀ i, 1 ≤ machineClass P X b y i ∧ machineClass P X b y i ≤ m) ∧
    ∀ ℓ : ℕ, (Finset.univ.filter (fun i => machineClass P X b y i ≤ ℓ)).card ≤ ℓ := by
  have h := MachineClassResearch.loop_invariant P X b y hy m Finset.univ (fun _ => 0)
    (by simp)
  constructor
  · intro i
    simpa [machineClass] using h.2.1 i (Finset.mem_univ i)
  · exact h.2.2

#print axioms solution
