-- Prove2me | solution 1 for SmaleNinth.khachiyan_feasibility_equiv
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:12:44.690522+00:00
-- url     : https://prove2.me/submissions/e0da2d69-daa4-4335-98bc-1958d577921c

import Mathlib
import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_Khachiyan
import Theorems.Thm_SmaleNinth_integer_polyhedron_solution_bound
import Theorems.Thm_SmaleNinth_khachiyan_nonempty_imp

open Matrix LinearOptimization

namespace FeasAux

variable {m n : ℕ} {U : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ}

lemma eps_pos (n U : ℕ) (hU : 1 ≤ U) : 0 < SmaleNinth.khachiyanEps n U := by
  unfold SmaleNinth.khachiyanEps
  have : (0:ℝ) < (U : ℝ) := by exact_mod_cast hU
  positivity

/-- On the first `m` rows the perturbed system agrees with `A` cast to `ℝ`. -/
lemma mulVec_lt_m (x : Fin n → ℝ) (i : Fin (m + n + n)) (hi : (i : ℕ) < m) :
    (SmaleNinth.khachiyanSystemA A).mulVec x i
      = (A.map (Int.cast : ℤ → ℝ)).mulVec x ⟨(i : ℕ), hi⟩ := by
  simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA, dif_pos hi,
    Matrix.map_apply]

/-- Forward direction: a feasible integer system stays feasible after perturbing and boxing. -/
lemma perturbed_nonempty_of_nonempty (hU : 1 ≤ U)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hne : (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty) :
    (polyhedron (SmaleNinth.khachiyanSystemA A)
      (SmaleNinth.khachiyanSystemb n U b)).Nonempty := by
  obtain ⟨x, hxmem, hxbd⟩ :=
    SmaleNinth.integer_polyhedron_solution_bound U hU A b hA hb hne
  refine ⟨x, ?_⟩
  intro i
  rcases lt_or_ge (i : ℕ) m with hi | hi
  · -- original row: the perturbation only relaxes it
    have hb' : SmaleNinth.khachiyanSystemb n U b i
        = ((b ⟨(i : ℕ), hi⟩ : ℤ) : ℝ) - SmaleNinth.khachiyanEps n U := by
      simp [SmaleNinth.khachiyanSystemb, dif_pos hi]
    have hrow : ((b ⟨(i : ℕ), hi⟩ : ℤ) : ℝ)
        ≤ (A.map (Int.cast : ℤ → ℝ)).mulVec x ⟨(i : ℕ), hi⟩ := hxmem _
    rw [hb', mulVec_lt_m x i hi]
    have := eps_pos n U hU
    linarith
  · -- a box row
    have hb' : SmaleNinth.khachiyanSystemb n U b i = -(SmaleNinth.khachiyanBox n U) := by
      have hnlt : ¬ ((i : ℕ) < m) := by omega
      simp [SmaleNinth.khachiyanSystemb, dif_neg hnlt]
    rw [hb']
    rcases lt_or_ge (i : ℕ) (m + n) with hi2 | hi2
    · -- `x j ≥ -M`
      have hjlt : (i : ℕ) - m < n := by omega
      have hval : (SmaleNinth.khachiyanSystemA A).mulVec x i = x ⟨(i : ℕ) - m, hjlt⟩ := by
        have hnlt : ¬ ((i : ℕ) < m) := by omega
        simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA,
          dif_neg hnlt, if_pos hi2]
        rw [Finset.sum_eq_single (⟨(i : ℕ) - m, hjlt⟩ : Fin n)]
        · simp
        · intro k _ hk
          have : (k : ℕ) ≠ (i : ℕ) - m := fun hc => hk (Fin.ext hc)
          simp [this]
        · simp
      rw [hval]
      have := hxbd ⟨(i : ℕ) - m, hjlt⟩
      unfold SmaleNinth.khachiyanBox
      rw [abs_le] at this
      linarith [this.1]
    · -- `-x j ≥ -M`
      have hjlt : (i : ℕ) - m - n < n := by omega
      have hval : (SmaleNinth.khachiyanSystemA A).mulVec x i = -x ⟨(i : ℕ) - m - n, hjlt⟩ := by
        have hnlt : ¬ ((i : ℕ) < m) := by omega
        have hnlt2 : ¬ ((i : ℕ) < m + n) := by omega
        simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA,
          dif_neg hnlt, if_neg hnlt2]
        rw [Finset.sum_eq_single (⟨(i : ℕ) - m - n, hjlt⟩ : Fin n)]
        · simp
        · intro k _ hk
          have : (k : ℕ) ≠ (i : ℕ) - m - n := fun hc => hk (Fin.ext hc)
          simp [this]
        · simp
      rw [hval]
      have := hxbd ⟨(i : ℕ) - m - n, hjlt⟩
      unfold SmaleNinth.khachiyanBox
      rw [abs_le] at this
      linarith [this.2]

end FeasAux

open FeasAux

theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty ↔
      (polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty :=
  ⟨fun hne => perturbed_nonempty_of_nonempty hU hA hb hne,
   SmaleNinth.khachiyan_nonempty_imp U hU hn A b hA hb⟩
