-- Prove2me | solution 1 for SmaleNinth.khachiyan_volume_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:21:08.876679+00:00
-- url     : https://prove2.me/submissions/93029392-b7f0-43ac-9af7-a07d3de6a524

import Mathlib
import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_Khachiyan
import Theorems.Thm_SmaleNinth_integer_polyhedron_solution_bound
import Theorems.Thm_SmaleNinth_khachiyan_nonempty_imp

open Matrix LinearOptimization MeasureTheory

namespace VolAux

/-- Half the side of the cube placed around a small solution. -/
noncomputable def halfSide (n U : ℕ) : ℝ :=
  SmaleNinth.khachiyanEps n U / (2 * (n : ℝ) * (U : ℝ))

lemma halfSide_pos {n U : ℕ} (hn : 1 ≤ n) (hU : 1 ≤ U) : 0 < halfSide n U := by
  unfold halfSide SmaleNinth.khachiyanEps
  have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU' : (0:ℝ) < (U : ℝ) := by exact_mod_cast hU
  positivity

/-- The cube of half-side `halfSide n U` around `x₀`. -/
noncomputable def cube (n U : ℕ) (x₀ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi fun j => Set.Icc (x₀ j - halfSide n U) (x₀ j + halfSide n U)

lemma volume_cube {n U : ℕ} (hn : 1 ≤ n) (hU : 1 ≤ U) (x₀ : Fin n → ℝ) :
    volume (cube n U x₀) = ENNReal.ofReal ((2 * halfSide n U) ^ n) := by
  have hpos := halfSide_pos (n := n) (U := U) hn hU
  rw [cube, volume_pi_pi]
  have hstep : ∀ j : Fin n,
      volume (Set.Icc (x₀ j - halfSide n U) (x₀ j + halfSide n U))
        = ENNReal.ofReal (2 * halfSide n U) := by
    intro j
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [Finset.prod_congr rfl fun j _ => hstep j, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by positivity)]

/-- The cube's volume is exactly the Khachiyan lower bound. -/
lemma cube_volume_eq_bound {n U : ℕ} (hn : 1 ≤ n) (hU : 1 ≤ U) (x₀ : Fin n → ℝ) :
    volume (cube n U x₀) = ENNReal.ofReal (SmaleNinth.khachiyanVolLB n U) := by
  rw [volume_cube hn hU]
  congr 1
  unfold SmaleNinth.khachiyanVolLB halfSide
  have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU' : (0:ℝ) < (U : ℝ) := by exact_mod_cast hU
  congr 1
  field_simp


lemma eps_le_one {n U : ℕ} (hn : 1 ≤ n) (hU : 1 ≤ U) :
    SmaleNinth.khachiyanEps n U ≤ 1 := by
  unfold SmaleNinth.khachiyanEps
  have hn' : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hU' : (1:ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have hf : (1:ℝ) ≤ (((n + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast (n + 1).factorial_pos
  have hp : (1:ℝ) ≤ (U : ℝ) ^ (n + 1) := one_le_pow₀ hU'
  rw [div_le_one (by positivity)]
  have hprod : (1:ℝ) ≤ (((n + 1).factorial : ℕ) : ℝ) * (U : ℝ) ^ (n + 1) := by
    have := mul_le_mul hf hp (by norm_num) (by linarith)
    rwa [one_mul] at this
  nlinarith [hprod, hn']

lemma halfSide_le_one {n U : ℕ} (hn : 1 ≤ n) (hU : 1 ≤ U) : halfSide n U ≤ 1 := by
  unfold halfSide
  have hn' : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hU' : (1:ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have he := eps_le_one (n := n) (U := U) hn hU
  have hepos : 0 < SmaleNinth.khachiyanEps n U := by
    unfold SmaleNinth.khachiyanEps; positivity
  rw [div_le_one (by positivity)]
  nlinarith

/-- The cube around a small solution of the original system sits inside the
perturbed-and-boxed polyhedron. -/
lemma cube_subset {m n U : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ}
    (hn : 1 ≤ n) (hU : 1 ≤ U) (hA : ∀ i j, |A i j| ≤ (U : ℤ))
    (x₀ : Fin n → ℝ)
    (hx₀ : x₀ ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)))
    (hbd : ∀ j, |x₀ j| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n) :
    cube n U x₀ ⊆ polyhedron (SmaleNinth.khachiyanSystemA A)
      (SmaleNinth.khachiyanSystemb n U b) := by
  intro x hxc
  have hclose : ∀ j, |x j - x₀ j| ≤ halfSide n U := by
    intro j
    have := hxc j (Set.mem_univ j)
    rw [Set.mem_Icc] at this
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  have hn' : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hU' : (1:ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have hδpos := halfSide_pos (n := n) (U := U) hn hU
  intro i
  rcases lt_or_ge (i : ℕ) m with hi | hi
  · -- an original row, relaxed by ε
    have hb' : SmaleNinth.khachiyanSystemb n U b i
        = ((b ⟨(i : ℕ), hi⟩ : ℤ) : ℝ) - SmaleNinth.khachiyanEps n U := by
      simp [SmaleNinth.khachiyanSystemb, dif_pos hi]
    have hAeq : (SmaleNinth.khachiyanSystemA A).mulVec x i
        = (A.map (Int.cast : ℤ → ℝ)).mulVec x ⟨(i : ℕ), hi⟩ := by
      simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA, dif_pos hi,
        Matrix.map_apply]
    rw [hb', hAeq]
    set i' : Fin m := ⟨(i : ℕ), hi⟩
    have horig : ((b i' : ℤ) : ℝ) ≤ (A.map (Int.cast : ℤ → ℝ)).mulVec x₀ i' := hx₀ i'
    -- the perturbation absorbs the displacement
    have hdiff : |(A.map (Int.cast : ℤ → ℝ)).mulVec x i'
        - (A.map (Int.cast : ℤ → ℝ)).mulVec x₀ i'| ≤ (n : ℝ) * (U : ℝ) * halfSide n U := by
      have hexp : (A.map (Int.cast : ℤ → ℝ)).mulVec x i'
          - (A.map (Int.cast : ℤ → ℝ)).mulVec x₀ i'
          = ∑ j, ((A i' j : ℤ) : ℝ) * (x j - x₀ j) := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hexp]
      calc |∑ j, ((A i' j : ℤ) : ℝ) * (x j - x₀ j)|
          ≤ ∑ j, |((A i' j : ℤ) : ℝ) * (x j - x₀ j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin n, (U : ℝ) * halfSide n U := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have h1 : |((A i' j : ℤ) : ℝ)| ≤ (U : ℝ) := by
              have := hA i' j
              rw [← Int.cast_abs]
              exact_mod_cast this
            exact mul_le_mul h1 (hclose j) (abs_nonneg _) (by linarith)
        _ = (n : ℝ) * ((U : ℝ) * halfSide n U) := by
            simp [Finset.sum_const, Finset.card_univ, mul_comm]
        _ = (n : ℝ) * (U : ℝ) * halfSide n U := by ring
    have hhalf : (n : ℝ) * (U : ℝ) * halfSide n U
        = SmaleNinth.khachiyanEps n U / 2 := by
      unfold halfSide
      field_simp
    rw [abs_le] at hdiff
    rw [hhalf] at hdiff
    linarith [hdiff.1, horig]
  · -- a box row
    have hb' : SmaleNinth.khachiyanSystemb n U b i = -(SmaleNinth.khachiyanBox n U) := by
      have hnlt : ¬ ((i : ℕ) < m) := by omega
      simp [SmaleNinth.khachiyanSystemb, dif_neg hnlt]
    rw [hb']
    have hδ1 := halfSide_le_one (n := n) (U := U) hn hU
    rcases lt_or_ge (i : ℕ) (m + n) with hi2 | hi2
    · have hjlt : (i : ℕ) - m < n := by omega
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
      set j : Fin n := ⟨(i : ℕ) - m, hjlt⟩
      have h1 := hbd j
      have h2 := hclose j
      rw [abs_le] at h1 h2
      unfold SmaleNinth.khachiyanBox
      linarith [h1.1, h2.1]
    · have hjlt : (i : ℕ) - m - n < n := by omega
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
      set j : Fin n := ⟨(i : ℕ) - m - n, hjlt⟩
      have h1 := hbd j
      have h2 := hclose j
      rw [abs_le] at h1 h2
      unfold SmaleNinth.khachiyanBox
      linarith [h1.2, h2.2]

end VolAux

open VolAux

theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    (polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty →
      ENNReal.ofReal (SmaleNinth.khachiyanVolLB n U) ≤
        MeasureTheory.volume (polyhedron (SmaleNinth.khachiyanSystemA A)
          (SmaleNinth.khachiyanSystemb n U b)) := by
  intro hpert
  have horig := SmaleNinth.khachiyan_nonempty_imp U hU hn A b hA hb hpert
  obtain ⟨x₀, hx₀mem, hx₀bd⟩ :=
    SmaleNinth.integer_polyhedron_solution_bound U hU A b hA hb horig
  have hsub := cube_subset (A := A) (b := b) hn hU hA x₀ hx₀mem hx₀bd
  calc ENNReal.ofReal (SmaleNinth.khachiyanVolLB n U)
      = MeasureTheory.volume (cube n U x₀) := (cube_volume_eq_bound hn hU x₀).symm
    _ ≤ MeasureTheory.volume (polyhedron (SmaleNinth.khachiyanSystemA A)
          (SmaleNinth.khachiyanSystemb n U b)) := measure_mono hsub
