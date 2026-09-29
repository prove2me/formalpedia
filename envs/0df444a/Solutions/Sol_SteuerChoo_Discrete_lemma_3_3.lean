-- Prove2me | solution 1 for SteuerChoo.Discrete.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:25:05.033835+00:00
-- url     : https://prove2.me/submissions/2121aa91-0cce-4be2-b3d3-f77507ddf039

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- Membership in the nondominated set. -/
theorem aux_sc33_mem_nondominated {k : ℕ} (Z : Finset (Fin k → ℝ)) (w : Fin k → ℝ) :
    w ∈ nondominated Z ↔ w ∈ Z ∧ ¬ ∃ z ∈ Z, Dominates z w := by
  classical
  unfold nondominated
  simp only [Finset.mem_filter]

/-- Every element of a finite set is below (componentwise) some nondominated element. -/
theorem aux_sc33_exists_nd_above {k : ℕ} (Z : Finset (Fin k → ℝ)) (zq : Fin k → ℝ)
    (hq : zq ∈ Z) : ∃ w ∈ nondominated Z, zq ≤ w := by
  classical
  set S := Z.filter (fun z => zq ≤ z) with hS
  have hqS : zq ∈ S := Finset.mem_filter.mpr ⟨hq, le_rfl⟩
  obtain ⟨w, hwS, hwmax⟩ := Finset.exists_max_image S (fun z => ∑ i, z i) ⟨zq, hqS⟩
  have hwZ : w ∈ Z := (Finset.mem_filter.mp hwS).1
  have hqw : zq ≤ w := (Finset.mem_filter.mp hwS).2
  refine ⟨w, (aux_sc33_mem_nondominated Z w).mpr ⟨hwZ, ?_⟩, hqw⟩
  rintro ⟨z, hzZ, hwz, i, hi⟩
  have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hzZ, le_trans hqw (fun j => hwz j)⟩
  have h1 := hwmax z hzS
  have h2 : ∑ j, w j < ∑ j, z j :=
    Finset.sum_lt_sum (fun j _ => hwz j) ⟨i, Finset.mem_univ i, hi⟩
  linarith

end SteuerChoo.Discrete

open SteuerChoo.Discrete

theorem solution {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) (hne : zq ≠ zp) (hnle : ¬ zq ≤ zp) :
    alphaPQ zstar zp zp < alphaPQ zstar zp zq := by
  classical
  obtain ⟨ε, hε0, hεmax, hεpos⟩ := hideal
  have hle : ∀ i, ∀ w ∈ Z, w i ≤ zstar i := by
    intro i w hw
    obtain ⟨z, ⟨_, hz⟩, hzi⟩ := hεmax i
    have := hz w hw
    linarith [hε0 i]
  have hpZ : zp ∈ Z := ((aux_sc33_mem_nondominated Z zp).mp hp).1
  have hpnd : ¬ ∃ z ∈ Z, Dominates z zp := ((aux_sc33_mem_nondominated Z zp).mp hp).2
  have hj : ∃ j, zq j < zp j := by
    by_contra h
    push_neg at h
    apply hpnd
    refine ⟨zq, hq, h, ?_⟩
    by_contra h2
    push_neg at h2
    exact hnle (fun i => h2 i)
  obtain ⟨j, hjlt⟩ := hj
  unfold alphaPQ tcheb lamP
  by_cases hall : ∀ j, zp j ≠ zstar j
  · simp only [hall, ne_eq, not_false_eq_true, implies_true, if_true]
    have hd : ∀ i, 0 < zstar i - zp i := by
      intro i
      have h1 := hle i zp hpZ
      have h2 := hall i
      have : zp i < zstar i := lt_of_le_of_ne h1 h2
      linarith
    set S := ∑ j, 1 / (zstar j - zp j) with hSdef
    have hSpos : 0 < S := by
      apply Finset.sum_pos
      · intro i _
        exact one_div_pos.mpr (hd i)
      · exact Finset.univ_nonempty
    have hpp : Finset.univ.sup' Finset.univ_nonempty
        (fun i => 1 / (zstar i - zp i) * S⁻¹ * (zstar i - zp i)) ≤ S⁻¹ := by
      apply Finset.sup'_le
      intro i _
      have := (hd i).ne'
      field_simp
      rfl
    refine lt_of_le_of_lt hpp (lt_of_lt_of_le ?_ (Finset.le_sup' _ (Finset.mem_univ j)))
    show S⁻¹ < 1 / (zstar j - zp j) * S⁻¹ * (zstar j - zq j)
    have hdj := hd j
    have hcoef : 0 < 1 / (zstar j - zp j) * S⁻¹ :=
      mul_pos (one_div_pos.mpr hdj) (inv_pos.mpr hSpos)
    have heq : 1 / (zstar j - zp j) * S⁻¹ * (zstar j - zp j) = S⁻¹ := by
      field_simp
    calc S⁻¹ = 1 / (zstar j - zp j) * S⁻¹ * (zstar j - zp j) := heq.symm
      _ < 1 / (zstar j - zp j) * S⁻¹ * (zstar j - zq j) := by
        apply mul_lt_mul_of_pos_left _ hcoef
        linarith
  · simp only [hall, if_false]
    push_neg at hall
    obtain ⟨j0, hj0⟩ := hall
    -- find i0 with zp i0 = zstar i0 and zq i0 < zstar i0
    have hi0 : ∃ i0, zp i0 = zstar i0 ∧ zq i0 < zstar i0 := by
      by_contra hcon
      push_neg at hcon
      have hqj0 : zstar j0 ≤ zq j0 := hcon j0 hj0
      obtain ⟨w, hwN, hqw⟩ := aux_sc33_exists_nd_above Z zq hq
      have hwZ : w ∈ Z := ((aux_sc33_mem_nondominated Z w).mp hwN).1
      have hwp : zp ≠ w := by
        rintro rfl
        exact hnle hqw
      have hcond : CondI Z j0 := by
        refine ⟨zp, hp, w, hwN, hwp, ⟨hpZ, ?_⟩, ⟨hwZ, ?_⟩⟩
        · intro v hv
          rw [hj0]
          exact hle j0 v hv
        · intro v hv
          have h1 := hle j0 v hv
          have h2 := hqw j0
          linarith
      have hεj0 := hεpos j0 (Or.inl hcond)
      obtain ⟨z, ⟨hzZ, hz⟩, hzi⟩ := hεmax j0
      have := hz zp hpZ
      linarith
    obtain ⟨i0, hpi0, hqi0⟩ := hi0
    have hpp : Finset.univ.sup' Finset.univ_nonempty
        (fun i => (if zp i = zstar i then (1 : ℝ) else 0) * (zstar i - zp i)) ≤ 0 := by
      apply Finset.sup'_le
      intro i _
      by_cases h : zp i = zstar i
      · simp [h]
      · simp [h]
    refine lt_of_le_of_lt hpp (lt_of_lt_of_le ?_ (Finset.le_sup' _ (Finset.mem_univ i0)))
    show (0 : ℝ) < (if zp i0 = zstar i0 then (1 : ℝ) else 0) * (zstar i0 - zq i0)
    rw [if_pos hpi0]
    linarith
