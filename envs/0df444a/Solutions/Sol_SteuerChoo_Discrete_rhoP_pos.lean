-- Prove2me | solution 1 for SteuerChoo.Discrete.rhoP_pos
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:47:40.652183+00:00
-- url     : https://prove2.me/submissions/68858625-63d1-4998-8d0c-df8b7da32e9a

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

theorem aux_rp_key {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) (hs : 0 < ∑ i, (zq i - zp i)) :
    alphaPQ zstar zp zp < alphaPQ zstar zp zq := by
  classical
  obtain ⟨ε, hε0, hmax, hcond⟩ := hideal
  have hpZ : zp ∈ Z := (Finset.mem_filter.mp hp).1
  have hpN : ¬ ∃ z ∈ Z, Dominates z zp := (Finset.mem_filter.mp hp).2
  have hub : ∀ w ∈ Z, ∀ i, w i ≤ zstar i := by
    intro w hw i
    obtain ⟨z, ⟨hzZ, hz⟩, hzi⟩ := hmax i
    have := hz w hw
    have := hε0 i
    linarith
  have hlt : ∃ i, zq i < zp i := by
    by_contra h
    push Not at h
    apply hpN
    refine ⟨zq, hq, h, ?_⟩
    by_contra h2
    push Not at h2
    have : ∑ i, (zq i - zp i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [h2 i])
    linarith
  unfold alphaPQ tcheb
  by_cases hall : ∀ j, zp j ≠ zstar j
  · have hd : ∀ j, 0 < zstar j - zp j := fun j =>
      lt_of_le_of_ne (by linarith [hub zp hpZ j]) (fun h => hall j (by linarith))
    set S := ∑ j, 1 / (zstar j - zp j) with hS
    have hSpos : 0 < S :=
      Finset.sum_pos (fun j _ => by have := hd j; positivity) Finset.univ_nonempty
    have hlam : ∀ i, lamP zstar zp i = (1 / (zstar i - zp i)) * S⁻¹ := by
      intro i
      simp only [lamP]
      rw [if_pos hall]
    have hpp : Finset.univ.sup' Finset.univ_nonempty
        (fun i => lamP zstar zp i * (zstar i - zp i)) ≤ S⁻¹ := by
      apply Finset.sup'_le
      intro i _
      rw [hlam]
      have := hd i
      apply le_of_eq
      field_simp
    obtain ⟨i, hi⟩ := hlt
    have h1 : 1 < (zstar i - zq i) / (zstar i - zp i) := by
      rw [lt_div_iff₀ (hd i)]; linarith
    calc _ ≤ S⁻¹ := hpp
      _ < lamP zstar zp i * (zstar i - zq i) := by
        rw [hlam]
        have e : 1 / (zstar i - zp i) * S⁻¹ * (zstar i - zq i)
            = S⁻¹ * ((zstar i - zq i) / (zstar i - zp i)) := by ring
        rw [e]
        exact lt_mul_of_one_lt_right (inv_pos.mpr hSpos) h1
      _ ≤ _ := Finset.le_sup' (fun i => lamP zstar zp i * (zstar i - zq i)) (Finset.mem_univ i)
  · push Not at hall
    obtain ⟨j0, hj0⟩ := hall
    have hnall : ¬ ∀ j, zp j ≠ zstar j := fun h => h j0 hj0
    have hlam : ∀ i, lamP zstar zp i = if zp i = zstar i then 1 else 0 := by
      intro i
      simp only [lamP, hnall, if_false]
    have hpp : Finset.univ.sup' Finset.univ_nonempty
        (fun i => lamP zstar zp i * (zstar i - zp i)) ≤ 0 := by
      apply Finset.sup'_le
      intro i _
      rw [hlam]
      split_ifs with h
      · rw [h]; simp
      · simp
    have hex : ∃ i, zp i = zstar i ∧ zq i < zstar i := by
      by_contra hne
      push Not at hne
      obtain ⟨w, hw, hwmax⟩ := Finset.exists_max_image (Z.filter (fun w => ∀ j, zq j ≤ w j))
        (fun w => ∑ j, w j) ⟨zq, Finset.mem_filter.mpr ⟨hq, fun j => le_refl _⟩⟩
      obtain ⟨hwZ, hwge⟩ := Finset.mem_filter.mp hw
      have hwN : w ∈ nondominated Z := by
        refine Finset.mem_filter.mpr ⟨hwZ, ?_⟩
        rintro ⟨u, huZ, hle, ⟨m, hm⟩⟩
        have hu : u ∈ Z.filter (fun w => ∀ j, zq j ≤ w j) :=
          Finset.mem_filter.mpr ⟨huZ, fun j => (hwge j).trans (hle j)⟩
        have h1 := hwmax u hu
        have h2 : ∑ j, w j < ∑ j, u j :=
          Finset.sum_lt_sum (fun j _ => hle j) ⟨m, Finset.mem_univ _, hm⟩
        linarith
      have hzpmax : MaximizesObj Z j0 zp := ⟨hpZ, fun v hv => by rw [hj0]; exact hub v hv j0⟩
      have hwmax' : MaximizesObj Z j0 w :=
        ⟨hwZ, fun v hv => by linarith [hub v hv j0, hne j0 hj0, hwge j0]⟩
      have hε : ε j0 = 0 := by
        obtain ⟨z, ⟨hzZ, hz⟩, hzi⟩ := hmax j0
        have := hz zp hpZ
        have := hε0 j0
        linarith
      by_cases hwp : w = zp
      · rw [hwp] at hwge
        have : ∑ i, (zq i - zp i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [hwge i])
        linarith
      · have := hcond j0 (Or.inl ⟨w, hwN, zp, hp, hwp, hwmax', hzpmax⟩)
        linarith
    obtain ⟨i, hi1, hi2⟩ := hex
    calc _ ≤ 0 := hpp
      _ < lamP zstar zp i * (zstar i - zq i) := by rw [hlam, if_pos hi1]; linarith
      _ ≤ _ := Finset.le_sup' (fun i => lamP zstar zp i * (zstar i - zq i)) (Finset.mem_univ i)

end SteuerChoo.Discrete

open SteuerChoo.Discrete

theorem solution {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    0 < rhoP Z zstar zp := by
  classical
  unfold rhoP
  simp only
  split_ifs with h
  · apply mul_pos (by norm_num)
    rw [Finset.lt_inf'_iff]
    intro zq hzq
    obtain ⟨hqZ, hs⟩ := Finset.mem_filter.mp hzq
    exact div_pos (sub_pos.mpr (aux_rp_key Z zstar hideal zp hp zq hqZ hs)) hs
  · norm_num
