-- Prove2me | solution 1 for SteuerChoo.Discrete.nondominated_iff_augmented_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:36:52.846445+00:00
-- url     : https://prove2.me/submissions/70f6df95-1cb2-4dc7-a0ee-7e30af10f610

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

lemma aux_scnd_le_zstar {k : ℕ} {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {z : Fin k → ℝ} (hz : z ∈ Z) (i : Fin k) :
    z i ≤ zstar i := by
  obtain ⟨ε, hε0, hεmax, -⟩ := hideal
  obtain ⟨w, ⟨_, hw⟩, hwi⟩ := hεmax i
  have := hw z hz
  have := hε0 i
  linarith

lemma aux_scnd_mem_nd {k : ℕ} {Z : Finset (Fin k → ℝ)} {z : Fin k → ℝ} :
    z ∈ nondominated Z ↔ z ∈ Z ∧ ¬ ∃ w ∈ Z, Dominates w z := by
  unfold nondominated
  simp only [Finset.mem_filter]

lemma aux_scnd_ext {k : ℕ} {Z : Finset (Fin k → ℝ)} {z : Fin k → ℝ} (hz : z ∈ Z) :
    ∃ w ∈ nondominated Z, ∀ i, z i ≤ w i := by
  classical
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image (Z.filter (fun v => ∀ i, z i ≤ v i))
    (fun v => ∑ i, v i) ⟨z, Finset.mem_filter.2 ⟨hz, fun i => le_rfl⟩⟩
  rw [Finset.mem_filter] at hw
  refine ⟨w, aux_scnd_mem_nd.2 ⟨hw.1, ?_⟩, hw.2⟩
  rintro ⟨v, hv, hle, j, hj⟩
  have h1 : ∑ i, v i ≤ ∑ i, w i :=
    hmax v (Finset.mem_filter.2 ⟨hv, fun i => (hw.2 i).trans (hle i)⟩)
  have h2 : ∑ i, w i < ∑ i, v i :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ _, hj⟩
  linarith

lemma aux_scnd_tight {k : ℕ} {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zi : Fin k → ℝ} (hzi : zi ∈ Z) {m : Fin k}
    (hm : zi m = zstar m) : (∀ v ∈ Z, v m ≤ zstar m) ∧ ¬ (CondI Z m ∨ CondII Z m) := by
  obtain ⟨ε, hε0, hεmax, hεpos⟩ := hideal
  obtain ⟨w, ⟨_, hw⟩, hwi⟩ := hεmax m
  have h1 := hw zi hzi
  have h2 := hε0 m
  refine ⟨fun v hv => ?_, fun h => ?_⟩
  · have := hw v hv
    linarith
  · have := hεpos m h
    linarith

lemma aux_scnd_uniq {k : ℕ} {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zi : Fin k → ℝ} (hzi : zi ∈ nondominated Z)
    {m1 m2 : Fin k} (h1 : zi m1 = zstar m1) (h2 : zi m2 = zstar m2) : m1 = m2 := by
  classical
  by_contra hne
  have hziZ : zi ∈ Z := (aux_scnd_mem_nd.1 hzi).1
  obtain ⟨hmax1, hnot⟩ := aux_scnd_tight hideal hziZ h1
  obtain ⟨hmax2, -⟩ := aux_scnd_tight hideal hziZ h2
  have hM1 : MaximizesObj Z m1 zi := ⟨hziZ, fun w hw => by rw [h1]; exact hmax1 w hw⟩
  have hM2 : MaximizesObj Z m2 zi := ⟨hziZ, fun w hw => by rw [h2]; exact hmax2 w hw⟩
  apply hnot
  by_cases hex : ∃ w ∈ nondominated Z, w ≠ zi ∧ MaximizesObj Z m1 w
  · obtain ⟨w, hw, hne', hMw⟩ := hex
    left
    exact ⟨zi, hzi, w, hw, fun h => hne' h.symm, hM1, hMw⟩
  · right
    refine ⟨zi, hzi, hM1, fun w hw hMw => ?_, m2, fun h => hne h.symm, hM2⟩
    by_contra hwne
    exact hex ⟨w, hw, hwne, hMw⟩

lemma aux_scnd_alpha {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zi zj : Fin k → ℝ} (hzi : zi ∈ nondominated Z)
    (hzj : zj ∈ Z) :
    alphaPQ zstar zi zi ≤ alphaPQ zstar zi zj ∧
      (0 < ∑ i, (zj i - zi i) → alphaPQ zstar zi zi < alphaPQ zstar zi zj) := by
  classical
  have hziZ := (aux_scnd_mem_nd.1 hzi).1
  have hnd := (aux_scnd_mem_nd.1 hzi).2
  have key : ∀ i, lamP zstar zi i * (zstar i - zj i) ≤ alphaPQ zstar zi zj := fun i =>
    Finset.le_sup' (fun i => lamP zstar zi i * (zstar i - zj i)) (Finset.mem_univ i)
  by_cases hA : ∀ j, zi j ≠ zstar j
  · have hd : ∀ j, 0 < zstar j - zi j := fun j =>
      lt_of_le_of_ne (sub_nonneg.2 (aux_scnd_le_zstar hideal hziZ j))
        (fun h => hA j (by linarith))
    set s := ∑ j, 1 / (zstar j - zi j) with hs
    have hspos : 0 < s :=
      Finset.sum_pos (fun j _ => by have := hd j; positivity) Finset.univ_nonempty
    have hlam : ∀ i, lamP zstar zi i = 1 / (zstar i - zi i) * s⁻¹ := fun i => by
      unfold lamP
      rw [if_pos hA]
    have hterm_i : ∀ i, lamP zstar zi i * (zstar i - zi i) = s⁻¹ := fun i => by
      rw [hlam]
      have := hd i
      field_simp
    have hii : alphaPQ zstar zi zi = s⁻¹ := by
      unfold alphaPQ tcheb
      simp only [hterm_i]
      exact Finset.sup'_const _ _
    have hcmp : ∀ i, lamP zstar zi i * (zstar i - zj i) ≤ s⁻¹ → zi i ≤ zj i := by
      intro i h
      rw [hlam] at h
      have hdi := hd i
      have h' : (zstar i - zj i) * (1 / (zstar i - zi i) * s⁻¹) ≤
          (zstar i - zi i) * (1 / (zstar i - zi i) * s⁻¹) := by
        have : (zstar i - zi i) * (1 / (zstar i - zi i) * s⁻¹) = s⁻¹ := by
          field_simp
        rw [this]; linarith
      have hp : 0 < 1 / (zstar i - zi i) * s⁻¹ := by positivity
      have := le_of_mul_le_mul_right h' hp
      linarith
    have hcmp' : ∀ i, lamP zstar zi i * (zstar i - zj i) < s⁻¹ → zi i < zj i := by
      intro i h
      rw [hlam] at h
      have hdi := hd i
      have h' : (zstar i - zj i) * (1 / (zstar i - zi i) * s⁻¹) <
          (zstar i - zi i) * (1 / (zstar i - zi i) * s⁻¹) := by
        have : (zstar i - zi i) * (1 / (zstar i - zi i) * s⁻¹) = s⁻¹ := by
          field_simp
        rw [this]; linarith
      have hp : 0 < 1 / (zstar i - zi i) * s⁻¹ := by positivity
      have := lt_of_mul_lt_mul_right h' hp.le
      linarith
    refine ⟨?_, fun hsum => ?_⟩
    · by_contra hlt
      push Not at hlt
      rw [hii] at hlt
      apply hnd
      refine ⟨zj, hzj, fun i => (hcmp' i (lt_of_le_of_lt (key i) hlt)).le, 0,
        hcmp' 0 (lt_of_le_of_lt (key 0) hlt)⟩
    · by_contra hle
      push Not at hle
      rw [hii] at hle
      have hall : ∀ i, zi i ≤ zj i := fun i => hcmp i (le_trans (key i) hle)
      apply hnd
      refine ⟨zj, hzj, hall, ?_⟩
      by_contra hno
      push Not at hno
      have : ∑ i, (zj i - zi i) ≤ 0 :=
        Finset.sum_nonpos (fun i _ => by linarith [hno i])
      linarith
  · push Not at hA
    obtain ⟨m0, hm0⟩ := hA
    have hlam : ∀ i, lamP zstar zi i = if zi i = zstar i then 1 else 0 := fun i => by
      unfold lamP
      rw [if_neg (by push Not; exact ⟨m0, hm0⟩)]
    have hterm_i : ∀ i, lamP zstar zi i * (zstar i - zi i) = 0 := fun i => by
      rw [hlam]
      split_ifs with h
      · rw [h]; ring
      · ring
    have hii : alphaPQ zstar zi zi = 0 := by
      unfold alphaPQ tcheb
      simp only [hterm_i]
      exact Finset.sup'_const _ _
    have hkm0 : zstar m0 - zj m0 ≤ alphaPQ zstar zi zj := by
      have := key m0
      rw [hlam, if_pos hm0, one_mul] at this
      exact this
    have hzj0 := aux_scnd_le_zstar hideal hzj m0
    refine ⟨by rw [hii]; linarith, fun hsum => ?_⟩
    rw [hii]
    by_contra hle
    push Not at hle
    have heq : zj m0 = zstar m0 := by linarith
    obtain ⟨hmax, hnot⟩ := aux_scnd_tight hideal hziZ hm0
    obtain ⟨w, hwN, hw⟩ := aux_scnd_ext hzj
    have hwZ := (aux_scnd_mem_nd.1 hwN).1
    have hMzi : MaximizesObj Z m0 zi := ⟨hziZ, fun v hv => by rw [hm0]; exact hmax v hv⟩
    have hMw : MaximizesObj Z m0 w :=
      ⟨hwZ, fun v hv => by have := hmax v hv; have := hw m0; linarith⟩
    by_cases hwe : w = zi
    · subst hwe
      have : ∑ i, (zj i - w i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [hw i])
      linarith
    · exact hnot (Or.inl ⟨zi, hzi, w, hwN, fun h => hwe h.symm, hMzi, hMw⟩)

lemma aux_scnd_simplex {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zi : Fin k → ℝ} (hzi : zi ∈ nondominated Z) :
    lamP zstar zi ∈ stdSimplex ℝ (Fin k) := by
  classical
  have hziZ := (aux_scnd_mem_nd.1 hzi).1
  by_cases hA : ∀ j, zi j ≠ zstar j
  · have hd : ∀ j, 0 < zstar j - zi j := fun j =>
      lt_of_le_of_ne (sub_nonneg.2 (aux_scnd_le_zstar hideal hziZ j))
        (fun h => hA j (by linarith))
    set s := ∑ j, 1 / (zstar j - zi j) with hs
    have hspos : 0 < s :=
      Finset.sum_pos (fun j _ => by have := hd j; positivity) Finset.univ_nonempty
    have hlam : ∀ i, lamP zstar zi i = 1 / (zstar i - zi i) * s⁻¹ := fun i => by
      unfold lamP
      rw [if_pos hA]
    refine ⟨fun i => ?_, ?_⟩
    · rw [hlam]
      have := hd i
      positivity
    · simp only [hlam]
      rw [← Finset.sum_mul, ← hs, mul_inv_cancel₀ hspos.ne']
  · push Not at hA
    obtain ⟨m0, hm0⟩ := hA
    have hlam : ∀ i, lamP zstar zi i = if i = m0 then 1 else 0 := fun i => by
      unfold lamP
      rw [if_neg (by push Not; exact ⟨m0, hm0⟩)]
      by_cases h : zi i = zstar i
      · rw [if_pos h, if_pos (aux_scnd_uniq hideal hzi h hm0)]
      · rw [if_neg h, if_neg (fun he => h (by rw [he]; exact hm0))]
    refine ⟨fun i => ?_, ?_⟩
    · rw [hlam]
      split_ifs <;> norm_num
    · simp only [hlam]
      simp

lemma aux_scnd_rho_pos {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) : 0 < rho38 Z zstar := by
  classical
  unfold rho38
  dsimp only
  split_ifs with h
  · apply mul_pos (by norm_num)
    rw [Finset.lt_inf'_iff]
    intro pr hpr
    rw [Finset.mem_filter, Finset.mem_product] at hpr
    obtain ⟨⟨h1, h2⟩, h3⟩ := hpr
    exact div_pos (sub_pos.2 ((aux_scnd_alpha hideal h1 h2).2 h3)) h3
  · norm_num

lemma aux_scnd_rho_le {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    {zp z : Fin k → ℝ} (hzp : zp ∈ nondominated Z) (hz : z ∈ Z)
    (hs : 0 < ∑ i, (z i - zp i)) :
    rho38 Z zstar ≤
      (1 / 2) * ((alphaPQ zstar zp z - alphaPQ zstar zp zp) / ∑ i, (z i - zp i)) := by
  unfold rho38
  dsimp only
  have hm : (zp, z) ∈ {pr ∈ nondominated Z ×ˢ Z | 0 < ∑ i, (pr.2 i - pr.1 i)} :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hzp, hz⟩, hs⟩
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact Finset.inf'_le _ hm
  · exact absurd ⟨_, hm⟩ h

end SteuerChoo.Discrete

open SteuerChoo.Discrete

theorem solution {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ))
    (zstar : Fin k → ℝ) (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hzp : zp ∈ Z) :
    zp ∈ nondominated Z ↔
      ∃ lam ∈ stdSimplex ℝ (Fin k),
        ∀ z ∈ Z, augTcheb lam (rho38 Z zstar) zstar zp ≤ augTcheb lam (rho38 Z zstar) zstar z := by
  have hρ := aux_scnd_rho_pos hideal
  constructor
  · intro hN
    refine ⟨lamP zstar zp, aux_scnd_simplex hideal hN, fun z hz => ?_⟩
    show alphaPQ zstar zp zp + rho38 Z zstar * ∑ i, (zstar i - zp i) ≤
      alphaPQ zstar zp z + rho38 Z zstar * ∑ i, (zstar i - z i)
    have hsum : ∑ i, (zstar i - zp i) = ∑ i, (zstar i - z i) + ∑ i, (z i - zp i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hsum' : rho38 Z zstar * ∑ i, (zstar i - zp i) =
        rho38 Z zstar * ∑ i, (zstar i - z i) + rho38 Z zstar * ∑ i, (z i - zp i) := by
      rw [hsum, mul_add]
    obtain ⟨h1, h2⟩ := aux_scnd_alpha hideal hN hz
    by_cases hs : 0 < ∑ i, (z i - zp i)
    · have hle := aux_scnd_rho_le (zstar := zstar) hN hz hs
      have : rho38 Z zstar * ∑ i, (z i - zp i) ≤
          (alphaPQ zstar zp z - alphaPQ zstar zp zp) / 2 := by
        calc _ ≤ (1 / 2) * ((alphaPQ zstar zp z - alphaPQ zstar zp zp) /
              ∑ i, (z i - zp i)) * ∑ i, (z i - zp i) := mul_le_mul_of_nonneg_right hle hs.le
          _ = _ := by field_simp
      linarith
    · push Not at hs
      have : rho38 Z zstar * ∑ i, (z i - zp i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hρ.le hs
      linarith
  · rintro ⟨lam, hlam, hmin⟩
    rw [aux_scnd_mem_nd]
    refine ⟨hzp, ?_⟩
    rintro ⟨z, hz, hle, j, hj⟩
    have h := hmin z hz
    have ht : tcheb lam zstar z ≤ tcheb lam zstar zp := by
      unfold tcheb
      apply Finset.sup'_le
      intro i _
      exact le_trans (mul_le_mul_of_nonneg_left (by linarith [hle i]) (hlam.1 i))
        (Finset.le_sup' (fun i => lam i * (zstar i - zp i)) (Finset.mem_univ i))
    have hs : ∑ i, (zstar i - z i) < ∑ i, (zstar i - zp i) :=
      Finset.sum_lt_sum (fun i _ => by linarith [hle i]) ⟨j, Finset.mem_univ _, by linarith⟩
    unfold augTcheb at h
    have := mul_lt_mul_of_pos_left hs hρ
    linarith
