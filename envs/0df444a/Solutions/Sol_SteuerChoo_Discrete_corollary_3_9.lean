-- Prove2me | solution 1 for SteuerChoo.Discrete.corollary_3_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:53:28.995646+00:00
-- url     : https://prove2.me/submissions/79e4ea17-1238-48e5-8931-02e0de56f6f5

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

theorem aux_c39_le_zstar {k : ℕ} {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) : ∀ w ∈ Z, ∀ l, w l ≤ zstar l := by
  obtain ⟨ε, hε0, hmax, -⟩ := hideal
  intro w hw l
  obtain ⟨z, ⟨_, hz⟩, heq⟩ := hmax l
  have := hz w hw
  linarith [hε0 l]

theorem aux_c39_not_cond {k : ℕ} {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zi : Fin k → ℝ} (hzi : zi ∈ Z) {l : Fin k}
    (h : zi l = zstar l) : ¬ (CondI Z l ∨ CondII Z l) := by
  obtain ⟨ε, _, hmax, hpos⟩ := hideal
  intro hc
  have h1 := hpos l hc
  obtain ⟨z, ⟨_, hz⟩, heq⟩ := hmax l
  have := hz zi hzi
  linarith

theorem aux_c39_mem_Z {k : ℕ} {Z : Finset (Fin k → ℝ)} {z : Fin k → ℝ}
    (h : z ∈ nondominated Z) : z ∈ Z := by
  classical
  unfold nondominated at h
  exact (Finset.mem_filter.1 h).1

theorem aux_c39_nd {k : ℕ} {Z : Finset (Fin k → ℝ)} {z : Fin k → ℝ}
    (h : z ∈ nondominated Z) : ¬ ∃ w ∈ Z, Dominates w z := by
  classical
  unfold nondominated at h
  exact (Finset.mem_filter.1 h).2

theorem aux_c39_exists_nd {k : ℕ} (Z : Finset (Fin k → ℝ)) {zj : Fin k → ℝ} (hzj : zj ∈ Z) :
    ∃ z' ∈ nondominated Z, ∀ l, zj l ≤ z' l := by
  classical
  obtain ⟨z', hz'D, hmax⟩ := (Z.filter (fun w => ∀ l, zj l ≤ w l)).exists_max_image
    (fun w => ∑ i, w i) ⟨zj, Finset.mem_filter.2 ⟨hzj, fun l => le_rfl⟩⟩
  rw [Finset.mem_filter] at hz'D
  refine ⟨z', ?_, hz'D.2⟩
  unfold nondominated
  rw [Finset.mem_filter]
  refine ⟨hz'D.1, ?_⟩
  rintro ⟨w, hw, hle, i, hlt⟩
  have hwD : w ∈ Z.filter (fun w => ∀ l, zj l ≤ w l) :=
    Finset.mem_filter.2 ⟨hw, fun l => (hz'D.2 l).trans (hle l)⟩
  have h1 := hmax w hwD
  have h2 : ∑ i, z' i < ∑ i, w i :=
    Finset.sum_lt_sum (fun l _ => hle l) ⟨i, Finset.mem_univ _, hlt⟩
  linarith

theorem aux_c39_uniq {k : ℕ} {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zi : Fin k → ℝ} (hzi : zi ∈ nondominated Z) {l : Fin k}
    (hl : zi l = zstar l) {zj : Fin k → ℝ} (hzj : zj ∈ Z) (hjl : zstar l ≤ zj l)
    (hne : zj ≠ zi) : ∑ i, (zj i - zi i) < 0 := by
  have hle := aux_c39_le_zstar hideal
  obtain ⟨z', hz'N, hz'ge⟩ := aux_c39_exists_nd Z hzj
  have hz'Z := aux_c39_mem_Z hz'N
  have hziZ := aux_c39_mem_Z hzi
  have hz'l : z' l = zstar l := le_antisymm (hle z' hz'Z l) (hjl.trans (hz'ge l))
  have heq : z' = zi := by
    by_contra hne'
    apply aux_c39_not_cond hideal hziZ hl
    left
    refine ⟨z', hz'N, zi, hzi, hne', ⟨hz'Z, fun w hw => ?_⟩, ⟨hziZ, fun w hw => ?_⟩⟩
    · rw [hz'l]; exact hle w hw l
    · rw [hl]; exact hle w hw l
  subst heq
  obtain ⟨m, hm⟩ := Function.ne_iff.1 hne
  have := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hz'ge i)
    ⟨m, Finset.mem_univ _, lt_of_le_of_ne (hz'ge m) hm⟩
  rw [Finset.sum_sub_distrib]
  linarith

theorem aux_c39_key {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zi : Fin k → ℝ} (hzi : zi ∈ nondominated Z)
    {zj : Fin k → ℝ} (hzj : zj ∈ Z) (hne : zj ≠ zi) :
    tcheb (lamP zstar zi) zstar zi ≤ tcheb (lamP zstar zi) zstar zj ∧
      (tcheb (lamP zstar zi) zstar zj ≤ tcheb (lamP zstar zi) zstar zi →
        ∑ i, (zj i - zi i) < 0) := by
  have hle := aux_c39_le_zstar hideal
  have hziZ := aux_c39_mem_Z hzi
  by_cases hA : ∀ j, zi j ≠ zstar j
  · have hd : ∀ j, 0 < zstar j - zi j := fun j =>
      sub_pos.2 (lt_of_le_of_ne (hle zi hziZ j) (hA j))
    set S := ∑ j, 1 / (zstar j - zi j) with hS
    have hSpos : 0 < S :=
      Finset.sum_pos (fun j _ => by have := hd j; positivity) Finset.univ_nonempty
    have hlam : ∀ i, lamP zstar zi i = (1 / (zstar i - zi i)) * S⁻¹ := by
      intro i; unfold lamP; rw [if_pos hA]
    have hterm : ∀ i, lamP zstar zi i * (zstar i - zi i) = S⁻¹ := by
      intro i; rw [hlam]; have := (hd i).ne'; field_simp
    have hii : tcheb (lamP zstar zi) zstar zi = S⁻¹ := by
      unfold tcheb
      simp only [hterm]
      exact Finset.sup'_const _ _
    have hlt : tcheb (lamP zstar zi) zstar zi < tcheb (lamP zstar zi) zstar zj := by
      rw [hii]
      by_contra hc
      push_neg at hc
      unfold tcheb at hc
      rw [Finset.sup'_le_iff] at hc
      have hge : ∀ l, zi l ≤ zj l := by
        intro l
        have h := hc l (Finset.mem_univ _)
        rw [hlam] at h
        have h' : ((zstar l - zj l) / (zstar l - zi l)) * S⁻¹ ≤ 1 * S⁻¹ := by
          calc ((zstar l - zj l) / (zstar l - zi l)) * S⁻¹
              = 1 / (zstar l - zi l) * S⁻¹ * (zstar l - zj l) := by ring
            _ ≤ S⁻¹ := h
            _ = 1 * S⁻¹ := by ring
        have h2 := le_of_mul_le_mul_right h' (inv_pos.2 hSpos)
        rw [div_le_one (hd l)] at h2
        linarith
      obtain ⟨m, hm⟩ := Function.ne_iff.1 hne
      exact aux_c39_nd hzi ⟨zj, hzj, hge, m, lt_of_le_of_ne (hge m) (Ne.symm hm)⟩
    exact ⟨hlt.le, fun h => absurd h (not_le.2 hlt)⟩
  · have hA' : ∃ l0, zi l0 = zstar l0 := by
      push_neg at hA; exact hA
    obtain ⟨l0, hl0⟩ := hA'
    have hlam1 : ∀ i, zi i = zstar i → lamP zstar zi i = 1 := by
      intro i hi; unfold lamP; rw [if_neg hA, if_pos hi]
    have hlam0 : ∀ i, zi i ≠ zstar i → lamP zstar zi i = 0 := by
      intro i hi; unfold lamP; rw [if_neg hA, if_neg hi]
    have hterm : ∀ i, lamP zstar zi i * (zstar i - zi i) = 0 := by
      intro i
      by_cases hi : zi i = zstar i
      · rw [hi, sub_self, mul_zero]
      · rw [hlam0 i hi, zero_mul]
    have hii : tcheb (lamP zstar zi) zstar zi = 0 := by
      unfold tcheb
      simp only [hterm]
      exact Finset.sup'_const _ _
    have hl0le : zstar l0 - zj l0 ≤ tcheb (lamP zstar zi) zstar zj := by
      unfold tcheb
      have := Finset.le_sup' (fun i => lamP zstar zi i * (zstar i - zj i)) (Finset.mem_univ l0)
      simp only [hlam1 l0 hl0, one_mul] at this
      exact this
    have hnn : 0 ≤ zstar l0 - zj l0 := sub_nonneg.2 (hle zj hzj l0)
    rw [hii]
    refine ⟨hnn.trans hl0le, fun h => ?_⟩
    exact aux_c39_uniq hideal hzi hl0 hzj (by linarith) hne

theorem aux_c39_simplex {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) {zp : Fin k → ℝ} (hp : zp ∈ nondominated Z) :
    lamP zstar zp ∈ stdSimplex ℝ (Fin k) := by
  have hle := aux_c39_le_zstar hideal
  have hpZ := aux_c39_mem_Z hp
  by_cases hA : ∀ j, zp j ≠ zstar j
  · have hd : ∀ j, 0 < zstar j - zp j := fun j =>
      sub_pos.2 (lt_of_le_of_ne (hle zp hpZ j) (hA j))
    set S := ∑ j, 1 / (zstar j - zp j) with hS
    have hSpos : 0 < S :=
      Finset.sum_pos (fun j _ => by have := hd j; positivity) Finset.univ_nonempty
    have hlam : ∀ i, lamP zstar zp i = (1 / (zstar i - zp i)) * S⁻¹ := by
      intro i; unfold lamP; rw [if_pos hA]
    refine ⟨fun i => ?_, ?_⟩
    · rw [hlam]; have := hd i; positivity
    · simp only [hlam]
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ hSpos.ne'
  · have hA' : ∃ l0, zp l0 = zstar l0 := by
      push_neg at hA; exact hA
    obtain ⟨l0, hl0⟩ := hA'
    have hmax : ∀ l, zp l = zstar l → MaximizesObj Z l zp := fun l hl =>
      ⟨hpZ, fun w hw => by rw [hl]; exact hle w hw l⟩
    have huniq : ∀ m, zp m = zstar m → m = l0 := by
      intro m hm
      by_contra hml
      apply aux_c39_not_cond hideal hpZ hl0
      by_cases hex : ∃ w ∈ nondominated Z, MaximizesObj Z l0 w ∧ w ≠ zp
      · obtain ⟨w, hwN, hwM, hwne⟩ := hex
        left; exact ⟨zp, hp, w, hwN, hwne.symm, hmax l0 hl0, hwM⟩
      · right
        push_neg at hex
        exact ⟨zp, hp, hmax l0 hl0, fun w hwN hwM => hex w hwN hwM, m, hml, hmax m hm⟩
    have hlam : ∀ i, lamP zstar zp i = if i = l0 then 1 else 0 := by
      intro i
      unfold lamP
      rw [if_neg hA]
      by_cases hi : i = l0
      · subst hi; rw [if_pos hl0, if_pos rfl]
      · rw [if_neg (fun h => hi (huniq i h)), if_neg hi]
    refine ⟨fun i => ?_, ?_⟩
    · rw [hlam]; split_ifs <;> norm_num
    · simp only [hlam]
      rw [Finset.sum_ite_eq']
      simp

theorem aux_c39_rho_pos {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    (hideal : IsIdealVector Z zstar) : 0 < rho38 Z zstar := by
  unfold rho38
  dsimp only
  split_ifs with h
  · apply mul_pos (by norm_num)
    rw [Finset.lt_inf'_iff]
    rintro ⟨zi, zj⟩ hpr
    rw [Finset.mem_filter, Finset.mem_product] at hpr
    obtain ⟨⟨hzi, hzj⟩, hs⟩ := hpr
    have hne : zj ≠ zi := by rintro rfl; simp at hs
    have key := aux_c39_key hideal hzi hzj hne
    apply div_pos _ hs
    unfold alphaPQ
    by_contra hc
    push_neg at hc
    have := key.2 (by linarith)
    linarith
  · norm_num

theorem aux_c39_rho_le {k : ℕ} [NeZero k] {Z : Finset (Fin k → ℝ)} {zstar : Fin k → ℝ}
    {zp zq : Fin k → ℝ} (hp : zp ∈ nondominated Z) (hzq : zq ∈ Z)
    (hs : 0 < ∑ i, (zq i - zp i)) :
    rho38 Z zstar ≤
      (1 / 2) * ((alphaPQ zstar zp zq - alphaPQ zstar zp zp) / ∑ i, (zq i - zp i)) := by
  unfold rho38
  dsimp only
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.inf'_le (b := (zp, zq)) _ ?_).trans_eq rfl
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp, hzq⟩, hs⟩
  · refine absurd ⟨(zp, zq), ?_⟩ h
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp, hzq⟩, hs⟩

end SteuerChoo.Discrete

open SteuerChoo.Discrete

theorem solution {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    lamP zstar zp ∈ stdSimplex ℝ (Fin k) ∧
      ∀ zq ∈ Z, zq ≠ zp →
        augTcheb (lamP zstar zp) (rho38 Z zstar) zstar zp <
          augTcheb (lamP zstar zp) (rho38 Z zstar) zstar zq := by
  refine ⟨aux_c39_simplex hideal hp, ?_⟩
  intro zq hzq hne
  have hρpos := aux_c39_rho_pos (Z := Z) hideal
  have key := aux_c39_key hideal hp hzq hne
  unfold augTcheb
  have hsum : ∑ i, (zstar i - zq i) = ∑ i, (zstar i - zp i) - ∑ i, (zq i - zp i) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext i; ring
  rw [hsum]
  have hmul : rho38 Z zstar * (∑ i, (zstar i - zp i) - ∑ i, (zq i - zp i)) =
      rho38 Z zstar * ∑ i, (zstar i - zp i) - rho38 Z zstar * ∑ i, (zq i - zp i) :=
    mul_sub _ _ _
  rw [hmul]
  by_cases hs : 0 < ∑ i, (zq i - zp i)
  · have hρle := aux_c39_rho_le (zstar := zstar) hp hzq hs
    unfold alphaPQ at hρle
    have hab : tcheb (lamP zstar zp) zstar zp < tcheb (lamP zstar zp) zstar zq := by
      rcases lt_or_eq_of_le key.1 with h | h
      · exact h
      · have := key.2 h.ge; linarith
    have h1 := mul_le_mul_of_nonneg_right hρle hs.le
    have h2 : (1 / 2) * ((tcheb (lamP zstar zp) zstar zq - tcheb (lamP zstar zp) zstar zp) /
        ∑ i, (zq i - zp i)) * ∑ i, (zq i - zp i) =
        (tcheb (lamP zstar zp) zstar zq - tcheb (lamP zstar zp) zstar zp) / 2 := by
      field_simp
    linarith
  · push_neg at hs
    rcases lt_or_eq_of_le key.1 with h | h
    · have : rho38 Z zstar * ∑ i, (zq i - zp i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hρpos.le hs
      linarith
    · have hneg := key.2 h.ge
      have : rho38 Z zstar * ∑ i, (zq i - zp i) < 0 := mul_neg_of_pos_of_neg hρpos hneg
      linarith
