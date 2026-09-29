-- Prove2me | solution 1 for SteuerChoo.Discrete.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:01:14.381174+00:00
-- url     : https://prove2.me/submissions/60e81ee7-ec43-4db3-a23b-854f3355592c

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

theorem aux_st34_zstar_ge {k : ℕ} (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) : ∀ w ∈ Z, ∀ i, w i ≤ zstar i := by
  obtain ⟨ε, hε0, hεmax, -⟩ := hideal
  intro w hw i
  obtain ⟨z, ⟨_, hzmax⟩, hz⟩ := hεmax i
  have h1 := hzmax w hw
  have h2 := hε0 i
  linarith

theorem aux_st34_exists_nd {k : ℕ} (Z : Finset (Fin k → ℝ)) (zq : Fin k → ℝ) (hq : zq ∈ Z) :
    ∃ w ∈ nondominated Z, ∀ i, zq i ≤ w i := by
  classical
  set S := Z.filter (fun w => ∀ i, zq i ≤ w i) with hS
  have hne : S.Nonempty := ⟨zq, by simp [hS, hq]⟩
  obtain ⟨w, hwS, hwmax⟩ := S.exists_max_image (fun w => ∑ i, w i) hne
  simp only [hS, Finset.mem_filter] at hwS
  refine ⟨w, ?_, hwS.2⟩
  unfold nondominated
  rw [Finset.mem_filter]
  refine ⟨hwS.1, ?_⟩
  rintro ⟨u, hu, hdom⟩
  have huS : u ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨hu, fun i => le_trans (hwS.2 i) (hdom.1 i)⟩
  have h1 := hwmax u huS
  obtain ⟨j, hj⟩ := hdom.2
  have : ∑ i, w i < ∑ i, u i :=
    Finset.sum_lt_sum (fun i _ => hdom.1 i) ⟨j, Finset.mem_univ _, hj⟩
  linarith

theorem aux_st34_key {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) :
    alphaPQ zstar zp zp ≤ alphaPQ zstar zp zq ∧
      ((∃ i, zp i < zq i) → alphaPQ zstar zp zp < alphaPQ zstar zp zq) := by
  classical
  have hge := aux_st34_zstar_ge Z zstar hideal
  have hp' := hp
  unfold nondominated at hp'
  rw [Finset.mem_filter] at hp'
  have hpZ : zp ∈ Z := hp'.1
  have hpnd : ¬ ∃ z ∈ Z, Dominates z zp := hp'.2
  by_cases hA : ∀ j, zp j ≠ zstar j
  · set S := ∑ j, 1 / (zstar j - zp j) with hSdef
    have hpos : ∀ j, 0 < zstar j - zp j := by
      intro j
      rcases lt_or_eq_of_le (hge zp hpZ j) with h | h
      · linarith
      · exact absurd h (hA j)
    have hSpos : 0 < S := Finset.sum_pos (fun j _ => by have := hpos j; positivity)
      Finset.univ_nonempty
    have hlam : ∀ i, lamP zstar zp i = 1 / (zstar i - zp i) * S⁻¹ := by
      intro i
      unfold lamP
      rw [if_pos hA]
    have hlampos : ∀ i, 0 < lamP zstar zp i := by
      intro i
      rw [hlam]
      have := hpos i
      positivity
    have hterm : ∀ i, lamP zstar zp i * (zstar i - zp i) = S⁻¹ := by
      intro i
      rw [hlam]
      field_simp [(hpos i).ne']
    have hpp : alphaPQ zstar zp zp = S⁻¹ := by
      unfold alphaPQ tcheb
      apply le_antisymm
      · exact Finset.sup'_le _ _ (fun i _ => (hterm i).le)
      · have i0 : Fin k := ⟨0, NeZero.pos k⟩
        calc S⁻¹ = lamP zstar zp i0 * (zstar i0 - zp i0) := (hterm i0).symm
        _ ≤ _ := Finset.le_sup' (fun i => lamP zstar zp i * (zstar i - zp i)) (Finset.mem_univ i0)
    have hstrict : (∃ m, zq m < zp m) → alphaPQ zstar zp zp < alphaPQ zstar zp zq := by
      rintro ⟨m, hm⟩
      rw [hpp]
      unfold alphaPQ tcheb
      rw [Finset.lt_sup'_iff]
      refine ⟨m, Finset.mem_univ _, ?_⟩
      rw [← hterm m]
      exact mul_lt_mul_of_pos_left (by linarith) (hlampos m)
    by_cases hm : ∃ m, zq m < zp m
    · exact ⟨(hstrict hm).le, fun _ => hstrict hm⟩
    · push Not at hm
      have hnot : ¬ ∃ i, zp i < zq i := fun h => hpnd ⟨zq, hq, hm, h⟩
      have heq : zq = zp := funext fun i => le_antisymm (not_lt.mp (fun h => hnot ⟨i, h⟩)) (hm i)
      subst heq
      exact ⟨le_rfl, fun h => absurd h hnot⟩
  · push Not at hA
    obtain ⟨j0, hj0⟩ := hA
    have hnA : ¬ ∀ j, zp j ≠ zstar j := fun h => h j0 hj0
    have hlam : ∀ i, lamP zstar zp i = if zp i = zstar i then 1 else 0 := by
      intro i
      unfold lamP
      rw [if_neg hnA]
    have hpp : alphaPQ zstar zp zp = 0 := by
      unfold alphaPQ tcheb
      have h0 : ∀ i, lamP zstar zp i * (zstar i - zp i) = 0 := by
        intro i
        rw [hlam]
        split_ifs with h
        · rw [h]; ring
        · ring
      simp only [h0]
      exact Finset.sup'_const _ _
    have hq0 : lamP zstar zp j0 * (zstar j0 - zq j0) = zstar j0 - zq j0 := by
      rw [hlam, if_pos hj0, one_mul]
    have hle0 : lamP zstar zp j0 * (zstar j0 - zq j0) ≤ alphaPQ zstar zp zq := by
      unfold alphaPQ tcheb
      exact Finset.le_sup' (fun i => lamP zstar zp i * (zstar i - zq i)) (Finset.mem_univ j0)
    rw [hq0] at hle0
    constructor
    · rw [hpp]
      have := hge zq hq j0
      linarith
    · rintro ⟨i, hi⟩
      rw [hpp]
      by_contra hle
      push Not at hle
      have hzq0 : zq j0 = zstar j0 := by
        have := hge zq hq j0
        linarith
      obtain ⟨w, hwN, hww⟩ := aux_st34_exists_nd Z zq hq
      have hwN' := hwN
      unfold nondominated at hwN'
      rw [Finset.mem_filter] at hwN'
      have hwZ : w ∈ Z := hwN'.1
      obtain ⟨ε, hε0, hεmax, hεpos⟩ := hideal
      have hcond : CondI Z j0 := by
        refine ⟨zp, hp, w, hwN, ?_, ⟨hpZ, ?_⟩, ⟨hwZ, ?_⟩⟩
        · intro h
          have := hww i
          rw [← h] at this
          linarith
        · intro u hu
          rw [hj0]
          exact hge u hu j0
        · intro u hu
          have := hww j0
          have := hge u hu j0
          linarith
      have hεj := hεpos j0 (Or.inl hcond)
      obtain ⟨z, ⟨_, hzmax⟩, hz⟩ := hεmax j0
      have := hzmax zp hpZ
      linarith

end SteuerChoo.Discrete

open SteuerChoo.Discrete

theorem solution {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    ∀ zq ∈ Z, zq ≠ zp →
      augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zp <
        augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zq := by
  classical
  intro zq hq hne
  obtain ⟨hge, hgt⟩ := aux_st34_key Z zstar hideal zp hp zq hq
  have hrho_pos : 0 < rhoP Z zstar zp := by
    unfold rhoP
    simp only []
    split_ifs with h
    · apply mul_pos (by norm_num)
      rw [Finset.lt_inf'_iff]
      intro b hb
      rw [Finset.mem_filter] at hb
      apply div_pos _ hb.2
      have hex : ∃ i, zp i < b i := by
        by_contra hc
        push Not at hc
        have : ∑ i, (b i - zp i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [hc i])
        linarith [hb.2]
      linarith [(aux_st34_key Z zstar hideal zp hp b hb.1).2 hex]
    · norm_num
  set s := ∑ i, (zq i - zp i) with hs
  set a := alphaPQ zstar zp zq - alphaPQ zstar zp zp with ha
  have hdiff : augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zq -
      augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zp = a - rhoP Z zstar zp * s := by
    unfold augTcheb
    rw [ha, hs]
    unfold alphaPQ
    have : ∑ i, (zstar i - zq i) = ∑ i, (zstar i - zp i) - ∑ i, (zq i - zp i) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext i
      ring
    rw [this]
    ring
  suffices hsuff : 0 < a - rhoP Z zstar zp * s by linarith
  by_cases hspos : 0 < s
  · have hex : ∃ i, zp i < zq i := by
      by_contra hc
      push Not at hc
      have : ∑ i, (zq i - zp i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [hc i])
      linarith
    have hapos : 0 < a := by rw [ha]; linarith [hgt hex]
    have hrho_le : rhoP Z zstar zp ≤ 1 / 2 * (a / s) := by
      unfold rhoP
      simp only []
      have hmem : zq ∈ Z.filter (fun zq => 0 < ∑ i, (zq i - zp i)) :=
        Finset.mem_filter.mpr ⟨hq, hspos⟩
      rw [dif_pos ⟨zq, hmem⟩]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.inf'_le _ hmem
    have : rhoP Z zstar zp * s ≤ 1 / 2 * a := by
      calc rhoP Z zstar zp * s ≤ 1 / 2 * (a / s) * s :=
            mul_le_mul_of_nonneg_right hrho_le hspos.le
      _ = 1 / 2 * a := by field_simp
    linarith
  · push Not at hspos
    by_cases hex : ∃ i, zp i < zq i
    · have hapos : 0 < a := by rw [ha]; linarith [hgt hex]
      have : rhoP Z zstar zp * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrho_pos.le hspos
      linarith
    · push Not at hex
      have hlt : ∃ i, zq i < zp i := by
        by_contra hc
        push Not at hc
        exact hne (funext fun i => le_antisymm (hex i) (hc i))
      obtain ⟨m, hm⟩ := hlt
      have hsneg : s < 0 := by
        rw [hs]
        have : ∑ i, (zq i - zp i) < ∑ _i : Fin k, (0:ℝ) :=
          Finset.sum_lt_sum (fun i _ => by linarith [hex i]) ⟨m, Finset.mem_univ _, by linarith⟩
        simpa using this
      have hanonneg : 0 ≤ a := by rw [ha]; linarith
      have : rhoP Z zstar zp * s < 0 := mul_neg_of_pos_of_neg hrho_pos hsneg
      linarith
