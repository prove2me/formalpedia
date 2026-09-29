-- Prove2me | solution 1 for SteuerChoo.Discrete.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:05:55.810566+00:00
-- url     : https://prove2.me/submissions/39b0992a-a3b0-4b51-b102-207b2e09f35e

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- Every element of a finite `Z` lies below some nondominated element. -/
theorem aux_sc32_exists_nd_above {k : ℕ} (Z : Finset (Fin k → ℝ)) (zq : Fin k → ℝ)
    (hq : zq ∈ Z) : ∃ z' ∈ nondominated Z, zq ≤ z' := by
  classical
  set T := Z.filter (fun w => zq ≤ w) with hT
  have hTne : T.Nonempty := ⟨zq, Finset.mem_filter.mpr ⟨hq, le_refl _⟩⟩
  obtain ⟨z', hz'T, hmax⟩ := Finset.exists_max_image T (fun w => ∑ i, w i) hTne
  obtain ⟨hz'Z, hqz'⟩ := Finset.mem_filter.mp hz'T
  refine ⟨z', ?_, hqz'⟩
  unfold nondominated
  refine Finset.mem_filter.mpr ⟨hz'Z, ?_⟩
  rintro ⟨w, hwZ, hle, i, hi⟩
  have hwT : w ∈ T := Finset.mem_filter.mpr ⟨hwZ, fun t => (hqz' t).trans (hle t)⟩
  have h1 := hmax w hwT
  have h2 : ∑ t, z' t < ∑ t, w t :=
    Finset.sum_lt_sum (fun t _ => hle t) ⟨i, Finset.mem_univ _, hi⟩
  linarith

end SteuerChoo.Discrete

open SteuerChoo.Discrete

theorem solution {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) (hne : zq ≠ zp) (hnle : ¬ zq ≤ zp) :
    zq ∉ Phi (lamP zstar zp) zstar (alphaPQ zstar zp zp) := by
  classical
  intro hPhi
  obtain ⟨ε, hε0, hεmax, hεpos⟩ := hideal
  have hp' := hp
  unfold nondominated at hp'
  have hpZ : zp ∈ Z := (Finset.mem_filter.mp hp').1
  have hpnd : ¬ ∃ z ∈ Z, Dominates z zp := (Finset.mem_filter.mp hp').2
  have hub : ∀ w ∈ Z, ∀ i, w i ≤ zstar i := by
    intro w hw i
    obtain ⟨z, ⟨_, hzmax⟩, hz⟩ := hεmax i
    have := hzmax w hw
    have := hε0 i
    linarith
  by_cases hall : ∀ j, zp j ≠ zstar j
  · have hlt : ∀ i, 0 < zstar i - zp i := fun i =>
      sub_pos.mpr (lt_of_le_of_ne (hub zp hpZ i) (hall i))
    set S := ∑ j, 1 / (zstar j - zp j) with hS
    have hSpos : 0 < S :=
      Finset.sum_pos (fun j _ => by have := hlt j; positivity) Finset.univ_nonempty
    have hlam : ∀ i, lamP zstar zp i = (1 / (zstar i - zp i)) * S⁻¹ := by
      intro i
      simp only [lamP, if_pos hall, hS]
    have hprod : ∀ i, lamP zstar zp i * (zstar i - zp i) = S⁻¹ := by
      intro i
      rw [hlam]
      have := (hlt i).ne'
      field_simp
    have halpha : alphaPQ zstar zp zp = S⁻¹ := by
      unfold alphaPQ tcheb
      simp only [hprod]
      exact Finset.sup'_const _ _
    have hge : ∀ i, zp i ≤ zq i := by
      intro i
      have hlpos : 0 < lamP zstar zp i := by
        rw [hlam]; have := hlt i; positivity
      have h1 := hPhi i hlpos
      rw [halpha] at h1
      have h2 : S⁻¹ / lamP zstar zp i = zstar i - zp i := by
        rw [← hprod i]
        field_simp
      linarith
    apply hpnd
    refine ⟨zq, hq, hge, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hne (funext fun i => le_antisymm (hcon i) (hge i))
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hlamj : lamP zstar zp j = 1 := by
      simp only [lamP]
      rw [if_neg (by push Not; exact ⟨j, hj⟩), if_pos hj]
    have hterm : ∀ i, lamP zstar zp i * (zstar i - zp i) = 0 := by
      intro i
      by_cases hi : zp i = zstar i
      · rw [hi, sub_self, mul_zero]
      · have : lamP zstar zp i = 0 := by
          simp only [lamP]
          rw [if_neg (by push Not; exact ⟨j, hj⟩), if_neg hi]
        rw [this, zero_mul]
    have halpha : alphaPQ zstar zp zp = 0 := by
      unfold alphaPQ tcheb
      simp only [hterm]
      exact Finset.sup'_const _ _
    have hqj : zstar j ≤ zq j := by
      have h1 := hPhi j (by rw [hlamj]; norm_num)
      rw [halpha, hlamj] at h1
      simpa using h1
    have hεj : ε j = 0 := by
      obtain ⟨z, ⟨_, hzmax⟩, hz⟩ := hεmax j
      have := hzmax zp hpZ
      have := hε0 j
      linarith
    have hnotI : ¬ CondI Z j := fun h => by
      have := hεpos j (Or.inl h)
      linarith
    have hmaxj : ∀ w ∈ Z, zstar j ≤ w j → MaximizesObj Z j w := fun w hw hwj =>
      ⟨hw, fun v hv => (hub v hv j).trans hwj⟩
    obtain ⟨z', hz'N, hqz'⟩ := aux_sc32_exists_nd_above Z zq hq
    have hz'N' := hz'N
    unfold nondominated at hz'N'
    have hz'Z : z' ∈ Z := (Finset.mem_filter.mp hz'N').1
    have heq : z' = zp := by
      by_contra hc
      exact hnotI ⟨z', hz'N, zp, hp, hc, hmaxj z' hz'Z (hqj.trans (hqz' j)),
        hmaxj zp hpZ (le_of_eq hj.symm)⟩
    exact hnle (heq ▸ hqz')
