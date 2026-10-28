-- Prove2me | solution 1 for RobustQueueRatio.SPStability.theorem_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:04:23.324642+00:00
-- url     : https://prove2.me/submissions/b917c013-52c9-4298-8508-7361c9cf265e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix
import Theorems.Thm_RobustQueueRatio_SPStability_lemma_3
import Theorems.Thm_RobustQueueRatio_SPStability_theorem_5_ii

open Matrix

namespace RQRThm4Aux

open RobustQueueRatio.SPStability

/-- If two `K × J` matrices agree outside column `k`, the determinant of `G * Δ` is affine
along the segment joining them. -/
theorem det_mul_comb_of_col {J K : ℕ} (G : Matrix (Fin J) (Fin K) ℝ)
    (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (k : Fin J)
    (hk : ∀ i j, j ≠ k → Δ₁ i j = Δ₂ i j) (lam : ℝ) :
    (G * (lam • Δ₁ + (1 - lam) • Δ₂)).det =
      lam * (G * Δ₁).det + (1 - lam) * (G * Δ₂).det := by
  set X₁ := G * Δ₁
  set X₂ := G * Δ₂
  have h2 : X₂ = updateCol X₁ k (fun i => X₂ i k) := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp
    · rw [updateCol_ne hj]
      simp only [X₁, X₂, mul_apply]
      exact Finset.sum_congr rfl (fun l _ => by rw [hk l j hj])
  have h3 : G * (lam • Δ₁ + (1 - lam) • Δ₂) =
      updateCol X₁ k (lam • (fun i => X₁ i k) + (1 - lam) • (fun i => X₂ i k)) := by
    ext i j
    by_cases hj : j = k
    · subst hj
      simp only [updateCol_self, X₁, X₂, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply,
        Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]
    · rw [updateCol_ne hj]
      simp only [X₁, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have : (G * Δ₂) i j = (G * Δ₁) i j := by
        simp only [mul_apply]
        exact Finset.sum_congr rfl (fun l _ => by rw [hk l j hj])
      rw [this]; ring
  rw [h3, det_updateCol_add, det_updateCol_smul, det_updateCol_smul]
  have e1 : updateCol X₁ k (fun i => X₁ i k) = X₁ := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp
    · rw [updateCol_ne hj]
  rw [e1, ← h2]


theorem cmd_apply {J K : ℕ} (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) (i j : Fin J) :
    (N.C * N.M * Δ) i j = ∑ k, if N.s k = i then N.m k * Δ k j else 0 := by
  rw [mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Network.C, Network.M, mul_diagonal, of_apply]
  split_ifs <;> ring

/-- A ratio matrix with at most one nonzero entry per column is static-priority. -/
theorem static_of_single {J K : ℕ} (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ)
    (hΔ : IsRatioMatrix N Δ)
    (hs : ∀ j k₁ k₂, Δ k₁ j ≠ 0 → Δ k₂ j ≠ 0 → k₁ = k₂) : IsStaticPriority N Δ := by
  refine ⟨hΔ, fun j => ?_⟩
  have h1 : (N.C * N.M * Δ) j j = 1 := by rw [hΔ.2.2]; simp
  rw [cmd_apply] at h1
  obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, (if N.s k = j then N.m k * Δ k j else 0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at h1
    exact zero_ne_one h1
  have hsk : N.s k = j := by
    by_contra h; simp [h] at hk
  have hΔk : Δ k j ≠ 0 := by
    intro h; simp [h] at hk
  have hsum : (∑ l, if N.s l = j then N.m l * Δ l j else 0) = N.m k * Δ k j := by
    rw [Finset.sum_eq_single k]
    · simp [hsk]
    · intro l _ hl
      have : Δ l j = 0 := by
        by_contra h
        exact hl (hs j l k h hΔk)
      simp [this]
    · simp
  rw [hsum] at h1
  have hm := N.m_pos k
  refine ⟨k, hsk, ?_, ?_⟩
  · field_simp
    linarith
  · intro l _ hl
    by_contra h
    exact hl (hs j l k h hΔk)

/-- The support of a matrix, as a finset of index pairs. -/
noncomputable def supp {J K : ℕ} (Δ : Matrix (Fin K) (Fin J) ℝ) : Finset (Fin K × Fin J) :=
  open Classical in Finset.univ.filter fun p => Δ p.1 p.2 ≠ 0

theorem mem_supp {J K : ℕ} (Δ : Matrix (Fin K) (Fin J) ℝ) (p : Fin K × Fin J) :
    p ∈ supp Δ ↔ Δ p.1 p.2 ≠ 0 := by
  simp [supp]

end RQRThm4Aux

open RobustQueueRatio.SPStability RQRThm4Aux in
theorem solution {J K : ℕ} (N : Network J K)
    (hcorner : ∀ Δ, IsStaticPriority N Δ →
      IsUnit (reflInv N Δ).det ∧ IsChenS (refl N Δ) (theta N Δ))
    (hsign : (∀ Δ, IsStaticPriority N Δ → 0 < (reflInv N Δ).det) ∨
      (∀ Δ, IsStaticPriority N Δ → (reflInv N Δ).det < 0)) :
    ∀ Δ, IsRatioMatrix N Δ → IsUnit (reflInv N Δ).det ∧ IsChenS (refl N Δ) (theta N Δ) := by
  obtain ⟨σ, hσ, hsgn⟩ : ∃ σ : ℝ, σ * σ = 1 ∧
      ∀ Δ, IsStaticPriority N Δ → 0 < σ * (reflInv N Δ).det := by
    rcases hsign with h | h
    · exact ⟨1, by norm_num, fun Δ hΔ => by simpa using h Δ hΔ⟩
    · exact ⟨-1, by norm_num, fun Δ hΔ => by have := h Δ hΔ; linarith⟩
  suffices H : ∀ n : ℕ, ∀ Δ, IsRatioMatrix N Δ → (supp Δ).card = n →
      0 < σ * (reflInv N Δ).det ∧ IsChenS (refl N Δ) (theta N Δ) by
    intro Δ hΔ
    obtain ⟨h1, h2⟩ := H _ Δ hΔ rfl
    refine ⟨isUnit_iff_ne_zero.2 ?_, h2⟩
    intro h0; rw [h0] at h1; simp at h1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Δ hΔ hn
  by_cases hdec : ∃ j k₁ k₂, k₁ ≠ k₂ ∧ Δ k₁ j ≠ 0 ∧ Δ k₂ j ≠ 0
  swap
  · push Not at hdec
    have hst := static_of_single N Δ hΔ (fun j k₁ k₂ h₁ h₂ => by
      by_contra hne; exact h₂ (hdec j k₁ k₂ hne h₁))
    exact ⟨hsgn Δ hst, (hcorner Δ hst).2⟩
  obtain ⟨j, k₁, k₂, hne, hk₁, hk₂⟩ := hdec
  obtain ⟨hzero, hnn, hcm⟩ := hΔ
  have hm₁ := N.m_pos k₁
  have hm₂ := N.m_pos k₂
  have hs₁ : N.s k₁ = j := by by_contra h; exact hk₁ (hzero k₁ j h)
  have hs₂ : N.s k₂ = j := by by_contra h; exact hk₂ (hzero k₂ j h)
  have hpos₁ : 0 < Δ k₁ j := lt_of_le_of_ne (hnn k₁ j) (Ne.symm hk₁)
  have hpos₂ : 0 < Δ k₂ j := lt_of_le_of_ne (hnn k₂ j) (Ne.symm hk₂)
  set lam := N.m k₁ * Δ k₁ j with hlam
  have hlam₀ : 0 < lam := mul_pos hm₁ hpos₁
  -- the column sum at station `j`
  have hcol : (∑ k, if N.s k = j then N.m k * Δ k j else 0) = 1 := by
    rw [← cmd_apply, hcm]; simp
  have hterm_nn : ∀ k, 0 ≤ (if N.s k = j then N.m k * Δ k j else 0) := by
    intro k; split_ifs
    · exact mul_nonneg (N.m_pos k).le (hnn k j)
    · exact le_rfl
  have hlam₁ : lam < 1 := by
    have hpair : (∑ k ∈ ({k₁, k₂} : Finset (Fin K)),
        (if N.s k = j then N.m k * Δ k j else 0)) ≤
        ∑ k, (if N.s k = j then N.m k * Δ k j else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => hterm_nn k)
    rw [Finset.sum_pair hne, hcol] at hpair
    simp only [hs₁, hs₂, if_true] at hpair
    have : 0 < N.m k₂ * Δ k₂ j := mul_pos hm₂ hpos₂
    linarith
  have h1lam : (1 - lam) ≠ 0 := by linarith
  obtain ⟨Δ₁, hD₁⟩ : ∃ D : Matrix (Fin K) (Fin J) ℝ, ∀ k j', D k j' =
      if j' = j then (if k = k₁ then (N.m k₁)⁻¹ else 0) else Δ k j' :=
    ⟨Matrix.of fun k j' => if j' = j then (if k = k₁ then (N.m k₁)⁻¹ else 0) else Δ k j',
      fun _ _ => rfl⟩
  obtain ⟨Δ₂, hD₂⟩ : ∃ D : Matrix (Fin K) (Fin J) ℝ, ∀ k j', D k j' =
      if j' = j then (if k = k₁ then 0 else Δ k j / (1 - lam)) else Δ k j' :=
    ⟨Matrix.of fun k j' => if j' = j then (if k = k₁ then 0 else Δ k j / (1 - lam)) else Δ k j',
      fun _ _ => rfl⟩
  have hcomb : lam • Δ₁ + (1 - lam) • Δ₂ = Δ := by
    ext k j'
    simp only [hD₁, hD₂, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hj : j' = j
    · subst hj
      by_cases hk : k = k₁
      · subst hk; simp only [if_true]; rw [hlam]; field_simp; ring
      · simp only [if_true, hk, if_false]; field_simp; ring
    · simp only [hj, if_false]; ring
  have hagree : ∀ i j', j' ≠ j → Δ₁ i j' = Δ₂ i j' := by
    intro i j' hj; simp [hD₁, hD₂, hj]
  -- ratio-matrix property of the two pieces
  have hR₁ : IsRatioMatrix N Δ₁ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k j' h
      rw [hD₁]
      by_cases hj : j' = j
      · subst hj
        by_cases hk : k = k₁
        · subst hk; exact absurd hs₁ h
        · simp [hk]
      · simp [hj, hzero k j' h]
    · intro k j'
      rw [hD₁]
      split_ifs
      · exact inv_nonneg.2 hm₁.le
      · exact le_rfl
      · exact hnn k j'
    · ext i j'
      rw [cmd_apply]
      by_cases hj : j' = j
      · subst hj
        rw [Finset.sum_eq_single k₁]
        · simp only [hD₁, if_true, hs₁]
          rw [one_apply]
          by_cases hij : i = j'
          · subst hij; simp only [if_true]; field_simp
          · simp only [hij, if_false, Ne.symm hij]
        · intro b _ hb; simp [hD₁, hb]
        · simp
      · have := congrFun (congrFun hcm i) j'
        rw [cmd_apply] at this
        rw [← this]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [hD₁, hj]
  have hR₂ : IsRatioMatrix N Δ₂ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k j' h
      rw [hD₂]
      by_cases hj : j' = j
      · subst hj
        by_cases hk : k = k₁
        · simp [hk]
        · simp [hk, hzero k j' h]
      · simp [hj, hzero k j' h]
    · intro k j'
      rw [hD₂]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hnn k j) (by linarith)
      · exact hnn k j'
    · ext i j'
      rw [cmd_apply]
      by_cases hj : j' = j
      · subst hj
        have hfull := congrFun (congrFun hcm i) j'
        rw [cmd_apply] at hfull
        have hsplit : (∑ k, if N.s k = i then N.m k * Δ₂ k j' else 0) =
            ((∑ k, if N.s k = i then N.m k * Δ k j' else 0) -
              (if N.s k₁ = i then N.m k₁ * Δ k₁ j' else 0)) / (1 - lam) := by
          rw [eq_div_iff h1lam, Finset.sum_mul]
          have hterm' : ∀ k, (if N.s k = i then N.m k * Δ₂ k j' else 0) * (1 - lam) =
              (if N.s k = i then N.m k * Δ k j' else 0) -
                (if k = k₁ then (if N.s k₁ = i then N.m k₁ * Δ k₁ j' else 0) else 0) := by
            intro k
            rw [hD₂]
            by_cases hk : k = k₁
            · subst hk; simp
            · simp only [if_true, hk, if_false, sub_zero]
              split_ifs
              · field_simp
              · ring
          rw [Finset.sum_congr rfl (fun k _ => hterm' k), Finset.sum_sub_distrib,
            Finset.sum_ite_eq']
          simp
        rw [hsplit, hfull, hs₁, one_apply]
        by_cases hij : i = j'
        · subst hij; simp only [if_true]; rw [← hlam]; field_simp
        · simp [hij, Ne.symm hij]
      · have := congrFun (congrFun hcm i) j'
        rw [cmd_apply] at this
        rw [← this]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [hD₂, hj]
  -- supports shrink strictly
  have hsub₁ : supp Δ₁ ⊂ supp Δ := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(k₂, j), (mem_supp _ _).2 hk₂, ?_⟩
      rw [mem_supp, hD₁]; simp [Ne.symm hne]
    · intro p hp
      rw [mem_supp, hD₁] at hp; rw [mem_supp]
      by_cases hj : p.2 = j
      · rw [hj] at hp ⊢
        by_cases hk : p.1 = k₁
        · rw [hk]; exact hk₁
        · simp [hk] at hp
      · simpa [hj] using hp
  have hsub₂ : supp Δ₂ ⊂ supp Δ := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(k₁, j), (mem_supp _ _).2 hk₁, ?_⟩
      rw [mem_supp, hD₂]; simp
    · intro p hp
      rw [mem_supp, hD₂] at hp; rw [mem_supp]
      by_cases hj : p.2 = j
      · rw [hj] at hp ⊢
        by_cases hk : p.1 = k₁
        · simp [hk] at hp
        · simp only [hk, if_true, if_false] at hp
          intro h; apply hp; rw [h]; simp
      · simpa [hj] using hp
  obtain ⟨hd₁, hC₁⟩ := ih _ (hn ▸ Finset.card_lt_card hsub₁) Δ₁ hR₁ rfl
  obtain ⟨hd₂, hC₂⟩ := ih _ (hn ▸ Finset.card_lt_card hsub₂) Δ₂ hR₂ rfl
  have hnb : AreNeighbors ![Δ₁, Δ₂] := by
    refine Set.Subsingleton.anti (Set.subsingleton_singleton (a := j)) ?_
    rintro j' ⟨a, b, k, hab⟩
    by_contra hj
    apply hab
    have hj' : j' ≠ j := hj
    fin_cases a <;> fin_cases b <;> simp [hagree k j' hj']
  have hdet : (reflInv N Δ).det = lam * (reflInv N Δ₁).det + (1 - lam) * (reflInv N Δ₂).det := by
    rw [← hcomb]; unfold reflInv
    exact det_mul_comb_of_col _ _ _ j hagree lam
  have hu₁ : IsUnit (reflInv N Δ₁).det :=
    isUnit_iff_ne_zero.2 (fun h0 => by rw [h0] at hd₁; simp at hd₁)
  have hu₂ : IsUnit (reflInv N Δ₂).det :=
    isUnit_iff_ne_zero.2 (fun h0 => by rw [h0] at hd₂; simp at hd₂)
  have hprod : 0 < (reflInv N Δ₁).det * (reflInv N Δ₂).det := by
    have := mul_pos hd₁ hd₂
    calc 0 < (σ * (reflInv N Δ₁).det) * (σ * (reflInv N Δ₂).det) := this
      _ = (σ * σ) * ((reflInv N Δ₁).det * (reflInv N Δ₂).det) := by ring
      _ = _ := by rw [hσ, one_mul]
  have hΔfull : IsRatioMatrix N Δ := ⟨hzero, hnn, hcm⟩
  obtain ⟨-, hu₃⟩ := RobustQueueRatio.SPStability.lemma_3 N Δ₁ Δ₂ lam hR₁ hR₂ hnb hlam₀ hlam₁
    hu₁ hu₂ hprod
  obtain ⟨-, hC⟩ := RobustQueueRatio.SPStability.theorem_5_ii N Δ₁ Δ₂ lam hR₁ hR₂ hnb hlam₀
    hlam₁ hu₁ hu₂ hu₃
  refine ⟨?_, ?_⟩
  · rw [hdet]
    have : 0 < 1 - lam := by linarith
    nlinarith
  · rw [hcomb] at hC
    exact hC hC₁ hC₂
