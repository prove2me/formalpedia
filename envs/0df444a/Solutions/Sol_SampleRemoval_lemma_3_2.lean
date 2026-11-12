-- Prove2me | solution 1 for SampleRemoval.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:34:46.186172+00:00
-- url     : https://prove2.me/submissions/ebe1a76a-6035-4167-8640-4bc199319972

import Mathlib
import Definitions.Def_SampleRemoval_ols
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_GeneralPosition
import Theorems.Thm_SampleRemoval_normal_equations
import Theorems.Thm_SampleRemoval_gram_posDef_iff_card_support

section
set_option autoImplicit false

open Matrix

namespace SampleRemoval.Dev.L32

open Finset

/-- fractional coordinates -/
noncomputable def Frac {n : ℕ} (w : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < w i ∧ w i < 1)

lemma exists_dep {n d : ℕ} (v : Fin n → Fin d → ℝ) (J : Finset (Fin n)) (hJ : d < J.card) :
    ∃ δ : Fin n → ℝ, (∀ i, i ∉ J → δ i = 0) ∧ (∃ i, δ i ≠ 0) ∧ ∑ i, δ i • v i = 0 := by
  classical
  have hnl : ¬ LinearIndependent ℝ (fun i : J => v i) := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hnl
  obtain ⟨g, hg, i0, hi0⟩ := hnl
  refine ⟨fun i => if h : i ∈ J then g ⟨i, h⟩ else 0, ?_, ⟨i0, ?_⟩, ?_⟩
  · intro i hi; simp [hi]
  · simp [i0.2, hi0]
  · rw [← Finset.sum_subset (Finset.subset_univ J)]
    · rw [← hg, ← Finset.sum_coe_sort J]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.2]
    · intro i _ hi; simp [hi]

lemma reduce {n d : ℕ} (v : Fin n → Fin d → ℝ) : ∀ k : ℕ, ∀ w : Fin n → ℝ,
    (∀ i, w i ∈ Set.Icc (0 : ℝ) 1) → ∑ i, w i • v i = 0 → (Frac w).card = k →
    ∃ w' : Fin n → ℝ, (∀ i, w' i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i, w' i • v i = 0 ∧
      ∑ i, w i ≤ ∑ i, w' i ∧ (Frac w').card ≤ d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro w hw hsum hk
  by_cases hkd : k ≤ d
  · exact ⟨w, hw, hsum, le_rfl, by omega⟩
  have hkd : d < k := not_le.mp hkd
  obtain ⟨δ₀, hδ0, ⟨j, hj⟩, hδsum⟩ := exists_dep v (Frac w) (by omega)
  -- choose sign
  obtain ⟨δ, hδJ, hδne, hδv, hδpos⟩ : ∃ δ : Fin n → ℝ, (∀ i, i ∉ Frac w → δ i = 0) ∧
      (∃ i, δ i ≠ 0) ∧ ∑ i, δ i • v i = 0 ∧ 0 ≤ ∑ i, δ i := by
    by_cases hs : 0 ≤ ∑ i, δ₀ i
    · exact ⟨δ₀, hδ0, ⟨j, hj⟩, hδsum, hs⟩
    · refine ⟨fun i => -δ₀ i, fun i hi => by simp [hδ0 i hi], ⟨j, by simpa using hj⟩, ?_, ?_⟩
      · simp [neg_smul, Finset.sum_neg_distrib, hδsum]
      · simp only [Finset.sum_neg_distrib]; linarith
  set S : Finset (Fin n) := Finset.univ.filter (fun i => δ i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hδne
    exact ⟨i, by simp [hS, hi]⟩
  let tt : Fin n → ℝ := fun i => if 0 < δ i then (1 - w i) / δ i else (- w i) / δ i
  obtain ⟨i0, hi0S, hi0min⟩ := Finset.exists_min_image S tt hSne
  have hSJ : ∀ i ∈ S, i ∈ Frac w := by
    intro i hi
    by_contra h
    have := hδJ i h
    simp [hS, this] at hi
  have hwfrac : ∀ i ∈ Frac w, 0 < w i ∧ w i < 1 := by
    intro i hi; simpa [Frac] using hi
  have htt_pos : ∀ i ∈ S, 0 < tt i := by
    intro i hi
    have hd : δ i ≠ 0 := by simpa [hS] using hi
    obtain ⟨h1, h2⟩ := hwfrac i (hSJ i hi)
    by_cases hp : 0 < δ i
    · simp only [tt, hp, if_true]; exact div_pos (by linarith) hp
    · have hn : δ i < 0 := lt_of_le_of_ne (not_lt.mp hp) hd
      simp only [tt, hp, if_false]; exact div_pos_of_neg_of_neg (by linarith) hn
  set T := tt i0 with hT
  have hTpos : 0 < T := htt_pos i0 hi0S
  have hbound : ∀ i, w i + T * δ i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : i ∈ S
    · have hd : δ i ≠ 0 := by simpa [hS] using hi
      obtain ⟨h1, h2⟩ := hwfrac i (hSJ i hi)
      have hle : T ≤ tt i := hi0min i hi
      by_cases hp : 0 < δ i
      · simp only [tt, hp, if_true] at hle
        rw [le_div_iff₀ hp] at hle
        constructor <;> nlinarith
      · have hn : δ i < 0 := lt_of_le_of_ne (not_lt.mp hp) hd
        simp only [tt, hp, if_false] at hle
        rw [le_div_iff_of_neg hn] at hle
        constructor <;> nlinarith
    · have : δ i = 0 := by simpa [hS] using hi
      simpa [this] using hw i
  set w' : Fin n → ℝ := fun i => w i + T * δ i with hw'
  have hw'I : ∀ i, w' i ∈ Set.Icc (0 : ℝ) 1 := hbound
  have hw'v : ∑ i, w' i • v i = 0 := by
    have : ∑ i, w' i • v i = ∑ i, w i • v i + T • ∑ i, δ i • v i := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw', add_smul, mul_smul]
    rw [this, hsum, hδv]; simp
  have hw'mass : ∑ i, w i ≤ ∑ i, w' i := by
    have : ∑ i, w' i = ∑ i, w i + T * ∑ i, δ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [this]; nlinarith
  -- fractional set shrinks
  have hsub : Frac w' ⊂ Frac w := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i0, hSJ i0 hi0S, ?_⟩
      have hd : δ i0 ≠ 0 := by simpa [hS] using hi0S
      simp only [Frac, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
      intro hpos
      by_cases hp : 0 < δ i0
      · have : w' i0 = 1 := by
          simp only [hw', hT, tt, hp, if_true]; field_simp; ring
        rw [this]
      · have : w' i0 = 0 := by
          simp only [hw', hT, tt, hp, if_false]; field_simp; ring
        rw [this] at hpos; exact absurd hpos (lt_irrefl 0)
    · intro i hi
      simp only [Frac, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_cases hJi : i ∈ Frac w
      · exact hwfrac i hJi
      · have h0 := hδJ i hJi
        have hwi : w i = 0 ∨ w i = 1 := by
          simp only [Frac, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hJi
          have := hw i
          rcases lt_or_eq_of_le this.1 with h | h
          · right; exact le_antisymm this.2 (hJi h)
          · left; exact h.symm
        simp only [hw', h0, mul_zero, add_zero] at hi
        rcases hwi with h | h <;> rw [h] at hi <;> linarith [hi.1, hi.2]
  obtain ⟨w'', h1, h2, h3, h4⟩ := ih (Frac w').card (hk ▸ Finset.card_lt_card hsub) w' hw'I hw'v rfl
  exact ⟨w'', h1, h2, hw'mass.trans h3, h4⟩

lemma card_supp_of_mass {n d : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (hm : (d : ℝ) - 1 < ∑ i, w i) : d ≤ (Finset.univ.filter (fun i => w i ≠ 0)).card := by
  have h1 : ∑ i, w i ≤ ((Finset.univ.filter (fun i => w i ≠ 0)).card : ℝ) := by
    rw [← Finset.sum_filter_ne_zero]
    calc ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), w i
        ≤ ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (hw i).2
      _ = _ := by simp
  have h2 : (d : ℝ) - 1 < ((Finset.univ.filter (fun i => w i ≠ 0)).card : ℝ) := lt_of_lt_of_le hm h1
  have h3 : (d : ℝ) < ((Finset.univ.filter (fun i => w i ≠ 0)).card : ℝ) + 1 := by linarith
  have h4 : d < (Finset.univ.filter (fun i => w i ≠ 0)).card + 1 := by exact_mod_cast h3
  omega

end SampleRemoval.Dev.L32

namespace SampleRemoval

open Matrix

theorem chk_lemma_3_2 {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ) (θ : ℝ)
    (hGP : GeneralPosition x) (w : Fin n → ℝ) (hw : w ∈ feasible x y e θ)
    (hmass : (d : ℝ) - 1 < ∑ i, w i) :
    ∃ w' ∈ feasible x y e θ, ∑ i, w i ≤ ∑ i, w' i ∧ ols x y w' = ols x y w ∧
      (Finset.univ.filter (fun i => 0 < w' i ∧ w' i < 1)).card ≤ d := by
  obtain ⟨hwI, hG, hθ⟩ := hw
  have hne := (SampleRemoval.normal_equations x y w hwI hG (ols x y w)).mpr rfl
  obtain ⟨w', h1, h2, h3, h4⟩ := Dev.L32.reduce (fun i => (y i - x i ⬝ᵥ ols x y w) • x i) _ w hwI
    (by rw [← hne]; refine Finset.sum_congr rfl fun i _ => ?_; simp [mul_smul]) rfl
  have hmass' : (d : ℝ) - 1 < ∑ i, w' i := lt_of_lt_of_le hmass h3
  have hG' : (gram x w').PosDef :=
    (SampleRemoval.gram_posDef_iff_card_support x hGP w' h1).mpr
      (Dev.L32.card_supp_of_mass w' h1 hmass')
  have hols : ols x y w' = ols x y w :=
    ((SampleRemoval.normal_equations x y w' h1 hG' (ols x y w)).mp
      (by rw [← h2]; refine Finset.sum_congr rfl fun i _ => ?_; simp [mul_smul])).symm
  exact ⟨w', ⟨h1, hG', by rw [hols]; exact hθ⟩, h3, hols, h4⟩

end SampleRemoval
end

theorem solution : type_of% @SampleRemoval.chk_lemma_3_2 := @SampleRemoval.chk_lemma_3_2
