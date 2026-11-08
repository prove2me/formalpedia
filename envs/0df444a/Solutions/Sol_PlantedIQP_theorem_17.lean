-- Prove2me | solution 1 for PlantedIQP.theorem_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:44:26.805172+00:00
-- url     : https://prove2.me/submissions/0645b4e1-2d3b-442a-b8b2-39fb64d72f0b

import Mathlib
import Definitions.Def_PlantedIQP_triForm
import Definitions.Def_PlantedIQP_hessSlice

set_option autoImplicit false

namespace Aux_PlantedIQP_17
open PlantedIQP PlantedIQP.CubicPoly

theorem two_z (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide
theorem h2 : (2 : ZMod 2) = 0 := rfl

theorem std_ne {n : ℕ} (i l : Fin n) (h : l ≠ i) : stdBasis i l = 0 := by
  simp [stdBasis, Pi.single_apply, h]
theorem std_eq {n : ℕ} (i : Fin n) : stdBasis i i = 1 := by simp [stdBasis]

theorem prod_agree {n : ℕ} (T : Finset (Fin n)) (y u : Vec n) (h : ∀ l ∈ T, y l = u l) :
    ∏ l ∈ T, y l = ∏ l ∈ T, u l := Finset.prod_congr rfl h

theorem delta {n : ℕ} (S : Finset (Fin n)) (u : Vec n) (i j : Fin n) (hij : i ≠ j) :
    ∏ l ∈ S, (u + stdBasis i + stdBasis j) l + ∏ l ∈ S, (u + stdBasis i) l +
      ∏ l ∈ S, (u + stdBasis j) l + ∏ l ∈ S, u l =
    if i ∈ S ∧ j ∈ S then ∏ l ∈ (S.erase i).erase j, u l else 0 := by
  have hA : ∀ l, l ≠ i → l ≠ j → (u + stdBasis i + stdBasis j) l = u l := by
    intro l h1 h2'; simp [std_ne i l h1, std_ne j l h2']
  have hB : ∀ l, l ≠ i → (u + stdBasis i) l = u l := by
    intro l h1; simp [std_ne i l h1]
  have hC : ∀ l, l ≠ j → (u + stdBasis j) l = u l := by
    intro l h1; simp [std_ne j l h1]
  have hji : j ≠ i := Ne.symm hij
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · rw [if_pos ⟨hi, hj⟩]
    have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
    have hrest : ∀ y : Vec n, (∀ l, l ≠ i → l ≠ j → y l = u l) →
        ∏ l ∈ S, y l = y i * (y j * ∏ l ∈ (S.erase i).erase j, u l) := by
      intro y hy
      rw [← Finset.mul_prod_erase S _ hi, ← Finset.mul_prod_erase (S.erase i) _ hj']
      congr 2
      apply Finset.prod_congr rfl
      intro l hl
      have h1 := Finset.ne_of_mem_erase hl
      have h2' := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      exact hy l h2' h1
    rw [hrest _ hA, hrest _ (fun l h1 _ => hB l h1), hrest _ (fun l _ h2' => hC l h2'),
      hrest u (fun _ _ _ => rfl)]
    simp only [Pi.add_apply, std_eq, std_ne i j hji, std_ne j i hij, add_zero]
    linear_combination (2 * u i * u j + u i + u j) * (∏ l ∈ (S.erase i).erase j, u l) * h2
  · rw [if_neg (fun h => hj h.2)]
    have hrest : ∀ y : Vec n, (∀ l, l ≠ i → y l = u l) →
        ∏ l ∈ S, y l = y i * ∏ l ∈ S.erase i, u l := by
      intro y hy
      rw [← Finset.mul_prod_erase S _ hi]
      congr 1
      apply Finset.prod_congr rfl
      intro l hl
      exact hy l (Finset.ne_of_mem_erase hl)
    have hrest2 : ∀ y : Vec n, (∀ l, l ≠ i → l ≠ j → y l = u l) →
        ∏ l ∈ S, y l = y i * ∏ l ∈ S.erase i, u l := by
      intro y hy
      rw [← Finset.mul_prod_erase S _ hi]
      congr 1
      apply Finset.prod_congr rfl
      intro l hl
      have h1 := Finset.ne_of_mem_erase hl
      have hlj : l ≠ j := fun h => hj (h ▸ Finset.mem_of_mem_erase hl)
      exact hy l h1 hlj
    rw [hrest2 _ hA, hrest _ hB, hrest2 _ (fun l _ h2' => hC l h2'), hrest u (fun _ _ => rfl)]
    simp only [Pi.add_apply, std_eq, std_ne j i hij, add_zero]
    linear_combination (2 * u i + 1) * (∏ l ∈ S.erase i, u l) * h2
  · rw [if_neg (fun h => hi h.1)]
    have hrest : ∀ y : Vec n, (∀ l, l ≠ i → l ≠ j → y l = u l) →
        ∏ l ∈ S, y l = y j * ∏ l ∈ S.erase j, u l := by
      intro y hy
      rw [← Finset.mul_prod_erase S _ hj]
      congr 1
      apply Finset.prod_congr rfl
      intro l hl
      have h1 := Finset.ne_of_mem_erase hl
      have hli : l ≠ i := fun h => hi (h ▸ Finset.mem_of_mem_erase hl)
      exact hy l hli h1
    rw [hrest _ hA, hrest _ (fun l h1 _ => hB l h1), hrest _ (fun l _ h2' => hC l h2'),
      hrest u (fun _ _ _ => rfl)]
    simp only [Pi.add_apply, std_eq, std_ne i j hji, add_zero, zero_add]
    linear_combination (2 * u j + 1) * (∏ l ∈ S.erase j, u l) * h2
  · rw [if_neg (fun h => hi h.1)]
    have hrest : ∀ y : Vec n, (∀ l, l ≠ i → l ≠ j → y l = u l) → ∏ l ∈ S, y l = ∏ l ∈ S, u l := by
      intro y hy
      apply Finset.prod_congr rfl
      intro l hl
      exact hy l (fun h => hi (h ▸ hl)) (fun h => hj (h ▸ hl))
    rw [hrest _ hA, hrest _ (fun l h1 _ => hB l h1), hrest _ (fun l _ h2' => hC l h2')]
    linear_combination (∏ l ∈ S, u l) * (h2 + h2)


theorem slice_apply {n : ℕ} (f : CubicPoly n) (u : Vec n) (i j : Fin n) :
    sliceMatrix f u i j = ∑ k, u k * f.coeff3 k i j := by
  simp [sliceMatrix, triForm, stdBasis, Pi.single_apply]

theorem quad_sum {n : ℕ} (f : CubicPoly n) (u : Vec n) (i j : Fin n) (hij : i ≠ j) :
    ∑ T : Mono n 2, f.c2 T * (if i ∈ T.1 ∧ j ∈ T.1 then ∏ l ∈ (T.1.erase i).erase j, u l else 0)
      = f.coeff2 i j := by
  have hcard : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
  unfold coeff2
  rw [dif_pos hcard, Finset.sum_eq_single ⟨{i, j}, hcard⟩]
  · have : (({i, j} : Finset (Fin n)).erase i).erase j = ∅ := by
      ext l; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false]; tauto
    rw [if_pos ⟨by simp, by simp⟩]
    show f.c2 _ * ∏ l ∈ (({i, j} : Finset (Fin n)).erase i).erase j, u l = _
    rw [this, Finset.prod_empty, mul_one]
  · intro T _ hT
    rw [if_neg, mul_zero]
    rintro ⟨hi, hj⟩
    apply hT
    apply Subtype.ext
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> assumption
    · rw [T.2, hcard]
  · simp

theorem cubic_sum {n : ℕ} (f : CubicPoly n) (u : Vec n) (i j : Fin n) (hij : i ≠ j) :
    ∑ S : Mono n 3, f.c3 S * (if i ∈ S.1 ∧ j ∈ S.1 then ∏ l ∈ (S.1.erase i).erase j, u l else 0)
      = ∑ k, u k * f.coeff3 k i j := by
  have hc : ∀ k, k ≠ i → k ≠ j → ({k, i, j} : Finset (Fin n)).card = 3 := by
    intro k hki hkj
    rw [Finset.card_insert_of_notMem (by simp [hki, hkj]), Finset.card_pair hij]
  have hR : ∀ k, f.coeff3 k i j * u k = if k ≠ i ∧ k ≠ j then
      (if h : k ≠ i ∧ k ≠ j then f.c3 ⟨{k, i, j}, hc k h.1 h.2⟩ * u k else 0) else 0 := by
    intro k
    unfold coeff3
    by_cases hk : k ≠ i ∧ k ≠ j
    · rw [dif_pos (hc k hk.1 hk.2), if_pos hk, dif_pos hk]
    · rw [if_neg hk]
      have : ¬ ({k, i, j} : Finset (Fin n)).card = 3 := by
        intro h3
        apply hk
        push_neg at hk
        by_cases hki : k = i
        · subst hki
          have : ({k, k, j} : Finset (Fin n)) = {k, j} := by simp
          rw [this, Finset.card_pair hij] at h3; omega
        · have hkj := hk hki
          subst hkj
          have : ({k, i, k} : Finset (Fin n)) = {k, i} := by
            ext l; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [this, Finset.card_pair hki] at h3; omega
      rw [dif_neg this, zero_mul]
  simp_rw [mul_comm (u _) (f.coeff3 _ i j), hR, ← Finset.sum_filter]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k hk => (⟨{k, i, j}, hc k (Finset.mem_filter.mp hk).2.1
    (Finset.mem_filter.mp hk).2.2⟩ : Mono n 3))
  · intro k hk
    simp
  · intro k hk k' hk' h
    have := congrArg (fun S : Mono n 3 => k ∈ S.1) h
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, eq_iff_iff, true_iff] at this
    have hk2 := (Finset.mem_filter.mp hk).2
    rcases this with h1 | h1 | h1
    · exact h1
    · exact absurd h1 hk2.1
    · exact absurd h1 hk2.2
  · intro S hS
    obtain ⟨hi, hj⟩ := (Finset.mem_filter.mp hS).2
    have hcard1 : ((S.1.erase i).erase j).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩),
        Finset.card_erase_of_mem hi, S.2]
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard1
    have hkmem : k ∈ (S.1.erase i).erase j := by rw [hk]; simp
    have hkj := Finset.ne_of_mem_erase hkmem
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hkmem)
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki, hkj⟩, ?_⟩
    apply Subtype.ext
    simp only
    apply Finset.eq_of_subset_of_card_le
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hkmem)
      · exact hi
      · exact hj
    · rw [S.2, hc k hki hkj]
  · intro k hk
    have hk2 := (Finset.mem_filter.mp hk).2
    rw [dif_pos hk2]
    have : (({k, i, j} : Finset (Fin n)).erase i).erase j = {k} := by
      ext l
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hlj, hli, h | h | h⟩
        · exact h
        · exact absurd h hli
        · exact absurd h hlj
      · rintro rfl; exact ⟨hk2.2, hk2.1, Or.inl rfl⟩
    show _ = f.c3 _ * ∏ l ∈ (({k, i, j} : Finset (Fin n)).erase i).erase j, u l
    rw [this, Finset.prod_singleton]

theorem hess_apply {n : ℕ} (f : CubicPoly n) (u : Vec n) (i j : Fin n) (hij : i ≠ j) :
    hessSlice f u i j = ∑ k, u k * f.coeff3 k i j + f.coeff2 i j := by
  unfold hessSlice eval
  simp only [Matrix.of_apply]
  rw [← cubic_sum f u i j hij, ← quad_sum f u i j hij]
  simp_rw [← delta _ u i j hij]
  have hlin : ∀ l, f.c1 l * (u + stdBasis i + stdBasis j) l + f.c1 l * (u + stdBasis i) l +
      f.c1 l * (u + stdBasis j) l + f.c1 l * u l = 0 := by
    intro l
    simp only [Pi.add_apply]
    linear_combination (f.c1 l * (2 * u l + stdBasis i l + stdBasis j l)) * h2
  have hz : ∑ l, (f.c1 l * (u + stdBasis i + stdBasis j) l + f.c1 l * (u + stdBasis i) l +
      f.c1 l * (u + stdBasis j) l + f.c1 l * u l) = 0 := Finset.sum_eq_zero (fun l _ => hlin l)
  simp only [mul_add, Finset.sum_add_distrib] at hz ⊢
  linear_combination hz

theorem diag {n : ℕ} (f : CubicPoly n) (u : Vec n) (i : Fin n) :
    hessSlice f u i i = 0 ∧ f.coeff2 i i = 0 ∧ sliceMatrix f u i i = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold hessSlice
    simp only [Matrix.of_apply]
    have : u + stdBasis i + stdBasis i = u := by
      funext l; simp only [Pi.add_apply]; rw [add_assoc, two_z, add_zero]
    rw [this]
    linear_combination (f.eval u + f.eval (u + stdBasis i)) * h2
  · unfold coeff2; rw [dif_neg]; simp
  · rw [slice_apply]
    apply Finset.sum_eq_zero
    intro k _
    unfold coeff3
    rw [dif_neg, mul_zero]
    intro h
    have : ({k, i, i} : Finset (Fin n)).card ≤ 2 := by
      have : ({k, i, i} : Finset (Fin n)) = {k, i} := by simp
      rw [this]; exact Finset.card_le_two
    omega

end Aux_PlantedIQP_17

open PlantedIQP Aux_PlantedIQP_17 in
theorem solution {n : ℕ} (f : CubicPoly n) (u : Vec n) :
    sliceMatrix f u = hessSlice f u + quadMatrix f ∧
      ∀ v w : Vec n, triForm f u v w = ∑ i, ∑ j, v i * (hessSlice f u + quadMatrix f) i j * w j := by
  have h1 : sliceMatrix f u = hessSlice f u + quadMatrix f := by
    ext i j
    simp only [Matrix.add_apply, quadMatrix, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      obtain ⟨a, b, c⟩ := diag f u i
      rw [a, b, c, add_zero]
    · rw [slice_apply, hess_apply f u i j hij]
      linear_combination (-(f.coeff2 i j)) * h2
  refine ⟨h1, fun v w => ?_⟩
  rw [← h1]
  simp only [slice_apply, triForm, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  ring
