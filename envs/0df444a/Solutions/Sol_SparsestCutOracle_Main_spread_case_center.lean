-- Prove2me | solution 1 for SparsestCutOracle.Main.spread_case_center
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:08.639751+00:00
-- url     : https://prove2.me/submissions/b22c1374-d402-4646-b7cc-72c6457455b7

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

open scoped BigOperators

lemma sc_sqdist_self {n : ℕ} (X : Mat n) (i : Fin n) : sqdist X i i = 0 := by
  simp [sqdist]
  ring

lemma sc_sqdist_comm {n : ℕ} (X : Mat n) (hX : X.PosSemidef) (i j : Fin n) :
    sqdist X i j = sqdist X j i := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  simp only [sqdist, hs]
  ring

lemma sc_sqdist_nonneg {n : ℕ} (X : Mat n) (hX : X.PosSemidef) (i j : Fin n) :
    0 ≤ sqdist X i j := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib, mul_ite, ite_mul] at h
  rw [hs] at h
  dsimp [sqdist]
  nlinarith [h]

lemma double_sum_add {n : ℕ} (a b c : Fin n → Fin n → ℝ)
    (h : ∀ i j, a i j + b i j = c i j) :
    (∑ i, ∑ j, a i j) + (∑ i, ∑ j, b i j) = ∑ i, ∑ j, c i j := by
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact h i j

lemma sc_dot_K_spread {n : ℕ} (π : Fin n → ℝ) (X : Mat n) (hX : X.PosSemidef) :
    dot (K π) X = (1 / 2 : ℝ) * spread π X Finset.univ := by
  have hs : ∀ i j, X j i = X i j := by
    intro i j
    simpa using hX.isHermitian.apply i j
  simp [dot, K, D, J, Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply,
    spread, sqdist, totalWeight, mass, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp_rw [ite_mul]
  simp_rw [zero_mul]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun x i => π x * π i * X i i * (1 / 2))]
  simp_rw [hs]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_neg_distrib]
  have hdiag := double_sum_add
    (fun i j => π i * π j * X i i * (1 / 2))
    (fun i j => π j * π i * X i i * (1 / 2))
    (fun i j => π j * π i * X i i) (by intros; ring)
  rw [hdiag]
  ring

lemma sc_mass_mono {n : ℕ} (π : Fin n → ℝ) (hπ : ∀ v, 0 < π v)
    {A B : Finset (Fin n)} (hAB : A ⊆ B) : mass π A ≤ mass π B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => (hπ i).le)

lemma sc_mass_sdiff_add_inter {n : ℕ} (π : Fin n → ℝ) (A B : Finset (Fin n)) :
    mass π (A \ B) + mass π (A ∩ B) = mass π A := by
  have h := Finset.sum_sdiff (f := π) (Finset.inter_subset_left : A ∩ B ⊆ A)
  have heq : A \ (A ∩ B) = A \ B := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [heq] at h
  exact h

lemma sc_total_pos {n : ℕ} (hn : 1 ≤ n) (π : Fin n → ℝ) (hπ : ∀ v, 0 < π v) :
    0 < totalWeight π := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  exact Finset.sum_pos (fun i _ => hπ i) Finset.univ_nonempty

lemma sc_r₀_sq : r₀ ^ 2 = (1 / 40 : ℝ) := by
  rw [r₀, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma sc_exists_dense_two {n : ℕ} (hn : 1 ≤ n) (π : Fin n → ℝ)
    (hπ : ∀ v, 0 < π v) (X : Mat n) (hX : X.PosSemidef)
    (hupper : dot (K π) X ≤ totalWeight π ^ 2) :
    ∃ i, totalWeight π / 2 ≤ mass π (ball X i 2) := by
  have hPi := sc_total_pos hn π hπ
  by_contra h
  push_neg at h
  have hrow : ∀ i, 2 * totalWeight π * π i <
      ∑ j, π i * π j * sqdist X i j := by
    intro i
    let B := ball X i 2
    have hsplit := Finset.sum_add_sum_compl B π
    have hmass : totalWeight π / 2 < mass π Bᶜ := by
      have hb : mass π B < totalWeight π / 2 := h i
      have heq : mass π B + mass π Bᶜ = totalWeight π := hsplit
      linarith
    have hterms : (4 : ℝ) * π i * mass π Bᶜ ≤
        ∑ j ∈ Bᶜ, π i * π j * sqdist X i j := by
      rw [mass, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjfar : (2 : ℝ) ^ 2 < sqdist X i j := by
        have := hj
        simp [B, ball] at this
        exact this
      have hp : 0 < π i * π j := mul_pos (hπ i) (hπ j)
      nlinarith
    have hrestrict : (∑ j ∈ Bᶜ, π i * π j * sqdist X i j) ≤
        ∑ j, π i * π j * sqdist X i j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact mul_nonneg (mul_nonneg (hπ i).le (hπ j).le) (sc_sqdist_nonneg X hX i j)
    calc
      2 * totalWeight π * π i = 4 * π i * (totalWeight π / 2) := by ring
      _ < 4 * π i * mass π Bᶜ := by nlinarith [mul_pos (by norm_num : (0:ℝ) < 4) (hπ i)]
      _ ≤ ∑ j ∈ Bᶜ, π i * π j * sqdist X i j := hterms
      _ ≤ ∑ j, π i * π j * sqdist X i j := hrestrict
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hsum : (∑ i, 2 * totalWeight π * π i) <
      ∑ i, ∑ j, π i * π j * sqdist X i j :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hrow i)
  have htotal : (∑ i, 2 * totalWeight π * π i) = 2 * totalWeight π ^ 2 := by
    rw [← Finset.mul_sum]
    change 2 * totalWeight π * totalWeight π = 2 * totalWeight π ^ 2
    ring
  have hspread : 2 * totalWeight π ^ 2 < spread π X Finset.univ := by
    rw [← htotal]
    exact hsum
  rw [sc_dot_K_spread π X hX] at hupper
  nlinarith

lemma sc_row_spread {n : ℕ} (π : Fin n → ℝ) (hπ : ∀ v, 0 < π v)
    (X : Mat n) (hX : X.PosSemidef)
    (hballs : ∀ i, mass π (ball X i r₀) < totalWeight π / 4)
    (A : Finset (Fin n)) (hmassA : totalWeight π / 2 ≤ mass π A) (i : Fin n) :
    (totalWeight π / 160) * π i ≤ ∑ j ∈ A, π i * π j * sqdist X i j := by
  let C := A \ ball X i r₀
  have hmassC : totalWeight π / 4 ≤ mass π C := by
    have hinter : mass π (A ∩ ball X i r₀) ≤ mass π (ball X i r₀) :=
      sc_mass_mono π hπ Finset.inter_subset_right
    have hdecomp := sc_mass_sdiff_add_inter π A (ball X i r₀)
    have hb := hballs i
    dsimp [C]
    linarith
  have hterms : r₀ ^ 2 * π i * mass π C ≤
      ∑ j ∈ C, π i * π j * sqdist X i j := by
    rw [mass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjfar : r₀ ^ 2 < sqdist X i j := by
      have := hj
      simp [C, ball] at this
      exact this.2
    have hp : 0 < π i * π j := mul_pos (hπ i) (hπ j)
    nlinarith
  have hrestrict : (∑ j ∈ C, π i * π j * sqdist X i j) ≤
      ∑ j ∈ A, π i * π j * sqdist X i j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro j _ _
    exact mul_nonneg (mul_nonneg (hπ i).le (hπ j).le) (sc_sqdist_nonneg X hX i j)
  calc
    (totalWeight π / 160) * π i = r₀ ^ 2 * π i * (totalWeight π / 4) := by
      rw [sc_r₀_sq]
      ring
    _ ≤ r₀ ^ 2 * π i * mass π C := by
      rw [sc_r₀_sq]
      have hp : 0 < (1 / 40 : ℝ) * π i := mul_pos (by norm_num) (hπ i)
      nlinarith
    _ ≤ ∑ j ∈ C, π i * π j * sqdist X i j := hterms
    _ ≤ ∑ j ∈ A, π i * π j * sqdist X i j := hrestrict

end SparsestCutOracle.Main

open SparsestCutOracle.Main

theorem solution {n : ℕ} (hn : 1 ≤ n) (π : Fin n → ℝ)
    (hπ : ∀ v, 0 < π v) (X : Mat n) (hX : X.PosSemidef)
    (htrace : dot (D π) X = totalWeight π)
    (hlower : (4 / 5 : ℝ) * totalWeight π ^ 2 ≤ dot (K π) X)
    (hupper : dot (K π) X ≤ totalWeight π ^ 2)
    (hballs : ∀ i, mass π (ball X i r₀) < totalWeight π / 4) :
    ∃ i₀ : Fin n, spreadCenter π X = some i₀ ∧
      let A := ball X i₀ 4
      i₀ ∈ A ∧ totalWeight π / 2 ≤ mass π A ∧
      (∀ i ∈ A, sqdist X i i₀ ≤ 16) ∧
      (1 / 320 : ℝ) * totalWeight π ^ 2 ≤ spread π X A := by
  classical
  obtain ⟨i, hi⟩ := sc_exists_dense_two hn π hπ X hX hupper
  have hsub : ball X i 2 ⊆ ball X i 4 := by
    intro j hj
    have hd : sqdist X i j ≤ (2 : ℝ) ^ 2 := (Finset.mem_filter.mp hj).2
    have hd' : sqdist X i j ≤ (4 : ℝ) ^ 2 := by norm_num at hd ⊢; linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hd'⟩
  have hi4 : totalWeight π / 2 ≤ mass π (ball X i 4) :=
    hi.trans (sc_mass_mono π hπ hsub)
  let C := Finset.univ.filter fun i => totalWeight π / 2 ≤ mass π (ball X i 4)
  have hC : C.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi4⟩⟩
  let i₀ := C.min' hC
  have hi₀C : i₀ ∈ C := C.min'_mem hC
  have hmassA : totalWeight π / 2 ≤ mass π (ball X i₀ 4) :=
    (Finset.mem_filter.mp hi₀C).2
  have hcenter : spreadCenter π X = some i₀ := by
    simp [spreadCenter, C, hC, i₀]
  refine ⟨i₀, hcenter, ?_⟩
  have hself : i₀ ∈ ball X i₀ 4 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i₀, ?_⟩
    rw [sc_sqdist_self]
    norm_num
  refine ⟨hself, hmassA, ?_, ?_⟩
  · intro j hj
    rw [sc_sqdist_comm X hX j i₀]
    have hd : sqdist X i₀ j ≤ (4 : ℝ) ^ 2 := (Finset.mem_filter.mp hj).2
    norm_num at hd ⊢
    exact hd
  · have hrows : (∑ j ∈ ball X i₀ 4, (totalWeight π / 160) * π j) ≤
        spread π X (ball X i₀ 4) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sc_row_spread π hπ X hX hballs (ball X i₀ 4) hmassA j
    rw [← Finset.mul_sum] at hrows
    change (totalWeight π / 160) * mass π (ball X i₀ 4) ≤ _ at hrows
    have hPi := sc_total_pos hn π hπ
    have hfactor : 0 ≤ totalWeight π *
        (mass π (ball X i₀ 4) - totalWeight π / 2) :=
      mul_nonneg hPi.le (sub_nonneg.mpr hmassA)
    nlinarith
