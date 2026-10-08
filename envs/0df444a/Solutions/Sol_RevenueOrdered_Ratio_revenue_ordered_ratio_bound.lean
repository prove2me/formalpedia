-- Prove2me | solution 1 for RevenueOrdered.Ratio.revenue_ordered_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:25:18.84264+00:00
-- url     : https://prove2.me/submissions/1e14f309-c084-405b-9c52-aeb9e8da46c4

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

set_option autoImplicit false

universe u

namespace P779221ce

open RevenueOrdered.Ratio

variable {C : Type u} [Fintype C]

lemma level_eq {r : C → ℝ} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ numVals r) :
    level r i = sortedVals r ⟨i - 1, by omega⟩ := by
  unfold level
  rw [dif_pos ⟨h1, h2⟩]

lemma level_zero (r : C → ℝ) : level r 0 = 0 := by
  unfold level
  rw [dif_neg (by omega)]

lemma level_lt {r : C → ℝ} {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ numVals r) :
    level r i < level r j := by
  rw [level_eq hi (by omega), level_eq (by omega) hj]
  apply (sortedVals r).strictMono
  rw [Fin.mk_lt_mk]
  omega

lemma level_mem {r : C → ℝ} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ numVals r) :
    level r i ∈ revVals r := by
  rw [level_eq h1 h2]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma level_pos {r : C → ℝ} (hr : ∀ x, 0 < r x) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ numVals r) :
    0 < level r i := by
  have h := level_mem h1 h2
  unfold revVals at h
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp h
  rw [← hx]; exact hr x

lemma exists_level (r : C → ℝ) (x : C) :
    ∃ j, 1 ≤ j ∧ j ≤ numVals r ∧ level r j = r x := by
  have hx : r x ∈ revVals r := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hrange : Set.range (sortedVals r) = (revVals r : Set ℝ) :=
    Finset.range_orderEmbOfFin _ _
  have : r x ∈ Set.range (sortedVals r) := by
    rw [hrange]; exact hx
  obtain ⟨i, hi⟩ := this
  refine ⟨i.1 + 1, by omega, by omega, ?_⟩
  rw [level_eq (by omega) (by omega)]
  rw [← hi]
  congr 1

lemma telescope (g : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.Icc 1 j, (g i - g (i - 1)) = g j - g 0 := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp

lemma d_nonneg {r : C → ℝ} (hr : ∀ x, 0 < r x) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ numVals r) :
    0 ≤ level r i - level r (i - 1) := by
  rcases Nat.lt_or_ge 1 i with h | h
  · have := level_lt (r := r) (i := i - 1) (j := i) (by omega) (by omega) h2
    linarith
  · have hi : i = 1 := by omega
    subst hi
    have := level_pos hr (le_refl 1) h2
    simp [level_zero]
    linarith

lemma r_decomp [DecidableEq C] (r : C → ℝ) (x : C) :
    r x = ∑ i ∈ Finset.Icc 1 (numVals r),
      (if x ∈ roSet r i then level r i - level r (i - 1) else 0) := by
  obtain ⟨j, hj1, hj2, hj⟩ := exists_level r x
  rw [← Finset.sum_filter]
  have hfil : (Finset.Icc 1 (numVals r)).filter (fun i => x ∈ roSet r i) = Finset.Icc 1 j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, roSet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      by_contra hc
      rw [not_le] at hc
      have := level_lt (r := r) hj1 hc h2
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, by omega⟩, ?_⟩
      rcases Nat.lt_or_ge i j with h | h
      · have := level_lt (r := r) h1 h hj2
        linarith
      · have : i = j := by omega
        subst this; exact le_of_eq hj
  rw [hfil, telescope (level r) j, level_zero, hj]
  ring

lemma key_bound [DecidableEq C] [Nonempty C] {P : C → Finset C → ℝ} (hP : RevenueOrdered.Ratio.IsRegular P)
    (r : C → ℝ) (hr : ∀ x, 0 < r x) (S : Finset C) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ numVals r) :
    level r i * ∑ x ∈ S.filter (fun x => x ∈ roSet r i), P x S ≤ roValue P r := by
  set T := S.filter (fun x => x ∈ roSet r i) with hT
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hTR : T ⊆ roSet r i := fun x hx => (Finset.mem_filter.mp hx).2
  have s1 : ∑ x ∈ T, P x S ≤ ∑ x ∈ T, P x T :=
    Finset.sum_le_sum (fun x hx => hP.mono T S x hTS hx)
  have s2 : ∑ x ∈ T, P x T ≤ ∑ x ∈ roSet r i, P x (roSet r i) := by
    have := hP.noPurchase_mono T (roSet r i) hTR
    unfold noPurchase at this
    linarith
  have s3 : level r i * ∑ x ∈ roSet r i, P x (roSet r i) ≤ revenue P r (roSet r i) := by
    unfold revenue
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have hl : level r i ≤ r x := by
      simp only [roSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
    have := hP.nonneg x (roSet r i)
    nlinarith
  have s4 : revenue P r (roSet r i) ≤ roValue P r := by
    unfold roValue
    exact Finset.le_sup' (fun i => revenue P r (roSet r i))
      (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hl := level_pos hr h1 h2
  have : level r i * ∑ x ∈ T, P x S ≤ level r i * ∑ x ∈ roSet r i, P x (roSet r i) :=
    mul_le_mul_of_nonneg_left (by linarith) hl.le
  linarith

lemma part1 [DecidableEq C] [Nonempty C] {P : C → Finset C → ℝ} (hP : RevenueOrdered.Ratio.IsRegular P)
    (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    opt P r ≤ ratioSum r * roValue P r := by
  unfold opt
  apply Finset.sup'_le
  intro S _
  have hrev : revenue P r S = ∑ i ∈ Finset.Icc 1 (numVals r),
      (level r i - level r (i - 1)) * ∑ x ∈ S.filter (fun x => x ∈ roSet r i), P x S := by
    unfold revenue
    conv_lhs => arg 2; ext x; rw [r_decomp r x, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [hrev]
  unfold ratioSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
  have hl := level_pos hr h1 h2
  have hd := d_nonneg hr h1 h2
  have hk := key_bound hP r hr S h1 h2
  have hQ : ∑ x ∈ S.filter (fun x => x ∈ roSet r i), P x S ≤ roValue P r / level r i := by
    rw [le_div_iff₀ hl]; linarith
  calc (level r i - level r (i - 1)) * ∑ x ∈ S.filter (fun x => x ∈ roSet r i), P x S
      ≤ (level r i - level r (i - 1)) * (roValue P r / level r i) :=
        mul_le_mul_of_nonneg_left hQ hd
    _ = (level r i - level r (i - 1)) / level r i * roValue P r := by ring

lemma part2 [Nonempty C] (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    ratioSum r ≤ 1 + Real.log (level r (numVals r) / level r 1) := by
  have hk := numVals_pos r
  have hl1 := level_pos hr (le_refl 1) hk
  have main : ∀ m, 1 ≤ m → m ≤ numVals r →
      ∑ i ∈ Finset.Icc 1 m, (level r i - level r (i - 1)) / level r i
        ≤ 1 + (Real.log (level r m) - Real.log (level r 1)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      simp [level_zero]
      rw [div_self hl1.ne']
    | succ n hn ih =>
      intro hn1
      rw [Finset.sum_Icc_succ_top (by omega)]
      have ih' := ih (by omega)
      have ha := level_pos hr (by omega : 1 ≤ n + 1) hn1
      have hb := level_pos hr hn (by omega)
      have hlt := level_lt (r := r) hn (Nat.lt_succ_self n) hn1
      have hx : 1 - (level r (n + 1) / level r n)⁻¹ ≤ Real.log (level r (n + 1) / level r n) :=
        Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
      rw [Real.log_div ha.ne' hb.ne', inv_div] at hx
      have he : (level r (n + 1) - level r (n + 1 - 1)) / level r (n + 1)
          = 1 - level r n / level r (n + 1) := by
        rw [Nat.add_sub_cancel]; field_simp
      rw [he]
      linarith
  have := main (numVals r) hk (le_refl _)
  unfold ratioSum
  rw [Real.log_div (level_pos hr hk (le_refl _)).ne' hl1.ne']
  exact this

end P779221ce

open RevenueOrdered.Ratio in
theorem solution {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    opt P r ≤ ratioSum r * roValue P r ∧
      ratioSum r ≤ 1 + Real.log (level r (numVals r) / level r 1) := by
  exact ⟨P779221ce.part1 hP r hr, P779221ce.part2 r hr⟩
