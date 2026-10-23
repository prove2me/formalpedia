-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P65.weylRatios_all
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:50:30.299985+00:00
-- url     : https://prove2.me/submissions/ea0119e5-20c1-464e-b2d5-a0cb33bfecb5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65

noncomputable section

namespace X4P65W

open QAlgorithms.Papers.Independent.Information100.P65

def fac (r : ℕ → ℕ) (a b : ℕ) : ℝ :=
  (((r a : ℝ) - (a : ℝ)) - ((r b : ℝ) - (b : ℝ))) / ((b : ℝ) - (a : ℝ))

lemma wd_succ (r : ℕ → ℕ) (n : ℕ) :
    weylDimension r (n + 1) = weylDimension r n * ∏ a ∈ Finset.range n, fac r a n := by
  unfold weylDimension
  rw [Finset.prod_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [Finset.prod_Ico_succ_top (by omega)]
  rfl

def Anti (r : ℕ → ℕ) : Prop := ∀ a b, a ≤ b → r b ≤ r a

lemma fac_pos {r : ℕ → ℕ} (hr : Anti r) {a b : ℕ} (h : a < b) : 0 < fac r a b := by
  have h1 : (r b : ℝ) ≤ r a := by exact_mod_cast hr a b h.le
  have h2 : (a : ℝ) < b := by exact_mod_cast h
  unfold fac; apply div_pos <;> linarith

lemma wd_ne {r : ℕ → ℕ} (hr : Anti r) (n : ℕ) : weylDimension r n ≠ 0 := by
  unfold weylDimension
  refine Finset.prod_ne_zero_iff.2 fun a ha => Finset.prod_ne_zero_iff.2 fun b hb => ?_
  simp only [Finset.mem_Ico] at hb
  exact (fac_pos hr (show a < b by omega)).ne'

lemma step_gen (r : ℕ → ℕ) (j n : ℕ) :
    dimensionRatio r j (n + 1) = dimensionRatio r j n *
      ∏ a ∈ Finset.range n, (fac (addedRows r j) a n / fac r a n) := by
  unfold dimensionRatio
  rw [wd_succ, wd_succ, Finset.prod_div_distrib, mul_div_mul_comm]

lemma prod_gt (r : ℕ → ℕ) (j n : ℕ) (hn : j < n) (hf : ∀ a < n, fac r a n ≠ 0) :
    ∏ a ∈ Finset.range n, (fac (addedRows r j) a n / fac r a n) =
      (shiftedRow r j - shiftedRow r n + 1) / (shiftedRow r j - shiftedRow r n) := by
  have hnj : n ≠ j := by omega
  rw [Finset.prod_eq_single j]
  · have hden : (n : ℝ) - j ≠ 0 := by
      have : (j : ℝ) < n := by exact_mod_cast hn
      linarith
    simp only [fac, addedRows, if_neg hnj, add_zero, shiftedRow]
    push_cast
    rw [div_div_div_cancel_right₀ hden]
    congr 1 <;> ring
  · intro a ha haj
    simp only [fac, addedRows, if_neg haj, if_neg hnj, add_zero]
    exact div_self (hf a (Finset.mem_range.1 ha))
  · intro h; exact absurd (Finset.mem_range.2 hn) h

lemma prod_eq (r : ℕ → ℕ) (j : ℕ) :
    ∏ a ∈ Finset.range j, (fac (addedRows r j) a j / fac r a j) =
      ∏ a ∈ Finset.range j,
        (shiftedRow r a - shiftedRow r j - 1) / (shiftedRow r a - shiftedRow r j) := by
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  have haj : a ≠ j := by omega
  have hden : (j : ℝ) - a ≠ 0 := by
    have : (a : ℝ) < j := by exact_mod_cast ha
    linarith
  simp only [fac, addedRows, if_neg haj, add_zero, shiftedRow]
  push_cast
  rw [div_div_div_cancel_right₀ hden]
  congr 1 <;> ring

lemma ratio_j (r : ℕ → ℕ) (j : ℕ) (hW : weylDimension r j ≠ 0) : dimensionRatio r j j = 1 := by
  unfold dimensionRatio
  have : weylDimension (addedRows r j) j = weylDimension r j := by
    unfold weylDimension
    refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
    simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
    simp only [addedRows, if_neg (show a ≠ j by omega), if_neg (show b ≠ j by omega), add_zero]
  rw [this, div_self hW]

lemma part1 (r : ℕ → ℕ) (hr : Anti r) (j n : ℕ) (hjn : j + 1 ≤ n) :
    dimensionRatio r j n =
      (∏ a ∈ Finset.range j,
        (shiftedRow r a - shiftedRow r j - 1) / (shiftedRow r a - shiftedRow r j)) *
      ∏ b ∈ Finset.Ico (j + 1) n,
        (shiftedRow r j - shiftedRow r b + 1) / (shiftedRow r j - shiftedRow r b) := by
  have hf : ∀ n, ∀ a < n, fac r a n ≠ 0 := fun n a ha => (fac_pos hr ha).ne'
  induction n, hjn using Nat.le_induction with
  | base =>
    rw [step_gen, ratio_j r j (wd_ne hr j), one_mul, prod_eq r j, Finset.Ico_self,
      Finset.prod_empty, mul_one]
  | succ n hn ih =>
    rw [step_gen, ih, prod_gt r j n (by omega) (hf n), Finset.prod_Ico_succ_top (by omega),
      mul_assoc]

lemma x_pos (r : ℕ → ℕ) (hr : Anti r) {j b : ℕ} (h : j < b) :
    0 < shiftedRow r j - shiftedRow r b := by
  have h1 : (r b : ℝ) ≤ r j := by exact_mod_cast hr j b h.le
  have h2 : (j : ℝ) < b := by exact_mod_cast h
  simp only [shiftedRow]; push_cast; linarith

lemma ratio_ne (r : ℕ → ℕ) (j : ℕ) (hr : Anti r) (hr' : Anti (addedRows r j)) (n : ℕ) :
    dimensionRatio r j n ≠ 0 :=
  div_ne_zero (wd_ne hr' n) (wd_ne hr n)

lemma part2 (r : ℕ → ℕ) (j : ℕ) (hr : Anti r) (hr' : Anti (addedRows r j)) (n d : ℕ)
    (hjn : j + 1 ≤ n) (hnd : n ≤ d) :
    dimensionRatio r j n / dimensionRatio r j d =
      ∏ b ∈ Finset.Ico n d,
        (shiftedRow r j - shiftedRow r b) / (shiftedRow r j - shiftedRow r b + 1) := by
  induction d, hnd using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.prod_empty, div_self (ratio_ne r j hr hr' n)]
  | succ d hd ih =>
    rw [Finset.prod_Ico_succ_top hd, ← ih, step_gen,
      prod_gt r j d (by omega) (fun a ha => (fac_pos hr ha).ne')]
    have h1 := ratio_ne r j hr hr' d
    have h2 := ratio_ne r j hr hr' n
    have hx := x_pos r hr (show j < d by omega)
    have hx1 : shiftedRow r j - shiftedRow r d + 1 ≠ 0 := by linarith
    field_simp

lemma wd_shift (s r : ℕ → ℕ) (n : ℕ) (h : ∀ a < n, s a + 1 = r a) :
    weylDimension s n = weylDimension r n := by
  unfold weylDimension
  refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
  have h1 : (r a : ℝ) = s a + 1 := by exact_mod_cast (h a ha).symm
  have h2 : (r b : ℝ) = s b + 1 := by exact_mod_cast (h b (by omega)).symm
  rw [h1, h2]; ring

lemma tele (y : ℝ → ℝ) (n d : ℕ) (hnd : n ≤ d) (hy : ∀ t : ℝ, y (t + 1) = y t + 1)
    (hpos : ∀ b : ℕ, n ≤ b → 0 < y b) :
    ∏ b ∈ Finset.Ico n d, y b / (y b + 1) = y n / y d := by
  induction d, hnd using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.prod_empty, div_self (hpos n le_rfl).ne']
  | succ d hd ih =>
    rw [Finset.prod_Ico_succ_top hd, ih]
    have h1 := hpos d hd
    have h2 := hpos n le_rfl
    push_cast
    rw [hy]
    field_simp

end X4P65W

open QAlgorithms.Papers.Independent.Information100.P65 X4P65W in
theorem solution {d j n : ℕ} (lower upper : YoungDiagram)
    (hpair : IsBoxPair d lower upper j) (hjn : j + 1 ≤ n) (hnd : n ≤ d) :
    (dimensionRatio lower.rowLen j n =
      (∏ a ∈ Finset.range j,
        (shiftedRow lower.rowLen a - shiftedRow lower.rowLen j - 1) /
          (shiftedRow lower.rowLen a - shiftedRow lower.rowLen j)) *
      (∏ b ∈ Finset.Ico (j + 1) n,
        (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b + 1) /
          (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b))) ∧
    (dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d =
      ∏ b ∈ Finset.Ico n d,
        (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b) /
          (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b + 1)) ∧
    (∀ other otherUpper : YoungDiagram, IsBoxPair d other otherUpper j →
      (∀ a ∈ Finset.Ico j d, other.rowLen a = lower.rowLen a) →
      dimensionRatio other.rowLen j n / dimensionRatio other.rowLen j d =
        dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d) ∧
    (∀ h : ℕ, n ≤ h → h ≤ d → lower.rowLen h < lower.rowLen (h - 1) →
      dimensionRatio (deletedColumnRows lower.rowLen h) j n =
        dimensionRatio lower.rowLen j n) ∧
    ((∀ b ∈ Finset.Ico n d, lower.rowLen b = 0) →
      dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d =
        ((upper.rowLen j : ℝ) + (n : ℝ) - ((j + 1 : ℕ) : ℝ)) /
          ((upper.rowLen j : ℝ) + (d : ℝ) - ((j + 1 : ℕ) : ℝ))) ∧
    ((∃ b ∈ Finset.Ico n d, 0 < lower.rowLen b) →
      dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d <
        ((upper.rowLen j : ℝ) + (n : ℝ) - ((j + 1 : ℕ) : ℝ)) /
          ((upper.rowLen j : ℝ) + (d : ℝ) - ((j + 1 : ℕ) : ℝ))) := by
  classical
  have anti_of : ∀ (lo up : YoungDiagram), IsBoxPair d lo up j →
      Anti lo.rowLen ∧ Anti (addedRows lo.rowLen j) := by
    intro lo up hp
    obtain ⟨-, -, -, -, hu⟩ := hp
    refine ⟨fun a b h => lo.rowLen_anti a b h, fun a b h => ?_⟩
    rw [← hu, ← hu]; exact up.rowLen_anti a b h
  obtain ⟨hr, hr'⟩ := anti_of lower upper hpair
  have hP2 := part2 lower.rowLen j hr hr' n d hjn hnd
  obtain ⟨hd, -, -, hj, hu⟩ := hpair
  have hj1 : (upper.rowLen j : ℝ) = lower.rowLen j + 1 := by
    have := hu j; simp only [addedRows, if_pos rfl] at this; exact_mod_cast this
  -- y b = ω_j - ω'_b with ω'_b = -(b+1)
  set y : ℝ → ℝ := fun t => (lower.rowLen j : ℝ) - (j + 1 : ℝ) + (t + 1) with hy
  have hyp : ∀ b : ℕ, n ≤ b → 0 < y b := by
    intro b hb
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
    have : (n : ℝ) ≤ b := by exact_mod_cast hb
    have : (0 : ℝ) ≤ lower.rowLen j := Nat.cast_nonneg _
    simp only [hy]; linarith
  have hrhs : ((upper.rowLen j : ℝ) + (n : ℝ) - ((j + 1 : ℕ) : ℝ)) /
      ((upper.rowLen j : ℝ) + (d : ℝ) - ((j + 1 : ℕ) : ℝ)) = y n / y d := by
    rw [hj1]; simp only [hy]; push_cast; congr 1 <;> ring
  have hYt : ∏ b ∈ Finset.Ico n d, y b / (y b + 1) = y n / y d :=
    tele y n d hnd (fun t => by simp only [hy]; ring) hyp
  refine ⟨part1 lower.rowLen hr j n hjn, hP2, ?_, ?_, ?_, ?_⟩
  · intro other ou hpo hag
    obtain ⟨ho, ho'⟩ := anti_of other ou hpo
    rw [part2 other.rowLen j ho ho' n d hjn hnd, hP2]
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [Finset.mem_Ico] at hb
    simp only [shiftedRow, hag j (Finset.mem_Ico.2 ⟨le_rfl, hj⟩),
      hag b (Finset.mem_Ico.2 ⟨by omega, hb.2⟩)]
  · intro h hnh hhd hlt
    have hpos : ∀ a < h, 1 ≤ lower.rowLen a := by
      intro a ha
      have := lower.rowLen_anti a (h - 1) (by omega)
      omega
    unfold dimensionRatio
    rw [wd_shift (deletedColumnRows lower.rowLen h) lower.rowLen n
      (fun a ha => by simp only [deletedColumnRows, if_pos (show a < h by omega)]; have := hpos a (by omega); omega)]
    rw [wd_shift (addedRows (deletedColumnRows lower.rowLen h) j) (addedRows lower.rowLen j) n
      (fun a ha => by
        simp only [addedRows, deletedColumnRows, if_pos (show a < h by omega)]
        have := hpos a (by omega)
        split_ifs <;> omega)]
  · intro hz
    rw [hP2, hrhs, ← hYt]
    refine Finset.prod_congr rfl fun b hb => ?_
    have hb0 := hz b hb
    simp only [shiftedRow, hb0, hy]
    push_cast
    ring_nf
  · rintro ⟨b0, hb0, hpos0⟩
    rw [hP2, hrhs, ← hYt]
    have hx : ∀ b ∈ Finset.Ico n d,
        shiftedRow lower.rowLen j - shiftedRow lower.rowLen b = y b - lower.rowLen b := by
      intro b _
      simp only [shiftedRow, hy]; push_cast; ring
    apply Finset.prod_lt_prod
    · intro b hb
      have := x_pos lower.rowLen hr (show j < b by rw [Finset.mem_Ico] at hb; omega)
      positivity
    · intro b hb
      have hxp := x_pos lower.rowLen hr (show j < b by rw [Finset.mem_Ico] at hb; omega)
      rw [hx b hb] at hxp ⊢
      have := hyp b (Finset.mem_Ico.1 hb).1
      have h0 : (0 : ℝ) ≤ lower.rowLen b := Nat.cast_nonneg _
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · refine ⟨b0, hb0, ?_⟩
      have hxp := x_pos lower.rowLen hr (show j < b0 by rw [Finset.mem_Ico] at hb0; omega)
      rw [hx b0 hb0] at hxp ⊢
      have := hyp b0 (Finset.mem_Ico.1 hb0).1
      have h0 : (0 : ℝ) < lower.rowLen b0 := by exact_mod_cast hpos0
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
