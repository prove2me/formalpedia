-- Prove2me | solution 1 for ProductFraming.Trunc.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T16:21:05.737047+00:00
-- url     : https://prove2.me/submissions/81c0e52e-ea73-4327-ba42-cb6f48b896af

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Framing
import Definitions.Def_ProductFraming_Trunc_Model
open Finset

set_option autoImplicit false

namespace PFT4Aux

open ProductFraming.Trunc

lemma tail_nonneg (m : ℕ) (lam : ℕ → ℝ) (hl : ∀ x ∈ Icc 1 m, 0 ≤ lam x) {x : ℕ} (hx : 1 ≤ x) :
    0 ≤ ProductFraming.Nest.tail m lam x := by
  unfold ProductFraming.Nest.tail
  apply sum_nonneg
  intro z hz
  rw [mem_Icc] at hz
  exact hl z (mem_Icc.mpr ⟨by omega, hz.2⟩)

lemma tail_anti (m : ℕ) (lam : ℕ → ℝ) (hl : ∀ x ∈ Icc 1 m, 0 ≤ lam x) {x x' : ℕ} (hx : 1 ≤ x)
    (hxx : x ≤ x') : ProductFraming.Nest.tail m lam x' ≤ ProductFraming.Nest.tail m lam x := by
  unfold ProductFraming.Nest.tail
  apply sum_le_sum_of_subset_of_nonneg
  · intro z hz
    rw [mem_Icc] at hz ⊢
    omega
  · intro z hz _
    rw [mem_Icc] at hz
    exact hl z (mem_Icc.mpr ⟨by omega, hz.2⟩)

lemma sum_tail_eq (m : ℕ) (lam : ℕ → ℝ) (y : ℕ) :
    ∑ k ∈ Icc y m, ProductFraming.Nest.tail m lam k
      = ∑ x ∈ Icc y m, lam x * ((x : ℝ) - y + 1) := by
  unfold ProductFraming.Nest.tail
  rw [Finset.sum_comm' (t' := Icc y m) (s' := fun x => Icc y x)
    (by intro k x; simp only [mem_Icc]; omega)]
  apply sum_congr rfl
  intro x hx
  rw [mem_Icc] at hx
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.cast_sub (by omega)]
  push_cast
  ring

lemma key (m : ℕ) (lam : ℕ → ℝ) (U : ℕ → ℝ) (M : ℝ)
    (hlam : ProductFraming.Nest.IsPageLaw m lam) (hB4 : IsIFR m lam)
    (hU0 : ∀ x ∈ Icc 1 m, 0 ≤ U x)
    (hB2 : ∀ x ∈ Icc 1 m, ∀ x' ∈ Icc 1 m, x ≤ x' → U x' / (x' : ℝ) ≤ U x / (x : ℝ))
    (hM : ∀ y ∈ Icc 1 m, ProductFraming.Nest.tail m lam y * U y ≤ M) :
    ∑ x ∈ Icc 1 m, lam x * U x ≤ 3 * M := by
  classical
  obtain ⟨hl, hsum⟩ := hlam
  -- the last support point `s`
  set T := (Icc 1 m).filter (fun x => 0 < lam x) with hT
  have hTne : T.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : ∑ x ∈ Icc 1 m, lam x ≤ 0 := by
      apply sum_nonpos
      intro x hx
      by_contra hpos
      have hxT : x ∈ T := mem_filter.mpr ⟨hx, not_le.mp hpos⟩
      rw [hne] at hxT
      simp at hxT
    linarith
  set s := T.max' hTne with hs
  have hsT : s ∈ T := max'_mem T hTne
  have hs1 : s ∈ Icc 1 m := (mem_filter.mp hsT).1
  have hspos : 0 < lam s := (mem_filter.mp hsT).2
  have hs1' := mem_Icc.mp hs1
  have htail_s : ProductFraming.Nest.tail m lam s = lam s := by
    unfold ProductFraming.Nest.tail
    apply sum_eq_single_of_mem s (mem_Icc.mpr ⟨le_refl _, hs1'.2⟩)
    intro z hz hzs
    rw [mem_Icc] at hz
    have hz1 : z ∈ Icc 1 m := mem_Icc.mpr ⟨by omega, hz.2⟩
    have h0 := hl z hz1
    by_contra hne
    have hzpos : 0 < lam z := lt_of_le_of_ne h0 (Ne.symm hne)
    have hzT : z ∈ T := mem_filter.mpr ⟨hz1, hzpos⟩
    have hzs' : z ≤ s := le_max' T z hzT
    omega
  -- the first point with `y * h(y) ≥ 1`
  have hex : ∃ y : ℕ, 0 < ProductFraming.Nest.tail m lam y ∧ 1 ≤ (y : ℝ) * failureRate m lam y := by
    refine ⟨s, by rw [htail_s]; exact hspos, ?_⟩
    unfold failureRate
    rw [htail_s, div_self hspos.ne']
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs1'.1
    linarith
  set y := Nat.find hex with hy
  have hPy := Nat.find_spec hex
  rw [← hy] at hPy
  have hmin : ∀ z < y, ¬ (0 < ProductFraming.Nest.tail m lam z ∧
      1 ≤ (z : ℝ) * failureRate m lam z) := fun z hz => Nat.find_min hex hz
  obtain ⟨hty, hyh⟩ := hPy
  have hy1 : 1 ≤ y := by
    by_contra hcon
    have h0 : y = 0 := by omega
    rw [h0] at hyh
    norm_num at hyh
  have hym : y ≤ m := by
    by_contra hcon
    unfold ProductFraming.Nest.tail at hty
    rw [Icc_eq_empty (by omega)] at hty
    simp at hty
  have hymem : y ∈ Icc 1 m := mem_Icc.mpr ⟨hy1, hym⟩
  have h1mem : 1 ∈ Icc 1 m := mem_Icc.mpr ⟨le_refl 1, by omega⟩
  have hM0 : 0 ≤ M :=
    le_trans (mul_nonneg (tail_nonneg m lam hl (le_refl 1)) (hU0 1 h1mem)) (hM 1 h1mem)
  rw [← sum_filter_add_sum_filter_not (Icc 1 m) (fun x => x < y)]
  -- part A: pages before `y`
  have hA : ∑ x ∈ (Icc 1 m).filter (fun x => x < y), lam x * U x ≤ M := by
    rcases Nat.lt_or_ge y 2 with hy2 | hy2
    · have hemp : (Icc 1 m).filter (fun x => x < y) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro x hx
        rw [mem_Icc] at hx
        omega
      rw [hemp, sum_empty]
      exact hM0
    · set w := y - 1 with hw
      have hw1 : 1 ≤ w := by omega
      have hwy : w < y := by omega
      have hwm : w ∈ Icc 1 m := mem_Icc.mpr ⟨hw1, by omega⟩
      have htw : 0 < ProductFraming.Nest.tail m lam w :=
        lt_of_lt_of_le hty (tail_anti m lam hl hw1 hwy.le)
      have hwh : (w : ℝ) * failureRate m lam w < 1 := by
        by_contra hc
        exact hmin w hwy ⟨htw, not_lt.mp hc⟩
      have hhw0 : 0 ≤ failureRate m lam w := div_nonneg (hl w hwm) htw.le
      have hterm : ∀ x ∈ (Icc 1 m).filter (fun x => x < y),
          lam x * U x ≤ failureRate m lam w * M := by
        intro x hx
        rw [mem_filter, mem_Icc] at hx
        obtain ⟨⟨hx1, hxm⟩, hxy⟩ := hx
        have hxmem : x ∈ Icc 1 m := mem_Icc.mpr ⟨hx1, hxm⟩
        have htx : 0 < ProductFraming.Nest.tail m lam x :=
          lt_of_lt_of_le hty (tail_anti m lam hl hx1 hxy.le)
        have hxw : x ≤ w := by omega
        have hhx : failureRate m lam x ≤ failureRate m lam w := hB4 x hxmem w hwm hxw htw
        have hlx : lam x = failureRate m lam x * ProductFraming.Nest.tail m lam x := by
          unfold failureRate
          field_simp
        have hhx0 : 0 ≤ failureRate m lam x := div_nonneg (hl x hxmem) htx.le
        have hMx := hM x hxmem
        rw [hlx, mul_assoc]
        calc failureRate m lam x * (ProductFraming.Nest.tail m lam x * U x)
            ≤ failureRate m lam x * M := mul_le_mul_of_nonneg_left hMx hhx0
          _ ≤ failureRate m lam w * M := mul_le_mul_of_nonneg_right hhx hM0
      have hcard : ((Icc 1 m).filter (fun x => x < y)).card ≤ w := by
        calc ((Icc 1 m).filter (fun x => x < y)).card ≤ (Ico 1 y).card := by
              apply card_le_card
              intro x hx
              rw [mem_filter, mem_Icc] at hx
              rw [mem_Ico]
              omega
          _ = w := by simp [hw]
      calc ∑ x ∈ (Icc 1 m).filter (fun x => x < y), lam x * U x
          ≤ ∑ x ∈ (Icc 1 m).filter (fun x => x < y), failureRate m lam w * M := sum_le_sum hterm
        _ = (((Icc 1 m).filter (fun x => x < y)).card : ℝ) * (failureRate m lam w * M) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ (w : ℝ) * (failureRate m lam w * M) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hhw0 hM0)
            exact_mod_cast hcard
        _ = ((w : ℝ) * failureRate m lam w) * M := by ring
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right hwh.le hM0
        _ = M := one_mul M
  -- part B: pages from `y` on
  have hB : ∑ x ∈ (Icc 1 m).filter (fun x => ¬ x < y), lam x * U x ≤ 2 * M := by
    have hfil : (Icc 1 m).filter (fun x => ¬ x < y) = Icc y m := by
      ext x
      simp only [mem_filter, mem_Icc]
      omega
    rw [hfil]
    have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hU_le : ∀ x ∈ Icc y m, lam x * U x ≤ lam x * x * (U y / y) := by
      intro x hx
      rw [mem_Icc] at hx
      have hx1 : x ∈ Icc 1 m := mem_Icc.mpr ⟨by omega, hx.2⟩
      have h2 := hB2 y hymem x hx1 hx.1
      have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
      rw [div_le_iff₀ hxpos] at h2
      have h3 : U x ≤ x * (U y / y) := by
        calc U x ≤ U y / y * x := h2
          _ = x * (U y / y) := mul_comm _ _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h3 (hl x hx1)
    have hsumx : ∑ x ∈ Icc y m, lam x * (x : ℝ)
        = ∑ k ∈ Icc y m, ProductFraming.Nest.tail m lam k
          + ((y : ℝ) - 1) * ProductFraming.Nest.tail m lam y := by
      rw [sum_tail_eq, show ProductFraming.Nest.tail m lam y = ∑ x ∈ Icc y m, lam x from rfl,
        mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      ring
    have hHT : ∑ k ∈ Icc y m, failureRate m lam y * ProductFraming.Nest.tail m lam k
        ≤ ProductFraming.Nest.tail m lam y := by
      calc ∑ k ∈ Icc y m, failureRate m lam y * ProductFraming.Nest.tail m lam k
          ≤ ∑ k ∈ Icc y m, lam k := by
            apply sum_le_sum
            intro k hk
            rw [mem_Icc] at hk
            have hk1 : k ∈ Icc 1 m := mem_Icc.mpr ⟨by omega, hk.2⟩
            rcases (tail_nonneg m lam hl (show 1 ≤ k by omega)).lt_or_eq with htk | htk
            · have hh := hB4 y hymem k hk1 hk.1 htk
              calc failureRate m lam y * ProductFraming.Nest.tail m lam k
                  ≤ failureRate m lam k * ProductFraming.Nest.tail m lam k :=
                    mul_le_mul_of_nonneg_right hh htk.le
                _ = lam k := by
                    unfold failureRate
                    field_simp
            · rw [← htk, mul_zero]
              exact hl k hk1
        _ = ProductFraming.Nest.tail m lam y := rfl
    have hT0 : 0 ≤ ∑ k ∈ Icc y m, ProductFraming.Nest.tail m lam k :=
      sum_nonneg (fun k hk => tail_nonneg m lam hl (by rw [mem_Icc] at hk; omega))
    rw [← mul_sum] at hHT
    have hy0 : (0 : ℝ) ≤ y := hypos.le
    have hTs : ∑ k ∈ Icc y m, ProductFraming.Nest.tail m lam k
        ≤ (y : ℝ) * ProductFraming.Nest.tail m lam y := by
      nlinarith
    have hUy0 := hU0 y hymem
    have hty0 := hty.le
    calc ∑ x ∈ Icc y m, lam x * U x ≤ ∑ x ∈ Icc y m, lam x * x * (U y / y) := sum_le_sum hU_le
      _ = (∑ x ∈ Icc y m, lam x * x) * (U y / y) := by rw [sum_mul]
      _ ≤ (2 * y * ProductFraming.Nest.tail m lam y) * (U y / y) := by
          apply mul_le_mul_of_nonneg_right _ (div_nonneg hUy0 hy0)
          rw [hsumx]
          nlinarith
      _ = 2 * (ProductFraming.Nest.tail m lam y * U y) * ((y : ℝ) * (y : ℝ)⁻¹) := by ring
      _ = 2 * (ProductFraming.Nest.tail m lam y * U y) := by
          rw [mul_inv_cancel₀ hypos.ne', mul_one]
      _ ≤ 2 * M := by linarith [hM y hymem]
  linarith

lemma card_consideration_le {n : ℕ} (m p : ℕ) (f : Fin n → ℕ) (hf : Feasible m p f) {x : ℕ}
    (hxm : x ≤ m) : (ProductFraming.Nest.consideration f x).card ≤ x * p := by
  have hf' : ProductFraming.Nest.IsFeasibleFraming m p f := hf
  have hsub : ProductFraming.Nest.consideration f x ⊆
      (Icc 1 x).biUnion (fun j => univ.filter (fun i => f i = j)) := by
    intro i hi
    simp only [ProductFraming.Nest.consideration, mem_filter, mem_univ, true_and] at hi
    simp only [mem_biUnion, mem_Icc, mem_filter, mem_univ, true_and]
    exact ⟨f i, ⟨hi.1, hi.2⟩, rfl⟩
  calc (ProductFraming.Nest.consideration f x).card
      ≤ ((Icc 1 x).biUnion (fun j => univ.filter (fun i => f i = j))).card := card_le_card hsub
    _ ≤ ∑ j ∈ Icc 1 x, (univ.filter (fun i => f i = j)).card := card_biUnion_le
    _ ≤ ∑ j ∈ Icc 1 x, p := by
        apply sum_le_sum
        intro j hj
        rw [mem_Icc] at hj
        exact hf'.2 j (mem_Icc.mpr ⟨hj.1, by omega⟩)
    _ = x * p := by simp

lemma Rt_le_Ut {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ) (x : ℕ)
    (S : Finset (Fin n)) (hS : S.card ≤ x * p) : Rt r Pt x S ≤ Ut p r Pt x := by
  unfold Ut
  exact le_sup' (Rt r Pt x) (mem_filter.mpr ⟨mem_univ _, hS⟩)

end PFT4Aux

open Finset ProductFraming.Trunc in
theorem solution {n : ℕ} (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ)
    (hP : ∀ x ∈ Icc 1 m, ProductFraming.Nest.IsChoiceModel (Pt x)) (lam : ℕ → ℝ) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (hB1 : AssumptionB1 m p r Pt) (hB2 : AssumptionB2 m p r Pt) (hB4 : IsIFR m lam)
    (S : ℕ → Finset (Fin n)) (F : ℕ → Fin n → ℕ)
    (hrun : ∀ y ∈ Icc 1 m, IsTruncRun m p r Pt y (S y) (F y)) :
    (1 / 3 : ℝ) * VoptT m p lam r Pt ≤
      (Icc 1 m).sup' (nonempty_Icc.mpr hm) (fun y => Vt m lam r Pt (F y)) := by
  have hl := hlam.1
  have hRt0 : ∀ x ∈ Icc 1 m, ∀ T : Finset (Fin n), 0 ≤ Rt r Pt x T := by
    intro x hx T
    unfold Rt
    exact sum_nonneg (fun i _ => mul_nonneg (hr i) ((hP x hx).nonneg i T))
  have hU0 : ∀ x ∈ Icc 1 m, 0 ≤ Ut p r Pt x := by
    intro x _
    have h := PFT4Aux.Rt_le_Ut p r Pt x ∅ (by simp)
    simp only [Rt, sum_empty] at h
    exact h
  have hVopt : VoptT m p lam r Pt ≤ ∑ x ∈ Icc 1 m, lam x * Ut p r Pt x := by
    classical
    unfold VoptT
    apply sup'_le
    intro g hg
    have hfeas : Feasible m p (fun i => (g i : ℕ)) := (mem_filter.mp hg).2
    unfold Vt
    apply sum_le_sum
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (hl x hx)
    exact PFT4Aux.Rt_le_Ut p r Pt x _
      (PFT4Aux.card_consideration_le m p _ hfeas (mem_Icc.mp hx).2)
  have hVt : ∀ y ∈ Icc 1 m,
      ProductFraming.Nest.tail m lam y * Ut p r Pt y ≤ Vt m lam r Pt (F y) := by
    intro y hy
    obtain ⟨hcard, hopt, _, hcons, hle⟩ := hrun y hy
    have hy' := mem_Icc.mp hy
    unfold Vt ProductFraming.Nest.tail
    rw [sum_mul]
    calc ∑ x ∈ Icc y m, lam x * Ut p r Pt y
        = ∑ x ∈ (Icc 1 m).filter (fun x => y ≤ x), lam x * Ut p r Pt y := by
          congr 1
          ext x
          simp only [mem_filter, mem_Icc]
          omega
      _ = ∑ x ∈ Icc 1 m, (if y ≤ x then lam x * Ut p r Pt y else 0) := sum_filter _ _
      _ ≤ ∑ x ∈ Icc 1 m, lam x * Rt r Pt x (ProductFraming.Nest.consideration (F y) x) := by
          apply sum_le_sum
          intro x hx
          have hx' := mem_Icc.mp hx
          split_ifs with hyx
          · apply mul_le_mul_of_nonneg_left _ (hl x hx)
            have hc : ProductFraming.Nest.consideration (F y) x = S y := by
              rw [← hcons]
              ext i
              simp only [ProductFraming.Nest.consideration, mem_filter, mem_univ, true_and]
              have hi := hle i
              constructor
              · rintro ⟨h1, _⟩
                exact ⟨h1, hi⟩
              · rintro ⟨h1, _⟩
                exact ⟨h1, by omega⟩
            rw [hc, ← hopt]
            exact hB1 y x (S y) hy'.1 hyx hx'.2 hcard
          · exact mul_nonneg (hl x hx) (hRt0 x hx _)
  have hkey := PFT4Aux.key m lam (Ut p r Pt)
    ((Icc 1 m).sup' (nonempty_Icc.mpr hm) (fun y => Vt m lam r Pt (F y))) hlam hB4 hU0 hB2
    (fun y hy => (hVt y hy).trans (le_sup' (fun y => Vt m lam r Pt (F y)) hy))
  have := hVopt.trans hkey
  linarith
