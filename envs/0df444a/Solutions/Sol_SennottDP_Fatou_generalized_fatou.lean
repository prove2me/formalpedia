-- Prove2me | solution 1 for SennottDP.Fatou.generalized_fatou
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:07:17.667138+00:00
-- url     : https://prove2.me/submissions/551af6c8-39e1-48f6-b7be-fbda470a1a84

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou.B928

lemma ptwise (x : EReal) (L : ℝ) (hL : 0 ≤ L) (h : ((-L : ℝ) : EReal) ≤ x) :
    (x + (L : EReal)).toENNReal + (-x).toENNReal = x.toENNReal + ENNReal.ofReal L := by
  induction x using EReal.rec with
  | bot => exact absurd h (by simp)
  | top => simp
  | coe r =>
    have hr : -L ≤ r := by exact_mod_cast h
    rw [← EReal.coe_add, ← EReal.coe_neg]
    simp only [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_or_gt 0 r with h0 | h0
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -r ≤ 0), add_zero, ENNReal.ofReal_add h0 hL]
    · rw [ENNReal.ofReal_of_nonpos h0.le, zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring

lemma wsum_shift {S : Type*} (p : S → ℝ≥0∞) (x : S → EReal) (L : ℝ) (hL : 0 ≤ L)
    (hp : ∑' j, p j = 1) (hx : ∀ j, p j ≠ 0 → ((-L : ℝ) : EReal) ≤ x j) :
    wsum p x = ((∑' j, p j * (x j + (L : EReal)).toENNReal : ℝ≥0∞) : EReal) - (L : EReal) := by
  unfold wsum
  set A := ∑' j, p j * (x j + (L : EReal)).toENNReal with hAdef
  set X := ∑' j, p j * (x j).toENNReal with hXdef
  set Y := ∑' j, p j * (-x j).toENNReal with hYdef
  have hsum : A + Y = X + ENNReal.ofReal L := by
    have h1 : ∑' j, p j * ENNReal.ofReal L = ENNReal.ofReal L := by
      rw [ENNReal.tsum_mul_right, hp, one_mul]
    rw [hAdef, hYdef, hXdef, ← h1, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    congr 1; funext j
    by_cases hj : p j = 0
    · simp [hj]
    · rw [← mul_add, ← mul_add, ptwise (x j) L hL (hx j hj)]
  have hY : Y ≤ ENNReal.ofReal L := by
    calc Y ≤ ∑' j, p j * ENNReal.ofReal L := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          by_cases hj : p j = 0
          · simp [hj]
          · gcongr
            have : -x j ≤ (L : EReal) := by
              have := hx j hj
              rw [EReal.neg_le]; simpa using this
            simpa [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _)] using
              EReal.toENNReal_le_toENNReal this
      _ = ENNReal.ofReal L := by rw [ENNReal.tsum_mul_right, hp, one_mul]
  have hYt : Y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY
  by_cases hX : X = ⊤
  · have hA : A = ⊤ := by
      by_contra hA
      have : A + Y ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hA, hYt⟩
      rw [hsum, hX, top_add] at this; exact this rfl
    rw [hX, hA, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hYt, EReal.top_sub_coe,
      EReal.top_sub_coe]
  · have hA : A ≠ ⊤ := by
      intro hA
      have : X + ENNReal.ofReal L ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hX, ENNReal.ofReal_ne_top⟩
      rw [← hsum, hA, top_add] at this; exact this rfl
    have hr := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add hA hYt, ENNReal.toReal_add hX ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hL] at hr
    rw [← EReal.coe_ennreal_toReal hX, ← EReal.coe_ennreal_toReal hYt,
      ← EReal.coe_ennreal_toReal hA, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1; linarith

lemma tsum_fatou {S : Type*} (b : ℕ → S → ℝ≥0∞) :
    ∑' j, liminf (fun N => b N j) atTop ≤ liminf (fun N => ∑' j, b N j) atTop := by
  let _ : MeasurableSpace S := ⊤
  rw [← MeasureTheory.lintegral_count' (measurable_from_top)]
  have h := MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count)
    (u := atTop) (f := b) (fun n => measurable_from_top)
  refine h.trans (le_of_eq ?_)
  congr 1; funext N
  exact MeasureTheory.lintegral_count' measurable_from_top

lemma liminf_shift (u : ℕ → EReal) (L : ℝ) :
    (liminf u atTop + (L : EReal)).toENNReal =
      liminf (fun N => (u N + (L : EReal)).toENNReal) atTop := by
  have hmono : Monotone (fun x : EReal => (x + (L : EReal)).toENNReal) := fun a b h =>
    EReal.toENNReal_le_toENNReal (add_le_add h le_rfl)
  have hcont : ContinuousAt (fun x : EReal => (x + (L : EReal)).toENNReal) (liminf u atTop) := by
    refine EReal.continuous_toENNReal.continuousAt.comp ?_
    have := EReal.continuousAt_add (p := (liminf u atTop, (L : EReal)))
      (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
    exact ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2)
      (f := fun x : EReal => (x, (L : EReal))) this (continuous_id.prodMk continuous_const).continuousAt
  exact hmono.map_liminf_of_continuousAt u hcont

lemma final_shift (B : ℕ → ℝ≥0∞) (A : ℝ≥0∞) (L : ℝ) (h : A ≤ liminf B atTop) :
    (A : EReal) - (L : EReal) ≤ liminf (fun N => (B N : EReal) - (L : EReal)) atTop := by
  have hmono : Monotone (fun x : ℝ≥0∞ => (x : EReal) - (L : EReal)) := fun a b hab =>
    EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hab) le_rfl
  have hcont : ContinuousAt (fun x : ℝ≥0∞ => (x : EReal) - (L : EReal)) (liminf B atTop) := by
    have hfun : (fun x : ℝ≥0∞ => (x : EReal) - (L : EReal)) =
        fun x : ℝ≥0∞ => (x : EReal) + ((-L : ℝ) : EReal) := by
      funext x; rw [sub_eq_add_neg, EReal.coe_neg]
    rw [hfun]
    have := EReal.continuousAt_add (p := (((liminf B atTop : ℝ≥0∞) : EReal), ((-L : ℝ) : EReal)))
      (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
    exact ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2)
      (f := fun x : ℝ≥0∞ => ((x : EReal), ((-L : ℝ) : EReal))) this
      (continuous_coe_ennreal_ereal.prodMk continuous_const).continuousAt
  have := hmono.map_liminf_of_continuousAt B hcont
  exact (hmono h).trans (le_of_eq this)

end SennottDP.Fatou.B928

open Filter Topology SennottDP.Fatou in open scoped ENNReal in
theorem solution {S : Type*} [Countable S] {P : S → ℝ≥0∞} {SN : ℕ → Set S}
    {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u : S → ℕ → EReal) (L : ℝ) (hL : 0 ≤ L) (hu : ∀ N, ∀ j ∈ SN N, ((-L : ℝ) : EReal) ≤ u j N) :
    wsum P (fun j => liminf (fun N => u j N) atTop) ≤
      liminf (fun N => wsum ((SN N).indicator (Q N)) (fun j => u j N)) atTop := by
  have hev : ∀ j, ∀ᶠ N in atTop, j ∈ SN N := by
    intro j
    have : j ∈ ⋃ N, SN N := by rw [hA.iUnion_eq]; trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 this
    exact Filter.eventually_atTop.2 ⟨n, fun N hN => hA.mono hN hn⟩
  have hv : ∀ j, ((-L : ℝ) : EReal) ≤ liminf (fun N => u j N) atTop := by
    intro j
    exact Filter.le_liminf_of_le (by isBoundedDefault)
      ((hev j).mono fun N hN => hu N j hN)
  rw [B928.wsum_shift P _ L hL hA.prob (fun j _ => hv j)]
  have hR : ∀ N, wsum ((SN N).indicator (Q N)) (fun j => u j N) =
      ((∑' j, (SN N).indicator (Q N) j * (u j N + (L : EReal)).toENNReal : ℝ≥0∞) : EReal)
        - (L : EReal) := by
    intro N
    refine B928.wsum_shift _ _ L hL (hA.prob_N N) (fun j hj => ?_)
    exact hu N j (Set.mem_of_indicator_ne_zero hj)
  simp_rw [hR]
  refine B928.final_shift _ _ L ?_
  refine le_trans ?_ (B928.tsum_fatou _)
  refine ENNReal.tsum_le_tsum fun j => ?_
  have hc : liminf (fun N => (SN N).indicator (Q N) j * (u j N + (L : EReal)).toENNReal) atTop
      = liminf (fun N => Q N j * (u j N + (L : EReal)).toENNReal) atTop := by
    refine Filter.liminf_congr ((hev j).mono fun N hN => ?_)
    rw [Set.indicator_of_mem hN]
  rw [hc, B928.liminf_shift, ← (hA.tendsto j).liminf_eq]
  exact ENNReal.le_liminf_mul
