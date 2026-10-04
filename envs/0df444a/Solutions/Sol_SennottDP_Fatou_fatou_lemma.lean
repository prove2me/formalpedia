-- Prove2me | solution 1 for SennottDP.Fatou.fatou_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:03:11.121003+00:00
-- url     : https://prove2.me/submissions/2e51a5f6-3b4d-4865-bcbc-aeee7e134cbd

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace SennottFatouAux

lemma ereal_aux (A C : EReal) (b l : ℝ) (h : C + b = A + l) : A - b = C - l := by
  induction A using EReal.rec <;> induction C using EReal.rec
  · rfl
  · simp at h
  · simp at h
  · simp at h
    exact absurd h.symm (EReal.coe_ne_bot _)
  · rename_i a c
    have h' : c + b = a + l := by exact_mod_cast h
    have : a - b = c - l := by linarith
    exact_mod_cast this
  · simp at h
    exact absurd h.symm (EReal.coe_ne_top _)
  · simp at h
  · simp at h
    exact absurd h (EReal.coe_ne_top _)
  · rfl

lemma pt_aux (L : ℝ) (hL : 0 ≤ L) (x : EReal) (hx : ((-L : ℝ) : EReal) ≤ x) :
    (x + (L : EReal)).toENNReal + (-x).toENNReal = x.toENNReal + ENNReal.ofReal L := by
  induction x using EReal.rec
  · simp at hx
  · rename_i r
    have hr : -L ≤ r := by exact_mod_cast hx
    rw [← EReal.coe_add, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    rcases le_total 0 r with h0 | h0
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -r ≤ 0), ENNReal.ofReal_add h0 hL, add_zero]
    · rw [ENNReal.ofReal_of_nonpos h0, zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring
  · simp

lemma key {S : Type*} (P : S → ℝ≥0∞) (hP : ∑' j, P j = 1) (L : ℝ) (hL : 0 ≤ L)
    (v : S → EReal) (hv : ∀ j, ((-L : ℝ) : EReal) ≤ v j) :
    SennottDP.Fatou.wsum P v =
      ((∑' j, P j * (v j + (L : EReal)).toENNReal : ℝ≥0∞) : EReal) - (L : EReal) := by
  unfold SennottDP.Fatou.wsum
  set A := ∑' j, P j * (v j).toENNReal
  set B := ∑' j, P j * (-v j).toENNReal
  set C := ∑' j, P j * (v j + (L : EReal)).toENNReal
  have hsum : C + B = A + ENNReal.ofReal L := by
    simp only [C, B, A]
    rw [← ENNReal.tsum_add]
    simp_rw [← mul_add, pt_aux L hL _ (hv _), mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hP, one_mul]
  have hB : B ≤ ENNReal.ofReal L := by
    calc B ≤ ∑' j, P j * ENNReal.ofReal L := by
          refine ENNReal.tsum_le_tsum (fun j => ?_)
          gcongr
          rw [← EReal.real_coe_toENNReal]
          apply EReal.toENNReal_le_toENNReal
          have := hv j
          rw [EReal.coe_neg] at this
          exact EReal.neg_le.mpr this
      _ = ENNReal.ofReal L := by rw [ENNReal.tsum_mul_right, hP, one_mul]
  have hBt : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  have hE : (C : EReal) + ((B.toReal : ℝ) : EReal) = (A : EReal) + (L : EReal) := by
    rw [EReal.coe_ennreal_toReal hBt, ← EReal.coe_ennreal_add, hsum, EReal.coe_ennreal_add,
      EReal.coe_ennreal_ofReal, max_eq_left hL]
  have := ereal_aux (A : EReal) (C : EReal) B.toReal L hE
  rwa [EReal.coe_ennreal_toReal hBt] at this

lemma g_mono (L : ℝ) : Monotone (fun x : EReal => (x + (L : EReal)).toENNReal) :=
  fun _ _ h => EReal.toENNReal_le_toENNReal (by gcongr)

lemma g_cont (L : ℝ) (y : EReal) :
    ContinuousAt (fun x : EReal => (x + (L : EReal)).toENNReal) y := by
  have h1 : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (y, (L : EReal)) :=
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot L)) (Or.inr (EReal.coe_ne_top L))
  have h2 : ContinuousAt (fun x : EReal => x + (L : EReal)) y :=
    h1.comp (f := fun x : EReal => (x, (L : EReal))) (continuousAt_id.prodMk continuousAt_const)
  exact EReal.continuous_toENNReal.continuousAt.comp h2

lemma h_mono (L : ℝ) : Monotone (fun x : ℝ≥0∞ => (x : EReal) - (L : EReal)) :=
  fun _ _ h => EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h) le_rfl

lemma h_cont (L : ℝ) (y : ℝ≥0∞) :
    ContinuousAt (fun x : ℝ≥0∞ => (x : EReal) - (L : EReal)) y := by
  have h1 : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) ((y : EReal), ((-L : ℝ) : EReal)) :=
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  have h2 : ContinuousAt (fun x : ℝ≥0∞ => (x : EReal) + ((-L : ℝ) : EReal)) y :=
    h1.comp (f := fun x : ℝ≥0∞ => ((x : EReal), ((-L : ℝ) : EReal)))
      (continuous_coe_ennreal_ereal.continuousAt.prodMk continuousAt_const)
  convert h2 using 2 with x
  rw [sub_eq_add_neg, EReal.coe_neg]

lemma tsum_fatou {S : Type*} (P : S → ℝ≥0∞) (f : ℕ → S → ℝ≥0∞) :
    ∑' j, P j * liminf (fun N => f N j) atTop ≤ liminf (fun N => ∑' j, P j * f N j) atTop := by
  let _ : MeasurableSpace S := ⊤
  let μ : MeasureTheory.Measure S := MeasureTheory.Measure.sum (fun j => P j • MeasureTheory.Measure.dirac j)
  have hint : ∀ g : S → ℝ≥0∞, ∫⁻ x, g x ∂μ = ∑' j, P j * g j := by
    intro g
    rw [MeasureTheory.lintegral_sum_measure]
    congr 1
    ext j
    rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac' j measurable_from_top,
      smul_eq_mul]
  have := MeasureTheory.lintegral_liminf_le' (μ := μ) (f := f) (u := atTop)
    (fun _ => measurable_from_top.aemeasurable)
  rw [hint] at this
  simpa only [hint] using this

end SennottFatouAux

open Filter Topology ENNReal SennottDP.Fatou in
theorem solution {S : Type*} [Countable S] (P : S → ℝ≥0∞) (hP : ∑' j, P j = 1)
    (u : S → ℕ → EReal) (L : ℝ) (hL : 0 ≤ L) (hu : ∀ j N, ((-L : ℝ) : EReal) ≤ u j N) :
    wsum P (fun j => liminf (fun N => u j N) atTop) ≤
      liminf (fun N => wsum P (fun j => u j N)) atTop := by
  have hlim : ∀ j, ((-L : ℝ) : EReal) ≤ liminf (fun N => u j N) atTop :=
    fun j => le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (hu j))
  rw [SennottFatouAux.key P hP L hL _ hlim]
  simp_rw [SennottFatouAux.key P hP L hL _ (fun j => hu j _)]
  have hg : ∀ j, ((liminf (fun N => u j N) atTop) + (L : EReal)).toENNReal =
      liminf (fun N => (u j N + (L : EReal)).toENNReal) atTop := fun j =>
    (SennottFatouAux.g_mono L).map_liminf_of_continuousAt (fun N => u j N)
      (SennottFatouAux.g_cont L _)
  simp_rw [hg]
  have hF := SennottFatouAux.tsum_fatou P (fun N j => (u j N + (L : EReal)).toENNReal)
  calc _ ≤ ((liminf (fun N => ∑' j, P j * (u j N + (L : EReal)).toENNReal) atTop : ℝ≥0∞) : EReal)
        - (L : EReal) := SennottFatouAux.h_mono L hF
    _ = _ := (SennottFatouAux.h_mono L).map_liminf_of_continuousAt _ (SennottFatouAux.h_cont L _)
