-- Prove2me | solution 2 for TaoFivePrimes.theorem51_typeII_dyadic_representation
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T12:19:38.075951+00:00
-- url     : https://prove2.me/submissions/9ef20ae4-3cea-4a94-89ec-595d005d8137

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_eta0_dyadic_integral

open MeasureTheory Set
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # The dyadic representation of the Type II sum (Tao, arXiv:1201.6656v4, Section 5)

Proof of `TaoFivePrimes.theorem51_typeII_dyadic_representation`: the dyadic block
`G(W)` of the Type II bilinear sum vanishes off `[V, x/U]`, `W ↦ G(W)/W` is
integrable on `(0,∞)`, and `T_II ≤ 4 ∫₀^∞ G(W) dW/W`. The engine is the public
node `TaoFivePrimes.eta0_dyadic_integral`; the double sum is truncated with
`tsum_eq_sum` to the finite box `d ≤ x/V`, `w ≤ x/U`, and the integral is
interchanged with the finite sums via `integral_finsetSum`. -/

namespace TaoFivePrimes

private noncomputable def Bc (alpha V : ℝ) (d w : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((theorem51Centered V w : ℝ) : ℂ) *
    expCircle (alpha * d * w)

private abbrev Bbase (U V : ℝ) (d w : ℕ) : Prop :=
  U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2

private abbrev Bbox (x W : ℝ) (d w : ℕ) : Prop :=
  x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W

private abbrev Bcond (U V x W : ℝ) (d w : ℕ) : Prop :=
  U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 ∧
    x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W

private noncomputable def Bsum (alpha U V x : ℝ) (W : ℝ) : ℂ :=
  ∑' d : ℕ, ∑' w : ℕ, (if Bcond U V x W d w then Bc alpha V d w else 0)

private noncomputable def Bfin (alpha U V x : ℝ) (D0 W0 : ℕ) (W : ℝ) : ℂ :=
  ∑ d ∈ Finset.range D0, ∑ w ∈ Finset.range W0,
    (if Bcond U V x W d w then Bc alpha V d w else 0)

private noncomputable def Tsum (alpha U V x : ℝ) : ℂ :=
  ∑' d : ℕ, ∑' w : ℕ,
    (if Bbase U V d w then Bc alpha V d w * (eta0 ((d : ℝ) * w / x) : ℂ) else 0)

private noncomputable def Tfin (alpha U V x : ℝ) (D0 W0 : ℕ) : ℂ :=
  ∑ d ∈ Finset.range D0, ∑ w ∈ Finset.range W0,
    (if Bbase U V d w then Bc alpha V d w * (eta0 ((d : ℝ) * w / x) : ℂ) else 0)

private lemma eta0_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith : 0 < t)]
  have h : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by
    have hlog2 : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
    have hpos : 0 < Real.log (2 * t) := Real.log_pos (by linarith)
    rw [abs_of_pos hpos]
    linarith
  rw [max_eq_left h]
  ring

private lemma Bcond_iff_box {U V x W : ℝ} {d w : ℕ} (h : Bbase U V d w) :
    (Bcond U V x W d w ↔ Bbox x W d w) := by
  rcases h with ⟨h1, h2, h3, h4⟩
  constructor
  · intro hh
    exact ⟨hh.2.2.2.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2⟩
  · intro hh
    exact ⟨h1, h2, h3, h4, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩

private lemma Bbase_of_Bcond {U V x W : ℝ} {d w : ℕ} (h : Bcond U V x W d w) :
    Bbase U V d w :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

private lemma Bbox_iff_mem {x W : ℝ} {d w : ℕ} (hx : 0 < x) (hd : 0 < (d : ℝ))
    (hw : 0 < (w : ℝ)) (hW : 0 < W) :
    (Bbox x W d w ↔
      W ∈ Set.Icc (max (x / (2 * (d : ℝ))) (w : ℝ)) (min (x / (d : ℝ)) (2 * (w : ℝ)))) := by
  rw [Set.mem_Icc, Bbox, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨hE, hF, hG, hH⟩
    refine ⟨⟨?_, hH⟩, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * W)] at hE
      linarith
    · rw [le_div_iff₀ hd]
      rw [le_div_iff₀ hW] at hF
      linarith
    · linarith
  · rintro ⟨⟨hE, hH⟩, hF, hG⟩
    refine ⟨?_, ?_, ?_, hH⟩
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * W)]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))] at hE
      linarith
    · rw [le_div_iff₀ hW]
      rw [le_div_iff₀ hd] at hF
      linarith
    · linarith


theorem theorem51_typeII_dyadic_representation
    (x alpha U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∀ W : ℝ, W ∉ Set.Icc V (x / U) → ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ = 0)
      ∧ MeasureTheory.IntegrableOn (fun W : ℝ => ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W) (Set.Ioi 0)
      ∧ TaoFivePrimes.theorem51TypeII x alpha U V
          ≤ 4 * ∫ W in Set.Ioi (0:ℝ), ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W := by
  classical
  change (∀ W : ℝ, W ∉ Set.Icc V (x / U) →
      ‖∑' d : ℕ, ∑' w : ℕ,
        (if Bcond U V x W d w then Bc alpha V d w else 0)‖ = 0) ∧
    MeasureTheory.IntegrableOn (fun W : ℝ => ‖∑' d : ℕ, ∑' w : ℕ,
        (if Bcond U V x W d w then Bc alpha V d w else 0)‖ / W) (Set.Ioi 0) ∧
    theorem51TypeII x alpha U V ≤ 4 * ∫ W in Set.Ioi (0 : ℝ), ‖∑' d : ℕ, ∑' w : ℕ,
        (if Bcond U V x W d w then Bc alpha V d w else 0)‖ / W
  have hVpos : 0 < V := by linarith
  have hUpos : 0 < U := by linarith
  have hBfin : ∀ W : ℝ, Bsum alpha U V x W =
      Bfin alpha U V x (⌊x / V⌋₊ + 1) (⌊x / U⌋₊ + 1) W := by
    intro W
    unfold Bsum Bfin
    rw [tsum_eq_sum (s := Finset.range (⌊x / V⌋₊ + 1))]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [tsum_eq_sum (s := Finset.range (⌊x / U⌋₊ + 1))]
      intro w hw
      · have hwge : ⌊x / U⌋₊ + 1 ≤ w := by
          simpa only [Finset.mem_range, not_lt] using hw
        by_cases hbc : Bcond U V x W d w
        · exfalso
          rcases hbc with ⟨hUd, hVw, -, -, -, hdle, -, hwle⟩
          have hWV : V < W := lt_of_lt_of_le hVw hwle
          have hWpos : 0 < W := by linarith
          have hwgt : x / U < (w : ℝ) := by
            have hle : ((⌊x / U⌋₊ : ℝ)) + 1 ≤ (w : ℝ) := by exact_mod_cast hwge
            have hfl := Nat.lt_floor_add_one (x / U)
            linarith
          have hWgt : x / U < W := lt_of_lt_of_le hwgt hwle
          have hxW : x / W < U := by
            rw [div_lt_iff₀ hWpos]
            have h1 : x < W * U := by
              rw [div_lt_iff₀ hUpos] at hWgt
              linarith
            linarith
          exact absurd (lt_trans (lt_of_le_of_lt hdle hxW) hUd) (lt_irrefl _)
        · simp only [hbc, if_false]
    · intro d hd
      have hz : ∀ w : ℕ, ¬ Bcond U V x W d w := by
        intro w hbc
        rcases hbc with ⟨hUd, hVw, -, -, -, hdle, -, hwle⟩
        have hdge : ⌊x / V⌋₊ + 1 ≤ d := by
          simpa only [Finset.mem_range, not_lt] using hd
        have hWV : V < W := lt_of_lt_of_le hVw hwle
        have hdgt : x / V < (d : ℝ) := by
          have hle : ((⌊x / V⌋₊ : ℝ)) + 1 ≤ (d : ℝ) := by exact_mod_cast hdge
          have hfl := Nat.lt_floor_add_one (x / V)
          linarith
        have hxWlt : x / W < x / V := div_lt_div_of_pos_left hx hVpos hWV
        exact absurd (lt_trans (lt_of_le_of_lt hdle hxWlt) hdgt) (lt_irrefl _)
      simp only [hz, if_false, tsum_zero]
  have hTfin : Tsum alpha U V x =
      Tfin alpha U V x (⌊x / V⌋₊ + 1) (⌊x / U⌋₊ + 1) := by
    unfold Tsum Tfin
    rw [tsum_eq_sum (s := Finset.range (⌊x / V⌋₊ + 1))]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [tsum_eq_sum (s := Finset.range (⌊x / U⌋₊ + 1))]
      intro w hw
      · have hwge : ⌊x / U⌋₊ + 1 ≤ w := by
          simpa only [Finset.mem_range, not_lt] using hw
        by_cases hbb : Bbase U V d w
        · have hwgt : x / U < (w : ℝ) := by
            have hle : ((⌊x / U⌋₊ : ℝ)) + 1 ≤ (w : ℝ) := by exact_mod_cast hwge
            have hfl := Nat.lt_floor_add_one (x / U)
            linarith
          have hbbs : Bbase U V d w := hbb
          obtain ⟨hUd, hVw, -, -⟩ := hbb
          have hdw : x < (d : ℝ) * (w : ℝ) := by
            have hUx : U * (x / U) = x := by field_simp
            nlinarith [hUd, hwgt, mul_pos hUpos (by positivity : (0 : ℝ) < x / U), hUx]
          have hη : eta0 ((d : ℝ) * (w : ℝ) / x) = 0 :=
            eta0_eq_zero_of_one_le (by rw [le_div_iff₀ hx]; linarith)
          rw [if_pos hbbs, hη]
          simp
        · simp only [hbb, if_false]
    · intro d hd
      have hz : ∀ w : ℕ,
          (if Bbase U V d w then Bc alpha V d w * (eta0 ((d : ℝ) * (w : ℝ) / x) : ℂ) else 0) = 0 := by
        intro w
        by_cases hbb : Bbase U V d w
        · have hbbs : Bbase U V d w := hbb
          obtain ⟨hUd, hVw, -, -⟩ := hbb
          have hdge : ⌊x / V⌋₊ + 1 ≤ d := by
            simpa only [Finset.mem_range, not_lt] using hd
          have hdgt : x / V < (d : ℝ) := by
            have hle : ((⌊x / V⌋₊ : ℝ)) + 1 ≤ (d : ℝ) := by exact_mod_cast hdge
            have hfl := Nat.lt_floor_add_one (x / V)
            linarith
          have hdw : x < (d : ℝ) * (w : ℝ) := by
            have hVx : V * (x / V) = x := by field_simp
            nlinarith [hVw, hdgt, mul_pos hVpos (by positivity : (0 : ℝ) < x / V), hVx]
          have hη : eta0 ((d : ℝ) * (w : ℝ) / x) = 0 :=
            eta0_eq_zero_of_one_le (by rw [le_div_iff₀ hx]; linarith)
          rw [if_pos hbbs, hη]
          simp
        · simp only [hbb, if_false]
      simp only [hz, tsum_zero]

  have hInt : ∀ d w : ℕ, MeasureTheory.IntegrableOn
      (fun W : ℝ => (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
      (Set.Ioi 0) := by
    intro d w
    by_cases hbb : Bbase U V d w
    · have hbbs : Bbase U V d w := hbb
      obtain ⟨hUd, hVw, -, -⟩ := hbb
      have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
      have hwpos : (0 : ℝ) < (w : ℝ) := by linarith
      have hInd : ∀ W : ℝ,
          (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0) =
          Set.indicator (Set.Icc (max (x / (2 * (d : ℝ))) (w : ℝ))
              (min (x / (d : ℝ)) (2 * (w : ℝ))))
            (fun W : ℝ => Bc alpha V d w * ((1 : ℝ) / W : ℂ)) W := by
        intro W
        by_cases hW : 0 < W
        · have hiff : (Bcond U V x W d w ↔
              W ∈ Set.Icc (max (x / (2 * (d : ℝ))) (w : ℝ))
                (min (x / (d : ℝ)) (2 * (w : ℝ)))) :=
            (Bcond_iff_box hbbs).trans (Bbox_iff_mem hx hdpos hwpos hW)
          by_cases hbc : Bcond U V x W d w
          · rw [if_pos hbc,
              Set.indicator_of_mem (hiff.mp hbc) (fun W => Bc alpha V d w * ((1 : ℝ) / W : ℂ))]
          · rw [if_neg hbc,
              Set.indicator_of_notMem (fun hmem => hbc (hiff.mpr hmem))
                (fun W => Bc alpha V d w * ((1 : ℝ) / W : ℂ))]
        · have hnot : ¬ Bcond U V x W d w := by
            intro hbc
            rcases hbc with ⟨-, hVw', -, -, -, -, -, hwle⟩
            have hle : (w : ℝ) ≤ W := hwle
            linarith
          rw [if_neg hnot,
            Set.indicator_of_notMem (fun hmem =>
              (not_lt_of_ge hmem.1)
                (lt_of_le_of_lt (le_of_not_gt hW)
                  (lt_max_of_lt_left (by positivity : (0 : ℝ) < x / (2 * (d : ℝ))))))]
      rw [show (fun W : ℝ => (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
          = Set.indicator (Set.Icc (max (x / (2 * (d : ℝ))) (w : ℝ))
              (min (x / (d : ℝ)) (2 * (w : ℝ))))
            (fun W : ℝ => Bc alpha V d w * ((1 : ℝ) / W : ℂ)) from funext hInd]
      rw [MeasureTheory.integrableOn_indicator_iff measurableSet_Icc]
      have hsub : Set.Icc (max (x / (2 * (d : ℝ))) (w : ℝ))
            (min (x / (d : ℝ)) (2 * (w : ℝ))) ⊆ Set.Ioi (0 : ℝ) := by
        intro W hW
        exact lt_of_lt_of_le
          (lt_max_of_lt_left (by positivity : (0 : ℝ) < x / (2 * (d : ℝ)))) hW.1
      rw [Set.inter_eq_left.mpr hsub]
      apply ContinuousOn.integrableOn_Icc
      have hreal : ContinuousOn (fun W : ℝ => (1 : ℂ) / (W : ℂ))
          (Set.Icc (max (x / (2 * (d : ℝ))) (w : ℝ))
            (min (x / (d : ℝ)) (2 * (w : ℝ)))) := by
        apply ContinuousOn.div continuousOn_const
        · exact Complex.continuous_ofReal.comp_continuousOn continuousOn_id
        · intro W hW
          exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le
            (lt_max_of_lt_left (by positivity : (0 : ℝ) < x / (2 * (d : ℝ)))) hW.1))
      have hmul : ContinuousOn
          ((fun _ : ℝ => Bc alpha V d w) * fun W : ℝ => (1 : ℂ) / (W : ℂ))
          (Set.Icc (max (x / (2 * (d : ℝ))) (w : ℝ))
            (min (x / (d : ℝ)) (2 * (w : ℝ)))) :=
        continuousOn_const.mul hreal
      refine hmul.congr (fun W _ => ?_)
      simp only [Pi.mul_apply, Complex.ofReal_div, Complex.ofReal_one]
    · have hzero : (fun W : ℝ => (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
          = fun _ => 0 := by
        funext W
        rw [if_neg (fun hbc => hbb (Bbase_of_Bcond hbc))]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero


  have hbridge : ∀ d w : ℕ,
      (if Bbase U V d w then Bc alpha V d w * (eta0 ((d : ℝ) * w / x) : ℂ) else 0) =
      4 * ∫ W in Set.Ioi (0 : ℝ),
        (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0) := by
    intro d w
    by_cases hbb : Bbase U V d w
    · have hbbs : Bbase U V d w := hbb
      obtain ⟨hUd, hVw, -, -⟩ := hbb
      have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
      have hwpos : (0 : ℝ) < (w : ℝ) := by linarith
      have hdy := eta0_dyadic_integral x (d : ℝ) (w : ℝ) hx hdpos hwpos
      rw [if_pos hbbs, ← hdy]
      have hcast : ((∫ W in Set.Ioi (0 : ℝ), (if Bbox x W d w then (1 : ℝ) / W else 0) : ℝ) : ℂ)
          = ∫ W in Set.Ioi (0 : ℝ), (if Bbox x W d w then ((1 : ℝ) / W : ℂ) else 0) := by
        symm
        calc (∫ W in Set.Ioi (0 : ℝ), (if Bbox x W d w then ((1 : ℝ) / W : ℂ) else 0))
            = ∫ W in Set.Ioi (0 : ℝ),
                (fun W : ℝ => ↑(if Bbox x W d w then (1 : ℝ) / W else 0)) W := by
              apply integral_congr_ae
              filter_upwards with W
              by_cases hb : Bbox x W d w
              · rw [if_pos hb, if_pos hb]
                exact (Complex.ofReal_div 1 W).symm
              · rw [if_neg hb, if_neg hb]
                exact Complex.ofReal_zero.symm
          _ = ↑(∫ W in Set.Ioi (0 : ℝ), (if Bbox x W d w then (1 : ℝ) / W else 0)) :=
              integral_ofReal
      have hpt : ∀ W : ℝ,
          (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)
            = Bc alpha V d w * (if Bbox x W d w then ((1 : ℝ) / W : ℂ) else 0) := by
        intro W
        by_cases hbc : Bcond U V x W d w
        · rw [if_pos hbc, if_pos ((Bcond_iff_box hbbs).mp hbc)]
        · rw [if_neg hbc, if_neg (fun hb => hbc ((Bcond_iff_box hbbs).mpr hb)), mul_zero]
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat, hcast]
      rw [show (∫ W in Set.Ioi (0 : ℝ),
            (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
          = ∫ W in Set.Ioi (0 : ℝ),
              Bc alpha V d w * (if Bbox x W d w then ((1 : ℝ) / W : ℂ) else 0)
          from integral_congr_ae (Filter.Eventually.of_forall hpt)]
      rw [integral_const_mul]
      ring
    · have hz : (fun W : ℝ =>
            (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)) = fun _ => 0 := by
        funext W
        rw [if_neg (fun hbc => hbb (Bbase_of_Bcond hbc))]
      rw [if_neg hbb, hz]
      simp

  have hpoint : ∀ᵐ W ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
          (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)‖ =
      ‖Bsum alpha U V x W‖ / W := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with W hW
    have hWpos : 0 < W := hW
    have hWne : W ≠ 0 := ne_of_gt hWpos
    have hscale : (∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
          (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)) =
        (∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
          (if Bcond U V x W d w then Bc alpha V d w else 0)) * ((1 : ℝ) / W : ℂ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hbc : Bcond U V x W d w
      · rw [if_pos hbc, if_pos hbc]
      · rw [if_neg hbc, if_neg hbc, zero_mul]
    have hnorm : ‖(((1 : ℝ) / W : ℂ))‖ = 1 / W := by
      rw [show ‖(((1 : ℝ) / W : ℂ))‖ = |(1 : ℝ) / W| from by simp]
      exact abs_of_pos (one_div_pos.mpr hWpos)
    rw [hscale, norm_mul, hnorm, hBfin]
    unfold Bfin
    ring

  constructor
  · intro W hW
    have hz : ∀ d w : ℕ, ¬ Bcond U V x W d w := by
      intro d w h
      rcases h with ⟨hUd, hVw, -, -, -, hdle, -, hwW⟩
      have hWV : V < W := lt_of_lt_of_le hVw hwW
      have hWpos : 0 < W := by linarith
      by_cases hWU : W ≤ x / U
      · exact hW ⟨hWV.le, hWU⟩
      · have hxWlt : x / W < U := by
          have hUW : x / U < W := lt_of_not_ge hWU
          rw [div_lt_iff₀ hWpos]
          rw [div_lt_iff₀ hUpos] at hUW
          nlinarith
        exact absurd (lt_trans (lt_of_le_of_lt hdle hxWlt) hUd) (lt_irrefl _)
    simp only [hz, if_false, tsum_zero, norm_zero]
  · constructor
    · change MeasureTheory.Integrable (fun W : ℝ => ‖Bsum alpha U V x W‖ / W)
          (volume.restrict (Set.Ioi (0 : ℝ)))
      have hsum : MeasureTheory.Integrable (fun W : ℝ =>
          ∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
            (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        refine MeasureTheory.integrable_finsetSum (Finset.range (⌊x / V⌋₊ + 1)) ?_
        intro d hd
        refine MeasureTheory.integrable_finsetSum (Finset.range (⌊x / U⌋₊ + 1)) ?_
        intro w hw
        exact hInt d w
      refine (hsum.norm).congr ?_
      filter_upwards [hpoint] with W hW
      exact hW
    · change ‖Tsum alpha U V x‖ ≤ 4 * ∫ W in Set.Ioi (0 : ℝ), ‖Bsum alpha U V x W‖ / W
      rw [hTfin]
      calc ‖Tfin alpha U V x (⌊x / V⌋₊ + 1) (⌊x / U⌋₊ + 1)‖
          = ‖∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
              (4 * ∫ W in Set.Ioi (0 : ℝ),
                (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))‖ := by
            congr 1
            unfold Tfin
            apply Finset.sum_congr rfl
            intro d hd
            apply Finset.sum_congr rfl
            intro w hw
            exact hbridge d w
        _ = 4 * ‖∫ W in Set.Ioi (0 : ℝ), ∑ d ∈ Finset.range (⌊x / V⌋₊ + 1),
              ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
              (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)‖ := by
            have hIntSum : (∫ W in Set.Ioi (0 : ℝ), ∑ d ∈ Finset.range (⌊x / V⌋₊ + 1),
                  ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
                  (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
                = ∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
                  ∫ W in Set.Ioi (0 : ℝ),
                    (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0) := by
              rw [MeasureTheory.integral_finsetSum (s := Finset.range (⌊x / V⌋₊ + 1))
                (f := fun d (W : ℝ) => ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
                  (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
                (fun d hd => MeasureTheory.integrable_finsetSum (Finset.range (⌊x / U⌋₊ + 1))
                  (fun w hw => hInt d w))]
              apply Finset.sum_congr rfl
              intro d hd
              rw [MeasureTheory.integral_finsetSum (s := Finset.range (⌊x / U⌋₊ + 1))
                (f := fun w (W : ℝ) =>
                  (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
                (fun w hw => hInt d w)]
            have hfact : (∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
                  (4 * ∫ W in Set.Ioi (0 : ℝ),
                    (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)))
                = 4 * (∑ d ∈ Finset.range (⌊x / V⌋₊ + 1), ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
                  ∫ W in Set.Ioi (0 : ℝ),
                    (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro d hd
              rw [Finset.mul_sum]
            rw [hfact, ← hIntSum, norm_mul, Complex.norm_ofNat]
        _ ≤ 4 * ∫ W in Set.Ioi (0 : ℝ), ‖∑ d ∈ Finset.range (⌊x / V⌋₊ + 1),
              ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
              (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0)‖ := by
            have hle := MeasureTheory.norm_integral_le_integral_norm
              (μ := volume.restrict (Set.Ioi (0 : ℝ)))
              (f := fun W : ℝ => ∑ d ∈ Finset.range (⌊x / V⌋₊ + 1),
                ∑ w ∈ Finset.range (⌊x / U⌋₊ + 1),
                (if Bcond U V x W d w then Bc alpha V d w * ((1 : ℝ) / W : ℂ) else 0))
            linarith
        _ = 4 * ∫ W in Set.Ioi (0 : ℝ), ‖Bsum alpha U V x W‖ / W := by
            congr 1
            apply integral_congr_ae
            filter_upwards [hpoint] with W hW
            exact hW

end TaoFivePrimes


theorem solution
    (x alpha U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∀ W : ℝ, W ∉ Set.Icc V (x / U) → ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ = 0)
      ∧ MeasureTheory.IntegrableOn (fun W : ℝ => ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W) (Set.Ioi 0)
      ∧ TaoFivePrimes.theorem51TypeII x alpha U V
          ≤ 4 * ∫ W in Set.Ioi (0:ℝ), ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W := by
  exact TaoFivePrimes.theorem51_typeII_dyadic_representation x alpha U V hx hU40 hV40 hUx hVx hUV hUV2
