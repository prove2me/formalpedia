-- Prove2me | solution 1 for RiemannVonMangoldt.riemann_von_mangoldt
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:37:37.361165+00:00
-- url     : https://prove2.me/submissions/50f8f178-e9a5-4d0a-8ae6-0879864bd03b

import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Theorems.Thm_Zeta23_RvM_rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount
import Theorems.Thm_Zeta23_RvM_rectangleIntegral_logDeriv_completedZeta_eq_halfContour
import Theorems.Thm_Zeta23_RvM_halfContour_completedZeta_split
import Theorems.Thm_Zeta23_RvM_gamma_side
import Theorems.Thm_Zeta23_RvM_exists_goodHeight
import Theorems.Thm_Zeta23_RvM_backlund_horizontal_of_count
import Theorems.Thm_Zeta23_RvM_reZeroSet_card_le_of_growth
import Theorems.Thm_Zeta23_RvM_zeta_growth_right_at
import Theorems.Thm_Zeta23_RvM_vertical_two
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_Zeta23_mu_smooth
import Theorems.Thm_Zeta23_StirlingVert_mu_stirling

/-
Some lemmas adapted from Zeta23 (copyright 2026 Anthropic, PBC), Apache-2.0.
Upstream revision: anthropics/formal-math 16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
In particular the window arithmetic is adapted from Zeta23/RvM/NcountWindow.lean
and the folded count is adapted from Zeta23/RvM/Fold.lean. The main theorem
assembles the cumulative count using the published Zeta23 estimates.
-/

/-!
Cumulative Riemann–von Mangoldt formula. The folded argument principle and
Backlund estimates are from the Apache-2.0 Zeta23 development, specifically
`Zeta23/RvM/{MainTerm,Backlund,LocalCount}.lean` and
`Zeta23/GammaFacts/StirlingVert.lean`, anthropics/formal-math commit
16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Fixing the lower good height leaves just one varying endpoint; summing
independent dyadic error bounds would lose a logarithm. The unit-window count
handles ordinates that are zero heights and gives the exact `(0,T]` convention.
-/

open Asymptotics Complex Filter MeasureTheory
open scoped Topology

noncomputable section

namespace MasulloAudit.RvM

open Zeta23 Zeta23.RvM
open Set

private lemma zerosIn_finite (a b : ℝ) : (zerosIn a b).Finite := by
  exact ZetaSeam.finite_window_holds a b

private lemma zerosIn_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    zerosIn a c = zerosIn a b ∪ zerosIn b c := by
  ext ρ
  simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hb⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hb⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, ha, hb⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 ha, hb⟩

/-- window additivity: N(a,c] = N(a,b] + N(b,c]. -/
private lemma Ncount_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Ncount a c = Ncount a b + Ncount b c := by
  unfold Ncount
  rw [zerosIn_union h1 h2]
  refine finsum_mem_union ?_ (zerosIn_finite a b) (zerosIn_finite b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, ha, _⟩
  exact absurd hb (not_le.2 ha)

/-- window monotonicity: (a,b] ⊆ (c,d] ⇒ N(a,b] ≤ N(c,d]. -/
private lemma Ncount_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Ncount a b ≤ Ncount c d := by
  unfold Ncount
  have hsub : zerosIn a b ⊆ zerosIn c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite a b),
    finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite c d)]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ


private lemma N_eq_halfContour_completedZeta {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ)
      = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im := by
  have h := rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount (by linarith) h12.le hg1 hg2
  change (1 / (2 * Real.pi * I)) • RectangleIntegral _ _ _ = _ at h
  rw [rectangleIntegral_logDeriv_completedZeta_eq_halfContour h1 h12 hg1 hg2, smul_eq_mul] at h
  have h' : ((Ncount T₁ T₂ : ℝ) : ℂ)
      = (((1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    field_simp
  exact_mod_cast h'

private lemma backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T := by
  apply backlund_horizontal_of_count
  exact ⟨_, 4, reZeroSet_card_le_of_growth (A := 1) (C := 20 / 3) (by norm_num)
    zeta_growth_right_at⟩

private def mainTerm (t : ℝ) : ℝ :=
  (t / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi)

private def mainDensity (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))

private lemma mainDensity_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable mainDensity volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  refine (ContinuousAt.const_mul ?_ _).continuousWithinAt
  exact (Real.continuousAt_log (by positivity)).comp (continuousAt_id.div_const _)

private lemma integral_mainDensity {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, mainDensity t) = mainTerm b - mainTerm a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ (mainDensity_integrable ha hab)
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hx0 : 0 < x := ha.trans_le hx.1
  have hπ : 0 < Real.pi := Real.pi_pos
  have hd : HasDerivAt (fun t : ℝ ↦ t / (2 * Real.pi)) (1 / (2 * Real.pi)) x :=
    (hasDerivAt_id x).div_const _
  have hlog := hd.log (by positivity : x / (2 * Real.pi) ≠ 0)
  have hf := (hd.mul hlog).sub hd
  have hone : x / (2 * Real.pi) * (1 / (2 * Real.pi) / (x / (2 * Real.pi))) =
      1 / (2 * Real.pi) := by
    field_simp
  rw [hone, add_sub_cancel_right] at hf
  exact hf

private lemma gamma_error {a b C : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hC : 0 ≤ C)
    (hst : ∀ t : ℝ, 1 ≤ |t| →
      |mu t - (1 / (2 * Real.pi)) * Real.log (|t| / (2 * Real.pi))| ≤ C / t ^ 2) :
    |(∫ t in a..b, mu t) - (mainTerm b - mainTerm a)| ≤ C := by
  have ha0 : 0 < a := by linarith
  have hm := mainDensity_integrable ha0 hab
  have hmu : IntervalIntegrable mu volume a b :=
    Zeta23.mu_smooth.continuous.intervalIntegrable a b
  have hdom : IntervalIntegrable (fun t : ℝ ↦ C / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.div (continuous_pow 2).continuousOn ?_
    exact fun t ht ↦ pow_ne_zero _ (ha0.trans_le ht.1).ne'
  have hinv : (∫ t in a..b, C / t ^ 2) = C / a - C / b := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ ↦ -C / t) (f' := fun t ↦ C / t ^ 2) ?_ hdom
    · rw [h]
      ring
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht0 : t ≠ 0 := (ha0.trans_le ht.1).ne'
      have hfun : (fun x : ℝ ↦ -C / x) = fun x ↦ -C * x⁻¹ :=
        funext fun x ↦ div_eq_mul_inv (-C) x
      rw [hfun, div_eq_mul_inv, ← neg_mul_neg C ((t ^ 2)⁻¹)]
      exact (hasDerivAt_inv ht0).const_mul (-C)
  calc
    _ = |∫ t in a..b, mu t - mainDensity t| := by
      rw [intervalIntegral.integral_sub hmu hm, integral_mainDensity ha0 hab]
    _ ≤ ∫ t in a..b, |mu t - mainDensity t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, C / t ^ 2 := by
      refine intervalIntegral.integral_mono_on hab (hmu.sub hm).abs hdom ?_
      intro t ht
      have ht1 : 1 ≤ t := ha.trans ht.1
      simpa [mainDensity, abs_of_nonneg (zero_le_one.trans ht1)] using
        hst t (by simpa [abs_of_nonneg (zero_le_one.trans ht1)] using ht1)
    _ ≤ C := by
      rw [hinv]
      apply (sub_le_self _ (div_nonneg hC (by linarith))).trans
      exact (div_le_iff₀ ha0).2 (le_mul_of_one_le_right hC ha)

private lemma mainTerm_short {T b : ℝ} (hT : 4 ≤ T) (hlarge : 2 * Real.pi ≤ T)
    (hTb : T ≤ b) (hb : b ≤ T + 1) :
    |mainTerm b - mainTerm T| ≤ 2 * Real.log T := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hbound (t : ℝ) (ht : t ∈ Set.uIoc T b) : ‖mainDensity t‖ ≤ 2 * Real.log T := by
    rw [Set.uIoc_of_le hTb] at ht
    have htπ : 1 ≤ t / (2 * Real.pi) := (le_div_iff₀ (by positivity)).2 (by linarith [ht.1])
    have htT : t / (2 * Real.pi) ≤ T ^ 2 := by
      calc
        _ ≤ t := div_le_self (by linarith [ht.1]) hπ1
        _ ≤ T + 1 := ht.2.trans hb
        _ ≤ T ^ 2 := by nlinarith
    rw [mainDensity, Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.log_nonneg htπ))]
    have hle := Real.log_le_log (zero_lt_one.trans_le htπ) htT
    rw [Real.log_pow] at hle
    norm_num at hle
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans <|
      mul_le_of_le_one_left (by positivity) (div_le_one_of_le₀ hπ1 (by positivity))
  rw [← integral_mainDensity hT0 hTb, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans ?_
  rw [abs_of_nonneg (sub_nonneg.mpr hTb)]
  exact mul_le_of_le_one_right (by positivity) (by linarith)

private lemma zeta_contour_bound {a b CB : ℝ}
    (ha : |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + a * I)).im| ≤ CB * Real.log a)
    (hb : |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + b * I)).im| ≤ CB * Real.log b) :
    |(halfContour (logDeriv riemannZeta) a b).im| ≤
      CB * Real.log a + Real.pi + CB * Real.log b := by
  unfold halfContour
  simp only [Complex.add_im, Complex.sub_im]
  rw [← intervalIntegral.integral_mul_const]
  exact (abs_sub _ _).trans <|
    add_le_add ((abs_add_le _ _).trans (add_le_add ha (vertical_two a b))) hb

private theorem cumulativeNcount :
    (fun T : ℝ ↦ (Ncount 0 T : ℝ) - mainTerm T) =O[atTop] Real.log := by
  obtain ⟨CB', TB, hB'⟩ := backlund_horizontal
  let CB := |CB'|
  have hCB : 0 ≤ CB := abs_nonneg _
  have hB (t : ℝ) (ht : 1 ≤ t) (htB : TB ≤ t) (hg : GoodHeight t) :
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + t * I)).im| ≤ CB * Real.log t :=
    (hB' t htB hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg ht))
  obtain ⟨a, ha, hga⟩ := exists_goodHeight (max 1 TB)
  have ha1 : 1 ≤ a := (le_max_left 1 TB).trans ha.1
  have haB : TB ≤ a := (le_max_right 1 TB).trans ha.1
  have ha0 : 0 < a := by linarith
  obtain ⟨CS', hS'⟩ := StirlingVert.mu_stirling
  let CS := |CS'|
  have hS (x : ℝ) (hx : 1 ≤ |x|) :
      |mu x - (1 / (2 * Real.pi)) * Real.log (|x| / (2 * Real.pi))| ≤ CS / x ^ 2 :=
    (hS' x hx).trans (div_le_div_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  obtain ⟨A, hA1, hA⟩ := zeta_local_zero_count
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  let K := |(Ncount 0 a : ℝ) - mainTerm a| + CS +
    (1 / Real.pi) * (CB * Real.log a + Real.pi)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hK : 0 ≤ K := by
    unfold K
    exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (by positivity) (add_nonneg (mul_nonneg hCB (Real.log_nonneg ha1)) hπ.le))
  apply Asymptotics.IsBigO.of_bound (K + (1 / Real.pi) * (2 * CB) + 2 * A + 2)
  filter_upwards [eventually_ge_atTop (max (max 4 (a + 1)) (2 * Real.pi))] with T hT
  have hT4 : 4 ≤ T := (le_max_left 4 _).trans ((le_max_left _ _).trans hT)
  have haT : a < T := by linarith [(le_max_right (4 : ℝ) (a + 1)).trans ((le_max_left _ _).trans hT)]
  have hTpi : 2 * Real.pi ≤ T := (le_max_right _ _).trans hT
  have hlog1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 ≤ Real.log T := by linarith
  obtain ⟨b, hb, hgb⟩ := exists_goodHeight T
  have hab : a < b := haT.trans_le hb.1
  have hb1 : 1 ≤ b := by linarith [hb.1]
  have hb0 : 0 < b := by linarith
  have hbB : TB ≤ b := haB.trans hab.le
  have hlogs (x : ℝ) (hx : 0 < x) (hxT : x ≤ T ^ 2) : Real.log x ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T ^ 2) := Real.log_le_log hx hxT
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlogb : Real.log b ≤ 2 * Real.log T := hlogs b hb0 (by nlinarith [hb.2])
  have hwindow : (Ncount T b : ℝ) ≤ (2 * A) * Real.log T := by
    have hm := Ncount_mono (a := T) (b := b) le_rfl hb.2
    calc
      _ ≤ (Ncount T (T + 1) : ℝ) := by exact_mod_cast hm
      _ ≤ A * Real.log (|T| + 3) := hA T
      _ ≤ _ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ T), mul_comm (2 : ℝ) A, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hlogs _ (by linarith) (by nlinarith)) hA0
  have hformula : (Ncount a b : ℝ) =
      (1 / Real.pi) * (halfContour (logDeriv riemannZeta) a b).im + ∫ t in a..b, mu t := by
    rw [N_eq_halfContour_completedZeta ha1 hab hga hgb,
      halfContour_completedZeta_split ha1 hab hga hgb, Complex.add_im, mul_add,
      gamma_side ha0 hb0]
  have hζ := zeta_contour_bound (hB a ha1 haB hga) (hB b hb1 hbB hgb)
  have hΓ := gamma_error (C := CS) ha1 hab.le (abs_nonneg _) hS
  have hshort := mainTerm_short hT4 hTpi hb.1 hb.2
  have hadd₁ : (Ncount 0 b : ℝ) = (Ncount 0 a : ℝ) + (Ncount a b : ℝ) := by
    exact_mod_cast Ncount_add ha0.le hab.le
  have hadd₂ : (Ncount 0 b : ℝ) = (Ncount 0 T : ℝ) + (Ncount T b : ℝ) := by
    exact_mod_cast Ncount_add (by linarith) hb.1
  have hrewrite : (Ncount 0 T : ℝ) - mainTerm T =
      ((Ncount 0 a : ℝ) - mainTerm a) +
      (1 / Real.pi) * (halfContour (logDeriv riemannZeta) a b).im +
      ((∫ t in a..b, mu t) - (mainTerm b - mainTerm a)) +
      (mainTerm b - mainTerm T) - (Ncount T b : ℝ) := by linarith
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hlog0, hrewrite]
  calc
    _ ≤ |(Ncount 0 a : ℝ) - mainTerm a| +
        (1 / Real.pi) * |(halfContour (logDeriv riemannZeta) a b).im| +
        |(∫ t in a..b, mu t) - (mainTerm b - mainTerm a)| +
        |mainTerm b - mainTerm T| + (Ncount T b : ℝ) := by
      refine (abs_sub _ _).trans (add_le_add ?_ (abs_of_nonneg (by positivity)).le)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)])
    _ ≤ K + (1 / Real.pi) * (2 * CB) * Real.log T +
        (2 * A) * Real.log T + 2 * Real.log T := by
      have hζ' := mul_le_mul_of_nonneg_left hζ (by positivity : 0 ≤ 1 / Real.pi)
      have hcbLog := mul_le_mul_of_nonneg_left hlogb hCB
      unfold K
      linarith [mul_le_mul_of_nonneg_left hcbLog (by positivity : 0 ≤ 1 / Real.pi)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlog1 hK]

private lemma zetaZeroCount_eq (T : ℝ) :
    RiemannVonMangoldt.zetaZeroCount T = (Ncount 0 T : ℝ) := by
  unfold RiemannVonMangoldt.zetaZeroCount Ncount
  have heq : {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ riemannZeta s = 0} =
      zerosIn 0 T := by
    ext s
    simp only [zerosIn, IsNontrivialZero, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  rw [Nat.cast_finsum_mem (zerosIn_finite 0 T)]
  rfl

open Real in
theorem _root_.solution :
    (fun T : ℝ => RiemannVonMangoldt.zetaZeroCount T -
      (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))) =O[atTop] Real.log := by
  simpa only [zetaZeroCount_eq, mainTerm] using cumulativeNcount

end MasulloAudit.RvM

/-
Zeta23 — a Lean 4 formalization of critical-line zero-proportion theorems
Copyright 2026 Anthropic, PBC

This product is licensed under the Apache License, Version 2.0 (see LICENSE).

This product includes software derived from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, licensed under the Apache License, Version 2.0.
The derived files are the ones under Zeta23/FromPNTPlus/; each carries its upstream notice
(source file, upstream commit, original copyright line) and a description of the local modifications.
Some of those files in turn derive from mathlib (https://github.com/leanprover-community/mathlib4),
Copyright the mathlib contributors, Apache License, Version 2.0; their original headers are preserved.

This product depends on, but does not include, Lean 4 (https://github.com/leanprover/lean4) and
mathlib4 with its standard dependency set — fetched by the build tool from their public repositories at the
revisions pinned in lake-manifest.json: batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient and
plausible are released under the Apache License, Version 2.0; Cli (leanprover/lean4-cli) is released under the
MIT License (Copyright (c) 2021 Marc Huisinga). None of these dependencies is included in this repository.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
