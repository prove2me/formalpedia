-- Prove2me | solution 1 for PGDRevision20261113.same_feature_tangency_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T10:42:08.334437+00:00
-- url     : https://prove2.me/submissions/5ecb7a7d-39c0-4491-bac1-19057e33d8dd

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Theorems.Thm_PGDRevision20261113_tangency_derivative_identity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
set_option maxHeartbeats 3000000

open PGDRevision20261113
noncomputable section

private def skew (c t : ℝ) : ℝ :=
  (Real.rpow (1 - t) (-c) - Real.rpow (1 + t) (-c)) /
    (Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c))

private lemma curvature_pos (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    0 < powerCurvature c t := by
  unfold powerCurvature
  exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
    (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)

private lemma skew_nonneg_mono (c₁ c₂ t : ℝ) (hc₁ : 0 ≤ c₁) (hc : c₁ ≤ c₂)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ skew c₁ t ∧ skew c₁ t ≤ skew c₂ t := by
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hbase : 1 ≤ (1 + t) / (1 - t) := by
    apply (le_div_iff₀ hminus).2
    linarith [ht.1]
  have hratio (c : ℝ) :
      Real.rpow (1 - t) (-c) / Real.rpow (1 + t) (-c) =
        Real.rpow ((1 + t) / (1 - t)) c := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hminus.le, Real.rpow_neg hplus.le,
      inv_div_inv, Real.div_rpow hplus.le hminus.le]
  have ha₁ : 0 < Real.rpow (1 - t) (-c₁) := Real.rpow_pos_of_pos hminus _
  have hb₁ : 0 < Real.rpow (1 + t) (-c₁) := Real.rpow_pos_of_pos hplus _
  have ha₂ : 0 < Real.rpow (1 - t) (-c₂) := Real.rpow_pos_of_pos hminus _
  have hb₂ : 0 < Real.rpow (1 + t) (-c₂) := Real.rpow_pos_of_pos hplus _
  have hratio₁ : 1 ≤ Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) := by
    rw [hratio]
    simpa using Real.rpow_le_rpow_of_exponent_le hbase hc₁
  have hratios : Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) ≤
      Real.rpow (1 - t) (-c₂) / Real.rpow (1 + t) (-c₂) := by
    rw [hratio, hratio]
    exact Real.rpow_le_rpow_of_exponent_le hbase hc
  have horder := (le_div_iff₀ hb₁).mp hratio₁
  have hcross := (div_le_div_iff₀ hb₁ hb₂).mp hratios
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · unfold skew
    apply (div_le_div_iff₀ (add_pos ha₁ hb₁) (add_pos ha₂ hb₂)).2
    nlinarith only [hcross]

private lemma curvature_hasDerivAt (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivAt (powerCurvature c)
      (powerCurvature c t * (c * (t + skew c t)) / (1 - t ^ 2)) t := by
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (Or.inl (ne_of_gt hplus) : 1 + t ≠ 0 ∨ 1 ≤ -c)
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (Or.inl (ne_of_gt hminus) : 1 - t ≠ 0 ∨ 1 ≤ -c)
  have hsum : Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c) ≠ 0 :=
    ne_of_gt (add_pos (Real.rpow_pos_of_pos hminus _) (Real.rpow_pos_of_pos hplus _))
  have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (hp.add hm).div_const 2 using 1 <;> try rfl
  unfold powerCurvature skew
  simp only [id_eq, Real.rpow_eq_pow] at hsum ⊢
  rw [Real.rpow_sub_one (ne_of_gt hplus), Real.rpow_sub_one (ne_of_gt hminus)]
  field_simp [hsum, hden, ne_of_gt hplus, ne_of_gt hminus]
  <;> ring

private lemma ratio_hasDerivAt (c₁ c₂ t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivAt (fun t => powerCurvature c₂ t / powerCurvature c₁ t)
      ((powerCurvature c₂ t / powerCurvature c₁ t) *
        (c₂ * (t + skew c₂ t) - c₁ * (t + skew c₁ t)) / (1 - t ^ 2)) t := by
  have hk : powerCurvature c₁ t ≠ 0 := ne_of_gt (curvature_pos c₁ t ht)
  have hd : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (curvature_hasDerivAt c₂ t ht).div (curvature_hasDerivAt c₁ t ht) hk using 1
    <;> try rfl
  field_simp [hk, hd]
  <;> ring

private lemma power_abs (c t : ℝ) : powerCurvature c |t| = powerCurvature c t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp only [powerCurvature, sub_eq_add_neg, neg_neg, add_comm]

private lemma kernel_pos (G : GeometryData) (hG : AdmissibleGeometry G)
    (c t : ℝ) (ht : t ∈ geometryDomain G) : 0 < geometryKernel G c t := by
  cases hf : G.family with
  | interval beta =>
    have htd : t ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [geometryDomain, hf] using ht
    simp only [geometryKernel, hf]
    unfold powerCurvature
    exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [htd.1]) _)
      (Real.rpow_pos_of_pos (by linarith [htd.2]) _)) (by norm_num)
  | realLine =>
    rcases hG with ⟨_, _, _, _, hG⟩
    simp only [hf] at hG
    have hb : 0 < G.b t := by
      by_cases ht0 : t = 0
      · subst t
        rw [hG.2.2.1]
        norm_num
      · linarith [hG.2.2.2.1 t ht0]
    simpa [geometryKernel, hf] using Real.rpow_pos_of_pos hb c

private lemma error_le_iff (A B v w : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hv : 0 < v) (hw : 0 < w) :
    (v - A) / (v + B) ≤ (w - A) / (w + B) ↔ v ≤ w := by
  rw [div_le_div_iff₀ (by linarith : 0 < v + B) (by linarith : 0 < w + B)]
  constructor
  · intro h
    by_contra hn
    have hp := mul_pos (by linarith : 0 < A + B) (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith
  · intro h
    have hp := mul_nonneg (by linarith : 0 ≤ A + B) (sub_nonneg.mpr h)
    nlinarith

private lemma error_bound (G : GeometryData) (w : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hw : geometryRho G w.1 w.2 ≤ ENNReal.ofReal r)
    (t : ℝ) (ht : t ∈ geometryDomain G) : |geometryError G w.1 w.2 t| ≤ r := by
  have hs : ENNReal.ofReal |geometryError G w.1 w.2 t| ≤ geometryRho G w.1 w.2 :=
    le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp (hs.trans hw)

private lemma power_neg (c t : ℝ) : powerCurvature c (-t) = powerCurvature c t := by
  simp only [powerCurvature, sub_eq_add_neg, neg_neg, add_comm]

private lemma score_strict (a b q : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) : a * (q + skew a q) < b * (q + skew b q) := by
  have hs := skew_nonneg_mono a b q ha hab.le ⟨hq.1.le, hq.2⟩
  calc
    _ < b * (q + skew a q) := mul_lt_mul_of_pos_right hab (by linarith [hq.1, hs.1])
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by linarith)

private lemma power_positive_jet (a b p q x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hq : 0 < q) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hval : p * powerCurvature a x = q * powerCurvature b x)
    (hd : deriv (fun t => p * powerCurvature a t) x = deriv (fun t => q * powerCurvature b t) x) :
    a = b ∧ p = q := by
  have hxc : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hden : 1 - x ^ 2 ≠ 0 := ne_of_gt (by nlinarith [hx.1, hx.2])
  have hda := (curvature_hasDerivAt a x hxc).const_mul p
  have hdb := (curvature_hasDerivAt b x hxc).const_mul q
  rw [hda.deriv, hdb.deriv] at hd
  have he : (p * powerCurvature a x) * (a * (x + skew a x)) =
      (q * powerCurvature b x) * (b * (x + skew b x)) := by
    have hc : ((p * powerCurvature a x) * (a * (x + skew a x))) / (1 - x ^ 2) =
        ((q * powerCurvature b x) * (b * (x + skew b x))) / (1 - x ^ 2) := by
      calc
        _ = p * (powerCurvature a x * (a * (x + skew a x)) / (1 - x ^ 2)) := by ring
        _ = q * (powerCurvature b x * (b * (x + skew b x)) / (1 - x ^ 2)) := hd
        _ = _ := by ring
    have hm := congrArg (fun z : ℝ => z * (1 - x ^ 2)) hc
    simpa only [div_mul_cancel₀ _ hden] using hm
  rw [hval] at he
  have hscore := mul_left_cancel₀ (ne_of_gt (mul_pos hq (curvature_pos b x hxc))) he
  have hab : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · exact False.elim ((ne_of_lt (score_strict a b x ha h hx)) hscore)
    · exact h
    · exact False.elim ((ne_of_lt (score_strict b a x hb h hx)) hscore.symm)
  refine ⟨hab, ?_⟩
  rw [hab] at hval
  exact mul_right_cancel₀ (ne_of_gt (curvature_pos b x hxc)) hval

private lemma power_jet (a b p q x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hq : 0 < q) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hval : p * powerCurvature a x = q * powerCurvature b x)
    (hd : deriv (fun t => p * powerCurvature a t) x = deriv (fun t => q * powerCurvature b t) x) :
    a = b ∧ p = q := by
  by_cases hxpos : 0 < x
  · exact power_positive_jet a b p q x ha hb hp hq ⟨hxpos, hx.2⟩ hval hd
  have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
  have hn : -x ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.1]⟩
  have hda := (curvature_hasDerivAt a (-x) hn).const_mul p
  have hdb := (curvature_hasDerivAt b (-x) hn).const_mul q
  have hna : HasDerivAt (fun t => p * powerCurvature a t)
      (-(p * (powerCurvature a (-x) * (a * (-x + skew a (-x))) / (1 - (-x) ^ 2)))) x := by
    have h := hda.comp x ((hasDerivAt_id x).neg)
    convert h using 1 <;> first | rfl | (funext t; simp only [Function.comp_def, id_eq, power_neg]) | ring
  have hnb : HasDerivAt (fun t => q * powerCurvature b t)
      (-(q * (powerCurvature b (-x) * (b * (-x + skew b (-x))) / (1 - (-x) ^ 2)))) x := by
    have h := hdb.comp x ((hasDerivAt_id x).neg)
    convert h using 1 <;> first | rfl | (funext t; simp only [Function.comp_def, id_eq, power_neg]) | ring
  have hvaln : p * powerCurvature a (-x) = q * powerCurvature b (-x) := by simpa only [power_neg] using hval
  have hdn : deriv (fun t => p * powerCurvature a t) (-x) = deriv (fun t => q * powerCurvature b t) (-x) := by
    rw [hda.deriv, hdb.deriv]
    rw [hna.deriv, hnb.deriv] at hd
    linarith
  exact power_positive_jet a b p q (-x) ha hb hp hq ⟨by linarith, hn.2⟩ hvaln hdn

private lemma domain_open (G : GeometryData) : IsOpen (geometryDomain G) := by
  cases hf : G.family with
  | interval beta => simpa only [geometryDomain, hf] using (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
  | realLine => simpa only [geometryDomain, hf] using (isOpen_univ : IsOpen (Set.univ : Set ℝ))

private lemma b_pos (G : GeometryData) (hG : AdmissibleGeometry G) (x : ℝ)
    (hx : x ∈ geometryDomain G) : 0 < G.b x := by
  have hk := kernel_pos G hG (matchedExponent G) x hx
  rcases hG with ⟨_, _, _, _, hG⟩
  cases hf : G.family with
  | interval beta =>
    simp only [hf] at hG
    rw [hG.2.1 x hx]
    simpa only [geometryKernel, matchedExponent, hf] using hk
  | realLine =>
    simp only [hf] at hG
    by_cases hx0 : x = 0
    · subst x
      rw [hG.2.2.1]
      norm_num
    · linarith [hG.2.2.2.1 x hx0]

private lemma fiber_eq (G : GeometryData) (hG : AdmissibleGeometry G)
    (x y : ℝ) (hx : x ∈ geometryDomain G) (hy : y ∈ geometryDomain G)
    (hxy : geometryFeature G x = geometryFeature G y) :
    G.b x = G.b y ∧ ∀ c : ℝ, geometryKernel G c x = geometryKernel G c y := by
  have hbx := b_pos G hG x hx
  have hby := b_pos G hG y hy
  rcases hG with ⟨_, _, _, _, hG⟩
  cases hf : G.family with
  | interval beta =>
    have habs : |x| = |y| := by simpa only [geometryFeature, hf] using hxy
    have hk (c : ℝ) : powerCurvature c x = powerCurvature c y := by
      rw [← power_abs c x, ← power_abs c y, habs]
    simp only [hf] at hG
    exact ⟨by rw [hG.2.1 x hx, hG.2.1 y hy, hk beta],
      fun c => by simpa only [geometryKernel, hf] using hk c⟩
  | realLine =>
    have he : G.b x = G.b y := by
      have hlog : Real.log (G.b x) = Real.log (G.b y) := by
        simpa only [geometryFeature, hf] using hxy
      have he := congrArg Real.exp hlog
      simpa only [Real.exp_log hbx, Real.exp_log hby] using he
    exact ⟨he, fun c => by simp only [geometryKernel, hf, he]⟩

private lemma kernel_diff (G : GeometryData) (hG : AdmissibleGeometry G) (c x : ℝ)
    (hx : x ∈ geometryDomain G) : DifferentiableAt ℝ (geometryKernel G c) x := by
  have hbx := b_pos G hG x hx
  rcases hG with ⟨_, _, _, _, hG⟩
  cases hf : G.family with
  | interval beta =>
    have hxd : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa only [geometryDomain, hf] using hx
    have hp := ((hasDerivAt_id x).const_add 1).rpow_const
      (Or.inl (ne_of_gt (by linarith [hxd.1]) : 1 + x ≠ 0) : 1 + x ≠ 0 ∨ 1 ≤ -c)
    have hm := ((hasDerivAt_id x).const_sub 1).rpow_const
      (Or.inl (ne_of_gt (by linarith [hxd.2]) : 1 - x ≠ 0) : 1 - x ≠ 0 ∨ 1 ≤ -c)
    have heq : geometryKernel G c = fun t => ((1 + t) ^ (-c) + (1 - t) ^ (-c)) / 2 := by
      funext t
      simp only [geometryKernel, hf, powerCurvature, Real.rpow_eq_pow]
    rw [heq]
    exact ((hp.add hm).div_const 2).differentiableAt
  | realLine =>
    simp only [hf] at hG
    have hb := (hG.2.1.differentiable (by norm_num) x).hasDerivAt
    have heq : geometryKernel G c = fun t => (G.b t) ^ c := by
      funext t
      simp only [geometryKernel, hf, Real.rpow_eq_pow]
    rw [heq]
    exact (hb.rpow_const (Or.inl hbx.ne' : G.b x ≠ 0 ∨ 1 ≤ c)).differentiableAt

private lemma b_diff (G : GeometryData) (hG : AdmissibleGeometry G) (x : ℝ)
    (hx : x ∈ geometryDomain G) : DifferentiableAt ℝ G.b x := by
  have hk := kernel_diff G hG (matchedExponent G) x hx
  rcases hG with ⟨_, _, _, _, hG⟩
  cases hf : G.family with
  | interval beta =>
    simp only [hf] at hG
    apply hk.congr_of_eventuallyEq
    filter_upwards [(domain_open G).mem_nhds hx] with t ht
    simpa only [geometryKernel, matchedExponent, hf] using hG.2.1 t ht
  | realLine =>
    simp only [hf] at hG
    exact hG.2.1.differentiable (by norm_num) x

private lemma real_jet (f : ℝ → ℝ) (a b p q x : ℝ) (hfx : 0 < f x)
    (hf : DifferentiableAt ℝ f x) (hfd : deriv f x ≠ 0) (hq : 0 < q)
    (hval : p * Real.rpow (f x) a = q * Real.rpow (f x) b)
    (hd : deriv (fun t => p * Real.rpow (f t) a) x = deriv (fun t => q * Real.rpow (f t) b) x) :
    a = b ∧ p = q := by
  have hda := (hf.hasDerivAt.rpow_const (Or.inl hfx.ne' : f x ≠ 0 ∨ 1 ≤ a)).const_mul p
  have hdb := (hf.hasDerivAt.rpow_const (Or.inl hfx.ne' : f x ≠ 0 ∨ 1 ≤ b)).const_mul q
  simp only [Real.rpow_eq_pow] at hval hd
  rw [hda.deriv, hdb.deriv] at hd
  rw [Real.rpow_sub_one hfx.ne', Real.rpow_sub_one hfx.ne'] at hd
  field_simp at hd
  have he : (p * (f x) ^ a) * a = (q * (f x) ^ b) * b := by
    convert hd using 1 <;> ring
  rw [hval] at he
  have hv : q * (f x) ^ b ≠ 0 := ne_of_gt (mul_pos hq (Real.rpow_pos_of_pos hfx b))
  have hab := mul_left_cancel₀ hv he
  refine ⟨hab, ?_⟩
  rw [hab] at hval
  exact mul_right_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hfx b)) hval

private lemma kernel_jet (G : GeometryData) (hG : AdmissibleGeometry G)
    (z w : ℝ × ℝ) (hz : FeasiblePair z) (hw : FeasiblePair w)
    (x : ℝ) (hx : x ∈ geometryDomain G) (hfeature : 0 < geometryFeature G x)
    (hval : w.2 * geometryKernel G w.1 x = z.2 * geometryKernel G z.1 x)
    (hd : deriv (fun t => w.2 * geometryKernel G w.1 t) x =
      deriv (fun t => z.2 * geometryKernel G z.1 t) x) : w = z := by
  have hbx := b_pos G hG x hx
  have hbd := b_diff G hG x hx
  rcases hG with ⟨_, _, _, _, hG⟩
  cases hf : G.family with
  | interval beta =>
    have hxd : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa only [geometryDomain, hf] using hx
    have hx0 : x ≠ 0 := by
      intro he
      simp only [geometryFeature, hf, he, abs_zero, lt_self_iff_false] at hfeature
    simp only [geometryKernel, hf] at hval hd
    obtain ⟨hc, hp⟩ := power_jet w.1 z.1 w.2 z.2 x hw.1 hz.1 hw.2 hz.2 hxd hx0 hval hd
    exact Prod.ext hc hp
  | realLine =>
    simp only [hf] at hG
    have hx0 : x ≠ 0 := by
      intro he
      simp only [geometryFeature, hf, he, hG.2.2.1, Real.log_one, lt_self_iff_false] at hfeature
    have hbd0 : deriv G.b x ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hn | hp
      · exact ne_of_lt (hG.2.2.2.2.1 x hn)
      · exact ne_of_gt (hG.2.2.2.2.2.1 x hp)
    simp only [geometryKernel, hf] at hval hd
    obtain ⟨hc, hp⟩ := real_jet G.b w.1 z.1 w.2 z.2 x hbx hbd hbd0 hz.2 hval hd
    exact Prod.ext hc hp

private lemma competitor_eq_same (G : GeometryData) (hG : AdmissibleGeometry G)
    (z w : ℝ × ℝ) (hz : FeasiblePair z) (hw : FeasiblePair w)
    (r : ℝ) (hr : 0 < r) (henv : UniformGeometryEnvelope G z r)
    (hc : SameFeatureContacts G z r)
    (hwr : geometryRho G w.1 w.2 ≤ ENNReal.ofReal r) : w = z := by
  rcases hc with ⟨x, hx, y, hy, hxyne, hfeature, hfeature0, hex, hey⟩
  have hfiber := fiber_eq G hG x y hx hy hfeature
  have hB (t : ℝ) (ht : t ∈ geometryDomain G) : 0 < G.lambda * G.b t :=
    mul_pos hG.1 (b_pos G hG t ht)
  have hvz (t : ℝ) (ht : t ∈ geometryDomain G) : 0 < z.2 * geometryKernel G z.1 t :=
    mul_pos hz.2 (kernel_pos G hG _ _ ht)
  have hvw (t : ℝ) (ht : t ∈ geometryDomain G) : 0 < w.2 * geometryKernel G w.1 t :=
    mul_pos hw.2 (kernel_pos G hG _ _ ht)
  have hbelow : w.2 * geometryKernel G w.1 x ≤ z.2 * geometryKernel G z.1 x := by
    apply (error_le_iff _ _ _ _ (hG.2.1 x hx) (hB x hx) (hvw x hx) (hvz x hx)).mp
    change geometryError G w.1 w.2 x ≤ geometryError G z.1 z.2 x
    rw [hex]
    exact (abs_le.mp (error_bound G w r hr.le hwr x hx)).2
  have habove : z.2 * geometryKernel G z.1 y ≤ w.2 * geometryKernel G w.1 y := by
    apply (error_le_iff _ _ _ _ (hG.2.1 y hy) (hB y hy) (hvz y hy) (hvw y hy)).mp
    change geometryError G z.1 z.2 y ≤ geometryError G w.1 w.2 y
    rw [hey]
    exact (abs_le.mp (error_bound G w r hr.le hwr y hy)).1
  have hval : w.2 * geometryKernel G w.1 x = z.2 * geometryKernel G z.1 x := by
    rw [← hfiber.2 z.1, ← hfiber.2 w.1] at habove
    exact le_antisymm hbelow habove
  have hA : DifferentiableAt ℝ G.A x := by
    have hgf := hG.2.2.2.2
    cases hf : G.family with
    | interval beta =>
      simp only [hf] at hgf
      rcases hgf.2.2.2 with heven | hsmooth
      · exfalso
        have habs : |x| = |y| := by simpa only [geometryFeature, hf] using hfeature
        have haeq : G.A x = G.A y := by
          rcases abs_eq_abs.mp habs with he | he
          · exact False.elim (hxyne he)
          · rw [he]
            exact heven y hy
        have heq : geometryError G z.1 z.2 x = geometryError G z.1 z.2 y := by
          unfold geometryError
          rw [hfiber.2 z.1, haeq, hfiber.1]
        rw [hex, hey] at heq
        linarith
      · exact (hsmooth.differentiableOn (by norm_num)).differentiableAt ((domain_open G).mem_nhds hx)
    | realLine =>
      simp only [hf] at hgf
      exact hgf.1.differentiable (by norm_num) x
  have hBd : DifferentiableAt ℝ (fun t => G.lambda * G.b t) x := (b_diff G hG x hx).const_mul _
  have hZd : DifferentiableAt ℝ (fun t => z.2 * geometryKernel G z.1 t) x :=
    (kernel_diff G hG z.1 x hx).const_mul _
  have hWd : DifferentiableAt ℝ (fun t => w.2 * geometryKernel G w.1 t) x :=
    (kernel_diff G hG w.1 x hx).const_mul _
  have hwx : geometryError G w.1 w.2 x = r := by
    unfold geometryError at hex ⊢
    rwa [hval]
  have hzmax : IsLocalMax (fun t =>
      (z.2 * geometryKernel G z.1 t - G.A t) / (z.2 * geometryKernel G z.1 t + G.lambda * G.b t)) x := by
    change ∀ᶠ t in nhds x, geometryError G z.1 z.2 t ≤ geometryError G z.1 z.2 x
    filter_upwards [(domain_open G).mem_nhds hx] with t ht
    rw [hex]
    exact (abs_le.mp (henv t ht)).2
  have hwmax : IsLocalMax (fun t =>
      (w.2 * geometryKernel G w.1 t - G.A t) / (w.2 * geometryKernel G w.1 t + G.lambda * G.b t)) x := by
    change ∀ᶠ t in nhds x, geometryError G w.1 w.2 t ≤ geometryError G w.1 w.2 x
    filter_upwards [(domain_open G).mem_nhds hx] with t ht
    rw [hwx]
    exact (abs_le.mp (error_bound G w r hr.le hwr t ht)).2
  have hden : 0 < z.2 * geometryKernel G z.1 x + G.lambda * G.b x := add_pos (hvz x hx) (hB x hx)
  have htan := PGDRevision20261113.tangency_derivative_identity G.A
    (fun t => G.lambda * G.b t) (fun t => z.2 * geometryKernel G z.1 t)
    (fun t => w.2 * geometryKernel G w.1 t) x hA hBd hZd hWd hden.ne' hval
  rw [hwmax.deriv_eq_zero, hzmax.deriv_eq_zero] at htan
  have hfac : 0 < (G.A x + G.lambda * G.b x) /
      (z.2 * geometryKernel G z.1 x + G.lambda * G.b x) ^ 2 :=
    div_pos (add_pos_of_nonneg_of_pos (hG.2.1 x hx) (hB x hx)) (sq_pos_of_pos hden)
  have hd : deriv (fun t => w.2 * geometryKernel G w.1 t) x =
      deriv (fun t => z.2 * geometryKernel G z.1 t) x := by
    have he : (G.A x + G.lambda * G.b x) / (z.2 * geometryKernel G z.1 x + G.lambda * G.b x) ^ 2 *
        (deriv (fun t => w.2 * geometryKernel G w.1 t) x - deriv (fun t => z.2 * geometryKernel G z.1 t) x) = 0 := by
      linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hfac.ne')
  exact kernel_jet G hG z w hz hw x hx hfeature0 hval hd

theorem solution : SameFeatureTangencyClaim := by
  intro G hG z r hz hr henv hc
  have hrho : geometryRho G z.1 z.2 = ENNReal.ofReal r := by
    apply le_antisymm
    · exact iSup_le fun t => iSup_le fun ht => ENNReal.ofReal_le_ofReal (henv t ht)
    · obtain ⟨x, hx, y, hy, hxy, hf, hf0, hex, hey⟩ := hc
      have habs : |geometryError G z.1 z.2 x| = r := by rw [hex, abs_of_pos hr]
      rw [← habs]
      exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have heq (w : ℝ × ℝ) (hw : FeasiblePair w)
      (hwr : geometryRho G w.1 w.2 ≤ geometryRho G z.1 z.2) : w = z :=
    competitor_eq_same G hG z w hz hw r hr henv hc (hwr.trans_eq hrho)
  have hopt : GeometryOptimum G z := by
    refine ⟨hz, ?_⟩
    intro w hw
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hwz := heq w hw hlt.le
    subst w
    exact (lt_irrefl _) hlt
  refine ⟨hopt, hrho, ?_⟩
  intro w hw
  exact heq w hw.1 (hw.2 z hz)

