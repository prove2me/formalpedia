-- Prove2me | solution 1 for ZhengQR.CostBounds.cost_integral_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:00:14.325431+00:00
-- url     : https://prove2.me/submissions/cf9a19d2-08d6-4b89-a79f-0bfd94589ddb

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

open MeasureTheory Filter Topology

section aux_cif_generic

variable {G : ℝ → ℝ} {L y0 : ℝ}

lemma aux_cif_cont (hL0 : 0 ≤ L) (hL : ∀ x y, |G x - G y| ≤ L * |x - y|) : Continuous G := by
  have : LipschitzWith (Real.toNNReal L) G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.coe_toNNReal _ hL0, Real.dist_eq, Real.dist_eq]
    exact hL x y
  exact this.continuous

/-- the key integral identity -/
lemma aux_cif_ident (hG : Continuous G) (Q r r' : ℝ) :
    (∫ y in r'..r' + Q, G y) - (∫ y in r..r + Q, G y)
      = ∫ s in r..r', (G (s + Q) - G s) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable G volume a b := fun a b => hG.intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun s => G (s + Q)) volume r r' :=
    (hG.comp (continuous_id.add continuous_const)).intervalIntegrable r r'
  rw [intervalIntegral.integral_sub hi2 (hi r r'), intervalIntegral.integral_comp_add_right]
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi r r') (hi r' (r' + Q))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi r (r + Q)) (hi (r + Q) (r' + Q))
  linarith

lemma aux_cif_root (hG : Continuous G) (hmin : ∀ z, G y0 ≤ G z) {Q : ℝ} (hQ : 0 < Q) :
    ∃ r, r ≤ y0 ∧ y0 ≤ r + Q ∧ G r = G (r + Q) := by
  have hc : ContinuousOn (fun r => G (r + Q) - G r) (Set.Icc (y0 - Q) y0) :=
    ((hG.comp (continuous_id.add continuous_const)).sub hG).continuousOn
  have h := intermediate_value_Icc (by linarith : y0 - Q ≤ y0) hc
  have h0 : (0:ℝ) ∈ Set.Icc ((fun r => G (r + Q) - G r) (y0 - Q))
      ((fun r => G (r + Q) - G r) y0) := by
    simp only [Set.mem_Icc, sub_add_cancel]
    constructor
    · have := hmin (y0 - Q); linarith
    · have := hmin (y0 + Q); linarith
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ := h h0
  simp only at hr
  exact ⟨r, hr2, by linarith, by linarith⟩

lemma aux_cif_opt_of_root (hG : Continuous G)
    (hanti : ∀ a b, a ≤ b → b ≤ y0 → G b ≤ G a)
    (hmono : ∀ a b, y0 ≤ a → a ≤ b → G a ≤ G b) {Q r : ℝ} (hQ : 0 < Q)
    (hr1 : r ≤ y0) (hr2 : y0 ≤ r + Q) (hr : G r = G (r + Q)) (r' : ℝ) :
    (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  have e := aux_cif_ident hG Q r r'
  rcases le_total r r' with h | h
  · have : 0 ≤ ∫ s in r..r', (G (s + Q) - G s) := by
      apply intervalIntegral.integral_nonneg h
      intro s hs
      have hs1 := hs.1
      rcases le_total y0 s with h' | h'
      · have := hmono s (s + Q) h' (by linarith); linarith
      · have h1 : G s ≤ G r := hanti r s hs1 h'
        have h2 : G (r + Q) ≤ G (s + Q) := hmono (r + Q) (s + Q) hr2 (by linarith)
        linarith
    linarith
  · have : 0 ≤ ∫ s in r'..r, (G s - G (s + Q)) := by
      apply intervalIntegral.integral_nonneg h
      intro s hs
      have hs2 := hs.2
      rcases le_total (s + Q) y0 with h' | h'
      · have := hanti s (s + Q) (by linarith) h'; linarith
      · have h1 : G (s + Q) ≤ G (r + Q) := hmono (s + Q) (r + Q) h' (by linarith)
        have h2 : G r ≤ G s := hanti s r hs2 hr1
        linarith
    have e2 : (∫ s in r'..r, (G s - G (s + Q))) = ∫ s in r..r', (G (s + Q) - G s) := by
      rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
      congr 1
      ext s; ring
    linarith

lemma aux_cif_fermat (hG : Continuous G) {Q r : ℝ}
    (hopt : ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y) : G r = G (r + Q) := by
  have hfun : (fun r' => ∫ y in r'..r' + Q, G y)
      = fun r' => (∫ y in (0:ℝ)..r' + Q, G y) - ∫ y in (0:ℝ)..r', G y := by
    funext r'
    rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
  have hd : HasDerivAt (fun r' => ∫ y in r'..r' + Q, G y) (G (r + Q) - G r) r := by
    rw [hfun]
    have h1 : HasDerivAt (fun u => ∫ y in (0:ℝ)..u, G y) (G (r + Q)) (r + Q) :=
      (hG.integral_hasStrictDerivAt 0 (r + Q)).hasDerivAt
    have h2 : HasDerivAt (fun u => ∫ y in (0:ℝ)..u, G y) (G r) r :=
      (hG.integral_hasStrictDerivAt 0 r).hasDerivAt
    exact (h1.comp_add_const r Q).sub h2
  have hmin : IsLocalMin (fun r' => ∫ y in r'..r' + Q, G y) r :=
    Filter.Eventually.of_forall hopt
  have := hmin.hasDerivAt_eq_zero hd
  linarith

end aux_cif_generic

structure aux_cif_Hyp (G : ℝ → ℝ) (L y0 : ℝ) : Prop where
  L0 : 0 ≤ L
  lip : ∀ x y, |G x - G y| ≤ L * |x - y|
  hmin : ∀ z, G y0 ≤ G z
  santi : ∀ a b, a < b → b ≤ y0 → G b < G a
  smono : ∀ a b, y0 ≤ a → a < b → G a < G b

noncomputable def aux_cif_Phi (G : ℝ → ℝ) (lam K q : ℝ) : ℝ :=
  ∫ y in reorderPt G lam K q..reorderPt G lam K q + q, G y

section aux_cif_generic2

variable {G : ℝ → ℝ} {L y0 lam K : ℝ}

lemma aux_cif_Hyp.cont (h : aux_cif_Hyp G L y0) : Continuous G := aux_cif_cont h.L0 h.lip

lemma aux_cif_Hyp.anti (h : aux_cif_Hyp G L y0) : ∀ a b, a ≤ b → b ≤ y0 → G b ≤ G a := by
  intro a b hab hb
  rcases eq_or_lt_of_le hab with e | hlt
  · rw [e]
  · exact (h.santi a b hlt hb).le

lemma aux_cif_Hyp.mono (h : aux_cif_Hyp G L y0) : ∀ a b, y0 ≤ a → a ≤ b → G a ≤ G b := by
  intro a b ha hab
  rcases eq_or_lt_of_le hab with e | hlt
  · rw [e]
  · exact (h.smono a b ha hlt).le

lemma aux_cif_exists (h : aux_cif_Hyp G L y0) {Q : ℝ} (hQ : 0 < Q) :
    ∃ r, IsOptReorder G lam K Q r := by
  obtain ⟨r, h1, h2, h3⟩ := aux_cif_root h.cont h.hmin hQ
  refine ⟨r, fun r' => ?_⟩
  unfold qrCost
  apply div_le_div_of_nonneg_right _ hQ.le
  have := aux_cif_opt_of_root h.cont h.anti h.mono hQ h1 h2 h3 r'
  linarith

lemma aux_cif_Ropt (h : aux_cif_Hyp G L y0) {Q : ℝ} (hQ : 0 < Q) (r' : ℝ) :
    (∫ y in reorderPt G lam K Q..reorderPt G lam K Q + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  have hex := aux_cif_exists (lam := lam) (K := K) h hQ
  have hopt : IsOptReorder G lam K Q (reorderPt G lam K Q) := by
    unfold reorderPt
    rw [dif_pos hex]
    exact hex.choose_spec
  have := hopt r'
  unfold qrCost at this
  rw [div_le_div_iff_of_pos_right hQ] at this
  linarith

lemma aux_cif_Req (h : aux_cif_Hyp G L y0) {Q : ℝ} (hQ : 0 < Q) :
    G (reorderPt G lam K Q) = G (reorderPt G lam K Q + Q) :=
  aux_cif_fermat h.cont (aux_cif_Ropt h hQ)

lemma aux_cif_Rbd (h : aux_cif_Hyp G L y0) {Q : ℝ} (hQ : 0 < Q) :
    reorderPt G lam K Q ≤ y0 ∧ y0 ≤ reorderPt G lam K Q + Q := by
  have e := aux_cif_Req (lam := lam) (K := K) h hQ
  set r := reorderPt G lam K Q
  constructor
  · by_contra hc
    push Not at hc
    have := h.smono r (r + Q) hc.le (by linarith)
    linarith
  · by_contra hc
    push Not at hc
    have := h.santi r (r + Q) (by linarith) hc.le
    linarith

lemma aux_cif_rootmono (h : aux_cif_Hyp G L y0) {q q' r r' : ℝ} (hqq : q < q')
    (e : G r = G (r + q)) (b1 : r ≤ y0) (b2 : y0 ≤ r + q)
    (e' : G r' = G (r' + q')) (b1' : r' ≤ y0) (b2' : y0 ≤ r' + q') :
    r' ≤ r ∧ r + q ≤ r' + q' := by
  have hA : r' ≤ r := by
    by_contra hc
    push Not at hc
    have h1 := h.santi r r' hc b1'
    have h2 := h.smono (r + q) (r' + q') b2 (by linarith)
    linarith
  refine ⟨hA, ?_⟩
  by_contra hc
  push Not at hc
  have h1 := h.smono (r' + q') (r + q) b2' hc
  have h2 := h.anti r' r hA b1
  linarith

lemma aux_cif_Rmono (h : aux_cif_Hyp G L y0) {q q' : ℝ} (hq : 0 < q) (hqq : q < q') :
    reorderPt G lam K q' ≤ reorderPt G lam K q ∧
      reorderPt G lam K q + q ≤ reorderPt G lam K q' + q' := by
  have hq' : 0 < q' := lt_trans hq hqq
  exact aux_cif_rootmono h hqq (aux_cif_Req h hq) (aux_cif_Rbd h hq).1 (aux_cif_Rbd h hq).2
    (aux_cif_Req h hq') (aux_cif_Rbd h hq').1 (aux_cif_Rbd h hq').2

lemma aux_cif_Rlip (h : aux_cif_Hyp G L y0) {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q') :
    |reorderPt G lam K q' - reorderPt G lam K q| ≤ |q' - q| := by
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · obtain ⟨m1, m2⟩ := aux_cif_Rmono (lam := lam) (K := K) h hq hlt
    rw [abs_of_pos (sub_pos.2 hlt), abs_le]
    constructor <;> linarith
  · subst heq
    simp
  · obtain ⟨m1, m2⟩ := aux_cif_Rmono (lam := lam) (K := K) h hq' hgt
    rw [abs_of_neg (sub_neg.2 hgt), abs_le]
    constructor <;> linarith

lemma aux_cif_est (hG : Continuous G) {a b c C : ℝ} (hb : ∀ x ∈ Set.uIoc a b, |G x - c| ≤ C) :
    |(∫ y in a..b, G y) - (b - a) * c| ≤ C * |b - a| := by
  have e : (∫ y in a..b, G y) - (b - a) * c = ∫ y in a..b, (G y - c) := by
    rw [intervalIntegral.integral_sub (hG.intervalIntegrable a b) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun y => G y - c) (C := C)
    (a := a) (b := b) (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx)
  rwa [Real.norm_eq_abs] at this

lemma aux_cif_bound (h : aux_cif_Hyp G L y0) {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q') :
    |aux_cif_Phi G lam K q' - aux_cif_Phi G lam K q - (q' - q) * G (reorderPt G lam K q)|
      ≤ 2 * L * |q' - q| ^ 2 := by
  have hG := h.cont
  have hi : ∀ a b, IntervalIntegrable G volume a b := fun a b => hG.intervalIntegrable a b
  have up1 := aux_cif_Ropt (lam := lam) (K := K) h hq' (reorderPt G lam K q)
  have lo1 := aux_cif_Ropt (lam := lam) (K := K) h hq (reorderPt G lam K q')
  have hc : G (reorderPt G lam K q) = G (reorderPt G lam K q + q) := aux_cif_Req h hq
  have hrr := aux_cif_Rlip (lam := lam) (K := K) h hq hq'
  unfold aux_cif_Phi
  set r := reorderPt G lam K q
  set r' := reorderPt G lam K q'
  set c := G r
  have up2 := intervalIntegral.integral_add_adjacent_intervals (hi r (r + q)) (hi (r + q) (r + q'))
  have lo2 := intervalIntegral.integral_add_adjacent_intervals (hi r' (r' + q))
    (hi (r' + q) (r' + q'))
  have estU := aux_cif_est hG (a := r + q) (b := r + q') (c := c) (C := L * |q' - q|) (by
    intro x hx
    have hx' := Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hx)
    rw [show r + q' - (r + q) = q' - q by ring] at hx'
    rw [hc]
    calc |G x - G (r + q)| ≤ L * |x - (r + q)| := h.lip _ _
      _ ≤ L * |q' - q| := mul_le_mul_of_nonneg_left hx' h.L0)
  have estL := aux_cif_est hG (a := r' + q) (b := r' + q') (c := c) (C := L * (2 * |q' - q|)) (by
    intro x hx
    have hx' := Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hx)
    rw [show r' + q' - (r' + q) = q' - q by ring] at hx'
    rw [hc]
    have htri : |x - (r + q)| ≤ 2 * |q' - q| := by
      calc |x - (r + q)| = |(x - (r' + q)) + (r' - r)| := by ring_nf
        _ ≤ |x - (r' + q)| + |r' - r| := abs_add_le _ _
        _ ≤ 2 * |q' - q| := by linarith
    calc |G x - G (r + q)| ≤ L * |x - (r + q)| := h.lip _ _
      _ ≤ L * (2 * |q' - q|) := mul_le_mul_of_nonneg_left htri h.L0)
  rw [show r + q' - (r + q) = q' - q by ring] at estU
  rw [show r' + q' - (r' + q) = q' - q by ring] at estL
  obtain ⟨u1, u2⟩ := abs_le.mp estU
  obtain ⟨l1, l2⟩ := abs_le.mp estL
  have hL0 := h.L0
  have habs := abs_nonneg (q' - q)
  have hsq : 0 ≤ L * |q' - q| * |q' - q| := by positivity
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

lemma aux_cif_deriv (h : aux_cif_Hyp G L y0) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (aux_cif_Phi G lam K) (G (reorderPt G lam K q)) q := by
  rw [hasDerivAt_iff_isLittleO]
  have hO : (fun q' => aux_cif_Phi G lam K q' - aux_cif_Phi G lam K q
      - (q' - q) • G (reorderPt G lam K q)) =O[𝓝 q] (fun q' => (q' - q) ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (2 * L)
    filter_upwards [lt_mem_nhds hq] with q' hq'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_pow]
    exact aux_cif_bound h hq hq'
  exact hO.trans_isLittleO ((Asymptotics.isLittleO_pow_sub_sub q one_lt_two).congr_left
    (fun x => by rw [Real.norm_eq_abs, sq_abs]))

lemma aux_cif_Phi0 : aux_cif_Phi G lam K 0 = 0 := by
  simp [aux_cif_Phi]

lemma aux_cif_cont0 (h : aux_cif_Hyp G L y0) (Q : ℝ) :
    ContinuousWithinAt (aux_cif_Phi G lam K) (Set.Icc 0 Q) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hB : 0 < |G y0| + L + 1 := by have := h.L0; positivity
  refine ⟨min 1 (ε / (|G y0| + L + 1)), by positivity, ?_⟩
  intro x hx hdx
  rw [aux_cif_Phi0, Real.dist_eq, sub_zero]
  rw [Real.dist_eq, sub_zero] at hdx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0, aux_cif_Phi0, abs_zero]
    exact hε
  · have hb := aux_cif_Rbd (lam := lam) (K := K) h hx0
    have hx1 : x < 1 := by
      have := lt_of_lt_of_le hdx (min_le_left _ _)
      rw [abs_of_pos hx0] at this; exact this
    have hx2 : x < ε / (|G y0| + L + 1) := by
      have := lt_of_lt_of_le hdx (min_le_right _ _)
      rw [abs_of_pos hx0] at this; exact this
    have hx3 : x * (|G y0| + L + 1) < ε := (lt_div_iff₀ hB).mp hx2
    unfold aux_cif_Phi
    set r := reorderPt G lam K x
    have hbound : ∀ y ∈ Set.uIoc r (r + x), ‖G y‖ ≤ |G y0| + L * x := by
      intro y hy
      rw [Set.uIoc_of_le (by linarith)] at hy
      rw [Real.norm_eq_abs]
      have h1 : |y - y0| ≤ x := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      have h2 := h.lip y y0
      have h3 : |G y| ≤ |G y0| + |G y - G y0| := by
        have := abs_add_le (G y0) (G y - G y0)
        rwa [show G y0 + (G y - G y0) = G y by ring] at this
      have h4 : L * |y - y0| ≤ L * x := mul_le_mul_of_nonneg_left h1 h.L0
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, show r + x - r = x by ring, abs_of_pos hx0] at this
    have hL0 := h.L0
    have : (|G y0| + L * x) * x ≤ x * (|G y0| + L + 1) := by
      nlinarith [mul_nonneg (mul_nonneg hL0 hx0.le) (sub_nonneg.2 hx1.le)]
    linarith

lemma aux_cif_Hmono (h : aux_cif_Hyp G L y0) : MonotoneOn (Hfun G lam K) (Set.Ici 0) := by
  intro a ha b hb hab
  have hideal : ∀ z, G (idealPt G) ≤ G z := by
    have hex : ∃ y, ∀ z, G y ≤ G z := ⟨y0, h.hmin⟩
    unfold idealPt
    rw [dif_pos hex]
    exact hex.choose_spec
  unfold Hfun
  by_cases ha0 : 0 < a
  · have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
    rw [if_pos ha0, if_pos hb0]
    rcases eq_or_lt_of_le hab with e | hlt
    · rw [e]
    · have := aux_cif_Rmono (lam := lam) (K := K) h ha0 hlt
      exact h.anti _ _ this.1 (aux_cif_Rbd h ha0).1
  · rw [if_neg ha0]
    split_ifs <;> exact hideal _

lemma aux_cif_main (h : aux_cif_Hyp G L y0) {Q : ℝ} (hQ : 0 < Q) :
    aux_cif_Phi G lam K Q = ∫ y in (0:ℝ)..Q, Hfun G lam K y := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hQ.le
    (f := aux_cif_Phi G lam K) (f' := Hfun G lam K) ?_ ?_ ?_
  · rw [hftc, aux_cif_Phi0, sub_zero]
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with e | hx0
    · rw [← e]
      exact aux_cif_cont0 h Q
    · exact (aux_cif_deriv h hx0).continuousAt.continuousWithinAt
  · intro x hx
    have := aux_cif_deriv (lam := lam) (K := K) h hx.1
    unfold Hfun
    rw [if_pos hx.1]
    exact this
  · apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hQ.le]
    exact (aux_cif_Hmono h).mono Set.Icc_subset_Ici_self

end aux_cif_generic2

section aux_cif_model

lemma aux_cif_integrable (M : QRModel) (y : ℝ) :
    Integrable (fun x => M.h * max (y - x) 0 + M.p * max (x - y) 0) M.μ := by
  have := M.isProb
  have h1 : Integrable (fun x : ℝ => y - x) M.μ := (integrable_const y).sub M.integrable_id
  have h2 : Integrable (fun x : ℝ => x - y) M.μ := M.integrable_id.sub (integrable_const y)
  exact (h1.pos_part.const_mul M.h).add (h2.pos_part.const_mul M.p)

lemma aux_cif_G_eq (M : QRModel) (y : ℝ) :
    M.G y = ∫ x, (M.h * max (y - x) 0 + M.p * max (x - y) 0) ∂M.μ := rfl

lemma aux_cif_lip (M : QRModel) : ∀ x y, |M.G x - M.G y| ≤ (M.h + M.p) * |x - y| := by
  intro y y'
  have := M.isProb
  rw [aux_cif_G_eq, aux_cif_G_eq, ← integral_sub (aux_cif_integrable M y) (aux_cif_integrable M y')]
  have := norm_integral_le_of_norm_le_const (μ := M.μ) (C := (M.h + M.p) * |y - y'|)
    (f := fun x => (M.h * max (y - x) 0 + M.p * max (x - y) 0)
      - (M.h * max (y' - x) 0 + M.p * max (x - y') 0)) ?_
  · simpa [Real.norm_eq_abs, probReal_univ] using this
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    have e1 := abs_max_sub_max_le_abs (y - x) (y' - x) 0
    have e2 := abs_max_sub_max_le_abs (x - y) (x - y') 0
    rw [show y - x - (y' - x) = y - y' by ring] at e1
    rw [show x - y - (x - y') = -(y - y') by ring, abs_neg] at e2
    obtain ⟨a1, a2⟩ := abs_le.mp e1
    obtain ⟨b1, b2⟩ := abs_le.mp e2
    have hh := M.h_pos
    have hp := M.p_pos
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left a1 hh.le, mul_le_mul_of_nonneg_left a2 hh.le,
      mul_le_mul_of_nonneg_left b1 hp.le, mul_le_mul_of_nonneg_left b2 hp.le]

lemma aux_cif_conv (M : QRModel) (a c t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    M.G (t * a + (1 - t) * c) ≤ t * M.G a + (1 - t) * M.G c := by
  rw [aux_cif_G_eq, aux_cif_G_eq, aux_cif_G_eq, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_cif_integrable M a).const_mul t)
      ((aux_cif_integrable M c).const_mul (1 - t))]
  apply integral_mono (aux_cif_integrable M _)
    (((aux_cif_integrable M a).const_mul t).add ((aux_cif_integrable M c).const_mul (1 - t)))
  intro x
  have hh := M.h_pos
  have hp := M.p_pos
  have ht1' : 0 ≤ 1 - t := sub_nonneg.2 ht1
  have e1 : max (t * a + (1 - t) * c - x) 0 ≤ t * max (a - x) 0 + (1 - t) * max (c - x) 0 := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (a - x) 0) ht0,
        mul_le_mul_of_nonneg_left (le_max_left (c - x) 0) ht1']
    · nlinarith [mul_nonneg ht0 (le_max_right (a - x) 0), mul_nonneg ht1' (le_max_right (c - x) 0)]
  have e2 : max (x - (t * a + (1 - t) * c)) 0 ≤ t * max (x - a) 0 + (1 - t) * max (x - c) 0 := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (x - a) 0) ht0,
        mul_le_mul_of_nonneg_left (le_max_left (x - c) 0) ht1']
    · nlinarith [mul_nonneg ht0 (le_max_right (x - a) 0), mul_nonneg ht1' (le_max_right (x - c) 0)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left e1 hh.le, mul_le_mul_of_nonneg_left e2 hp.le]

lemma aux_cif_hyp (M : QRModel) {y0 : ℝ} (hy0 : ∀ z, M.G y0 ≤ M.G z)
    (huniq : ∀ y, (∀ z, M.G y ≤ M.G z) → y = y0) : aux_cif_Hyp M.G (M.h + M.p) y0 := by
  have hne : ∀ a, a ≠ y0 → M.G y0 < M.G a := by
    intro a ha
    by_contra hc
    push Not at hc
    exact ha (huniq a (fun z => le_trans hc (hy0 z)))
  refine ⟨by linarith [M.h_pos, M.p_pos], aux_cif_lip M, hy0, ?_, ?_⟩
  · intro a b hab hb
    have hya := hne a (by linarith)
    rcases eq_or_lt_of_le hb with e | hlt
    · rw [e]; exact hya
    · have hya' : 0 < y0 - a := by linarith
      set t := (y0 - b) / (y0 - a) with ht
      have ht0 : 0 < t := div_pos (by linarith) hya'
      have ht1 : t < 1 := (div_lt_one hya').2 (by linarith)
      have hb' : t * a + (1 - t) * y0 = b := by
        rw [ht]; field_simp; ring
      have := aux_cif_conv M a y0 t ht0.le ht1.le
      rw [hb'] at this
      nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 hya)]
  · intro a b ha hab
    have hyb := hne b (by linarith)
    rcases eq_or_lt_of_le ha with e | hlt
    · rw [← e]; exact hyb
    · have hyb' : 0 < b - y0 := by linarith
      set t := (a - y0) / (b - y0) with ht
      have ht0 : 0 < t := div_pos (by linarith) hyb'
      have ht1 : t < 1 := (div_lt_one hyb').2 (by linarith)
      have ha' : t * b + (1 - t) * y0 = a := by
        rw [ht]; field_simp; ring
      have := aux_cif_conv M b y0 t ht0.le ht1.le
      rw [ha'] at this
      nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 hyb)]

end aux_cif_model

end ZhengQR.CostBounds

open ZhengQR.CostBounds

theorem solution (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in reorderPt M.G M.lam M.K Q..reorderPt M.G M.lam M.K Q + Q, M.G y)
        = ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y ∧
      Cfun M.G M.lam M.K Q = (M.lam * M.K + ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y) / Q := by
  obtain ⟨y0, hy0, huniq⟩ := M.unique_min
  have hH : aux_cif_Hyp M.G (M.h + M.p) y0 := aux_cif_hyp M hy0 huniq
  have main := aux_cif_main (lam := M.lam) (K := M.K) hH hQ
  unfold aux_cif_Phi at main
  refine ⟨main, ?_⟩
  unfold Cfun qrCost
  rw [main]
