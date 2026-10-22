-- Prove2me | solution 1 for ZipkinLostSales.Variability.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:45:01.805018+00:00
-- url     : https://prove2.me/submissions/1763ba7e-7d91-42f4-aea4-033bece6201b

import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
import Definitions.Def_StochasticOrders_Convex_ConvexOrder
open MeasureTheory
open ZipkinLostSales.LNatural

namespace ZipkinLostSales.Variability

/-- increase coordinate 0 by `δ` -/
def zvBump {L : ℕ} (v : Fin L → ℝ) (δ : ℝ) : Fin L → ℝ :=
  fun l => v l + if (l : ℕ) = 0 then δ else 0

/-- the integrand of `gstep` -/
noncomputable def zvH {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (v : Fin L → ℝ) (ζ d : ℝ) : ℝ :=
  qhat hh p (vext v 0 - vext v 1 - d) + γ * F (next v d ζ)

/-- nonnegativity and one-sided Lipschitz bounds in coordinate 0 -/
def zvP {L : ℕ} (p C : ℝ) (F : (Fin L → ℝ) → ℝ) : Prop :=
  (∀ v ∈ V L, 0 ≤ F v) ∧ ∀ v ∈ V L, ∀ δ : ℝ, 0 ≤ δ →
    F v - p * δ ≤ F (zvBump v δ) ∧ F (zvBump v δ) ≤ F v + C * δ

lemma zv_bump_bump {L : ℕ} (v : Fin L → ℝ) (a b : ℝ) :
    zvBump (zvBump v a) b = zvBump v (a + b) := by
  funext l; simp only [zvBump]; split_ifs <;> ring

lemma zv_bump_V {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) {δ : ℝ} (hδ : 0 ≤ δ) :
    zvBump v δ ∈ V L := by
  obtain ⟨hA, hN⟩ := hv
  refine ⟨fun i j hij => ?_, fun l => ?_⟩
  · have hij' : (i : ℕ) ≤ j := hij
    have := hA hij
    simp only [zvBump]
    split_ifs with h1 h2 h2
    all_goals first | linarith | (exfalso; omega)
  · simp only [zvBump]; have := hN l; split_ifs <;> linarith

lemma zv_vext_anti {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) {m n : ℕ} (hmn : m ≤ n) :
    vext v n ≤ vext v m := by
  unfold vext
  by_cases h1 : n < L
  · have h2 : m < L := by omega
    rw [dif_pos h1, dif_pos h2]; exact hv.1 (Fin.mk_le_mk.2 hmn)
  · rw [dif_neg h1]; split_ifs with h2
    · exact hv.2 _
    · exact le_rfl

lemma zv_vext_nonneg {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) (n : ℕ) : 0 ≤ vext v n := by
  unfold vext; split_ifs
  · exact hv.2 _
  · exact le_rfl

lemma zv_vext_bump0 {L : ℕ} (hL : 0 < L) (v : Fin L → ℝ) (δ : ℝ) :
    vext (zvBump v δ) 0 = vext v 0 + δ := by
  simp [vext, hL, zvBump]

lemma zv_vext_bump_ne {L : ℕ} (v : Fin L → ℝ) (δ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    vext (zvBump v δ) n = vext v n := by
  unfold vext zvBump; split_ifs with h <;> simp [hn]

lemma zv_vext_comb {L : ℕ} (v1 v2 : Fin L → ℝ) (a b : ℝ) (n : ℕ) :
    vext (a • v1 + b • v2) n = a * vext v1 n + b * vext v2 n := by
  unfold vext; split_ifs <;> simp

lemma zv_next'_V {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) {ζ x : ℝ} (hζ : ζ ≤ 0)
    (hx : vext v 1 ≤ x) : next' x v ζ ∈ V L := by
  refine ⟨fun i j hij => ?_, fun l => ?_⟩
  · have hij' : (i : ℕ) ≤ j := hij
    simp only [next']
    have e1 := zv_vext_anti hv (show 1 ≤ (j : ℕ) + 1 by omega)
    have e2 := zv_vext_anti hv (show (i : ℕ) + 1 ≤ (j : ℕ) + 1 by omega)
    split_ifs with h1 h2 h2
    all_goals first | linarith | (exfalso; omega)
  · simp only [next']
    have := zv_vext_nonneg hv 1
    have := zv_vext_nonneg hv ((l : ℕ) + 1)
    split_ifs <;> linarith

lemma zv_next_bump {L : ℕ} (v : Fin L → ℝ) (d ζ : ℝ) :
    next v d ζ = zvBump (next' (vext v 1) v ζ) (max (vext v 0 - vext v 1 - d) 0) := by
  funext l; simp only [next, next', zvBump]; split_ifs with h
  · simp only [h, zero_add]; ring
  · ring

lemma zv_next'_add {L : ℕ} (v : Fin L → ℝ) (x t ζ : ℝ) :
    next' (x + t) v ζ = zvBump (next' x v ζ) t := by
  funext l; simp only [next', zvBump]; split_ifs <;> ring

lemma zv_next'_bump_eq {L : ℕ} (v : Fin L → ℝ) (x δ ζ : ℝ) :
    next' x (zvBump v δ) ζ = next' x v ζ := by
  funext l; simp only [next']; split_ifs
  · rfl
  · rw [zv_vext_bump_ne _ _ (by omega)]

lemma zv_next_eq' {L : ℕ} (v : Fin L → ℝ) (d ζ : ℝ) :
    next v d ζ = next' (max (vext v 0 - d) (vext v 1)) v ζ := by
  rw [zv_next_bump]
  have : max (vext v 0 - d) (vext v 1) = vext v 1 + max (vext v 0 - vext v 1 - d) 0 := by
    rcases le_total (vext v 0 - d) (vext v 1) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  rw [this, zv_next'_add]

lemma zv_next_V {L : ℕ} {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) (d : ℝ) :
    next v d ζ ∈ V L := by
  rw [zv_next_bump]; exact zv_bump_V (zv_next'_V hv hζ le_rfl) (le_max_right _ _)

lemma zv_next'_comb {L : ℕ} (v1 v2 : Fin L → ℝ) (a b x1 x2 ζ1 ζ2 : ℝ) :
    next' (a * x1 + b * x2) (a • v1 + b • v2) (a * ζ1 + b * ζ2)
      = a • next' x1 v1 ζ1 + b • next' x2 v2 ζ2 := by
  funext l; simp only [next', Pi.add_apply, Pi.smul_apply, smul_eq_mul, zv_vext_comb]
  split_ifs <;> ring

lemma zv_V_convex {L : ℕ} : Convex ℝ (V L) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i j hij => ?_, fun l => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 hij; have := hy.1 hij
    nlinarith [mul_le_mul_of_nonneg_left (hx.1 hij) ha, mul_le_mul_of_nonneg_left (hy.1 hij) hb]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.2 l; have := hy.2 l
    positivity

/-! qhat -/

lemma zv_max_neg (x : ℝ) : max (-x) 0 = max x 0 - x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma zv_qhat_shift (hh p u δ : ℝ) :
    qhat hh p (u + δ) = qhat hh p u + (hh + p) * (max (u + δ) 0 - max u 0) - p * δ := by
  unfold qhat; rw [zv_max_neg, zv_max_neg]; ring

lemma zv_qhat_nonneg {hh p : ℝ} (hhh : 0 ≤ hh) (hp : 0 ≤ p) (u : ℝ) : 0 ≤ qhat hh p u :=
  add_nonneg (mul_nonneg hhh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

lemma zv_qhat_lip {hh p : ℝ} (hhh : 0 ≤ hh) (hp : 0 ≤ p) (u u' : ℝ) :
    qhat hh p u ≤ qhat hh p u' + (hh + p) * |u - u'| := by
  unfold qhat
  have h1 := abs_max_sub_max_le_abs u u' 0
  have h2 := abs_max_sub_max_le_abs (-u) (-u') 0
  rw [show -u - -u' = -(u - u') by ring, abs_neg] at h2
  have k1 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hhh
  have k2 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hp
  nlinarith

lemma zv_qhat_at (hh p a b d : ℝ) :
    qhat hh p (a - b - d) = hh * (max (a - d) b - b) + p * (max (a - d) b - a + d) := by
  unfold qhat
  rcases le_total (a - d) b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring

/-! integrability -/

lemma zv_lip_int (h : ℝ → ℝ) (K : ℝ) (hl : ∀ s s', h s ≤ h s' + K * |s - s'|)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable id μ) : Integrable h μ := by
  have hlip : LipschitzWith (Real.toNNReal K) h :=
    LipschitzWith.of_le_add_mul' K (fun x y => by rw [Real.dist_eq]; exact hl x y)
  have hb : Integrable (fun d => |h 0| + K * |d|) μ :=
    (integrable_const _).add ((hint.abs).const_mul K)
  refine hb.mono' hlip.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := hl d 0
  have h2 := hl 0 d
  rw [sub_zero] at h1
  rw [zero_sub, abs_neg] at h2
  constructor <;> linarith [neg_abs_le (h 0), le_abs_self (h 0)]

lemma zv_bump_lip {L : ℕ} {p C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F) (hp : 0 ≤ p)
    (hC : 0 ≤ C) {b : Fin L → ℝ} (hb : b ∈ V L) {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') :
    F (zvBump b s) ≤ F (zvBump b s') + (p + C) * |s - s'| := by
  rcases le_total s s' with h | h
  · have e : zvBump b s' = zvBump (zvBump b s) (s' - s) := by
      rw [zv_bump_bump]; congr 1; ring
    have := (hP.2 _ (zv_bump_V hb hs) (s' - s) (by linarith)).1
    rw [← e] at this
    rw [abs_of_nonpos (by linarith)]
    nlinarith [mul_nonneg hC (sub_nonneg.2 h)]
  · have e : zvBump b s = zvBump (zvBump b s') (s - s') := by
      rw [zv_bump_bump]; congr 1; ring
    have := (hP.2 _ (zv_bump_V hb hs') (s - s') (by linarith)).2
    rw [← e] at this
    rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_nonneg hp (sub_nonneg.2 h)]

lemma zv_lip_Fnext {L : ℕ} {p C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F) (hp : 0 ≤ p)
    (hC : 0 ≤ C) {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) (d d' : ℝ) :
    F (next v d ζ) ≤ F (next v d' ζ) + (p + C) * |d - d'| := by
  rw [zv_next_bump, zv_next_bump]
  have hb : next' (vext v 1) v ζ ∈ V L := zv_next'_V hv hζ le_rfl
  have hss : |max (vext v 0 - vext v 1 - d) 0 - max (vext v 0 - vext v 1 - d') 0| ≤ |d - d'| := by
    have := abs_max_sub_max_le_abs (vext v 0 - vext v 1 - d) (vext v 0 - vext v 1 - d') 0
    rwa [show vext v 0 - vext v 1 - d - (vext v 0 - vext v 1 - d') = -(d - d') by ring,
      abs_neg] at this
  have := zv_bump_lip hP hp hC hb (le_max_right (vext v 0 - vext v 1 - d) 0)
    (le_max_right (vext v 0 - vext v 1 - d') 0)
  have := mul_le_mul_of_nonneg_left hss (show 0 ≤ p + C by linarith)
  linarith

lemma zv_lip_q (hh p : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (y : ℝ) (d d' : ℝ) :
    qhat hh p (y - d) ≤ qhat hh p (y - d') + (hh + p) * |d - d'| := by
  have := zv_qhat_lip hhh hp (y - d) (y - d')
  rwa [show y - d - (y - d') = -(d - d') by ring, abs_neg] at this

lemma zv_H_lip {L : ℕ} {hh p γ C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hγ0 : 0 ≤ γ) {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ}
    (hζ : ζ ≤ 0) (d d' : ℝ) :
    zvH hh p γ F v ζ d ≤ zvH hh p γ F v ζ d' + (hh + p + γ * (p + C)) * |d - d'| := by
  unfold zvH
  have hq := zv_lip_q hh p hhh hp (vext v 0 - vext v 1) d d'
  have hF := mul_le_mul_of_nonneg_left (zv_lip_Fnext hP hp hC hv hζ d d') hγ0
  linear_combination hq + hF

lemma zv_int_q (hh p : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (y : ℝ) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (hint : Integrable id μ) : Integrable (fun d => qhat hh p (y - d)) μ :=
  zv_lip_int _ (hh + p) (zv_lip_q hh p hhh hp y) μ hint

lemma zv_int_F {L : ℕ} {p C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F) (hp : 0 ≤ p)
    (hC : 0 ≤ C) {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (hint : Integrable id μ) : Integrable (fun d => F (next v d ζ)) μ :=
  zv_lip_int _ (p + C) (zv_lip_Fnext hP hp hC hv hζ) μ hint

lemma zv_int_H {L : ℕ} {hh p γ C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hγ0 : 0 ≤ γ) {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ}
    (hζ : ζ ≤ 0) (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable id μ) :
    Integrable (zvH hh p γ F v ζ) μ :=
  zv_lip_int _ _ (zv_H_lip hP hhh hp hC hγ0 hv hζ) μ hint

lemma zv_gstep_eq {L : ℕ} {c hh p γ C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F)
    (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hC : 0 ≤ C) {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ}
    (hζ : ζ ≤ 0) (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable id μ) :
    gstep c hh p γ μ F v ζ = -(γ ^ L * c * ζ) + ∫ d, zvH hh p γ F v ζ d ∂μ := by
  unfold gstep qhat0 zvH
  rw [integral_add (zv_int_q hh p hhh hp _ μ hint) ((zv_int_F hP hp hC hv hζ μ hint).const_mul γ),
    integral_const_mul]
  ring

lemma zv_gstep_nonneg {L : ℕ} {c hh p γ : ℝ} (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 ≤ γ) (μ : Measure ℝ) {F : (Fin L → ℝ) → ℝ} (hFnn : ∀ v ∈ V L, 0 ≤ F v)
    {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) : 0 ≤ gstep c hh p γ μ F v ζ := by
  unfold gstep qhat0
  have h0 : 0 ≤ γ ^ L * c := mul_nonneg (pow_nonneg hγ0 L) hc
  have h1 : 0 ≤ -(γ ^ L * c * ζ) := by nlinarith
  have h2 : 0 ≤ ∫ d, qhat hh p (vext v 0 - vext v 1 - d) ∂μ :=
    integral_nonneg fun d => zv_qhat_nonneg hhh hp _
  have h3 : 0 ≤ ∫ d, F (next v d ζ) ∂μ := integral_nonneg fun d => hFnn _ (zv_next_V hv hζ d)
  have := mul_nonneg hγ0 h3
  linarith

lemma zv_const_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hf : Integrable f μ)
    {c : ℝ} (h : ∀ x, c ≤ f x) : c ≤ ∫ x, f x ∂μ := by
  have := integral_mono (integrable_const c) hf h
  simpa using this

lemma zv_le_const {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hf : Integrable f μ)
    {c : ℝ} (h : ∀ x, f x ≤ c) : ∫ x, f x ∂μ ≤ c := by
  have := integral_mono hf (integrable_const c) h
  simpa using this

lemma zv_H_bump {L : ℕ} (hL : 0 < L) {hh p γ C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F)
    (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hC : 0 ≤ C) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {v : Fin L → ℝ} (hv : v ∈ V L) {ζ : ℝ} (hζ : ζ ≤ 0) {δ : ℝ} (hδ : 0 ≤ δ) (d : ℝ) :
    zvH hh p γ F v ζ d - p * δ ≤ zvH hh p γ F (zvBump v δ) ζ d ∧
      zvH hh p γ F (zvBump v δ) ζ d ≤ zvH hh p γ F v ζ d + (hh + C) * δ := by
  unfold zvH
  rw [zv_vext_bump0 hL, zv_vext_bump_ne _ _ one_ne_zero,
    show vext v 0 + δ - vext v 1 - d = (vext v 0 - vext v 1 - d) + δ by ring]
  have e : next (zvBump v δ) d ζ = zvBump (next v d ζ)
      (max ((vext v 0 - vext v 1 - d) + δ) 0 - max (vext v 0 - vext v 1 - d) 0) := by
    rw [zv_next_bump, zv_next_bump, zv_next'_bump_eq, zv_vext_bump0 hL,
      zv_vext_bump_ne _ _ one_ne_zero, zv_bump_bump,
      show vext v 0 + δ - vext v 1 - d = (vext v 0 - vext v 1 - d) + δ by ring]
    congr 1; ring
  rw [e, zv_qhat_shift]
  set u := vext v 0 - vext v 1 - d
  have hN := zv_next_V hv hζ d
  have hδ'0 : 0 ≤ max (u + δ) 0 - max u 0 := sub_nonneg.2 (max_le_max (by linarith) le_rfl)
  have hδ'1 : max (u + δ) 0 - max u 0 ≤ δ := by
    have := abs_max_sub_max_le_abs (u + δ) u 0
    rw [show u + δ - u = δ by ring, abs_of_nonneg hδ] at this
    exact (le_abs_self _).trans this
  set δ' := max (u + δ) 0 - max u 0
  obtain ⟨h1, h2⟩ := hP.2 _ hN δ' hδ'0
  have k1 := mul_le_mul_of_nonneg_left h1 hγ0
  have k2 := mul_le_mul_of_nonneg_left h2 hγ0
  constructor
  · nlinarith [mul_nonneg hhh hδ'0, mul_nonneg (mul_nonneg hp hδ'0) (sub_nonneg.2 hγ1)]
  · nlinarith [mul_le_mul_of_nonneg_left hδ'1 hhh, mul_le_mul_of_nonneg_left hδ'1 hp,
      mul_nonneg (mul_nonneg hC hδ'0) (sub_nonneg.2 hγ1), mul_le_mul_of_nonneg_left hδ'1 hC]

lemma zv_step {L : ℕ} (hL : 0 < L) {c hh p γ : ℝ} (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) {F : (Fin L → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C) (hP : zvP p C F) :
    zvP p (hh + C) (fun v => ⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ F v ζ) := by
  have hnn : ∀ v ∈ V L, ∀ ζ : ℝ, ζ ≤ 0 → 0 ≤ gstep c hh p γ μ F v ζ :=
    fun v hv ζ hζ => zv_gstep_nonneg hc hhh hp hγ0 μ hP.1 hv hζ
  haveI : Nonempty (Set.Iic (0 : ℝ)) := ⟨⟨0, Set.mem_Iic.2 le_rfl⟩⟩
  have bdd : ∀ v ∈ V L, BddBelow (Set.range fun ζ : Set.Iic (0 : ℝ) => gstep c hh p γ μ F v ζ) :=
    fun v hv => ⟨0, by rintro _ ⟨ζ, rfl⟩; exact hnn v hv ζ ζ.2⟩
  refine ⟨fun v hv => le_ciInf fun ζ => hnn v hv ζ ζ.2, fun v hv δ hδ => ?_⟩
  have hv' := zv_bump_V hv hδ
  have key : ∀ ζ : ℝ, ζ ≤ 0 → gstep c hh p γ μ F v ζ - p * δ ≤ gstep c hh p γ μ F (zvBump v δ) ζ ∧
      gstep c hh p γ μ F (zvBump v δ) ζ ≤ gstep c hh p γ μ F v ζ + (hh + C) * δ := by
    intro ζ hζ
    rw [zv_gstep_eq hP hhh hp hC hv hζ μ hint, zv_gstep_eq hP hhh hp hC hv' hζ μ hint]
    have hI := zv_int_H hP hhh hp hC hγ0 hv hζ μ hint
    have hI' := zv_int_H hP hhh hp hC hγ0 hv' hζ μ hint
    have hpt := zv_H_bump hL hP hhh hp hC hγ0 hγ1 hv hζ hδ
    have e : ∫ d, zvH hh p γ F (zvBump v δ) ζ d ∂μ - ∫ d, zvH hh p γ F v ζ d ∂μ
        = ∫ d, (zvH hh p γ F (zvBump v δ) ζ d - zvH hh p γ F v ζ d) ∂μ :=
      (integral_sub hI' hI).symm
    have l1 : -(p * δ) ≤ ∫ d, (zvH hh p γ F (zvBump v δ) ζ d - zvH hh p γ F v ζ d) ∂μ :=
      zv_const_le (hI'.sub hI) (fun d => by simp only [Pi.sub_apply]; linarith [(hpt d).1])
    have l2 : ∫ d, (zvH hh p γ F (zvBump v δ) ζ d - zvH hh p γ F v ζ d) ∂μ ≤ (hh + C) * δ :=
      zv_le_const (hI'.sub hI) (fun d => by simp only [Pi.sub_apply]; linarith [(hpt d).2])
    constructor <;> linarith
  constructor
  · show (⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ F v ζ) - p * δ ≤
      ⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ F (zvBump v δ) ζ
    refine le_ciInf fun ζ => ?_
    have := ciInf_le (bdd v hv) ζ
    linarith [(key ζ ζ.2).1]
  · show (⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ F (zvBump v δ) ζ) ≤
      (⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ F v ζ) + (hh + C) * δ
    have : (⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ F (zvBump v δ) ζ) - (hh + C) * δ ≤
        ⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ F v ζ := le_ciInf fun ζ => by
      have := ciInf_le (bdd _ hv') ζ
      linarith [(key ζ ζ.2).2]
    linarith

lemma zv_lemA {L : ℕ} (hL : 0 < L) {c hh p γ : ℝ} (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) : ∀ k : ℕ, ∃ C, 0 ≤ C ∧ zvP p C (fbar c hh p γ μ k (L := L)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, le_rfl, fun v _ => le_rfl, fun v _ δ hδ => ?_⟩
    show (0 : ℝ) - p * δ ≤ 0 ∧ (0 : ℝ) ≤ 0 + 0 * δ
    constructor
    · nlinarith [mul_nonneg hp hδ]
    · simp
  | succ k ih =>
    obtain ⟨C, hC, hP⟩ := ih
    exact ⟨hh + C, by linarith, zv_step hL hc hhh hp hγ0 hγ1 μ hint hC hP⟩

/-! kappa -/

lemma zv_kappa_eq {L : ℕ} {hh p γ C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F)
    (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {v : Fin L → ℝ} (hv : v ∈ V L)
    {ζ : ℝ} (hζ : ζ ≤ 0) {d : ℝ} (hd : 0 ≤ d) :
    kappa hh p γ F d v ζ = qhat hh p (vext v 0 - vext v 1 - d) + γ * F (next v d ζ) := by
  have h10 : vext v 1 ≤ vext v 0 := zv_vext_anti hv (Nat.zero_le 1)
  have ha : max (vext v 0 - d) (vext v 1) ≤ vext v 0 := max_le (by linarith) h10
  haveI : Nonempty (Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0)) := ⟨⟨_, le_rfl, ha⟩⟩
  have hN := zv_next_V hv hζ d
  have lower : ∀ x : Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0),
      qhat hh p (vext v 0 - vext v 1 - d) + γ * F (next v d ζ) ≤ psi hh p γ F d x v ζ := by
    rintro ⟨x, hx1, hx2⟩
    unfold psi
    have e : next' x v ζ = zvBump (next v d ζ) (x - max (vext v 0 - d) (vext v 1)) := by
      rw [zv_next_eq', ← zv_next'_add]; congr 1; ring
    rw [e, zv_qhat_at]
    have h1 := (hP.2 _ hN _ (sub_nonneg.2 hx1)).1
    have k1 := mul_le_mul_of_nonneg_left h1 hγ0
    have : 0 ≤ x - max (vext v 0 - d) (vext v 1) := sub_nonneg.2 hx1
    nlinarith [mul_nonneg hhh this, mul_nonneg (mul_nonneg hp this) (sub_nonneg.2 hγ1)]
  apply le_antisymm
  · have hb : BddBelow (Set.range fun x : Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0) =>
        psi hh p γ F d x v ζ) := ⟨_, by rintro _ ⟨x, rfl⟩; exact lower x⟩
    refine (ciInf_le hb ⟨_, le_rfl, ha⟩).trans (le_of_eq ?_)
    show psi hh p γ F d (max (vext v 0 - d) (vext v 1)) v ζ = _
    unfold psi
    rw [← zv_next_eq', zv_qhat_at]
  · exact le_ciInf lower

/-! partial infimum of a convex function -/

lemma zv_convexOn_iInf {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (C : E → Set ℝ) (Φ : ℝ → E → ℝ)
    (hne : ∀ w ∈ S, (C w).Nonempty) (hnn : ∀ w ∈ S, ∀ x ∈ C w, 0 ≤ Φ x w)
    (hcomb : ∀ w1 ∈ S, ∀ w2 ∈ S, ∀ x1 ∈ C w1, ∀ x2 ∈ C w2, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → a * x1 + b * x2 ∈ C (a • w1 + b • w2) ∧
        Φ (a * x1 + b * x2) (a • w1 + b • w2) ≤ a * Φ x1 w1 + b * Φ x2 w2) :
    ConvexOn ℝ S (fun w => ⨅ x : C w, Φ x w) := by
  refine ⟨hS, ?_⟩
  intro w1 hw1 w2 hw2 a b ha hb hab
  have hw : a • w1 + b • w2 ∈ S := hS hw1 hw2 ha hb hab
  have bdd : ∀ w ∈ S, BddBelow (Set.range fun x : C w => Φ x w) :=
    fun w hw => ⟨0, by rintro _ ⟨x, rfl⟩; exact hnn w hw x x.2⟩
  simp only [smul_eq_mul]
  apply le_of_forall_pos_lt_add
  intro ε hε
  haveI := (hne w1 hw1).to_subtype
  haveI := (hne w2 hw2).to_subtype
  obtain ⟨x1, hx1⟩ := exists_lt_of_ciInf_lt
    (show ⨅ x : C w1, Φ x w1 < (⨅ x : C w1, Φ x w1) + ε / 2 by linarith)
  obtain ⟨x2, hx2⟩ := exists_lt_of_ciInf_lt
    (show ⨅ x : C w2, Φ x w2 < (⨅ x : C w2, Φ x w2) + ε / 2 by linarith)
  obtain ⟨hmem, hle⟩ := hcomb w1 hw1 w2 hw2 x1 x1.2 x2 x2.2 a b ha hb hab
  have k1 := mul_le_mul_of_nonneg_left hx1.le ha
  have k2 := mul_le_mul_of_nonneg_left hx2.le hb
  calc (⨅ x : C (a • w1 + b • w2), Φ x (a • w1 + b • w2))
      ≤ Φ (a * x1 + b * x2) (a • w1 + b • w2) :=
        ciInf_le (bdd _ hw) (⟨_, hmem⟩ : C (a • w1 + b • w2))
    _ ≤ a * Φ x1 w1 + b * Φ x2 w2 := hle
    _ < a * (⨅ x : C w1, Φ x w1) + b * (⨅ x : C w2, Φ x w2) + ε := by nlinarith

/-! joint convexity of kappa -/

lemma zv_kappa_conv_core {L : ℕ} {hh p γ : ℝ} (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 ≤ γ)
    (F : (Fin L → ℝ) → ℝ) (hFconv : ConvexOn ℝ (V L) F) (hFnn : ∀ v ∈ V L, 0 ≤ F v) :
    ConvexOn ℝ {w : (Fin L → ℝ) × ℝ × ℝ | w.1 ∈ V L ∧ w.2.1 ≤ 0 ∧ 0 ≤ w.2.2}
      (fun w => kappa hh p γ F w.2.2 w.1 w.2.1) := by
  have hS : Convex ℝ {w : (Fin L → ℝ) × ℝ × ℝ | w.1 ∈ V L ∧ w.2.1 ≤ 0 ∧ 0 ≤ w.2.2} := by
    rintro ⟨v1, ζ1, d1⟩ ⟨hv1, hζ1, hd1⟩ ⟨v2, ζ2, d2⟩ ⟨hv2, hζ2, hd2⟩ a b ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have k1 := mul_nonneg ha (neg_nonneg.2 hζ1)
    have k2 := mul_nonneg hb (neg_nonneg.2 hζ2)
    have k3 : 0 ≤ a * d1 + b * d2 := by positivity
    exact ⟨zv_V_convex hv1 hv2 ha hb hab, by nlinarith, k3⟩
  refine zv_convexOn_iInf hS
    (fun w => Set.Icc (max (vext w.1 0 - w.2.2) (vext w.1 1)) (vext w.1 0))
    (fun x w => psi hh p γ F w.2.2 x w.1 w.2.1) ?_ ?_ ?_
  · rintro ⟨v, ζ, d⟩ ⟨hv, hζ, hd⟩
    exact Set.nonempty_Icc.2 (max_le (by simp only; linarith) (zv_vext_anti hv (Nat.zero_le 1)))
  · rintro ⟨v, ζ, d⟩ ⟨hv, hζ, hd⟩ x ⟨hx1, hx2⟩
    simp only at hx1 hx2 ⊢
    unfold psi
    have e1 := le_max_left (vext v 0 - d) (vext v 1)
    have e2 := le_max_right (vext v 0 - d) (vext v 1)
    have := hFnn _ (zv_next'_V hv hζ (e2.trans hx1))
    have := mul_nonneg hhh (show 0 ≤ x - vext v 1 by linarith)
    have := mul_nonneg hp (show 0 ≤ x - vext v 0 + d by linarith)
    have := mul_nonneg hγ0 (hFnn _ (zv_next'_V hv hζ (e2.trans hx1)))
    linarith
  · rintro ⟨v1, ζ1, d1⟩ ⟨hv1, hζ1, hd1⟩ ⟨v2, ζ2, d2⟩ ⟨hv2, hζ2, hd2⟩ x1 ⟨hx11, hx12⟩
      x2 ⟨hx21, hx22⟩ a b ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hx11 hx12 hx21 hx22 ⊢
    rw [zv_vext_comb, zv_vext_comb]
    have a1 := le_max_left (vext v1 0 - d1) (vext v1 1)
    have a2 := le_max_right (vext v1 0 - d1) (vext v1 1)
    have b1 := le_max_left (vext v2 0 - d2) (vext v2 1)
    have b2 := le_max_right (vext v2 0 - d2) (vext v2 1)
    refine ⟨⟨max_le ?_ ?_, ?_⟩, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left (a1.trans hx11) ha,
        mul_le_mul_of_nonneg_left (b1.trans hx21) hb]
    · nlinarith [mul_le_mul_of_nonneg_left (a2.trans hx11) ha,
        mul_le_mul_of_nonneg_left (b2.trans hx21) hb]
    · nlinarith [mul_le_mul_of_nonneg_left hx12 ha, mul_le_mul_of_nonneg_left hx22 hb]
    · have hc := hFconv.2 (zv_next'_V hv1 hζ1 (a2.trans hx11)) (zv_next'_V hv2 hζ2 (b2.trans hx21))
        ha hb hab
      simp only [smul_eq_mul] at hc
      have hc' := mul_le_mul_of_nonneg_left hc hγ0
      unfold psi
      rw [zv_vext_comb, zv_vext_comb, zv_next'_comb]
      linear_combination hc'

lemma zv_ae_nonneg {μ : Measure ℝ} (hμ : μ (Set.Iio 0) = 0) : ∀ᵐ d ∂μ, 0 ≤ d := by
  rw [ae_iff]
  have : {d : ℝ | ¬ 0 ≤ d} = Set.Iio 0 := by ext; simp
  rw [this]; exact hμ

/-- the integrand `zvH` is jointly convex for `d ≥ 0` -/
lemma zv_H_conv {L : ℕ} {hh p γ C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F)
    (hFconv : ConvexOn ℝ (V L) F) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {v1 v2 : Fin L → ℝ} (hv1 : v1 ∈ V L) (hv2 : v2 ∈ V L) {ζ1 ζ2 d1 d2 : ℝ} (hζ1 : ζ1 ≤ 0)
    (hζ2 : ζ2 ≤ 0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    zvH hh p γ F (a • v1 + b • v2) (a * ζ1 + b * ζ2) (a * d1 + b * d2) ≤
      a * zvH hh p γ F v1 ζ1 d1 + b * zvH hh p γ F v2 ζ2 d2 := by
  have hK := (zv_kappa_conv_core hhh hp hγ0 F hFconv hP.1).2
    (show ((v1, ζ1, d1) : (Fin L → ℝ) × ℝ × ℝ) ∈
      {w : (Fin L → ℝ) × ℝ × ℝ | w.1 ∈ V L ∧ w.2.1 ≤ 0 ∧ 0 ≤ w.2.2} from ⟨hv1, hζ1, hd1⟩)
    (show ((v2, ζ2, d2) : (Fin L → ℝ) × ℝ × ℝ) ∈
      {w : (Fin L → ℝ) × ℝ × ℝ | w.1 ∈ V L ∧ w.2.1 ≤ 0 ∧ 0 ≤ w.2.2} from ⟨hv2, hζ2, hd2⟩)
    ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hK
  have hW := zv_V_convex hv1 hv2 ha hb hab
  have hZ : a * ζ1 + b * ζ2 ≤ 0 := by
    nlinarith [mul_nonneg ha (neg_nonneg.2 hζ1), mul_nonneg hb (neg_nonneg.2 hζ2)]
  have hD : 0 ≤ a * d1 + b * d2 := by positivity
  rw [zv_kappa_eq hP hhh hp hγ0 hγ1 hW hZ hD, zv_kappa_eq hP hhh hp hγ0 hγ1 hv1 hζ1 hd1,
    zv_kappa_eq hP hhh hp hγ0 hγ1 hv2 hζ2 hd2] at hK
  exact hK

lemma zv_gstep_conv {L : ℕ} {c hh p γ C : ℝ} {F : (Fin L → ℝ) → ℝ} (hP : zvP p C F)
    (hFconv : ConvexOn ℝ (V L) F) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hC : 0 ≤ C) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (hint : Integrable id μ)
    {v1 v2 : Fin L → ℝ} (hv1 : v1 ∈ V L) (hv2 : v2 ∈ V L) {ζ1 ζ2 : ℝ} (hζ1 : ζ1 ≤ 0)
    (hζ2 : ζ2 ≤ 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    gstep c hh p γ μ F (a • v1 + b • v2) (a * ζ1 + b * ζ2) ≤
      a * gstep c hh p γ μ F v1 ζ1 + b * gstep c hh p γ μ F v2 ζ2 := by
  have hW := zv_V_convex hv1 hv2 ha hb hab
  have hZ : a * ζ1 + b * ζ2 ≤ 0 := by
    nlinarith [mul_nonneg ha (neg_nonneg.2 hζ1), mul_nonneg hb (neg_nonneg.2 hζ2)]
  rw [zv_gstep_eq hP hhh hp hC hW hZ μ hint, zv_gstep_eq hP hhh hp hC hv1 hζ1 μ hint,
    zv_gstep_eq hP hhh hp hC hv2 hζ2 μ hint]
  have hIW := zv_int_H hP hhh hp hC hγ0 hW hZ μ hint
  have hI1 := zv_int_H hP hhh hp hC hγ0 hv1 hζ1 μ hint
  have hI2 := zv_int_H hP hhh hp hC hγ0 hv2 hζ2 μ hint
  have hpt : ∀ᵐ d ∂μ, zvH hh p γ F (a • v1 + b • v2) (a * ζ1 + b * ζ2) d ≤
      a * zvH hh p γ F v1 ζ1 d + b * zvH hh p γ F v2 ζ2 d := by
    filter_upwards [zv_ae_nonneg hμ] with d hd
    have := zv_H_conv hP hFconv hhh hp hγ0 hγ1 hv1 hv2 hζ1 hζ2 hd hd ha hb hab
    rwa [show a * d + b * d = d by rw [← add_mul, hab, one_mul]] at this
  have hm := integral_mono_ae hIW ((hI1.const_mul a).add (hI2.const_mul b)) hpt
  simp only [Pi.add_apply] at hm
  rw [integral_add (hI1.const_mul a) (hI2.const_mul b), integral_const_mul,
    integral_const_mul] at hm
  linear_combination hm

lemma zv_fbar_conv {L : ℕ} (hL : 0 < L) {c hh p γ : ℝ} (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hint : Integrable id μ) :
    ∀ k : ℕ, ConvexOn ℝ (V L) (fbar c hh p γ μ k) := by
  intro k
  induction k with
  | zero => exact convexOn_const (0 : ℝ) zv_V_convex
  | succ k ih =>
    obtain ⟨C, hC, hP⟩ := zv_lemA hL hc hhh hp hγ0 hγ1 μ hint k
    show ConvexOn ℝ (V L) (fun v => ⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ (fbar c hh p γ μ k) v ζ)
    refine zv_convexOn_iInf zv_V_convex (fun _ => Set.Iic (0 : ℝ))
      (fun ζ v => gstep c hh p γ μ (fbar c hh p γ μ k) v ζ) (fun _ _ => ⟨0, Set.mem_Iic.2 le_rfl⟩)
      (fun v hv ζ hζ => zv_gstep_nonneg hc hhh hp hγ0 μ hP.1 hv hζ) ?_
    intro v1 hv1 v2 hv2 ζ1 hζ1 ζ2 hζ2 a b ha hb hab
    have hζ1' : ζ1 ≤ 0 := hζ1
    have hζ2' : ζ2 ≤ 0 := hζ2
    refine ⟨?_, zv_gstep_conv hP ih hhh hp hC hγ0 hγ1 μ hμ hint hv1 hv2 hζ1' hζ2' ha hb hab⟩
    show a * ζ1 + b * ζ2 ≤ 0
    nlinarith [mul_nonneg ha (neg_nonneg.2 hζ1'), mul_nonneg hb (neg_nonneg.2 hζ2')]

/-! convex extension and convex order -/

lemma zv_ext_mixed (h : ℝ → ℝ) (M : ℝ) (hconv : ConvexOn ℝ (Set.Ici 0) h)
    (hlow : ∀ z, 0 ≤ z → h 0 - M * z ≤ h z) {x z a b : ℝ} (hx : x < 0) (hz : 0 ≤ z)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (fun d => if 0 ≤ d then h d else h 0 - M * d) (a * x + b * z) ≤
      a * (fun d => if 0 ≤ d then h d else h 0 - M * d) x +
        b * (fun d => if 0 ≤ d then h d else h 0 - M * d) z := by
  simp only [if_neg (not_le.2 hx), if_pos hz]
  have hlz := hlow z hz
  split_ifs with hw
  · -- 0 ≤ a x + b z
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · subst hz0
      have ha0 : a = 0 := by nlinarith
      have hb1 : b = 1 := by linarith
      subst ha0; subst hb1; simp
    · have hwz : a * x + b * z ≤ z := by nlinarith
      have hA : 0 ≤ (z - (a * x + b * z)) / z := div_nonneg (by linarith) hz
      have hB : 0 ≤ (a * x + b * z) / z := div_nonneg hw hz
      have hAB : (z - (a * x + b * z)) / z + (a * x + b * z) / z = 1 := by
        rw [← add_div, sub_add_cancel, div_self hzpos.ne']
      have h3 := hconv.2 (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hz) hA hB hAB
      simp only [smul_eq_mul, mul_zero, zero_add] at h3
      rw [div_mul_cancel₀ _ hzpos.ne'] at h3
      have q1 : z * ((z - (a * x + b * z)) / z) = z - (a * x + b * z) := by field_simp
      have q2 : z * ((a * x + b * z) / z) = a * x + b * z := by field_simp
      have h3' : z * h (a * x + b * z) ≤
          (z - (a * x + b * z)) * h 0 + (a * x + b * z) * h z := by
        have := mul_le_mul_of_nonneg_left h3 hz
        calc _ ≤ _ := this
          _ = (z * ((z - (a * x + b * z)) / z)) * h 0 + (z * ((a * x + b * z) / z)) * h z := by
            ring
          _ = _ := by rw [q1, q2]
      have P := mul_nonneg (mul_nonneg ha (neg_nonneg.2 hx.le))
        (show 0 ≤ h z - h 0 + M * z by linarith)
      have key : z * h (a * x + b * z) ≤ z * (a * (h 0 - M * x) + b * h z) := by
        linear_combination h3' + P - (h 0 * z) * hab
      exact le_of_mul_le_mul_left key hzpos
  · linear_combination (mul_le_mul_of_nonneg_left hlz hb) - h 0 * hab

lemma zv_cx_ext (h : ℝ → ℝ) (M : ℝ) (hconv : ConvexOn ℝ (Set.Ici 0) h)
    (hlow : ∀ z, 0 ≤ z → h 0 - M * z ≤ h z) :
    ConvexOn ℝ Set.univ (fun d => if 0 ≤ d then h d else h 0 - M * d) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  simp only [smul_eq_mul]
  by_cases hx : 0 ≤ x <;> by_cases hz : 0 ≤ z
  · have hw : 0 ≤ a * x + b * z := by positivity
    simp only [if_pos hx, if_pos hz, if_pos hw]
    have := hconv.2 (show x ∈ Set.Ici (0:ℝ) from hx) (show z ∈ Set.Ici (0:ℝ) from hz) ha hb hab
    simpa only [smul_eq_mul] using this
  · have := zv_ext_mixed h M hconv hlow (not_le.1 hz) hx hb ha (by linarith)
    rw [add_comm (b * z), add_comm (b * _)] at this
    exact this
  · exact zv_ext_mixed h M hconv hlow (not_le.1 hx) hz ha hb hab
  · have hw : ¬ 0 ≤ a * x + b * z := by
      push_neg at hx hz
      rcases eq_or_lt_of_le ha with ha0 | hapos
      · subst ha0; nlinarith
      · nlinarith [mul_pos hapos (neg_pos.2 hx), mul_nonneg hb (neg_nonneg.2 hz.le)]
    simp only [if_neg hx, if_neg hz, if_neg hw]
    linear_combination (-(h 0)) * hab

lemma zv_cx_apply (μ1 μ2 : Measure ℝ) [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ2]
    (h1 : μ1 (Set.Iio 0) = 0) (h2 : μ2 (Set.Iio 0) = 0)
    (hcx : StochasticOrders.Convex.ConvexOrder μ1 μ2 id id) (h : ℝ → ℝ) (M : ℝ)
    (hconv : ConvexOn ℝ (Set.Ici 0) h) (hlow : ∀ z, 0 ≤ z → h 0 - M * z ≤ h z)
    (hi1 : Integrable h μ1) (hi2 : Integrable h μ2) : ∫ d, h d ∂μ1 ≤ ∫ d, h d ∂μ2 := by
  have e1 : (fun d => if 0 ≤ d then h d else h 0 - M * d) =ᵐ[μ1] h :=
    (zv_ae_nonneg h1).mono (fun d hd => by simp only [if_pos hd])
  have e2 : (fun d => if 0 ≤ d then h d else h 0 - M * d) =ᵐ[μ2] h :=
    (zv_ae_nonneg h2).mono (fun d hd => by simp only [if_pos hd])
  have := hcx _ (zv_cx_ext h M hconv hlow) (hi1.congr e1.symm) (hi2.congr e2.symm)
  rw [← integral_congr_ae e1, ← integral_congr_ae e2]
  exact this

/-! monotonicity in the demand law -/

lemma zv_gbar_mono {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (μ : ℝ → Measure ℝ)
    (hμprob : ∀ φ, IsProbabilityMeasure (μ φ)) (hμnonneg : ∀ φ, μ φ (Set.Iio 0) = 0)
    (hμint : ∀ φ, Integrable id (μ φ))
    (hcx : ∀ φ φ' : ℝ, φ ≤ φ' → StochasticOrders.Convex.ConvexOrder (μ φ) (μ φ') id id) :
    ∀ k : ℕ, (∀ v ∈ V L, Monotone (fun φ : ℝ => fbar c hh p γ (μ φ) k v)) →
      ∀ v ∈ V L, ∀ ζ : ℝ, ζ ≤ 0 → Monotone (fun φ : ℝ => gbar c hh p γ (μ φ) k v ζ) := by
  intro k hk v hv ζ hζ φ φ' hφ
  haveI := hμprob φ
  haveI := hμprob φ'
  obtain ⟨C1, hC1, hP1⟩ := zv_lemA hL hc hhh hp hγ0 hγ1 (μ φ) (hμint φ) k
  obtain ⟨C2, hC2, hP2⟩ := zv_lemA hL hc hhh hp hγ0 hγ1 (μ φ') (hμint φ') k
  have hconv1 := zv_fbar_conv hL hc hhh hp hγ0 hγ1 (μ φ) (hμnonneg φ) (hμint φ) k
  show gstep c hh p γ (μ φ) (fbar c hh p γ (μ φ) k) v ζ ≤
    gstep c hh p γ (μ φ') (fbar c hh p γ (μ φ') k) v ζ
  rw [zv_gstep_eq hP1 hhh hp hC1 hv hζ (μ φ) (hμint φ),
    zv_gstep_eq hP2 hhh hp hC2 hv hζ (μ φ') (hμint φ')]
  have hM : 0 ≤ hh + p + γ * (p + C1) := by positivity
  have hconvH : ConvexOn ℝ (Set.Ici 0) (zvH hh p γ (fbar c hh p γ (μ φ) k) v ζ) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro d1 hd1 d2 hd2 a b ha hb hab
    have := zv_H_conv hP1 hconv1 hhh hp hγ0 hγ1 hv hv hζ hζ hd1 hd2 ha hb hab
    rw [← add_smul, hab, one_smul, ← add_mul, hab, one_mul] at this
    simpa only [smul_eq_mul] using this
  have hlowH : ∀ z, 0 ≤ z → zvH hh p γ (fbar c hh p γ (μ φ) k) v ζ 0 -
      (hh + p + γ * (p + C1)) * z ≤ zvH hh p γ (fbar c hh p γ (μ φ) k) v ζ z := by
    intro z hz
    have := zv_H_lip hP1 hhh hp hC1 hγ0 hv hζ 0 z
    rw [zero_sub, abs_neg, abs_of_nonneg hz] at this
    linarith
  have i1 := zv_int_H hP1 hhh hp hC1 hγ0 hv hζ (μ φ) (hμint φ)
  have i1' := zv_int_H hP1 hhh hp hC1 hγ0 hv hζ (μ φ') (hμint φ')
  have i2' := zv_int_H hP2 hhh hp hC2 hγ0 hv hζ (μ φ') (hμint φ')
  have s1 := zv_cx_apply (μ φ) (μ φ') (hμnonneg φ) (hμnonneg φ') (hcx φ φ' hφ) _ _ hconvH
    hlowH i1 i1'
  have s2 : ∫ d, zvH hh p γ (fbar c hh p γ (μ φ) k) v ζ d ∂(μ φ') ≤
      ∫ d, zvH hh p γ (fbar c hh p γ (μ φ') k) v ζ d ∂(μ φ') := by
    refine integral_mono i1' i2' (fun d => ?_)
    show qhat hh p (vext v 0 - vext v 1 - d) + γ * fbar c hh p γ (μ φ) k (next v d ζ) ≤
      qhat hh p (vext v 0 - vext v 1 - d) + γ * fbar c hh p γ (μ φ') k (next v d ζ)
    have := hk (next v d ζ) (zv_next_V hv hζ d) hφ
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left this hγ0)
  linarith

lemma zv_thm11 {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (μ : ℝ → Measure ℝ)
    (hμprob : ∀ φ, IsProbabilityMeasure (μ φ)) (hμnonneg : ∀ φ, μ φ (Set.Iio 0) = 0)
    (hμint : ∀ φ, Integrable id (μ φ))
    (hcx : ∀ φ φ' : ℝ, φ ≤ φ' → StochasticOrders.Convex.ConvexOrder (μ φ) (μ φ') id id) :
    ∀ k : ℕ, ∀ v ∈ V L, Monotone (fun φ : ℝ => fbar c hh p γ (μ φ) k v) := by
  intro k
  induction k with
  | zero => intro v _ φ φ' _; exact le_rfl
  | succ k ih =>
    intro v hv φ φ' hφ
    have hg := zv_gbar_mono hL c hh p γ hc hhh hp hγ0 hγ1 μ hμprob hμnonneg hμint hcx k ih v hv
    haveI := hμprob φ
    obtain ⟨C, hC, hP⟩ := zv_lemA hL hc hhh hp hγ0 hγ1 (μ φ) (hμint φ) k
    haveI : Nonempty (Set.Iic (0 : ℝ)) := ⟨⟨0, Set.mem_Iic.2 le_rfl⟩⟩
    show (⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ (μ φ) (fbar c hh p γ (μ φ) k) v ζ) ≤
      ⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ (μ φ') (fbar c hh p γ (μ φ') k) v ζ
    exact ciInf_mono ⟨0, by rintro _ ⟨ζ, rfl⟩; exact zv_gstep_nonneg hc hhh hp hγ0 _ hP.1 hv ζ.2⟩
      (fun ζ => hg ζ ζ.2 hφ)

lemma zv_kappa_fbar_core {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) :
    ∀ k : ℕ, ∀ v ∈ V L, ∀ ζ : ℝ, ζ ≤ 0 → ∀ d : ℝ, 0 ≤ d →
      kappa hh p γ (fbar c hh p γ μ k) d v ζ
        = qhat hh p (vext v 0 - vext v 1 - d) + γ * fbar c hh p γ μ k (next v d ζ) := by
  intro k v hv ζ hζ d hd
  obtain ⟨C, hC, hP⟩ := zv_lemA hL hc hhh hp hγ0.le hγ1 μ hμint k
  exact zv_kappa_eq hP hhh hp hγ0.le hγ1 hv hζ hd

end ZipkinLostSales.Variability

open ZipkinLostSales.Variability


theorem solution {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : ℝ → Measure ℝ)
    (hμprob : ∀ φ, IsProbabilityMeasure (μ φ)) (hμnonneg : ∀ φ, μ φ (Set.Iio 0) = 0)
    (hμint : ∀ φ, Integrable id (μ φ))
    (hcx : ∀ φ φ' : ℝ, φ ≤ φ' → StochasticOrders.Convex.ConvexOrder (μ φ) (μ φ') id id) :
    ∀ k : ℕ, ∀ v ∈ ZipkinLostSales.LNatural.V L, Monotone (fun φ : ℝ => ZipkinLostSales.LNatural.fbar c hh p γ (μ φ) k v) := by
  exact zv_thm11 hL c hh p γ hc hhh hp hγ0.le hγ1 μ hμprob hμnonneg hμint hcx
