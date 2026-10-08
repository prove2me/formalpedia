-- Prove2me | solution 1 for ServiceParts.BaseStock.property_a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T11:15:32.099327+00:00
-- url     : https://prove2.me/submissions/8fd83cce-b776-4495-985b-ebc194c771d5

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology


namespace ServiceParts.BaseStock

namespace BSX

variable (M : Model)

lemma g_nonneg {x : ℝ} (hx : x ∈ Ioi (0:ℝ)) : 0 ≤ M.g x := (M.g_pos x hx).le

lemma g_int : IntegrableOn M.g (Ioi 0) := by
  by_contra h
  have := M.g_total
  rw [integral_undef h] at this
  norm_num at this

lemma b_pos : 0 < M.b := by
  have h1 : 0 ≤ (1 - M.α) / M.α * M.c :=
    mul_nonneg (div_nonneg (by linarith [M.α_lt_one]) M.α_pos.le) M.c_nonneg
  linarith [M.b_gt]

/-- expectation operator -/
noncomputable def E (k : ℝ → ℝ) (z : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), k (z - x) * M.g x

noncomputable def mu : ℝ := ∫ x in Ioi (0:ℝ), x * M.g x

def Lip (k : ℝ → ℝ) (K : ℝ) : Prop := ∀ a b, |k a - k b| ≤ K * |a - b|

lemma Lip.continuous {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) : Continuous k := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / (|K| + 1), by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  calc |k y - k x| ≤ K * |y - x| := hk y x
    _ ≤ |K| * |y - x| := mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
    _ ≤ |K| * (ε / (|K| + 1)) := mul_le_mul_of_nonneg_left hy.le (abs_nonneg _)
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg K]

lemma E_integrable {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (z : ℝ) :
    IntegrableOn (fun x => k (z - x) * M.g x) (Ioi 0) := by
  have hg := g_int M
  have hxg := M.g_mean
  have hbound : IntegrableOn (fun x => (|k 0| + K * |z|) * M.g x + K * (x * M.g x)) (Ioi 0) :=
    (hg.const_mul _).add (hxg.const_mul _)
  refine Integrable.mono' hbound ?_ ?_
  · exact ((hk.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      hg.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx' : (0:ℝ) < x := hx
    have hgx := g_nonneg M hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgx]
    have h1 : |k (z - x)| ≤ |k 0| + K * |z| + K * x := by
      have := hk (z - x) 0
      have h2 : |z - x - 0| ≤ |z| + x := by
        rw [sub_zero]; calc |z - x| ≤ |z| + |x| := abs_sub _ _
          _ = |z| + x := by rw [abs_of_pos hx']
      have h3 : |k (z - x)| ≤ |k 0| + |k (z - x) - k 0| := by
        have := abs_sub_abs_le_abs_sub (k (z - x)) (k 0); linarith
      nlinarith
    nlinarith

/-- slope bounds transfer -/
lemma E_slope {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (m Mx : ℝ)
    (hs : ∀ a b, a ≤ b → m * (b - a) ≤ k b - k a ∧ k b - k a ≤ Mx * (b - a))
    (a b : ℝ) (hab : a ≤ b) :
    m * (b - a) ≤ E M k b - E M k a ∧ E M k b - E M k a ≤ Mx * (b - a) := by
  have hg := g_int M
  have hsub : E M k b - E M k a = ∫ x in Ioi (0:ℝ), (k (b - x) - k (a - x)) * M.g x := by
    unfold E
    rw [← integral_sub (E_integrable M hk hK b) (E_integrable M hk hK a)]
    congr 1; ext x; ring
  rw [hsub]
  have hint : IntegrableOn (fun x => (k (b - x) - k (a - x)) * M.g x) (Ioi 0) := by
    have := (E_integrable M hk hK b).sub (E_integrable M hk hK a)
    refine this.congr (Filter.Eventually.of_forall (fun x => ?_)); simp only [Pi.sub_apply]; ring
  constructor
  · have : ∫ x in Ioi (0:ℝ), (m * (b - a)) * M.g x = m * (b - a) := by
      rw [integral_const_mul, M.g_total, mul_one]
    rw [← this]
    refine setIntegral_mono_on (hg.const_mul _) hint measurableSet_Ioi (fun x hx => ?_)
    have := (hs (a - x) (b - x) (by linarith)).1
    have h2 : b - x - (a - x) = b - a := by ring
    rw [h2] at this
    exact mul_le_mul_of_nonneg_right this (g_nonneg M hx)
  · have : ∫ x in Ioi (0:ℝ), (Mx * (b - a)) * M.g x = Mx * (b - a) := by
      rw [integral_const_mul, M.g_total, mul_one]
    rw [← this]
    refine setIntegral_mono_on hint (hg.const_mul _) measurableSet_Ioi (fun x hx => ?_)
    have := (hs (a - x) (b - x) (by linarith)).2
    have h2 : b - x - (a - x) = b - a := by ring
    rw [h2] at this
    exact mul_le_mul_of_nonneg_right this (g_nonneg M hx)

lemma E_convex {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (hc : ConvexOn ℝ univ k) :
    ConvexOn ℝ univ (E M k) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold E
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((E_integrable M hk hK x).const_mul _) ((E_integrable M hk hK y).const_mul _)]
  refine setIntegral_mono_on (E_integrable M hk hK _)
    (((E_integrable M hk hK x).const_mul _).add ((E_integrable M hk hK y).const_mul _))
    measurableSet_Ioi (fun t ht => ?_)
  have h1 : a * x + b * y - t = a • (x - t) + b • (y - t) := by
    simp only [smul_eq_mul]; linear_combination t * hab
  have h2 := hc.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
  rw [← h1] at h2
  simp only [smul_eq_mul] at h2
  have := mul_le_mul_of_nonneg_right h2 (g_nonneg M ht)
  linarith

lemma E_lower {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (A B0 : ℝ)
    (hlow : ∀ w, A * w + B0 ≤ k w) (z : ℝ) :
    A * z + B0 - A * mu M ≤ E M k z := by
  have hg := g_int M
  have hxg := M.g_mean
  have heq : ∫ x in Ioi (0:ℝ), ((A * z + B0) * M.g x - A * (x * M.g x)) =
      A * z + B0 - A * mu M := by
    rw [integral_sub (hg.const_mul _) (hxg.const_mul _), integral_const_mul, integral_const_mul,
      M.g_total, mul_one]
    rfl
  rw [← heq]
  unfold E
  refine setIntegral_mono_on ((hg.const_mul _).sub (hxg.const_mul _)) (E_integrable M hk hK z)
    measurableSet_Ioi (fun x hx => ?_)
  have := mul_le_mul_of_nonneg_right (hlow (z - x)) (g_nonneg M hx)
  nlinarith

lemma E_nonneg {k : ℝ → ℝ} (hk : ∀ w, 0 ≤ k w) (z : ℝ) : 0 ≤ E M k z := by
  unfold E
  exact setIntegral_nonneg measurableSet_Ioi (fun x hx => mul_nonneg (hk _) (g_nonneg M hx))

lemma E_hasDerivAt {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (d : ℝ → ℝ)
    (hd : Measurable d) (z : ℝ)
    (hdiff : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), HasDerivAt k (d (z - x)) (z - x)) :
    HasDerivAt (E M k) (∫ x in Ioi (0:ℝ), d (z - x) * M.g x) z := by
  have hg := g_int M
  have := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun w x => k (w - x) * M.g x) (F' := fun x => d (z - x) * M.g x) (x₀ := z)
    (bound := fun x => K * |M.g x|) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall (fun w =>
      ((hk.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
        hg.aestronglyMeasurable))
    (E_integrable M hk hK z)
    (((hd.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
        hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => by
      refine LipschitzOnWith.of_dist_le_mul (fun w _ w' _ => ?_)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, ← sub_mul, abs_mul, abs_mul,
        abs_of_nonneg hK]
      have := hk (w - x) (w' - x)
      have h2 : w - x - (w' - x) = w - w' := by ring
      rw [h2] at this
      rw [abs_abs]
      have := mul_le_mul_of_nonneg_right this (abs_nonneg (M.g x))
      linarith))
    (hg.norm.const_mul K)
    (hdiff.mono (fun x hx => by
      have h1 : HasDerivAt (fun w => w - x) 1 z := (hasDerivAt_id z).sub_const x
      have h2 := hx.comp z h1
      simpa using h2.mul_const (M.g x)))
  exact this.2

/-! the kernel of L -/
noncomputable def phi (t : ℝ) : ℝ := M.h * max t 0 + M.b * max (-t) 0

lemma phi_lip : Lip (phi M) (M.h + M.b) := by
  intro x y
  unfold phi
  have hh := M.h_pos.le
  have hb := (b_pos M).le
  have e1 : |max x 0 - max y 0| ≤ |x - y| := abs_max_sub_max_le_abs x y 0
  have e2 : |max (-x) 0 - max (-y) 0| ≤ |x - y| := by
    have := abs_max_sub_max_le_abs (-x) (-y) 0
    rwa [show -x - -y = -(x - y) by ring, abs_neg] at this
  calc |M.h * max x 0 + M.b * max (-x) 0 - (M.h * max y 0 + M.b * max (-y) 0)|
      = |M.h * (max x 0 - max y 0) + M.b * (max (-x) 0 - max (-y) 0)| := by ring_nf
    _ ≤ |M.h * (max x 0 - max y 0)| + |M.b * (max (-x) 0 - max (-y) 0)| := abs_add_le _ _
    _ = M.h * |max x 0 - max y 0| + M.b * |max (-x) 0 - max (-y) 0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hh, abs_of_nonneg hb]
    _ ≤ M.h * |x - y| + M.b * |x - y| := by gcongr
    _ = (M.h + M.b) * |x - y| := by ring

lemma phi_convex : ConvexOn ℝ univ (phi M) := by
  have h1 : ConvexOn ℝ univ (fun t : ℝ => max t 0) :=
    (convexOn_id convex_univ).sup (convexOn_const 0 convex_univ)
  have h2 : ConvexOn ℝ univ (fun t : ℝ => max (-t) 0) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    rcases le_total 0 (-x) with hx | hx <;> rcases le_total 0 (-y) with hy | hy <;>
    simp only [max_eq_left, max_eq_right, hx, hy] <;>
    · apply max_le <;> nlinarith
  exact (h1.smul M.h_pos.le).add (h2.smul (b_pos M).le)

lemma phi_slope (a b : ℝ) (hab : a ≤ b) :
    -M.b * (b - a) ≤ phi M b - phi M a ∧ phi M b - phi M a ≤ M.h * (b - a) := by
  unfold phi
  have hh := M.h_pos
  have hb := b_pos M
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb' | hb' <;>
  simp only [max_eq_left, max_eq_right, ha, hb', neg_nonneg, neg_nonpos] <;>
  constructor <;> nlinarith

lemma phi_ge (w : ℝ) : M.h * w + 0 ≤ phi M w := by
  unfold phi
  have hh := M.h_pos
  have hb := b_pos M
  have : 0 ≤ M.b * max (-w) 0 := mul_nonneg hb.le (le_max_right _ _)
  have : M.h * w ≤ M.h * max w 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hh.le
  linarith

lemma phi_nonneg (w : ℝ) : 0 ≤ phi M w := by
  unfold phi
  have := M.h_pos; have := b_pos M
  positivity

lemma phi_hasDerivAt (t : ℝ) (ht : t ≠ 0) : HasDerivAt (phi M) (deriv (phi M) t) t := by
  apply DifferentiableAt.hasDerivAt
  rcases lt_or_gt_of_ne ht with h | h
  · have : (fun s => M.b * (-s)) =ᶠ[𝓝 t] phi M := by
      filter_upwards [Iio_mem_nhds h] with s hs
      have hs' : s < 0 := hs
      unfold phi; rw [max_eq_right hs'.le, max_eq_left (by linarith)]; ring
    exact (by fun_prop : DifferentiableAt ℝ (fun s => M.b * (-s)) t).congr_of_eventuallyEq
      this.symm
  · have : (fun s => M.h * s) =ᶠ[𝓝 t] phi M := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      have hs' : 0 < s := hs
      unfold phi; rw [max_eq_left hs'.le, max_eq_right (by linarith)]; ring
    exact (by fun_prop : DifferentiableAt ℝ (fun s => M.h * s) t).congr_of_eventuallyEq
      this.symm

lemma L_eq (y : ℝ) : M.L y = E M (phi M) y := by
  have hK : 0 ≤ M.h + M.b := by linarith [M.h_pos, b_pos M]
  have hint := E_integrable M (phi_lip M) hK y
  unfold Model.L E
  split_ifs with hy
  · have hU : Ioi (0:ℝ) = Ioc 0 y ∪ Ioi y := (Ioc_union_Ioi_eq_Ioi hy.le).symm
    rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (by rw [hU]; exact subset_union_left))
      (hint.mono_set (by rw [hU]; exact subset_union_right)),
      ← integral_const_mul, ← integral_const_mul]
    congr 1
    · refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      simp only [phi]
      rw [max_eq_left (by linarith [hx.2]), max_eq_right (by linarith [hx.2])]; ring
    · refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      have hx' : y < x := hx
      simp only [phi]
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : 0 < x := hx
    simp only [phi]
    rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring


/-! general analysis lemmas -/

lemma touch {f q : ℝ → ℝ} {D y : ℝ} (hf : ConvexOn ℝ univ f) (hq : HasDerivAt q D y)
    (hle : ∀ᶠ z in 𝓝 y, f z ≤ q z) (heq : f y = q y) : HasDerivAt f D y := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hq ⊢
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_neg.tendsto (0:ℝ)); simp only [neg_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht; simpa using ht
  have hq2 := hq.comp hneg
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hle
  have hmn := hq.min hq2
  have hmx := hq.max hq2
  rw [min_self] at hmn
  rw [max_self] at hmx
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmn hmx ?_ ?_ <;>
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hδ)]
      with t ht htb
    have ht' : t ≠ 0 := ht
    have htb' : |t| < δ := by simpa [Real.dist_eq] using htb
    have hA : f (y + t) ≤ q (y + t) := hball (by rw [Real.dist_eq]; simpa using htb')
    have hB : f (y + -t) ≤ q (y + -t) := hball (by rw [Real.dist_eq]; simpa using htb')
    have hmid : 2 * f y ≤ f (y + t) + f (y + -t) := by
      have := hf.2 (mem_univ (y + t)) (mem_univ (y + -t)) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      simp only [smul_eq_mul] at this
      have e : 1/2 * (y + t) + 1/2 * (y + -t) = y := by ring
      rw [e] at this; linarith
    simp only [Function.comp, smul_eq_mul, inv_neg]
    rcases lt_or_gt_of_ne ht' with h | h
    · have hs : t⁻¹ < 0 := inv_lt_zero.2 h
      first
      | (apply min_le_of_left_le; nlinarith)
      | (apply le_max_of_le_right; nlinarith)
    · have hs : 0 < t⁻¹ := inv_pos.2 h
      first
      | (apply min_le_of_right_le; nlinarith)
      | (apply le_max_of_le_left; nlinarith)

lemma deriv_bounds_of_slope {f : ℝ → ℝ} {d y m Mx : ℝ} (hd : HasDerivAt f d y)
    (hs : ∀ a b, a ≤ b → m * (b - a) ≤ f b - f a ∧ f b - f a ≤ Mx * (b - a)) :
    m ≤ d ∧ d ≤ Mx := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ),
      m ≤ t⁻¹ • (f (y + t) - f y) ∧ t⁻¹ • (f (y + t) - f y) ≤ Mx := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp only [smul_eq_mul, ← div_eq_inv_mul]
    rcases lt_or_gt_of_ne ht' with h | h
    · have := hs (y + t) y (by linarith)
      have e : y - (y + t) = -t := by ring
      rw [e] at this
      constructor
      · rw [le_div_iff_of_neg h]; nlinarith
      · rw [div_le_iff_of_neg h]; nlinarith
    · have := hs y (y + t) (by linarith)
      have e : y + t - y = t := by ring
      rw [e] at this
      constructor
      · rw [le_div_iff₀ h]; nlinarith
      · rw [div_le_iff₀ h]; nlinarith
  exact ⟨ge_of_tendsto hd (hev.mono fun _ h => h.1), le_of_tendsto hd (hev.mono fun _ h => h.2)⟩

lemma lip_of_slope {k : ℝ → ℝ} {m Mx : ℝ} (hm : m ≤ 0) (hM : 0 ≤ Mx)
    (hs : ∀ a b, a ≤ b → m * (b - a) ≤ k b - k a ∧ k b - k a ≤ Mx * (b - a)) :
    Lip k (Mx - m) := by
  intro a b
  rcases le_total a b with h | h
  · have := hs a b h
    rw [abs_sub_comm a b, abs_of_nonneg (by linarith : 0 ≤ b - a), abs_le]
    have : 0 ≤ b - a := by linarith
    constructor <;> nlinarith
  · have := hs b a h
    rw [abs_of_nonneg (by linarith : 0 ≤ a - b), abs_le]
    have : 0 ≤ a - b := by linarith
    constructor <;> nlinarith

/-! L facts -/

lemma hK0 : 0 ≤ M.h + M.b := by linarith [M.h_pos, b_pos M]

lemma L_fun : M.L = E M (phi M) := funext (L_eq M)

lemma L_slope (a b : ℝ) (hab : a ≤ b) :
    -M.b * (b - a) ≤ M.L b - M.L a ∧ M.L b - M.L a ≤ M.h * (b - a) := by
  rw [L_fun]; exact E_slope M (phi_lip M) (hK0 M) _ _ (phi_slope M) a b hab

lemma L_convex' : ConvexOn ℝ univ M.L := by
  rw [L_fun]; exact E_convex M (phi_lip M) (hK0 M) (phi_convex M)

lemma L_nonneg (w : ℝ) : 0 ≤ M.L w := by
  rw [L_fun]; exact E_nonneg M (phi_nonneg M) w

lemma L_lower (w : ℝ) : M.h * w + 0 - M.h * mu M ≤ M.L w := by
  rw [L_fun]; exact E_lower M (phi_lip M) (hK0 M) _ _ (phi_ge M) w

lemma L_hasDerivAt (y : ℝ) :
    HasDerivAt M.L (∫ x in Ioi (0:ℝ), deriv (phi M) (y - x) * M.g x) y := by
  rw [L_fun]
  refine E_hasDerivAt M (phi_lip M) (hK0 M) _ (measurable_deriv _) y ?_
  have : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ y := by
    rw [ae_iff]; simp
  refine ae_restrict_of_ae (this.mono fun x hx => ?_)
  exact phi_hasDerivAt M _ (sub_ne_zero.2 (Ne.symm hx))

lemma L_diff : Differentiable ℝ M.L := fun y => (L_hasDerivAt M y).differentiableAt

/-! the operator -/

noncomputable def Mup : ℝ := M.h / (1 - M.α)

lemma Mup_eq : M.h + M.α * Mup M = Mup M := by
  unfold Mup
  have : 1 - M.α ≠ 0 := by linarith [M.α_lt_one]
  field_simp; ring

lemma h_le_Mup : M.h ≤ Mup M := by
  unfold Mup
  rw [le_div_iff₀ (by linarith [M.α_lt_one])]
  nlinarith [M.h_pos, M.α_pos]

lemma Mup_nonneg : 0 ≤ Mup M := le_trans M.h_pos.le (h_le_Mup M)

def Good (f : ℝ → ℝ) : Prop :=
  (∀ w, M.L w ≤ f w) ∧ ConvexOn ℝ univ f ∧
  (∀ a b, a ≤ b → -(M.c + M.b) * (b - a) ≤ f b - f a ∧ f b - f a ≤ Mup M * (b - a)) ∧
  Differentiable ℝ f

noncomputable def T (f : ℝ → ℝ) (y : ℝ) : ℝ := sInf (M.stageCost f y '' Ici 0)

lemma S_eq (f : ℝ → ℝ) (y u : ℝ) :
    M.stageCost f y u = M.c * u + M.L y + M.α * E M f (y + u) := rfl

section step
variable {M} {f : ℝ → ℝ} (hf : Good M f)
include hf

lemma cb_nonneg : 0 ≤ M.c + M.b := by linarith [M.c_nonneg, b_pos M]

lemma good_lip : Lip f (Mup M - -(M.c + M.b)) :=
  lip_of_slope (by linarith [cb_nonneg hf]) (Mup_nonneg M) hf.2.2.1

lemma good_K : 0 ≤ Mup M - -(M.c + M.b) := by linarith [cb_nonneg hf, Mup_nonneg M]

lemma Ef_slope (a b : ℝ) (hab : a ≤ b) :
    -(M.c + M.b) * (b - a) ≤ E M f b - E M f a ∧ E M f b - E M f a ≤ Mup M * (b - a) :=
  E_slope M (good_lip hf) (good_K hf) _ _ hf.2.2.1 a b hab

lemma Ef_cont : Continuous (E M f) :=
  (lip_of_slope (by linarith [cb_nonneg hf]) (Mup_nonneg M) (Ef_slope hf)).continuous

lemma f_nonneg (w : ℝ) : 0 ≤ f w := le_trans (L_nonneg M w) (hf.1 w)

lemma Ef_nonneg (z : ℝ) : 0 ≤ E M f z := E_nonneg M (f_nonneg hf) z

lemma Ef_hasDerivAt (z : ℝ) :
    HasDerivAt (E M f) (∫ x in Ioi (0:ℝ), deriv f (z - x) * M.g x) z :=
  E_hasDerivAt M (good_lip hf) (good_K hf) _ (measurable_deriv f) z
    (Filter.Eventually.of_forall fun x => (hf.2.2.2 (z - x)).hasDerivAt)

lemma exists_min (y : ℝ) : ∃ u, 0 ≤ u ∧ ∀ u', 0 ≤ u' → M.stageCost f y u ≤ M.stageCost f y u' := by
  have hcont : Continuous (fun u => M.stageCost f y u) := by
    simp only [S_eq]
    exact ((continuous_const.mul continuous_id).add continuous_const).add
      (continuous_const.mul ((Ef_cont hf).comp (continuous_const.add continuous_id)))
  have hlow : ∀ z, M.h * z + -(M.h * mu M) - M.h * mu M ≤ E M f z := by
    intro z
    refine E_lower M (good_lip hf) (good_K hf) _ _ (fun w => ?_) z
    have := L_lower M w; have := hf.1 w; linarith
  set S0 := M.stageCost f y 0
  have hP : 0 < M.α * M.h := mul_pos M.α_pos M.h_pos
  set R := |S0 - M.L y| / (M.α * M.h) + |y| + 2 * |mu M| with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨u0, hu0, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R)).exists_isMinOn
    ⟨0, le_rfl, hR0⟩ hcont.continuousOn
  refine ⟨u0, hu0.1, fun u' hu' => ?_⟩
  by_cases hu'R : u' ≤ R
  · exact hmin ⟨hu', hu'R⟩
  · push_neg at hu'R
    have h0 : M.stageCost f y u0 ≤ S0 := hmin ⟨le_rfl, hR0⟩
    refine le_trans h0 ?_
    have h1 : M.stageCost f y u' ≥ M.L y + M.α * (M.h * (y + u') - 2 * (M.h * mu M)) := by
      rw [S_eq]
      have := hlow (y + u')
      have := mul_le_mul_of_nonneg_left this M.α_pos.le
      have := mul_nonneg M.c_nonneg hu'
      nlinarith
    have h2 : |S0 - M.L y| / (M.α * M.h) ≤ y + u' - 2 * mu M := by
      have := neg_abs_le y; have := neg_abs_le (mu M); have := le_abs_self (mu M)
      rw [hR] at hu'R; linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hP.le
    rw [mul_div_cancel₀ _ hP.ne'] at h3
    have := le_abs_self (S0 - M.L y)
    nlinarith

lemma T_eq {y u : ℝ} (hu : 0 ≤ u) (hmin : ∀ u', 0 ≤ u' → M.stageCost f y u ≤ M.stageCost f y u') :
    T M f y = M.stageCost f y u :=
  IsLeast.csInf_eq ⟨⟨u, hu, rfl⟩, by rintro _ ⟨u', hu', rfl⟩; exact hmin u' hu'⟩

lemma T_le (y u' : ℝ) (hu' : 0 ≤ u') : T M f y ≤ M.stageCost f y u' := by
  obtain ⟨u, hu, hmin⟩ := exists_min hf y
  rw [T_eq hf hu hmin]; exact hmin u' hu'

lemma T_convex : ConvexOn ℝ univ (T M f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨u1, hu1, hmin1⟩ := exists_min hf x
  obtain ⟨u2, hu2, hmin2⟩ := exists_min hf y
  have hle := T_le hf (a • x + b • y) (a * u1 + b * u2) (by positivity)
  rw [T_eq hf hu1 hmin1, T_eq hf hu2 hmin2]
  have hL := (L_convex' M).2 (mem_univ x) (mem_univ y) ha hb hab
  have hE := (E_convex M (good_lip hf) (good_K hf) hf.2.1).2 (mem_univ (x + u1))
    (mem_univ (y + u2)) ha hb hab
  simp only [S_eq, smul_eq_mul] at *
  have e : a * x + b * y + (a * u1 + b * u2) = a * (x + u1) + b * (y + u2) := by ring
  rw [e] at hle
  have := mul_le_mul_of_nonneg_left hE M.α_pos.le
  nlinarith

lemma T_deriv_pos (y u : ℝ) (hu : 0 < u)
    (hmin : ∀ u', 0 ≤ u' → M.stageCost f y u ≤ M.stageCost f y u') :
    HasDerivAt (T M f) (-M.c + deriv M.L y) y := by
  have hq : HasDerivAt (fun y' => M.c * (y + u - y') + M.L y' + M.α * E M f (y + u))
      (-M.c + deriv M.L y) y := by
    have h1 := (((hasDerivAt_id' y).const_sub (y + u)).const_mul M.c).add
      ((L_diff M) y).hasDerivAt
    have h2 := h1.add_const (M.α * E M f (y + u))
    exact h2.congr_deriv (by ring)
  refine touch (T_convex hf) hq ?_ ?_
  · filter_upwards [Iio_mem_nhds (by linarith : y < y + u)] with y' hy'
    have hy'' : y' < y + u := hy'
    have := T_le hf y' (y + u - y') (by linarith)
    rw [S_eq] at this
    have e : y' + (y + u - y') = y + u := by ring
    rw [e] at this; exact this
  · rw [T_eq hf hu.le hmin, S_eq]; simp

lemma T_deriv_zero (y : ℝ)
    (hmin : ∀ u', 0 ≤ u' → M.stageCost f y 0 ≤ M.stageCost f y u') :
    HasDerivAt (T M f)
      (deriv M.L y + M.α * ∫ x in Ioi (0:ℝ), deriv f (y - x) * M.g x) y := by
  have hq : HasDerivAt (fun y' => M.L y' + M.α * E M f y')
      (deriv M.L y + M.α * ∫ x in Ioi (0:ℝ), deriv f (y - x) * M.g x) y :=
    ((L_diff M) y).hasDerivAt.add ((Ef_hasDerivAt hf y).const_mul M.α)
  refine touch (T_convex hf) hq (Filter.Eventually.of_forall fun y' => ?_) ?_
  · have := T_le hf y' 0 le_rfl
    rw [S_eq] at this; simpa using this
  · rw [T_eq hf le_rfl hmin, S_eq]; simp

lemma T_good : Good M (T M f) := by
  refine ⟨fun w => ?_, T_convex hf, fun a b hab => ?_, fun y => ?_⟩
  · obtain ⟨u, hu, hmin⟩ := exists_min hf w
    rw [T_eq hf hu hmin, S_eq]
    have := mul_nonneg M.c_nonneg hu
    have := mul_nonneg M.α_pos.le (Ef_nonneg hf (w + u))
    linarith
  · obtain ⟨ua, hua, hmina⟩ := exists_min hf a
    obtain ⟨ub, hub, hminb⟩ := exists_min hf b
    have hLs := L_slope M a b hab
    constructor
    · have h1 := T_le hf a (ub + (b - a)) (by linarith)
      rw [S_eq] at h1
      have e : a + (ub + (b - a)) = b + ub := by ring
      rw [e] at h1
      rw [T_eq hf hub hminb, S_eq]
      nlinarith [M.c_nonneg]
    · rw [T_eq hf hua hmina]
      by_cases hcase : b - a ≤ ua
      · have h1 := T_le hf b (ua - (b - a)) (by linarith)
        rw [S_eq] at h1
        have e : b + (ua - (b - a)) = a + ua := by ring
        rw [e] at h1
        rw [S_eq]
        have := h_le_Mup M
        nlinarith [M.c_nonneg]
      · push_neg at hcase
        have h1 := T_le hf b 0 le_rfl
        rw [S_eq] at h1
        rw [S_eq]
        have hE := (Ef_slope hf (a + ua) b (by linarith)).2
        simp only [add_zero, mul_zero] at h1
        have hmono := Mup_eq M
        have h3 := mul_le_mul_of_nonneg_left hE M.α_pos.le
        have h4 : 0 ≤ M.α * Mup M * ua := by
          have := Mup_nonneg M; have := M.α_pos; positivity
        have := mul_nonneg M.c_nonneg hua
        nlinarith
  · obtain ⟨u, hu, hmin⟩ := exists_min hf y
    rcases hu.lt_or_eq with h | h
    · exact (T_deriv_pos hf y u h hmin).differentiableAt
    · subst h; exact (T_deriv_zero hf y hmin).differentiableAt

end step

lemma L_good : Good M M.L := by
  refine ⟨fun w => le_rfl, L_convex' M, fun a b hab => ?_, L_diff M⟩
  have := L_slope M a b hab
  have := h_le_Mup M
  have := M.c_nonneg
  constructor <;> nlinarith

lemma f_succ_succ (m : ℕ) : M.f (m + 2) = T M (M.f (m + 1)) := rfl

lemma f_good (n : ℕ) (hn : 1 ≤ n) : Good M (M.f n) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · exact L_good M
    · rw [show k + 1 + 1 = k + 2 by ring, f_succ_succ]
      exact T_good (ih (by omega))

end BSX

theorem f_convex_core (M : Model) (n : ℕ) (hn : 1 ≤ n) : ConvexOn ℝ univ (M.f n) :=
  (BSX.f_good M n hn).2.1

theorem deriv_bounds_core (M : Model) (n : ℕ) (hn : 1 ≤ n) :
    Differentiable ℝ (M.f n) ∧
      ∀ y : ℝ, -(M.c + M.b) ≤ deriv (M.f n) y ∧ deriv (M.f n) y ≤ M.h / (1 - M.α) := by
  have hg := BSX.f_good M n hn
  refine ⟨hg.2.2.2, fun y => ?_⟩
  exact BSX.deriv_bounds_of_slope (hg.2.2.2 y).hasDerivAt hg.2.2.1


theorem property_b_core (M : Model) (n : ℕ) (hn : 2 ≤ n) (s : ℝ)
    (hs : M.IsOrderUpToOptimal n s) (y : ℝ) :
    HasDerivAt (M.f n)
      (if y < s then -M.c + deriv M.L y
       else deriv M.L y + M.α * ∫ x in Ioi (0 : ℝ), deriv (M.f (n - 1)) (y - x) * M.g x) y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hgood := BSX.f_good M (m + 1) (by omega)
  have hopt := hs y
  unfold Model.IsOptimalOrder Model.orderCost at hopt
  simp only [show m + 2 - 1 = m + 1 by omega] at hopt ⊢
  rw [BSX.f_succ_succ]
  split_ifs with h
  · rw [max_eq_right (by linarith)] at hopt
    exact BSX.T_deriv_pos hgood y (s - y) (by linarith) hopt.2
  · rw [max_eq_left (by linarith)] at hopt
    exact BSX.T_deriv_zero hgood y hopt.2

lemma BSX.L_neg (M : Model) (y : ℝ) (hy : y ≤ 0) : M.L y = M.b * (BSX.mu M - y) := by
  unfold Model.L
  rw [if_neg (not_lt.2 hy)]
  congr 1
  have h1 : ∫ x in Ioi (0:ℝ), (x - y) * M.g x = ∫ x in Ioi (0:ℝ), (x * M.g x - y * M.g x) := by
    congr 1; ext x; ring
  rw [h1, integral_sub M.g_mean ((BSX.g_int M).const_mul y), integral_const_mul, M.g_total]
  unfold BSX.mu; ring

lemma BSX.L_deriv_neg (M : Model) (z : ℝ) (hz : z < 0) : deriv M.L z = -M.b := by
  have h1 : HasDerivAt (fun y => M.b * (BSX.mu M - y)) (-M.b) z :=
    (((hasDerivAt_id' z).const_sub (BSX.mu M)).const_mul M.b).congr_deriv (by ring)
  have h2 : (fun y => M.b * (BSX.mu M - y)) =ᶠ[𝓝 z] M.L := by
    filter_upwards [Iio_mem_nhds hz] with y hy
    exact (BSX.L_neg M y (le_of_lt hy)).symm
  exact (h1.congr_of_eventuallyEq h2.symm).deriv

theorem F_tendsto_atBot_core (M : Model) (n : ℕ) (hn : 2 ≤ n) (s : ℝ)
    (hs : M.IsOrderUpToOptimal n s) :
    Tendsto (M.F n) atBot (𝓝 ((1 - M.α) * M.c - M.b * M.α)) ∧
      (1 - M.α) * M.c - M.b * M.α < 0 := by
  have key : ∀ w, w < min s 0 → M.F n w = (1 - M.α) * M.c - M.b * M.α := by
    intro w hw
    have hws : w < s := lt_of_lt_of_le hw (min_le_left _ _)
    have hw0 : w < 0 := lt_of_lt_of_le hw (min_le_right _ _)
    unfold Model.F
    have : ∫ x in Ioi (0:ℝ), deriv (M.f n) (w - x) * M.g x =
        ∫ x in Ioi (0:ℝ), (-(M.c + M.b)) * M.g x := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      have hx' : (0:ℝ) < x := hx
      have hz : w - x < s := by linarith
      rw [(property_b_core M n hn s hs (w - x)).deriv, if_pos hz,
        BSX.L_deriv_neg M (w - x) (by linarith)]
      ring
    rw [this, integral_const_mul, M.g_total]; ring
  refine ⟨tendsto_const_nhds.congr' ?_, ?_⟩
  · exact Filter.eventually_atBot.2 ⟨min s 0 - 1, fun w hw => (key w (by linarith)).symm⟩
  · have h1 := mul_lt_mul_of_pos_right M.b_gt M.α_pos
    have e : (1 - M.α) / M.α * M.c * M.α = (1 - M.α) * M.c := by
      have := M.α_pos.ne'
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self this, mul_one]
    rw [e] at h1; linarith


namespace BSX
variable (M : Model)

lemma E_diff {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (a b : ℝ) :
    E M k b - E M k a = ∫ x in Ioi (0:ℝ), (k (b - x) - k (a - x)) * M.g x := by
  unfold E
  rw [← integral_sub (E_integrable M hk hK b) (E_integrable M hk hK a)]
  congr 1; ext x; ring

noncomputable def gap (k : ℝ → ℝ) (u v : ℝ) : ℝ := (k u + k v) / 2 - k ((u + v) / 2)

lemma gap_nonneg {k : ℝ → ℝ} (hc : ConvexOn ℝ univ k) (u v : ℝ) : 0 ≤ gap k u v := by
  have := hc.2 (mem_univ u) (mem_univ v) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at this
  unfold gap
  rw [show (u + v) / 2 = 1/2 * u + 1/2 * v by ring]
  linarith

lemma gap_int {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (u v : ℝ) :
    IntegrableOn (fun x => gap k (u - x) (v - x) * M.g x) (Ioi 0) := by
  have := (((E_integrable M hk hK u).const_mul (1/2)).add
    ((E_integrable M hk hK v).const_mul (1/2))).sub (E_integrable M hk hK ((u + v) / 2))
  refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Pi.add_apply, Pi.sub_apply, gap]
  rw [show (u - x + (v - x)) / 2 = (u + v) / 2 - x by ring]; ring

lemma E_gap {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (u v : ℝ) :
    gap (E M k) u v = ∫ x in Ioi (0:ℝ), gap k (u - x) (v - x) * M.g x := by
  have e : ∀ x, gap k (u - x) (v - x) * M.g x = ((1/2) * (k (u - x) * M.g x) +
      (1/2) * (k (v - x) * M.g x)) - k ((u + v) / 2 - x) * M.g x := by
    intro x; unfold gap; rw [show (u - x + (v - x)) / 2 = (u + v) / 2 - x by ring]; ring
  simp_rw [e]
  have hA : IntegrableOn (fun x => (1/2) * (k (u - x) * M.g x) + (1/2) * (k (v - x) * M.g x))
      (Ioi 0) := ((E_integrable M hk hK u).const_mul (1/2)).add
    ((E_integrable M hk hK v).const_mul (1/2))
  have hB : IntegrableOn (fun x => k ((u + v) / 2 - x) * M.g x) (Ioi 0) :=
    E_integrable M hk hK ((u + v) / 2)
  have hC : IntegrableOn (fun x => (1/2) * (k (u - x) * M.g x)) (Ioi 0) :=
    (E_integrable M hk hK u).const_mul (1/2)
  have hD : IntegrableOn (fun x => (1/2) * (k (v - x) * M.g x)) (Ioi 0) :=
    (E_integrable M hk hK v).const_mul (1/2)
  rw [integral_sub hA hB, integral_add hC hD, integral_const_mul, integral_const_mul]
  unfold gap E; ring

lemma E_gap_pos {k : ℝ → ℝ} {K : ℝ} (hk : Lip k K) (hK : 0 ≤ K) (hc : ConvexOn ℝ univ k)
    (u v x0 : ℝ) (hx0 : 0 < x0) (hpos : 0 < gap k (u - x0) (v - x0)) :
    0 < gap (E M k) u v := by
  rw [E_gap M hk hK]
  set γ := fun x => gap k (u - x) (v - x) * M.g x with hγ
  have hcont : ContinuousOn γ (Ioi 0) := by
    have hkc := hk.continuous
    refine ContinuousOn.mul (Continuous.continuousOn ?_) M.g_cont
    unfold gap; fun_prop
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (gap_int M hk hK u v)]
  · have hγ0 : 0 < γ x0 := mul_pos hpos (M.g_pos x0 hx0)
    have hca : ContinuousAt γ x0 := hcont.continuousAt (Ioi_mem_nhds hx0)
    have hev : ∀ᶠ y in 𝓝 x0, 0 < γ y ∧ 0 < y :=
      (hca.eventually (Ioi_mem_nhds hγ0)).and (Ioi_mem_nhds hx0)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine lt_of_lt_of_le (Metric.measure_ball_pos volume x0 hε) (measure_mono ?_)
    intro y hy
    have := hball hy
    exact ⟨this.1.ne', this.2⟩
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun x hx => mul_nonneg (gap_nonneg hc _ _) (g_nonneg M hx))

lemma phi_gap_pos (p q : ℝ) (hp : p < 0) (hq : 0 < q) : 0 < gap (phi M) p q := by
  have hh := M.h_pos
  have hb := b_pos M
  unfold gap phi
  rw [max_eq_right hp.le, max_eq_left (by linarith : (0:ℝ) ≤ -p), max_eq_left hq.le,
    max_eq_right (by linarith : -q ≤ 0)]
  rcases le_total 0 ((p + q) / 2) with hr | hr
  · rw [max_eq_left hr, max_eq_right (by linarith : -((p + q) / 2) ≤ 0)]; nlinarith
  · rw [max_eq_right hr, max_eq_left (by linarith : 0 ≤ -((p + q) / 2))]; nlinarith

lemma L_gap_pos (u v : ℝ) (huv : u < v) (hv : 0 < v) : 0 < gap M.L u v := by
  rw [L_fun]
  have h1 : max u 0 < v := max_lt huv hv
  refine E_gap_pos M (phi_lip M) (hK0 M) (phi_convex M) u v ((max u 0 + v) / 2)
    (by have := le_max_right u 0; linarith) (phi_gap_pos M _ _ ?_ ?_)
  · have := le_max_left u 0; linarith
  · linarith

lemma L_lip : Lip M.L (M.h - -M.b) :=
  lip_of_slope (by linarith [b_pos M]) M.h_pos.le (L_slope M)

lemma key_neg : (1 - M.α) * M.c - M.b * M.α < 0 := by
  have h1 := mul_lt_mul_of_pos_right M.b_gt M.α_pos
  have e : (1 - M.α) / M.α * M.c * M.α = (1 - M.α) * M.c := by
    have := M.α_pos.ne'
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self this, mul_one]
  rw [e] at h1; linarith

lemma T_mono {f : ℝ → ℝ} (hf : Good M f) (a b : ℝ) (hab : a ≤ b) :
    M.L b - M.L a - M.c * (b - a) ≤ T M f b - T M f a := by
  obtain ⟨ub, hub, hminb⟩ := exists_min hf b
  have h1 := T_le hf a (ub + (b - a)) (by linarith)
  rw [S_eq] at h1
  have e : a + (ub + (b - a)) = b + ub := by ring
  rw [e] at h1
  rw [T_eq hf hub hminb, S_eq]
  linarith

lemma f_mono (k : ℕ) (hk : 1 ≤ k) (a b : ℝ) (hab : a ≤ b) :
    M.L b - M.L a - M.c * (b - a) ≤ M.f k b - M.f k a := by
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · show M.L b - M.L a - M.c * (b - a) ≤ M.L b - M.L a
    nlinarith [M.c_nonneg]
  · rw [f_succ_succ]; exact T_mono M (f_good M (k + 1) (by omega)) a b hab

lemma opt_min {f : ℝ → ℝ} (s : ℝ)
    (h : ∀ y, ∀ u', 0 ≤ u' → M.stageCost f y (max 0 (s - y)) ≤ M.stageCost f y u') (z : ℝ) :
    M.c * s + M.α * E M f s ≤ M.c * z + M.α * E M f z := by
  rcases le_total z s with hz | hz
  · have := h z 0 le_rfl
    rw [max_eq_right (by linarith), S_eq, S_eq, show z + (s - z) = s by ring, add_zero,
      mul_zero] at this
    linarith
  · have := h s (z - s) (by linarith)
    rw [sub_self, max_self, S_eq, S_eq, show s + (z - s) = z by ring, add_zero,
      mul_zero] at this
    linarith

lemma opt_form {f : ℝ → ℝ} (hf : Good M f) (s : ℝ)
    (h : ∀ y, ∀ u', 0 ≤ u' → M.stageCost f y (max 0 (s - y)) ≤ M.stageCost f y u') (w : ℝ)
    (hw : w ≤ s) : T M f w = M.c * (s - w) + M.L w + M.α * E M f s := by
  rw [T_eq hf (le_max_left _ _) (h w), max_eq_right (by linarith), S_eq,
    show w + (s - w) = s by ring]

end BSX

theorem property_a_core (M : Model) (n : ℕ) (hn : 2 ≤ n) (s s' : ℝ)
    (hs : M.IsOrderUpToOptimal n s) (hs' : M.IsOrderUpToOptimal (n + 1) s') : s ≤ s' := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have g0 := BSX.f_good M (m + 1) (by omega)
  have g1 := BSX.f_good M (m + 2) (by omega)
  have h0 : ∀ y, ∀ u', 0 ≤ u' →
      M.stageCost (M.f (m + 1)) y (max 0 (s - y)) ≤ M.stageCost (M.f (m + 1)) y u' :=
    fun y => (hs y).2
  have h1 : ∀ y, ∀ u', 0 ≤ u' →
      M.stageCost (M.f (m + 2)) y (max 0 (s' - y)) ≤ M.stageCost (M.f (m + 2)) y u' :=
    fun y => (hs' y).2
  set f0 := M.f (m + 1) with hf0
  set f1 := M.f (m + 2) with hf1
  have hf1T : f1 = BSX.T M f0 := BSX.f_succ_succ M m
  have hform : ∀ w, w ≤ s → f1 w = M.c * (s - w) + M.L w + M.α * BSX.E M f0 s := by
    intro w hw; rw [hf1T]; exact BSX.opt_form M g0 s h0 w hw
  have hG0 := BSX.opt_min M s h0
  have hG1 := BSX.opt_min M s' h1
  have lip0 := BSX.good_lip g0
  have lip1 := BSX.good_lip g1
  have K0 := BSX.good_K g0
  have K1 := BSX.good_K g1
  by_contra hlt
  push_neg at hlt
  -- Δ monotonicity
  have hΔ : BSX.E M f1 s - BSX.E M f1 s' ≤ BSX.E M f0 s - BSX.E M f0 s' := by
    rw [BSX.E_diff M lip1 K1, BSX.E_diff M lip0 K0]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi (fun x hx => ?_)
    · have := (BSX.E_integrable M lip1 K1 s).sub (BSX.E_integrable M lip1 K1 s')
      refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Pi.sub_apply]; ring
    · have := (BSX.E_integrable M lip0 K0 s).sub (BSX.E_integrable M lip0 K0 s')
      refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Pi.sub_apply]; ring
    · have hx' : (0:ℝ) < x := hx
      have hm := BSX.f_mono M (m + 1) (by omega) (s' - x) (s - x) (by linarith)
      rw [hform (s - x) (by linarith), hform (s' - x) (by linarith)]
      refine mul_le_mul_of_nonneg_right ?_ (BSX.g_nonneg M hx)
      have e : s - x - (s' - x) = s - s' := by ring
      rw [e] at hm
      nlinarith
  have hEq : M.c * s + M.α * BSX.E M f1 s = M.c * s' + M.α * BSX.E M f1 s' := by
    have a1 := hG0 s'
    have a2 := hG1 s
    have a3 := mul_le_mul_of_nonneg_left hΔ M.α_pos.le
    apply le_antisymm _ a2
    nlinarith
  rcases le_or_gt s 0 with hs0 | hs0
  · -- s ≤ 0 : G1 strictly decreasing on (-∞, s]
    have hd : BSX.E M f1 s - BSX.E M f1 s' = -(M.c + M.b) * (s - s') := by
      rw [BSX.E_diff M lip1 K1]
      have : ∫ x in Ioi (0:ℝ), (f1 (s - x) - f1 (s' - x)) * M.g x =
          ∫ x in Ioi (0:ℝ), (-(M.c + M.b) * (s - s')) * M.g x := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        have hx' : (0:ℝ) < x := hx
        rw [hform (s - x) (by linarith), hform (s' - x) (by linarith),
          BSX.L_neg M (s - x) (by linarith), BSX.L_neg M (s' - x) (by linarith)]
        ring
      rw [this, integral_const_mul, M.g_total, mul_one]
    have hk := BSX.key_neg M
    have : M.c * s + M.α * BSX.E M f1 s - (M.c * s' + M.α * BSX.E M f1 s') =
        ((1 - M.α) * M.c - M.b * M.α) * (s - s') := by
      have : M.α * BSX.E M f1 s - M.α * BSX.E M f1 s' = M.α * (-(M.c + M.b) * (s - s')) := by
        rw [← hd]; ring
      linear_combination this
    have hpos : 0 < s - s' := by linarith
    nlinarith
  · -- s > 0 : strict convexity contradiction
    set a := max s' 0 with ha
    have has : a < s := max_lt hlt hs0
    have hsa : s' ≤ a := le_max_left _ _
    set G1 := fun z => M.c * z + M.α * BSX.E M f1 z with hG1def
    have hG1c : ConvexOn ℝ univ G1 := by
      have := (BSX.E_convex M lip1 K1 g1.2.1).smul M.α_pos.le
      exact (convexOn_id convex_univ |>.smul M.c_nonneg).add this
    have hseg : ∀ z, s' ≤ z → z ≤ s → G1 z = G1 s' := by
      intro z hz1 hz2
      apply le_antisymm _ (hG1 z)
      have := hG1c.le_max_of_mem_segment (mem_univ s') (mem_univ s)
        (by rw [segment_eq_Icc hlt.le]; exact ⟨hz1, hz2⟩)
      have e : G1 s = G1 s' := hEq
      rw [e, max_self] at this; exact this
    have hgap0 : BSX.gap G1 a s = 0 := by
      unfold BSX.gap
      rw [hseg a hsa has.le, hseg s hlt.le le_rfl, hseg ((a + s) / 2) (by linarith) (by linarith)]
      ring
    have hgapE : BSX.gap G1 a s = M.α * BSX.gap (BSX.E M f1) a s := by
      simp only [BSX.gap, hG1def]; ring
    have hgapEq : BSX.gap (BSX.E M f1) a s = BSX.gap (BSX.E M M.L) a s := by
      rw [BSX.E_gap M lip1 K1, BSX.E_gap M (BSX.L_lip M) (by linarith [M.h_pos, BSX.b_pos M])]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      have hx' : (0:ℝ) < x := hx
      simp only [BSX.gap]
      rw [hform (a - x) (by linarith), hform (s - x) (by linarith),
        hform ((a - x + (s - x)) / 2) (by linarith)]
      ring
    have hpos : 0 < BSX.gap (BSX.E M M.L) a s :=
      BSX.E_gap_pos M (BSX.L_lip M) (by linarith [M.h_pos, BSX.b_pos M]) (BSX.L_convex' M)
        a s (s / 2) (by linarith) (BSX.L_gap_pos M _ _ (by linarith) (by linarith))
    rw [hgapE, hgapEq] at hgap0
    have := mul_pos M.α_pos hpos
    linarith

end ServiceParts.BaseStock

open ServiceParts.BaseStock


theorem solution (M : Model) (n : ℕ) (hn : 2 ≤ n) (s s' : ℝ)
    (hs : M.IsOrderUpToOptimal n s) (hs' : M.IsOrderUpToOptimal (n + 1) s') : s ≤ s' := by
  exact property_a_core M n hn s s' hs hs'
