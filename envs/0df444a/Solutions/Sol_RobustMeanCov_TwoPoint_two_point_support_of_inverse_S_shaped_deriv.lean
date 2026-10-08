-- Prove2me | solution 1 for RobustMeanCov.TwoPoint.two_point_support_of_inverse_S_shaped_deriv
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T02:17:04.400214+00:00
-- url     : https://prove2.me/submissions/6021564f-c3b1-40ba-9ca2-f3afa80f8589

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_SShaped
import Definitions.Def_RobustMeanCov_TwoPoint_TwoPointSupport
open Filter Topology

set_option autoImplicit false


/- Inlined checked module: FlatContactSupport -/
section
noncomputable section
namespace PopescuSupport

/-- Expectation on the two-point law with lower deviation `d` and variance `v`. -/
def twoValue (u : ℝ → ℝ) (μ v d : ℝ) : ℝ :=
  (v * u (μ - d) + d ^ 2 * u (μ + v / d)) / (v + d ^ 2)

def quadratic (A B C x : ℝ) : ℝ := A * x ^ 2 + B * x + C

lemma twoValue_quadratic (A B C μ v d : ℝ) (hv : 0 < v) (hd : 0 < d) :
    twoValue (quadratic A B C) μ v d = A * (μ ^ 2 + v) + B * μ + C := by
  unfold twoValue quadratic
  have hden : v + d ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- A minimum over all two-point laws cannot have a globally false quadratic support
when the utility and quadratic agree throughout its contact interval. The alternative
law pairs any offending exterior point with a point inside that interval. -/
theorem quadratic_support_of_flat_minimizer
    (u : ℝ → ℝ) (A B C μ v d : ℝ) (hv : 0 < v) (hd : 0 < d)
    (hmin : ∀ e : ℝ, 0 < e → twoValue u μ v d ≤ twoValue u μ v e)
    (hflat : ∀ x ∈ Set.Icc (μ - d) (μ + v / d), u x = quadratic A B C x) :
    ∀ x : ℝ, quadratic A B C x ≤ u x := by
  have hdiv : 0 < v / d := div_pos hv hd
  have hbase : twoValue u μ v d = A * (μ ^ 2 + v) + B * μ + C := by
    rw [twoValue, hflat (μ - d) (by constructor <;> linarith),
      hflat (μ + v / d) (by constructor <;> linarith)]
    exact twoValue_quadratic A B C μ v d hv hd
  have hcomp (e : ℝ) (he : 0 < e) :
      v * quadratic A B C (μ - e) + e ^ 2 * quadratic A B C (μ + v / e) ≤
        v * u (μ - e) + e ^ 2 * u (μ + v / e) := by
    have h := hmin e he
    rw [hbase, ← twoValue_quadratic A B C μ v e hv he] at h
    exact (div_le_div_iff_of_pos_right (show 0 < v + e ^ 2 by positivity)).mp h
  intro x
  by_cases hleft : x < μ - d
  · let e := μ - x
    have he : 0 < e := by dsimp [e]; linarith
    have hde : d ≤ e := by dsimp [e]; linarith
    have hupper : μ + v / e ∈ Set.Icc (μ - d) (μ + v / d) := by
      constructor
      · have := div_pos hv he
        linarith
      · have h := div_le_div_of_nonneg_left hv.le hd hde
        linarith
    have h := hcomp e he
    rw [hflat _ hupper] at h
    have hlow : μ - e = x := by dsimp [e]; ring
    rw [hlow] at h
    nlinarith
  by_cases hright : μ + v / d < x
  · let e := v / (x - μ)
    have hx : 0 < x - μ := by linarith
    have he : 0 < e := div_pos hv hx
    have hed : e ≤ d := by
      apply (div_le_iff₀ hx).2
      have h := (div_lt_iff₀ hd).1 (show v / d < x - μ by linarith)
      nlinarith
    have hlower : μ - e ∈ Set.Icc (μ - d) (μ + v / d) := by
      constructor <;> linarith
    have hhigh : μ + v / e = x := by
      dsimp [e]
      field_simp
      ring
    have h := hcomp e he
    rw [hflat _ hlower, hhigh] at h
    have he2 : 0 < e ^ 2 := sq_pos_of_pos he
    nlinarith
  · have hx : x ∈ Set.Icc (μ - d) (μ + v / d) := ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
    exact (hflat x hx).ge

end PopescuSupport
end
end


/- Inlined checked module: CurvatureSupport -/
section
namespace PopescuSupport
open Set

/-- A concave-then-convex function with zero endpoint values cannot have a negative
value followed by a positive value between those endpoints. Weak curvature suffices. -/
lemma no_negative_then_positive (h : ℝ → ℝ) (a b c x y : ℝ)
    (hc : ConcaveOn ℝ (Iic c) h) (hv : ConvexOn ℝ (Ici c) h)
    (ha : h a = 0) (hb : h b = 0) (hax : a < x) (hxy : x < y) (hyb : y < b)
    (hx : h x < 0) (hy : 0 < h y) : False := by
  by_cases hyc : y ≤ c
  · have hz := hc.ge_on_segment (show a ≤ c by linarith) hyc
      (show x ∈ segment ℝ a y by rw [segment_eq_Icc (by linarith)]; exact ⟨hax.le, hxy.le⟩)
    rw [ha, min_eq_left hy.le] at hz
    linarith
  by_cases hcx : c ≤ x
  · have hz := hv.le_on_segment hcx (show c ≤ b by linarith)
      (show y ∈ segment ℝ x b by rw [segment_eq_Icc (by linarith)]; exact ⟨hxy.le, hyb.le⟩)
    rw [hb, max_eq_right hx.le] at hz
    linarith
  have hxc : x < c := lt_of_not_ge hcx
  have hcy : c < y := lt_of_not_ge hyc
  have hcn : h c < 0 := by
    by_contra hn
    have hn' : 0 ≤ h c := le_of_not_gt hn
    have hz := hc.ge_on_segment (show a ≤ c by linarith) (le_refl c)
      (show x ∈ segment ℝ a c by rw [segment_eq_Icc (by linarith)]; exact ⟨hax.le, hxc.le⟩)
    rw [ha, min_eq_left hn'] at hz
    linarith
  have hz := hv.le_on_segment (le_refl c) (show c ≤ b by linarith)
    (show y ∈ segment ℝ c b by rw [segment_eq_Icc (by linarith)]; exact ⟨hcy.le, hyb.le⟩)
  rw [hb, max_eq_right hcn.le] at hz
  linarith

/-- Between two tangent zero contacts, concave-then-convex derivative shape forces
the primitive to be nonnegative, including all affine-interval degeneracies. -/
theorem nonnegative_between_contacts (g h : ℝ → ℝ) (a b c : ℝ)
    (hder : ∀ x, HasDerivAt g (h x) x)
    (hc : ConcaveOn ℝ (Iic c) h) (hv : ConvexOn ℝ (Ici c) h)
    (hga : g a = 0) (hgb : g b = 0) (hha : h a = 0) (hhb : h b = 0) :
    ∀ z ∈ Icc a b, 0 ≤ g z := by
  intro z hz
  by_contra hn
  have hneg : g z < 0 := lt_of_not_ge hn
  have haz : a < z := lt_of_le_of_ne hz.1 (by intro he; subst z; linarith)
  have hzb : z < b := lt_of_le_of_ne hz.2 (by intro he; subst z; linarith)
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun x => (hder x).continuousAt
  obtain ⟨x, hx, hvalx⟩ := exists_hasDerivAt_eq_slope g h haz hcont.continuousOn
    (fun t _ => hder t)
  obtain ⟨y, hy, hvaly⟩ := exists_hasDerivAt_eq_slope g h hzb hcont.continuousOn
    (fun t _ => hder t)
  have hxn : h x < 0 := by rw [hvalx, hga, sub_zero]; exact div_neg_of_neg_of_pos hneg (sub_pos.mpr haz)
  have hyp : 0 < h y := by rw [hvaly, hgb, zero_sub]; exact div_pos (neg_pos.mpr hneg) (sub_pos.mpr hzb)
  exact no_negative_then_positive h a b c x y hc hv hha hhb hx.1 (hx.2.trans hy.1) hy.2 hxn hyp

end PopescuSupport
end


/- Inlined checked module: ExteriorSupport -/
section
namespace PopescuSupport
open Set

lemma exterior_signs_of_both_signs (h : ℝ → ℝ) (a b c : ℝ)
    (hc : ConcaveOn ℝ (Iic c) h) (hv : ConvexOn ℝ (Ici c) h)
    (ha : h a = 0) (hb : h b = 0)
    (hp : ∃ p ∈ Ioo a b, 0 < h p) (hq : ∃ q ∈ Ioo a b, h q < 0) :
    (∀ x < a, h x ≤ 0) ∧ (∀ x, b < x → 0 ≤ h x) := by
  obtain ⟨p, hp, hpp⟩ := hp
  obtain ⟨q, hq, hqn⟩ := hq
  have hab : a < b := hp.1.trans hp.2
  have hac : a < c := by
    by_contra hn
    have hca : c ≤ a := le_of_not_gt hn
    have hz := hv.le_on_segment hca (show c ≤ b by linarith)
      (show p ∈ segment ℝ a b by rw [segment_eq_Icc hab.le]; exact ⟨hp.1.le, hp.2.le⟩)
    rw [ha, hb, max_self] at hz
    linarith
  have hcb : c < b := by
    by_contra hn
    have hbc : b ≤ c := le_of_not_gt hn
    have hz := hc.ge_on_segment (show a ≤ c by linarith) hbc
      (show q ∈ segment ℝ a b by rw [segment_eq_Icc hab.le]; exact ⟨hq.1.le, hq.2.le⟩)
    rw [ha, hb, min_self] at hz
    linarith
  have hp' : ∃ t, a < t ∧ t ≤ c ∧ 0 < h t := by
    by_cases hpc : p ≤ c
    · exact ⟨p, hp.1, hpc, hpp⟩
    · refine ⟨c, hac, le_refl c, ?_⟩
      have hz := hv.le_on_segment (le_refl c) hcb.le
        (show p ∈ segment ℝ c b by rw [segment_eq_Icc hcb.le]; exact ⟨le_of_not_ge hpc, hp.2.le⟩)
      rw [hb] at hz
      by_contra hn
      have hn' : h c ≤ 0 := le_of_not_gt hn
      rw [max_eq_right hn'] at hz
      linarith
  have hq' : ∃ t, c ≤ t ∧ t < b ∧ h t < 0 := by
    by_cases hcq : c ≤ q
    · exact ⟨q, hcq, hq.2, hqn⟩
    · refine ⟨c, le_refl c, hcb, ?_⟩
      have hz := hc.ge_on_segment hac.le (le_refl c)
        (show q ∈ segment ℝ a c by rw [segment_eq_Icc hac.le]; exact ⟨hq.1.le, le_of_not_ge hcq⟩)
      rw [ha] at hz
      by_contra hn
      have hn' : 0 ≤ h c := le_of_not_gt hn
      rw [min_eq_left hn'] at hz
      linarith
  obtain ⟨p', hap', hp'c, hpp'⟩ := hp'
  obtain ⟨q', hcq', hq'b, hqn'⟩ := hq'
  constructor
  · intro x hxa
    have hz := hc.left_le_of_le_right (show x ≤ c by linarith) hp'c
      (show a ∈ openSegment ℝ x p' by rw [openSegment_eq_Ioo (by linarith)]; exact ⟨hxa, hap'⟩)
      (show h a ≤ h p' by rw [ha]; exact hpp'.le)
    simpa only [ha] using hz
  · intro x hbx
    have hz := hv.le_right_of_left_le hcq' (show c ≤ x by linarith)
      (show b ∈ openSegment ℝ q' x by rw [openSegment_eq_Ioo (by linarith)]; exact ⟨hq'b, hbx⟩)
      (show h q' ≤ h b by rw [hb]; exact hqn'.le)
    simpa only [hb] using hz

/-- Two tangent contacts either give a global lower support, or the primitive is
identically zero between the contacts. The latter case is retained explicitly. -/
theorem support_or_flat (g h : ℝ → ℝ) (a b c : ℝ)
    (hder : ∀ x, HasDerivAt g (h x) x)
    (hc : ConcaveOn ℝ (Iic c) h) (hv : ConvexOn ℝ (Ici c) h)
    (hga : g a = 0) (hgb : g b = 0) (hha : h a = 0) (hhb : h b = 0) :
    (∀ x : ℝ, 0 ≤ g x) ∨ (∀ x ∈ Icc a b, g x = 0) := by
  classical
  have hinside := nonnegative_between_contacts g h a b c hder hc hv hga hgb hha hhb
  by_cases hflat : ∀ x ∈ Icc a b, g x = 0
  · exact Or.inr hflat
  push Not at hflat
  obtain ⟨z, hz, hn⟩ := hflat
  have hpos : 0 < g z := lt_of_le_of_ne (hinside z hz) (Ne.symm hn)
  have haz : a < z := lt_of_le_of_ne hz.1 (by intro he; subst z; exact hn hga)
  have hzb : z < b := lt_of_le_of_ne hz.2 (by intro he; subst z; exact hn hgb)
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun x => (hder x).continuousAt
  obtain ⟨p, hp, hvalp⟩ := exists_hasDerivAt_eq_slope g h haz hcont.continuousOn (fun t _ => hder t)
  obtain ⟨q, hq, hvalq⟩ := exists_hasDerivAt_eq_slope g h hzb hcont.continuousOn (fun t _ => hder t)
  have hpp : 0 < h p := by rw [hvalp, hga, sub_zero]; exact div_pos hpos (sub_pos.mpr haz)
  have hqn : h q < 0 := by rw [hvalq, hgb, zero_sub]; exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hpos) (sub_pos.mpr hzb)
  obtain ⟨hleft, hright⟩ := exterior_signs_of_both_signs h a b c hc hv hha hhb
    ⟨p, ⟨hp.1, hp.2.trans hzb⟩, hpp⟩ ⟨q, ⟨haz.trans hq.1, hq.2⟩, hqn⟩
  left
  intro x
  by_cases hxa : x < a
  · obtain ⟨t, ht, hvalt⟩ := exists_hasDerivAt_eq_slope g h hxa hcont.continuousOn (fun s _ => hder s)
    have hh := hleft t ht.2
    rw [hvalt, hga, zero_sub] at hh
    have := (div_le_iff₀ (sub_pos.mpr hxa)).mp hh
    linarith
  by_cases hbx : b < x
  · obtain ⟨t, ht, hvalt⟩ := exists_hasDerivAt_eq_slope g h hbx hcont.continuousOn (fun s _ => hder s)
    have hh := hright t ht.1
    rw [hvalt, hgb, sub_zero] at hh
    simpa only [zero_mul] using (le_div_iff₀ (sub_pos.mpr hbx)).mp hh
  · exact hinside x ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩

end PopescuSupport
end


/- Inlined checked module: DerivativeShape -/
section
namespace PopescuSupport
open Set Filter
open scoped Topology

/-- The continuity needed at the shape breakpoint follows from monotonicity and
Darboux's theorem; it is not an extra smoothness hypothesis. -/
theorem continuous_deriv_of_strictAnti (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (ha : StrictAnti (deriv u)) : Continuous (deriv u) := by
  let v : ℝ → ℝ := -u
  have hv : Differentiable ℝ v := hu.neg
  have heq : deriv v = fun x => -deriv u x :=
    funext fun x => (hu x).hasDerivAt.neg.deriv
  have hm : StrictMono (deriv v) := by rw [heq]; exact ha.neg
  have hconn : OrdConnected (deriv v '' univ) :=
    convex_univ.ordConnected.image_deriv (fun x _ => hv x)
  have hcontinuous : Continuous (deriv v) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (hm.strictMonoOn univ).continuousAt_of_image_mem_nhds Filter.univ_mem
    have hleft : deriv v (x - 1) < deriv v x := hm (by linarith)
    have hright : deriv v x < deriv v (x + 1) := hm (by linarith)
    apply Filter.mem_of_superset (Ioo_mem_nhds hleft hright)
    intro y hy
    exact hconn.out ⟨x - 1, mem_univ _, rfl⟩ ⟨x + 1, mem_univ _, rfl⟩ ⟨hy.1.le, hy.2.le⟩
  rw [heq] at hcontinuous
  have hnegeq : -(fun x => -deriv u x) = deriv u := by
    funext x
    exact neg_neg _
  exact hnegeq ▸ hcontinuous.neg

lemma convexOn_closure_of_continuous (f : ℝ → ℝ) (s : Set ℝ)
    (hf : Continuous f) (hc : ConvexOn ℝ s f) : ConvexOn ℝ (closure s) f := by
  refine ⟨hc.1.closure, ?_⟩
  intro x hx y hy a b ha hb hab
  have hclosed : IsClosed {p : ℝ × ℝ |
      f (a * p.1 + b * p.2) ≤ a * f p.1 + b * f p.2} :=
    isClosed_le (hf.comp ((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd)))
      ((continuous_const.mul (hf.comp continuous_fst)).add
        (continuous_const.mul (hf.comp continuous_snd)))
  have hsub : s ×ˢ s ⊆ {p : ℝ × ℝ |
      f (a * p.1 + b * p.2) ≤ a * f p.1 + b * f p.2} := by
    intro p hp
    exact hc.2 hp.1 hp.2 ha hb hab
  have hmem : (x, y) ∈ closure (s ×ˢ s) := by
    rw [closure_prod_eq]
    exact ⟨hx, hy⟩
  exact hclosed.closure_subset_iff.mpr hsub hmem

end PopescuSupport
end


/- Inlined checked module: TwoValueBounds -/
section
namespace PopescuSupport
open Set Filter
open scoped Topology

lemma derivative_between_limits (f : ℝ → ℝ) (ha : Antitone f) (lm lp : ℝ)
    (hlm : Tendsto f atBot (𝓝 lm)) (hlp : Tendsto f atTop (𝓝 lp)) (x : ℝ) :
    lp ≤ f x ∧ f x ≤ lm := by
  constructor
  · exact le_of_tendsto hlp (eventually_atTop.mpr ⟨x, fun y hy => ha hy⟩)
  · exact ge_of_tendsto hlm (eventually_atBot.mpr ⟨x, fun y hy => ha hy⟩)

theorem exists_linear_bound (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (ha : Antitone (deriv u)) (lm lp : ℝ)
    (hlm : Tendsto (deriv u) atBot (𝓝 lm)) (hlp : Tendsto (deriv u) atTop (𝓝 lp)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, |u y - u x| ≤ L * |y - x| := by
  refine ⟨|lm| + |lp|, by positivity, ?_⟩
  have hnorm (x : ℝ) : ‖deriv u x‖ ≤ |lm| + |lp| := by
    obtain ⟨hlo, hhi⟩ := derivative_between_limits (deriv u) ha lm lp hlm hlp x
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [le_abs_self lm, neg_abs_le lp, abs_nonneg lm, abs_nonneg lp]
  intro x y
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le (fun x (_ : x ∈ (univ : Set ℝ)) => hu x)
      (fun x _ => hnorm x) convex_univ (mem_univ x) (mem_univ y)

lemma twoValue_lower_bounds (u : ℝ → ℝ) (μ v d L : ℝ) (hv : 0 < v) (hd : 0 < d)
    (hL : 0 ≤ L) (hu : ∀ x : ℝ, |u x - u μ| ≤ L * |x - μ|) :
    u μ - 2 * L * d ≤ twoValue u μ v d ∧
      u μ - 2 * L * v / d ≤ twoValue u μ v d := by
  have hD : 0 < v + d ^ 2 := by positivity
  have hdiv : 0 < v / d := div_pos hv hd
  have ha := hu (μ - d)
  have hb := hu (μ + v / d)
  rw [show μ - d - μ = -d by ring, abs_neg, abs_of_pos hd] at ha
  rw [show μ + v / d - μ = v / d by ring, abs_of_pos hdiv] at hb
  have ha' : u μ - L * d ≤ u (μ - d) := by have := (abs_le.mp ha).1; linarith
  have hb' : u μ - L * (v / d) ≤ u (μ + v / d) := by have := (abs_le.mp hb).1; linarith
  have hsum := add_le_add (mul_le_mul_of_nonneg_left ha' hv.le)
    (mul_le_mul_of_nonneg_left hb' (sq_nonneg d))
  have hfine : u μ - 2 * L * v * d / (v + d ^ 2) ≤ twoValue u μ v d := by
    calc
      _ = (v * (u μ - L * d) + d ^ 2 * (u μ - L * (v / d))) / (v + d ^ 2) := by
        field_simp
        ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hD).mpr hsum
  have hn : 0 ≤ 2 * L * v * d := by positivity
  have hs : 2 * L * v * d / (v + d ^ 2) ≤ 2 * L * d := by
    calc
      _ ≤ 2 * L * v * d / v := div_le_div_of_nonneg_left hn hv (by nlinarith)
      _ = _ := by field_simp
  have hl : 2 * L * v * d / (v + d ^ 2) ≤ 2 * L * v / d := by
    calc
      _ ≤ 2 * L * v * d / d ^ 2 := div_le_div_of_nonneg_left hn (sq_pos_of_pos hd) (by linarith)
      _ = _ := by field_simp
  constructor <;> linarith

lemma twoValue_one_lt (u : ℝ → ℝ) (hc : StrictConcaveOn ℝ univ u) (μ v : ℝ)
    (hv : 0 < v) : twoValue u μ v 1 < u μ := by
  have hD : 0 < v + 1 := by linarith
  have hsum : v / (v + 1) + 1 / (v + 1) = 1 := by field_simp
  have h := hc.2 (mem_univ (μ - 1)) (mem_univ (μ + v))
    (show μ - 1 ≠ μ + v by linarith) (div_pos hv hD) (div_pos zero_lt_one hD) hsum
  have hmean : (v / (v + 1)) • (μ - 1) + (1 / (v + 1)) • (μ + v) = μ := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hmean] at h
  have heq : twoValue u μ v 1 = (v / (v + 1)) * u (μ - 1) +
      (1 / (v + 1)) * u (μ + v) := by
    simp only [twoValue, one_pow, div_one, one_mul]
    ring
  rw [heq]
  exact h

end PopescuSupport
end


/- Inlined checked module: TwoValueAttainment -/
section
namespace PopescuSupport
open Set

lemma continuousOn_twoValue (u : ℝ → ℝ) (hu : Continuous u) (μ v : ℝ) (hv : 0 < v) :
    ContinuousOn (twoValue u μ v) (Ioi 0) := by
  intro d hd
  apply ContinuousAt.continuousWithinAt
  have hd' : 0 < d := hd
  have hd0 : d ≠ 0 := ne_of_gt hd'
  have hD : v + d ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold twoValue
  fun_prop

/-- Linear growth and one strict Jensen gap give a genuinely attained minimum among
all positive-deviation two-point laws, not merely an asymptotic infimum. -/
theorem twoValue_exists_min (u : ℝ → ℝ) (hu : Continuous u) (μ v L : ℝ)
    (hv : 0 < v) (hL : 0 ≤ L) (hbound : ∀ x, |u x - u μ| ≤ L * |x - μ|)
    (hgap : twoValue u μ v 1 < u μ) :
    ∃ d : ℝ, 0 < d ∧ ∀ e : ℝ, 0 < e → twoValue u μ v d ≤ twoValue u μ v e := by
  let η := u μ - twoValue u μ v 1
  have hη : 0 < η := sub_pos.mpr hgap
  have hL1 : 0 < L + 1 := by linarith
  let a := min 1 (η / (2 * (L + 1)))
  let b := max 1 (2 * (L + 1) * v / η)
  have ha : 0 < a := lt_min zero_lt_one (div_pos hη (by positivity))
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb1 : 1 ≤ b := le_max_left _ _
  have hmem : (1 : ℝ) ∈ Icc a b := ⟨ha1, hb1⟩
  have hcont : ContinuousOn (twoValue u μ v) (Icc a b) :=
    (continuousOn_twoValue u hu μ v hv).mono fun x hx => ha.trans_le hx.1
  obtain ⟨d, hd, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨1, hmem⟩ hcont
  refine ⟨d, ha.trans_le hd.1, ?_⟩
  intro e he
  obtain ⟨hsmall, hlarge⟩ := twoValue_lower_bounds u μ v e L hv he hL hbound
  have hbase : twoValue u μ v d ≤ twoValue u μ v 1 := hmin hmem
  by_cases hea : e < a
  · have heη : e < η / (2 * (L + 1)) := hea.trans_le (min_le_right _ _)
    have hmul := (lt_div_iff₀ (show 0 < 2 * (L + 1) by positivity)).mp heη
    have hh : 2 * L * e < η := by nlinarith
    dsimp [η] at hh
    linarith
  by_cases hbe : b < e
  · have hηe : 2 * (L + 1) * v / η < e := (le_max_right _ _).trans_lt hbe
    have hmul := (div_lt_iff₀ hη).mp hηe
    have hh : 2 * L * v / e < η := (div_lt_iff₀ he).mpr (by nlinarith)
    dsimp [η] at hh
    linarith
  · exact hmin ⟨le_of_not_gt hea, le_of_not_gt hbe⟩

end PopescuSupport
end


/- Inlined checked module: TwoValueStationarity -/
section
namespace PopescuSupport
open Set

lemma hasDerivAt_twoValue (u : ℝ → ℝ) (hu : Differentiable ℝ u) (μ v d : ℝ)
    (hv : 0 < v) (hd : 0 < d) :
    HasDerivAt (twoValue u μ v)
      (v * (2 * d * (u (μ + v / d) - u (μ - d)) -
        (v + d ^ 2) * (deriv u (μ - d) + deriv u (μ + v / d))) /
          (v + d ^ 2) ^ 2) d := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hD : v + d ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hlow := (hu (μ - d)).hasDerivAt.comp d
    ((hasDerivAt_const d μ).sub (hasDerivAt_id d))
  have hupp := (hu (μ + v / d)).hasDerivAt.comp d
    ((hasDerivAt_const d μ).add ((hasDerivAt_const d v).div (hasDerivAt_id d) hd0))
  have hp := (hasDerivAt_id d).pow 2
  have hN := (hlow.const_mul v).add (hp.mul hupp)
  have hden := (hasDerivAt_const d v).add hp
  unfold twoValue
  convert! hN.div hden hD using 1
  all_goals first | rfl | (dsimp; field_simp; ring)

theorem chord_identity_of_minimum (u : ℝ → ℝ) (hu : Differentiable ℝ u) (μ v d : ℝ)
    (hv : 0 < v) (hd : 0 < d)
    (hmin : ∀ e : ℝ, 0 < e → twoValue u μ v d ≤ twoValue u μ v e) :
    (u (μ + v / d) - u (μ - d)) / ((μ + v / d) - (μ - d)) =
      (deriv u (μ - d) + deriv u (μ + v / d)) / 2 := by
  have hlocal : IsLocalMin (twoValue u μ v) d :=
    (show IsMinOn (twoValue u μ v) (Ioi 0) d from hmin).isLocalMin (Ioi_mem_nhds hd)
  have hzero := hlocal.hasDerivAt_eq_zero (hasDerivAt_twoValue u hu μ v d hv hd)
  have hD : v + d ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hn : 2 * d * (u (μ + v / d) - u (μ - d)) =
      (v + d ^ 2) * (deriv u (μ - d) + deriv u (μ + v / d)) := by
    have hnum := (div_eq_zero_iff).mp hzero
    rcases hnum with hn | hn
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left (ne_of_gt hv))
    · exact False.elim ((pow_ne_zero _ hD) hn)
  have hgap : (μ + v / d) - (μ - d) ≠ 0 := by
    have := div_pos hv hd
    linarith
  apply (div_eq_div_iff hgap (by norm_num : (2 : ℝ) ≠ 0)).mpr
  apply (mul_right_inj' (ne_of_gt hd)).mp
  have hgd : ((μ + v / d) - (μ - d)) * d = v + d ^ 2 := by
    field_simp
    ring
  have hprod := congrArg (fun z : ℝ =>
    (deriv u (μ - d) + deriv u (μ + v / d)) * z) hgd
  nlinarith only [hn, hprod]

end PopescuSupport
end


/- Inlined checked module: TangentQuadratic -/
section
namespace PopescuSupport

lemma hasDerivAt_quadratic (A B C x : ℝ) :
    HasDerivAt (quadratic A B C) (2 * A * x + B) x := by
  unfold quadratic
  convert! ((((hasDerivAt_id x).pow 2).const_mul A).add
    ((hasDerivAt_id x).const_mul B)).add_const C using 1
  all_goals first | rfl | (dsimp; ring)

theorem exists_tangent_quadratic (u : ℝ → ℝ) (a b fa fb : ℝ) (hab : a < b)
    (hchord : (u b - u a) / (b - a) = (fa + fb) / 2) :
    ∃ A B C : ℝ, quadratic A B C a = u a ∧ quadratic A B C b = u b ∧
      2 * A * a + B = fa ∧ 2 * A * b + B = fb := by
  let A := (fb - fa) / (2 * (b - a))
  let B := fa - 2 * A * a
  let C := u a - A * a ^ 2 - B * a
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hA : 2 * A * (b - a) = fb - fa := by dsimp [A]; field_simp
  have hchord' : 2 * (u b - u a) = (b - a) * (fa + fb) := by
    have h := (div_eq_iff hba).mp hchord
    nlinarith
  refine ⟨A, B, C, ?_, ?_, ?_, ?_⟩
  · dsimp [quadratic, C]
    ring
  · dsimp [quadratic, C, B]
    have h := congrArg (fun z : ℝ => z * (b - a)) hA
    nlinarith [hchord', h]
  · dsimp [B]
    ring
  · dsimp [B]
    nlinarith [hA]

lemma affine_convex_concave (A B : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => 2 * A * x + B) ∧
      ConcaveOn ℝ Set.univ (fun x : ℝ => 2 * A * x + B) := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [smul_eq_mul]
    nlinarith [show (a + b) * B = B by rw [hab, one_mul]]
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [smul_eq_mul]
    nlinarith [show (a + b) * B = B by rw [hab, one_mul]]

end PopescuSupport
end


/- Inlined checked module: SupportFromMinimum -/
section
namespace PopescuSupport
open Set

/-- Global minimization selects a valid supporting contact pair even when the derivative
has affine intervals. Both the nonflat and completely flat cases are included. -/
theorem support_from_minimum (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (μ v d c : ℝ) (hv : 0 < v) (hd : 0 < d)
    (hc : ConcaveOn ℝ (Iic c) (deriv u)) (hx : ConvexOn ℝ (Ici c) (deriv u))
    (hmin : ∀ e : ℝ, 0 < e → twoValue u μ v d ≤ twoValue u μ v e) :
    ∃ A B C : ℝ, (∀ x, quadratic A B C x ≤ u x) ∧
      quadratic A B C (μ - d) = u (μ - d) ∧
      quadratic A B C (μ + v / d) = u (μ + v / d) := by
  have hdiv : 0 < v / d := div_pos hv hd
  have hab : μ - d < μ + v / d := by linarith
  obtain ⟨A, B, C, hqa, hqb, hda, hdb⟩ := exists_tangent_quadratic u
    (μ - d) (μ + v / d) (deriv u (μ - d)) (deriv u (μ + v / d)) hab
    (chord_identity_of_minimum u hu μ v d hv hd hmin)
  let g := fun x : ℝ => u x - quadratic A B C x
  let h := fun x : ℝ => deriv u x - (2 * A * x + B)
  have hgder (x : ℝ) : HasDerivAt g (h x) x :=
    (hu x).hasDerivAt.sub (hasDerivAt_quadratic A B C x)
  obtain ⟨hlinv, hlinc⟩ := affine_convex_concave A B
  have hhc : ConcaveOn ℝ (Iic c) h :=
    hc.sub (hlinv.subset (subset_univ _) (convex_Iic c))
  have hhx : ConvexOn ℝ (Ici c) h :=
    hx.sub (hlinc.subset (subset_univ _) (convex_Ici c))
  have hga : g (μ - d) = 0 := by dsimp [g]; rw [hqa, sub_self]
  have hgb : g (μ + v / d) = 0 := by dsimp [g]; rw [hqb, sub_self]
  have hha : h (μ - d) = 0 := by dsimp [h]; rw [hda, sub_self]
  have hhb : h (μ + v / d) = 0 := by dsimp [h]; rw [hdb, sub_self]
  have hsupport : ∀ x, quadratic A B C x ≤ u x := by
    rcases support_or_flat g h (μ - d) (μ + v / d) c hgder hhc hhx hga hgb hha hhb with hs | hf
    · intro x
      exact sub_nonneg.mp (hs x)
    · apply quadratic_support_of_flat_minimizer u A B C μ v d hv hd hmin
      intro x hmem
      exact sub_eq_zero.mp (hf x hmem)
  exact ⟨A, B, C, hsupport, hqa, hqb⟩

end PopescuSupport
end


/- Inlined checked module: PopescuRoot -/
section
open Set Filter
open scoped Topology

namespace RobustMeanCov.TwoPoint
open PopescuSupport

theorem two_point_support_of_inverse_S_shaped_deriv (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hinv : IsInverseSShaped (deriv u))
    (hbot : ∃ l : ℝ, Tendsto (deriv u) atBot (𝓝 l))
    (htop : ∃ l : ℝ, Tendsto (deriv u) atTop (𝓝 l)) :
    TwoPointSupport u := by
  obtain ⟨hm, c, hleft, hright⟩ := hinv
  have ha : StrictAnti (deriv u) := by
    intro x y hxy
    have h := hm hxy
    change -deriv u x < -deriv u y at h
    linarith
  have hcont := continuous_deriv_of_strictAnti u hu ha
  have hleft' : ConcaveOn ℝ (Iic c) (deriv u) := by
    have h := (convexOn_closure_of_continuous (-deriv u) (Iio c) hcont.neg hleft).neg
    simpa only [closure_Iio, neg_neg] using h
  have hright' : ConvexOn ℝ (Ici c) (deriv u) := by
    have hh : ConvexOn ℝ (Ioi c) (deriv u) := by simpa only [neg_neg] using hright.neg
    simpa only [closure_Ioi] using convexOn_closure_of_continuous (deriv u) (Ioi c) hcont hh
  obtain ⟨lm, hlm⟩ := hbot
  obtain ⟨lp, hlp⟩ := htop
  obtain ⟨L, hL, hbound⟩ := exists_linear_bound u hu ha.antitone lm lp hlm hlp
  have hconc := ha.strictConcaveOn_univ_of_deriv hu.continuous
  intro μ σ hσ
  have hv : 0 < σ ^ 2 := sq_pos_of_pos hσ
  obtain ⟨d, hd, hmin⟩ := twoValue_exists_min u hu.continuous μ (σ ^ 2) L hv hL
    (fun x => hbound μ x) (twoValue_one_lt u hconc μ (σ ^ 2) hv)
  obtain ⟨A, B, C, hs, hqa, hqb⟩ := support_from_minimum u hu μ (σ ^ 2) d c hv hd hleft' hright' hmin
  have hdiv : 0 < σ ^ 2 / d := div_pos hv hd
  have hab : μ - d < μ + σ ^ 2 / d := by linarith
  refine ⟨μ - d, μ + σ ^ 2 / d, A, B, C, hab, hs, hqa, hqb, ?_⟩
  let p := σ ^ 2 / (σ ^ 2 + d ^ 2)
  have hD : 0 < σ ^ 2 + d ^ 2 := by positivity
  have hp : 0 < p := div_pos hv hD
  have hp1 : p < 1 := (div_lt_one₀ hD).mpr (by nlinarith [sq_pos_of_pos hd])
  refine ⟨p, ⟨hp, hp1⟩, ?_, ?_⟩
  · dsimp [p]
    field_simp
    ring
  · dsimp [p]
    field_simp
    ring

end RobustMeanCov.TwoPoint
end


open Filter Topology RobustMeanCov.TwoPoint

theorem solution (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hinv : IsInverseSShaped (deriv u))
    (hbot : ∃ l : ℝ, Tendsto (deriv u) atBot (𝓝 l))
    (htop : ∃ l : ℝ, Tendsto (deriv u) atTop (𝓝 l)) :
    TwoPointSupport u := RobustMeanCov.TwoPoint.two_point_support_of_inverse_S_shaped_deriv u hu hinv hbot htop
