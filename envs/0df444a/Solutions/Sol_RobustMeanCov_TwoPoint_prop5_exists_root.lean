-- Prove2me | solution 1 for RobustMeanCov.TwoPoint.prop5_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:15:40.67402+00:00
-- url     : https://prove2.me/submissions/bbb2fc8a-6208-41a6-b33c-ab584a5ef1c5

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_SShaped
import Definitions.Def_RobustMeanCov_TwoPoint_Prop5Gap

set_option autoImplicit false

open Filter Topology

namespace P2be12cfd

lemma cont_neg_deriv (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hm : StrictMono (-deriv u)) : Continuous (-deriv u) := by
  have hF : deriv (fun x => -u x) = -deriv u := by
    funext x; simp
  have hoc : Set.OrdConnected ((-deriv u) '' Set.univ) := by
    rw [← hF]
    exact Set.ordConnected_univ.image_deriv (fun x _ => (hu x).neg)
  refine continuous_iff_continuousAt.mpr fun a => ?_
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (hm.monotone.monotoneOn _)
    Filter.univ_mem ?_
  have h1 : (-deriv u) (a - 1) < (-deriv u) a := hm (by linarith)
  have h2 : (-deriv u) a < (-deriv u) (a + 1) := hm (by linarith)
  refine Filter.mem_of_superset (Icc_mem_nhds h1 h2) ?_
  exact hoc.out (Set.mem_image_of_mem _ (Set.mem_univ _))
    (Set.mem_image_of_mem _ (Set.mem_univ _))

lemma slope_bounds (u : ℝ → ℝ) (hu : Differentiable ℝ u) (ha : StrictAnti (deriv u))
    {p q : ℝ} (h : p < q) :
    deriv u q * (q - p) ≤ u q - u p ∧ u q - u p ≤ deriv u p * (q - p) := by
  obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope u h hu.continuous.continuousOn
    hu.differentiableOn
  have hpq : 0 < q - p := by linarith
  have he : u q - u p = deriv u ξ * (q - p) := by rw [hd]; field_simp
  have h1 := ha hξ.2
  have h2 := ha hξ.1
  rw [he]; constructor <;> nlinarith

end P2be12cfd

open Filter Topology RobustMeanCov.TwoPoint in
theorem solution (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hinv : IsInverseSShaped (deriv u))
    (hbot : ∃ l : ℝ, Tendsto (deriv u) atBot (𝓝 l))
    (htop : ∃ l : ℝ, Tendsto (deriv u) atTop (𝓝 l))
    (μ σ : ℝ) (hσ : 0 < σ) :
    ∃ a b : ℝ, a < μ ∧ b = partnerPoint μ σ a ∧ prop5Gap u μ σ a = 0 ∧ a < b ∧
      (b - μ) * (μ - a) = σ ^ 2 ∧
      (u b - u a) / (b - a) = (deriv u a + deriv u b) / 2 := by
  have hm : StrictMono (-deriv u) := hinv.1
  have ha : StrictAnti (deriv u) := by
    intro a b hab
    have := hm hab
    simp only [Pi.neg_apply, neg_lt_neg_iff] at this
    exact this
  have hfc : Continuous (deriv u) := by
    have h := (P2be12cfd.cont_neg_deriv u hu hm).neg
    have he : deriv u = -(-deriv u) := by simp
    rw [he]; exact h
  have hσ2 : 0 < σ ^ 2 := by positivity
  have zgt : ∀ y, y < μ → μ < partnerPoint μ σ y := by
    intro y hy
    have : 0 < σ ^ 2 / (μ - y) := div_pos hσ2 (by linarith)
    simp only [partnerPoint]; linarith
  -- continuity of the gap on (-∞, μ)
  have hzc : ∀ y, y < μ → ContinuousAt (fun y => partnerPoint μ σ y) y := by
    intro y hy
    have hne : μ - y ≠ 0 := by linarith
    unfold partnerPoint
    exact continuousAt_const.add
      (continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne)
  have hgc : ContinuousOn (fun y => prop5Gap u μ σ y) (Set.Iio μ) := by
    intro y hy
    have hy' : y < μ := hy
    apply ContinuousAt.continuousWithinAt
    have hz := hzc y hy'
    have hne : partnerPoint μ σ y - y ≠ 0 := by
      have := zgt y hy'; linarith
    have hu1 : ContinuousAt (fun y => u (partnerPoint μ σ y)) y :=
      hu.continuous.continuousAt.comp hz
    have hf1 : ContinuousAt (fun y => deriv u (partnerPoint μ σ y)) y :=
      hfc.continuousAt.comp hz
    unfold prop5Gap
    exact ((hu1.sub hu.continuous.continuousAt).div (hz.sub continuousAt_id) hne).sub
      ((hfc.continuousAt.add hf1).div_const 2)
  obtain ⟨L, hL⟩ := hbot
  obtain ⟨T, hT⟩ := htop
  have hfL : deriv u μ < L := by
    have h1 : deriv u μ < deriv u (μ - 1) := ha (by linarith)
    have h2 : deriv u (μ - 1) ≤ L := ge_of_tendsto hL (by
      filter_upwards [eventually_le_atBot (μ - 1)] with x hx
      exact ha.antitone hx)
    linarith
  have hfT : T < deriv u μ := by
    have h1 : deriv u (μ + 1) < deriv u μ := ha (by linarith)
    have h2 : T ≤ deriv u (μ + 1) := le_of_tendsto hT (by
      filter_upwards [eventually_ge_atTop (μ + 1)] with x hx
      exact ha.antitone hx)
    linarith
  -- positive value far to the left
  obtain ⟨y1, hy1μ, hg1⟩ : ∃ y, y < μ ∧ 0 < prop5Gap u μ σ y := by
    obtain ⟨c, hc1, hcμ⟩ : ∃ c, (L + deriv u μ) / 2 < deriv u c ∧ c < μ :=
      ((hL.eventually (lt_mem_nhds (by linarith : (L + deriv u μ) / 2 < L))).and
        (eventually_lt_atBot μ)).exists
    have hmy : Tendsto (fun y : ℝ => μ - y) atBot atTop :=
      tendsto_atTop.2 fun b => by
        filter_upwards [eventually_le_atBot (μ - b)] with y hy
        linarith
    have hz_bot : Tendsto (fun y => partnerPoint μ σ y) atBot (𝓝 μ) := by
      have h1 := (tendsto_const_nhds (x := σ ^ 2)).div_atTop hmy
      have h2 := (tendsto_const_nhds (x := μ)).add h1
      simpa [partnerPoint] using h2
    have hzy : Tendsto (fun y => partnerPoint μ σ y - y) atBot atTop := by
      refine tendsto_atTop_mono' _ ?_ hmy
      filter_upwards [eventually_lt_atBot μ] with y hy
      have := zgt y hy
      linarith
    have hfz : Tendsto (fun y => deriv u (partnerPoint μ σ y)) atBot (𝓝 (deriv u μ)) :=
      (hfc.tendsto μ).comp hz_bot
    have hD : Tendsto (fun y => (deriv u c + (deriv u (partnerPoint μ σ y) - deriv u c) *
        ((partnerPoint μ σ y - c) / (partnerPoint μ σ y - y))) -
        (deriv u y + deriv u (partnerPoint μ σ y)) / 2) atBot
        (𝓝 ((deriv u c + (deriv u μ - deriv u c) * 0) - (L + deriv u μ) / 2)) :=
      (tendsto_const_nhds.add ((hfz.sub tendsto_const_nhds).mul
        ((hz_bot.sub_const c).div_atTop hzy))).sub ((hL.add hfz).div_const 2)
    have hpos : 0 < (deriv u c + (deriv u μ - deriv u c) * 0) - (L + deriv u μ) / 2 := by
      linarith
    obtain ⟨y, hyD, hyc⟩ := ((hD.eventually (lt_mem_nhds hpos)).and
      (eventually_lt_atBot c)).exists
    refine ⟨y, by linarith, ?_⟩
    have hyμ : y < μ := by linarith
    have hzμ := zgt y hyμ
    set z := partnerPoint μ σ y with hzdef
    have hs : 0 < z - y := by linarith
    have b1 := (P2be12cfd.slope_bounds u hu ha hyc).1
    have b2 := (P2be12cfd.slope_bounds u hu ha (show c < z by linarith)).1
    have hlow : deriv u c + (deriv u z - deriv u c) * ((z - c) / (z - y)) ≤
        (u z - u y) / (z - y) := by
      have e : deriv u c + (deriv u z - deriv u c) * ((z - c) / (z - y)) =
          (deriv u c * (z - y) + (deriv u z - deriv u c) * (z - c)) / (z - y) := by
        field_simp
      rw [e, div_le_div_iff_of_pos_right hs]
      nlinarith
    show 0 < (u z - u y) / (z - y) - (deriv u y + deriv u z) / 2
    linarith
  -- negative value just left of μ
  obtain ⟨y2, hy2μ, hg2⟩ : ∃ y, y < μ ∧ prop5Gap u μ σ y < 0 := by
    obtain ⟨c, hc1, hcμ⟩ : ∃ c, deriv u c < (T + deriv u μ) / 2 ∧ μ < c :=
      ((hT.eventually (gt_mem_nhds (by linarith : T < (T + deriv u μ) / 2))).and
        (eventually_gt_atTop μ)).exists
    have hmy0 : Tendsto (fun y : ℝ => μ - y) (𝓝[<] μ) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℝ => μ - y) (𝓝 μ) (𝓝 (μ - μ)) :=
          tendsto_const_nhds.sub tendsto_id
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_pos.2 (show y < μ from hy)
    have hz_top : Tendsto (fun y => partnerPoint μ σ y) (𝓝[<] μ) atTop := by
      have h1 := (tendsto_inv_nhdsGT_zero.comp hmy0).const_mul_atTop hσ2
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [tendsto_atTop.1 h1 (b - μ)] with y hy
      simp only [Function.comp_apply] at hy
      simp only [partnerPoint, div_eq_mul_inv]
      linarith
    have hzy : Tendsto (fun y => partnerPoint μ σ y - y) (𝓝[<] μ) atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [tendsto_atTop.1 hz_top (b + μ), self_mem_nhdsWithin] with y hy hyμ
      have : y < μ := hyμ
      linarith
    have hfy : Tendsto (deriv u) (𝓝[<] μ) (𝓝 (deriv u μ)) :=
      (hfc.tendsto μ).mono_left nhdsWithin_le_nhds
    have hcy : Tendsto (fun y : ℝ => c - y) (𝓝[<] μ) (𝓝 (c - μ)) :=
      (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    have hfz : Tendsto (fun y => deriv u (partnerPoint μ σ y)) (𝓝[<] μ) (𝓝 T) :=
      hT.comp hz_top
    have hD : Tendsto (fun y => (deriv u c + (deriv u y - deriv u c) *
        ((c - y) / (partnerPoint μ σ y - y))) -
        (deriv u y + deriv u (partnerPoint μ σ y)) / 2) (𝓝[<] μ)
        (𝓝 ((deriv u c + (deriv u μ - deriv u c) * 0) - (deriv u μ + T) / 2)) :=
      (tendsto_const_nhds.add ((hfy.sub tendsto_const_nhds).mul
        (hcy.div_atTop hzy))).sub ((hfy.add hfz).div_const 2)
    have hneg : (deriv u c + (deriv u μ - deriv u c) * 0) - (deriv u μ + T) / 2 < 0 := by
      linarith
    obtain ⟨y, ⟨hyD, hzc'⟩, hyμ⟩ := (((hD.eventually (gt_mem_nhds hneg)).and
      (hz_top.eventually (eventually_gt_atTop c))).and self_mem_nhdsWithin).exists
    have hyμ' : y < μ := hyμ
    refine ⟨y, hyμ', ?_⟩
    have hzμ := zgt y hyμ'
    set z := partnerPoint μ σ y with hzdef
    have hs : 0 < z - y := by linarith
    have b1 := (P2be12cfd.slope_bounds u hu ha (show y < c by linarith)).2
    have b2 := (P2be12cfd.slope_bounds u hu ha hzc').2
    have hup : (u z - u y) / (z - y) ≤
        deriv u c + (deriv u y - deriv u c) * ((c - y) / (z - y)) := by
      have e : deriv u c + (deriv u y - deriv u c) * ((c - y) / (z - y)) =
          (deriv u c * (z - y) + (deriv u y - deriv u c) * (c - y)) / (z - y) := by
        field_simp
      rw [e, div_le_div_iff_of_pos_right hs]
      nlinarith
    show (u z - u y) / (z - y) - (deriv u y + deriv u z) / 2 < 0
    linarith
  -- intermediate value theorem
  have hsub : Set.uIcc y1 y2 ⊆ Set.Iio μ := by
    intro x hx
    rcases Set.mem_uIcc.1 hx with h | h
    · show x < μ; linarith [h.2]
    · show x < μ; linarith [h.2]
  have h0 : (0 : ℝ) ∈ Set.uIcc (prop5Gap u μ σ y1) (prop5Gap u μ σ y2) :=
    Set.mem_uIcc.2 (Or.inr ⟨hg2.le, hg1.le⟩)
  obtain ⟨x, hx, hgx⟩ := intermediate_value_uIcc (hgc.mono hsub) h0
  have hxμ : x < μ := hsub hx
  have hzx := zgt x hxμ
  refine ⟨x, partnerPoint μ σ x, hxμ, rfl, hgx, by linarith, ?_, ?_⟩
  · have hne : μ - x ≠ 0 := by linarith
    simp only [partnerPoint]
    field_simp
    ring
  · have h := hgx
    simp only [prop5Gap] at h
    exact sub_eq_zero.1 h
