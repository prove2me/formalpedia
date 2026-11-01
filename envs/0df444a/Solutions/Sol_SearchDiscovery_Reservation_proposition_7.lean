-- Prove2me | solution 1 for SearchDiscovery.Reservation.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:17:07.9929+00:00
-- url     : https://prove2.me/submissions/48c8a3ee-8573-4134-ae2e-008abf2eb76e

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model
import Theorems.Thm_SearchDiscovery_Reservation_eq6_unique_solution
import Theorems.Thm_SearchDiscovery_Reservation_appendixB_Qd_formula

open SearchDiscovery.Reservation MeasureTheory ProbabilityTheory

namespace SDProp7Aux

/-- For a probability measure and a measurable `W` whose excess `max 0 (W - z)` is integrable for
every `z`, the equation `E[max 0 (W - z)] = c` has a unique solution for every `c > 0`. -/
lemma exists_unique_excess {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (W : α → ℝ) (hW : Measurable W)
    (hg : ∀ z, Integrable (fun p => max 0 (W p - z)) μ) (c : ℝ) (hc : 0 < c) :
    ∃! z : ℝ, ∫ p, max 0 (W p - z) ∂μ = c := by
  set f : ℝ → ℝ := fun z => ∫ p, max 0 (W p - z) ∂μ with hf
  have hlip : ∀ a b : ℝ, |f a - f b| ≤ |a - b| := by
    intro a b
    rw [hf]; dsimp only
    rw [← integral_sub (hg a) (hg b)]
    calc |∫ p, (max 0 (W p - a) - max 0 (W p - b)) ∂μ|
        = ‖∫ p, (max 0 (W p - a) - max 0 (W p - b)) ∂μ‖ := rfl
      _ ≤ ∫ p, ‖max 0 (W p - a) - max 0 (W p - b)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ p, |a - b| ∂μ := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _)
          refine Filter.Eventually.of_forall fun p => ?_
          simp only [Real.norm_eq_abs]
          have := abs_max_sub_max_le_max (0:ℝ) (W p - a) 0 (W p - b)
          calc _ ≤ max |(0:ℝ) - 0| |W p - a - (W p - b)| := this
            _ = |a - b| := by
                rw [sub_self, abs_zero, show W p - a - (W p - b) = b - a by ring, abs_sub_comm]
                exact max_eq_right (abs_nonneg _)
      _ = |a - b| := by simp
  have hcont : Continuous f := by
    refine LipschitzWith.continuous (K := 1) ?_
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [Real.dist_eq] using hlip a b
  -- some level is exceeded with positive probability
  obtain ⟨d, hd⟩ : ∃ d : ℝ, 0 < μ.real {p | d < W p} := by
    by_contra h
    push Not at h
    have h0 : ∀ n : ℕ, μ {p | -(n:ℝ) < W p} = 0 := by
      intro n
      have := h (-(n:ℝ))
      have hle : μ.real {p | -(n:ℝ) < W p} = 0 := le_antisymm this measureReal_nonneg
      rwa [measureReal_eq_zero_iff] at hle
    have hU : (⋃ n : ℕ, {p | -(n:ℝ) < W p}) = Set.univ := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (-W p)
      exact ⟨n, by linarith⟩
    have := measure_iUnion_null h0
    rw [hU] at this
    simp at this
  have hdm : MeasurableSet {p | d < W p} := measurableSet_lt measurable_const hW
  have hlow : ∀ z, z ≤ d → (d - z) * μ.real {p | d < W p} ≤ f z := by
    intro z hz
    have : ∫ p, Set.indicator {p | d < W p} (fun _ => d - z) p ∂μ ≤ f z := by
      apply integral_mono ((integrable_const _).indicator hdm) (hg z)
      intro p
      by_cases hp : p ∈ {p | d < W p}
      · rw [Set.indicator_of_mem hp]
        simp only [Set.mem_setOf_eq] at hp
        exact le_max_of_le_right (by linarith)
      · rw [Set.indicator_of_notMem hp]; exact le_max_left _ _
    rw [integral_indicator hdm, setIntegral_const, smul_eq_mul, mul_comm] at this
    exact this
  have htop : Filter.Tendsto f Filter.atTop (nhds 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ)
      (F := fun z p => max 0 (W p - z)) (f := fun _ => (0:ℝ))
      (l := Filter.atTop) (bound := fun p => max 0 (W p - 0))
      (Filter.Eventually.of_forall fun z => (hg z).aestronglyMeasurable)
      (by
        filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with z hz
        refine Filter.Eventually.of_forall fun p => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        exact max_le_max le_rfl (by linarith))
      (hg 0)
      (Filter.Eventually.of_forall fun p => by
        have : Filter.Tendsto (fun z : ℝ => W p - z) Filter.atTop Filter.atBot :=
          Filter.tendsto_atBot_add_const_left _ (W p) Filter.tendsto_neg_atTop_atBot |>.congr
            (fun z => by ring)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [this.eventually (Filter.eventually_le_atBot 0)] with z hz
        exact (max_eq_left hz).symm)
    simpa using this
  obtain ⟨z1, hz1⟩ : ∃ z1, f z1 ≤ c := by
    obtain ⟨z, hz⟩ := (htop.eventually (gt_mem_nhds hc)).exists
    exact ⟨z, hz.le⟩
  set q := μ.real {p | d < W p}
  set z0 := min z1 (d - c / q) with hz0
  have hz0le : z0 ≤ z1 := min_le_left _ _
  have hfz0 : c ≤ f z0 := by
    have h1 : z0 ≤ d - c / q := min_le_right _ _
    have hcq : 0 < c / q := div_pos hc hd
    have := hlow z0 (by linarith)
    have : c ≤ (d - z0) * q := by
      have : c = (c / q) * q := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hd.le
    linarith
  have hstrict : ∀ a b, a < b → f a = f b → f b = 0 := by
    intro a b hab heq
    have hd : ∫ p, (max 0 (W p - a) - max 0 (W p - b)) ∂μ = 0 := by
      rw [integral_sub (hg a) (hg b)]; exact sub_eq_zero.mpr heq
    have hnn : 0 ≤ᵐ[μ] fun p => max 0 (W p - a) - max 0 (W p - b) :=
      Filter.Eventually.of_forall fun p => by
        simp only [Pi.zero_apply, sub_nonneg]
        exact max_le_max le_rfl (by linarith)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn ((hg a).sub (hg b))).mp hd
    have : (fun p => max 0 (W p - b)) =ᵐ[μ] fun _ => (0:ℝ) := by
      filter_upwards [hae] with p hp
      simp only [Pi.zero_apply] at hp
      by_contra hne
      have hpos : 0 < W p - b := by
        by_contra h; push Not at h; exact hne (max_eq_left h)
      rw [max_eq_right hpos.le, max_eq_right (by linarith : (0:ℝ) ≤ W p - a)] at hp
      linarith
    show ∫ p, max 0 (W p - b) ∂μ = 0
    rw [integral_congr_ae this]; simp
  obtain ⟨a, -, hza⟩ := intermediate_value_Icc' hz0le hcont.continuousOn ⟨hz1, hfz0⟩
  refine ⟨a, hza, fun b hb => ?_⟩
  have ha : f a = c := hza
  have hb' : f b = c := hb
  rcases lt_trichotomy a b with h | h | h
  · have := hstrict a b h (ha.trans hb'.symm); linarith
  · exact h.symm
  · have := hstrict b a h (hb'.trans ha.symm); linarith

end SDProp7Aux

theorem solution (M : SDModel) (hM : M.Standing) :
    ∃! z : ℝ, M.Qd z = 0 := by
  have hcd := hM.cd_pos
  have hnd : Nonempty (Fin M.nd) := ⟨⟨0, hM.nd_pos⟩⟩
  choose zs hzs using fun x => (eq6_unique_solution M hM x).exists
  -- integrability facts for `Q_s`
  have hgκ : ∀ x z : ℝ, Integrable (fun y : ℝ => max 0 (x + y - z)) (M.κ x) := by
    intro x z
    have hint : Integrable (fun y : ℝ => y) (M.κ x) := (hM.memLp_κ x).integrable (by norm_num)
    have h1 : Integrable (fun y : ℝ => x + y - z) (M.κ x) :=
      ((integrable_const x).add hint).sub (integrable_const z)
    exact (integrable_const (0:ℝ)).sup h1
  have hanti : ∀ x a b, a ≤ b → M.Qs x b ≤ M.Qs x a := by
    intro x a b hab
    simp only [SDModel.Qs]
    have := integral_mono (hgκ x b) (hgκ x a) (fun y => max_le_max le_rfl (by linarith))
    linarith
  have hiff : ∀ x c, zs x ≤ c ↔ M.Qs x c ≤ 0 := by
    intro x c
    constructor
    · intro h; exact (hanti x _ _ h).trans (hzs x).le
    · intro h
      by_contra hlt
      push Not at hlt
      have h0 : M.Qs x c = 0 := le_antisymm h ((hzs x).symm.le.trans (hanti x _ _ hlt.le))
      have := (eq6_unique_solution M hM x).unique h0 (hzs x)
      linarith
  have hQm : ∀ c, Measurable fun x => M.Qs x c := by
    intro c
    have hF : StronglyMeasurable fun q : ℝ × ℝ => max 0 (q.1 + q.2 - c) :=
      (by fun_prop : Continuous fun q : ℝ × ℝ => max 0 (q.1 + q.2 - c)).stronglyMeasurable
    exact (hF.integral_kernel_prod_right' (κ := M.κ)).measurable.sub_const _
  have hzsm : Measurable zs := by
    refine measurable_of_Iic fun c => ?_
    have : zs ⁻¹' Set.Iic c = {x | M.Qs x c ≤ 0} := by
      ext x; simp [hiff]
    rw [this]
    exact measurableSet_le (hQm c) measurable_const
  -- the random variable `max_k W̃_k`
  set W : (Fin M.nd → ℝ × ℝ) → ℝ :=
    fun p => ⨆ k : Fin M.nd, min (zs (p k).1) ((p k).1 + (p k).2) with hWdef
  set μ : Measure (Fin M.nd → ℝ × ℝ) := Measure.pi fun _ : Fin M.nd => M.G ⊗ₘ M.κ with hμ
  have hWm : Measurable W := by
    refine Measurable.iSup fun k => ?_
    have h1 : Measurable fun p : Fin M.nd → ℝ × ℝ => (p k).1 :=
      measurable_fst.comp (measurable_pi_apply k)
    have h2 : Measurable fun p : Fin M.nd → ℝ × ℝ => (p k).2 :=
      measurable_snd.comp (measurable_pi_apply k)
    exact (hzsm.comp h1).min (h1.add h2)
  -- integrability of the purchase values of the discovered products
  set ν := M.G ⊗ₘ M.κ with hν
  have hfst : ν.map Prod.fst = M.G := by
    rw [← Measure.fst, hν, Measure.fst_compProd]
  have hX : Integrable (fun q : ℝ × ℝ => q.1) ν := by
    have hG : Integrable (fun x : ℝ => x) M.G := hM.memLp_G.integrable (by norm_num)
    rw [← hfst] at hG
    exact hG.comp_measurable measurable_fst
  have hv : Integrable (fun q : ℝ × ℝ => q.1 + q.2) ν := hX.add hM.integrable_Y
  have hvk : ∀ (k : Fin M.nd) (z : ℝ),
      Integrable (fun p : Fin M.nd → ℝ × ℝ => max 0 ((p k).1 + (p k).2 - z)) μ := by
    intro k z
    have hmp : MeasurePreserving (Function.eval k) μ ν := measurePreserving_eval _ k
    have : Integrable (fun q : ℝ × ℝ => max 0 (q.1 + q.2 - z)) ν :=
      (integrable_const (0:ℝ)).sup (hv.sub (integrable_const z))
    exact hmp.integrable_comp_of_integrable this
  have hint : ∀ z, Integrable (fun p => max 0 (W p - z)) μ := by
    intro z
    refine Integrable.mono' (integrable_finset_sum Finset.univ fun k _ => hvk k z)
      ((measurable_const.max (hWm.sub measurable_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have hsum : 0 ≤ ∑ k, max 0 ((p k).1 + (p k).2 - z) :=
      Finset.sum_nonneg fun k _ => le_max_left _ _
    have hW : W p - z ≤ ∑ k, max 0 ((p k).1 + (p k).2 - z) := by
      have : W p ≤ z + ∑ k, max 0 ((p k).1 + (p k).2 - z) := by
        refine ciSup_le fun k => ?_
        refine (min_le_right _ _).trans ?_
        have h1 : max 0 ((p k).1 + (p k).2 - z) ≤ ∑ k, max 0 ((p k).1 + (p k).2 - z) :=
          Finset.single_le_sum (f := fun k => max 0 ((p k).1 + (p k).2 - z))
            (fun k _ => le_max_left _ _) (Finset.mem_univ k)
        have h2 := le_max_right 0 ((p k).1 + (p k).2 - z)
        linarith
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le hsum hW
  have hQd : ∀ z, M.Qd z = (∫ p, max 0 (W p - z) ∂μ) - M.cd := fun z =>
    (appendixB_Qd_formula M hM zs hzs z).2.1
  obtain ⟨z, hz, huniq⟩ := SDProp7Aux.exists_unique_excess μ W hWm hint M.cd hcd
  refine ⟨z, show M.Qd z = 0 by rw [hQd, hz, sub_self], fun y hy => huniq y ?_⟩
  have hy' : M.Qd y = 0 := hy
  rw [hQd] at hy'
  linarith
