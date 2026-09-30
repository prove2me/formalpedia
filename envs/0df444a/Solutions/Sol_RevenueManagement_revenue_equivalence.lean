-- Prove2me | solution 1 for RevenueManagement.revenue_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:59:20.222182+00:00
-- url     : https://prove2.me/submissions/02f3d1cd-ff77-479f-aa90-0da46b1a9d87

import Definitions.Def_RevenueManagement_auctions

open MeasureTheory Set Filter Topology

namespace RevenueManagement

/-! ### Clamping to an interval -/

/-- `x` clamped to `[a, b]`. -/
noncomputable def reClamp (a b x : ℝ) : ℝ := max a (min x b)

lemma reClamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : reClamp a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma reClamp_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : reClamp a b x = x := by
  unfold reClamp; rw [min_eq_left hx.2, max_eq_right hx.1]

lemma reClamp_cont (a b : ℝ) : Continuous (reClamp a b) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma reClamp_mono (a b : ℝ) : Monotone (reClamp a b) :=
  fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

/-! ### The envelope argument -/

/-- If `(y - x) P x ≤ S y - S x` on `[a, b]`, then `S` has derivative `P x` at every interior
point where `P` is continuous. -/
lemma re_deriv {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) {x : ℝ}
    (hx : x ∈ Ioo a b) (hPc : ContinuousAt P x) : HasDerivAt S (P x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlo : Tendsto (fun y => min (P x) (P y)) (𝓝[≠] x) (𝓝 (P x)) := by
    have : Tendsto (fun y => min (P x) (P y)) (𝓝 x) (𝓝 (min (P x) (P x))) :=
      tendsto_const_nhds.min hPc
    rw [min_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun y => max (P x) (P y)) (𝓝[≠] x) (𝓝 (P x)) := by
    have : Tendsto (fun y => max (P x) (P y)) (𝓝 x) (𝓝 (max (P x) (P x))) :=
      tendsto_const_nhds.max hPc
    rw [max_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hxI : x ∈ Icc a b := Ioo_subset_Icc_self hx
  have hev : ∀ᶠ y in 𝓝[≠] x, y ∈ Icc a b ∧ y ≠ x := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      with y hy hyI
    exact ⟨hyI, hy⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev] with y hy
    obtain ⟨hyI, hyx⟩ := hy
    have h1 := hsand x hxI y hyI
    have h2 := hsand y hyI x hxI
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have hneg : y - x < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      calc (S y - S x) ≤ (y - x) * P y := by linarith
        _ ≤ min (P x) (P y) * (y - x) := by
          rw [mul_comm]; exact mul_le_mul_of_nonpos_right (min_le_right _ _) hneg.le
    · have hpos : 0 < y - x := by linarith
      rw [le_div_iff₀ hpos]
      calc min (P x) (P y) * (y - x) ≤ P x * (y - x) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hpos.le
        _ ≤ S y - S x := by linarith
  · filter_upwards [hev] with y hy
    obtain ⟨hyI, hyx⟩ := hy
    have h1 := hsand x hxI y hyI
    have h2 := hsand y hyI x hxI
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have hneg : y - x < 0 := by linarith
      rw [div_le_iff_of_neg hneg]
      calc max (P x) (P y) * (y - x) ≤ P x * (y - x) :=
            mul_le_mul_of_nonpos_right (le_max_left _ _) hneg.le
        _ ≤ S y - S x := by linarith
    · have hpos : 0 < y - x := by linarith
      rw [div_le_iff₀ hpos]
      calc S y - S x ≤ (y - x) * P y := by linarith
        _ ≤ max (P x) (P y) * (y - x) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

/-- The sandwich makes `P` monotone. -/
lemma re_mono {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    MonotoneOn P (Icc a b) := by
  intro x hx y hy hxy
  rcases hxy.lt_or_eq with h | h
  · have h1 := hsand x hx y hy
    have h2 := hsand y hy x hx
    have : (y - x) * P x ≤ (y - x) * P y := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  · rw [h]

/-- The sandwich makes `S` continuous on `[a, b]` (it is Lipschitz). -/
lemma re_cont {P S : ℝ → ℝ} {a b : ℝ}
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    ContinuousOn S (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty (not_le.mpr hba)]; exact continuousOn_empty _
  have hm := re_mono hsand
  set L := max |P a| |P b| with hL
  have hbound : ∀ x ∈ Icc a b, |P x| ≤ L := by
    intro x hx
    have h1 := hm ⟨le_rfl, hab⟩ hx hx.1
    have h2 := hm hx ⟨hab, le_rfl⟩ hx.2
    rw [abs_le]
    constructor
    · have := neg_abs_le (P a); have := le_max_left |P a| |P b|; linarith
    · have := le_abs_self (P b); have := le_max_right |P a| |P b|; linarith
  have hlip : LipschitzOnWith (Real.toNNReal L) S (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ ((abs_nonneg _).trans (hbound x hx))]
    have h1 := hsand x hx y hy
    have h2 := hsand y hy x hx
    have bx := abs_le.mp (hbound x hx)
    have by' := abs_le.mp (hbound y hy)
    rcases le_total x y with hxy | hxy
    · rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
      rw [abs_le]
      constructor <;> nlinarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
      rw [abs_le]
      constructor <;> nlinarith
  exact hlip.continuousOn

/-- The countable set of discontinuities of `P` (through its clamped monotone extension). -/
lemma re_countable {P : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hm : MonotoneOn P (Icc a b)) :
    ∃ D : Set ℝ, D.Countable ∧ ∀ x ∈ Ioo a b \ D, ContinuousAt P x := by
  have hmono : Monotone (fun x => P (reClamp a b x)) := fun x y hxy =>
    hm (reClamp_mem hab x) (reClamp_mem hab y) (reClamp_mono a b hxy)
  refine ⟨{x | ¬ContinuousAt (fun x => P (reClamp a b x)) x}, hmono.countable_not_continuousAt,
    fun x hx => ?_⟩
  have hc : ContinuousAt (fun x => P (reClamp a b x)) x := by
    by_contra h; exact hx.2 h
  refine hc.congr ?_
  filter_upwards [Ioo_mem_nhds hx.1.1 hx.1.2] with y hy
  rw [reClamp_of_mem (Ioo_subset_Icc_self hy)]

/-- The envelope formula: `S b - S a = ∫_a^b P`. -/
lemma re_ftc {P S : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    S b - S a = ∫ x in a..b, P x := by
  obtain ⟨D, hD, hDc⟩ := re_countable hab (re_mono hsand)
  have hint : IntervalIntegrable P volume a b :=
    (re_mono hsand).mono (by rw [uIcc_of_le hab]) |>.intervalIntegrable
  exact (integral_eq_of_hasDerivAt_off_countable_of_le S P hab hD (re_cont hsand)
    (fun x hx => re_deriv hsand hx.1 (hDc x hx)) hint).symm


variable (V : PrivateValues)

/-- The density clamped to `[0, vbar]`: continuous and equal to `f` there. -/
noncomputable def reDens (x : ℝ) : ℝ := V.f (reClamp 0 V.vbar x)

lemma reDens_cont (hV : V.IsRegular) : Continuous (reDens V) :=
  hV.2.2.2.1.comp_continuous (reClamp_cont 0 V.vbar) (reClamp_mem hV.1.le)

lemma re_mu_eq (hV : V.IsRegular) :
    V.μ = (volume.restrict (Icc 0 V.vbar)).withDensity
      (fun x => ((Real.toNNReal (reDens V x) : NNReal) : ENNReal)) := by
  unfold PrivateValues.μ
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [reDens, reClamp_of_mem hx]
  rfl

lemma re_mu_integral (hV : V.IsRegular) (g : ℝ → ℝ) :
    ∫ x, g x ∂V.μ = ∫ x in Icc 0 V.vbar, V.f x * g x := by
  rw [re_mu_eq V hV, integral_withDensity_eq_integral_smul
    ((reDens_cont V hV).measurable.real_toNNReal)]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  simp only [reDens, reClamp_of_mem hx, NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (hV.2.2.2.2.1 x hx).le]

lemma re_Fderiv (hV : V.IsRegular) {x : ℝ} (hx : x ∈ Ioo 0 V.vbar) :
    HasDerivAt V.F (V.f x) x :=
  (hV.2.2.2.2.2 x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

lemma re_Fcont (hV : V.IsRegular) : ContinuousOn V.F (Icc 0 V.vbar) :=
  fun v hv => (hV.2.2.2.2.2 v hv).continuousWithinAt

lemma re_f_int (hV : V.IsRegular) : ∫ x in (0 : ℝ)..V.vbar, V.f x = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hV.1.le (re_Fcont V hV)
    (fun x hx => (re_Fderiv V hV hx).hasDerivWithinAt)
    (hV.2.2.2.1.mono (by rw [uIcc_of_le hV.1.le])).intervalIntegrable, hV.2.2.1, hV.2.1]
  ring

lemma re_prob (hV : V.IsRegular) : IsProbabilityMeasure V.μ := by
  constructor
  have hint : IntegrableOn V.f (Icc 0 V.vbar) := hV.2.2.2.1.integrableOn_Icc
  unfold PrivateValues.μ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_mem measurableSet_Icc).mono fun x hx => (hV.2.2.2.2.1 x hx).le),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hV.1.le, re_f_int V hV,
    ENNReal.ofReal_one]

lemma re_mu_ae (hV : V.IsRegular) : ∀ᵐ x ∂V.μ, x ∈ Icc 0 V.vbar :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

lemma re_joint_ae (hV : V.IsRegular) : ∀ᵐ v ∂V.joint, ∀ j, v j ∈ Icc 0 V.vbar := by
  have := re_prob V hV
  unfold PrivateValues.joint
  exact Measure.ae_pi_le_pi (Filter.eventually_pi fun _ => re_mu_ae V hV)

/-- Replacing coordinate `i` by an independent draw preserves the joint distribution. -/
lemma re_update_mp (hV : V.IsRegular) (i : Fin V.N) :
    MeasurePreserving (fun vw : (Fin V.N → ℝ) × ℝ => Function.update vw.1 i vw.2)
      (V.joint.prod V.μ) V.joint := by
  have := re_prob V hV
  refine ⟨measurable_update', (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun vw : (Fin V.N → ℝ) × ℝ => Function.update vw.1 i vw.2) ⁻¹' (univ.pi s) =
      (univ.pi (Function.update s i univ)) ×ˢ (s i) := by
    ext ⟨v, w⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp
        · have := h j
          rw [Function.update_of_ne hj] at this
          rw [Function.update_of_ne hj]
          exact this
      · have := h i
        rwa [Function.update_self] at this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; rwa [Function.update_self]
      · have := h1 j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]
        exact this
  rw [hpre, Measure.prod_prod]
  unfold PrivateValues.joint
  rw [Measure.pi_pi]
  have h1 : ∀ j, V.μ (Function.update s i univ j) =
      Function.update (fun j => V.μ (s j)) i (V.μ univ) j := fun j => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [h1]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), measure_univ, one_mul,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j => V.μ (s j)), mul_comm]

/-- Integrating out one coordinate: `E[g(v)] = E_w[E_v[g(v with v_i := w)]]`. -/
lemma re_marg (hV : V.IsRegular) (i : Fin V.N) (g : (Fin V.N → ℝ) → ℝ)
    (hg : Integrable g V.joint) :
    ∫ v, g v ∂V.joint = ∫ w, (∫ v, g (Function.update v i w) ∂V.joint) ∂V.μ := by
  have := re_prob V hV
  have : IsProbabilityMeasure V.joint := by unfold PrivateValues.joint; infer_instance
  have hmp := re_update_mp V hV i
  have e1 : ∫ v, g v ∂V.joint =
      ∫ x, g (Function.update x.1 i x.2) ∂(V.joint.prod V.μ) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [e1, integral_prod_symm]
  exact (hmp.integrable_comp hg.aestronglyMeasurable).mpr hg


/-! ### Revenue equivalence -/

variable {V}

/-- The incentive-compatibility sandwich for the expected surplus. -/
lemma re_sand (M : Mechanism V.N) (hic : IsIncentiveCompatible V M) (i : Fin V.N) :
    ∀ x ∈ Icc 0 V.vbar, ∀ y ∈ Icc 0 V.vbar,
      (y - x) * winProb V M i x ≤ expSurplus V M i y - expSurplus V M i x := by
  intro x hx y hy
  have h := hic i y hy x hx
  unfold expSurplus at h ⊢
  linarith

lemma re_sand_sub {P S : ℝ → ℝ} {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (y - x) * P x ≤ S y - S x) :
    ∀ x ∈ Icc a' b', ∀ y ∈ Icc a' b', (y - x) * P x ≤ S y - S x :=
  fun x hx y hy => hsand x ⟨ha.trans hx.1, hx.2.trans hb⟩ y ⟨ha.trans hy.1, hy.2.trans hb⟩

/-- The envelope identity (6.A.1). -/
lemma re_payment (hV : V.IsRegular) (M : Mechanism V.N) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) (i : Fin V.N) (w : ℝ) (hw : w ∈ Icc 0 V.vbar) :
    expPayment V M i w = w * winProb V M i w - ∫ s in (0 : ℝ)..w, winProb V M i s := by
  have h := re_ftc hw.1 (re_sand_sub le_rfl hw.2 (re_sand M hic i))
  rw [hzero i, sub_zero] at h
  rw [← h]
  unfold expSurplus
  ring

/-- Integration by parts: `∫₀^vbar (P (F − 1) + S f) = 0`. -/
lemma re_ibp (hV : V.IsRegular) (M : Mechanism V.N) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) (i : Fin V.N) :
    ∫ x in (0 : ℝ)..V.vbar, (winProb V M i x * (V.F x - 1) + expSurplus V M i x * V.f x) = 0 := by
  have hsand := re_sand M hic i
  obtain ⟨D, hD, hDc⟩ := re_countable hV.1.le (re_mono hsand)
  have hPint : IntervalIntegrable (winProb V M i) volume 0 V.vbar :=
    (re_mono hsand).mono (by rw [uIcc_of_le hV.1.le]) |>.intervalIntegrable
  have hSc := re_cont hsand
  have hFc := re_Fcont V hV
  have hint : IntervalIntegrable
      (fun x => winProb V M i x * (V.F x - 1) + expSurplus V M i x * V.f x) volume 0 V.vbar := by
    refine (hPint.mul_continuousOn ?_).add ?_
    · rw [uIcc_of_le hV.1.le]; exact hFc.sub continuousOn_const
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hV.1.le]; exact hSc.mul hV.2.2.2.1
  rw [integral_eq_of_hasDerivAt_off_countable_of_le
    (fun x => expSurplus V M i x * (V.F x - 1)) _ hV.1.le hD
    (hSc.mul (hFc.sub continuousOn_const))
    (fun x hx => (re_deriv hsand hx.1 (hDc x hx)).mul ((re_Fderiv V hV hx.1).sub_const 1)) hint]
  simp [hV.2.2.1, hV.2.1, hzero i]

/-- The expected payment of customer `i` equals the expected virtual surplus it generates. -/
lemma re_one (hV : V.IsRegular) (M : Mechanism V.N) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) (i : Fin V.N) :
    ∫ w in Icc 0 V.vbar, V.f w * expPayment V M i w =
      ∫ w in Icc 0 V.vbar, V.f w * (virtualValue V w * winProb V M i w) := by
  have hsand := re_sand M hic i
  have hPint : IntervalIntegrable (winProb V M i) volume 0 V.vbar :=
    (re_mono hsand).mono (by rw [uIcc_of_le hV.1.le]) |>.intervalIntegrable
  have hSc := re_cont hsand
  have hFc := re_Fcont V hV
  have hfc := hV.2.2.2.1
  have hRdef : ∀ w, expPayment V M i w = w * winProb V M i w - expSurplus V M i w := by
    intro w; unfold expSurplus; ring
  have hfJ : ContinuousOn (fun w => V.f w * virtualValue V w) (Icc 0 V.vbar) := by
    unfold virtualValue
    refine hfc.mul (continuousOn_id.sub ((continuousOn_const.sub hFc).div hfc ?_))
    intro x hx; exact (hV.2.2.2.2.1 x hx).ne'
  have i1 : IntervalIntegrable (fun w => V.f w * expPayment V M i w) volume 0 V.vbar := by
    have : (fun w => V.f w * expPayment V M i w) =
        fun w => (V.f w * w) * winProb V M i w - V.f w * expSurplus V M i w := by
      funext w; rw [hRdef]; ring
    rw [this]
    refine (hPint.continuousOn_mul ?_).sub ?_
    · rw [uIcc_of_le hV.1.le]; exact hfc.mul continuousOn_id
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hV.1.le]; exact hfc.mul hSc
  have i2 : IntervalIntegrable (fun w => V.f w * (virtualValue V w * winProb V M i w))
      volume 0 V.vbar := by
    have : (fun w => V.f w * (virtualValue V w * winProb V M i w)) =
        fun w => (V.f w * virtualValue V w) * winProb V M i w := by
      funext w; ring
    rw [this]
    refine hPint.continuousOn_mul ?_
    rw [uIcc_of_le hV.1.le]; exact hfJ
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hV.1.le, ← intervalIntegral.integral_of_le hV.1.le]
  have hdiff : ∫ x in (0 : ℝ)..V.vbar, (V.f x * expPayment V M i x -
      V.f x * (virtualValue V x * winProb V M i x)) =
      ∫ x in (0 : ℝ)..V.vbar, -(winProb V M i x * (V.F x - 1) + expSurplus V M i x * V.f x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hV.1.le] at hx
    have hf0 : V.f x ≠ 0 := (hV.2.2.2.2.1 x hx).ne'
    rw [hRdef]
    unfold virtualValue
    field_simp
    ring
  rw [intervalIntegral.integral_neg, re_ibp hV M hzero hic i, neg_zero,
    intervalIntegral.integral_sub i1 i2] at hdiff
  linarith

lemma re_payment_int (hV : V.IsRegular) (M : Mechanism V.N) {C : ℕ}
    (hM : M.IsFeasible C V.vbar) (i : Fin V.N) : Integrable (fun v => M.p v i) V.joint := by
  have := re_prob V hV
  have : IsProbabilityMeasure V.joint := by unfold PrivateValues.joint; infer_instance
  obtain ⟨K, hK⟩ := hM.2.2.2.2
  refine Integrable.of_bound (hM.2.2.2.1 i).aestronglyMeasurable K ?_
  filter_upwards [re_joint_ae V hV] with v hv
  rw [Real.norm_eq_abs]
  exact hK v hv i

lemma re_virtual_int (hV : V.IsRegular) (M : Mechanism V.N) {C : ℕ}
    (hM : M.IsFeasible C V.vbar) (i : Fin V.N) :
    Integrable (fun v => virtualValue V (v i) * M.y v i) V.joint := by
  have := re_prob V hV
  have : IsProbabilityMeasure V.joint := by unfold PrivateValues.joint; infer_instance
  have hfc := hV.2.2.2.1
  have hFc := re_Fcont V hV
  have hJc : ContinuousOn (virtualValue V) (Icc 0 V.vbar) := by
    unfold virtualValue
    refine continuousOn_id.sub ((continuousOn_const.sub hFc).div hfc ?_)
    intro x hx; exact (hV.2.2.2.2.1 x hx).ne'
  have hJt : Continuous (fun x => virtualValue V (reClamp 0 V.vbar x)) :=
    hJc.comp_continuous (reClamp_cont 0 V.vbar) (reClamp_mem hV.1.le)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hJc
  have hmeas : AEStronglyMeasurable (fun v => virtualValue V (v i) * M.y v i) V.joint := by
    refine (((hJt.measurable.comp (measurable_pi_apply i)).mul
      (hM.2.2.1 i)).aestronglyMeasurable).congr ?_
    filter_upwards [re_joint_ae V hV] with v hv
    simp only [Function.comp, Pi.mul_apply]
    rw [reClamp_of_mem (hv i)]
  refine Integrable.of_bound hmeas B ?_
  filter_upwards [re_joint_ae V hV] with v hv
  have h1 := hB (v i) (hv i)
  have h2 : |M.y v i| ≤ 1 := by
    rcases hM.1 v i with h | h <;> rw [h] <;> norm_num
  rw [Real.norm_eq_abs, abs_mul]
  rw [Real.norm_eq_abs] at h1
  calc |virtualValue V (v i)| * |M.y v i| ≤ B * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = B := mul_one B

theorem re_main (V : PrivateValues) (hV : V.IsRegular) (C : ℕ) (M : Mechanism V.N)
    (hM : M.IsFeasible C V.vbar) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) :
    expRevenue V M = ∫ v, ∑ i, virtualValue V (v i) * M.y v i ∂V.joint ∧
    ∀ i, ∀ w ∈ Set.Icc 0 V.vbar,
      expPayment V M i w = w * winProb V M i w - ∫ s in (0 : ℝ)..w, winProb V M i s := by
  refine ⟨?_, fun i w hw => re_payment hV M hzero hic i w hw⟩
  unfold expRevenue
  rw [integral_finsetSum _ fun i _ => re_payment_int hV M hM i,
    integral_finsetSum _ fun i _ => re_virtual_int hV M hM i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [re_marg V hV i _ (re_payment_int hV M hM i), re_marg V hV i _ (re_virtual_int hV M hM i)]
  have e1 : ∀ w, ∫ v, M.p (Function.update v i w) i ∂V.joint = expPayment V M i w :=
    fun w => rfl
  have e2 : ∀ w, ∫ v, virtualValue V (Function.update v i w i) *
      M.y (Function.update v i w) i ∂V.joint = virtualValue V w * winProb V M i w := by
    intro w
    simp only [Function.update_self]
    rw [integral_const_mul]
    rfl
  simp only [e1, e2]
  rw [re_mu_integral V hV, re_mu_integral V hV]
  exact re_one hV M hzero hic i

end RevenueManagement

open RevenueManagement

theorem solution (V : PrivateValues) (hV : V.IsRegular) (C : ℕ) (M : Mechanism V.N)
    (hM : M.IsFeasible C V.vbar) (hmono : HasMonotoneAllocation V M)
    (hzero : HasZeroSurplusAtZero V M) (hic : IsIncentiveCompatible V M) :
    expRevenue V M = ∫ v, ∑ i, virtualValue V (v i) * M.y v i ∂V.joint ∧
    ∀ i, ∀ w ∈ Set.Icc 0 V.vbar,
      expPayment V M i w = w * winProb V M i w - ∫ s in (0 : ℝ)..w, winProb V M i s :=
  re_main V hV C M hM hzero hic
