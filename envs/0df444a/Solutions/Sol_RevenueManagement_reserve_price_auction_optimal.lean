-- Prove2me | solution 1 for RevenueManagement.reserve_price_auction_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T00:10:47.354666+00:00
-- url     : https://prove2.me/submissions/fe99d085-c3b3-42d4-a034-ef9956216c4c

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

section RE
open MeasureTheory Set Filter Topology

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


end RE

section OA

open Classical Finset

section
variable {N : ℕ} (v : Fin N → ℝ)

/-- `j` is ahead of `i` in the second-price ranking. -/
def oaAhead (i j : Fin N) : Prop := v i < v j ∨ (v j = v i ∧ j < i)

/-- The rank of `i`: the number of customers ahead of it. -/
noncomputable def oaRank (i : Fin N) : ℕ := (univ.filter (fun j => oaAhead v i j)).card

lemma oa_irrefl (i : Fin N) : ¬ oaAhead v i i := by
  unfold oaAhead; rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma oa_trans {i j k : Fin N} (hij : oaAhead v i j) (hjk : oaAhead v j k) : oaAhead v i k := by
  unfold oaAhead at *
  rcases hij with h1 | ⟨h1, h1'⟩ <;> rcases hjk with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h2.trans h1, h2'.trans h1'⟩

lemma oa_total {i j : Fin N} (hne : i ≠ j) : oaAhead v i j ∨ oaAhead v j i := by
  unfold oaAhead
  rcases lt_trichotomy (v i) (v j) with h | h | h
  · left; left; exact h
  · rcases lt_or_gt_of_ne hne with h' | h'
    · right; right; exact ⟨h, h'⟩
    · left; right; exact ⟨h.symm, h'⟩
  · right; left; exact h

/-- If `j` is ahead of `i`, `j` has strictly smaller rank. -/
lemma oa_rank_lt {i j : Fin N} (h : oaAhead v i j) : oaRank v j < oaRank v i := by
  unfold oaRank
  apply card_lt_card
  refine ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact oa_trans v h hk
  · have := hsub (mem_filter.mpr ⟨mem_univ j, h⟩)
    simp only [mem_filter, mem_univ, true_and] at this
    exact oa_irrefl v j this

lemma oa_rank_inj : Function.Injective (oaRank v) := by
  intro i j hij
  by_contra hne
  rcases oa_total v hne with h | h
  · have := oa_rank_lt v h; omega
  · have := oa_rank_lt v h; omega

lemma oa_rank_lt_N (i : Fin N) : oaRank v i < N := by
  unfold oaRank
  calc (univ.filter (fun j => oaAhead v i j)).card < (univ : Finset (Fin N)).card := by
        apply card_lt_card
        refine ⟨subset_univ _, fun hsub => ?_⟩
        have := hsub (mem_univ i)
        simp only [mem_filter, mem_univ, true_and] at this
        exact oa_irrefl v i this
    _ = N := by simp

/-- Exactly `k` customers have rank below `k ≤ N`. -/
lemma oa_card_rank_lt {k : ℕ} (hk : k ≤ N) : (univ.filter (fun i => oaRank v i < k)).card = k := by
  have himg : univ.image (oaRank v) = range N := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨i, -, rfl⟩ := mem_image.mp hr
      exact mem_range.mpr (oa_rank_lt_N v i)
    · rw [card_image_of_injective _ (oa_rank_inj v)]; simp
  have : (univ.filter (fun i => oaRank v i < k)).image (oaRank v) = range k := by
    ext r
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hr
      have : r ∈ univ.image (oaRank v) := by rw [himg]; exact mem_range.mpr (by omega)
      obtain ⟨i, -, hi⟩ := mem_image.mp this
      exact ⟨i, hi ▸ hr, hi⟩
  rw [← card_image_of_injective _ (oa_rank_inj v), this, card_range]

end

lemma oa_spWins_iff {N C : ℕ} (r : ℝ) (v : Fin N → ℝ) (i : Fin N) :
    spWins N C r v i ↔ r < v i ∧ oaRank v i < C := by
  unfold spWins oaRank oaAhead
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by convert h2 using 2; ext j; simp⟩

/-- `∑_P a ≤ ∑_Q b` when `|P| ≤ |Q|`, every `a` is at most every `b`, and the `a`'s are `≥ 0`. -/
lemma oa_sum_exchange {ι : Type*} (P Q : Finset ι) (f : ι → ℝ) (hcard : P.card ≤ Q.card)
    (hle : ∀ i ∈ P, ∀ w ∈ Q, f i ≤ f w) (hnn : ∀ i ∈ P, 0 ≤ f i) (hQ : ∀ w ∈ Q, 0 ≤ f w) :
    ∑ i ∈ P, f i ≤ ∑ w ∈ Q, f w := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simpa using sum_nonneg hQ
  · obtain ⟨i0, hi0, hmax⟩ := exists_max_image P f hP
    calc ∑ i ∈ P, f i ≤ P.card • f i0 := sum_le_card_nsmul P f (f i0) hmax
      _ ≤ Q.card • f i0 := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hnn i0 hi0)
      _ ≤ ∑ w ∈ Q, f w := card_nsmul_le_sum Q f (f i0) (fun w hw => hle i0 hi0 w hw)

theorem oa_main (V : PrivateValues)
    (hJ : MonotoneOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) (v : Fin V.N → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc 0 V.vbar) (y : Fin V.N → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hC : ∑ i, y i ≤ C) :
    ∑ i, virtualValue V (v i) * y i ≤
      ∑ i, virtualValue V (v i) * (secondPriceReserve V.N C vstar).y v i := by
  set J := fun i => virtualValue V (v i) with hJdef
  -- signs of J
  have hJpos : ∀ i, vstar < v i → 0 ≤ J i := fun i h => by
    have := hJ hvs (hv i) h.le; simp only [hJdef]; linarith
  have hJneg : ∀ i, v i ≤ vstar → J i ≤ 0 := fun i h => by
    have := hJ (hv i) hvs h; simp only [hJdef]; linarith
  set Y := univ.filter (fun i => y i = 1) with hY
  set W := univ.filter (fun i => spWins V.N C vstar v i) with hW
  set Yp := Y.filter (fun i => vstar < v i) with hYp
  have hLHS : ∑ i, virtualValue V (v i) * y i = ∑ i ∈ Y, J i := by
    rw [hY, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    rcases hy i with h | h <;> simp [h, hJdef]
  have hRHS : ∑ i, virtualValue V (v i) * (secondPriceReserve V.N C vstar).y v i = ∑ i ∈ W, J i := by
    rw [hW, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    simp only [secondPriceReserve, hJdef]
    split_ifs <;> simp
  rw [hLHS, hRHS]
  -- drop the non-positive terms
  have hdrop : ∑ i ∈ Y, J i ≤ ∑ i ∈ Yp, J i := by
    rw [hYp, ← sum_filter_add_sum_filter_not Y (fun i => vstar < v i)]
    have : ∑ i ∈ Y.filter (fun i => ¬ vstar < v i), J i ≤ 0 :=
      sum_nonpos fun i hi => hJneg i (not_lt.mp (mem_filter.mp hi).2)
    linarith
  -- |Y| ≤ C
  have hYC : Y.card ≤ C := by
    have : ∑ i, y i = (Y.card : ℝ) := by
      rw [hY, card_filter, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      rcases hy i with h | h <;> simp [h]
    exact_mod_cast this ▸ hC
  -- winners beat every non-winner above the reserve
  have hbeat : ∀ i ∈ Yp \ W, ∀ w ∈ W, J i ≤ J w := by
    intro i hi w hw
    simp only [mem_sdiff, hYp, mem_filter, hW, mem_univ, true_and, oa_spWins_iff] at hi hw
    have hri : C ≤ oaRank v i := by by_contra h; exact hi.2 ⟨hi.1.2, by omega⟩
    have hne : i ≠ w := by rintro rfl; omega
    rcases oa_total v hne with h | h
    · -- w ahead of i: v i ≤ v w
      have hvle : v i ≤ v w := by rcases h with h | ⟨h, _⟩ <;> [exact h.le; exact h.ge]
      exact hJ (hv i) (hv w) hvle
    · have := oa_rank_lt v h; omega
  have hWpos : ∀ w ∈ W, 0 ≤ J w := fun w hw => by
    simp only [hW, mem_filter, mem_univ, true_and, oa_spWins_iff] at hw
    exact hJpos w hw.1
  have hYppos : ∀ i ∈ Yp \ W, 0 ≤ J i := fun i hi => by
    simp only [mem_sdiff, hYp, mem_filter] at hi
    exact hJpos i hi.1.2
  -- counting
  have hcount : (Yp \ W).card ≤ (W \ Yp).card := by
    rcases (Yp \ W).eq_empty_or_nonempty with h | ⟨i0, hi0⟩
    · rw [h]; simp
    · have hi0' := hi0
      simp only [mem_sdiff, hYp, mem_filter, hW, mem_univ, true_and, oa_spWins_iff] at hi0'
      have hri : C ≤ oaRank v i0 := by by_contra h; exact hi0'.2 ⟨hi0'.1.2, by omega⟩
      have hCN : C ≤ V.N := (hri.trans (oa_rank_lt_N v i0).le)
      have hWC : C ≤ W.card := by
        rw [← oa_card_rank_lt v hCN]
        apply card_le_card
        intro a ha
        simp only [mem_filter, mem_univ, true_and] at ha
        simp only [hW, mem_filter, mem_univ, true_and, oa_spWins_iff]
        refine ⟨?_, ha⟩
        have hne : a ≠ i0 := by rintro rfl; omega
        rcases oa_total v hne with h | h
        · have := oa_rank_lt v h; omega
        · have hvle : v i0 ≤ v a := by rcases h with h | ⟨h, _⟩ <;> [exact h.le; exact h.ge]
          linarith [hi0'.1.2]
      have h1 := card_sdiff_add_card_inter Yp W
      have h2 := card_sdiff_add_card_inter W Yp
      have hYpY : Yp.card ≤ Y.card := card_filter_le _ _
      rw [inter_comm] at h2
      omega
  -- assemble
  have hsplitY := sum_sdiff (s₁ := Yp ∩ W) (s₂ := Yp) (f := J) inter_subset_left
  have hsplitW := sum_sdiff (s₁ := Yp ∩ W) (s₂ := W) (f := J) inter_subset_right
  have hsd1 : Yp \ (Yp ∩ W) = Yp \ W := by ext; simp
  have hsd2 : W \ (Yp ∩ W) = W \ Yp := by ext; simp
  rw [hsd1] at hsplitY; rw [hsd2] at hsplitW
  have hex := oa_sum_exchange (Yp \ W) (W \ Yp) J hcount
    (fun i hi w hw => hbeat i hi w (mem_sdiff.mp hw).1) hYppos
    (fun w hw => hWpos w (mem_sdiff.mp hw).1)
  linarith



/-! ### The second-price auction with reserve: the combinatorics of one bidder's report -/

section sp
variable {N : ℕ}

/-- The number of other customers (not `i`) ahead of `j` in the ranking by `v`. -/
noncomputable def spA (v : Fin N → ℝ) (i j : Fin N) : ℕ :=
  ((univ.erase i).filter (fun k => oaAhead v j k)).card

lemma sp_rank_split (u : Fin N → ℝ) (i j : Fin N) :
    oaRank u j = ((univ.erase i).filter (fun k => oaAhead u j k)).card +
      (if oaAhead u j i then 1 else 0) := by
  unfold oaRank
  rw [card_filter, card_filter, ← sum_erase_add _ _ (mem_univ i)]

lemma sp_ahead_upd (v : Fin N → ℝ) (i : Fin N) (x : ℝ) {j k : Fin N} (hj : j ≠ i)
    (hk : k ≠ i) : oaAhead (Function.update v i x) j k ↔ oaAhead v j k := by
  simp only [oaAhead, Function.update_of_ne hj, Function.update_of_ne hk]

lemma sp_A_upd (v : Fin N → ℝ) (i : Fin N) (x : ℝ) {j : Fin N} (hj : j ≠ i) :
    ((univ.erase i).filter (fun k => oaAhead (Function.update v i x) j k)).card = spA v i j := by
  unfold spA
  congr 1
  exact filter_congr fun k hk => sp_ahead_upd v i x hj (ne_of_mem_erase hk)

/-- When `i` wins with report `x`, another customer wins iff it beats the reserve and fewer
than `C - 1` other customers (besides `i`) are ahead of it: independent of `x`. -/
lemma sp_other_win {C : ℕ} {r : ℝ} (v : Fin N → ℝ) (i : Fin N) (x : ℝ)
    (hwin : spWins N C r (Function.update v i x) i) {j : Fin N} (hj : j ≠ i) :
    spWins N C r (Function.update v i x) j ↔ (r < v j ∧ spA v i j + 1 < C) := by
  obtain ⟨hrx, hrank⟩ := (oa_spWins_iff r _ i).mp hwin
  rw [Function.update_self] at hrx
  rw [oa_spWins_iff, Function.update_of_ne hj, sp_rank_split _ i j, sp_A_upd v i x hj]
  by_cases h : oaAhead (Function.update v i x) j i
  · rw [if_pos h]
  · rw [if_neg h, add_zero]
    have hji : oaAhead (Function.update v i x) i j := (oa_total _ hj.symm).resolve_right h
    have hvj : x ≤ v j := by
      unfold oaAhead at hji
      rw [Function.update_self, Function.update_of_ne hj] at hji
      rcases hji with h1 | ⟨h1, -⟩
      · exact h1.le
      · exact h1.ge
    have hcard : spA v i j + 1 ≤ oaRank (Function.update v i x) i := by
      rw [sp_rank_split _ i i, if_neg (oa_irrefl _ i), add_zero]
      have hsub : insert j ((univ.erase i).filter (fun k => oaAhead v j k)) ⊆
          (univ.erase i).filter (fun k => oaAhead (Function.update v i x) i k) := by
        intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · exact mem_filter.mpr ⟨mem_erase.mpr ⟨hj, mem_univ _⟩, hji⟩
        · obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
          exact mem_filter.mpr ⟨hk1, oa_trans _ hji
            ((sp_ahead_upd v i x hj (ne_of_mem_erase hk1)).mpr hk2)⟩
      have hnot : j ∉ (univ.erase i).filter (fun k => oaAhead v j k) := by
        intro hm; exact oa_irrefl v j (mem_filter.mp hm).2
      have := card_le_card hsub
      rw [card_insert_of_notMem hnot] at this
      exact this
    constructor
    · rintro ⟨h1, -⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- The losers other than `i` when `i` wins. -/
def spLo (C : ℕ) (r : ℝ) (v : Fin N → ℝ) (i : Fin N) : Set (Fin N) :=
  {j | j ≠ i ∧ ¬ (r < v j ∧ spA v i j + 1 < C)}

/-- The critical price of customer `i`. -/
noncomputable def spTau (C : ℕ) (r : ℝ) (v : Fin N → ℝ) (i : Fin N) : ℝ :=
  max r (sSup ((fun j => v j) '' spLo C r v i))

lemma sp_losers_eq {C : ℕ} {r : ℝ} (v : Fin N → ℝ) (i : Fin N) (x : ℝ)
    (hwin : spWins N C r (Function.update v i x) i) :
    (Set.range fun j : {j // ¬ spWins N C r (Function.update v i x) j} =>
      Function.update v i x j) = (fun j => v j) '' spLo C r v i := by
  ext y
  simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop, spLo, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hji : j ≠ i := by rintro rfl; exact hj hwin
    refine ⟨j, ⟨hji, fun h => hj ((sp_other_win v i x hwin hji).mpr h)⟩, ?_⟩
    rw [Function.update_of_ne hji]
  · rintro ⟨j, ⟨hji, hj⟩, rfl⟩
    refine ⟨j, fun h => hj ((sp_other_win v i x hwin hji).mp h), ?_⟩
    rw [Function.update_of_ne hji]

/-- Claim A: a winning customer pays the critical price. -/
lemma sp_pay_eq {C : ℕ} {r : ℝ} (v : Fin N → ℝ) (i : Fin N) (x : ℝ)
    (hwin : spWins N C r (Function.update v i x) i) :
    (secondPriceReserve N C r).p (Function.update v i x) i = spTau C r v i := by
  simp only [secondPriceReserve, if_pos hwin]
  rw [sp_losers_eq v i x hwin]
  rfl

lemma sp_lo_le {C : ℕ} {r : ℝ} (v : Fin N → ℝ) (i : Fin N) {j : Fin N}
    (hj : j ∈ spLo C r v i) : v j ≤ sSup ((fun j => v j) '' spLo C r v i) :=
  le_csSup ((Set.toFinite _).image _ |>.bddAbove) ⟨j, hj, rfl⟩

/-- Claim B: a winning report is at least the critical price. -/
lemma sp_tau_le {C : ℕ} {r : ℝ} (hr : 0 ≤ r) (v : Fin N → ℝ) (i : Fin N) (x : ℝ)
    (hwin : spWins N C r (Function.update v i x) i) : spTau C r v i ≤ x := by
  have hrx : r < x := by
    have := hwin.1; rwa [Function.update_self] at this
  refine max_le hrx.le ?_
  rcases (spLo C r v i).eq_empty_or_nonempty with he | hne
  · rw [he, Set.image_empty, Real.sSup_empty]; linarith
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨j, hj, rfl⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨hji, hjl⟩ := hj
    -- `j` is ahead of `i`, hence it wins
    have hahead : oaAhead (Function.update v i x) i j := by
      left; rw [Function.update_self, Function.update_of_ne hji]; exact hlt
    have hwj : spWins N C r (Function.update v i x) j := by
      rw [oa_spWins_iff, Function.update_of_ne hji]
      refine ⟨by linarith, ?_⟩
      have hr1 : oaRank (Function.update v i x) j < oaRank (Function.update v i x) i :=
        oa_rank_lt _ hahead
      have := ((oa_spWins_iff r _ i).mp hwin).2
      omega
    exact hjl ((sp_other_win v i x hwin hji).mp hwj)

/-- The customers other than `i` that win whenever `i` wins: at most `C - 1` of them. -/
lemma sp_card_wo {C : ℕ} {r : ℝ} (v : Fin N → ℝ) (i : Fin N) :
    ((univ.erase i).filter (fun k => r < v k ∧ spA v i k + 1 < C)).card + 1 ≤ max C 1 := by
  set Wo := (univ.erase i).filter (fun k => r < v k ∧ spA v i k + 1 < C) with hWo
  rcases Wo.eq_empty_or_nonempty with he | hne
  · rw [he, card_empty]; exact le_max_right _ _
  obtain ⟨k, hk, hmax⟩ := exists_max_image Wo (oaRank v) hne
  have hk' := mem_filter.mp hk
  have hsub : Wo.erase k ⊆ (univ.erase i).filter (fun k' => oaAhead v k k') := by
    intro k' hk'
    obtain ⟨hne', hk'W⟩ := mem_erase.mp hk'
    obtain ⟨hk'1, -⟩ := mem_filter.mp hk'W
    refine mem_filter.mpr ⟨hk'1, ?_⟩
    rcases oa_total v hne'.symm with h | h
    · exact h
    · have := oa_rank_lt v h
      have := hmax k' hk'W
      omega
  have h1 := card_le_card hsub
  rw [card_erase_of_mem hk] at h1
  have h2 : Wo.card ≥ 1 := card_pos.mpr hne
  have h3 := hk'.2.2
  unfold spA at h3
  omega

/-- Claim C: a report above the critical price wins (for `C ≥ 1`). -/
lemma sp_win_of_lt {C : ℕ} (hC : 1 ≤ C) {r : ℝ} (v : Fin N → ℝ) (i : Fin N) (x : ℝ)
    (hx : spTau C r v i < x) : spWins N C r (Function.update v i x) i := by
  have hrx : r < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hsx : sSup ((fun j => v j) '' spLo C r v i) < x := lt_of_le_of_lt (le_max_right _ _) hx
  rw [oa_spWins_iff, Function.update_self]
  refine ⟨hrx, ?_⟩
  rw [sp_rank_split _ i i, if_neg (oa_irrefl _ i), add_zero]
  have hsub : (univ.erase i).filter (fun k => oaAhead (Function.update v i x) i k) ⊆
      (univ.erase i).filter (fun k => r < v k ∧ spA v i k + 1 < C) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
    have hki := ne_of_mem_erase hk1
    have hvk : x ≤ v k := by
      unfold oaAhead at hk2
      rw [Function.update_self, Function.update_of_ne hki] at hk2
      rcases hk2 with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    refine mem_filter.mpr ⟨hk1, ?_⟩
    by_contra hnot
    have := sp_lo_le v i (show k ∈ spLo C r v i from ⟨hki, hnot⟩)
    linarith
  have h1 := card_le_card hsub
  have h2 := sp_card_wo (C := C) (r := r) v i
  rw [max_eq_left hC] at h2
  omega

/-- Pointwise incentive compatibility (for `C ≥ 1` and `0 ≤ r`). -/
lemma sp_pointwise {C : ℕ} (hC : 1 ≤ C) {r : ℝ} (hr : 0 ≤ r) (v : Fin N → ℝ) (i : Fin N)
    (w w' : ℝ) :
    w * (secondPriceReserve N C r).y (Function.update v i w') i -
        (secondPriceReserve N C r).p (Function.update v i w') i ≤
      w * (secondPriceReserve N C r).y (Function.update v i w) i -
        (secondPriceReserve N C r).p (Function.update v i w) i := by
  have hu : ∀ x, w * (secondPriceReserve N C r).y (Function.update v i x) i -
      (secondPriceReserve N C r).p (Function.update v i x) i =
      if spWins N C r (Function.update v i x) i then w - spTau C r v i else 0 := by
    intro x
    by_cases h : spWins N C r (Function.update v i x) i
    · rw [if_pos h, sp_pay_eq v i x h]
      simp only [secondPriceReserve, if_pos h]
      ring
    · simp only [secondPriceReserve, if_neg h]
      ring
  rw [hu, hu]
  by_cases h' : spWins N C r (Function.update v i w') i
  · rw [if_pos h']
    by_cases h : spWins N C r (Function.update v i w) i
    · rw [if_pos h]
    · rw [if_neg h]
      have : ¬ spTau C r v i < w := fun hlt => h (sp_win_of_lt hC v i w hlt)
      linarith
  · rw [if_neg h']
    by_cases h : spWins N C r (Function.update v i w) i
    · rw [if_pos h]
      have := sp_tau_le hr v i w h
      linarith
    · rw [if_neg h]

end sp


/-! ### Properties of the second-price auction with reserve -/

section spr
open MeasureTheory

variable {N : ℕ} {V : PrivateValues}

lemma spr_y01 (C : ℕ) (r : ℝ) (v : Fin N → ℝ) (i : Fin N) :
    (secondPriceReserve N C r).y v i = 0 ∨ (secondPriceReserve N C r).y v i = 1 := by
  simp only [secondPriceReserve]; split_ifs <;> simp

lemma spr_sum_le (C : ℕ) (r : ℝ) (v : Fin N → ℝ) :
    ∑ i, (secondPriceReserve N C r).y v i ≤ C := by
  have e : ∑ i, (secondPriceReserve N C r).y v i =
      ((univ.filter fun i => spWins N C r v i).card : ℝ) := by
    simp only [secondPriceReserve]
    rw [sum_boole]
  rw [e]
  have : (univ.filter fun i => spWins N C r v i).card ≤ (range C).card := by
    refine card_le_card_of_injOn (oaRank v) (fun i hi => ?_) (fun i _ j _ h => oa_rank_inj v h)
    exact mem_range.mpr ((oa_spWins_iff r v i).mp (mem_filter.mp hi).2).2
  rw [card_range] at this
  exact_mod_cast this

lemma spr_ahead_meas (i j : Fin N) : MeasurableSet {v : Fin N → ℝ | oaAhead v i j} := by
  have : {v : Fin N → ℝ | oaAhead v i j} =
      {v | v i < v j} ∪ ({v | v j = v i} ∩ {_v | j < i}) := by
    ext v; simp [oaAhead]
  rw [this]
  exact (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)).union
    ((measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply i)).inter
      (MeasurableSet.const _))

lemma spr_win_meas (C : ℕ) (r : ℝ) (i : Fin N) :
    MeasurableSet {v : Fin N → ℝ | spWins N C r v i} := by
  have hsum : Measurable (fun v : Fin N → ℝ => ∑ j, if oaAhead v i j then (1 : ℝ) else 0) :=
    Finset.measurable_fun_sum _ fun j _ =>
      Measurable.ite (spr_ahead_meas i j) measurable_const measurable_const
  have hr : ∀ v : Fin N → ℝ, (∑ j, if oaAhead v i j then (1 : ℝ) else 0) = (oaRank v i : ℝ) := by
    intro v; rw [sum_boole]; rfl
  have : {v : Fin N → ℝ | spWins N C r v i} =
      {v | r < v i} ∩ {v | (∑ j, if oaAhead v i j then (1 : ℝ) else 0) < C} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hr, oa_spWins_iff, Nat.cast_lt]
  rw [this]
  exact (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_lt hsum measurable_const)

lemma spr_loserSup_eq (C : ℕ) (r : ℝ) (v : Fin N → ℝ) :
    sSup (Set.range fun j : {j // ¬ spWins N C r v j} => v j) =
      ∑ L ∈ (univ : Finset (Fin N)).powerset,
        if univ.filter (fun j => ¬ spWins N C r v j) = L then
          sSup ((fun j => v j) '' (L : Set (Fin N))) else 0 := by
  rw [sum_ite_eq, if_pos (mem_powerset.mpr (subset_univ _))]
  congr 1
  ext y
  simp

lemma spr_sup_meas (L : Finset (Fin N)) :
    Measurable (fun v : Fin N → ℝ => sSup ((fun j => v j) '' (L : Set (Fin N)))) := by
  rcases L.eq_empty_or_nonempty with rfl | hL
  · simp
  · have : (fun v : Fin N → ℝ => sSup ((fun j => v j) '' (L : Set (Fin N)))) =
        L.sup' hL (fun j v => v j) := by
      funext v
      rw [Finset.sup'_apply, Finset.sup'_eq_csSup_image]
    rw [this]
    exact Finset.measurable_sup' hL fun j _ => measurable_pi_apply j

lemma spr_p_meas (C : ℕ) (r : ℝ) (i : Fin N) :
    Measurable (fun v => (secondPriceReserve N C r).p v i) := by
  have hh : Measurable (fun v : Fin N → ℝ =>
      sSup (Set.range fun j : {j // ¬ spWins N C r v j} => v j)) := by
    have e : (fun v : Fin N → ℝ => sSup (Set.range fun j : {j // ¬ spWins N C r v j} => v j)) =
        fun v => ∑ L ∈ (univ : Finset (Fin N)).powerset,
          if univ.filter (fun j => ¬ spWins N C r v j) = L then
            sSup ((fun j => v j) '' (L : Set (Fin N))) else 0 :=
      funext (spr_loserSup_eq C r)
    rw [e]
    refine Finset.measurable_fun_sum _ fun L _ => Measurable.ite ?_ (spr_sup_meas L) measurable_const
    have : {v : Fin N → ℝ | univ.filter (fun j => ¬ spWins N C r v j) = L} =
        ⋂ j, {v | (¬ spWins N C r v j) ↔ j ∈ L} := by
      ext v; simp [Finset.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hj : j ∈ L
    · simp only [hj, iff_true]; exact (spr_win_meas C r j).compl
    · simp only [hj, iff_false, not_not]; exact spr_win_meas C r j
  show Measurable (fun v => if spWins N C r v i then
    max r (sSup (Set.range fun j : {j // ¬ spWins N C r v j} => v j)) else 0)
  exact Measurable.ite (spr_win_meas C r i) (measurable_const.max hh) measurable_const

lemma spr_p_bound (C : ℕ) {r vbar : ℝ} (hr0 : 0 ≤ r) (hrv : r ≤ vbar) (v : Fin N → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 vbar) (i : Fin N) :
    |(secondPriceReserve N C r).p v i| ≤ vbar := by
  simp only [secondPriceReserve]
  split_ifs with h
  · have hS : sSup (Set.range fun j : {j // ¬ spWins N C r v j} => v j) ≤ vbar := by
      rcases (Set.range fun j : {j // ¬ spWins N C r v j} => v j).eq_empty_or_nonempty with he | hne
      · rw [he, Real.sSup_empty]; linarith
      · exact csSup_le hne (by rintro _ ⟨j, rfl⟩; exact (hv j).2)
    rw [abs_of_nonneg (le_max_of_le_left hr0)]
    exact max_le hrv hS
  · simp only [abs_zero]; linarith

lemma spr_feasible (hV : V.IsRegular) (C : ℕ) {vstar : ℝ} (hvs : vstar ∈ Set.Icc 0 V.vbar) :
    (secondPriceReserve V.N C vstar).IsFeasible C V.vbar :=
  ⟨fun v i => spr_y01 C vstar v i, fun v => spr_sum_le C vstar v,
    fun i => (show Measurable (fun v => if spWins V.N C vstar v i then (1 : ℝ) else 0) from
      Measurable.ite (spr_win_meas C vstar i) measurable_const measurable_const),
    fun i => spr_p_meas C vstar i, V.vbar, fun v hv i => spr_p_bound C hvs.1 hvs.2 v hv i⟩

lemma spr_mono (C : ℕ) {vstar : ℝ} :
    HasMonotoneAllocation V (secondPriceReserve V.N C vstar) := by
  intro i v w _ w' _ hle
  show (if spWins V.N C vstar (Function.update v i w) i then (1 : ℝ) else 0) ≤
    (if spWins V.N C vstar (Function.update v i w') i then (1 : ℝ) else 0)
  by_cases h : spWins V.N C vstar (Function.update v i w) i
  · have h' : spWins V.N C vstar (Function.update v i w') i := by
      rw [oa_spWins_iff] at h ⊢
      rw [Function.update_self] at h ⊢
      refine ⟨lt_of_lt_of_le h.1 hle, lt_of_le_of_lt ?_ h.2⟩
      unfold oaRank
      apply card_le_card
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      have hki : k ≠ i := by rintro rfl; exact oa_irrefl _ k hk
      unfold oaAhead at hk ⊢
      rw [Function.update_self, Function.update_of_ne hki] at hk ⊢
      rcases hk with hk | ⟨hk1, hk2⟩
      · left; linarith
      · rcases hle.lt_or_eq with hlt | heq
        · left; linarith
        · right; exact ⟨by rw [hk1, heq], hk2⟩
    rw [if_pos h, if_pos h']
  · rw [if_neg h]; split_ifs <;> norm_num

lemma spr_zero (C : ℕ) {vstar : ℝ} (hvs0 : 0 ≤ vstar) :
    HasZeroSurplusAtZero V (secondPriceReserve V.N C vstar) := by
  intro i
  unfold expSurplus expPayment
  have hp : ∀ v : Fin V.N → ℝ,
      (secondPriceReserve V.N C vstar).p (Function.update v i 0) i = 0 := by
    intro v
    have hnw : ¬ spWins V.N C vstar (Function.update v i 0) i := fun h => by
      have := h.1; rw [Function.update_self] at this; linarith
    simp only [secondPriceReserve, if_neg hnw]
  simp only [hp, integral_zero]; ring

lemma spr_ic (hV : V.IsRegular) (C : ℕ) {vstar : ℝ} (hvs : vstar ∈ Set.Icc 0 V.vbar) :
    IsIncentiveCompatible V (secondPriceReserve V.N C vstar) := by
  have := re_prob V hV
  have hJp : IsProbabilityMeasure V.joint := by unfold PrivateValues.joint; infer_instance
  have hfeas := spr_feasible hV C hvs
  intro i w hw w' hw'
  unfold expSurplus winProb expPayment
  rcases Nat.eq_zero_or_pos C with hC0 | hCpos
  · subst hC0
    have hno : ∀ u : Fin V.N → ℝ, ∀ j, ¬ spWins V.N 0 vstar u j :=
      fun u j h => Nat.not_lt_zero _ h.2
    simp [secondPriceReserve, hno]
  · have hyi : ∀ x, Integrable
        (fun v => (secondPriceReserve V.N C vstar).y (Function.update v i x) i) V.joint :=
      fun x => Integrable.of_bound ((hfeas.2.2.1 i).comp measurable_update_left).aestronglyMeasurable
        1 (ae_of_all _ fun v => by
          rcases spr_y01 C vstar (Function.update v i x) i with h | h <;> simp [h])
    have hpi : ∀ x ∈ Set.Icc 0 V.vbar, Integrable
        (fun v => (secondPriceReserve V.N C vstar).p (Function.update v i x) i) V.joint :=
      fun x hx => Integrable.of_bound
        ((hfeas.2.2.2.1 i).comp measurable_update_left).aestronglyMeasurable V.vbar (by
          filter_upwards [re_joint_ae V hV] with v hv
          rw [Real.norm_eq_abs]
          refine spr_p_bound C hvs.1 hvs.2 _ (fun j => ?_) i
          by_cases hj : j = i
          · subst hj; rw [Function.update_self]; exact hx
          · rw [Function.update_of_ne hj]; exact hv j)
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((hyi w').const_mul w) (hpi w' hw'),
      ← integral_sub ((hyi w).const_mul w) (hpi w hw)]
    exact integral_mono (((hyi w').const_mul w).sub (hpi w' hw'))
      (((hyi w).const_mul w).sub (hpi w hw)) fun v => sp_pointwise hCpos hvs.1 v i w w'

theorem spr_main (V : PrivateValues) (hV : V.IsRegular)
    (hJ : StrictMonoOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) :
    ((secondPriceReserve V.N C vstar).IsFeasible C V.vbar ∧
      HasMonotoneAllocation V (secondPriceReserve V.N C vstar) ∧
      HasZeroSurplusAtZero V (secondPriceReserve V.N C vstar) ∧
      IsIncentiveCompatible V (secondPriceReserve V.N C vstar)) ∧
    ∀ M : Mechanism V.N, M.IsFeasible C V.vbar → HasMonotoneAllocation V M →
      HasZeroSurplusAtZero V M → IsIncentiveCompatible V M →
      expRevenue V M ≤ expRevenue V (secondPriceReserve V.N C vstar) := by
  have hf := spr_feasible hV C hvs
  have hz := spr_zero (V := V) C hvs.1
  have hi := spr_ic hV C hvs
  refine ⟨⟨hf, spr_mono C, hz, hi⟩, fun M hM _ hzM hicM => ?_⟩
  rw [(re_main V hV C M hM hzM hicM).1, (re_main V hV C _ hf hz hi).1]
  refine integral_mono_ae (integrable_finsetSum _ fun i _ => re_virtual_int hV M hM i)
    (integrable_finsetSum _ fun i _ => re_virtual_int hV _ hf i) ?_
  filter_upwards [re_joint_ae V hV] with v hv
  exact oa_main V hJ.monotoneOn C vstar hvs hJ0 v hv (fun i => M.y v i) (hM.1 v) (hM.2.1 v)

end spr

end OA

end RevenueManagement

open RevenueManagement

theorem solution (V : PrivateValues) (hV : V.IsRegular)
    (hJ : StrictMonoOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) :
    ((secondPriceReserve V.N C vstar).IsFeasible C V.vbar ∧
      HasMonotoneAllocation V (secondPriceReserve V.N C vstar) ∧
      HasZeroSurplusAtZero V (secondPriceReserve V.N C vstar) ∧
      IsIncentiveCompatible V (secondPriceReserve V.N C vstar)) ∧
    ∀ M : Mechanism V.N, M.IsFeasible C V.vbar → HasMonotoneAllocation V M →
      HasZeroSurplusAtZero V M → IsIncentiveCompatible V M →
      expRevenue V M ≤ expRevenue V (secondPriceReserve V.N C vstar) :=
  spr_main V hV hJ C vstar hvs hJ0
