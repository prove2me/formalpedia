-- Prove2me | solution 1 for UnifiedFBSDE.Cubic.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T19:08:01.0622+00:00
-- url     : https://prove2.me/submissions/9ee17bb1-5ab4-43d9-be70-59e052207f92

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

open Set

namespace RRAux_UnifiedFBSDE_Cubic_theorem_5_3

def cub (A0 A1 A2 A3 u : ℝ) : ℝ := A0 + A1 * u + A2 * u ^ 2 + A3 * u ^ 3

lemma cub_cont (A0 A1 A2 A3 : ℝ) : Continuous (cub A0 A1 A2 A3) := by
  unfold cub; fun_prop

lemma cub_lip (A0 A1 A2 A3 R u v : ℝ) (hu : |u| ≤ R) (hv : |v| ≤ R) :
    |cub A0 A1 A2 A3 u - cub A0 A1 A2 A3 v|
      ≤ (|A1| + 2 * |A2| * R + 3 * |A3| * R ^ 2) * |u - v| := by
  have e : cub A0 A1 A2 A3 u - cub A0 A1 A2 A3 v
      = (A1 + A2 * (u + v) + A3 * (u ^ 2 + u * v + v ^ 2)) * (u - v) := by
    unfold cub; ring
  rw [e, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hR : 0 ≤ R := (abs_nonneg u).trans hu
  have h1 : |u + v| ≤ 2 * R := by
    have := abs_add_le u v; linarith
  have h2 : |u ^ 2 + u * v + v ^ 2| ≤ 3 * R ^ 2 := by
    have a1 : |u ^ 2| ≤ R ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have a2 : |v ^ 2| ≤ R ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
    have a3 : |u * v| ≤ R ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul hu hv (abs_nonneg _) hR
    have := abs_add_le (u ^ 2 + u * v) (v ^ 2)
    have := abs_add_le (u ^ 2) (u * v)
    linarith
  calc |A1 + A2 * (u + v) + A3 * (u ^ 2 + u * v + v ^ 2)|
      ≤ |A1| + |A2| * |u + v| + |A3| * |u ^ 2 + u * v + v ^ 2| := by
        have := abs_add_le (A1 + A2 * (u + v)) (A3 * (u ^ 2 + u * v + v ^ 2))
        have := abs_add_le A1 (A2 * (u + v))
        simp only [abs_mul] at *
        linarith
    _ ≤ |A1| + |A2| * (2 * R) + |A3| * (3 * R ^ 2) := by
        gcongr
    _ = |A1| + 2 * |A2| * R + 3 * |A3| * R ^ 2 := by ring

lemma cub_bound (A0 A1 A2 A3 R u : ℝ) (hu : |u| ≤ R) :
    |cub A0 A1 A2 A3 u| ≤ |A0| + |A1| * R + |A2| * R ^ 2 + |A3| * R ^ 3 := by
  unfold cub
  have hR : 0 ≤ R := (abs_nonneg u).trans hu
  have b2 : |u ^ 2| ≤ R ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  have b3 : |u ^ 3| ≤ R ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hu 3
  calc |A0 + A1 * u + A2 * u ^ 2 + A3 * u ^ 3|
      ≤ |A0| + |A1| * |u| + |A2| * |u ^ 2| + |A3| * |u ^ 3| := by
        have := abs_add_le (A0 + A1 * u + A2 * u ^ 2) (A3 * u ^ 3)
        have := abs_add_le (A0 + A1 * u) (A2 * u ^ 2)
        have := abs_add_le A0 (A1 * u)
        simp only [abs_mul] at *
        linarith
    _ ≤ |A0| + |A1| * R + |A2| * R ^ 2 + |A3| * R ^ 3 := by gcongr

/-- From a derivative description on `[0, T]` to a bounded solution of the integral equation. -/
lemma bridge (p : ℝ → ℝ) (hp : Continuous p) (h T : ℝ) (y : ℝ → ℝ)
    (hyT : y T = h) (hy : ∀ s ∈ Icc 0 T, HasDerivAt y (-(p (y s))) s) :
    UnifiedFBSDE.Cubic.IsBoundedSolution (fun _ v => p v) h T y := by
  have ycont : ContinuousOn y (Icc 0 T) := fun s hs => (hy s hs).continuousAt.continuousWithinAt
  have pycont : ContinuousOn (fun s => p (y s)) (Icc 0 T) := hp.comp_continuousOn ycont
  refine ⟨fun t ht => ⟨?_, ?_⟩, ?_⟩
  · exact (pycont.mono (Icc_subset_Icc ht.1 le_rfl)).integrableOn_Icc
  · have hsub : uIcc t T ⊆ Icc 0 T := by
      rw [uIcc_of_le ht.2]; exact Icc_subset_Icc ht.1 le_rfl
    have hint : IntervalIntegrable (fun s => -(p (y s))) MeasureTheory.volume t T :=
      ((pycont.mono hsub).neg).intervalIntegrable
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hy x (hsub hx)) hint
    rw [intervalIntegral.integral_neg, hyT] at this
    simp only
    linarith
  · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ycont
    exact ⟨C, fun t ht => by simpa [Real.norm_eq_abs] using hC t ht⟩

lemma exists_global (G : ℝ → ℝ) (K M : NNReal) (hG : LipschitzWith K G) (hb : ∀ x, |G x| ≤ M)
    (h T : ℝ) (hT : 0 < T) :
    ∃ z : ℝ → ℝ, Continuous z ∧ ∀ t ∈ Icc 0 T, z t = h + ∫ τ in (0 : ℝ)..t, G (z τ) := by
  have hf : IsPicardLindelof (fun _ => G) (tmin := 0) (tmax := T) ⟨0, ⟨le_rfl, hT.le⟩⟩ h
      (M * T.toNNReal) 0 M K := by
    apply IsPicardLindelof.of_time_independent
    · intro x _; simpa [Real.norm_eq_abs] using hb x
    · exact hG.lipschitzOnWith
    · simp [Real.coe_toNNReal _ hT.le, hT.le]
  have hx : h ∈ Metric.closedBall h ((0 : NNReal) : ℝ) := by simp
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨(ODE.FunSpace.next hf hx α).compProj, ODE.FunSpace.continuous_compProj _, fun t ht => ?_⟩
  have := ODE.FunSpace.compProj_apply (α := ODE.FunSpace.next hf hx α) (t := t)
  rw [this, ODE.FunSpace.next_apply, hα, projIcc_of_mem _ ht]
  rfl

lemma le_of_eps (u v τ : ℝ) (hτ : 0 ≤ τ) (h : ∀ ε : ℝ, 0 < ε → u ≤ v + ε * (1 + τ)) : u ≤ v := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h1 : 0 < 1 + τ := by linarith
  have := h (ε / (1 + τ)) (div_pos hε h1)
  rwa [div_mul_cancel₀ _ h1.ne'] at this

lemma exist_clamp (A0 A1 A2 A3 a b h T : ℝ) (hab : a ≤ b) (hah : a ≤ h) (hhb : h ≤ b)
    (hFa : 0 ≤ cub A0 A1 A2 A3 a) (hFb : cub A0 A1 A2 A3 b ≤ 0) (hT : 0 < T) :
    ∃ y : ℝ → ℝ, UnifiedFBSDE.Cubic.IsBoundedSolution (fun _ v => cub A0 A1 A2 A3 v) h T y := by
  set p := cub A0 A1 A2 A3 with hpdef
  let cl : ℝ → ℝ := fun x => (projIcc a b hab x : ℝ)
  let G : ℝ → ℝ := fun x => p (cl x)
  set R := |a| + |b| with hR
  have hclR : ∀ x, |cl x| ≤ R := by
    intro x
    have h1 := (projIcc a b hab x).2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b, h1.1, h1.2]
  set KF := |A1| + 2 * |A2| * R + 3 * |A3| * R ^ 2 with hKF
  set MF := |A0| + |A1| * R + |A2| * R ^ 2 + |A3| * R ^ 3 with hMF
  have hR0 : 0 ≤ R := by positivity
  have hKF0 : 0 ≤ KF := by positivity
  have hMF0 : 0 ≤ MF := by positivity
  have hGl : LipschitzWith KF.toNNReal G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hKF0]
    have h1 := cub_lip A0 A1 A2 A3 R (cl x) (cl y) (hclR x) (hclR y)
    have h2 : |cl x - cl y| ≤ |x - y| := by
      have := (LipschitzWith.projIcc hab).dist_le_mul x y
      rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq] at this
      simpa using this
    calc |G x - G y| ≤ KF * |cl x - cl y| := h1
      _ ≤ KF * |x - y| := mul_le_mul_of_nonneg_left h2 hKF0
  have hGb : ∀ x, |G x| ≤ MF.toNNReal := by
    intro x
    rw [Real.coe_toNNReal _ hMF0]
    exact cub_bound A0 A1 A2 A3 R (cl x) (hclR x)
  have hGc : Continuous G := hGl.continuous
  obtain ⟨z, hzc, hz⟩ := exists_global G _ _ hGl hGb h T hT
  let w : ℝ → ℝ := fun τ => h + ∫ σ in (0 : ℝ)..τ, G (z σ)
  have hw : ∀ τ, HasDerivAt w (G (z τ)) τ := fun τ =>
    ((hGc.comp hzc).integral_hasStrictDerivAt 0 τ).hasDerivAt.const_add h
  have hwc : Continuous w := continuous_iff_continuousAt.mpr (fun τ => (hw τ).continuousAt)
  have hwz : ∀ τ ∈ Icc 0 T, z τ = w τ := fun τ hτ => hz τ hτ
  have hw0 : w 0 = h := by simp [w]
  -- invariance
  have hup : ∀ τ ∈ Icc 0 T, w τ ≤ b := by
    intro τ hτ
    apply le_of_eps _ _ τ hτ.1
    intro ε hε
    refine image_le_of_deriv_right_lt_deriv_boundary' (f := w) (f' := fun x => G (z x))
      (B := fun x => b + ε * (1 + x)) (B' := fun _ => ε) hwc.continuousOn
      (fun x _ => (hw x).hasDerivWithinAt) ?_ (by fun_prop) ?_ ?_ hτ
    · rw [hw0]; nlinarith
    · intro x _
      have : HasDerivAt (fun x => b + ε * (1 + x)) ε x := by
        simpa using (((hasDerivAt_id x).const_add 1).const_mul ε).const_add b
      exact this.hasDerivWithinAt
    · intro x hx hxB
      have hzx : b ≤ z x := by
        rw [hwz x (Ico_subset_Icc_self hx), hxB]; nlinarith [hx.1]
      show p (cl (z x)) < ε
      simp only [cl, projIcc_of_right_le hab hzx]
      linarith
  have hlow : ∀ τ ∈ Icc 0 T, a ≤ w τ := by
    intro τ hτ
    have : -w τ ≤ -a := by
      apply le_of_eps _ _ τ hτ.1
      intro ε hε
      refine image_le_of_deriv_right_lt_deriv_boundary' (f := fun x => -w x)
        (f' := fun x => -G (z x)) (B := fun x => -a + ε * (1 + x)) (B' := fun _ => ε)
        hwc.neg.continuousOn (fun x _ => (hw x).neg.hasDerivWithinAt) ?_ (by fun_prop) ?_ ?_ hτ
      · simp only [hw0]; nlinarith
      · intro x _
        have : HasDerivAt (fun x => -a + ε * (1 + x)) ε x := by
          simpa using (((hasDerivAt_id x).const_add 1).const_mul ε).const_add (-a)
        exact this.hasDerivWithinAt
      · intro x hx hxB
        have hzx : z x ≤ a := by
          rw [hwz x (Ico_subset_Icc_self hx)]
          have : w x = a - ε * (1 + x) := by linarith
          rw [this]; nlinarith [hx.1]
        show -p (cl (z x)) < ε
        simp only [cl, projIcc_of_le_left hab hzx]
        linarith
    linarith
  -- the backward solution
  refine ⟨fun t => w (T - t), ?_⟩
  apply bridge p (cub_cont A0 A1 A2 A3) h T
  · simp [hw0]
  · intro s hs
    have hTs : T - s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hd := (hw (T - s)).comp_const_sub T s
    refine hd.congr_deriv ?_
    have hmem : z (T - s) ∈ Icc a b := by
      rw [hwz _ hTs]; exact ⟨hlow _ hTs, hup _ hTs⟩
    show -(p (cl (z (T - s)))) = -(p (w (T - s)))
    simp only [cl, projIcc_of_mem hab hmem]
    rw [hwz _ hTs]

lemma low_bound2 (A0 A1 A2 v : ℝ) (hv : 1 ≤ v) :
    |A0 + A1 * v + A2 * v ^ 2| ≤ (|A0| + |A1| + |A2|) * v ^ 2 := by
  have hv0 : 0 ≤ v := by linarith
  have h1 : v ≤ v ^ 2 := by nlinarith
  have h2 : 1 ≤ v ^ 2 := by nlinarith
  have e1 := abs_add_le (A0 + A1 * v) (A2 * v ^ 2)
  have e2 := abs_add_le A0 (A1 * v)
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ v ^ 2)] at e1
  rw [abs_mul, abs_of_nonneg hv0] at e2
  have := mul_le_mul_of_nonneg_left h1 (abs_nonneg A1)
  have := mul_le_mul_of_nonneg_left h2 (abs_nonneg A0)
  nlinarith

lemma low_bound1 (A0 A1 v : ℝ) (hv : 1 ≤ v) :
    |A0 + A1 * v| ≤ (|A0| + |A1|) * v := by
  have hv0 : 0 ≤ v := by linarith
  have e2 := abs_add_le A0 (A1 * v)
  rw [abs_mul, abs_of_nonneg hv0] at e2
  have := mul_le_mul_of_nonneg_left hv (abs_nonneg A0)
  nlinarith

lemma growth (A0 A1 A2 A3 h : ℝ) (hpos : ∀ v, h ≤ v → 0 < cub A0 A1 A2 A3 v)
    (hdeg : A3 ≠ 0 ∨ A2 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 1 ≤ R ∧ ∀ v, R ≤ v → c * v ^ 2 ≤ cub A0 A1 A2 A3 v := by
  by_cases h3 : A3 = 0
  · have h2 : A2 ≠ 0 := hdeg.resolve_left (not_not.mpr h3)
    set S := |A0| + |A1| with hS
    have hS0 : 0 ≤ S := by positivity
    rcases lt_or_gt_of_ne h2 with hneg | hpos2
    · exfalso
      set v := max (max 1 (2 * S / |A2|)) h + 1 with hv
      have hv1 : 1 ≤ v := by
        have := le_max_left (max 1 (2 * S / |A2|)) h; have := le_max_left 1 (2 * S / |A2|)
        linarith
      have hvh : h ≤ v := by have := le_max_right (max 1 (2 * S / |A2|)) h; linarith
      have hvS : 2 * S / |A2| ≤ v := by
        have := le_max_left (max 1 (2 * S / |A2|)) h; have := le_max_right 1 (2 * S / |A2|)
        linarith
      have habs : |A2| = -A2 := abs_of_neg hneg
      have hA : 0 < |A2| := abs_pos.mpr h2
      have hvS' : 2 * S ≤ |A2| * v := by
        rw [div_le_iff₀ hA] at hvS; linarith
      have hb := low_bound1 A0 A1 v hv1
      have hp := hpos v hvh
      unfold cub at hp
      rw [h3] at hp
      have hv0 : 0 ≤ v := by linarith
      have : A0 + A1 * v ≤ S * v := (le_abs_self _).trans hb
      have : 2 * S * v ≤ |A2| * v * v := mul_le_mul_of_nonneg_right hvS' hv0
      nlinarith
    · refine ⟨A2 / 2, by positivity, max 1 (2 * S / A2), le_max_left _ _, fun v hv => ?_⟩
      have hv1 : 1 ≤ v := (le_max_left _ _).trans hv
      have hvS : 2 * S / A2 ≤ v := (le_max_right _ _).trans hv
      have hvS' : 2 * S ≤ A2 * v := by rw [div_le_iff₀ hpos2] at hvS; linarith
      have hb := low_bound1 A0 A1 v hv1
      have hv0 : 0 ≤ v := by linarith
      have : -(S * v) ≤ A0 + A1 * v := by have := neg_abs_le (A0 + A1 * v); linarith
      have : 2 * S * v ≤ A2 * v * v := mul_le_mul_of_nonneg_right hvS' hv0
      unfold cub; rw [h3]
      nlinarith
  · set S := |A0| + |A1| + |A2| with hS
    have hS0 : 0 ≤ S := by positivity
    rcases lt_or_gt_of_ne h3 with hneg | hpos3
    · exfalso
      set v := max (max 1 (2 * S / |A3|)) h + 1 with hv
      have hv1 : 1 ≤ v := by
        have := le_max_left (max 1 (2 * S / |A3|)) h; have := le_max_left 1 (2 * S / |A3|)
        linarith
      have hvh : h ≤ v := by have := le_max_right (max 1 (2 * S / |A3|)) h; linarith
      have hvS : 2 * S / |A3| ≤ v := by
        have := le_max_left (max 1 (2 * S / |A3|)) h; have := le_max_right 1 (2 * S / |A3|)
        linarith
      have habs : |A3| = -A3 := abs_of_neg hneg
      have hA : 0 < |A3| := abs_pos.mpr h3
      have hvS' : 2 * S ≤ |A3| * v := by
        rw [div_le_iff₀ hA] at hvS; linarith
      have hb := low_bound2 A0 A1 A2 v hv1
      have hp := hpos v hvh
      unfold cub at hp
      have hv0 : 0 ≤ v := by linarith
      have hv2 : 0 ≤ v ^ 2 := by positivity
      have : A0 + A1 * v + A2 * v ^ 2 ≤ S * v ^ 2 := (le_abs_self _).trans hb
      have : 2 * S * v ^ 2 ≤ |A3| * v * v ^ 2 := mul_le_mul_of_nonneg_right hvS' hv2
      have e : A3 * v ^ 3 = -(|A3| * v * v ^ 2) := by rw [habs]; ring
      nlinarith
    · refine ⟨A3 / 2, by positivity, max 1 (2 * S / A3), le_max_left _ _, fun v hv => ?_⟩
      have hv1 : 1 ≤ v := (le_max_left _ _).trans hv
      have hvS : 2 * S / A3 ≤ v := (le_max_right _ _).trans hv
      have hvS' : 2 * S ≤ A3 * v := by rw [div_le_iff₀ hpos3] at hvS; linarith
      have hb := low_bound2 A0 A1 A2 v hv1
      have hv0 : 0 ≤ v := by linarith
      have hv2 : 0 ≤ v ^ 2 := by positivity
      have : -(S * v ^ 2) ≤ A0 + A1 * v + A2 * v ^ 2 := by
        have := neg_abs_le (A0 + A1 * v + A2 * v ^ 2); linarith
      have : 2 * S * v ^ 2 ≤ A3 * v * v ^ 2 := mul_le_mul_of_nonneg_right hvS' hv2
      have hv3 : v ^ 2 ≤ v * v ^ 2 := by nlinarith
      have : A3 / 2 * v ^ 2 ≤ A3 / 2 * (v * v ^ 2) := mul_le_mul_of_nonneg_left hv3 (by positivity)
      unfold cub
      nlinarith

lemma inv_integrable (A0 A1 A2 A3 h0 : ℝ) (hpos : ∀ v, h0 ≤ v → 0 < cub A0 A1 A2 A3 v)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 1 ≤ R) (hg : ∀ v, R ≤ v → c * v ^ 2 ≤ cub A0 A1 A2 A3 v) :
    MeasureTheory.IntegrableOn (fun v => 1 / cub A0 A1 A2 A3 v) (Ioi h0) := by
  set R' := max R h0 with hR'
  have hR'0 : 0 < R' := lt_of_lt_of_le (by linarith) (le_max_left R h0)
  have h1 : MeasureTheory.IntegrableOn (fun v => 1 / cub A0 A1 A2 A3 v) (Icc h0 R') := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div (cub_cont A0 A1 A2 A3).continuousOn
      (fun v hv => ne_of_gt (hpos v hv.1))
  have h2 : MeasureTheory.IntegrableOn (fun v => 1 / cub A0 A1 A2 A3 v) (Ioi R') := by
    have hgi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR'0).const_mul (1 / c)
    refine MeasureTheory.Integrable.mono' hgi ?_ ?_
    · exact (measurable_const.div (cub_cont A0 A1 A2 A3).measurable).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => ?_)
      have hvR : R ≤ v := (le_max_left R h0).trans (le_of_lt hv)
      have hv0 : 0 < v := hR'0.trans hv
      have hgv := hg v hvR
      have hcv : 0 < c * v ^ 2 := by positivity
      have hpv : 0 < cub A0 A1 A2 A3 v := hcv.trans_le hgv
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpv), Real.rpow_neg hv0.le,
        Real.rpow_two]
      rw [div_le_iff₀ hpv]
      calc (1 : ℝ) = 1 / c * (v ^ 2)⁻¹ * (c * v ^ 2) := by field_simp
        _ ≤ 1 / c * (v ^ 2)⁻¹ * cub A0 A1 A2 A3 v :=
          mul_le_mul_of_nonneg_left hgv (by positivity)
  refine (h1.union h2).mono_set ?_
  intro v hv
  by_cases hvR : v ≤ R'
  · exact Or.inl ⟨le_of_lt hv, hvR⟩
  · exact Or.inr (not_le.mp hvR)

lemma no_sol (A0 A1 A2 A3 h : ℝ) (hp : 0 < cub A0 A1 A2 A3 h)
    (hnz : ∀ l, h ≤ l → cub A0 A1 A2 A3 l ≠ 0) (hdeg : A3 ≠ 0 ∨ A2 ≠ 0) :
    ∃ T : ℝ, 0 < T ∧
      ∀ y : ℝ → ℝ, ¬ UnifiedFBSDE.Cubic.IsSolution (fun _ v => cub A0 A1 A2 A3 v) h T y := by
  set p := cub A0 A1 A2 A3 with hpdef
  have hpc : Continuous p := cub_cont A0 A1 A2 A3
  have hposh : ∀ v, h ≤ v → 0 < p v := by
    intro v hv
    by_contra hneg
    rw [not_lt] at hneg
    obtain ⟨l, hl, hl0⟩ := intermediate_value_Icc' hv hpc.continuousOn ⟨hneg, hp.le⟩
    exact hnz l hl.1 hl0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hpc.continuousAt (x := h) |>.eventually (lt_mem_nhds hp))
  set η := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  have hpos0 : ∀ v, h - η ≤ v → 0 < p v := by
    intro v hv
    by_cases hvh : h ≤ v
    · exact hposh v hvh
    · apply hball
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
  obtain ⟨c, hc, R, hR, hg⟩ := growth A0 A1 A2 A3 (h - η) hpos0 hdeg
  have hint := inv_integrable A0 A1 A2 A3 (h - η) hpos0 c hc R hR hg
  set I := ∫ v in Ioi (h - η), 1 / p v with hIdef
  have hI0 : 0 ≤ I := MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun v hv => (one_div_pos.mpr (hpos0 v (le_of_lt hv))).le)
  refine ⟨I + 1, by linarith, fun y hy => ?_⟩
  set T := I + 1 with hTdef
  have hT : 0 < T := by linarith
  -- continuity of y on [0, T]
  have hq : MeasureTheory.IntegrableOn (fun s => p (y s)) (Icc 0 T) := (hy 0 ⟨le_rfl, hT.le⟩).1
  have hprim : ContinuousOn (fun t => ∫ s in t..T, p (y s)) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval_left (a := 0) (b := T)
      (μ := MeasureTheory.volume) (f := fun s => p (y s)) (by rwa [uIcc_of_le hT.le])
    rwa [uIcc_of_le hT.le] at this
  have ycont : ContinuousOn y (Icc 0 T) :=
    (continuousOn_const.add hprim).congr (fun t ht => (hy t ht).2)
  let yt : ℝ → ℝ := fun s => y (projIcc 0 T hT.le s)
  have hyt : Continuous yt :=
    ycont.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc 0 T hT.le s).2)
  have hyteq : ∀ s ∈ Icc 0 T, yt s = y s := fun s hs => by
    simp only [yt, projIcc_of_mem _ hs]
  let z : ℝ → ℝ := fun τ => yt (T - τ)
  have hzc : Continuous z := hyt.comp (continuous_const.sub continuous_id)
  let w : ℝ → ℝ := fun τ => h + ∫ σ in (0 : ℝ)..τ, p (z σ)
  have hw : ∀ τ, HasDerivAt w (p (z τ)) τ := fun τ =>
    ((hpc.comp hzc).integral_hasStrictDerivAt 0 τ).hasDerivAt.const_add h
  have hwc : Continuous w := continuous_iff_continuousAt.mpr (fun τ => (hw τ).continuousAt)
  have hw0 : w 0 = h := by simp [w]
  have hwz : ∀ τ ∈ Icc 0 T, w τ = z τ := by
    intro τ hτ
    have hTτ : T - τ ∈ Icc 0 T := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hc := intervalIntegral.integral_comp_sub_left (a := 0) (b := τ) (fun s => p (yt s)) T
    show h + ∫ σ in (0 : ℝ)..τ, p (yt (T - σ)) = yt (T - τ)
    rw [hc, hyteq _ hTτ, (hy _ hTτ).2, sub_zero]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith [hτ.1])] at hs
    simp only
    rw [hyteq s ⟨by linarith [hs.1, hτ.2], hs.2⟩]
  -- the trajectory stays where p > 0
  have hlow : ∀ τ ∈ Icc 0 T, h - η / 2 ≤ w τ := by
    intro τ hτ
    have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun x => -w x)
      (f' := fun x => -p (z x)) (a := 0) (b := T) hwc.neg.continuousOn
      (fun x _ => (hw x).neg.hasDerivWithinAt) (B := fun _ => -(h - η / 2)) (B' := fun _ => 0)
      (by simp only [hw0]; linarith) continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _) ?_ hτ
    · linarith
    · intro x hx hxB
      have hwx : w x = h - η / 2 := by linarith
      have hzx : z x = h - η / 2 := by rw [← hwz x (Ico_subset_Icc_self hx), hwx]
      show -p (z x) < 0
      rw [hzx]
      have := hpos0 (h - η / 2) (by linarith)
      linarith
  -- the time function
  let Φ : ℝ → ℝ := fun u => ∫ v in (h - η)..u, 1 / p v
  have hΦ : ∀ u, h - η < u → HasDerivAt Φ (1 / p u) u := by
    intro u hu
    apply intervalIntegral.integral_hasDerivAt_right
    · apply MeasureTheory.IntegrableOn.intervalIntegrable
      rw [uIcc_of_le hu.le]
      exact (continuousOn_const.div hpc.continuousOn
        (fun v hv => ne_of_gt (hpos0 v hv.1))).integrableOn_Icc
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        (continuousOn_const.div hpc.continuousOn (fun v hv => ne_of_gt (hpos0 v (le_of_lt hv))))
        u hu
    · exact continuousAt_const.div hpc.continuousAt (ne_of_gt (hpos0 u hu.le))
  have hchain : ∀ τ ∈ Icc 0 T, HasDerivAt (fun τ => Φ (w τ)) 1 τ := by
    intro τ hτ
    have hwτ : h - η < w τ := by have := hlow τ hτ; linarith
    have := (hΦ (w τ) hwτ).comp τ (hw τ)
    refine this.congr_deriv ?_
    rw [← hwz τ hτ]
    exact one_div_mul_cancel (ne_of_gt (hpos0 _ hwτ.le))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ => Φ (w τ))
    (f' := fun _ => (1 : ℝ)) (a := 0) (b := T)
    (fun x hx => hchain x (by rwa [uIcc_of_le hT.le] at hx)) intervalIntegrable_const
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, hw0] at hFTC
  have hΦh : 0 ≤ Φ h := intervalIntegral.integral_nonneg (by linarith)
    (fun v hv => (one_div_pos.mpr (hpos0 v hv.1)).le)
  have hwT : h - η ≤ w T := by have := hlow T ⟨hT.le, le_rfl⟩; linarith
  have hΦT : Φ (w T) ≤ I := by
    show ∫ v in (h - η)..(w T), 1 / p v ≤ I
    rw [intervalIntegral.integral_of_le hwT]
    exact MeasureTheory.setIntegral_mono_set hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun v hv => (one_div_pos.mpr (hpos0 v (le_of_lt hv))).le))
      Ioc_subset_Ioi_self.eventuallyLE
  linarith

lemma exist_affine (A0 A1 h T : ℝ) :
    ∃ y : ℝ → ℝ, UnifiedFBSDE.Cubic.IsBoundedSolution (fun _ v => cub A0 A1 0 0 v) h T y := by
  by_cases hA1 : A1 = 0
  · refine ⟨fun t => h + A0 * (T - t), bridge _ (cub_cont A0 A1 0 0) h T _ (by simp)
      (fun s _ => ?_)⟩
    have : HasDerivAt (fun t => h + A0 * (T - t)) (A0 * (-1)) s :=
      (((hasDerivAt_id s).const_sub T).const_mul A0).const_add h
    refine this.congr_deriv ?_
    simp [cub, hA1]
  · refine ⟨fun t => -A0 / A1 + (h + A0 / A1) * Real.exp (A1 * (T - t)),
      bridge _ (cub_cont A0 A1 0 0) h T _ (by simp; field_simp; ring) (fun s _ => ?_)⟩
    have h1 : HasDerivAt (fun t => A1 * (T - t)) (A1 * (-1)) s :=
      ((hasDerivAt_id s).const_sub T).const_mul A1
    have h2 := (h1.exp.const_mul (h + A0 / A1)).const_add (-A0 / A1)
    refine h2.congr_deriv ?_
    unfold cub
    field_simp
    ring

lemma reflect (A0 A1 A2 A3 h T : ℝ) (y : ℝ → ℝ)
    (hy : UnifiedFBSDE.Cubic.IsSolution (fun _ v => cub A0 A1 A2 A3 v) h T y) :
    UnifiedFBSDE.Cubic.IsSolution (fun _ v => cub (-A0) A1 (-A2) A3 v) (-h) T (fun t => -y t) := by
  have e : ∀ v, cub (-A0) A1 (-A2) A3 (-v) = -cub A0 A1 A2 A3 v := by
    intro v; unfold cub; ring
  intro t ht
  obtain ⟨h1, h2⟩ := hy t ht
  refine ⟨?_, ?_⟩
  · simp only [e]; exact h1.neg
  · simp only [e, intervalIntegral.integral_neg]
    rw [h2]; ring

end RRAux_UnifiedFBSDE_Cubic_theorem_5_3

open UnifiedFBSDE.Cubic in
theorem solution (c : Coeffs) (h : ℝ) :
    (∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ, IsBoundedSolution (fun _ y => c.F y) h T y) ↔
      ((0 ≤ c.F h ∧ ∃ l : ℝ, h ≤ l ∧ c.F l = 0) ∨
        (c.F h ≤ 0 ∧ ∃ l : ℝ, l ≤ h ∧ c.F l = 0) ∨
        (c.σ₂ * c.b₃ = 0 ∧ c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁ = 0)) := by
  have hF : ∀ v, c.F v = RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub c.f₁ (c.f₂ + c.b₁ + c.σ₁ * c.f₃)
      (c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁) (c.σ₂ * c.b₃) v := by
    intro v; unfold Coeffs.F RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub; ring
  have hfun : (fun (_ : ℝ) (v : ℝ) => c.F v) = fun _ v => RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub
      c.f₁ (c.f₂ + c.b₁ + c.σ₁ * c.f₃) (c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁) (c.σ₂ * c.b₃) v := by
    funext _ v; exact hF v
  rw [hfun]
  simp only [hF]
  set A0 := c.f₁
  set A1 := c.f₂ + c.b₁ + c.σ₁ * c.f₃
  set A2 := c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁
  set A3 := c.σ₂ * c.b₃
  constructor
  · intro hall
    by_contra hcon
    simp only [not_or, not_and, not_exists] at hcon
    obtain ⟨n1, n2, n3⟩ := hcon
    have hdeg : A3 ≠ 0 ∨ A2 ≠ 0 := by
      by_cases h3 : A3 = 0
      · exact Or.inr (n3 h3)
      · exact Or.inl h3
    by_cases hs : 0 ≤ RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub A0 A1 A2 A3 h
    · have hnz : ∀ l, h ≤ l → RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub A0 A1 A2 A3 l ≠ 0 :=
        fun l hl => n1 hs l hl
      have hp : 0 < RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub A0 A1 A2 A3 h :=
        lt_of_le_of_ne hs (fun e => hnz h le_rfl e.symm)
      obtain ⟨T, hT, hno⟩ := RRAux_UnifiedFBSDE_Cubic_theorem_5_3.no_sol A0 A1 A2 A3 h hp hnz hdeg
      obtain ⟨y, hy⟩ := hall T hT
      exact hno y hy.1
    · have hs' : RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub A0 A1 A2 A3 h ≤ 0 := (not_le.mp hs).le
      have hnz : ∀ l, l ≤ h → RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub A0 A1 A2 A3 l ≠ 0 :=
        fun l hl => n2 hs' l hl
      have e : ∀ v, RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub (-A0) A1 (-A2) A3 v
          = -RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub A0 A1 A2 A3 (-v) := by
        intro v; unfold RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub; ring
      have hp : 0 < RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub (-A0) A1 (-A2) A3 (-h) := by
        rw [e, neg_neg]; exact neg_pos.mpr (not_le.mp hs)
      have hnz' : ∀ l, -h ≤ l → RRAux_UnifiedFBSDE_Cubic_theorem_5_3.cub (-A0) A1 (-A2) A3 l ≠ 0 := by
        intro l hl
        rw [e, neg_ne_zero]
        exact hnz (-l) (by linarith)
      have hdeg' : A3 ≠ 0 ∨ -A2 ≠ 0 := by
        rcases hdeg with h3 | h2
        · exact Or.inl h3
        · exact Or.inr (neg_ne_zero.mpr h2)
      obtain ⟨T, hT, hno⟩ :=
        RRAux_UnifiedFBSDE_Cubic_theorem_5_3.no_sol (-A0) A1 (-A2) A3 (-h) hp hnz' hdeg'
      obtain ⟨y, hy⟩ := hall T hT
      exact hno _ (RRAux_UnifiedFBSDE_Cubic_theorem_5_3.reflect A0 A1 A2 A3 h T y hy.1)
  · rintro (⟨hFh, l, hl, hFl⟩ | ⟨hFh, l, hl, hFl⟩ | ⟨h3, h2⟩) T hT
    · exact RRAux_UnifiedFBSDE_Cubic_theorem_5_3.exist_clamp A0 A1 A2 A3 h l h T hl le_rfl hl
        hFh hFl.le hT
    · exact RRAux_UnifiedFBSDE_Cubic_theorem_5_3.exist_clamp A0 A1 A2 A3 l h h T hl hl le_rfl
        hFl.ge hFh hT
    · rw [h3, h2]
      exact RRAux_UnifiedFBSDE_Cubic_theorem_5_3.exist_affine A0 A1 h T

#print axioms solution
