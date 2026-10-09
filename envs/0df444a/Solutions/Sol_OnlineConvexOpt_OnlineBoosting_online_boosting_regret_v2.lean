-- Prove2me | solution 1 for OnlineConvexOpt.OnlineBoosting.online_boosting_regret_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T20:34:30.223066+00:00
-- url     : https://prove2.me/submissions/442d4260-976c-4f92-ad4b-87ffca15e22d

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Algorithm_v2
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_WOCL_v2
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_SmoothOn

set_option autoImplicit false

open MeasureTheory Metric

namespace P6219dff5

theorem vol_ball_pos (n : ℕ) :
    0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_closedBall_pos volume _ one_pos).ne'
    measure_closedBall_lt_top.ne

theorem lip_of_abs {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * dist x y) : LipschitzWith ⟨L, hL⟩ F :=
  LipschitzWith.of_dist_le_mul fun x y => by rw [Real.dist_eq]; exact hF x y

theorem integrableOn_comp {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Continuous F)
    (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    IntegrableOn (fun v => F (x + δ • v)) (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) volume := by
  have hφ : Continuous (fun v : EuclideanSpace ℝ (Fin n) => F (x + δ • v)) := by fun_prop
  exact hφ.continuousOn.integrableOn_compact (isCompact_closedBall _ _)

theorem smoothed_hasFDerivAt {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * dist x y) (δ : ℝ) (hδ : 0 < δ) (x0 : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun x => ∫ v in closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, F (x + δ • v))
      (∫ v in closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, fderiv ℝ F (x0 + δ • v)) x0 := by
  have hLip := lip_of_abs F L hL hF
  have hcont : Continuous F := hLip.continuous
  have hae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ F z :=
    hLip.ae_differentiableAt
  have hae1 : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      DifferentiableAt ℝ F (x0 + z) :=
    (measurePreserving_add_left volume x0).quasiMeasurePreserving.ae hae
  have hae2 : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      DifferentiableAt ℝ F (x0 + δ • v) :=
    (Measure.quasiMeasurePreserving_smul volume hδ.ne').ae hae1
  have hfin : volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  refine (hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℝ) (s := Set.univ)
    (bound := fun _ => L) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · intro x _
    have hφ : Continuous (fun v : EuclideanSpace ℝ (Fin n) => F (x + δ • v)) := by fun_prop
    exact hφ.aestronglyMeasurable
  · exact integrableOn_comp F hcont x0 δ
  · have hm : Measurable (fun v : EuclideanSpace ℝ (Fin n) => x0 + δ • v) := by fun_prop
    exact ((measurable_fderiv ℝ F).comp hm).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v x _ => ?_
    rw [Real.norm_eq_abs]
    calc |F (x + δ • v) - F (x0 + δ • v)| ≤ L * dist (x + δ • v) (x0 + δ • v) := hF _ _
      _ = L * ‖x - x0‖ := by rw [dist_add_right, dist_eq_norm]
  · exact integrableOn_const hfin
  · exact ae_restrict_of_ae (hae2.mono fun v hv => by
      have := hv.hasFDerivAt.comp x0 ((hasFDerivAt_id x0).add_const (δ • v))
      simpa [Function.comp_def] using this)

/-- integral of a bounded function over a difference set -/
theorem norm_int_diff_le {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (hg : Measurable g) (L : ℝ) (hgL : ∀ w, ‖g w‖ ≤ L)
    (B B' : Set (EuclideanSpace ℝ (Fin n))) (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hBf : volume B ≠ ⊤) (hB'f : volume B' ≠ ⊤) :
    ‖(∫ w in B, g w) - ∫ w in B', g w‖ ≤ L * volume.real (B \ B') + L * volume.real (B' \ B) := by
  have hint : ∀ S : Set (EuclideanSpace ℝ (Fin n)), volume S ≠ ⊤ → IntegrableOn g S volume := by
    intro S hS
    refine Integrable.mono' (integrableOn_const (C := L) hS) hg.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => hgL w
  rw [← integral_inter_add_sdiff hB' (hint B hBf), ← integral_inter_add_sdiff hB (hint B' hB'f),
    Set.inter_comm B' B]
  have e : ((∫ w in B ∩ B', g w) + ∫ w in B \ B', g w) - ((∫ w in B ∩ B', g w) + ∫ w in B' \ B, g w)
      = (∫ w in B \ B', g w) - ∫ w in B' \ B, g w := by abel
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hBf.lt_top) fun w _ => hgL w
  · exact norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hB'f.lt_top) fun w _ => hgL w

theorem vol_closedBall_real {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 ≤ r) :
    volume.real (closedBall c r) =
      r ^ n * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_closedBall' volume c hr,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n)]

theorem half_smul_norm {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : ‖(1/2 : ℝ) • u‖ = ‖u‖ / 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]; ring

theorem vol_diff_le {n : ℕ} (c1 c2 : EuclideanSpace ℝ (Fin n)) (hk : ‖c1 - c2‖ ≤ 2) :
    volume.real (closedBall c1 1 \ closedBall c2 1) ≤
      (n * (‖c1 - c2‖ / 2)) * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  set V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  set s := ‖c1 - c2‖ / 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  set m := c2 + (1/2 : ℝ) • (c1 - c2)
  set M := closedBall m (1 - s)
  have hMB : M ⊆ closedBall c1 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    have e : z - c1 = (z - m) - (1/2 : ℝ) • (c1 - c2) := by simp only [m]; module
    rw [e]
    calc ‖(z - m) - (1/2 : ℝ) • (c1 - c2)‖ ≤ ‖z - m‖ + ‖(1/2 : ℝ) • (c1 - c2)‖ := norm_sub_le _ _
      _ ≤ (1 - s) + s := by rw [half_smul_norm]; linarith
      _ = 1 := by ring
  have hMB' : M ⊆ closedBall c2 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    have e : z - c2 = (z - m) + (1/2 : ℝ) • (c1 - c2) := by simp only [m]; module
    rw [e]
    calc ‖(z - m) + (1/2 : ℝ) • (c1 - c2)‖ ≤ ‖z - m‖ + ‖(1/2 : ℝ) • (c1 - c2)‖ := norm_add_le _ _
      _ ≤ (1 - s) + s := by rw [half_smul_norm]; linarith
      _ = 1 := by ring
  have hsub : closedBall c1 1 \ closedBall c2 1 ⊆ closedBall c1 1 \ M :=
    fun z hz => ⟨hz.1, fun h => hz.2 (hMB' h)⟩
  have h1 : volume.real (closedBall c1 1 \ closedBall c2 1) ≤ volume.real (closedBall c1 1 \ M) :=
    measureReal_mono hsub (measure_ne_top_of_subset (fun z hz => hz.1) measure_closedBall_lt_top.ne)
  have hM : volume.real M = (1 - s) ^ n * V := vol_closedBall_real m (1 - s) (by linarith)
  have hc1 : volume.real (closedBall c1 1) = V := by
    rw [vol_closedBall_real c1 1 zero_le_one, one_pow, one_mul]
  rw [measureReal_sdiff hMB measurableSet_closedBall measure_closedBall_lt_top.ne, hc1, hM] at h1
  have hB : 1 - n * s ≤ (1 - s) ^ n := by
    have := one_add_mul_le_pow (show (-2:ℝ) ≤ -s by linarith) n
    rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
    exact this
  have hV : 0 < V := vol_ball_pos n
  nlinarith

theorem grad_diff_le {n : ℕ} (hn : 0 < n) (F : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * dist x y) (δ : ℝ) (hδ : 0 < δ) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖(∫ v in closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, fderiv ℝ F (x + δ • v)) -
      ∫ v in closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, fderiv ℝ F (y + δ • v)‖ ≤
      (n * L / δ) * ‖x - y‖ * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hLip := lip_of_abs F L hL hF
  set B := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 with hBdef
  set V := volume.real B with hVdef
  have hV : 0 < V := vol_ball_pos n
  have hgL : ∀ z, ‖fderiv ℝ F z‖ ≤ L := fun z => norm_fderiv_le_of_lipschitz ℝ hLip
  set g : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun w => fderiv ℝ F (x + δ • w) with hgdef
  have hgm : Measurable g := (measurable_fderiv ℝ F).comp (by fun_prop)
  set k : EuclideanSpace ℝ (Fin n) := δ⁻¹ • (x - y) with hkdef
  have hknorm : ‖k‖ = ‖x - y‖ / δ := by
    rw [hkdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]; ring
  have hshift : (∫ v in B, fderiv ℝ F (y + δ • v)) = ∫ w in closedBall (-k) 1, g w := by
    have hmp : MeasurePreserving (fun v : EuclideanSpace ℝ (Fin n) => v - k) volume volume :=
      measurePreserving_sub_right volume k
    have hemb : MeasurableEmbedding (fun v : EuclideanSpace ℝ (Fin n) => v - k) :=
      (MeasurableEquiv.subRight k).measurableEmbedding
    rw [← hmp.setIntegral_preimage_emb hemb g (closedBall (-k) 1)]
    have hpre : (fun v : EuclideanSpace ℝ (Fin n) => v - k) ⁻¹' closedBall (-k) 1 = B := by
      ext v; simp [hBdef, dist_eq_norm]
    rw [hpre]
    have hfun : (fun v => fderiv ℝ F (y + δ • v)) = fun v => g (v - k) := by
      funext v
      simp only [hgdef, hkdef]
      congr 1
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
      abel
    rw [hfun]
  rw [hshift]
  have hBf : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hB'f : volume (closedBall (-k) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hgoal : (n * L / δ) * ‖x - y‖ * V = n * L * ‖k‖ * V := by
    rw [hknorm]; field_simp
  rw [hgoal]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hk : ‖k‖ ≤ 2
  · have h0 := norm_int_diff_le g hgm L (fun w => hgL _) B (closedBall (-k) 1) measurableSet_closedBall
      measurableSet_closedBall hBf hB'f
    have h1 := vol_diff_le (0 : EuclideanSpace ℝ (Fin n)) (-k) (by simpa using hk)
    have h2 := vol_diff_le (-k) (0 : EuclideanSpace ℝ (Fin n)) (by simpa using hk)
    simp only [zero_sub, norm_neg, sub_zero] at h1 h2
    rw [← hBdef, ← hVdef] at h1 h2
    calc _ ≤ _ := h0
      _ ≤ L * ((n * (‖k‖ / 2)) * V) + L * ((n * (‖k‖ / 2)) * V) := by gcongr
      _ = n * L * ‖k‖ * V := by ring
  · push Not at hk
    have ha : ‖∫ w in B, g w‖ ≤ L * V :=
      norm_setIntegral_le_of_norm_le_const hBf.lt_top fun w _ => hgL (x + δ • w)
    have hb : ‖∫ w in closedBall (-k) 1, g w‖ ≤ L * V := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := g) hB'f.lt_top fun w _ => hgL (x + δ • w)
      rwa [vol_closedBall_real _ _ zero_le_one, one_pow, one_mul] at this
    calc _ ≤ ‖∫ w in B, g w‖ + ‖∫ w in closedBall (-k) 1, g w‖ := norm_sub_le _ _
      _ ≤ L * V + L * V := add_le_add ha hb
      _ ≤ n * L * ‖k‖ * V := by
          have : 2 ≤ (n:ℝ) * ‖k‖ := by nlinarith
          nlinarith [mul_nonneg hL hV.le]

theorem descent {n : ℕ} (S : EuclideanSpace ℝ (Fin n) → ℝ)
    (S' : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (hS : ∀ x, HasFDerivAt S (S' x) x) (β : ℝ)
    (hlip : ∀ x y, ‖S' x - S' y‖ ≤ β * ‖x - y‖) (x y : EuclideanSpace ℝ (Fin n)) :
    S y ≤ S x + S' x (y - x) + (β / 2) * ‖y - x‖ ^ 2 := by
  set h := y - x with hh
  let φ : ℝ → ℝ := fun t => S (x + t • h) - t * S' x h - (β / 2) * t ^ 2 * ‖h‖ ^ 2
  have hderiv : ∀ t : ℝ, HasDerivAt φ (S' (x + t • h) h - S' x h - β * t * ‖h‖ ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 := (hS (x + t • h)).comp_hasDerivAt t h1
    have h3 := (hasDerivAt_id t).mul_const (S' x h)
    have h4 := ((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖h‖ ^ 2)
    exact ((h2.sub h3).sub h4).congr_deriv (by ring)
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hl := hlip (x + t • h) x
      have h5 : (S' (x + t • h) - S' x) h ≤ ‖S' (x + t • h) - S' x‖ * ‖h‖ :=
        le_trans (le_abs_self _) (by
          rw [← Real.norm_eq_abs]; exact (S' (x + t • h) - S' x).le_opNorm h)
      have e : x + t • h - x = t • h := by abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hl
      rw [ContinuousLinearMap.sub_apply] at h5
      have hh0 := norm_nonneg h
      nlinarith [mul_le_mul_of_nonneg_right hl hh0]
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [φ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_pow] at this
  have e2 : x + h = y := by rw [hh]; abel
  rw [e2] at this
  linarith


open OnlineConvexOpt.OnlineBoosting in
theorem smoothed_facts {n : ℕ} (hn : 0 < n) (F : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * dist x y) (hFc : ConvexOn ℝ Set.univ F) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ x, HasGradientAt (SmoothedFunction F δ) (g x) x) ∧
      SmoothOn Set.univ (SmoothedFunction F δ) g (n * L / δ) ∧
      ConvexOn ℝ Set.univ (SmoothedFunction F δ) ∧
      (∀ x y, |SmoothedFunction F δ x - SmoothedFunction F δ y| ≤ L * dist x y) ∧
      (∀ x, |SmoothedFunction F δ x - F x| ≤ L * δ) := by
  have hcont : Continuous F := (lip_of_abs F L hL hF).continuous
  set B := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 with hBdef
  set V := volume.real B with hVdef
  have hV : 0 < V := vol_ball_pos n
  have hBf : volume B < ⊤ := measure_closedBall_lt_top
  have hfun : SmoothedFunction F δ = fun x => V⁻¹ * ∫ v in B, F (x + δ • v) := by
    funext x; simp only [SmoothedFunction, hVdef, hBdef, measureReal_def]
  set D : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun x => ∫ v in B, fderiv ℝ F (x + δ • v) with hDdef
  have hder : ∀ x, HasFDerivAt (SmoothedFunction F δ) (V⁻¹ • D x) x := by
    intro x
    rw [hfun]
    exact (smoothed_hasFDerivAt F L hL hF δ hδ x).const_mul V⁻¹
  have hlipD : ∀ x y, ‖V⁻¹ • D x - V⁻¹ • D y‖ ≤ (n * L / δ) * ‖x - y‖ := by
    intro x y
    have e : V⁻¹ • D x - V⁻¹ • D y = V⁻¹ • (D x - D y) := by
      ext v; simp [mul_sub]
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hV.le)]
    have := grad_diff_le hn F L hL hF δ hδ x y
    rw [← hBdef, ← hVdef] at this
    calc V⁻¹ * ‖D x - D y‖ ≤ V⁻¹ * ((n * L / δ) * ‖x - y‖ * V) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hV.le)
      _ = (n * L / δ) * ‖x - y‖ := by field_simp
  refine ⟨fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (V⁻¹ • D x),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hasGradientAt_iff_hasFDerivAt, LinearIsometryEquiv.apply_symm_apply]
    exact hder x
  · intro x _ y _
    rw [InnerProductSpace.toDual_symm_apply]
    exact descent _ _ hder _ hlipD x y
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    rw [hfun]
    simp only [smul_eq_mul]
    have hix := integrableOn_comp F hcont x δ
    have hiy := integrableOn_comp F hcont y δ
    have key : (∫ v in B, F ((a • x + b • y) + δ • v)) ≤
        ∫ v in B, (a * F (x + δ • v) + b * F (y + δ • v)) := by
      refine integral_mono (integrableOn_comp F hcont _ δ) ((hix.const_mul a).add (hiy.const_mul b)) ?_
      intro v
      simp only
      have e : (a • x + b • y) + δ • v = a • (x + δ • v) + b • (y + δ • v) := by
        calc (a • x + b • y) + δ • v = (a • x + b • y) + (a + b) • δ • v := by rw [hab, one_smul]
          _ = a • (x + δ • v) + b • (y + δ • v) := by module
      rw [e]
      exact hFc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
    rw [integral_add (hix.const_mul a) (hiy.const_mul b), integral_const_mul,
      integral_const_mul] at key
    have := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hV.le)
    linarith
  · intro x y
    rw [hfun]
    simp only
    rw [← mul_sub, ← integral_sub (integrableOn_comp F hcont x δ) (integrableOn_comp F hcont y δ),
      abs_mul, abs_of_pos (inv_pos.2 hV)]
    have hb : ‖∫ v in B, (F (x + δ • v) - F (y + δ • v))‖ ≤ (L * dist x y) * V := by
      refine norm_setIntegral_le_of_norm_le_const hBf fun v _ => ?_
      rw [Real.norm_eq_abs]
      calc |F (x + δ • v) - F (y + δ • v)| ≤ L * dist (x + δ • v) (y + δ • v) := hF _ _
        _ = L * dist x y := by rw [dist_add_right]
    rw [Real.norm_eq_abs] at hb
    calc V⁻¹ * |∫ v in B, (F (x + δ • v) - F (y + δ • v))| ≤ V⁻¹ * ((L * dist x y) * V) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hV.le)
      _ = L * dist x y := by field_simp
  · intro x
    rw [hfun]
    simp only
    have hI : ∫ v in B, (F (x + δ • v) - F x) = (∫ v in B, F (x + δ • v)) - V * F x := by
      rw [integral_sub (integrableOn_comp F hcont x δ) (integrableOn_const hBf.ne), setIntegral_const,
        smul_eq_mul]
    have e : V⁻¹ * (∫ v in B, F (x + δ • v)) - F x = V⁻¹ * ∫ v in B, (F (x + δ • v) - F x) := by
      rw [hI]; field_simp
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hV)]
    have hb : ‖∫ v in B, (F (x + δ • v) - F x)‖ ≤ (L * δ) * V := by
      refine norm_setIntegral_le_of_norm_le_const hBf fun v hv => ?_
      rw [Real.norm_eq_abs]
      have hv1 : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.1 hv
      calc |F (x + δ • v) - F x| ≤ L * dist (x + δ • v) x := hF _ _
        _ = L * (δ * ‖v‖) := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
        _ ≤ L * (δ * 1) := by gcongr
        _ = L * δ := by ring
    rw [Real.norm_eq_abs] at hb
    calc V⁻¹ * |∫ v in B, (F (x + δ • v) - F x)| ≤ V⁻¹ * ((L * δ) * V) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hV.le)
      _ = L * δ := by field_simp

theorem infDist_convex {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Convex ℝ K)
    (hne : K.Nonempty) : ConvexOn ℝ Set.univ (fun y => Metric.infDist y K) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨p, hp, hpd⟩ := (Metric.infDist_lt_iff hne).1
    (lt_add_of_pos_right (infDist x K) hε)
  obtain ⟨q, hq, hqd⟩ := (Metric.infDist_lt_iff hne).1
    (lt_add_of_pos_right (infDist y K) hε)
  have hmem : a • p + b • q ∈ K := hK hp hq ha hb hab
  calc infDist (a • x + b • y) K ≤ dist (a • x + b • y) (a • p + b • q) :=
        infDist_le_dist_of_mem hmem
    _ ≤ a * dist x p + b * dist y q := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
        have e : a • x + b • y - (a • p + b • q) = a • (x - p) + b • (y - q) := by module
        rw [e]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * (infDist x K + ε) + b * (infDist y K + ε) := by gcongr
    _ = a * infDist x K + b * infDist y K + ε := by linear_combination ε * hab

theorem final_arith (n G D T γ N δ R : ℝ) (hn : 1 ≤ n) (hG : 0 < G) (hD : 0 < D) (hT : 0 ≤ T)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hN : 0 < N) (hδ : δ = Real.sqrt (D ^ 2 / (γ * N))) :
    0 < δ ∧ 2 * (n * (2 * G) / δ) * D ^ 2 * T / (γ ^ 2 * N) + (2 * G * D / γ) * R + 4 * G * δ * T ≤
      8 * n * G * D * T / (γ ^ (3 / 2 : ℝ) * Real.sqrt N) + (2 * G * D / γ) * R := by
  have hδpos : 0 < δ := by rw [hδ]; exact Real.sqrt_pos.2 (by positivity)
  refine ⟨hδpos, ?_⟩
  set q := Real.sqrt γ with hqdef
  set r := Real.sqrt N with hrdef
  have hq0 : 0 < q := Real.sqrt_pos.2 hγ
  have hr0 : 0 < r := Real.sqrt_pos.2 hN
  have hq : q ^ 2 = γ := Real.sq_sqrt hγ.le
  have hr : r ^ 2 = N := Real.sq_sqrt hN.le
  have hγ32 : γ ^ (3 / 2 : ℝ) = q ^ 3 := by
    rw [hqdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hγ.le]; norm_num
  have hδsq : δ ^ 2 = D ^ 2 / (γ * N) := by rw [hδ, Real.sq_sqrt (by positivity)]
  have hDe : D = δ * q * r := by
    have h2 : (δ * q * r) ^ 2 = D ^ 2 := by
      rw [mul_pow, mul_pow, hδsq, hq, hr]; field_simp
    exact ((pow_left_inj₀ (by positivity) hD.le two_ne_zero).1 h2).symm
  rw [hγ32, ← hq, ← hr, hDe]
  have e1 : 2 * (n * (2 * G) / δ) * (δ * q * r) ^ 2 * T / ((q ^ 2) ^ 2 * r ^ 2) =
      4 * n * G * δ * T / q ^ 2 := by field_simp <;> ring
  have e2 : 8 * n * G * (δ * q * r) * T / (q ^ 3 * r) = 8 * n * G * δ * T / q ^ 2 := by
    field_simp <;> ring
  rw [e1, e2]
  have hq1 : q ^ 2 ≤ 1 := by rw [hq]; exact hγ1
  have h3 : 4 * G * δ * T ≤ 4 * n * G * δ * T / q ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ 4 * G * δ * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hq1 this]
  have h4 : 8 * n * G * δ * T / q ^ 2 = 4 * n * G * δ * T / q ^ 2 + 4 * n * G * δ * T / q ^ 2 := by
    ring
  linarith

end P6219dff5

namespace P57cc6451

/-- First-order condition for a convex function with a gradient. -/
theorem first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g p q : E} (hf : ConvexOn ℝ Set.univ f) (hg : HasGradientAt f g p) :
    inner ℝ g (q - p) ≤ f q - f p := by
  set φ : ℝ → ℝ := fun s => f (p + s • (q - p)) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have e : a • (p + x • (q - p)) + b • (p + y • (q - p))
        = (a + b) • p + (a * x + b * y) • (q - p) := by module
    rw [hab, one_smul] at e
    simp only [hφ, smul_eq_mul]
    rw [← e]
    exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have h1 : HasDerivAt (fun s : ℝ => p + s • (q - p)) ((1 : ℝ) • (q - p)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const (q - p)).const_add p
  have hg' : HasGradientAt f g (p + (0 : ℝ) • (q - p)) := by simpa using hg
  have hd := hg'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hd' : HasDerivAt φ (inner ℝ g (q - p)) 0 := by
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hd
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd'
  simpa [slope_def_field, hφ] using this

/-- A Lipschitz function has gradient of norm at most the Lipschitz constant. -/
theorem grad_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g p : E} {G : ℝ} (hG : 0 ≤ G) (hg : HasGradientAt f g p)
    (hL : ∀ x y, |f x - f y| ≤ G * dist x y) : ‖g‖ ≤ G := by
  have := hg.hasFDerivAt.le_of_lip' hG (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, ← dist_eq_norm]; exact hL x p)
  simpa using this

/-- The Frank–Wolfe style recursion. -/
theorem recursion (Δ η : ℕ → ℝ) (c E : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (hstep : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      Δ i ≤ (1 - η i) * Δ (i - 1) + η i * E + η i ^ 2 * c / 2) :
    ∀ i : ℕ, 1 ≤ i → i ≤ N → Δ i ≤ 2 * c / i + E := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro h1N
    have h := hstep 1 le_rfl h1N
    have e1 : η 1 = 1 := by rw [hη 1 le_rfl]; norm_num
    rw [e1] at h
    simp only [Nat.cast_one]
    nlinarith
  | succ i hi ih =>
    intro hiN
    have hprev := ih (by omega)
    have h := hstep (i + 1) (by omega) hiN
    have hm : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have eη : η (i + 1) = 2 / ((i : ℝ) + 1) := by
      rw [hη (i + 1) (by omega)]; push_cast
      apply min_eq_left
      rw [div_le_one (by positivity)]; linarith
    rw [eη] at h
    simp only [Nat.add_sub_cancel] at h
    have hnn : 0 ≤ 1 - 2 / ((i : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have h2 := mul_le_mul_of_nonneg_left hprev hnn
    have key : (1 - 2 / ((i : ℝ) + 1)) * (2 * c / i + E) + 2 / ((i : ℝ) + 1) * E
        + (2 / ((i : ℝ) + 1)) ^ 2 * c / 2
        = 2 * c / ((i : ℝ) + 1) + E - 2 * c / ((i : ℝ) * ((i : ℝ) + 1) ^ 2) := by
      field_simp; ring
    have hpos : 0 ≤ 2 * c / ((i : ℝ) * ((i : ℝ) + 1) ^ 2) := by positivity
    push_cast
    linarith

end P57cc6451

open OnlineConvexOpt.OnlineBoosting in
theorem P57cc6451.lemma125
    {n : ℕ} {A : Type*} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    (D γ : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (fhat : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (β Ghat : ℝ) (hβpos : 0 < β) (hGhatpos : 0 < Ghat)
    (ghat : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hghat : ∀ t x, HasGradientAt (fhat t) (ghat t x) x)
    (hfconv : ∀ t, ConvexOn ℝ Set.univ (fhat t))
    (hsmooth : ∀ t, SmoothOn Set.univ (fhat t) (ghat t) β)
    (hLip : ∀ t, ∀ x y, |fhat t x - fhat t y| ≤ Ghat * dist x y)
    (η : ℕ → ℝ) (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (a : ℕ → A) (H : Set (A → EuclideanSpace ℝ (Fin n))) (hHne : H.Nonempty)
    (hHK : ∀ h ∈ H, ∀ c : A, h c ∈ K)
    (W x : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (hW : ∀ t i, W t i ∈ K)
    (hx0 : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t 0 = 0)
    (hxstep : ∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
      x t i = (1 - η i) • x t (i - 1) + η i • ((1 / γ) • W t i))
    (fstage : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfstage : ∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
      fstage t i = fun y => inner ℝ (ghat t (x t (i - 1))) y)
    (RegretBoundW : ℝ)
    (hWOCL : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsGammaWOCL K γ T a H (fun t => W t i) (fun t y => fstage t i y / (Ghat * D)) RegretBoundW)
    (hstar : A → EuclideanSpace ℝ (Fin n)) (hstar_mem : hstar ∈ convexHull ℝ H) :
    (∑ t ∈ Finset.Icc 1 T, fhat t (x t N)) - ∑ t ∈ Finset.Icc 1 T, fhat t (hstar (a t)) ≤
      (2 * β * D ^ 2 * T) / (γ ^ 2 * N) + (Ghat * D / γ) * RegretBoundW := by
  -- basic facts on η
  have hη01 : ∀ i : ℕ, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi
    rw [hη i hi]
    exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hGD : 0 < Ghat * D := mul_pos hGhatpos hDpos
  -- iterates scaled by γ stay in K
  have hmem : ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ i : ℕ, i ≤ N → γ • x t i ∈ K := by
    intro t ht1 htT i
    induction i with
    | zero => intro _; rw [hx0 t ht1 htT, smul_zero]; exact h0K
    | succ i ih =>
      intro hiN
      have hs := hxstep t (i + 1) ht1 htT (by omega) hiN
      simp only [Nat.add_sub_cancel] at hs
      rw [hs]
      have e : γ • ((1 - η (i + 1)) • x t i + η (i + 1) • ((1 / γ) • W t (i + 1)))
          = (1 - η (i + 1)) • (γ • x t i) + η (i + 1) • W t (i + 1) := by
        rw [smul_add, smul_comm γ (1 - η (i + 1)), smul_comm γ (η (i + 1)), smul_smul γ (1 / γ),
          mul_one_div_cancel hγpos.ne', one_smul]
      rw [e]
      obtain ⟨h0, h1⟩ := hη01 (i + 1) (by omega)
      exact hKconv (ih (by omega)) (hW t (i + 1)) (by linarith) h0 (by ring)
  -- gradient norm bound
  have hgn : ∀ t p, ‖ghat t p‖ ≤ Ghat := fun t p =>
    P57cc6451.grad_norm_le hGhatpos.le (hghat t p) (hLip t)
  -- WOCL consequence at stage i
  have hwocl : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      ∑ t ∈ Finset.Icc 1 T, (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
        - inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) ≤ Ghat * D / γ * RegretBoundW := by
    intro i hi1 hiN
    set L : (A → EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun h => ∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (h (a t)) / (Ghat * D) with hL
    have hfl : ∀ t ∈ Finset.Icc 1 T, ∀ y, fstage t i y / (Ghat * D)
        = inner ℝ (ghat t (x t (i - 1))) y / (Ghat * D) := by
      intro t ht y
      rw [Finset.mem_Icc] at ht
      rw [hfstage t i ht.1 ht.2 hi1 hiN]
    have hpre : ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ u ∈ K, ∀ v ∈ K,
        fstage t i u / (Ghat * D) - fstage t i v / (Ghat * D) ≤ 1 := by
      intro t ht1 htT u hu v hv
      rw [hfstage t i ht1 htT hi1 hiN, div_sub_div_same, div_le_one hGD, ← inner_sub_right]
      refine (real_inner_le_norm _ _).trans ?_
      rw [← dist_eq_norm]
      exact mul_le_mul (hgn _ _) (hD u hu v hv) dist_nonneg hGhatpos.le
    have hW' := hWOCL i hi1 hiN hpre
    simp only at hW'
    set S := (fun h => ∑ t ∈ Finset.Icc 1 T, fstage t i (h (a t)) / (Ghat * D)) '' H with hS
    have hSL : ∀ h, ∑ t ∈ Finset.Icc 1 T, fstage t i (h (a t)) / (Ghat * D) = L h := by
      intro h
      exact Finset.sum_congr rfl fun t ht => hfl t ht _
    have hbdd : BddBelow S := by
      refine ⟨∑ t ∈ Finset.Icc 1 T, (-1 : ℝ), ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      have := hpre t ht'.1 ht'.2 0 h0K (h (a t)) (hHK h hh (a t))
      rw [hfstage t i ht'.1 ht'.2 hi1 hiN] at this ⊢
      simp only [inner_zero_right, zero_div, zero_sub] at this
      linarith
    have hsub : H ⊆ {h | sInf S ≤ L h} := by
      intro h hh
      show sInf S ≤ L h
      rw [← hSL]
      exact csInf_le hbdd ⟨h, hh, rfl⟩
    have hconv : Convex ℝ {h : A → EuclideanSpace ℝ (Fin n) | sInf S ≤ L h} := by
      intro h1 hh1 h2 hh2 p q hp hq hpq
      simp only [Set.mem_ofPred_eq] at hh1 hh2 ⊢
      have e : L (p • h1 + q • h2) = p * L h1 + q * L h2 := by
        simp only [hL, Pi.add_apply, Pi.smul_apply, inner_add_right, inner_smul_right, add_div,
          Finset.sum_add_distrib, Finset.mul_sum, mul_div_assoc]
      rw [e]
      have : sInf S = p * sInf S + q * sInf S := by rw [← add_mul, hpq, one_mul]
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left hh1 hp) (mul_le_mul_of_nonneg_left hh2 hq)
    have hstarL : sInf S ≤ L hstar := convexHull_min hsub hconv hstar_mem
    -- hW' : L-type sum for W ≤ γ * sInf S + R
    have hWsum : ∑ t ∈ Finset.Icc 1 T, fstage t i (W t i) / (Ghat * D)
        = (∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (W t i)) / (Ghat * D) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun t ht => hfl t ht _
    have hLs : L hstar
        = (∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) / (Ghat * D) := by
      rw [hL, Finset.sum_div]
    rw [hWsum] at hW'
    rw [hLs] at hstarL
    have e2 : ∑ t ∈ Finset.Icc 1 T, (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
        - inner ℝ (ghat t (x t (i - 1))) (hstar (a t)))
        = Ghat * D / γ * ((∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (W t i)) / (Ghat * D)
          - γ * ((∑ t ∈ Finset.Icc 1 T, inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) / (Ghat * D))) := by
      simp only [inner_smul_right, Finset.sum_sub_distrib, ← Finset.mul_sum]
      field_simp
    rw [e2]
    have hcoef : 0 ≤ Ghat * D / γ := by positivity
    apply mul_le_mul_of_nonneg_left _ hcoef
    have := mul_le_mul_of_nonneg_left hstarL hγpos.le
    linarith
  -- per-round inequality
  set c : ℝ := β * D ^ 2 * T / γ ^ 2 with hc
  set E : ℝ := Ghat * D / γ * RegretBoundW with hE
  set Δ : ℕ → ℝ := fun i => ∑ t ∈ Finset.Icc 1 T, (fhat t (x t i) - fhat t (hstar (a t))) with hΔ
  have hstep : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      Δ i ≤ (1 - η i) * Δ (i - 1) + η i * E + η i ^ 2 * c / 2 := by
    intro i hi1 hiN
    obtain ⟨hη0, hη1⟩ := hη01 i hi1
    have hpt : ∀ t ∈ Finset.Icc 1 T,
        fhat t (x t i) - fhat t (hstar (a t)) ≤
          (1 - η i) * (fhat t (x t (i - 1)) - fhat t (hstar (a t)))
          + η i * (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
              - inner ℝ (ghat t (x t (i - 1))) (hstar (a t)))
          + η i ^ 2 * (β * D ^ 2 / γ ^ 2) / 2 := by
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      set p := x t (i - 1) with hp
      set y := (1 / γ) • W t i with hy
      set z := hstar (a t) with hz
      set g := ghat t p with hg
      have hxi : x t i - p = η i • (y - p) := by
        rw [hxstep t i ht'.1 ht'.2 hi1 hiN]; module
      have hsm := hsmooth t p (Set.mem_univ _) (x t i) (Set.mem_univ _)
      rw [← hg, hxi, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hsm
      have hco := P57cc6451.first_order (q := z) (hfconv t) (hghat t p)
      rw [← hg] at hco
      have hnorm : ‖y - p‖ ≤ D / γ := by
        have hpm := hmem t ht'.1 ht'.2 (i - 1) (by omega)
        have : y - p = (1 / γ) • (W t i - γ • p) := by
          rw [hy, smul_sub, smul_smul, one_div_mul_cancel hγpos.ne', one_smul]
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← dist_eq_norm]
        rw [one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right (hD _ (hW t i) _ hpm) hγpos.le
      have hn2 : ‖y - p‖ ^ 2 ≤ (D / γ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hsplit : inner ℝ g (y - p) = (inner ℝ g y - inner ℝ g z) + inner ℝ g (z - p) := by
        rw [inner_sub_right, inner_sub_right]; ring
      rw [hsplit] at hsm
      have h3 := mul_le_mul_of_nonneg_left hco hη0
      have h4 : η i ^ 2 * ‖y - p‖ ^ 2 ≤ η i ^ 2 * (D / γ) ^ 2 :=
        mul_le_mul_of_nonneg_left hn2 (by positivity)
      have e5 : η i ^ 2 * (β * D ^ 2 / γ ^ 2) / 2 = β / 2 * (η i ^ 2 * (D / γ) ^ 2) := by
        rw [div_pow]; ring
      rw [e5]
      have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ β / 2)
      nlinarith
    calc Δ i ≤ ∑ t ∈ Finset.Icc 1 T,
          ((1 - η i) * (fhat t (x t (i - 1)) - fhat t (hstar (a t)))
          + η i * (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
              - inner ℝ (ghat t (x t (i - 1))) (hstar (a t)))
          + η i ^ 2 * (β * D ^ 2 / γ ^ 2) / 2) := Finset.sum_le_sum hpt
      _ = (1 - η i) * Δ (i - 1) + η i * ∑ t ∈ Finset.Icc 1 T,
            (inner ℝ (ghat t (x t (i - 1))) ((1 / γ) • W t i)
              - inner ℝ (ghat t (x t (i - 1))) (hstar (a t))) + η i ^ 2 * c / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hc, hΔ]
          simp only [Nat.add_sub_cancel]
          ring
      _ ≤ (1 - η i) * Δ (i - 1) + η i * E + η i ^ 2 * c / 2 := by
          have := mul_le_mul_of_nonneg_left (hwocl i hi1 hiN) hη0
          rw [hE]; linarith
  have hc0 : 0 ≤ c := by positivity
  have hfin := P57cc6451.recursion Δ η c E hc0 N hη hstep N hN le_rfl
  have hlhs : (∑ t ∈ Finset.Icc 1 T, fhat t (x t N)) - ∑ t ∈ Finset.Icc 1 T, fhat t (hstar (a t))
      = Δ N := by simp only [hΔ, Finset.sum_sub_distrib]
  rw [hlhs]
  have e : 2 * c / (N : ℝ) = (2 * β * D ^ 2 * T) / (γ ^ 2 * N) := by
    rw [hc]; field_simp
  rw [← e]
  exact hfin

open OnlineConvexOpt.OnlineBoosting OnlineConvexOpt.FirstOrder in
theorem solution
    {n : ℕ} (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (γ : ℝ) (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (δ : ℝ) (hδ : δ = Real.sqrt (D ^ 2 / (γ * N)))
    (η : ℕ → ℝ) (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (A : Type*) (a : ℕ → A) (H : Set (A → EuclideanSpace ℝ (Fin n))) (hHne : H.Nonempty)
    (hHK : ∀ h ∈ H, ∀ c : A, h c ∈ K)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hfG : ∀ t, ∀ x y, |f t x - f t y| ≤ G * dist x y)
    (W x : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (hW : ∀ t i, W t i ∈ K)
    (fstage : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (xplay : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsOnlineBoostingRun K γ δ G N T η a f W x fstage xplay)
    (RegretBoundW : ℝ)
    (hWOCL : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsGammaWOCL K γ T a H (fun t => W t i) (fun t y => fstage t i y / (2 * G * D))
        RegretBoundW)
    (hstar : A → EuclideanSpace ℝ (Fin n)) (hstar_mem : hstar ∈ convexHull ℝ H) :
    (∑ t ∈ Finset.Icc 1 T, f t (xplay t)) - ∑ t ∈ Finset.Icc 1 T, f t (hstar (a t)) ≤
      (8 * n * G * D * T) / (γ ^ (3 / 2 : ℝ) * Real.sqrt N) + (2 * G * D / γ) * RegretBoundW := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have harith := P6219dff5.final_arith n G D T γ N δ RegretBoundW hn1 hGpos hDpos
    (Nat.cast_nonneg T) hγpos hγ1 hNpos hδ
  have hδpos : 0 < δ := harith.1
  have hKne : K.Nonempty := ⟨0, h0K⟩
  set Fx : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun t y => f t y + G * Metric.infDist y K
    with hFx
  have hFxL : ∀ t, ∀ y z, |Fx t y - Fx t z| ≤ (2 * G) * dist y z := by
    intro t y z
    have h1 := hfG t y z
    have h2 : |Metric.infDist y K - Metric.infDist z K| ≤ dist y z := by
      have := (Metric.lipschitz_infDist_pt K).dist_le_mul y z
      rw [Real.dist_eq] at this
      simpa using this
    have e : Fx t y - Fx t z = (f t y - f t z) + G * (Metric.infDist y K - Metric.infDist z K) := by
      simp only [hFx]; ring
    rw [e]
    calc |(f t y - f t z) + G * (Metric.infDist y K - Metric.infDist z K)|
        ≤ |f t y - f t z| + |G * (Metric.infDist y K - Metric.infDist z K)| := abs_add_le _ _
      _ ≤ G * dist y z + G * dist y z := by
          rw [abs_mul, abs_of_pos hGpos]; gcongr
      _ = 2 * G * dist y z := by ring
  have hFxc : ∀ t, ConvexOn ℝ Set.univ (Fx t) := fun t =>
    (hfconv t).add ((P6219dff5.infDist_convex K hKconv hKne).smul hGpos.le)
  choose ghat hgrad hsm hcv hlip hclose using fun t =>
    P6219dff5.smoothed_facts hn (Fx t) (2 * G) (by linarith) (hFxL t) (hFxc t) δ hδpos
  have hfstage : ∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
      fstage t i = fun y => inner ℝ (ghat t (x t (i - 1))) y := fun t i h1 h2 h3 h4 =>
    hrun.2.2.2 t i h1 h2 h3 h4 (ghat t (x t (i - 1))) (hgrad t _)
  have key := P57cc6451.lemma125 K hKconv h0K D γ hDpos hD hγpos hγ1 N T hN hT
    (fun t => SmoothedFunction (Fx t) δ) (n * (2 * G) / δ) (2 * G) (by positivity) (by linarith)
    ghat hgrad hcv hsm hlip η hη a H hHne hHK W x hW hrun.1 hrun.2.1 fstage hfstage RegretBoundW
    hWOCL hstar hstar_mem
  -- per-round comparisons
  have hstarK : ∀ c : A, hstar c ∈ K := by
    intro c
    have hconv : Convex ℝ {h : A → EuclideanSpace ℝ (Fin n) | h c ∈ K} := by
      intro u hu v hv s r hs hr hsr
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply] at hu hv ⊢
      exact hKconv hu hv hs hr hsr
    exact convexHull_min (fun h hh => hHK h hh c) hconv hstar_mem
  have hplay : ∀ t ∈ Finset.Icc 1 T,
      f t (xplay t) ≤ SmoothedFunction (Fx t) δ (x t N) + 2 * G * δ := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨hpK, hpmin⟩ := hrun.2.2.1 t ht.1 ht.2
    have hd : dist (x t N) (xplay t) ≤ Metric.infDist (x t N) K :=
      (Metric.le_infDist hKne).2 hpmin
    have h1 : f t (xplay t) - f t (x t N) ≤ G * dist (xplay t) (x t N) :=
      le_trans (le_abs_self _) (hfG t _ _)
    have h2 := hclose t (x t N)
    have h3 : Fx t (x t N) = f t (x t N) + G * Metric.infDist (x t N) K := rfl
    rw [dist_comm] at h1
    have h4 : G * dist (x t N) (xplay t) ≤ G * Metric.infDist (x t N) K :=
      mul_le_mul_of_nonneg_left hd hGpos.le
    have h5 := (abs_le.1 h2).1
    linarith
  have hcomp : ∀ t ∈ Finset.Icc 1 T,
      SmoothedFunction (Fx t) δ (hstar (a t)) ≤ f t (hstar (a t)) + 2 * G * δ := by
    intro t _
    have h2 := hclose t (hstar (a t))
    have h3 : Fx t (hstar (a t)) = f t (hstar (a t)) := by
      simp only [hFx, Metric.infDist_zero_of_mem (hstarK (a t)), mul_zero, add_zero]
    rw [h3] at h2
    linarith [(abs_le.1 h2).2]
  have s1 := Finset.sum_le_sum hplay
  have s2 := Finset.sum_le_sum hcomp
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at s1 s2
  have hT' : ((T + 1 - 1 : ℕ) : ℝ) = T := by norm_cast
  rw [hT'] at s1 s2
  have hfin := harith.2
  linarith
