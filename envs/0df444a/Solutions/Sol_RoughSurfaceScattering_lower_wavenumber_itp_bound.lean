-- Prove2me | solution 1 for RoughSurfaceScattering.lower_wavenumber_itp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T02:28:01.665094+00:00
-- url     : https://prove2.me/submissions/03fa8a53-28bb-4e52-b8ce-2368e7a8bd23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_itp_small_domain_l2
import Theorems.Thm_RoughSurfaceScattering_dipole_upper_agree
import Theorems.Thm_RoughSurfaceScattering_dipole_away_h1
import Theorems.Thm_RoughSurfaceScattering_same_upper_boundary

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

lemma abs_coord_le_norm (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < arcDen f s := Real.sqrt_pos.mpr (by positivity)
  have hpt : ‖pt (deriv f s) (-1)‖ = arcDen f s := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [pt, arcDen]
    ring_nf
  rw [normal, norm_smul, hpt, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- Mirror of `cone_below_interface`: points in a cone around `-n` lie above `Γ`. -/
lemma cone_above_interface (f : ℝ → ℝ) (s0 : ℝ) (hf : DifferentiableAt ℝ f s0) :
    ∃ r > (0 : ℝ), ∀ v : R2, v ≠ 0 → ‖v‖ < r →
      ‖v‖ ≤ -(2 * @inner ℝ R2 _ v (normal f s0)) → gpt f s0 + v ∈ Dplus f := by
  set d := deriv f s0 with hd
  set a := arcDen f s0 with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hlo := hf.hasDerivAt.isLittleO
  have hev := hlo.def (c := a / 4) (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, fun v hv0 hvr hcone => ?_⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hinner : @inner ℝ R2 _ v (normal f s0) = a⁻¹ * (d * v 0 - v 1) := by
    simp [normal, pt, ← ha, ← hd, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_right]
    ring_nf
    try simp
  rw [hinner] at hcone
  have hkey : a * ‖v‖ ≤ 2 * (v 1 - d * v 0) := by
    have := mul_le_mul_of_nonneg_left hcone hapos.le
    calc a * ‖v‖ ≤ a * -(2 * (a⁻¹ * (d * v 0 - v 1))) := this
      _ = 2 * (v 1 - d * v 0) := by field_simp; ring
  have h0 := abs_coord_le_norm v 0
  have hdist : dist (s0 + v 0) s0 < r := by
    rw [Real.dist_eq, add_sub_cancel_left]; linarith
  have htay := hball hdist
  simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul] at htay
  have hup : f (s0 + v 0) ≤ f s0 + v 0 * d + a / 4 * |v 0| := by
    have := (abs_le.mp htay).2
    linarith
  show f ((gpt f s0 + v) 0) < (gpt f s0 + v) 1
  simp only [gpt, pt, PiLp.add_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have : a / 4 * |v 0| ≤ a / 4 * ‖v‖ := mul_le_mul_of_nonneg_left h0 (by positivity)
  nlinarith


lemma IsC1On.mono' {S T : Set R2} {u : R2 → ℂ} {Du : R2 → (R2 →L[ℝ] ℂ)} (h : IsC1On S u Du)
    (hT : T ⊆ S) : IsC1On T u Du :=
  ⟨h.1.mono hT, h.2.1.mono hT, fun x hx => h.2.2 x (interior_mono hT hx)⟩

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ : ℝ) (hpar1 : ParamCond kp k1 μ) (hpar2 : ParamCond kp k2 μ) (hk : k1 ≠ k2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) (s0 : ℝ) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
        ∀ u1 u2 : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k1 μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u1 j).1 (u1 j).2) →
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k2 μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u2 j).1 (u2 j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j → l2Norm D0 (u1 j).2 ≤ ENNReal.ofReal C := by
  have hk1 : 0 < k1 := hpar1.2.1
  have hk2 : 0 < k2 := hpar2.2.1
  have hμ : 0 < μ := hpar1.2.2.1
  obtain ⟨r, hr, hcone⟩ := cone_above_interface f s0 (hf.1 s0)
  obtain ⟨δa, hδa, hA⟩ := itp_small_domain_l2 f hf lam hlam hf' s0 k1 k2 hk1 hk2 hk
  obtain ⟨δb, hδb, hB⟩ := dipole_away_h1 f hf lam hlam.1 hlam.2 hf' kp k1 μ hpar1 s0
  obtain ⟨δc, hδc, hC⟩ := dipole_away_h1 f hf lam hlam.1 hlam.2 hf' kp k2 μ hpar2 s0
  refine ⟨min (min r δa) (min δb δc), lt_min (lt_min hr hδa) (lt_min hδb hδc),
    fun δ hδ hδ0 => ?_⟩
  have hδr : δ < r := lt_of_lt_of_le hδ0 ((min_le_left _ _).trans (min_le_left _ _))
  have hδa' : δ < δa := lt_of_lt_of_le hδ0 ((min_le_left _ _).trans (min_le_right _ _))
  have hδb' : δ < δb := lt_of_lt_of_le hδ0 ((min_le_right _ _).trans (min_le_left _ _))
  have hδc' : δ < δc := lt_of_lt_of_le hδ0 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨D0, hD0, hball, hsub, CA, hCA⟩ := hA δ hδ hδa'
  refine ⟨D0, hD0, hball, hsub, fun u1 u2 hu1 hu2 => ?_⟩
  obtain ⟨C1, hC1⟩ := hB δ hδ hδb' D0 hD0 hball hsub u1 hu1
  obtain ⟨C2, hC2⟩ := hC δ hδ hδc' D0 hD0 hball hsub u2 hu2
  refine ⟨max CA 0 * (max C1 0 + max C2 0), fun j hj => ?_⟩
  -- the source point lies above `Γ`
  have hn1 := normal_norm f s0
  have hn0 : normal f s0 ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 < δ / (j : ℝ) := by positivity
  have hnv : ‖-((δ / (j : ℝ)) • normal f s0)‖ = δ / j := by
    rw [norm_neg, norm_smul, hn1, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  have hxj : gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∈ Dplus f := by
    have := hcone (-((δ / (j : ℝ)) • normal f s0))
      (by rw [neg_ne_zero]; exact smul_ne_zero ht.ne' hn0)
      (by rw [hnv]; linarith [div_le_self hδ.le hj'])
      (by
        rw [hnv, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq, hn1]
        simp only [one_pow, mul_one, RCLike.conj_to_real]
        linarith)
    rwa [← sub_eq_add_neg] at this
  have hag := dipole_upper_agree f hf kp k1 k2 μ μ hpar1 hpar2 U1 U2 hU1 hU2 hagree _ hxj
    (normal f s0) (u1 j) (u2 j) (hu1 j hj) (hu2 j hj)
  obtain ⟨DV, DW, hDV, hDW, hbd⟩ := same_upper_boundary f hf kp k1 k2 μ μ hpar1 hpar2 _ _ _ _ _ _
    (hu1 j hj) (hu2 j hj) hag
  obtain ⟨-, -, -, -, -, -, -, hum1, -, -, -, hH1, -⟩ := hu1 j hj
  obtain ⟨-, -, -, -, -, -, -, hum2, -, -, -, hH2, -⟩ := hu2 j hj
  have hcl : closure D0 ∩ ball (gpt f s0) (2 * δ) ⊆ closure (Dminus f) :=
    fun x hx => closure_mono hsub hx.1
  have hitp := hCA (u1 j).2 (u2 j).2 DV DW (hum1.mono hsub) (hum2.mono hsub)
    (fun x hx => hH1 x (hsub hx)) (fun x hx => hH2 x (hsub hx))
    (IsC1On.mono' hDV hcl) (IsC1On.mono' hDW hcl) (fun s _ => by
      obtain ⟨h1, h2⟩ := hbd s
      refine ⟨h1, ?_⟩
      rw [div_self hμ.ne', Complex.ofReal_one, one_mul] at h2
      exact h2)
  calc l2Norm D0 (u1 j).2 ≤ l2Norm D0 (u1 j).2 + l2Norm D0 (u2 j).2 := le_self_add
    _ ≤ _ := hitp
    _ ≤ ENNReal.ofReal (max CA 0) * (ENNReal.ofReal (max C1 0) + ENNReal.ofReal (max C2 0)) := by
        gcongr
        · exact le_max_left _ _
        · exact (hC1 j hj).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        · exact (hC2 j hj).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (max CA 0 * (max C1 0 + max C2 0)) := by
        rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
          ← ENNReal.ofReal_mul (le_max_right _ _)]
