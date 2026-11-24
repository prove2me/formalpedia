-- Prove2me | solution 1 for RoughSurfaceScattering.lower_wavenumber_uniqueness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T03:44:46.097227+00:00
-- url     : https://prove2.me/submissions/b565e5d3-60ab-458e-800f-25ae4658d997
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_lower_wavenumber_itp_bound
import Theorems.Thm_RoughSurfaceScattering_dipole_l2_blowup
import Theorems.Thm_RoughSurfaceScattering_dipole_tsp_exists
import Theorems.Thm_RoughSurfaceScattering_vCorr_continuousOn
import Theorems.Thm_RoughSurfaceScattering_point_source_singularity
import Theorems.Thm_RoughSurfaceScattering_dipole_source_singularity

open MeasureTheory
open RoughSurfaceScattering

/-- The Laplace dipole `x ↦ ∇ₓΦ₀(x,z)·ν` is continuous away from the source point. -/
lemma dipole0_continuousOn (z ν : R2) :
    ContinuousOn (dipoleSource 0 z ν) {x | x ≠ z} := by
  have hopen : IsOpen {x : R2 | x ≠ z} := isOpen_ne
  have hcd : ContDiffOn ℝ 1 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
    intro x hx
    have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
    have hn : ContDiffAt ℝ 1 (fun x' : R2 => ‖x' - z‖) x :=
      (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
    have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
    have hinv : ContDiffAt ℝ 1 (fun x' : R2 => 1 / ‖x' - z‖) x := by
      have := (contDiffAt_inv ℝ hpos.ne').comp x hn
      simpa [one_div, Function.comp_def] using this
    have hlog : ContDiffAt ℝ 1 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
      (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
    have hreal : ContDiffAt ℝ 1
        (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
      contDiffAt_const.mul hlog
    have hc : ContDiffAt ℝ 1
        (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
    simpa [Phi] using hc.contDiffWithinAt
  have hfd := hcd.continuousOn_fderiv_of_isOpen hopen le_rfl
  exact (continuous_id.clm_apply continuous_const).comp_continuousOn hfd
    |>.congr (fun x _ => rfl)

/-- The `L²(D)` norm is bounded by the `H¹(D)` norm. -/
lemma l2Norm_le_h1Norm (D : Set R2) (w : R2 → ℂ) : l2Norm D w ≤ h1Norm D w := by
  unfold l2Norm h1Norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply lintegral_mono
  intro x
  simp only [ENNReal.rpow_two]
  exact le_add_right (le_add_right le_rfl)

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < 1 + deriv f s ^ 2 := by positivity
  have hpt : ‖pt (deriv f s) (-1)‖ = Real.sqrt (1 + deriv f s ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [pt, Fin.sum_univ_two]
    ring_nf
  rw [normal, norm_smul, hpt, arcDen, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'

lemma isOpen_Dplus (f : ℝ → ℝ) (hf : Continuous f) : IsOpen (Dplus f) := by
  unfold Dplus
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ : ℝ) (hpar1 : ParamCond kp k1 μ) (hpar2 : ParamCond kp k2 μ)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) :
    k1 = k2 := by
  classical
  by_contra hk
  -- thresholds from the interior transmission bound and from Theorems 5.2, 5.3
  obtain ⟨δ1, hδ1, hITP⟩ := lower_wavenumber_itp_bound f hf lam hlam hf' kp k1 k2 μ hpar1 hpar2
    hk U1 U2 hU1 hU2 hagree 0
  obtain ⟨δ2, hδ2, h53⟩ := dipole_source_singularity f hf lam hlam.1 hlam.2 hf' kp k1 μ hpar1 0
  obtain ⟨δ3, hδ3, h52⟩ := point_source_singularity f hf lam hlam.1 hlam.2 hf' kp k1 μ hpar1 0
  have hm0 : 0 < min δ1 (min δ2 δ3) := lt_min hδ1 (lt_min hδ2 hδ3)
  obtain ⟨δ, hδ, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < min δ1 (min δ2 δ3) :=
    ⟨min δ1 (min δ2 δ3) / 2, by linarith, by linarith⟩
  have hδ1' : δ < δ1 := lt_of_lt_of_le hδm (min_le_left _ _)
  have hδ2' : δ < δ2 := lt_of_lt_of_le hδm ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3' : δ < δ3 := lt_of_lt_of_le hδm ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hxj, -⟩ := h52 δ hδ hδ3'
  obtain ⟨hyj, h53'⟩ := h53 δ hδ hδ2'
  obtain ⟨D0, hD0, hsub, hsubD, hbd⟩ := hITP δ hδ hδ1'
  -- TSP solutions for the hypersingular point sources at x_j
  have hex : ∀ k : ℝ, ParamCond kp k μ → ∀ j : ℕ, 1 ≤ j → ∃ u : (R2 → ℂ) × (R2 → ℂ),
      IsTSPSolution f kp k μ
        (incData f (dipoleSource kp (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0))).1
        (incData f (dipoleSource kp (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0))).2
        u.1 u.2 :=
    fun k hk' j hj => dipole_tsp_exists f hf kp k μ hk' _ (hxj j hj) _
  let u1 : ℕ → (R2 → ℂ) × (R2 → ℂ) := fun j =>
    if hj : 1 ≤ j then (hex k1 hpar1 j hj).choose else (0, 0)
  let u2 : ℕ → (R2 → ℂ) × (R2 → ℂ) := fun j =>
    if hj : 1 ≤ j then (hex k2 hpar2 j hj).choose else (0, 0)
  have hu1 : ∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k1 μ
      (incData f (dipoleSource kp (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0))).1
      (incData f (dipoleSource kp (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0))).2
      (u1 j).1 (u1 j).2 := by
    intro j hj
    simp only [u1, dif_pos hj]
    exact (hex k1 hpar1 j hj).choose_spec
  have hu2 : ∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k2 μ
      (incData f (dipoleSource kp (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0))).1
      (incData f (dipoleSource kp (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0))).2
      (u2 j).1 (u2 j).2 := by
    intro j hj
    simp only [u2, dif_pos hj]
    exact (hex k2 hpar2 j hj).choose_spec
  obtain ⟨C1, hC1⟩ := hbd u1 u2 hu1 hu2
  obtain ⟨C2, hC2⟩ := h53' D0 hD0 hsub hsubD u1 hu1
  -- the blow-up of the Laplace dipole in L²(D₀)
  have hμ : 0 < μ := hpar1.2.2.1
  have ha : 0 < 2 / (μ + 1) := by positivity
  obtain ⟨j, hj, hblow⟩ := dipole_l2_blowup f hf 0 δ hδ D0 hsub
    ((2 / (μ + 1))⁻¹ * (max C1 0 + 2 * max C2 0))
  -- measurability on D₀
  have hDmeas : MeasurableSet D0 := hD0.1.measurableSet
  have hDisj : Disjoint (Dplus f) (Dminus f) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    simp only [Dplus, Dminus, Set.mem_setOf_eq] at h1 h2
    linarith
  have hxjD : ∀ x ∈ D0, x ≠ gpt f 0 - (δ / (j : ℝ)) • normal f 0 := by
    intro x hx h
    exact Set.disjoint_left.mp hDisj (h ▸ hxj j hj) (hsubD hx)
  have hdipc : ContinuousOn (dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0))
      D0 := (dipole0_continuousOn _ _).mono (fun x hx => hxjD x hx)
  have huc : ContinuousOn (u1 j).2 D0 := by
    obtain ⟨_, _, _, _, _, _, _, hum, -⟩ := hu1 j hj
    exact hum.continuousOn.mono hsubD
  have hxf : gpt f 0 - (δ / (j : ℝ)) • normal f 0 ∉ frontier D0 := by
    intro h
    have hcl : gpt f 0 - (δ / (j : ℝ)) • normal f 0 ∈ closure (Dminus f) :=
      closure_mono hsubD (frontier_subset_closure h)
    exact Set.disjoint_left.mp (hDisj.closure_right (isOpen_Dplus f hf.1.continuous))
      (hxj j hj) hcl
  have hyD : gpt f 0 + (δ / (j : ℝ)) • normal f 0 ∈ D0 := by
    apply hsub
    refine ⟨?_, hyj j hj⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, normal_norm, mul_one,
      Real.norm_of_nonneg (by positivity)]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    calc δ / (j : ℝ) ≤ δ := div_le_self hδ.le hj1
      _ < 2 * δ := by linarith
  have hyf : gpt f 0 + (δ / (j : ℝ)) • normal f 0 ∉ frontier D0 := by
    rw [hD0.1.frontier_eq]
    exact fun h => h.2 hyD
  have hvc := vCorr_continuousOn lam hlam μ D0 hD0 (normal f 0) _ _ hxf hyf
  have hu := huc.aestronglyMeasurable (μ := volume) hDmeas
  have hv := hvc.aestronglyMeasurable (μ := volume) hDmeas
  have hdip := hdipc.aestronglyMeasurable (μ := volume) hDmeas
  have hw : AEStronglyMeasurable (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
      dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0) x -
      vCorr μ D0 (normal f 0) (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
        (gpt f 0 + (δ / (j : ℝ)) • normal f 0) x) (volume.restrict D0) :=
    (hu.sub (aestronglyMeasurable_const.mul hdip)).sub hv
  have hid : (((2 / (μ + 1) : ℝ) : ℂ) •
      dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0)) =
      ((u1 j).2 - vCorr μ D0 (normal f 0) (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
        (gpt f 0 + (δ / (j : ℝ)) • normal f 0)) -
      (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
        dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0) x -
        vCorr μ D0 (normal f 0) (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
          (gpt f 0 + (δ / (j : ℝ)) • normal f 0) x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring
  have hnorm : ‖((2 / (μ + 1) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (2 / (μ + 1)) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hbound : ENNReal.ofReal (2 / (μ + 1)) *
      l2Norm D0 (dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0)) ≤
      ENNReal.ofReal C1 + ENNReal.ofReal C2 + ENNReal.ofReal C2 := by
    rw [← hnorm]
    unfold l2Norm
    rw [← eLpNorm_const_smul, hid]
    calc _ ≤ eLpNorm ((u1 j).2 - vCorr μ D0 (normal f 0) (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
            (gpt f 0 + (δ / (j : ℝ)) • normal f 0)) 2 (volume.restrict D0) +
          eLpNorm (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
            dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0) x -
            vCorr μ D0 (normal f 0) (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
              (gpt f 0 + (δ / (j : ℝ)) • normal f 0) x) 2 (volume.restrict D0) :=
          eLpNorm_sub_le (hu.sub hv) hw (by norm_num)
      _ ≤ (eLpNorm (u1 j).2 2 (volume.restrict D0) +
            eLpNorm (vCorr μ D0 (normal f 0) (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
              (gpt f 0 + (δ / (j : ℝ)) • normal f 0)) 2 (volume.restrict D0)) +
          eLpNorm (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
            dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0) x -
            vCorr μ D0 (normal f 0) (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
              (gpt f 0 + (δ / (j : ℝ)) • normal f 0) x) 2 (volume.restrict D0) := by
          gcongr
          exact eLpNorm_sub_le hu hv (by norm_num)
      _ ≤ (ENNReal.ofReal C1 + ENNReal.ofReal C2) + ENNReal.ofReal C2 := by
          gcongr
          · exact hC1 j hj
          · exact (hC2 j hj).2
          · exact (l2Norm_le_h1Norm _ _).trans (hC2 j hj).1
  -- contradiction with the blow-up
  have hlt : ENNReal.ofReal (2 / (μ + 1)) *
      ENNReal.ofReal ((2 / (μ + 1))⁻¹ * (max C1 0 + 2 * max C2 0)) <
      ENNReal.ofReal (2 / (μ + 1)) *
      l2Norm D0 (dipoleSource 0 (gpt f 0 - (δ / (j : ℝ)) • normal f 0) (normal f 0)) :=
    ENNReal.mul_lt_mul_right (by simpa using ha) ENNReal.ofReal_ne_top hblow
  have hleft : ENNReal.ofReal (2 / (μ + 1)) *
      ENNReal.ofReal ((2 / (μ + 1))⁻¹ * (max C1 0 + 2 * max C2 0)) =
      ENNReal.ofReal (max C1 0) + ENNReal.ofReal (max C2 0) + ENNReal.ofReal (max C2 0) := by
    rw [← ENNReal.ofReal_mul ha.le, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul,
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      ← ENNReal.ofReal_add (by positivity) (le_max_right _ _)]
    congr 1
    ring
  have hmax : ENNReal.ofReal C1 + ENNReal.ofReal C2 + ENNReal.ofReal C2 ≤
      ENNReal.ofReal (max C1 0) + ENNReal.ofReal (max C2 0) + ENNReal.ofReal (max C2 0) := by
    gcongr <;> exact le_max_left _ _
  exact absurd (hlt.trans_le (hbound.trans (hmax.trans hleft.symm.le))) (lt_irrefl _)
