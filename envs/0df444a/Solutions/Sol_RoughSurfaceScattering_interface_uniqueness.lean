-- Prove2me | solution 1 for RoughSurfaceScattering.interface_uniqueness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:01:55.809346+00:00
-- url     : https://prove2.me/submissions/1edd5002-d4eb-428f-8d29-f92279b5e608
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_interface_itp_bound_point
import Theorems.Thm_RoughSurfaceScattering_interface_itp_bound_dipole
import Theorems.Thm_RoughSurfaceScattering_helmholtz_h1_blowup
import Theorems.Thm_RoughSurfaceScattering_laplace_l2_bound
import Theorems.Thm_RoughSurfaceScattering_phi_contDiffOn
import Theorems.Thm_RoughSurfaceScattering_h1Norm_sub_le
import Theorems.Thm_RoughSurfaceScattering_dipole_l2_blowup
import Theorems.Thm_RoughSurfaceScattering_dipole_tsp_exists
import Theorems.Thm_RoughSurfaceScattering_vCorr_continuousOn
import Theorems.Thm_RoughSurfaceScattering_point_source_singularity
import Theorems.Thm_RoughSurfaceScattering_dipole_source_singularity

open MeasureTheory
open RoughSurfaceScattering

/-- `x ↦ Φ₀(x,z)` is `C¹` away from the source point. -/
lemma phi0_contDiffOn (z : R2) :
    ContDiffOn ℝ 1 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
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

/-- The Laplace dipole `x ↦ ∇ₓΦ₀(x,z)·ν` is continuous away from the source point. -/
lemma dipole0_continuousOn (z ν : R2) :
    ContinuousOn (dipoleSource 0 z ν) {x | x ≠ z} := by
  have hfd := (phi0_contDiffOn z).continuousOn_fderiv_of_isOpen isOpen_ne le_rfl
  exact (continuous_id.clm_apply continuous_const).comp_continuousOn hfd
    |>.congr (fun x _ => rfl)

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

lemma disjoint_Dplus_Dminus (f : ℝ → ℝ) : Disjoint (Dplus f) (Dminus f) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  simp only [Dplus, Dminus, Set.mem_setOf_eq] at h1 h2
  linarith

/-- The contradiction of part (ii)(a)/(iii): an interior-transmission `L²` bound for the
transmitted fields of the hypersingular sources at `x_j` is incompatible with Theorem 5.3 and
the blow-up of the Laplace dipole. -/
lemma dipole_bound_false (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ)
    (hITP : ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
        ∀ u1 : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u1 j).1 (u1 j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j → l2Norm D0 (u1 j).2 ≤ ENNReal.ofReal C) : False := by
  classical
  obtain ⟨δ1, hδ1, hITP⟩ := hITP
  obtain ⟨δ2, hδ2, h53⟩ := dipole_source_singularity f hf lam hlam.1 hlam.2 hf' kp km μ hpar s0
  obtain ⟨δ3, hδ3, h52⟩ := point_source_singularity f hf lam hlam.1 hlam.2 hf' kp km μ hpar s0
  have hm0 : 0 < min δ1 (min δ2 δ3) := lt_min hδ1 (lt_min hδ2 hδ3)
  obtain ⟨δ, hδ, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < min δ1 (min δ2 δ3) :=
    ⟨min δ1 (min δ2 δ3) / 2, by linarith, by linarith⟩
  have hδ1' : δ < δ1 := lt_of_lt_of_le hδm (min_le_left _ _)
  have hδ2' : δ < δ2 := lt_of_lt_of_le hδm ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3' : δ < δ3 := lt_of_lt_of_le hδm ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hxj, -⟩ := h52 δ hδ hδ3'
  obtain ⟨hyj, h53'⟩ := h53 δ hδ hδ2'
  obtain ⟨D0, hD0, hsub, hsubD, hbd⟩ := hITP δ hδ hδ1'
  have hex : ∀ j : ℕ, 1 ≤ j → ∃ u : (R2 → ℂ) × (R2 → ℂ),
      IsTSPSolution f kp km μ
        (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
        (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
        u.1 u.2 :=
    fun j hj => dipole_tsp_exists f hf kp km μ hpar _ (hxj j hj) _
  let u1 : ℕ → (R2 → ℂ) × (R2 → ℂ) := fun j =>
    if hj : 1 ≤ j then (hex j hj).choose else (0, 0)
  have hu1 : ∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
      (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
      (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
      (u1 j).1 (u1 j).2 := by
    intro j hj
    simp only [u1, dif_pos hj]
    exact (hex j hj).choose_spec
  obtain ⟨C1, hC1⟩ := hbd u1 hu1
  obtain ⟨C2, hC2⟩ := h53' D0 hD0 hsub hsubD u1 hu1
  have hμ : 0 < μ := hpar.2.2.1
  have ha : 0 < 2 / (μ + 1) := by positivity
  obtain ⟨j, hj, hblow⟩ := dipole_l2_blowup f hf s0 δ hδ D0 hsub
    ((2 / (μ + 1))⁻¹ * (max C1 0 + 2 * max C2 0))
  have hDmeas : MeasurableSet D0 := hD0.1.measurableSet
  have hDisj := disjoint_Dplus_Dminus f
  have hxjD : ∀ x ∈ D0, x ≠ gpt f s0 - (δ / (j : ℝ)) • normal f s0 := by
    intro x hx h
    exact Set.disjoint_left.mp hDisj (h ▸ hxj j hj) (hsubD hx)
  have hdipc : ContinuousOn
      (dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0)) D0 :=
    (dipole0_continuousOn _ _).mono (fun x hx => hxjD x hx)
  have huc : ContinuousOn (u1 j).2 D0 := by
    obtain ⟨_, _, _, _, _, _, _, hum, -⟩ := hu1 j hj
    exact hum.continuousOn.mono hsubD
  have hxf : gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∉ frontier D0 := by
    intro h
    have hcl : gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∈ closure (Dminus f) :=
      closure_mono hsubD (frontier_subset_closure h)
    exact Set.disjoint_left.mp (hDisj.closure_right (isOpen_Dplus f hf.1.continuous))
      (hxj j hj) hcl
  have hyD : gpt f s0 + (δ / (j : ℝ)) • normal f s0 ∈ D0 := by
    apply hsub
    refine ⟨?_, hyj j hj⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, normal_norm, mul_one,
      Real.norm_of_nonneg (by positivity)]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    calc δ / (j : ℝ) ≤ δ := div_le_self hδ.le hj1
      _ < 2 * δ := by linarith
  have hyf : gpt f s0 + (δ / (j : ℝ)) • normal f s0 ∉ frontier D0 := by
    rw [hD0.1.frontier_eq]
    exact fun h => h.2 hyD
  have hvc := vCorr_continuousOn lam hlam μ D0 hD0 (normal f s0) _ _ hxf hyf
  have hu := huc.aestronglyMeasurable (μ := volume) hDmeas
  have hv := hvc.aestronglyMeasurable (μ := volume) hDmeas
  have hdip := hdipc.aestronglyMeasurable (μ := volume) hDmeas
  have hw : AEStronglyMeasurable (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
      dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
      vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
        (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) (volume.restrict D0) :=
    (hu.sub (aestronglyMeasurable_const.mul hdip)).sub hv
  have hid : (((2 / (μ + 1) : ℝ) : ℂ) •
      dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0)) =
      ((u1 j).2 - vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
        (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) -
      (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
        dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
        vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
          (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring
  have hnorm : ‖((2 / (μ + 1) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (2 / (μ + 1)) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hbound : ENNReal.ofReal (2 / (μ + 1)) *
      l2Norm D0 (dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0)) ≤
      ENNReal.ofReal C1 + ENNReal.ofReal C2 + ENNReal.ofReal C2 := by
    rw [← hnorm]
    unfold l2Norm
    rw [← eLpNorm_const_smul, hid]
    calc _ ≤ eLpNorm ((u1 j).2 - vCorr μ D0 (normal f s0)
            (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
            (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) 2 (volume.restrict D0) +
          eLpNorm (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
            dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
            vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
              (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) 2 (volume.restrict D0) :=
          eLpNorm_sub_le (hu.sub hv) hw (by norm_num)
      _ ≤ (eLpNorm (u1 j).2 2 (volume.restrict D0) +
            eLpNorm (vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
              (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) 2 (volume.restrict D0)) +
          eLpNorm (fun x => (u1 j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
            dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
            vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
              (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) 2 (volume.restrict D0) := by
          gcongr
          exact eLpNorm_sub_le hu hv (by norm_num)
      _ ≤ (ENNReal.ofReal C1 + ENNReal.ofReal C2) + ENNReal.ofReal C2 := by
          gcongr
          · exact hC1 j hj
          · exact (hC2 j hj).2
          · exact (l2Norm_le_h1Norm _ _).trans (hC2 j hj).1
  have hlt : ENNReal.ofReal (2 / (μ + 1)) *
      ENNReal.ofReal ((2 / (μ + 1))⁻¹ * (max C1 0 + 2 * max C2 0)) <
      ENNReal.ofReal (2 / (μ + 1)) *
      l2Norm D0 (dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0)) :=
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

/-- Part (i): with `μ₁ ≠ 1`, the interior transmission bound (6.2) together with Theorem 5.2
bounds `Φ_{k₊}(·, x_j)` in `H¹(D₀)`, which is impossible. -/
lemma interface_point_false (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (hμ1 : μ1 ≠ 1)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x)
    (s0 : ℝ) (hs : f2 s0 < f1 s0) : False := by
  obtain ⟨δ1, hδ1, hA⟩ := interface_itp_bound_point f1 f2 hf1 hf2 lam1 lam2 hlam1 hlam2 hf1' hf2'
    kp k1 k2 μ1 μ2 hpar1 hpar2 hμ1 U1 U2 hU1 hU2 hagree s0 hs
  obtain ⟨δ2, hδ2, h52⟩ := point_source_singularity f1 hf1 lam1 hlam1.1 hlam1.2 hf1' kp k1 μ1
    hpar1 s0
  obtain ⟨δ, hδ, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < min δ1 δ2 :=
    ⟨min δ1 δ2 / 2, by have := lt_min hδ1 hδ2; linarith,
      by have := lt_min hδ1 hδ2; linarith⟩
  have hδ1' : δ < δ1 := lt_of_lt_of_le hδm (min_le_left _ _)
  have hδ2' : δ < δ2 := lt_of_lt_of_le hδm (min_le_right _ _)
  obtain ⟨hxj2, D0, hD0, hsub, hsubD, hD0p, hA'⟩ := hA δ hδ hδ1'
  obtain ⟨hxj1, h52'⟩ := h52 δ hδ hδ2'
  -- Theorem 5.2 for the family `j ↦ U1 x_j`
  obtain ⟨C2, hC2⟩ := h52' D0 hD0 hsub hsubD
    (fun j => U1 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)) (fun j hj => hU1 _ (hxj1 j hj))
  have hμ : 0 < μ1 := hpar1.2.2.1
  obtain ⟨C4, hC4⟩ := laplace_l2_bound f1 s0 δ D0 hD0.2.2.1 (2 / (μ1 + 1))
  have hDmeas : MeasurableSet D0 := hD0.1.measurableSet
  have hxjD : ∀ j : ℕ, 1 ≤ j → ∀ x ∈ D0, x ≠ gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0 := by
    intro j hj x hx h
    exact Set.disjoint_left.mp (disjoint_Dplus_Dminus f1) (h ▸ hxj1 j hj) (hsubD hx)
  -- the transmitted fields `u₁₋(·, x_j)` are bounded in `L²(D₀)`
  have hL2 : ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
      l2Norm D0 (U1 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).2 ≤ ENNReal.ofReal C := by
    refine ⟨max C2 0 + max C4 0, fun j hj => ?_⟩
    have huc : ContDiffOn ℝ 1 (U1 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).2 D0 := by
      obtain ⟨_, _, _, _, _, _, _, hum, -⟩ := hU1 _ (hxj1 j hj)
      exact (hum.of_le (by norm_num)).mono hsubD
    have hphic : ContDiffOn ℝ 1 (fun x => ((2 / (μ1 + 1) : ℝ) : ℂ) *
        Phi 0 x (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)) D0 :=
      contDiffOn_const.mul ((phi0_contDiffOn _).mono (fun x hx => hxjD j hj x hx))
    have hw := (huc.sub hphic).continuousOn.aestronglyMeasurable (μ := volume) hDmeas
    have hp := hphic.continuousOn.aestronglyMeasurable (μ := volume) hDmeas
    have he : (U1 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).2 =
        (fun x => (U1 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).2 x -
          ((2 / (μ1 + 1) : ℝ) : ℂ) * Phi 0 x (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)) +
        (fun x => ((2 / (μ1 + 1) : ℝ) : ℂ) *
          Phi 0 x (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)) := by
      funext x
      simp only [Pi.add_apply]
      ring
    unfold l2Norm
    rw [he, ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine (eLpNorm_add_le hw hp (by norm_num)).trans (add_le_add ?_ ?_)
    · exact (l2Norm_le_h1Norm _ _).trans ((hC2 j hj).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    · exact (hC4 j hj).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- interior transmission estimate (6.2) and Theorem 4.3
  obtain ⟨C', hC'⟩ := hA' hL2
  obtain ⟨j, hj, hblow⟩ := helmholtz_h1_blowup f1 hf1 s0 δ hδ D0 hsub kp hpar1.1
    (max C' 0 + max C' 0)
  have hS : ContDiffOn ℝ 1 (U2 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).1 D0 := by
    obtain ⟨_, _, _, _, _, _, hup, -⟩ := hU2 _ (hxj2 j hj)
    exact (hup.of_le (by norm_num)).mono hD0p
  have hT : ContDiffOn ℝ 1 (fun x => pointSource kp (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0) x +
      (U2 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).1 x) D0 :=
    ((phi_contDiffOn kp hpar1.1 _).mono (fun x hx => hxjD j hj x hx)).add hS
  have htri := h1Norm_sub_le D0 hD0.1 _ _ hT hS
  have heq : (fun x => (pointSource kp (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0) x +
      (U2 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).1 x) -
      (U2 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).1 x) =
      (fun x => Phi kp x (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)) := by
    funext x
    simp [pointSource]
  rw [heq] at htri
  have hbound : h1Norm D0 (fun x => Phi kp x (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)) ≤
      ENNReal.ofReal (max C' 0 + max C' 0) := by
    rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine htri.trans (add_le_add ((hC' j hj).1.trans ?_) ((hC' j hj).2.trans ?_)) <;>
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  exact absurd (hblow.trans_le hbound) (lt_irrefl _)

/-- If `f₂(s₀) < f₁(s₀)`, the data cannot agree (parts (i) and (ii)(a)). -/
lemma interface_false (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x)
    (s0 : ℝ) (hs : f2 s0 < f1 s0) : False := by
  by_cases hμ1 : μ1 = 1
  · exact dipole_bound_false f1 hf1 lam1 hlam1 hf1' kp k1 μ1 hpar1 s0
      (interface_itp_bound_dipole f1 f2 hf1 hf2 lam1 lam2 hlam1 hlam2 hf1' hf2' kp k1 k2 μ1 μ2
        hpar1 hpar2 hμ1 U1 U2 hU1 hU2 hagree s0 hs)
  · exact interface_point_false f1 f2 hf1 hf2 lam1 lam2 hlam1 hlam2 hf1' hf2' kp k1 k2 μ1 μ2
      hpar1 hpar2 hμ1 U1 U2 hU1 hU2 hagree s0 hs

theorem solution (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x) :
    f1 = f2 := by
  by_contra hne
  obtain ⟨s0, hs0⟩ := Function.ne_iff.mp hne
  rcases lt_or_gt_of_ne hs0 with h | h
  · -- `f₁(s₀) < f₂(s₀)`: the roles of the two scatterers are exchanged
    exact interface_false f2 f1 hf2 hf1 lam2 lam1 hlam2 hlam1 hf2' hf1' kp k2 k1 μ2 μ1 hpar2 hpar1
      U2 U1 hU2 hU1 (fun x hx y hy => (hagree x ⟨hx.2, hx.1⟩ y ⟨hy.2, hy.1⟩).symm) s0 h
  · exact interface_false f1 f2 hf1 hf2 lam1 lam2 hlam1 hlam2 hf1' hf2' kp k1 k2 μ1 μ2 hpar1 hpar2
      U1 U2 hU1 hU2 hagree s0 h
