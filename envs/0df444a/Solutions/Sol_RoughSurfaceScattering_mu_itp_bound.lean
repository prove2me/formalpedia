-- Prove2me | solution 1 for RoughSurfaceScattering.mu_itp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T02:16:35.7098+00:00
-- url     : https://prove2.me/submissions/8e0d8ab9-c912-4e5f-986e-94a6e09d7d14
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_point_source_singularity
import Theorems.Thm_RoughSurfaceScattering_exists_c2_domain
import Theorems.Thm_RoughSurfaceScattering_itp_local_estimate
import Theorems.Thm_RoughSurfaceScattering_phi0_near_bounds
import Theorems.Thm_RoughSurfaceScattering_same_upper_boundary
import Theorems.Thm_RoughSurfaceScattering_h1Norm_sub_le

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

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

lemma IsC1On.mono' {S T : Set R2} {u : R2 → ℂ} {Du : R2 → (R2 →L[ℝ] ℂ)} (h : IsC1On S u Du)
    (hT : T ⊆ S) : IsC1On T u Du :=
  ⟨h.1.mono hT, h.2.1.mono hT, fun x hx => h.2.2 x (interior_mono hT hx)⟩

lemma l2_le_h1 (D : Set R2) (w : R2 → ℂ) : l2Norm D w ≤ h1Norm D w := by
  unfold l2Norm h1Norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
  rw [ENNReal.rpow_two]
  exact le_add_right (le_add_right le_rfl)

lemma h1Norm_mono_set {S T : Set R2} (hST : S ⊆ T) (w : R2 → ℂ) : h1Norm S w ≤ h1Norm T w := by
  unfold h1Norm
  exact ENNReal.rpow_le_rpow (lintegral_mono_set hST) (by norm_num)

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (hμ : μ1 ≠ μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ1 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ2 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) (s0 : ℝ) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
        ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
          h1Norm D0 (U1 (gpt f s0 - (δ / (j : ℝ)) • normal f s0)).2 ≤ ENNReal.ofReal C := by
  obtain ⟨δa, hδa, hA⟩ := point_source_singularity f hf lam hlam.1 hlam.2 hf' kp k1 μ1 hpar1 s0
  obtain ⟨δb, hδb, hB⟩ := point_source_singularity f hf lam hlam.1 hlam.2 hf' kp k2 μ2 hpar2 s0
  have hμ1 : 0 < μ1 := hpar1.2.2.1
  have hμ2 : 0 < μ2 := hpar2.2.2.1
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδ0 => ?_⟩
  obtain ⟨hxj, hA'⟩ := hA δ hδ (lt_of_lt_of_le hδ0 (min_le_left _ _))
  obtain ⟨-, hB'⟩ := hB δ hδ (lt_of_lt_of_le hδ0 (min_le_right _ _))
  obtain ⟨D0, hD0, hball, hsub⟩ := exists_c2_domain f hf lam hlam hf' s0 δ hδ
  refine ⟨D0, hD0, hball, hsub, ?_⟩
  set xj : ℕ → R2 := fun j => gpt f s0 - (δ / (j : ℝ)) • normal f s0 with hxjdef
  have hu1 : ∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k1 μ1
      (incData f (pointSource kp (xj j))).1 (incData f (pointSource kp (xj j))).2
      (U1 (xj j)).1 (U1 (xj j)).2 := fun j hj => hU1 _ (hxj j hj)
  have hu2 : ∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k2 μ2
      (incData f (pointSource kp (xj j))).1 (incData f (pointSource kp (xj j))).2
      (U2 (xj j)).1 (U2 (xj j)).2 := fun j hj => hU2 _ (hxj j hj)
  obtain ⟨C1, hC1⟩ := hA' D0 hD0 hball hsub (fun j => U1 (xj j)) hu1
  obtain ⟨C2, hC2⟩ := hB' D0 hD0 hball hsub (fun j => U2 (xj j)) hu2
  have hρ : 0 < μ1 / μ2 := div_pos hμ1 hμ2
  have hρ1 : μ1 / μ2 ≠ 1 := fun h => hμ ((div_eq_one_iff_eq hμ2.ne').mp h)
  obtain ⟨CB, hCB⟩ := itp_local_estimate f hf lam hlam hf' s0 δ hδ D0 hD0 hball hsub
    (μ1 / μ2) k1 k2 hρ hρ1
  set a1 : ℂ := ((2 / (μ1 + 1) : ℝ) : ℂ)
  set a2 : ℂ := ((2 / (μ2 + 1) : ℝ) : ℂ)
  obtain ⟨CΦ1, hCΦ1⟩ := phi0_near_bounds f hf s0 δ hδ D0 hD0.1 hD0.2.2.1 hsub hxj (-a1)
  obtain ⟨CΦ2, hCΦ2⟩ := phi0_near_bounds f hf s0 δ hδ D0 hD0.1 hD0.2.2.1 hsub hxj (-a2)
  set T1 := max C1 0 + max CΦ1 0
  set T2 := max C2 0 + max CΦ2 0
  refine ⟨max CB 0 * (2 * T1 + 2 * T2), fun j hj => ?_⟩
  have hDm : MeasurableSet D0 := hD0.1.measurableSet
  have hxjD : ∀ x ∈ D0, x ≠ xj j := fun x hx h => by
    have h1 := hsub hx; have h2 := hxj j hj
    rw [h] at h1
    simp only [Dminus, Dplus, Set.mem_setOf_eq] at h1 h2; linarith
  have hsubD : D0 ⊆ {x | x ≠ xj j} := fun x hx => hxjD x hx
  obtain ⟨-, -, -, -, -, -, -, hum1, -, -, -, hH1, -⟩ := hu1 j hj
  obtain ⟨-, -, -, -, -, -, -, hum2, -, -, -, hH2, -⟩ := hu2 j hj
  have hV2 : ContDiffOn ℝ 2 (U1 (xj j)).2 D0 := hum1.mono hsub
  have hW2 : ContDiffOn ℝ 2 (U2 (xj j)).2 D0 := hum2.mono hsub
  obtain ⟨DV, DW, hDV, hDW, hbd⟩ := same_upper_boundary f hf kp k1 k2 μ1 μ2 hpar1 hpar2 _ _ _ _ _ _
    (hu1 j hj) (hu2 j hj) (fun x hx => hagree x hx _ (hxj j hj))
  have hcl : closure D0 ∩ ball (gpt f s0) (2 * δ) ⊆ closure (Dminus f) :=
    fun x hx => closure_mono hsub hx.1
  have hitp := hCB _ _ DV DW hV2 hW2 (fun x hx => hH1 x (hsub hx)) (fun x hx => hH2 x (hsub hx))
    (IsC1On.mono' hDV hcl) (IsC1On.mono' hDW hcl) (fun s _ => hbd s)
  -- the singular parts
  have hΦ : ContDiffOn ℝ 1 (fun x => Phi 0 x (xj j)) D0 := (phi0_contDiffOn (xj j)).mono hsubD
  -- bounds for one scatterer
  have key : ∀ (V : R2 → ℂ) (a : ℂ) (C Cφ : ℝ), ContDiffOn ℝ 2 V D0 →
      h1Norm D0 (fun x => V x - a * Phi 0 x (xj j)) ≤ ENNReal.ofReal C →
      (l2Norm D0 (fun x => -a * Phi 0 x (xj j)) ≤ ENNReal.ofReal Cφ ∧
        h1Norm (D0 \ closedBall (gpt f s0) δ) (fun x => -a * Phi 0 x (xj j)) ≤ ENNReal.ofReal Cφ) →
      l2Norm D0 V ≤ ENNReal.ofReal (max C 0 + max Cφ 0) ∧
        h1Norm (D0 \ closedBall (gpt f s0) δ) V ≤ ENNReal.ofReal (max C 0 + max Cφ 0) := by
    intro V a C Cφ hV hC hφ
    have hv1 : ContDiffOn ℝ 1 (fun x => V x - a * Phi 0 x (xj j)) D0 :=
      (hV.of_le (by norm_num)).sub (contDiffOn_const.mul hΦ)
    have hw1 : ContDiffOn ℝ 1 (fun x => -a * Phi 0 x (xj j)) D0 := contDiffOn_const.mul hΦ
    have heq : V = (fun x => V x - a * Phi 0 x (xj j)) - (fun x => -a * Phi 0 x (xj j)) := by
      funext x; simp only [Pi.sub_apply]; ring
    have hsum : ENNReal.ofReal C + ENNReal.ofReal Cφ ≤ ENNReal.ofReal (max C 0 + max Cφ 0) := by
      rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
      exact add_le_add (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    constructor
    · rw [heq]
      unfold l2Norm
      refine (eLpNorm_sub_le (hv1.continuousOn.aestronglyMeasurable hDm)
        (hw1.continuousOn.aestronglyMeasurable hDm) (by norm_num)).trans ?_
      refine le_trans (add_le_add ((l2_le_h1 D0 _).trans hC) hφ.1) hsum
    · have hO : IsOpen (D0 \ closedBall (gpt f s0) δ) := hD0.1.sdiff isClosed_closedBall
      have hsd : D0 \ closedBall (gpt f s0) δ ⊆ D0 := Set.diff_subset
      have htri := h1Norm_sub_le _ hO _ _ (hv1.mono hsd) (hw1.mono hsd)
      have e : (fun x => (V x - a * Phi 0 x (xj j)) - -a * Phi 0 x (xj j)) = V := by
        funext x; ring
      rw [e] at htri
      exact htri.trans (le_trans (add_le_add ((h1Norm_mono_set hsd _).trans hC) hφ.2) hsum)
  obtain ⟨b1, b2⟩ := key _ a1 C1 CΦ1 hV2 (hC1 j hj) (hCΦ1 j hj)
  obtain ⟨b3, b4⟩ := key _ a2 C2 CΦ2 hW2 (hC2 j hj) (hCΦ2 j hj)
  calc h1Norm D0 (U1 (xj j)).2 ≤ h1Norm D0 (U1 (xj j)).2 + h1Norm D0 (U2 (xj j)).2 := le_self_add
    _ ≤ _ := hitp
    _ ≤ ENNReal.ofReal (max CB 0) * (ENNReal.ofReal T1 + ENNReal.ofReal T2 + ENNReal.ofReal T1 +
          ENNReal.ofReal T2) := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (max CB 0 * (2 * T1 + 2 * T2)) := by
        have hT1 : 0 ≤ T1 := by positivity
        have hT2 : 0 ≤ T2 := by positivity
        rw [← ENNReal.ofReal_add hT1 hT2, ← ENNReal.ofReal_add (by positivity) hT1,
          ← ENNReal.ofReal_add (by positivity) hT2, ← ENNReal.ofReal_mul (le_max_right _ _)]
        congr 1; ring
