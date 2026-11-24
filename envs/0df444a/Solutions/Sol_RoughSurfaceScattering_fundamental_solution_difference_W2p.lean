-- Prove2me | solution 1 for RoughSurfaceScattering.fundamental_solution_difference_W2p
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T15:56:16.459217+00:00
-- url     : https://prove2.me/submissions/fd6d0044-0682-4339-ba23-1425241547fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_weak_deriv_removable_point
import Theorems.Thm_RoughSurfaceScattering_fundamental_solution_difference_regular

open MeasureTheory Metric
open RoughSurfaceScattering

/-- A function continuous on a compact set and vanishing outside it is integrable. -/
lemma integrable_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : R2 → E) (K : Set R2) (hK : IsCompact K) (hc : ContinuousOn F K)
    (h0 : ∀ x, x ∉ K → F x = 0) : Integrable F := by
  have hind : Set.indicator K F = F := by
    funext x; by_cases hx : x ∈ K <;> simp [hx, h0 x]
  rw [← hind, integrable_indicator_iff hK.measurableSet]
  exact hc.integrableOn_compact hK

lemma fderiv_ofReal_apply (φ : R2 → ℝ) (hφ : Differentiable ℝ φ) (x v : R2) :
    fderiv ℝ (fun x => (φ x : ℂ)) x v = ((fderiv ℝ φ x v : ℝ) : ℂ) := by
  have := (Complex.ofRealCLM.hasFDerivAt (x := φ x)).comp x (hφ x).hasFDerivAt
  rw [show (fun x => (φ x : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, this.fderiv]
  simp

theorem solution (y : R2) (k k1 : ℝ) (hk : 0 ≤ k) (hk1 : 0 ≤ k1)
    (p : ENNReal) (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    MemW2p (Metric.ball y 1) p (fun x => Phi k1 x y - Phi k x y) := by
  obtain ⟨Dt, hDt, hC1, hd2, hLp0, hLp1, hLp2⟩ :=
    fundamental_solution_difference_regular y k k1 hk hk1 p hp1 hp
  set B := ball y (1 : ℝ) with hB
  have hBo : IsOpen B := isOpen_ball
  haveI : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- `D = Dt` almost everywhere
  have hne : ∀ᵐ x ∂(volume.restrict B), x ≠ y := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (measure_singleton y).le)
  have hae : (fun x => Phi k1 x y - Phi k x y) =ᵐ[volume.restrict B] Dt := by
    filter_upwards [hne] with x hx using (hDt x hx).symm
  have hDtc : ContinuousOn Dt B := hC1.continuousOn
  have hDfc : ContinuousOn (fderiv ℝ Dt) B := hC1.continuousOn_fderiv_of_isOpen hBo le_rfl
  have hDtd : ∀ x ∈ B, DifferentiableAt ℝ Dt x := fun x hx =>
    (hC1.differentiableOn one_ne_zero x hx).differentiableAt (hBo.mem_nhds hx)
  refine ⟨hLp0.ae_eq hae.symm, fun i => ⟨fun x => fderiv ℝ Dt x (EuclideanSpace.single i 1),
    hLp1 i, ?_, fun j => ⟨_, hLp2 i j, ?_⟩⟩⟩
  · -- first weak derivatives: integration by parts for the `C¹` function `Dt`
    intro φ hφ hcs hts
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    set e := EuclideanSpace.single i (1 : ℝ)
    have hK : IsCompact (tsupport φ) := hcs
    have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    have hdφ0 : ∀ x, x ∉ tsupport φ → fderiv ℝ φ x = 0 := fun x hx =>
      Function.notMem_support.mp fun h => hx (support_fderiv_subset ℝ h)
    have hφc : Continuous φ := hφd.continuous
    have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
    rw [integral_congr_ae (hae.mono fun x hx => by rw [hx])]
    -- pass to integrals over the whole plane
    have hout1 : ∀ x, x ∉ B → Dt x * ((fderiv ℝ φ x e : ℝ) : ℂ) = 0 := fun x hx => by
      rw [hdφ0 x fun h => hx (hts h)]; simp
    have hout2 : ∀ x, x ∉ B → fderiv ℝ Dt x e * (φ x : ℂ) = 0 := fun x hx => by
      rw [hφ0 x fun h => hx (hts h)]; simp
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout1,
      setIntegral_eq_integral_of_forall_compl_eq_zero hout2]
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := Dt) (g := fun x => (φ x : ℂ)) (v := e)
      (integrable_of_compact _ _ hK
        (((hDfc.mono hts).clm_apply continuousOn_const).mul
          (Complex.continuous_ofReal.comp hφc).continuousOn)
        fun x hx => by simp [hφ0 x hx])
      (integrable_of_compact _ _ hK
        ((hDtc.mono hts).mul (by
          simp only [fderiv_ofReal_apply φ hφd]
          exact (Complex.continuous_ofReal.comp
            (hdφc.clm_apply continuous_const)).continuousOn))
        fun x hx => by simp [fderiv_ofReal_apply φ hφd, hdφ0 x hx])
      (integrable_of_compact _ _ hK ((hDtc.mono hts).mul
          (Complex.continuous_ofReal.comp hφc).continuousOn)
        fun x hx => by simp [hφ0 x hx])
      (fun x hx => hDtd x (hts (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero φ hx)))
      (fun x _ => by
        simpa [Function.comp_def] using Complex.ofRealCLM.differentiableAt.comp x (hφd x))
    simp only [fderiv_ofReal_apply φ hφd] at hibp
    exact hibp
  · -- second weak derivatives: the point `y` is removable
    exact weak_deriv_removable_point B hBo y _
      ((hDfc.clm_apply continuousOn_const))
      (fun x hx hxy => hd2 i x hx hxy) _ ((hLp2 i j).integrable hp1)
