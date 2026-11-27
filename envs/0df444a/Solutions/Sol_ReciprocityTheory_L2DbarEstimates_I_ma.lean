-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:32.593352+00:00
-- url     : https://prove2.me/submissions/fac1de3b-9d3c-4909-b074-47d0cc65e92f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_IntegrableWd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_integrable_wd
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_mul__a2b138e5ee83
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cHess_add_smul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_adj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_wd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cont_adj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_hasDerivAt_det
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_wd_zero_of_eqOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_wd_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (hCof : MACofStatement n) : MAStatement n := by
  intro Ω ph v hΩ hph hv hvc hsub
  have hvo : ContDiffOn ℝ ∞ v Ω := hv.contDiffOn
  have hP : ContDiffOn ℝ ∞ (fun w => (ph w : ℂ)) Ω := MongeAmpereIntegrability.cdo_ofReal hph
  have hQ : ContDiffOn ℝ ∞ (fun w => (v w : ℂ)) univ := MongeAmpereIntegrability.cdo_ofReal hv.contDiffOn
  have hKc : IsOpen (tsupport v)ᶜ := (isClosed_tsupport v).isOpen_compl
  have hv0 : ∀ w ∈ (tsupport v)ᶜ, (v w : ℂ) = 0 := fun w hw => by
    simp [image_eq_zero_of_notMem_tsupport hw]
  have hQ1 : ∀ k, ∀ w ∈ (tsupport v)ᶜ, wdb n k (fun w => (v w : ℂ)) w = 0 := fun k w hw =>
    (MongeAmpereIntegrability.wd_zero_of_eqOn hKc hv0 k hw).2
  have hB0 : ∀ y ∉ tsupport v, cHess n (fun w => (v w : ℂ)) y = 0 := by
    intro y hy
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact (MongeAmpereIntegrability.wd_zero_of_eqOn hKc (hQ1 k) j hy).1
  have hQ1c : ∀ k, ContDiffOn ℝ ∞ (wdb n k (fun w => (v w : ℂ))) univ := fun k =>
    (MongeAmpereIntegrability.cdo_wd isOpen_univ hQ k).2
  have hBc : ∀ j k, ContDiffOn ℝ ∞ (fun y => cHess n (fun w => (v w : ℂ)) y j k) univ := by
    intro j k
    simp only [cHess, Matrix.of_apply]
    exact (MongeAmpereIntegrability.cdo_wd isOpen_univ (hQ1c k) j).1
  have hAc : ∀ j k, ContDiffOn ℝ ∞ (fun y => cHess n (fun w => (ph w : ℂ)) y j k) Ω := by
    intro j k
    simp only [cHess, Matrix.of_apply]
    exact (MongeAmpereIntegrability.cdo_wd hΩ (MongeAmpereIntegrability.cdo_wd hΩ hP k).2 j).1
  set D : ℝ → V n → ℂ := fun t y => ∑ k, ∑ j,
    (cHess n (fun w => (ph w : ℂ)) y + (t : ℂ) • cHess n (fun w => (v w : ℂ)) y).adjugate k j *
      cHess n (fun w => (v w : ℂ)) y j k with hD
  have hD0 : ∀ t, ∀ y ∉ tsupport v, D t y = 0 := by
    intro t y hy
    simp [hD, hB0 y hy]
  have hm : ∀ y (t : ℝ), cHess n (fun w => (ph w : ℂ)) y + (t : ℂ) • cHess n (fun w => (v w : ℂ)) y =
      Matrix.of fun i j => cHess n (fun w => (ph w : ℂ)) y i j +
        (t : ℂ) * cHess n (fun w => (v w : ℂ)) y i j := by
    intro y t; ext i j; simp
  have hDc : ContinuousOn (fun p : V n × ℝ => D p.2 p.1) (Ω ×ˢ univ) := by
    simp only [hD, hm]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun j _ =>
      ContinuousOn.mul ?_ ?_
    · refine MongeAmpereIntegrability.cont_adj (fun i l (p : V n × ℝ) => cHess n (fun w => (ph w : ℂ)) p.1 i l +
        (p.2 : ℂ) * cHess n (fun w => (v w : ℂ)) p.1 i l) (fun i l => ?_) k j
      have h1 : ContinuousOn (fun p : V n × ℝ => cHess n (fun w => (ph w : ℂ)) p.1 i l)
          (Ω ×ˢ univ) := (hAc i l).continuousOn.comp continuousOn_fst fun p hp => hp.1
      have h2 : ContinuousOn (fun p : V n × ℝ => cHess n (fun w => (v w : ℂ)) p.1 i l)
          (Ω ×ˢ univ) := (hBc i l).continuousOn.comp continuousOn_fst fun p _ => mem_univ _
      have h3 : ContinuousOn (fun p : V n × ℝ => (p.2 : ℂ)) (Ω ×ˢ univ) :=
        (Complex.continuous_ofReal.comp continuous_snd).continuousOn
      exact h1.add (h3.mul h2)
    · exact (hBc j k).continuousOn.comp continuousOn_fst fun p _ => mem_univ _
  have hFTC : ∀ y, ∫ t in (0 : ℝ)..1, D t y =
      (cHess n (fun w => (ph w : ℂ)) y + cHess n (fun w => (v w : ℂ)) y).det -
        (cHess n (fun w => (ph w : ℂ)) y).det := by
    intro y
    have hcont : Continuous fun t : ℝ => D t y := by
      rw [← continuousOn_univ]
      simp only [hD, hm]
      refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun j _ =>
        ContinuousOn.mul ?_ continuousOn_const
      exact MongeAmpereIntegrability.cont_adj (fun i l (t : ℝ) => cHess n (fun w => (ph w : ℂ)) y i l +
        (t : ℂ) * cHess n (fun w => (v w : ℂ)) y i l)
        (fun i l => (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).continuousOn) k j
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => MongeAmpereIntegrability.hasDerivAt_det (cHess n (fun w => (ph w : ℂ)) y)
        (cHess n (fun w => (v w : ℂ)) y) t) (hcont.intervalIntegrable 0 1)]
    simp
  have hDint : ∀ t : ℝ, ∫ y in Ω, D t y = 0 := by
    intro t
    set f : V n → ℝ := fun w => ph w + t * v w with hf_def
    have hf : ContDiffOn ℝ ∞ f Ω := hph.add (contDiffOn_const.mul hvo)
    have hF : ContDiffOn ℝ ∞ (fun w => (f w : ℂ)) Ω := MongeAmpereIntegrability.cdo_ofReal hf
    have hHc : ∀ k j, ContDiffOn ℝ ∞
        (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) Ω := fun k j =>
      MongeAmpereIntegrability.cdo_adj (fun i l w => wd n i (wdb n l (fun w' => (f w' : ℂ))) w)
        (fun i l => (MongeAmpereIntegrability.cdo_wd hΩ (MongeAmpereIntegrability.cdo_wd hΩ hF l).2 i).1) k j
    set G : Fin n → Fin n → V n → ℂ := fun k j w =>
      (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j * wdb n k (fun w => (v w : ℂ)) w with hG
    have hG0 : ∀ k j, ∀ w ∉ tsupport v, G k j w = 0 := fun k j w hw => by
      simp [hG, hQ1 k w hw]
    have hGc : ∀ k j, ContDiff ℝ 1 (G k j) := by
      intro k j
      rw [contDiff_iff_contDiffAt]
      intro w
      by_cases hw : w ∈ Ω
      · exact (((hHc k j).mul ((hQ1c k).mono (subset_univ _))).contDiffAt
          (hΩ.mem_nhds hw)).of_le (by simp)
      · have hwK : w ∉ tsupport v := fun h => hw (hsub h)
        have he : G k j =ᶠ[𝓝 w] fun _ => (0 : ℂ) :=
          Filter.eventually_of_mem (hKc.mem_nhds hwK) fun x hx => hG0 k j x hx
        exact contDiffAt_const.congr_of_eventuallyEq he
    have hGs : ∀ k j, HasCompactSupport (G k j) := fun k j =>
      HasCompactSupport.intro hvc.isCompact (hG0 k j)
    have hpt : ∀ y, D t y = ∑ k, ∑ j, wd n j (G k j) y := by
      intro y
      by_cases hy : y ∈ Ω
      · have hHy : cHess n (fun w' => (f w' : ℂ)) y = cHess n (fun w => (ph w : ℂ)) y +
            (t : ℂ) • cHess n (fun w => (v w : ℂ)) y := MongeAmpereIntegrability.cHess_add_smul hΩ hph hvo t hy
        simp only [hD]
        rw [← hHy]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hc := hCof Ω f hΩ hf y hy k
        have d1 : ∀ j, DifferentiableAt ℝ
            (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y := fun j =>
          ((hHc k j).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
        have d2 : DifferentiableAt ℝ (wdb n k (fun w => (v w : ℂ))) y :=
          ((hQ1c k).differentiableOn (by simp)).differentiableAt Filter.univ_mem
        have e : ∀ j, wd n j (G k j) y =
            wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y *
              wdb n k (fun w => (v w : ℂ)) y +
            (cHess n (fun w' => (f w' : ℂ)) y).adjugate k j *
              wd n j (wdb n k (fun w => (v w : ℂ))) y := fun j =>
          ChartWirtingerDerivatives.wd_mul' n j _ _ y (d1 j) d2
        simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hc, zero_mul, zero_add]
        rfl
      · have hyK : y ∉ tsupport v := fun h => hy (hsub h)
        rw [hD0 t y hyK]
        symm
        refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
        exact (MongeAmpereIntegrability.wd_zero_of_eqOn hKc (hG0 k j) j hyK).1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hD0 t y (fun h => hy (hsub h)))]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun j _ =>
      MongeAmpereIntegrability.integrable_wd (hGc k j) (hGs k j) j)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_finsetSum _ (fun j _ => MongeAmpereIntegrability.integrable_wd (hGc k j) (hGs k j) j)]
    exact Finset.sum_eq_zero fun j _ => integral_wd_eq_zero n j (G k j) (hGc k j) (hGs k j)
  have hInt : Integrable (Function.uncurry fun (y : V n) (t : ℝ) => D t y)
      ((volume.restrict Ω).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := tsupport v ×ˢ Icc (0 : ℝ) 1) ?_
      (hΩ.measurableSet.prod measurableSet_Ioc) ?_
    · exact ContinuousOn.integrableOn_compact (hvc.isCompact.prod isCompact_Icc)
        (hDc.mono fun p hp => ⟨hsub hp.1, mem_univ _⟩)
    · rintro ⟨y, t⟩ ⟨⟨_, ht⟩, hn⟩
      have hyK : y ∉ tsupport v := fun h => hn ⟨h, Ioc_subset_Icc_self ht⟩
      exact hD0 t y hyK
  calc ∫ y in Ω, ((cHess n (fun w => ((ph w + v w : ℝ) : ℂ)) y).det -
        (cHess n (fun w => (ph w : ℂ)) y).det)
      = ∫ y in Ω, ∫ t in Ioc (0 : ℝ) 1, D t y := by
        refine setIntegral_congr_fun hΩ.measurableSet fun y hy => ?_
        have h1 := MongeAmpereIntegrability.cHess_add_smul hΩ hph hvo 1 hy
        simp only [one_mul, Complex.ofReal_one, one_smul] at h1
        rw [h1, ← intervalIntegral.integral_of_le zero_le_one, hFTC y]
    _ = ∫ t in Ioc (0 : ℝ) 1, ∫ y in Ω, D t y := integral_integral_swap hInt
    _ = 0 := by simp [hDint]
end ReciprocityTheory.L2DbarEstimates.I
