-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.hormander
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:22:25.489276+00:00
-- url     : https://prove2.me/submissions/194ce880-6ebe-484d-b796-43f8c1bad984

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_Hormander
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_inner_toLp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_ipV_single
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_norm_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_single_isTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_tstar_single
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_sub_weightedL2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_rieszOnRange
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_db_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hTI : TestIneqStatement n M) (hReg : RegMStatement n M) :
    HStatement n M := by
  intro X ph F0 h hph hlevi hF0 hh hpt
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hphc : Continuous ph := gm_cont_of_smoothR n X.z hz ph hph
  have hphm : Measurable ph := hphc.measurable
  have hF0c : Continuous F0 := Smooth.continuous n X.z hz F0 hF0
  by_cases hA : (∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n X.z) = ⊤
  · exact ⟨fun _ => 0, Holo.const n X.z 0, by rw [hA]; exact le_top⟩
  set Ae := ∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n X.z with hAe
  have hAe' : ENNReal.ofReal Ae.toReal = Ae := ENNReal.ofReal_toReal hA
  have hv : Continuous (dbarF n X.z F0) :=
    gm_form_continuous _ fun k => Smooth.continuous n X.z hz _ (Smooth.db n X.z k F0 hF0)

  have hθ : ∀ e : gmTestForms n X.z,
      ENNReal.ofReal (‖gmTheta n X.z hz ph hph e‖ ^ 2) =
        wint n X.z (tstar n X.z ph ph e) ph := by
    intro e
    rw [gm_norm_sq]
    have hae : (gmTheta n X.z hz ph hph e : M → ℂ) =ᵐ[wvol n X.z ph] tstar n X.z ph ph e :=
      (gm_memLp_tstar n X.z hz ph hph e e.2).coeFn_toLp
    have hae2 : (fun x => ‖(gmTheta n X.z hz ph hph e : M → ℂ) x‖ₑ ^ (2:ℝ)) =ᵐ[wvol n X.z ph]
        fun x => ‖tstar n X.z ph ph e x‖ₑ ^ (2:ℝ) :=
      hae.mono fun x hx => congrArg (fun t : ℂ => ‖t‖ₑ ^ (2:ℝ)) hx
    rw [lintegral_congr_ae hae2]
    exact gm_lintegral_wvol n X.z ph hphm _
  have hbound : ∀ e : gmTestForms n X.z,
      ‖gmEll n X.z hz ph hph (dbarF n X.z F0) hv e‖ ^ 2 ≤
        Ae.toReal * ‖gmTheta n X.z hz ph hph e‖ ^ 2 := by
    intro e
    have h1 : ENNReal.ofReal (‖ipV n X.z (dbarF n X.z F0) e ph‖ ^ 2) ≤
        Ae * wint n X.z (tstar n X.z ph ph e) ph :=
      hTI X ph F0 h hph hlevi hF0 hh hpt hA e e.2
    rw [← hθ e, ← hAe', ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))).1 h1
  obtain ⟨u, -, hu2, hu⟩ := rieszOnRange (gmTestForms n X.z) (Lp ℂ 2 (wvol n X.z ph))
    (gmTheta n X.z hz ph hph) (gmEll n X.z hz ph hph (dbarF n X.z F0) hv) Ae.toReal
    ENNReal.toReal_nonneg hbound
  have hexp : ∀ x, (Real.exp (-ph x) : ℂ) * (Real.exp (ph x) : ℂ) = 1 := by
    intro x
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

  have hweak : ∀ φ : M → ℂ, IsTest n X.z φ → ∀ j : Fin n,
      ∫ x, (F0 x - u x) * db n X.z j φ x ∂vol n X.z = 0 := by
    intro φ hφ j
    have hdφc : Continuous (db n X.z j φ) :=
      Smooth.continuous n X.z hz _ (Smooth.db n X.z j φ hφ.1)
    have hdφs : HasCompactSupport (db n X.z j φ) :=
      hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n X.z j φ))
    have hIF : Integrable (fun x => F0 x * db n X.z j φ x) (vol n X.z) :=
      integrable_of_continuous n X.z hz _ (hF0c.mul hdφc) hdφs.mul_left
    have hS := gm_single_isTestForm n X.z ph hph φ hφ j
    have hmem : MemLp (tstar n X.z ph ph (gmSingle ph φ j)) 2 (wvol n X.z ph) :=
      gm_memLp_tstar n X.z hz ph hph _ hS
    obtain ⟨hin, hint⟩ := gm_inner_toLp n X.z ph hphm u _ hmem
    have key := hu ⟨gmSingle ph φ j, hS⟩
    have k1 : gmTheta n X.z hz ph hph ⟨gmSingle ph φ j, hS⟩ = hmem.toLp _ := rfl
    have k2 : gmEll n X.z hz ph hph (dbarF n X.z F0) hv ⟨gmSingle ph φ j, hS⟩ =
        ipV n X.z (dbarF n X.z F0) (gmSingle ph φ j) ph := rfl
    have hfun : (fun x => (Real.exp (-ph x) : ℂ) *
        (conj (u x) * tstar n X.z ph ph (gmSingle ph φ j) x)) =
          fun x => -(conj (u x * db n X.z j φ x)) := by
      funext x
      rw [gm_tstar_single, map_mul]
      linear_combination (-(conj (u x) * conj (db n X.z j φ x))) * hexp x
    rw [k1, k2, hin, gm_ipV_single, hfun, integral_neg, integral_conj,
      integral_db_mul n X.z hz j F0 φ (Smooth.ck n X.z 1 F0 hF0) (Smooth.ck n X.z 1 φ hφ.1) hφ.2,
      map_neg] at key
    have hEq : ∫ x, u x * db n X.z j φ x ∂vol n X.z = ∫ x, F0 x * db n X.z j φ x ∂vol n X.z :=
      (starRingEnd ℂ).injective (neg_inj.mp key)
    have hI : Integrable (fun x => -(conj (u x * db n X.z j φ x))) (vol n X.z) := by
      rw [← hfun]; exact hint
    have hIu : Integrable (fun x => u x * db n X.z j φ x) (vol n X.z) := by
      refine Integrable.mono' hI.norm ?_ (Eventually.of_forall fun x => by simp)
      have hm := Complex.continuous_conj.comp_aestronglyMeasurable hI.aestronglyMeasurable.neg
      simpa using hm
    have hsplit : (fun x => (F0 x - u x) * db n X.z j φ x) =
        fun x => F0 x * db n X.z j φ x - u x * db n X.z j φ x := by
      funext x; ring
    rw [hsplit, integral_sub hIF hIu, hEq, sub_self]
  obtain ⟨G, hG, hGae⟩ := hReg X.z hz (fun x => F0 x - u x)
    (locL2_sub_weightedL2 n X.z hz ph hph F0 hF0c u) hweak
  refine ⟨G, hG, ?_⟩
  have hae : (fun x => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * Real.exp (-ph x))) =ᵐ[vol n X.z]
      fun x => ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) := by
    filter_upwards [hGae] with x hx
    have hx' : F0 x - u x = G x := hx
    rw [← hx', sub_sub_cancel]
  calc wint n X.z (fun x => F0 x - G x) ph
      = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂vol n X.z := lintegral_congr_ae hae
    _ = ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n X.z ph := (gm_lintegral_wvol n X.z ph hphm _).symm
    _ = ENNReal.ofReal (‖u‖ ^ 2) := (gm_norm_sq u).symm
    _ ≤ ENNReal.ofReal Ae.toReal := ENNReal.ofReal_le_ofReal hu2
    _ = Ae := hAe'
end ReciprocityTheory.L2DbarEstimates.F
