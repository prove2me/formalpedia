-- Prove2me | solution 1 for QPK.weil_quotient_global_assumptions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:22.659799+00:00
-- url     : https://prove2.me/submissions/9cb92ad2-ec06-480f-a308-ae1536f7aec2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_LintegralFintypeProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_WeilQuotientGlobalAssumptions
import Theorems.Thm_QPK_isGrp_pi
import Theorems.Thm_QPK_invOn_pi
import Theorems.Thm_QPK_lintegral_pi_prod_mul
import Theorems.Thm_QPK_lintegral_fintype_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
namespace QPK
theorem _root_.solution : GlobAsm := by
  intro hU hL ι _ n ε N H hNc hHc hNg hHg hnorm hunim muN muH nuQ hmuN hmuH hW
  have hloc := fun v => hL (Formalism.REAL.UJ (ε v)) (Formalism.REAL.muG (ε v)) (N v) (H v) (hNc v) (hHc v)
    (hNg v) (hHg v) (hnorm v) (hunim v)
  choose μN μH β hμN hμH hμS hβm hβ1 hLW using hloc
  haveI := fun v => (hμN v).1
  haveI := fun v => (hμH v).1
  haveI := fun v => (hμS v).1
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := hU (∀ v, Formalism.REAL.UJ (ε v)) (Set.pi univ N)
    (isClosed_set_pi fun v _ => hNc v) (isGrp_pi N hNg) muN (Measure.pi μN) hmuN
    (invOn_pi N μN hμN)
  obtain ⟨cH, hcH0, hcHt, hcH⟩ := hU (∀ v, Formalism.REAL.UJ (ε v)) (Set.pi univ H)
    (isClosed_set_pi fun v _ => (hHc v).isClosed) (isGrp_pi H hHg) muH (Measure.pi μH) hmuH
    (invOn_pi H μH hμH)
  refine ⟨fun v => mulMap (μN v) (μH v), fun v => (Formalism.REAL.muG (ε v)).withDensity (β v),
    (cN * cH)⁻¹, ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top hcNt hcHt),
    ENNReal.inv_ne_top.mpr (mul_ne_zero hcN0 hcH0), fun v => ⟨hμS v, hLW v⟩, ?_⟩
  intro F hFm hFinv
  set f : (∀ v, Formalism.REAL.UJ (ε v)) → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hfdef
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := hW f hfm

  have hL1 : ∫⁻ x, f x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
      ∏ v, ∫⁻ y, F v y ∂((Formalism.REAL.muG (ε v)).withDensity (β v)) := by
    rw [hfdef, lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [lintegral_withDensity_eq_lintegral_mul _ (hβm v) (hFm v)]
    rfl

  have hin : ∀ x, ∫⁻ s, f (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2)) =
      (cN * cH) * ∏ v, F v (x v) := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      hcN, hcH,
      Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have h1 : ∀ p : (∀ v, Formalism.REAL.UJ (ε v)) × (∀ v, Formalism.REAL.UJ (ε v)),
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [h1]
    rw [lintegral_pi_prod_mul μN μH (fun v z => β v (z * x v) * F v (z * x v)) (fun v => ((hβm v).comp (measurable_mul_const _)).mul
      ((hFm v).comp (measurable_mul_const _)))]
    have h2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(mulMap (μN v) (μH v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(mulMap (μN v) (μH v)), s ∈ prodSet (N v) (H v) :=
        mem_ae_iff.mpr (hμS v).2.2.1
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        simp only [hFinv v m hm h hh])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [h2]
    ring
  simp_rw [hin] at key
  have hPm : Measurable (fun x : (∀ v, Formalism.REAL.UJ (ε v)) => ∏ v, F v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hFm v).comp (measurable_pi_apply v)
  rw [lintegral_const_mul _ hPm, hL1] at key
  change _ = (cN * cH)⁻¹ * ∏ v, ∫⁻ y, F v y ∂((Formalism.REAL.muG (ε v)).withDensity (β v))
  rw [key, ← mul_assoc, ENNReal.inv_mul_cancel (mul_ne_zero hcN0 hcH0)
    (ENNReal.mul_ne_top hcNt hcHt), one_mul]
end QPK
