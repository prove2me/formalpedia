-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Ald.PCI.iteratedFDeriv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:09.641839+00:00
-- url     : https://prove2.me/submissions/329aae8c-06ca-4f63-ad92-a82e6a59d539

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LagrangianDecomposition_IteratedFDerivIntegral
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Ald_PCI_contDiff_pder
import Theorems.Thm_GlobalTheory_SchwartzDiv_hasFDerivAt_integral_smul_param


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open MeasureTheory Set Filter Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Ald PositivityTheory.SiegelWeilFormula.Ald.PCI
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
namespace PositivityTheory.SiegelWeilFormula.Ald.PCI
theorem _root_.solution {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (fun y => ∫ s in Ioc (0 : ℝ) 1, Θ (y, s)) x = ∫ s in Ioc (0 : ℝ) 1, pder n Θ (x, s) := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply, pder, iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ n ih =>
    have hfun : iteratedFDeriv ℝ n (fun y => ∫ s in Ioc (0 : ℝ) 1, Θ (y, s)) =
        fun y => ∫ s in Ioc (0 : ℝ) 1, (1 : ℂ) • pder n Θ (y, id s) := by
      funext y; simp [ih y]
    have hd := GlobalTheory.SchwartzDiv.hasFDerivAt_integral_smul_param (ν := volume.restrict (Ioc (0 : ℝ) 1)) (c := id)
      (S := Icc (0 : ℝ) 1) (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_id isCompact_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht)
      (integrableOn_const (by simp)) (contDiff_pder n hΘ) x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hfun, hd.fderiv]
    have hc := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).symm.toLinearIsometry.integral_comp_comm
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (fun y => (1 : ℂ) • fderiv ℝ (fun s => pder n Θ (s, id y)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hc
    rw [← hc]
    refine integral_congr_ae (.of_forall fun s => ?_)
    simp only [one_smul, id, pder]
    rw [iteratedFDeriv_succ_eq_comp_left]
    rfl
end PositivityTheory.SiegelWeilFormula.Ald.PCI
