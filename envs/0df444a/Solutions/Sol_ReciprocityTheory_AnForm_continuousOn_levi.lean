-- Prove2me | solution 1 for ReciprocityTheory.AnForm.continuousOn_levi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:34.606475+00:00
-- url     : https://prove2.me/submissions/89c61db2-5ecd-4b46-a0b9-03f065d8f3f2

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace ReciprocityTheory.AnForm
theorem _root_.solution {φ : (ι → ℂ) → ℝ} {U : Set (ι → ℂ)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) :
    ContinuousOn (fun p : (ι → ℂ) × (ι → ℂ) => levi φ p.1 p.2) (U ×ˢ Set.univ) := by
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U := h1.continuousOn_fderiv_of_isOpen hU le_rfl
  have h3 : ContinuousOn (fun p : (ι → ℂ) × (ι → ℂ) => fderiv ℝ (fderiv ℝ φ) p.1) (U ×ˢ Set.univ) :=
    h2.comp continuousOn_fst fun p hp => hp.1
  have h4 : ContinuousOn (fun p : (ι → ℂ) × (ι → ℂ) => Complex.I • p.2) (U ×ˢ Set.univ) :=
    (by fun_prop : Continuous fun p : (ι → ℂ) × (ι → ℂ) => Complex.I • p.2).continuousOn
  unfold levi
  exact (((h3.clm_apply continuousOn_snd).clm_apply continuousOn_snd).add
    ((h3.clm_apply h4).clm_apply h4)).div_const 4
end ReciprocityTheory.AnForm
