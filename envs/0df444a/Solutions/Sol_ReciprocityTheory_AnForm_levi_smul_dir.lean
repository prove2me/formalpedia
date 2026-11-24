-- Prove2me | solution 1 for ReciprocityTheory.AnForm.levi_smul_dir
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:34.959509+00:00
-- url     : https://prove2.me/submissions/41f42ac0-8ace-444c-9b4b-8af5be03f25d

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
theorem _root_.solution (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) (t : ℝ) :
    levi φ z (t • w) = t ^ 2 * levi φ z w := by
  unfold levi
  rw [smul_comm Complex.I t w]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.AnForm
