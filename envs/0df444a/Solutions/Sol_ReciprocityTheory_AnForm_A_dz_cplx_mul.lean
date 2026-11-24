-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dz_cplx_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:30.908478+00:00
-- url     : https://prove2.me/submissions/9e41d525-30c0-4373-a278-3446207b3bda

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (j : Fin D) (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (cplx fun y => f y * g y) z = (f z : ℂ) * dz j (cplx g) z + (g z : ℂ) * dz j (cplx f) z := by
  rw [dz_cplx, dz_cplx, dz_cplx, HasFDerivAt.fderiv (f := fun y => f y * g y) (hf.hasFDerivAt.mul hg.hasFDerivAt)]
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  ring
end ReciprocityTheory.AnForm.A
