-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_isHermitian_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:10.481849+00:00
-- url     : https://prove2.me/submissions/71e07c6b-4a21-481f-96d8-f4089194a11e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_hessC_eq_leviC


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
variable {e : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (h : IsSymmSndFDerivAt ℝ φ z) : (hessC φ z).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, hessC_eq_leviC, leviC]
  rw [h (Pi.single j 1) (Pi.single i 1), h (Complex.I • Pi.single j 1) (Complex.I • Pi.single i 1),
    h (Pi.single j 1) (Complex.I • Pi.single i 1), h (Complex.I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp
end ReciprocityTheory.AnForm.A
