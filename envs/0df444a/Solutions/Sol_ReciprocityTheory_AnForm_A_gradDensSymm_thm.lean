-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.gradDensSymm_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:44.592417+00:00
-- url     : https://prove2.me/submissions/6a122b66-78dc-4a51-a210-a9ce700df604

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradMat_swap
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_isHermitian_of_symm
import Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_conjTranspose

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
theorem _root_.solution : GradDensSymmStatement := by
  intro n φ v w U hU hφ z hz
  have hB : ∀ i, (hessC (φ i) z).IsHermitian := fun i =>
    hessC_isHermitian_of_symm _ _
      (((hφ i).contDiffAt (hU.mem_nhds hz)).isSymmSndFDerivAt (by simp))
  unfold gradDens
  rw [gradMat_swap v w z, re_mdisc_cons_conjTranspose _ _ hB]
end ReciprocityTheory.AnForm.A
