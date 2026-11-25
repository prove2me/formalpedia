-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_hessC_isHermitian__4fd7a1bbb7ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:57.882566+00:00
-- url     : https://prove2.me/submissions/42370866-7848-4ebe-a0ff-138adb739798

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  ext i j
  simp only [Matrix.conjTranspose_apply, hessC]
  rw [hs (Pi.single j 1) (Pi.single i 1), hs (Complex.I • Pi.single j 1) (Complex.I • Pi.single i 1),
    hs (Pi.single j 1) (Complex.I • Pi.single i 1), hs (Complex.I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp
end ReciprocityTheory.AnForm.M
