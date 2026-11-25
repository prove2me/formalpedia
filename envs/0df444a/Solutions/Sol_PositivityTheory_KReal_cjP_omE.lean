-- Prove2me | solution 1 for PositivityTheory.KReal.cjP_omE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:38:59.637565+00:00
-- url     : https://prove2.me/submissions/bc1d9cc0-b120-4052-9e93-c639fc00a43a

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
import Theorems.Thm_PositivityTheory_KReal_cjP_add
import Theorems.Thm_PositivityTheory_KReal_cjP_smul
import Theorems.Thm_PositivityTheory_KReal_cjP_lowB
import Theorems.Thm_PositivityTheory_KReal_cjP_raiB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (l l' : Ln p q r s) (P : Pol p q r s) : cjP (omE l l' P) = omE l l' (cjP P) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, cjP_add, cjP_raiB, cjP_lowB]
  split_ifs
  · simp only [LinearMap.smul_apply, cjP_smul, Module.End.one_apply]
    congr 2
    rw [map_div₀, map_one, Complex.conj_ofNat]
  · simp [cjP]
end PositivityTheory.KReal
