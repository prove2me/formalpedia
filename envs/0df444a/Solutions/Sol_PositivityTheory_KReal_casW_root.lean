-- Prove2me | solution 1 for PositivityTheory.KReal.casW_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:34.777034+00:00
-- url     : https://prove2.me/submissions/40dfff6b-7528-4161-b729-6b11ece80ea9

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Theorems.Thm_PositivityTheory_KReal_cw_two
import Theorems.Thm_PositivityTheory_KReal_cw_root
import Theorems.Thm_PositivityTheory_KReal_casW_eq
import Theorems.Thm_PI_FockOneDegW_Core_key


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
namespace PositivityTheory.KReal
theorem _root_.solution {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    casW ν = casW La + 2 * (La b - La a) + 2 + (rho2 b - rho2 a) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  rw [casW_eq, casW_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key := cw_two (fun x => ν x ^ 2 + rho2 x * ν x) (fun x => La x ^ 2 + rho2 x * La x) hab
    (fun x h1 h2 => by simp only [hx x h1 h2])
  simp only [ha, hb] at key
  linear_combination key
end PositivityTheory.KReal
