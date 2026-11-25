-- Prove2me | solution 1 for P2M_CompanionTheory_ThKR_Mp_C_toBlocks___mul_lo_fbd01804b3f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:46.519015+00:00
-- url     : https://prove2.me/submissions/1fdbcece-23b4-40ff-9151-4d55474a5fe6

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C
open CompanionTheory.ThKR.Mp.C
namespace CompanionTheory.ThKR.Mp.C
theorem _root_.solution (s : Mat l) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks s, lo, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp
end CompanionTheory.ThKR.Mp.C
