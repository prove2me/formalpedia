-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_46ce3eed0a97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:10.702293+00:00
-- url     : https://prove2.me/submissions/dcdd89f5-0cf6-4ebc-b425-47d652446957

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PModulesFromPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {K : Type*} {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1))
    (b : K → ℤ) : DegLT (diffStep b f) n := by
  intro bs
  have h := hf (Fin.snoc bs b)
  have he : mixedDiff (Fin.snoc bs b) f = mixedDiff bs (diffStep b f) := by
    unfold mixedDiff
    rw [List.ofFn_succ', List.concat_eq_append, List.foldr_append]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rwa [he] at h
end GroundTheory.Heights₂.Heights.HilbertSamuel
