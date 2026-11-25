-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_blockWeight_cast_eq_unitDeg_2474fcdc3522
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:42.553194+00:00
-- url     : https://prove2.me/submissions/097ec7a1-c439-4c1a-9a49-17c179666be1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion

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
universe u
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {K : Type} [DecidableEq K] (ι : K → Type) (b : K) (i : ι b) :
    (fun k => ((blockWeight ι ⟨b, i⟩ k : ℕ) : ℤ)) = unitDeg b := by
  funext k
  simp only [blockWeight, unitDeg, Pi.single_apply]
  split_ifs <;> rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel
