-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.minorOp_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:06.204154+00:00
-- url     : https://prove2.me/submissions/d443e9e4-f72d-4a0a-a3fa-c98777535758

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_foldr_phi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.Mi
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (f : Pm (Polynomial ℂ) ρ) :
    minorOp s m b I J (phi b I J f) = (-(cMn s b)) ^ ρ • phi b I J (detE (alMn m b) f) := by
  simp only [minorOp, detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_phi, List.length_finRange, map_sum,
    map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, smul_comm]
end PositivityTheory.Rg.Sw.SP
