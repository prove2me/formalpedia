-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.iter_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:47.656934+00:00
-- url     : https://prove2.me/submissions/b9218fe6-fb67-4c69-924a-77e5cac4f246

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_minorOp_phi

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
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (N : ℕ) (f : Pm (Polynomial ℂ) ρ) :
    (minorOp s m b I J)^[N] (phi b I J f) = ((-(cMn s b)) ^ ρ) ^ N • phi b I J ((detE (alMn m b))^[N] f) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, minorOp_phi, smul_smul, Function.iterate_succ_apply', pow_succ,
      mul_comm]
end PositivityTheory.Rg.Sw.SP
