-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleConnected_exists_ne_zero_7c26e2820178
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:11.318618+00:00
-- url     : https://prove2.me/submissions/b376ea34-f246-4c81-b5dc-dcd6f8f98f9f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StatementsBasicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIrreducibleConnected

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace IrreducibleConnected
theorem _root_.solution {σ : Type} [Fintype σ] {W : Ideal (MvPolynomial σ ℂ)}
    (hW : W.IsPrime) {h : MvPolynomial σ ℂ} (hh : h ∉ W) :
    ∃ x ∈ zeroLocus ℂ W, eval x h ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hh
  have hv : h ∈ vanishingIdeal ℂ (zeroLocus ℂ W) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    simpa [coe_aeval_eq_eval] using hcon x hx
  rwa [vanishingIdeal_zeroLocus_eq_radical (K := ℂ), hW.isRadical.radical] at hv
end IrreducibleConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel
