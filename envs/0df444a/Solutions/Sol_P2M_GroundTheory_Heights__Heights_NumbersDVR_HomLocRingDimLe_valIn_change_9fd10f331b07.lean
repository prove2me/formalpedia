-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_change_9fd10f331b07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:39.025829+00:00
-- url     : https://prove2.me/submissions/1d25d37e-bcb3-41e3-b58e-e3c74d143510

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
theorem _root_.solution (hPW : P ≤ W) {q : Ideal (homLocRing P W)} {b : K → ℕ} {f g g' : MRing ι R}
    (hg : IsMultiHomog g b) (hg' : IsMultiHomog g' b) (hgW : g ∉ W) (hg'W : g' ∉ W)
    (h : ValIn P W q (frac P f / frac P g)) : ValIn P W q (frac P f / frac P g') := by
  have e : frac P f / frac P g' = frac P f / frac P g * (frac P g / frac P g') := by
    rw [div_mul_div_cancel₀ (frac_ne_zero hPW hgW)]
  rw [e]
  exact valIn_mul h (div_mem hg hg' hg'W)
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
