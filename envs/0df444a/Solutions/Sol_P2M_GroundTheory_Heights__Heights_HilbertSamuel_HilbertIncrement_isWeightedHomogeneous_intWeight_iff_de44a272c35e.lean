-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isWeightedHomogeneous_intWeight_iff_de44a272c35e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:02.04517+00:00
-- url     : https://prove2.me/submissions/80644450-8af2-472e-bb39-90162211087e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_weight_intWeight_8853f7eb7b24

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
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
theorem _root_.solution {f : MRing ι F} {a : K → ℕ} :
    IsWeightedHomogeneous (intWeight (ι := ι)) f (fun k => (a k : ℤ)) ↔
      IsWeightedHomogeneous (blockWeight ι) f a := by
  constructor
  · intro h e he
    funext k
    have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = (a k : ℤ) := by
      have := congrFun (h he) k
      rw [weight_intWeight] at this
      exact this
    exact_mod_cast e1
  · intro h e he
    rw [weight_intWeight, h he]
end GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
