-- Prove2me | solution 1 for PI.SqPairLocal.pres_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:40.792386+00:00
-- url     : https://prove2.me/submissions/31d06e81-9c8a-435d-b3ed-333adbab9ceb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_stdHG_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
variable {L : Submodule (𝓞 E) (Fin N → E)}
namespace PI.SqPairLocal
theorem _root_.solution (hL : IsSDG E N L) {e : Matrix (Fin N) (Fin N) E} (he : Pres L e) :
    Pres L eᴴ := by
  have hmem : ∀ y, y ∈ L ↔ ∀ x ∈ L, stdHG E N x y ∈ (algebraMap (𝓞 E) E).range := by
    first
      | exact hL.2.2
      | (unfold IsSDG at hL; exact hL.2.2)
  intro y hy
  refine (hmem _).2 fun x hx => ?_
  rw [stdHG_conj]
  exact (hmem y).1 hy _ (he x hx)
end PI.SqPairLocal
