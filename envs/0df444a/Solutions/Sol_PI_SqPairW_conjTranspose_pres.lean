-- Prove2me | solution 1 for PI.SqPairW.conjTranspose_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:57.574923+00:00
-- url     : https://prove2.me/submissions/a19b0ad0-3cff-47c3-a4f9-3fae5cc67233

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Theorems.Thm_PI_SqPairW_stdHG_eq_dot

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
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution {L : Submodule (𝓞 E) (Fin N → E)} (hL : IsSDG E N L)
    {e : Matrix (Fin N) (Fin N) E} (he : ∀ y ∈ L, e *ᵥ y ∈ L) : ∀ y ∈ L, eᴴ *ᵥ y ∈ L := by
  intro y hy
  refine (hL.2.2 _).2 (fun x hx => ?_)
  have hy' := (hL.2.2 y).1 hy (e *ᵥ x) (he x hx)
  rw [stdHG_eq_dot] at hy' ⊢
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  exact hy'
end PI.SqPairW
