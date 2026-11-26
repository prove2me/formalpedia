-- Prove2me | solution 1 for PI.SqPairW.mem_lam
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:21.139878+00:00
-- url     : https://prove2.me/submissions/8b36ed4b-ff36-4eb3-8e1f-25c7052cb86d

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Mathlib



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
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} {e : Matrix (Fin N) (Fin N) E} :
    e ∈ lam L' L'' ↔ (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_10_1"

end 
