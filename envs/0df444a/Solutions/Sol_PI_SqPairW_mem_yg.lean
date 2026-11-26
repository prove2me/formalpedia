-- Prove2me | solution 1 for PI.SqPairW.mem_yg
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:19.521158+00:00
-- url     : https://prove2.me/submissions/6f2b4e3d-5a7d-4eb1-94d9-e9778c069cc5

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
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} {n : 𝓞 E} {x : Fin N → E} :
    x ∈ yg L' L'' n ↔ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ x = (n : E) • m := by
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
  trace "HIT_10_0"

end 
