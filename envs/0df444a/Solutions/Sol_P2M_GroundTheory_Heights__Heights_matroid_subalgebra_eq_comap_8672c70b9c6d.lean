-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_matroid_subalgebra_eq_comap_8672c70b9c6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:31.542813+00:00
-- url     : https://prove2.me/submissions/db5ecae0-1f65-4738-87bb-9ce4b59d7b35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegAdjoinLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal Set AlgebraicIndependent
noncomputable section
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (S : Subalgebra K Ω) :
    AlgebraicIndependent.matroid K S = (AlgebraicIndependent.matroid K Ω).comap ((↑) : S → Ω) := by
  refine Matroid.ext_indep (by simp) fun I _ => ?_
  have hinj : InjOn ((↑) : S → Ω) I := Subtype.val_injective.injOn
  rw [Matroid.comap_indep_iff, matroid_indep_iff, matroid_indep_iff]
  simp only [hinj, and_true]
  change AlgebraicIndependent K (fun i : I => (i : S)) ↔
    AlgebraicIndependent K (fun x : (((↑) : S → Ω) '' I) => (x : Ω))
  rw [← algebraicIndependent_image hinj]
  exact (S.val.algebraicIndependent_iff Subtype.val_injective).symm
end GroundTheory.Heights₂.Heights
