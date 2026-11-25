-- Prove2me | solution 1 for PI.Dv.TIW.asAlgebraHom_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:26.942089+00:00
-- url     : https://prove2.me/submissions/17075a5f-9d07-461f-b7b6-a3756ad6afc0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]
namespace PI.Dv.TIW
theorem _root_.solution (τ : Representation K G W) (z : MonoidAlgebra K G) (w : W) :
    τ.asAlgebraHom z w ∈ Submodule.span K (Set.range fun x => τ x w) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | single x r =>
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
end PI.Dv.TIW
