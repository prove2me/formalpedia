-- Prove2me | solution 1 for PI.Dv.TIW.map_matV_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:13.194078+00:00
-- url     : https://prove2.me/submissions/5aea7ab9-0f91-4264-a6ec-13332aeda701

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Theorems.Thm_PI_Dv_TIW_matV_apply
import Theorems.Thm_PI_Dv_TIW_matV_inv_cancel

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
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (S : Submodule K V) :
    (Submodule.pi Set.univ fun _ : n => S).map (matV A) = Submodule.pi Set.univ fun _ : n => S := by
  have hsub : ∀ B : Matrix n n K, ∀ x ∈ (Submodule.pi Set.univ fun _ : n => S), matV B x ∈
      (Submodule.pi Set.univ fun _ : n => S) := by
    intro B x hx k _
    rw [matV_apply]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact hsub A x hx
  · intro x hx
    exact ⟨matV A⁻¹ x, hsub _ x hx, matV_inv_cancel A hA x⟩
end PI.Dv.TIW
