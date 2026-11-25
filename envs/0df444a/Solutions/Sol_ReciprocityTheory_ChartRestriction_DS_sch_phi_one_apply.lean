-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sch_phi_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:43.84351+00:00
-- url     : https://prove2.me/submissions/1ef9e812-7fa1-4a0f-a4e0-47e84939405d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchPhiOneApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_coord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_word_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (G : Big n 1 M) :
    phi E 1 G = ∑ p : Fin n × Fin n, E p.1 p.2 (G (fun _ => p)) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun κ => ?_)
  rw [Equiv.funUnique_apply, sch_word_one, sch_coord_apply]
  obtain ⟨p, rfl⟩ : ∃ p, κ = fun _ => p := ⟨κ 0, funext fun j => by rw [Fin.fin_one_eq_zero j]⟩
  rfl
end ReciprocityTheory.ChartRestriction.DS
