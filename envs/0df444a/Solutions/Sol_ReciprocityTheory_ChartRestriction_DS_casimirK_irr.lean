-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:46.20085+00:00
-- url     : https://prove2.me/submissions/6cf3f3c5-543e-4037-83bd-858e8f2850b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_khwVec


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
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) :
    ∀ v ∈ V, casimirK ε A v = (casValK ε Λ : ℂ) • v := by
  obtain ⟨-, hst, hirr, w, hwV, hw0, hwK⟩ := hV
  let S : Submodule ℂ X := V ⊓ (casimirK ε A).eigenspace (casValK ε Λ : ℂ)
  have hS : IsKStableSub ε A S := by
    intro a b hab v hv
    have hv2 := Module.End.mem_eigenspace_iff.1 hv.2
    refine ⟨hst a b hab v hv.1, Module.End.mem_eigenspace_iff.2 ?_⟩
    have := LinearMap.congr_fun (casimirK_comm ε hA a b hab) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv2, map_smul]
  rcases hirr S inf_le_left hS with h | h
  · exfalso
    have hwS : w ∈ S := ⟨hwV, Module.End.mem_eigenspace_iff.2 (casimirK_khwVec ε hA hwK)⟩
    rw [h] at hwS
    exact hw0 ((Submodule.mem_bot ℂ).1 hwS)
  · intro v hv
    rw [← h] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
end ReciprocityTheory.ChartRestriction.DS
