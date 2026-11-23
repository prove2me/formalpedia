-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Wm_kStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:50.706945+00:00
-- url     : https://prove2.me/submissions/2574e79a-1c74-44f7-9ae1-712d1a2cdbbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_InnerCrossOpEigEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_kStable


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
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) : IsKStableSub ε (bAct E 1) (Wm ε E V) := by
  intro a b hab v hv
  have hVs : IsKStableSub ε E V := hV.2.1
  have hle : Wm ε E V ≤ (Wm ε E V).comap (bAct E 1 a b) := by
    unfold Wm
    refine iSup₂_le fun θ hθ x hx => ?_
    rw [Submodule.mem_comap]
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hx
    have hc : crossOp ε E 1 0 (bAct E 1 a b x) = bAct E 1 a b (crossOp ε E 1 0 x) :=
      LinearMap.congr_fun (crossOp_comm hE 1 0 hab) x
    have hmem : bAct E 1 a b x ∈
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 := by
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
      refine ⟨?_, ncV_kStable hVs 1 a b hab x hx.2⟩
      rw [hc, hx.1, map_smul]
    exact Submodule.mem_iSup_of_mem θ (Submodule.mem_iSup_of_mem hθ hmem)
  exact hle hv
end ReciprocityTheory.ChartRestriction.DS
