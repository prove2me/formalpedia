-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isDerivedOn_natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:49.897024+00:00
-- url     : https://prove2.me/submissions/c0cc906b-a67f-446e-b7b5-60fb2abe8988

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_actM_rsM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_glRep_rsM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_continuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_deriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (n : ℕ) :
    ∃ (σ : Matrix (Fin n) (Fin n) ℂ → (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
      (E : Fin n → Fin n → Module.End ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))),
      IsURepOn (UJset (fun _ : Fin n => true)) σ ∧ IsDerivedOn (fun _ => true) σ ⊤ E ∧
        ∀ a b, E a b ≠ 0 := by

  refine ⟨toEuclideanCLM (n := Fin n) (𝕜 := ℂ), fun a b => rsM (single a b (1 : ℂ)), ⟨⟨map_one _, fun a _ b _ => ?_⟩, fun g hg v => toE_unitary g hg v,
    fun v => ?_⟩, ⟨glRep_rsM n, fun _ _ v _ => Submodule.mem_top, fun X _ v => ?_⟩, fun a b => ?_⟩
  · rw [map_mul]
    rfl
  · exact ((ContinuousLinearMap.apply ℂ (EH n) v).continuous.comp (toE_continuous n)).continuousOn
  · rw [actM_rsM, rsM_apply]
    exact toE_deriv X v
  · intro h
    have h1 : toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (single a b (1 : ℂ)) = 0 := by
      ext1 v
      have := congrArg (fun f : Module.End ℂ (⊤ : Submodule ℂ (EH n)) =>
        ((f ⟨v, Submodule.mem_top⟩ : (⊤ : Submodule ℂ (EH n))) : EH n)) h
      simpa [rsM_apply] using this
    have h2 : single a b (1 : ℂ) = 0 := (map_eq_zero_iff _ (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective).mp h1
    have h3 := congrFun (congrFun h2 a) b
    simp at h3
end ReciprocityTheory.ChartRestriction.DS
