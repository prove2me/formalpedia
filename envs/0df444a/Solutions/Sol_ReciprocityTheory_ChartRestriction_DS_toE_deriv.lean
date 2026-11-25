-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.toE_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:37:08.790587+00:00
-- url     : https://prove2.me/submissions/497b02c5-4b4d-4b59-8e0b-4f63e294a1e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_exp

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
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : EH n) :
    HasDerivAt (fun t : ℝ => toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp ((t : ℂ) • X)) v)
      (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v) 0 := by

  have h2 : HasDerivAt (fun s : ℂ => NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X))
      (NormedSpace.exp ((0 : ℂ) • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) * toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) 0 :=
    hasDerivAt_exp_smul_const (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have h3 : HasDerivAt (fun s : ℂ => NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) v) (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v) 0 := by
    have h4 := (ContinuousLinearMap.apply ℂ (EH n) v).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h2
    exact h4
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h3' : HasDerivAt (fun s : ℂ => (NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X)) v) (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v)
      ((fun t : ℝ => (t : ℂ)) 0) := by
    simpa using h3
  have h6 := h3'.scomp (0 : ℝ) hid
  simp only [one_smul] at h6
  have hfun : (fun t : ℝ => toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp ((t : ℂ) • X)) v) =
      ((fun s : ℂ => (NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X)) v) ∘ Complex.ofReal) := by
    funext t
    simp only [Function.comp_apply]
    rw [toE_exp, map_smul]
  rw [hfun]
  exact h6
end ReciprocityTheory.ChartRestriction.DS
