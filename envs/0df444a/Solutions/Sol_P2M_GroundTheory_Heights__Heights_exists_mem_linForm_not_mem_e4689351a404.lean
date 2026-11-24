-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_mem_linForm_not_mem_e4689351a404
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:54.771255+00:00
-- url     : https://prove2.me/submissions/a136e77a-04c7-407c-9cc8-e4ca0933d9ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsRelevant I)
    {S : Set (Fin n → 𝓞 K)} (hS : Submodule.span (𝓞 K) S = ⊤) :
    ∃ s ∈ S, linForm (fun j => (s j : K)) ∉ I := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hI
  apply hj
  have hmem : Pi.single j 1 ∈ Submodule.span (𝓞 K) S := by rw [hS]; trivial
  have key : ∀ v ∈ Submodule.span (𝓞 K) S, linForm (fun j => (v j : K)) ∈ I := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact hcon x hx
    | zero => simp [linForm]
    | add x y _ _ hx hy =>
      have : linForm (fun j => ((x + y) j : K)) = linForm (fun j => (x j : K)) + linForm (fun j => (y j : K)) := by
        simp [linForm, Finset.sum_add_distrib, add_mul]
      rw [this]
      exact I.add_mem hx hy
    | smul r x _ hx =>
      have : linForm (fun j => ((r • x) j : K)) = C (r : K) * linForm (fun j => (x j : K)) := by
        simp [linForm, Finset.mul_sum, mul_assoc]
      rw [this]
      exact I.mul_mem_left _ hx
  have := key _ hmem
  convert this using 1
  simp [linForm, Pi.single_apply]
end GroundTheory.Heights₂.Heights
