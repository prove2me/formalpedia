-- Prove2me | solution 1 for ProbabilityTheory.ElementaryPredictableSet.integrable_integral_real
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:11:20.536631+00:00
-- url     : https://prove2.me/submissions/2906e45a-6180-4378-bea7-1ad68cb3d711

import Definitions.Def_BrownianMotion_StochasticIntegral_SimpleProcess_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/

/-! # Simple processes and elementary stochastic integral

## Main definitions

- `ElementaryPredictableSet`: the type of elementary predictable sets
- `SimpleProcess`: the type of simple processes, as a Module over ℝ
- `SimpleProcess.toFun`: simple process interpreted as a stochastic process, with a CoeFun instance
- `SimpleProcess.integral`: elementary stochastic integral
- `SimpleProcess.isPredictable`: simple processes are predictable

## Implementation notes

`SimpleProcess` consists of a value function as a `Finsupp`: `value : ι × ι →₀ Ω → E` and a
value at ⊥: `valueBot : Ω → E`. This allows the definition of operations like addition to be
defined naturally.

However, this makes the function `SimpleProcess.toFun` non-injective, so `SimpleProcess` is not
`FunLike`. In other words, two distinct elements `X Y : SimpleProcess E 𝓕` may produce the same
function `(⇑X : ι → Ω → E) = (⇑Y : ι → Ω → E)`.

There are subtleties that are caused by this: for example, by a nonnegative simple
process, we mean `X : SimpleProcess E 𝓕` with `0 ≤ X.valueBot` and `0 ≤ X.value`, which is not the
same as `0 ≤ (⇑X : ι → Ω → E)`.

Similarly, `ElementaryPredictableSet` is a data type that has a coercion to `Set (ι × Ω)`, but
this coercion is not injective, so it is not `SetLike`. This makes it easy to define the indicator
function of an elementary predictable set as a simple process by mapping respective datas
(which is why it also requires disjoint unions).

## TODO

- Generalize instance variables.
-/

@[expose] public section

open MeasureTheory Finset Filter ContinuousLinearMap
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [mE : MeasurableSpace E]
-- Note: separable space is needed for `ContinuousAdd.measurableMul₂` (which has the wrong name)
variable [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {𝓕 : Filtration ι mΩ}

attribute [local measurability]
  measurableSet_predictable_singleton_bot_prod
  measurableSet_predictable_Ioi_prod
  measurableSet_predictable_Ioc_prod

namespace ElementaryPredictableSet

                                                                

end ElementaryPredictableSet

namespace SimpleProcess

                                        

-- todo: replace the condition on W by IsPredictable

section Module

-- TODO: Mathlib's Finset.measurable_prod is wrong because it is currently an exact duplicate of
-- Finset.measurable_fun_sum; we want the following version instead.

end Module

section ToFun

end ToFun

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

section Integral

              
                                                      

              
                                                   

              
                                                                                

variable {B : E →L[ℝ] F →L[ℝ] G}

-- @[simp] lemma integral_top (V : SimpleProcess E 𝓕) (X : ι → Ω → F) (ω : Ω) :
--     integral B V X ⊤ ω = V.value.sum fun p v ↦ B (v ω) (X p.2 ω - X p.1 ω) := by simp [integral]

end Integral

section Assoc

section Bilin

section map₂

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

-- Analogous to LinearMap.finsupp_sum_apply and AddMonoidHom.finsuppSum_apply:

end map₂

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {I : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I]
variable {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
variable [MeasurableSpace J] [BorelSpace J] [SecondCountableTopology J]

end Bilin

section Comp

variable [SecondCountableTopology (F →L[ℝ] G)]
variable [SecondCountableTopology (E →L[ℝ] F)]
variable [SecondCountableTopology (E →L[ℝ] G)]
omit mE [SecondCountableTopology E]

end Comp

section SMul

-- TODO: cor:elemStochIntegral_assoc_real_bilin and lem:elemStochIntegral_assoc

end SMul

end Assoc

end SimpleProcess

section Indicator

namespace ElementaryPredictableSet

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open scoped SimpleProcess


theorem _root_.solution {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hXint : ∀ s, Integrable (X s) μ) (S : ElementaryPredictableSet 𝓕) (c : ℝ) (t : ι) :
    Integrable (((S.indicator c) ● X) t) μ := by
  have h : ((S.indicator c) ● X) t = fun ω => ∑ p ∈ S.I, (S.set p).indicator (fun ω ↦
      (ContinuousLinearMap.mul ℝ ℝ) c
        (stoppedProcess X (fun _ ↦ t) p.2 ω - stoppedProcess X (fun _ ↦ t) p.1 ω)) ω := by
    funext ω
    exact ProbabilityTheory.ElementaryPredictableSet.integral_indicator_apply S c _ X t ω
  rw [h]
  refine integrable_finsetSum _ (fun p hp => ?_)
  refine Integrable.indicator ?_ (𝓕.le p.1 _ (S.measurableSet_set p hp))
  refine ((ContinuousLinearMap.mul ℝ ℝ) c).integrable_comp ?_
  simp only [stoppedProcess]
  exact (hXint _).sub (hXint _)

