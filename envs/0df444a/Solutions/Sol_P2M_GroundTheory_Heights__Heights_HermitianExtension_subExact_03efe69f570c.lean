-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_subExact_03efe69f570c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:33.572619+00:00
-- url     : https://prove2.me/submissions/9ee33202-a623-40f3-b6aa-76676c6aceb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable (F : Submodule (𝓞 K) E.carrier)
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution : Function.Exact (X.subIncl F) (X.subProj F) := by
  intro y
  constructor
  · intro hy
    have h0 : X.proj (y : E.carrier) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (X.exact (y : E.carrier)).mp h0
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change X.incl x ∈ F
    rw [hx]
    exact y.2
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (X.exact.apply_apply_eq_zero (x : E'.carrier))
end GroundTheory.Heights₂.Heights.HermitianExtension
