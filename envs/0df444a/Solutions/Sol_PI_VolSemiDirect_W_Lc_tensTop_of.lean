-- Prove2me | solution 1 for PI.VolSemiDirect.W.Lc.tensTop_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:31.535806+00:00
-- url     : https://prove2.me/submissions/d7fe12f5-499a-47eb-b6cb-03384582e7d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TensTopOf
import Theorems.Thm_PI_VolSemiDirect_W_Lc_finite_nf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Lc
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.VolSemiDirect.W.Lc
theorem _root_.solution (h : AFTop) : TensTop := by
  intro F E _ _ _ _ _
  obtain ⟨hlc, hsc, ht2⟩ := h F
  have := finite_nf F E
  let R := AF F
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let bR := Algebra.TensorProduct.basis R b
  let e : (R ⊗[F] E) ≃ₗ[R] (Fin (Module.finrank F E) → R) := bR.equivFun
  have htr : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  let hm : (R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R) :=
    { toEquiv := e.toEquiv, continuous_toFun := by simpa using c1, continuous_invFun := by simpa using c2 }
  refine ⟨htr, ?_, ?_, ?_⟩
  · exact hm.isEmbedding.t2Space
  · exact hm.isClosedEmbedding.locallyCompactSpace
  · exact hm.isEmbedding.secondCountableTopology
end PI.VolSemiDirect.W.Lc
