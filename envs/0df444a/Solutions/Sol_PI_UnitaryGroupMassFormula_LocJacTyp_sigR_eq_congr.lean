-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.sigR_eq_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:05.401379+00:00
-- url     : https://prove2.me/submissions/70029eb3-e351-4c75-b4c0-df449bbae9c5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
variable {σ v}
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (hfin : Module.finrank F E = 2) :
    ∃ τ : E ≃ₐ[F] E, ∀ z, sigR (Fv F v) σ z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ z := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨AlgEquiv.ofBijective σ (AlgHom.bijective σ), fun z => rfl⟩
end PI.UnitaryGroupMassFormula.LocJacTyp
