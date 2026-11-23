-- Prove2me | solution 1 for PI.LevelKSplit.W.ExS.lcsc_HAf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:10.96663+00:00
-- url     : https://prove2.me/submissions/b2c9d86b-9aa6-42be-8edf-71c8609e4d2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SubgroupLocallyCompactHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProdHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExS
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.VolSemiDirect.W
open scoped TensorProduct
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
variable {F E σ M J}
namespace PI.LevelKSplit.W.ExS
theorem _root_.solution [FiniteDimensional F E] (hsc : SecondCountableTopology (Af F)) :
    LCSC (HA (Af F) σ J) := by
  haveI := hsc
  refine ⟨inferInstance, ?_, ?_, inferInstance⟩
  · haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
    let e := (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun
    have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : (Af F ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Af F) := ⟨e.toEquiv, hc1, hc2⟩
    haveI : SecondCountableTopology (Af F ⊗[F] E) := h.secondCountableTopology
    haveI h4 : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin M → Fin M → Af F ⊗[F] E))
    haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin M) (Af F ⊗[F] E)) :=
      Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
    show SecondCountableTopology ↥(HR (Af F) σ J)
    exact Topology.IsInducing.subtypeVal.secondCountableTopology
  · show T2Space ↥(HR (Af F) σ J)
    infer_instance
end PI.LevelKSplit.W.ExS
