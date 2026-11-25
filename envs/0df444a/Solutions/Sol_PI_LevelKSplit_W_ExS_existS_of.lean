-- Prove2me | solution 1 for PI.LevelKSplit.W.ExS.existS_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:56.52125+00:00
-- url     : https://prove2.me/submissions/2cd20839-13b9-4d96-86d4-2a78de230986

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SubgroupLocallyCompactHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProdHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Theorems.Thm_PI_LevelKSplit_W_ExS_lcsc_HAf
import Theorems.Thm_PI_LevelKSplit_W_ExC_closed_SNH


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
theorem _root_.solution [FiniteDimensional F E] (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x)
    (hPr : ProdHaarG) (hsc : SecondCountableTopology (Af F)) (hS : SemiNHS F E σ M J)
    (hCo : ConjNH F E σ M J) : ExistS F E σ M J := by
  intro r P T hP μN hN μH hH
  obtain ⟨hSc, hNc, hHc⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP
  obtain ⟨hLC, hSC, hT2, hTG⟩ := lcsc_HAf (σ := σ) (J := J) hsc
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hTG
  have hsub : ∀ K : Subgroup (HA (Af F) σ J), IsClosed (K : Set (HA (Af F) σ J)) → LCSC K := by
    intro K hK
    refine ⟨?_, ?_, ?_, inferInstance⟩
    · first
        | exact hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
        | exact hK.locallyCompactSpace
        | exact hK.closedEmbedding_subtypeVal.locallyCompactSpace
    · first
        | exact Topology.IsInducing.subtypeVal.secondCountableTopology
        | exact @Topology.IsInducing.secondCountableTopology _ _ _ _ hSC _ Topology.IsInducing.subtypeVal
    · first
        | exact inferInstance
        | exact Topology.IsEmbedding.subtypeVal.t2Space
  obtain ⟨μS, hμS, hprod⟩ := hPr (HA (Af F) σ J) _ _ _ (hS hJ hinv r P T hP) (hsub _ hSc)
    (hsub _ hNc) (hsub _ hHc) (hCo hJ hinv r P T hP) μN hN μH hH
  exact ⟨μS, hμS, hprod⟩
end PI.LevelKSplit.W.ExS
