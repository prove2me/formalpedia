-- Prove2me | solution 1 for PI.AprimeInfT.secondCountable_HA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:34.274883+00:00
-- url     : https://prove2.me/submissions/08f5cf1b-39fa-4b2e-a942-425d1532707f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_T2SpaceTensorProductFiniteExtension
import Theorems.Thm_PI_AprimeInfT_secondCountable_tens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfT
open scoped TensorProduct
open NumberField MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]
variable {M : ℕ}
namespace PI.AprimeInfT
theorem _root_.solution [SecondCountableTopology R] (σ : E →ₐ[F] E)
    (J : Matrix (Fin M) (Fin M) E) : SecondCountableTopology (HA R σ J) := by
  have := secondCountable_tens (F := F) (E := E) R
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have h1 : SecondCountableTopology (HR R σ J) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact h1
end PI.AprimeInfT
