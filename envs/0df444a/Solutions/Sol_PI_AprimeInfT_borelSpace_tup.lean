-- Prove2me | solution 1 for PI.AprimeInfT.borelSpace_tup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:38.703884+00:00
-- url     : https://prove2.me/submissions/85c0bbf2-24ab-4bde-8059-633e1f2c77ff

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
theorem _root_.solution [SecondCountableTopology R] (a : ℕ) :
    BorelSpace (Fin a → Fin M → R ⊗[F] E) := by
  have := secondCountable_tens (F := F) (E := E) R
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  infer_instance
end PI.AprimeInfT
