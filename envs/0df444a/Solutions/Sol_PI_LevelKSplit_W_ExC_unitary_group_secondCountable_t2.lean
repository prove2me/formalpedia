-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.unitary_group_secondCountable_t2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:14:33.458689+00:00
-- url     : https://prove2.me/submissions/14ce4678-6cea-4e16-b5a8-85417acb3a64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.ExC
theorem _root_.solution (hsc : SecondCountableTopology (Af F)) :
    SecondCountableTopology (HA (Af F) σ J) ∧ T2Space (HA (Af F) σ J) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Af F)
  have : SecondCountableTopology (Af F ⊗[F] E) := h.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : T2Space (Matrix (Fin n) (Fin n) (Af F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  have : SecondCountableTopology (GL (Fin n) (Af F ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : T2Space (GL (Fin n) (Af F ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space
  have hemb : Topology.IsEmbedding (Subtype.val : HR (Af F) σ J → GL (Fin n) (Af F ⊗[F] E)) :=
    Topology.IsEmbedding.subtypeVal
  have h1 : SecondCountableTopology (HR (Af F) σ J) := hemb.secondCountableTopology
  have h2 : T2Space (HR (Af F) σ J) := hemb.t2Space
  exact ⟨inferInstanceAs (SecondCountableTopology (HR (Af F) σ J)),
    inferInstanceAs (T2Space (HR (Af F) σ J))⟩
end PI.LevelKSplit.W.ExC
