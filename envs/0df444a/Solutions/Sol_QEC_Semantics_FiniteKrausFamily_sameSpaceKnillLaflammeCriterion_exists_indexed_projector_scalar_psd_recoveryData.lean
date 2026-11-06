-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:24.194528+00:00
-- url     : https://prove2.me/submissions/317dcf3d-f423-4c41-ab0f-ebc881b86d3e

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_complete_diagonal_sum
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_adjoint_projector
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_posSemidef_of_carrier_ne_bot
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_of_indexedProjectorConditionWithScalar
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation


set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hC : C.carrier ≠ ⊥)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar ∧
        (Matrix.of fun i j => scalar i j).PosSemidef ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector ∧
        ∀ i j : ι, star (scalar i j) • C.projector = scalar j i • C.projector := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation C).1 hKL with
    ⟨scalar, hscalar⟩
  exact ⟨scalar, hscalar,
    indexedConditionWithScalar_posSemidef_of_carrier_ne_bot hC
      (indexedConditionWithScalar_of_indexedProjectorConditionWithScalar hscalar),
    indexedProjectorConditionWithScalar_complete_diagonal_sum hE hscalar,
    indexedProjectorConditionWithScalar_adjoint_projector hscalar⟩
end QEC.Semantics.FiniteKrausFamily
