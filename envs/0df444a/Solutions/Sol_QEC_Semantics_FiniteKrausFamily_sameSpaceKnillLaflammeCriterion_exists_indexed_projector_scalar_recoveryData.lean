-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_recoveryData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:17.49321+00:00
-- url     : https://prove2.me/submissions/60b06c0f-224b-4139-a905-2f130186a8e5

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_complete_diagonal_sum
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_adjoint_projector
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
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector ∧
        ∀ i j : ι, star (scalar i j) • C.projector = scalar j i • C.projector := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation C).1 hKL with
    ⟨scalar, hscalar⟩
  exact ⟨scalar, hscalar,
    indexedProjectorConditionWithScalar_complete_diagonal_sum hE hscalar,
    indexedProjectorConditionWithScalar_adjoint_projector hscalar⟩
end QEC.Semantics.FiniteKrausFamily
