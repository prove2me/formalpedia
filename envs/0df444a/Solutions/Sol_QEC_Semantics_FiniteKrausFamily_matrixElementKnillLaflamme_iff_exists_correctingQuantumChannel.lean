-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:08.535118+00:00
-- url     : https://prove2.me/submissions/b39cb1eb-f126-4189-9405-667106473816

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_of_sameSpaceKnillLaflammeCriterion
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar


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
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (hE : E.Complete) :
    (∃ scalar : ι → ι → Complex,
      ∀ i j : ι,
        ∀ x : H, x ∈ C.carrier →
          ∀ y : H, y ∈ C.carrier →
            inner Complex (E.operator i x) (E.operator j y) =
              scalar i j * inner Complex x y) ↔
      ∃ recovery : QuantumChannel H H,
        ∀ rho : DensityOperator H,
          DensityOperator.SupportedOn C rho →
            recovery (E.inducedMap rho.toOperator) = rho.toOperator := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    have hKL : E.sameSpaceKnillLaflammeCriterion C :=
      (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).2
        ⟨scalar, hscalar⟩
    rcases exists_recovery_of_sameSpaceKnillLaflammeCriterion E C hE hKL with
      ⟨recovery, _, hcorrected⟩
    exact ⟨recovery, hcorrected⟩
  · rintro ⟨recovery, hcorrected⟩
    have hKL : E.sameSpaceKnillLaflammeCriterion C :=
      sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
        E C recovery ⟨hE, hcorrected⟩
    exact (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).1 hKL
end QEC.Semantics.FiniteKrausFamily
