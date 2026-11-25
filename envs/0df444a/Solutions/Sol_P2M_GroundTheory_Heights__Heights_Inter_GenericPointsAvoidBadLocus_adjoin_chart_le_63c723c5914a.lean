-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_adjoin_chart_le_63c723c5914a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:03.675233+00:00
-- url     : https://prove2.me/submissions/c903e0e5-438a-4770-ad5b-0dcd97cae367

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogProdInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
    (G : GenFibre v P') (i j : ∀ k : FibreBlock κ, ι' k.1) (hi : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) :
    IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) ≤
      IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have hq : G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ =
      (G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) / (G.x' ⟨q.1.1, j q.1⟩ / G.x' ⟨q.1.1, i q.1⟩) :=
    (div_div_div_cancel_right₀ (hi q.1) _ _).symm
  show G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ ∈ _
  rw [hq]
  exact div_mem (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    (IntermediateField.subset_adjoin _ _ ⟨⟨q.1, j q.1⟩, rfl⟩)
end GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus
