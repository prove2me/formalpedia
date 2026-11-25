-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_HadamardGramBound_linearIndependent_of_mem_span_a89d91bbfa19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:03.445394+00:00
-- url     : https://prove2.me/submissions/d786315f-4a07-4081-afa1-012b08ab1ae3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LinearIndependentOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℕ} (v b : Fin r → E) (hv : LinearIndependent ℝ v)
    (hb : ∀ i, v i ∈ Submodule.span ℤ (Set.range b)) : LinearIndependent ℝ b := by
  have hle : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le_restrictScalars ℤ ℝ (Set.range b) (hb i)
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = r := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hfin : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have h2 : r ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range b)) := by
    have := Submodule.finrank_mono hle
    omega
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) ≤ r := by
    simpa [Set.finrank] using finrank_range_le_card (R := ℝ) b
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank]
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound
