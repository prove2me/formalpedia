-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_adjoin_embK_eq_span_8c48a6f16835
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:19:41.717545+00:00
-- url     : https://prove2.me/submissions/519b864e-2c05-4abd-a9ac-08491bd3a434

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]
variable {T : Type}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (Φ₀ : Type) [Field Φ₀]
    [Algebra Φ₀ (dualStdModelField K i)] :
    Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range (embK K i))) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by
  have hq : ∀ q : ℚ, (q : dualStdModelField K i) = algebraMap Φ₀ _ ((q.num : Φ₀) / (q.den : Φ₀)) := fun q => by
    rw [map_div₀, map_intCast, map_natCast, Rat.cast_def]
  rw [Algebra.adjoin_eq_span, show Submonoid.closure (Set.range (embK K i)) = (embK K i).range.toSubmonoid from
    Submonoid.closure_eq (embK K i).range.toSubmonoid]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← B.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast, hq, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨B k, rfl⟩)
end GroundTheory.Heights₂.Heights.StandardModelDualRank
