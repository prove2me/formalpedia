-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_int_cofinite_824d33c90484
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:34.116294+00:00
-- url     : https://prove2.me/submissions/991b5925-50ab-49df-b0fe-154661b52151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_compAt_sum_5049def067bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_c21a49f6d250

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution (a : AE F E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, compAt E v a ∈ intAt E v := by
  obtain ⟨X, rfl⟩ := exists_repr a
  have hev : ∀ᶠ v in Filter.cofinite, ∀ l, X l v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun l => (X l).2
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv => ?_⟩
  have hv' : ∀ l, X l v ∈ v.adicCompletionIntegers F := by
    by_contra h
    exact hv ((Filter.eventually_cofinite.1 hev).mem_toFinset.2 h)
  rw [compAt_sum]
  exact AddSubgroup.sum_mem _ fun l _ => AddSubgroup.subset_closure ⟨X l v, hv' l, _, rfl⟩
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
