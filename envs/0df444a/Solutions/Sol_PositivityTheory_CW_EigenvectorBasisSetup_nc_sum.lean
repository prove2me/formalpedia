-- Prove2me | solution 1 for PositivityTheory.CW.EigenvectorBasisSetup.nc_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:46.064444+00:00
-- url     : https://prove2.me/submissions/503078ef-6c3e-44be-bb3a-aca757a472fb

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_OrthonormalEigenbasisOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenvectorBasisSetup
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.EigenvectorBasisSetup
theorem _root_.solution {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε b = ε a then 0 else f (a, b) := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]
end PositivityTheory.CW.EigenvectorBasisSetup
