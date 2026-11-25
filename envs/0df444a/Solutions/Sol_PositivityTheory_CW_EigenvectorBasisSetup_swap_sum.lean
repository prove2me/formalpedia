-- Prove2me | solution 1 for PositivityTheory.CW.EigenvectorBasisSetup.swap_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:03.787708+00:00
-- url     : https://prove2.me/submissions/bf20b7cf-d3dd-4728-87aa-32303c36d2bb

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f g : Fin n → Fin n → M) :
    (∑ a, ∑ b, if ε b = ε a then f a b else g a b) =
      ∑ a, ∑ b, if ε b = ε a then f b a else g b a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]
end PositivityTheory.CW.EigenvectorBasisSetup
