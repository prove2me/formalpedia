-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefD_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:29.174931+00:00
-- url     : https://prove2.me/submissions/85df11c2-d794-4f2d-b47e-5d958b1e1a5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefC_choose_coef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (s : ℂ) (m : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (L : Fin n → Fin n → ℕ → ℂ) :
    s ^ m / (m.factorial : ℂ) * ∑ c, ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) *
        ∑ d, (B ^ kl.1) c d * L c d kl.2 =
      ∑ c, ∑ d, ∑ kl ∈ antidiagonal m,
        s ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * (s ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← mul_assoc, ← hkl, coefC_choose_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.DS
