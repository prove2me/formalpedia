-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirrH_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:36.424079+00:00
-- url     : https://prove2.me/submissions/9514f763-ed22-4000-9c5d-fa2e2afc669e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) {μ : Fin n → ℝ} {x : X} (hx : ∀ a, A a a x = (μ a : ℂ) • x) :
    kirrH A k x = (kirrPs k μ : ℂ) • x := by
  rw [kirrH, LinearMap.sum_apply]
  simp only [hx, kirrPs, Complex.ofReal_sum, Finset.sum_smul]
end ReciprocityTheory.ChartRestriction.DS
