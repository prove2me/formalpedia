-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirr_eq_of_ps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:25.378615+00:00
-- url     : https://prove2.me/submissions/198a954b-9ea2-4291-aff0-5e68fe386303

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
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section KIrr
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
private theorem kirrPs_succ (μ : Fin n → ℝ) (a : Fin n) : kirrPs (a.val + 1) μ = kirrPs a.val μ + μ a := by
  simp only [kirrPs]
  rw [show univ.filter (fun b : Fin n => b.val < a.val + 1) = insert a (univ.filter (fun b : Fin n => b.val < a.val)) by
    ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]; omega]
  rw [Finset.sum_insert (by simp), add_comm]
end KIrr
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {μ ν : Fin n → ℝ} (h : ∀ k, kirrPs k μ = kirrPs k ν) : μ = ν := by
  funext a
  have h1 := h (a.val + 1)
  rw [kirrPs_succ, kirrPs_succ, h a.val] at h1
  linarith
end ReciprocityTheory.ChartRestriction.DS
