-- Prove2me | solution 1 for P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:36:27.174384+00:00
-- url     : https://prove2.me/submissions/e6a1b8a9-7c80-4204-8648-ba38205295fa

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly
import Theorems.Thm_KernelRank_eq_zero_of_sum_expPoly_eq_zero
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero



set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {κ : Type*} [Fintype κ] {ν : κ → ℂ}
    (hν : Function.Injective ν) (P : κ → ℂ[X])
    (h : ∀ u : ℝ, 0 < u → ∑ k, expPoly (P k) (ν k) u = 0) : ∀ k, P k = 0 := by
  classical
  intro k
  have : Nonempty κ := ⟨k⟩
  let Q : ℂ → ℂ[X] := fun μ => P (Function.invFun ν μ)
  have hQ : ∀ k, Q (ν k) = P k := fun k => congrArg P (Function.leftInverse_invFun hν k)
  have hsum : ∀ u : ℝ, 0 < u →
      ∑ μ ∈ Finset.univ.image ν, expPoly (Q μ) μ u = 0 := by
    intro u hu
    rw [Finset.sum_image fun a _ b _ hab => hν hab]
    simpa [hQ] using h u hu
  rw [← hQ k]
  exact eq_zero_of_sum_expPoly_eq_zero _ Q hsum (ν k)
    (Finset.mem_image_of_mem ν (Finset.mem_univ k))
end KernelRank
