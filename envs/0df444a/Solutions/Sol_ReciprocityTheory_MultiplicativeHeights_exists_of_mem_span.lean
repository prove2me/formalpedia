-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.exists_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:29.588449+00:00
-- url     : https://prove2.me/submissions/70270879-449b-452f-8ee2-47ebe8ac1913

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι κ : Type*} (F : MvPolynomial ι ℂ) (m : κ → (ι →₀ ℕ)) (A : Set κ)
    (y : MvPolynomial ι ℂ)
    (hy : y ∈ Submodule.span ℂ ((fun j => F * MvPolynomial.monomial (m j) (1 : ℂ)) '' A)) :
    ∃ Q : MvPolynomial ι ℂ, y = F * Q ∧ (Q.support : Set (ι →₀ ℕ)) ⊆ m '' A := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨MvPolynomial.monomial (m j) 1, rfl, ?_⟩
    intro t ht
    have h1 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp ht)
    rw [Finset.mem_singleton] at h1
    exact ⟨j, hj, h1.symm⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Q1, rfl, h1⟩ := hx
    obtain ⟨Q2, rfl, h2⟩ := hy
    refine ⟨Q1 + Q2, by ring, ?_⟩
    intro t ht
    rcases Finset.mem_union.mp (MvPolynomial.support_add (Finset.mem_coe.mp ht)) with h | h
    exacts [h1 h, h2 h]
  | smul a x _ hx =>
    obtain ⟨Q, rfl, h⟩ := hx
    refine ⟨a • Q, by rw [mul_smul_comm], ?_⟩
    intro t ht
    exact h (MvPolynomial.support_smul (Finset.mem_coe.mp ht))
end ReciprocityTheory.MultiplicativeHeights
