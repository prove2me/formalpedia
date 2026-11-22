-- Prove2me | solution 1 for P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___20106223d85b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:50.684856+00:00
-- url     : https://prove2.me/submissions/1bfd02a2-1e2a-4e08-9e31-9f6b9e6de9a6

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples
section
public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
private lemma marginal_comp {e : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ} (he : ∀ x, e (e x) = x)
    (hs : ∀ x, e x ∈ sumTriples N ↔ x ∈ sumTriples N) :
    marginal N (J ∘ e) g = marginal N J (g ∘ e) := by
  ext k
  refine sum_nbij' e e ?_ ?_ (fun x _ ↦ he x) (fun x _ ↦ he x) (fun _ _ ↦ rfl)
  all_goals
    intro x hx
    simpa [hs, he] using hx
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace Compatible
theorem _root_.solution (h : Compatible N π₁ π₂ π₃) : Compatible N π₂ π₁ π₃ := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  have hcomp (g) := marginal_comp (N := N) (J := J) (g := g) (e := fun (a, b, c) ↦ (b, a, c))
    (fun _ ↦ rfl) (by simp [add_comm])
  exact ⟨_, fun x ↦ hJ _, hcomp _, hcomp _, hcomp _⟩
end Compatible
end ArithmeticTriangleRemovalInVectorSpaces
