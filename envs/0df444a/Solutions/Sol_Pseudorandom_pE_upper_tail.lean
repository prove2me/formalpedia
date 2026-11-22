-- Prove2me | solution 1 for Pseudorandom.pE_upper_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:17.011075+00:00
-- url     : https://prove2.me/submissions/4f0ea7e1-e224-4bce-b30c-aa9bd619aafe

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Theorems.Thm_Pseudorandom_pE_upper_tail_fin
public import Theorems.Thm_Pseudorandom_pE_equiv
public import Theorems.Thm_Pseudorandom_pProb_equiv


set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
namespace Pseudorandom
theorem _root_.solution (P : ι → α → ℝ) (hP : IsPMF P)
    (f : (ι → α) → ℝ) (c q : ι → ℝ) (R : ι → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  set e := Fintype.equivFin ι
  rw [pProb_equiv e, pE_equiv e]
  have hP' : IsPMF (fun j => P (e.symm j)) := ⟨fun j a => hP.1 _ a, fun j => hP.2 _⟩
  have hV : ∑ i, q i * c i ^ 2 = ∑ j, q (e.symm j) * c (e.symm j) ^ 2 :=
    (Fintype.sum_equiv e.symm _ _ (fun j => rfl)).symm
  rw [hV]
  apply pE_upper_tail_fin _ hP' (fun ω' => f (ω' ∘ e)) (fun j => c (e.symm j))
    (fun j => q (e.symm j)) (fun j => R (e.symm j)) L hL (fun j => hc _) _ _
    (fun j => hq _) t ht
  · intro j ω' a b
    have := hf (e.symm j) (ω' ∘ e) a b
    simpa [Function.update_comp_equiv] using this
  · intro j ω' a b ha hb
    have := hfR (e.symm j) (ω' ∘ e) a b ha hb
    simpa [Function.update_comp_equiv] using this
end Pseudorandom
