-- Prove2me | solution 1 for Pseudorandom.pE_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:27.096272+00:00
-- url     : https://prove2.me/submissions/2cbfb9fc-dc49-4c32-bbb1-f362d58b5036

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Theorems.Thm_Pseudorandom_CoordGap_neg
public import Theorems.Thm_Pseudorandom_CoordRare_neg
public import Theorems.Thm_Pseudorandom_pE_upper_tail
public import Theorems.Thm_Pseudorandom_pE_neg


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
    pProb P (fun ω => t ≤ pE P f - f ω) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  have h := pE_upper_tail P hP (fun ω => -f ω) c q R L hL hc hf.neg hfR.neg hq t ht
  rw [pE_neg] at h
  convert h using 3
  constructor <;> intro h' <;> linarith
end Pseudorandom
