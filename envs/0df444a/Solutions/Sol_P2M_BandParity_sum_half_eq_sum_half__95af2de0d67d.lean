-- Prove2me | solution 1 for P2M_BandParity_sum_half_eq_sum_half__95af2de0d67d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:04.193412+00:00
-- url     : https://prove2.me/submissions/b42d1c82-9b62-4044-a0b2-990a92dcfd1c

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution {R : Type*} [AddCommMonoid R] (h : ZMod p → R) (h0 : h 0 = 0) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), h x =
      ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p), h x := by
  symm
  refine Finset.sum_subset (fun x hx => by simp at hx ⊢; exact hx.2) fun x hx hx' => ?_
  simp only [mem_filter, mem_univ, true_and, not_and, not_lt] at hx hx'
  have : x.val = 0 := by
    by_contra hne; exact absurd hx (by have := hx' (Nat.pos_of_ne_zero hne); omega)
  rw [(ZMod.val_eq_zero x).1 this, h0]
end BandParity
