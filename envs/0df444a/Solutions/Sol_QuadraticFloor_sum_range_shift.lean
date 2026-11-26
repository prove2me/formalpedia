-- Prove2me | solution 1 for QuadraticFloor.sum_range_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:10.241806+00:00
-- url     : https://prove2.me/submissions/6e737a10-253c-4bed-b7df-deddc9c55f23

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_periodic_int
public import Theorems.Thm_QuadraticFloor_sum_range_eq_sum_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution {g : ℤ → ℤ} (hg : ∀ m, g (m + p) = g m) (t : ℤ) :
    ∑ n ∈ range p, g (n + t) = ∑ n ∈ range p, g n := by
  have hgz : ∀ m : ℤ, g m = g ((m : ZMod p).val) := by
    intro m
    rw [ZMod.val_intCast]
    have := periodic_int hg (m % p) (m / p)
    rw [Int.emod_add_mul_ediv] at this
    exact this
  set G : ZMod p → ℤ := fun x => g x.val
  have h1 : ∀ n : ℕ, g (n + t) = G ((n : ZMod p) + (t : ZMod p)) := by
    intro n; rw [hgz]; push_cast; rfl
  have h2 : ∀ n : ℕ, g n = G (n : ZMod p) := by
    intro n; rw [hgz]; push_cast; rfl
  simp_rw [h1, h2]
  rw [sum_range_eq_sum_zmod (fun x => G (x + (t : ZMod p))), sum_range_eq_sum_zmod G]
  exact Equiv.sum_comp (Equiv.addRight (t : ZMod p)) G
end QuadraticFloor
