-- Prove2me | solution 1 for P2M_QuadraticFloor_floorSum_one__50c18f664e37
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:51.567839+00:00
-- url     : https://prove2.me/submissions/3fad6c17-e8f0-4521-99fb-3926a33d448e

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
public import Theorems.Thm_P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07
public import Theorems.Thm_QuadraticFloor_eta_mul_chi4_sq
public import Theorems.Thm_QuadraticFloor_ite_of_neg


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) :
    (floorSum 1 1 0 p : ℂ) = 1 - bern (8 * p) (fun x => (eta p x : ℂ)) := by
  have h := floorSum_universal' (A := 1) hp2 odd_one (fun h => by
    have := Nat.le_of_dvd one_pos h; have := hp.out.two_le; omega)
  have hsub : Subsingleton (DirichletCharacter ℂ 1) := ⟨fun ψ ψ' => MulChar.ext' fun a => by
    rw [Subsingleton.elim a 1, map_one, map_one]⟩
  rw [Fintype.sum_subsingleton _ 1] at h
  push_cast at h
  rw [h]
  simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul]
  congr 2
  funext x
  unfold vartheta
  have h1 : (1 : DirichletCharacter ℂ 1) (-1) ≠ -1 := by
    rw [Subsingleton.elim (-1 : ZMod 1) 1, map_one]; norm_num
  rw [ite_of_neg h1, Subsingleton.elim (x : ZMod 1) 1, map_one, mul_one, eta_mul_chi4_sq]
end QuadraticFloor
