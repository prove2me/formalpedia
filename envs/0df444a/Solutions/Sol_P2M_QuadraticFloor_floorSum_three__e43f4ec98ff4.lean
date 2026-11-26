-- Prove2me | solution 1 for P2M_QuadraticFloor_floorSum_three__e43f4ec98ff4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:59.779215+00:00
-- url     : https://prove2.me/submissions/d95c22e5-2736-4e00-8880-892f9e0ae6f9

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
public import Theorems.Thm_P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07
public import Theorems.Thm_QuadraticFloor_chi3_apply
public import Theorems.Thm_QuadraticFloor_chi3_two
public import Theorems.Thm_QuadraticFloor_char3_cases
public import Theorems.Thm_QuadraticFloor_eta_mul_chi4_sq
public import Theorems.Thm_QuadraticFloor_ite_of_neg
public import Theorems.Thm_QuadraticFloor_ite_of_pos


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      (bern (24 * p) (fun x => (eta p x : ℂ) * (if 3 ∣ x then 0 else 1)) +
        bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
          (legendreSym 3 x : ℂ))) := by
  have hpA : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h)
  have h := floorSum_universal' (A := 3) hp2 (by decide) hpA
  have hne : (1 : DirichletCharacter ℂ 3) ≠ chi3 := by
    intro h; have := DFunLike.congr_fun h 2
    rw [chi3_two, MulChar.one_apply (IsUnit.of_mul_eq_one (2 : ZMod 3)
      (by decide))] at this; norm_num at this
  have huniv : (univ : Finset (DirichletCharacter ℂ 3)) = {1, chi3} := by
    ext ψ; simp only [mem_univ, mem_insert, mem_singleton, true_iff]; exact char3_cases ψ
  rw [huniv, sum_pair hne] at h
  push_cast at h
  rw [h, show Nat.totient 3 = 2 by decide, show 8 * 3 * p = 24 * p by ring]
  push_cast
  congr 3
  · congr 1
    funext x
    unfold vartheta
    have h1 : (1 : DirichletCharacter ℂ 3) (-1) ≠ -1 := by
      rw [MulChar.one_apply (IsUnit.neg isUnit_one)]; norm_num
    rw [ite_of_neg h1, eta_mul_chi4_sq]
    congr 1
    by_cases h3 : 3 ∣ x
    · rw [ite_of_pos h3, MulChar.map_nonunit]
      rw [(ZMod.natCast_eq_zero_iff x 3).2 h3]; exact not_isUnit_zero
    · rw [ite_of_neg h3, MulChar.one_apply]
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
  · congr 1
    funext x
    unfold vartheta
    have h1 : chi3 (-1) = -1 := by rw [show (-1 : ZMod 3) = 2 by decide, chi3_two]
    rw [ite_of_pos h1, chi3_apply]
end QuadraticFloor
