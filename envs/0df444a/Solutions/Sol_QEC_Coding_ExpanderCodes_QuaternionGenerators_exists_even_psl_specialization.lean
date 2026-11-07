-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.exists_even_psl_specialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:27.017256+00:00
-- url     : https://prove2.me/submissions/f8001403-69d3-4303-a7c8-7c16647786ce

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_base_prime_matrix_mem_psl_of_root
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_even_psl_parameters


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (p n : ℕ) [Fact p.Prime]
    (hOdd : 3 ≤ p) (hDegree : 1 < n) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) :
    ∃ (y r : GaloisField p (2 * n)) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
      (hR : r ≠ 0)
      (hRoot : r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
      (hTwo : (2 : GaloisField p (2 * n)) ≠ 0),
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n ∧
      projectiveMatrixEquivOfRoot
          (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y hRoot hR hOne hTwo
          (projectiveBase (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
            y hY hOne) ∈ ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquivOfRoot
          (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y hRoot hR hOne hTwo
          (projectivePrime (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
            y ((map_ne_zero _).mpr hEpsilon) hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by
  obtain ⟨y, r, s, i, hY, hOne, hR, _, hRoot, hRatio, hI, hIrreducible, hMinDegree⟩ :=
    exists_even_psl_parameters p n hDegree epsilon hEpsilon
  have hTwo : (2 : GaloisField p (2 * n)) ≠ 0 := by
    intro hZero
    have hDvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p (2 * n)) p 2).mp hZero
    have := Nat.le_of_dvd (by decide : 0 < 2) hDvd
    omega
  have hBoth := base_prime_matrix_mem_psl_of_root
    (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y s i
    ((map_ne_zero _).mpr hEpsilon) hRoot hR hY hOne hTwo hRatio hI
  exact ⟨y, r, hY, hOne, hR, hRoot, hTwo, hIrreducible, hMinDegree, hBoth⟩
end QEC.Coding.ExpanderCodes.QuaternionGenerators
