-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:22:53.6122+00:00
-- url     : https://prove2.me/submissions/d25e036e-5dd9-40b1-80fb-42eb74f94f2a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorPGL_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_mul_cyclic_zpow_of_mem_compactCyclicSubgroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r) :
    ∃ u : (ConstantExtension P r)ˣ, ∃ j : ℕ, j < r.matrixRank ∧
      g = buildingConstantPGLHom P r u *
        buildingCyclicGeneratorPGL P r ^ j := by
  obtain ⟨u, n, hn⟩ :=
    exists_constant_mul_cyclic_zpow_of_mem_compactCyclicSubgroup P r g hg
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  let m : ℤ := n % (r.matrixRank : ℤ)
  have hmNonneg : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hd)
  have hmLt : m < (r.matrixRank : ℤ) := Int.emod_lt_of_pos n hd
  let j : ℕ := m.toNat
  have hj : j < r.matrixRank := by
    exact (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2 hmLt
  refine ⟨u, j, hj, ?_⟩
  rw [hn]
  have hreduce : buildingCyclicGeneratorPGL P r ^ n =
      buildingCyclicGeneratorPGL P r ^ m := by
    exact zpow_eq_zpow_emod' n
      (buildingCyclicGeneratorPGL_pow_matrixRank P r)
  rw [hreduce]
  congr 1
  rw [← zpow_natCast]
  congr 1
  exact (Int.toNat_of_nonneg hmNonneg).symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
