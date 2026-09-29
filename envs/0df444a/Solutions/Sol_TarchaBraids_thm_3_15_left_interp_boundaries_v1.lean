-- Prove2me | solution 1 for TarchaBraids.thm_3_15_left_interp_boundaries_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T09:27:19.855872+00:00
-- url     : https://prove2.me/submissions/2d3300b2-24e5-4344-bb67-dc239b19a409

import Mathlib
import Definitions.Def_TarchaBraids_left_interp_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_zero_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_one_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_one_endpoint_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma adjacent_hi2_boundary_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : (i : ℕ) + 2 < n := by
  have hj := j.isLt
  omega

lemma leftInterp_zero_u_boundary_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : unitInterval) :
    configProj n (leftOuterInterpConfig i j hji 0 q) =
      configProj n (leftBraidConfig n i j (q : ℝ)) := by
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  simp [leftOuterInterpConfig, leftOuterInterpFun, braidInterp, leftBraidConfig]

lemma leftInterp_one_u_boundary_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (hi2 : (i : ℕ) + 2 < n)
    (q : unitInterval) :
    configProj n (leftOuterInterpConfig i j hji 1 q) =
      configProj n (outerRotateConfig i hi2 (q : ℝ)) := by
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  simp [leftOuterInterpConfig, leftOuterInterpFun, braidInterp, outerRotateConfig]

lemma leftInterp_zero_time_boundary_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u : unitInterval) :
    configProj n (leftOuterInterpConfig i j hji u 0) = baseUnordered n := by
  change configProj n (leftOuterInterpConfig i j hji u 0) =
    configProj n (baseOrdered n)
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  have hL := thm_3_15_adjacent_raw_zero_endpoints_v1.1 n i j
  have hO := thm_3_15_adjacent_raw_zero_endpoints_v1.2.2 n i
  change braidInterp (u : ℝ) (leftBraidFun n i j 0 k) (outerRotateFun n i 0 k) =
    (baseOrdered n).1 k
  rw [congrFun hL k, congrFun hO k]
  unfold braidInterp
  module

lemma leftInterp_one_fun_boundary_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u : unitInterval) :
    (leftOuterInterpConfig i j hji u 1).1 =
      (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  funext k
  have hi2 := adjacent_hi2_boundary_v1 i j hji
  have hL := (thm_3_15_adjacent_word_one_endpoints_v1 i j hji).1
  have hO := thm_3_15_adjacent_outer_one_endpoint_v1 i j hji hi2
  change braidInterp (u : ℝ) (leftBraidFun n i j 1 k) (outerRotateFun n i 1 k) =
    ((baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j)) k
  rw [congrFun hL k, congrFun hO k]
  unfold braidInterp
  module

lemma leftInterp_one_time_boundary_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u : unitInterval) :
    configProj n (leftOuterInterpConfig i j hji u 1) = baseUnordered n := by
  change Quotient.mk (configSetoid n) (leftOuterInterpConfig i j hji u 1) =
    Quotient.mk (configSetoid n) (baseOrdered n)
  have h : configProj n (baseOrdered n) =
      configProj n (leftOuterInterpConfig i j hji u 1) :=
    Quotient.sound ⟨Equiv.swap (strandIdx i) (strandIdxSucc j),
      leftInterp_one_fun_boundary_v1 i j hji u⟩
  exact h.symm

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : unitInterval,
        configProj n (leftOuterInterpConfig i j hji 0 q) =
          configProj n (leftBraidConfig n i j (q : ℝ))) ∧
      (∀ (hi2 : (i : ℕ) + 2 < n) (q : unitInterval),
        configProj n (leftOuterInterpConfig i j hji 1 q) =
          configProj n (outerRotateConfig i hi2 (q : ℝ))) ∧
      (∀ u : unitInterval,
        configProj n (leftOuterInterpConfig i j hji u 0) = baseUnordered n) ∧
      (∀ u : unitInterval,
        configProj n (leftOuterInterpConfig i j hji u 1) = baseUnordered n) := by
  intro n i j hji
  exact ⟨leftInterp_zero_u_boundary_v1 i j hji,
    ⟨fun hi2 => leftInterp_one_u_boundary_v1 i j hji hi2,
      ⟨leftInterp_zero_time_boundary_v1 i j hji,
        leftInterp_one_time_boundary_v1 i j hji⟩⟩⟩
