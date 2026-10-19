-- Prove2me | solution 1 for TwoDegenerateGraphs.twoDegenerateExtremalCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/25f70fc7-12de-4054-aa0f-0503a2113b6e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_extremalNumber_monotone_of_no_isolated
import Theorems.Thm_TwoDegenerateGraphs_entropyUpperEndpoint_lt_one
import Theorems.Thm_TwoDegenerateGraphs_exponentGain_pos
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_connected
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_isBipartite
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_isTwoDegenerate
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_bipartition_maximum_degree_gt_two
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_forall_exists_adj
import Theorems.Thm_TwoDegenerateGraphs_manuscriptExtremalPower_pos
import Theorems.Thm_TwoDegenerateGraphs_eventually_manuscriptVertexCount_power_le_extremalNumber
import Theorems.Thm_TwoDegenerateGraphs_manuscriptVertexCount_succ_le_two_mul
import Theorems.Thm_TwoDegenerateGraphs_exists_manuscriptVertexCount_bracket

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsTwoDegenerate H ∧
      (∀ coloring : H.Coloring (Fin 2), ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin q => coloring vertex = side)).sup
          (fun vertex => H.degree vertex)) ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  classical
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hsubsequence⟩ :=
    eventually_manuscriptVertexCount_power_le_extremalNumber
  have hwidth : certifiedWindowWidth < 1 := by
    rw [← entropyWindow_eq_certifiedWindowWidth]
    linarith [entropyLowerEndpoint_pos, entropyUpperEndpoint_lt_one]
  have hproduct :
      0 ≤ (depth : ℝ) * (1 - certifiedWindowWidth) :=
    mul_nonneg (Nat.cast_nonneg depth) (sub_nonneg.mpr hwidth.le)
  have hdepth_real : (2 : ℝ) < (depth : ℝ) := by
    nlinarith
  have hdepth_nat : 2 < depth := by
    exact_mod_cast hdepth_real
  have hdepth_two : 2 ≤ depth := by
    omega
  let forbidden :
      SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
    pairGraphOverFin baseSize depth
  have hnoisolated :
      ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
        ∃ neighbor, forbidden.Adj vertex neighbor := by
    exact pairGraphOverFin_forall_exists_adj
      baseSize depth hbase hdepth
  refine ⟨Fintype.card (PairVertex baseSize depth), forbidden,
    pairGraphOverFin_connected baseSize depth (by omega) hdepth,
    pairGraphOverFin_isBipartite baseSize depth,
    pairGraphOverFin_isTwoDegenerate baseSize depth,
    ?_,
    1 / (2 : ℝ) ^ manuscriptExtremalPower,
    exponentGain, ?_, exponentGain_pos, ?_⟩
  · simpa only [forbidden] using
      pairGraphOverFin_bipartition_maximum_degree_gt_two
        baseSize depth hbase hdepth_two
  · exact one_div_pos.mpr
      (Real.rpow_pos_of_pos (by norm_num) manuscriptExtremalPower)
  · obtain ⟨minimum, hminimum⟩ :=
      Filter.eventually_atTop.1 hsubsequence
    apply Filter.eventually_atTop.2
    refine ⟨manuscriptVertexCount minimum, ?_⟩
    intro n hn
    obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
      exists_manuscriptVertexCount_bracket minimum n hn
    have hdouble :=
      manuscriptVertexCount_succ_le_two_mul dimension
    have hn_bound :
        n ≤ 2 * manuscriptVertexCount dimension := by
      omega
    have hn_real :
        (n : ℝ) ≤
          2 * (manuscriptVertexCount dimension : ℝ) := by
      exact_mod_cast hn_bound
    have hsubseq := hminimum dimension hdimension
    have hmonotone :
        SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden ≤
          SimpleGraph.extremalNumber n forbidden :=
      CompactnessConjecture.extremalNumber_monotone_of_no_isolated
        forbidden hnoisolated hbelow
    change
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ)
    calc
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (2 * (manuscriptVertexCount dimension : ℝ)) ^
            manuscriptExtremalPower := by
          apply mul_le_mul_of_nonneg_left
          · exact Real.rpow_le_rpow
              (Nat.cast_nonneg n) hn_real
              manuscriptExtremalPower_pos.le
          · positivity
      _ = (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower := by
          rw [Real.mul_rpow (by norm_num)
            (Nat.cast_nonneg (manuscriptVertexCount dimension))]
          have htwo :
              (2 : ℝ) ^ manuscriptExtremalPower ≠ 0 :=
            (Real.rpow_pos_of_pos (by norm_num)
              manuscriptExtremalPower).ne'
          field_simp [htwo]
      _ ≤ (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden : ℝ) :=
          hsubseq
      _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by
          exact_mod_cast hmonotone
end TwoDegenerateGraphs
