-- Prove2me | solution 1 for PCLAssort.lemma_2_edge_sign
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:41:17.905106+00:00
-- url     : https://prove2.me/submissions/8b9f9a6a-1286-4389-ba50-7ec31c9891b7

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_xiShare
import Definitions.Def_PCLAssort_pclWeight

namespace Aux_PCL2

theorem ratio_le (v w γ : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    v ^ (1 / γ) / (v ^ (1 / γ) + w ^ (1 / γ)) ^ (1 - γ) ≤ v := by
  have hγne : γ ≠ 0 := hγ0.ne'
  rcases eq_or_lt_of_le hv with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity), zero_div]
  · have ha : 0 < v ^ (1 / γ) := Real.rpow_pos_of_pos hpos _
    have hb : 0 ≤ w ^ (1 / γ) := Real.rpow_nonneg hw _
    have h1 : (v ^ (1 / γ)) ^ (1 - γ) ≤ (v ^ (1 / γ) + w ^ (1 / γ)) ^ (1 - γ) :=
      Real.rpow_le_rpow ha.le (by linarith) (by linarith)
    have h2 : 0 < (v ^ (1 / γ)) ^ (1 - γ) := Real.rpow_pos_of_pos ha _
    calc v ^ (1 / γ) / (v ^ (1 / γ) + w ^ (1 / γ)) ^ (1 - γ)
        ≤ v ^ (1 / γ) / (v ^ (1 / γ)) ^ (1 - γ) := div_le_div_of_nonneg_left ha.le h2 h1
      _ = v := by
        have e : v ^ (1 / γ) / (v ^ (1 / γ)) ^ (1 - γ) = (v ^ (1 / γ)) ^ γ := by
          rw [div_eq_iff h2.ne', ← Real.rpow_add ha, show γ + (1 - γ) = 1 by ring, Real.rpow_one]
        rw [e, ← Real.rpow_mul hv, show 1 / γ * γ = 1 by field_simp, Real.rpow_one]

theorem ratio_nonneg (v w γ : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ v ^ (1 / γ) / (v ^ (1 / γ) + w ^ (1 / γ)) ^ (1 - γ) :=
  div_nonneg (Real.rpow_nonneg hv _)
    (Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg hv _) (Real.rpow_nonneg hw _)) _)

end Aux_PCL2

open PCLAssort in
theorem solution {n : ℕ} (I : PCLAssort.PCLInstance n) (z : ℝ) (i : Fin n) :
    (I.r i - z < 0 → ∀ e ∈ PCLAssort.pclEdges n, e.1 = some i → PCLAssort.pclWeight I z e ≤ 0) ∧
    (0 ≤ I.r i - z → ∀ e ∈ PCLAssort.pclEdges n, e.1 = some i → 0 ≤ PCLAssort.pclWeight I z e) := by
  have hxi : ∀ k l, PCLAssort.xiShare I z k l i = (I.r i - z) *
      (I.v i ^ (1 / I.γ k l) / (I.v k ^ (1 / I.γ k l) + I.v l ^ (1 / I.γ k l)) ^ (1 - I.γ k l)) := by
    intro k l; unfold PCLAssort.xiShare; ring
  have hR1 : ∀ j, j ≠ i →
      I.v i ^ (1 / I.γ i j) / (I.v i ^ (1 / I.γ i j) + I.v j ^ (1 / I.γ i j)) ^ (1 - I.γ i j)
        ≤ I.v i := fun j hj =>
    Aux_PCL2.ratio_le _ _ _ (I.v_nonneg i) (I.v_nonneg j) (I.γ_pos i j (Ne.symm hj))
      (I.γ_le_one i j (Ne.symm hj))
  have hR2 : ∀ j, j ≠ i →
      I.v i ^ (1 / I.γ j i) / (I.v j ^ (1 / I.γ j i) + I.v i ^ (1 / I.γ j i)) ^ (1 - I.γ j i)
        ≤ I.v i := fun j hj => by
    rw [add_comm (I.v j ^ (1 / I.γ j i))]
    exact Aux_PCL2.ratio_le _ _ _ (I.v_nonneg i) (I.v_nonneg j) (I.γ_pos j i hj)
      (I.γ_le_one j i hj)
  have hN1 : ∀ k l, 0 ≤ I.v i ^ (1 / I.γ k l) /
      (I.v k ^ (1 / I.γ k l) + I.v l ^ (1 / I.γ k l)) ^ (1 - I.γ k l) := fun k l =>
    div_nonneg (Real.rpow_nonneg (I.v_nonneg i) _)
      (Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg (I.v_nonneg k) _)
        (Real.rpow_nonneg (I.v_nonneg l) _)) _)
  constructor
  · intro hneg e he he1
    obtain ⟨e1, e2⟩ := e
    simp only at he1
    subst he1
    cases e2 with
    | none =>
      show ∑ k ∈ Finset.univ.erase i, (PCLAssort.xiShare I z i k i + PCLAssort.xiShare I z k i i) ≤ 0
      apply Finset.sum_nonpos
      intro k _
      rw [hxi, hxi]
      nlinarith [hN1 i k, hN1 k i]
    | some j =>
      show (if i = j then 0 else 2 * (I.v i * (I.r i - z)) - PCLAssort.xiShare I z i j i -
        PCLAssort.xiShare I z j i i) ≤ 0
      split_ifs with hij
      · exact le_rfl
      · rw [hxi, hxi]
        have h1 := hR1 j (Ne.symm hij)
        have h2 := hR2 j (Ne.symm hij)
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -(I.r i - z))
          (by linarith : (0:ℝ) ≤ 2 * I.v i -
            I.v i ^ (1 / I.γ i j) / (I.v i ^ (1 / I.γ i j) + I.v j ^ (1 / I.γ i j)) ^ (1 - I.γ i j) -
            I.v i ^ (1 / I.γ j i) / (I.v j ^ (1 / I.γ j i) + I.v i ^ (1 / I.γ j i)) ^ (1 - I.γ j i))]
  · intro hpos e he he1
    obtain ⟨e1, e2⟩ := e
    simp only at he1
    subst he1
    cases e2 with
    | none =>
      show 0 ≤ ∑ k ∈ Finset.univ.erase i, (PCLAssort.xiShare I z i k i + PCLAssort.xiShare I z k i i)
      apply Finset.sum_nonneg
      intro k _
      rw [hxi, hxi]
      nlinarith [mul_nonneg hpos (hN1 i k), mul_nonneg hpos (hN1 k i)]
    | some j =>
      show 0 ≤ (if i = j then 0 else 2 * (I.v i * (I.r i - z)) - PCLAssort.xiShare I z i j i -
        PCLAssort.xiShare I z j i i)
      split_ifs with hij
      · exact le_rfl
      · rw [hxi, hxi]
        have h1 := hR1 j (Ne.symm hij)
        have h2 := hR2 j (Ne.symm hij)
        nlinarith [mul_nonneg hpos
          (by linarith : (0:ℝ) ≤ 2 * I.v i -
            I.v i ^ (1 / I.γ i j) / (I.v i ^ (1 / I.γ i j) + I.v j ^ (1 / I.γ i j)) ^ (1 - I.γ i j) -
            I.v i ^ (1 / I.γ j i) / (I.v j ^ (1 / I.γ j i) + I.v i ^ (1 / I.γ j i)) ^ (1 - I.γ j i))]
