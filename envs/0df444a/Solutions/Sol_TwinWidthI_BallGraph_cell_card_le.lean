-- Prove2me | solution 1 for TwinWidthI.BallGraph.cell_card_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:16:01.656634+00:00
-- url     : https://prove2.me/submissions/60f389ed-141c-40ef-9730-851579cd7a74

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace Aux_CellW31
open TwinWidthI.BallGraph

lemma dist_le {d : ℕ} (z : Fin d → ℤ) (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ cell z) (hq : q ∈ cell z) : dist p q ≤ 2 := by
  rw [EuclideanSpace.dist_eq]
  set s : ℝ := 2 / Real.sqrt d with hs
  have hterm : ∀ i, dist (p i) (q i) ^ 2 ≤ s ^ 2 := by
    intro i
    obtain ⟨hp1, hp2⟩ := hp i
    obtain ⟨hq1, hq2⟩ := hq i
    have e : ((z i : ℝ) + 1) * s = (z i : ℝ) * s + s := by ring
    rw [Real.dist_eq]
    have h1 : |p i - q i| ≤ s := by rw [abs_le]; constructor <;> linarith
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsum : ∑ i, dist (p i) (q i) ^ 2 ≤ 4 := by
    calc ∑ i, dist (p i) (q i) ^ 2 ≤ ∑ _i : Fin d, s ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * (4 / d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs, div_pow,
          Real.sq_sqrt (Nat.cast_nonneg d)]
        norm_num
      _ ≤ 4 := by
        by_cases hd : (d : ℝ) = 0
        · rw [hd]; norm_num
        · rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hd, mul_one]
  calc Real.sqrt (∑ i, dist (p i) (q i) ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hsum
    _ = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end Aux_CellW31

open TwinWidthI.BallGraph in
theorem solution (d k : ℕ) {V : Type*} [Fintype V]
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (z : Fin d → ℤ) :
    {v : V | c v ∈ cell z}.ncard ≤ k := by
  classical
  by_contra hlt
  push_neg at hlt
  set S := {v : V | c v ∈ cell z} with hS
  rw [Set.ncard_eq_toFinset_card' S] at hlt
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (s := S.toFinset) (n := k + 1) (by omega)
  apply hK t
  refine ⟨?_, htc⟩
  intro u hu v hv huv
  have hu' : c u ∈ cell z := by
    have := hts (Finset.mem_coe.1 hu); rw [Set.mem_toFinset] at this; exact this
  have hv' : c v ∈ cell z := by
    have := hts (Finset.mem_coe.1 hv); rw [Set.mem_toFinset] at this; exact this
  exact ⟨huv, Aux_CellW31.dist_le z _ _ hu' hv'⟩
