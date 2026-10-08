-- Prove2me | solution 1 for RetailVariety.Statics.share_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:24:05.048723+00:00
-- url     : https://prove2.me/submissions/0eacf721-d2db-473a-83a9-40f35b22c5ed

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology RetailVariety.Statics

theorem solution (n : ℕ) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j) :
    (∀ (S : Finset (Fin n)) (j : Fin n), S.Nonempty →
      Tendsto (fun v0 : ℝ => RetailVariety.Structure.share v v0 S j) (𝓝[>] 0) (𝓝 (v j / ∑ k ∈ S, v k))) ∧
    (∀ i : ℕ, 1 ≤ i → i < n →
      Tendsto (fun v0 : ℝ => ∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j
          - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j) (𝓝[>] 0) (𝓝 0)) := by
  have hpos (S : Finset (Fin n)) (hS : S.Nonempty) : 0 < ∑ k ∈ S, v k :=
    Finset.sum_pos (fun k _ => hv k) hS
  have hlim (S : Finset (Fin n)) (j : Fin n) (hS : S.Nonempty) :
      Tendsto (fun v0 : ℝ => RetailVariety.Structure.share v v0 S j) (𝓝[>] 0)
        (𝓝 (v j / ∑ k ∈ S, v k)) := by
    have hid : Tendsto (fun v0 : ℝ => v0) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hden : Tendsto (fun v0 : ℝ => (∑ k ∈ S, v k) + v0) (𝓝[>] 0)
        (𝓝 (∑ k ∈ S, v k)) := by
      simpa using (tendsto_const_nhds.add hid)
    simpa only [RetailVariety.Structure.share, Pi.div_def] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => v j) (𝓝[>] 0) (𝓝 (v j))).div
        hden (ne_of_gt (hpos S hS)))
  refine ⟨hlim, ?_⟩
  intro i hi hin
  have hne (k : ℕ) (hk : 1 ≤ k) : (A n k).Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [A, RetailVariety.Structure.popularSet]; omega
  have hsum (S : Finset (Fin n)) (hS : S.Nonempty) :
      Tendsto (fun v0 : ℝ => ∑ j ∈ S, RetailVariety.Structure.share v v0 S j)
        (𝓝[>] 0) (𝓝 1) := by
    have ht := tendsto_finset_sum S (fun j _ => hlim S j hS)
    simpa [← Finset.sum_div, div_self (ne_of_gt (hpos S hS))] using ht
  simpa using (hsum (A n (i+1)) (hne _ (by omega))).sub (hsum (A n i) (hne _ hi))

#print axioms solution
