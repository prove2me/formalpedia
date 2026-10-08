-- Prove2me | solution 1 for RetailVariety.Statics.numerator13_tendsto_pos
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:31:02.479979+00:00
-- url     : https://prove2.me/submissions/13f0e480-f9fc-4734-8da4-7c94f3972971

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology
open RetailVariety.Statics
set_option maxHeartbeats 20000
private lemma power_add_gain (V a B β : ℝ) (hV : 0 < V) (ha : 0 < a)
    (hB : 0 < B) (hb : β < 1) (hbound : B * a ≤ V * a ^ β) :
    B / V ^ β < (B + a ^ β) / (V + a) ^ β := by
  let q := (V + a) / V
  have hq : 1 < q := by dsimp [q]; apply (one_lt_div hV).mpr; linarith
  have hpow := Real.rpow_lt_self_of_one_lt hq hb
  have hqb : B * q ≤ B + a ^ β := by
    dsimp [q]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hV).mpr
    nlinarith
  have hstrict : B * q ^ β < B + a ^ β :=
    (mul_lt_mul_of_pos_left hpow hB).trans_le hqb
  have hVp : 0 < V ^ β := Real.rpow_pos_of_pos hV _
  have hqp : 0 < q ^ β := Real.rpow_pos_of_pos (by linarith) _
  have he : (V + a) ^ β = q ^ β * V ^ β := by
    rw [← Real.mul_rpow (by linarith : 0 ≤ q) hV.le]
    congr 1
    exact (div_mul_cancel₀ _ hV.ne').symm
  rw [he]
  apply (div_lt_div_iff₀ hVp (mul_pos hqp hVp)).mpr
  nlinarith [mul_lt_mul_of_pos_right hstrict hVp]


theorem solution (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ)
    (hv : ∀ j, 0 < v j) (hanti : Antitone v) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun v0 : ℝ => ∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j ^ β
          - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j ^ β) (𝓝[>] 0)
        (𝓝 (∑ j ∈ A n (i + 1), (v j / ∑ k ∈ A n (i + 1), v k) ^ β
          - ∑ j ∈ A n i, (v j / ∑ k ∈ A n i, v k) ^ β)) ∧
      0 < ∑ j ∈ A n (i + 1), (v j / ∑ k ∈ A n (i + 1), v k) ^ β
          - ∑ j ∈ A n i, (v j / ∑ k ∈ A n i, v k) ^ β := by
  classical
  let S := A n i
  let a : Fin n := ⟨i, hin⟩
  have hnext : A n (i + 1) = insert a S := by
    ext j
    simp only [S, A, RetailVariety.Structure.popularSet, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert]
    change j.val < i + 1 ↔ j = a ∨ j.val < i
    rw [Fin.ext_iff]
    dsimp [a]
    omega
  have han : a ∉ S := by simp [S, A, RetailVariety.Structure.popularSet, a]
  have hS : S.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [S, A, RetailVariety.Structure.popularSet]
    omega
  let V : ℝ := ∑ j ∈ S, v j
  let B : ℝ := ∑ j ∈ S, v j ^ β
  have hV : 0 < V := Finset.sum_pos (fun j _ => hv j) hS
  have hB : 0 < B := Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hv j) _) hS
  have hVa : 0 < V + v a := add_pos hV (hv a)
  have hbound : B * v a ≤ V * v a ^ β := by
    dsimp [B, V]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjval : j.val < i := by simpa [S, A, RetailVariety.Structure.popularSet] using hj
    have haj : v a ≤ v j := hanti (show j ≤ a by exact hjval.le)
    have hr : 1 ≤ v j / v a := (one_le_div (hv a)).mpr haj
    have hrp := Real.rpow_le_self_of_one_le hr hβ1.le
    rw [Real.div_rpow (hv j).le (hv a).le] at hrp
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos (hv a) β)).mp hrp
    have hh' := mul_le_mul_of_nonneg_right hh (hv a).le
    have heq : (v j / v a * v a ^ β) * v a = v j * v a ^ β := by
      field_simp [(hv a).ne']
    rw [heq] at hh'
    exact hh'
  constructor
  · have hcont (R : Finset (Fin n)) (hR : 0 < ∑ j ∈ R, v j) :
        Tendsto (fun v0 : ℝ => ∑ j ∈ R, RetailVariety.Structure.share v v0 R j ^ β)
          (𝓝[>] 0) (𝓝 (∑ j ∈ R, (v j / ∑ k ∈ R, v k) ^ β)) := by
      apply tendsto_finsetSum
      intro j hj
      have hc : ContinuousAt (fun v0 : ℝ => RetailVariety.Structure.share v v0 R j) 0 := by
        unfold RetailVariety.Structure.share
        apply ContinuousAt.div continuousAt_const
        · fun_prop
        · simpa using hR.ne'
      have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [RetailVariety.Structure.share] using ht.rpow_const (Or.inr hβ0)
    apply (hcont _ (by rw [hnext, Finset.sum_insert han]; simpa [V, add_comm] using hVa)).sub (hcont S hV)
  · rw [hnext]
    have hsum (R : Finset (Fin n)) (hR : 0 ≤ ∑ k ∈ R, v k) :
        (∑ j ∈ R, (v j / ∑ k ∈ R, v k) ^ β) = (∑ j ∈ R, v j ^ β) / (∑ k ∈ R, v k) ^ β := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      exact Real.div_rpow (hv j).le hR β
    rw [hsum _ (by rw [Finset.sum_insert han]; simpa [V, add_comm] using hVa.le),
      hsum S hV.le, Finset.sum_insert han, Finset.sum_insert han]
    change 0 < (v a ^ β + B) / (v a + V) ^ β - B / V ^ β
    have := power_add_gain V (v a) B β hV (hv a) hB hβ1 hbound
    simpa [add_comm, sub_pos] using this

#print axioms solution
