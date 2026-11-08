-- Prove2me | solution 1 for QueueSignal.lamO_eq_and_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:31:06.474284+00:00
-- url     : https://prove2.me/submissions/4c3b4cff-4d50-43df-9433-11b5738d1589

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

open QueueSignal in
theorem solution (P : Params) (hP : P.Valid) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (∀ lam : ℝ, 0 < lam →
      lamO P lam d = lam * (1 - (lam / P.μ) ^ ((P.naorN d).toNat + 1) /
          ∑ i ∈ Finset.range ((P.naorN d).toNat + 2), (lam / P.μ) ^ i) ∧
      lamO P lam d = P.μ - P.μ / ∑ i ∈ Finset.range ((P.naorN d).toNat + 2), (lam / P.μ) ^ i) ∧
    StrictMonoOn (fun lam => lamO P lam d) (Set.Ioi 0) := by
  have hμ : 0 < P.μ := hP.1
  obtain ⟨m, hm⟩ : ∃ m, m = (P.naorN d).toNat := ⟨_, rfl⟩
  rw [← hm]
  have hS1 : ∀ lam : ℝ, ∑ i ∈ Finset.range (m + 2), (lam / P.μ) ^ i =
      ∑ i ∈ Finset.range (m + 1), (lam / P.μ) ^ i + (lam / P.μ) ^ (m + 1) := fun lam =>
    Finset.sum_range_succ _ _
  have hS2 : ∀ lam : ℝ, ∑ i ∈ Finset.range (m + 2), (lam / P.μ) ^ i =
      (lam / P.μ) * ∑ i ∈ Finset.range (m + 1), (lam / P.μ) ^ i + 1 := by
    intro lam
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hSpos : ∀ lam : ℝ, 0 < lam → 0 < ∑ i ∈ Finset.range (m + 2), (lam / P.μ) ^ i := by
    intro lam hl
    rw [hS2]
    have : 0 ≤ (lam / P.μ) * ∑ i ∈ Finset.range (m + 1), (lam / P.μ) ^ i :=
      mul_nonneg (div_nonneg hl.le hμ.le)
        (Finset.sum_nonneg fun i _ => pow_nonneg (div_nonneg hl.le hμ.le) _)
    linarith
  have hb : ∀ lam : ℝ, 0 < lam →
      lamO P lam d = P.μ - P.μ / ∑ i ∈ Finset.range (m + 2), (lam / P.μ) ^ i := by
    intro lam hl
    have hSpos' := hSpos lam hl
    unfold lamO
    rw [← hm]
    obtain ⟨T, hT⟩ : ∃ T, T = ∑ i ∈ Finset.range (m + 1), (lam / P.μ) ^ i := ⟨_, rfl⟩
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ i ∈ Finset.range (m + 2), (lam / P.μ) ^ i := ⟨_, rfl⟩
    have hS2' : S = (lam / P.μ) * T + 1 := by rw [hS, hT]; exact hS2 lam
    have hSne : S ≠ 0 := by rw [hS]; exact hSpos'.ne'
    rw [← hT, ← hS]
    have key : P.μ * (lam / P.μ) = lam := by field_simp
    rw [div_eq_iff hSne, sub_mul, div_mul_cancel₀ _ hSne, hS2']
    linear_combination (-T) * key
  refine ⟨fun lam hl => ⟨?_, hb lam hl⟩, ?_⟩
  · have hSne := (hSpos lam hl).ne'
    unfold lamO
    rw [← hm, one_sub_div hSne, hS1 lam, add_sub_cancel_right, mul_div_assoc]
  · intro l1 hl1 l2 hl2 hlt
    simp only
    rw [hb l1 hl1, hb l2 hl2]
    have h1 := hSpos l1 hl1
    have hlt' : ∑ i ∈ Finset.range (m + 2), (l1 / P.μ) ^ i <
        ∑ i ∈ Finset.range (m + 2), (l2 / P.μ) ^ i := by
      apply Finset.sum_lt_sum
      · intro i _
        exact pow_le_pow_left₀ (div_nonneg (le_of_lt hl1) hμ.le)
          (div_le_div_of_nonneg_right hlt.le hμ.le) i
      · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
        rw [pow_one, pow_one]
        exact div_lt_div_of_pos_right hlt hμ
    have := div_lt_div_of_pos_left hμ h1 hlt'
    linarith
