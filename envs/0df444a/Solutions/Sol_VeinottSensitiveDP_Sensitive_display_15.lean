-- Prove2me | solution 1 for VeinottSensitiveDP.Sensitive.display_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:26:12.331574+00:00
-- url     : https://prove2.me/submissions/9cee1ace-c04a-4bbe-89aa-70a8654737db

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace VeinottD15Aux
open VeinottSensitiveDP.Sensitive

section Sub
variable {n : Type} [Fintype n] [DecidableEq n]

instance sbs_fc : FirstCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (FirstCountableTopology (n → n → ℝ))

lemma sbs_mul {A B : Matrix n n ℝ} (hA : IsSubstochastic A) (hB : IsSubstochastic B) :
    IsSubstochastic (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc ∑ k, A i k * ∑ j, B k j ≤ ∑ k, A i k * 1 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hB.2 k) (hA.1 i k)
      _ ≤ 1 := by simpa using hA.2 i

lemma sbs_one : IsSubstochastic (1 : Matrix n n ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma sbs_pow {P : Matrix n n ℝ} (hP : IsSubstochastic P) (k : ℕ) : IsSubstochastic (P ^ k) := by
  induction k with
  | zero => simpa using (sbs_one (n := n))
  | succ k ih => rw [pow_succ]; exact sbs_mul ih hP

lemma sbs_le_one {P : Matrix n n ℝ} (hP : IsSubstochastic P) (i j : n) : P i j ≤ 1 :=
  (Finset.single_le_sum (f := fun j => P i j) (fun j _ => hP.1 i j) (Finset.mem_univ j)).trans
    (hP.2 i)

lemma sbs_cesaro {P : Matrix n n ℝ} (hP : IsSubstochastic P) (N : ℕ) (i j : n) :
    0 ≤ cesaroMean P N i j ∧ cesaroMean P N i j ≤ 1 := by
  unfold cesaroMean
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (sbs_pow hP k).1 i j), ?_⟩
  have h : ∑ k ∈ Finset.range (N + 1), (P ^ k) i j ≤ ((N : ℝ) + 1) := by
    calc ∑ k ∈ Finset.range (N + 1), (P ^ k) i j ≤ ∑ k ∈ Finset.range (N + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => sbs_le_one (sbs_pow hP k) i j
      _ = (N : ℝ) + 1 := by simp
  rw [inv_mul_le_iff₀ (by positivity)]; linarith

lemma sbs_P_mul_sum (P : Matrix n n ℝ) (N : ℕ) :
    P * ∑ k ∈ Finset.range (N + 1), P ^ k = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ']
    abel

lemma sbs_sum_mul_P (P : Matrix n n ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), P ^ k) * P = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, ← pow_succ]
    abel

lemma sbs_P_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, sbs_P_mul_sum, smul_add]
  abel

lemma sbs_cesaro_P (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, sbs_sum_mul_P, smul_add]
  abel

lemma sbs_D_tendsto {P : Matrix n n ℝ} (hP : IsSubstochastic P) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hb : ∀ N : ℕ, ‖(((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) i j‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Real.norm_eq_abs]
    have h1 := (sbs_pow hP (N + 1)).1 i j
    have h2 := sbs_le_one (sbs_pow hP (N + 1)) i j
    have h3 : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := sbs_one.1 i j
    have h4 : (1 : Matrix n n ℝ) i j ≤ 1 := sbs_le_one sbs_one i j
    rw [abs_mul, abs_of_pos (by positivity), one_div]
    have : |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ((N : ℝ) + 1)⁻¹ * |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ ((N : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  exact squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat

lemma sbs_clus {P : Matrix n n ℝ} (hP : IsSubstochastic P) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {L : Matrix n n ℝ}
    (hL : Tendsto (fun j => cesaroMean P (ns j)) atTop (𝓝 L)) : P * L = L ∧ L * P = L := by
  have hD := (sbs_D_tendsto hP).comp hns
  constructor
  · have h1 : Tendsto (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) atTop
        (𝓝 (P * L - L)) := (hL.const_mul P).sub hL
    have h2 : (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact sbs_P_cesaro P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)
  · have h1 : Tendsto (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) atTop
        (𝓝 (L * P - L)) := (hL.mul_const P).sub hL
    have h2 : (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact sbs_cesaro_P P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)

lemma sbs_avg_const (L : Matrix n n ℝ) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), L = L := by
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma sbs_cesaro_mul_fix {P L : Matrix n n ℝ} (h : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [hk]
  exact sbs_avg_const L N

lemma sbs_fix_mul_cesaro {P L : Matrix n n ℝ} (h : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [hk]
  exact sbs_avg_const L N

lemma sbs_compact : IsCompact {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} := by
  have e : {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : n) => Set.pi Set.univ (fun (_ : n) => Set.Icc (0 : ℝ) 1)) := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi (fun (_ : n) => isCompact_univ_pi (fun (_ : n) => isCompact_Icc))

theorem sbs_tendsto {P : Matrix n n ℝ} (hP : IsSubstochastic P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) := by
  have hmem : ∀ N, cesaroMean P N ∈ {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} :=
    fun N i j => ⟨(sbs_cesaro hP N i j).1, (sbs_cesaro hP N i j).2⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := sbs_compact.tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hPL, hLP⟩ := sbs_clus hP hφt hL
  have main : Tendsto (cesaroMean P) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL'⟩ := sbs_compact.tendsto_subseq (fun j => hmem (ns j))
    refine ⟨ψ, ?_⟩
    have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨hPL', hL'P⟩ := sbs_clus hP hnsψ hL'
    have e1 : L * L' = L' := by
      have t : Tendsto (fun j => cesaroMean P (φ j) * L') atTop (𝓝 (L * L')) := hL.mul_const L'
      simp_rw [sbs_cesaro_mul_fix hPL'] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have e2 : L * L' = L := by
      have t : Tendsto (fun j => L * cesaroMean P ((ns ∘ ψ) j)) atTop (𝓝 (L * L')) :=
        hL'.const_mul L
      simp_rw [sbs_fix_mul_cesaro hLP] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have : L' = L := e1.symm.trans e2
    rw [this] at hL'
    exact hL'
  rw [limitMatrix, main.limUnder_eq]
  exact main

end Sub
end VeinottD15Aux

open VeinottSensitiveDP.Sensitive VeinottD15Aux in
theorem solution {St : Type} [Fintype St] [DecidableEq St] (P : Matrix St St ℝ)
    (hP : IsSubstochastic P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) ∧
      P * limitMatrix P = limitMatrix P ∧ limitMatrix P * P = limitMatrix P ∧
      limitMatrix P * limitMatrix P = limitMatrix P := by
  have hT := sbs_tendsto hP
  obtain ⟨hPL, hLP⟩ := sbs_clus hP tendsto_id hT
  refine ⟨hT, hPL, hLP, ?_⟩
  have t : Tendsto (fun N => cesaroMean P N * limitMatrix P) atTop
      (𝓝 (limitMatrix P * limitMatrix P)) := hT.mul_const _
  simp_rw [sbs_cesaro_mul_fix hPL] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm
