-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T01:47:10.694299+00:00
-- url     : https://prove2.me/submissions/a4054b07-ba97-4629-bc7a-7e1670ece5ee

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity

namespace Aux_majlb

open QAlgorithms QuantumLTF.Membership.Supplement
open scoped ComplexConjugate

/-! ### Part 1: Elementary Real & Harmonic Inequalities -/

lemma harmonic_ge_log_succ (m : ℕ) :
    Real.log ((m + 1 : ℕ) : ℝ) ≤ ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 m)]
    have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hlog : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div (by positivity) hm1.ne']
      have hdiv : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) =
          1 + (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      rw [hdiv]
      have hle := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((m + 1 : ℕ) : ℝ))
      linarith
    linarith

lemma harmonic_ge_one {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) ≤ ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
  have hmem : 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
  calc
    (1 : ℝ) = (1 : ℝ) / (1 : ℕ) := by norm_num
    _ ≤ ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s :=
      Finset.single_le_sum (f := fun s : ℕ => (1 : ℝ) / s) (fun _ _ => by positivity) hmem

lemma inv_sqrt_sum_le (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, (1 : ℝ) / Real.sqrt j ≤ 2 * Real.sqrt i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 i)]
    have hstep : (1 : ℝ) / Real.sqrt (i + 1 : ℕ) ≤
        2 * Real.sqrt (i + 1 : ℕ) - 2 * Real.sqrt i := by
      have h1 : (0 : ℝ) < Real.sqrt (i + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
      have h0 : (0 : ℝ) ≤ Real.sqrt i := Real.sqrt_nonneg _
      have hle : Real.sqrt i ≤ Real.sqrt (i + 1 : ℕ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ i)
      have hsq1 : Real.sqrt (i + 1 : ℕ) ^ 2 = (i : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hsq0 : Real.sqrt i ^ 2 = (i : ℝ) := Real.sq_sqrt (by positivity)
      rw [div_le_iff₀ h1]
      nlinarith only [h1, h0, hle, hsq1, hsq0]
    linarith

lemma inv_sqrt_cube_step {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt (m + 1 : ℕ)) ≤
      2 / Real.sqrt m - 2 / Real.sqrt (m + 1 : ℕ) := by
  set s0 : ℝ := Real.sqrt m
  set s1 : ℝ := Real.sqrt (m + 1 : ℕ)
  have hs0 : 0 < s0 := Real.sqrt_pos.mpr (by positivity)
  have hs1 : 0 < s1 := Real.sqrt_pos.mpr (by positivity)
  have hle : s0 ≤ s1 := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)
  have hsq0 : s0 ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
  have hsq1 : s1 ^ 2 = ((m + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hdiff : s1 ^ 2 - s0 ^ 2 = 1 := by rw [hsq0, hsq1]; push_cast; ring
  have hmul : s0 * (s1 + s0) ≤ 2 * s1 ^ 2 * (s1 - s0) * (s1 + s0) := by
    have h1 : s0 * (s1 + s0) ≤ 2 * s1 ^ 2 := by nlinarith only [hs0, hs1, hle]
    have h2 : 2 * s1 ^ 2 * (s1 - s0) * (s1 + s0) = 2 * s1 ^ 2 := by
      calc 2 * s1 ^ 2 * (s1 - s0) * (s1 + s0) = 2 * s1 ^ 2 * (s1 ^ 2 - s0 ^ 2) := by ring
        _ = 2 * s1 ^ 2 := by rw [hdiff, mul_one]
    linarith
  have hkey : s0 ≤ 2 * s1 ^ 2 * (s1 - s0) := by nlinarith only [hs0, hs1, hmul]
  rw [← hsq1, div_sub_div _ _ hs0.ne' hs1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hs0, hs1, hkey]

lemma inv_sqrt_cube_sum_le_sub (i N : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    ∑ j ∈ Finset.Icc (i + 1) N, (1 : ℝ) / ((j : ℝ) * Real.sqrt j) ≤
      2 / Real.sqrt i - 2 / Real.sqrt N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases eq_or_lt_of_le hiN with h_eq | hlt
    · rw [← h_eq]
      have hempty : Finset.Icc (i + 1) i = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
      linarith
    · have hiN' : i ≤ N := by omega
      have hN1 : 1 ≤ N := by omega
      rw [Finset.sum_Icc_succ_top (by omega : i + 1 ≤ N + 1)]
      have hstep := inv_sqrt_cube_step hN1
      have ih' := ih hiN'
      linarith

lemma weighted_harmonic_sum_bound (i N : ℕ) (hi : 1 ≤ i) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) ≤
      4 / Real.sqrt i := by
  have hsplit : Finset.Icc 1 N =
      (Finset.Icc 1 (min N i)) ∪ (Finset.Icc (i + 1) N) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (min N i)) (Finset.Icc (i + 1) N) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_Icc] at hj1 hj2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hpart1 : ∑ j ∈ Finset.Icc 1 (min N i),
      (1 : ℝ) / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) ≤ 2 / Real.sqrt i := by
    have hsub : ∑ j ∈ Finset.Icc 1 (min N i), (1 : ℝ) / Real.sqrt j ≤
        ∑ j ∈ Finset.Icc 1 i, (1 : ℝ) / Real.sqrt j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (min_le_right N i))
        (fun _ _ _ => by positivity)
    calc ∑ j ∈ Finset.Icc 1 (min N i), (1 : ℝ) / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j)
        ≤ ∑ j ∈ Finset.Icc 1 (min N i), (1 : ℝ) / ((i : ℝ) * Real.sqrt j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_Icc] at hj
          have hj1 : 1 ≤ j := hj.1
          have hpos : (0 : ℝ) < (i : ℝ) * Real.sqrt j := by positivity
          have hle : (i : ℝ) * Real.sqrt j ≤ ((i + j - 1 : ℕ) : ℝ) * Real.sqrt j := by
            gcongr
            exact_mod_cast (by omega : i ≤ i + j - 1)
          exact one_div_le_one_div_of_le hpos hle
      _ = (1 / (i : ℝ)) * ∑ j ∈ Finset.Icc 1 (min N i), (1 : ℝ) / Real.sqrt j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ (1 / (i : ℝ)) * ∑ j ∈ Finset.Icc 1 i, (1 : ℝ) / Real.sqrt j :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ ≤ (1 / (i : ℝ)) * (2 * Real.sqrt i) := by
          gcongr
          exact inv_sqrt_sum_le i
      _ = 2 / Real.sqrt i := by
          have hs : 0 < Real.sqrt i := Real.sqrt_pos.mpr (by positivity)
          have hsq : Real.sqrt i ^ 2 = (i : ℝ) := Real.sq_sqrt (by positivity)
          field_simp
          linarith [hsq]
  have hpart2 : ∑ j ∈ Finset.Icc (i + 1) N,
      (1 : ℝ) / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) ≤ 2 / Real.sqrt i := by
    by_cases hNi : i ≤ N
    · calc ∑ j ∈ Finset.Icc (i + 1) N, (1 : ℝ) / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j)
          ≤ ∑ j ∈ Finset.Icc (i + 1) N, (1 : ℝ) / ((j : ℝ) * Real.sqrt j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            simp only [Finset.mem_Icc] at hj
            have hj1 : 1 ≤ j := by omega
            have hpos : (0 : ℝ) < (j : ℝ) * Real.sqrt j := by positivity
            have hle : (j : ℝ) * Real.sqrt j ≤ ((i + j - 1 : ℕ) : ℝ) * Real.sqrt j := by
              gcongr
              exact_mod_cast (by omega : j ≤ i + j - 1)
            exact one_div_le_one_div_of_le hpos hle
        _ ≤ 2 / Real.sqrt i - 2 / Real.sqrt N := inv_sqrt_cube_sum_le_sub i N hi hNi
        _ ≤ 2 / Real.sqrt i := by linarith [show (0 : ℝ) ≤ 2 / Real.sqrt N by positivity]
    · have hempty : Finset.Icc (i + 1) N = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
      positivity
  calc
    ∑ j ∈ Finset.Icc 1 (min N i), (1 : ℝ) / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) +
      ∑ j ∈ Finset.Icc (i + 1) N, (1 : ℝ) / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j)
      ≤ 2 / Real.sqrt i + 2 / Real.sqrt i := add_le_add hpart1 hpart2
    _ = 4 / Real.sqrt i := by ring

lemma inner_final_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψA ψB : EuclideanSpace ℂ ι) (hA : ‖ψA‖ = 1) (hB : ‖ψB‖ = 1)
    (EA EB : ι → Prop) [DecidablePred EA] [DecidablePred EB]
    (hdisj : ∀ z, ¬ (EA z ∧ EB z))
    (hpA : probEvent ψA EA ≥ 2 / 3) (hpB : probEvent ψB EB ≥ 2 / 3) :
    ‖inner ℂ ψA ψB‖ ≤ (19 / 20 : ℝ) := by
  have hnorm_sq : ∀ φ : EuclideanSpace ℂ ι, ‖φ‖ = 1 → ∑ z : ι, ‖φ z‖ ^ 2 = 1 := by
    intro φ hφ
    have h := EuclideanSpace.norm_sq_eq φ
    rw [hφ, one_pow] at h
    simpa [Real.norm_eq_abs, sq_abs] using h.symm
  have hprob_eq : ∀ (φ : EuclideanSpace ℂ ι) (P : ι → Prop) [DecidablePred P],
      probEvent φ P = ∑ z ∈ Finset.univ.filter P, ‖φ z‖ ^ 2 := by
    intro φ P _
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [prob, ket, EuclideanSpace.inner_single_left]
  set SA : Finset ι := Finset.univ.filter EA
  set SB : Finset ι := Finset.univ.filter EB
  set SR : Finset ι := Finset.univ.filter (fun z => ¬ EA z ∧ ¬ EB z)
  have hSAB : Disjoint SA SB := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    exact hdisj z ⟨(Finset.mem_filter.mp hzA).2, (Finset.mem_filter.mp hzB).2⟩
  have hSAR : Disjoint SA SR := by
    rw [Finset.disjoint_left]
    intro z hzA hzR
    exact (Finset.mem_filter.mp hzR).2.1 (Finset.mem_filter.mp hzA).2
  have hSBR : Disjoint SB SR := by
    rw [Finset.disjoint_left]
    intro z hzB hzR
    exact (Finset.mem_filter.mp hzR).2.2 (Finset.mem_filter.mp hzB).2
  have h_part : SA ∪ SB ∪ SR = Finset.univ := by
    ext z
    simp only [SA, SB, SR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    tauto
  have h_sum_split : ∀ f : ι → ℝ,
      ∑ z : ι, f z = (∑ z ∈ SA, f z) + (∑ z ∈ SB, f z) + (∑ z ∈ SR, f z) := by
    intro f
    rw [← h_part, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hSAR, hSBR⟩),
      Finset.sum_union hSAB]
  set pA := ∑ z ∈ SA, ‖ψA z‖ ^ 2
  set b1 := ∑ z ∈ SB, ‖ψA z‖ ^ 2
  set b2 := ∑ z ∈ SR, ‖ψA z‖ ^ 2
  set a1 := ∑ z ∈ SA, ‖ψB z‖ ^ 2
  set pB := ∑ z ∈ SB, ‖ψB z‖ ^ 2
  set a2 := ∑ z ∈ SR, ‖ψB z‖ ^ 2
  have hpA' : (2 / 3 : ℝ) ≤ pA := by dsimp [pA, SA]; rw [← hprob_eq ψA EA]; exact hpA
  have hpB' : (2 / 3 : ℝ) ≤ pB := by dsimp [pB, SB]; rw [← hprob_eq ψB EB]; exact hpB
  have hsumA : pA + b1 + b2 = 1 := by
    have := hnorm_sq ψA hA
    rw [h_sum_split] at this
    exact this
  have hsumB : a1 + pB + a2 = 1 := by
    have := hnorm_sq ψB hB
    rw [h_sum_split] at this
    exact this
  have ha1 : 0 ≤ a1 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha2 : 0 ≤ a2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb1 : 0 ≤ b1 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb2 : 0 ≤ b2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpA0 : 0 ≤ pA := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpB0 : 0 ≤ pB := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set uA := ∑ z ∈ SA, ‖ψA z‖ * ‖ψB z‖
  set uB := ∑ z ∈ SB, ‖ψA z‖ * ‖ψB z‖
  set uR := ∑ z ∈ SR, ‖ψA z‖ * ‖ψB z‖
  have huA0 : 0 ≤ uA := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have huB0 : 0 ≤ uB := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have huR0 : 0 ≤ uR := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcsA : uA ^ 2 ≤ pA * a1 := Finset.sum_mul_sq_le_sq_mul_sq SA (fun z => ‖ψA z‖) (fun z => ‖ψB z‖)
  have hcsB : uB ^ 2 ≤ b1 * pB := Finset.sum_mul_sq_le_sq_mul_sq SB (fun z => ‖ψA z‖) (fun z => ‖ψB z‖)
  have hcsR : uR ^ 2 ≤ b2 * a2 := Finset.sum_mul_sq_le_sq_mul_sq SR (fun z => ‖ψA z‖) (fun z => ‖ψB z‖)
  set s : ℝ := Real.sqrt 2
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs_sq : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs_le : s ≤ 2 := by nlinarith only [hs_pos, hs_sq]
  have h2uA : 2 * uA ≤ pA / s + s * a1 := by
    have hdiff_sq : (pA / s + s * a1) ^ 2 - 4 * (pA * a1) = (pA / s - s * a1) ^ 2 := by
      field_simp; ring
    have hpos_r : 0 ≤ pA / s + s * a1 := by positivity
    nlinarith only [hcsA, hdiff_sq, sq_nonneg (pA / s - s * a1), hpos_r, huA0]
  have h2uB : 2 * uB ≤ s * b1 + pB / s := by
    have hdiff_sq : (s * b1 + pB / s) ^ 2 - 4 * (b1 * pB) = (s * b1 - pB / s) ^ 2 := by
      field_simp; ring
    have hpos_r : 0 ≤ s * b1 + pB / s := by positivity
    nlinarith only [hcsB, hdiff_sq, sq_nonneg (s * b1 - pB / s), hpos_r, huB0]
  have h2uR : 2 * uR ≤ b2 + a2 := by
    nlinarith only [hcsR, sq_nonneg (b2 - a2), hb2, ha2, huR0]
  have hinner_le : ‖inner ℂ ψA ψB‖ ≤ uA + uB + uR := by
    have h_inner_eq : inner ℂ ψA ψB = ∑ z : ι, starRingEnd ℂ (ψA z) * ψB z := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [mul_comm]
    rw [h_inner_eq]
    calc ‖∑ z : ι, starRingEnd ℂ (ψA z) * ψB z‖
        ≤ ∑ z : ι, ‖starRingEnd ℂ (ψA z) * ψB z‖ := norm_sum_le _ _
      _ = ∑ z : ι, ‖ψA z‖ * ‖ψB z‖ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [norm_mul, Complex.norm_conj]
      _ = uA + uB + uR := h_sum_split _
  have hA' : 2 * s * uA ≤ pA + 2 * a1 := by
    have h1 := mul_le_mul_of_nonneg_left h2uA hs_pos.le
    calc 2 * s * uA = s * (2 * uA) := by ring
      _ ≤ s * (pA / s + s * a1) := h1
      _ = pA + s ^ 2 * a1 := by field_simp
      _ = pA + 2 * a1 := by rw [hs_sq]
  have hB' : 2 * s * uB ≤ 2 * b1 + pB := by
    have h1 := mul_le_mul_of_nonneg_left h2uB hs_pos.le
    calc 2 * s * uB = s * (2 * uB) := by ring
      _ ≤ s * (s * b1 + pB / s) := h1
      _ = s ^ 2 * b1 + pB := by field_simp
      _ = 2 * b1 + pB := by rw [hs_sq]
  have hR' : 2 * s * uR ≤ 2 * (b2 + a2) := by
    have h1 := mul_le_mul_of_nonneg_left h2uR hs_pos.le
    nlinarith only [h1, hs_le, hb2, ha2]
  have h_final_s : 2 * s * ‖inner ℂ ψA ψB‖ ≤ 8 / 3 := by
    have h1 := mul_le_mul_of_nonneg_left hinner_le (by positivity : 0 ≤ 2 * s)
    linarith only [h1, hA', hB', hR', hsumA, hsumB, hpA', hpB']
  have h60 : 60 * s * ‖inner ℂ ψA ψB‖ ≤ 80 := by linarith only [h_final_s]
  have hs_57 : (80 : ℝ) ≤ 57 * s := by nlinarith only [hs_pos, hs_sq]
  have h60_57 : 60 * s * ‖inner ℂ ψA ψB‖ ≤ 57 * s := le_trans h60 hs_57
  nlinarith only [h60_57, hs_pos]

/-! ### Part 2: Deterministic Cycle Lemma -/

def isGoodStart (s : ℕ) (z : ℕ → ℤ) (r : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 s, 0 < ∑ j ∈ Finset.range k, z (r + j)

lemma cycle_lemma {s : ℕ} (hs : 1 ≤ s) (z : ℕ → ℤ)
    (hz_per : ∀ i, z (i + s) = z i) (hz_le : ∀ i, z i ≤ 1)
    (hq : 0 < ∑ i ∈ Finset.range s, z i) :
    letI := Classical.decPred (isGoodStart s z)
    ((Finset.range s).filter (isGoodStart s z)).card =
      (∑ i ∈ Finset.range s, z i).toNat := by
  classical
  set q : ℤ := ∑ i ∈ Finset.range s, z i
  let P : ℕ → ℤ := fun i => ∑ j ∈ Finset.range i, z j
  have hP_succ : ∀ i, P (i + 1) = P i + z i := fun i => Finset.sum_range_succ z i
  have hP_add : ∀ a b, P (a + b) - P a = ∑ j ∈ Finset.range b, z (a + j) := by
    intro a b
    dsimp [P]
    rw [Finset.sum_range_add]
    ring
  have hP_period : ∀ i, P (i + s) = P i + q := by
    intro i
    induction i with
    | zero => simp [P, q]
    | succ i ih =>
      rw [show i + 1 + s = (i + s) + 1 by omega, hP_succ, hP_succ, ih, hz_per i]
      ring
  have hP_mul : ∀ m i, P (i + m * s) = P i + (m : ℤ) * q := by
    intro m i
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show i + (m + 1) * s = (i + m * s) + s by ring, hP_period, ih]
      push_cast
      ring
  have hS_ne : (Finset.range s).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  set M_set := (Finset.range s).image P
  have hM_ne : M_set.Nonempty := hS_ne.image P
  set M : ℤ := M_set.min' hM_ne
  obtain ⟨i0, hi0_mem, hi0_eq⟩ : ∃ i0 ∈ Finset.range s, P i0 = M := by
    have hmem : M ∈ M_set := Finset.min'_mem M_set hM_ne
    simpa [M_set] using hmem
  have hM_le_range : ∀ i ∈ Finset.range s, M ≤ P i := fun i hi =>
    Finset.min'_le M_set (P i) (Finset.mem_image_of_mem P hi)
  have hM_le_all : ∀ j : ℕ, M ≤ P j := by
    intro j
    have hmod : j % s ∈ Finset.range s := Finset.mem_range.mpr (Nat.mod_lt j (by omega))
    have hdiv : j = j % s + (j / s) * s := by
      have := Nat.div_add_mod j s
      linarith
    rw [hdiv, hP_mul (j / s) (j % s)]
    have h1 := hM_le_range (j % s) hmod
    have h2 : (0 : ℤ) ≤ ((j / s : ℕ) : ℤ) * q := mul_nonneg (by positivity) hq.le
    linarith
  have hgood_iff : ∀ r < s,
      isGoodStart s z r ↔ ∀ j : ℕ, r < j → P r < P j := by
    intro r hr
    constructor
    · intro hgood j hj
      set d := j - r - 1
      have hdm : d % s + (d / s) * s = d := by linarith [Nat.div_add_mod d s]
      have hd : j = (r + (d % s + 1)) + (d / s) * s := by omega
      rw [hd, hP_mul]
      have hk_mem : d % s + 1 ∈ Finset.Icc 1 s :=
        Finset.mem_Icc.mpr ⟨by omega, Nat.lt_of_lt_of_le (Nat.mod_lt d (by omega)) le_rfl⟩
      have hpos := hgood (d % s + 1) hk_mem
      rw [← hP_add] at hpos
      have h2 : (0 : ℤ) ≤ ((d / s : ℕ) : ℤ) * q := mul_nonneg (by positivity) hq.le
      linarith
    · intro hall k hk
      simp only [Finset.mem_Icc] at hk
      rw [← hP_add]
      have := hall (r + k) (by omega)
      linarith
  have hcard_target : (Finset.Ico M (M + q)).card = q.toNat := by
    rw [Int.card_Ico]
    omega
  rw [← hcard_target]
  refine Finset.card_bij (fun r _ => P r) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    have hr_all := (hgood_iff r hr.1).mp hr.2
    simp only [Finset.mem_Ico]
    refine ⟨hM_le_range r (Finset.mem_range.mpr hr.1), ?_⟩
    have hi0_lt : i0 < s := Finset.mem_range.mp hi0_mem
    have hlt := hr_all (i0 + s) (by omega)
    rw [hP_period, hi0_eq] at hlt
    exact hlt
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
    have h1 := (hgood_iff r1 hr1.1).mp hr1.2
    have h2 := (hgood_iff r2 hr2.1).mp hr2.2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd heq (ne_of_lt (h1 r2 hlt))
    · exact absurd heq.symm (ne_of_lt (h2 r1 hlt))
  · intro v hv
    simp only [Finset.mem_Ico] at hv
    set B : ℕ := (v - M).toNat + 1
    have hB_bound : ∀ j : ℕ, B * s ≤ j → v < P j := by
      intro j hj
      have hdiv : j = j % s + (j / s) * s := by
        have := Nat.div_add_mod j s
        linarith
      have hj_div : B ≤ j / s := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        exact hj
      rw [hdiv, hP_mul]
      have hM_mod : M ≤ P (j % s) := hM_le_range (j % s) (Finset.mem_range.mpr (Nat.mod_lt j (by omega)))
      have hq1 : (1 : ℤ) ≤ q := by omega
      have hBq : ((v - M) + 1 : ℤ) ≤ ((j / s : ℕ) : ℤ) * q := by
        have hB1 : ((v - M) + 1 : ℤ) ≤ (B : ℤ) := by
          dsimp [B]; omega
        have hB2 : (B : ℤ) ≤ ((j / s : ℕ) : ℤ) := by exact_mod_cast hj_div
        nlinarith only [hq1, hB1, hB2]
      linarith
    set cand := (Finset.range (B * s)).filter (fun j => P j ≤ v)
    have hcand_ne : cand.Nonempty := by
      refine ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
      · have hi0_lt : i0 < s := Finset.mem_range.mp hi0_mem
        have hB1 : 1 ≤ B := by omega
        nlinarith only [hi0_lt, hB1, hs]
      · rw [hi0_eq]; exact hv.1
    set rv := cand.max' hcand_ne
    have hrv_mem := Finset.max'_mem cand hcand_ne
    simp only [cand, Finset.mem_filter, Finset.mem_range] at hrv_mem
    have hrv_lt_Bs : rv < B * s := hrv_mem.1
    have hP_rv_le : P rv ≤ v := hrv_mem.2
    have hrv_gt : ∀ j : ℕ, rv < j → v < P j := by
      intro j hj
      by_cases hjB : j < B * s
      · by_contra hle
        push Not at hle
        have hmem : j ∈ cand := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjB, hle⟩
        have := Finset.le_max' cand j hmem
        omega
      · exact hB_bound j (by omega)
    have hrv_succ : v < P (rv + 1) := hrv_gt (rv + 1) (by omega)
    have hP_rv_eq : P rv = v := by
      have h1 := hP_succ rv
      have h2 := hz_le rv
      omega
    have hrv_lt_s : rv < s := by
      by_contra hge
      push Not at hge
      have hsub := hP_period (rv - s)
      rw [show rv - s + s = rv by omega, hP_rv_eq] at hsub
      have hM_sub := hM_le_all (rv - s)
      omega
    refine ⟨rv, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrv_lt_s, ?_⟩, hP_rv_eq⟩
    exact (hgood_iff rv hrv_lt_s).mpr fun j hj => by rw [hP_rv_eq]; exact hrv_gt j hj

/-! ### Part 3: Involution Matrices, Circuit Operations & Query Complexity Nonemptiness -/

def invMat {k : ℕ} (f : Qubits k → Qubits k) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun y z => if y = f z then 1 else 0

lemma invMat_star {k : ℕ} (f : Qubits k → Qubits k) (hf : ∀ x, f (f x) = x) :
    star (invMat f) = invMat f := by
  ext y z
  simp only [Matrix.star_apply, invMat, Matrix.of_apply]
  have heq : z = f y ↔ y = f z :=
    ⟨fun h => by rw [h, hf], fun h => by rw [h, hf]⟩
  by_cases h : z = f y
  · have h' := heq.mp h
    rw [if_pos h, if_pos h']
    simp
  · have h' : y ≠ f z := fun h1 => h (heq.mpr h1)
    rw [if_neg h, if_neg h']
    simp

lemma invMat_mul_self {k : ℕ} (f : Qubits k → Qubits k) (hf : ∀ x, f (f x) = x) :
    invMat f * invMat f = 1 := by
  ext y z
  simp only [Matrix.mul_apply, invMat, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (f z)]
  · rcases eq_or_ne y z with rfl | h
    · simp [hf y]
    · have h' : y ≠ f (f z) := by rw [hf z]; exact h
      simp [h, h']
  · intro x _ hx
    simp [hx]
  · simp

lemma invMat_mem_unitaryGroup {k : ℕ} (f : Qubits k → Qubits k) (hf : ∀ x, f (f x) = x) :
    invMat f ∈ Matrix.unitaryGroup (Qubits k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [invMat_star f hf]
  exact invMat_mul_self f hf

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y
  simp [act, Matrix.mulVec_mulVec]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext y
  simp [act]

lemma act_invMat {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι) (hf : ∀ x, f (f x) = x)
    (ψ : EuclideanSpace ℂ ι) (y : ι) :
    act (Matrix.of fun a b => if a = f b then (1 : ℂ) else 0) ψ y = ψ (f y) := by
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (f y)]
  · simp [hf y]
  · intro x _ hx
    have hne : y ≠ f x := fun h => hx (by rw [h, hf x])
    simp [hne]
  · simp

lemma act_embedOp_invMat {k m : ℕ} (f : Qubits k → Qubits k)
    (w : Fin k ↪ Fin m) (z : Qubits m) :
    act (embedOp (invMat f) w) (ket z) =
      ket (fun a => if h : ∃ b, w b = a then f (z ∘ w) (Classical.choose h) else z a) := by
  ext y
  have hact : (act (embedOp (invMat f) w) (ket z)) y = embedOp (invMat f) w y z := by
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single z]
    · simp [ket]
    · intro x _ hx; simp [ket, hx]
    · simp
  rw [hact]
  set z' : Qubits m := fun a => if h : ∃ b, w b = a then f (z ∘ w) (Classical.choose h) else z a
  have hiff : ((∀ a ∉ Set.range w, y a = z a) ∧ y ∘ w = f (z ∘ w)) ↔ y = z' := by
    constructor
    · rintro ⟨h1, h2⟩
      funext a
      by_cases ha : ∃ b, w b = a
      · obtain ⟨b, hb⟩ := ha
        have hch : Classical.choose (⟨b, hb⟩ : ∃ b, w b = a) = b :=
          w.injective (Classical.choose_spec (⟨b, hb⟩ : ∃ b, w b = a) |>.trans hb.symm)
        have hya : y a = f (z ∘ w) b := by rw [← hb]; exact congrFun h2 b
        dsimp [z']
        rw [dif_pos ⟨b, hb⟩, hch, hya]
      · dsimp [z']
        rw [dif_neg ha]
        exact h1 a (by simpa [Set.mem_range] using ha)
    · intro hy
      subst hy
      refine ⟨fun a ha => ?_, ?_⟩
      · have hna : ¬ ∃ b, w b = a := by simpa [Set.mem_range] using ha
        dsimp [z']
        rw [dif_neg hna]
      · funext b
        have ha : ∃ b', w b' = w b := ⟨b, rfl⟩
        have hch : Classical.choose ha = b := w.injective (Classical.choose_spec ha)
        dsimp [z']
        rw [dif_pos ha, hch]
  simp only [embedOp, Matrix.of_apply, invMat, ket, PiLp.single_apply]
  by_cases hyz' : y = z'
  · have h12 := hiff.mpr hyz'
    rw [if_pos h12.1, if_pos h12.2, if_pos hyz']
  · rw [if_neg hyz']
    split_ifs with h1 h2
    · exfalso; exact hyz' (hiff.mp ⟨h1, h2⟩)
    · rfl
    · rfl

def majToggle {n : ℕ} (A : Finset (Fin n)) (z : Qubits (n + 1)) : Qubits (n + 1) :=
  Fin.snoc (Fin.init z)
    (xor (z (Fin.last n)) (decide (majJunta A (Finset.univ.filter fun i => Fin.init z i = true) = -1)))

lemma majToggle_invol {n : ℕ} (A : Finset (Fin n)) (z : Qubits (n + 1)) :
    majToggle A (majToggle A z) = z := by
  dsimp only [majToggle]
  rw [Fin.init_snoc, Fin.snoc_last, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  exact Fin.snoc_init_self z

lemma majOracle_eq_invMat {n : ℕ} (A : Finset (Fin n)) :
    majOracle A = invMat (majToggle A) := rfl

lemma majOracle_star {n : ℕ} (A : Finset (Fin n)) : star (majOracle A) = majOracle A := by
  rw [majOracle_eq_invMat]
  exact invMat_star (majToggle A) (majToggle_invol A)

lemma majOracle_mem_unitaryGroup {n : ℕ} (A : Finset (Fin n)) :
    majOracle A ∈ Matrix.unitaryGroup (Qubits (n + 1)) ℂ := by
  rw [majOracle_eq_invMat]
  exact invMat_mem_unitaryGroup (majToggle A) (majToggle_invol A)

lemma majJunta_eq_subset {n : ℕ} {A B : Finset (Fin n)} (hA : A.Nonempty)
    (h : ∀ S : Finset (Fin n), majJunta A S = majJunta B S) : A ⊆ B := by
  intro a ha
  have hcard1 : 1 ≤ A.card := Finset.Nonempty.card_pos hA
  set t : ℕ := (A.card + 1) / 2 - 1
  have ht_le : t ≤ (A.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq ht_le
  set S : Finset (Fin n) := insert a S'
  have haS' : a ∉ S' := fun hmem => (Finset.mem_erase.mp (hS'sub hmem)).1 rfl
  have hS_sub : S ⊆ A := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact ha
    · exact Finset.erase_subset a A (hS'sub hx')
  have hS_card : S.card = (A.card + 1) / 2 := by
    simp only [S, Finset.card_insert_eq_ite, if_neg haS', hS'card]
    omega
  have hmajA_S : majJunta A S = 1 := by
    simp only [majJunta, Finset.inter_eq_right.mpr hS_sub, hS_card]
    rw [if_pos (by omega)]
  have hmajA_S' : majJunta A S' = -1 := by
    have hS'subA : S' ⊆ A := hS'sub.trans (Finset.erase_subset a A)
    simp only [majJunta, Finset.inter_eq_right.mpr hS'subA, hS'card]
    rw [if_neg (by omega)]
  have hmajB_S : majJunta B S = 1 := by rw [← h S, hmajA_S]
  have hmajB_S' : majJunta B S' = -1 := by rw [← h S', hmajA_S']
  by_contra haB
  have hBS : B ∩ S = B ∩ S' := by
    ext x
    simp only [Finset.mem_inter, S, Finset.mem_insert]
    constructor
    · rintro ⟨hxB, rfl | hx'⟩
      · exact absurd hxB haB
      · exact ⟨hxB, hx'⟩
    · rintro ⟨hxB, hx'⟩
      exact ⟨hxB, Or.inr hx'⟩
  have h_eq : majJunta B S = majJunta B S' := by simp [majJunta, hBS]
  rw [hmajB_S, hmajB_S'] at h_eq
  norm_num at h_eq

lemma majJunta_injective_on_nonempty {n : ℕ} {A B : Finset (Fin n)}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ S : Finset (Fin n), majJunta A S = majJunta B S) : A = B :=
  Finset.Subset.antisymm (majJunta_eq_subset hA h)
    (majJunta_eq_subset hB fun S => (h S).symm)

lemma oracleCircuit_unitary_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c1 c2 : OracleCircuit S a m)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    (c1 ++ c2).unitary orc = c2.unitary orc * c1.unitary orc := by
  simp [OracleCircuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma oracleCircuit_queryCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c1 c2 : OracleCircuit S a m) (k : Fin r) :
    (c1 ++ c2).queryCount k = c1.queryCount k + c2.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

lemma queryComplexity_set_nonempty (n : ℕ) (P : Finset (Fin n) → Prop)
    (hP : ∀ A, P A → A.Nonempty) :
    {T : ℕ | ∃ (m : ℕ) (c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m)
      (out : Fin n ↪ Fin m), c.queryCount 0 ≤ T ∧
      ∀ A : Finset (Fin n), P A →
        open Classical in
        probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
          (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 2 / 3}.Nonempty := by
  classical
  let N : ℕ := 2 ^ n
  let m : ℕ := n + N + n
  let qWire : Fin n → Fin m := fun i => ⟨i.1,
    Nat.lt_of_lt_of_le i.isLt (Nat.le_trans (Nat.le_add_right n N) (Nat.le_add_right (n + N) n))⟩
  let rWire : Fin N → Fin m := fun j => ⟨n + j.1,
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt n) (Nat.le_add_right (n + N) n)⟩
  let outWire : Fin n → Fin m := fun i => ⟨n + N + i.1, Nat.add_lt_add_left i.isLt (n + N)⟩
  let qEmb : Fin n ↪ Fin m :=
    ⟨qWire, fun a b h => Fin.ext (by simpa [qWire, Fin.ext_iff] using h)⟩
  let outEmb : Fin n ↪ Fin m :=
    ⟨outWire, fun a b h => Fin.ext (by simpa [outWire, Fin.ext_iff] using h)⟩
  let oracleWires (j : Fin N) : Fin (n + 1) ↪ Fin m :=
    ⟨Fin.lastCases (rWire j) qWire, by
      intro a b
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => intro _; rfl
        | cast b' =>
          intro h
          exfalso
          have hval := congrArg Fin.val h
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc, rWire, qWire] at hval
          have hb := b'.isLt
          omega
      | cast a' =>
        induction b using Fin.lastCases with
        | last =>
          intro h
          exfalso
          have hval := congrArg Fin.val h
          simp only [Fin.lastCases_castSucc, Fin.lastCases_last, qWire, rWire] at hval
          have ha := a'.isLt
          omega
        | cast b' =>
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.lastCases_castSucc, qWire] at hval
          exact congrArg Fin.castSucc (Fin.ext hval)⟩
  let truthTable (A : Finset (Fin n)) : Qubits N := fun j =>
    decide (majJunta A (Finset.univ.filter fun i => ((bitsEquivFin n).symm j) i = true) = -1)
  have hTT_inj : ∀ A B : Finset (Fin n), A.Nonempty → B.Nonempty →
      truthTable A = truthTable B → A = B := by
    intro A B hA hB hTT
    refine majJunta_injective_on_nonempty hA hB fun S => ?_
    let s : Qubits n := fun i => decide (i ∈ S)
    let j : Fin N := bitsEquivFin n s
    have hsj : (bitsEquivFin n).symm j = s := (bitsEquivFin n).symm_apply_apply s
    have hS_eq : (Finset.univ.filter fun i => ((bitsEquivFin n).symm j) i = true) = S := by
      ext i
      simp [hsj, s]
    have hj_eq := congrFun hTT j
    dsimp [truthTable] at hj_eq
    rw [hS_eq] at hj_eq
    rcases (show majJunta A S = 1 ∨ majJunta A S = -1 by unfold majJunta; split_ifs <;> simp) with h1 | h1 <;>
    rcases (show majJunta B S = 1 ∨ majJunta B S = -1 by unfold majJunta; split_ifs <;> simp) with h2 | h2 <;>
    simp_all
  let decode : Qubits N → Qubits n := fun tbl =>
    if h : ∃ A : Finset (Fin n), A.Nonempty ∧ truthTable A = tbl then
      fun i => decide (i ∈ Classical.choose h)
    else fun _ => false
  have hdecode : ∀ A : Finset (Fin n), A.Nonempty →
      decode (truthTable A) = fun i => decide (i ∈ A) := by
    intro A hA
    have hex : ∃ A' : Finset (Fin n), A'.Nonempty ∧ truthTable A' = truthTable A := ⟨A, hA, rfl⟩
    dsimp [decode]
    rw [dif_pos hex]
    have hspec := Classical.choose_spec hex
    have hEq := hTT_inj (Classical.choose hex) A hspec.1 hA hspec.2
    rw [hEq]
  let bitFlipFun (s : Qubits n) : Qubits n → Qubits n := fun z i => xor (z i) (s i)
  have hbitFlip_invol : ∀ s x, bitFlipFun s (bitFlipFun s x) = x := by
    intro s x; funext i; simp [bitFlipFun]
  let bitFlipGate (s : Qubits n) : Gate := ⟨n, invMat (bitFlipFun s)⟩
  let decodeFun : Qubits m → Qubits m := fun z a =>
    if h : n + N ≤ a.1 then
      xor (z a) (decode (fun j => z (rWire j)) ⟨a.1 - (n + N), by
        have ha := a.isLt
        change a.1 < n + N + n at ha
        omega⟩)
    else z a
  have hdecode_invol : ∀ z, decodeFun (decodeFun z) = z := by
    intro z
    have hrec : ∀ j : Fin N, decodeFun z (rWire j) = z (rWire j) := by
      intro j
      have hj : ¬ (n + N ≤ (rWire j).1) := by dsimp [rWire]; omega
      simp [decodeFun, hj]
    funext a
    by_cases ha : n + N ≤ a.1
    · have htbl : (fun j => decodeFun z (rWire j)) = (fun j => z (rWire j)) := funext hrec
      simp [decodeFun, ha, htbl]
    · simp [decodeFun, ha]
  let decodeGate : Gate := ⟨m, invMat decodeFun⟩
  let stepAt (j : Fin N) : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m :=
    let s := (bitsEquivFin n).symm j
    [ .gate ⟨bitFlipGate s, invMat_mem_unitaryGroup (bitFlipFun s) (hbitFlip_invol s), qEmb⟩
    , .query 0 false none (oracleWires j) (fun _ h => by simp at h)
    , .gate ⟨bitFlipGate s, invMat_mem_unitaryGroup (bitFlipFun s) (hbitFlip_invol s), qEmb⟩ ]
  let loopCirc (l : List (Fin N)) : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m :=
    l.flatMap stepAt
  let decStep : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m :=
    .gate ⟨decodeGate, invMat_mem_unitaryGroup decodeFun hdecode_invol, Function.Embedding.refl _⟩
  let fullCirc : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m :=
    loopCirc (List.finRange N) ++ [decStep]
  have hloop_q : ∀ l : List (Fin N), (loopCirc l).queryCount 0 = l.length := by
    intro l
    induction l with
    | nil => simp [loopCirc, OracleCircuit.queryCount]
    | cons j l ih =>
      simp only [loopCirc, List.flatMap_cons] at ih ⊢
      rw [oracleCircuit_queryCount_append, ih]
      have hstep_q : (stepAt j).queryCount 0 = 1 := by
        simp [stepAt, OracleCircuit.queryCount, OracleStep.IsQueryTo]
      rw [hstep_q, List.length_cons]
      omega
  have hfull_q : fullCirc.queryCount 0 = N := by
    dsimp [fullCirc]
    rw [oracleCircuit_queryCount_append, hloop_q, List.length_finRange]
    simp [decStep, OracleCircuit.queryCount, OracleStep.IsQueryTo]
  have hstep_act : ∀ (A : Finset (Fin n)) (j : Fin N) (z : Qubits m),
      (∀ i : Fin n, z (qWire i) = false) → z (rWire j) = false →
      act ((stepAt j).unitary fun _ => majOracle A) (ket z) =
        ket (fun a => if a = rWire j then truthTable A j else z a) := by
    intro A j z hzq hzr
    let s := (bitsEquivFin n).symm j
    have hstep_u : (stepAt j).unitary (fun _ => majOracle A) =
        embedOp (invMat (bitFlipFun s)) qEmb *
          (embedOp (majOracle A) (oracleWires j) * embedOp (invMat (bitFlipFun s)) qEmb) := by
      dsimp [stepAt, s]
      simp [OracleCircuit.unitary, OracleStep.mat, bitFlipGate]
    rw [hstep_u, act_mul, act_mul]
    have h1 := act_embedOp_invMat (bitFlipFun s) qEmb z
    set z1 : Qubits m := fun a =>
      if h : ∃ b, qEmb b = a then bitFlipFun s (z ∘ qEmb) (Classical.choose h) else z a
    have hz1_q : ∀ i : Fin n, z1 (qWire i) = s i := by
      intro i
      have hex : ∃ b, qEmb b = qWire i := ⟨i, rfl⟩
      have hch : Classical.choose hex = i := qEmb.injective (Classical.choose_spec hex)
      dsimp [z1]
      rw [dif_pos hex, hch]
      change xor (z (qWire i)) (s i) = s i
      rw [hzq i, Bool.false_xor]
    have hz1_r : ∀ j' : Fin N, z1 (rWire j') = z (rWire j') := by
      intro j'
      have hnex : ¬ ∃ b, qEmb b = rWire j' := by
        rintro ⟨b, hb⟩
        have hval : (qWire b).1 = (rWire j').1 := congrArg Fin.val hb
        dsimp [qWire, rWire] at hval
        have hlt : b.1 < n := b.isLt
        omega
      dsimp [z1]; rw [dif_neg hnex]
    rw [h1, majOracle_eq_invMat]
    have h2 := act_embedOp_invMat (majToggle A) (oracleWires j) z1
    set z2 : Qubits m := fun a =>
      if h : ∃ b, oracleWires j b = a then majToggle A (z1 ∘ oracleWires j) (Classical.choose h) else z1 a
    have hor_cast : ∀ i : Fin n, oracleWires j (Fin.castSucc i) = qWire i := by
      intro i
      change Fin.lastCases (rWire j) qWire (Fin.castSucc i) = qWire i
      exact Fin.lastCases_castSucc i
    have hor_last : oracleWires j (Fin.last n) = rWire j := by
      change Fin.lastCases (rWire j) qWire (Fin.last n) = rWire j
      exact Fin.lastCases_last
    have hz2_q : ∀ i : Fin n, z2 (qWire i) = s i := by
      intro i
      have hex : ∃ b, oracleWires j b = qWire i := ⟨Fin.castSucc i, hor_cast i⟩
      have hch : Classical.choose hex = Fin.castSucc i :=
        (oracleWires j).injective ((Classical.choose_spec hex).trans (hor_cast i).symm)
      dsimp [z2]
      rw [dif_pos hex, hch]
      change majToggle A (z1 ∘ oracleWires j) (Fin.castSucc i) = s i
      dsimp [majToggle]
      rw [Fin.snoc_castSucc]
      change (z1 ∘ oracleWires j) (Fin.castSucc i) = s i
      rw [Function.comp_apply, hor_cast i]
      exact hz1_q i
    have hz2_r : z2 (rWire j) = truthTable A j := by
      have hex : ∃ b, oracleWires j b = rWire j := ⟨Fin.last n, hor_last⟩
      have hch : Classical.choose hex = Fin.last n :=
        (oracleWires j).injective ((Classical.choose_spec hex).trans hor_last.symm)
      dsimp [z2]
      rw [dif_pos hex, hch]
      change majToggle A (z1 ∘ oracleWires j) (Fin.last n) = truthTable A j
      dsimp [majToggle]
      rw [Fin.snoc_last]
      have h_last : (z1 ∘ oracleWires j) (Fin.last n) = false := by
        rw [Function.comp_apply, hor_last, hz1_r, hzr]
      have h_init : Fin.init (z1 ∘ oracleWires j) = s := by
        funext i
        change (z1 ∘ oracleWires j) (Fin.castSucc i) = s i
        rw [Function.comp_apply, hor_cast i]
        exact hz1_q i
      change xor ((z1 ∘ oracleWires j) (Fin.last n))
        (decide (majJunta A (Finset.univ.filter fun i => Fin.init (z1 ∘ oracleWires j) i = true) = -1)) =
        truthTable A j
      rw [h_last, h_init, Bool.false_xor]
    have hz2_other : ∀ a, a ≠ rWire j → (∀ i, a ≠ qWire i) → z2 a = z a := by
      intro a har haq
      have hnex : ¬ ∃ b, oracleWires j b = a := by
        rintro ⟨b, hb⟩
        revert hb
        refine Fin.lastCases ?_ ?_ b
        · intro h
          have h1 : rWire j = a := by
            change Fin.lastCases (rWire j) qWire (Fin.last n) = a at h
            rwa [Fin.lastCases_last] at h
          exact har h1.symm
        · intro i h
          have h1 : qWire i = a := by
            change Fin.lastCases (rWire j) qWire (Fin.castSucc i) = a at h
            rwa [Fin.lastCases_castSucc] at h
          exact haq i h1.symm
      have hnex1 : ¬ ∃ b, qEmb b = a := by rintro ⟨b, hb⟩; exact haq b hb.symm
      dsimp [z2, z1]
      rw [dif_neg hnex, dif_neg hnex1]
    rw [h2]
    have h3 := act_embedOp_invMat (bitFlipFun s) qEmb z2
    rw [h3]
    congr 1
    funext a
    by_cases ha_r : a = rWire j
    · subst ha_r
      have hnex : ¬ ∃ b, qEmb b = rWire j := by
        rintro ⟨b, hb⟩
        have hval : (qWire b).1 = (rWire j).1 := congrArg Fin.val hb
        dsimp [qWire, rWire] at hval
        have hlt : b.1 < n := b.isLt
        omega
      rw [dif_neg hnex, if_pos rfl, hz2_r]
    · rw [if_neg ha_r]
      by_cases ha_q : ∃ i, qEmb i = a
      · obtain ⟨i, rfl⟩ := ha_q
        have hex : ∃ b, qEmb b = qEmb i := ⟨i, rfl⟩
        have hch : Classical.choose hex = i := qEmb.injective (Classical.choose_spec hex)
        have hcomp : z2 ∘ qEmb = s := funext fun i' => hz2_q i'
        rw [dif_pos hex, hch, hcomp]
        dsimp [bitFlipFun]
        rw [Bool.xor_self]
        exact (hzq i).symm
      · have haq' : ∀ i, a ≠ qWire i := fun i h => ha_q ⟨i, h.symm⟩
        rw [dif_neg ha_q]
        exact hz2_other a ha_r haq'
  have hloop_act : ∀ (A : Finset (Fin n)) (l : List (Fin N)) (hl : l.Nodup) (z : Qubits m),
      (∀ i : Fin n, z (qWire i) = false) → (∀ j ∈ l, z (rWire j) = false) →
      act ((loopCirc l).unitary fun _ => majOracle A) (ket z) =
        ket (fun a => if h : ∃ j ∈ l, rWire j = a then truthTable A (Classical.choose h) else z a) := by
    intro A l hl z hzq hzr
    induction l generalizing z with
    | nil =>
      simp only [loopCirc, List.flatMap_nil, OracleCircuit.unitary, List.map_nil, List.reverse_nil,
        List.prod_nil, act_one]
      congr 1
      funext a
      have hnex : ¬ ∃ j ∈ ([] : List (Fin N)), rWire j = a := by simp
      rw [dif_neg hnex]
    | cons j l ih =>
      rw [List.nodup_cons] at hl
      simp only [loopCirc, List.flatMap_cons]
      rw [oracleCircuit_unitary_append, act_mul]
      rw [hstep_act A j z hzq (hzr j (by simp))]
      set z1 : Qubits m := fun a => if a = rWire j then truthTable A j else z a
      have hz1_q : ∀ i : Fin n, z1 (qWire i) = false := by
        intro i
        have hne : qWire i ≠ rWire j := by simp [qWire, rWire, Fin.ext_iff]; omega
        simp [z1, hne, hzq i]
      have hz1_r : ∀ j' ∈ l, z1 (rWire j') = false := by
        intro j' hj'
        have hne : rWire j' ≠ rWire j := by
          intro heq
          have hj_eq : j' = j := Fin.ext (by simpa [rWire, Fin.ext_iff] using heq)
          exact hl.1 (hj_eq ▸ hj')
        simp [z1, hne, hzr j' (by simp [hj'])]
      rw [ih hl.2 z1 hz1_q hz1_r]
      congr 1
      funext a
      by_cases ha : ∃ j' ∈ j :: l, rWire j' = a
      · obtain ⟨j', hj', rfl⟩ := ha
        have hex_c : ∃ k ∈ j :: l, rWire k = rWire j' := ⟨j', hj', rfl⟩
        have hch_c : Classical.choose hex_c = j' :=
          Fin.ext (by simpa [rWire, Fin.ext_iff] using (Classical.choose_spec hex_c).2)
        rw [dif_pos hex_c, hch_c]
        rcases List.mem_cons.mp hj' with rfl | hj'l
        · have hnex : ¬ ∃ k ∈ l, rWire k = rWire j' := by
            rintro ⟨k, hk, heq⟩
            have hkj : k = j' := Fin.ext (by simpa [rWire, Fin.ext_iff] using heq)
            exact hl.1 (hkj ▸ hk)
          rw [dif_neg hnex]
          simp [z1]
        · have hex_l : ∃ k ∈ l, rWire k = rWire j' := ⟨j', hj'l, rfl⟩
          have hch_l : Classical.choose hex_l = j' :=
            Fin.ext (by simpa [rWire, Fin.ext_iff] using (Classical.choose_spec hex_l).2)
          rw [dif_pos hex_l, hch_l]
      · have ha_l : ¬ ∃ k ∈ l, rWire k = a := fun ⟨k, hk, heq⟩ => ha ⟨k, by simp [hk], heq⟩
        have harj : a ≠ rWire j := fun heq => ha ⟨j, by simp, heq.symm⟩
        rw [dif_neg ha_l, dif_neg ha]
        simp [z1, harj]
  refine ⟨N, m, fullCirc, outEmb, hfull_q.le, fun A hPA => ?_⟩
  have hA_ne : A.Nonempty := hP A hPA
  dsimp [fullCirc]
  rw [oracleCircuit_unitary_append, act_mul]
  have h0_q : ∀ i : Fin n, (fun _ : Fin m => false) (qWire i) = false := fun _ => rfl
  have h0_r : ∀ j ∈ List.finRange N, (fun _ : Fin m => false) (rWire j) = false := fun _ _ => rfl
  change probEvent (act _ (act ((loopCirc (List.finRange N)).unitary fun _ => majOracle A)
      (ket fun _ : Fin m => false))) _ ≥ 2 / 3
  rw [hloop_act A (List.finRange N) (List.nodup_finRange N) _ h0_q h0_r]
  set z_tbl : Qubits m := fun a =>
    if h : ∃ j ∈ List.finRange N, rWire j = a then truthTable A (Classical.choose h) else false
  have hz_tbl_r : ∀ j : Fin N, z_tbl (rWire j) = truthTable A j := by
    intro j
    have hex : ∃ j' ∈ List.finRange N, rWire j' = rWire j := ⟨j, List.mem_finRange j, rfl⟩
    have hch : Classical.choose hex = j :=
      Fin.ext (by simpa [rWire, Fin.ext_iff] using (Classical.choose_spec hex).2)
    dsimp [z_tbl]
    rw [dif_pos hex, hch]
  have hz_tbl_out : ∀ i : Fin n, z_tbl (outWire i) = false := by
    intro i
    have hnex : ¬ ∃ j ∈ List.finRange N, rWire j = outWire i := by
      rintro ⟨j, _, heq⟩; simp [rWire, outWire, Fin.ext_iff] at heq; omega
    dsimp [z_tbl]
    rw [dif_neg hnex]
  have hdec_step : act (OracleCircuit.unitary [decStep] fun _ => majOracle A) (ket z_tbl) =
      ket (decodeFun z_tbl) := by
    simp only [OracleCircuit.unitary, List.map_singleton, List.reverse_singleton,
      List.prod_singleton, decStep, OracleStep.mat, decodeGate]
    rw [act_embedOp_invMat decodeFun (Function.Embedding.refl _) z_tbl]
    congr 1
    funext a
    have hex : ∃ b, Function.Embedding.refl (Fin m) b = a := ⟨a, rfl⟩
    have hch : Classical.choose hex = a := Classical.choose_spec hex
    rw [dif_pos hex, hch]
    rfl
  rw [hdec_step]
  have hout_ok : ∀ i : Fin n, decodeFun z_tbl (outEmb i) = decide (i ∈ A) := by
    intro i
    have hi_ge : n + N ≤ (outEmb i).1 := by
      change n + N ≤ n + N + i.1
      omega
    have hsub : (⟨(outEmb i).1 - (n + N), by
        have := (outEmb i).isLt
        change (outEmb i).1 < n + N + n at this
        omega⟩ : Fin n) = i := by
      ext
      change (n + N + i.1) - (n + N) = i.1
      omega
    have htbl_eq : (fun j => z_tbl (rWire j)) = truthTable A := funext hz_tbl_r
    dsimp [decodeFun]
    rw [dif_pos hi_ge, htbl_eq, hdecode A hA_ne, hsub]
    change xor (z_tbl (outWire i)) (decide (i ∈ A)) = decide (i ∈ A)
    rw [hz_tbl_out i, Bool.false_xor]
  have hprob_one : probEvent (ket (decodeFun z_tbl))
      (fun z => ∀ i : Fin n, z (outEmb i) = decide (i ∈ A)) = 1 := by
    simp only [probEvent]
    rw [Finset.sum_eq_single (decodeFun z_tbl)]
    · simp [prob, ket]
    · intro x _ hx
      rw [prob, ket, ket, EuclideanSpace.inner_single_left]
      simp [hx.symm]
    · intro hmem
      exfalso
      apply hmem
      simp [hout_ok]
  linarith [hprob_one]

/-! ### Part 4: Combinatorial Counting, Shifted-Threshold Schur Bound & Ambainis Potential -/

abbrev Fam {n : ℕ} (U : Finset (Fin n)) (m : ℕ) := {A : Finset (Fin n) // A ⊆ U ∧ A.card = m}

noncomputable def gamma {n m : ℕ} {U : Finset (Fin n)} (A B : Fam U m) : ℝ :=
  if A = B then 0 else 1 / (((A.1 \ B.1).card : ℝ) * ((m.choose (A.1 \ B.1).card : ℕ) : ℝ) ^ 2)

lemma sdiff_card_eq_symm {n m : ℕ} {U : Finset (Fin n)} (A B : Fam U m) :
    (A.1 \ B.1).card = (B.1 \ A.1).card := by
  have h1 : (A.1 \ B.1).card + (A.1 ∩ B.1).card = A.1.card := Finset.card_sdiff_add_card_inter A.1 B.1
  have h2 : (B.1 \ A.1).card + (B.1 ∩ A.1).card = B.1.card := Finset.card_sdiff_add_card_inter B.1 A.1
  rw [Finset.inter_comm] at h2
  rw [A.2.2] at h1
  rw [B.2.2] at h2
  omega

lemma gamma_nonneg {n m : ℕ} {U : Finset (Fin n)} (A B : Fam U m) : 0 ≤ gamma A B := by
  unfold gamma
  split_ifs <;> positivity

lemma gamma_symm {n m : ℕ} {U : Finset (Fin n)} (A B : Fam U m) : gamma A B = gamma B A := by
  unfold gamma
  by_cases h : A = B
  · subst h; simp
  · have h' : B ≠ A := fun h1 => h h1.symm
    rw [if_neg h, if_neg h', sdiff_card_eq_symm A B]

lemma sdiff_card_bounds {n m : ℕ} {U : Finset (Fin n)} {A B : Fam U m} (hAB : A ≠ B) :
    1 ≤ (A.1 \ B.1).card ∧ (A.1 \ B.1).card ≤ m := by
  have hle : (A.1 \ B.1).card ≤ m := by
    calc (A.1 \ B.1).card ≤ A.1.card := Finset.card_le_card Finset.sdiff_subset
      _ = m := A.2.2
  have hpos : 1 ≤ (A.1 \ B.1).card := by
    by_contra h0
    have hz : (A.1 \ B.1).card = 0 := by omega
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hz
    apply hAB
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hz (by rw [A.2.2, B.2.2])
  exact ⟨hpos, hle⟩

lemma sum_gamma_eq_harmonic {n m : ℕ} {U : Finset (Fin n)} (hU : U.card = 2 * m)
    (A : Fam U m) :
    ∑ B : Fam U m, gamma A B = ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
  classical
  have hUA : (U \ A.1).card = m := by
    have h1 := Finset.card_sdiff_add_card_eq_card A.2.1
    rw [A.2.2, hU] at h1
    omega
  rw [← Finset.add_sum_erase Finset.univ (fun B => gamma A B) (Finset.mem_univ A)]
  have hAA : gamma A A = 0 := by simp [gamma]
  rw [hAA, zero_add]
  have hmaps : ∀ B ∈ Finset.univ.erase A, (A.1 \ B.1).card ∈ Finset.Icc 1 m := by
    intro B hB
    have hne : A ≠ B := fun h => (Finset.mem_erase.mp hB).1 h.symm
    have hs := sdiff_card_bounds hne
    exact Finset.mem_Icc.mpr hs
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun B => gamma A B)]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Finset.mem_Icc] at hs
  have h_const : ∀ B ∈ (Finset.univ.erase A).filter (fun B : Fam U m => (A.1 \ B.1).card = s),
      gamma A B = 1 / ((s : ℝ) * ((m.choose s : ℕ) : ℝ) ^ 2) := by
    intro B hB
    simp only [Finset.mem_filter, Finset.mem_erase] at hB
    have hne : A ≠ B := fun h => hB.1.1 h.symm
    simp [gamma, hne, hB.2]
  rw [Finset.sum_congr rfl h_const, Finset.sum_const, nsmul_eq_mul]
  have hcard_fiber : ((Finset.univ.erase A).filter (fun B : Fam U m => (A.1 \ B.1).card = s)).card =
      m.choose s * m.choose s := by
    have hpair : (Finset.univ.filter fun p : Finset (Fin n) × Finset (Fin n) =>
        p.1 ∈ A.1.powersetCard s ∧ p.2 ∈ (U \ A.1).powersetCard s).card = m.choose s * m.choose s := by
      have hset : (Finset.univ.filter fun p : Finset (Fin n) × Finset (Fin n) =>
          p.1 ∈ A.1.powersetCard s ∧ p.2 ∈ (U \ A.1).powersetCard s) =
          A.1.powersetCard s ×ˢ (U \ A.1).powersetCard s := by
        ext p; simp
      rw [hset, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, A.2.2, hUA]
    rw [← hpair]
    refine Finset.card_bij (fun B _ => (A.1 \ B.1, B.1 \ A.1)) ?_ ?_ ?_
    · intro B hB
      simp only [Finset.mem_filter, Finset.mem_erase] at hB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
      refine ⟨⟨Finset.sdiff_subset, hB.2⟩, ⟨?_, ?_⟩⟩
      · intro x hx
        simp only [Finset.mem_sdiff] at hx ⊢
        exact ⟨B.2.1 hx.1, hx.2⟩
      · rw [← sdiff_card_eq_symm A B, hB.2]
    · intro B1 hB1 B2 hB2 heq
      have h1 : A.1 \ B1.1 = A.1 \ B2.1 := congrArg Prod.fst heq
      have h2 : B1.1 \ A.1 = B2.1 \ A.1 := congrArg Prod.snd heq
      apply Subtype.ext
      have hB1_eq : B1.1 = (A.1 \ (A.1 \ B1.1)) ∪ (B1.1 \ A.1) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      have hB2_eq : B2.1 = (A.1 \ (A.1 \ B2.1)) ∪ (B2.1 \ A.1) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      rw [hB1_eq, hB2_eq, h1, h2]
    · intro ⟨X, Y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard] at hp
      have hX_sub : X ⊆ A.1 := hp.1.1
      have hX_card : X.card = s := hp.1.2
      have hY_sub : Y ⊆ U \ A.1 := hp.2.1
      have hY_card : Y.card = s := hp.2.2
      have hdisj : Disjoint (A.1 \ X) Y := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp (hY_sub hx2)).2 (Finset.mem_sdiff.mp hx1).1
      let Bset : Finset (Fin n) := (A.1 \ X) ∪ Y
      have hB_sub : Bset ⊆ U := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · exact A.2.1 (Finset.mem_sdiff.mp hx1).1
        · exact (Finset.mem_sdiff.mp (hY_sub hx2)).1
      have hB_card : Bset.card = m := by
        rw [Finset.card_union_of_disjoint hdisj]
        have hAX := Finset.card_sdiff_add_card_eq_card hX_sub
        rw [A.2.2, hX_card] at hAX
        omega
      let B : Fam U m := ⟨Bset, hB_sub, hB_card⟩
      have hAB_sdiff : A.1 \ B.1 = X := by
        ext x
        simp only [B, Bset, Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxA, hnot⟩
          by_contra hxX
          exact hnot (Or.inl ⟨hxA, hxX⟩)
        · intro hxX
          refine ⟨hX_sub hxX, fun h => ?_⟩
          rcases h with ⟨_, hnx⟩ | hxY
          · exact hnx hxX
          · exact (Finset.mem_sdiff.mp (hY_sub hxY)).2 (hX_sub hxX)
      have hBA_sdiff : B.1 \ A.1 = Y := by
        ext x
        simp only [B, Bset, Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx1 | hx2, hna⟩
          · exact absurd hx1.1 hna
          · exact hx2
        · intro hxY
          exact ⟨Or.inr hxY, (Finset.mem_sdiff.mp (hY_sub hxY)).2⟩
      have hB_ne : B ≠ A := by
        intro hBA
        have : (A.1 \ B.1).card = 0 := by rw [hBA]; simp
        rw [hAB_sdiff, hX_card] at this
        omega
      refine ⟨B, ?_, Prod.ext hAB_sdiff hBA_sdiff⟩
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hB_ne, Finset.mem_univ _⟩, by rw [hAB_sdiff, hX_card]⟩
  rw [hcard_fiber]
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
  have hch_pos : (0 : ℝ) < ((m.choose s : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos hs.2
  push_cast
  field_simp

lemma equiv_prefix_card {α : Type*} [Fintype α] [DecidableEq α] {m s : ℕ}
    (hs : s ≤ m) (hcard : Fintype.card α = m) (P : α → Prop) [DecidablePred P]
    (hP : (Finset.univ.filter P).card = s) :
    (Finset.univ.filter fun e : Fin m ≃ α => ∀ i : Fin m, i.1 < s → P (e i)).card =
      s.factorial * (m - s).factorial := by
  classical
  let I := {i : Fin m // i.1 < s}
  let Ic := {i : Fin m // ¬ (i.1 < s)}
  let T := {a : α // P a}
  let Tc := {a : α // ¬ P a}
  have hI_card : Fintype.card I = s := by
    rw [Fintype.card_subtype]
    have hsub : (Finset.univ.filter fun i : Fin m => i.1 < s).card = s := by
      conv_rhs => rw [← Finset.card_range s]
      refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
      · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i1 _ i2 _ heq; exact Fin.ext heq
      · intro j hj
        have hj' : j < s := Finset.mem_range.mp hj
        exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩
    exact hsub
  have hIc_card : Fintype.card Ic = m - s := by
    have hcomp := Fintype.card_subtype_compl (fun i : Fin m => i.1 < s)
    rw [Fintype.card_fin] at hcomp
    change Fintype.card Ic = m - Fintype.card I at hcomp
    rw [hcomp, hI_card]
  have hT_card : Fintype.card T = s := by
    rw [Fintype.card_subtype]; exact hP
  have hTc_card : Fintype.card Tc = m - s := by
    have hcomp := Fintype.card_subtype_compl P
    rw [hcard] at hcomp
    change Fintype.card Tc = m - Fintype.card T at hcomp
    rw [hcomp, hT_card]
  have hequiv : ((I ≃ T) × (Ic ≃ Tc)) ≃
      {e : Fin m ≃ α // ∀ i : Fin m, i.1 < s → P (e i)} :=
    { toFun := fun ⟨e1, e2⟩ =>
        ⟨{ toFun := fun i => if h : i.1 < s then (e1 ⟨i, h⟩).1 else (e2 ⟨i, h⟩).1
         , invFun := fun a => if h : P a then (e1.symm ⟨a, h⟩).1 else (e2.symm ⟨a, h⟩).1
         , left_inv := fun i => by
             by_cases h : i.1 < s
             · have hP1 : P (e1 ⟨i, h⟩).1 := (e1 ⟨i, h⟩).2
               simp [h, hP1]
             · have hP2 : ¬ P (e2 ⟨i, h⟩).1 := (e2 ⟨i, h⟩).2
               simp [h, hP2]
         , right_inv := fun a => by
             by_cases h : P a
             · have h1 : (e1.symm ⟨a, h⟩).1.1 < s := (e1.symm ⟨a, h⟩).2
               simp [h, h1]
             · have h2 : ¬ ((e2.symm ⟨a, h⟩).1.1 < s) := (e2.symm ⟨a, h⟩).2
               simp [h, h2] },
         fun i hi => by simp [hi, (e1 ⟨i, hi⟩).2]⟩
      invFun := fun ⟨e, he⟩ =>
        have hI_bij : Function.Bijective (fun i : I => (⟨e i.1, he i.1 i.2⟩ : T)) := by
          rw [Fintype.bijective_iff_injective_and_card]
          refine ⟨fun i1 i2 h => Subtype.ext (e.injective (congrArg Subtype.val h)), ?_⟩
          rw [hI_card, hT_card]
        let e1 : I ≃ T := Equiv.ofBijective _ hI_bij
        have hIc_mem : ∀ i : Ic, ¬ P (e i.1) := by
          intro i hPi
          obtain ⟨j, hj⟩ := hI_bij.2 ⟨e i.1, hPi⟩
          have heq : e j.1 = e i.1 := congrArg Subtype.val hj
          have hji : j.1 = i.1 := e.injective heq
          exact i.2 (hji ▸ j.2)
        have hIc_bij : Function.Bijective (fun i : Ic => (⟨e i.1, hIc_mem i⟩ : Tc)) := by
          rw [Fintype.bijective_iff_injective_and_card]
          refine ⟨fun i1 i2 h => Subtype.ext (e.injective (congrArg Subtype.val h)), ?_⟩
          rw [hIc_card, hTc_card]
        let e2 : Ic ≃ Tc := Equiv.ofBijective _ hIc_bij
        ⟨e1, e2⟩
      left_inv := fun ⟨e1, e2⟩ => by
        ext x
        · dsimp; simp [x.2]
        · dsimp; simp [x.2]
      right_inv := fun ⟨e, he⟩ => by
        ext i
        by_cases h : i.1 < s <;> simp }
  rw [← Fintype.card_subtype]
  rw [← Fintype.card_congr hequiv, Fintype.card_prod]
  have hc1 : Fintype.card (I ≃ T) = s.factorial := by
    have eI : I ≃ Fin s := Fintype.equivFinOfCardEq hI_card
    have eT : T ≃ Fin s := Fintype.equivFinOfCardEq hT_card
    rw [Fintype.card_congr (Equiv.equivCongr eI eT), Fintype.card_perm, Fintype.card_fin]
  have hc2 : Fintype.card (Ic ≃ Tc) = (m - s).factorial := by
    have eIc : Ic ≃ Fin (m - s) := Fintype.equivFinOfCardEq hIc_card
    have eTc : Tc ≃ Fin (m - s) := Fintype.equivFinOfCardEq hTc_card
    rw [Fintype.card_congr (Equiv.equivCongr eIc eTc), Fintype.card_perm, Fintype.card_fin]
  rw [hc1, hc2]

lemma card_prefix_inter {α : Type*} [DecidableEq α] {m : ℕ} (f : Fin m → α)
    (hf : Function.Injective f) (S : Finset α) {t : ℕ} (ht : t ≤ m) :
    ((Finset.univ.filter fun i : Fin m => i.1 < t).image f ∩ S).card =
      ∑ i ∈ Finset.range t, if h : i < m then (if f ⟨i, h⟩ ∈ S then (1 : ℕ) else 0) else 0 := by
  have h1 : ((Finset.univ.filter fun i : Fin m => i.1 < t).image f ∩ S).card =
      (Finset.univ.filter fun i : Fin m => i.1 < t ∧ f i ∈ S).card := by
    refine Finset.card_bij
      (fun x hx => Classical.choose (Finset.mem_image.mp (Finset.mem_inter.mp hx).1))
      ?_ ?_ ?_
    · intro x hx
      have hmem := (Finset.mem_inter.mp hx).1
      have hspec := Classical.choose_spec (Finset.mem_image.mp hmem)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hspec.1).2, ?_⟩
      rw [hspec.2]
      exact (Finset.mem_inter.mp hx).2
    · intro x1 hx1 x2 hx2 heq
      have h1' := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp hx1).1)
      have h2' := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp hx2).1)
      rw [← h1'.2, ← h2'.2, heq]
    · intro i hi
      rw [Finset.mem_filter] at hi
      refine ⟨f i, Finset.mem_inter.mpr
        ⟨Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2.1⟩), hi.2.2⟩, ?_⟩
      apply hf
      exact (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp (Finset.mem_inter.mpr
        ⟨Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2.1⟩), hi.2.2⟩)).1)).2
  rw [h1]
  have h2 : (Finset.univ.filter fun i : Fin m => i.1 < t ∧ f i ∈ S).card =
      ((Finset.range t).filter fun i => if h : i < m then f ⟨i, h⟩ ∈ S else False).card := by
    refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hi.2.1, ?_⟩
      rw [dif_pos i.isLt]
      exact hi.2.2
    · intro i1 _ i2 _ heq; exact Fin.ext heq
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      have hj_m : j < m := Nat.lt_of_lt_of_le hj.1 ht
      have hfj : f ⟨j, hj_m⟩ ∈ S := by simpa [hj_m] using hj.2
      exact ⟨⟨j, hj_m⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1, hfj⟩, rfl⟩
  rw [h2, Finset.card_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i < m := Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) ht
  simp [him]

abbrev SwapΩ {n : ℕ} (m : ℕ) (U A : Finset (Fin n)) :=
  (Fin m ≃ {x : Fin n // x ∈ A}) × (Fin m ≃ {x : Fin n // x ∈ U \ A})

def prefA {n m : ℕ} {A : Finset (Fin n)} (α : Fin m ≃ {x : Fin n // x ∈ A}) (t : ℕ) :
    Finset (Fin n) :=
  (Finset.univ.filter fun i : Fin m => i.1 < t).image (fun i => (α i).1)

def prefU {n m : ℕ} {U A : Finset (Fin n)} (β : Fin m ≃ {x : Fin n // x ∈ U \ A}) (t : ℕ) :
    Finset (Fin n) :=
  (Finset.univ.filter fun i : Fin m => i.1 < t).image (fun i => (β i).1)

def swapSet {n m : ℕ} {U : Finset (Fin n)} (A : Fam U m) (ω : SwapΩ m U A.1) (t : ℕ) :
    Finset (Fin n) :=
  (A.1 \ prefA ω.1 t) ∪ prefU ω.2 t

lemma prefA_subset {n m : ℕ} {A : Finset (Fin n)} (α : Fin m ≃ {x : Fin n // x ∈ A}) (t : ℕ) :
    prefA α t ⊆ A := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact (α i).2

lemma prefU_subset {n m : ℕ} {U A : Finset (Fin n)} (β : Fin m ≃ {x : Fin n // x ∈ U \ A})
    (t : ℕ) : prefU β t ⊆ U \ A := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact (β i).2

lemma prefA_card {n m : ℕ} {A : Finset (Fin n)} (α : Fin m ≃ {x : Fin n // x ∈ A})
    {t : ℕ} (ht : t ≤ m) : (prefA α t).card = t := by
  dsimp [prefA]
  rw [Finset.card_image_of_injective _ (fun i j hij => α.injective (Subtype.ext hij))]
  conv_rhs => rw [← Finset.card_range t]
  refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
  · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i1 _ i2 _ heq; exact Fin.ext heq
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩

lemma prefU_card {n m : ℕ} {U A : Finset (Fin n)} (β : Fin m ≃ {x : Fin n // x ∈ U \ A})
    {t : ℕ} (ht : t ≤ m) : (prefU β t).card = t := by
  dsimp [prefU]
  rw [Finset.card_image_of_injective _ (fun i j hij => β.injective (Subtype.ext hij))]
  conv_rhs => rw [← Finset.card_range t]
  refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
  · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i1 _ i2 _ heq; exact Fin.ext heq
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩

lemma swapSet_sdiff {n m : ℕ} {U : Finset (Fin n)} (A : Fam U m) (ω : SwapΩ m U A.1) (t : ℕ) :
    A.1 \ swapSet A ω t = prefA ω.1 t := by
  ext x
  simp only [swapSet, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hxA, hnot⟩
    by_contra hnp
    exact hnot (Or.inl ⟨hxA, hnp⟩)
  · intro hxp
    refine ⟨prefA_subset ω.1 t hxp, fun h => ?_⟩
    rcases h with ⟨_, hnp⟩ | hxu
    · exact hnp hxp
    · exact (Finset.mem_sdiff.mp (prefU_subset ω.2 t hxu)).2 (prefA_subset ω.1 t hxp)

lemma swapSet_rsdiff {n m : ℕ} {U : Finset (Fin n)} (A : Fam U m) (ω : SwapΩ m U A.1) (t : ℕ) :
    swapSet A ω t \ A.1 = prefU ω.2 t := by
  ext x
  simp only [swapSet, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hx1 | hx2, hna⟩
    · exact absurd hx1.1 hna
    · exact hx2
  · intro hxu
    exact ⟨Or.inr hxu, (Finset.mem_sdiff.mp (prefU_subset ω.2 t hxu)).2⟩

lemma swapSet_mem_fam {n m : ℕ} {U : Finset (Fin n)} (A : Fam U m) (ω : SwapΩ m U A.1)
    {s : ℕ} (hs : s ≤ m) : swapSet A ω s ⊆ U ∧ (swapSet A ω s).card = m := by
  have hdisj : Disjoint (A.1 \ prefA ω.1 s) (prefU ω.2 s) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp (prefU_subset ω.2 s hx2)).2 (Finset.mem_sdiff.mp hx1).1
  refine ⟨?_, ?_⟩
  · intro x hx
    dsimp [swapSet] at hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · exact A.2.1 (Finset.mem_sdiff.mp hx1).1
    · exact (Finset.mem_sdiff.mp (prefU_subset ω.2 s hx2)).1
  · dsimp [swapSet]
    rw [Finset.card_union_of_disjoint hdisj]
    have h1 := Finset.card_sdiff_add_card_eq_card (prefA_subset ω.1 s)
    rw [A.2.2, prefA_card ω.1 hs] at h1
    rw [prefU_card ω.2 hs]
    omega

lemma swapOmega_card {n m : ℕ} {U : Finset (Fin n)} (hU : U.card = 2 * m) (A : Fam U m) :
    Fintype.card (SwapΩ m U A.1) = m.factorial * m.factorial := by
  have hUA : (U \ A.1).card = m := by
    have h1 := Finset.card_sdiff_add_card_eq_card A.2.1
    rw [A.2.2, hU] at h1
    omega
  have hcard_A1 : Fintype.card {x : Fin n // x ∈ A.1} = m := by
    rw [Fintype.card_coe]; exact A.2.2
  have hcard_UA : Fintype.card {x : Fin n // x ∈ U \ A.1} = m := by
    rw [Fintype.card_coe]; exact hUA
  dsimp [SwapΩ]
  rw [Fintype.card_prod]
  have c1 : Fintype.card (Fin m ≃ {x : Fin n // x ∈ A.1}) = m.factorial := by
    rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin m)) (Fintype.equivFinOfCardEq hcard_A1)),
      Fintype.card_perm, Fintype.card_fin]
  have c2 : Fintype.card (Fin m ≃ {x : Fin n // x ∈ U \ A.1}) = m.factorial := by
    rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin m)) (Fintype.equivFinOfCardEq hcard_UA)),
      Fintype.card_perm, Fintype.card_fin]
  rw [c1, c2]

lemma swapSet_count_eq {n m : ℕ} {U : Finset (Fin n)} (hU : U.card = 2 * m) (A : Fam U m)
    {s : ℕ} (hs : s ≤ m) (B : Fam U m) (hBs : (A.1 \ B.1).card = s) :
    (Finset.univ.filter fun ω : SwapΩ m U A.1 => swapSet A ω s = B.1).card =
      (s.factorial * (m - s).factorial) ^ 2 := by
  classical
  have hUA : (U \ A.1).card = m := by
    have h1 := Finset.card_sdiff_add_card_eq_card A.2.1
    rw [A.2.2, hU] at h1
    omega
  have hcard_A1 : Fintype.card {x : Fin n // x ∈ A.1} = m := by
    rw [Fintype.card_coe]; exact A.2.2
  have hcard_UA : Fintype.card {x : Fin n // x ∈ U \ A.1} = m := by
    rw [Fintype.card_coe]; exact hUA
  have hiff : ∀ ω : SwapΩ m U A.1, swapSet A ω s = B.1 ↔
      (∀ i : Fin m, i.1 < s → (ω.1 i).1 ∈ A.1 \ B.1) ∧
      (∀ i : Fin m, i.1 < s → (ω.2 i).1 ∈ B.1 \ A.1) := by
    intro ω
    constructor
    · intro heq
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have hmem : (ω.1 i).1 ∈ prefA ω.1 s :=
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        rw [← swapSet_sdiff A ω s, heq] at hmem
        exact hmem
      · have hmem : (ω.2 i).1 ∈ prefU ω.2 s :=
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        rw [← swapSet_rsdiff A ω s, heq] at hmem
        exact hmem
    · rintro ⟨h1, h2⟩
      have hpA_sub : prefA ω.1 s ⊆ A.1 \ B.1 := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact h1 i (Finset.mem_filter.mp hi).2
      have hpA_eq : prefA ω.1 s = A.1 \ B.1 :=
        Finset.eq_of_subset_of_card_le hpA_sub (by rw [prefA_card _ hs, hBs])
      have hpU_sub : prefU ω.2 s ⊆ B.1 \ A.1 := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact h2 i (Finset.mem_filter.mp hi).2
      have hpU_eq : prefU ω.2 s = B.1 \ A.1 := by
        have hBs' : (B.1 \ A.1).card = s := by rw [← sdiff_card_eq_symm A B, hBs]
        exact Finset.eq_of_subset_of_card_le hpU_sub (by rw [prefU_card _ hs, hBs'])
      ext x
      simp only [swapSet, hpA_eq, hpU_eq, Finset.mem_union, Finset.mem_sdiff]
      tauto
  have hfilt : (Finset.univ.filter fun ω : SwapΩ m U A.1 => swapSet A ω s = B.1) =
      (Finset.univ.filter fun α : Fin m ≃ {x : Fin n // x ∈ A.1} =>
        ∀ i : Fin m, i.1 < s → (α i).1 ∈ A.1 \ B.1) ×ˢ
      (Finset.univ.filter fun β : Fin m ≃ {x : Fin n // x ∈ U \ A.1} =>
        ∀ i : Fin m, i.1 < s → (β i).1 ∈ B.1 \ A.1) := by
    ext ⟨α, β⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff (α, β)
  rw [hfilt, Finset.card_product]
  have hc1 : (Finset.univ.filter fun α : Fin m ≃ {x : Fin n // x ∈ A.1} =>
      ∀ i : Fin m, i.1 < s → (α i).1 ∈ A.1 \ B.1).card = s.factorial * (m - s).factorial := by
    refine equiv_prefix_card hs hcard_A1 (fun x => x.1 ∈ A.1 \ B.1) ?_
    rw [← hBs]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x1 _ x2 _ heq; exact Subtype.ext heq
    · intro y hy
      exact ⟨⟨y, (Finset.mem_sdiff.mp hy).1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
  have hc2 : (Finset.univ.filter fun β : Fin m ≃ {x : Fin n // x ∈ U \ A.1} =>
      ∀ i : Fin m, i.1 < s → (β i).1 ∈ B.1 \ A.1).card = s.factorial * (m - s).factorial := by
    refine equiv_prefix_card hs hcard_UA (fun x => x.1 ∈ B.1 \ A.1) ?_
    have hBs' : (B.1 \ A.1).card = s := by rw [← sdiff_card_eq_symm A B, hBs]
    rw [← hBs']
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x1 _ x2 _ heq; exact Subtype.ext heq
    · intro y hy
      have hyU : y ∈ U \ A.1 := by
        have := Finset.mem_sdiff.mp hy
        exact Finset.mem_sdiff.mpr ⟨B.2.1 this.1, this.2⟩
      exact ⟨⟨y, hyU⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
  rw [hc1, hc2, sq]

def isFirstHit {n m : ℕ} {U : Finset (Fin n)} (A : Fam U m) (S : Finset (Fin n)) (b : ℕ)
    (ω : SwapΩ m U A.1) (s : ℕ) : Prop :=
  1 ≤ s ∧ s ≤ m ∧ (swapSet A ω s ∩ S).card = b ∧
  ∀ t ∈ Finset.Ico 1 s, (swapSet A ω t ∩ S).card ≠ b

open Classical in
lemma swapSet_cycle_count {n m : ℕ} {U : Finset (Fin n)} (A : Fam U m) (S : Finset (Fin n))
    (b : ℕ) (hb : b ≠ (A.1 ∩ S).card) {s : ℕ} (hs1 : 1 ≤ s) (hs_le : s ≤ m) :
    Int.natAbs ((b : ℤ) - ((A.1 ∩ S).card : ℤ)) *
        (Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b).card =
      s * (Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card := by
  classical
  set a : ℕ := (A.1 ∩ S).card
  set qnat : ℕ := Int.natAbs ((b : ℤ) - (a : ℤ))
  have hq_pos : 1 ≤ qnat := by omega
  let d (ω : SwapΩ m U A.1) (i : ℕ) : ℤ :=
    if h : i % s < m then
      (if (ω.2 ⟨i % s, h⟩).1 ∈ S then (1 : ℤ) else 0) -
      (if (ω.1 ⟨i % s, h⟩).1 ∈ S then (1 : ℤ) else 0)
    else 0
  have hd_bounds : ∀ ω i, -1 ≤ d ω i ∧ d ω i ≤ 1 := by
    intro ω i; dsimp [d]; split_ifs <;> omega
  have hswap_inc : ∀ ω (t : ℕ), t ≤ s →
      ((swapSet A ω t ∩ S).card : ℤ) = (a : ℤ) + ∑ i ∈ Finset.range t, d ω i := by
    intro ω t ht
    have htm : t ≤ m := ht.trans hs_le
    have hpA_inter : (prefA ω.1 t ∩ S).card =
        ∑ i ∈ Finset.range t,
          if h : i < m then (if (ω.1 ⟨i, h⟩).1 ∈ S then (1 : ℕ) else 0) else 0 :=
      card_prefix_inter (fun i : Fin m => (ω.1 i).1)
        (fun i j hij => ω.1.injective (Subtype.ext hij)) S htm
    have hpU_inter : (prefU ω.2 t ∩ S).card =
        ∑ i ∈ Finset.range t,
          if h : i < m then (if (ω.2 ⟨i, h⟩).1 ∈ S then (1 : ℕ) else 0) else 0 :=
      card_prefix_inter (fun i : Fin m => (ω.2 i).1)
        (fun i j hij => ω.2.injective (Subtype.ext hij)) S htm
    have hset_eq : swapSet A ω t ∩ S = ((A.1 ∩ S) \ (prefA ω.1 t ∩ S)) ∪ (prefU ω.2 t ∩ S) := by
      ext x
      simp only [swapSet, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hdisj_S : Disjoint ((A.1 ∩ S) \ (prefA ω.1 t ∩ S)) (prefU ω.2 t ∩ S) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hxA : x ∈ A.1 := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx1).1).1
      have hxU : x ∈ U \ A.1 := prefU_subset ω.2 t (Finset.mem_inter.mp hx2).1
      exact (Finset.mem_sdiff.mp hxU).2 hxA
    have hsub_S : prefA ω.1 t ∩ S ⊆ A.1 ∩ S := Finset.inter_subset_inter_right (prefA_subset ω.1 t)
    have hcard_S : (swapSet A ω t ∩ S).card + (prefA ω.1 t ∩ S).card =
        (A.1 ∩ S).card + (prefU ω.2 t ∩ S).card := by
      rw [hset_eq, Finset.card_union_of_disjoint hdisj_S]
      have := Finset.card_sdiff_add_card_eq_card hsub_S
      omega
    have hsum_d : ∑ i ∈ Finset.range t, d ω i =
        (∑ i ∈ Finset.range t,
          if h : i < m then (if (ω.2 ⟨i, h⟩).1 ∈ S then (1 : ℤ) else 0) else 0) -
        (∑ i ∈ Finset.range t,
          if h : i < m then (if (ω.1 ⟨i, h⟩).1 ∈ S then (1 : ℤ) else 0) else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi_t : i < t := Finset.mem_range.mp hi
      have hmod : i % s = i := Nat.mod_eq_of_lt (by omega)
      have him : i < m := by omega
      dsimp [d]
      rw [dif_pos (by omega), dif_pos him, dif_pos him]
      simp [hmod]
    have hpA_z : ((prefA ω.1 t ∩ S).card : ℤ) =
        ∑ i ∈ Finset.range t,
          if h : i < m then (if (ω.1 ⟨i, h⟩).1 ∈ S then (1 : ℤ) else 0) else 0 := by
      rw [hpA_inter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have hpU_z : ((prefU ω.2 t ∩ S).card : ℤ) =
        ∑ i ∈ Finset.range t,
          if h : i < m then (if (ω.2 ⟨i, h⟩).1 ∈ S then (1 : ℤ) else 0) else 0 := by
      rw [hpU_inter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have hcard_z : ((swapSet A ω t ∩ S).card : ℤ) + ((prefA ω.1 t ∩ S).card : ℤ) =
        (a : ℤ) + ((prefU ω.2 t ∩ S).card : ℤ) := by
      exact_mod_cast hcard_S
    rw [hpA_z, hpU_z] at hcard_z
    linarith
  let rotFun (r : ℕ) (i : Fin m) : Fin m :=
    if h : i.1 < s then ⟨(i.1 + r) % s, by have := Nat.mod_lt (i.1 + r) (by omega : 0 < s); omega⟩ else i
  have hrotFun_lt : ∀ r' (i : Fin m), i.1 < s → (rotFun r' i).1 = (i.1 + r') % s := by
    intro r' i hi; dsimp [rotFun]; simp [hi]
  have hrotFun_ge : ∀ r' (i : Fin m), ¬ i.1 < s → rotFun r' i = i := by
    intro r' i hi; dsimp [rotFun]; simp [hi]
  let rot (r : ℕ) : Equiv.Perm (Fin m) :=
    { toFun := rotFun r
    , invFun := rotFun (s - r % s)
    , left_inv := fun i => by
        by_cases h : i.1 < s
        · have h1 : (rotFun r i).1 < s := by
            rw [hrotFun_lt r i h]; exact Nat.mod_lt _ (by omega)
          apply Fin.ext
          rw [hrotFun_lt (s - r % s) (rotFun r i) h1, hrotFun_lt r i h]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hr : r % s < s := Nat.mod_lt r (by omega)
          have hsum : i.1 + r + (s - r % s) = i.1 + s * (r / s) + s := by
            have := Nat.div_add_mod r s
            omega
          rw [hsum]
          simp [Nat.add_mod_right, Nat.mod_eq_of_lt h]
        · rw [hrotFun_ge r i h, hrotFun_ge (s - r % s) i h]
    , right_inv := fun i => by
        by_cases h : i.1 < s
        · have h1 : (rotFun (s - r % s) i).1 < s := by
            rw [hrotFun_lt (s - r % s) i h]; exact Nat.mod_lt _ (by omega)
          apply Fin.ext
          rw [hrotFun_lt r (rotFun (s - r % s) i) h1, hrotFun_lt (s - r % s) i h]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hr : r % s < s := Nat.mod_lt r (by omega)
          have hsum : i.1 + (s - r % s) + r = i.1 + s * (r / s) + s := by
            have := Nat.div_add_mod r s
            omega
          rw [hsum]
          simp [Nat.add_mod_right, Nat.mod_eq_of_lt h]
        · rw [hrotFun_ge (s - r % s) i h, hrotFun_ge r i h] }
  let shift (r : ℕ) : SwapΩ m U A.1 ≃ SwapΩ m U A.1 :=
    { toFun := fun ω => ((rot r).trans ω.1, (rot r).trans ω.2)
    , invFun := fun ω => ((rot r).symm.trans ω.1, (rot r).symm.trans ω.2)
    , left_inv := fun ⟨α, β⟩ => by ext x <;> simp
    , right_inv := fun ⟨α, β⟩ => by ext x <;> simp }
  have hshift_swap : ∀ r ω, swapSet A (shift r ω) s = swapSet A ω s := by
    intro r ω
    have h1 : prefA (shift r ω).1 s = prefA ω.1 s := by
      ext x
      simp only [prefA, shift, Equiv.coe_fn_mk, Equiv.coe_trans, Function.comp_apply,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨rot r i, ?_, rfl⟩
        dsimp [rot, rotFun]; split_ifs; exact Nat.mod_lt _ (by omega)
      · rintro ⟨i, hi, rfl⟩
        refine ⟨(rot r).symm i, ?_, by simp⟩
        dsimp [rot, rotFun]; split_ifs; exact Nat.mod_lt _ (by omega)
    have h2 : prefU (shift r ω).2 s = prefU ω.2 s := by
      ext x
      simp only [prefU, shift, Equiv.coe_fn_mk, Equiv.coe_trans, Function.comp_apply,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨rot r i, ?_, rfl⟩
        dsimp [rot, rotFun]; split_ifs; exact Nat.mod_lt _ (by omega)
      · rintro ⟨i, hi, rfl⟩
        refine ⟨(rot r).symm i, ?_, by simp⟩
        dsimp [rot, rotFun]; split_ifs; exact Nat.mod_lt _ (by omega)
    dsimp [swapSet]
    rw [h1, h2]
  let zrev (ω : SwapΩ m U A.1) (i : ℕ) : ℤ :=
    if a < b then d ω (s - 1 - i % s) else - d ω (s - 1 - i % s)
  have hzrev_per : ∀ ω i, zrev ω (i + s) = zrev ω i := by
    intro ω i; simp [zrev, Nat.add_mod_right]
  have hzrev_le : ∀ ω i, zrev ω i ≤ 1 := by
    intro ω i; dsimp [zrev]; split_ifs <;> linarith [hd_bounds ω (s - 1 - i % s)]
  have hzrev_sum : ∀ ω, (swapSet A ω s ∩ S).card = b →
      ∑ i ∈ Finset.range s, zrev ω i = (qnat : ℤ) := by
    intro ω hω
    have h_inc := hswap_inc ω s le_rfl
    rw [hω] at h_inc
    have hsum_d : ∑ i ∈ Finset.range s, d ω (s - 1 - i % s) = ∑ i ∈ Finset.range s, d ω i := by
      refine Finset.sum_bij (fun i _ => s - 1 - i) ?_ ?_ ?_ ?_
      · intro i hi; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
      · intro i1 hi1 i2 hi2 heq
        have h1 := Finset.mem_range.mp hi1; have h2 := Finset.mem_range.mp hi2; omega
      · intro j hj
        have hj' := Finset.mem_range.mp hj
        exact ⟨s - 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [Nat.mod_eq_of_lt hi']
    dsimp [zrev]
    split_ifs with hab
    · rw [hsum_d]; omega
    · rw [Finset.sum_neg_distrib, hsum_d]; omega
  have hshift_zrev : ∀ (r : ℕ) (ω : SwapΩ m U A.1) (j : ℕ),
      zrev (shift (s - r % s) ω) j = zrev ω (r + j) := by
    intro r ω j
    have hd_shift : ∀ (k : ℕ), k < s →
        d (shift (s - r % s) ω) k = d ω ((k + (s - r % s)) % s) := by
      intro k hk
      have hk_mod : k % s = k := Nat.mod_eq_of_lt hk
      have hkm : k % s < m := lt_of_lt_of_le (by omega) hs_le
      have hm2 : ((k + (s - r % s)) % s) % s = (k + (s - r % s)) % s := Nat.mod_mod _ s
      have hk2 : ((k + (s - r % s)) % s) % s < m := by
        rw [hm2]; exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hs_le
      have hrot_val : (rot (s - r % s) ⟨k % s, hkm⟩).1 = ((k + (s - r % s)) % s) % s := by
        change (rotFun (s - r % s) ⟨k % s, hkm⟩).1 = _
        dsimp [rotFun]
        split_ifs with hlt
        · simp [hk_mod, hm2]
        · exfalso; apply hlt; exact lt_of_eq_of_lt hk_mod hk
      have hrot_idx : rot (s - r % s) ⟨k % s, hkm⟩ = ⟨((k + (s - r % s)) % s) % s, hk2⟩ :=
        Fin.ext hrot_val
      dsimp [d, shift]
      rw [dif_pos hkm, dif_pos hk2]
      simp only [hrot_idx]
    have hidx_lt : s - 1 - j % s < s := by have := Nat.mod_lt j (by omega : 0 < s); omega
    have hidx_eq : (s - 1 - j % s + (s - r % s)) % s = s - 1 - (r + j) % s := by
      have hj : j % s < s := Nat.mod_lt j (by omega)
      have hr : r % s < s := Nat.mod_lt r (by omega)
      have h1 : (r + j) % s = (r % s + j % s) % s := Nat.add_mod r j s
      by_cases hsum : r % s + j % s < s
      · have hmod_rj : (r + j) % s = r % s + j % s := by rw [h1, Nat.mod_eq_of_lt hsum]
        have heq : s - 1 - j % s + (s - r % s) = s + (s - 1 - (r % s + j % s)) := by omega
        rw [hmod_rj, heq, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      · have hsum2 : r % s + j % s = s + (r % s + j % s - s) := by omega
        have hmod_rj : (r + j) % s = r % s + j % s - s := by
          calc (r + j) % s = (r % s + j % s) % s := h1
            _ = (s + (r % s + j % s - s)) % s := by conv_lhs => rw [hsum2]
            _ = (r % s + j % s - s) % s := Nat.add_mod_left _ _
            _ = r % s + j % s - s := Nat.mod_eq_of_lt (by omega)
        have heq : s - 1 - j % s + (s - r % s) = s - 1 - (r % s + j % s - s) := by omega
        rw [hmod_rj, heq]
        exact Nat.mod_eq_of_lt (by omega)
    dsimp [zrev]
    rw [hd_shift _ hidx_lt, hidx_eq]
  have hgood_iff_first : ∀ (ω : SwapΩ m U A.1) (r : ℕ), (swapSet A ω s ∩ S).card = b →
      (isGoodStart s (zrev ω) r ↔ isFirstHit A S b (shift (s - r % s) ω) s) := by
    intro ω r hωb
    let ω' := shift (s - r % s) ω
    have hω'b : (swapSet A ω' s ∩ S).card = b := by rw [hshift_swap, hωb]
    have hgood_eq : isGoodStart s (zrev ω) r ↔ isGoodStart s (zrev ω') 0 := by
      simp only [isGoodStart, ω']
      refine forall₂_congr fun k _ => ?_
      have hsum_eq : ∑ j ∈ Finset.range k, zrev (shift (s - r % s) ω) (0 + j) =
          ∑ j ∈ Finset.range k, zrev ω (r + j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [zero_add, hshift_zrev]
      rw [hsum_eq]
    rw [hgood_eq]
    have h0_iff : isGoodStart s (zrev ω') 0 ↔
        ∀ t ∈ Finset.Ico 0 s, (swapSet A ω' t ∩ S).card ≠ b := by
      have hsum_rel : ∀ k ∈ Finset.Icc 1 s,
          ∑ j ∈ Finset.range k, zrev ω' j =
            if a < b then (b : ℤ) - ((swapSet A ω' (s - k) ∩ S).card : ℤ)
            else ((swapSet A ω' (s - k) ∩ S).card : ℤ) - (b : ℤ) := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have h_s := hswap_inc ω' s le_rfl
        have h_sk := hswap_inc ω' (s - k) (by omega)
        rw [hω'b] at h_s
        have hsum_rev : ∑ j ∈ Finset.range k, d ω' (s - 1 - j % s) =
            ∑ u ∈ Finset.range s, d ω' u - ∑ u ∈ Finset.range (s - k), d ω' u := by
          have hsk_eq : (s - k) + k = s := by omega
          have hsplit : ∑ u ∈ Finset.range s, d ω' u =
              ∑ u ∈ Finset.range (s - k), d ω' u + ∑ j ∈ Finset.range k, d ω' ((s - k) + j) := by
            conv_lhs => rw [← hsk_eq, Finset.sum_range_add]
          rw [hsplit, add_sub_cancel_left]
          refine Finset.sum_bij (fun j _ => k - 1 - j) ?_ ?_ ?_ ?_
          · intro j hj; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
          · intro j1 hj1 j2 hj2 heq
            have h1 := Finset.mem_range.mp hj1; have h2 := Finset.mem_range.mp hj2; omega
          · intro u hu
            have hu' := Finset.mem_range.mp hu
            exact ⟨k - 1 - u, Finset.mem_range.mpr (by omega), by omega⟩
          · intro j hj
            have hj' := Finset.mem_range.mp hj
            rw [Nat.mod_eq_of_lt (by omega : j < s)]
            congr 1; omega
        dsimp [zrev]
        split_ifs with hab
        · rw [hsum_rev]; linarith
        · rw [Finset.sum_neg_distrib, hsum_rev]; linarith
      constructor
      · intro hgood t ht
        simp only [Finset.mem_Ico] at ht
        have hk : s - t ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hpos := hgood (s - t) hk
        simp only [zero_add] at hpos
        rw [hsum_rel (s - t) hk, show s - (s - t) = t by omega] at hpos
        split_ifs at hpos <;> omega
      · intro hne k hk
        simp only [zero_add]
        rw [hsum_rel k hk]
        have hstep_le : ∀ t < s,
            (if a < b then ((swapSet A ω' (t + 1) ∩ S).card : ℤ) ≤ ((swapSet A ω' t ∩ S).card : ℤ) + 1
             else ((swapSet A ω' t ∩ S).card : ℤ) - 1 ≤ ((swapSet A ω' (t + 1) ∩ S).card : ℤ)) := by
          intro t ht
          have h1 := hswap_inc ω' t (by omega)
          have h2 := hswap_inc ω' (t + 1) (by omega)
          rw [Finset.sum_range_succ] at h2
          have hbd := hd_bounds ω' t
          split_ifs <;> omega
        have h_strict : ∀ t ≤ s - 1,
            if a < b then ((swapSet A ω' t ∩ S).card : ℤ) < (b : ℤ)
            else (b : ℤ) < ((swapSet A ω' t ∩ S).card : ℤ) := by
          intro t ht
          induction t with
          | zero =>
            have h0 := hswap_inc ω' 0 (by omega)
            simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h0
            rw [h0]
            split_ifs with hab <;> omega
          | succ t iht =>
            have iht' := iht (by omega)
            have hst := hstep_le t (by omega)
            have hne_t : (swapSet A ω' (t + 1) ∩ S).card ≠ b :=
              hne (t + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
            split_ifs at iht' hst ⊢ <;> omega
        have h_sk := h_strict (s - k) (by have := (Finset.mem_Icc.mp hk).1; omega)
        split_ifs at h_sk ⊢ <;> omega
    rw [h0_iff]
    simp only [isFirstHit]
    constructor
    · intro hne
      refine ⟨hs1, hs_le, hω'b, fun t ht => hne t (Finset.mem_Ico.mpr ⟨by omega, (Finset.mem_Ico.mp ht).2⟩)⟩
    · rintro ⟨_, _, _, hne⟩ t ht
      simp only [Finset.mem_Ico] at ht
      rcases eq_or_lt_of_le ht.1 with rfl | ht1
      · have h0 := hswap_inc ω' 0 (by omega)
        simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h0
        omega
      · exact hne t (Finset.mem_Ico.mpr ⟨ht1, ht.2⟩)
  let Eb := Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b
  have hLHS : ∑ ω ∈ Eb, ∑ r ∈ Finset.range s,
      (if isFirstHit A S b (shift (s - r % s) ω) s then (1 : ℕ) else 0) =
      qnat * Eb.card := by
    have h_inner : ∀ ω ∈ Eb,
        ∑ r ∈ Finset.range s, (if isFirstHit A S b (shift (s - r % s) ω) s then (1 : ℕ) else 0) = qnat := by
      intro ω hω
      have hωb : (swapSet A ω s ∩ S).card = b := (Finset.mem_filter.mp hω).2
      have hcongr : ∑ r ∈ Finset.range s, (if isFirstHit A S b (shift (s - r % s) ω) s then (1 : ℕ) else 0) =
          ∑ r ∈ Finset.range s, (if isGoodStart s (zrev ω) r then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [if_congr (hgood_iff_first ω r hωb).symm rfl rfl]
      rw [hcongr, ← Finset.card_filter]
      have hpos_q : 0 < ∑ i ∈ Finset.range s, zrev ω i := by
        rw [hzrev_sum ω hωb]; exact_mod_cast hq_pos
      have hcl := cycle_lemma hs1 (zrev ω) (hzrev_per ω) (hzrev_le ω) hpos_q
      rw [hzrev_sum ω hωb] at hcl
      simpa using hcl
    rw [Finset.sum_congr rfl h_inner, Finset.sum_const, smul_eq_mul, mul_comm]
  have hRHS : ∑ r ∈ Finset.range s, ∑ ω ∈ Eb,
      (if isFirstHit A S b (shift (s - r % s) ω) s then (1 : ℕ) else 0) =
      s * (Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card := by
    have h_inner : ∀ r ∈ Finset.range s,
        ∑ ω ∈ Eb, (if isFirstHit A S b (shift (s - r % s) ω) s then (1 : ℕ) else 0) =
          (Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card := by
      intro r _
      rw [← Finset.card_filter]
      refine Finset.card_bij (fun ω _ => shift (s - r % s) ω) ?_ ?_ ?_
      · intro ω hω
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2⟩
      · intro ω1 _ ω2 _ heq
        exact (shift (s - r % s)).injective heq
      · intro ω' hω'
        have hfirst : isFirstHit A S b ω' s := (Finset.mem_filter.mp hω').2
        refine ⟨(shift (s - r % s)).symm ω', Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have := hshift_swap (s - r % s) ((shift (s - r % s)).symm ω')
          simp only [Equiv.apply_symm_apply] at this
          rw [← this]
          exact hfirst.2.2.1
        · simp [hfirst]
        · simp
    rw [Finset.sum_congr rfl h_inner, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [← hLHS, Finset.sum_comm, hRHS]

lemma fiber_gamma_le {n m : ℕ} {U : Finset (Fin n)} (hU : U.card = 2 * m) (_hm : 1 ≤ m)
    (A : Fam U m) (S : Finset (Fin n)) (b : ℕ) (hb : b ≠ (A.1 ∩ S).card) :
    ∑ B ∈ Finset.univ.filter (fun B : Fam U m => (B.1 ∩ S).card = b), gamma A B ≤
      1 / ((Int.natAbs ((b : ℤ) - ((A.1 ∩ S).card : ℤ)) : ℕ) : ℝ) := by
  classical
  set a : ℕ := (A.1 ∩ S).card
  set qnat : ℕ := Int.natAbs ((b : ℤ) - (a : ℤ))
  have hq_pos : 1 ≤ qnat := by omega
  have hΩ_card : Fintype.card (SwapΩ m U A.1) = m.factorial * m.factorial := swapOmega_card hU A
  have hΩ_pos : 0 < Fintype.card (SwapΩ m U A.1) := by rw [hΩ_card]; positivity
  let Lb := Finset.univ.filter (fun B : Fam U m => (B.1 ∩ S).card = b)
  have hmaps_Lb : ∀ B ∈ Lb, (A.1 \ B.1).card ∈ Finset.Icc 1 m := by
    intro B hB
    have hb_eq : (B.1 ∩ S).card = b := (Finset.mem_filter.mp hB).2
    have hAB : A ≠ B := fun heq => hb (by subst heq; exact hb_eq.symm)
    exact Finset.mem_Icc.mpr (sdiff_card_bounds hAB)
  have hsum_split : ∑ B ∈ Lb, gamma A B =
      ∑ s ∈ Finset.Icc 1 m,
        ((Lb.filter fun B : Fam U m => (A.1 \ B.1).card = s).card : ℝ) /
          ((s : ℝ) * ((m.choose s : ℕ) : ℝ) ^ 2) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps_Lb (fun B => gamma A B)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hconst : ∀ B ∈ Lb.filter (fun B : Fam U m => (A.1 \ B.1).card = s),
        gamma A B = 1 / ((s : ℝ) * ((m.choose s : ℕ) : ℝ) ^ 2) := by
      intro B hB
      have hB' := Finset.mem_filter.mp hB
      have hb_eq : (B.1 ∩ S).card = b := (Finset.mem_filter.mp hB'.1).2
      have hAB : A ≠ B := fun heq => hb (by subst heq; exact hb_eq.symm)
      simp [gamma, hAB, hB'.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum_split]
  have hterm_eq : ∀ s ∈ Finset.Icc 1 m,
      ((Lb.filter fun B : Fam U m => (A.1 \ B.1).card = s).card : ℝ) /
        ((s : ℝ) * ((m.choose s : ℕ) : ℝ) ^ 2) =
      ((Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b).card : ℝ) /
        ((s : ℝ) * (Fintype.card (SwapΩ m U A.1) : ℝ)) := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    have hs_le : s ≤ m := hs.2
    have hΩ_count : (Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b).card =
        (Lb.filter fun B : Fam U m => (A.1 \ B.1).card = s).card *
          (s.factorial * (m - s).factorial) ^ 2 := by
      have hsub_maps : ∀ ω ∈ Finset.univ.filter (fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b),
          ∃ B : Fam U m, B.1 = swapSet A ω s := by
        intro ω _
        have hmem := swapSet_mem_fam A ω hs_le
        exact ⟨⟨swapSet A ω s, hmem.1, hmem.2⟩, rfl⟩
      have hcard_fiber : ∀ B ∈ Lb.filter (fun B : Fam U m => (A.1 \ B.1).card = s),
          (Finset.univ.filter fun ω : SwapΩ m U A.1 => swapSet A ω s = B.1).card =
            (s.factorial * (m - s).factorial) ^ 2 := by
        intro B hB
        exact swapSet_count_eq hU A hs_le B (Finset.mem_filter.mp hB).2
      have hsum_B : (Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b).card =
          ∑ B ∈ Lb.filter (fun B : Fam U m => (A.1 \ B.1).card = s),
            (Finset.univ.filter fun ω : SwapΩ m U A.1 => swapSet A ω s = B.1).card := by
        have hpart : (Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b) =
            (Lb.filter fun B : Fam U m => (A.1 \ B.1).card = s).biUnion
              (fun B => Finset.univ.filter fun ω : SwapΩ m U A.1 => swapSet A ω s = B.1) := by
          ext ω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Lb]
          constructor
          · intro hω
            obtain ⟨B, hB⟩ := hsub_maps ω (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩)
            refine ⟨B, ⟨⟨?_, ?_⟩, hB.symm⟩⟩
            · rw [hB]; exact hω
            · rw [hB, swapSet_sdiff A ω s, prefA_card ω.1 hs_le]
          · rintro ⟨B, ⟨hB1, _⟩, hB2⟩
            rw [hB2]; exact hB1
        rw [hpart, Finset.card_biUnion]
        intro B1 _ B2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro ω h1 h2
        apply hne
        apply Subtype.ext
        rw [← (Finset.mem_filter.mp h1).2, ← (Finset.mem_filter.mp h2).2]
      rw [hsum_B, Finset.sum_congr rfl hcard_fiber, Finset.sum_const, smul_eq_mul]
    have hcomb : m.choose s * (s.factorial * (m - s).factorial) = m.factorial := by
      have := Nat.choose_mul_factorial_mul_factorial hs_le
      linarith
    have hcomb_sq : (m.choose s) ^ 2 * (s.factorial * (m - s).factorial) ^ 2 =
        Fintype.card (SwapΩ m U A.1) := by
      rw [hΩ_card]
      calc (m.choose s) ^ 2 * (s.factorial * (m - s).factorial) ^ 2
          = (m.choose s * (s.factorial * (m - s).factorial)) ^ 2 := by ring
        _ = m.factorial ^ 2 := by rw [hcomb]
        _ = m.factorial * m.factorial := by ring
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    have hden_pos : (0 : ℝ) < ((s.factorial * (m - s).factorial : ℕ) : ℝ) ^ 2 := by positivity
    have hΩ_pos_r : (0 : ℝ) < (Fintype.card (SwapΩ m U A.1) : ℝ) := by exact_mod_cast hΩ_pos
    have hch_pos : (0 : ℝ) < ((m.choose s : ℕ) : ℝ) ^ 2 := by
      have := Nat.choose_pos hs_le; positivity
    have hnum_r : (((Lb.filter fun B : Fam U m => (A.1 \ B.1).card = s).card *
        (s.factorial * (m - s).factorial) ^ 2 : ℕ) : ℝ) =
        ((Lb.filter fun B : Fam U m => (A.1 \ B.1).card = s).card : ℝ) *
          (((s.factorial * (m - s).factorial : ℕ) : ℝ) ^ 2) := by
      push_cast; rfl
    have hcomb_r : ((m.choose s : ℕ) : ℝ) ^ 2 * (((s.factorial * (m - s).factorial : ℕ) : ℝ) ^ 2) =
        (Fintype.card (SwapΩ m U A.1) : ℝ) := by exact_mod_cast hcomb_sq
    rw [hΩ_count, hnum_r, ← hcomb_r]
    field_simp
  rw [Finset.sum_congr rfl hterm_eq]
  have hsum_real : ∑ s ∈ Finset.Icc 1 m,
      ((Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b).card : ℝ) /
        ((s : ℝ) * (Fintype.card (SwapΩ m U A.1) : ℝ)) =
      (1 / ((qnat : ℝ) * (Fintype.card (SwapΩ m U A.1) : ℝ))) *
        ∑ s ∈ Finset.Icc 1 m, ((Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [Finset.mem_Icc] at hs
    have hc := swapSet_cycle_count A S b hb hs.1 hs.2
    have hc_r : (qnat : ℝ) * ((Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b).card : ℝ) =
        (s : ℝ) * ((Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card : ℝ) := by
      have hc' : ((Int.natAbs ((b : ℤ) - ((A.1 ∩ S).card : ℤ)) : ℕ) : ℝ) *
          ((Finset.univ.filter fun ω : SwapΩ m U A.1 => (swapSet A ω s ∩ S).card = b).card : ℝ) =
          (s : ℝ) * ((Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card : ℝ) := by
        exact_mod_cast hc
      simpa [qnat, a] using hc'
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    have hq_r : (0 : ℝ) < (qnat : ℝ) := by exact_mod_cast hq_pos
    have hΩ_r : (0 : ℝ) < (Fintype.card (SwapΩ m U A.1) : ℝ) := by exact_mod_cast hΩ_pos
    field_simp
    linarith
  rw [hsum_real]
  have hdisj_hits : (∑ s ∈ Finset.Icc 1 m,
      (Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card) ≤ Fintype.card (SwapΩ m U A.1) := by
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_univ _
    · intro s1 _ s2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro ω h1 h2
      have hf1 := (Finset.mem_filter.mp h1).2
      have hf2 := (Finset.mem_filter.mp h2).2
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hf2.2.2.2 s1 (Finset.mem_Ico.mpr ⟨hf1.1, hlt⟩) hf1.2.2.1
      · exact hf1.2.2.2 s2 (Finset.mem_Ico.mpr ⟨hf2.1, hlt⟩) hf2.2.2.1
  have hsum_le_Ω : ∑ s ∈ Finset.Icc 1 m,
      ((Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card : ℝ) ≤
      (Fintype.card (SwapΩ m U A.1) : ℝ) := by
    exact_mod_cast hdisj_hits
  have hq_r : (0 : ℝ) < (qnat : ℝ) := by exact_mod_cast hq_pos
  have hΩ_r : (0 : ℝ) < (Fintype.card (SwapΩ m U A.1) : ℝ) := by exact_mod_cast hΩ_pos
  calc (1 / ((qnat : ℝ) * (Fintype.card (SwapΩ m U A.1) : ℝ))) *
        ∑ s ∈ Finset.Icc 1 m, ((Finset.univ.filter fun ω : SwapΩ m U A.1 => isFirstHit A S b ω s).card : ℝ)
      ≤ (1 / ((qnat : ℝ) * (Fintype.card (SwapΩ m U A.1) : ℝ))) * (Fintype.card (SwapΩ m U A.1) : ℝ) := by
        gcongr
    _ = 1 / (qnat : ℝ) := by field_simp

lemma schur_step_bound {n c0 m : ℕ} (hm : 1 ≤ m) {C U : Finset (Fin n)}
    (hCU : Disjoint C U) (hC : C.card = c0) (hU : U.card = 2 * m)
    (S : Finset (Fin n)) (v : Fam U m → ℝ) (_hv : ∀ A, 0 ≤ v A) :
    ∑ A : Fam U m, ∑ B : Fam U m,
      (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * v A * v B else 0) ≤
      4 * ∑ A : Fam U m, (v A) ^ 2 := by
  classical
  set cS : ℕ := (C ∩ S).card
  set r : ℤ := (((c0 + m + 1) / 2 : ℕ) : ℤ) - (cS : ℤ)
  have hmaj_iff : ∀ A : Fam U m, majJunta (C ∪ A.1) S = 1 ↔ r ≤ ((A.1 ∩ S).card : ℤ) := by
    intro A
    have hdisjA : Disjoint C A.1 := Finset.disjoint_of_subset_right A.2.1 hCU
    have hcard_tot : (C ∪ A.1).card = c0 + m := by
      rw [Finset.card_union_of_disjoint hdisjA, hC, A.2.2]
    have hcard_inter : ((C ∪ A.1) ∩ S).card = cS + (A.1 ∩ S).card := by
      rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
      exact Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hdisjA)
    unfold majJunta
    rw [hcard_tot, hcard_inter]
    split_ifs with h
    · constructor <;> intro _ <;> [omega; rfl]
    · constructor
      · intro h1; exfalso; norm_num at h1
      · intro h2; exfalso; apply h; omega
  have hmaj_ne_iff : ∀ A B : Fam U m,
      majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S ↔
      (((A.1 ∩ S).card : ℤ) < r ∧ r ≤ ((B.1 ∩ S).card : ℤ)) ∨
      (((B.1 ∩ S).card : ℤ) < r ∧ r ≤ ((A.1 ∩ S).card : ℤ)) := by
    intro A B
    have hA1 : majJunta (C ∪ A.1) S = 1 ∨ majJunta (C ∪ A.1) S = -1 := by
      unfold majJunta; split_ifs <;> simp
    have hB1 : majJunta (C ∪ B.1) S = 1 ∨ majJunta (C ∪ B.1) S = -1 := by
      unfold majJunta; split_ifs <;> simp
    have hA_iff := hmaj_iff A
    have hB_iff := hmaj_iff B
    rcases hA1 with hA | hA <;> rcases hB1 with hB | hB
    · rw [hA, hB]
      constructor
      · intro h; exact absurd rfl h
      · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · have := hA_iff.mp hA; omega
        · have := hB_iff.mp hB; omega
    · have hAr := hA_iff.mp hA
      have hBr : ((B.1 ∩ S).card : ℤ) < r := by
        by_contra hc; push Not at hc; have := hB_iff.mpr hc; rw [this] at hB; norm_num at hB
      rw [hA, hB]
      constructor
      · intro _; exact Or.inr ⟨hBr, hAr⟩
      · intro _; norm_num
    · have hBr := hB_iff.mp hB
      have hAr : ((A.1 ∩ S).card : ℤ) < r := by
        by_contra hc; push Not at hc; have := hA_iff.mpr hc; rw [this] at hA; norm_num at hA
      rw [hA, hB]
      constructor
      · intro _; exact Or.inl ⟨hAr, hBr⟩
      · intro _; norm_num
    · rw [hA, hB]
      constructor
      · intro h; exact absurd rfl h
      · rintro (⟨_, h2⟩ | ⟨_, h2⟩)
        · have := hB_iff.mpr h2; rw [this] at hB; norm_num at hB
        · have := hA_iff.mpr h2; rw [this] at hA; norm_num at hA
  let w (A : Fam U m) : ℝ :=
    let a : ℤ := ((A.1 ∩ S).card : ℤ)
    if a < r then 1 / Real.sqrt (Int.natAbs (r - a))
    else 1 / Real.sqrt (Int.natAbs (a - r + 1))
  have hw_pos : ∀ A : Fam U m, 0 < w A := by
    intro A
    dsimp [w]
    split_ifs with h
    · have h1 : 0 < Int.natAbs (r - ((A.1 ∩ S).card : ℤ)) := by omega
      positivity
    · have h1 : 0 < Int.natAbs (((A.1 ∩ S).card : ℤ) - r + 1) := by omega
      positivity
  have hrow : ∀ A : Fam U m,
      ∑ B : Fam U m, (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * w B else 0) ≤
        4 * w A := by
    intro A
    set a : ℕ := (A.1 ∩ S).card
    set N : ℕ := m + Int.natAbs r + 1
    by_cases ha : (a : ℤ) < r
    · set i : ℕ := Int.natAbs (r - (a : ℤ))
      have hi_pos : 1 ≤ i := by omega
      have hwA_eq : w A = 1 / Real.sqrt i := by dsimp [w]; rw [if_pos ha]
      let FA := Finset.univ.filter fun B : Fam U m => majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S
      have h_filt : ∑ B : Fam U m,
          (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * w B else 0) =
          ∑ B ∈ FA, gamma A B * w B := by
        rw [← Finset.sum_filter]
      rw [h_filt]
      have hmaps : ∀ B ∈ FA, Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) ∈ Finset.Icc 1 N := by
        intro B hB
        have hne := (Finset.mem_filter.mp hB).2
        have hAB := (hmaj_ne_iff A B).mp hne
        have hBr : r ≤ ((B.1 ∩ S).card : ℤ) := by
          rcases hAB with ⟨_, h2⟩ | ⟨_, h2⟩
          · exact h2
          · exfalso; omega
        have hBm : (B.1 ∩ S).card ≤ m := by
          calc (B.1 ∩ S).card ≤ B.1.card := Finset.card_le_card Finset.inter_subset_left
            _ = m := B.2.2
        rw [Finset.mem_Icc]
        omega
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun B => gamma A B * w B)]
      have hfiber_le : ∀ j ∈ Finset.Icc 1 N,
          ∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) = j),
            gamma A B * w B ≤
          (1 / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j)) := by
        intro j hj
        simp only [Finset.mem_Icc] at hj
        set b_int : ℤ := r + (j : ℤ) - 1
        by_cases hb0 : b_int < 0
        · have hempty : FA.filter (fun B : Fam U m => Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) = j) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro B hB
            have hB' := Finset.mem_filter.mp hB
            have hne := (Finset.mem_filter.mp hB'.1).2
            have hBr : r ≤ ((B.1 ∩ S).card : ℤ) := by
              rcases (hmaj_ne_iff A B).mp hne with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact h2
              · exfalso; omega
            omega
          rw [hempty, Finset.sum_empty]
          positivity
        · set b : ℕ := b_int.toNat
          have hb_eq : (b : ℤ) = b_int := by omega
          have hba : b ≠ a := by omega
          have hsub : FA.filter (fun B : Fam U m => Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) = j) ⊆
              Finset.univ.filter (fun B : Fam U m => (B.1 ∩ S).card = b) := by
            intro B hB
            have hB' := Finset.mem_filter.mp hB
            have hne := (Finset.mem_filter.mp hB'.1).2
            have hBr : r ≤ ((B.1 ∩ S).card : ℤ) := by
              rcases (hmaj_ne_iff A B).mp hne with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact h2
              · exfalso; omega
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            omega
          have hw_eq : ∀ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) = j),
              gamma A B * w B = gamma A B * (1 / Real.sqrt j) := by
            intro B hB
            have hB' := Finset.mem_filter.mp hB
            have hne := (Finset.mem_filter.mp hB'.1).2
            have hBr : r ≤ ((B.1 ∩ S).card : ℤ) := by
              rcases (hmaj_ne_iff A B).mp hne with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact h2
              · exfalso; omega
            have hwB : w B = 1 / Real.sqrt j := by
              dsimp [w]
              rw [if_neg (by omega), hB'.2]
            rw [hwB]
          rw [Finset.sum_congr rfl hw_eq, ← Finset.sum_mul]
          have hle1 : ∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) = j),
              gamma A B ≤
              ∑ B ∈ Finset.univ.filter (fun B : Fam U m => (B.1 ∩ S).card = b), gamma A B :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun B _ _ => gamma_nonneg A B)
          have hle2 := fiber_gamma_le hU hm A S b hba
          have hdiff : Int.natAbs ((b : ℤ) - (a : ℤ)) = i + j - 1 := by omega
          rw [hdiff] at hle2
          have hle3 := le_trans hle1 hle2
          calc (∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) = j),
                gamma A B) * (1 / Real.sqrt j)
              ≤ (1 / ((i + j - 1 : ℕ) : ℝ)) * (1 / Real.sqrt j) :=
                mul_le_mul_of_nonneg_right hle3 (by positivity)
            _ = 1 / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) := by ring
      calc ∑ j ∈ Finset.Icc 1 N,
            ∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (((B.1 ∩ S).card : ℤ) - r + 1) = j),
              gamma A B * w B
          ≤ ∑ j ∈ Finset.Icc 1 N, 1 / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) :=
            Finset.sum_le_sum hfiber_le
        _ ≤ 4 / Real.sqrt i := weighted_harmonic_sum_bound i N hi_pos
        _ = 4 * w A := by rw [hwA_eq]; ring
    · push Not at ha
      set i : ℕ := Int.natAbs ((a : ℤ) - r + 1)
      have hi_pos : 1 ≤ i := by omega
      have hwA_eq : w A = 1 / Real.sqrt i := by dsimp [w]; rw [if_neg (by omega)]
      let FA := Finset.univ.filter fun B : Fam U m => majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S
      have h_filt : ∑ B : Fam U m,
          (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * w B else 0) =
          ∑ B ∈ FA, gamma A B * w B := by
        rw [← Finset.sum_filter]
      rw [h_filt]
      have hmaps : ∀ B ∈ FA, Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) ∈ Finset.Icc 1 N := by
        intro B hB
        have hne := (Finset.mem_filter.mp hB).2
        have hAB := (hmaj_ne_iff A B).mp hne
        have hBr : ((B.1 ∩ S).card : ℤ) < r := by
          rcases hAB with ⟨h1, _⟩ | ⟨h1, _⟩
          · exfalso; omega
          · exact h1
        rw [Finset.mem_Icc]
        omega
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun B => gamma A B * w B)]
      have hfiber_le : ∀ j ∈ Finset.Icc 1 N,
          ∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) = j),
            gamma A B * w B ≤
          (1 / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j)) := by
        intro j hj
        simp only [Finset.mem_Icc] at hj
        set b_int : ℤ := r - (j : ℤ)
        by_cases hb0 : b_int < 0
        · have hempty : FA.filter (fun B : Fam U m => Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) = j) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro B hB
            have hB' := Finset.mem_filter.mp hB
            have hne := (Finset.mem_filter.mp hB'.1).2
            have hBr : ((B.1 ∩ S).card : ℤ) < r := by
              rcases (hmaj_ne_iff A B).mp hne with ⟨h1, _⟩ | ⟨h1, _⟩
              · exfalso; omega
              · exact h1
            omega
          rw [hempty, Finset.sum_empty]
          positivity
        · set b : ℕ := b_int.toNat
          have hb_eq : (b : ℤ) = b_int := by omega
          have hba : b ≠ a := by omega
          have hsub : FA.filter (fun B : Fam U m => Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) = j) ⊆
              Finset.univ.filter (fun B : Fam U m => (B.1 ∩ S).card = b) := by
            intro B hB
            have hB' := Finset.mem_filter.mp hB
            have hne := (Finset.mem_filter.mp hB'.1).2
            have hBr : ((B.1 ∩ S).card : ℤ) < r := by
              rcases (hmaj_ne_iff A B).mp hne with ⟨h1, _⟩ | ⟨h1, _⟩
              · exfalso; omega
              · exact h1
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            omega
          have hw_eq : ∀ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) = j),
              gamma A B * w B = gamma A B * (1 / Real.sqrt j) := by
            intro B hB
            have hB' := Finset.mem_filter.mp hB
            have hne := (Finset.mem_filter.mp hB'.1).2
            have hBr : ((B.1 ∩ S).card : ℤ) < r := by
              rcases (hmaj_ne_iff A B).mp hne with ⟨h1, _⟩ | ⟨h1, _⟩
              · exfalso; omega
              · exact h1
            have hwB : w B = 1 / Real.sqrt j := by
              dsimp [w]
              rw [if_pos hBr, hB'.2]
            rw [hwB]
          rw [Finset.sum_congr rfl hw_eq, ← Finset.sum_mul]
          have hle1 : ∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) = j),
              gamma A B ≤
              ∑ B ∈ Finset.univ.filter (fun B : Fam U m => (B.1 ∩ S).card = b), gamma A B :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun B _ _ => gamma_nonneg A B)
          have hle2 := fiber_gamma_le hU hm A S b hba
          have hdiff : Int.natAbs ((b : ℤ) - (a : ℤ)) = i + j - 1 := by omega
          rw [hdiff] at hle2
          have hle3 := le_trans hle1 hle2
          calc (∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) = j),
                gamma A B) * (1 / Real.sqrt j)
              ≤ (1 / ((i + j - 1 : ℕ) : ℝ)) * (1 / Real.sqrt j) :=
                mul_le_mul_of_nonneg_right hle3 (by positivity)
            _ = 1 / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) := by ring
      calc ∑ j ∈ Finset.Icc 1 N,
            ∑ B ∈ FA.filter (fun B : Fam U m => Int.natAbs (r - ((B.1 ∩ S).card : ℤ)) = j),
              gamma A B * w B
          ≤ ∑ j ∈ Finset.Icc 1 N, 1 / (((i + j - 1 : ℕ) : ℝ) * Real.sqrt j) :=
            Finset.sum_le_sum hfiber_le
        _ ≤ 4 / Real.sqrt i := weighted_harmonic_sum_bound i N hi_pos
        _ = 4 * w A := by rw [hwA_eq]; ring
  have hpoint : ∀ A B : Fam U m,
      (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * v A * v B else 0) ≤
      (1 / 2 : ℝ) *
        ((if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
            gamma A B * (w B / w A) * (v A) ^ 2 else 0) +
         (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
            gamma A B * (w A / w B) * (v B) ^ 2 else 0)) := by
    intro A B
    split_ifs with h
    · have hwA := hw_pos A
      have hwB := hw_pos B
      have hg := gamma_nonneg A B
      have hsq : 0 ≤ (w B * v A - w A * v B) ^ 2 := sq_nonneg _
      have h2 : v A * v B ≤ (1 / 2 : ℝ) * ((w B / w A) * (v A) ^ 2 + (w A / w B) * (v B) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hpos : 0 < w A * w B := mul_pos hwA hwB
        have hmul : (w A * w B) * (v A * v B) ≤
            (w A * w B) * ((1 / 2 : ℝ) * ((w B * (w A)⁻¹) * (v A) ^ 2 + (w A * (w B)⁻¹) * (v B) ^ 2)) := by
          have hexp : (w A * w B) * ((1 / 2 : ℝ) * ((w B * (w A)⁻¹) * (v A) ^ 2 + (w A * (w B)⁻¹) * (v B) ^ 2)) =
              (1 / 2 : ℝ) * ((w B * v A) ^ 2 + (w A * v B) ^ 2) := by
            field_simp
          rw [hexp]
          nlinarith only [hsq]
        exact le_of_mul_le_mul_left hmul hpos
      calc gamma A B * v A * v B = gamma A B * (v A * v B) := by ring
        _ ≤ gamma A B * ((1 / 2 : ℝ) * ((w B / w A) * (v A) ^ 2 + (w A / w B) * (v B) ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 hg
        _ = (1 / 2 : ℝ) * (gamma A B * (w B / w A) * (v A) ^ 2 + gamma A B * (w A / w B) * (v B) ^ 2) := by
            ring
    · norm_num
  calc ∑ A : Fam U m, ∑ B : Fam U m,
        (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * v A * v B else 0)
      ≤ ∑ A : Fam U m, ∑ B : Fam U m, (1 / 2 : ℝ) *
          ((if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
              gamma A B * (w B / w A) * (v A) ^ 2 else 0) +
           (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
              gamma A B * (w A / w B) * (v B) ^ 2 else 0)) :=
        Finset.sum_le_sum fun A _ => Finset.sum_le_sum fun B _ => hpoint A B
    _ = (1 / 2 : ℝ) *
          ((∑ A : Fam U m, ∑ B : Fam U m,
              if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
                gamma A B * (w B / w A) * (v A) ^ 2 else 0) +
           (∑ A : Fam U m, ∑ B : Fam U m,
              if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
                gamma A B * (w A / w B) * (v B) ^ 2 else 0)) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ A : Fam U m, ((v A) ^ 2 / w A) *
          ∑ B : Fam U m, (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * w B else 0) := by
          have hsymm_sum :
              (∑ A : Fam U m, ∑ B : Fam U m,
                if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
                  gamma A B * (w A / w B) * (v B) ^ 2 else 0) =
              ∑ B : Fam U m, ∑ A : Fam U m,
                if majJunta (C ∪ B.1) S ≠ majJunta (C ∪ A.1) S then
                  gamma B A * (w A / w B) * (v B) ^ 2 else 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
            by_cases hAB : majJunta (C ∪ A.1) S = majJunta (C ∪ B.1) S
            · have hBA : majJunta (C ∪ B.1) S = majJunta (C ∪ A.1) S := hAB.symm
              rw [if_neg (not_not.mpr hAB), if_neg (not_not.mpr hBA)]
            · rw [if_pos hAB, if_pos (Ne.symm hAB), gamma_symm A B]
          rw [hsymm_sum]
          have hfactor : ∀ A : Fam U m,
              (∑ B : Fam U m,
                if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
                  gamma A B * (w B / w A) * (v A) ^ 2 else 0) =
              ((v A) ^ 2 / w A) *
                ∑ B : Fam U m,
                  if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then gamma A B * w B else 0 := by
            intro A
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun B _ => ?_
            split_ifs <;> ring
          simp_rw [hfactor]
          ring
    _ ≤ ∑ A : Fam U m, ((v A) ^ 2 / w A) * (4 * w A) := by
          refine Finset.sum_le_sum fun A _ => ?_
          exact mul_le_mul_of_nonneg_left (hrow A) (by positivity)
    _ = 4 * ∑ A : Fam U m, (v A) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun A _ => ?_
          have hwA := hw_pos A
          field_simp

def querySet {n qNum : ℕ} (wires : Fin (n + 1) ↪ Fin qNum) (z : Qubits qNum) : Finset (Fin n) :=
  Finset.univ.filter fun i => z (wires (Fin.castSucc i)) = true

def stepPerm {n qNum : ℕ} (ctrl : Option (Fin qNum)) (wires : Fin (n + 1) ↪ Fin qNum)
    (H : Finset (Fin n)) (z : Qubits qNum) : Qubits qNum :=
  Function.update z (wires (Fin.last n))
    (xor (z (wires (Fin.last n)))
      ((match ctrl with | none => true | some c => z c) &&
        decide (majJunta H (querySet wires z) = -1)))

lemma querySet_stepPerm {n qNum : ℕ} (ctrl : Option (Fin qNum)) (wires : Fin (n + 1) ↪ Fin qNum)
    (H : Finset (Fin n)) (z : Qubits qNum) :
    querySet wires (stepPerm ctrl wires H z) = querySet wires z := by
  ext i
  simp only [querySet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : wires (Fin.castSucc i) ≠ wires (Fin.last n) := by
    intro h
    have := wires.injective h
    exact (Fin.castSucc_lt_last i).ne this
  dsimp only [stepPerm]
  rw [Function.update_of_ne hne]

lemma stepPerm_invol {n qNum : ℕ} (ctrl : Option (Fin qNum)) (wires : Fin (n + 1) ↪ Fin qNum)
    (hc : ∀ c, ctrl = some c → c ∉ Set.range wires)
    (H : Finset (Fin n)) (z : Qubits qNum) :
    stepPerm ctrl wires H (stepPerm ctrl wires H z) = z := by
  cases ctrl with
  | none =>
    let z1 : Qubits qNum := stepPerm none wires H z
    have hq : querySet wires z1 = querySet wires z := querySet_stepPerm none wires H z
    have hdec : decide (majJunta H (querySet wires z1) = -1) =
        decide (majJunta H (querySet wires z) = -1) := by simp only [hq]
    have hz1_upd : z1 = Function.update z (wires (Fin.last n))
        (xor (z (wires (Fin.last n))) (true && decide (majJunta H (querySet wires z) = -1))) := rfl
    have hlast : z1 (wires (Fin.last n)) =
        xor (z (wires (Fin.last n))) (true && decide (majJunta H (querySet wires z) = -1)) := by
      simp [hz1_upd]
    have hstep2 : stepPerm none wires H z1 = Function.update z1 (wires (Fin.last n))
        (xor (z1 (wires (Fin.last n))) (true && decide (majJunta H (querySet wires z1) = -1))) := rfl
    rw [hstep2, hdec, hlast, hz1_upd, Function.update_idem, Bool.xor_assoc, Bool.xor_self,
      Bool.xor_false, Function.update_eq_self]
  | some c =>
    have hne : c ≠ wires (Fin.last n) := fun h => hc c rfl ⟨Fin.last n, h.symm⟩
    let z1 : Qubits qNum := stepPerm (some c) wires H z
    have hq : querySet wires z1 = querySet wires z := querySet_stepPerm (some c) wires H z
    have hdec : decide (majJunta H (querySet wires z1) = -1) =
        decide (majJunta H (querySet wires z) = -1) := by simp only [hq]
    have hz1_upd : z1 = Function.update z (wires (Fin.last n))
        (xor (z (wires (Fin.last n))) (z c && decide (majJunta H (querySet wires z) = -1))) := rfl
    have hc_eq : z1 c = z c := by simp [hz1_upd, Function.update_of_ne hne]
    have hlast : z1 (wires (Fin.last n)) =
        xor (z (wires (Fin.last n))) (z c && decide (majJunta H (querySet wires z) = -1)) := by
      simp [hz1_upd]
    have hstep2 : stepPerm (some c) wires H z1 = Function.update z1 (wires (Fin.last n))
        (xor (z1 (wires (Fin.last n))) (z1 c && decide (majJunta H (querySet wires z1) = -1))) := rfl
    rw [hstep2, hc_eq, hdec, hlast, hz1_upd, Function.update_idem, Bool.xor_assoc, Bool.xor_self,
      Bool.xor_false, Function.update_eq_self]

lemma query_step_eq_invMat {n qNum : ℕ} (k : Fin 1) (adj : Bool) (ctrl : Option (Fin qNum))
    (wires : Fin (n + 1) ↪ Fin qNum) (hc : ∀ c, ctrl = some c → c ∉ Set.range wires)
    (H : Finset (Fin n)) :
    OracleStep.mat (S := {g : Gate | g.IsUnitary}) (r := 1) (a := fun _ => n + 1) (n := qNum)
        (fun _ => majOracle H) (.query k adj ctrl wires hc) =
      Matrix.of (fun y z => if y = stepPerm ctrl wires H z then 1 else 0) := by
  have hk0 : k = 0 := Subsingleton.elim k 0
  subst hk0
  have hadj : (if adj then star (majOracle H) else majOracle H) = majOracle H := by
    cases adj <;> simp [majOracle_star]
  have h_querySet_init : ∀ z : Qubits qNum,
      (Finset.univ.filter fun i : Fin n => Fin.init (z ∘ wires) i = true) = querySet wires z := by
    intro z; ext i; rfl
  cases ctrl with
  | none =>
    simp only [OracleStep.mat, hadj, embedOp]
    ext y z
    rw [Matrix.of_apply, Matrix.of_apply]
    have hiff : ((∀ a ∉ Set.range wires, y a = z a) ∧
        majOracle H (y ∘ wires) (z ∘ wires) = 1) ↔ y = stepPerm none wires H z := by
      rw [majOracle_eq_invMat, invMat, Matrix.of_apply]
      have h_eq1 : (if y ∘ wires = majToggle H (z ∘ wires) then (1 : ℂ) else 0) = 1 ↔
          y ∘ wires = majToggle H (z ∘ wires) := by split_ifs <;> simp [*]
      rw [h_eq1]
      constructor
      · rintro ⟨h1, h2⟩
        funext a
        by_cases ha_last : a = wires (Fin.last n)
        · subst ha_last
          have hval := congrFun h2 (Fin.last n)
          dsimp [majToggle] at hval
          rw [Fin.snoc_last] at hval
          simp [stepPerm, hval, h_querySet_init]
        · have h_upd : stepPerm none wires H z a = z a := by
            simp [stepPerm, Function.update_of_ne ha_last]
          rw [h_upd]
          by_cases ha_range : a ∈ Set.range wires
          · obtain ⟨b, hb⟩ := ha_range
            revert hb
            refine Fin.lastCases ?_ ?_ b
            · intro h; exact absurd h.symm ha_last
            · intro i hb
              have hval := congrFun h2 (Fin.castSucc i)
              dsimp [majToggle] at hval
              rw [Fin.snoc_castSucc] at hval
              change y (wires (Fin.castSucc i)) = z (wires (Fin.castSucc i)) at hval
              rw [← hb]; exact hval
          · exact h1 a ha_range
      · intro hy
        subst hy
        refine ⟨fun a ha => ?_, ?_⟩
        · have hne : a ≠ wires (Fin.last n) := fun h => ha ⟨Fin.last n, h.symm⟩
          simp [stepPerm, Function.update_of_ne hne]
        · funext b
          refine Fin.lastCases ?_ ?_ b
          · dsimp [majToggle, stepPerm]
            rw [Fin.snoc_last]
            simp [h_querySet_init]
          · intro i
            dsimp [majToggle, stepPerm]
            rw [Fin.snoc_castSucc]
            have hne : wires (Fin.castSucc i) ≠ wires (Fin.last n) :=
              fun h => (Fin.castSucc_lt_last i).ne (wires.injective h)
            change Function.update z (wires (Fin.last n)) _ (wires (Fin.castSucc i)) =
              z (wires (Fin.castSucc i))
            rw [Function.update_of_ne hne]
    by_cases hy : y = stepPerm none wires H z
    · have h12 := hiff.mpr hy
      rw [if_pos hy, if_pos h12.1, h12.2]
    · rw [if_neg hy]
      by_cases h1 : ∀ a ∉ Set.range wires, y a = z a
      · rw [if_pos h1]
        have hne : majOracle H (y ∘ wires) (z ∘ wires) ≠ 1 := fun h2 => hy (hiff.mp ⟨h1, h2⟩)
        rw [majOracle_eq_invMat, invMat, Matrix.of_apply] at hne ⊢
        by_cases h2 : y ∘ wires = majToggle H (z ∘ wires)
        · rw [if_pos h2] at hne; exact absurd rfl hne
        · rw [if_neg h2]
      · rw [if_neg h1]
  | some c =>
    simp only [OracleStep.mat, hadj, embedOp]
    ext y z
    rw [Matrix.of_apply, Matrix.of_apply]
    let wExt : Fin (n + 1 + 1) ↪ Fin qNum :=
      ⟨Fin.cons c wires, Fin.cons_injective_iff.2 ⟨hc c rfl, wires.injective⟩⟩
    have hc_not : c ∉ Set.range wires := hc c rfl
    have hlast_ne_c : wires (Fin.last n) ≠ c := fun h => hc_not ⟨Fin.last n, h⟩
    have hiff : ((∀ a ∉ Set.range wExt, y a = z a) ∧ y c = z c ∧
        (if z c then majOracle H (y ∘ wires) (z ∘ wires) = 1 else y ∘ wires = z ∘ wires)) ↔
        y = stepPerm (some c) wires H z := by
      rw [majOracle_eq_invMat, invMat, Matrix.of_apply]
      have h_eq1 : (if y ∘ wires = majToggle H (z ∘ wires) then (1 : ℂ) else 0) = 1 ↔
          y ∘ wires = majToggle H (z ∘ wires) := by split_ifs <;> simp [*]
      rw [h_eq1]
      constructor
      · rintro ⟨h1, h2, h3⟩
        funext a
        by_cases ha_last : a = wires (Fin.last n)
        · subst ha_last
          cases hzc : z c
          · rw [if_neg (by simp [hzc])] at h3
            have hval := congrFun h3 (Fin.last n)
            change y (wires (Fin.last n)) = z (wires (Fin.last n)) at hval
            simp [stepPerm, hzc, hval]
          · rw [if_pos (by simp [hzc])] at h3
            have hval := congrFun h3 (Fin.last n)
            dsimp [majToggle] at hval
            rw [Fin.snoc_last] at hval
            simp [stepPerm, hzc, hval, h_querySet_init]
        · have h_upd : stepPerm (some c) wires H z a = z a := by
            simp [stepPerm, Function.update_of_ne ha_last]
          rw [h_upd]
          by_cases hac : a = c
          · subst hac; exact h2
          · by_cases ha_range : a ∈ Set.range wires
            · obtain ⟨b, hb⟩ := ha_range
              revert hb
              refine Fin.lastCases ?_ ?_ b
              · intro h; exact absurd h.symm ha_last
              · intro i hb
                cases hzc : z c
                · rw [if_neg (by simp [hzc])] at h3
                  rw [← hb]; exact congrFun h3 (Fin.castSucc i)
                · rw [if_pos (by simp [hzc])] at h3
                  have hval := congrFun h3 (Fin.castSucc i)
                  dsimp [majToggle] at hval
                  rw [Fin.snoc_castSucc] at hval
                  change y (wires (Fin.castSucc i)) = z (wires (Fin.castSucc i)) at hval
                  rw [← hb]; exact hval
            · have ha_ext : a ∉ Set.range wExt := by
                rintro ⟨b, hb⟩
                revert hb
                refine Fin.cases ?_ ?_ b
                · intro h; exact hac h.symm
                · intro b' h; exact ha_range ⟨b', h⟩
              exact h1 a ha_ext
      · intro hy
        subst hy
        refine ⟨fun a ha => ?_, ?_, ?_⟩
        · have hne : a ≠ wires (Fin.last n) := by
            intro h; apply ha; exact ⟨Fin.succ (Fin.last n), h.symm⟩
          simp [stepPerm, Function.update_of_ne hne]
        · simp [stepPerm, Function.update_of_ne hlast_ne_c.symm]
        · cases hzc : z c
          · simp only [Bool.false_eq_true, ↓reduceIte]
            funext b
            refine Fin.lastCases ?_ ?_ b
            · simp [stepPerm, hzc]
            · intro i
              have hne : wires (Fin.castSucc i) ≠ wires (Fin.last n) :=
                fun h => (Fin.castSucc_lt_last i).ne (wires.injective h)
              change Function.update z (wires (Fin.last n)) _ (wires (Fin.castSucc i)) =
                z (wires (Fin.castSucc i))
              rw [Function.update_of_ne hne]
          · simp only [↓reduceIte]
            funext b
            refine Fin.lastCases ?_ ?_ b
            · dsimp [majToggle, stepPerm]
              rw [Fin.snoc_last]
              simp [hzc, h_querySet_init]
            · intro i
              dsimp [majToggle, stepPerm]
              rw [Fin.snoc_castSucc]
              have hne : wires (Fin.castSucc i) ≠ wires (Fin.last n) :=
                fun h => (Fin.castSucc_lt_last i).ne (wires.injective h)
              change Function.update z (wires (Fin.last n)) _ (wires (Fin.castSucc i)) =
                z (wires (Fin.castSucc i))
              rw [Function.update_of_ne hne]
    have hctrl_eval : ∀ (y' z' : Qubits qNum),
        controlledQubits (majOracle H) (y' ∘ wExt) (z' ∘ wExt) =
          if y' c = z' c then
            (if y' c then majOracle H (y' ∘ wires) (z' ∘ wires)
             else (1 : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ) (y' ∘ wires) (z' ∘ wires))
          else 0 := by
      intro y' z'
      dsimp only [controlledQubits, controlled]
      rw [Matrix.submatrix_apply, Matrix.of_apply]
      have hy0 : (y' ∘ wExt) 0 = y' c := rfl
      have hz0 : (z' ∘ wExt) 0 = z' c := rfl
      have hyt : Fin.tail (y' ∘ wExt) = y' ∘ wires := rfl
      have hzt : Fin.tail (z' ∘ wExt) = z' ∘ wires := rfl
      rw [hy0, hz0, hyt, hzt]
    change (if ∀ a ∉ Set.range wExt, y a = z a then
        controlledQubits (majOracle H) (y ∘ wExt) (z ∘ wExt) else 0) =
      if y = stepPerm (some c) wires H z then 1 else 0
    rw [hctrl_eval y z]
    by_cases hy : y = stepPerm (some c) wires H z
    · have h123 := hiff.mpr hy
      rw [if_pos hy, if_pos h123.1, if_pos h123.2.1]
      cases hzc : z c
      · have hyc : y c = false := by rw [h123.2.1, hzc]
        simp only [hyc, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
        have h3' := h123.2.2
        rw [if_neg (by simp [hzc])] at h3'
        rw [if_pos h3']
      · have hyc : y c = true := by rw [h123.2.1, hzc]
        simp only [hyc, ↓reduceIte]
        have h3' := h123.2.2
        rw [if_pos (by simp [hzc])] at h3'
        exact h3'
    · rw [if_neg hy]
      by_cases h1 : ∀ a ∉ Set.range wExt, y a = z a
      · rw [if_pos h1]
        by_cases h2 : y c = z c
        · rw [if_pos h2]
          cases hzc : z c
          · have hyc : y c = false := by rw [h2, hzc]
            simp only [hyc, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
            have h3' : y ∘ wires ≠ z ∘ wires := fun h3 => hy (hiff.mp ⟨h1, h2, by simp [hzc, h3]⟩)
            rw [if_neg h3']
          · have hyc : y c = true := by rw [h2, hzc]
            simp only [hyc, ↓reduceIte]
            have hne : majOracle H (y ∘ wires) (z ∘ wires) ≠ 1 :=
              fun h3 => hy (hiff.mp ⟨h1, h2, by simp [hzc, h3]⟩)
            rw [majOracle_eq_invMat, invMat, Matrix.of_apply] at hne ⊢
            by_cases h3 : y ∘ wires = majToggle H (z ∘ wires)
            · rw [if_pos h3] at hne; exact absurd rfl hne
            · rw [if_neg h3]
        · rw [if_neg h2]
      · rw [if_neg h1]

lemma embedOp_star {k m : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin m) :
    star (embedOp M w) = embedOp (star M) w := by
  ext y z
  simp only [Matrix.star_apply, embedOp, Matrix.of_apply]
  have heq : (∀ a, a ∉ Set.range w → z a = y a) ↔ (∀ a, a ∉ Set.range w → y a = z a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a, a ∉ Set.range w → z a = y a
  · rw [if_pos h, if_pos (heq.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (heq.mpr h'))]; simp

lemma embedOp_mul {k m : ℕ} (M N : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin m) :
    embedOp M w * embedOp N w = embedOp (M * N) w := by
  classical
  ext y z
  simp only [Matrix.mul_apply, embedOp, Matrix.of_apply]
  by_cases hyz : ∀ a, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    let extend (u : Qubits k) : Qubits m := fun a =>
      if h : ∃ b, w b = a then u (Classical.choose h) else y a
    have hext_off : ∀ u a, a ∉ Set.range w → extend u a = y a := by
      intro u a ha
      have hna : ¬ ∃ b, w b = a := by simpa [Set.mem_range] using ha
      dsimp [extend]; rw [dif_neg hna]
    have hext_on : ∀ u, extend u ∘ w = u := by
      intro u; funext b
      have ha : ∃ b', w b' = w b := ⟨b, rfl⟩
      have hch : Classical.choose ha = b := w.injective (Classical.choose_spec ha)
      dsimp [extend]; rw [dif_pos ha, hch]
    have hsplit : ∑ x : Qubits m,
        (if ∀ a, a ∉ Set.range w → y a = x a then M (y ∘ w) (x ∘ w) else 0) *
        (if ∀ a, a ∉ Set.range w → x a = z a then N (x ∘ w) (z ∘ w) else 0) =
        ∑ x ∈ Finset.univ.filter (fun x : Qubits m => ∀ a, a ∉ Set.range w → x a = y a),
          M (y ∘ w) (x ∘ w) * N (x ∘ w) (z ∘ w) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hxy : ∀ a, a ∉ Set.range w → x a = y a
      · have hyx : ∀ a, a ∉ Set.range w → y a = x a := fun a ha => (hxy a ha).symm
        have hxz : ∀ a, a ∉ Set.range w → x a = z a := fun a ha => (hxy a ha).trans (hyz a ha)
        rw [if_pos hxy, if_pos hyx, if_pos hxz]
      · have hnyx : ¬ ∀ a, a ∉ Set.range w → y a = x a := fun h => hxy fun a ha => (h a ha).symm
        rw [if_neg hxy, if_neg hnyx, zero_mul]
    rw [hsplit]
    refine Finset.sum_bij (fun x _ => x ∘ w) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x1 hx1 x2 hx2 heq
      funext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨b, rfl⟩ := ha; exact congrFun heq b
      · rw [(Finset.mem_filter.mp hx1).2 a ha, (Finset.mem_filter.mp hx2).2 a ha]
    · intro u _
      refine ⟨extend u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hext_off u⟩, hext_on u⟩
    · intro _ _; rfl
  · rw [if_neg hyz]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : ∀ a, a ∉ Set.range w → y a = x a
    · have h2 : ¬ ∀ a, a ∉ Set.range w → x a = z a := fun h => hyz fun a ha => (h1 a ha).trans (h a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma embedOp_mem_unitaryGroup {k m : ℕ} {M : Matrix (Qubits k) (Qubits k) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin m) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  rw [embedOp_star, embedOp_mul, hM, embedOp_one]

lemma inner_act_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (u v : EuclideanSpace ℂ ι) :
    inner ℂ (act U u) (act U v) = inner ℂ u v := by
  have hU' : star U * U = 1 := (Matrix.mem_unitaryGroup_iff'.mp hU)
  have h_inner_eq : ∀ φ1 φ2 : EuclideanSpace ℂ ι,
      inner ℂ φ1 φ2 = ∑ y : ι, starRingEnd ℂ (φ1 y) * φ2 y := by
    intro φ1 φ2
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [mul_comm]
  rw [h_inner_eq, h_inner_eq]
  have h_expand : ∀ y : ι,
      starRingEnd ℂ (act U u y) * act U v y =
        ∑ a : ι, ∑ b : ι, (starRingEnd ℂ (u a) * (starRingEnd ℂ (U y a) * U y b)) * v b := by
    intro y
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [h_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have hcol : ∀ b : ι,
      ∑ y : ι, (starRingEnd ℂ (u a) * (starRingEnd ℂ (U y a) * U y b)) * v b =
        starRingEnd ℂ (u a) * ((star U * U) a b) * v b := by
    intro b
    have hmul_entry : (star U * U) a b = ∑ y : ι, starRingEnd ℂ (U y a) * U y b := by
      simp [Matrix.mul_apply]
    rw [hmul_entry, Finset.mul_sum, Finset.sum_mul]
  simp_rw [hcol, hU', Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba; simp [Ne.symm hba]
  · simp

noncomputable def potential {n m qNum : ℕ} {U : Finset (Fin n)}
    (ψ : Fam U m → EuclideanSpace ℂ (Qubits qNum)) : ℝ :=
  ∑ A : Fam U m, ∑ B : Fam U m, gamma A B * ‖inner ℂ (ψ A) (ψ B)‖

lemma step_potential_bound {n c0 m qNum : ℕ} (hm : 1 ≤ m) {C U : Finset (Fin n)}
    (hCU : Disjoint C U) (hC : C.card = c0) (hU : U.card = 2 * m)
    (step : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) qNum)
    (ψ : Fam U m → EuclideanSpace ℂ (Qubits qNum)) (hnorm : ∀ A, ‖ψ A‖ = 1) :
    let ψ' : Fam U m → EuclideanSpace ℂ (Qubits qNum) :=
      fun A => act (step.mat fun _ => majOracle (C ∪ A.1)) (ψ A)
    (∀ A, ‖ψ' A‖ = 1) ∧
    potential ψ - potential ψ' ≤
      if step.IsQueryTo 0 then 8 * (Fintype.card (Fam U m) : ℝ) else 0 := by
  classical
  cases step with
  | gate g =>
    have hgU : embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits qNum) ℂ :=
      embedOp_mem_unitaryGroup g.mem g.wires
    have hstep_eq : ∀ A : Fam U m,
        OracleStep.mat (S := {g : Gate | g.IsUnitary}) (r := 1) (a := fun _ => n + 1) (n := qNum)
          (fun _ => majOracle (C ∪ A.1)) (.gate g) = embedOp g.gate.mat g.wires := fun _ => rfl
    have hnorm' : ∀ A : Fam U m,
        ‖act (OracleStep.mat (S := {g : Gate | g.IsUnitary}) (r := 1) (a := fun _ => n + 1) (n := qNum)
          (fun _ => majOracle (C ∪ A.1)) (.gate g)) (ψ A)‖ = 1 := by
      intro A
      rw [hstep_eq A, act_norm_of_mem_unitaryGroup hgU, hnorm A]
    have hpot : potential (fun A : Fam U m => act (OracleStep.mat (S := {g : Gate | g.IsUnitary})
          (r := 1) (a := fun _ => n + 1) (n := qNum) (fun _ => majOracle (C ∪ A.1)) (.gate g)) (ψ A)) =
        potential ψ := by
      dsimp [potential]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      rw [hstep_eq A, hstep_eq B, inner_act_unitary hgU]
    refine ⟨hnorm', ?_⟩
    simp only [OracleStep.IsQueryTo, Bool.false_eq_true, ↓reduceIte]
    linarith [hpot]
  | query k adj ctrl wires hc =>
    have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    let stepOp (A : Fam U m) : Matrix (Qubits qNum) (Qubits qNum) ℂ :=
      OracleStep.mat (S := {g : Gate | g.IsUnitary}) (r := 1) (a := fun _ => n + 1) (n := qNum)
        (fun _ => majOracle (C ∪ A.1)) (.query 0 adj ctrl wires hc)
    have hmat_eq : ∀ A : Fam U m, stepOp A = invMat (stepPerm ctrl wires (C ∪ A.1)) :=
      fun A => query_step_eq_invMat 0 adj ctrl wires hc (C ∪ A.1)
    have hunit : ∀ A : Fam U m,
        invMat (stepPerm ctrl wires (C ∪ A.1)) ∈ Matrix.unitaryGroup (Qubits qNum) ℂ :=
      fun A => invMat_mem_unitaryGroup (stepPerm ctrl wires (C ∪ A.1))
        (stepPerm_invol ctrl wires hc (C ∪ A.1))
    have hnorm' : ∀ A : Fam U m, ‖act (stepOp A) (ψ A)‖ = 1 := by
      intro A
      rw [hmat_eq A, act_norm_of_mem_unitaryGroup (hunit A), hnorm A]
    refine ⟨hnorm', ?_⟩
    simp only [OracleStep.IsQueryTo, decide_true, ↓reduceIte]
    let fiberNorm (φ : EuclideanSpace ℂ (Qubits qNum)) (S : Finset (Fin n)) : ℝ :=
      Real.sqrt (∑ z ∈ Finset.univ.filter (fun z : Qubits qNum => querySet wires z = S), ‖φ z‖ ^ 2)
    have hfiber_sq : ∀ (φ : EuclideanSpace ℂ (Qubits qNum)) (S : Finset (Fin n)),
        (fiberNorm φ S) ^ 2 =
          ∑ z ∈ Finset.univ.filter (fun z : Qubits qNum => querySet wires z = S), ‖φ z‖ ^ 2 := by
      intro φ S
      exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hfiber_sum : ∀ A : Fam U m, ∑ S : Finset (Fin n), (fiberNorm (ψ A) S) ^ 2 = 1 := by
      intro A
      have h1 : ∀ S : Finset (Fin n), (fiberNorm (ψ A) S) ^ 2 =
          ∑ z ∈ Finset.univ.filter (fun z : Qubits qNum => querySet wires z = S), ‖ψ A z‖ ^ 2 :=
        hfiber_sq (ψ A)
      rw [Finset.sum_congr rfl fun S _ => h1 S]
      rw [Finset.sum_fiberwise_of_maps_to (f := fun z : Qubits qNum => ‖ψ A z‖ ^ 2)
        (g := querySet wires) (fun _ _ => Finset.mem_univ _)]
      have hsq := EuclideanSpace.norm_sq_eq (ψ A)
      rw [hnorm A, one_pow] at hsq
      simpa [Real.norm_eq_abs, sq_abs] using hsq.symm
    have hpair_diff : ∀ A B : Fam U m,
        |‖inner ℂ (ψ A) (ψ B)‖ - ‖inner ℂ (act (stepOp A) (ψ A)) (act (stepOp B) (ψ B))‖| ≤
          2 * ∑ S : Finset (Fin n),
            (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
              fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0) := by
      intro A B
      let fA := stepPerm ctrl wires (C ∪ A.1)
      let fB := stepPerm ctrl wires (C ∪ B.1)
      have hfA_invol : ∀ z, fA (fA z) = z := stepPerm_invol ctrl wires hc (C ∪ A.1)
      have hfB_invol : ∀ z, fB (fB z) = z := stepPerm_invol ctrl wires hc (C ∪ B.1)
      have hfA_q : ∀ z, querySet wires (fA z) = querySet wires z :=
        querySet_stepPerm ctrl wires (C ∪ A.1)
      have hfB_q : ∀ z, querySet wires (fB z) = querySet wires z :=
        querySet_stepPerm ctrl wires (C ∪ B.1)
      have hactA : ∀ z, act (stepOp A) (ψ A) z = ψ A (fA z) := by
        intro z; rw [hmat_eq A]; exact act_invMat fA hfA_invol (ψ A) z
      have hactB : ∀ z, act (stepOp B) (ψ B) z = ψ B (fB z) := by
        intro z; rw [hmat_eq B]; exact act_invMat fB hfB_invol (ψ B) z
      have h_inner_eq : ∀ (φ1 φ2 : EuclideanSpace ℂ (Qubits qNum)),
          inner ℂ φ1 φ2 = ∑ z : Qubits qNum, starRingEnd ℂ (φ1 z) * φ2 z := by
        intro φ1 φ2
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp [mul_comm]
      have hdiff_split :
          inner ℂ (ψ A) (ψ B) - inner ℂ (act (stepOp A) (ψ A)) (act (stepOp B) (ψ B)) =
          ∑ S : Finset (Fin n),
            ∑ z ∈ Finset.univ.filter (fun z : Qubits qNum => querySet wires z = S),
              (starRingEnd ℂ (ψ A z) * ψ B z - starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z)) := by
        rw [h_inner_eq, h_inner_eq, ← Finset.sum_sub_distrib]
        rw [← Finset.sum_fiberwise_of_maps_to (g := querySet wires) (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun z _ => ?_
        rw [hactA z, hactB z]
      have hS_term : ∀ S : Finset (Fin n),
          ‖∑ z ∈ Finset.univ.filter (fun z : Qubits qNum => querySet wires z = S),
              (starRingEnd ℂ (ψ A z) * ψ B z - starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z))‖ ≤
            2 * (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
              fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0) := by
        intro S
        set FS := Finset.univ.filter (fun z : Qubits qNum => querySet wires z = S)
        by_cases hmaj : majJunta (C ∪ A.1) S = majJunta (C ∪ B.1) S
        · rw [if_neg (not_not.mpr hmaj), mul_zero]
          have hf_eq : ∀ z ∈ FS, fB z = fA z := by
            intro z hz
            have hzS : querySet wires z = S := (Finset.mem_filter.mp hz).2
            dsimp [fA, fB, stepPerm]
            rw [hzS, hmaj]
          have hsum_zero : ∑ z ∈ FS,
              (starRingEnd ℂ (ψ A z) * ψ B z - starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z)) = 0 := by
            rw [Finset.sum_sub_distrib]
            have hbij : ∑ z ∈ FS, starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z) =
                ∑ z ∈ FS, starRingEnd ℂ (ψ A z) * ψ B z := by
              refine Finset.sum_bij (fun z _ => fA z) ?_ ?_ ?_ ?_
              · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfA_q, (Finset.mem_filter.mp hz).2]⟩
              · intro z1 _ z2 _ heq; have := congrArg fA heq; rwa [hfA_invol, hfA_invol] at this
              · intro w hw
                refine ⟨fA w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfA_q, (Finset.mem_filter.mp hw).2]⟩,
                  hfA_invol w⟩
              · intro z hz; rw [hf_eq z hz]
            rw [hbij, sub_self]
          rw [hsum_zero, norm_zero]
        · rw [if_pos hmaj]
          have hcs1 : ∑ z ∈ FS, ‖ψ A z‖ * ‖ψ B z‖ ≤ fiberNorm (ψ A) S * fiberNorm (ψ B) S := by
            have hsq := Finset.sum_mul_sq_le_sq_mul_sq FS (fun z => ‖ψ A z‖) (fun z => ‖ψ B z‖)
            have hfn : 0 ≤ fiberNorm (ψ A) S * fiberNorm (ψ B) S :=
              mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            have hprod_sq : (fiberNorm (ψ A) S * fiberNorm (ψ B) S) ^ 2 =
                (∑ z ∈ FS, ‖ψ A z‖ ^ 2) * (∑ z ∈ FS, ‖ψ B z‖ ^ 2) := by
              rw [mul_pow, hfiber_sq, hfiber_sq]
            exact le_of_pow_le_pow_left₀ (n := 2) two_ne_zero hfn (by rw [hprod_sq]; exact hsq)
          have hcs2 : ∑ z ∈ FS, ‖ψ A (fA z)‖ * ‖ψ B (fB z)‖ ≤ fiberNorm (ψ A) S * fiberNorm (ψ B) S := by
            have hA_bij : ∑ z ∈ FS, ‖ψ A (fA z)‖ ^ 2 = ∑ z ∈ FS, ‖ψ A z‖ ^ 2 := by
              refine Finset.sum_bij (fun z _ => fA z) ?_ ?_ ?_ (fun _ _ => rfl)
              · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfA_q, (Finset.mem_filter.mp hz).2]⟩
              · intro z1 _ z2 _ heq; have := congrArg fA heq; rwa [hfA_invol, hfA_invol] at this
              · intro w hw
                refine ⟨fA w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfA_q, (Finset.mem_filter.mp hw).2]⟩,
                  hfA_invol w⟩
            have hB_bij : ∑ z ∈ FS, ‖ψ B (fB z)‖ ^ 2 = ∑ z ∈ FS, ‖ψ B z‖ ^ 2 := by
              refine Finset.sum_bij (fun z _ => fB z) ?_ ?_ ?_ (fun _ _ => rfl)
              · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfB_q, (Finset.mem_filter.mp hz).2]⟩
              · intro z1 _ z2 _ heq; have := congrArg fB heq; rwa [hfB_invol, hfB_invol] at this
              · intro w hw
                refine ⟨fB w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfB_q, (Finset.mem_filter.mp hw).2]⟩,
                  hfB_invol w⟩
            have hsq := Finset.sum_mul_sq_le_sq_mul_sq FS (fun z => ‖ψ A (fA z)‖) (fun z => ‖ψ B (fB z)‖)
            rw [hA_bij, hB_bij] at hsq
            have hfn : 0 ≤ fiberNorm (ψ A) S * fiberNorm (ψ B) S :=
              mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            have hprod_sq : (fiberNorm (ψ A) S * fiberNorm (ψ B) S) ^ 2 =
                (∑ z ∈ FS, ‖ψ A z‖ ^ 2) * (∑ z ∈ FS, ‖ψ B z‖ ^ 2) := by
              rw [mul_pow, hfiber_sq, hfiber_sq]
            exact le_of_pow_le_pow_left₀ (n := 2) two_ne_zero hfn (by rw [hprod_sq]; exact hsq)
          calc ‖∑ z ∈ FS, (starRingEnd ℂ (ψ A z) * ψ B z - starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z))‖
              ≤ ∑ z ∈ FS, ‖starRingEnd ℂ (ψ A z) * ψ B z - starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ z ∈ FS, (‖ψ A z‖ * ‖ψ B z‖ + ‖ψ A (fA z)‖ * ‖ψ B (fB z)‖) := by
                refine Finset.sum_le_sum fun z _ => ?_
                calc ‖starRingEnd ℂ (ψ A z) * ψ B z - starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z)‖
                    ≤ ‖starRingEnd ℂ (ψ A z) * ψ B z‖ + ‖starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z)‖ :=
                      norm_sub_le _ _
                  _ = ‖ψ A z‖ * ‖ψ B z‖ + ‖ψ A (fA z)‖ * ‖ψ B (fB z)‖ := by
                      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
            _ = (∑ z ∈ FS, ‖ψ A z‖ * ‖ψ B z‖) + (∑ z ∈ FS, ‖ψ A (fA z)‖ * ‖ψ B (fB z)‖) :=
                Finset.sum_add_distrib
            _ ≤ 2 * (fiberNorm (ψ A) S * fiberNorm (ψ B) S) := by linarith
      calc |‖inner ℂ (ψ A) (ψ B)‖ - ‖inner ℂ (act (stepOp A) (ψ A)) (act (stepOp B) (ψ B))‖|
          ≤ ‖inner ℂ (ψ A) (ψ B) - inner ℂ (act (stepOp A) (ψ A)) (act (stepOp B) (ψ B))‖ :=
            abs_norm_sub_norm_le _ _
        _ ≤ ∑ S : Finset (Fin n),
              ‖∑ z ∈ Finset.univ.filter (fun z : Qubits qNum => querySet wires z = S),
                (starRingEnd ℂ (ψ A z) * ψ B z - starRingEnd ℂ (ψ A (fA z)) * ψ B (fB z))‖ := by
            rw [hdiff_split]; exact norm_sum_le _ _
        _ ≤ ∑ S : Finset (Fin n), 2 * (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
              fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0) := Finset.sum_le_sum fun S _ => hS_term S
        _ = 2 * ∑ S : Finset (Fin n), (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
              fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0) := (Finset.mul_sum _ _ _).symm
    calc potential ψ - potential (fun A => act (stepOp A) (ψ A))
        ≤ ∑ A : Fam U m, ∑ B : Fam U m,
            gamma A B * |‖inner ℂ (ψ A) (ψ B)‖ - ‖inner ℂ (act (stepOp A) (ψ A)) (act (stepOp B) (ψ B))‖| := by
          dsimp [potential]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun A _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun B _ => ?_
          rw [← mul_sub]
          exact mul_le_mul_of_nonneg_left (le_abs_self _) (gamma_nonneg A B)
      _ ≤ ∑ A : Fam U m, ∑ B : Fam U m,
            gamma A B * (2 * ∑ S : Finset (Fin n),
              if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
                fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0) :=
          Finset.sum_le_sum fun A _ => Finset.sum_le_sum fun B _ =>
            mul_le_mul_of_nonneg_left (hpair_diff A B) (gamma_nonneg A B)
      _ = 2 * ∑ S : Finset (Fin n), ∑ A : Fam U m, ∑ B : Fam U m,
            (if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
              gamma A B * fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0) := by
          have hterm : ∀ A B : Fam U m,
              gamma A B * (2 * ∑ S : Finset (Fin n),
                if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
                  fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0) =
              2 * ∑ S : Finset (Fin n),
                if majJunta (C ∪ A.1) S ≠ majJunta (C ∪ B.1) S then
                  gamma A B * fiberNorm (ψ A) S * fiberNorm (ψ B) S else 0 := by
            intro A B
            rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun S _ => ?_
            split_ifs <;> ring
          simp_rw [hterm, ← Finset.mul_sum]
          congr 1
          refine (Finset.sum_congr rfl fun A _ => Finset.sum_comm).trans Finset.sum_comm
      _ ≤ 2 * ∑ S : Finset (Fin n), 4 * ∑ A : Fam U m, (fiberNorm (ψ A) S) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S _ => ?_) (by norm_num)
          exact schur_step_bound hm hCU hC hU S (fun A => fiberNorm (ψ A) S) (fun _ => Real.sqrt_nonneg _)
      _ = 8 * ∑ A : Fam U m, ∑ S : Finset (Fin n), (fiberNorm (ψ A) S) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          ring
      _ = 8 * (Fintype.card (Fam U m) : ℝ) := by
          simp_rw [hfiber_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma circuit_potential_bound {n c0 m qNum : ℕ} (hm : 1 ≤ m) {C U : Finset (Fin n)}
    (hCU : Disjoint C U) (hC : C.card = c0) (hU : U.card = 2 * m)
    (c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) qNum)
    (ψ : Fam U m → EuclideanSpace ℂ (Qubits qNum)) (hnorm : ∀ A, ‖ψ A‖ = 1) :
    let ψ_final : Fam U m → EuclideanSpace ℂ (Qubits qNum) :=
      fun A => act (c.unitary fun _ => majOracle (C ∪ A.1)) (ψ A)
    (∀ A, ‖ψ_final A‖ = 1) ∧
    potential ψ - potential ψ_final ≤
      (c.queryCount 0 : ℝ) * (8 * (Fintype.card (Fam U m) : ℝ)) := by
  induction c generalizing ψ with
  | nil =>
    intro ψ_final
    have heq : ψ_final = ψ := by
      funext A; simp [ψ_final, OracleCircuit.unitary, act_one]
    rw [heq]
    refine ⟨hnorm, ?_⟩
    simp [OracleCircuit.queryCount]
  | cons step rest ih =>
    let ψ_mid : Fam U m → EuclideanSpace ℂ (Qubits qNum) :=
      fun A => act (step.mat fun _ => majOracle (C ∪ A.1)) (ψ A)
    have hstep := step_potential_bound hm hCU hC hU step ψ hnorm
    have hrest := ih ψ_mid hstep.1
    have hfin_eq : (fun A : Fam U m =>
        act (OracleCircuit.unitary (step :: rest) fun _ => majOracle (C ∪ A.1)) (ψ A)) =
        (fun A : Fam U m =>
        act (OracleCircuit.unitary rest fun _ => majOracle (C ∪ A.1)) (ψ_mid A)) := by
      funext A
      have hunit_cons : OracleCircuit.unitary (step :: rest) (fun _ => majOracle (C ∪ A.1)) =
          OracleCircuit.unitary rest (fun _ => majOracle (C ∪ A.1)) *
            OracleStep.mat (fun _ => majOracle (C ∪ A.1)) step := by
        simp [OracleCircuit.unitary]
      rw [hunit_cons, act_mul]
    rw [hfin_eq]
    refine ⟨hrest.1, ?_⟩
    have hq : (OracleCircuit.queryCount (step :: rest) 0 : ℝ) =
        (if step.IsQueryTo 0 then (1 : ℝ) else 0) + (OracleCircuit.queryCount rest 0 : ℝ) := by
      simp only [OracleCircuit.queryCount, List.countP_cons]
      cases step.IsQueryTo 0 <;> simp [add_comm]
    rw [hq, add_mul]
    have hstep' : potential ψ - potential ψ_mid ≤
        (if step.IsQueryTo 0 then (1 : ℝ) else 0) * (8 * (Fintype.card (Fam U m) : ℝ)) := by
      cases hq0 : step.IsQueryTo 0
      · simp [hq0] at hstep ⊢; exact hstep.2
      · simp [hq0] at hstep ⊢; exact hstep.2
    linarith [hstep', hrest.2]

lemma ambainis_shifted_lower_bound {n c0 m qNum : ℕ} (hm : 1 ≤ m) {C U : Finset (Fin n)}
    (hCU : Disjoint C U) (hC : C.card = c0) (hU : U.card = 2 * m)
    (c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) qNum)
    (out : Fin n ↪ Fin qNum)
    (hsuc : ∀ A : Finset (Fin n), A ⊆ U → A.card = m →
      probEvent (act (c.unitary fun _ => majOracle (C ∪ A)) (zeroKet qNum))
        (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ C ∪ A)) ≥ 2 / 3) :
    (1 / 160 : ℝ) * ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s ≤ (c.queryCount 0 : ℝ) := by
  let ψ0 : Fam U m → EuclideanSpace ℂ (Qubits qNum) := fun _ => zeroKet qNum
  have hnorm0 : ∀ A, ‖ψ0 A‖ = 1 := fun _ => by simp [ψ0, zeroKet, ket]
  let ψf : Fam U m → EuclideanSpace ℂ (Qubits qNum) :=
    fun A => act (c.unitary fun _ => majOracle (C ∪ A.1)) (ψ0 A)
  have hcirc := circuit_potential_bound hm hCU hC hU c ψ0 hnorm0
  have hW0 : potential ψ0 = (Fintype.card (Fam U m) : ℝ) * ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
    dsimp [potential, ψ0]
    have hinner0 : ‖inner ℂ (zeroKet qNum) (zeroKet qNum)‖ = 1 := by
      simp [zeroKet, ket]
    simp_rw [hinner0, mul_one, sum_gamma_eq_harmonic hU, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hWf_pair : ∀ A B : Fam U m, A ≠ B → ‖inner ℂ (ψf A) (ψf B)‖ ≤ (19 / 20 : ℝ) := by
    intro A B hAB
    refine inner_final_bound (ψf A) (ψf B) (hcirc.1 A) (hcirc.1 B)
      (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ C ∪ A.1))
      (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ C ∪ B.1))
      (fun z ⟨hzA, hzB⟩ => ?_)
      (hsuc A.1 A.2.1 A.2.2) (hsuc B.1 B.2.1 B.2.2)
    have hCA_ne_CB : C ∪ A.1 ≠ C ∪ B.1 := by
      intro hEq
      apply hAB
      apply Subtype.ext
      have h1 : (C ∪ A.1) ∩ U = (C ∪ B.1) ∩ U := congrArg (· ∩ U) hEq
      have hCU_empty : C ∩ U = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hCU
      have hCA : (C ∪ A.1) ∩ U = A.1 := by
        rw [Finset.union_inter_distrib_right, hCU_empty, Finset.empty_union,
          Finset.inter_eq_left.mpr A.2.1]
      have hCB : (C ∪ B.1) ∩ U = B.1 := by
        rw [Finset.union_inter_distrib_right, hCU_empty, Finset.empty_union,
          Finset.inter_eq_left.mpr B.2.1]
      rw [hCA, hCB] at h1
      exact h1
    have hex : ∃ i : Fin n, decide (i ∈ C ∪ A.1) ≠ decide (i ∈ C ∪ B.1) := by
      by_contra hall
      push Not at hall
      apply hCA_ne_CB
      ext i
      have hi := hall i
      simpa only [ne_eq, decide_eq_decide] using hi
    obtain ⟨i, hi⟩ := hex
    exact hi ((hzA i).symm.trans (hzB i))
  have hWf : potential ψf ≤ (19 / 20 : ℝ) *
      (Fintype.card (Fam U m) : ℝ) * ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
    dsimp [potential]
    calc ∑ A : Fam U m, ∑ B : Fam U m, gamma A B * ‖inner ℂ (ψf A) (ψf B)‖
        ≤ ∑ A : Fam U m, ∑ B : Fam U m, gamma A B * (19 / 20 : ℝ) := by
          refine Finset.sum_le_sum fun A _ => Finset.sum_le_sum fun B _ => ?_
          by_cases hAB : A = B
          · subst hAB; simp [gamma]
          · exact mul_le_mul_of_nonneg_left (hWf_pair A B hAB) (gamma_nonneg A B)
      _ = (19 / 20 : ℝ) * ∑ A : Fam U m, ∑ B : Fam U m, gamma A B := by
          simp_rw [← Finset.sum_mul]
          ring
      _ = (19 / 20 : ℝ) * (Fintype.card (Fam U m) : ℝ) * ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
          simp_rw [sum_gamma_eq_harmonic hU, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hFam_ne : Nonempty (Fam U m) := by
    obtain ⟨A, hAU, hAm⟩ := Finset.exists_subset_card_eq (by rw [hU]; omega : m ≤ U.card)
    exact ⟨⟨A, hAU, hAm⟩⟩
  have hcard_pos : (0 : ℝ) < (Fintype.card (Fam U m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Fam U m)
  have hdiff : (1 / 20 : ℝ) * (Fintype.card (Fam U m) : ℝ) * ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s ≤
      (c.queryCount 0 : ℝ) * (8 * (Fintype.card (Fam U m) : ℝ)) := by
    linarith [hcirc.2, hW0, hWf]
  nlinarith only [hdiff, hcard_pos]

end Aux_majlb

open QAlgorithms QuantumLTF.Membership.Supplement Aux_majlb

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      c * Real.log k ≤ queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) := by
  refine ⟨1 / 320, by norm_num, fun n k hk hkn => ?_⟩
  let P : Finset (Fin n) → Prop := fun A => 1 ≤ A.card ∧ A.card ≤ k
  have hne : {T : ℕ | ∃ (m : ℕ) (c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m)
      (out : Fin n ↪ Fin m), c.queryCount 0 ≤ T ∧
      ∀ A : Finset (Fin n), P A →
        open Classical in
        probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
          (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 2 / 3}.Nonempty :=
    queryComplexity_set_nonempty n P (fun A hPA => Finset.card_pos.mp hPA.1)
  obtain ⟨qNum, c, out, hqc, hsuc⟩ := Nat.sInf_mem hne
  set m : ℕ := k / 2
  have hm1 : 1 ≤ m := by omega
  have h2m : 2 * m ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]; omega
  obtain ⟨U, _, hU⟩ := Finset.exists_subset_card_eq h2m
  have hlb := ambainis_shifted_lower_bound hm1 (Finset.disjoint_empty_left U)
    Finset.card_empty hU c out (fun A hAU hAm => by
      rw [Finset.empty_union]
      exact hsuc A ⟨by omega, by omega⟩)
  have hlog : Real.log (k : ℝ) ≤ 2 * Real.log ((m + 1 : ℕ) : ℝ) := by
    have hk_le : (k : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
      have hk_nat : k ≤ (m + 1) * (m + 1) := by
        have h1 : k ≤ 2 * (m + 1) := by omega
        have h2 : 2 ≤ m + 1 := by omega
        nlinarith only [h1, h2]
      exact_mod_cast (by simpa [sq] using hk_nat)
    have h1 : Real.log (k : ℝ) ≤ Real.log (((m + 1 : ℕ) : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hk_le
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hharm := harmonic_ge_log_succ m
  have hqc_r : (c.queryCount 0 : ℝ) ≤ (queryComplexity n P : ℝ) := by exact_mod_cast hqc
  linarith [hlog, hharm, hlb, hqc_r]
