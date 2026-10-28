-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.relaxation_strictness_and_tightness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:39:47.958301+00:00
-- url     : https://prove2.me/submissions/14220658-432b-4da8-9f78-bd15f53a65c7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_two_moment_continuous_optimum
noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace P19RS
open QAlgorithms.Papers.Independent.Information100.P19

lemma feas_iff {N : ℕ} (r1 r2 : ℝ) (s : Fin N → ℝ) :
    discreteFeasible ![r1, r2] s ↔
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ ∑ i, s i ^ 2 = r1 ∧ ∑ i, s i ^ 4 = r2 := by
  unfold discreteFeasible
  simp only [Fin.forall_fin_two, Set.mem_Icc]
  simp

lemma pair_bound {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, 0 ≤ s i) :
    2 * ((∑ i, s i ^ 2) ^ 2 - ∑ i, s i ^ 4) ≤ ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) ^ 2 := by
  classical
  set x : Fin N × Fin N → ℝ := fun p => s p.1 * s p.2 - if p.1 = p.2 then s p.1 * s p.2 else 0
    with hx
  have hxnn : ∀ p, 0 ≤ x p := by
    intro p; simp only [hx]; split_ifs <;> simp [mul_nonneg (hs _) (hs _)]
  have hxsw : ∀ p : Fin N × Fin N, x p.swap = x p := by
    intro p; simp only [hx, Prod.fst_swap, Prod.snd_swap]
    by_cases h : p.1 = p.2
    · simp [h]
    · rw [if_neg (Ne.symm h), if_neg h]; ring
  have h1 : ∑ p, x p = (∑ i, s i) ^ 2 - ∑ i, s i ^ 2 := by
    simp only [hx, Finset.sum_sub_distrib, Fintype.sum_prod_type]
    rw [sq, Finset.sum_mul_sum]
    simp [Finset.sum_ite_eq, sq]
  have h2 : ∑ p, x p ^ 2 = (∑ i, s i ^ 2) ^ 2 - ∑ i, s i ^ 4 := by
    have : ∀ p : Fin N × Fin N, x p ^ 2 =
        s p.1 ^ 2 * s p.2 ^ 2 - if p.1 = p.2 then s p.1 ^ 2 * s p.2 ^ 2 else 0 := by
      intro p; simp only [hx]; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Fintype.sum_prod_type]
    rw [sq (∑ i, s i ^ 2), Finset.sum_mul_sum]
    congr 1
    simp [Finset.sum_ite_eq]
    refine Finset.sum_congr rfl fun i _ => by ring
  have h3 : 2 * ∑ p, x p ^ 2 ≤ (∑ p, x p) ^ 2 := by
    rw [Finset.mul_sum, sq (∑ p, x p), Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : p.1 = p.2
    · have : x p = 0 := by simp [hx, hp]
      rw [this]; simp
    · have hne : p ≠ p.swap := by
        intro h; apply hp; have := congrArg Prod.fst h; simpa using this
      have hsub : ({p, p.swap} : Finset _) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun q => x q * x p) (fun q _ _ => mul_nonneg (hxnn q) (hxnn p))
      rw [Finset.sum_pair hne, hxsw] at this
      rw [← Finset.sum_mul] at this
      nlinarith
  rw [← h1, ← h2]; exact h3


lemma part1 : alphaC ![(1:ℝ), 2/3] = ENNReal.ofReal (Real.sqrt (3/2)) := by
  rw [(two_moment_continuous_optimum 1 (2/3) (by norm_num) (by norm_num)).1]
  congr 1
  rw [Real.sqrt_one, one_mul, one_div, ← Real.sqrt_inv]
  norm_num

lemma part2 : alpha ![(1:ℝ), 2/3] = ENNReal.ofReal (Real.sqrt (1 + Real.sqrt (2/3))) := by
  apply le_antisymm
  · -- witness
    set u : ℝ := Real.sqrt (1/3) with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = 1/3 := Real.sq_sqrt (by norm_num)
    have hu1 : u < 1 := by nlinarith
    set a : ℝ := Real.sqrt ((1 + u) / 2) with ha
    set b : ℝ := Real.sqrt ((1 - u) / 2) with hb
    have ha2 : a ^ 2 = (1 + u) / 2 := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = (1 - u) / 2 := Real.sq_sqrt (by linarith)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hab : a * b = Real.sqrt (1/6) := by
      rw [ha, hb, ← Real.sqrt_mul (by linarith)]
      congr 1; nlinarith
    have h23 : Real.sqrt (2/3) = 2 * Real.sqrt (1/6) := by
      rw [show (2/3 : ℝ) = 2 ^ 2 * (1/6) by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have hsum : a + b = Real.sqrt (1 + Real.sqrt (2/3)) := by
      rw [h23, ← hab]
      rw [show 1 + 2 * (a * b) = (a + b) ^ 2 by nlinarith, Real.sqrt_sq (by positivity)]
    apply sInf_le
    refine ⟨2, ![a, b], ?_, ?_⟩
    · rw [feas_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> constructor <;> nlinarith
      · simp [Fin.sum_univ_two]; nlinarith
      · simp [Fin.sum_univ_two]
        have : a ^ 4 + b ^ 4 = (a^2)^2 + (b^2)^2 := by ring
        rw [this, ha2, hb2]; nlinarith
    · simp [Fin.sum_univ_two, hsum]
  · apply le_sInf
    rintro v ⟨N, s, hf, rfl⟩
    rw [feas_iff] at hf
    obtain ⟨hb, h2, h4⟩ := hf
    apply ENNReal.ofReal_le_ofReal
    have hpb := pair_bound s (fun i => (hb i).1)
    rw [h2, h4] at hpb
    have hS : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => (hb i).1
    -- P := S^2 - 1 ≥ 0
    have hP : 0 ≤ (∑ i, s i) ^ 2 - 1 := by
      rw [← h2, sq (∑ i, s i), Finset.sum_mul_sum]
      refine sub_nonneg.mpr (Finset.sum_le_sum fun i _ => ?_)
      rw [sq]
      exact Finset.single_le_sum (f := fun j => s i * s j)
        (fun j _ => mul_nonneg (hb i).1 (hb j).1) (Finset.mem_univ i)
    have hPs : Real.sqrt (2/3) ≤ (∑ i, s i) ^ 2 - 1 := by
      rw [Real.sqrt_le_left hP]; nlinarith
    calc Real.sqrt (1 + Real.sqrt (2/3)) ≤ Real.sqrt ((∑ i, s i) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = ∑ i, s i := Real.sqrt_sq hS

lemma part3 : alphaC ![(1:ℝ), 2/3] < alpha ![(1:ℝ), 2/3] := by
  rw [part1, part2, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  apply Real.sqrt_lt_sqrt (by norm_num)
  have : (1/2 : ℝ) < Real.sqrt (2/3) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith


lemma gap_identity {N : ℕ} (s : Fin N → ℝ) (a r1 r2 : ℝ) (ha : 0 < a)
    (h2 : ∑ i, s i ^ 2 = r1) (h4 : ∑ i, s i ^ 4 = r2) (har : r2 = a ^ 2 * r1) :
    ∑ i, s i - r1 / a = ∑ i, s i * (s i - a) ^ 2 * (s i + 2 * a) / (2 * a ^ 3) := by
  rw [← Finset.sum_div]
  have : ∑ i, s i * (s i - a) ^ 2 * (s i + 2 * a) =
      ∑ i, s i ^ 4 - 3 * a ^ 2 * ∑ i, s i ^ 2 + 2 * a ^ 3 * ∑ i, s i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, h2, h4, har]
  field_simp
  ring

lemma term_nonneg (s a : ℝ) (ha : 0 < a) (hs : 0 ≤ s) :
    0 ≤ s * (s - a) ^ 2 * (s + 2 * a) / (2 * a ^ 3) := by positivity

lemma pointwise (w W : ℝ) (hw0 : 0 ≤ w) (hwW : w ≤ W) :
    |(2 * w ^ 2 - w ^ 4) - (if 1/2 ≤ w then 1 else 0)| ≤
      (2 * (W + 1) ^ 2 + 8) * (w * (w - 1) ^ 2) := by
  split_ifs with h
  · have e : (2 * w ^ 2 - w ^ 4) - 1 = -((w - 1) ^ 2 * (w + 1) ^ 2) := by ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : (w + 1) ^ 2 ≤ (W + 1) ^ 2 := by nlinarith
    have h2 : (w + 1) ^ 2 ≤ (2 * (W + 1) ^ 2 + 8) * w := by nlinarith
    have h3 : 0 ≤ (w - 1) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  · rw [not_le] at h
    have e : (2 * w ^ 2 - w ^ 4) - 0 = w ^ 2 * (2 - w ^ 2) := by ring
    rw [e, abs_of_nonneg (mul_nonneg (sq_nonneg w) (by nlinarith))]
    have h1 : w ^ 2 * (2 - w ^ 2) ≤ 2 * w ^ 2 := by nlinarith
    have h2 : 2 * w ^ 2 ≤ 8 * (w * (w - 1) ^ 2) := by nlinarith
    have h3 : 0 ≤ w * (w - 1) ^ 2 := by positivity
    have h4 : 8 * (w * (w - 1) ^ 2) ≤ (2 * (W + 1) ^ 2 + 8) * (w * (w - 1) ^ 2) := by
      nlinarith [sq_nonneg (W + 1)]
    linarith

lemma count_bound {N : ℕ} (s : Fin N → ℝ) (a r1 r2 : ℝ) (ha : 0 < a) (hr1 : 0 < r1)
    (hb : ∀ i, 0 ≤ s i ∧ s i ≤ 1)
    (h2 : ∑ i, s i ^ 2 = r1) (h4 : ∑ i, s i ^ 4 = r2) (har : r2 = a ^ 2 * r1) :
    |r1 ^ 2 / r2 - ((Finset.univ.filter (fun i => a / 2 ≤ s i)).card : ℝ)| ≤
      (2 * (1 / a + 1) ^ 2 + 8) / a * (∑ i, s i - r1 / a) := by
  set C := 2 * (1 / a + 1) ^ 2 + 8 with hC
  have hC0 : 0 ≤ C := by positivity
  have hρ : r1 ^ 2 / r2 = ∑ i, (2 * (s i / a) ^ 2 - (s i / a) ^ 4) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [div_pow, ← Finset.sum_div]
    rw [h2, h4, har]
    field_simp
    ring
  have hcard : ((Finset.univ.filter (fun i => a / 2 ≤ s i)).card : ℝ) =
      ∑ i, (if 1/2 ≤ s i / a then (1:ℝ) else 0) := by
    rw [Finset.sum_boole]
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [le_div_iff₀ ha]
    constructor <;> intro h <;> linarith
  rw [hρ, hcard, gap_identity s a r1 r2 ha h2 h4 har, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hw0 : 0 ≤ s i / a := div_nonneg (hb i).1 ha.le
  have hwW : s i / a ≤ 1 / a := div_le_div_of_nonneg_right (hb i).2 ha.le
  refine (pointwise (s i / a) (1 / a) hw0 hwW).trans ?_
  have key : s i / a * (s i / a - 1) ^ 2 ≤
      1 / a * (s i * (s i - a) ^ 2 * (s i + 2 * a) / (2 * a ^ 3)) := by
    have e1 : s i / a * (s i / a - 1) ^ 2 = s i * (s i - a) ^ 2 / a ^ 3 := by
      field_simp
    have e2 : 1 / a * (s i * (s i - a) ^ 2 * (s i + 2 * a) / (2 * a ^ 3)) =
        s i * (s i - a) ^ 2 / a ^ 3 * ((s i + 2 * a) / (2 * a)) := by
      field_simp
    rw [e1, e2]
    have hq : 1 ≤ (s i + 2 * a) / (2 * a) := by
      rw [le_div_iff₀ (by positivity)]; linarith [(hb i).1]
    have hp : 0 ≤ s i * (s i - a) ^ 2 / a ^ 3 := by
      have := (hb i).1; positivity
    nlinarith
  calc C * (s i / a * (s i / a - 1) ^ 2)
      ≤ C * (1 / a * (s i * (s i - a) ^ 2 * (s i + 2 * a) / (2 * a ^ 3))) :=
        mul_le_mul_of_nonneg_left key hC0
    _ = C / a * (s i * (s i - a) ^ 2 * (s i + 2 * a) / (2 * a ^ 3)) := by ring


lemma part4 (r1 r2 : ℝ) (h0 : 0 ≤ r1) (h1 : r1 ≤ 1) (h2 : 0 < r2) (hle : r2 ≤ r1 ^ 2) :
    (alpha ![r1, r2] = alphaC ![r1, r2] ↔ ∃ k : ℕ, r1 ^ 2 / r2 = (k : ℝ)) := by
  have hr1 : 0 < r1 := by
    rcases h0.lt_or_eq with h | h
    · exact h
    · subst h; nlinarith
  have hr2r1 : r2 ≤ r1 := by nlinarith
  set a := Real.sqrt (r2 / r1) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (div_pos h2 hr1)
  have ha2 : a ^ 2 = r2 / r1 := Real.sq_sqrt (div_pos h2 hr1).le
  have har : r2 = a ^ 2 * r1 := by rw [ha2]; field_simp
  have ha1 : a ≤ 1 := by
    have : a ^ 2 ≤ 1 := by
      rw [ha2, div_le_one hr1]; linarith
    nlinarith
  have hC : alphaC ![r1, r2] = ENNReal.ofReal (r1 / a) := by
    rw [(two_moment_continuous_optimum r1 r2 h2 hr2r1).1]
    congr 1
    rw [ha, Real.sqrt_div' _ hr1.le]
    have : 0 < Real.sqrt r1 := Real.sqrt_pos.mpr hr1
    have : 0 < Real.sqrt r2 := Real.sqrt_pos.mpr h2
    field_simp
  have hge : ENNReal.ofReal (r1 / a) ≤ alpha ![r1, r2] := by
    apply le_sInf
    rintro v ⟨N, s, hf, rfl⟩
    rw [feas_iff] at hf
    obtain ⟨hb, hs2, hs4⟩ := hf
    apply ENNReal.ofReal_le_ofReal
    have := gap_identity s a r1 r2 ha0 hs2 hs4 har
    have : 0 ≤ ∑ i, s i * (s i - a) ^ 2 * (s i + 2 * a) / (2 * a ^ 3) :=
      Finset.sum_nonneg fun i _ => term_nonneg (s i) a ha0 (hb i).1
    linarith
  rw [hC]
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    set ρ := r1 ^ 2 / r2 with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    set n := ⌊ρ⌋₊ with hn
    have hn1 : (n : ℝ) ≤ ρ := Nat.floor_le hρ0
    have hn2 : ρ < n + 1 := Nat.lt_floor_add_one ρ
    have hn3 : (n : ℝ) < ρ := lt_of_le_of_ne hn1 (fun h => hne n h.symm)
    set δ := min (ρ - n) (n + 1 - ρ) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
    set C := 2 * (1 / a + 1) ^ 2 + 8 with hCdef
    have hC0 : 0 < C := by positivity
    set ε := δ * a / (2 * C) with hε
    have hε0 : 0 < ε := by positivity
    have hlt : alpha ![r1, r2] < ENNReal.ofReal (r1 / a + ε) := by
      rw [heq, ENNReal.ofReal_lt_ofReal_iff (by positivity)]; linarith
    unfold alpha at hlt
    rw [sInf_lt_iff] at hlt
    obtain ⟨v, ⟨N, s, hf, rfl⟩, hv⟩ := hlt
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hv
    rw [feas_iff] at hf
    obtain ⟨hb, hs2, hs4⟩ := hf
    have hcb := count_bound s a r1 r2 ha0 hr1 hb hs2 hs4 har
    rw [← hCdef] at hcb
    set m := (Finset.univ.filter (fun i => a / 2 ≤ s i)).card
    have hsmall : C / a * (∑ i, s i - r1 / a) < δ := by
      have hpos : 0 < C / a := by positivity
      calc C / a * (∑ i, s i - r1 / a) < C / a * ε := by
            apply mul_lt_mul_of_pos_left _ hpos; linarith
        _ = δ / 2 := by rw [hε]; field_simp
        _ < δ := by linarith
    have hm : |ρ - m| < δ := lt_of_le_of_lt hcb hsmall
    rw [abs_lt] at hm
    rcases le_or_gt m n with hmn | hmn
    · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have : δ ≤ ρ - n := min_le_left _ _
      linarith
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hmn
      have : δ ≤ n + 1 - ρ := min_le_right _ _
      linarith
  · rintro ⟨k, hk⟩
    refine le_antisymm ?_ hge
    have hka : (k : ℝ) * a ^ 2 = r1 := by
      rw [← hk, ha2]; field_simp
    apply sInf_le
    refine ⟨k, fun _ => a, ?_, ?_⟩
    · rw [feas_iff]
      refine ⟨fun _ => ⟨ha0.le, ha1⟩, ?_, ?_⟩
      · simp [hka]
      · simp
        rw [har, ← hka]; ring
    · congr 1
      simp
      field_simp
      linarith

end P19RS

theorem solution :
    QAlgorithms.Papers.Independent.Information100.P19.alphaC ![(1:ℝ),2/3] =
        ENNReal.ofReal (Real.sqrt (3/2)) ∧
    QAlgorithms.Papers.Independent.Information100.P19.alpha ![(1:ℝ),2/3] =
        ENNReal.ofReal (Real.sqrt (1+Real.sqrt (2/3))) ∧
    QAlgorithms.Papers.Independent.Information100.P19.alphaC ![(1:ℝ),2/3] <
        QAlgorithms.Papers.Independent.Information100.P19.alpha ![(1:ℝ),2/3] ∧
    (∀ r1 r2 : ℝ, 0≤r1 → r1≤1 → 0<r2 → r2≤r1^2 →
      (QAlgorithms.Papers.Independent.Information100.P19.alpha ![r1,r2] =
          QAlgorithms.Papers.Independent.Information100.P19.alphaC ![r1,r2] ↔
        ∃ k : ℕ, r1^2/r2=(k:ℝ))) :=
  ⟨P19RS.part1, P19RS.part2, P19RS.part3, P19RS.part4⟩

