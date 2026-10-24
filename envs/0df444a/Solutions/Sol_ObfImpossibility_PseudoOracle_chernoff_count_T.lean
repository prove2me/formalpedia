-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.chernoff_count_T
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T23:56:28.920767+00:00
-- url     : https://prove2.me/submissions/7b4364e9-2e4d-4060-9f59-7fc4961f6315

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

open ObfImpossibility.PseudoOracle
open scoped BigOperators

namespace WentaoSubsetConcentration

private lemma choose_ratio (n m r : ℕ) (hn : 0 < n) (hm : m ≤ n) (hr : r ≤ m) :
    ((n - r).choose (m - r) : ℝ) ≤ (n.choose m : ℝ) * ((m : ℝ) / n) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrm : r ≤ m := by omega
    have hrn : r < n := by omega
    have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast (by omega : 0 < n - r)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hmnr : (0 : ℝ) ≤ (m - r : ℕ) := Nat.cast_nonneg _
    have hrec :=  Nat.add_one_mul_choose_eq (n - (r + 1)) (m - (r + 1))
    rw [show n - (r + 1) + 1 = n - r by omega,
      show m - (r + 1) + 1 = m - r by omega] at hrec
    have rec' : ((n - r : ℕ) : ℝ) * ((n - (r + 1)).choose (m - (r + 1)) : ℝ) =
        ((n - r).choose (m - r) : ℝ) * (m - r : ℕ) := by exact_mod_cast hrec
    have ratio : ((m - r : ℕ) : ℝ) / (n - r : ℕ) ≤ (m : ℝ) / n := by
      rw [div_le_div_iff₀ hnr hn0, Nat.cast_sub hrm, Nat.cast_sub hrn.le]
      have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
      nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
    calc
      _ = ((n - r).choose (m - r) : ℝ) * (((m - r : ℕ) : ℝ) / (n - r : ℕ)) := by
        rw [← mul_div_assoc]
        apply (eq_div_iff hnr.ne').mpr
        nlinarith [rec']
      _ ≤ ((n.choose m : ℝ) * ((m : ℝ) / n) ^ r) *
          (((m - r : ℕ) : ℝ) / (n - r : ℕ)) :=
        mul_le_mul_of_nonneg_right (ih hrm) (by positivity)
      _ ≤ ((n.choose m : ℝ) * ((m : ℝ) / n) ^ r) * ((m : ℝ) / n) :=
        mul_le_mul_of_nonneg_left ratio (by positivity)
      _ = _ := by rw [pow_succ]; ring

private lemma count_containing {α : Type} [DecidableEq α] (U A : Finset α)
    (hn : 0 < U.card) (m : ℕ) (hm : m ≤ U.card) (hA : A ⊆ U) :
    (((U.powersetCard m).filter (A ⊆ ·)).card : ℝ) ≤
      (U.card.choose m : ℝ) * ((m : ℝ) / U.card) ^ A.card := by
  by_cases hr : A.card ≤ m
  · rw [Finset.card_filter_powersetCard_subset A U m hA hr]
    exact choose_ratio U.card m A.card hn hm hr
  · have hempty : (U.powersetCard m).filter (A ⊆ ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hT, hAT⟩ := Finset.mem_filter.mp hT
      have := Finset.card_le_card hAT
      have := (Finset.mem_powersetCard.mp hT).2
      omega
    rw [hempty]; simp only [Finset.card_empty, Nat.cast_zero]; positivity

private noncomputable def val (b : Bool) : ℝ := if b then 1 else 0

private lemma val_nonneg (b : Bool) : 0 ≤ val b := by cases b <;> simp [val]

private lemma average_sum {α : Type} (U : Finset α) (f : α → Bool) :
    avg U f = (∑ x ∈ U, val (f x)) / U.card := by
  unfold avg
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

private lemma average_nonneg {α : Type} (U : Finset α) (f : α → Bool) :
    0 ≤ avg U f := by unfold avg; positivity

private lemma average_le_one {α : Type} (U : Finset α) (f : α → Bool) :
    avg U f ≤ 1 := by
  unfold avg
  by_cases h : U.card = 0
  · simp [h]
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)]
    exact_mod_cast Finset.card_filter_le U _

private lemma mgf {α : Type} [DecidableEq α] (U : Finset α) (f : α → Bool)
    (hn : 0 < U.card) (m : ℕ) (hm : m ≤ U.card) (t : ℝ) (ht : 0 ≤ t) :
    ∑ T ∈ U.powersetCard m, Real.exp (t * ∑ x ∈ T, val (f x)) ≤
      (U.card.choose m : ℝ) * Real.exp ((m : ℝ) * avg U f * (Real.exp t - 1)) := by
  classical
  let F := U.filter fun x => f x = true
  let a := Real.exp t - 1
  have ha : 0 ≤ a := sub_nonneg.mpr (Real.one_le_exp ht)
  have expansion (T : Finset α) (hT : T ⊆ U) :
      Real.exp (t * ∑ x ∈ T, val (f x)) =
        ∑ A ∈ F.powerset, if A ⊆ T then a ^ A.card else 0 := by
    have heq : T.filter (fun x => f x = true) = T ∩ F := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter, F]
      tauto
    have hsum : ∑ x ∈ T, val (f x) = ((T ∩ F).card : ℝ) := by
      rw [← heq, Finset.card_filter]; push_cast; rfl
    rw [hsum, mul_comm t, Real.exp_nat_mul]
    have hexp : Real.exp t = 1 + a := by dsimp [a]; ring
    rw [hexp, ← Finset.prod_const, Finset.prod_one_add]
    simp only [Finset.prod_const]
    calc
      _ = ∑ A ∈ (T ∩ F).powerset, if A ⊆ T then a ^ A.card else 0 := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [if_pos ((Finset.mem_powerset.mp hA).trans Finset.inter_subset_left)]
      _ = _ := by
        apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.inter_subset_right)
        intro A hAF hAT
        rw [if_neg]
        intro h
        apply hAT
        exact Finset.mem_powerset.mpr (Finset.subset_inter h (Finset.mem_powerset.mp hAF))
  have hexpand : (∑ T ∈ U.powersetCard m, Real.exp (t * ∑ x ∈ T, val (f x))) =
      ∑ A ∈ F.powerset, a ^ A.card *
        (((U.powersetCard m).filter (A ⊆ ·)).card : ℝ) := by
    simp_rw [Finset.sum_congr rfl (fun T hT => expansion T (Finset.mem_powersetCard.mp hT).1)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hexpand]
  calc
    _ ≤ ∑ A ∈ F.powerset, a ^ A.card *
        ((U.card.choose m : ℝ) * ((m : ℝ) / U.card) ^ A.card) := by
      apply Finset.sum_le_sum
      intro A hA
      exact mul_le_mul_of_nonneg_left
        (count_containing U A hn m hm ((Finset.mem_powerset.mp hA).trans (Finset.filter_subset _ _)))
        (pow_nonneg ha _)
    _ = (U.card.choose m : ℝ) * (1 + a * ((m : ℝ) / U.card)) ^ F.card := by
      rw [← Finset.prod_const, Finset.prod_one_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.prod_const, mul_pow]
      ring
    _ ≤ (U.card.choose m : ℝ) *
        (Real.exp (a * ((m : ℝ) / U.card))) ^ F.card := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      linarith [Real.add_one_le_exp (a * ((m : ℝ) / U.card))]
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 2
      dsimp [F, a]
      unfold avg
      ring

private lemma upper {α : Type} [DecidableEq α] (U : Finset α) (f : α → Bool)
    (m : ℕ) (hm0 : 0 < m) (hm : m ≤ U.card) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (((U.powersetCard m).filter fun T => ε < avg T f - avg U f).card : ℝ) ≤
      Real.exp (-((1 / 4 : ℝ) * (m : ℝ) * ε ^ 2)) * (U.card.choose m : ℝ) := by
  classical
  let P := U.powersetCard m
  let B := P.filter fun T => ε < avg T f - avg U f
  let p := avg U f
  let t := ε / 2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have ht : 0 < t := by dsimp [t]; positivity
  have hp0 : 0 ≤ p := average_nonneg U f
  have hp1 : p ≤ 1 := average_le_one U f
  have hpoint (T : Finset α) (hT : T ∈ B) :
      (p + ε) * m ≤ ∑ x ∈ T, val (f x) := by
    obtain ⟨hTP, hbad⟩ := Finset.mem_filter.mp hT
    have hcard := (Finset.mem_powersetCard.mp hTP).2
    rw [average_sum, hcard] at hbad
    have := (lt_div_iff₀ hmpos).mp (show p + ε < (∑ x ∈ T, val (f x)) / m by
      dsimp [p]; linarith)
    exact this.le
  have hmark : (B.card : ℝ) * Real.exp (t * ((p + ε) * m)) ≤
      ∑ T ∈ P, Real.exp (t * ∑ x ∈ T, val (f x)) := by
    calc
      _ = ∑ _T ∈ B, Real.exp (t * ((p + ε) * m)) := by simp
      _ ≤ ∑ T ∈ B, Real.exp (t * ∑ x ∈ T, val (f x)) := by
        apply Finset.sum_le_sum
        intro T hT
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hpoint T hT) ht.le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => (Real.exp_pos _).le)
  have hmgf := mgf U f (by omega) m hm t ht.le
  have htotal : (B.card : ℝ) * Real.exp (t * ((p + ε) * m)) ≤
      (U.card.choose m : ℝ) * Real.exp ((m : ℝ) * p * (Real.exp t - 1)) :=
    hmark.trans hmgf
  have hquad : Real.exp t ≤ 1 + t + t ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := t) (by
      rw [abs_le]; dsimp [t]; constructor <;> linarith)
    linarith [(abs_le.mp h).2]
  have hexponent : (m : ℝ) * p * (Real.exp t - 1) - t * ((p + ε) * m) ≤
      -((1 / 4 : ℝ) * m * ε ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hquad (mul_nonneg hmpos.le hp0)
    dsimp [t] at *
    nlinarith [mul_nonneg hmpos.le (mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg ε))]
  change (B.card : ℝ) ≤ _
  calc
    _ ≤ ((U.card.choose m : ℝ) * Real.exp ((m : ℝ) * p * (Real.exp t - 1))) /
        Real.exp (t * ((p + ε) * m)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr htotal
    _ = (U.card.choose m : ℝ) *
        Real.exp ((m : ℝ) * p * (Real.exp t - 1) - t * ((p + ε) * m)) := by
      rw [mul_div_assoc, Real.exp_sub]
    _ ≤ _ := by
      rw [mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (Nat.cast_nonneg _)

end WentaoSubsetConcentration

open WentaoSubsetConcentration in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ {α : Type} [DecidableEq α] (U : Finset α) (f : α → Bool) (m : ℕ)
      (ε : ℝ), 0 < ε →
        (((U.powersetCard m).filter fun T => ε < avg T f - avg U f).card : ℝ) ≤
          Real.exp (-(c * (m : ℝ) * ε ^ 2)) * ((U.card.choose m : ℕ) : ℝ) := by
  classical
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α _ U f m ε hε
  by_cases hm : m ≤ U.card
  · by_cases hm0 : m = 0
    · subst m
      simp only [Finset.powersetCard_zero]
      have hempty : ({∅} : Finset (Finset α)).filter (fun T => ε < avg T f - avg U f) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro T hT
        obtain ⟨hT, hbad⟩ := Finset.mem_filter.mp hT
        have hTempty : T = ∅ := by simpa using hT
        subst T
        have havg : avg (∅ : Finset α) f = 0 := by simp [avg]
        rw [havg] at hbad
        linarith [average_nonneg U f]
      rw [hempty]; norm_num
    · by_cases hε1 : ε ≤ 1
      · exact upper U f m (Nat.pos_of_ne_zero hm0) hm ε hε hε1
      · have hempty : (U.powersetCard m).filter (fun T => ε < avg T f - avg U f) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro T hT
          have h := (Finset.mem_filter.mp hT).2
          linarith [average_nonneg U f, average_le_one T f]
        rw [hempty]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · rw [Finset.powersetCard_eq_empty.mpr (by omega)]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
