-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.proposition_3_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:05:29.726199+00:00
-- url     : https://prove2.me/submissions/b8db68e7-2f85-46f2-b745-dce9abf208f4

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_9
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_5
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_8
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable

private def extendSigns {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : {e // e ∈ F} → Bool) (e : ColoredEdge N c) : Bool :=
  if h : e ∈ F then b ⟨e,h⟩ else false

private lemma rank_nonnegative {N c : ℕ} (F : Finset (ColoredEdge N c)) (hF : Consistent F) :
    0 ≤ CycleRank F := by
  let signs := fun (x : Fin N → Bool) (e : {e // e ∈ F}) => xor (x e.val.1) (x e.val.2.1)
  let base : ℝ := (2 : ℝ)^(-((Vertices F).card : ℤ)+(Components F).card)
  have hbase : 0 ≤ base := by dsimp [base]; positivity
  have hfiber (b : {e // e ∈ F} → Bool) :
      ((univ.filter (fun x : Fin N → Bool => signs x = b)).card : ℝ) ≤ base * (2 : ℝ)^N := by
    have hset : (univ.filter (fun x : Fin N → Bool => signs x = b)) =
        (univ.filter (fun x : Fin N → Bool => ∀ e ∈ F, xor (x e.1) (x e.2.1) = extendSigns F b e)) := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hx e he
        have hh := congrFun hx ⟨e,he⟩
        simpa only [signs, extendSigns, dif_pos he] using hh
      · intro hx
        funext e
        simpa only [signs, extendSigns, dif_pos e.property] using hx e.val e.property
    have hp : SignProbYes F (extendSigns F b) ≤ base := by
      rw [(lemma_3_5 F hF (extendSigns F b)).2.1]
      split_ifs
      · exact le_rfl
      · exact hbase
    unfold SignProbYes at hp
    rw [← hset] at hp
    exact (div_le_iff₀ (by positivity)).mp hp
  have hcount : (2 : ℝ)^N ≤ (2 : ℝ)^F.card * (base * (2 : ℝ)^N) := by
    have hc : (univ : Finset (Fin N → Bool)).card =
        ∑ b : {e // e ∈ F} → Bool, (univ.filter (fun x : Fin N → Bool => signs x = b)).card :=
      card_eq_sum_card_fiberwise (fun x _ => mem_univ (signs x))
    have hcr := congrArg (fun n : ℕ => (n : ℝ)) hc
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum] at hcr
    calc
      _ = _ := hcr
      _ ≤ ∑ b : {e // e ∈ F} → Bool, base * (2 : ℝ)^N := sum_le_sum (fun b _ => hfiber b)
      _ = _ := by simp
  have hbound : (1 : ℝ) ≤ (2 : ℝ)^(CycleRank F) := by
    have hm : (1 : ℝ)*(2 : ℝ)^N ≤ ((2 : ℝ)^F.card*base)*(2 : ℝ)^N := by
      nlinarith [hcount]
    have h := (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < (2 : ℝ)^N)).mp hm
    have heq : (2 : ℝ)^F.card*base = (2 : ℝ)^(CycleRank F) := by
      dsimp [base]
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      unfold CycleRank
      ring
    rw [heq] at h
    exact h
  exact (one_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hbound

private lemma rank_le_edges {N c : ℕ} (F : Finset (ColoredEdge N c)) : CycleRank F ≤ F.card := by
  have hc : (Components F).card ≤ (Vertices F).card := card_image_le
  unfold CycleRank
  omega

private lemma pattern_card {N : ℕ} (T : GraphTable N) : (PatternOf T).card ≤ T.val.card := by
  unfold PatternOf
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ az ∈ T.val, 1 := by
      apply sum_le_sum
      intro az haz
      cases az.1.1 <;> simp
    _ = _ := by simp

private def tableExponent {α : Type} [DecidableEq α] (s : Finset α) : α →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

private lemma exponent_support {α : Type} [DecidableEq α] (s : Finset α) :
    (tableExponent s).support = s := by
  ext a
  simp [tableExponent, Finsupp.mem_support_iff, Finsupp.indicator_apply]

private lemma exponent_injective {α : Type} [DecidableEq α] :
    Function.Injective (tableExponent (α := α)) := by
  intro s t h
  simpa only [exponent_support] using congrArg Finsupp.support h

private lemma table_monomial {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) :
    TableMonomial T = MvPolynomial.monomial (tableExponent T.val) (1 : ℝ) := by
  simpa only [pow_one, TableMonomial, tableExponent] using
    (MvPolynomial.prod_X_pow (R := ℝ) (fun _ : I × S => 1) T.val)

private lemma canonical_coefficient {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) :
    (CanonicalPolynomial E A out).coeff (tableExponent T.val) = CanonicalCoeff E A out T := by
  unfold CanonicalPolynomial
  rw [MvPolynomial.coeff_sum]
  rw [sum_eq_single T]
  · simp [table_monomial]
  · intro U hU hUT
    have he : tableExponent U.val ≠ tableExponent T.val := by
      intro h
      exact hUT (Subtype.ext (exponent_injective h))
    simp [table_monomial, he]
  · simp

private lemma coefficient_zero {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) (hT : 2*q < T.val.card) :
    CanonicalCoeff E A out T = 0 := by
  have hdegree := (lemma_2_9 E A out).1
  rw [← canonical_coefficient E A out T]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [exponent_support]
  have hsum : (∑ a ∈ T.val, tableExponent T.val a) = T.val.card := by
    simp [tableExponent, Finsupp.indicator_apply]
  rw [hsum]
  exact hdegree.trans_lt hT


private lemma query_scale_bound (q : ℕ) : (q : ℝ) ≤ 2*DegreeScale q := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hl : (1/2 : ℝ) ≤ Real.log (q+2 : ℝ) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ q+2)
    linarith [Real.log_two_gt_d9]
  unfold DegreeScale
  nlinarith

private lemma table_numerator {N k w q : ℕ} (Cdeg : ℝ) (hCdeg : 0 < Cdeg)
    (hcore : ∀ F : Finset (ColoredEdge N), Consistent F → F.card ≤ 2*q →
      ∃ B : Bivariate, (B.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        TopologyMoment F M l = l ^ CycleRank F * Eval B M l / Eval (Denominator q) M l)
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N 3) k w q)
    (out : (Address N 3 × Bits k) × Fin w → Bool) (T : GraphTable N) :
    ∃ H : Bivariate, (H.totalDegree : ℝ) ≤ (Cdeg+4)*DegreeScale q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        CanonicalCoeff E A out T * (FormalMonomial .yes T M l - FormalMonomial .no T M l) =
          l * Eval H M l / Eval (Denominator q) M l := by
  have hscale := query_scale_bound q
  have hSq : 0 ≤ DegreeScale q := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hzero : (0 : ℝ) ≤ (Cdeg+4)*DegreeScale q := mul_nonneg (by linarith) hSq
  by_cases hsize : T.val.card ≤ 2*q
  swap
  · refine ⟨0,by simpa using hzero,?_⟩
    intro M l hl hden
    rw [coefficient_zero E A out T (Nat.lt_of_not_ge hsize)]
    simp [Eval]
  by_cases hcons : ConsistentTable T
  swap
  · refine ⟨0,by simpa using hzero,?_⟩
    intro M l hl hden
    simp [FormalMonomial,hcons,Eval]
  let F := PatternOf T
  have hF : Consistent F := hcons.1
  by_cases hforest : Forest F
  · refine ⟨0,by simpa using hzero,?_⟩
    intro M l hl hden
    have hs := (lemma_3_5 F hF (PatternSign T)).2.2 hforest
    simp only [FormalMonomial, if_pos hcons]
    change CanonicalCoeff E A out T *
      (TopologyMoment F M l * SignProbYes F (PatternSign T) -
        TopologyMoment F M l * SignProbNo F (PatternSign T)) = _
    rw [hs]
    simp [Eval]
  obtain ⟨B,hBdeg,hB⟩ := hcore F hF ((pattern_card T).trans hsize)
  have hrank : 1 ≤ CycleRank F := by
    have := rank_nonnegative F hF
    have hn : CycleRank F ≠ 0 := hforest
    omega
  let m : ℕ := (CycleRank F).toNat-1
  have hm : m ≤ 2*q := by
    have hrankle := rank_le_edges F
    have hFcard : F.card ≤ 2*q := (pattern_card T).trans hsize
    dsimp only [m]
    omega
  have hmr : (m : ℝ) ≤ 2*q := by exact_mod_cast hm
  have hr : CycleRank F = ((m+1 : ℕ) : ℤ) := by dsimp [m]; omega
  let H : Bivariate := C (CanonicalCoeff E A out T * (SignProbYes F (PatternSign T)-SignProbNo F (PatternSign T))) *
    (X 1 ^ m * B)
  refine ⟨H,?_,?_⟩
  · have hdeg : H.totalDegree ≤ m+B.totalDegree := by
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      apply (totalDegree_mul _ _).trans_eq
      simp
    have hdeg' : (H.totalDegree : ℝ) ≤ m+B.totalDegree := by exact_mod_cast hdeg
    nlinarith
  · intro M l hl hden
    have he := hB M l hl hden
    simp only [FormalMonomial, if_pos hcons]
    change CanonicalCoeff E A out T *
      (TopologyMoment F M l * SignProbYes F (PatternSign T) -
        TopologyMoment F M l * SignProbNo F (PatternSign T)) = _
    rw [he,hr,zpow_natCast,pow_succ]
    simp only [H, Eval, map_mul, map_pow, eval_C, eval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness Finset

theorem solution : ∃ Cdeg : ℝ, 0 < Cdeg ∧
    ∀ N k w q : ℕ, ∀ E : Encoding (Fin N × Bool) k,
    ∀ A : Algorithm (Address N 3) k w q,
    ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
    ∃ H : Bivariate, (H.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        FormalGap E A out M l = l * Eval H M l / Eval (Denominator q) M l := by
  obtain ⟨Cdeg,hCdeg,hcore⟩ := lemma_3_8
  refine ⟨Cdeg+4,by linarith,?_⟩
  intro N k w q E A out
  have ht := fun T : GraphTable N => table_numerator Cdeg hCdeg (hcore N q) E A out T
  choose H hdegree heval using ht
  refine ⟨∑ T : GraphTable N, H T, ?_, ?_⟩
  · have hS : 0 ≤ DegreeScale q := by
      have hq := query_scale_bound q
      have := Nat.cast_nonneg (α := ℝ) q
      linarith
    have hnonneg : 0 ≤ (Cdeg+4)*DegreeScale q := mul_nonneg (by linarith) hS
    have hn : (∑ T : GraphTable N, H T).totalDegree ≤ ⌊(Cdeg+4)*DegreeScale q⌋₊ := by
      apply (MvPolynomial.totalDegree_finsetSum _ _).trans
      apply Finset.sup_le
      intro T hT
      exact (Nat.le_floor_iff hnonneg).mpr (hdegree T)
    exact (show ((∑ T : GraphTable N, H T).totalDegree : ℝ) ≤ ⌊(Cdeg+4)*DegreeScale q⌋₊ by
      exact_mod_cast hn).trans (Nat.floor_le hnonneg)
  · intro M l hl hden
    unfold FormalGap FormalAcceptance
    rw [← sum_sub_distrib]
    calc
      _ = ∑ T : GraphTable N, l * Eval (H T) M l / Eval (Denominator q) M l := by
        apply sum_congr rfl
        intro T hT
        rw [← mul_sub]
        exact heval T M l hl hden
      _ = _ := by
        simp only [Eval, map_sum]
        rw [← sum_div, ← mul_sum]
