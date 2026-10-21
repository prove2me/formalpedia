-- Prove2me | solution 1 for StatComplexityDM.HellingerChain.kl_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:13:11.483311+00:00
-- url     : https://prove2.me/submissions/f37ea192-a703-405b-8679-3a693a5bbab4

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_HellingerChain_SeqLaw

set_option autoImplicit false
open FoundationsRL.GeneralDM StatComplexityDM.HellingerChain

universe u

lemma fup_gibbs {Y : Type*} [Fintype Y] (q p : Y → ℝ) (hq : ∀ y, 0 ≤ q y) (hp : ∀ y, 0 ≤ p y)
    (hq1 : ∑ y, q y = 1) (hp1 : ∑ y, p y = 1) (hac : ∀ y, p y = 0 → q y = 0) :
    0 ≤ ∑ y, q y * Real.log (q y / p y) := by
  have h : ∀ y, q y - p y ≤ q y * Real.log (q y / p y) := by
    intro y
    by_cases h : q y = 0
    · rw [h]; linarith [hp y]
    · have hqpos : 0 < q y := lt_of_le_of_ne (hq y) (Ne.symm h)
      have hppos : 0 < p y := lt_of_le_of_ne (hp y) (fun h0 => h (hac y h0.symm))
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hqpos hppos)
      have h2 := mul_le_mul_of_nonneg_left h1 hqpos.le
      have h3 : q y * (1 - (q y / p y)⁻¹) = q y - p y := by field_simp
      linarith
  have := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => h y)
  rw [Finset.sum_sub_distrib, hq1, hp1] at this
  linarith

section peel
variable {n : ℕ} {X : Fin (n + 1) → Type u}

def tailK (P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ) (a : X 0) :
    (i : Fin n) → ((j : Fin n) → X j.succ) → X i.succ → ℝ :=
  fun i x' b => P i.succ (Fin.cons a x' : (j : Fin (n + 1)) → X j) b

lemma tail_isSeq [∀ i, Fintype (X i)]
    {P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ}
    (hP : IsSeqKernel P) (a : X 0) : IsSeqKernel (tailK P a) := by
  refine ⟨fun i x => hP.1 i.succ _, ?_⟩
  intro i x x' hxx
  have := hP.2 i.succ (Fin.cons a x : (j : Fin (n + 1)) → X j) (Fin.cons a x') (by
    intro j hj
    induction j using Fin.cases with
    | zero => simp
    | succ j' =>
      simp only [Fin.cons_succ]
      exact hxx j' (Fin.succ_lt_succ_iff.mp hj))
  funext b
  exact congrFun this b

lemma P0_const {P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ}
    (hP : ∀ i x x', (∀ j, j < i → x j = x' j) → P i x = P i x') (y y' : (j : Fin (n + 1)) → X j) :
    P 0 y = P 0 y' := hP 0 y y' (fun j hj => absurd hj (Fin.not_lt_zero j))

lemma seqLaw_cons (P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ)
    (a : X 0) (x' : (j : Fin n) → X j.succ) :
    seqLaw P (Fin.cons a x' : (j : Fin (n + 1)) → X j) =
      P 0 (Fin.cons a x' : (j : Fin (n + 1)) → X j) a * seqLaw (tailK P a) x' := by
  unfold seqLaw
  rw [Fin.prod_univ_succ]
  simp [tailK]

lemma sum_cons {M : Type*} [AddCommMonoid M] [∀ i, Fintype (X i)]
    (f : ((j : Fin (n + 1)) → X j) → M) :
    ∑ y, f y = ∑ a, ∑ x' : (j : Fin n) → X j.succ, f (Fin.cons a x') := by
  rw [← (Fin.consEquiv X).sum_comp, Fintype.sum_prod_type]
  rfl

end peel

lemma seqLaw_nonneg {n : ℕ} {X : Fin n → Type u} [∀ i, Fintype (X i)]
    {P : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ} (hP : IsSeqKernel P) (x : (j : Fin n) → X j) :
    0 ≤ seqLaw P x :=
  Finset.prod_nonneg (fun i _ => (hP.1 i x).1 (x i))

lemma seqLaw_sum : ∀ (n : ℕ) (X : Fin n → Type u) [∀ i, Fintype (X i)]
    (P : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) (_hP : IsSeqKernel P)
    (_hne : Nonempty ((j : Fin n) → X j)), ∑ x, seqLaw P x = 1 := by
  intro n
  induction n with
  | zero =>
    intro X _ P hP hne
    simp [seqLaw]
  | succ n ih =>
    intro X _ P hP hne
    obtain ⟨y0⟩ := hne
    have hne' : Nonempty ((j : Fin n) → X j.succ) := ⟨fun j => y0 j.succ⟩
    rw [sum_cons]
    have : ∀ a (x' : (j : Fin n) → X j.succ), seqLaw P (Fin.cons a x' : (j : Fin (n + 1)) → X j) =
        P 0 y0 a * seqLaw (tailK P a) x' := by
      intro a x'
      rw [seqLaw_cons, P0_const hP.2 _ y0]
    simp_rw [this, ← Finset.mul_sum]
    have h1 : ∀ a, ∑ x', seqLaw (tailK P a) x' = 1 := fun a =>
      ih (fun j => X j.succ) (tailK P a) (tail_isSeq hP a) hne'
    simp_rw [h1, mul_one]
    exact (hP.1 0 y0).2

theorem chain : ∀ (n : ℕ) (X : Fin n → Type u) [∀ i, Fintype (X i)]
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ)
    (_hP : IsSeqKernel P) (_hQ : IsSeqKernel Q),
    klDivDiscrete (seqLaw Q) (seqLaw P) =
      ∑ x : (j : Fin n) → X j,
        ENNReal.ofReal (seqLaw Q x) * ∑ i, klDivDiscrete (Q i x) (P i x) := by
  intro n
  induction n with
  | zero =>
    intro X _ P Q hP hQ
    simp [klDivDiscrete, seqLaw]
  | succ n ih =>
    intro X _ P Q hP hQ
    rcases isEmpty_or_nonempty ((j : Fin (n + 1)) → X j) with hE | hne
    · simp [klDivDiscrete]
    obtain ⟨y0⟩ := hne
    have hne' : Nonempty ((j : Fin n) → X j.succ) := ⟨fun j => y0 j.succ⟩
    by_cases hAC : ∀ y, seqLaw P y = 0 → seqLaw Q y = 0
    swap
    · -- Q is not absolutely continuous w.r.t. P: both sides are ⊤
      rw [klDivDiscrete, if_neg hAC]
      push_neg at hAC
      obtain ⟨y, hPy, hQy⟩ := hAC
      symm
      rw [ENNReal.sum_eq_top]
      refine ⟨y, Finset.mem_univ _, ?_⟩
      have hQpos : 0 < seqLaw Q y := lt_of_le_of_ne (seqLaw_nonneg hQ y) (Ne.symm hQy)
      rw [ENNReal.mul_eq_top]
      left
      refine ⟨(ENNReal.ofReal_pos.mpr hQpos).ne', ?_⟩
      · rw [ENNReal.sum_eq_top]
        unfold seqLaw at hPy hQy
        obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hPy
        refine ⟨i, Finset.mem_univ _, ?_⟩
        rw [klDivDiscrete, if_neg]
        intro hall
        have := hall (y i) hi
        exact (Finset.prod_ne_zero_iff.mp hQy i (Finset.mem_univ _)) this
    -- Q is absolutely continuous w.r.t. P
    set q0 := Q 0 y0 with hq0def
    set p0 := P 0 y0 with hp0def
    have hq0 : ∀ y, Q 0 y = q0 := fun y => P0_const hQ.2 y y0
    have hp0 : ∀ y, P 0 y = p0 := fun y => P0_const hP.2 y y0
    have hLQ : ∀ a (x' : (j : Fin n) → X j.succ),
        seqLaw Q (Fin.cons a x' : (j : Fin (n + 1)) → X j) = q0 a * seqLaw (tailK Q a) x' := by
      intro a x'; rw [seqLaw_cons, hq0]
    have hLP : ∀ a (x' : (j : Fin n) → X j.succ),
        seqLaw P (Fin.cons a x' : (j : Fin (n + 1)) → X j) = p0 a * seqLaw (tailK P a) x' := by
      intro a x'; rw [seqLaw_cons, hp0]
    have hq0nn : ∀ a, 0 ≤ q0 a := (hQ.1 0 y0).1
    have hp0nn : ∀ a, 0 ≤ p0 a := (hP.1 0 y0).1
    have hq0s : ∑ a, q0 a = 1 := (hQ.1 0 y0).2
    have hp0s : ∑ a, p0 a = 1 := (hP.1 0 y0).2
    have hQs : ∀ a, ∑ x', seqLaw (tailK Q a) x' = 1 := fun a =>
      seqLaw_sum n (fun j => X j.succ) (tailK Q a) (tail_isSeq hQ a) hne'
    have hPs : ∀ a, ∑ x', seqLaw (tailK P a) x' = 1 := fun a =>
      seqLaw_sum n (fun j => X j.succ) (tailK P a) (tail_isSeq hP a) hne'
    have hQnn : ∀ a x', 0 ≤ seqLaw (tailK Q a) x' := fun a x' => seqLaw_nonneg (tail_isSeq hQ a) x'
    have hPnn : ∀ a x', 0 ≤ seqLaw (tailK P a) x' := fun a x' => seqLaw_nonneg (tail_isSeq hP a) x'
    have AC0 : ∀ a, p0 a = 0 → q0 a = 0 := by
      intro a hpa
      by_contra hqa
      obtain ⟨x', hx'⟩ : ∃ x', seqLaw (tailK Q a) x' ≠ 0 := by
        by_contra h
        push_neg at h
        have := hQs a
        simp [h] at this
      have := hAC (Fin.cons a x') (by rw [hLP, hpa, zero_mul])
      rw [hLQ] at this
      exact mul_ne_zero hqa hx' this
    have ACa : ∀ a, q0 a ≠ 0 → ∀ x', seqLaw (tailK P a) x' = 0 → seqLaw (tailK Q a) x' = 0 := by
      intro a hqa x' hPx'
      by_contra hQx'
      have := hAC (Fin.cons a x') (by rw [hLP, hPx', mul_zero])
      rw [hLQ] at this
      exact mul_ne_zero hqa hQx' this
    set Ra : X 0 → ℝ := fun a => ∑ x', seqLaw (tailK Q a) x' *
      Real.log (seqLaw (tailK Q a) x' / seqLaw (tailK P a) x') with hRa
    set KL0 : ℝ := ∑ a, q0 a * Real.log (q0 a / p0 a) with hKL0
    have hKL0nn : 0 ≤ KL0 := fup_gibbs q0 p0 hq0nn hp0nn hq0s hp0s AC0
    have hRanonneg : ∀ a, 0 ≤ q0 a * Ra a := by
      intro a
      by_cases hqa : q0 a = 0
      · simp [hqa]
      · exact mul_nonneg (hq0nn a) (fup_gibbs _ _ (hQnn a) (hPnn a) (hQs a) (hPs a) (ACa a hqa))
    -- the real identity
    have hR : ∑ y, seqLaw Q y * Real.log (seqLaw Q y / seqLaw P y) = KL0 + ∑ a, q0 a * Ra a := by
      rw [sum_cons]
      have hterm : ∀ a (x' : (j : Fin n) → X j.succ),
          seqLaw Q (Fin.cons a x' : (j : Fin (n + 1)) → X j) *
            Real.log (seqLaw Q (Fin.cons a x' : (j : Fin (n + 1)) → X j) /
              seqLaw P (Fin.cons a x' : (j : Fin (n + 1)) → X j)) =
          q0 a * Real.log (q0 a / p0 a) * seqLaw (tailK Q a) x' +
            q0 a * (seqLaw (tailK Q a) x' *
              Real.log (seqLaw (tailK Q a) x' / seqLaw (tailK P a) x')) := by
        intro a x'
        by_cases h : q0 a * seqLaw (tailK Q a) x' = 0
        · rw [hLQ]
          rcases mul_eq_zero.mp h with h | h
          · rw [h]; simp
          · rw [h]; simp
        · obtain ⟨hqa, hlq⟩ := mul_ne_zero_iff.mp h
          have hPne : seqLaw P (Fin.cons a x' : (j : Fin (n + 1)) → X j) ≠ 0 := by
            intro h0
            have := hAC _ h0
            rw [hLQ] at this
            exact h this
          rw [hLP] at hPne
          obtain ⟨hpa, hlp⟩ := mul_ne_zero_iff.mp hPne
          rw [hLQ, hLP, mul_div_mul_comm, Real.log_mul (div_ne_zero hqa hpa) (div_ne_zero hlq hlp)]
          ring
      have e : ∀ a, ∑ x' : (j : Fin n) → X j.succ,
          (q0 a * Real.log (q0 a / p0 a) * seqLaw (tailK Q a) x' +
            q0 a * (seqLaw (tailK Q a) x' *
              Real.log (seqLaw (tailK Q a) x' / seqLaw (tailK P a) x'))) =
          q0 a * Real.log (q0 a / p0 a) + q0 a * Ra a := by
        intro a
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hQs, mul_one]
      rw [Finset.sum_congr rfl (fun a _ => by simp only [hterm]; exact e a),
        Finset.sum_add_distrib]
    rw [klDivDiscrete, if_pos hAC, hR]
    have hK0 : klDivDiscrete q0 p0 = ENNReal.ofReal KL0 := by rw [klDivDiscrete, if_pos AC0]
    have hKa : ∀ a, q0 a ≠ 0 → klDivDiscrete (seqLaw (tailK Q a)) (seqLaw (tailK P a)) =
        ENNReal.ofReal (Ra a) := by
      intro a hqa; rw [klDivDiscrete, if_pos (ACa a hqa)]
    have hrhs : ∀ a, ∑ x' : (j : Fin n) → X j.succ,
        ENNReal.ofReal (seqLaw Q (Fin.cons a x' : (j : Fin (n + 1)) → X j)) *
          ∑ i : Fin (n + 1), klDivDiscrete (Q i (Fin.cons a x' : (j : Fin (n + 1)) → X j))
            (P i (Fin.cons a x' : (j : Fin (n + 1)) → X j)) =
        ENNReal.ofReal (q0 a) * (ENNReal.ofReal KL0 + ENNReal.ofReal (Ra a)) := by
      intro a
      have ih' := ih (fun j => X j.succ) (tailK P a) (tailK Q a) (tail_isSeq hP a) (tail_isSeq hQ a)
      have hsum1 : ∑ x', ENNReal.ofReal (seqLaw (tailK Q a) x') = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun x' _ => hQnn a x'), hQs a, ENNReal.ofReal_one]
      have step : ∀ x' : (j : Fin n) → X j.succ,
          ENNReal.ofReal (seqLaw Q (Fin.cons a x' : (j : Fin (n + 1)) → X j)) *
            ∑ i : Fin (n + 1), klDivDiscrete (Q i (Fin.cons a x' : (j : Fin (n + 1)) → X j))
              (P i (Fin.cons a x' : (j : Fin (n + 1)) → X j)) =
          ENNReal.ofReal (q0 a) * (ENNReal.ofReal (seqLaw (tailK Q a) x') *
            (klDivDiscrete q0 p0 + ∑ i : Fin n,
              klDivDiscrete (tailK Q a i x') (tailK P a i x'))) := by
        intro x'
        rw [Fin.sum_univ_succ, hq0, hp0, hLQ, ENNReal.ofReal_mul (hq0nn a), mul_assoc]
        rfl
      simp_rw [step]
      rw [← Finset.mul_sum]
      have h2 : ∑ x' : (j : Fin n) → X j.succ, ENNReal.ofReal (seqLaw (tailK Q a) x') *
            (klDivDiscrete q0 p0 + ∑ i : Fin n, klDivDiscrete (tailK Q a i x') (tailK P a i x')) =
          klDivDiscrete q0 p0 + klDivDiscrete (seqLaw (tailK Q a)) (seqLaw (tailK P a)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum1, one_mul, ih']
      rw [h2]
      by_cases hqa : q0 a = 0
      · simp [hqa]
      · rw [hKa a hqa, hK0]
    rw [sum_cons]
    simp_rw [hrhs]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      ← ENNReal.ofReal_sum_of_nonneg (fun a _ => hq0nn a), hq0s, ENNReal.ofReal_one, one_mul,
      ENNReal.ofReal_add hKL0nn (Finset.sum_nonneg (fun a _ => hRanonneg a)),
      ENNReal.ofReal_sum_of_nonneg (fun a _ => hRanonneg a)]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.ofReal_mul (hq0nn a)]

theorem solution {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ)
    (hP : IsSeqKernel P) (hQ : IsSeqKernel Q) :
    klDivDiscrete (seqLaw Q) (seqLaw P) =
      ∑ x : (j : Fin n) → X j,
        ENNReal.ofReal (seqLaw Q x) * ∑ i, klDivDiscrete (Q i x) (P i x) :=
  chain n X P Q hP hQ
