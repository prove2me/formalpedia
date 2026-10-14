-- Prove2me | solution 1 for StatComplexityDM.HellingerChain.hellinger_subadditivity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:26:50.977978+00:00
-- url     : https://prove2.me/submissions/e31e4fcf-083c-4ed4-9292-51f832e47ed7

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_HellingerChain_SeqLaw

set_option autoImplicit false
universe u

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_seqLaw_nonneg {n : ℕ} {X : Fin n → Type u} [∀ i, Fintype (X i)]
    (P : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ)
    (hP : IsSeqKernel P) (x : (j : Fin n) → X j) : 0 ≤ seqLaw P x :=
  Finset.prod_nonneg (fun i _ => (hP.1 i x).1 _)

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_hell_nonneg {Y : Type*} [Fintype Y] (p q : Y → ℝ) : 0 ≤ hellingerSq p q :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_hell_expand {Y : Type*} [Fintype Y] (p q : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (hq : ∀ y, 0 ≤ q y) :
    hellingerSq p q = ∑ y, p y + ∑ y, q y - 2 * ∑ y, Real.sqrt (p y * q y) := by
  unfold hellingerSq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have e1 := Real.sq_sqrt (hp y)
  have e2 := Real.sq_sqrt (hq y)
  rw [Real.sqrt_mul (hp y)]
  linear_combination e1 + e2

/-- The conditional system after fixing the first coordinate to `a`. -/
def hcChild {n : ℕ} {X : Fin (n + 1) → Type u}
    (P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ) (a : X 0) :
    (i : Fin n) → ((j : Fin n) → X j.succ) → X i.succ → ℝ :=
  fun i t b => P i.succ (Fin.cons a t : (j : Fin (n + 1)) → X j) b

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_child_kernel {n : ℕ} {X : Fin (n + 1) → Type u} [∀ i, Fintype (X i)]
    (P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ)
    (hP : IsSeqKernel P) (a : X 0) : IsSeqKernel (X := fun i : Fin n => X i.succ) (hcChild P a) := by
  refine ⟨fun i t => hP.1 i.succ _, fun i t t' h => ?_⟩
  funext b
  have := hP.2 i.succ (Fin.cons a t : (j : Fin (n + 1)) → X j) (Fin.cons a t' : (j : Fin (n + 1)) → X j) (by
    intro j hj
    induction j using Fin.cases with
    | zero => simp
    | succ k =>
      simp only [Fin.cons_succ]
      exact h k (Fin.succ_lt_succ_iff.mp hj))
  exact congrFun this b

theorem hc_sum_cons {n : ℕ} {X : Fin (n + 1) → Type u} [∀ i, Fintype (X i)]
    (f : ((j : Fin (n + 1)) → X j) → ℝ) :
    ∑ x, f x = ∑ a : X 0, ∑ t : ((j : Fin n) → X j.succ), f (Fin.cons a t) := by
  rw [← (Fin.consEquiv X).sum_comp, Fintype.sum_prod_type]
  rfl

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_seqLaw_cons {n : ℕ} {X : Fin (n + 1) → Type u}
    (P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ) (a : X 0)
    (t : (j : Fin n) → X j.succ) :
    seqLaw P (Fin.cons a t : (j : Fin (n + 1)) → X j) =
      P 0 (Fin.cons a t : (j : Fin (n + 1)) → X j) a *
        seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t := by
  unfold seqLaw
  rw [Fin.prod_univ_succ]
  simp [hcChild]

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_seqLaw_cons_root {n : ℕ} {X : Fin (n + 1) → Type u} [∀ i, Fintype (X i)]
    (P : (i : Fin (n + 1)) → ((j : Fin (n + 1)) → X j) → X i → ℝ) (hP : IsSeqKernel P)
    (x₀ : (j : Fin (n + 1)) → X j) (a : X 0)
    (t : (j : Fin n) → X j.succ) :
    seqLaw P (Fin.cons a t : (j : Fin (n + 1)) → X j) =
      P 0 x₀ a * seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t := by
  rw [hc_seqLaw_cons]
  have := hP.2 0 (Fin.cons a t : (j : Fin (n + 1)) → X j) x₀
    (fun j hj => absurd hj (Fin.not_lt_zero j))
  rw [this]

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_norm : ∀ (n : ℕ) {X : Fin n → Type u} [∀ i, Fintype (X i)]
    (_ : ∀ i, Nonempty (X i))
    (P : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) (_ : IsSeqKernel P),
    ∑ x, seqLaw P x = 1 := by
  intro n
  induction n with
  | zero =>
    intro X _ hne P hP
    simp [seqLaw]
  | succ n ih =>
    intro X _ hne P hP
    set x₀ : (j : Fin (n + 1)) → X j := fun j => Classical.choice (hne j) with hx₀
    rw [hc_sum_cons]
    have key : ∀ a : X 0, ∑ t : ((j : Fin n) → X j.succ),
        seqLaw P (Fin.cons a t : (j : Fin (n + 1)) → X j) = P 0 x₀ a := by
      intro a
      have hc := ih (X := fun i : Fin n => X i.succ) (fun i => hne i.succ) (hcChild P a)
        (hc_child_kernel P hP a)
      simp_rw [hc_seqLaw_cons_root P hP x₀ a]
      rw [← Finset.mul_sum, hc, mul_one]
    simp_rw [key]
    exact (hP.1 0 x₀).2

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_cond_nonneg {n : ℕ} {X : Fin n → Type u} [∀ i, Fintype (X i)]
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) (hP : IsSeqKernel P) :
    0 ≤ condHellingerSum P Q :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hc_seqLaw_nonneg P hP x)
    (Finset.sum_nonneg (fun i _ => hc_hell_nonneg _ _)))

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_hell_law {n : ℕ} {X : Fin n → Type u} [∀ i, Fintype (X i)]
    (hne : ∀ i, Nonempty (X i))
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) (hP : IsSeqKernel P)
    (hQ : IsSeqKernel Q) :
    hellingerSq (seqLaw P) (seqLaw Q) =
      2 - 2 * ∑ x, Real.sqrt (seqLaw P x * seqLaw Q x) := by
  rw [hc_hell_expand _ _ (hc_seqLaw_nonneg P hP) (hc_seqLaw_nonneg Q hQ), hc_norm n hne P hP,
    hc_norm n hne Q hQ]
  ring

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem hc_core : ∀ (n : ℕ) {X : Fin n → Type u} [∀ i, Fintype (X i)]
    (_ : ∀ i, Nonempty (X i))
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) (_ : IsSeqKernel P)
    (_ : IsSeqKernel Q) (α β : ℝ), 0 ≤ α → 0 ≤ β →
    α * β * (1 - ∑ x, Real.sqrt (seqLaw P x * seqLaw Q x)) ≤
      5 * α ^ 2 * (condHellingerSum P Q / 2) +
      5 / 16 * ((α - β) ^ 2 + 2 * α * β * (1 - ∑ x, Real.sqrt (seqLaw P x * seqLaw Q x))) := by
  intro n
  induction n with
  | zero =>
    intro X _ hne P Q hP hQ α β hα hβ
    simp [seqLaw, condHellingerSum]
    nlinarith [sq_nonneg (α - β)]
  | succ n ih =>
    intro X _ hne P Q hP hQ α β hα hβ
    set x₀ : (j : Fin (n + 1)) → X j := fun j => Classical.choice (hne j) with hx₀
    set p : X 0 → ℝ := P 0 x₀ with hp
    set q : X 0 → ℝ := Q 0 x₀ with hq
    have hp0 : ∀ a, 0 ≤ p a := fun a => (hP.1 0 x₀).1 a
    have hq0 : ∀ a, 0 ≤ q a := fun a => (hQ.1 0 x₀).1 a
    have hp1 : ∑ a, p a = 1 := (hP.1 0 x₀).2
    have hq1 : ∑ a, q a = 1 := (hQ.1 0 x₀).2
    have hne' : ∀ i : Fin n, Nonempty (X i.succ) := fun i => hne i.succ
    obtain ⟨A, hA⟩ : ∃ A : X 0 → ℝ, ∀ a, A a = ∑ t : ((j : Fin n) → X j.succ),
        Real.sqrt (seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t *
          seqLaw (X := fun i : Fin n => X i.succ) (hcChild Q a) t) := ⟨_, fun _ => rfl⟩
    obtain ⟨C, hC⟩ : ∃ C : X 0 → ℝ, ∀ a,
        C a = condHellingerSum (X := fun i : Fin n => X i.succ) (hcChild P a) (hcChild Q a) :=
      ⟨_, fun _ => rfl⟩
    have hAeq : ∑ x, Real.sqrt (seqLaw P x * seqLaw Q x) =
        ∑ a, Real.sqrt (p a * q a) * A a := by
      rw [hc_sum_cons]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [hc_seqLaw_cons_root P hP x₀, hc_seqLaw_cons_root Q hQ x₀]
      have : p a * seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t *
          (q a * seqLaw (X := fun i : Fin n => X i.succ) (hcChild Q a) t) =
          (p a * q a) * (seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t *
            seqLaw (X := fun i : Fin n => X i.succ) (hcChild Q a) t) := by ring
      rw [this, Real.sqrt_mul (mul_nonneg (hp0 a) (hq0 a))]
    have hCeq : condHellingerSum P Q = hellingerSq p q + ∑ a, p a * C a := by
      unfold condHellingerSum
      rw [hc_sum_cons]
      have hP' := fun a => hc_norm n hne' (hcChild P a) (hc_child_kernel P hP a)
      have e : ∀ (a : X 0) (t : (j : Fin n) → X j.succ),
          seqLaw P (Fin.cons a t : (j : Fin (n + 1)) → X j) *
            ∑ i, hellingerSq (P i (Fin.cons a t : (j : Fin (n + 1)) → X j))
              (Q i (Fin.cons a t : (j : Fin (n + 1)) → X j)) =
          p a * (seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t * hellingerSq p q +
            seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t *
              ∑ j : Fin n, hellingerSq (hcChild P a j t) (hcChild Q a j t)) := by
        intro a t
        rw [hc_seqLaw_cons_root P hP x₀, Fin.sum_univ_succ]
        have h0 : P 0 (Fin.cons a t : (j : Fin (n + 1)) → X j) = p :=
          hP.2 0 _ _ (fun j hj => absurd hj (Fin.not_lt_zero j))
        have h0' : Q 0 (Fin.cons a t : (j : Fin (n + 1)) → X j) = q :=
          hQ.2 0 _ _ (fun j hj => absurd hj (Fin.not_lt_zero j))
        rw [h0, h0']
        have hs : (∑ i : Fin n, hellingerSq (P i.succ (Fin.cons a t : (j : Fin (n + 1)) → X j))
            (Q i.succ (Fin.cons a t : (j : Fin (n + 1)) → X j))) =
            ∑ j : Fin n, hellingerSq (hcChild P a j t) (hcChild Q a j t) := rfl
        have hpa : P 0 x₀ a = p a := rfl
        rw [hs, hpa]
        ring
      have per : ∀ a : X 0, ∑ t : ((j : Fin n) → X j.succ),
          p a * (seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t * hellingerSq p q +
            seqLaw (X := fun i : Fin n => X i.succ) (hcChild P a) t *
              ∑ j : Fin n, hellingerSq (hcChild P a j t) (hcChild Q a j t)) =
          p a * (hellingerSq p q + C a) := by
        intro a
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hP' a, hC a]
        unfold condHellingerSum
        rw [one_mul]
      simp_rw [e, per]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
    have hd0 : 0 ≤ hellingerSq p q := hc_hell_nonneg p q
    have hsum_s : ∑ a, Real.sqrt (p a * q a) = 1 - hellingerSq p q / 2 := by
      rw [hc_hell_expand p q hp0 hq0, hp1, hq1]; ring
    have hs0 : ∀ a, 0 ≤ Real.sqrt (p a * q a) := fun a => Real.sqrt_nonneg _
    have hA0 : ∀ a, 0 ≤ A a := fun a => by
      rw [hA]; exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
    -- per-coordinate inequality from the induction hypothesis
    have step : ∀ a : X 0, α * β * Real.sqrt (p a * q a) - α * β * (Real.sqrt (p a * q a) * A a) ≤
        5 * α ^ 2 / 2 * (p a * C a) + 5 / 16 * α ^ 2 * p a + 5 / 16 * β ^ 2 * q a
          - 5 / 8 * α * β * (Real.sqrt (p a * q a) * A a) := by
      intro a
      have ih' := ih (X := fun i : Fin n => X i.succ) hne' (hcChild P a) (hcChild Q a)
        (hc_child_kernel P hP a) (hc_child_kernel Q hQ a) (α * Real.sqrt (p a))
        (β * Real.sqrt (q a)) (mul_nonneg hα (Real.sqrt_nonneg _))
        (mul_nonneg hβ (Real.sqrt_nonneg _))
      rw [← hA a, ← hC a] at ih'
      have e1 : Real.sqrt (p a) ^ 2 = p a := Real.sq_sqrt (hp0 a)
      have e2 : Real.sqrt (q a) ^ 2 = q a := Real.sq_sqrt (hq0 a)
      have e3 : Real.sqrt (p a * q a) = Real.sqrt (p a) * Real.sqrt (q a) :=
        Real.sqrt_mul (hp0 a) _
      rw [e3]
      have hpa : p a = Real.sqrt (p a) ^ 2 := e1.symm
      have hqa : q a = Real.sqrt (q a) ^ 2 := e2.symm
      generalize Real.sqrt (p a) = ra at hpa ih' ⊢
      generalize Real.sqrt (q a) = rb at hqa ih' ⊢
      rw [hpa, hqa]
      nlinarith [ih']
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => step a)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    rw [hsum_s, ← hAeq, hp1, hq1] at hsum
    have hCp : ∑ a, p a * C a = condHellingerSum P Q - hellingerSq p q := by
      rw [hCeq]; ring
    rw [hCp] at hsum
    have hC0 := hc_cond_nonneg P Q hP
    have hAle : (∑ x, Real.sqrt (seqLaw P x * seqLaw Q x)) ≤ 1 := by
      have := hc_hell_law hne P Q hP hQ
      have h2 : 0 ≤ hellingerSq (seqLaw P) (seqLaw Q) := hc_hell_nonneg _ _
      linarith
    have hAge : 0 ≤ ∑ x, Real.sqrt (seqLaw P x * seqLaw Q x) :=
      Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
    by_cases hcase : β ≤ 5 * α
    · have key : α * β * hellingerSq p q / 2 ≤ 5 * α ^ 2 * hellingerSq p q / 2 := by
        nlinarith [mul_nonneg (mul_nonneg hα (sub_nonneg.2 hcase)) hd0]
      nlinarith [hsum, key]
    · rw [not_le] at hcase
      have h1 : 4 * β / 5 ≤ β - α := by linarith
      have h2 : (4 * β / 5) ^ 2 ≤ (β - α) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      have h3 : α * β ≤ β ^ 2 / 5 := by nlinarith
      have h4 : 0 ≤ α * β * (1 - ∑ x, Real.sqrt (seqLaw P x * seqLaw Q x)) :=
        mul_nonneg (mul_nonneg hα hβ) (by linarith)
      have h5 : α * β * (1 - ∑ x, Real.sqrt (seqLaw P x * seqLaw Q x)) ≤ α * β := by
        nlinarith [mul_nonneg hα hβ]
      have h6 : 0 ≤ 5 * α ^ 2 * (condHellingerSum P Q / 2) := by positivity
      nlinarith [h2, h3, h4, h5, h6]

open StatComplexityDM.HellingerChain FoundationsRL.GeneralDM in
theorem solution {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ)
    (hP : IsSeqKernel P) (hQ : IsSeqKernel Q) (hn : 2 ≤ n) :
    hellingerSq (seqLaw P) (seqLaw Q) ≤ 10 ^ 2 * Real.log n * condHellingerSum P Q := by
  by_cases hne : ∀ i, Nonempty (X i)
  · have h1 := hc_core n hne P Q hP hQ 1 1 zero_le_one zero_le_one
    have hD := hc_hell_law hne P Q hP hQ
    have hC0 := hc_cond_nonneg P Q hP
    have hlog : (69 : ℝ) / 100 ≤ Real.log n := by
      have : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      linarith [Real.log_two_gt_d9]
    rw [hD]
    nlinarith [mul_nonneg (sub_nonneg.2 hlog) hC0]
  · simp only [not_forall, not_nonempty_iff] at hne
    obtain ⟨i, hi⟩ := hne
    have : IsEmpty ((j : Fin n) → X j) := ⟨fun x => hi.false (x i)⟩
    simp [hellingerSq, condHellingerSum]
