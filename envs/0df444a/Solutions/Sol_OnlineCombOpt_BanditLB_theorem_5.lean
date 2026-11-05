-- Prove2me | solution 1 for OnlineCombOpt.BanditLB.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:37:44.776027+00:00
-- url     : https://prove2.me/submissions/fcc9fc82-4c9c-4f75-8b9a-32d8ec8f54fb

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Setting


open Finset

namespace BLBSol

section SeqLaw
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {X : Type*} [Fintype X]

/-- Law of a sequence built round by round from a kernel. -/
noncomputable def seqLaw (κ : (t : ℕ) → (Fin t → X) → X → ℝ) (N : ℕ) (y : Fin N → X) : ℝ :=
  ∏ t : Fin N, κ t.val (fun s : Fin t.val => y ⟨s.val, Nat.lt_trans s.isLt t.isLt⟩) (y t)

lemma sum_fin_succ_fun (N : ℕ) (F : (Fin (N + 1) → X) → ℝ) :
    ∑ y, F y = ∑ y : Fin N → X, ∑ x : X, F (Fin.snoc y x) := by
  rw [← (Fin.snocEquiv (fun _ => X)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma seqLaw_snoc (κ : (t : ℕ) → (Fin t → X) → X → ℝ) (N : ℕ) (y : Fin N → X) (x : X) :
    seqLaw κ (N + 1) (Fin.snoc y x) = seqLaw κ N y * κ N y x := by
  unfold seqLaw
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t _
    have h1 : (fun s : Fin (Fin.castSucc t).val =>
        (Fin.snoc y x : Fin (N + 1) → X) ⟨s.val, Nat.lt_trans s.isLt (Fin.castSucc t).isLt⟩) =
        (fun s : Fin t.val => y ⟨s.val, Nat.lt_trans s.isLt t.isLt⟩) := by
      funext s
      simp [Fin.snoc, Nat.lt_trans s.isLt t.isLt]
    simp only [Fin.val_castSucc] at h1 ⊢
    rw [h1]
    simp [Fin.snoc]
  · have h2 : (fun s : Fin (Fin.last N).val =>
        (Fin.snoc y x : Fin (N + 1) → X) ⟨s.val, Nat.lt_trans s.isLt (Fin.last N).isLt⟩) = y := by
      funext s
      simp [Fin.snoc]
    simp only [Fin.val_last] at h2 ⊢
    rw [h2]
    simp

variable (κ : (t : ℕ) → (Fin t → X) → X → ℝ)

lemma seqLaw_nonneg (hκ : ∀ t h x, 0 ≤ κ t h x) (N : ℕ) (y : Fin N → X) :
    0 ≤ seqLaw κ N y :=
  Finset.prod_nonneg (fun t _ => hκ _ _ _)

lemma seqLaw_sum (hsum : ∀ t h, ∑ x, κ t h x = 1) (N : ℕ) :
    ∑ y, seqLaw κ N y = 1 := by
  induction N with
  | zero => simp [seqLaw]
  | succ N ih =>
    rw [sum_fin_succ_fun]
    simp_rw [seqLaw_snoc, ← Finset.mul_sum, hsum, mul_one]
    exact ih

/-- Marginal of the first `t + 1` rounds. -/
lemma seqLaw_marg (hsum : ∀ t h, ∑ x, κ t h x = 1) (t : ℕ) (F : (Fin t → X) → X → ℝ) :
    ∀ N (ht : t < N),
    ∑ y : Fin N → X, seqLaw κ N y *
        F (fun s : Fin t => y ⟨s.val, Nat.lt_trans s.isLt ht⟩) (y ⟨t, ht⟩) =
      ∑ y' : Fin t → X, seqLaw κ t y' * ∑ x, κ t y' x * F y' x := by
  intro N
  induction N with
  | zero => intro ht; omega
  | succ N ih =>
    intro ht
    rw [sum_fin_succ_fun]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
    · have : ∀ (y : Fin N → X) (x : X),
          seqLaw κ (N + 1) (Fin.snoc y x) *
            F (fun s : Fin t => (Fin.snoc y x : Fin (N + 1) → X) ⟨s.val, Nat.lt_trans s.isLt ht⟩)
              ((Fin.snoc y x : Fin (N + 1) → X) ⟨t, ht⟩) =
          (seqLaw κ N y * F (fun s : Fin t => y ⟨s.val, Nat.lt_trans s.isLt hlt⟩) (y ⟨t, hlt⟩)) *
            κ N y x := by
        intro y x
        rw [seqLaw_snoc]
        have e1 : (fun s : Fin t => (Fin.snoc y x : Fin (N + 1) → X) ⟨s.val, Nat.lt_trans s.isLt ht⟩)
            = (fun s : Fin t => y ⟨s.val, Nat.lt_trans s.isLt hlt⟩) := by
          funext s; simp [Fin.snoc, Nat.lt_trans s.isLt hlt]
        have e2 : (Fin.snoc y x : Fin (N + 1) → X) ⟨t, ht⟩ = y ⟨t, hlt⟩ := by
          simp [Fin.snoc, hlt]
        rw [e1, e2]; ring
      simp_rw [this, ← Finset.mul_sum, hsum, mul_one]
      exact ih hlt
    · subst heq
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [seqLaw_snoc]
      have e1 : (fun s : Fin t => (Fin.snoc y x : Fin (t + 1) → X) ⟨s.val, Nat.lt_trans s.isLt ht⟩)
          = y := by
        funext s; simp [Fin.snoc]
      have e2 : (Fin.snoc y x : Fin (t + 1) → X) ⟨t, ht⟩ = x := by
        simp [Fin.snoc]
      rw [e1, e2]; ring

/-- Marginal form for a function of the current round only. -/
lemma seqLaw_marg' (hsum : ∀ t h, ∑ x, κ t h x = 1) (N : ℕ) (t : Fin N) (F : X → ℝ) :
    ∑ y : Fin N → X, seqLaw κ N y * F (y t) =
      ∑ y' : Fin t.val → X, seqLaw κ t.val y' * ∑ x, κ t.val y' x * F x := by
  have := seqLaw_marg κ hsum t.val (fun _ x => F x) N t.isLt
  simpa using this

end SeqLaw

end BLBSol


open Finset

namespace BLBSol

/-- KL divergence on a finite type. -/
noncomputable def klS {ι : Type*} [Fintype ι] (Q P : ι → ℝ) : ℝ :=
  ∑ x, Q x * Real.log (Q x / P x)

lemma kl_term_le_chi2 (Q P : ℝ) (hQ : 0 ≤ Q) (hP : 0 < P) :
    Q * Real.log (Q / P) ≤ (Q - P) ^ 2 / P + (Q - P) := by
  rcases hQ.eq_or_lt with h | h
  · subst h; simp
    rw [sq, mul_div_assoc, div_self hP.ne', mul_one]
  · have h1 := Real.log_le_sub_one_of_pos (div_pos h hP)
    have h2 : Q * Real.log (Q / P) ≤ Q * (Q / P - 1) := mul_le_mul_of_nonneg_left h1 h.le
    have h3 : (Q - P) ^ 2 / P + (Q - P) = Q * (Q / P - 1) := by
      field_simp; ring
    linarith

lemma kl_le_chi2 {ι : Type*} [Fintype ι] (Q P : ι → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hP : ∀ x, 0 < P x) (hs : ∑ x, Q x = ∑ x, P x) :
    klS Q P ≤ ∑ x, (Q x - P x) ^ 2 / P x := by
  unfold klS
  calc ∑ x, Q x * Real.log (Q x / P x) ≤ ∑ x, ((Q x - P x) ^ 2 / P x + (Q x - P x)) :=
        Finset.sum_le_sum (fun x _ => kl_term_le_chi2 _ _ (hQ x) (hP x))
    _ = ∑ x, (Q x - P x) ^ 2 / P x := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs, sub_self, add_zero]

lemma logsum_point (Q P c : ℝ) (hQ : 0 ≤ Q) (hP : 0 ≤ P) (hac : 0 < Q → 0 < P) (hc : 0 < c) :
    Q * Real.log c + Q - P * c ≤ Q * Real.log (Q / P) := by
  rcases hQ.eq_or_lt with h | h
  · subst h; simp; exact mul_nonneg hP hc.le
  · have hP' := hac h
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h (mul_pos hP' hc))
    rw [Real.log_div h.ne' (mul_pos hP' hc).ne', Real.log_mul hP'.ne' hc.ne'] at h1
    rw [Real.log_div h.ne' hP'.ne']
    have h2 : (Q / (P * c))⁻¹ = P * c / Q := by rw [inv_div]
    rw [h2] at h1
    have h3 : Q * (1 - P * c / Q) = Q - P * c := by field_simp
    have h4 := mul_le_mul_of_nonneg_left h1 h.le
    nlinarith

lemma logsum {ι : Type*} (s : Finset ι) (Q P : ι → ℝ) (hQ : ∀ x ∈ s, 0 ≤ Q x)
    (hP : ∀ x ∈ s, 0 ≤ P x) (hac : ∀ x ∈ s, 0 < Q x → 0 < P x) :
    (∑ x ∈ s, Q x) * Real.log ((∑ x ∈ s, Q x) / (∑ x ∈ s, P x)) ≤
      ∑ x ∈ s, Q x * Real.log (Q x / P x) := by
  have hQs : 0 ≤ ∑ x ∈ s, Q x := Finset.sum_nonneg hQ
  rcases hQs.eq_or_lt with h | h
  · rw [← h]; simp only [zero_mul]
    have : ∀ x ∈ s, Q x = 0 := (Finset.sum_eq_zero_iff_of_nonneg hQ).mp h.symm
    rw [Finset.sum_eq_zero]; intro x hx; rw [this x hx]; simp
  · obtain ⟨x0, hx0, hQx0⟩ : ∃ x ∈ s, 0 < Q x := by
      by_contra hcon
      push Not at hcon
      have : ∀ x ∈ s, Q x = 0 := fun x hx => le_antisymm (hcon x hx) (hQ x hx)
      rw [Finset.sum_eq_zero this] at h; exact lt_irrefl _ h
    have hPs : 0 < ∑ x ∈ s, P x :=
      lt_of_lt_of_le (hac x0 hx0 hQx0) (Finset.single_le_sum hP hx0)
    set c := (∑ x ∈ s, Q x) / (∑ x ∈ s, P x) with hc
    have hcpos : 0 < c := div_pos h hPs
    have hsum := Finset.sum_le_sum (fun x hx => logsum_point (Q x) (P x) c (hQ x hx) (hP x hx)
      (hac x hx) hcpos)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
    have : (∑ x ∈ s, P x) * c = ∑ x ∈ s, Q x := by rw [hc]; field_simp
    linarith

lemma pinsker_two (p q : ℝ) (hq : 0 ≤ q) (hqp : q < p) (hp1 : p < 1) :
    2 * (p - q) ^ 2 ≤ q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) := by
  set φ : ℝ → ℝ := fun x => q * Real.log q - q * Real.log x + (1 - q) * Real.log (1 - q)
      - (1 - q) * Real.log (1 - x) - 2 * (x - q) ^ 2 with hφ
  have hderiv : ∀ x ∈ Set.Ioo q p, HasDerivAt φ (-(q * x⁻¹) - (1 - q) * ((-1) / (1 - x))
      - 2 * (2 * (x - q))) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have := hx.1; intro h; linarith
    have hx1 : 1 - x ≠ 0 := by have := hx.2; intro h; linarith
    have h1 : HasDerivAt (fun x => Real.log x) x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun x => Real.log (1 - x)) ((-1) / (1 - x)) x := by
      have := ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).log (by simpa using hx1)
      simpa using this
    have h3 : HasDerivAt (fun x => (x - q) ^ 2) (2 * (x - q)) x := by
      have := ((hasDerivAt_id' x).sub_const q).pow 2
      exact this.congr_deriv (by norm_num)
    have := ((((hasDerivAt_const x (q * Real.log q)).sub (h1.const_mul q)).add
      (hasDerivAt_const x ((1 - q) * Real.log (1 - q)))).sub (h2.const_mul (1 - q))).sub
      (h3.const_mul 2)
    exact this.congr_deriv (by ring)
  have hmono : MonotoneOn φ (Set.Icc q p) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc q p)
    · rcases hq.eq_or_lt with h0 | h0
      · subst h0
        have : φ = fun x => -Real.log (1 - x) - 2 * (x - 0) ^ 2 := by
          funext x; simp [hφ]
        rw [this]
        apply ContinuousOn.sub
        · apply ContinuousOn.neg
          apply ContinuousOn.log (by fun_prop)
          intro x hx; have := hx.2; intro h; linarith
        · fun_prop
      · apply ContinuousOn.sub
        · apply ContinuousOn.sub
          · apply ContinuousOn.add
            · apply ContinuousOn.sub continuousOn_const
              apply ContinuousOn.mul continuousOn_const
              apply ContinuousOn.log continuousOn_id
              intro x hx; have := hx.1; simp; intro h; linarith
            · exact continuousOn_const
          · apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.log (by fun_prop)
            intro x hx; have := hx.2; intro h; linarith
        · fun_prop
    · rw [interior_Icc]
      intro x hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderiv x hx).deriv]
      have hx0 : 0 < x := lt_of_le_of_lt hq hx.1
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have : -(q * x⁻¹) - (1 - q) * ((-1) / (1 - x)) - 2 * (2 * (x - q)) =
          (x - q) * (1 - 2 * x) ^ 2 / (x * (1 - x)) := by
        field_simp; ring
      rw [this]
      apply div_nonneg
      · exact mul_nonneg (by linarith [hx.1]) (sq_nonneg _)
      · exact (mul_pos hx0 hx1).le
  have hle := hmono ⟨le_refl q, hqp.le⟩ ⟨hqp.le, le_refl p⟩ hqp.le
  have hφq : φ q = 0 := by simp [hφ]
  have hp0 : 0 < p := lt_of_le_of_lt hq hqp
  have hφp : φ p = q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))
      - 2 * (p - q) ^ 2 := by
    simp only [hφ]
    have e1 : Real.log ((1 - q) / (1 - p)) = Real.log (1 - q) - Real.log (1 - p) :=
      Real.log_div (by linarith) (by linarith)
    rw [e1]
    rcases hq.eq_or_lt with h0 | h0
    · subst h0; simp
    · rw [Real.log_div h0.ne' hp0.ne']; ring
  linarith

lemma pinsker {ι : Type*} [Fintype ι] (P Q f : ι → ℝ) (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hP1 : ∑ x, P x = 1) (hQ1 : ∑ x, Q x = 1) (hac : ∀ x, 0 < Q x → 0 < P x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∑ x, P x * f x ≤ ∑ x, Q x * f x + Real.sqrt (klS Q P / 2) := by
  classical
  set S := Finset.univ.filter (fun x => Q x < P x) with hS
  set p := ∑ x ∈ S, P x with hp
  set q := ∑ x ∈ S, Q x with hq
  have step1 : ∑ x, P x * f x - ∑ x, Q x * f x ≤ p - q := by
    rw [← Finset.sum_sub_distrib, hp, hq, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => Q x < P x)]
    have h1 : ∑ x ∈ Finset.univ.filter (fun x => Q x < P x), (P x * f x - Q x * f x) ≤
        ∑ x ∈ Finset.univ.filter (fun x => Q x < P x), (P x - Q x) := by
      apply Finset.sum_le_sum; intro x hx
      simp only [Finset.mem_filter] at hx
      have := hf x
      nlinarith
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ Q x < P x), (P x * f x - Q x * f x) ≤ 0 := by
      apply Finset.sum_nonpos; intro x hx
      simp only [Finset.mem_filter] at hx
      have := hf x
      nlinarith
    linarith
  have hsq : 0 ≤ Real.sqrt (klS Q P / 2) := Real.sqrt_nonneg _
  by_cases hpq : p - q ≤ 0
  · linarith
  push Not at hpq
  have hq0 : 0 ≤ q := Finset.sum_nonneg (fun x _ => hQ x)
  have hpc : ∑ x ∈ Finset.univ.filter (fun x => ¬ Q x < P x), P x = 1 - p := by
    rw [← hP1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => Q x < P x)]; ring
  have hqc : ∑ x ∈ Finset.univ.filter (fun x => ¬ Q x < P x), Q x = 1 - q := by
    rw [← hQ1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => Q x < P x)]; ring
  have hp1 : p < 1 := by
    by_contra hcon
    have hple : p ≤ 1 := by
      rw [hp, ← hP1]; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => hP x)
    have hpeq : p = 1 := le_antisymm hple (not_lt.mp hcon)
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ Q x < P x), P x = 0 := by rw [hpc, hpeq]; ring
    have h0' := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hP x)).mp h0
    have hq0' : ∑ x ∈ Finset.univ.filter (fun x => ¬ Q x < P x), Q x = 0 := by
      apply Finset.sum_eq_zero; intro x hx
      rcases (hQ x).eq_or_lt with h | h
      · exact h.symm
      · have := hac x h; rw [h0' x hx] at this; exact absurd this (lt_irrefl _)
    rw [hqc] at hq0'
    linarith
  have hkl : q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) ≤ klS Q P := by
    unfold klS
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => Q x < P x)]
    have a1 := logsum (Finset.univ.filter (fun x => Q x < P x)) Q P (fun x _ => hQ x)
      (fun x _ => hP x) (fun x _ => hac x)
    have a2 := logsum (Finset.univ.filter (fun x => ¬ Q x < P x)) Q P (fun x _ => hQ x)
      (fun x _ => hP x) (fun x _ => hac x)
    rw [hpc, hqc] at a2
    rw [← hp, ← hq] at a1
    linarith
  have h2 := pinsker_two p q hq0 (by linarith) hp1
  have h3 : p - q ≤ Real.sqrt (klS Q P / 2) := by
    rw [← Real.sqrt_sq (by linarith : (0:ℝ) ≤ p - q)]
    apply Real.sqrt_le_sqrt
    linarith
  linarith

lemma sum_sqrt_le {ι : Type*} (s : Finset ι) (g : ι → ℝ) (hg : ∀ x ∈ s, 0 ≤ g x) :
    ∑ x ∈ s, Real.sqrt (g x) ≤ Real.sqrt ((s.card : ℝ) * ∑ x ∈ s, g x) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun x => Real.sqrt (g x))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h2 : ∑ x ∈ s, Real.sqrt (g x) ^ 2 = ∑ x ∈ s, g x :=
    Finset.sum_congr rfl (fun x hx => Real.sq_sqrt (hg x hx))
  rw [h2] at h
  rw [← Real.sqrt_sq (Finset.sum_nonneg (fun x _ => Real.sqrt_nonneg (g x)))]
  exact Real.sqrt_le_sqrt h

end BLBSol


open Finset Polynomial

namespace BLBSol

/-- Generating polynomial of a Bernoulli law. -/
noncomputable def Bp (p : ℝ) : ℝ[X] := C p * X + C (1 - p)

/-- Triangular discrimination between `F` and its shift. -/
noncomputable def Dsum (R : ℕ) (F : ℝ[X]) : ℝ :=
  ∑ v ∈ range R, ((X * F).coeff v - F.coeff v) ^ 2 / ((X * F).coeff v + F.coeff v)

def NonnegCoeff (F : ℝ[X]) : Prop := ∀ v, 0 ≤ F.coeff v

lemma coeff_X_mul' (F : ℝ[X]) (v : ℕ) :
    (X * F).coeff v = if v = 0 then 0 else F.coeff (v - 1) := by
  rcases v with _ | u
  · simp
  · simp [coeff_X_mul]

lemma nonnegCoeff_mul {F G : ℝ[X]} (hF : NonnegCoeff F) (hG : NonnegCoeff G) :
    NonnegCoeff (F * G) := by
  intro v
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hF _) (hG _))

lemma nonnegCoeff_X_mul {F : ℝ[X]} (hF : NonnegCoeff F) : NonnegCoeff (X * F) := by
  intro v; rw [coeff_X_mul']; split_ifs
  · exact le_refl _
  · exact hF _

lemma coeff_Bp_mul (p : ℝ) (F : ℝ[X]) (v : ℕ) :
    (Bp p * F).coeff v = (1 - p) * F.coeff v + p * (X * F).coeff v := by
  have : Bp p * F = C (1 - p) * F + C p * (X * F) := by unfold Bp; ring
  rw [this, coeff_add, coeff_C_mul, coeff_C_mul]

lemma nonnegCoeff_Bp {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : NonnegCoeff (Bp p) := by
  intro v
  have := coeff_Bp_mul p 1 v
  rw [mul_one] at this
  have hc : ∀ u, 0 ≤ (1:ℝ[X]).coeff u := by intro u; rw [coeff_one]; split_ifs <;> norm_num
  rw [this, coeff_X_mul']
  split_ifs
  · nlinarith [hc v]
  · nlinarith [hc v, hc (v - 1)]

lemma nonnegCoeff_prod {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    NonnegCoeff (∏ i ∈ s, Bp (p i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro v; rw [prod_empty, coeff_one]; split_ifs <;> norm_num
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact nonnegCoeff_mul (nonnegCoeff_Bp (hp a).1 (hp a).2) ih

lemma two_term (p a a' b b' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : |a| ≤ b) (hb' : |a'| ≤ b') :
    ((1 - p) * a + p * a') ^ 2 / ((1 - p) * b + p * b') ≤
      (1 - p) * (a ^ 2 / b) + p * (a' ^ 2 / b') := by
  have hb0 : 0 ≤ b := le_trans (abs_nonneg _) hb
  have hb0' : 0 ≤ b' := le_trans (abs_nonneg _) hb'
  have hR : 0 ≤ (1 - p) * (a ^ 2 / b) + p * (a' ^ 2 / b') := by
    apply add_nonneg
    · exact mul_nonneg (by linarith) (div_nonneg (sq_nonneg _) hb0)
    · exact mul_nonneg hp0 (div_nonneg (sq_nonneg _) hb0')
  set u := (1 - p) * b
  set w := p * b'
  have hu : 0 ≤ u := mul_nonneg (by linarith) hb0
  have hw : 0 ≤ w := mul_nonneg hp0 hb0'
  rcases (add_nonneg hu hw).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]; exact hR
  -- general case
  have ha2 : a ^ 2 ≤ b ^ 2 := by
    have := sq_abs a; nlinarith [abs_nonneg a]
  have ha2' : a' ^ 2 ≤ b' ^ 2 := by
    have := sq_abs a'; nlinarith [abs_nonneg a']
  rcases hu.eq_or_lt with hu0 | hu0
  · -- u = 0: either p = 1 or b = 0
    have hx : (1 - p) * a = 0 := by
      rcases mul_eq_zero.mp hu0.symm with h | h
      · rw [h, zero_mul]
      · have : a = 0 := by
          have : |a| ≤ 0 := h ▸ hb
          exact abs_nonpos_iff.mp this
        rw [this, mul_zero]
    rw [hx, zero_add, ← hu0, zero_add]
    have hwpos : 0 < w := by linarith
    have e1 : (p * a') ^ 2 / w = p * (a' ^ 2 / b') := by
      have hp' : p ≠ 0 := by intro h; simp [w, h] at hwpos
      have hb'' : b' ≠ 0 := by intro h; simp [w, h] at hwpos
      simp only [w]; field_simp
    have : 0 ≤ (1 - p) * (a ^ 2 / b) :=
      mul_nonneg (by linarith) (div_nonneg (sq_nonneg _) hb0)
    linarith
  rcases hw.eq_or_lt with hw0 | hw0
  · have hy : p * a' = 0 := by
      rcases mul_eq_zero.mp hw0.symm with h | h
      · rw [h, zero_mul]
      · have : a' = 0 := by
          have : |a'| ≤ 0 := h ▸ hb'
          exact abs_nonpos_iff.mp this
        rw [this, mul_zero]
    rw [hy, add_zero, ← hw0, add_zero]
    have e1 : ((1 - p) * a) ^ 2 / u = (1 - p) * (a ^ 2 / b) := by
      have hp' : 1 - p ≠ 0 := by intro h; simp [u, h] at hu0
      have hb'' : b ≠ 0 := by intro h; simp [u, h] at hu0
      simp only [u]; field_simp
    have : 0 ≤ p * (a' ^ 2 / b') :=
      mul_nonneg hp0 (div_nonneg (sq_nonneg _) hb0')
    linarith
  -- both positive
  have hp' : 1 - p ≠ 0 := by intro h; simp [u, h] at hu0
  have hb'' : b ≠ 0 := by intro h; simp [u, h] at hu0
  have hp'' : p ≠ 0 := by intro h; simp [w, h] at hw0
  have hb''' : b' ≠ 0 := by intro h; simp [w, h] at hw0
  have e1 : (1 - p) * (a ^ 2 / b) = ((1 - p) * a) ^ 2 / u := by simp only [u]; field_simp
  have e2 : p * (a' ^ 2 / b') = (p * a') ^ 2 / w := by simp only [w]; field_simp
  rw [e1, e2]
  set x := (1 - p) * a
  set y := p * a'
  rw [div_add_div _ _ hu0.ne' hw0.ne', div_le_div_iff₀ h0 (mul_pos hu0 hw0)]
  nlinarith [sq_nonneg (x * w - y * u), mul_pos hu0 hw0]

lemma Dsum_nonneg_term {F : ℝ[X]} (hF : NonnegCoeff F) (v : ℕ) :
    0 ≤ ((X * F).coeff v - F.coeff v) ^ 2 / ((X * F).coeff v + F.coeff v) :=
  div_nonneg (sq_nonneg _) (add_nonneg (nonnegCoeff_X_mul hF v) (hF v))

lemma Dsum_X_mul_le (R : ℕ) {F : ℝ[X]} (hF : NonnegCoeff F) : Dsum R (X * F) ≤ Dsum R F := by
  unfold Dsum
  rcases R with _ | R
  · simp
  rw [sum_range_succ', sum_range_succ]
  simp only [coeff_X_mul, coeff_X_mul_zero, sub_self, add_zero]
  have : (0:ℝ) ^ 2 / 0 = 0 := by simp
  rw [this, add_zero]
  linarith [Dsum_nonneg_term hF R]

lemma Dsum_Bp_mul_le (R : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {F : ℝ[X]}
    (hF : NonnegCoeff F) : Dsum R (Bp p * F) ≤ Dsum R F := by
  have h1 : Dsum R (Bp p * F) ≤ (1 - p) * Dsum R F + p * Dsum R (X * F) := by
    unfold Dsum
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro v _
    have e1 : (X * (Bp p * F)).coeff v = (1 - p) * (X * F).coeff v + p * (X * (X * F)).coeff v := by
      rw [← coeff_Bp_mul]; congr 1; ring
    rw [e1, coeff_Bp_mul]
    have hXF := nonnegCoeff_X_mul hF
    have hXXF := nonnegCoeff_X_mul hXF
    have := two_term p ((X * F).coeff v - F.coeff v) ((X * (X * F)).coeff v - (X * F).coeff v)
      ((X * F).coeff v + F.coeff v) ((X * (X * F)).coeff v + (X * F).coeff v) hp0 hp1
      (by rw [abs_le]; constructor <;> linarith [hF v, hXF v])
      (by rw [abs_le]; constructor <;> linarith [hXF v, hXXF v])
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_)) <;> ring
  have h2 := Dsum_X_mul_le R hF
  nlinarith

lemma Dsum_prod_mul_le {ι : Type*} (R : ℕ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (U : Finset ι) {G : ℝ[X]} (hG : NonnegCoeff G) :
    Dsum R ((∏ i ∈ U, Bp (p i)) * G) ≤ Dsum R G := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert a U ha ih =>
    rw [prod_insert ha, mul_assoc]
    refine le_trans (Dsum_Bp_mul_le R (p a) (hp a).1 (hp a).2 ?_) ih
    exact nonnegCoeff_mul (nonnegCoeff_prod U p hp) hG

lemma Dsum_subset_le {ι : Type*} [DecidableEq ι] (R : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {T T' : Finset ι} (h : T' ⊆ T) :
    Dsum R (∏ i ∈ T, Bp (p i)) ≤ Dsum R (∏ i ∈ T', Bp (p i)) := by
  rw [← Finset.prod_sdiff h]
  exact Dsum_prod_mul_le R p hp _ (nonnegCoeff_prod T' p hp)

lemma Dsum_mono_R {F : ℝ[X]} (hF : NonnegCoeff F) {R R' : ℕ} (h : R ≤ R') :
    Dsum R F ≤ Dsum R' F := by
  unfold Dsum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun v _ _ => Dsum_nonneg_term hF v)

end BLBSol


open Finset Polynomial

namespace BLBSol

lemma natDegree_Bp_le (p : ℝ) : (Bp p).natDegree ≤ 1 := natDegree_linear_le

lemma eval_one_Bp (p : ℝ) : (Bp p).eval 1 = 1 := by simp [Bp]

lemma sum_coeff_eq_one {F : ℝ[X]} {R : ℕ} (hR : F.natDegree < R) (h1 : F.eval 1 = 1) :
    ∑ v ∈ range R, F.coeff v = 1 := by
  rw [← h1, eval_eq_sum_range' hR]; simp

lemma coeff_X_mul_derivative (F : ℝ[X]) (v : ℕ) :
    (X * derivative F).coeff v = (v : ℝ) * F.coeff v := by
  rcases v with _ | u
  · simp
  · rw [coeff_X_mul, coeff_derivative]; push_cast; ring

lemma binom_identity (q : ℝ) (N v : ℕ) :
    ((N + 1 : ℝ) * q * (1 - q)) * ((X * Bp q ^ N).coeff v - (Bp q ^ N).coeff v) =
      (Bp q ^ (N + 1)).coeff v * ((v : ℝ) - (N + 1) * q) := by
  have hpoly : C ((N + 1 : ℝ) * q * (1 - q)) * (X * Bp q ^ N - Bp q ^ N) =
      X * derivative (Bp q ^ (N + 1)) - C ((N + 1 : ℝ) * q) * Bp q ^ (N + 1) := by
    rw [derivative_pow]
    have hd : derivative (Bp q) = C q := by
      simp [Bp]
    rw [hd]
    simp only [Nat.add_sub_cancel, Bp, map_mul, map_sub, map_one, map_add, map_natCast]
    push_cast
    ring
  have := congrArg (fun F => F.coeff v) hpoly
  simp only [coeff_C_mul, coeff_sub, coeff_X_mul_derivative] at this
  rw [this]; ring

lemma Dsum_binom_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (N R : ℕ) (hR : N + 2 ≤ R) :
    Dsum R (Bp q ^ N) ≤ max q (1 - q) / ((N + 1) * q * (1 - q)) := by
  set s := Bp q ^ N with hs
  set c : ℝ := (N + 1) * q * (1 - q) with hc
  set κ := max q (1 - q) with hκ
  have hcpos : 0 < c := by positivity
  have hsnn : NonnegCoeff s := by
    rw [hs]; intro v
    have := nonnegCoeff_prod (Finset.range N) (fun _ => q) (fun _ => ⟨hq0.le, hq1.le⟩) v
    simpa [Finset.prod_const] using this
  have hXs := nonnegCoeff_X_mul hsnn
  have hterm : ∀ v, ((X * s).coeff v - s.coeff v) ^ 2 / ((X * s).coeff v + s.coeff v) ≤
      κ / c * (((X * s).coeff v - s.coeff v) * ((v : ℝ) - (N + 1) * q)) := by
    intro v
    set a := (X * s).coeff v - s.coeff v
    set b := (X * s).coeff v + s.coeff v
    set t := (Bp q ^ (N + 1)).coeff v
    have hid : c * a = t * ((v : ℝ) - (N + 1) * q) := binom_identity q N v
    have ht : t = (1 - q) * s.coeff v + q * (X * s).coeff v := by
      simp only [t]; rw [pow_succ', coeff_Bp_mul]
    have ht0 : 0 ≤ t := by rw [ht]; nlinarith [hsnn v, hXs v]
    have htb : t ≤ κ * b := by
      rw [ht]; simp only [b]
      have h1 : q ≤ κ := le_max_left _ _
      have h2 : 1 - q ≤ κ := le_max_right _ _
      nlinarith [hsnn v, hXs v]
    have hab : |a| ≤ b := by rw [abs_le]; constructor <;> linarith [hsnn v, hXs v]
    rcases (le_trans (abs_nonneg a) hab).eq_or_lt with hb0 | hb0
    · have : a = 0 := abs_nonpos_iff.mp (hb0 ▸ hab)
      rw [this]; simp
    rcases ht0.eq_or_lt with ht00 | ht00
    · have : a = 0 := by
        rw [← ht00, zero_mul] at hid
        rcases mul_eq_zero.mp hid with h | h
        · exact absurd h hcpos.ne'
        · exact h
      rw [this]; simp
    have he : ((v : ℝ) - (N + 1) * q) = c * a / t := by
      field_simp; linarith
    rw [he]
    have : κ / c * (a * (c * a / t)) = κ * a ^ 2 / t := by
      field_simp
    rw [this, div_le_div_iff₀ hb0 ht00]
    nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (sub_nonneg.mpr htb)]
  have hsum : ∑ v ∈ range R, ((X * s).coeff v - s.coeff v) * ((v : ℝ) - (N + 1) * q) = 1 := by
    obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    have hdeg : s.natDegree ≤ N := by
      rw [hs]
      exact le_trans natDegree_pow_le (by nlinarith [natDegree_Bp_le q])
    simp_rw [sub_mul]
    rw [sum_sub_distrib, sum_range_succ', sum_range_succ (fun v => s.coeff v * _)]
    simp only [coeff_X_mul, coeff_X_mul_zero, zero_mul, add_zero]
    have hz : s.coeff R' = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, zero_mul, add_zero, ← sum_sub_distrib]
    have : ∀ u ∈ range R', s.coeff u * (((u + 1 : ℕ) : ℝ) - (N + 1) * q) -
        s.coeff u * ((u : ℝ) - (N + 1) * q) = s.coeff u := by
      intro u _; push_cast; ring
    rw [sum_congr rfl this]
    apply sum_coeff_eq_one (by omega)
    rw [hs, eval_pow, eval_one_Bp, one_pow]
  unfold Dsum
  calc _ ≤ ∑ v ∈ range R, κ / c * (((X * s).coeff v - s.coeff v) * ((v : ℝ) - (N + 1) * q)) :=
        sum_le_sum (fun v _ => hterm v)
    _ = κ / c := by rw [← mul_sum, hsum, mul_one]

lemma coeff_prod_pos {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    ∀ v ≤ s.card, 0 < (∏ i ∈ s, Bp (p i)).coeff v := by
  classical
  induction s using Finset.induction_on with
  | empty => intro v hv; simp at hv; subst hv; simp
  | insert a s ha ih =>
    intro v hv
    rw [prod_insert ha, coeff_Bp_mul]
    have hnn := nonnegCoeff_prod s p (fun i => ⟨(hp i).1.le, (hp i).2.le⟩)
    have hXnn := nonnegCoeff_X_mul hnn
    rw [card_insert_of_notMem ha] at hv
    rcases Nat.lt_or_ge v (s.card + 1) with h | h
    · have := ih v (by omega)
      nlinarith [hp a, hXnn v]
    · have hv' : v = s.card + 1 := by omega
      subst hv'
      rw [coeff_X_mul]
      have := ih s.card le_rfl
      nlinarith [hp a, hnn (s.card + 1)]

end BLBSol


open Finset Polynomial

namespace BLBSol

lemma Dsum_majority (q ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (hq : q = 1 / 2 ∨ q = 1 / 2 - ε)
    {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (T T' : Finset ι)
    (hT : T' ⊆ T) (hT' : ∀ i ∈ T', p i = q) (R : ℕ) :
    Dsum R (∏ i ∈ T, Bp (p i)) ≤ 1 / ((1 / 2 - ε) * (T'.card + 1)) := by
  have hq0 : 0 < q := by rcases hq with h | h <;> rw [h] <;> linarith
  have hq1 : q < 1 := by rcases hq with h | h <;> rw [h] <;> linarith
  have h1 := Dsum_subset_le R p hp hT
  have h2 : ∏ i ∈ T', Bp (p i) = Bp q ^ T'.card := by
    rw [Finset.prod_congr rfl (fun i hi => by rw [hT' i hi]), prod_const]
  rw [h2] at h1
  have hnn : NonnegCoeff (Bp q ^ T'.card) := by
    rw [← h2]; exact nonnegCoeff_prod T' p hp
  have h3 := Dsum_mono_R hnn (le_max_left R (T'.card + 2))
  have h4 := Dsum_binom_le q hq0 hq1 T'.card (max R (T'.card + 2)) (le_max_right _ _)
  have h5 : max q (1 - q) / ((T'.card + 1) * q * (1 - q)) ≤ 1 / ((1 / 2 - ε) * (T'.card + 1)) := by
    have hc : (0:ℝ) < T'.card + 1 := by positivity
    rcases hq with h | h
    · subst h
      rw [show max (1/2 : ℝ) (1 - 1/2) = 1/2 by norm_num, div_le_div_iff₀ (by positivity)
        (by nlinarith)]
      nlinarith
    · subst h
      rw [show max (1/2 - ε : ℝ) (1 - (1/2 - ε)) = 1/2 + ε by
        rw [max_eq_right (by linarith)]; ring]
      rw [div_le_div_iff₀ (by have : 0 < 1/2 - ε := by linarith
                              have : 0 < 1 - (1/2 - ε) := by linarith
                              positivity) (by nlinarith)]
      nlinarith
  linarith

lemma one_round_poly (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (p : Fin m → ℝ)
    (hp : ∀ i, p i = 1 / 2 ∨ p i = 1 / 2 - ε) (i0 : Fin m) (hi0 : p i0 = 1 / 2 - ε) :
    ∑ v : Fin (m + 1), (∏ i, Bp (Function.update p i0 (1 / 2) i)).coeff v *
        Real.log ((∏ i, Bp (Function.update p i0 (1 / 2) i)).coeff v /
          (∏ i, Bp (p i)).coeff v) ≤
      2 * ε ^ 2 / ((1 / 2 - ε) ^ 2 * m) := by
  set G := ∏ i, Bp (p i) with hG
  set G' := ∏ i, Bp (Function.update p i0 (1 / 2) i) with hG'
  set S := ∏ i ∈ univ.erase i0, Bp (p i) with hS
  have hp01 : ∀ i, 0 < p i ∧ p i < 1 := by
    intro i; rcases hp i with h | h <;> rw [h] <;> constructor <;> linarith
  have hp01' : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨(hp01 i).1.le, (hp01 i).2.le⟩
  have hGS : G = Bp (1 / 2 - ε) * S := by
    rw [hG, hS, ← Finset.mul_prod_erase univ (fun i => Bp (p i)) (mem_univ i0), hi0]
  have hG'S : G' = Bp (1 / 2) * S := by
    rw [hG', hS, ← Finset.mul_prod_erase univ _ (mem_univ i0)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hSnn : NonnegCoeff S := nonnegCoeff_prod _ p hp01'
  have hXS := nonnegCoeff_X_mul hSnn
  have hGc : ∀ v, G.coeff v = (1 / 2 + ε) * S.coeff v + (1 / 2 - ε) * (X * S).coeff v := by
    intro v; rw [hGS, coeff_Bp_mul]; ring
  have hG'c : ∀ v, G'.coeff v = (1 / 2) * S.coeff v + (1 / 2) * (X * S).coeff v := by
    intro v; rw [hG'S, coeff_Bp_mul]; ring
  have hGpos : ∀ v : Fin (m + 1), 0 < G.coeff v := by
    intro v
    have := coeff_prod_pos univ p hp01 v (by simpa using Nat.lt_succ_iff.mp v.isLt)
    exact this
  have hdeg : ∀ (q : Fin m → ℝ), (∏ i, Bp (q i)).natDegree < m + 1 := by
    intro q
    have := natDegree_prod_le (s := univ) (f := fun i => Bp (q i))
    have h2 : ∑ i : Fin m, (Bp (q i)).natDegree ≤ m := by
      calc _ ≤ ∑ _i : Fin m, 1 := sum_le_sum (fun i _ => natDegree_Bp_le _)
        _ = m := by simp
    omega
  have hsum1 : ∀ (q : Fin m → ℝ), ∑ v : Fin (m + 1), (∏ i, Bp (q i)).coeff v = 1 := by
    intro q
    rw [Fin.sum_univ_eq_sum_range (fun v => (∏ i, Bp (q i)).coeff v)]
    apply sum_coeff_eq_one (hdeg q)
    rw [eval_prod]; simp [eval_one_Bp]
  have hkl := kl_le_chi2 (fun v : Fin (m + 1) => G'.coeff v) (fun v => G.coeff v)
    (fun v => by rw [hG'c]; nlinarith [hSnn v, hXS v]) hGpos
    (by rw [hsum1, hsum1])
  have hchi : ∑ v : Fin (m + 1), (G'.coeff v - G.coeff v) ^ 2 / G.coeff v ≤
      ε ^ 2 / (1 / 2 - ε) * Dsum (m + 1) S := by
    unfold Dsum
    have hconv := Fin.sum_univ_eq_sum_range (fun v : ℕ => ε ^ 2 / (1 / 2 - ε) *
      (((X * S).coeff v - S.coeff v) ^ 2 / ((X * S).coeff v + S.coeff v))) (m + 1)
    rw [mul_sum, ← hconv]
    apply sum_le_sum
    intro v _
    have hb0 : 0 ≤ (X * S).coeff v + S.coeff v := add_nonneg (hXS v) (hSnn v)
    have hdiff : G'.coeff v - G.coeff v = ε * ((X * S).coeff v - S.coeff v) := by
      rw [hGc, hG'c]; ring
    rw [hdiff]
    rcases hb0.eq_or_lt with h0 | h0
    · have ha : (X * S).coeff v - S.coeff v = 0 := by
        have := hXS v; have := hSnn v; linarith
      rw [ha]; simp
    have hpos : 0 < 1 / 2 - ε := by linarith
    have hle : (1 / 2 - ε) * ((X * S).coeff v + S.coeff v) ≤ G.coeff v := by
      rw [hGc]; nlinarith [hSnn v]
    calc (ε * ((X * S).coeff v - S.coeff v)) ^ 2 / G.coeff v ≤
          (ε * ((X * S).coeff v - S.coeff v)) ^ 2 /
            ((1 / 2 - ε) * ((X * S).coeff v + S.coeff v)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hpos h0) hle
      _ = _ := by field_simp
  -- majority
  classical
  set T := univ.erase i0 with hT
  set T1 := T.filter (fun i => p i = 1 / 2) with hT1
  set T2 := T.filter (fun i => ¬ p i = 1 / 2) with hT2
  have hcard : T1.card + T2.card = m - 1 := by
    rw [hT1, hT2, Finset.card_filter_add_card_filter_not, hT, card_erase_of_mem
      (mem_univ _), card_univ, Fintype.card_fin]
  have hD : Dsum (m + 1) S ≤ 2 / ((1 / 2 - ε) * m) := by
    have hpos : 0 < 1 / 2 - ε := by linarith
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm
    by_cases h12 : T2.card ≤ T1.card
    · have := Dsum_majority (1 / 2) ε hε (Or.inl rfl) p hp01' T T1 (filter_subset _ _)
        (fun i hi => (mem_filter.mp hi).2) (m + 1)
      refine le_trans this ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (m : ℝ) ≤ 2 * (T1.card + 1) := by
        have : m ≤ 2 * (T1.card + 1) := by omega
        exact_mod_cast this
      nlinarith
    · have := Dsum_majority (1 / 2 - ε) ε hε (Or.inr rfl) p hp01' T T2 (filter_subset _ _)
        (fun i hi => by
          have h := (mem_filter.mp hi).2
          rcases hp i with h' | h'
          · exact absurd h' h
          · exact h') (m + 1)
      refine le_trans this ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (m : ℝ) ≤ 2 * (T2.card + 1) := by
        have : m ≤ 2 * (T2.card + 1) := by omega
        exact_mod_cast this
      nlinarith
  have hpos : 0 < 1 / 2 - ε := by linarith
  have hfin : ε ^ 2 / (1 / 2 - ε) * Dsum (m + 1) S ≤ 2 * ε ^ 2 / ((1 / 2 - ε) ^ 2 * m) := by
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm
    calc ε ^ 2 / (1 / 2 - ε) * Dsum (m + 1) S ≤ ε ^ 2 / (1 / 2 - ε) * (2 / ((1 / 2 - ε) * m)) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by field_simp
  unfold klS at hkl
  linarith

end BLBSol


open Finset

namespace BLBSol

abbrev GA (m k : ℕ) := Fin m → Fin k
abbrev Rd (m k : ℕ) := Fin m → Fin k → Bool

def bern (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def emb {m k : ℕ} (a : GA m k) : Fin (m * k) → ℝ := fun c =>
  if a (finProdFinEquiv.symm c).1 = (finProdFinEquiv.symm c).2 then 1 else 0

noncomputable def zOf {m k : ℕ} (r : Rd m k) : Fin (m * k) → ℝ := fun c =>
  if r (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2 then 1 else 0

def obsCount {m k : ℕ} (a : GA m k) (r : Rd m k) : ℕ := ∑ i, if r i (a i) then 1 else 0

noncomputable def roundProb {m k : ℕ} (P : Fin m → Fin k → ℝ) (r : Rd m k) : ℝ :=
  ∏ i, ∏ j, bern (P i j) (r i j)

noncomputable def Obs {m k : ℕ} (P : Fin m → Fin k → ℝ) (a : GA m k) (v : ℕ) : ℝ :=
  ∑ r : Rd m k, roundProb P r * (if v = obsCount a r then 1 else 0)

lemma sum_fin_mk {m k : ℕ} (F : Fin (m * k) → ℝ) :
    ∑ c, F c = ∑ i : Fin m, ∑ j : Fin k, F (finProdFinEquiv (i, j)) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]

lemma dot_emb_zOf {m k : ℕ} (a : GA m k) (r : Rd m k) :
    emb a ⬝ᵥ zOf r = (obsCount a r : ℝ) := by
  unfold dotProduct
  rw [sum_fin_mk]
  simp only [emb, zOf, Equiv.symm_apply_apply, obsCount]
  push_cast
  apply sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (a i)]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

lemma emb_apply {m k : ℕ} (a : GA m k) (i : Fin m) (j : Fin k) :
    emb a (finProdFinEquiv (i, j)) = if a i = j then 1 else 0 := by
  simp [emb]

lemma emb_injective {m k : ℕ} : Function.Injective (emb (m := m) (k := k)) := by
  intro a b h
  funext i
  have := congrFun h (finProdFinEquiv (i, a i))
  rw [emb_apply, emb_apply] at this
  by_contra hne
  simp [Ne.symm hne] at this

lemma emb_binary {m k : ℕ} (a : GA m k) :
    (∀ c, emb a c = 0 ∨ emb a c = 1) ∧ ∑ c, emb a c = (m : ℝ) := by
  constructor
  · intro c; unfold emb; split_ifs <;> simp
  · rw [sum_fin_mk]
    simp only [emb_apply]
    simp

lemma zOf_mem {m k : ℕ} (r : Rd m k) (c : Fin (m * k)) : zOf r c ∈ Set.Icc (0:ℝ) 1 := by
  unfold zOf; split_ifs <;> simp

lemma zOf_injective {m k : ℕ} : Function.Injective (zOf (m := m) (k := k)) := by
  intro r s h
  funext i j
  have := congrFun h (finProdFinEquiv (i, j))
  simp only [zOf, Equiv.symm_apply_apply] at this
  cases hr : r i j <;> cases hs : s i j <;> simp_all

lemma obsCount_le {m k : ℕ} (a : GA m k) (r : Rd m k) : obsCount a r ≤ m := by
  unfold obsCount
  calc (∑ i, if r i (a i) then 1 else 0) ≤ ∑ _i : Fin m, 1 :=
        sum_le_sum (fun i _ => by split_ifs <;> simp)
    _ = m := by simp

lemma sum_prod_prod {R : Type*} [CommSemiring R] {m k : ℕ} (f : Fin m → Fin k → Bool → R) :
    ∑ r : Rd m k, ∏ i, ∏ j, f i j (r i j) = ∏ i, ∏ j, ∑ b, f i j b := by
  have h1 : ∀ i, ∏ j, ∑ b, f i j b = ∑ y : Fin k → Bool, ∏ j, f i j (y j) := by
    intro i; rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma roundProb_nonneg {m k : ℕ} (P : Fin m → Fin k → ℝ) (hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1)
    (r : Rd m k) : 0 ≤ roundProb P r := by
  unfold roundProb
  apply prod_nonneg; intro i _; apply prod_nonneg; intro j _
  unfold bern; split_ifs <;> linarith [hP i j]

lemma roundProb_sum {m k : ℕ} (P : Fin m → Fin k → ℝ) : ∑ r : Rd m k, roundProb P r = 1 := by
  unfold roundProb
  rw [sum_prod_prod]
  simp [bern, Fintype.sum_bool]

open Polynomial in
lemma gen_eq {m k : ℕ} (P : Fin m → Fin k → ℝ) (a : GA m k) :
    ∑ r : Rd m k, C (roundProb P r) * X ^ (obsCount a r) = ∏ i, Bp (P i (a i)) := by
  classical
  set F : Fin m → Fin k → Bool → ℝ[X] := fun i j b =>
    C (bern (P i j) b) * (if j = a i then X ^ (if b then 1 else 0) else 1) with hF
  have key : ∀ r : Rd m k, C (roundProb P r) * X ^ (obsCount a r) = ∏ i, ∏ j, F i j (r i j) := by
    intro r
    simp only [hF, Finset.prod_mul_distrib, Finset.prod_ite_eq', mem_univ, if_true]
    rw [roundProb, map_prod, obsCount, ← Finset.prod_pow_eq_pow_sum]
    congr 1
    apply prod_congr rfl
    intro i _
    rw [map_prod]
  simp_rw [key]
  rw [sum_prod_prod]
  apply prod_congr rfl
  intro i _
  have : ∀ j, ∑ b, F i j b = if j = a i then Bp (P i j) else 1 := by
    intro j
    simp only [hF, Fintype.sum_bool, bern, if_true, Bool.false_eq_true, if_false]
    split_ifs
    · simp [Bp]
    · simp only [mul_one]; rw [← map_add]; simp
  simp_rw [this]
  rw [Finset.prod_ite_eq']
  simp

open Polynomial in
lemma Obs_eq_coeff {m k : ℕ} (P : Fin m → Fin k → ℝ) (a : GA m k) (v : ℕ) :
    Obs P a v = (∏ i, Bp (P i (a i))).coeff v := by
  rw [← gen_eq, finsetSum_coeff]
  unfold Obs
  apply sum_congr rfl
  intro r _
  rw [coeff_C_mul_X_pow]
  split_ifs <;> simp

lemma natDegree_prod_Bp {m : ℕ} (q : Fin m → ℝ) : (∏ i, Bp (q i)).natDegree ≤ m := by
  have := Polynomial.natDegree_prod_le (s := univ) (f := fun i => Bp (q i))
  have h2 : ∑ i : Fin m, (Bp (q i)).natDegree ≤ m := by
    calc _ ≤ ∑ _i : Fin m, 1 := sum_le_sum (fun i _ => natDegree_Bp_le _)
      _ = m := by simp
  omega

lemma sum_coeff_prod_Bp {m : ℕ} (q : Fin m → ℝ) :
    ∑ v : Fin (m + 1), (∏ i, Bp (q i)).coeff v = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun v => (∏ i, Bp (q i)).coeff v)]
  apply sum_coeff_eq_one (by have := natDegree_prod_Bp q; omega)
  rw [Polynomial.eval_prod]; simp [eval_one_Bp]

lemma Obs_sum {m k : ℕ} (P : Fin m → Fin k → ℝ) (a : GA m k) :
    ∑ v : Fin (m + 1), Obs P a v = 1 := by
  simp_rw [Obs_eq_coeff]; exact sum_coeff_prod_Bp _

lemma Obs_nonneg {m k : ℕ} (P : Fin m → Fin k → ℝ) (hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1)
    (a : GA m k) (v : ℕ) : 0 ≤ Obs P a v := by
  unfold Obs
  apply sum_nonneg; intro r _
  apply mul_nonneg (roundProb_nonneg P hP r); split_ifs <;> norm_num

lemma Obs_pos {m k : ℕ} (P : Fin m → Fin k → ℝ) (hP : ∀ i j, 0 < P i j ∧ P i j < 1)
    (a : GA m k) (v : Fin (m + 1)) : 0 < Obs P a v := by
  rw [Obs_eq_coeff]
  have := coeff_prod_pos univ (fun i => P i (a i)) (fun i => hP i (a i)) v
    (by simpa using Nat.lt_succ_iff.mp v.isLt)
  exact this

/-- Expected observation. -/
lemma Obs_mean {m k : ℕ} (hm : 1 ≤ m) (P : Fin m → Fin k → ℝ) (a : GA m k) :
    ∑ v : Fin (m + 1), Obs P a v * ((v : ℕ) : ℝ) = ∑ i, P i (a i) := by
  classical
  simp_rw [Obs_eq_coeff]
  set G := ∏ i, Bp (P i (a i)) with hG
  have h1 : ∀ v : ℕ, G.coeff v * (v : ℝ) = (Polynomial.X * Polynomial.derivative G).coeff v := by
    intro v; rw [coeff_X_mul_derivative]; ring
  rw [Fin.sum_univ_eq_sum_range (fun v => G.coeff v * (v : ℝ))]
  simp_rw [h1]
  have hdeg : (Polynomial.X * Polynomial.derivative G).natDegree < m + 1 := by
    have h2 := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := Polynomial.derivative G)
    have h3 := Polynomial.natDegree_derivative_le G
    have h4 := natDegree_prod_Bp (fun i => P i (a i))
    rw [← hG] at h4
    rw [Polynomial.natDegree_X] at h2
    omega
  have hev := Polynomial.eval_eq_sum_range' hdeg 1
  simp only [one_pow, mul_one] at hev
  rw [← hev]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul]
  rw [hG, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply sum_congr rfl
  intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  simp [eval_one_Bp, Bp]

/-- Expected observation in terms of the round randomness. -/
lemma roundProb_obs {m k : ℕ} (P : Fin m → Fin k → ℝ) (a : GA m k) :
    ∑ r : Rd m k, roundProb P r * (obsCount a r : ℝ) =
      ∑ v : Fin (m + 1), Obs P a v * ((v : ℕ) : ℝ) := by
  unfold Obs
  simp_rw [sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single (⟨obsCount a r, Nat.lt_succ_of_le (obsCount_le a r)⟩ : Fin (m + 1))]
  · simp
  · intro v _ hv
    have : (v : ℕ) ≠ obsCount a r := by
      intro h; apply hv; ext; exact h
    simp [this]
  · simp

end BLBSol


open Finset OnlineCombOpt.BanditLB

namespace BLBSol

variable {m k : ℕ}

abbrev XX (m k : ℕ) := GA m k × Fin (m + 1)

noncomputable def hist {t : ℕ} (h : Fin t → XX m k) : Fin t → (Fin (m * k) → ℝ) × ℝ :=
  fun s => (emb (h s).1, (((h s).2 : ℕ) : ℝ))

noncomputable def kern (σ : BanditStrategy (m * k)) (P : Fin m → Fin k → ℝ) :
    (t : ℕ) → (Fin t → XX m k) → XX m k → ℝ :=
  fun t h x => σ t (hist h) (emb x.1) * Obs P x.1 x.2

noncomputable def Aset (m k : ℕ) : Finset (Fin (m * k) → ℝ) := univ.image (emb (m := m) (k := k))

lemma sigma_sum (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ) (t : ℕ)
    (h : Fin t → (Fin (m * k) → ℝ) × ℝ) : ∑ a : GA m k, σ t h (emb a) = 1 := by
  have := hσ.2 t h
  rw [Aset, Finset.sum_image (fun a _ b _ hab => emb_injective hab)] at this
  exact this

lemma sigma_nonneg (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ) (t : ℕ)
    (h : Fin t → (Fin (m * k) → ℝ) × ℝ) (a : GA m k) : 0 ≤ σ t h (emb a) :=
  hσ.1 t h (emb a) (by simp [Aset])

lemma kern_nonneg (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (P : Fin m → Fin k → ℝ) (hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) :
    ∀ t h x, 0 ≤ kern σ P t h x :=
  fun t h x => mul_nonneg (sigma_nonneg σ hσ _ _ _) (Obs_nonneg P hP _ _)

/-- Sum of a function against the kernel, splitting off the observation. -/
lemma kern_sum_split (σ : BanditStrategy (m * k)) (P : Fin m → Fin k → ℝ) (t : ℕ)
    (h : Fin t → XX m k) (G : XX m k → ℝ) :
    ∑ x, kern σ P t h x * G x =
      ∑ a : GA m k, σ t (hist h) (emb a) * ∑ v : Fin (m + 1), Obs P a v * G (a, v) := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl; intro a _
  rw [mul_sum]; apply sum_congr rfl; intro v _
  simp only [kern]; ring

lemma kern_sum (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (P : Fin m → Fin k → ℝ) : ∀ t h, ∑ x, kern σ P t h x = 1 := by
  intro t h
  have := kern_sum_split σ P t h (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  simp_rw [Obs_sum, mul_one]
  exact sigma_sum σ hσ t _

lemma kern_avg (σ : BanditStrategy (m * k)) (P : Fin m → Fin k → ℝ) (t : ℕ)
    (h : Fin t → XX m k) (G : XX m k → ℝ) (H : GA m k → ℝ)
    (hGH : ∀ a, ∑ v : Fin (m + 1), Obs P a v * G (a, v) = H a) :
    ∑ x, kern σ P t h x * G x = ∑ x, kern σ P t h x * H x.1 := by
  rw [kern_sum_split, kern_sum_split]
  apply sum_congr rfl; intro a _
  rw [hGH]; simp only
  rw [← sum_mul, Obs_sum, one_mul]

/-- The law of the observed trajectory. -/
noncomputable def law (σ : BanditStrategy (m * k)) (P : Fin m → Fin k → ℝ) (n : ℕ) :
    (Fin n → XX m k) → ℝ := seqLaw (kern σ P) n

noncomputable def Sig (σ : BanditStrategy (m * k)) {n : ℕ} (y : Fin n → XX m k) : ℝ :=
  ∏ t : Fin n, σ t.val (hist (fun s : Fin t.val => y ⟨s.val, Nat.lt_trans s.isLt t.isLt⟩))
    (emb (y t).1)

lemma law_eq (σ : BanditStrategy (m * k)) (P : Fin m → Fin k → ℝ) {n : ℕ} (y : Fin n → XX m k) :
    law σ P n y = Sig σ y * ∏ t, Obs P (y t).1 (y t).2 := by
  unfold law seqLaw Sig kern
  rw [prod_mul_distrib]

lemma Sig_nonneg (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ) {n : ℕ}
    (y : Fin n → XX m k) : 0 ≤ Sig σ y :=
  prod_nonneg (fun t _ => sigma_nonneg σ hσ _ _ _)

/-! ### The adversary -/

noncomputable def rOf (z : Fin (m * k) → ℝ) : Rd m k := fun i j => decide (z (finProdFinEquiv (i, j)) = 1)

lemma rOf_zOf (r : Rd m k) : rOf (zOf r) = r := by
  funext i j; simp [rOf, zOf]

noncomputable def zSeq {n : ℕ} (ω : Fin n → Rd m k) : Fin n → Fin (m * k) → ℝ :=
  fun t => zOf (ω t)

lemma zSeq_injective {n : ℕ} : Function.Injective (zSeq (m := m) (k := k) (n := n)) := by
  intro ω ω' h
  funext t
  exact zOf_injective (congrFun h t)

noncomputable def Zset (m k n : ℕ) : Finset (Fin n → Fin (m * k) → ℝ) :=
  univ.image (zSeq (m := m) (k := k) (n := n))

noncomputable def muP {n : ℕ} (P : Fin m → Fin k → ℝ) (z : Fin n → Fin (m * k) → ℝ) : ℝ :=
  ∏ t, roundProb P (rOf (z t))

lemma muP_zSeq {n : ℕ} (P : Fin m → Fin k → ℝ) (ω : Fin n → Rd m k) :
    muP P (zSeq ω) = ∏ t, roundProb P (ω t) := by
  simp [muP, zSeq, rOf_zOf]

lemma sum_Zset {n : ℕ} (P : Fin m → Fin k → ℝ) (F : (Fin n → Fin (m * k) → ℝ) → ℝ) :
    ∑ z ∈ Zset m k n, muP P z * F z =
      ∑ ω : Fin n → Rd m k, (∏ t, roundProb P (ω t)) * F (zSeq ω) := by
  rw [Zset, sum_image (fun a _ b _ hab => zSeq_injective hab)]
  simp_rw [muP_zSeq]

lemma sum_prod_fun {n : ℕ} {Y : Type*} [Fintype Y] [DecidableEq Y] (f : Fin n → Y → ℝ) :
    ∑ ω : Fin n → Y, ∏ t, f t (ω t) = ∏ t, ∑ r, f t r := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma oblivious {n : ℕ} (P : Fin m → Fin k → ℝ) (hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) :
    IsObliviousAdversary (Zset m k n) (muP P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [Zset, mem_image] at hz
    obtain ⟨ω, _, rfl⟩ := hz
    rw [muP_zSeq]
    exact prod_nonneg (fun t _ => roundProb_nonneg P hP _)
  · have := sum_Zset (n := n) P (fun _ => 1)
    simp only [mul_one] at this
    rw [this, sum_prod_fun (fun _ r => roundProb P r)]
    simp [roundProb_sum]
  · intro z hz t i
    rw [Zset, mem_image] at hz
    obtain ⟨ω, _, rfl⟩ := hz
    exact zOf_mem _ _

/-- single round marginal of the adversary -/
lemma adv_marg {n : ℕ} (P : Fin m → Fin k → ℝ) (t : Fin n) (h : Rd m k → ℝ) :
    ∑ ω : Fin n → Rd m k, (∏ s, roundProb P (ω s)) * h (ω t) =
      ∑ r, roundProb P r * h r := by
  classical
  have e1 : ∀ ω : Fin n → Rd m k, (∏ s, roundProb P (ω s)) * h (ω t) =
      ∏ s, (roundProb P (ω s) * (if s = t then h (ω s) else 1)) := by
    intro ω
    rw [prod_mul_distrib, prod_ite_eq']; simp
  simp_rw [e1]
  rw [sum_prod_fun (fun s r => roundProb P r * (if s = t then h r else 1))]
  have e2 : ∀ s, ∑ r, roundProb P r * (if s = t then h r else 1) =
      if s = t then ∑ r, roundProb P r * h r else 1 := by
    intro s; split_ifs
    · rfl
    · simp [roundProb_sum]
  simp_rw [e2]
  rw [prod_ite_eq']; simp

end BLBSol


open Finset OnlineCombOpt.BanditLB

namespace BLBSol

variable {m k : ℕ}

def vOf {n : ℕ} (g : Fin n → GA m k) (ω : Fin n → Rd m k) : Fin n → Fin (m + 1) :=
  fun t => ⟨obsCount (g t) (ω t), Nat.lt_succ_of_le (obsCount_le _ _)⟩

def pairOf {n : ℕ} (g : Fin n → GA m k) (v : Fin n → Fin (m + 1)) : Fin n → XX m k :=
  fun t => (g t, v t)

lemma sum_pairs {n : ℕ} (H : (Fin n → XX m k) → ℝ) :
    ∑ g : Fin n → GA m k, ∑ v : Fin n → Fin (m + 1), H (pairOf g v) = ∑ y, H y := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ (fun _ => rfl)

lemma pathProb_eq (σ : BanditStrategy (m * k)) {n : ℕ} (g : Fin n → GA m k)
    (ω : Fin n → Rd m k) :
    pathProb σ (zSeq ω) (fun t => emb (g t)) = Sig σ (pairOf g (vOf g ω)) := by
  unfold pathProb Sig hist pairOf vOf zSeq
  simp only [dot_emb_zOf]

lemma piFinset_Aset {n : ℕ} :
    Fintype.piFinset (fun _ : Fin n => Aset m k) =
      univ.image (fun g : Fin n → GA m k => fun t => emb (g t)) := by
  classical
  ext path
  simp only [Fintype.mem_piFinset, Aset, mem_image, mem_univ, true_and]
  constructor
  · intro h
    choose g hg using h
    exact ⟨g, funext hg⟩
  · rintro ⟨g, rfl⟩ t
    exact ⟨g t, rfl⟩

lemma sum_piFinset_Aset {n : ℕ} (G : (Fin n → Fin (m * k) → ℝ) → ℝ) :
    ∑ path ∈ Fintype.piFinset (fun _ : Fin n => Aset m k), G path =
      ∑ g : Fin n → GA m k, G (fun t => emb (g t)) := by
  rw [piFinset_Aset, sum_image]
  intro g _ g' _ h
  funext t
  exact emb_injective (congrFun h t)

lemma adv_vOf {n : ℕ} (P : Fin m → Fin k → ℝ) (g : Fin n → GA m k) (v : Fin n → Fin (m + 1)) :
    ∑ ω : Fin n → Rd m k, (∏ t, roundProb P (ω t)) * (if vOf g ω = v then 1 else 0) =
      ∏ t, Obs P (g t) (v t) := by
  classical
  have e1 : ∀ ω : Fin n → Rd m k, (∏ t, roundProb P (ω t)) * (if vOf g ω = v then 1 else 0) =
      ∏ t, (roundProb P (ω t) * (if ((v t : ℕ)) = obsCount (g t) (ω t) then 1 else 0)) := by
    intro ω
    rw [prod_mul_distrib, prod_boole]
    congr 1
    congr 1
    apply propext
    constructor
    · intro h t _; rw [← h]; rfl
    · intro h; funext t; exact Fin.ext (h t (mem_univ t)).symm
  simp_rw [e1]
  rw [sum_prod_fun (fun t r => roundProb P r * (if ((v t : ℕ)) = obsCount (g t) r then 1 else 0))]
  rfl

lemma term1_eq (σ : BanditStrategy (m * k)) (P : Fin m → Fin k → ℝ) {n : ℕ} :
    ∑ z ∈ Zset m k n, muP P z *
      ∑ path ∈ Fintype.piFinset (fun _ : Fin n => Aset m k),
        pathProb σ z path * ∑ t : Fin n, dotProduct (path t) (z t) =
    ∑ y, law σ P n y * ∑ t, (((y t).2 : ℕ) : ℝ) := by
  classical
  rw [sum_Zset]
  have h1 : ∀ ω : Fin n → Rd m k,
      ∑ path ∈ Fintype.piFinset (fun _ : Fin n => Aset m k),
        pathProb σ (zSeq ω) path * ∑ t : Fin n, dotProduct (path t) (zSeq ω t) =
      ∑ g : Fin n → GA m k, ∑ v : Fin n → Fin (m + 1),
        (if vOf g ω = v then 1 else 0) * (Sig σ (pairOf g v) * ∑ t, (((v t : ℕ)) : ℝ)) := by
    intro ω
    rw [sum_piFinset_Aset]
    apply sum_congr rfl; intro g _
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, if_true]
    rw [pathProb_eq]
    congr 1
    apply sum_congr rfl; intro t _
    simp [zSeq, dot_emb_zOf, vOf]
  simp_rw [h1]
  rw [← sum_pairs]
  calc _ = ∑ g : Fin n → GA m k, ∑ v : Fin n → Fin (m + 1),
        (∑ ω : Fin n → Rd m k, (∏ t, roundProb P (ω t)) * (if vOf g ω = v then 1 else 0)) *
          (Sig σ (pairOf g v) * ∑ t, (((v t : ℕ)) : ℝ)) := by
        simp_rw [mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl; intro g _
        rw [Finset.sum_comm]
        apply sum_congr rfl; intro v _
        rw [Finset.sum_comm]
        apply sum_congr rfl; intro i _
        rw [sum_mul]
        apply sum_congr rfl; intro ω _
        ring
    _ = _ := by
        apply sum_congr rfl; intro g _
        apply sum_congr rfl; intro v _
        rw [adv_vOf, law_eq]
        simp only [pairOf]
        ring

/-- Averaging lemma: replace a per-round function by its conditional expectation. -/
lemma law_avg (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (P : Fin m → Fin k → ℝ) {n : ℕ} (G : XX m k → ℝ) (H : GA m k → ℝ)
    (hGH : ∀ a, ∑ v : Fin (m + 1), Obs P a v * G (a, v) = H a) :
    ∑ y, law σ P n y * ∑ t, G (y t) = ∑ y, law σ P n y * ∑ t, H (y t).1 := by
  simp_rw [mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun y t => law σ P n y * H (y t).1)]
  apply sum_congr rfl; intro t _
  unfold law
  rw [seqLaw_marg' _ (kern_sum σ hσ P) n t G,
    seqLaw_marg' _ (kern_sum σ hσ P) n t (fun x => H x.1)]
  apply sum_congr rfl; intro y' _
  rw [kern_avg σ P t _ G H hGH]

lemma law_avg_le (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (P : Fin m → Fin k → ℝ) (hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) {n : ℕ} (G : XX m k → ℝ)
    (H : GA m k → ℝ) (hGH : ∀ a, ∑ v : Fin (m + 1), Obs P a v * G (a, v) ≤ H a) :
    ∑ y, law σ P n y * ∑ t, G (y t) ≤ ∑ y, law σ P n y * ∑ t, H (y t).1 := by
  simp_rw [mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun y t => law σ P n y * H (y t).1)]
  apply sum_le_sum; intro t _
  unfold law
  rw [seqLaw_marg' _ (kern_sum σ hσ P) n t G,
    seqLaw_marg' _ (kern_sum σ hσ P) n t (fun x => H x.1)]
  apply sum_le_sum; intro y' _
  apply mul_le_mul_of_nonneg_left _ (seqLaw_nonneg _ (kern_nonneg σ hσ P hP) _ _)
  rw [kern_sum_split, kern_sum_split]
  apply sum_le_sum; intro a _
  apply mul_le_mul_of_nonneg_left _ (sigma_nonneg σ hσ _ _ _)
  calc _ ≤ H a := hGH a
    _ = ∑ v : Fin (m + 1), Obs P a v * H (a, v).1 := by
      simp only; rw [← sum_mul, Obs_sum, one_mul]

lemma law_sum (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (P : Fin m → Fin k → ℝ) (n : ℕ) : ∑ y, law σ P n y = 1 :=
  seqLaw_sum _ (kern_sum σ hσ P) n

lemma law_nonneg (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (P : Fin m → Fin k → ℝ) (hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) (n : ℕ) (y : Fin n → XX m k) :
    0 ≤ law σ P n y :=
  seqLaw_nonneg _ (kern_nonneg σ hσ P hP) n y

end BLBSol


open Finset OnlineCombOpt.BanditLB

namespace BLBSol

variable {m k : ℕ}

noncomputable def Palpha (ε : ℝ) (α : GA m k) : Fin m → Fin k → ℝ :=
  fun i j => if α i = j then 1 / 2 - ε else 1 / 2

noncomputable def Qalpha (ε : ℝ) (i0 : Fin m) (α : GA m k) : Fin m → Fin k → ℝ :=
  fun i j => if i = i0 then 1 / 2 else Palpha ε α i j

noncomputable def cnt {n : ℕ} (i0 : Fin m) (α : GA m k) (y : Fin n → XX m k) : ℝ :=
  ∑ t, if (y t).1 i0 = α i0 then (1:ℝ) else 0

lemma Palpha_mem (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (α : GA m k) :
    ∀ i j, 0 < Palpha ε α i j ∧ Palpha ε α i j < 1 := by
  intro i j; unfold Palpha; split_ifs <;> constructor <;> linarith

lemma Qalpha_mem (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (i0 : Fin m) (α : GA m k) :
    ∀ i j, 0 < Qalpha ε i0 α i j ∧ Qalpha ε i0 α i j < 1 := by
  intro i j; unfold Qalpha
  split_ifs
  · constructor <;> norm_num
  · exact Palpha_mem ε hε α i j

lemma weak (P : Fin m → Fin k → ℝ) (h : ∀ i j, 0 < P i j ∧ P i j < 1) :
    ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1 := fun i j => ⟨(h i j).1.le, (h i j).2.le⟩

lemma regret_lower (hm : 1 ≤ m) (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (ε : ℝ) (α : GA m k) (n : ℕ) :
    ε * ∑ i : Fin m, ((n : ℝ) - ∑ y, law σ (Palpha ε α) n y * cnt i α y) ≤
      banditRegret (Aset m k) σ (Zset m k n) (muP (Palpha ε α)) := by
  classical
  set P := Palpha ε α with hP
  have hne : (Aset m k).Nonempty := ⟨emb α, by simp [Aset]⟩
  unfold banditRegret
  rw [dif_pos hne, term1_eq]
  have hmean : ∀ a : GA m k, ∑ v : Fin (m + 1), Obs P a v * (((a, v) : XX m k).2 : ℕ) =
      ∑ i, P i (a i) := fun a => Obs_mean hm P a
  have hT1 := law_avg σ hσ P (n := n) (fun x => (((x.2 : ℕ)) : ℝ)) (fun a => ∑ i, P i (a i)) hmean
  have hT2 : (Aset m k).inf' hne (fun a => ∑ z ∈ Zset m k n, muP P z *
      ∑ t : Fin n, dotProduct a (z t)) ≤ n * ∑ i, P i (α i) := by
    refine le_trans (Finset.inf'_le _ (by simp [Aset] : emb α ∈ Aset m k)) ?_
    rw [sum_Zset]
    simp only [zSeq, dot_emb_zOf]
    simp_rw [mul_sum]
    rw [Finset.sum_comm]
    have : ∀ t : Fin n, ∑ ω : Fin n → Rd m k, (∏ s, roundProb P (ω s)) * (obsCount α (ω t) : ℝ) =
        ∑ i, P i (α i) := by
      intro t
      rw [adv_marg P t (fun r => (obsCount α r : ℝ)), roundProb_obs, Obs_mean hm]
    simp_rw [this]
    simp [mul_sum]
  have hsum := law_sum σ hσ P n
  have key : ∑ y, law σ P n y * ∑ t, ∑ i, P i ((y t).1 i) - n * ∑ i, P i (α i) =
      ε * ∑ i : Fin m, ((n : ℝ) - ∑ y, law σ P n y * cnt i α y) := by
    have e1 : ∀ a : GA m k, ∑ i, P i (a i) - ∑ i, P i (α i) =
        ε * ∑ i, (1 - if a i = α i then (1:ℝ) else 0) := by
      intro a
      rw [← sum_sub_distrib, mul_sum]
      apply sum_congr rfl; intro i _
      simp only [hP, Palpha, if_true]
      by_cases h : a i = α i
      · simp [h]
      · simp [h, Ne.symm h]
    calc _ = ∑ y, law σ P n y * ∑ t, (∑ i, P i ((y t).1 i) - ∑ i, P i (α i)) := by
          simp_rw [sum_sub_distrib, mul_sub]
          rw [sum_sub_distrib, ← sum_mul, hsum]
          simp
      _ = ∑ y, law σ P n y * (ε * ∑ i : Fin m, ((n : ℝ) - cnt i α y)) := by
          apply sum_congr rfl; intro y _
          congr 1
          simp_rw [e1]
          rw [← mul_sum, Finset.sum_comm]
          congr 1
          apply sum_congr rfl; intro i _
          rw [sum_sub_distrib, cnt]; simp
      _ = _ := by
          simp_rw [mul_sum, mul_sub]
          rw [Finset.sum_comm]
          apply sum_congr rfl; intro i _
          rw [sum_sub_distrib]
          congr 1
          · rw [← sum_mul, hsum]; ring
          · rw [mul_sum]; apply sum_congr rfl; intro y _; ring
  rw [hT1]
  linarith

end BLBSol


open Finset OnlineCombOpt.BanditLB

namespace BLBSol

variable {m k : ℕ}

lemma one_round_model (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (i0 : Fin m) (α : GA m k)
    (a : GA m k) :
    ∑ v : Fin (m + 1), Obs (Qalpha ε i0 α) a v *
        Real.log (Obs (Qalpha ε i0 α) a v / Obs (Palpha ε α) a v) ≤
      2 * ε ^ 2 / ((1 / 2 - ε) ^ 2 * m) * (if a i0 = α i0 then 1 else 0) := by
  classical
  by_cases ha : a i0 = α i0
  · rw [if_pos ha, mul_one]
    simp_rw [Obs_eq_coeff]
    have hupd : (fun i => Qalpha ε i0 α i (a i)) =
        Function.update (fun i => Palpha ε α i (a i)) i0 (1 / 2) := by
      funext i
      by_cases hi : i = i0
      · subst hi; simp [Qalpha]
      · rw [Function.update_of_ne hi]; simp [Qalpha, hi]
    have := one_round_poly m hm ε hε (fun i => Palpha ε α i (a i))
      (by intro i; unfold Palpha; split_ifs <;> simp) i0 (by simp [Palpha, ha])
    rw [← hupd] at this
    exact this
  · rw [if_neg ha, mul_zero]
    have heq : ∀ v, Obs (Qalpha ε i0 α) a v = Obs (Palpha ε α) a v := by
      intro v
      rw [Obs_eq_coeff, Obs_eq_coeff]
      congr 2
      funext i
      by_cases hi : i = i0
      · subst hi; simp [Qalpha, Palpha, Ne.symm ha]
      · simp [Qalpha, hi]
    apply le_of_eq
    apply sum_eq_zero; intro v _
    rw [heq, div_self (Obs_pos _ (Palpha_mem ε hε α) a v).ne', Real.log_one, mul_zero]

lemma kl_bound (hm : 1 ≤ m) (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (i0 : Fin m) (α : GA m k) (n : ℕ) :
    klS (law σ (Qalpha ε i0 α) n) (law σ (Palpha ε α) n) ≤
      2 * ε ^ 2 / ((1 / 2 - ε) ^ 2 * m) * ∑ y, law σ (Qalpha ε i0 α) n y * cnt i0 α y := by
  classical
  set Q := Qalpha ε i0 α
  set P := Palpha ε α
  set c := 2 * ε ^ 2 / ((1 / 2 - ε) ^ 2 * m)
  have hQ := Qalpha_mem ε hε i0 α
  have hP := Palpha_mem ε hε α
  have hpt : ∀ y : Fin n → XX m k, law σ Q n y * Real.log (law σ Q n y / law σ P n y) =
      law σ Q n y * ∑ t, Real.log (Obs Q (y t).1 (y t).2 / Obs P (y t).1 (y t).2) := by
    intro y
    rw [law_eq, law_eq]
    by_cases hs : Sig σ y = 0
    · rw [hs]; simp
    rw [mul_div_mul_left _ _ hs, ← prod_div_distrib, Real.log_prod]
    intro t _
    exact (div_pos (Obs_pos Q hQ _ _) (Obs_pos P hP _ _)).ne'
  unfold klS
  simp_rw [hpt]
  have := law_avg_le σ hσ Q (weak Q hQ) (n := n)
    (fun x => Real.log (Obs Q x.1 x.2 / Obs P x.1 x.2))
    (fun a => c * (if a i0 = α i0 then 1 else 0))
    (fun a => one_round_model hm ε hε i0 α a)
  refine le_trans this (le_of_eq ?_)
  rw [mul_sum]
  apply sum_congr rfl; intro y _
  rw [cnt, mul_sum, mul_sum, mul_sum]
  apply sum_congr rfl; intro t _
  ring

lemma Qalpha_update (ε : ℝ) (i0 : Fin m) (α : GA m k) (j : Fin k) :
    Qalpha ε i0 (Function.update α i0 j) = Qalpha ε i0 α := by
  classical
  funext i j'
  by_cases hi : i = i0
  · simp [Qalpha, hi]
  · simp [Qalpha, Palpha, hi]

lemma sum_update (i0 : Fin m) (H : GA m k → ℝ) :
    ∑ α : GA m k, ∑ j : Fin k, H (Function.update α i0 j) = (k : ℝ) * ∑ α, H α := by
  classical
  let e : GA m k × Fin k → GA m k × Fin k := fun p => (Function.update p.1 i0 p.2, p.1 i0)
  have he : Function.Involutive e := by
    intro p
    simp only [e, Function.update_self, Function.update_idem, Function.update_eq_self]
  rw [← Fintype.sum_prod_type']
  have := Equiv.sum_comp he.toPerm (fun p : GA m k × Fin k => H p.1)
  simp only [Function.Involutive.coe_toPerm, e] at this
  rw [this, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_sum]

lemma symmetry (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ) (ε : ℝ)
    (i0 : Fin m) (n : ℕ) :
    (k : ℝ) * ∑ α : GA m k, ∑ y, law σ (Qalpha ε i0 α) n y * cnt i0 α y =
      n * (k : ℝ) ^ m := by
  classical
  rw [← sum_update i0]
  have h1 : ∀ α : GA m k, ∑ j : Fin k, ∑ y, law σ (Qalpha ε i0 (Function.update α i0 j)) n y *
      cnt i0 (Function.update α i0 j) y = n := by
    intro α
    simp_rw [Qalpha_update]
    rw [Finset.sum_comm]
    simp_rw [← mul_sum]
    have : ∀ y : Fin n → XX m k, ∑ j : Fin k, cnt i0 (Function.update α i0 j) y = n := by
      intro y
      unfold cnt
      rw [Finset.sum_comm]
      simp only [Function.update_self]
      simp [Finset.sum_ite_eq]
    simp_rw [this]
    rw [← sum_mul, law_sum σ hσ, one_mul]
  simp_rw [h1]
  simp; ring

lemma pinsker_app (σ : BanditStrategy (m * k)) (hσ : IsStrategyOn (Aset m k) σ) (ε : ℝ)
    (hε : 0 < ε ∧ ε < 1 / 2) (i0 : Fin m) (α : GA m k) (n : ℕ) (hn : 1 ≤ n) :
    ∑ y, law σ (Palpha ε α) n y * cnt i0 α y ≤
      ∑ y, law σ (Qalpha ε i0 α) n y * cnt i0 α y +
        n * Real.sqrt (klS (law σ (Qalpha ε i0 α) n) (law σ (Palpha ε α) n) / 2) := by
  set Q := Qalpha ε i0 α
  set P := Palpha ε α
  have hQ := Qalpha_mem ε hε i0 α
  have hP := Palpha_mem ε hε α
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hcnt : ∀ y : Fin n → XX m k, 0 ≤ cnt i0 α y ∧ cnt i0 α y ≤ n := by
    intro y; unfold cnt
    constructor
    · exact sum_nonneg (fun t _ => by split_ifs <;> norm_num)
    · calc _ ≤ ∑ _t : Fin n, (1:ℝ) := sum_le_sum (fun t _ => by split_ifs <;> norm_num)
        _ = n := by simp
  have := pinsker (law σ P n) (law σ Q n) (fun y => cnt i0 α y / n)
    (law_nonneg σ hσ P (weak P hP) n) (law_nonneg σ hσ Q (weak Q hQ) n)
    (law_sum σ hσ P n) (law_sum σ hσ Q n)
    (by
      intro y hy
      rw [law_eq] at hy ⊢
      have hs : 0 ≤ Sig σ y := Sig_nonneg σ hσ y
      have hs' : 0 < Sig σ y := by
        rcases hs.eq_or_lt with h | h
        · rw [← h, zero_mul] at hy; exact absurd hy (lt_irrefl _)
        · exact h
      exact mul_pos hs' (prod_pos (fun t _ => Obs_pos P hP _ _)))
    (fun y => ⟨div_nonneg (hcnt y).1 hnpos.le, (div_le_one hnpos).mpr (hcnt y).2⟩)
  have e1 : ∀ L : (Fin n → XX m k) → ℝ, ∑ y, L y * (cnt i0 α y / n) =
      (∑ y, L y * cnt i0 α y) / n := by
    intro L; rw [sum_div]; apply sum_congr rfl; intro y _; ring
  rw [e1, e1] at this
  have h2 := mul_le_mul_of_nonneg_left this hnpos.le
  rw [mul_add, mul_div_cancel₀ _ hnpos.ne', mul_div_cancel₀ _ hnpos.ne'] at h2
  exact h2

end BLBSol


open Finset OnlineCombOpt.BanditLB

namespace BLBSol

variable {m k : ℕ}

lemma card_GA : (Fintype.card (GA m k) : ℝ) = (k : ℝ) ^ m := by
  simp [Fintype.card_fun]

lemma main_claim (hm : 1 ≤ m) (hk : 2 ≤ k) (σ : BanditStrategy (m * k))
    (hσ : IsStrategyOn (Aset m k) σ) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1 / 10)
    (hε2 : ε ^ 2 * (100 * n) = m * k) :
    ∃ α : GA m k, ε * m * n / 4 ≤
      banditRegret (Aset m k) σ (Zset m k n) (muP (Palpha ε α)) := by
  classical
  have hε' : 0 < ε ∧ ε < 1 / 2 := ⟨hε.1, by linarith [hε.2]⟩
  set K : ℝ := (k : ℝ) ^ m with hK
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hKpos : 0 < K := by positivity
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set c : ℝ := 2 * ε ^ 2 / ((1 / 2 - ε) ^ 2 * m) with hc
  have hcpos : 0 ≤ c := by positivity
  have hcn : c * n ≤ k / 8 := by
    have h1 : c * n = 2 * (ε ^ 2 * n) / ((1 / 2 - ε) ^ 2 * m) := by rw [hc]; ring
    have h2 : ε ^ 2 * n = m * k / 100 := by linarith
    rw [h1, h2, div_le_div_iff₀ (by have : 0 < 1/2 - ε := by linarith
                                    positivity) (by norm_num)]
    have h3 : (2:ℝ) / 5 ≤ 1 / 2 - ε := by linarith [hε.2]
    have h4 : (4:ℝ) / 25 ≤ (1 / 2 - ε) ^ 2 := by nlinarith
    nlinarith [mul_pos hmpos hkpos]
  -- notation
  set EP : GA m k → Fin m → ℝ := fun α i => ∑ y, law σ (Palpha ε α) n y * cnt i α y with hEP
  set EQ : GA m k → Fin m → ℝ := fun α i => ∑ y, law σ (Qalpha ε i α) n y * cnt i α y with hEQ
  set KL : GA m k → Fin m → ℝ := fun α i =>
    klS (law σ (Qalpha ε i α) n) (law σ (Palpha ε α) n) with hKL
  have hEQnn : ∀ α i, 0 ≤ EQ α i := by
    intro α i; apply sum_nonneg; intro y _
    apply mul_nonneg (law_nonneg σ hσ _ (weak _ (Qalpha_mem ε hε' i α)) n y)
    unfold cnt; exact sum_nonneg (fun t _ => by split_ifs <;> norm_num)
  have hsumEQ : ∀ i, ∑ α, EQ α i = n * K / k := by
    intro i
    have := symmetry σ hσ ε i n
    rw [eq_div_iff hkpos.ne']; linarith
  have hsumEP : ∀ i, ∑ α, EP α i ≤ 3 * n * K / 4 := by
    intro i
    have hpin : ∀ α, EP α i ≤ EQ α i + n * Real.sqrt (max (KL α i / 2) 0) := by
      intro α
      have := pinsker_app σ hσ ε hε' i α n hn
      have e : Real.sqrt (max (KL α i / 2) 0) = Real.sqrt (KL α i / 2) := by
        rcases le_total (KL α i / 2) 0 with h | h
        · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]
        · rw [max_eq_left h]
      rw [e]; exact this
    have hg : ∑ α, max (KL α i / 2) 0 ≤ c * (n * K / k) / 2 := by
      calc ∑ α, max (KL α i / 2) 0 ≤ ∑ α, c * EQ α i / 2 := by
            apply sum_le_sum; intro α _
            apply max_le
            · have := kl_bound hm σ hσ ε hε' i α n
              linarith
            · have := hEQnn α i; positivity
        _ = c * (n * K / k) / 2 := by rw [← sum_div, ← mul_sum, hsumEQ]
    have hsq : ∑ α, Real.sqrt (max (KL α i / 2) 0) ≤ K / 4 := by
      have h1 := sum_sqrt_le univ (fun α => max (KL α i / 2) 0) (fun α _ => le_max_right _ _)
      rw [card_univ, card_GA] at h1
      refine le_trans h1 ?_
      rw [show K / 4 = Real.sqrt ((K / 4) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      calc K * ∑ α, max (KL α i / 2) 0 ≤ K * (c * (n * K / k) / 2) :=
            mul_le_mul_of_nonneg_left hg hKpos.le
        _ = K * K * (c * n) / (2 * k) := by field_simp
        _ ≤ K * K * (k / 8) / (2 * k) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hcn (by positivity)
        _ = (K / 4) ^ 2 := by field_simp; ring
    calc ∑ α, EP α i ≤ ∑ α, (EQ α i + n * Real.sqrt (max (KL α i / 2) 0)) :=
          sum_le_sum (fun α _ => hpin α)
      _ = n * K / k + n * ∑ α, Real.sqrt (max (KL α i / 2) 0) := by
          rw [sum_add_distrib, hsumEQ, mul_sum]
      _ ≤ n * K / 2 + n * (K / 4) := by
          gcongr
      _ = 3 * n * K / 4 := by ring
  -- sum of regrets
  have hR : ∀ α, ε * ∑ i : Fin m, ((n : ℝ) - EP α i) ≤
      banditRegret (Aset m k) σ (Zset m k n) (muP (Palpha ε α)) :=
    fun α => regret_lower hm σ hσ ε α n
  have htot : ∑ _α : GA m k, ε * m * n / 4 ≤
      ∑ α, banditRegret (Aset m k) σ (Zset m k n) (muP (Palpha ε α)) := by
    calc ∑ _α : GA m k, ε * m * n / 4 = K * (ε * m * n / 4) := by
          rw [sum_const, card_univ, nsmul_eq_mul, card_GA]
      _ ≤ ε * ∑ i : Fin m, ((n : ℝ) * K - ∑ α, EP α i) := by
          have : ∀ i : Fin m, (n : ℝ) * K / 4 ≤ (n : ℝ) * K - ∑ α, EP α i := by
            intro i; have := hsumEP i; linarith
          have h2 : ∑ _i : Fin m, (n : ℝ) * K / 4 ≤ ∑ i : Fin m, ((n : ℝ) * K - ∑ α, EP α i) :=
            sum_le_sum (fun i _ => this i)
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
          have h3 := mul_le_mul_of_nonneg_left h2 hε.1.le
          linarith
      _ = ∑ α, ε * ∑ i : Fin m, ((n : ℝ) - EP α i) := by
          rw [← mul_sum]; congr 1
          rw [Finset.sum_comm]
          apply sum_congr rfl; intro i _
          rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, card_GA]; ring
      _ ≤ _ := sum_le_sum (fun α _ => hR α)
  haveI : Nonempty (GA m k) := ⟨fun _ => ⟨0, by omega⟩⟩
  obtain ⟨α, _, hα⟩ := Finset.exists_le_of_sum_le univ_nonempty htot
  exact ⟨α, hα⟩

end BLBSol

open OnlineCombOpt.BanditLB BLBSol in
theorem solution (n d m : ℕ) (hn : d ≤ n) (hd : 2 * m ≤ d)
    (hdiv : m ∣ d) :
    ∃ A : Finset (Fin d → ℝ), OnlineCombOpt.Exp2LB.IsBinaryActionSet A m ∧
      ∀ σ : BanditStrategy d, IsStrategyOn A σ →
        ∃ (Z : Finset (Fin n → Fin d → ℝ))
          (μ : (Fin n → Fin d → ℝ) → ℝ),
          IsObliviousAdversary Z μ ∧
          ((2 : ℝ) / 100) * m * Real.sqrt ((d : ℝ) * n) ≤
            banditRegret A σ Z μ := by
  classical
  obtain ⟨k, rfl⟩ := hdiv
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    refine ⟨{0}, ⟨singleton_nonempty _, ?_⟩, ?_⟩
    · intro a ha
      rw [mem_singleton] at ha; subst ha
      simp
    · intro σ _
      refine ⟨{0}, fun _ => 1, ⟨by simp, by simp, by simp⟩, ?_⟩
      simp [banditRegret]
  · have hk : 2 ≤ k := by
      have : m * 2 ≤ m * k := by linarith
      exact Nat.le_of_mul_le_mul_left this hm
    refine ⟨Aset m k, ⟨⟨emb (fun _ => ⟨0, by omega⟩), by simp [Aset]⟩, ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      exact emb_binary b
    · intro σ hσ
      have hn1 : 1 ≤ n := by nlinarith
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
      have hD : (0:ℝ) < ((m * k : ℕ) : ℝ) := by
        have : 0 < m * k := by nlinarith
        exact_mod_cast this
      have hDn : ((m * k : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      set ε := Real.sqrt (((m * k : ℕ) : ℝ) * n) / (10 * n) with hεdef
      have hsq : Real.sqrt (((m * k : ℕ) : ℝ) * n) ^ 2 = ((m * k : ℕ) : ℝ) * n :=
        Real.sq_sqrt (by positivity)
      have hsqle : Real.sqrt (((m * k : ℕ) : ℝ) * n) ≤ n := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      have hεpos : 0 < ε := by positivity
      have hεle : ε ≤ 1 / 10 := by
        rw [hεdef, div_le_iff₀ (by positivity)]; linarith
      have hε2 : ε ^ 2 * (100 * n) = m * k := by
        rw [hεdef, div_pow, hsq]; push_cast; field_simp; norm_num
      obtain ⟨α, hα⟩ := main_claim (by omega) hk σ hσ n hn1 ε ⟨hεpos, hεle⟩ hε2
      refine ⟨Zset m k n, muP (Palpha ε α),
        oblivious _ (weak _ (Palpha_mem ε ⟨hεpos, by linarith⟩ α)), le_trans ?_ hα⟩
      have : ε * m * n / 4 = (1 / 40) * m * Real.sqrt (((m * k : ℕ) : ℝ) * n) := by
        rw [hεdef]; field_simp; ring
      rw [this]
      have : 0 ≤ (m : ℝ) * Real.sqrt (((m * k : ℕ) : ℝ) * n) := by positivity
      nlinarith
