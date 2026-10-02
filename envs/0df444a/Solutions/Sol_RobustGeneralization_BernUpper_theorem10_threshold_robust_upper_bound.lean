-- Prove2me | solution 1 for RobustGeneralization.BernUpper.theorem10_threshold_robust_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:48:57.987978+00:00
-- url     : https://prove2.me/submissions/c29c29ac-2ea8-4fa7-9d79-62fb962e1c53

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

set_option autoImplicit false

open RobustGeneralization.BernUpper in
theorem c6dfef9f_lab_mul_self (b : Bool) : lab b * lab b = 1 := by
  cases b <;> simp [lab]

open RobustGeneralization.BernUpper in
theorem c6dfef9f_lab_pm (b : Bool) : lab b = 1 ∨ lab b = -1 := by
  cases b <;> simp [lab]

open RobustGeneralization.BernUpper in
theorem c6dfef9f_inner {d : ℕ} (w x : E d) : inner ℝ w x = ∑ i, w i * x i := by
  simp [PiLp.inner_apply, mul_comm]

open RobustGeneralization.BernUpper in
theorem c6dfef9f_bernW_nonneg {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2)
    (p : (Fin d → Bool) × Bool) : 0 ≤ bernW θ τ p := by
  unfold bernW
  apply mul_nonneg (by norm_num)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

open RobustGeneralization.BernUpper in
theorem c6dfef9f_bprob_le {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2)
    (A : (Fin d → Bool) × Bool → Prop) (f : (Fin d → Bool) × Bool → ℝ)
    (hf : ∀ p, A p → 0 ≤ f p) :
    bprob θ τ A ≤ ∑ p, bernW θ τ p * Real.exp (f p) := by
  unfold bprob
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (c6dfef9f_bernW_nonneg θ τ h0 h1 p)
  split_ifs with h
  · exact Real.one_le_exp (hf p h)
  · exact (Real.exp_pos _).le

open RobustGeneralization.BernUpper in
theorem c6dfef9f_mgf {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (c : Fin d → ℝ) :
    ∑ p : (Fin d → Bool) × Bool, bernW θ τ p * Real.exp (∑ i, c i * (lab p.2 * lab (p.1 i)))
      = ∏ i, ((1 / 2 + τ) * Real.exp (c i * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-(c i * lab (θ i)))) := by
  have key : ∀ y : Bool, ∑ s : Fin d → Bool,
      (∏ i, ((if s i = (y == θ i) then 1 / 2 + τ else 1 / 2 - τ)
        * Real.exp (c i * (lab y * lab (s i)))))
      = ∏ i, ((1 / 2 + τ) * Real.exp (c i * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-(c i * lab (θ i)))) := by
    intro y
    rw [← Fintype.prod_sum (fun i b => (if b = (y == θ i) then 1 / 2 + τ else 1 / 2 - τ)
        * Real.exp (c i * (lab y * lab b)))]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.sum_bool]
    cases y <;> cases h : θ i <;> simp [lab] <;> ring_nf
  have hy : ∀ y : Bool, ∑ s : Fin d → Bool,
      bernW θ τ (s, y) * Real.exp (∑ i, c i * (lab y * lab (s i)))
      = (1 / 2) * ∏ i, ((1 / 2 + τ) * Real.exp (c i * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-(c i * lab (θ i)))) := by
    intro y
    rw [← key y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [bernW, Real.exp_sum, Finset.prod_mul_distrib]
    ring
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Fintype.sum_bool, hy true, hy false]
  ring

theorem c6dfef9f_coord (τ l a : ℝ) (ha : a = 1 ∨ a = -1) :
    (1 / 2 + τ) * Real.exp (-l * a) + (1 / 2 - τ) * Real.exp (-(-l * a))
      ≤ Real.exp (Real.cosh l - 1 - 2 * τ * a * Real.sinh l) := by
  have h : (1 / 2 + τ) * Real.exp (-l * a) + (1 / 2 - τ) * Real.exp (-(-l * a))
      = Real.cosh l - 2 * τ * a * Real.sinh l := by
    rcases ha with rfl | rfl <;> simp [Real.cosh_eq, Real.sinh_eq] <;> ring
  rw [h]
  have := Real.add_one_le_exp (Real.cosh l - 1 - 2 * τ * a * Real.sinh l)
  linarith

theorem c6dfef9f_prod_bound {d : ℕ} (τ l : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2)
    (u a : Fin d → ℝ) (ha : ∀ i, a i = 1 ∨ a i = -1) (hu : ∀ i, u i = -l * a i) :
    ∏ i, ((1 / 2 + τ) * Real.exp (u i) + (1 / 2 - τ) * Real.exp (-(u i)))
      ≤ Real.exp (d * (Real.cosh l - 1) - 2 * τ * Real.sinh l * ∑ i, a i) := by
  have hE : Real.exp (d * (Real.cosh l - 1) - 2 * τ * Real.sinh l * ∑ i, a i)
      = ∏ i, Real.exp (Real.cosh l - 1 - 2 * τ * a i * Real.sinh l) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hE]
  apply Finset.prod_le_prod
  · intro i _
    have := Real.exp_pos (u i)
    have := Real.exp_pos (-(u i))
    have h2 : 0 ≤ 1 / 2 - τ := by linarith
    positivity
  · intro i _
    rw [hu i]
    exact c6dfef9f_coord τ l (a i) (ha i)

theorem c6dfef9f_cosh (l : ℝ) (hl : l ^ 2 ≤ 2) : Real.cosh l - 1 ≤ l ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq l
  have hnn : (0 : ℝ) ≤ l ^ 2 / 2 := by positivity
  have h2 := Real.abs_exp_sub_one_le (x := l ^ 2 / 2) (by rw [abs_of_nonneg hnn]; linarith)
  have h3 := le_abs_self (Real.exp (l ^ 2 / 2) - 1)
  rw [abs_of_nonneg hnn] at h2
  linarith

open RobustGeneralization.BernUpper in
theorem c6dfef9f_thr {d : ℕ} (s : Fin d → Bool) (ε : ℝ) (hε : ε < 1) (x : E d)
    (hx : x ∈ linfBall (pm s) ε) : thr x = pm s := by
  unfold thr pm
  congr 1
  funext i
  have hi := hx i
  simp only [pm] at hi
  rw [abs_le] at hi
  cases h : s i <;> simp [h, lab] at hi ⊢
  · intro h0
    linarith [hi.2]
  · intro h0
    linarith [hi.1]

open RobustGeneralization.BernUpper in
theorem c6dfef9f_stage2 {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hc : 4 * (d : ℝ) ^ (-(1 : ℝ) / 4) ≤ τ) (p : (Fin d → Bool) × Bool)
    (hS : τ * d / 4 < ∑ i, lab p.2 * lab (p.1 i) * lab (θ i)) (ε : ℝ) (hε : ε < 1) :
    robErr θ τ (thrClf (zvec p)) ε ≤ 1 / 100 := by
  have hd : (d : ℝ) ≠ 0 := by
    intro h
    have h' : d = 0 := by exact_mod_cast h
    subst h'
    simp at hS
  have hdpos : (0 : ℝ) < d := lt_of_le_of_ne (Nat.cast_nonneg d) (Ne.symm hd)
  -- τ^4 d ≥ 256
  have h256 : 256 ≤ τ ^ 4 * d := by
    set t : ℝ := (d : ℝ) ^ ((1 : ℝ) / 4) with ht
    have htpos : 0 < t := Real.rpow_pos_of_pos hdpos _
    have ht4 : t ^ 4 = d := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]
      norm_num
    have hneg : (d : ℝ) ^ (-(1 : ℝ) / 4) = t⁻¹ := by
      rw [neg_div, Real.rpow_neg hdpos.le]
    rw [hneg] at hc
    have h4 : 4 ≤ τ * t := by
      have := mul_le_mul_of_nonneg_right hc htpos.le
      rw [mul_assoc, inv_mul_cancel₀ htpos.ne', mul_one] at this
      exact this
    have := pow_le_pow_left₀ (by norm_num) h4 4
    rw [mul_pow, ht4] at this
    norm_num at this
    linarith
  set l : ℝ := τ ^ 2 / 4 with hl
  have hl0 : 0 ≤ l := by positivity
  have hτsq : τ ^ 2 ≤ 1 / 4 := by nlinarith
  have hl2 : l ^ 2 ≤ 2 := by
    have : l ≤ 1 / 16 := by rw [hl]; linarith
    nlinarith
  set S : ℝ := ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) with hSdef
  have hcosh := c6dfef9f_cosh l hl2
  have hsinh : l ≤ Real.sinh l := Real.self_le_sinh_iff.mpr hl0
  calc robErr θ τ (thrClf (zvec p)) ε
      ≤ ∑ p' : (Fin d → Bool) × Bool, bernW θ τ p'
          * Real.exp (∑ i, (-l * (lab p.2 * lab (p.1 i))) * (lab p'.2 * lab (p'.1 i))) := by
        unfold robErr
        apply c6dfef9f_bprob_le θ τ hτ0.le hτ1
        rintro p' ⟨x', hx', hne⟩
        have hthr : thr x' = pm p'.1 := c6dfef9f_thr p'.1 ε hε x' hx'
        have hin : inner ℝ (zvec p) (pm p'.1)
            = ∑ i, lab p.2 * lab (p.1 i) * lab (p'.1 i) := by
          rw [c6dfef9f_inner]
          apply Finset.sum_congr rfl
          intro i _
          simp [zvec, pm]
        have hsum : ∑ i, (-l * (lab p.2 * lab (p.1 i))) * (lab p'.2 * lab (p'.1 i))
            = -l * (lab p'.2 * ∑ i, lab p.2 * lab (p.1 i) * lab (p'.1 i)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hsum]
        simp only [thrClf, linClf, hthr, hin] at hne
        set I : ℝ := ∑ i, lab p.2 * lab (p.1 i) * lab (p'.1 i) with hI
        cases hy : p'.2 <;> rw [hy] at hne <;> simp [lab] at hne ⊢ <;> nlinarith
    _ = ∏ i, ((1 / 2 + τ) * Real.exp ((-l * (lab p.2 * lab (p.1 i))) * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-((-l * (lab p.2 * lab (p.1 i))) * lab (θ i)))) :=
        c6dfef9f_mgf θ τ (fun i => -l * (lab p.2 * lab (p.1 i)))
    _ ≤ Real.exp (d * (Real.cosh l - 1) - 2 * τ * Real.sinh l * S) :=
        c6dfef9f_prod_bound τ l hτ0.le hτ1
          (fun i => (-l * (lab p.2 * lab (p.1 i))) * lab (θ i))
          (fun i => lab p.2 * lab (p.1 i) * lab (θ i))
          (fun i => by
            rcases c6dfef9f_lab_pm p.2 with h1 | h1 <;>
            rcases c6dfef9f_lab_pm (p.1 i) with h2 | h2 <;>
            rcases c6dfef9f_lab_pm (θ i) with h3 | h3 <;>
            simp [h1, h2, h3])
          (fun i => by ring)
    _ ≤ Real.exp (-16) := by
        apply Real.exp_le_exp.mpr
        have hSpos : 0 < S := by
          have : 0 ≤ τ * d / 4 := by positivity
          linarith
        have e1 : (d : ℝ) * (Real.cosh l - 1) ≤ d * l ^ 2 :=
          mul_le_mul_of_nonneg_left hcosh hdpos.le
        have e2 : 2 * τ * l * S ≤ 2 * τ * Real.sinh l * S := by
          have : 0 ≤ 2 * τ * S := by positivity
          nlinarith
        have e3 : 2 * τ * l * (τ * d / 4) ≤ 2 * τ * l * S := by
          have : 0 ≤ 2 * τ * l := by positivity
          exact mul_le_mul_of_nonneg_left hS.le this
        have e4 : (d : ℝ) * l ^ 2 - 2 * τ * l * (τ * d / 4) = -(τ ^ 4 * d) / 16 := by
          rw [hl]; ring
        linarith
    _ ≤ 1 / 100 := by
        have h1 := Real.quadratic_le_exp_of_nonneg (x := 16) (by norm_num)
        rw [Real.exp_neg]
        rw [inv_le_comm₀ (Real.exp_pos 16) (by norm_num)]
        norm_num at h1 ⊢
        linarith

open RobustGeneralization.BernUpper in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (θ : Fin d → Bool) (τ : ℝ), 0 < τ → τ ≤ 1 / 2 →
      c * (d : ℝ) ^ (-(1 : ℝ) / 4) ≤ τ →
      bprob θ τ (fun p => ∃ ε : ℝ, ε < 1 ∧ 1 / 100 < robErr θ τ (thrClf (zvec p)) ε)
        ≤ Real.exp (-(τ ^ 2 * d / 2)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro d θ τ hτ0 hτ1 hc
  have hsumeq : ∀ p : (Fin d → Bool) × Bool,
      ∑ i, (-τ * lab (θ i)) * (lab p.2 * lab (p.1 i))
        = -τ * ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) := by
    intro p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hτsq : τ ^ 2 ≤ 2 := by nlinarith
  have hcosh := c6dfef9f_cosh τ hτsq
  have hsinh : τ ≤ Real.sinh τ := Real.self_le_sinh_iff.mpr hτ0.le
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc bprob θ τ (fun p => ∃ ε : ℝ, ε < 1 ∧ 1 / 100 < robErr θ τ (thrClf (zvec p)) ε)
      ≤ ∑ p : (Fin d → Bool) × Bool, bernW θ τ p
          * Real.exp (τ * (τ * d / 4) + ∑ i, (-τ * lab (θ i)) * (lab p.2 * lab (p.1 i))) := by
        apply c6dfef9f_bprob_le θ τ hτ0.le hτ1
        rintro p ⟨ε, hε, hbad⟩
        have hS : ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) ≤ τ * d / 4 := by
          by_contra hS
          have := c6dfef9f_stage2 θ τ hτ0 hτ1 hc p (not_le.mp hS) ε hε
          linarith
        rw [hsumeq p]
        nlinarith
    _ = Real.exp (τ * (τ * d / 4)) * ∑ p : (Fin d → Bool) × Bool, bernW θ τ p
          * Real.exp (∑ i, (-τ * lab (θ i)) * (lab p.2 * lab (p.1 i))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [Real.exp_add]
        ring
    _ = Real.exp (τ * (τ * d / 4)) * ∏ i, ((1 / 2 + τ) * Real.exp ((-τ * lab (θ i)) * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-((-τ * lab (θ i)) * lab (θ i)))) := by
        rw [c6dfef9f_mgf θ τ (fun i => -τ * lab (θ i))]
    _ ≤ Real.exp (τ * (τ * d / 4))
          * Real.exp (d * (Real.cosh τ - 1) - 2 * τ * Real.sinh τ * ∑ _i : Fin d, (1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact c6dfef9f_prod_bound τ τ hτ0.le hτ1
          (fun i => (-τ * lab (θ i)) * lab (θ i)) (fun _ => (1 : ℝ))
          (fun _ => Or.inl rfl)
          (fun i => by
            show -τ * lab (θ i) * lab (θ i) = -τ * 1
            rw [mul_assoc, c6dfef9f_lab_mul_self])
    _ ≤ Real.exp (-(τ ^ 2 * d / 2)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        have e1 : (d : ℝ) * (Real.cosh τ - 1) ≤ d * τ ^ 2 :=
          mul_le_mul_of_nonneg_left hcosh hd0
        have e2 : 2 * τ * τ * d ≤ 2 * τ * Real.sinh τ * d := by
          have : 0 ≤ 2 * τ * d := by positivity
          nlinarith
        nlinarith
