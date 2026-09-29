-- Prove2me | solution 1 for RobustMDP.EntropyInner.kl_ball_inner_problem_dual
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T11:31:51.668668+00:00
-- url     : https://prove2.me/submissions/f08c3654-d610-436d-abc0-ca124bf3a768

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_klBall
import Definitions.Def_RobustMDP_EntropyInner_dualFunction

set_option autoImplicit false

/-- Pointwise Gibbs bound: `p log (p/r) ≥ p - r` for `p ≥ 0`, `r > 0`. -/
theorem kl218_term_ge (p r : ℝ) (hp : 0 ≤ p) (hr : 0 < r) :
    p - r ≤ p * Real.log (p / r) := by
  rcases hp.lt_or_eq with hp | hp
  · have h := Real.log_le_sub_one_of_pos (div_pos hr hp)
    have h2 : Real.log (p / r) = - Real.log (r / p) := by
      rw [← Real.log_inv, inv_div]
    have h3 : p * (r / p - 1) = r - p := by field_simp
    have h4 := mul_le_mul_of_nonneg_left h hp.le
    rw [h2, mul_neg]
    linarith
  · subst hp
    simp only [zero_mul, zero_sub]
    linarith

/-- Gibbs' inequality on the simplex. -/
theorem kl218_gibbs {n : ℕ} (p r : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hps : ∑ j, p j = 1)
    (hr : ∀ j, 0 < r j) (hrs : ∑ j, r j = 1) :
    0 ≤ ∑ j, p j * Real.log (p j / r j) := by
  have h : ∑ j, (p j - r j) ≤ ∑ j, p j * Real.log (p j / r j) :=
    Finset.sum_le_sum fun j _ => kl218_term_ge (p j) (r j) (hp j) (hr j)
  rw [Finset.sum_sub_distrib, hps, hrs, sub_self] at h
  exact h

/-- The partition function is positive. -/
theorem kl218_Z_pos {n : ℕ} (q w : Fin n → ℝ) (hq : ∀ j, 0 < q j) (hqs : ∑ j, q j = 1) :
    0 < ∑ j, q j * Real.exp (w j) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty] at hqs
      exact absurd hqs zero_ne_one
    · exact h
  exact Finset.sum_pos (fun j _ => mul_pos (hq j) (Real.exp_pos _)) hne

/-- Pointwise splitting of `p log (p/q)` against a tilted weight. -/
theorem kl218_term_split (p q Z w : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hZ : 0 < Z) :
    p * Real.log (p / q) = p * Real.log (p / (q * Real.exp w / Z)) + p * (w - Real.log Z) := by
  rcases hp.lt_or_eq with hp | hp
  · have hr : 0 < q * Real.exp w / Z := div_pos (mul_pos hq (Real.exp_pos w)) hZ
    rw [Real.log_div hp.ne' hq.ne', Real.log_div hp.ne' hr.ne',
      Real.log_div (mul_pos hq (Real.exp_pos w)).ne' hZ.ne',
      Real.log_mul hq.ne' (Real.exp_pos w).ne', Real.log_exp]
    ring
  · subst hp
    simp

/-- `D(p‖q) = D(p‖r) + (∑ p w - log Z)` for the tilted `r = q e^w / Z`. -/
theorem kl218_decomp {n : ℕ} (p q w : Fin n → ℝ) (Z : ℝ) (hp : ∀ j, 0 ≤ p j)
    (hps : ∑ j, p j = 1) (hq : ∀ j, 0 < q j) (hZ : 0 < Z) :
    ∑ j, p j * Real.log (p j / q j) =
      ∑ j, p j * Real.log (p j / (q j * Real.exp (w j) / Z)) + (∑ j, p j * w j - Real.log Z) := by
  rw [Finset.sum_congr rfl fun j _ => kl218_term_split (p j) (q j) Z (w j) (hp j) (hq j) hZ,
    Finset.sum_add_distrib]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hps, one_mul]

/-- Donsker–Varadhan / Gibbs variational inequality. -/
theorem kl218_weak {n : ℕ} (p q w : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hps : ∑ j, p j = 1)
    (hq : ∀ j, 0 < q j) (hqs : ∑ j, q j = 1) :
    ∑ j, p j * w j - Real.log (∑ i, q i * Real.exp (w i)) ≤ ∑ j, p j * Real.log (p j / q j) := by
  have hZ := kl218_Z_pos q w hq hqs
  have hdec := kl218_decomp p q w (∑ i, q i * Real.exp (w i)) hp hps hq hZ
  have hg : 0 ≤ ∑ j, p j * Real.log (p j / (q j * Real.exp (w j) / ∑ i, q i * Real.exp (w i))) :=
    kl218_gibbs p (fun j => q j * Real.exp (w j) / ∑ i, q i * Real.exp (w i)) hp hps
      (fun j => div_pos (mul_pos (hq j) (Real.exp_pos _)) hZ)
      (by
        show ∑ j, q j * Real.exp (w j) / (∑ i, q i * Real.exp (w i)) = 1
        rw [← Finset.sum_div]
        exact div_self hZ.ne')
  linarith

/-- Weak duality for the dual function (47). -/
theorem kl218_weak_dual {n : ℕ} (q v : Fin n → ℝ) (β : ℝ) (hq : ∀ j, 0 < q j)
    (hqs : ∑ j, q j = 1) (p : Fin n → ℝ) (hp : p ∈ RobustMDP.EntropyInner.klBall q β)
    (lam : ℝ) (hlam : 0 < lam) :
    ∑ j, p j * v j ≤ RobustMDP.EntropyInner.dualFn q v β lam := by
  have hp2 : p ∈ stdSimplex ℝ (Fin n) ∧ RobustMDP.EntropyInner.klDiv p q ≤ β := hp
  have hp' : (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 := hp2.1
  have hkl : ∑ j, p j * Real.log (p j / q j) ≤ β := hp2.2
  have h1 : ∑ j, p j * (v j / lam) - Real.log (∑ i, q i * Real.exp (v i / lam)) ≤
      ∑ j, p j * Real.log (p j / q j) := kl218_weak p q (fun j => v j / lam) hp'.1 hp'.2 hq hqs
  have h3 : ∑ j, p j * (v j / lam) = (∑ j, p j * v j) / lam := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3] at h1
  have h4 : (∑ j, p j * v j) / lam ≤ β + Real.log (∑ i, q i * Real.exp (v i / lam)) := by
    linarith
  rw [div_le_iff₀ hlam] at h4
  have h5 : (β + Real.log (∑ i, q i * Real.exp (v i / lam))) * lam
      = lam * Real.log (∑ i, q i * Real.exp (v i / lam)) + β * lam := by ring
  show _ ≤ lam * Real.log (∑ j, q j * Real.exp (v j / lam)) + β * lam
  linarith

/-- `p log (p/q) = p log p - p log q` for `q > 0` (all `p`, with `log 0 = 0`). -/
theorem kl218_log_split (p q : ℝ) (hq : 0 < q) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  rcases eq_or_ne p 0 with h | h
  · subst h
    simp
  · rw [Real.log_div h hq.ne']
    ring

/-- The KL ball is compact. -/
theorem kl218_compact {n : ℕ} (q : Fin n → ℝ) (β : ℝ) (hq : ∀ j, 0 < q j) :
    IsCompact (RobustMDP.EntropyInner.klBall q β) := by
  have hcont : Continuous fun p : Fin n → ℝ =>
      ∑ j, (p j * Real.log (p j) - p j * Real.log (q j)) :=
    continuous_finsetSum _ fun j _ =>
      (Real.continuous_mul_log.comp (continuous_apply j)).sub
        ((continuous_apply j).mul continuous_const)
  have heq : RobustMDP.EntropyInner.klBall q β =
      stdSimplex ℝ (Fin n) ∩ (fun p : Fin n → ℝ =>
        ∑ j, (p j * Real.log (p j) - p j * Real.log (q j))) ⁻¹' Set.Iic β := by
    ext p
    show p ∈ stdSimplex ℝ (Fin n) ∧ ∑ j, p j * Real.log (p j / q j) ≤ β ↔ _
    rw [Finset.sum_congr rfl fun j _ => kl218_log_split (p j) (q j) (hq j)]
    rfl
  rw [heq]
  exact (isCompact_stdSimplex ℝ (Fin n)).inter_right (isClosed_Iic.preimage hcont)

/-- `q` itself lies in the KL ball. -/
theorem kl218_q_mem {n : ℕ} (q : Fin n → ℝ) (β : ℝ) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hqp : ∀ j, 0 < q j) (hβ : 0 ≤ β) : q ∈ RobustMDP.EntropyInner.klBall q β := by
  show q ∈ stdSimplex ℝ (Fin n) ∧ ∑ j, q j * Real.log (q j / q j) ≤ β
  refine ⟨hq, ?_⟩
  rw [Finset.sum_eq_zero fun j _ => by rw [div_self (hqp j).ne', Real.log_one, mul_zero]]
  exact hβ

/-- KL divergence of the tilted distribution. -/
theorem kl218_tilted {n : ℕ} (q v : Fin n → ℝ) (t : ℝ) (hq : ∀ j, 0 < q j)
    (hqs : ∑ j, q j = 1) :
    ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) *
        Real.log (q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) / q j) =
      ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * (t * v j)
        - Real.log (∑ i, q i * Real.exp (t * v i)) := by
  have hZ0 : 0 < ∑ i, q i * Real.exp (t * v i) := kl218_Z_pos q (fun i => t * v i) hq hqs
  generalize hZd : ∑ i, q i * Real.exp (t * v i) = Z
  have hZ : 0 < Z := by rw [← hZd]; exact hZ0
  have h : ∀ j, q j * Real.exp (t * v j) / Z * Real.log (q j * Real.exp (t * v j) / Z / q j)
      = q j * Real.exp (t * v j) / Z * (t * v j) - q j * Real.exp (t * v j) / Z * Real.log Z := by
    intro j
    have hqj : q j ≠ 0 := (hq j).ne'
    have e1 : q j * Real.exp (t * v j) / Z / q j = Real.exp (t * v j) / Z := by
      rw [div_div, mul_comm Z (q j), mul_div_mul_left _ _ hqj]
    rw [e1, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
    ring
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_div, hZd, div_self hZ.ne', one_mul]

/-- The tilted distribution lies in the KL ball once its divergence is at most `β`. -/
theorem kl218_tilted_mem {n : ℕ} (q v : Fin n → ℝ) (β t : ℝ) (hq : ∀ j, 0 < q j)
    (hqs : ∑ j, q j = 1)
    (hG : ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * (t * v j)
          - Real.log (∑ i, q i * Real.exp (t * v i)) ≤ β) :
    (fun j => q j * Real.exp (t * v j) / ∑ i, q i * Real.exp (t * v i)) ∈
      RobustMDP.EntropyInner.klBall q β := by
  have hZ : 0 < ∑ i, q i * Real.exp (t * v i) := kl218_Z_pos q (fun i => t * v i) hq hqs
  refine ⟨⟨fun j => div_nonneg (mul_pos (hq j) (Real.exp_pos _)).le hZ.le, ?_⟩, ?_⟩
  · show ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) = 1
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  · show ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) *
        Real.log (q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) / q j) ≤ β
    rw [kl218_tilted q v t hq hqs]
    exact hG

/-- Continuity of the divergence of the tilted family in the inverse temperature. -/
theorem kl218_G_cont {n : ℕ} (q v : Fin n → ℝ)
    (hZ : ∀ t : ℝ, 0 < ∑ i, q i * Real.exp (t * v i)) :
    Continuous fun t : ℝ =>
      ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * (t * v j)
        - Real.log (∑ i, q i * Real.exp (t * v i)) := by
  have hZc : Continuous fun t : ℝ => ∑ i, q i * Real.exp (t * v i) := by fun_prop
  have hZne : ∀ t : ℝ, (∑ i, q i * Real.exp (t * v i)) ≠ 0 := fun t => (hZ t).ne'
  refine Continuous.sub (continuous_finsetSum _ fun j _ => ?_) (hZc.log hZne)
  exact Continuous.mul (Continuous.div (by fun_prop) hZc hZne) (by fun_prop)

/-- The dual function at `λ = 1/t` in terms of the tilted distribution. -/
theorem kl218_dual_eq {n : ℕ} (q v : Fin n → ℝ) (β t : ℝ) (ht : 0 < t) :
    RobustMDP.EntropyInner.dualFn q v β (1 / t) =
      ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * v j
      + (β - (∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * (t * v j)
          - Real.log (∑ i, q i * Real.exp (t * v i)))) / t := by
  unfold RobustMDP.EntropyInner.dualFn
  have hvt : ∀ j, v j / (1 / t) = t * v j := fun j => by
    rw [div_eq_mul_inv, one_div, inv_inv, mul_comm]
  simp only [hvt]
  generalize ∑ i, q i * Real.exp (t * v i) = Z
  have hsum : ∑ j, q j * Real.exp (t * v j) / Z * (t * v j)
      = t * ∑ j, q j * Real.exp (t * v j) / Z * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  linear_combination (∑ j, q j * Real.exp (t * v j) / Z * v j) * htt

/-- The tilted family packaged for the duality argument. -/
theorem kl218_package {n : ℕ} (q v : Fin n → ℝ) (β s : ℝ) (hq : ∀ j, 0 < q j)
    (hqs : ∑ j, q j = 1)
    (hs : ∀ p ∈ RobustMDP.EntropyInner.klBall q β, ∑ j, p j * v j ≤ s) :
    ∃ G : ℝ → ℝ, Continuous G ∧ G 0 = 0 ∧
      ∀ t, 0 < t → G t ≤ β →
        RobustMDP.EntropyInner.dualFn q v β (1 / t) ≤ s + (β - G t) / t ∧ 0 ≤ G t := by
  have hZ : ∀ t : ℝ, 0 < ∑ i, q i * Real.exp (t * v i) :=
    fun t => kl218_Z_pos q (fun i => t * v i) hq hqs
  refine ⟨fun t => ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * (t * v j)
      - Real.log (∑ i, q i * Real.exp (t * v i)), kl218_G_cont q v hZ, ?_, ?_⟩
  · simp [hqs]
  · intro t ht hGt
    have hmem := kl218_tilted_mem q v β t hq hqs hGt
    have hle : ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * v j ≤ s :=
      hs _ hmem
    have hGnn : 0 ≤ ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) * (t * v j)
        - Real.log (∑ i, q i * Real.exp (t * v i)) := by
      rw [← kl218_tilted q v t hq hqs]
      exact kl218_gibbs (fun j => q j * Real.exp (t * v j) / ∑ i, q i * Real.exp (t * v i)) q
        (fun j => div_nonneg (mul_pos (hq j) (Real.exp_pos _)).le (hZ t).le)
        (by
          show ∑ j, q j * Real.exp (t * v j) / (∑ i, q i * Real.exp (t * v i)) = 1
          rw [← Finset.sum_div]
          exact div_self (hZ t).ne')
        hq hqs
    have hde := kl218_dual_eq q v β t ht
    refine ⟨?_, hGnn⟩
    rw [hde]
    exact add_le_add hle le_rfl

open RobustMDP.EntropyInner in
theorem solution {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    ∃ s : ℝ,
      IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' klBall q β) s ∧
      IsGLB ((fun lam => dualFn q v β lam) '' Set.Ioi 0) s := by
  have hqs : ∑ j, q j = 1 := hq.2
  have hcomp := kl218_compact q β hq_pos
  have hqball : q ∈ klBall q β := kl218_q_mem q β hq hq_pos hβ.le
  have hlin : Continuous fun p : Fin n → ℝ => ∑ j, p j * v j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const
  obtain ⟨p0, hp0, hmax⟩ := hcomp.exists_isMaxOn ⟨q, hqball⟩ hlin.continuousOn
  have hs : ∀ p ∈ klBall q β, ∑ j, p j * v j ≤ ∑ j, p0 j * v j :=
    fun p hp => isMaxOn_iff.mp hmax p hp
  obtain ⟨G, hGc, hG0, hGp⟩ := kl218_package q v β (∑ j, p0 j * v j) hq_pos hqs hs
  refine ⟨∑ j, p0 j * v j, ⟨⟨p0, hp0, rfl⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hs p hp
  · rintro _ ⟨lam, hlam, rfl⟩
    exact kl218_weak_dual q v β hq_pos hqs p0 hp0 lam hlam
  · intro b hb
    have hb' : ∀ lam : ℝ, 0 < lam → b ≤ dualFn q v β lam :=
      fun lam hlam => hb ⟨lam, hlam, rfl⟩
    by_cases hcase : ∃ T : ℝ, 0 < T ∧ β ≤ G T
    · obtain ⟨T, hT, hGT⟩ := hcase
      obtain ⟨t, ⟨ht0, -⟩, hGt⟩ := intermediate_value_Icc hT.le hGc.continuousOn
        (show β ∈ Set.Icc (G 0) (G T) from ⟨by rw [hG0]; exact hβ.le, hGT⟩)
      have htpos : 0 < t := by
        rcases ht0.lt_or_eq with h | h
        · exact h
        · rw [← h, hG0] at hGt
          exact absurd hGt hβ.ne
      have h1 := (hGp t htpos hGt.le).1
      rw [hGt, sub_self, zero_div, add_zero] at h1
      exact (hb' (1 / t) (one_div_pos.mpr htpos)).trans h1
    · simp only [not_exists, not_and, not_le] at hcase
      apply le_of_forall_pos_le_add
      intro ε hε
      have ht : 0 < β / ε := div_pos hβ hε
      have h1 := hGp (β / ε) ht (hcase _ ht).le
      have hbe : β / (β / ε) = ε := by field_simp
      have hGd : 0 ≤ G (β / ε) / (β / ε) := div_nonneg h1.2 ht.le
      have h2 : (β - G (β / ε)) / (β / ε) ≤ ε := by
        rw [sub_div]
        linarith
      linarith [hb' (1 / (β / ε)) (one_div_pos.mpr ht), h1.1]
