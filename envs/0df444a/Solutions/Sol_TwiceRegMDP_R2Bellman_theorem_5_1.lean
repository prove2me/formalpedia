-- Prove2me | solution 1 for TwiceRegMDP.R2Bellman.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:37:48.252518+00:00
-- url     : https://prove2.me/submissions/6d203426-2d33-43c7-8eb8-b5166870c1b0

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_R2Bellman_MDP
import Definitions.Def_TwiceRegMDP_R2Bellman_R2Ops



namespace TwiceRegMDP.R2Bellman

open Finset Filter Topology

lemma l2norm_nonneg' {Z : Type} [Fintype Z] (a : Z → ℝ) : 0 ≤ l2norm a := Real.sqrt_nonneg _

lemma l2norm_eq' {Z : Type} [Fintype Z] (a : Z → ℝ) :
    l2norm a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ Z)‖ := by
  rw [EuclideanSpace.norm_eq]; simp [l2norm, sq_abs]

lemma l2norm_sub_le' {Z : Type} [Fintype Z] (a b : Z → ℝ) :
    |l2norm a - l2norm b| ≤ l2norm (a - b) := by
  rw [l2norm_eq', l2norm_eq', l2norm_eq']
  have := abs_norm_sub_norm_le (WithLp.toLp 2 a : EuclideanSpace ℝ Z) (WithLp.toLp 2 b)
  simpa using this

lemma l2norm_mul' {Z : Type} [Fintype Z] (c : ℝ) (p : Z → ℝ) :
    l2norm (fun a => c * p a) = |c| * l2norm p := by
  unfold l2norm
  have : ∑ a, (c * p a) ^ 2 = c ^ 2 * ∑ a, p a ^ 2 := by
    rw [mul_sum]; apply sum_congr rfl; intro a _; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma l2norm_le_one' {Z : Type} [Fintype Z] (p : Z → ℝ) (hp : p ∈ stdSimplex ℝ Z) :
    l2norm p ≤ 1 := by
  unfold l2norm
  apply Real.sqrt_le_one.mpr
  calc ∑ a, p a ^ 2 ≤ ∑ a, p a := by
        apply sum_le_sum; intro a _
        have h0 := hp.1 a
        have h1 : p a ≤ 1 := hp.2 ▸ Finset.single_le_sum (fun i _ => hp.1 i) (mem_univ a)
        nlinarith
    _ = 1 := hp.2

lemma l2norm_pos' {Z : Type} [Fintype Z] (p : Z → ℝ) (hp : p ∈ stdSimplex ℝ Z) :
    0 < l2norm p := by
  unfold l2norm
  apply Real.sqrt_pos.mpr
  by_contra h
  push_neg at h
  have h0 : ∑ a, p a ^ 2 = 0 := le_antisymm h (sum_nonneg fun a _ => sq_nonneg _)
  rw [sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg _)] at h0
  have : ∑ a, p a = 0 := sum_eq_zero fun a ha => by
    have := h0 a ha
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have h2 := hp.2
  linarith

lemma l2norm_le_card' {Z : Type} [Fintype Z] (d : Z → ℝ) :
    l2norm d ≤ Real.sqrt (Fintype.card Z) * ‖d‖ := by
  unfold l2norm
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc ∑ z, d z ^ 2 ≤ ∑ z : Z, ‖d‖ ^ 2 := by
        apply sum_le_sum; intro z _
        have := norm_le_pi_norm d z
        rw [Real.norm_eq_abs] at this
        nlinarith [abs_nonneg (d z), sq_abs (d z)]
    _ = _ := by simp

section main

variable {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]

noncomputable def Fq (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (v : S → ℝ) (s : S) (p : A → ℝ) : ℝ :=
  ∑ a, p a * qfun γ P₀ r₀ v s a - r2Reg γ αr αP v s p

lemma evalOpR2_eq (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (π : S → A → ℝ) (v : S → ℝ) (s : S) :
    evalOpR2 γ P₀ r₀ αr αP π v s = Fq γ P₀ r₀ αr αP v s (π s) := rfl

lemma X_bound (P₀ : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀) (s : S)
    (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) (d : S → ℝ) (M : ℝ) (hd : ∀ s', |d s'| ≤ M) :
    |∑ a, p a * ∑ s', P₀ s a s' * d s'| ≤ M := by
  calc _ ≤ ∑ a, |p a * ∑ s', P₀ s a s' * d s'| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, p a * M := by
      apply Finset.sum_le_sum; intro a _
      rw [abs_mul, abs_of_nonneg (hp.1 a)]
      apply mul_le_mul_of_nonneg_left _ (hp.1 a)
      calc |∑ s', P₀ s a s' * d s'| ≤ ∑ s', |P₀ s a s' * d s'| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ s', P₀ s a s' * M := by
          apply sum_le_sum; intro s' _
          rw [abs_mul, abs_of_nonneg ((hP s a).1 s')]
          exact mul_le_mul_of_nonneg_left (hd s') ((hP s a).1 s')
        _ = M := by rw [← sum_mul, (hP s a).2, one_mul]
    _ = M := by rw [← sum_mul, hp.2, one_mul]

lemma Fq_sub (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (v1 v2 : S → ℝ) (s : S) (p : A → ℝ) :
    Fq γ P₀ r₀ αr αP v1 s p - Fq γ P₀ r₀ αr αP v2 s p =
      γ * (∑ a, p a * ∑ s', P₀ s a s' * (v1 - v2) s') -
        l2norm p * (αP s * γ * (l2norm v1 - l2norm v2)) := by
  have h1 : ∑ a, p a * qfun γ P₀ r₀ v1 s a - ∑ a, p a * qfun γ P₀ r₀ v2 s a =
      γ * (∑ a, p a * ∑ s', P₀ s a s' * (v1 - v2) s') := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    simp only [qfun, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  unfold Fq r2Reg
  linarith [h1, show l2norm p * (αr s + αP s * γ * l2norm v1) -
      l2norm p * (αr s + αP s * γ * l2norm v2) =
      l2norm p * (αP s * γ * (l2norm v1 - l2norm v2)) by ring]

lemma F_contr (γ : ℝ) (hγ0 : 0 < γ)
    (P₀ : S → A → S → ℝ) (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ) (αr αP : S → ℝ) (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ)
    (hαP : ∀ s, 0 ≤ αP s)
    (v1 v2 : S → ℝ) (s : S) (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) :
    |Fq γ P₀ r₀ αr αP v1 s p - Fq γ P₀ r₀ αr αP v2 s p| ≤ (1 - ϵ s) * ‖v1 - v2‖ := by
  rw [Fq_sub]
  set M := ‖v1 - v2‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hX : |∑ a, p a * ∑ s', P₀ s a s' * (v1 - v2) s'| ≤ M :=
    X_bound P₀ hP s p hp _ M (fun s' => by
      have := norm_le_pi_norm (v1 - v2) s'
      simpa [Real.norm_eq_abs] using this)
  have hcard : 0 < γ * Real.sqrt (Fintype.card S) := by
    have : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
    positivity
  have hα : αP s * (γ * Real.sqrt (Fintype.card S)) ≤ 1 - γ - ϵ s :=
    (le_div_iff₀ hcard).mp (hasm s).2.1
  have hn1 := l2norm_le_one' p hp
  have hn0 := l2norm_nonneg' p
  have hd := l2norm_sub_le' v1 v2
  have hd2 := l2norm_le_card' (v1 - v2)
  have hY : |l2norm p * (αP s * γ * (l2norm v1 - l2norm v2))| ≤ (1 - γ - ϵ s) * M := by
    rw [abs_mul, abs_of_nonneg hn0, abs_mul, abs_of_nonneg (mul_nonneg (hαP s) hγ0.le)]
    have h3 : |l2norm v1 - l2norm v2| ≤ Real.sqrt (Fintype.card S) * M := hd.trans hd2
    have h4 : αP s * γ * |l2norm v1 - l2norm v2| ≤ αP s * γ * (Real.sqrt (Fintype.card S) * M) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (hαP s) hγ0.le)
    calc l2norm p * (αP s * γ * |l2norm v1 - l2norm v2|)
        ≤ 1 * (αP s * γ * |l2norm v1 - l2norm v2|) :=
          mul_le_mul_of_nonneg_right hn1 (mul_nonneg (mul_nonneg (hαP s) hγ0.le) (abs_nonneg _))
      _ ≤ αP s * γ * (Real.sqrt (Fintype.card S) * M) := by linarith
      _ = (αP s * (γ * Real.sqrt (Fintype.card S))) * M := by ring
      _ ≤ (1 - γ - ϵ s) * M := mul_le_mul_of_nonneg_right hα hM0
  have hX' : |γ * ∑ a, p a * ∑ s', P₀ s a s' * (v1 - v2) s'| ≤ γ * M := by
    rw [abs_mul, abs_of_pos hγ0]; exact mul_le_mul_of_nonneg_left hX hγ0.le
  calc _ ≤ |γ * ∑ a, p a * ∑ s', P₀ s a s' * (v1 - v2) s'| +
        |l2norm p * (αP s * γ * (l2norm v1 - l2norm v2))| := abs_sub _ _
    _ ≤ γ * M + (1 - γ - ϵ s) * M := add_le_add hX' hY
    _ = (1 - ϵ s) * M := by ring

lemma eps_facts (γ : ℝ) (hγ0 : 0 < γ)
    (P₀ : S → A → S → ℝ) (αP : S → ℝ) (hαP : ∀ s, 0 ≤ αP s) (ϵ : S → ℝ)
    (hasm : BoundedRadius γ P₀ αP ϵ) :
    0 < epsStar ϵ ∧ (∀ s, epsStar ϵ ≤ ϵ s) ∧ epsStar ϵ < 1 := by
  have hle : ∀ s, epsStar ϵ ≤ ϵ s := fun s => Finset.inf'_le _ (Finset.mem_univ s)
  refine ⟨?_, hle, ?_⟩
  · unfold epsStar
    rw [Finset.lt_inf'_iff]
    exact fun s _ => (hasm s).1
  · obtain ⟨s⟩ := (inferInstance : Nonempty S)
    have hcard : 0 < γ * Real.sqrt (Fintype.card S) := by
      have : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
      positivity
    have hα : αP s * (γ * Real.sqrt (Fintype.card S)) ≤ 1 - γ - ϵ s :=
      (le_div_iff₀ hcard).mp (hasm s).2.1
    have := mul_nonneg (hαP s) hcard.le
    have := hle s
    linarith

lemma opt_spec (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (v : S → ℝ) (s : S) :
    ∃ p ∈ stdSimplex ℝ A, Fq γ P₀ r₀ αr αP v s p = optOpR2 γ P₀ r₀ αr αP v s ∧
      ∀ q ∈ stdSimplex ℝ A, Fq γ P₀ r₀ αr αP v s q ≤ optOpR2 γ P₀ r₀ αr αP v s := by
  have hcont : Continuous (Fq γ P₀ r₀ αr αP v s) := by
    unfold Fq r2Reg l2norm
    fun_prop
  have hne : (stdSimplex ℝ A).Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty A)
    exact ⟨Pi.single a 1, single_mem_stdSimplex ℝ a⟩
  obtain ⟨x, hx, hmax⟩ := (isCompact_stdSimplex ℝ A).exists_isMaxOn hne hcont.continuousOn
  have hopt : optOpR2 γ P₀ r₀ αr αP v s = Fq γ P₀ r₀ αr αP v s x := by
    unfold optOpR2
    apply IsGreatest.csSup_eq
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hmax hq
  refine ⟨x, hx, hopt.symm, fun q hq => ?_⟩
  rw [hopt]; exact hmax hq

lemma F_mono (γ : ℝ) (hγ0 : 0 < γ)
    (P₀ : S → A → S → ℝ) (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ) (αr αP : S → ℝ) (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ)
    (hαP : ∀ s, 0 ≤ αP s)
    (v1 v2 : S → ℝ) (h12 : v1 ≤ v2) (s : S) (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) :
    Fq γ P₀ r₀ αr αP v1 s p ≤ Fq γ P₀ r₀ αr αP v2 s p := by
  have key := Fq_sub γ P₀ r₀ αr αP v2 v1 s p
  set d : S → ℝ := v2 - v1 with hd
  have hd0 : ∀ s', 0 ≤ d s' := fun s' => sub_nonneg.mpr (h12 s')
  set X := ∑ a, p a * ∑ s', P₀ s a s' * d s' with hX
  have hX0 : 0 ≤ X := sum_nonneg fun a _ => mul_nonneg (hp.1 a)
    (sum_nonneg fun s' _ => mul_nonneg ((hP s a).1 s') (hd0 s'))
  have hXge : αP s * (l2norm p * l2norm d) ≤ X := by
    by_cases hdz : l2norm d = 0
    · rw [hdz]; simpa using hX0
    · have hdpos : 0 < l2norm d := lt_of_le_of_ne (l2norm_nonneg' d) (Ne.symm hdz)
      have hppos := l2norm_pos' p hp
      let u : A → ℝ := fun a => (1 / l2norm p) * p a
      let w : S → ℝ := fun s' => (1 / l2norm d) * d s'
      have hu1 : l2norm u = 1 := by
        simp only [u]; rw [l2norm_mul', abs_of_pos (one_div_pos.2 hppos)]; field_simp
      have hw1 : l2norm w = 1 := by
        simp only [w]; rw [l2norm_mul', abs_of_pos (one_div_pos.2 hdpos)]; field_simp
      have hmem : (u, w) ∈ {uw : (A → ℝ) × (S → ℝ) | (∀ a, 0 ≤ uw.1 a) ∧ l2norm uw.1 = 1 ∧
          (∀ s', 0 ≤ uw.2 s') ∧ l2norm uw.2 = 1} :=
        ⟨fun a => mul_nonneg (one_div_pos.2 hppos).le (hp.1 a), hu1,
          fun s' => mul_nonneg (one_div_pos.2 hdpos).le (hd0 s'), hw1⟩
      have hbdd : BddBelow ((fun uw : (A → ℝ) × (S → ℝ) => ∑ a, ∑ s', uw.1 a * P₀ s a s' * uw.2 s') ''
          {uw | (∀ a, 0 ≤ uw.1 a) ∧ l2norm uw.1 = 1 ∧ (∀ s', 0 ≤ uw.2 s') ∧ l2norm uw.2 = 1}) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨uw, ⟨h1, _, h3, _⟩, rfl⟩
        exact sum_nonneg fun a _ => sum_nonneg fun s' _ =>
          mul_nonneg (mul_nonneg (h1 a) ((hP s a).1 s')) (h3 s')
      have hle1 : innerMin P₀ s ≤ ∑ a, ∑ s', u a * P₀ s a s' * w s' :=
        csInf_le hbdd ⟨(u, w), hmem, rfl⟩
      have hval : ∑ a, ∑ s', u a * P₀ s a s' * w s' = (1 / l2norm p) * (1 / l2norm d) * X := by
        rw [hX, mul_sum]
        apply sum_congr rfl; intro a _
        rw [mul_sum, mul_sum]
        apply sum_congr rfl; intro s' _
        simp only [u, w]; ring
      have h3 : αP s ≤ (1 / l2norm p) * (1 / l2norm d) * X := by
        rw [← hval]; exact (hasm s).2.2.trans hle1
      have h4 : αP s * (l2norm p * l2norm d) ≤ (1 / l2norm p) * (1 / l2norm d) * X * (l2norm p * l2norm d) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      have h5 : (1 / l2norm p) * (1 / l2norm d) * X * (l2norm p * l2norm d) = X := by
        field_simp
      linarith
  have hn := l2norm_sub_le' v2 v1
  have hn0 := l2norm_nonneg' p
  have hY : l2norm p * (αP s * γ * (l2norm v2 - l2norm v1)) ≤
      l2norm p * (αP s * γ * l2norm d) := by
    apply mul_le_mul_of_nonneg_left _ hn0
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hαP s) hγ0.le)
    exact (le_abs_self _).trans hn
  have : γ * (αP s * (l2norm p * l2norm d)) ≤ γ * X := mul_le_mul_of_nonneg_left hXge hγ0.le
  nlinarith

lemma F_unique (γ : ℝ) (hγ0 : 0 < γ)
    (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ)
    (hαP : ∀ s, 0 ≤ αP s) (v : S → ℝ) (s : S) (hαr : 0 < αr s)
    (p1 p2 : A → ℝ) (hp1 : p1 ∈ stdSimplex ℝ A) (hp2 : p2 ∈ stdSimplex ℝ A)
    (h1 : Fq γ P₀ r₀ αr αP v s p1 = optOpR2 γ P₀ r₀ αr αP v s)
    (h2 : Fq γ P₀ r₀ αr αP v s p2 = optOpR2 γ P₀ r₀ αr αP v s) : p1 = p2 := by
  by_contra hne
  obtain ⟨p0, _, _, hmax⟩ := opt_spec γ P₀ r₀ αr αP v s
  set c := αr s + αP s * γ * l2norm v with hc
  have hcpos : 0 < c := by
    have := mul_nonneg (mul_nonneg (hαP s) hγ0.le) (l2norm_nonneg' v)
    rw [hc]; linarith
  have hlt : l2norm (fun a => p1 a + p2 a) < l2norm p1 + l2norm p2 := by
    rw [l2norm_eq', l2norm_eq', l2norm_eq']
    have : (WithLp.toLp 2 (fun a => p1 a + p2 a) : EuclideanSpace ℝ A) =
        WithLp.toLp 2 p1 + WithLp.toLp 2 p2 := rfl
    rw [this]
    apply norm_add_lt_of_not_sameRay
    intro hray
    rcases hray with h | h | ⟨r1, r2, hr1, hr2, h⟩
    · have : p1 = 0 := by simpa using h
      have h2' := hp1.2
      rw [this] at h2'; simp at h2'
    · have : p2 = 0 := by simpa using h
      have h2' := hp2.2
      rw [this] at h2'; simp at h2'
    · have hco : ∀ a, r1 * p1 a = r2 * p2 a := by
        intro a
        have := congrArg (fun z : EuclideanSpace ℝ A => z a) h
        simpa using this
      have hs : r1 = r2 := by
        have e1 : ∑ a, r1 * p1 a = r1 := by rw [← mul_sum, hp1.2, mul_one]
        have e2 : ∑ a, r2 * p2 a = r2 := by rw [← mul_sum, hp2.2, mul_one]
        rw [← e1, ← e2]; exact sum_congr rfl fun a _ => hco a
      apply hne
      funext a
      have := hco a
      rw [← hs] at this
      exact mul_left_cancel₀ hr1.ne' this
  have hmid : (fun a => 1 / 2 * (p1 a + p2 a)) ∈ stdSimplex ℝ A := by
    refine ⟨fun a => ?_, ?_⟩
    · have := hp1.1 a; have := hp2.1 a; positivity
    · rw [← Finset.mul_sum, Finset.sum_add_distrib, hp1.2, hp2.2]; norm_num
  have hF := hmax _ hmid
  have hL : ∑ a, (1 / 2 * (p1 a + p2 a)) * qfun γ P₀ r₀ v s a =
      1 / 2 * (∑ a, p1 a * qfun γ P₀ r₀ v s a) + 1 / 2 * (∑ a, p2 a * qfun γ P₀ r₀ v s a) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro a _; ring
  have hN : l2norm (fun a => 1 / 2 * (p1 a + p2 a)) = 1 / 2 * l2norm (fun a => p1 a + p2 a) := by
    rw [l2norm_mul']; norm_num
  unfold Fq r2Reg at hF h1 h2
  rw [hL, hN, ← hc] at hF
  have := mul_pos (sub_pos.2 hlt) hcpos
  nlinarith

end main

lemma banach_aux {S : Type} [Fintype S] [Nonempty S] (f : (S → ℝ) → (S → ℝ)) (K : ℝ)
    (hK0 : 0 ≤ K) (hK1 : K < 1) (hf : ∀ v w, ‖f v - f w‖ ≤ K * ‖v - w‖) :
    ∃ x, f x = x ∧ (∀ y, f y = y → y = x) ∧
      ∀ y, Tendsto (fun n => f^[n] y) atTop (𝓝 x) := by
  have hc : ContractingWith ⟨K, hK0⟩ f :=
    ⟨by exact_mod_cast hK1, LipschitzWith.of_dist_le_mul (fun v w => by
      rw [dist_eq_norm, dist_eq_norm]; exact hf v w)⟩
  exact ⟨ContractingWith.fixedPoint f hc, hc.fixedPoint_isFixedPt,
    fun y hy => hc.fixedPoint_unique hy, fun y => hc.tendsto_iterate_fixedPoint y⟩

theorem r2_core {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαr : ∀ s, 0 ≤ αr s) (hαP : ∀ s, 0 ≤ αP s)
    (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ) :
    ∃ vstar : S → ℝ,
      optOpR2 γ P₀ r₀ αr αP vstar = vstar ∧
      (∀ v : S → ℝ, optOpR2 γ P₀ r₀ αr αP v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π → ∃! v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v) ∧
      (∃ π : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      (∀ πstar : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar πstar →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP πstar v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v ≤ vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        (∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v = vstar) →
        IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      ((∀ s, 0 < αr s) →
        ∀ π₁ π₂ : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π₁ →
          IsGreedy γ P₀ r₀ αr αP vstar π₂ → π₁ = π₂) := by
  obtain ⟨hεpos, hεle, hεlt⟩ := eps_facts γ hγ0 P₀ αP hαP ϵ hasm
  obtain ⟨K, hK⟩ : ∃ K, K = 1 - epsStar ϵ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have hK1 : K < 1 := by rw [hK]; linarith
  have hKM : ∀ s, (1 - ϵ s) * ‖(0:ℝ)‖ ≤ K * ‖(0:ℝ)‖ := fun s => by simp
  have hFc : ∀ (v1 v2 : S → ℝ) (s : S) (p : A → ℝ), p ∈ stdSimplex ℝ A →
      |Fq γ P₀ r₀ αr αP v1 s p - Fq γ P₀ r₀ αr αP v2 s p| ≤ K * ‖v1 - v2‖ := by
    intro v1 v2 s p hp
    refine (F_contr γ hγ0 P₀ hP₀ r₀ αr αP ϵ hasm hαP v1 v2 s p hp).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [hK]; linarith [hεle s]
  have heval : ∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π → ∀ v w : S → ℝ,
      ‖evalOpR2 γ P₀ r₀ αr αP π v - evalOpR2 γ P₀ r₀ αr αP π w‖ ≤ K * ‖v - w‖ := by
    intro π hπ v w
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK0 (norm_nonneg _))).2 fun s => ?_
    rw [Real.norm_eq_abs]
    exact hFc v w s (π s) (hπ s)
  have hoptle : ∀ v w : S → ℝ, ∀ s,
      optOpR2 γ P₀ r₀ αr αP v s ≤ optOpR2 γ P₀ r₀ αr αP w s + K * ‖v - w‖ := by
    intro v w s
    obtain ⟨p, hp, hpe, _⟩ := opt_spec γ P₀ r₀ αr αP v s
    obtain ⟨_, _, _, hmax⟩ := opt_spec γ P₀ r₀ αr αP w s
    have h1 := hFc v w s p hp
    have h2 := hmax p hp
    rw [← hpe]
    linarith [(abs_le.mp h1).2]
  have hopt : ∀ v w : S → ℝ,
      ‖optOpR2 γ P₀ r₀ αr αP v - optOpR2 γ P₀ r₀ αr αP w‖ ≤ K * ‖v - w‖ := by
    intro v w
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK0 (norm_nonneg _))).2 fun s => ?_
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hoptle v w s
    have h2 := hoptle w v s
    rw [norm_sub_rev w v] at h2
    simp only [Pi.sub_apply]
    constructor <;> linarith
  have hoptmono : ∀ v w : S → ℝ, v ≤ w →
      optOpR2 γ P₀ r₀ αr αP v ≤ optOpR2 γ P₀ r₀ αr αP w := by
    intro v w hvw s
    obtain ⟨p, hp, hpe, _⟩ := opt_spec γ P₀ r₀ αr αP v s
    obtain ⟨_, _, _, hmax⟩ := opt_spec γ P₀ r₀ αr αP w s
    rw [← hpe]
    exact (F_mono γ hγ0 P₀ hP₀ r₀ αr αP ϵ hasm hαP v w hvw s p hp).trans (hmax p hp)
  obtain ⟨vstar, hfix, huniq, hlim⟩ := banach_aux _ K hK0 hK1 hopt
  have hevfix : ∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
      ∃ x, evalOpR2 γ P₀ r₀ αr αP π x = x ∧ (∀ y, evalOpR2 γ P₀ r₀ αr αP π y = y → y = x) ∧
        ∀ y, Tendsto (fun n => (evalOpR2 γ P₀ r₀ αr αP π)^[n] y) atTop (𝓝 x) :=
    fun π hπ => banach_aux _ K hK0 hK1 (heval π hπ)
  refine ⟨vstar, hfix, huniq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro π hπ
    obtain ⟨x, hx, hu, _⟩ := hevfix π hπ
    exact ⟨x, hx, hu⟩
  · choose π hπ using fun s => opt_spec γ P₀ r₀ αr αP vstar s
    exact ⟨π, fun s => (hπ s).1, fun s => by
      rw [evalOpR2_eq]; exact (hπ s).2.1⟩
  · intro π hπ v hv
    have h1 : evalOpR2 γ P₀ r₀ αr αP π vstar = vstar := by
      funext s
      rw [hπ.2 s]; exact congrFun hfix s
    obtain ⟨x, _, hu, _⟩ := hevfix π hπ.1
    rw [hu v hv, hu vstar h1]
  · intro π hπ v hv
    have hle1 : v ≤ optOpR2 γ P₀ r₀ αr αP v := by
      intro s
      have := congrFun hv s
      rw [evalOpR2_eq] at this
      obtain ⟨_, _, _, hmax⟩ := opt_spec γ P₀ r₀ αr αP v s
      rw [← this]; exact hmax _ (hπ s)
    have hit : ∀ n, v ≤ (optOpR2 γ P₀ r₀ αr αP)^[n] v := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hle1.trans (hoptmono _ _ ih)
    intro s
    exact ge_of_tendsto' ((tendsto_pi_nhds.1 (hlim v)) s) (fun n => hit n s)
  · intro π hπ hall
    obtain ⟨x, hx, _, _⟩ := hevfix π hπ
    have hxv := hall x hx
    subst hxv
    refine ⟨hπ, fun s => ?_⟩
    rw [congrFun hx s]
    exact (congrFun hfix s).symm
  · intro hαr' π₁ π₂ h1 h2
    funext s
    exact F_unique γ hγ0 P₀ r₀ αr αP hαP vstar s (hαr' s) (π₁ s) (π₂ s) (h1.1 s) (h2.1 s)
      (h1.2 s) (h2.2 s)
end TwiceRegMDP.R2Bellman

open TwiceRegMDP.R2Bellman


theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαr : ∀ s, 0 ≤ αr s) (hαP : ∀ s, 0 ≤ αP s)
    (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ) :
    ∃ vstar : S → ℝ,
      optOpR2 γ P₀ r₀ αr αP vstar = vstar ∧
      (∀ v : S → ℝ, optOpR2 γ P₀ r₀ αr αP v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π → ∃! v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v) ∧
      (∃ π : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      (∀ πstar : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar πstar →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP πstar v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v ≤ vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        (∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v = vstar) →
        IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      ((∀ s, 0 < αr s) →
        ∀ π₁ π₂ : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π₁ →
          IsGreedy γ P₀ r₀ αr αP vstar π₂ → π₁ = π₂) := by
  exact r2_core γ hγ0 hγ1 P₀ hP₀ r₀ αr αP hαr hαP ϵ hasm
