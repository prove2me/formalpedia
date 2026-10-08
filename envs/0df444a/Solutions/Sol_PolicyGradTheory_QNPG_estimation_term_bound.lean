-- Prove2me | solution 1 for PolicyGradTheory.QNPG.estimation_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:40:42.200975+00:00
-- url     : https://prove2.me/submissions/2e180d70-2be4-460f-a6af-9e6e9108a7c2

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

set_option autoImplicit false

open FoundationsML.ReinforcementLearning in
theorem q84_M_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s s' : S) : 0 ≤ InducedTransition π P s s' := by
  unfold InducedTransition
  exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))

open FoundationsML.ReinforcementLearning in
theorem q84_M_sum {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s : S) : ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  have h1 : ∀ a, ∑ s', P s a s' = 1 := fun a => (hP s a).2
  simp_rw [← Finset.mul_sum, h1, mul_one]
  exact (hπ s).2

open FoundationsML.ReinforcementLearning in
theorem q84_D_prob {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · show 0 ≤ (if s = s0 then (1:ℝ) else 0)
      split_ifs <;> norm_num
    · show ∑ s, (if s = s0 then (1:ℝ) else 0) = 1
      simp
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · show 0 ≤ ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s'
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (q84_M_nonneg π hπ P hP s s'))
    · show ∑ s', ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, q84_M_sum π hπ P hP, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem q84_vis {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) :
    (∀ s, 0 ≤ PolicyGradTheory.ProjGA.visitation π P γ ρ s) ∧
      ∑ s, PolicyGradTheory.ProjGA.visitation π P γ ρ s = 1 := by
  have hterm_nn : ∀ s t, 0 ≤ γ ^ t * ∑ s₀, ρ s₀ * OccupationDist π P s₀ t s := fun s t =>
    mul_nonneg (pow_nonneg hγ0 t) (Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (hρ.1 s₀) ((q84_D_prob π hπ P hP s₀ t).1 s))
  have hsumS : ∀ t, ∑ s, γ ^ t * ∑ s₀, ρ s₀ * OccupationDist π P s₀ t s = γ ^ t := by
    intro t
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, fun s₀ => (q84_D_prob π hπ P hP s₀ t).2, mul_one, hρ.2, mul_one]
  have hsumm : ∀ s, Summable (fun t => γ ^ t * ∑ s₀, ρ s₀ * OccupationDist π P s₀ t s) := by
    intro s
    refine Summable.of_nonneg_of_le (hterm_nn s) (fun t => ?_)
      (summable_geometric_of_lt_one hγ0 hγ1)
    exact (Finset.single_le_sum (f := fun s => γ ^ t * ∑ s₀, ρ s₀ * OccupationDist π P s₀ t s)
      (fun i _ => hterm_nn i t) (Finset.mem_univ s)).trans_eq (hsumS t)
  refine ⟨fun s => mul_nonneg (by linarith) (tsum_nonneg (hterm_nn s)), ?_⟩
  unfold PolicyGradTheory.ProjGA.visitation
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun s _ => hsumm s)]
  simp_rw [hsumS]
  rw [tsum_geometric_of_lt_one hγ0 hγ1]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp

theorem q84_cs {S A : Type} [Fintype S] [Fintype A]
    (w g : S → A → ℝ) (Q : ℝ) (hw : ∀ s a, 0 ≤ w s a)
    (hw1 : ∑ s, ∑ a, w s a ≤ 1) (hQ : ∑ s, ∑ a, w s a * g s a ^ 2 ≤ Q) :
    ∑ s, ∑ a, w s a * g s a ≤ Real.sqrt Q := by
  set X := ∑ s, ∑ a, w s a * g s a with hX
  by_cases hX0 : X ≤ 0
  · exact le_trans hX0 (Real.sqrt_nonneg _)
  push Not at hX0
  rw [Real.le_sqrt hX0.le (le_trans (Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ =>
    mul_nonneg (hw s a) (sq_nonneg _)) hQ)]
  have h : ∀ s a, 2 * X * (w s a * g s a) ≤ w s a * g s a ^ 2 + X ^ 2 * w s a := fun s a => by
    nlinarith [mul_nonneg (hw s a) (sq_nonneg (g s a - X))]
  have hs : ∑ s, ∑ a, 2 * X * (w s a * g s a) ≤
      ∑ s, ∑ a, (w s a * g s a ^ 2 + X ^ 2 * w s a) :=
    Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => h s a
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  rw [← hX] at hs
  nlinarith [sq_nonneg X]

open SuttonBartoRL.PolicyGradient in
theorem q84_grad {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (x : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    HasGradientAt (fun θ' => Real.log (softmaxPolicy (linearPref x) θ' s a))
      (x s a - ∑ b, softmaxPolicy (linearPref x) θ s b • x s b) θ := by
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun θ' => ∑ b, Real.exp (inner ℝ θ' (x s b)) with hG
  have hGpos : ∀ θ', 0 < G θ' := fun θ' =>
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hfun : (fun θ' => Real.log (softmaxPolicy (linearPref x) θ' s a)) =
      fun θ' => inner ℝ θ' (x s a) - Real.log (G θ') := by
    funext θ'
    simp only [softmaxPolicy, linearPref]
    rw [Real.log_div (Real.exp_pos _).ne' (hGpos θ').ne', Real.log_exp]
  have hlin : ∀ v : EuclideanSpace ℝ (Fin d),
      HasFDerivAt (fun θ' : EuclideanSpace ℝ (Fin d) => inner ℝ θ' v) (innerSL ℝ v) θ := by
    intro v
    have := (innerSL ℝ v).hasFDerivAt (x := θ)
    convert this using 1
    funext θ'
    simp [real_inner_comm]
  have hGd : HasFDerivAt G (∑ b, Real.exp (inner ℝ θ (x s b)) • innerSL ℝ (x s b)) θ :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hlin (x s b)).exp)
  have hL := (hlin (x s a)).sub (hGd.log (hGpos θ).ne')
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hL.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
  · simpa using congrFun hfun y
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, inner_sub_left, sum_inner, real_inner_smul_left,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    innerSL_apply_apply, smul_eq_mul, softmaxPolicy, linearPref, Finset.mul_sum, hG]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

open PolicyGradTheory.QNPG FoundationsML.ReinforcementLearning in
theorem q84_policy {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) :
    IsPolicy (logLinearPolicy φ θ) := by
  intro s
  have hpos : 0 < ∑ b, Real.exp (inner ℝ θ (φ s b)) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  refine ⟨fun a => ?_, ?_⟩
  · unfold logLinearPolicy SuttonBartoRL.PolicyGradient.softmaxPolicy
      SuttonBartoRL.PolicyGradient.linearPref
    exact div_nonneg (Real.exp_pos _).le hpos.le
  · unfold logLinearPolicy SuttonBartoRL.PolicyGradient.softmaxPolicy
      SuttonBartoRL.PolicyGradient.linearPref
    rw [← Finset.sum_div, div_self hpos.ne']

-- First-order optimality on the ball: excess loss dominates the on-measure quadratic form.
open PolicyGradTheory.QNPG in
theorem q84_excess {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (μ : S × A → ℝ)
    (W : ℝ) (θ wstar w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ W)
    (hmin : ‖wstar‖ ≤ W ∧ ∀ v, ‖v‖ ≤ W → qLoss P r γ φ wstar θ μ ≤ qLoss P r γ φ v θ μ) :
    quadForm φ μ (wstar - w) ≤ qLoss P r γ φ w θ μ - qLoss P r γ φ wstar θ μ := by
  set Qf := FoundationsML.ReinforcementLearning.QFunction (logLinearPolicy φ θ) P r γ
  set e : S → A → ℝ := fun s a => Qf s a - inner ℝ wstar (φ s a) with he
  set δ : S → A → ℝ := fun s a => inner ℝ (w - wstar) (φ s a) with hδ
  set G := ∑ s, ∑ a, μ (s, a) * (e s a * δ s a) with hG
  set q := ∑ s, ∑ a, μ (s, a) * δ s a ^ 2 with hq
  have hL : ∀ t : ℝ, qLoss P r γ φ (wstar + t • (w - wstar)) θ μ =
      qLoss P r γ φ wstar θ μ - 2 * t * G + t ^ 2 * q := by
    intro t
    have hterm : ∀ s a, μ (s, a) * (Qf s a - inner ℝ (wstar + t • (w - wstar)) (φ s a)) ^ 2 =
        μ (s, a) * (Qf s a - inner ℝ wstar (φ s a)) ^ 2 - 2 * t * (μ (s, a) * (e s a * δ s a))
          + t ^ 2 * (μ (s, a) * δ s a ^ 2) := by
      intro s a
      simp only [he, hδ, inner_add_left, real_inner_smul_left]
      ring
    show ∑ s, ∑ a, μ (s, a) * (Qf s a - inner ℝ (wstar + t • (w - wstar)) (φ s a)) ^ 2 =
      ∑ s, ∑ a, μ (s, a) * (Qf s a - inner ℝ wstar (φ s a)) ^ 2 - 2 * t * G + t ^ 2 * q
    simp_rw [hterm]
    simp only [hG, hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hball : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖wstar + t • (w - wstar)‖ ≤ W := by
    intro t h0 h1
    have : wstar + t • (w - wstar) = (1 - t) • wstar + t • w := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    calc ‖(1 - t) • wstar + t • w‖ ≤ ‖(1 - t) • wstar‖ + ‖t • w‖ := norm_add_le _ _
      _ = (1 - t) * ‖wstar‖ + t * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
      _ ≤ (1 - t) * W + t * W :=
          add_le_add (mul_le_mul_of_nonneg_left hmin.1 (by linarith)) (mul_le_mul_of_nonneg_left hw h0)
      _ = W := by ring
  have hopt : ∀ t : ℝ, 0 < t → t ≤ 1 → 2 * G ≤ t * q := by
    intro t h0 h1
    have := hmin.2 _ (hball t h0.le h1)
    rw [hL t] at this
    have h2 : t * (2 * G) ≤ t * (t * q) := by nlinarith
    exact le_of_mul_le_mul_left h2 h0
  have hGle : G ≤ 0 := by
    by_contra hpos
    push Not at hpos
    by_cases hq0 : q ≤ 0
    · have := hopt 1 one_pos le_rfl; linarith
    push Not at hq0
    set t := min 1 (G / q)
    have ht0 : 0 < t := lt_min one_pos (div_pos hpos hq0)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htq : t * q ≤ G := by
      calc t * q ≤ (G / q) * q := mul_le_mul_of_nonneg_right (min_le_right _ _) hq0.le
        _ = G := div_mul_cancel₀ G hq0.ne'
    have := hopt t ht0 ht1
    linarith
  have h1 := hL 1
  simp only [one_smul, add_sub_cancel] at h1
  have hquad : quadForm φ μ (wstar - w) = q := by
    unfold quadForm
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [hδ]
    rw [show wstar - w = -(w - wstar) by abel, inner_neg_left]
    ring
  rw [hquad, h1]
  linarith

open PolicyGradTheory.QNPG FoundationsML.ReinforcementLearning in
theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (ν : S × A → ℝ) (hν : PolicyGradTheory.ProjGA.IsDist ν)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (κ : ℝ) (hκnonneg : 0 ≤ κ)
    (hκ : ∀ v, quadForm φ (dstar P γ ρ πstar) v ≤ κ * quadForm φ ν v)
    (W : ℝ) (θ wstar w : EuclideanSpace ℝ (Fin d))
    (hw : ‖w‖ ≤ W)
    (hmin : ‖wstar‖ ≤ W ∧
      ∀ v, ‖v‖ ≤ W →
        qLoss P r γ φ wstar θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν) ≤
          qLoss P r γ φ v θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν)) :
    (∑ s : S, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s *
      ∑ a : A, πstar s a *
        inner ℝ (wstar - w)
          (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ)) ≤
      2 * Real.sqrt (((Fintype.card A : ℝ) * κ / (1 - γ)) *
        (qLoss P r γ φ w θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν) -
          qLoss P r γ φ wstar θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν))) := by
  obtain ⟨hP, -, hγ0, hγ1⟩ := hM
  have h1γ : 0 < 1 - γ := by linarith
  set μ := onPolicyMeasure (logLinearPolicy φ θ) P γ ν with hμ
  set πθ := logLinearPolicy φ θ with hπθ
  set v := PolicyGradTheory.ProjGA.visitation πstar P γ ρ with hv
  set u := wstar - w with hu
  set g : S → A → ℝ := fun s a => inner ℝ u (φ s a) with hg
  have hπθ_pol : IsPolicy πθ := q84_policy φ θ
  obtain ⟨hv0, hv1⟩ := q84_vis πstar hπstar P hP γ hγ0 hγ1 ρ hρ
  -- the gradient
  have hgrad : ∀ s a, gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ =
      φ s a - ∑ b, πθ s b • φ s b := fun s a => (q84_grad φ θ s a).gradient
  -- rewrite LHS
  have hLHS : (∑ s : S, v s * ∑ a : A, πstar s a *
        inner ℝ (wstar - w) (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ)) =
      (∑ s, ∑ a, (v s * πstar s a) * g s a) + ∑ s, ∑ a, (v s * πθ s a) * (-g s a) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [hgrad, inner_sub_right, inner_sum, real_inner_smul_right]
    have hsum1 := (hπstar s).2
    simp only [hg, ← hu, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul,
      mul_neg, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  -- the comparator quadratic form
  set Qd := quadForm φ (dstar P γ ρ πstar) u with hQd
  have hQd_eq : ∑ s, ∑ a, v s * g s a ^ 2 = (Fintype.card A : ℝ) * Qd := by
    have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [hQd, quadForm, dstar, Finset.mul_sum, hg]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
    field_simp
    rw [hv]; ring
  have hbound : ∀ π' : S → A → ℝ, IsPolicy π' → ∀ g' : S → A → ℝ, (∀ s a, g' s a ^ 2 = g s a ^ 2) →
      ∑ s, ∑ a, (v s * π' s a) * g' s a ≤ Real.sqrt ((Fintype.card A : ℝ) * Qd) := by
    intro π' hπ' g' hg'
    apply q84_cs
    · exact fun s a => mul_nonneg (hv0 s) ((hπ' s).1 a)
    · simp only [← Finset.mul_sum, (hπ' _).2, mul_one]
      exact hv1.le
    · rw [← hQd_eq]
      refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => ?_
      rw [hg' s a, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hv0 s)
      have hle : π' s a ≤ 1 := by
        rw [← (hπ' s).2]
        exact Finset.single_le_sum (fun i _ => (hπ' s).1 i) (Finset.mem_univ a)
      nlinarith [sq_nonneg (g s a), (hπ' s).1 a]
  have hT1 := hbound πstar hπstar g (fun _ _ => rfl)
  have hT2 := hbound πθ hπθ_pol (fun s a => -g s a) (fun _ _ => by ring)
  rw [hLHS]
  -- chain of quadratic-form comparisons
  have hμν : (1 - γ) * quadForm φ ν u ≤ quadForm φ μ u := by
    unfold quadForm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    show (1 - γ) * ν (s, a) ≤ saVisitation πθ P γ ν s a
    unfold saVisitation
    refine mul_le_mul_of_nonneg_left ?_ h1γ.le
    have : 0 ≤ ∑' t : ℕ, γ ^ (t + 1) *
        ∑ s₀ : S, ∑ a₀ : A, ν (s₀, a₀) *
          ∑ s₁ : S, P s₀ a₀ s₁ * OccupationDist πθ P s₁ t s * πθ s a := by
      refine tsum_nonneg fun t => mul_nonneg (pow_nonneg hγ0 _) ?_
      refine Finset.sum_nonneg fun s₀ _ => Finset.sum_nonneg fun a₀ _ =>
        mul_nonneg (hν.1 _) (Finset.sum_nonneg fun s₁ _ => ?_)
      exact mul_nonneg (mul_nonneg ((hP s₀ a₀).1 s₁)
        ((q84_D_prob πθ hπθ_pol P hP s₁ t).1 s)) ((hπθ_pol s).1 a)
    linarith
  have hex := q84_excess P r γ φ μ W θ wstar w hw hmin
  have hchain : (Fintype.card A : ℝ) * Qd ≤ ((Fintype.card A : ℝ) * κ / (1 - γ)) *
      (qLoss P r γ φ w θ μ - qLoss P r γ φ wstar θ μ) := by
    have hA : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
    have h1 : Qd ≤ κ * quadForm φ ν u := hκ u
    have h2 : quadForm φ ν u ≤ quadForm φ μ u / (1 - γ) := by
      rw [le_div_iff₀ h1γ]; linarith
    have h3 : quadForm φ μ u / (1 - γ) ≤
        (qLoss P r γ φ w θ μ - qLoss P r γ φ wstar θ μ) / (1 - γ) :=
      div_le_div_of_nonneg_right hex h1γ.le
    calc (Fintype.card A : ℝ) * Qd ≤ (Fintype.card A : ℝ) * (κ * quadForm φ ν u) :=
          mul_le_mul_of_nonneg_left h1 hA
      _ ≤ (Fintype.card A : ℝ) * (κ * ((qLoss P r γ φ w θ μ - qLoss P r γ φ wstar θ μ) / (1 - γ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h2.trans h3) hκnonneg) hA
      _ = _ := by ring
  have hsq := Real.sqrt_le_sqrt hchain
  linarith
