-- Prove2me | solution 1 for SuttonBartoRL.PolicyGradient.grad_stateValue_unrolled
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:21:52.595669+00:00
-- url     : https://prove2.me/submissions/8f14f176-07bb-40c3-be7a-782fb5b46107

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

open Matrix Filter Topology

namespace PGCore

lemma summable_half_pow_div (m : ℕ) (hm : 0 < m) :
    Summable (fun n : ℕ => (1/2 : ℝ) ^ (n / m)) := by
  set r : ℝ := (1/2 : ℝ) ^ ((1 : ℝ) / m) with hr
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left 2)
  have key : r ^ n = (1/2 : ℝ) ^ ((n : ℝ) / m) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; field_simp
  rw [key]
  have hle : (n : ℝ) / m - 1 ≤ ((n / m : ℕ) : ℝ) := by
    have h1 : n < n / m * m + m := Nat.lt_div_mul_add hm
    have h2 : (n : ℝ) < ((n / m : ℕ) : ℝ) * m + m := by exact_mod_cast h1
    rw [sub_le_iff_le_add, div_le_iff₀ hmR]; nlinarith
  calc (1/2 : ℝ) ^ (n / m) = (1/2 : ℝ) ^ (((n / m : ℕ)) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ (1/2 : ℝ) ^ ((n : ℝ) / m - 1) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hle
    _ = 2 * (1/2 : ℝ) ^ ((n : ℝ) / m) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]; ring

lemma summable_pow_of_norm_pow_le {R : Type*} [NormedRing R] [CompleteSpace R] (x : R)
    (m : ℕ) (hm : 0 < m) (hxm : ‖x ^ m‖ ≤ 1/2) : Summable (fun n : ℕ => x ^ n) := by
  set C : ℝ := ∑ j ∈ Finset.range m, ‖x ^ j‖
  have hC : ∀ j < m, ‖x ^ j‖ ≤ C := fun j hj =>
    Finset.single_le_sum (f := fun j => ‖x ^ j‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 hj)
  have hb : ∀ q j, j < m → ‖x ^ (j + m * q)‖ ≤ (1/2 : ℝ) ^ q * C := by
    intro q j hj
    induction q with
    | zero => simpa using hC j hj
    | succ q ih =>
      have : x ^ (j + m * (q + 1)) = x ^ (j + m * q) * x ^ m := by
        rw [← pow_add]; ring_nf
      rw [this]
      calc ‖x ^ (j + m * q) * x ^ m‖ ≤ ‖x ^ (j + m * q)‖ * ‖x ^ m‖ := norm_mul_le _ _
        _ ≤ ((1/2 : ℝ) ^ q * C) * (1/2) :=
            mul_le_mul ih hxm (norm_nonneg _) (by positivity)
        _ = (1/2 : ℝ) ^ (q + 1) * C := by ring
  refine Summable.of_norm_bounded ((summable_half_pow_div m hm).mul_right C) (fun n => ?_)
  have := hb (n / m) (n % m) (Nat.mod_lt _ hm)
  rwa [Nat.mod_add_div] at this

lemma neumann {R : Type*} [NormedRing R] [CompleteSpace R] (x : R)
    (hs : Summable (fun n : ℕ => x ^ n)) :
    (1 - x) * (∑' n, x ^ n) = 1 ∧ (∑' n, x ^ n) * (1 - x) = 1 := by
  have h0 := hs.tsum_eq_zero_add
  have hl : ∑' n, x ^ (n + 1) = x * ∑' n, x ^ n := by
    rw [← hs.tsum_mul_left]; congr 1; funext n; rw [pow_succ']
  have hr : ∑' n, x ^ (n + 1) = (∑' n, x ^ n) * x := by
    rw [← hs.tsum_mul_right]; congr 1; funext n; rw [pow_succ]
  simp only [pow_zero] at h0
  constructor
  · rw [sub_mul, one_mul]; nth_rewrite 1 [h0]; rw [hl]; abel
  · rw [mul_sub, mul_one]; nth_rewrite 1 [h0]; rw [hr]; abel

section MDP
open SuttonBartoRL.PolicyGradient SuttonBartoRL.PolicyGradient.EpisodicMDP
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

instance instCompleteMat : CompleteSpace (Matrix S S ℝ) := FiniteDimensional.complete ℝ _

variable (M : EpisodicMDP S A) (π : ParamPolicy S A d)

lemma P_cont : Continuous (fun θ => M.policyTrans π θ) := by
  unfold policyTrans
  exact continuous_pi fun x => continuous_pi fun y => continuous_finsetSum _ fun a _ =>
    ((π.differentiable x a).continuous).mul continuous_const

lemma entry_summable {θ : EuclideanSpace ℝ (Fin d)} (hs : Summable (fun k : ℕ => M.policyTrans π θ ^ k))
    (i j : S) : Summable (fun k : ℕ => (M.policyTrans π θ ^ k) i j) :=
  Pi.summable.1 (Pi.summable.1 hs i) j

lemma tsum_entry {θ : EuclideanSpace ℝ (Fin d)} (hs : Summable (fun k : ℕ => M.policyTrans π θ ^ k))
    (i j : S) : (∑' k : ℕ, M.policyTrans π θ ^ k) i j = ∑' k : ℕ, (M.policyTrans π θ ^ k) i j := by
  have h1 : (∑' k : ℕ, M.policyTrans π θ ^ k) i = ∑' k : ℕ, (M.policyTrans π θ ^ k) i :=
    tsum_apply (f := fun k : ℕ => (M.policyTrans π θ ^ k : S → S → ℝ)) hs
  rw [h1]
  exact tsum_apply (Pi.summable.1 hs i)

lemma mulVec_summable {θ : EuclideanSpace ℝ (Fin d)} (hs : Summable (fun k : ℕ => M.policyTrans π θ ^ k))
    (v : S → ℝ) (i : S) : Summable (fun k : ℕ => ((M.policyTrans π θ ^ k) *ᵥ v) i) := by
  simp only [mulVec, dotProduct]
  exact summable_sum fun y _ => (entry_summable M π hs i y).mul_right _

lemma value_eq {θ : EuclideanSpace ℝ (Fin d)} (hs : Summable (fun k : ℕ => M.policyTrans π θ ^ k))
    (s : S) : M.stateValue π θ s =
      ∑ y, (∑' k : ℕ, M.policyTrans π θ ^ k) s y * M.policyReward π θ y := by
  unfold stateValue
  simp only [mulVec, dotProduct]
  rw [Summable.tsum_finsetSum (fun y _ => (entry_summable M π hs s y).mul_right _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tsum_entry M π hs, (entry_summable M π hs s y).tsum_mul_right]

lemma actionValue_eq {θ : EuclideanSpace ℝ (Fin d)} (hs : Summable (fun k : ℕ => M.policyTrans π θ ^ k))
    (x : S) (a : A) : M.actionValue π θ x a =
      M.expReward x a + ∑ z, M.trans x a z * M.stateValue π θ z := by
  unfold actionValue
  congr 1
  rw [Summable.tsum_finsetSum (fun z _ => (mulVec_summable M π hs _ z).mul_left _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [(mulVec_summable M π hs _ z).tsum_mul_left]; rfl

lemma eventually_summable {θ₀ : EuclideanSpace ℝ (Fin d)} (hT : M.Terminates π θ₀) :
    ∀ᶠ θ in 𝓝 θ₀, Summable (fun k : ℕ => M.policyTrans π θ ^ k) := by
  have hs0 : Summable (fun k : ℕ => M.policyTrans π θ₀ ^ k) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => hT i j
  have tend := hs0.tendsto_atTop_zero.norm
  rw [norm_zero] at tend
  obtain ⟨m, hm, hm1⟩ := ((tend.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)).and
    (eventually_ge_atTop 1)).exists
  have hc : Continuous (fun θ => ‖M.policyTrans π θ ^ m‖) := ((P_cont M π).pow m).norm
  filter_upwards [(hc.tendsto θ₀).eventually_lt_const hm] with θ hθ
  exact summable_pow_of_norm_pow_le _ m hm1 hθ.le

noncomputable def unitOf {θ : EuclideanSpace ℝ (Fin d)}
    (hs : Summable (fun k : ℕ => M.policyTrans π θ ^ k)) : (Matrix S S ℝ)ˣ :=
  ⟨1 - M.policyTrans π θ, ∑' k : ℕ, M.policyTrans π θ ^ k, (neumann _ hs).1, (neumann _ hs).2⟩

lemma inverse_eq {θ : EuclideanSpace ℝ (Fin d)}
    (hs : Summable (fun k : ℕ => M.policyTrans π θ ^ k)) :
    Ring.inverse (1 - M.policyTrans π θ) = ∑' k : ℕ, M.policyTrans π θ ^ k := by
  have : (1 - M.policyTrans π θ) = ((unitOf M π hs : (Matrix S S ℝ)ˣ) : Matrix S S ℝ) := rfl
  rw [this, Ring.inverse_unit]; rfl

noncomputable def dpi (θ₀ : EuclideanSpace ℝ (Fin d)) (x : S) (a : A) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fderiv ℝ (fun θ => π.prob θ x a) θ₀

lemma P_hasFDerivAt (θ₀ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun θ => M.policyTrans π θ)
      (∑ x, ∑ y, ∑ a, (M.trans x a y • dpi π θ₀ x a).smulRight (Matrix.single x y (1:ℝ))) θ₀ := by
  have eq : (fun θ => M.policyTrans π θ) = fun θ =>
      ∑ x, ∑ y, ∑ a, (π.prob θ x a * M.trans x a y) • Matrix.single x y (1:ℝ) := by
    funext θ; ext i j
    simp only [policyTrans, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]
  rw [eq]
  refine HasFDerivAt.fun_sum fun x _ => HasFDerivAt.fun_sum fun y _ => HasFDerivAt.fun_sum fun a _ => ?_
  have h1 := ((π.differentiable x a θ₀).hasFDerivAt).mul_const (M.trans x a y)
  exact h1.smul_const (Matrix.single x y (1:ℝ))

lemma r_hasFDerivAt (θ₀ : EuclideanSpace ℝ (Fin d)) (y : S) :
    HasFDerivAt (fun θ => M.policyReward π θ y) (∑ a, M.expReward y a • dpi π θ₀ y a) θ₀ := by
  unfold policyReward
  exact HasFDerivAt.fun_sum fun a _ => ((π.differentiable y a θ₀).hasFDerivAt).mul_const _

noncomputable def ent (i j : S) : Matrix S S ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => B i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

lemma ent_apply (i j : S) (B : Matrix S S ℝ) : ent i j B = B i j := rfl

omit [DecidableEq S] in
lemma alg (N : Matrix S S ℝ) (s : S) (r : S → ℝ) (ER : S → A → ℝ) (T : S → A → S → ℝ)
    (D : S → A → ℝ) :
    ∑ x, (N s x * ∑ a, ER x a * D x a + r x * ∑ i, ∑ z, N s i * (∑ a, T i a z * D i a) * N z x) =
    ∑ x, N s x * ∑ a, (ER x a + ∑ z, T x a z * ∑ y, N z y * r y) * D x a := by
  simp only [Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext z; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun z _ =>
    Finset.sum_congr rfl fun y _ => by ring

lemma P'_apply (θ₀ : EuclideanSpace ℝ (Fin d)) (h : EuclideanSpace ℝ (Fin d)) (i j : S) :
    (∑ x, ∑ y, ∑ a, (M.trans x a y • dpi π θ₀ x a).smulRight (Matrix.single x y (1:ℝ))) h i j =
      ∑ a, M.trans i a j * dpi π θ₀ i a h := by
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp [ite_and]

theorem unrolled (θ₀ : EuclideanSpace ℝ (Fin d)) (hT : M.Terminates π θ₀) (s : S) :
    HasGradientAt (fun θ => M.stateValue π θ s)
      (∑ x, (∑' k : ℕ, (M.policyTrans π θ₀ ^ k) s x) •
        ∑ a, M.actionValue π θ₀ x a • gradient (fun θ => π.prob θ x a) θ₀) θ₀ := by
  have hs0 : Summable (fun k : ℕ => M.policyTrans π θ₀ ^ k) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => hT i j
  set N := ∑' k : ℕ, M.policyTrans π θ₀ ^ k with hN
  have hInv := (hasFDerivAt_ringInverse (𝕜 := ℝ) (unitOf M π hs0)).comp θ₀
    ((P_hasFDerivAt M π θ₀).const_sub 1)
  have hF := HasFDerivAt.fun_sum (u := Finset.univ) fun y _ =>
    (((ent s y).hasFDerivAt.comp θ₀ hInv)).mul (r_hasFDerivAt M π θ₀ y)
  have hev : (fun θ => M.stateValue π θ s) =ᶠ[𝓝 θ₀]
      fun θ => ∑ y, ent s y (Ring.inverse (1 - M.policyTrans π θ)) * M.policyReward π θ y := by
    filter_upwards [eventually_summable M π hT] with θ hθ
    rw [value_eq M π hθ, inverse_eq M π hθ]; rfl
  have hf := hF.congr_of_eventuallyEq hev
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hf.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  have hinv0 : (((unitOf M π hs0)⁻¹ : (Matrix S S ℝ)ˣ) : Matrix S S ℝ) = N := rfl
  have hinv1 : Ring.inverse (1 - M.policyTrans π θ₀) = N := inverse_eq M π hs0
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, hinv0, hinv1, ent_apply,
    smul_eq_mul, InnerProductSpace.toDual_apply_apply, sum_inner, real_inner_smul_left]
  have key : ∀ y, (ent s y ∘SL (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ) N N)) ∘SL
      (-∑ x, ∑ y, ∑ a, (M.trans x a y • dpi π θ₀ x a).smulRight (Matrix.single x y (1:ℝ)))) h =
      ∑ i, ∑ z, N s i * (∑ a, M.trans i a z * dpi π θ₀ i a h) * N z y := by
    intro y
    show ent s y (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ) N N)
      (-((∑ x, ∑ y, ∑ a, (M.trans x a y • dpi π θ₀ x a).smulRight (Matrix.single x y (1:ℝ))) h))) = _
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, mul_neg,
      neg_mul, neg_neg, ent_apply, Matrix.mul_apply, P'_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hg : ∀ x a, inner ℝ (gradient (fun θ => π.prob θ x a) θ₀) h = dpi π θ₀ x a h :=
    fun x a => InnerProductSpace.toDual_symm_apply
  simp only [hg, actionValue_eq M π hs0, value_eq M π hs0, ← tsum_entry M π hs0, ← hN]
  refine (Finset.sum_congr rfl fun y _ => ?_).trans
    (alg N s (M.policyReward π θ₀) M.expReward M.trans (fun x a => dpi π θ₀ x a h))
  congr 1; congr 1; exact key y

theorem recursion (θ₀ : EuclideanSpace ℝ (Fin d)) (hT : M.Terminates π θ₀) (s : S) :
    HasGradientAt (fun θ => M.stateValue π θ s)
      (∑ a, (M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀ +
        π.prob θ₀ s a • ∑ s', M.trans s a s' • gradient (fun θ => M.stateValue π θ s') θ₀)) θ₀ := by
  have hs0 : Summable (fun k : ℕ => M.policyTrans π θ₀ ^ k) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => hT i j
  set N := ∑' k : ℕ, M.policyTrans π θ₀ ^ k with hN
  set w : S → EuclideanSpace ℝ (Fin d) := fun x =>
    ∑ a, M.actionValue π θ₀ x a • gradient (fun θ => π.prob θ x a) θ₀ with hw
  have hG : ∀ s', gradient (fun θ => M.stateValue π θ s') θ₀ = ∑ x, N s' x • w x := by
    intro s'
    rw [(unrolled M π θ₀ hT s').gradient]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hN, tsum_entry M π hs0]
  have hNe : N = 1 + M.policyTrans π θ₀ * N := by
    have h1 : (1 - M.policyTrans π θ₀) * N = 1 := (neumann _ hs0).1
    rw [sub_mul, one_mul] at h1
    calc N = (N - M.policyTrans π θ₀ * N) + M.policyTrans π θ₀ * N := by abel
      _ = 1 + M.policyTrans π θ₀ * N := by rw [h1]
  convert unrolled M π θ₀ hT s using 1
  have hR : (∑ x, (∑' k : ℕ, (M.policyTrans π θ₀ ^ k) s x) • w x) = ∑ x, N s x • w x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hN, tsum_entry M π hs0]
  rw [hR]
  simp only [hG]
  conv_rhs => arg 2; ext x; rw [hNe]
  simp only [Matrix.add_apply, Matrix.one_apply, add_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.mul_apply,
    policyTrans, Finset.sum_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc]

end MDP

end PGCore

open SuttonBartoRL.PolicyGradient in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ₀) (s : S) :
    HasGradientAt (fun θ => M.stateValue π θ s)
      (∑ x, (∑' k : ℕ, (M.policyTrans π θ₀ ^ k) s x) •
        ∑ a, M.actionValue π θ₀ x a • gradient (fun θ => π.prob θ x a) θ₀)
      θ₀ :=
  PGCore.unrolled M π θ₀ hT s
