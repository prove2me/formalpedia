-- Prove2me | solution 2 for SuttonBartoRL.LinearTD.td_fixed_point_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:34.782157+00:00
-- url     : https://prove2.me/submissions/1741ba5b-261a-427c-8cb3-7a7fd25c087e

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD
import Theorems.Thm_SuttonBartoRL_LinearTD_keyMatrix_posDef
import Theorems.Thm_SuttonBartoRL_LinearTD_tdA_eq_matrix_form

-- carved verbatim out of submission e1c22824-c51e-45c6-b40d-38d6165f1370, lines 310-408

section
open Matrix
set_option autoImplicit false

theorem TDFP_det {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (h : SuttonBartoRL.LinearTD.IsPosDefNonsym A) : IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have := h v hv
  rw [hAv, dotProduct_zero] at this
  exact lt_irrefl _ this

open SuttonBartoRL.LinearTD in
theorem TDFP_bellman {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (s : S) :
    M.stateValue γ π s = M.policyReward π s + γ * ∑ t, M.policyTrans π s t * M.stateValue γ π t := by
  set P := M.policyTrans π with hPdef
  set r := M.policyReward π with hrdef
  have hPnn : ∀ s s', 0 ≤ P s s' := fun s s' =>
    Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a)
      (Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r)
  have hProw : ∀ s, ∑ s', P s s' = 1 := by
    intro s
    simp only [hPdef, MDP.policyTrans, MDP.trans]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]
  have hmv : ∀ (x : S → ℝ) (s : S), (P *ᵥ x) s = ∑ t, P s t * x t := fun x s => rfl
  have hbd : ∀ k s, |(P ^ k *ᵥ r) s| ≤ ∑ t, |r t| := by
    intro k
    induction k with
    | zero =>
      intro s
      rw [pow_zero, one_mulVec]
      exact Finset.single_le_sum (f := fun t => |r t|) (fun t _ => abs_nonneg _)
        (Finset.mem_univ s)
    | succ k ih =>
      intro s
      rw [pow_succ', ← mulVec_mulVec, hmv]
      calc |∑ t, P s t * (P ^ k *ᵥ r) t| ≤ ∑ t, |P s t * (P ^ k *ᵥ r) t| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t, P s t * ∑ t, |r t| := by
            refine Finset.sum_le_sum fun t _ => ?_
            rw [abs_mul, abs_of_nonneg (hPnn s t)]
            exact mul_le_mul_of_nonneg_left (ih t) (hPnn s t)
        _ = ∑ t, |r t| := by rw [← Finset.sum_mul, hProw, one_mul]
  have hsum : ∀ t, Summable (fun k : ℕ => γ ^ k * (P ^ k *ᵥ r) t) := by
    intro t
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ t, |r t|)) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hγ0]
    exact mul_le_mul_of_nonneg_left (hbd k t) (pow_nonneg hγ0 k)
  have hv : ∀ t, M.stateValue γ π t = ∑' k : ℕ, γ ^ k * (P ^ k *ᵥ r) t := fun t => rfl
  have hstep : ∀ k : ℕ, γ ^ (k + 1) * (P ^ (k + 1) *ᵥ r) s
      = ∑ t, γ * (P s t * (γ ^ k * (P ^ k *ᵥ r) t)) := by
    intro k
    rw [pow_succ' P k, ← mulVec_mulVec, hmv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hv s, (hsum s).tsum_eq_zero_add, pow_zero, pow_zero, one_mul, one_mulVec,
    tsum_congr hstep,
    Summable.tsum_finsetSum (fun t _ => ((hsum t).mul_left (P s t)).mul_left γ)]
  simp only [tsum_mul_left]
  rw [Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
  rw [hv t]

open SuttonBartoRL.LinearTD in
theorem TDFP_tdB {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) :
    tdB M π μ X = Xᵀ *ᵥ (fun s => μ s * M.policyReward π s) := by
  funext i
  simp only [tdB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
    transpose_apply, MDP.policyReward, MDP.expReward]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 : ∀ a, ∑ s', ∑ r ∈ M.R, M.p s a s' r * r * X s i
      = X s i * ∑ r ∈ M.R, r * ∑ s', M.p s a s' r := by
    intro a
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by ring
  simp only [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

open SuttonBartoRL.LinearTD in
theorem TDFP_quad {S : Type} [Fintype S] [DecidableEq S] {d : ℕ} (X : Matrix S (Fin d) ℝ)
    (μ : S → ℝ) (P : Matrix S S ℝ) (γ : ℝ) (u w : Fin d → ℝ) :
    u ⬝ᵥ ((Xᵀ * diagonal μ * (1 - γ • P) * X) *ᵥ w)
      = ∑ s, μ s * (X *ᵥ u) s * ((X *ᵥ w) s - γ * (P *ᵥ (X *ᵥ w)) s) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    sub_mulVec, one_mulVec, smul_mulVec]
  simp only [dotProduct, mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

open Matrix SuttonBartoRL.LinearTD in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hμ : IsStationaryDist (M.policyTrans π) μ) (hμpos : ∀ s, 0 < μ s)
    (hX : LinearIndependent ℝ Xᵀ) :
    IsUnit (tdA M π μ X γ).det ∧
      tdB M π μ X = tdA M π μ X γ *ᵥ tdFixedPoint M π μ X γ ∧
      ∀ w : Fin d → ℝ,
        VE μ (M.stateValue γ π) X (tdFixedPoint M π μ X γ) ≤
          1 / (1 - γ) * VE μ (M.stateValue γ π) X w := by
  have hdet : IsUnit (tdA M π μ X γ).det :=
    TDFP_det _ (SuttonBartoRL.LinearTD.keyMatrix_posDef M π μ X γ hγ0 hγ1 hμ hμpos hX).2
  have hAw : tdA M π μ X γ *ᵥ tdFixedPoint M π μ X γ = tdB M π μ X := by
    rw [tdFixedPoint, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  refine ⟨hdet, hAw.symm, fun w => ?_⟩
  set P := M.policyTrans π with hPdef
  set r := M.policyReward π with hrdef
  set v := M.stateValue γ π with hvdef
  set wT := tdFixedPoint M π μ X γ with hwTdef
  have hPnn : ∀ s s', 0 ≤ P s s' := fun s s' =>
    Finset.sum_nonneg fun a _ => mul_nonneg (π.nonneg s a)
      (Finset.sum_nonneg fun r _ => M.p_nonneg s a s' r)
  have hProw : ∀ s, ∑ s', P s s' = 1 := by
    intro s
    simp only [hPdef, MDP.policyTrans, MDP.trans]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]
  have hmv : ∀ (x : S → ℝ) (s : S), (P *ᵥ x) s = ∑ t, P s t * x t := fun x s => rfl
  have hstat : ∀ t, ∑ s, μ s * P s t = μ t := fun t => congrFun hμ.2.2 t
  have hvhat : ∀ (w : Fin d → ℝ) s, vhat X w s = (X *ᵥ w) s := by
    intro w s; simp only [vhat, mulVec, dotProduct_comm]
  set y := X *ᵥ wT with hydef
  set e : S → ℝ := v - y with hedef
  set q := P *ᵥ e with hqdef
  -- orthogonality
  have hOrth : ∀ u : Fin d → ℝ, ∑ s, μ s * (X *ᵥ u) s * (e s - γ * q s) = 0 := by
    intro u
    have h1 : u ⬝ᵥ (tdA M π μ X γ *ᵥ wT) = u ⬝ᵥ tdB M π μ X := by rw [hAw]
    rw [SuttonBartoRL.LinearTD.tdA_eq_matrix_form, TDFP_quad, TDFP_tdB, dotProduct_mulVec, vecMul_transpose] at h1
    have hq : ∀ s, q s = (P *ᵥ v) s - (P *ᵥ y) s := by
      intro s; rw [hqdef, hedef, mulVec_sub, Pi.sub_apply]
    have hB : ∀ s, v s = r s + γ * (P *ᵥ v) s := fun s => by
      rw [hmv]; exact TDFP_bellman M π γ hγ0 hγ1 s
    have h2 : ∀ s, μ s * (X *ᵥ u) s * (e s - γ * q s)
        = (X *ᵥ u) s * (μ s * r s) - μ s * (X *ᵥ u) s * (y s - γ * (P *ᵥ y) s) := by
      intro s
      rw [hq s, hedef, Pi.sub_apply, hB s]
      ring
    rw [Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_sub_distrib]
    rw [h1]
    simp only [dotProduct]
    ring
  -- non-expansiveness
  have hJ : ∀ s, q s ^ 2 ≤ ∑ t, P s t * e t ^ 2 := by
    intro s
    have h0 : 0 ≤ ∑ t, P s t * (e t - q s) ^ 2 :=
      Finset.sum_nonneg fun t _ => mul_nonneg (hPnn s t) (sq_nonneg _)
    have hexp : ∑ t, P s t * (e t - q s) ^ 2
        = ∑ t, P s t * e t ^ 2 - 2 * q s * ∑ t, P s t * e t + q s ^ 2 * ∑ t, P s t := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    have hq : q s = ∑ t, P s t * e t := hmv e s
    rw [hProw, ← hq] at hexp
    nlinarith
  have hNE : ∑ s, μ s * q s ^ 2 ≤ ∑ s, μ s * e s ^ 2 := by
    calc ∑ s, μ s * q s ^ 2 ≤ ∑ s, μ s * ∑ t, P s t * e t ^ 2 :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hJ s) (hμpos s).le
      _ = ∑ t, (∑ s, μ s * P s t) * e t ^ 2 := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
      _ = ∑ s, μ s * e s ^ 2 := by simp only [hstat]
  -- decomposition
  set z := X *ᵥ (w - wT) with hzdef
  have hf : ∀ s, v s - vhat X w s = e s - z s := by
    intro s
    rw [hvhat, hzdef, mulVec_sub, hedef, hydef]
    simp only [Pi.sub_apply]
    ring
  have hE : VE μ v X wT = ∑ s, μ s * e s ^ 2 := by
    simp only [VE, hvhat, hedef, hydef, Pi.sub_apply]
  have hF : VE μ v X w = ∑ s, μ s * e s ^ 2 + ∑ s, μ s * (z s - γ * q s) ^ 2
      - γ ^ 2 * ∑ s, μ s * q s ^ 2 - 2 * ∑ s, μ s * z s * (e s - γ * q s) := by
    simp only [VE, hf]
    have hid : ∀ s, μ s * (e s - z s) ^ 2 = μ s * e s ^ 2 + μ s * (z s - γ * q s) ^ 2
        - γ ^ 2 * (μ s * q s ^ 2) - 2 * (μ s * z s * (e s - γ * q s)) := fun s => by ring
    rw [Finset.sum_congr rfl fun s _ => hid s, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hO := hOrth (w - wT)
  rw [← hzdef] at hO
  rw [hO, mul_zero, sub_zero] at hF
  have hZ : 0 ≤ ∑ s, μ s * (z s - γ * q s) ^ 2 :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hμpos s).le (sq_nonneg _)
  have hE0 : 0 ≤ ∑ s, μ s * e s ^ 2 :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hμpos s).le (sq_nonneg _)
  rw [hE, hF, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hNE (sq_nonneg γ),
    mul_nonneg (mul_nonneg hγ0 hE0) (by linarith : (0:ℝ) ≤ 1 - γ)]

end
