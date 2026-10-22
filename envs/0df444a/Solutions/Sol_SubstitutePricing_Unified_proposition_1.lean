-- Prove2me | solution 1 for SubstitutePricing.Unified.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T22:14:02.443329+00:00
-- url     : https://prove2.me/submissions/23865142-075e-48e8-9a97-eb28586ec7d1

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

set_option autoImplicit false

namespace SPU13
open SubstitutePricing.Unified

variable (M : Model)

lemma den_pos (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : 0 < M.den x r := by
  unfold Model.den
  have h1 := Real.exp_pos (M.u0 / M.μ)
  have h2 : 0 ≤ ∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ) :=
    Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  linarith

lemma P_of_mem {x : Fin M.n → ℕ} (r : Fin M.n → ℝ) {i : Fin M.n} (hi : i ∈ M.S x) :
    M.P x r i = Real.exp ((M.a i - r i) / M.μ) / M.den x r := by
  simp [Model.P, hi]

lemma sumP_add_P0 (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    (∑ i ∈ M.S x, M.P x r i) + M.P0 x r = 1 := by
  have hd := den_pos M x r
  rw [Finset.sum_congr rfl (fun i hi => P_of_mem M r hi), ← Finset.sum_div, Model.P0,
    ← add_div, div_eq_one_iff_eq hd.ne']
  rfl

lemma obj_eq (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.obj V x r = V x + M.lam * ∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i))) := by
  have h := sumP_add_P0 M x r
  unfold Model.obj
  have e1 : ∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i))) =
      (∑ i ∈ M.S x, r i * M.P x r i) + (∑ i ∈ M.S x, M.P x r i * V (M.sell x i))
        - (∑ i ∈ M.S x, M.P x r i) * V x := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1]
  have h0 : M.P0 x r = 1 - ∑ i ∈ M.S x, M.P x r i := by linarith
  rw [h0]; ring

lemma E_split (r : ℝ) (i : Fin M.n) :
    Real.exp ((M.a i - r) / M.μ) = Real.exp (M.a i / M.μ) * Real.exp (-r / M.μ) := by
  rw [← Real.exp_add]; congr 1; ring

lemma sumE (x : Fin M.n → ℕ) (r : ℝ) :
    ∑ i ∈ M.S x, Real.exp ((M.a i - r) / M.μ) = Real.exp (-r / M.μ) * M.wsum x := by
  simp_rw [E_split]
  rw [← Finset.sum_mul, Model.wsum]; ring

lemma sumEδ (x : Fin M.n → ℕ) (hW : M.wsum x ≠ 0) (r : ℝ) (δ : Fin M.n → ℝ) :
    ∑ i ∈ M.S x, Real.exp ((M.a i - r) / M.μ) * (r - δ i)
      = Real.exp (-r / M.μ) * M.wsum x * (r - M.wavg x δ) := by
  simp_rw [E_split]
  have e : ∑ i ∈ M.S x, Real.exp (M.a i / M.μ) * Real.exp (-r / M.μ) * (r - δ i)
      = Real.exp (-r / M.μ) * (r * M.wsum x - ∑ i ∈ M.S x, Real.exp (M.a i / M.μ) * δ i) := by
    rw [Model.wsum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e, Model.wavg]
  field_simp

lemma den_const (x : Fin M.n → ℕ) (r : ℝ) :
    M.den x (M.const r) = Real.exp (-r / M.μ) * M.wsum x + Real.exp (M.u0 / M.μ) := by
  show (∑ j ∈ M.S x, Real.exp ((M.a j - r) / M.μ)) + Real.exp (M.u0 / M.μ) = _
  rw [sumE]

lemma objU_closed (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (hW : M.wsum x ≠ 0) (r : ℝ) :
    M.objU V x r = V x + M.lam *
      (Real.exp (-r / M.μ) * M.wsum x * (r - M.wavg x (fun i => V x - V (M.sell x i)))
        / (Real.exp (-r / M.μ) * M.wsum x + Real.exp (M.u0 / M.μ))) := by
  rw [Model.objU, obj_eq]
  congr 2
  rw [Finset.sum_congr rfl (fun i hi => by rw [P_of_mem M _ hi])]
  rw [← den_const, ← sumEδ M x hW r (fun i => V x - V (M.sell x i)), Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Model.const]; ring)

lemma conv (hM : M.Assumptions) (x : Fin M.n → ℕ) (hW : 0 < M.wsum x) (d m : ℝ)
    (hm : M.marginLHS m = Real.exp ((M.aW x - d) / M.μ)) :
    (m - M.μ) * Real.exp (M.u0 / M.μ) = M.μ * M.wsum x * Real.exp (-(d + m) / M.μ) := by
  have hμ := hM.mu_pos
  have h1 : Real.exp ((m + M.u0) / M.μ) = Real.exp (m / M.μ) * Real.exp (M.u0 / M.μ) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp ((M.aW x - d) / M.μ) = M.wsum x * Real.exp (-d / M.μ) := by
    rw [show (M.aW x - d) / M.μ = Real.log (M.wsum x) + -d / M.μ by
      rw [Model.aW]; field_simp; ring, Real.exp_add, Real.exp_log hW]
  have h3 : Real.exp (-(d + m) / M.μ) = Real.exp (-d / M.μ) * Real.exp (-m / M.μ) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (m / M.μ) * Real.exp (-m / M.μ) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  unfold Model.marginLHS at hm
  rw [h1, h2] at hm
  rw [h3]
  calc (m - M.μ) * Real.exp (M.u0 / M.μ)
      = M.μ * (m / M.μ - 1) * Real.exp (M.u0 / M.μ) * (Real.exp (m / M.μ) * Real.exp (-m / M.μ)) := by
        rw [h4]; field_simp
    _ = M.μ * ((m / M.μ - 1) * (Real.exp (m / M.μ) * Real.exp (M.u0 / M.μ))) * Real.exp (-m / M.μ) := by
        ring
    _ = M.μ * M.wsum x * (Real.exp (-d / M.μ) * Real.exp (-m / M.μ)) := by rw [hm]; ring

lemma key_scalar {μ W U d m : ℝ} (hμ : 0 < μ) (hW : 0 < W) (hU : 0 < U)
    (hrel : (m - μ) * U = μ * W * Real.exp (-(d + m) / μ)) (r : ℝ) :
    Real.exp (-r / μ) * W * (r - d) / (Real.exp (-r / μ) * W + U) ≤ m - μ := by
  have he := Real.exp_pos (-r / μ)
  have heW : 0 < Real.exp (-r / μ) * W := mul_pos he hW
  have hz : Real.exp (-(d + m) / μ) = Real.exp (-r / μ) * Real.exp ((r - d - m) / μ) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hz1 := Real.add_one_le_exp ((r - d - m) / μ)
  rw [div_le_iff₀ (by positivity)]
  calc Real.exp (-r / μ) * W * (r - d)
      = (m - μ) * (Real.exp (-r / μ) * W) + μ * (Real.exp (-r / μ) * W) * ((r - d - m) / μ + 1) := by
        field_simp; ring
    _ ≤ (m - μ) * (Real.exp (-r / μ) * W) + μ * (Real.exp (-r / μ) * W) * Real.exp ((r - d - m) / μ) := by
        gcongr
    _ = (m - μ) * (Real.exp (-r / μ) * W + U) := by
        rw [mul_add (m - μ), hrel, hz]; ring

lemma key_scalar_eq {μ W U d m : ℝ} (hμ : 0 < μ) (hW : 0 < W) (hU : 0 < U)
    (hrel : (m - μ) * U = μ * W * Real.exp (-(d + m) / μ)) :
    Real.exp (-(d + m) / μ) * W * ((d + m) - d) / (Real.exp (-(d + m) / μ) * W + U) = m - μ ∧
    m * (U / (Real.exp (-(d + m) / μ) * W + U)) = μ := by
  have he := Real.exp_pos (-(d + m) / μ)
  have hD : 0 < Real.exp (-(d + m) / μ) * W + U := by positivity
  constructor
  · rw [div_eq_iff hD.ne']; linear_combination (-1 : ℝ) * hrel
  · rw [mul_div_assoc', div_eq_iff hD.ne']; linear_combination hrel

lemma root_ge (hM : M.Assumptions) {m σ : ℝ} (hσ : 0 ≤ σ) (h : M.marginLHS m = σ) :
    M.μ ≤ m := by
  have hμ := hM.mu_pos
  by_contra hlt
  push Not at hlt
  have h1 : m / M.μ - 1 < 0 := by
    rw [sub_neg, div_lt_one hμ]; exact hlt
  have h2 := mul_neg_of_neg_of_pos h1 (Real.exp_pos ((m + M.u0) / M.μ))
  unfold Model.marginLHS at h
  linarith

lemma root_exists (hM : M.Assumptions) {σ : ℝ} (hσ : 0 ≤ σ) : ∃ m, M.marginLHS m = σ := by
  have hμ := hM.mu_pos
  have hc0 : 0 ≤ M.μ * σ * Real.exp (-(M.u0 / M.μ)) :=
    mul_nonneg (mul_nonneg hμ.le hσ) (Real.exp_pos _).le
  have hK : M.μ ≤ M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ)) := by linarith
  have hf : M.marginLHS = fun m => (m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ) := rfl
  have hcont : ContinuousOn M.marginLHS
      (Set.Icc M.μ (M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ)))) := by
    rw [hf]; exact (by fun_prop : Continuous _).continuousOn
  have h0 : M.marginLHS M.μ = 0 := by simp [Model.marginLHS, div_self hμ.ne']
  have hKv : σ ≤ M.marginLHS (M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ))) := by
    unfold Model.marginLHS
    have e : (M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ))) / M.μ - 1
        = σ * Real.exp (-(M.u0 / M.μ)) := by field_simp; ring
    rw [e]
    have hle : Real.exp (M.u0 / M.μ)
        ≤ Real.exp ((M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ)) + M.u0) / M.μ) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff_of_pos_right hμ]; linarith
    have hinv : Real.exp (-(M.u0 / M.μ)) * Real.exp (M.u0 / M.μ) = 1 := by
      rw [← Real.exp_add]; simp
    have hp : 0 ≤ σ * Real.exp (-(M.u0 / M.μ)) := mul_nonneg hσ (Real.exp_pos _).le
    calc σ = σ * Real.exp (-(M.u0 / M.μ)) * Real.exp (M.u0 / M.μ) := by
          rw [mul_assoc, hinv, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hp
  obtain ⟨m, _, hm⟩ := intermediate_value_Icc hK hcont ⟨by rw [h0]; exact hσ, hKv⟩
  exact ⟨m, hm⟩

lemma wsum_pos (x : Fin M.n → ℕ) (hS : (M.S x).Nonempty) : 0 < M.wsum x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hS

/-- The analytic core: for any continuation value `V`, the margin equation determines the
maximiser and the value of the unified one-period problem. -/
lemma closedU (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ)
    (hS : (M.S x).Nonempty) (m : ℝ)
    (hm : M.marginLHS m
      = Real.exp ((M.aW x - M.wavg x (fun i => V x - V (M.sell x i))) / M.μ)) :
    (∀ r, M.objU V x r ≤ V x + M.lam * (m - M.μ)) ∧
    M.objU V x (M.wavg x (fun i => V x - V (M.sell x i)) + m) = V x + M.lam * (m - M.μ) ∧
    m * M.P0 x (M.const (M.wavg x (fun i => V x - V (M.sell x i)) + m)) = M.μ ∧
    M.μ ≤ m := by
  have hμ := hM.mu_pos
  have hlam := hM.lam_pos
  have hW := wsum_pos M x hS
  have hU := Real.exp_pos (M.u0 / M.μ)
  have hrel := conv M hM x hW _ m hm
  obtain ⟨q1, q2⟩ := key_scalar_eq hμ hW hU hrel
  refine ⟨?_, ?_, ?_, root_ge M hM (Real.exp_pos _).le hm⟩
  · intro r
    rw [objU_closed M V x hW.ne' r]
    have := mul_le_mul_of_nonneg_left (key_scalar hμ hW hU hrel r) hlam.le
    linarith
  · rw [objU_closed M V x hW.ne', q1]
  · rw [Model.P0, den_const, q2]

lemma sell_comm (x : Fin M.n → ℕ) (i j : Fin M.n) :
    M.sell (M.sell x i) j = M.sell (M.sell x j) i := by
  by_cases hij : i = j
  · subst hij; rfl
  · funext k
    by_cases hki : k = i
    · subst hki
      simp [Model.sell, Function.update_apply, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [Model.sell, Function.update_apply, hki, Ne.symm hki, hij, Ne.symm hij]
      · simp [Model.sell, Function.update_apply, hki, hkj]

lemma objU_FD (V : (Fin M.n → ℕ) → ℝ) (z : Fin M.n → ℕ) (r : ℝ) :
    M.objU V z r = (1 - M.lam) * V z + M.lam *
      (((∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ) * (r + V (M.sell z j)))
          + Real.exp (M.u0 / M.μ) * V z) /
        ((∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ)) + Real.exp (M.u0 / M.μ))) := by
  have hD := den_pos M z (M.const r)
  have hDe : M.den z (M.const r)
      = (∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ)) + Real.exp (M.u0 / M.μ) := rfl
  rw [hDe] at hD
  unfold Model.objU Model.obj Model.P0
  rw [hDe]
  have u1 : ∑ j ∈ M.S z, M.const r j * M.P z (M.const r) j
      = (∑ j ∈ M.S z, r * Real.exp ((M.a j - r) / M.μ))
        / ((∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ)) + Real.exp (M.u0 / M.μ)) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj => by
      rw [P_of_mem M _ hj, hDe]; simp only [Model.const]; ring)
  have u2 : ∑ j ∈ M.S z, M.P z (M.const r) j * V (M.sell z j)
      = (∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ) * V (M.sell z j))
        / ((∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ)) + Real.exp (M.u0 / M.μ)) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj => by
      rw [P_of_mem M _ hj, hDe]; simp only [Model.const]; ring)
  have u3 : ∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ) * (r + V (M.sell z j))
      = (∑ j ∈ M.S z, r * Real.exp ((M.a j - r) / M.μ))
        + ∑ j ∈ M.S z, Real.exp ((M.a j - r) / M.μ) * V (M.sell z j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [u1, u2, u3]
  field_simp
  ring

lemma real_ineq2 {lam U τ Ay By Bx Vx Vy r : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hU : 0 < U)
    (hAy : 0 ≤ Ay) (hτ : 0 ≤ τ) (hB : By ≤ Bx) (hV : Vy ≤ Vx)
    (hF : By + U * Vy ≤ (Ay + U) * (r + Vy)) :
    (1 - lam) * Vy + lam * ((By + U * Vy) / (Ay + U))
      ≤ (1 - lam) * Vx + lam * ((τ * (r + Vy) + Bx + U * Vx) / (τ + Ay + U)) := by
  have hDy : 0 < Ay + U := by linarith
  have hDx : 0 < τ + Ay + U := by linarith
  have k1 : (By + U * Vy) / (Ay + U) ≤ (τ * (r + Vy) + By + U * Vy) / (τ + Ay + U) := by
    rw [div_le_div_iff₀ hDy hDx]
    nlinarith [mul_le_mul_of_nonneg_left hF hτ]
  have k2 : (τ * (r + Vy) + By + U * Vy) / (τ + Ay + U)
      ≤ (τ * (r + Vy) + Bx + U * Vx) / (τ + Ay + U) := by
    apply div_le_div_of_nonneg_right _ hDx.le
    nlinarith [mul_le_mul_of_nonneg_left hV hU.le]
  have k3 := mul_le_mul_of_nonneg_left (k1.trans k2) hl0
  have k4 := mul_le_mul_of_nonneg_left hV (show 0 ≤ 1 - lam by linarith)
  linarith

lemma mono_step (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ)
    (hV : ∀ z k, k ∈ M.S z → V (M.sell z k) ≤ V z) (x : Fin M.n → ℕ) (i : Fin M.n)
    (hi : i ∈ M.S x) (r : ℝ) (hr : 0 ≤ r) :
    M.objU V (M.sell x i) r ≤ M.objU V x r := by
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_le_one
  have hmemS : ∀ (z : Fin M.n → ℕ) k, k ∈ M.S z ↔ 0 < z k := fun z k => by simp [Model.S]
  have hxi : 0 < x i := (hmemS x i).1 hi
  set y := M.sell x i with hy
  have hyk : ∀ k, y k ≤ x k := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [y, Model.sell]
    · simp [y, Model.sell, Function.update_apply, hk]
  have hsub : M.S y ⊆ M.S x := fun k hk =>
    (hmemS x k).2 (lt_of_lt_of_le ((hmemS y k).1 hk) (hyk k))
  have hT : ∀ j ∈ M.S x \ M.S y, j = i := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    by_contra hji
    apply hj.2
    rw [hmemS]
    have : y j = x j := by simp [y, Model.sell, Function.update_apply, hji]
    rw [this]; exact (hmemS x j).1 hj.1
  have hcont : ∀ j ∈ M.S y, V (M.sell y j) ≤ V (M.sell x j) := by
    intro j hj
    rw [hy, sell_comm M x i j]
    apply hV
    rw [hmemS]
    by_cases hji : j = i
    · subst hji; exact (hmemS _ _).1 hj
    · simp [Model.sell, Function.update_apply, Ne.symm hji, hxi]
  set E : Fin M.n → ℝ := fun j => Real.exp ((M.a j - r) / M.μ) with hE
  have hE0 : ∀ j, 0 ≤ E j := fun j => (Real.exp_pos _).le
  rw [objU_FD M V y r, objU_FD M V x r]
  rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub (f := fun j => Real.exp ((M.a j - r) / M.μ))]
  have hTs : ∑ j ∈ M.S x \ M.S y, Real.exp ((M.a j - r) / M.μ) * (r + V (M.sell x j))
      = (∑ j ∈ M.S x \ M.S y, Real.exp ((M.a j - r) / M.μ)) * (r + V y) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j hj => by rw [hT j hj])
  rw [hTs]
  apply real_ineq2 hl0.le hl1 (Real.exp_pos _)
    (Finset.sum_nonneg (fun j _ => hE0 j)) (Finset.sum_nonneg (fun j _ => hE0 j))
  · exact Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (by linarith [hcont j hj]) (hE0 j))
  · exact hV x i hi
  · have hb : ∑ j ∈ M.S y, Real.exp ((M.a j - r) / M.μ) * (r + V (M.sell y j))
        ≤ (∑ j ∈ M.S y, Real.exp ((M.a j - r) / M.μ)) * (r + V y) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun j hj =>
        mul_le_mul_of_nonneg_left (by linarith [hV y j hj]) (hE0 j))
    have hu := mul_le_mul_of_nonneg_left hr (Real.exp_pos (M.u0 / M.μ)).le
    nlinarith

lemma bdd (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ)
    (hS : (M.S x).Nonempty) : BddAbove (M.objU V x '' Set.Ici 0) := by
  obtain ⟨m, hm⟩ := root_exists M hM
    (Real.exp_pos ((M.aW x - M.wavg x (fun i => V x - V (M.sell x i))) / M.μ)).le
  obtain ⟨h1, -⟩ := closedU M hM V x hS m hm
  exact ⟨V x + M.lam * (m - M.μ), by rintro _ ⟨r, _, rfl⟩; exact h1 r⟩

lemma mono_all (hM : M.Assumptions) :
    ∀ s z k, k ∈ M.S z → M.piU s (M.sell z k) ≤ M.piU s z := by
  intro s
  induction s with
  | zero => intro z k _; simp [Model.piU]
  | succ s ih =>
    intro z k hk
    show sSup (M.objU (M.piU s) (M.sell z k) '' Set.Ici 0)
      ≤ sSup (M.objU (M.piU s) z '' Set.Ici 0)
    apply csSup_le (Set.nonempty_Ici.image _)
    rintro _ ⟨r, hr, rfl⟩
    exact (mono_step M hM (M.piU s) ih z k hk r hr).trans
      (le_csSup (bdd M hM _ z ⟨k, hk⟩) ⟨r, hr, rfl⟩)

lemma deltaW_succ (s : ℕ) (x : Fin M.n → ℕ) :
    M.deltaW (s + 1) x = M.wavg x (fun i => M.piU s x - M.piU s (M.sell x i)) := by
  simp [Model.deltaW, Model.deltaU]

lemma pi_succ_facts (hM : M.Assumptions) (s : ℕ) (x : Fin M.n → ℕ) (hS : (M.S x).Nonempty)
    (m : ℝ) (hm : M.marginLHS m = M.sigmaU (s + 1) x) :
    0 ≤ M.deltaW (s + 1) x + m ∧
    IsMaxOn (M.objU (M.piU s) x) (Set.Ici 0) (M.deltaW (s + 1) x + m) ∧
    M.piU (s + 1) x = M.objU (M.piU s) x (M.deltaW (s + 1) x + m) ∧
    M.objU (M.piU s) x (M.deltaW (s + 1) x + m) = M.piU s x + M.lam * (m - M.μ) ∧
    m * M.P0 x (M.const (M.deltaW (s + 1) x + m)) = M.μ := by
  have hμ := hM.mu_pos
  have hm' : M.marginLHS m = Real.exp ((M.aW x
      - M.wavg x (fun i => M.piU s x - M.piU s (M.sell x i))) / M.μ) := by
    rw [hm, Model.sigmaU, deltaW_succ]
  obtain ⟨h1, h2, h3, h4⟩ := closedU M hM (M.piU s) x hS m hm'
  rw [deltaW_succ]
  have hd : 0 ≤ M.wavg x (fun i => M.piU s x - M.piU s (M.sell x i)) := by
    apply div_nonneg _ (wsum_pos M x hS).le
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (Real.exp_pos _).le
      (sub_nonneg.mpr (mono_all M hM s x i hi)))
  have hgr : IsGreatest (M.objU (M.piU s) x '' Set.Ici 0)
      (M.objU (M.piU s) x (M.wavg x (fun i => M.piU s x - M.piU s (M.sell x i)) + m)) := by
    refine ⟨⟨_, Set.mem_Ici.mpr (by linarith), rfl⟩, ?_⟩
    rintro _ ⟨r, _, rfl⟩
    rw [h2]; exact h1 r
  refine ⟨by linarith, ?_, ?_, h2, h3⟩
  · exact isMaxOn_iff.mpr (fun r _ => by rw [h2]; exact h1 r)
  · show sSup (M.objU (M.piU s) x '' Set.Ici 0) = _
    exact hgr.csSup_eq

end SPU13

open SubstitutePricing.Unified in
theorem solution (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) (hx : (M.S x).Nonempty) :
    (∃! m : ℝ, M.marginLHS m = M.sigmaU t x) ∧
    (∀ m : ℝ, M.marginLHS m = M.sigmaU t x →
      0 ≤ M.deltaW t x + m ∧
      IsMaxOn (M.objU (M.piU (t - 1)) x) (Set.Ici 0) (M.deltaW t x + m) ∧
      M.piU t x = M.objU (M.piU (t - 1)) x (M.deltaW t x + m) ∧
      m * M.P0 x (M.const (M.deltaW t x + m)) = M.μ) ∧
    (∀ ms : ℕ → ℝ, (∀ s ∈ Finset.Icc 1 t, M.marginLHS (ms s) = M.sigmaU s x) →
      M.piU t x = M.lam * ∑ s ∈ Finset.Icc 1 t, (ms s - M.μ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hlam := hM.lam_pos
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := SPU13.root_exists M hM (Real.exp_pos _).le (σ := M.sigmaU (k + 1) x)
    refine ⟨m, hm, fun m' hm' => ?_⟩
    obtain ⟨-, -, a3, a4, -⟩ := SPU13.pi_succ_facts M hM k x hx m hm
    obtain ⟨-, -, b3, b4, -⟩ := SPU13.pi_succ_facts M hM k x hx m' hm'
    have e : M.lam * (m' - M.μ) = M.lam * (m - M.μ) := by linarith
    have := mul_left_cancel₀ hlam.ne' e
    linarith
  · intro m hm
    obtain ⟨h1, h2, h3, -, h5⟩ := SPU13.pi_succ_facts M hM k x hx m hm
    simp only [Nat.add_sub_cancel]
    exact ⟨h1, h2, h3, h5⟩
  · intro ms hms
    have tel : ∀ u, (∀ v ∈ Finset.Icc 1 u, M.marginLHS (ms v) = M.sigmaU v x) →
        M.piU u x = M.lam * ∑ v ∈ Finset.Icc 1 u, (ms v - M.μ) := by
      intro u
      induction u with
      | zero => intro _; simp [Model.piU]
      | succ u ih =>
        intro h
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ u + 1)]
        have hu := h (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩)
        obtain ⟨-, -, e3, e4, -⟩ := SPU13.pi_succ_facts M hM u x hx _ hu
        have hih := ih (fun v hv => h v (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hv).1, by have := (Finset.mem_Icc.mp hv).2; omega⟩))
        rw [e3, e4, hih]
        ring
    exact tel _ hms
