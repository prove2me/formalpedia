-- Prove2me | solution 1 for OptInapprox.MaxCut.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:28:09.004084+00:00
-- url     : https://prove2.me/submissions/249f10c4-5f36-436d-8637-2d6094692335

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Verifier

open OptInapprox.MaxCut

lemma ite_ne_eq_one_sub_pm_mul (b₁ b₂ : Bool) :
    (if b₁ ≠ b₂ then (1 : ℝ) else 0) = 1 / 2 - 1 / 2 * (pm b₁ * pm b₂) := by
  cases b₁ <;> cases b₂ <;> norm_num [pm]

lemma pm_xor (a b : Bool) : pm (xor a b) = pm a * pm b := by
  cases a <;> cases b <;> norm_num [pm]

def muEquiv {M : ℕ} (σ' : Equiv.Perm (Fin M)) (x : Fin M → Bool) :
    (Fin M → Bool) ≃ (Fin M → Bool) where
  toFun y := fun i => xor (x (σ' i)) (y (σ' i))
  invFun μ := fun j => xor (x j) (μ (σ'.symm j))
  left_inv y := by
    ext j
    simp only [Equiv.apply_symm_apply]
    cases x j <;> cases y j <;> rfl
  right_inv μ := by
    ext i
    simp only [Equiv.symm_apply_apply]
    cases x (σ' i) <;> cases μ i <;> rfl

lemma coordMul_compose_muEquiv {M : ℕ} (σ' : Equiv.Perm (Fin M)) (x y : Fin M → Bool) :
    coordMul (compose x σ') (muEquiv σ' x y) = compose y σ' := by
  ext i
  change xor (x (σ' i)) (xor (x (σ' i)) (y (σ' i))) = y (σ' i)
  cases x (σ' i) <;> cases y (σ' i) <;> rfl

lemma muWeight_muEquiv {M : ℕ} (ρ : ℝ) (σ' : Equiv.Perm (Fin M)) (x y : Fin M → Bool) :
    muWeight ρ (muEquiv σ' x y) = corrKernel ρ x y := by
  unfold muWeight corrKernel
  have h := Equiv.prod_comp σ' (fun j => (1 + ρ * pm (xor (x j) (y j))) / 2)
  change (∏ i, (1 + ρ * pm (xor (x (σ' i)) (y (σ' i)))) / 2) =
    ∏ i, (1 + ρ * pm (x i) * pm (y i)) / 2
  rw [h]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [pm_xor]
  ring

lemma sum_corrKernel {M : ℕ} (ρ : ℝ) (x : Fin M → Bool) :
    ∑ y : Fin M → Bool, corrKernel ρ x y = 1 := by
  unfold corrKernel
  have h := (Fintype.prod_sum (fun (i : Fin M) (b : Bool) => (1 + ρ * pm (x i) * pm b) / 2)).symm
  rw [h]
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin M)),
      (∑ b : Bool, (1 + ρ * pm (x i) * pm b) / 2) = 1 := by
    intro i _
    rw [Fintype.sum_bool]
    have ht : pm true = -1 := rfl
    have hf : pm false = 1 := rfl
    rw [ht, hf]
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_const_one]

lemma sum_mu_inner {M : ℕ} (ρ : ℝ) (σ σ' : Equiv.Perm (Fin M))
    (fw fw' : (Fin M → Bool) → Bool) (x : Fin M → Bool) :
    ∑ μ : Fin M → Bool, muWeight ρ μ *
        (if fw (compose x σ) ≠ fw' (coordMul (compose x σ') μ) then (1 : ℝ) else 0) =
      1 / 2 - 1 / 2 * ∑ y : Fin M → Bool,
        corrKernel ρ x y * (pm (fw (compose x σ)) * pm (fw' (compose y σ'))) := by
  have h := Equiv.sum_comp (muEquiv σ' x)
    (fun μ => muWeight ρ μ *
      (if fw (compose x σ) ≠ fw' (coordMul (compose x σ') μ) then (1 : ℝ) else 0))
  rw [← h]
  have hterm : ∀ y : Fin M → Bool,
      muWeight ρ (muEquiv σ' x y) *
        (if fw (compose x σ) ≠ fw' (coordMul (compose x σ') (muEquiv σ' x y)) then (1 : ℝ) else 0) =
      corrKernel ρ x y * (1 / 2 : ℝ) -
        1 / 2 * (corrKernel ρ x y * (pm (fw (compose x σ)) * pm (fw' (compose y σ')))) := by
    intro y
    rw [muWeight_muEquiv, coordMul_compose_muEquiv, ite_ne_eq_one_sub_pm_mul]
    ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sum_corrKernel, one_mul]

lemma sum_x_inner {M : ℕ} (ρ : ℝ) (σ σ' : Equiv.Perm (Fin M))
    (fw fw' : (Fin M → Bool) → Bool) :
    (2 ^ M : ℝ)⁻¹ * ∑ x : Fin M → Bool, ∑ μ : Fin M → Bool, muWeight ρ μ *
        (if fw (compose x σ) ≠ fw' (coordMul (compose x σ') μ) then (1 : ℝ) else 0) =
      1 / 2 - 1 / 2 * ((2 ^ M : ℝ)⁻¹ * ∑ x : Fin M → Bool, ∑ y : Fin M → Bool,
        corrKernel ρ x y * (pm (fw (compose x σ)) * pm (fw' (compose y σ')))) := by
  simp_rw [sum_mu_inner, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  have h2M : (2 : ℝ) ^ M ≠ 0 := pow_ne_zero M (by norm_num)
  push_cast
  field_simp [h2M]

lemma swap_four_sums {α β : Type*} [Fintype α] (s : Finset β) (f : α → α → β → β → ℝ) :
    ∑ x : α, ∑ y : α, ∑ w ∈ s, ∑ w' ∈ s, f x y w w' =
      ∑ w ∈ s, ∑ w' ∈ s, ∑ x : α, ∑ y : α, f x y w w' := by
  trans ∑ x : α, ∑ w ∈ s, ∑ w' ∈ s, ∑ y : α, f x y w w'
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_comm]

lemma noiseStab_gv_eq (L : ULC) (ρ : ℝ) (F : Fin L.nW → (Fin L.M → Bool) → Bool)
    (v : Fin L.nV) :
    noiseStab ρ (gv L F v) =
      ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
        ((2 ^ L.M : ℝ)⁻¹ * ∑ x : Fin L.M → Bool, ∑ y : Fin L.M → Bool,
          corrKernel ρ x y * (pm (F w (compose x (L.σ v w))) * pm (F w' (compose y (L.σ v w'))))) := by
  unfold noiseStab cubeE
  have hinner : ∀ (x y : Fin L.M → Bool),
      corrKernel ρ x y * (gv L F v x * gv L F v y) =
      ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
        corrKernel ρ x y * (pm (F w (compose x (L.σ v w))) * pm (F w' (compose y (L.σ v w')))) := by
    intro x y
    unfold gv
    have hmul : (∑ w ∈ L.nbrs v, pm (F w (compose x (L.σ v w)))) *
          (∑ w' ∈ L.nbrs v, pm (F w' (compose y (L.σ v w')))) =
        ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
          pm (F w (compose x (L.σ v w))) * pm (F w' (compose y (L.σ v w'))) := by
      rw [Finset.sum_mul_sum]
    calc corrKernel ρ x y * ((((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v, pm (F w (compose x (L.σ v w)))) *
            (((L.nbrs v).card : ℝ)⁻¹ * ∑ w' ∈ L.nbrs v, pm (F w' (compose y (L.σ v w')))))
        = ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * (corrKernel ρ x y *
            ((∑ w ∈ L.nbrs v, pm (F w (compose x (L.σ v w)))) *
              (∑ w' ∈ L.nbrs v, pm (F w' (compose y (L.σ v w')))))) := by ring
      _ = ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
            corrKernel ρ x y * (pm (F w (compose x (L.σ v w))) * pm (F w' (compose y (L.σ v w')))) := by
          rw [hmul, Finset.mul_sum]
          simp_rw [Finset.mul_sum]
  simp_rw [hinner]
  have hpull : (2 ^ L.M : ℝ)⁻¹ * ∑ x : Fin L.M → Bool, ∑ y : Fin L.M → Bool,
      ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
        corrKernel ρ x y * (pm (F w (compose x (L.σ v w))) * pm (F w' (compose y (L.σ v w')))) =
      ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ((2 ^ L.M : ℝ)⁻¹ *
        ∑ x : Fin L.M → Bool, ∑ y : Fin L.M → Bool, ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
          corrKernel ρ x y * (pm (F w (compose x (L.σ v w))) * pm (F w' (compose y (L.σ v w'))))) := by
    simp_rw [← Finset.mul_sum]
    ring
  rw [hpull]
  congr 1
  rw [swap_four_sums, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.mul_sum]

lemma sum_w_inner (L : ULC) (ρ : ℝ) (F : Fin L.nW → (Fin L.M → Bool) → Bool)
    (v : Fin L.nV) (hd : 0 < (L.nbrs v).card) :
    ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
        (2 ^ L.M : ℝ)⁻¹ * ∑ x, ∑ μ, muWeight ρ μ *
          (if F w (compose x (L.σ v w)) ≠ F w' (coordMul (compose x (L.σ v w')) μ) then 1 else 0) =
      1 / 2 - 1 / 2 * noiseStab ρ (gv L F v) := by
  simp_rw [sum_x_inner]
  let pairVal (w w' : Fin L.nW) : ℝ :=
    (2 ^ L.M : ℝ)⁻¹ * ∑ x : Fin L.M → Bool, ∑ y : Fin L.M → Bool,
      corrKernel ρ x y * (pm (F w (compose x (L.σ v w))) * pm (F w' (compose y (L.σ v w'))))
  change ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, (1 / 2 - 1 / 2 * pairVal w w') =
    1 / 2 - 1 / 2 * noiseStab ρ (gv L F v)
  have hns : noiseStab ρ (gv L F v) =
      ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, pairVal w w' :=
    noiseStab_gv_eq L ρ F v
  rw [hns]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard0 : ((L.nbrs v).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  field_simp [hcard0]

theorem solution (L : ULC) (hreg : L.IsVRegular) (ρ : ℝ) (_hρ₁ : -1 < ρ) (_hρ₂ : ρ < 0)
    (F : Fin L.nW → (Fin L.M → Bool) → Bool) :
    accProb L ρ F = 1 / 2 - 1 / 2 * ((L.nV : ℝ)⁻¹ * ∑ v, noiseStab ρ (gv L F v)) := by
  obtain ⟨hnV, d, hd, hcard⟩ := hreg
  unfold accProb
  have hv : ∀ v : Fin L.nV,
      ((L.nbrs v).card : ℝ)⁻¹ ^ 2 * ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v,
        (2 ^ L.M : ℝ)⁻¹ * ∑ x, ∑ μ, muWeight ρ μ *
          (if F w (compose x (L.σ v w)) ≠ F w' (coordMul (compose x (L.σ v w')) μ) then 1 else 0) =
      1 / 2 - 1 / 2 * noiseStab ρ (gv L F v) := by
    intro v
    exact sum_w_inner L ρ F v (by rw [hcard v]; exact hd)
  simp_rw [hv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  have hnV0 : (L.nV : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnV)
  field_simp [hnV0]
