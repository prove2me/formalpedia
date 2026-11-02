-- Prove2me | solution 1 for OblivEllipsoid.Infeas.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:31:56.336582+00:00
-- url     : https://prove2.me/submissions/9c0be52b-1308-495f-b113-4d4864be24f8

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEALem71

lemma AT_mulVec_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (k : Fin m) :
    (Aᵀ *ᵥ x) k = col A k ⬝ᵥ x := by
  simp [Matrix.mulVec, dotProduct, col, Matrix.transpose_apply]

lemma quad_B {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (B A d *ᵥ x) = ∑ k : Fin m, d k * (col A k ⬝ᵥ x) ^ 2 := by
  have h1 : B A d *ᵥ x = A *ᵥ (diagonal d *ᵥ (Aᵀ *ᵥ x)) := by
    simp [B, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, AT_mulVec_apply]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma B_symm {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) :
    (B A d)ᵀ = B A d := by
  simp [B, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Under Assumption 1.1 and `d > 0`, `B(d)` is invertible. -/
lemma B_isUnit {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A)
    (d : Fin m → ℝ) (hd : ∀ i, 0 < d i) : IsUnit (B A d) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices H : ∀ x, B A d *ᵥ x = 0 → x = 0 by
    intro x y hxy
    have := H (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
    exact sub_eq_zero.1 this
  intro x hx
  have hq : ∑ k : Fin m, d k * (col A k ⬝ᵥ x) ^ 2 = 0 := by
    rw [← quad_B, hx, dotProduct_zero]
  have hall : ∀ k, col A k ⬝ᵥ x = 0 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
      have := hd k; positivity)).1 hq k (Finset.mem_univ _)
    have hdk := (hd k).ne'
    have : (col A k ⬝ᵥ x) ^ 2 = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hdk
      · exact h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  obtain ⟨lam, -, hlam⟩ := hA.1 x
  have hATx : Aᵀ *ᵥ x = 0 := by
    funext k; rw [AT_mulVec_apply]; exact hall k
  have : x ⬝ᵥ x = 0 := by
    calc x ⬝ᵥ x = x ⬝ᵥ (A *ᵥ lam) := by rw [hlam]
      _ = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hATx, zero_dotProduct]
  exact dotProduct_self_eq_zero.1 this

theorem prop71 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hf : 0 < f A u d ell) :
    ∀ i : Fin m, slabRadius A u d ell i ≤
      (d i / f A u d ell) ^ (-(1 / 2 : ℝ)) := by
  intro i
  set w := (B A d)⁻¹ *ᵥ col A i with hw
  have hBu := B_isUnit A hA d hd
  have hBw : B A d *ᵥ w = col A i := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBu),
      Matrix.one_mulVec]
  set q := col A i ⬝ᵥ w with hq
  have hq_eq : q = ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 := by
    rw [← quad_B, hBw, hq, dotProduct_comm]
  have hq_nonneg : 0 ≤ q := by
    rw [hq_eq]; exact Finset.sum_nonneg fun k _ => by have := hd k; positivity
  have hq_ge : d i * q ^ 2 ≤ q := by
    have := Finset.single_le_sum (f := fun k => d k * (col A k ⬝ᵥ w) ^ 2)
      (fun k _ => by have := hd k; positivity) (Finset.mem_univ i)
    simpa [← hq_eq] using this
  have hdi := hd i
  have hq_le : q ≤ 1 / d i := by
    rcases hq_nonneg.eq_or_lt with h | h
    · rw [← h]; positivity
    · rw [le_div_iff₀ hdi]
      nlinarith
  have hS : slabRadius A u d ell i = Real.sqrt (f A u d ell * q) := rfl
  have hR : (d i / f A u d ell) ^ (-(1 / 2 : ℝ)) = Real.sqrt (f A u d ell / d i) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, inv_div]
  rw [hS, hR]
  apply Real.sqrt_le_sqrt
  calc f A u d ell * q ≤ f A u d ell * (1 / d i) := by gcongr
    _ = f A u d ell / d i := by ring


/-- The slab radius is positive under Assumption 1.1. -/
lemma slab_pos {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hf : 0 < f A u d ell) (i : Fin m) :
    0 < slabRadius A u d ell i := by
  set w := (B A d)⁻¹ *ᵥ col A i with hw
  have hBu := B_isUnit A hA d hd
  have hBw : B A d *ᵥ w = col A i := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBu),
      Matrix.one_mulVec]
  set q := col A i ⬝ᵥ w with hq
  have hq_eq : q = ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 := by
    rw [← quad_B, hBw, hq, dotProduct_comm]
  have hq_nonneg : 0 ≤ q := by
    rw [hq_eq]; exact Finset.sum_nonneg fun k _ => by have := hd k; positivity
  have hqpos : 0 < q := by
    rcases hq_nonneg.eq_or_lt with h | h
    · exfalso
      have hq0 : ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 = 0 := by rw [← hq_eq, h]
      have hall : ∀ k, col A k ⬝ᵥ w = 0 := by
        intro k
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
          have := hd k; positivity)).1 hq0 k (Finset.mem_univ _)
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (hd k).ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      have hATw : Aᵀ *ᵥ w = 0 := by
        funext k; rw [AT_mulVec_apply]; exact hall k
      have hB0 : B A d *ᵥ w = 0 := by
        simp [B, ← Matrix.mulVec_mulVec, hATw]
      have hcol : col A i = 0 := by rw [← hBw, hB0]
      have h1 := hA.2 i
      have : ∀ k, A k i = 0 := fun k => congrFun hcol k
      simp [this] at h1
    · exact h
  exact Real.sqrt_pos.2 (mul_pos hf hqpos)

lemma rpow_neg_half {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- `m ≥ 2` under Assumption 1.1 whenever `m ≠ 0`. -/
lemma two_le_m {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A)
    (j : Fin m) : 2 ≤ m := by
  by_contra hm
  have hm1 : m = 1 := by have := j.pos; omega
  subst hm1
  obtain ⟨lam, hlam0, hlam⟩ := hA.1 (fun k => - A k 0)
  have h1 := hA.2 0
  have hk : ∀ k, (lam 0 + 1) * A k 0 = 0 := by
    intro k
    have := congrFun hlam k
    simp [Matrix.mulVec, dotProduct] at this
    linarith
  have hl : 0 < lam 0 + 1 := by have := hlam0 0; simp at this; linarith
  have : ∀ k, A k 0 = 0 := fun k => by
    rcases mul_eq_zero.1 (hk k) with h | h
    · linarith
    · exact h
  simp [this] at h1

/-- The numerical inequality at the end of the proof of Lemma 7.1. -/
lemma const_bound (m : ℕ) (hm : 2 ≤ m) :
    ((m : ℝ) / ((m : ℝ) + 1)) * Real.sqrt ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) ^ (m - 1) ≤
      Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
  set ρ := Real.sqrt ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) with hρ
  have hρ2 : ρ ^ 2 = (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hL0 : 0 ≤ ((m : ℝ) / ((m : ℝ) + 1)) * ρ ^ (m - 1) := by positivity
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.exp_pos _).le
  rw [mul_pow, ← pow_mul, mul_comm (m - 1) 2, pow_mul, hρ2, ← Real.exp_nat_mul]
  have e1 : (m : ℝ) / ((m : ℝ) + 1) ≤ Real.exp (-(1 / ((m : ℝ) + 1))) := by
    have := Real.add_one_le_exp (-(1 / ((m : ℝ) + 1)))
    have : (m : ℝ) / ((m : ℝ) + 1) = -(1 / ((m : ℝ) + 1)) + 1 := by
      field_simp; ring
    linarith
  have e2 : (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) ≤ Real.exp (1 / ((m : ℝ) ^ 2 - 1)) := by
    have := Real.add_one_le_exp (1 / ((m : ℝ) ^ 2 - 1))
    have : (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) = 1 / ((m : ℝ) ^ 2 - 1) + 1 := by
      field_simp; ring
    linarith
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  calc ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 * ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) ^ (m - 1)
      ≤ Real.exp (-(1 / ((m : ℝ) + 1))) ^ 2 * Real.exp (1 / ((m : ℝ) ^ 2 - 1)) ^ (m - 1) := by
        gcongr
    _ = Real.exp (2 * (-(1 / ((m : ℝ) + 1))) + ((m - 1 : ℕ) : ℝ) * (1 / ((m : ℝ) ^ 2 - 1))) := by
        rw [Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    _ = Real.exp (((2 : ℕ) : ℝ) * (-(1 / (2 * ((m : ℝ) + 1))))) := by
        congr 1
        rw [hmcast]
        have h3 : (m : ℝ) ^ 2 - 1 = ((m : ℝ) - 1) * ((m : ℝ) + 1) := by ring
        rw [h3]
        have : (m : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring

theorem lem71 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell dTilde ellTilde : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hdTilde : ∀ i, 0 < dTilde i)
    (hf : 0 < f A u d ell) (hfTilde : 0 < f A u dTilde ellTilde)
    (j : Fin m) (alpha : ℝ)
    (hupdate : (1 / f A u dTilde ellTilde) • dTilde = alpha •
      ((1 / f A u d ell) • d +
        ((2 / ((m : ℝ) - 1)) * (1 / slabRadius A u d ell j ^ 2)) • Pi.single j 1))
    (halpha : (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) ≤ alpha)
    (htau : tau A u ≤ (d j / f A u d ell) ^ (-(1 / 2 : ℝ))) :
    potential A u dTilde ellTilde ≤
      Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) * potential A u d ell := by
  have hm := two_le_m A hA j
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
  set F := f A u d ell
  set Ft := f A u dTilde ellTilde
  set γ := slabRadius A u d ell j
  set κ := ((m : ℝ) / ((m : ℝ) + 1)) * tau A u with hκ
  have hτ0 : 0 ≤ tau A u := abs_nonneg _
  have hκ0 : 0 ≤ κ := by positivity
  have hκτ : κ ≤ tau A u := by
    rw [hκ]
    have : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  set N : Fin m → ℝ := fun i => d i / F
  set Nt : Fin m → ℝ := fun i => dTilde i / Ft
  have hN : ∀ i, 0 < N i := fun i => div_pos (hd i) hf
  have hNt : ∀ i, 0 < Nt i := fun i => div_pos (hdTilde i) hfTilde
  have hupd : ∀ i, Nt i = alpha * (N i +
      ((2 / ((m : ℝ) - 1)) * (1 / γ ^ 2)) * ((Pi.single j (1 : ℝ) : Fin m → ℝ) i)) := by
    intro i
    have := congrFun hupdate i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at this
    simp only [Nt, N]
    rw [div_eq_inv_mul, div_eq_inv_mul, ← one_div, ← one_div, this]
  have hmu : ∀ i, mu A u d ell i = max (Real.sqrt (N i))⁻¹ κ := by
    intro i; simp only [mu]; rw [rpow_neg_half (hN i).le]
  have hmut : ∀ i, mu A u dTilde ellTilde i = max (Real.sqrt (Nt i))⁻¹ κ := by
    intro i; simp only [mu]; rw [rpow_neg_half (hNt i).le]
  -- alpha positive
  have hα : ((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2 ≤ alpha := halpha
  have hαpos : 0 < alpha := lt_of_lt_of_le (by positivity) hα
  -- the j-th coordinate
  have hγpos : 0 < γ := slab_pos A u d ell hA hd hf j
  have hγle : γ ≤ (Real.sqrt (N j))⁻¹ := by
    have := prop71 A u d ell hA hd hf j
    rwa [rpow_neg_half (hN j).le] at this
  have hγ2 : N j ≤ 1 / γ ^ 2 := by
    have hs := Real.sqrt_pos.2 (hN j)
    have h1 : γ * Real.sqrt (N j) ≤ 1 := by
      calc γ * Real.sqrt (N j) ≤ (Real.sqrt (N j))⁻¹ * Real.sqrt (N j) := by gcongr
        _ = 1 := inv_mul_cancel₀ hs.ne'
    have h2 : γ ^ 2 * N j ≤ 1 := by
      have := mul_self_le_mul_self (by positivity) h1
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hN j).le] at this
      nlinarith
    rw [le_div_iff₀ (by positivity)]; linarith
  have hNtj : (((m : ℝ) + 1) / m) ^ 2 * N j ≤ Nt j := by
    rw [hupd j]
    simp only [Pi.single_eq_same, mul_one]
    have hc : 2 / ((m : ℝ) - 1) * N j ≤ 2 / ((m : ℝ) - 1) * (1 / γ ^ 2) := by
      have : 0 ≤ 2 / ((m : ℝ) - 1) := by apply div_nonneg <;> linarith
      gcongr
    have hNj := hN j
    have step : (((m : ℝ) + 1) / m) ^ 2 * N j =
        (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) * (N j + 2 / ((m : ℝ) - 1) * N j) := by
      have : (m : ℝ) - 1 ≠ 0 := by linarith
      have : (m : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [step]
    calc (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) * (N j + 2 / ((m : ℝ) - 1) * N j)
        ≤ alpha * (N j + 2 / ((m : ℝ) - 1) * N j) := by
          gcongr
          have : 0 ≤ 2 / ((m : ℝ) - 1) := by apply div_nonneg <;> linarith
          positivity
      _ ≤ alpha * (N j + 2 / ((m : ℝ) - 1) * (1 / γ ^ 2)) := by gcongr
  have hj : mu A u dTilde ellTilde j ≤ ((m : ℝ) / ((m : ℝ) + 1)) * mu A u d ell j := by
    rw [hmut, hmu]
    have hτ' : tau A u ≤ (Real.sqrt (N j))⁻¹ := by rwa [rpow_neg_half (hN j).le] at htau
    have hmax : max (Real.sqrt (N j))⁻¹ κ = (Real.sqrt (N j))⁻¹ := max_eq_left (hκτ.trans hτ')
    rw [hmax]
    have hsq : (Real.sqrt (Nt j))⁻¹ ≤ ((m : ℝ) / ((m : ℝ) + 1)) * (Real.sqrt (N j))⁻¹ := by
      have h1 : ((m : ℝ) + 1) / m * Real.sqrt (N j) ≤ Real.sqrt (Nt j) := by
        rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ ((m : ℝ) + 1) / m), ← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt hNtj
      have hs := Real.sqrt_pos.2 (hN j)
      have hst := Real.sqrt_pos.2 (hNt j)
      rw [inv_le_comm₀ hst (by positivity), mul_inv, inv_div, inv_inv]
      exact h1
    apply max_le hsq
    calc κ = ((m : ℝ) / ((m : ℝ) + 1)) * tau A u := rfl
      _ ≤ ((m : ℝ) / ((m : ℝ) + 1)) * (Real.sqrt (N j))⁻¹ := by gcongr
  -- other coordinates
  set ρ := Real.sqrt ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) with hρ
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, Real.one_le_sqrt]
    rw [le_div_iff₀ hm1]; linarith
  have hi : ∀ i, i ≠ j → mu A u dTilde ellTilde i ≤ ρ * mu A u d ell i := by
    intro i hij
    rw [hmut, hmu]
    have hNti : Nt i = alpha * N i := by
      rw [hupd i, Pi.single_eq_of_ne hij]; ring
    have hsq : (Real.sqrt (Nt i))⁻¹ ≤ ρ * (Real.sqrt (N i))⁻¹ := by
      have hs := Real.sqrt_pos.2 (hN i)
      have hst := Real.sqrt_pos.2 (hNt i)
      have h1 : Real.sqrt (N i) ≤ ρ * Real.sqrt (Nt i) := by
        rw [hρ, ← Real.sqrt_mul (by positivity)]
        apply Real.sqrt_le_sqrt
        rw [hNti]
        have hNi := hN i
        calc N i = ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) * ((((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) * N i) := by
              have : (m : ℝ) ≠ 0 := by positivity
              field_simp
          _ ≤ ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) * (alpha * N i) := by gcongr
      have hρpos : 0 < ρ := by linarith
      rw [inv_le_comm₀ hst (by positivity), mul_inv, inv_inv]
      calc Real.sqrt (Nt i) = ρ⁻¹ * (ρ * Real.sqrt (Nt i)) := by field_simp
        _ ≥ ρ⁻¹ * Real.sqrt (N i) := by gcongr
    apply max_le
    · exact hsq.trans (by gcongr; exact le_max_left _ _)
    · calc κ ≤ max (Real.sqrt (N i))⁻¹ κ := le_max_right _ _
        _ ≤ ρ * max (Real.sqrt (N i))⁻¹ κ := le_mul_of_one_le_left (by positivity) hρ1
  -- combine
  have hmu0 : ∀ i, 0 ≤ mu A u d ell i := fun i => by rw [hmu]; exact le_max_of_le_right hκ0
  have hmut0 : ∀ i, 0 ≤ mu A u dTilde ellTilde i := fun i => by rw [hmut]; exact le_max_of_le_right hκ0
  unfold potential
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, mu A u dTilde ellTilde i ≤
      ρ ^ (m - 1) * ∏ i ∈ Finset.univ.erase j, mu A u d ell i := by
    have hcard : (Finset.univ.erase j).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _ => hmut0 i)
    intro i hi'
    exact hi i (Finset.ne_of_mem_erase hi')
  have hC := const_bound m hm
  have hP0 : 0 ≤ ∏ i ∈ Finset.univ.erase j, mu A u d ell i := Finset.prod_nonneg fun i _ => hmu0 i
  calc mu A u dTilde ellTilde j * ∏ i ∈ Finset.univ.erase j, mu A u dTilde ellTilde i
      ≤ (((m : ℝ) / ((m : ℝ) + 1)) * mu A u d ell j) *
          (ρ ^ (m - 1) * ∏ i ∈ Finset.univ.erase j, mu A u d ell i) := by
        apply mul_le_mul hj hrest (Finset.prod_nonneg fun i _ => hmut0 i)
        have := hmu0 j; positivity
    _ = (((m : ℝ) / ((m : ℝ) + 1)) * ρ ^ (m - 1)) *
          (mu A u d ell j * ∏ i ∈ Finset.univ.erase j, mu A u d ell i) := by ring
    _ ≤ Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) *
          (mu A u d ell j * ∏ i ∈ Finset.univ.erase j, mu A u d ell i) := by
        apply mul_le_mul_of_nonneg_right hC
        have := hmu0 j; positivity

end OEALem71
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell dTilde ellTilde : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hdTilde : ∀ i, 0 < dTilde i)
    (hf : 0 < f A u d ell) (hfTilde : 0 < f A u dTilde ellTilde)
    (j : Fin m) (alpha : ℝ)
    (hupdate : (1 / f A u dTilde ellTilde) • dTilde = alpha •
      ((1 / f A u d ell) • d +
        ((2 / ((m : ℝ) - 1)) * (1 / slabRadius A u d ell j ^ 2)) • Pi.single j 1))
    (halpha : (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) ≤ alpha)
    (htau : tau A u ≤ (d j / f A u d ell) ^ (-(1 / 2 : ℝ))) :
    potential A u dTilde ellTilde ≤
      Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) * potential A u d ell :=
  OblivEllipsoid.Infeas.OEALem71.lem71 A u d ell dTilde ellTilde hA hd hdTilde hf hfTilde j alpha
    hupdate halpha htau
