-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:18:03.889745+00:00
-- url     : https://prove2.me/submissions/2328258e-cd9f-464a-97e1-3536595725cb

import Definitions.Def_SingleExpBisect_Main_FormalSeries
open scoped Classical BigOperators
open SingleExpBisect.Main
namespace ExpLogProof

open PowerSeries in
private lemma exp_at_log :
    (PowerSeries.exp ℚ).subst (PowerSeries.log ℚ) = (1 + PowerSeries.X : PowerSeries ℚ) := by
  let E : PowerSeries ℚ := (exp ℚ).subst (log ℚ)
  let Q : PowerSeries ℚ := 1 + X
  have shift (A : PowerSeries ℚ) (n : ℕ) :
      coeff (n+1) (A * X) = coeff n A := by
    simpa using coeff_mul_X_pow A 1 n
  have hg : derivative ℚ (log ℚ) * Q = 1 := by
    rw [deriv_log]
    ext n
    cases n with
    | zero => simp [Q, coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_mk]
    | succ n =>
      simp only [Q, mul_add, mul_one, map_add, shift, coeff_mk, coeff_one,
        Nat.succ_ne_zero, if_false, Algebra.algebraMap_self_apply]
      rw [pow_succ]
      ring
  have hd : derivative ℚ E * Q = E := by
    dsimp only [E]
    rw [derivative_subst HasSubst.log, derivative_exp, mul_assoc, hg, mul_one]
  have hQ : derivative ℚ Q * Q = Q := by simp [Q, derivative_one]
  let R := E - Q
  have hR : derivative ℚ R * Q = R := by simp only [R, map_sub, sub_mul, hd, hQ]
  have hc : constantCoeff E = 1 := by
    change MvPowerSeries.constantCoeff ((exp ℚ).subst (log ℚ)) = 1
    rw [constantCoeff_subst HasSubst.log]
    rw [finsum_eq_single _ 0]
    · simp
    · intro n hn
      simp [map_pow, ← PowerSeries.constantCoeff_eq, zero_pow hn]
  have hzero : R = 0 := by
    ext n
    change coeff n R = 0
    induction n with
    | zero => simp [R,Q,coeff_zero_eq_constantCoeff,hc]
    | succ n ih =>
      have hh := congrArg (coeff n) hR
      change coeff n (derivative ℚ R * (1+X)) = coeff n R at hh
      rw [mul_add, mul_one, map_add, coeff_derivative, ih] at hh
      have hshift : coeff n (derivative ℚ R * X) = 0 := by
        cases n with
        | zero => simp [coeff_zero_eq_constantCoeff]
        | succ k => rw [shift,coeff_derivative,ih,zero_mul]
      rw [hshift,add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right (by positivity)
  exact sub_eq_zero.mp hzero

private lemma finite_subst {σ : Type} (A : MvPowerSeries σ ℚ)
    (hA : A.constantCoeff = 0) (F : PowerSeries ℚ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (F.subst A) =
      ∑ j ∈ Finset.range (m.degree + 1),
        PowerSeries.coeff j F * MvPowerSeries.coeff m (A ^ j) := by
  rw [PowerSeries.coeff_subst (.of_constantCoeff_zero hA)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  have hj' : m.degree < j := by simpa using h
  have hz := MvPowerSeries.coeff_of_lt_order (f := A^j) (d := m)
    (lt_of_lt_of_le (by exact_mod_cast hj') (A.le_order_pow_of_constantCoeff_eq_zero j hA))
  exact hj (by simp [hz])

private lemma expPS_eq {σ : Type} (A : MvPowerSeries σ ℚ) (hA : A.constantCoeff = 0) :
    expPS A = (PowerSeries.exp ℚ).subst A := by
  ext m
  rw [finite_subst A hA]
  change (∑ j ∈ Finset.range (m.degree + 1), _ * _) = _
  simp

private lemma logPS_eq {σ : Type} (A : MvPowerSeries σ ℚ) (hA : A.constantCoeff = 1) :
    logPS A = (PowerSeries.log ℚ).subst (A-1) := by
  ext m
  rw [finite_subst (A-1) (by simp [hA])]
  change (∑ j ∈ Finset.Icc 1 m.degree, _ * _) = _
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m.degree+1)) (fun j => 0 < j)]
  have heq : (Finset.range (m.degree+1)).filter (fun j => 0 < j) = Finset.Icc 1 m.degree := by
    ext j; simp; omega
  rw [heq]
  have hzero : ∑ j ∈ (Finset.range (m.degree+1)).filter (fun j => ¬ 0 < j),
      PowerSeries.coeff j (PowerSeries.log ℚ) * MvPowerSeries.coeff m ((A-1)^j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have : j = 0 := by have := (Finset.mem_filter.mp hj).2; omega
    simp [this]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [show j ≠ 0 by have := (Finset.mem_Icc.mp hj).1; omega]

private lemma pow_congr_off {σ : Type} (U : Set (σ →₀ ℕ)) (hU : IsUpClosed U)
    (F G : MvPowerSeries σ ℚ)
    (h : ∀ m ∉ U, MvPowerSeries.coeff m F = MvPowerSeries.coeff m G)
    (n : ℕ) : ∀ m ∉ U, MvPowerSeries.coeff m (F^n) = MvPowerSeries.coeff m (G^n) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    intro m hm
    simp only [pow_succ, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨a,b⟩ hab
    have hsum : a+b=m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have ha : a ∉ U := fun hu => hm (hsum ▸ hU a hu b)
    have hb : b ∉ U := fun hu => hm ((add_comm a b ▸ hsum) ▸ hU b hu a)
    rw [ih a ha, h b hb]

end ExpLogProof
open ExpLogProof
theorem solution {σ : Type} (U : Set (σ →₀ ℕ)) (hU : IsUpClosed U)
    (Z : MvPowerSeries σ ℚ) (hZ : MvPowerSeries.constantCoeff Z = 1) :
    discard U (expPS (discard U (logPS Z))) = discard U Z := by
  classical
  have hz : (Z-1).constantCoeff = 0 := by simp [hZ]
  have hl : (logPS Z).constantCoeff = 0 := by
    rw [logPS_eq Z hZ]
    exact PowerSeries.constantCoeff_subst_eq_zero hz _ PowerSeries.constantCoeff_log
  have hi : expPS (logPS Z) = Z := by
    rw [expPS_eq _ hl, logPS_eq _ hZ, ← PowerSeries.subst_comp_subst_apply
      PowerSeries.HasSubst.log (PowerSeries.HasSubst.of_constantCoeff_zero hz), exp_at_log]
    rw [← PowerSeries.coe_substAlgHom (.of_constantCoeff_zero hz)]
    simp [PowerSeries.substAlgHom_X]
  ext m
  change (if m ∈ U then 0 else _) = (if m ∈ U then 0 else _)
  split_ifs with hm
  · rfl
  · conv_rhs => rw [←hi]
    change (∑ j ∈ Finset.range (m.degree+1), _ * _) = (∑ j ∈ Finset.range (m.degree+1), _ * _)
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply pow_congr_off U hU _ _ _ j m hm
    intro a ha
    change (if a ∈ U then 0 else _) = _
    simp [ha]
