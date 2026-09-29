-- Prove2me | solution 1 for WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/52eb23ab-05e1-58a7-8be7-18d3ca303f4f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_psiSq_eq_zero_of_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial WeierstrassCurve

namespace P2MtkGenKernel

universe u

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
variable {N : ℕ} (Q : W.toAffine.Point)

theorem eq_or_eq_neg_of_x_eq {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ = x₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ ∨
      Affine.Point.some x₁ y₁ h₁ = -Affine.Point.some x₂ y₂ h₂ := by
  subst hx
  rcases Affine.Y_eq_of_X_eq h₁.1 h₂.1 rfl with hy | hy
  · left; subst hy; rfl
  · right
    rw [Affine.Point.neg_some]
    subst hy; rfl

abbrev xOf (P : W.toAffine.Point) : F := (P.coordsOrZero).1

theorem xOf_some {x y : F} (h : W.toAffine.Nonsingular x y) : xOf W (Affine.Point.some x y h) = x := rfl

theorem xOf_neg (P : W.toAffine.Point) : xOf W (-P) = xOf W P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

theorem eq_or_eq_neg_of_xOf_eq {P P' : W.toAffine.Point} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (hx : xOf W P = xOf W P') : P = P' ∨ P = -P' := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨x', y', h'⟩
  · exact absurd rfl hP'
  exact eq_or_eq_neg_of_x_eq W h h' hx

theorem nsmul_ne_zero (hQ : addOrderOf Q = N) {k : ℕ} (hk : ¬ N ∣ k) : k • Q ≠ 0 := by
  intro h
  apply hk
  rw [← hQ]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h

theorem eq_of_xOf_nsmul_eq (hQ : addOrderOf Q = N) {k k' : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k < N)
    (hk1' : 1 ≤ k') (hk' : 2 * k' < N)
    (hx : xOf W (k • Q) = xOf W (k' • Q)) : k = k' := by
  have hkN : ¬ N ∣ k := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hkN' : ¬ N ∣ k' := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  rcases eq_or_eq_neg_of_xOf_eq W (nsmul_ne_zero W Q hQ hkN) (nsmul_ne_zero W Q hQ hkN') hx with h | h
  · have hz : ((k : ℤ) - k') • Q = 0 := by rw [sub_zsmul, natCast_zsmul, natCast_zsmul, h]; abel
    have hd : ((addOrderOf Q : ℕ) : ℤ) ∣ (k : ℤ) - k' := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
    rw [hQ] at hd
    have habs : |((k : ℤ) - k')| < N := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  · have hz : (k + k') • Q = 0 := by rw [add_nsmul, h, neg_add_cancel]
    have hd : N ∣ k + k' := by rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    have := Nat.le_of_dvd (by omega) hd
    omega

theorem ne_zero_of_isCoprime_of_eval_eq {f g : F[X]} (hfg : IsCoprime f g) {x : F} (hg : g.eval x = 0) :
    f.eval x ≠ 0 := by
  intro hf
  obtain ⟨u, v, huv⟩ := hfg
  have := congrArg (Polynomial.eval x) huv
  rw [eval_add, eval_mul, eval_mul, hf, hg, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

theorem PsiSq_ne_zero_and_Phi_eq {x y : F} (h : W.toAffine.Nonsingular x y) (m : ℕ)
    (hm : m • Affine.Point.some x y h ≠ 0) :
    (W.ΨSq (m : ℤ)).eval x ≠ 0 ∧
      (W.Φ (m : ℤ)).eval x = xOf W (m • Affine.Point.some x y h) * (W.ΨSq (m : ℤ)).eval x := by
  generalize hP' : m • Affine.Point.some x y h = P' at hm
  rcases P' with _ | ⟨x', y', h'⟩
  · exact absurd rfl hm
  have hz : (m : ℤ) • Affine.Point.some x y h = Affine.Point.some x' y' h' := by
    rw [natCast_zsmul, hP']
  have hform := Affine.Point.zsmul_x_mul_psi_sq W (m : ℤ) h h' hz
  rw [Affine.evalEval_psi_sq W h.1, Affine.evalEval_phi W h.1] at hform
  refine ⟨fun h0 => ?_, ?_⟩
  · apply ne_zero_of_isCoprime_of_eval_eq (WeierstrassCurve.isCoprime_Phi_PsiSq W (m : ℤ)) h0
    rw [← hform, h0, mul_zero]
  · rw [xOf_some, ← hform]

theorem prePsi_eval_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y) (m : ℕ)
    (hm : m • Affine.Point.some x y h ≠ 0) : (W.preΨ (m : ℤ)).eval x ≠ 0 := by
  intro h0
  apply (PsiSq_ne_zero_and_Phi_eq W h m hm).1
  simp only [WeierstrassCurve.ΨSq, eval_mul, eval_pow, h0]
  ring

theorem prePsi_eval_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y) (M : ℕ)
    (hM : M • Affine.Point.some x y h = 0) (h2 : 2 • Affine.Point.some x y h ≠ 0) :
    (W.preΨ (M : ℤ)).eval x = 0 := by
  have hΨ := Affine.Point.eval_psiSq_eq_zero_of_smul_eq_zero (W := W) (n := (M : ℤ)) h
    (by rw [natCast_zsmul]; exact hM)
  have h2' := (PsiSq_ne_zero_and_Phi_eq W h 2 h2).1
  rw [show ((2 : ℕ) : ℤ) = 2 from rfl, WeierstrassCurve.ΨSq_two] at h2'
  simp only [WeierstrassCurve.ΨSq, eval_mul, eval_pow] at hΨ
  split_ifs at hΨ
  · rcases mul_eq_zero.mp hΨ with h0 | h0
    · exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h0
    · exact absurd h0 h2'
  · rw [eval_one, mul_one] at hΨ
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hΨ

variable (p : ℕ) [Fact p.Prime]

theorem exists_mem_xOf_nsmul_eq (hQ : addOrderOf Q = N) (hpN : p ∣ N) (hN : 0 < N) {m : ℕ}
    (hm : ¬ p ∣ m) :
    ∃ r ∈ (Finset.Icc 1 (N / 2)).filter (fun a => ¬ p ∣ a), xOf W (m • Q) = xOf W (r • Q) := by
  set r := m % N with hr
  have hmN : ¬ N ∣ m := fun h => hm (dvd_trans hpN h)
  have hr0 : r ≠ 0 := fun h => hmN (Nat.dvd_of_mod_eq_zero h)
  have hrN : r < N := Nat.mod_lt m hN
  have hNQ : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hm' : m = m / N * N + r := by rw [hr, Nat.div_add_mod']
  have hmr : m • Q = r • Q := by
    rw [hm', add_nsmul, mul_nsmul', hNQ, nsmul_zero, zero_add]
  have hpr : ¬ p ∣ r := by
    intro h
    apply hm
    rw [hm']
    exact dvd_add (dvd_mul_of_dvd_right hpN _) h
  by_cases hrn : r ≤ N / 2
  · refine ⟨r, ?_, by rw [hmr]⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.pos_of_ne_zero hr0, hrn⟩, hpr⟩
  · refine ⟨N - r, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, fun h => hpr ?_⟩
      exact (Nat.dvd_add_right h).mp (by rwa [Nat.sub_add_cancel hrN.le])
    · have hneg : (N - r) • Q = -(r • Q) := by
        rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hrN.le, hNQ]
      rw [hmr, hneg, xOf_neg]

variable (k : ℕ)

theorem two_mul_lt_of_mem (hk : 0 < k) (hN2 : p ^ k ≠ 2) {a : ℕ}
    (ha : a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)) :
    1 ≤ a ∧ 2 * a < p ^ k ∧ ¬ p ∣ a := by
  have hp : p.Prime := Fact.out
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha
  obtain ⟨⟨ha1, ha2⟩, hpa⟩ := ha
  refine ⟨ha1, ?_, hpa⟩
  have h2a : 2 * a ≤ p ^ k := by omega
  rcases h2a.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hpdvd : p ∣ 2 * a := heq ▸ dvd_pow_self p hk.ne'
    rcases hp.dvd_mul.mp hpdvd with h2 | h2
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst hp2
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        subst hk1
        exact hN2 rfl
      apply hpa
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
      refine ⟨2 ^ j, ?_⟩
      have : 2 ^ (2 + j) = 2 * (2 * 2 ^ j) := by ring
      omega
    · exact hpa h2

theorem card_filter_eq (hk : 0 < k) (hN2 : p ^ k ≠ 2) :
    ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)).card = Nat.totient (p ^ k) / 2 := by
  have hp : p.Prime := Fact.out
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 (p ^ k / 2)) (p := fun a => p ∣ a)
  have hIcc : (Finset.Icc 1 (p ^ k / 2)).card = p ^ k / 2 := by simp
  have hdvd : ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => p ∣ a)).card = p ^ k / 2 / p := by
    rw [show Finset.Icc 1 (p ^ k / 2) = Finset.Ioc 0 (p ^ k / 2) by ext a; simp; omega]
    exact Nat.Ioc_filter_dvd_card_eq_div _ p
  rw [hIcc, hdvd] at hsplit
  have hcard : ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)).card = p ^ k / 2 - p ^ k / 2 / p := by
    omega
  rw [hcard, Nat.totient_prime_pow hp hk]

  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel]
  have hN : p ^ (j + 1) = p * p ^ j := by rw [pow_succ, mul_comm]
  rw [hN]
  rw [hN] at hN2
  rcases hp.eq_two_or_odd' with rfl | hodd
  ·
    have hj : j ≠ 0 := by rintro rfl; exact hN2 (by norm_num)
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ j = 2 * t :=
      ⟨2 ^ (j - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hj)]⟩
    rw [ht]
    omega
  · obtain ⟨s, hs⟩ := hodd
    have hqodd : Odd (p ^ j) := Odd.pow ⟨s, hs⟩
    obtain ⟨t, ht⟩ := hqodd
    rw [ht, hs]
    have h1 : (2 * s + 1) * (2 * t + 1) / 2 = 2 * (s * t) + s + t := by
      rw [show (2 * s + 1) * (2 * t + 1) = 1 + 2 * (2 * (s * t) + s + t) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
      norm_num
    have h2 : (2 * (s * t) + s + t) / (2 * s + 1) = t := by
      rw [show 2 * (s * t) + s + t = s + (2 * s + 1) * t by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
    have h3 : (2 * t + 1) * (2 * s + 1 - 1) / 2 = 2 * (s * t) + s := by
      rw [Nat.add_sub_cancel, show (2 * t + 1) * (2 * s) = 2 * (2 * (s * t) + s) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h1, h2, h3]
    omega

def genKer : F[X] :=
  ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C (xOf W (a • Q)))

theorem monic_genKer : (genKer W Q p k).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C _

theorem natDegree_genKer :
    (genKer W Q p k).natDegree = ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)).card := by
  rw [genKer, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C _]
  simp

theorem genKer_dvd_of_eval_eq_zero (hQ : addOrderOf Q = p ^ k) (hk : 0 < k) (hN2 : p ^ k ≠ 2) (g : F[X])
    (hg : ∀ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), g.eval (xOf W (a • Q)) = 0) :
    genKer W Q p k ∣ g := by
  apply Finset.prod_dvd_of_coprime
  · intro a ha a' ha' haa'
    obtain ⟨ha1, ha2, _⟩ := two_mul_lt_of_mem p k hk hN2 ha
    obtain ⟨ha1', ha2', _⟩ := two_mul_lt_of_mem p k hk hN2 ha'
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    intro hx
    exact haa' (eq_of_xOf_nsmul_eq W Q hQ ha1 ha2 ha1' ha2' hx)
  · intro a ha
    rw [dvd_iff_isRoot, IsRoot.def]
    exact hg a ha

theorem isCoprime_genKer_of_eval_ne_zero (g : F[X])
    (hg : ∀ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), g.eval (xOf W (a • Q)) ≠ 0) :
    IsCoprime (genKer W Q p k) g := by
  apply IsCoprime.prod_left
  intro a ha
  refine (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr fun hd => hg a ha ?_
  rwa [dvd_iff_isRoot, IsRoot.def] at hd

theorem main (hQ : addOrderOf Q = p ^ k) (hN2 : p ^ k ≠ 2) :
    W.IsCyclicGenKernel p k (genKer W Q p k) := by
  have hp : p.Prime := Fact.out
  rcases Nat.eq_zero_or_pos k with rfl | hk
  ·
    have hS : (Finset.Icc 1 (p ^ 0 / 2)).filter (fun a => ¬ p ∣ a) = ∅ := by simp
    have h1 : genKer W Q p 0 = 1 := by rw [genKer, hS, Finset.prod_empty]
    rw [h1]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · simp
    · intro a ha ha'
      simp at ha'
      omega

  have hN0 : 0 < p ^ k := pow_pos hp.pos k
  have hpN : p ∣ p ^ k := dvd_pow_self p hk.ne'
  have hNQ : (p ^ k) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hcard := card_filter_eq p k hk hN2
  have hdeg : (genKer W Q p k).natDegree = Nat.totient (p ^ k) / 2 := by rw [natDegree_genKer, hcard]

  have key : ∀ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
      ∃ (x y : F) (h : W.toAffine.Nonsingular x y), a • Q = Affine.Point.some x y h ∧
        (∀ m : ℕ, ¬ p ∣ m → m • Affine.Point.some x y h ≠ 0) ∧
        (p ^ (k - 1)) • Affine.Point.some x y h ≠ 0 ∧
        (p ^ k) • Affine.Point.some x y h = 0 ∧
        2 • Affine.Point.some x y h ≠ 0 := by
    intro a ha
    obtain ⟨ha1, ha2, hpa⟩ := two_mul_lt_of_mem p k hk hN2 ha
    have haN : ¬ p ^ k ∣ a := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    have hne := nsmul_ne_zero W Q hQ haN
    generalize hP : a • Q = P at hne
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hne
    refine ⟨x, y, h, rfl, ?_, ?_, ?_, ?_⟩
    · intro m hm
      rw [← hP, ← mul_nsmul']
      refine nsmul_ne_zero W Q hQ fun hd => ?_
      have : p ∣ m * a := dvd_trans hpN hd
      rcases hp.dvd_mul.mp this with h1 | h1
      · exact hm h1
      · exact hpa h1
    · rw [← hP, ← mul_nsmul']
      refine nsmul_ne_zero W Q hQ fun hd => hpa ?_
      have hd' : p ^ (k - 1) * p ∣ p ^ (k - 1) * a := by
        rwa [← pow_succ, Nat.sub_add_cancel hk]
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos _)).mp hd'
    · rw [← hP, ← mul_nsmul, mul_comm, mul_nsmul, hNQ, nsmul_zero]
    · rw [← hP, ← mul_nsmul]
      refine nsmul_ne_zero W Q hQ fun hd => ?_
      have := Nat.le_of_dvd (by omega) hd
      omega
  refine ⟨hdeg.le, ?_, ?_, ?_⟩
  ·
    have := (monic_genKer W Q p k).coeff_natDegree
    rwa [hdeg] at this
  ·
    have hdvd1 : genKer W Q p k ∣ W.preΨ ((p ^ k : ℕ) : ℤ) := by
      refine genKer_dvd_of_eval_eq_zero W Q p k hQ hk hN2 _ fun a ha => ?_
      obtain ⟨x, y, h, hP, -, -, hNP, h2P⟩ := key a ha
      rw [hP, xOf_some]
      exact prePsi_eval_eq_zero W h (p ^ k) hNP h2P
    have hdvd2 : W.preΨ ((p ^ (k - 1) : ℕ) : ℤ) ∣ W.preΨ ((p ^ k : ℕ) : ℤ) :=
      W.prePsi_dvd_prePsi_of_dvd (by exact_mod_cast pow_dvd_pow p (Nat.sub_le k 1))
    have hcop : IsCoprime (genKer W Q p k) (W.preΨ ((p ^ (k - 1) : ℕ) : ℤ)) := by
      refine isCoprime_genKer_of_eval_ne_zero W Q p k _ fun a ha => ?_
      obtain ⟨x, y, h, hP, -, hpk, -, -⟩ := key a ha
      rw [hP, xOf_some]
      exact prePsi_eval_ne_zero W h (p ^ (k - 1)) hpk
    have := hcop.mul_dvd hdvd1 hdvd2
    push_cast at this
    exact this
  ·
    intro b hb2 hb hpb
    refine genKer_dvd_of_eval_eq_zero W Q p k hQ hk hN2 _ fun a ha => ?_
    obtain ⟨x, y, h, hP, hm, -, -, -⟩ := key a ha
    obtain ⟨hΨ, hΦ⟩ := PsiSq_ne_zero_and_Phi_eq W h b (hm b hpb)
    have hba : b • Affine.Point.some x y h = (b * a) • Q := by rw [mul_nsmul', hP]
    obtain ⟨_, _, hpa⟩ := two_mul_lt_of_mem p k hk hN2 ha
    have hpba : ¬ p ∣ b * a := fun hd => (hp.dvd_mul.mp hd).elim hpb hpa
    obtain ⟨r, hr, hxr⟩ := exists_mem_xOf_nsmul_eq W Q p hQ hpN hN0 hpba
    rw [hba, hxr] at hΦ
    rw [hP, xOf_some]
    set d := Nat.totient (p ^ k) / 2 with hd
    set hpol := genKer W Q p k with hh
    set s := (W.ΨSq (b : ℤ)).eval x with hs
    set x' := xOf W (r • Q) with hx'
    have heval : (W.smulNumerator b d hpol).eval x =
        s ^ d * ∑ i ∈ Finset.range (d + 1), hpol.coeff i * x' ^ i := by
      rw [WeierstrassCurve.smulNumerator, eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [eval_mul, eval_mul, eval_C, eval_pow, eval_pow, hΦ, mul_pow]
      have : s ^ d = s ^ i * s ^ (d - i) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [this]; ring
    have hroot : hpol.eval x' = 0 := by
      rw [hh, genKer, eval_prod]
      exact Finset.prod_eq_zero hr (by rw [eval_sub, eval_X, eval_C, sub_self])
    rw [heval, ← eval_eq_sum_range' (by rw [hdeg]; exact Nat.lt_succ_self d) x', hroot, mul_zero]

theorem isTwoKernel (hQ : addOrderOf Q = 2) : W.IsTwoKernel (X - C (xOf W Q)) := by
  have hne : Q ≠ 0 := by
    intro h; rw [h, addOrderOf_zero] at hQ; exact absurd hQ (by norm_num)
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hne
  refine ⟨(natDegree_X_sub_C _).le, by simp [coeff_sub, coeff_X_one], ?_⟩
  rw [xOf_some, dvd_iff_isRoot, IsRoot.def, ← WeierstrassCurve.ΨSq_two,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
  refine Affine.Point.eval_psiSq_eq_zero_of_smul_eq_zero (W := W) h ?_
  rw [natCast_zsmul, ← hQ]
  exact addOrderOf_nsmul_eq_zero _

theorem isGamma0PowAt (hQ : addOrderOf Q = p ^ k) :
    ModularCurve.IsGamma0PowAt W p k (genKer W Q p k) := by
  have hp : p.Prime := Fact.out
  by_cases hN2 : p ^ k = 2
  · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two W hN2]
    have hk : k ≠ 0 := by rintro rfl; simp at hN2
    have hp2 : p = 2 := by
      have : p ∣ 2 := hN2 ▸ dvd_pow_self p hk
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    subst hp2
    have hk1 : k = 1 := Nat.pow_right_injective (le_refl 2) (hN2.trans (pow_one 2).symm)
    subst hk1
    have hS : (Finset.Icc 1 (2 ^ 1 / 2)).filter (fun a => ¬ 2 ∣ a) = {1} := by decide
    rw [genKer, hS, Finset.prod_singleton, one_nsmul]
    exact isTwoKernel W Q (by rw [hQ]; norm_num)
  · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two W hN2]
    exact main W Q p k hQ hN2

theorem eq_genKer_of_isRoot (h : F[X]) (hh : W.IsCyclicGenKernel p k h)
    (hQ : addOrderOf Q = p ^ k) (hpk : 3 ≤ p ^ k)
    {x y : F} (hxy : W.toAffine.Nonsingular x y) (hQe : Q = Affine.Point.some x y hxy) (hroot : h.eval x = 0) :
    h = genKer W Q p k := by
  have hp : p.Prime := Fact.out
  have hN2 : p ^ k ≠ 2 := by omega
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hpk
    · exact hk
  have hN0 : 0 < p ^ k := pow_pos hp.pos k
  have hpN : p ∣ p ^ k := dvd_pow_self p hk.ne'
  have hcard := card_filter_eq p k hk hN2
  set d := Nat.totient (p ^ k) / 2 with hd

  have hmon : h.Monic := hh.monic
  have hdegh : h.natDegree = d := by
    refine le_antisymm hh.natDegree_le ?_
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hh.coeff_eq_one]; exact one_ne_zero)

  have hQne : ∀ m : ℕ, ¬ p ∣ m → m • Q ≠ 0 := by
    intro m hm
    refine nsmul_ne_zero W Q hQ fun hd' => hm (dvd_trans hpN hd')
  have hroots : ∀ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), h.eval (xOf W (a • Q)) = 0 := by
    intro a ha
    obtain ⟨ha1, ha2, hpa⟩ := two_mul_lt_of_mem p k hk hN2 ha
    rcases Nat.eq_or_lt_of_le ha1 with h1 | h1
    · rw [← h1, one_nsmul, hQe, xOf_some]; exact hroot
    ·
      have hdv := hh.dvd_smulNumerator a (by omega) (by omega) hpa
      have hmQ : a • Affine.Point.some x y hxy ≠ 0 := by rw [← hQe]; exact hQne a hpa
      obtain ⟨hΨ, hΦ⟩ := PsiSq_ne_zero_and_Phi_eq W hxy a hmQ
      rw [← hQe] at hΦ
      set s := (W.ΨSq (a : ℤ)).eval x with hs
      set x' := xOf W (a • Q) with hx'
      have heval : (W.smulNumerator a d h).eval x =
          s ^ d * ∑ i ∈ Finset.range (d + 1), h.coeff i * x' ^ i := by
        rw [WeierstrassCurve.smulNumerator, eval_finsetSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [eval_mul, eval_mul, eval_C, eval_pow, eval_pow, hΦ, mul_pow]
        have : s ^ d = s ^ i * s ^ (d - i) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        rw [this]; ring
      have hzero : (W.smulNumerator a d h).eval x = 0 := by
        obtain ⟨c, hc⟩ := hdv
        rw [hc, eval_mul, hroot, zero_mul]
      rw [heval, ← eval_eq_sum_range' (by rw [hdegh]; exact Nat.lt_succ_self d) x'] at hzero
      rcases mul_eq_zero.mp hzero with h0 | h0
      · exact absurd (pow_eq_zero_iff'.mp h0).1 hΨ
      · exact h0

  have hdvd : genKer W Q p k ∣ h := genKer_dvd_of_eval_eq_zero W Q p k hQ hk hN2 h hroots
  have hdegG : (genKer W Q p k).natDegree = d := by rw [natDegree_genKer, hcard]
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (monic_genKer W Q p k) hmon hdvd (by rw [hdegh, hdegG])

end P2MtkGenKernel

end

universe u

open Polynomial in

theorem solution
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) [W.IsElliptic]
    (p k : ℕ) [Fact p.Prime] (hp : (p : Ω) ≠ 0) (hpk : 3 ≤ p ^ k)
    (h : Polynomial Ω) (hh : W.IsCyclicGenKernel p k h)
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = p ^ k) (hroot : ∃ (x y : Ω) (hxy : W.toAffine.Nonsingular x y),
      Q = WeierstrassCurve.Affine.Point.some x y hxy ∧ h.IsRoot x) :
    h = ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C ((a • Q).coordsOrZero).1) := by
  obtain ⟨x, y, hxy, hQe, hr⟩ := hroot
  exact P2MtkGenKernel.eq_genKer_of_isRoot W Q p k h hh hQ hpk hxy hQe hr

end S_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul
end P2MW
export P2MW.S_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul (solution)
