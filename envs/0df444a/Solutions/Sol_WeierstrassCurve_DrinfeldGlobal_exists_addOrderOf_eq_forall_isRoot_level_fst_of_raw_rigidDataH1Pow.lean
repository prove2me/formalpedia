-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a55274d0-b35f-5261-ac37-13ce5b5e1810

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_psiSq_eq_zero_of_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace GenKerSol

p2m_open "ModularCurve WeierstrassCurve~evalEval_ψ_sq WeierstrassCurve.Affine Polynomial"

variable {K : Type} [Field K] [DecidableEq K]

def xco {W : WeierstrassCurve.Affine K} : W.Point → K
  | 0 => 0
  | .some x _ _ => x

@[scoped simp] theorem xco_some {W : WeierstrassCurve.Affine K} (x y : K) (h : W.Nonsingular x y) :
    xco (Point.some x y h) = x := rfl

theorem xco_neg {W : WeierstrassCurve.Affine K} (P : W.Point) : xco (-P) = xco P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]; rfl

theorem eq_or_eq_neg_of_xco_eq {W : WeierstrassCurve.Affine K} {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : xco P = xco Q) : Q = P ∨ Q = -P := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ
  simp only [xco_some] at h
  subst h
  rcases Y_eq_of_X_eq h₂.left h₁.left rfl with hy | hy
  · left; subst hy; rfl
  · right
    rw [Point.neg_some]
    subst hy; rfl

theorem exists_eq_some_of_ne_zero {W : WeierstrassCurve.Affine K} {P : W.Point} (hP : P ≠ 0) :
    ∃ (y : K) (h : W.Nonsingular (xco P) y), P = Point.some (xco P) y h := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨y, h, rfl⟩

theorem card_filter_xco_le_two {W : WeierstrassCurve.Affine K} (S : Finset W.Point) (hS : ∀ P ∈ S, P ≠ 0) (b : K) :
    (S.filter (fun P => xco P = b)).card ≤ 2 := by
  classical
  by_cases hne : (S.filter (fun P => xco P = b)).Nonempty
  · obtain ⟨P₀, hP₀⟩ := hne
    have hsub : S.filter (fun P => xco P = b) ⊆ ({P₀, -P₀} : Finset W.Point) := by
      intro Q hQ
      rw [Finset.mem_filter] at hQ hP₀
      have hx : xco P₀ = xco Q := by rw [hQ.2, hP₀.2]
      rcases eq_or_eq_neg_of_xco_eq (hS _ hP₀.1) (hS _ hQ.1) hx with h | h
      · simp [h]
      · simp [h]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

section OnCurve

variable (W : WeierstrassCurve K)

theorem exists_nonsingular [IsAlgClosed K] [W.IsElliptic] (x₀ : K) : ∃ y₀ : K, W.toAffine.Nonsingular x₀ y₀ := by
  set b : K := W.a₁ * x₀ + W.a₃ with hb
  set c : K := x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ with hc
  set f : K[X] := X ^ 2 + (C b * X - C c) with hf
  have hlt : (C b * X - C c).degree < ((X : K[X]) ^ 2).degree := by
    rw [degree_X_pow]
    refine (degree_sub_le _ _).trans_lt ?_
    refine max_lt ?_ ?_
    · exact (degree_C_mul_X_le b).trans_lt (by exact_mod_cast Nat.lt_succ_self 1)
    · exact (degree_C_le).trans_lt (by exact_mod_cast Nat.zero_lt_two)
  have hdeg : f.degree = 2 := by
    rw [hf, degree_add_eq_left_of_degree_lt hlt, degree_X_pow]; rfl
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root f (by rw [hdeg]; exact two_ne_zero)
  refine ⟨y₀, (equation_iff_nonsingular).mp ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [IsRoot, hf] at hy₀
  simp only [eval_add, eval_pow, eval_X, eval_sub, eval_mul, eval_C] at hy₀
  rw [hb, hc] at hy₀
  linear_combination hy₀

theorem evalEval_ψ_sq (n : ℤ) {x y : K} (hxy : W.toAffine.Equation x y) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h1 : (Affine.CoordinateRing.mk W) ((W.ψ n) ^ 2) = (Affine.CoordinateRing.mk W) (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨r, hr⟩ := (AdjoinRoot.mk_eq_mk).mp h1
  have h2 := congrArg (Polynomial.evalEval x y) hr
  rw [evalEval_sub, evalEval_pow, evalEval_C, evalEval_mul] at h2
  have h3 : Polynomial.evalEval x y (WeierstrassCurve.Affine.polynomial W) = 0 := hxy
  rw [h3, zero_mul, sub_eq_zero] at h2
  exact h2

theorem eval_ΨSq_ne_zero_of_zsmul_ne_zero [W.IsElliptic] (n : ℤ) {x y : K} (hxy : W.toAffine.Nonsingular x y)
    (hn : n • (Point.some x y hxy : W.toAffine.Point) ≠ 0) : (W.ΨSq n).eval x ≠ 0 := by
  intro h0
  apply hn
  rw [WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W hxy n]
  have := evalEval_ψ_sq W n hxy.left
  rw [h0] at this
  exact pow_eq_zero_iff two_ne_zero |>.mp this

theorem eval_preΨ'_eq_zero_of_nsmul_eq_zero [W.IsElliptic] {m : ℕ} {x y : K} (hxy : W.toAffine.Nonsingular x y)
    (hm : m • (Point.some x y hxy : W.toAffine.Point) = 0) (h2 : 2 • (Point.some x y hxy : W.toAffine.Point) ≠ 0) :
    (W.preΨ' m).eval x = 0 := by
  have h1 : ((m : ℤ)) • (Point.some x y hxy : W.toAffine.Point) = 0 := by rw [natCast_zsmul]; exact hm
  have h3 := WeierstrassCurve.Affine.Point.eval_psiSq_eq_zero_of_smul_eq_zero hxy h1
  rw [WeierstrassCurve.ΨSq_ofNat, eval_mul, eval_pow] at h3
  have h4 : W.Ψ₂Sq.eval x ≠ 0 := by
    intro h5
    exact h2 ((WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff W hxy).mpr h5)
  split_ifs at h3 with he
  · exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h3).resolve_right h4)
  · rw [eval_one, mul_one] at h3
    exact pow_eq_zero_iff two_ne_zero |>.mp h3

end OnCurve

section Roots

variable (W : WeierstrassCurve K)

theorem natCard_torsion [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card {P : W.toAffine.Point // n • P = 0} = n ^ 2 := by
  have h := WeierstrassCurve.card_torsion_of_isAlgClosed (F := K) (K := K) W hn
  have h' : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) = n ^ 2 := h
  rw [← h']
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

theorem exists_torsion_finset [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    ∃ T : Finset W.toAffine.Point, (∀ P, P ∈ T ↔ n • P = 0) ∧ T.card = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have hc := natCard_torsion W hn
  have hfin : {P : W.toAffine.Point | n • P = 0}.Finite := by
    have : Finite {P : W.toAffine.Point // n • P = 0} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 hn0)
    exact Set.finite_coe_iff.mp this
  refine ⟨hfin.toFinset, fun P => by simp, ?_⟩
  rw [← Nat.card_eq_card_finite_toFinset hfin]
  exact hc

theorem preΨ'_roots [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    (∀ x₀ : K, (W.preΨ' n).IsRoot x₀ →
      ∃ (y₀ : K) (h₀ : W.toAffine.Nonsingular x₀ y₀),
        n • (Point.some x₀ y₀ h₀ : W.toAffine.Point) = 0 ∧ 2 • (Point.some x₀ y₀ h₀ : W.toAffine.Point) ≠ 0) ∧
    (W.preΨ' n).roots.Nodup := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  obtain ⟨T, hT, hTc⟩ := exists_torsion_finset W hn

  set Pts : Finset W.toAffine.Point := T.filter (fun P => 2 • P ≠ 0) with hPts
  have hPtsmem : ∀ P, P ∈ Pts ↔ n • P = 0 ∧ 2 • P ≠ 0 := by
    intro P; rw [hPts, Finset.mem_filter, hT]
  have hPtsne : ∀ P ∈ Pts, P ≠ 0 := by
    intro P hP h0; rw [hPtsmem] at hP; exact hP.2 (by rw [h0, smul_zero])

  set c : ℕ := if Even n then 4 else 1 with hc
  have hkill : (T.filter (fun P => ¬ (2 • P ≠ 0))).card = c := by
    by_cases he : Even n
    · rw [hc, if_pos he]
      obtain ⟨m, rfl⟩ := he
      have h2 : ((2 : ℕ) : K) ≠ 0 := by
        rw [Nat.cast_ofNat]
        intro h2; apply hn; push_cast; rw [show (m : K) + m = 2 * m by ring, h2, zero_mul]
      obtain ⟨T₂, hT₂, hT₂c⟩ := exists_torsion_finset W h2
      have : T.filter (fun P => ¬ (2 • P ≠ 0)) = T₂ := by
        ext P
        rw [Finset.mem_filter, hT, hT₂, not_not]
        constructor
        · exact fun h => h.2
        · intro h; refine ⟨?_, h⟩
          rw [show m + m = m * 2 by ring, mul_nsmul', h, smul_zero]
      rw [this, hT₂c]; norm_num
    · rw [hc, if_neg he]
      have hodd : Odd n := Nat.not_even_iff_odd.mp he
      have : T.filter (fun P => ¬ (2 • P ≠ 0)) = {0} := by
        ext P
        rw [Finset.mem_filter, hT, not_not, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩
          have hd1 : addOrderOf P ∣ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h1
          have hd2 : addOrderOf P ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
          have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hodd
          have : addOrderOf P ∣ 1 := by
            rw [← hcop]; exact Nat.dvd_gcd hd2 hd1
          exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
        · rintro rfl; simp
      rw [this, Finset.card_singleton]
  have hcle : c ≤ n ^ 2 := by
    rw [hc]; split_ifs with he
    · obtain ⟨m, rfl⟩ := he
      have : m ≠ 0 := by rintro rfl; exact hn0 rfl
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr this
      nlinarith
    · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hn0)
  have hPtsc : Pts.card = n ^ 2 - c := by
    have := Finset.card_filter_add_card_filter_not (s := T) (fun P => 2 • P ≠ 0)
    rw [hkill, hTc, ← hPts] at this
    omega

  set Xs : Finset K := Pts.image xco with hXs
  have hXsc : Pts.card ≤ 2 * Xs.card :=
    Finset.card_le_mul_card_image _ 2 (fun b _ => card_filter_xco_le_two Pts hPtsne b)
  have hXsroot : ∀ b ∈ Xs, (W.preΨ' n).IsRoot b := by
    intro b hb
    rw [hXs, Finset.mem_image] at hb
    obtain ⟨P, hP, rfl⟩ := hb
    obtain ⟨y, hxy, hPe⟩ := exists_eq_some_of_ne_zero (hPtsne P hP)
    rw [hPtsmem] at hP
    rw [hPe] at hP
    exact eval_preΨ'_eq_zero_of_nsmul_eq_zero W hxy hP.1 hP.2

  have hne : W.preΨ' n ≠ 0 := WeierstrassCurve.preΨ'_ne_zero W hn
  set R := (W.preΨ' n).roots with hR
  have hsub : Xs ⊆ R.toFinset := by
    intro b hb
    rw [Multiset.mem_toFinset, hR, mem_roots hne]
    exact hXsroot b hb
  have hdeg : (W.preΨ' n).natDegree ≤ (n ^ 2 - c) / 2 := WeierstrassCurve.natDegree_preΨ'_le W n
  have hchain : R.toFinset.card ≤ Xs.card :=
    calc R.toFinset.card ≤ R.card := Multiset.toFinset_card_le R
      _ ≤ (W.preΨ' n).natDegree := card_roots' _
      _ ≤ (n ^ 2 - c) / 2 := hdeg
      _ ≤ Xs.card := by rw [← hPtsc]; omega
  have heq : Xs = R.toFinset := Finset.eq_of_subset_of_card_le hsub hchain
  have hnodup : R.Nodup := by
    rw [← Multiset.dedup_card_eq_card_iff_nodup, ← Multiset.card_toFinset]
    refine le_antisymm (Multiset.toFinset_card_le R) ?_
    calc R.card ≤ (W.preΨ' n).natDegree := card_roots' _
      _ ≤ (n ^ 2 - c) / 2 := hdeg
      _ ≤ Xs.card := by rw [← hPtsc]; omega
      _ = R.toFinset.card := by rw [heq]
  refine ⟨?_, hnodup⟩
  intro x₀ hx₀
  have hmem : x₀ ∈ Xs := by
    rw [heq, Multiset.mem_toFinset, hR, mem_roots hne]; exact hx₀
  rw [hXs, Finset.mem_image] at hmem
  obtain ⟨P, hP, hPx⟩ := hmem
  obtain ⟨y, hxy, hPe⟩ := exists_eq_some_of_ne_zero (hPtsne P hP)
  rw [hPtsmem, hPe] at hP
  subst hPx
  exact ⟨y, hxy, hP.1, hP.2⟩

theorem not_sq_dvd_preΨ' [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) (x₀ : K) :
    ¬ (X - C x₀) ^ 2 ∣ W.preΨ' n := by
  classical
  intro hdvd
  have hne : W.preΨ' n ≠ 0 := WeierstrassCurve.preΨ'_ne_zero W hn
  have h2 : 2 ≤ rootMultiplicity x₀ (W.preΨ' n) := (le_rootMultiplicity_iff hne).mpr hdvd
  have hnodup := (preΨ'_roots W hn).2
  have h1 : Multiset.count x₀ (W.preΨ' n).roots ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnodup x₀
  rw [count_roots] at h1
  omega

end Roots

theorem eval_smulNumerator (W : WeierstrassCurve K) (a d : ℕ) (h : K[X]) (hd : h.natDegree ≤ d) (x : K)
    (hψ : (W.ΨSq a).eval x ≠ 0) :
    (W.smulNumerator a d h).eval x = (W.ΨSq a).eval x ^ d * h.eval ((W.Φ a).eval x / (W.ΨSq a).eval x) := by
  set φ : K := (W.Φ a).eval x with hφ
  set ψ : K := (W.ΨSq a).eval x with hψ'
  rw [WeierstrassCurve.smulNumerator, eval_finset_sum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [eval_mul, eval_pow, eval_C]
  rw [← hφ, ← hψ']
  have hi' : i ≤ d := Nat.lt_succ_iff.mp hi
  rw [div_pow, show ψ ^ d = ψ ^ i * ψ ^ (d - i) by rw [← pow_add, Nat.add_sub_cancel' hi']]
  field_simp

section OnePrime

variable (W : WeierstrassCurve K)

theorem nsmul_eq_self_of_addOrderOf_two {P : W.toAffine.Point} (hP : addOrderOf P = 2) {m : ℕ}
    (hm : addOrderOf (m • P) = 2) : m • P = P := by
  rw [← mod_addOrderOf_nsmul P m, hP]
  have h2 : m % 2 < 2 := Nat.mod_lt _ two_pos
  interval_cases hmod : m % 2
  · exfalso
    rw [← mod_addOrderOf_nsmul P m, hP, hmod, zero_smul, addOrderOf_zero] at hm
    exact absurd hm (by norm_num)
  · rw [one_smul]

theorem exists_generator_twoKernel [IsAlgClosed K] [W.IsElliptic] {h : K[X]} (hh : W.IsTwoKernel h) :
    ∃ P : W.toAffine.Point, addOrderOf P = 2 ∧
      ∀ (m : ℕ) (x₁ y₁ : K) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        m • P = Point.some x₁ y₁ h₁ → addOrderOf (m • P) = 2 → h.IsRoot x₁ := by
  have e := eq_X_add_C_of_natDegree_le_one hh.natDegree_le
  rw [hh.coeff_eq_one, map_one, one_mul] at e
  set x₀ : K := - h.coeff 0 with hx₀
  have hroot : h.IsRoot x₀ := by
    rw [IsRoot, e, eval_add, eval_X, eval_C, hx₀, neg_add_cancel]
  have hΨ : W.Ψ₂Sq.eval x₀ = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero hh.dvd_Ψ₂Sq hroot
  obtain ⟨y₀, h₀⟩ := exists_nonsingular W x₀
  set P : W.toAffine.Point := Point.some x₀ y₀ h₀ with hPdef
  have h2P : 2 • P = 0 := (WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff W h₀).mpr hΨ
  have hP0 : P ≠ 0 := Point.some_ne_zero h₀
  have hord : addOrderOf P = 2 := by
    have hd : addOrderOf P ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2P
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hP0
    · exact h2
  refine ⟨P, hord, ?_⟩
  intro m x₁ y₁ h₁ hm hmo
  have := nsmul_eq_self_of_addOrderOf_two W hord hmo
  rw [this, hPdef] at hm
  have hx : x₀ = x₁ := ((Point.some.injEq _ _ _ _ _ _).mp hm).1
  rw [← hx]; exact hroot

theorem sub_nsmul_eq_neg {P : W.toAffine.Point} {q a : ℕ} (hq : q • P = 0) (ha : a ≤ q) : (q - a) • P = -(a • P) := by
  rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel ha, hq]

theorem exists_generator_cyclicGenKernel [IsAlgClosed K] [W.IsElliptic] {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hpK : (p : K) ≠ 0) (hpk2 : 2 < p ^ k) {h : K[X]} (hh : W.IsCyclicGenKernel p k h) :
    ∃ P : W.toAffine.Point, addOrderOf P = p ^ k ∧
      ∀ (m : ℕ) (x₁ y₁ : K) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        m • P = Point.some x₁ y₁ h₁ → addOrderOf (m • P) = p ^ k → h.IsRoot x₁ := by
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = p ^ k := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℕ, d = Nat.totient (p ^ k) / 2 := ⟨_, rfl⟩
  have hqK : (q : K) ≠ 0 := by rw [hqdef]; push_cast; exact pow_ne_zero k hpK

  have hdeg : h.natDegree = d := by
    rw [hddef]
    exact le_antisymm hh.natDegree_le (le_natDegree_of_ne_zero (by rw [hh.coeff_eq_one]; exact one_ne_zero))
  have hmon : h.Monic := hh.monic W
  have hne : h ≠ 0 := hmon.ne_zero
  have hdpos : 0 < d := by
    obtain ⟨e, he⟩ := Nat.totient_even hpk2
    have hpos : 0 < (p ^ k).totient := Nat.totient_pos.mpr (by omega)
    rw [hddef, he]; omega

  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root h (by
    rw [degree_eq_natDegree hne, hdeg]; exact_mod_cast hdpos.ne')

  have hE1' : h * W.preΨ' (p ^ (k - 1)) ∣ W.preΨ' (p ^ k) := by
    have := hh.mul_preΨ_dvd
    rwa [← Nat.cast_pow, ← Nat.cast_pow, WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.preΨ_ofNat] at this
  have hE1 : (W.preΨ' q).IsRoot x₀ := by
    rw [hqdef]
    exact eval_eq_zero_of_dvd_of_eval_eq_zero ((dvd_mul_right h _).trans hE1') hx₀

  obtain ⟨y₀, h₀, hqP, h2P⟩ := (preΨ'_roots W hqK).1 x₀ hE1
  set P : W.toAffine.Point := Point.some x₀ y₀ h₀ with hPdef
  have hP0 : P ≠ 0 := Point.some_ne_zero h₀

  have hord : addOrderOf P = q := by
    have hdvd : addOrderOf P ∣ p ^ k := by rw [← hqdef]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hqP
    obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases Nat.lt_or_ge j k with hlt | hge
    · exfalso
      have hkill : p ^ (k - 1) • P = 0 := by
        apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
        rw [hj]; exact pow_dvd_pow p (by omega)
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · have : k - 1 = 0 := by omega
        rw [this, pow_zero, one_smul] at hkill
        exact hP0 hkill
      · have hpre : (W.preΨ' (p ^ (k - 1))).eval x₀ = 0 := eval_preΨ'_eq_zero_of_nsmul_eq_zero W h₀ hkill h2P
        have hsq : (X - C x₀) ^ 2 ∣ W.preΨ' q := by
          rw [pow_two, hqdef]
          exact (mul_dvd_mul (dvd_iff_isRoot.mpr hx₀) (dvd_iff_isRoot.mpr hpre)).trans hE1'
        exact not_sq_dvd_preΨ' W hqK x₀ hsq
    · have : j = k := le_antisymm hjk hge
      rw [hj, this, hqdef]
  have hq2 : 2 < q := by rw [hqdef]; exact hpk2
  refine ⟨P, hqdef ▸ hord, ?_⟩

  intro m x₁ y₁ h₁ hm hmo
  rw [← hqdef] at hmo
  have hfin : IsOfFinAddOrder P := by
    rw [← addOrderOf_pos_iff, hord]; omega
  have hcop : q.Coprime m := by
    have h1 := hfin.addOrderOf_nsmul P m
    rw [hmo, hord] at h1
    have h2 : q / q.gcd m = q := h1.symm
    rcases Nat.div_eq_self.mp h2 with h3 | h3
    · omega
    · exact h3
  set a : ℕ := m % q with hadef
  have haq : a < q := Nat.mod_lt _ (by omega)
  have haP : a • P = m • P := by rw [hadef, ← hord, mod_addOrderOf_nsmul]
  have hcopa : q.Coprime a := by
    rw [Nat.Coprime, Nat.gcd_comm, hadef, ← Nat.gcd_rec]; exact hcop
  have ha0 : a ≠ 0 := by
    rintro ha0; rw [ha0] at hcopa
    have : q = 1 := by simpa using hcopa
    omega

  have hqP' : q • P = 0 := by rw [← hord]; exact addOrderOf_nsmul_eq_zero P

  have key : ∀ b : ℕ, 0 < b → 2 * b < q → q.Coprime b → h.IsRoot (xco (b • P)) := by
    intro b hb0 hb2 hbq
    have hbP : (b : ℤ) • P ≠ 0 := by
      rw [natCast_zsmul]
      intro h0
      have := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
      rw [hord] at this
      have : q ≤ b := Nat.le_of_dvd hb0 this
      omega
    rcases Nat.lt_or_ge b 2 with hb1 | hb2'
    · have : b = 1 := by omega
      subst this
      rw [one_smul, hPdef, xco_some]; exact hx₀
    ·
      have hpb : ¬ p ∣ b := by
        intro hpb
        have h1 : p ∣ q.gcd b := Nat.dvd_gcd (by rw [hqdef]; exact dvd_pow_self p hk.ne') hpb
        rw [hbq] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      have hble : b ≤ (p ^ k - 1) / 2 := by
        rw [← hqdef]; omega
      have hdle : h.natDegree ≤ d := hdeg.le
      have hst := hh.dvd_smulNumerator b hb2' hble hpb
      rw [← hddef] at hst
      have hΨ : (W.ΨSq b).eval x₀ ≠ 0 := eval_ΨSq_ne_zero_of_zsmul_ne_zero W b h₀ hbP
      have hev : (W.smulNumerator b d h).eval x₀ = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero hst hx₀
      rw [eval_smulNumerator W b d h hdle x₀ hΨ] at hev
      have hroot : h.eval ((W.Φ b).eval x₀ / (W.ΨSq b).eval x₀) = 0 :=
        (mul_eq_zero.mp hev).resolve_left (pow_ne_zero d hΨ)

      have hψ : (W.ψ b).evalEval x₀ y₀ ≠ 0 := by
        intro h0
        exact hbP ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h₀ b).mpr h0)
      obtain ⟨y', h', hbP'⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div W h₀ hψ
      rw [natCast_zsmul] at hbP'
      rw [← hPdef] at hbP'
      rw [hbP', xco_some]
      exact hroot

  have hx₁ : x₁ = xco (m • P) := by rw [hm, xco_some]
  rw [hx₁, ← haP]
  rcases Nat.lt_or_ge (2 * a) q with hlt | hge
  · exact key a (Nat.pos_of_ne_zero ha0) hlt hcopa
  ·
    have hne2 : 2 * a ≠ q := by
      intro h2a
      have h2 : 2 ∣ q := ⟨a, h2a.symm⟩
      have ha : a ∣ q := ⟨2, by omega⟩
      have hg : q.gcd a = a := Nat.gcd_eq_right ha
      rw [Nat.Coprime, hg] at hcopa
      omega
    set b : ℕ := q - a with hbdef
    have hb0 : 0 < b := by omega
    have hb2 : 2 * b < q := by omega
    have hbq : q.Coprime b := by
      rw [hbdef, Nat.Coprime, Nat.gcd_comm]
      exact (Nat.coprime_self_sub_left haq.le).mpr (Nat.coprime_comm.mp hcopa)
    have hneg : b • P = -(a • P) := sub_nsmul_eq_neg W hqP' haq.le
    have := key b hb0 hb2 hbq
    rw [hneg, xco_neg] at this
    exact this

theorem exists_generator_gamma0PowAt [IsAlgClosed K] [W.IsElliptic] {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hpK : (p : K) ≠ 0) {h : K[X]} (hh : IsGamma0PowAt W p k h) :
    ∃ P : W.toAffine.Point, addOrderOf P = p ^ k ∧
      ∀ (m : ℕ) (x₁ y₁ : K) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        m • P = Point.some x₁ y₁ h₁ → addOrderOf (m • P) = p ^ k → h.IsRoot x₁ := by
  by_cases h2 : p ^ k = 2
  · rw [isGamma0PowAt_of_pow_eq_two W h2] at hh
    rw [h2]
    exact exists_generator_twoKernel W hh
  · rw [isGamma0PowAt_of_pow_ne_two W h2] at hh
    have hpk : 2 < p ^ k := by
      have : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
      omega
    exact exists_generator_cyclicGenKernel W hp hk hpK hpk hh

end OnePrime

section Assembly

theorem addOrderOf_sum_eq_prod {G : Type*} [AddCommMonoid G] {ι : Type*} (s : Finset ι) (f : ι → G) (o : ι → ℕ)
    (hf : ∀ i ∈ s, addOrderOf (f i) = o i)
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (o i).Coprime (o j)) :
    addOrderOf (∑ i ∈ s, f i) = ∏ i ∈ s, o i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hco i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    have hcop : (addOrderOf (f a)).Coprime (addOrderOf (∑ i ∈ s, f i)) := by
      rw [ih', hf a (Finset.mem_insert_self a s)]
      exact Nat.Coprime.prod_right fun i hi =>
        hco a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [(AddCommute.all _ _).addOrderOf_add_eq_mul_addOrderOf_of_coprime hcop, ih', hf a (Finset.mem_insert_self a s)]

end Assembly

end GenKerSol
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow.GenKerSol"

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel in
open scoped Classical in
theorem solution
    (A : Type) [CommRing A] (ℓg M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] [Algebra A κ] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (x : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw κ) :
    ∃ g : (x.curve).toAffine.Point, (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x.level.1 p).IsRoot x₁) := by
  classical
  have hM0 : M' ≠ 0 := NeZero.ne M'
  haveI : x.curve.IsElliptic := ⟨x.isUnit_Δ⟩

  have hpK : ∀ p : ↥M'.primeFactors, ((p : ℕ) : κ) ≠ 0 := by
    intro p hp0
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_primeFactors p.2
    apply hM'κ
    rw [hc]; push_cast; rw [hp0, zero_mul]
  have hprime : ∀ p : ↥M'.primeFactors, (p : ℕ).Prime := fun p => Nat.prime_of_mem_primeFactors p.2
  have hkpos : ∀ p : ↥M'.primeFactors, 0 < M'.factorization (p : ℕ) := fun p =>
    (hprime p).factorization_pos_of_dvd hM0 (Nat.dvd_of_mem_primeFactors p.2)
  choose P hP hPgen using fun p : ↥M'.primeFactors =>
    GenKerSol.exists_generator_gamma0PowAt x.curve (hprime p) (hkpos p) (hpK p) (x.isLevel.1.1 p)

  refine ⟨∑ p : ↥M'.primeFactors, P p, ?_, ?_⟩
  ·
    rw [GenKerSol.addOrderOf_sum_eq_prod (Finset.univ : Finset ↥M'.primeFactors) P
      (fun p => (p : ℕ) ^ M'.factorization (p : ℕ)) (fun p _ => hP p) ?_]
    · rw [Finset.prod_coe_sort M'.primeFactors (fun p => p ^ M'.factorization p)]
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hM0]
      rw [Finsupp.prod, Nat.support_factorization]
    · intro i _ j _ hij
      apply Nat.Coprime.pow
      rw [Nat.coprime_primes (hprime i) (hprime j)]
      exact fun h => hij (Subtype.ext h)
  ·
    intro p n x₁ y₁ h₁ hn hord
    set qp : ℕ := (p : ℕ) ^ M'.factorization (p : ℕ) with hqp
    set c : ℕ := M' / qp with hcdef
    have hqdvd : qp ∣ M' := Nat.ordProj_dvd M' _
    have hcq : c * qp = M' := Nat.div_mul_cancel hqdvd
    have hqpos : 0 < qp := pow_pos (hprime p).pos _

    have hgo : addOrderOf (∑ p : ↥M'.primeFactors, P p) = M' := by
      rw [GenKerSol.addOrderOf_sum_eq_prod (Finset.univ : Finset ↥M'.primeFactors) P
        (fun p => (p : ℕ) ^ M'.factorization (p : ℕ)) (fun p _ => hP p) ?_]
      · rw [Finset.prod_coe_sort M'.primeFactors (fun p => p ^ M'.factorization p)]
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hM0]
        rw [Finsupp.prod, Nat.support_factorization]
      · intro i _ j _ hij
        apply Nat.Coprime.pow
        rw [Nat.coprime_primes (hprime i) (hprime j)]
        exact fun h => hij (Subtype.ext h)

    have hfin : IsOfFinAddOrder (∑ p : ↥M'.primeFactors, P p) := by
      rw [← addOrderOf_pos_iff, hgo]; exact Nat.pos_of_ne_zero hM0
    have hgcd : M'.gcd n = c := by
      have h1 := hfin.addOrderOf_nsmul _ n
      rw [hord, hgo] at h1
      have h2 : M'.gcd n ∣ M' := Nat.gcd_dvd_left _ _
      have hmul : M'.gcd n * qp = M' := by rw [h1, Nat.mul_div_cancel' h2]
      rw [hcdef]
      conv_rhs => rw [← hmul, Nat.mul_div_cancel _ hqpos]
    have hcn : c ∣ n := by rw [← hgcd]; exact Nat.gcd_dvd_right _ _
    obtain ⟨t, rfl⟩ := hcn

    have hcg : c • (∑ ℓ : ↥M'.primeFactors, P ℓ) = c • P p := by
      rw [← Finset.sum_nsmul]
      rw [Finset.sum_eq_single p]
      · intro ℓ _ hℓp
        apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
        rw [hP ℓ]
        have hℓdvd : (ℓ : ℕ) ^ M'.factorization (ℓ : ℕ) ∣ M' := Nat.ordProj_dvd M' _
        have hℓdvd' : (ℓ : ℕ) ^ M'.factorization (ℓ : ℕ) ∣ c * qp := hℓdvd.trans (dvd_of_eq hcq.symm)
        refine (Nat.Coprime.dvd_of_dvd_mul_right ?_ hℓdvd')
        apply Nat.Coprime.pow
        rw [Nat.coprime_primes (hprime ℓ) (hprime p)]
        exact fun h => hℓp (Subtype.ext h)
      · intro h; exact absurd (Finset.mem_univ p) h
    have hng : (c * t) • (∑ ℓ : ↥M'.primeFactors, P ℓ) = (c * t) • P p := by
      rw [mul_comm, mul_nsmul', hcg, ← mul_nsmul']
    rw [hng] at hn hord
    exact hPgen p (c * t) x₁ y₁ h₁ hn hord

#print axioms solution

end S_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow (solution)
