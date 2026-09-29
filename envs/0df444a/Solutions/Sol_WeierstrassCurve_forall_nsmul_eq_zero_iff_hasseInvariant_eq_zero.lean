-- Prove2me | solution 1 for WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1821aaf1-a2d2-5be3-afcc-69342982bd97

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_exists_prePsi_eq_expand
import Theorems.Thm_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ Ψ₂Sq a₄ a₂ a₆ Affine.Point.some preΨ' toAffine Affine.Point Affine.equation_iff_nonsingular Affine.Point.some_ne_zero natDegree_preΨ'_le Affine.equation_iff natDegree_Ψ₂Sq Affine.Point.neg_some hasseInvariant Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi Affine.Point.two_smul_some_eq_zero_iff Psi2Sq_ne_zero_of_isElliptic exists_prePsi_eq_expand coeff_prePsi_eq_hasseInvariant"
p2m_open "WeierstrassCurve"

section lemmas

variable {K : Type*} [Field K]

theorem pow_char_injective (q : ℕ) [Fact q.Prime] [CharP K q] {x y : K} (h : x ^ q = y ^ q) :
    x = y := by
  have := sub_pow_char (p := q) x y
  rw [h, sub_self] at this
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : q.Prime).ne_zero |>.mp this)

theorem exists_nonsingular_of_isAlgClosed [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (x : K) : ∃ y, W.toAffine.Nonsingular x y := by
  set b := W.a₁ * x + W.a₃ with hb
  set c := x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ with hc
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (b ^ 2 + 4 * c)
  refine ⟨(s - b) / 2, (Affine.equation_iff_nonsingular).mp ?_⟩
  rw [Affine.equation_iff]
  field_simp
  linear_combination (-1 : K) * hs

theorem eq_or_eq_negY_of_equation (W : WeierstrassCurve K) {x y₁ y₂ : K}
    (h₁ : W.toAffine.Equation x y₁) (h₂ : W.toAffine.Equation x y₂) :
    y₂ = y₁ ∨ y₂ = W.toAffine.negY x y₁ := by
  rw [Affine.equation_iff] at h₁ h₂
  have : (y₂ - y₁) * (y₂ - (-y₁ - W.a₁ * x - W.a₃)) = 0 := by linear_combination h₂ - h₁
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem some_eq_or_eq_neg (W : WeierstrassCurve K) {x y₁ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x y₁) (h₂ : W.toAffine.Nonsingular x y₂) :
    Affine.Point.some x y₂ h₂ = Affine.Point.some x y₁ h₁ ∨
      Affine.Point.some x y₂ h₂ = -Affine.Point.some x y₁ h₁ := by
  rcases eq_or_eq_negY_of_equation W h₁.1 h₂.1 with rfl | rfl
  · exact Or.inl rfl
  · right; rw [Affine.Point.neg_some]

namespace Affine p2m_export "WeierstrassCurve.Affine" "Equation negY Point.some Nonsingular Point equation_iff_nonsingular Point.some_ne_zero equation_iff polynomial Point.neg_some Point.nsmul_some_eq_zero_iff_eval_prePsi Point.two_smul_some_eq_zero_iff" namespace Point p2m_export "WeierstrassCurve.Affine.Point" "some map_zero some_ne_zero zero neg_some nsmul_some_eq_zero_iff_eval_prePsi two_smul_some_eq_zero_iff" end Affine.Point
namespace Affine.Point
p2m_open_scoped "WeierstrassCurve.Affine WeierstrassCurve.Affine.Point" in

private def _root_.WeierstrassCurve.Affine.Point.xcoord {W' : Affine K} : W'.Point → K
  | .zero => 0
  | .some x _ _ => x

end Affine.Point
p2m_export "WeierstrassCurve" "Affine.Point.xcoord"
end lemmas

private theorem _root_.WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero' {K : Type*} [Field K] [IsAlgClosed K]
    [DecidableEq K] (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) [CharP K q] (W : WeierstrassCurve K)
    [W.IsElliptic] :
    (∀ P : W.toAffine.Point, q • P = 0 → P = 0) ↔ W.hasseInvariant q = 0 := by
  have hqp : q.Prime := Fact.out
  have hoddq : Odd q := hqp.odd_of_ne_two hq
  obtain ⟨m, hm⟩ := hoddq
  have hm1 : 1 ≤ m := by have := hqp.two_le; omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h2q : q ∣ 2 := (CharP.cast_eq_zero_iff K q 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos h2q
    have := hqp.two_le
    omega
  have hdiv : (q - 1) / 2 = m := by omega
  have hα := coeff_prePsi_eq_hasseInvariant q hq W
  rw [hdiv] at hα
  constructor
  ·
    intro htors
    by_contra hH
    have hne : (W.preΨ' q).coeff (q * m) ≠ 0 := by rwa [hα]
    have hdeg : (W.preΨ' q).degree ≠ 0 := by
      intro hd
      apply hne
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_eq_zero_iff_degree_le_zero.mpr hd.le]
      exact Nat.mul_pos hqp.pos hm1
    obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root _ hdeg
    obtain ⟨y₀, hns⟩ := exists_nonsingular_of_isAlgClosed W h2 x₀
    have hq0 := (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ⟨m, hm⟩ hns).mpr hx₀
    exact Affine.Point.some_ne_zero hns (htors _ hq0)
  ·
    intro hH P hP
    obtain ⟨g, hg⟩ := exists_prePsi_eq_expand q W
    have hgm : g.coeff m = 0 := by
      rw [← coeff_expand_mul hqp.pos, ← hg, mul_comm, hα, hH]
    have hgdeg : g.natDegree ≤ m := by
      have h1 := W.natDegree_preΨ'_le q
      have hne : ¬ Even q := Nat.not_even_iff_odd.mpr ⟨m, hm⟩
      rw [if_neg hne, hg, natDegree_expand] at h1
      refine not_lt.mp fun hc => ?_
      have h3 : (m + 1) * q ≤ (q ^ 2 - 1) / 2 := le_trans (Nat.mul_le_mul_right q hc) h1
      have e : q ^ 2 - 1 = 2 * (m * q + m) := by
        have : q ^ 2 = 2 * (m * q + m) + 1 := by rw [hm]; ring
        omega
      rw [e, Nat.mul_div_cancel_left _ two_pos, add_mul, one_mul] at h3
      omega
    by_contra hP0
    rcases eq_or_ne g 0 with rfl | hg0
    ·
      rw [map_zero] at hg
      have h4 : (4 : K) ≠ 0 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      have hdeg2 : W.Ψ₂Sq.degree ≠ 0 := by
        rw [degree_eq_natDegree (Psi2Sq_ne_zero_of_isElliptic W), natDegree_Ψ₂Sq W h4]
        exact_mod_cast (by norm_num : (3 : ℕ) ≠ 0)
      obtain ⟨x₂, hx₂⟩ := IsAlgClosed.exists_root _ hdeg2
      obtain ⟨y₂, hns₂⟩ := exists_nonsingular_of_isAlgClosed W h2 x₂
      have h2t := (Affine.Point.two_smul_some_eq_zero_iff W hns₂).mpr hx₂
      have hqt := (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ⟨m, hm⟩ hns₂).mpr
        (by rw [hg, eval_zero])
      apply Affine.Point.some_ne_zero hns₂
      have e : (2 * m + 1) • Affine.Point.some x₂ y₂ hns₂
          = (m * 2) • Affine.Point.some x₂ y₂ hns₂ + Affine.Point.some x₂ y₂ hns₂ := by
        rw [mul_comm m 2, add_nsmul, one_nsmul]
      rw [← smul_smul, h2t, smul_zero, zero_add, ← hm, hqt] at e
      exact e.symm
    ·
      have hgdeg' : g.natDegree < m := by
        refine lt_of_le_of_ne hgdeg fun h => hg0 ?_
        rw [← leadingCoeff_eq_zero, leadingCoeff, h, hgm]
      have hord : addOrderOf P = q := by
        refine ((hqp.eq_one_or_self_of_dvd _ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hP)).resolve_left ?_)
        rwa [AddMonoid.addOrderOf_eq_one_iff]
      have hk0 : ∀ k, 0 < k → k < q → k • P ≠ 0 := by
        intro k hk hkq h
        have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
        rw [hord] at hd
        exact absurd (Nat.le_of_dvd hk hd) (not_le.mpr hkq)
      have hroot : ∀ Q : W.toAffine.Point, Q ≠ 0 → q • Q = 0 → g.IsRoot (Q.xcoord ^ q) := by
        rintro (_ | ⟨x, y, h⟩) hQ hqQ
        · exact absurd rfl hQ
        · have := (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ⟨m, hm⟩ h).mp hqQ
          rwa [hg, expand_eval] at this
      have hxx : ∀ Q Q' : W.toAffine.Point, Q ≠ 0 → Q' ≠ 0 → Q.xcoord = Q'.xcoord →
          Q' = Q ∨ Q' = -Q := by
        rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hQ hQ' hx
        · exact absurd rfl hQ
        · exact absurd rfl hQ
        · exact absurd rfl hQ'
        · change x = x' at hx
          subst hx
          exact some_eq_or_eq_neg W h h'
      have hinj : Set.InjOn (fun k : ℕ => (k • P).xcoord ^ q) (Finset.Icc 1 m) := by
        intro k hk l hl hkl
        simp only [Finset.coe_Icc, Set.mem_Icc] at hk hl
        have hxkl : (k • P).xcoord = (l • P).xcoord := pow_char_injective q hkl
        rcases hxx _ _ (hk0 k (by omega) (by omega)) (hk0 l (by omega) (by omega)) hxkl with h | h
        · have := (nsmul_inj_mod (x := P) (n := l) (m := k)).mp h
          rwa [hord, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), eq_comm] at this
        · exfalso
          have : (l + k) • P = 0 := by rw [add_nsmul, h, neg_add_cancel]
          exact hk0 _ (by omega) (by omega) this
      have hsub : (Finset.Icc 1 m).image (fun k : ℕ => (k • P).xcoord ^ q) ⊆ g.roots.toFinset := by
        intro z hz
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_Icc] at hk
        rw [Multiset.mem_toFinset, mem_roots hg0]
        refine hroot _ (hk0 k (by omega) (by omega)) ?_
        rw [smul_smul, mul_comm, ← smul_smul, hP, smul_zero]
      have hcard : m ≤ g.natDegree :=
        calc m = (Finset.Icc 1 m).card := by simp
          _ = ((Finset.Icc 1 m).image fun k : ℕ => (k • P).xcoord ^ q).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ g.roots.card := Multiset.toFinset_card_le _
          _ ≤ g.natDegree := card_roots' g
      omega

p2m_export "WeierstrassCurve" "forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero'"
end WeierstrassCurve

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime]
    (hq : q ≠ 2) [CharP K q] (W : WeierstrassCurve K) [W.IsElliptic] :
    (∀ P : W.toAffine.Point, q • P = 0 → P = 0) ↔ W.hasseInvariant q = 0 :=
  W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero' q hq

end S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero (solution)
