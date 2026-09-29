-- Prove2me | solution 1 for WeierstrassCurve.exists_forall_mem_zmultiples_of_char_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/944fb969-15fe-5679-9f6b-4b78d1ab1eee

import Mathlib
import Theorems.Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_forall_mem_zmultiples_of_char_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_exists_forall_mem_zmultiples_of_char_nsmul_eq_zero.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ natDegree_Φ natDegree_ΨSq_le a₄ a₂ a₆ ΨSq_ne_zero ΨSq toAffine Affine.Point Affine.equation_iff j Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq Psi2Sq_ne_zero_of_isElliptic Affine.Point.smul_some_eq_zero_iff Affine.evalEval_psi_sq"
namespace PTorsionCyclic
p2m_open "WeierstrassCurve"

variable {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p]
  (W : WeierstrassCurve k) [W.IsElliptic]

theorem wronskian_Φ_ΨSq_eq_zero : wronskian (W.Φ p) (W.ΨSq p) = 0 := by
  have h := WeierstrassCurve.Psi2Sq_mul_wronskian_sq W (p : ℤ)
  have hp : ((p : ℤ) : k) = 0 := by rw [Int.cast_natCast]; exact CharP.cast_eq_zero k p
  rw [hp, zero_pow two_ne_zero, C_0, zero_mul] at h
  have h2 := (mul_eq_zero.mp h).resolve_left (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W)
  have h3 : derivative (W.Φ p) * W.ΨSq p - W.Φ p * derivative (W.ΨSq p) = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp h2
  rw [wronskian, ← neg_eq_zero, neg_sub', sub_neg_eq_add]
  linear_combination h3

theorem ΨSq_ne_zero : W.ΨSq p ≠ 0 := by
  intro h0
  have hc := WeierstrassCurve.isCoprime_Phi_PsiSq W (p : ℤ)
  rw [h0, isCoprime_zero_right] at hc
  have := natDegree_eq_zero_of_isUnit hc
  rw [WeierstrassCurve.natDegree_Φ] at this
  simp [(Fact.out : p.Prime).ne_zero] at this

theorem exists_ΨSq_eq_expand : ∃ g : k[X], W.ΨSq p = expand k p g ∧ g ≠ 0 ∧ g.natDegree ≤ p - 1 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hcop := WeierstrassCurve.isCoprime_Phi_PsiSq W (p : ℤ)
  obtain ⟨-, hd2⟩ := hcop.wronskian_eq_zero_iff.mp (wronskian_Φ_ΨSq_eq_zero p W)
  refine ⟨contract p (W.ΨSq p), (expand_contract p hd2 hp).symm, ?_, ?_⟩
  · intro h0
    apply ΨSq_ne_zero p W
    rw [← expand_contract p hd2 hp, h0, map_zero]
  · have hdeg : (W.ΨSq p).natDegree = (contract p (W.ΨSq p)).natDegree * p := by
      conv_lhs => rw [← expand_contract p hd2 hp]
      rw [natDegree_expand]
    have hle := WeierstrassCurve.natDegree_ΨSq_le W (p : ℤ)
    rw [hdeg] at hle
    simp only [Int.natAbs_natCast] at hle

    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    by_contra hcon
    push Not at hcon
    have h1 : p * p ≤ (contract p (W.ΨSq ↑p)).natDegree * p := by
      have : p ≤ (contract p (W.ΨSq ↑p)).natDegree := by omega
      exact Nat.mul_le_mul_right p this
    have h2 : p ^ 2 - 1 < p * p := by
      rw [pow_two]; exact Nat.sub_one_lt (Nat.mul_ne_zero hp hp)
    omega

noncomputable def absc : Finset k := (W.ΨSq p).roots.toFinset

theorem card_absc_le : (absc p W).card ≤ p - 1 := by
  obtain ⟨g, hg, hg0, hdeg⟩ := exists_ΨSq_eq_expand p W
  have hne : expand k p g ≠ 0 := by rw [← hg]; exact ΨSq_ne_zero p W
  calc (absc p W).card ≤ g.roots.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun x => x ^ p) ?_ ?_
        · intro x hx
          rw [Finset.mem_coe, absc, hg, Multiset.mem_toFinset, mem_roots hne, IsRoot.def,
            expand_eval] at hx
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hg0]
          exact hx
        · intro x _ y _ hxy
          exact frobenius_inj k p hxy
    _ ≤ g.natDegree := (Multiset.toFinset_card_le _).trans (card_roots' _)
    _ ≤ p - 1 := hdeg

noncomputable def quad (x : k) : k[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

omit [DecidableEq k] [Fact p.Prime] [CharP k p] [W.IsElliptic] in
theorem quad_natDegree (x : k) : (quad W x).natDegree = 2 := by
  have : (quad W x).degree = 2 := by rw [quad]; compute_degree!
  exact natDegree_eq_of_degree_eq_some this

omit [DecidableEq k] [Fact p.Prime] [CharP k p] [W.IsElliptic] in
theorem quad_ne_zero (x : k) : quad W x ≠ 0 := by
  intro h; have := quad_natDegree W x; rw [h, natDegree_zero] at this; exact absurd this (by norm_num)

omit [DecidableEq k] [Fact p.Prime] [CharP k p] [W.IsElliptic] in
theorem eval_quad_eq_zero {x y : k} (h : W.toAffine.Equation x y) : (quad W x).eval y = 0 := by
  rw [Affine.equation_iff] at h
  simp only [quad, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  linear_combination h

open Classical in

noncomputable def mkPt (x y : k) : W.toAffine.Point :=
  if h : W.toAffine.Nonsingular x y then .some x y h else 0

noncomputable def torsFinset : Finset W.toAffine.Point :=
  insert 0 ((absc p W).biUnion fun x => ((quad W x).roots.toFinset).image (mkPt W x))

theorem mem_torsFinset {T : W.toAffine.Point} (hT : p • T = 0) : T ∈ torsFinset p W := by
  rw [torsFinset, Finset.mem_insert]
  rcases T with _ | ⟨x, y, h⟩
  · exact Or.inl rfl
  · right
    simp only [Finset.mem_biUnion, Finset.mem_image, Multiset.mem_toFinset]
    have hψ : (W.ψ p).evalEval x y = 0 := by
      rw [← WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h (p : ℤ), natCast_zsmul]
      exact hT
    have hΨ : (W.ΨSq p).eval x = 0 := by
      rw [← WeierstrassCurve.Affine.evalEval_psi_sq W h.1 (p : ℤ), hψ, zero_pow two_ne_zero]
    refine ⟨x, ?_, y, (mem_roots (quad_ne_zero W x)).mpr (eval_quad_eq_zero W h.1), ?_⟩
    · rw [absc, Multiset.mem_toFinset, mem_roots (ΨSq_ne_zero p W)]
      exact hΨ
    · rw [mkPt, dif_pos h]

theorem card_torsFinset_le : (torsFinset p W).card ≤ 2 * (p - 1) + 1 := by
  rw [torsFinset]
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ x ∈ absc p W, (((quad W x).roots.toFinset).image (mkPt W x)).card
      ≤ ∑ _x ∈ absc p W, 2 := Finset.sum_le_sum fun x _ => by
        refine Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans ?_)
        exact (card_roots' _).trans (quad_natDegree W x).le
    _ = 2 * (absc p W).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * (p - 1) := Nat.mul_le_mul_left 2 (card_absc_le p W)

omit [CharP k p] [W.IsElliptic] in

theorem injOn_comb {T₀ T : W.toAffine.Point} (hT₀ : p • T₀ = 0) (hT₀0 : T₀ ≠ 0) (hT : p • T = 0)
    (hnot : T ∉ AddSubgroup.zmultiples T₀) :
    Function.Injective fun ij : Fin p × Fin p => ((ij.1 : ℕ) : ℤ) • T₀ + ((ij.2 : ℕ) : ℤ) • T := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hord : addOrderOf T₀ = p := addOrderOf_eq_prime hT₀ hT₀0
  have hpT : (p : ℤ) • T = 0 := by rw [natCast_zsmul]; exact hT
  rintro ⟨i, j⟩ ⟨i', j'⟩ hij
  simp only at hij

  have h1 : ((j : ℕ) - (j' : ℕ) : ℤ) • T = ((i' : ℕ) - (i : ℕ) : ℤ) • T₀ := by
    have h0 : ((i : ℕ) : ℤ) • T₀ + ((j : ℕ) : ℤ) • T - (((i' : ℕ) : ℤ) • T₀ + ((j' : ℕ) : ℤ) • T) = 0 :=
      sub_eq_zero.mpr hij
    rw [← sub_eq_zero]
    rw [← h0]
    module
  have hj : (j : ℕ) = (j' : ℕ) := by
    by_contra hne
    apply hnot
    set d : ℤ := (j : ℕ) - (j' : ℕ) with hd
    have hd0 : d ≠ 0 := by rw [hd]; omega
    have habs : |d| < p := by
      rw [hd, abs_lt]; constructor <;> omega
    have hndvd : ¬ (p : ℤ) ∣ d := fun hdvd => hd0 (Int.eq_zero_of_abs_lt_dvd hdvd habs)
    have hcop : IsCoprime (p : ℤ) d := (Irreducible.coprime_iff_not_dvd hpp.irreducible).mpr hndvd
    obtain ⟨a, b, hab⟩ := hcop
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨b * ((i' : ℕ) - (i : ℕ) : ℤ), ?_⟩
    calc (b * ((i' : ℕ) - (i : ℕ) : ℤ)) • T₀ = b • (((i' : ℕ) - (i : ℕ) : ℤ) • T₀) := mul_zsmul _ _ _
      _ = b • (d • T) := by rw [← h1]
      _ = (a * p + b * d) • T := by rw [add_zsmul, mul_zsmul, mul_zsmul, hpT, zsmul_zero, zero_add]
      _ = T := by rw [hab, one_zsmul]
  have hi : (i : ℕ) = (i' : ℕ) := by
    rw [hj, sub_self, zero_zsmul] at h1
    have hdvd : ((addOrderOf T₀ : ℕ) : ℤ) ∣ ((i' : ℕ) - (i : ℕ) : ℤ) :=
      (addOrderOf_dvd_iff_zsmul_eq_zero).mpr h1.symm
    rw [hord] at hdvd
    have habs : |((i' : ℕ) - (i : ℕ) : ℤ)| < p := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  exact Prod.ext (Fin.ext hi) (Fin.ext hj)

theorem main : ∃ T₀ : W.toAffine.Point, p • T₀ = 0 ∧
    ∀ T : W.toAffine.Point, p • T = 0 → T ∈ AddSubgroup.zmultiples T₀ := by
  by_cases hex : ∃ T₀ : W.toAffine.Point, p • T₀ = 0 ∧ T₀ ≠ 0
  · obtain ⟨T₀, hT₀, hT₀0⟩ := hex
    refine ⟨T₀, hT₀, fun T hT => ?_⟩
    by_contra hnot

    have hinj := injOn_comb p W hT₀ hT₀0 hT hnot
    have hmaps : Set.MapsTo (fun ij : Fin p × Fin p => ((ij.1 : ℕ) : ℤ) • T₀ + ((ij.2 : ℕ) : ℤ) • T)
        ((Finset.univ : Finset (Fin p × Fin p)) : Set (Fin p × Fin p)) (torsFinset p W) := by
      intro ij _
      apply mem_torsFinset p W
      show p • ((((ij.1 : ℕ) : ℤ)) • T₀ + (((ij.2 : ℕ) : ℤ)) • T) = 0
      rw [smul_add, smul_comm p _ T₀, hT₀, smul_comm p _ T, hT, smul_zero, smul_zero, add_zero]
    have hcard := Finset.card_le_card_of_injOn _ hmaps (hinj.injOn)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hcard
    have hle := card_torsFinset_le p W
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have : p * p ≤ 2 * (p - 1) + 1 := hcard.trans hle
    have h3 : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
    omega
  · push Not at hex
    exact ⟨0, smul_zero _, fun T hT => by rw [hex T hT]; exact AddSubgroup.zero_mem _⟩

end WeierstrassCurve.PTorsionCyclic

theorem solution {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic] : ∃ T₀ : W.toAffine.Point, p • T₀ = 0 ∧ ∀ T : W.toAffine.Point, p • T = 0 → T ∈ AddSubgroup.zmultiples T₀ :=
  WeierstrassCurve.PTorsionCyclic.main p W

end S_WeierstrassCurve_exists_forall_mem_zmultiples_of_char_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_forall_mem_zmultiples_of_char_nsmul_eq_zero (solution)
