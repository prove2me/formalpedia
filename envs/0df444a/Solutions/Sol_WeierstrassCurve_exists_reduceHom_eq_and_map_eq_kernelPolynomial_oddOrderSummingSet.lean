-- Prove2me | solution 1 for WeierstrassCurve.exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/21b22b79-54e7-5594-a968-2aa8c26ed29e

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Theorems.Thm_WeierstrassCurve_bijective_reduceHom_restrict_torsion
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.Y_eq_of_Y_ne mk.injEq map mk Affine.Point.some map_preΨ' reduction preΨ' toAffine Affine.Point map_Δ Δ Affine.Point.neg_some reduceHom X_mem_of_nsmul_eq_zero' Affine.Y_mem_of_X_mem Affine.nonsingular_residue reducePoint_some_of_mem Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet kernelPolynomial kernelPolynomial_eq_multiset_prod monic_kernelPolynomial natDegree_kernelPolynomial eval_kernelPolynomial_eq_zero bijective_reduceHom_restrict_torsion separable_prePsi_of_isUnit Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi"
p2m_open "WeierstrassCurve"

namespace KernelAtPlace

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

theorem eq_or_eq_neg_of_fst_eq {x y y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') :
    Affine.Point.some x y' h' = Affine.Point.some x y h ∨
      Affine.Point.some x y' h' = -Affine.Point.some x y h := by
  by_cases hy : y' = W.toAffine.negY x y
  · right
    rw [Affine.Point.neg_some]
    simp only [hy]
  · left
    have := Affine.Y_eq_of_Y_ne h'.left h.left rfl hy
    subst this
    rfl

omit [DecidableEq F] in
theorem exists_eq_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ x y h, P = Affine.Point.some x y h ∧ P.coordsOrZero = (x, y) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl, rfl⟩

omit [DecidableEq F] in
theorem eq_of_coordsOrZero_eq {P P' : W.toAffine.Point} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (h : P.coordsOrZero = P'.coordsOrZero) : P = P' := by
  rcases P with _ | ⟨x, y, hx⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨x', y', hx'⟩
  · exact absurd rfl hP'
  simp only [Affine.Point.coordsOrZero_some, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

variable (W)

theorem nsmul_ne_zero_of_le {Q : W.toAffine.Point} {n k : ℕ} (hQ : addOrderOf Q = 2 * n + 1)
    (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) : k • Q ≠ 0 :=
  nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)

theorem card_oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) :
    (W.oddOrderSummingSet Q n).card = n := by
  rw [oddOrderSummingSet, Finset.card_image_of_injOn, Nat.card_Icc, Nat.add_sub_cancel]
  intro k hk l hl hkl
  rw [Finset.coe_Icc, Set.mem_Icc] at hk hl
  have hk0 := nsmul_ne_zero_of_le W hQ hk.1 (by omega)
  have hl0 := nsmul_ne_zero_of_le W hQ hl.1 (by omega)
  have heq : k • Q = l • Q := eq_of_coordsOrZero_eq hk0 hl0 hkl
  rw [nsmul_eq_nsmul_iff_modEq, hQ] at heq
  exact Nat.ModEq.eq_of_lt_of_lt heq (by omega) (by omega)

theorem injOn_fst_oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn Prod.fst (W.oddOrderSummingSet Q n : Set (F × F)) := by
  intro P hP P' hP' hfst
  rw [Finset.mem_coe, mem_oddOrderSummingSet] at hP hP'
  obtain ⟨k, hk1, hkn, rfl⟩ := hP
  obtain ⟨l, hl1, hln, rfl⟩ := hP'
  have hk0 := nsmul_ne_zero_of_le W hQ hk1 (by omega)
  have hl0 := nsmul_ne_zero_of_le W hQ hl1 (by omega)
  obtain ⟨x, y, h, hkQ, hck⟩ := exists_eq_some_of_ne_zero hk0
  obtain ⟨x', y', h', hlQ, hcl⟩ := exists_eq_some_of_ne_zero hl0
  rw [hck, hcl] at hfst ⊢
  simp only at hfst
  subst hfst
  rcases eq_or_eq_neg_of_fst_eq h h' with e | e
  · rw [← hkQ, ← hlQ] at e
    rw [← hcl, ← hck, e]
  · exfalso
    rw [← hkQ, ← hlQ] at e
    have h0 : (k + l) • Q = 0 := by rw [add_nsmul, add_comm, e, neg_add_cancel]
    exact nsmul_ne_zero_of_le W hQ (by omega) (by omega) h0

theorem kernelPolynomial_dvd_of_roots (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    {p : F[X]} (hp : p ≠ 0)
    (hroots : ∀ k, 1 ≤ k → k ≤ n → ∀ x y hxy, k • Q = Affine.Point.some x y hxy → p.eval x = 0) :
    kernelPolynomial (W.oddOrderSummingSet Q n) ∣ p := by
  rw [kernelPolynomial_eq_multiset_prod, Multiset.prod_X_sub_C_dvd_iff_le_roots hp,
    Multiset.le_iff_subset]
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    rw [mem_roots hp, IsRoot.def]
    have hP' := Finset.mem_val.mp hP
    rw [mem_oddOrderSummingSet] at hP'
    obtain ⟨k, hk1, hkn, rfl⟩ := hP'
    obtain ⟨x, y, h, hkQ, hck⟩ := exists_eq_some_of_ne_zero (nsmul_ne_zero_of_le W hQ hk1 (by omega))
    rw [hck]
    exact hroots k hk1 hkn x y h hkQ
  · exact Multiset.Nodup.map_on (fun P hP P' hP' h =>
      injOn_fst_oddOrderSummingSet W Q n hQ (Finset.mem_val.mp hP) (Finset.mem_val.mp hP') h)
      (Finset.nodup _)

end Field

section Place

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [HenselianLocalRing A] [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)]
  {E : WeierstrassCurve A}

theorem main (hΔ : (E.map (residue A)).Δ ≠ 0) {n : ℕ}
    (hm : ((2 * n + 1 : ℕ) : ResidueField A) ≠ 0)
    (Q₀ : (E.map (residue A)).toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    {h : A[X]} (hh : h.Monic) (hdvd : h ∣ E.preΨ' (2 * n + 1))
    (hmap : h.map (residue A) = kernelPolynomial ((E.map (residue A)).oddOrderSummingSet Q₀ n)) :
    ∃ Q : (E.map A.subtype).toAffine.Point, addOrderOf Q = 2 * n + 1 ∧ reduceHom hΔ Q = Q₀ ∧
      h.map A.subtype = kernelPolynomial ((E.map A.subtype).oddOrderSummingSet Q n) := by
  set m : ℕ := 2 * n + 1 with hm_def
  have hmodd : Odd m := ⟨n, rfl⟩

  haveI hE₀ : (E.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hΔA : IsUnit E.Δ := by
    rw [← residue_ne_zero_iff_isUnit]
    simpa [map_Δ] using hΔ
  haveI hEL : (E.map A.subtype).IsElliptic := ⟨by rw [map_Δ]; exact hΔA.map _⟩

  have hQ₀tor : m • Q₀ = 0 := by rw [← hQ₀]; exact addOrderOf_nsmul_eq_zero Q₀
  obtain ⟨⟨Q, hQm⟩, hQeq⟩ := (bijective_reduceHom_restrict_torsion hΔ hm).2 ⟨Q₀, hQ₀tor⟩
  have hQred : reduceHom hΔ Q = Q₀ := congrArg Subtype.val hQeq
  have hQord : addOrderOf Q = m := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hQm) ?_
    have := addOrderOf_map_dvd (reduceHom hΔ) Q
    rwa [hQred, hQ₀] at this
  refine ⟨Q, hQord, hQred, ?_⟩

  obtain ⟨g, hg⟩ := hdvd
  have hsep : ((E.map (residue A)).preΨ' m).Separable :=
    separable_prePsi_of_isUnit _ hmodd ((isUnit_iff_ne_zero.mpr hm).mul (E.map (residue A)).isUnit_Δ)
  have hcop : IsCoprime (h.map (residue A)) (g.map (residue A)) := by
    rw [map_preΨ', hg, Polynomial.map_mul] at hsep
    exact hsep.isCoprime

  have hroot : ∀ k, 1 ≤ k → k ≤ n → ∀ x y hxy,
      k • Q = Affine.Point.some x y hxy → (h.map A.subtype).eval x = 0 := by
    intro k hk1 hkn x y hxy hkQ

    have hPm : m • (Affine.Point.some x y hxy : (E.map A.subtype).toAffine.Point) = 0 := by
      rw [← hkQ, ← mul_nsmul', mul_comm, mul_nsmul', hQm, nsmul_zero]
    have hx : x ∈ A := X_mem_of_nsmul_eq_zero' E hm hxy hPm

    have hgen : ((E.map A.subtype).preΨ' m).eval x = 0 :=
      (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi (E.map A.subtype) hmodd hxy).mp hPm
    rw [map_preΨ', hg, Polynomial.map_mul, eval_mul] at hgen

    have hred : reduceHom hΔ (Affine.Point.some x y hxy) =
        Affine.Point.some (residue A ⟨x, hx⟩)
          (residue A ⟨y, Affine.Y_mem_of_X_mem E hxy.1 hx⟩)
          (Affine.nonsingular_residue E hΔ hxy.1) :=
      reducePoint_some_of_mem hΔ hxy hx
    have hkQ₀ : k • Q₀ = reduceHom hΔ (Affine.Point.some x y hxy) := by
      rw [← hkQ, map_nsmul, hQred]
    have hmem : (residue A ⟨x, hx⟩, residue A ⟨y, Affine.Y_mem_of_X_mem E hxy.1 hx⟩) ∈
        (E.map (residue A)).oddOrderSummingSet Q₀ n := by
      rw [mem_oddOrderSummingSet]
      exact ⟨k, hk1, hkn, by rw [hkQ₀, hred]; rfl⟩
    have hhbar : residue A (h.eval ⟨x, hx⟩) = 0 := by
      rw [← eval_map_apply, hmap]
      exact eval_kernelPolynomial_eq_zero hmem
    have hgbar : residue A (g.eval ⟨x, hx⟩) ≠ 0 := by
      intro h0
      obtain ⟨a, b, hab⟩ := hcop
      have := congrArg (Polynomial.eval (residue A ⟨x, hx⟩)) hab
      rw [eval_add, eval_mul, eval_mul, eval_map_apply, eval_map_apply, hhbar, h0, eval_one] at this
      simp at this

    have hgunit : IsUnit (g.eval ⟨x, hx⟩) := (residue_ne_zero_iff_isUnit _).mp hgbar
    have hgL : (g.map A.subtype).eval x ≠ 0 := by
      have hx' : x = A.subtype ⟨x, hx⟩ := rfl
      rw [hx', eval_map_apply]
      exact fun h0 => hgunit.ne_zero (Subtype.ext (by simpa using h0))
    exact (mul_eq_zero.mp hgen).resolve_right hgL

  have hne : h.map A.subtype ≠ 0 := (hh.map _).ne_zero
  have hK := kernelPolynomial_dvd_of_roots (E.map A.subtype) Q n hQord hne hroot
  have hdeg : (h.map A.subtype).natDegree =
      (kernelPolynomial ((E.map A.subtype).oddOrderSummingSet Q n)).natDegree := by
    rw [hh.natDegree_map, natDegree_kernelPolynomial, card_oddOrderSummingSet _ Q n hQord,
      ← hh.natDegree_map (residue A), hmap, natDegree_kernelPolynomial,
      card_oddOrderSummingSet _ Q₀ n hQ₀]
  exact eq_of_monic_of_dvd_of_natDegree_le (monic_kernelPolynomial _) (hh.map _) hK hdeg.le

end Place

end KernelAtPlace

end WeierstrassCurve

theorem solution {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [HenselianLocalRing A] [DecidableEq (IsLocalRing.ResidueField A)]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    {E : WeierstrassCurve A} (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hm : ((2 * n + 1 : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (Q₀ : (E.map (IsLocalRing.residue A)).toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    {h : Polynomial A} (hh : h.Monic) (hdvd : h ∣ E.preΨ' (2 * n + 1))
    (hmap : h.map (IsLocalRing.residue A) =
      WeierstrassCurve.kernelPolynomial ((E.map (IsLocalRing.residue A)).oddOrderSummingSet Q₀ n)) :
    ∃ Q : (E.map A.subtype).toAffine.Point, addOrderOf Q = 2 * n + 1 ∧
      WeierstrassCurve.reduceHom hΔ Q = Q₀ ∧
      h.map A.subtype =
        WeierstrassCurve.kernelPolynomial ((E.map A.subtype).oddOrderSummingSet Q n) :=
  WeierstrassCurve.KernelAtPlace.main hΔ hm Q₀ hQ₀ hh hdvd hmap

end S_WeierstrassCurve_exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet
end P2MW
export P2MW.S_WeierstrassCurve_exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet (solution)
