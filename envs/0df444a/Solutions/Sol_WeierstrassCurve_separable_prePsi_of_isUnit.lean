-- Prove2me | solution 1 for WeierstrassCurve.separable_prePsi_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d67dc890-df2b-5343-b6ec-dc7c807034b6

import Mathlib
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_separable_prePsi_of_isUnit
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open Polynomial

namespace SeparablePrePsi

theorem separable_C_mul_iff {R : Type*} [CommRing R] {c : R} (hc : IsUnit c) (f : R[X]) :
    (C c * f).Separable ↔ f.Separable := by
  rw [Separable, Separable, derivative_C_mul]
  exact isCoprime_mul_unit_left (hc.map C) _ _

theorem separable_of_forall_isMaximal {R : Type*} [CommRing R] {f : R[X]}
    (hf : IsUnit f.leadingCoeff)
    (h : ∀ m : Ideal R, m.IsMaximal → (f.map (Ideal.Quotient.mk m)).Separable) :
    f.Separable := by
  obtain ⟨u, hu⟩ := hf

  set f₀ : R[X] := C (↑u⁻¹ : R) * f with hf₀
  have hmon : f₀.Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu, Units.inv_mul])
  suffices h₀ : f₀.Separable from (separable_C_mul_iff (Units.isUnit u⁻¹) f).mp h₀
  rw [Separable, ← isUnit_resultant_iff_isCoprime hmon]
  by_contra hnu
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {resultant f₀ (derivative f₀)})
    (fun htop => hnu (Ideal.span_singleton_eq_top.mp htop))
  have hmem : resultant f₀ (derivative f₀) ∈ m := hle (Ideal.mem_span_singleton_self _)
  haveI : Nontrivial (R ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  set π : R →+* R ⧸ m := Ideal.Quotient.mk m with hπ_def
  have hπ0 : π (resultant f₀ (derivative f₀)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem

  have hsep : (f₀.map π).Separable := by
    rw [hf₀, Polynomial.map_mul, map_C]
    exact (separable_C_mul_iff ((Units.isUnit u⁻¹).map π) _).mpr (h m hm)
  have hmon' : (f₀.map π).Monic := hmon.map π
  have hunit : IsUnit ((f₀.map π).resultant (derivative (f₀.map π))) :=
    (isUnit_resultant_iff_isCoprime hmon').mpr hsep
  rw [derivative_map] at hunit
  have hdeg : (f₀.map π).natDegree = f₀.natDegree := hmon.natDegree_map π
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (natDegree_map_le (p := derivative f₀) (f := π) :
      ((derivative f₀).map π).natDegree ≤ (derivative f₀).natDegree)
  have key : π (resultant f₀ (derivative f₀)) =
      (f₀.map π).coeff f₀.natDegree ^ k *
        (f₀.map π).resultant ((derivative f₀).map π) f₀.natDegree
          ((derivative f₀).map π).natDegree := by
    rw [← resultant_map_map, hk, resultant_add_right_deg _ _ _ _ _ le_rfl]
  have hcoeff : (f₀.map π).coeff f₀.natDegree = 1 := by
    rw [← hdeg]; exact hmon'.leadingCoeff
  rw [hcoeff, one_pow, one_mul] at key
  rw [hdeg] at hunit
  rw [key] at hπ0
  exact not_isUnit_zero (hπ0 ▸ hunit)

section AlgClosed

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {L : Type*} [Field L] [DecidableEq L] {W : WeierstrassCurve L}

theorem card_fibre_le_two (ξ : L) : Nat.card {y : L // W.toAffine.Equation ξ y} ≤ 2 := by
  rcases isEmpty_or_nonempty {y : L // W.toAffine.Equation ξ y} with hE | ⟨⟨y₀, hy₀⟩⟩
  · simp
  · have hmem : ∀ z : {y : L // W.toAffine.Equation ξ y},
        (z : L) ∈ ({y₀, W.toAffine.negY ξ y₀} : Finset L) := fun z => by
      rcases Affine.Y_eq_of_X_eq z.2 hy₀ rfl with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hinj : Function.Injective
        (fun z : {y : L // W.toAffine.Equation ξ y} =>
          (⟨z.1, hmem z⟩ : ({y₀, W.toAffine.negY ξ y₀} : Finset L))) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab
    calc Nat.card {y : L // W.toAffine.Equation ξ y}
        ≤ Nat.card ({y₀, W.toAffine.negY ξ y₀} : Finset L) :=
          Nat.card_le_card_of_injective _ hinj
      _ ≤ 2 := by
          rw [Nat.card_eq_finsetCard]
          exact (Finset.card_insert_le _ _).trans (by simp)

scoped instance finite_fibre (ξ : L) : Finite {y : L // W.toAffine.Equation ξ y} := by
  rcases isEmpty_or_nonempty {y : L // W.toAffine.Equation ξ y} with hE | ⟨⟨y₀, hy₀⟩⟩
  · infer_instance
  · have hset : {y : L | W.toAffine.Equation ξ y} ⊆ {y₀, W.toAffine.negY ξ y₀} :=
      fun y hy => Affine.Y_eq_of_X_eq hy hy₀ rfl
    exact (((Set.finite_singleton _).insert _).subset hset).to_subtype

variable [W.IsElliptic]

theorem mem_roots_toFinset_of_mem_torsionBy {n : ℕ} (hn : Odd n) (hnL : (n : L) ≠ 0)
    {x y : L} (h : W.toAffine.Nonsingular x y)
    (hP : (Point.some x y h : W.toAffine.Point) ∈ Submodule.torsionBy ℤ W.toAffine.Point n) :
    x ∈ (W.preΨ' n).roots.toFinset := by
  rw [Multiset.mem_toFinset, mem_roots (W.preΨ'_ne_zero hnL), IsRoot.def]
  have hnP : n • (Point.some x y h : W.toAffine.Point) = 0 := by
    have := (Submodule.mem_torsionBy_iff _ _).mp hP
    rwa [Nat.cast_smul_eq_nsmul] at this
  exact (Point.nsmul_some_eq_zero_iff_eval_prePsi W hn h).mp hnP

noncomputable def torsionToRoot {n : ℕ} (hn : Odd n) (hnL : (n : L) ≠ 0) :
    Submodule.torsionBy ℤ W.toAffine.Point n →
      Option ((ξ : (W.preΨ' n).roots.toFinset) × {y : L // W.toAffine.Equation ξ.1 y}) :=
  fun ⟨P, hP⟩ =>
    match P, hP with
    | 0, _ => none
    | .some x y h, hP =>
        some ⟨⟨x, mem_roots_toFinset_of_mem_torsionBy hn hnL h hP⟩, ⟨y, h.1⟩⟩

theorem torsionToRoot_injective {n : ℕ} (hn : Odd n) (hnL : (n : L) ≠ 0) :
    Function.Injective (torsionToRoot (W := W) hn hnL) := by
  rintro ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩ heq
  cases P₁ with
  | zero =>
    cases P₂ with
    | zero => rfl
    | some x y h => exact absurd heq (by simp [torsionToRoot])
  | some x₁ y₁ h₁ =>
    cases P₂ with
    | zero => exact absurd heq (by simp [torsionToRoot])
    | some x₂ y₂ h₂ =>
      simp only [torsionToRoot, Option.some.injEq] at heq
      have hx : x₁ = x₂ := congrArg (fun s => (s.1 : L)) heq
      subst hx
      have hy : y₁ = y₂ := congrArg (fun s => (s.2 : L)) heq
      subst hy
      rfl

theorem separable_preΨ'_of_isAlgClosed [IsAlgClosed L] {n : ℕ} (hn : Odd n) (hnL : (n : L) ≠ 0)
    (hcard : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) = n ^ 2) :
    (W.preΨ' n).Separable := by
  have hne : (W.preΨ' n : L[X]) ≠ 0 := W.preΨ'_ne_zero hnL
  have hdeg : (W.preΨ' n).natDegree = (n ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ' hnL, if_neg (Nat.not_even_iff_odd.mpr hn)]
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn.pos
  haveI : Finite (Submodule.torsionBy ℤ W.toAffine.Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.one_le_iff_ne_zero.mp hn1)

  have hcard_le : n ^ 2 ≤ 1 + 2 * (W.preΨ' n).roots.toFinset.card := by
    have hinj := torsionToRoot_injective (W := W) hn hnL
    haveI : ∀ ξ : (W.preΨ' n).roots.toFinset,
        Fintype {y : L // W.toAffine.Equation ξ.1 y} := fun ξ => Fintype.ofFinite _
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sigma] at hle
    calc n ^ 2 ≤ (∑ ξ : (W.preΨ' n).roots.toFinset,
          Fintype.card {y : L // W.toAffine.Equation ξ.1 y}) + 1 := hle
      _ ≤ (∑ _ξ : (W.preΨ' n).roots.toFinset, 2) + 1 := by
          refine Nat.add_le_add_right (Finset.sum_le_sum fun ξ _ => ?_) 1
          rw [← Nat.card_eq_fintype_card]
          exact card_fibre_le_two (W := W) ξ.1
      _ = 1 + 2 * (W.preΨ' n).roots.toFinset.card := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe]
          ring

  have hrootcard : Multiset.card (W.preΨ' n).roots = (n ^ 2 - 1) / 2 := by
    rw [← (IsAlgClosed.splits (W.preΨ' n)).natDegree_eq_card_roots, hdeg]
  have hsq : n ^ 2 % 2 = 1 := Nat.odd_iff.mp (Odd.pow hn)
  have hle' : (W.preΨ' n).roots.toFinset.card ≤ Multiset.card (W.preΨ' n).roots :=
    Multiset.toFinset_card_le _
  have heq : (W.preΨ' n).roots.toFinset.card = Multiset.card (W.preΨ' n).roots := by omega
  exact (nodup_roots_iff_of_splits hne (IsAlgClosed.splits _)).mp
    (Multiset.toFinset_card_eq_card_iff_nodup.mp heq)

end AlgClosed

section Field

open WeierstrassCurve

theorem separable_map_preΨ' {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : Odd n) (hnK : (n : K) ≠ 0) :
    ((W.preΨ' n).map (algebraMap F K)).Separable := by
  classical
  haveI : (WeierstrassCurve.Affine.baseChange W K).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F K)).IsElliptic
  have hcard := W.card_torsion_of_isAlgClosed (K := K) hnK
  have hmap : (W.preΨ' n).map (algebraMap F K) =
      (WeierstrassCurve.Affine.baseChange W K).preΨ' n :=
    (W.map_preΨ' (algebraMap F K) n).symm
  rw [hmap]
  exact separable_preΨ'_of_isAlgClosed hn hnK hcard

theorem separable_preΨ'_of_field {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : Odd n) (hnF : (n : F) ≠ 0) : (W.preΨ' n).Separable := by
  have hnK : (n : AlgebraicClosure F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (AlgebraicClosure F))]
    exact (_root_.map_ne_zero _).mpr hnF
  exact (separable_map (algebraMap F (AlgebraicClosure F))).mp (separable_map_preΨ' W hn hnK)

end Field

theorem separable_preΨ'_of_isUnit {R : Type*} [CommRing R] (W : WeierstrassCurve R) {n : ℕ}
    (hn : Odd n) (hu : IsUnit ((n : R) * W.Δ)) : (W.preΨ' n).Separable := by
  have hnu : IsUnit (n : R) := isUnit_of_mul_isUnit_left hu
  refine separable_of_forall_isMaximal ?_ (fun m hm => ?_)
  · nontriviality R
    rw [W.leadingCoeff_preΨ' hnu.ne_zero, if_neg (Nat.not_even_iff_odd.mpr hn)]
    exact hnu
  · letI := Ideal.Quotient.field m
    have hπu : IsUnit (Ideal.Quotient.mk m ((n : R) * W.Δ)) := hu.map _
    rw [map_mul, map_natCast, IsUnit.mul_iff] at hπu
    haveI : (W.map (Ideal.Quotient.mk m)).IsElliptic := ⟨by rw [W.map_Δ]; exact hπu.2⟩
    rw [← W.map_preΨ']
    exact separable_preΨ'_of_field (W.map (Ideal.Quotient.mk m)) hn hπu.1.ne_zero

end SeparablePrePsi
p2m_reactivate "P2MW.S_WeierstrassCurve_separable_prePsi_of_isUnit.SeparablePrePsi"

theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : Odd n) (hu : IsUnit ((n : R) * W.Δ)) : (W.preΨ' n).Separable :=
  SeparablePrePsi.separable_preΨ'_of_isUnit W hn hu

end S_WeierstrassCurve_separable_prePsi_of_isUnit
end P2MW
export P2MW.S_WeierstrassCurve_separable_prePsi_of_isUnit (solution)
