-- Prove2me | solution 1 for WeierstrassCurve.rationalEndSubring_baseChange_eq_of_frobenius_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/00ac8b9c-74ef-53cd-97c1-27708bc76150

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_rationalEndSubring_baseChange_eq_of_frobenius_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map map_id Affine.Point Affine.Point.map baseChange evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul"
namespace FFDescent
p2m_open "WeierstrassCurve"

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_rationalEndSubring_baseChange_eq_of_frobenius_eq_smul.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

theorem evalEvalBC_map (p : F[X][Y]) (x y : k) :
    evalEvalBC k (p.map (mapRingHom (algebraMap F k))) x y = evalEvalBC k p x y := by
  have h1 : mapRingHom (algebraMap k k) = RingHom.id (k[X]) := by
    rw [show algebraMap k k = RingHom.id k from rfl, mapRingHom_id]
  rw [evalEvalBC, evalEvalBC, h1, Polynomial.map_id]

variable [DecidableEq k]

theorem isRationallyRepresented_baseChange {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁⁄k).Point →+ (W₂⁄k).Point} (hα : IsRationallyRepresented k W₁ W₂ α) :
    IsRationallyRepresented k (W₁.baseChange k) (W₂.baseChange k) α := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine ⟨nX.map (mapRingHom (algebraMap F k)), dX.map (mapRingHom (algebraMap F k)),
    nY.map (mapRingHom (algebraMap F k)), dY.map (mapRingHom (algebraMap F k)), B, hB, ?_⟩
  intro x y h hx
  simp only [evalEvalBC_map]
  exact hrep x y h hx

theorem rationalHomSet_subset_baseChange (W₁ W₂ : WeierstrassCurve F) :
    rationalHomSet k W₁ W₂ ⊆ rationalHomSet k (W₁.baseChange k) (W₂.baseChange k) := by
  rintro α (rfl | hα)
  · exact Or.inl rfl
  · exact Or.inr (isRationallyRepresented_baseChange hα)

theorem frobenius_bijective [Fintype F] [IsAlgClosed k] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) :
    Function.Bijective σ := by
  obtain ⟨p, hpF, n, hp, hn⟩ := FiniteField.card' (K := F)
  haveI := hpF
  haveI : CharP k p := ((algebraMap F k).charP_iff_charP p).mp hpF
  haveI : ExpChar k p := ExpChar.prime hp
  constructor
  · intro x y hxy
    have hxy' : σ x = σ y := hxy
    rw [hσ, hσ, hn] at hxy'
    exact iterateFrobenius_inj k p n hxy'
  · intro x
    have hq : 0 < Fintype.card F := Fintype.card_pos
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x hq
    exact ⟨z, by rw [hσ, hz]⟩

theorem rationalEndSubring_baseChange_eq [Fintype F] [IsAlgClosed k]
    (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (a : ℤ)
    (ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) :
    rationalEndSubring k (W.baseChange k) = rationalEndSubring k W := by

  let σ' : k ≃ₐ[F] k := AlgEquiv.ofBijective σ (frobenius_bijective σ hσ)
  have hσ' : ∀ x : k, σ' x = x ^ Fintype.card F := hσ
  have hσ'P : ∀ P : (W⁄k).Point, σ' • P = a • P := by
    intro P
    rw [algEquiv_smul_def]
    exact ha P
  apply le_antisymm
  ·
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    intro β hβ
    apply Subring.subset_closure
    refine mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul W W σ' hσ' hβ ?_
    intro P
    rw [hσ'P, hσ'P, map_zsmul]
  · show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    intro α hα
    exact Subring.subset_closure (rationalHomSet_subset_baseChange W W hα)

end WeierstrassCurve.FFDescent

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_rationalEndSubring_baseChange_eq_of_frobenius_eq_smul.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in
theorem solution
    {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k]
    (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (a : ℤ)
    (ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) :
    WeierstrassCurve.rationalEndSubring k (W.baseChange k) = WeierstrassCurve.rationalEndSubring k W :=
  WeierstrassCurve.FFDescent.rationalEndSubring_baseChange_eq W σ hσ a ha

end S_WeierstrassCurve_rationalEndSubring_baseChange_eq_of_frobenius_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_rationalEndSubring_baseChange_eq_of_frobenius_eq_smul (solution)
