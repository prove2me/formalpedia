-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c46cd556-d930-5214-bc58-368a6d931664

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval
import Theorems.Thm_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval
import Theorems.Thm_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) [Fact n.Prime]
    (hbc : ∀ (L : Type) [Field L] [Algebra K L],
        Nonempty (pullback (projModelStrCR W.toProjective)
            (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          ≅ projModelCR (W.toProjective.baseChange L)))
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by
  classical
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _

  have hℓ : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 →
      ∃ P : (W.toProjective.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0 := by
    intro F _ _ _ _ ℓ hℓp hℓF
    have hcard : Nat.card ↥(Submodule.torsionBy ℤ (W⁄F).Point ℓ) = ℓ ^ 2 :=
      WeierstrassCurve.card_torsion_of_isAlgClosed W hℓF
    have hne0 : Nat.card ↥(Submodule.torsionBy ℤ (W⁄F).Point ℓ) ≠ 0 := by
      rw [hcard]; exact pow_ne_zero 2 hℓp.pos.ne'
    have : Finite ↥(Submodule.torsionBy ℤ (W⁄F).Point ℓ) := (Nat.card_ne_zero.mp hne0).2
    have hnt : Nontrivial ↥(Submodule.torsionBy ℤ (W⁄F).Point ℓ) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      exact one_lt_pow₀ hℓp.one_lt two_ne_zero
    obtain ⟨⟨P, hP⟩, hPne⟩ := exists_ne (0 : ↥(Submodule.torsionBy ℤ (W⁄F).Point ℓ))
    refine ⟨P, fun h => hPne (Subtype.ext h), ?_⟩
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP

  have hfin : IsFinite (G.schemeKerStr n) :=
    WeierstrassProjModel.isFinite_schemeKerStr_of_isPointsEval W.toProjective hbc G ev hev hℓ
      (Fact.out : n.Prime).pos

  obtain ⟨A, instCR, instHA, hfinA, hcocomm, eH, heH_mul, heH_gal⟩ :=
    WeierstrassProjModel.exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
      K W n G ev hev hfin

  obtain ⟨e', he'_ev, he'_add, he'_gal⟩ :=
    WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_of_isPointsEval
      W.toProjective G ev hev (AlgebraicClosure K) n

  refine ⟨A, instCR, instHA, hfinA, hcocomm, eH.trans e', ?_, ?_⟩
  ·
    intro f g
    apply Subtype.ext

    have hmul := heH_mul f g
    have hclosed : G.mul _ (eH f).1 (eH g).1 ∈
        G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) n := by
      rw [← hmul]; exact (eH (f * g)).2
    have := he'_add (eH f) (eH g) hclosed
    simp only [Equiv.trans_apply]
    rw [show eH (f * g) = ⟨G.mul _ (eH f).1 (eH g).1, hclosed⟩ from Subtype.ext hmul]
    exact_mod_cast congrArg Subtype.val this
  ·
    intro σ f g hfg
    apply Subtype.ext
    simp only [Equiv.trans_apply]
    have hgal := heH_gal σ f g hfg
    have hclosed : galTwist σ (eH f).1 ∈
        G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) n := by
      rw [← hgal]; exact (eH g).2
    rw [show eH g = ⟨galTwist σ (eH f).1, hclosed⟩ from Subtype.ext hgal]
    have := he'_gal σ (eH f) hclosed

    rw [this]
    rfl

end S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval (solution)
