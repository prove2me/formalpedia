-- Prove2me | solution 1 for WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0b26e58f-036f-5c4a-b678-1ec774925570

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_WeierstrassCurve_exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_stableLine_character_of_not_isGoodPrimeFor
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"
set_option autoImplicit false
open scoped WeierstrassCurve.Affine

noncomputable section

namespace WLightEB

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Module
open scoped WeierstrassCurve.Affine

private theorem galoisRepModuleEnd_sub_smul_mem_of_sign (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : Submodule (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
    (hM : ∀ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
      P ∈ M ↔ W.InZeroComponentAt A
        (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point))
    (ψ : ↥(A.decompositionSubgroup ℚ) →* ℤˣ)
    (hψ : ∀ σ : ↥(A.decompositionSubgroup ℚ),
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, p • y = 0 →
        W.InZeroComponentAt A
          ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • y - ((ψ σ : ℤˣ) : ℤ) • y))
    (σ : ↥(A.decompositionSubgroup ℚ))
    (v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) :
    galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v -
      ((Units.map (Int.castRingHom (ZMod p)).toMonoidHom (ψ σ) : (ZMod p)ˣ) : ZMod p) • v ∈ M := by

  have hv : p • (v : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    have h := (Submodule.mem_torsionBy_iff (R := ℤ) _ _).mp v.2
    rw [← natCast_zsmul]
    exact h

  have hsmul : ((Units.map (Int.castRingHom (ZMod p)).toMonoidHom (ψ σ) : (ZMod p)ˣ) : ZMod p) • v
      = ((ψ σ : ℤˣ) : ℤ) • v := by
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, eq_intCast,
      Int.cast_smul_eq_zsmul]

  have hX : ((galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v -
        ((Units.map (Int.castRingHom (ZMod p)).toMonoidHom (ψ σ) : (ZMod p)ˣ) : ZMod p) • v :
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
      = (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
          (v : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) -
        ((ψ σ : ℤˣ) : ℤ) • (v : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by
    rw [hsmul]
    rfl
  rw [hM, hX]
  exact hψ σ v hv

private theorem zeroComponent_submodule_ne_bot_ne_top (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hF : ∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      x ∈ F ↔ p ^ 1 • x = 0 ∧ W.InZeroComponentAt A x)
    (hcardF : Nat.card F = p ^ 1)
    (M : Submodule (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
    (hM : ∀ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
      P ∈ M ↔ W.InZeroComponentAt A
        (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point))
    (hcardT : Nat.card
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    M ≠ ⊥ ∧ M ≠ ⊤ := by
  have hp : p.Prime := Fact.out

  have e : M ≃ F :=
    { toFun := fun m => ⟨m.1.1,
        (hF _).mpr ⟨by
          rw [pow_one, ← natCast_zsmul]
          exact (Submodule.mem_torsionBy_iff (R := ℤ) _ _).mp m.1.2,
          (hM _).mp m.2⟩⟩
      invFun := fun x => ⟨⟨(x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
          (Submodule.mem_torsionBy_iff (R := ℤ) _ _).mpr (by
            have h := ((hF _).mp x.2).1
            rw [pow_one] at h
            rw [natCast_zsmul]
            exact h)⟩,
        (hM _).mpr ((hF _).mp x.2).2⟩
      left_inv := fun m => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  have hcardM : Nat.card M = p := by rw [Nat.card_congr e, hcardF, pow_one]
  constructor
  · rintro rfl
    rw [Nat.card_unique] at hcardM
    exact hp.one_lt.ne hcardM
  · rintro rfl
    rw [Nat.card_congr (Submodule.topEquiv.toEquiv), hcardT] at hcardM
    have h : p * p = p * 1 := by rw [← sq, hcardM, mul_one]
    exact hp.one_lt.ne' (mul_left_cancel₀ hp.ne_zero h)

private theorem exists_eq_smul_and_det_eq_mul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h2 : Module.finrank K V = 2) (M : Submodule K V)
    (hM0 : M ≠ ⊥) (hM1 : M ≠ ⊤) (φ : Module.End K V) (hstab : ∀ v ∈ M, φ v ∈ M) (d : K)
    (hquot : ∀ w : V, φ w - d • w ∈ M) :
    ∃ c : K, (∀ v ∈ M, φ v = c • v) ∧ LinearMap.det φ = c * d := by
  classical

  have hfinM : Module.finrank K M = 1 := by
    have hlt : Module.finrank K M < 2 := h2 ▸ Submodule.finrank_lt hM1
    have hne : Module.finrank K M ≠ 0 := fun h => hM0 (Submodule.finrank_eq_zero.mp h)
    omega
  obtain ⟨v₀, hv₀, hgen⟩ := finrank_eq_one_iff'.mp hfinM
  have hv₀' : (v₀ : V) ≠ 0 := fun h => hv₀ (Subtype.ext h)

  obtain ⟨c, hc⟩ := hgen ⟨φ v₀, hstab _ v₀.2⟩
  have hc' : φ (v₀ : V) = c • (v₀ : V) := by
    have h := congrArg Subtype.val hc
    simp only [SetLike.val_smul] at h
    exact h.symm
  refine ⟨c, ?_, ?_⟩
  · intro v hv
    obtain ⟨a, ha⟩ := hgen ⟨v, hv⟩
    have hav : v = a • (v₀ : V) := by
      have h := congrArg Subtype.val ha
      simp only [SetLike.val_smul] at h
      exact h.symm
    rw [hav, map_smul, hc']
    exact smul_comm a c _
  ·
    have hnot : ¬ ∀ x : V, x ∈ M := fun h => hM1 (Submodule.eq_top_iff'.mpr h)
    obtain ⟨w, hw⟩ := not_forall.mp hnot
    have hli : LinearIndependent K ![(v₀ : V), w] := by
      refine (LinearIndependent.pair_iff' hv₀').mpr fun a ha => hw ?_
      rw [← ha]
      exact M.smul_mem a v₀.2
    obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2) K V, ⇑b = ![(v₀ : V), w] :=
      ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2]),
        coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
    have hb0 : b 0 = (v₀ : V) := by rw [hb]; rfl
    have hb1 : b 1 = w := by rw [hb]; rfl

    obtain ⟨e, he⟩ := hgen ⟨φ w - d • w, hquot w⟩
    have he' : φ w = e • (v₀ : V) + d • w := by
      have h := congrArg Subtype.val he
      simp only [SetLike.val_smul] at h
      rw [eq_sub_iff_add_eq] at h
      exact h.symm
    have hφ0 : φ (b 0) = c • b 0 := by rw [hb0]; exact hc'
    have hφ1 : φ (b 1) = e • b 0 + d • b 1 := by rw [hb0, hb1]; exact he'
    rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, hφ0, hφ1]

private theorem galoisRepModuleEnd_eq_smul_of_detIsCyclotomic (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve ℤ)
    (hcard : Nat.card
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p))
    (hdet : (GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).DetIsCyclotomic p)
    (M : Submodule (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
    (hM0 : M ≠ ⊥) (hM1 : M ≠ ⊤)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hstab : ∀ v ∈ M,
      galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ v ∈ M)
    (d : ZMod p) (hd : d * d = 1)
    (hquot : ∀ w : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
      galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ w - d • w ∈ M)
    (a : ℕ) (hσa : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) :
    ∀ v ∈ M, galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ v =
      ((a : ZMod p) * d) • v := by
  have hp : p.Prime := Fact.out
  haveI : Finite
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 hp.pos.ne')
  have h2 : Module.finrank (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = 2 :=
    ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).finrank_eq
  obtain ⟨c, hc, hdetc⟩ := exists_eq_smul_and_det_eq_mul h2 M hM0 hM1
    (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ) hstab d hquot

  have hdet1 := hdet.2 1 σ a (by simpa only [pow_one] using hσa)
  have hspan : Ideal.span {((p ^ 1 : ℕ) : ZMod p)} = ⊥ := by
    rw [Ideal.span_singleton_eq_bot, pow_one, ZMod.natCast_self]
  rw [hspan, Ideal.mem_bot, sub_eq_zero] at hdet1
  change LinearMap.det
      (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ) =
    (a : ZMod p) at hdet1
  have hcd : c = (a : ZMod p) * d := by
    have h : c * d = (a : ZMod p) := hdetc.symm.trans hdet1
    calc c = c * (d * d) := by rw [hd, mul_one]
      _ = c * d * d := by ring
      _ = (a : ZMod p) * d := by rw [h]
  intro v hv
  rw [hc v hv, hcd]

private theorem exists_stableLine_character_of_parts (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hcard : Nat.card (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p))
    (hdet : (GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).DetIsCyclotomic p)
    (F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hF : ∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, x ∈ F ↔ p ^ 1 • x = 0 ∧ W.InZeroComponentAt A x)
    (hcardF : Nat.card F = p ^ 1)
    (M : Submodule (ZMod p) (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
    (hM : ∀ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p, P ∈ M ↔ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point))
    (hMstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ x ∈ M, σ • x ∈ M)
    (ψ : ↥(A.decompositionSubgroup ℚ) →* ℤˣ)
    (hψI : ∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → ψ σ = 1)
    (hψ : ∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, p • y = 0 →
      W.InZeroComponentAt A ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • y - ((ψ σ : ℤˣ) : ℤ) • y)) :
    ∃ (L : Submodule (ZMod p) (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
      (ψ : ↥(A.decompositionSubgroup ℚ) →* (ZMod p)ˣ),
      L ≠ ⊥ ∧ L ≠ ⊤ ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ v ∈ L,
        WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v ∈ L) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        ∀ v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v -
            ((ψ σ : (ZMod p)ˣ) : ZMod p) • v ∈ L) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) μ = μ ^ a) →
        ∀ v ∈ L,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v =
            ((a : ZMod p) * ((ψ σ : (ZMod p)ˣ) : ZMod p)) • v) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → ψ σ = 1) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ψ σ ^ 2 = 1) := by
  have hne := zeroComponent_submodule_ne_bot_ne_top p W A F hF hcardF M hM hcard

  have hsq : ∀ σ : ↥(A.decompositionSubgroup ℚ),
      (Units.map (Int.castRingHom (ZMod p)).toMonoidHom).comp ψ σ *
        (Units.map (Int.castRingHom (ZMod p)).toMonoidHom).comp ψ σ = 1 := fun σ => by
    rw [MonoidHom.comp_apply, ← map_mul, Int.units_mul_self, map_one]
  have hstab : ∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ v ∈ M,
      WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v ∈ M := fun σ v hv => by
    rw [galoisRepModuleEnd_apply]
    exact hMstab σ σ.2 v hv
  refine ⟨M, (Units.map (Int.castRingHom (ZMod p)).toMonoidHom).comp ψ, hne.1, hne.2, hstab,
    fun σ v => galoisRepModuleEnd_sub_smul_mem_of_sign p W A M hM ψ hψ σ v, ?_, ?_, ?_⟩
  · intro σ a hσa v hv
    have hd : (((Units.map (Int.castRingHom (ZMod p)).toMonoidHom).comp ψ σ : (ZMod p)ˣ) : ZMod p) *
        (((Units.map (Int.castRingHom (ZMod p)).toMonoidHom).comp ψ σ : (ZMod p)ˣ) : ZMod p) = 1 := by
      rw [← Units.val_mul, hsq σ, Units.val_one]
    exact galoisRepModuleEnd_eq_smul_of_detIsCyclotomic p W hcard hker hdet M hne.1 hne.2
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hstab σ) _ hd
      (fun w => galoisRepModuleEnd_sub_smul_mem_of_sign p W A M hM ψ hψ σ w) a hσa v hv
  · intro σ hσ
    rw [MonoidHom.comp_apply, hψI σ hσ, map_one]
  · intro σ
    rw [sq]
    exact hsq σ

end WLightEB

end

noncomputable section

namespace WLightEB

open scoped WeierstrassCurve.Affine

private theorem galoisFactorsThroughFiniteLevel_galoisRepModuleEnd_of_Δ_ne_zero (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (p : ℕ) [Fact p.Prime] :
    GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p) := by
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, eq_intCast]; exact_mod_cast hΔ⟩
  exact WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) p

end WLightEB

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hbad : ¬ W.IsGoodPrimeFor p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ (L : Submodule (ZMod p)
        (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
      (ψ : ↥(A.decompositionSubgroup ℚ) →* (ZMod p)ˣ),
      L ≠ ⊥ ∧ L ≠ ⊤ ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ v ∈ L,
        WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v ∈ L) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        ∀ v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
              (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v -
            ((ψ σ : (ZMod p)ˣ) : ZMod p) • v ∈ L) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) μ = μ ^ a) →
        ∀ v ∈ L,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
              (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v =
            ((a : ZMod p) * ((ψ σ : (ZMod p)ˣ) : ZMod p)) • v) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → ψ σ = 1) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ψ σ ^ 2 = 1) := by
  have hp : p.Prime := Fact.out
  have hpΔ : (p : ℤ) ∣ W.Δ := by simpa [WeierstrassCurve.IsGoodPrimeFor] using hbad
  have hpc₄ : ¬ (p : ℤ) ∣ W.c₄ := hW p hp hpΔ

  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, eq_intCast]; exact_mod_cast hΔ⟩
  have hcard : Nat.card (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ))
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hker := WLightEB.galoisFactorsThroughFiniteLevel_galoisRepModuleEnd_of_Δ_ne_zero W hΔ p
  have hΔ' : (W.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, eq_intCast]; exact_mod_cast hΔ
  have hdet := WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic
    (W.map (Int.castRingHom ℚ)) p hΔ' hcard hker

  obtain ⟨F, hF, hcardF, -, -⟩ :=
    WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction W p hp2 hΔ hpΔ hpc₄ A hA 1 le_rfl
  obtain ⟨M, hM, hMstab, -⟩ :=
    WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction W hp hΔ hpΔ hpc₄
      A hA hp

  obtain ⟨ψ, hψI, hψ⟩ :=
    WeierstrassCurve.exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor p hp2 W hΔ hW hbad A hA
  exact WLightEB.exists_stableLine_character_of_parts p W A hcard hker hdet F hF hcardF M hM hMstab ψ hψI hψ

end S_WeierstrassCurve_exists_stableLine_character_of_not_isGoodPrimeFor
end P2MW
export P2MW.S_WeierstrassCurve_exists_stableLine_character_of_not_isGoodPrimeFor (solution)
