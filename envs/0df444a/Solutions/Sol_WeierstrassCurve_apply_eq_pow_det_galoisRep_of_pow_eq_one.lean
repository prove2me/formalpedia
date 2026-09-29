-- Prove2me | solution 1 for WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/85aba5e0-d6e3-50a9-9f4f-357f19737222

import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_pairing_torsionBy
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : n.Prime) (hnK : (n : K) ≠ 0) (σ : K ≃ₐ[F] K) (ζ : K) (hζ : ζ ^ n = 1) : σ ζ = ζ ^ (LinearMap.det ((DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ (W⁄K).Point n) σ).toZModLinearMap n)).val := by
  haveI : Fact n.Prime := ⟨hn⟩
  set V := Submodule.torsionBy ℤ (W⁄K).Point n with hV

  have hcard : Nat.card V = n ^ 2 := WeierstrassCurve.card_torsion_of_isAlgClosed W hnK
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hn.ne_zero)
  haveI : Module.Finite (ZMod n) V := Module.Finite.of_finite
  have h2 : Module.finrank (ZMod n) V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod n) (V := V)
    rw [hcard, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hn.two_le h).symm
  let b : Module.Basis (Fin 2) (ZMod n) V := Module.finBasisOfFinrankEq (ZMod n) V h2

  obtain ⟨e, haddL, haddR, halt, hgal, hnd⟩ := W.exists_pairing_torsionBy (K := K) hnK
  have hzeroL : ∀ B, e 0 B = 1 := fun B => by
    have h := haddL 0 0 B
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hzeroR : ∀ A, e A 0 = 1 := fun A => by
    have h := haddR A 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hpowL : ∀ (k : ℕ) (A B : V), e (k • A) B = e A B ^ k := by
    intro k A B
    induction k with
    | zero => rw [zero_nsmul, pow_zero, hzeroL]
    | succ k ih => rw [succ_nsmul, haddL, ih, pow_succ]
  have hpowR : ∀ (k : ℕ) (A B : V), e A (k • B) = e A B ^ k := by
    intro k A B
    induction k with
    | zero => rw [zero_nsmul, pow_zero, hzeroR]
    | succ k ih => rw [succ_nsmul, haddR, ih, pow_succ]
  have hsmulL : ∀ (x : ZMod n) (A B : V), e (x • A) B = e A B ^ x.val := by
    intro x A B
    conv_lhs => rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul]
    exact hpowL _ _ _
  have hsmulR : ∀ (x : ZMod n) (A B : V), e A (x • B) = e A B ^ x.val := by
    intro x A B
    conv_lhs => rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul]
    exact hpowR _ _ _
  have hskew : ∀ A B : V, e B A = (e A B)⁻¹ := by
    intro A B
    have h := halt (A + B)
    rw [haddL, haddR, haddR, halt, halt, one_mul, mul_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hpown : ∀ A B : V, e A B ^ n = 1 := by
    intro A B
    rw [← hpowL, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul, hzeroL]

  have hmod : ∀ u : Kˣ, u ^ n = 1 → ∀ a : ℕ, u ^ (a % n) = u ^ a := by
    intro u hu a
    conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, hu, one_pow, mul_one]
  have hvadd : ∀ u : Kˣ, u ^ n = 1 → ∀ x y : ZMod n, u ^ (x + y).val = u ^ x.val * u ^ y.val := by
    intro u hu x y
    rw [ZMod.val_add, hmod u hu, pow_add]
  have hvmul : ∀ u : Kˣ, u ^ n = 1 → ∀ x y : ZMod n, u ^ (x * y).val = (u ^ x.val) ^ y.val := by
    intro u hu x y
    rw [ZMod.val_mul, hmod u hu, pow_mul]
  have hvneg : ∀ u : Kˣ, u ^ n = 1 → ∀ x : ZMod n, u ^ (-x).val = (u ^ x.val)⁻¹ := by
    intro u hu x
    have h := hvadd u hu x (-x)
    rw [add_neg_cancel, ZMod.val_zero, pow_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm

  set f : V →ₗ[ZMod n] V := (DistribSMul.toAddMonoidHom V σ).toZModLinearMap n with hfdef
  have hf : ∀ A : V, f A = σ • A := fun A => rfl
  set M := LinearMap.toMatrix b b f with hMdef
  have hfb : ∀ j, f (b j) = M 0 j • b 0 + M 1 j • b 1 := by
    intro j
    have h := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at h
    rw [← h]
    simp only [hMdef, LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]

  set ζ₀ : Kˣ := e (b 0) (b 1) with hζ₀
  have hζ₀n : ζ₀ ^ n = 1 := hpown _ _
  have hσζ₀ : σ (ζ₀ : K) = (ζ₀ : K) ^ (LinearMap.det f).val := by
    have h1 : e (σ • b 0) (σ • b 1) = e (M 0 0 • b 0 + M 1 0 • b 1) (M 0 1 • b 0 + M 1 1 • b 1) := by
      rw [← hf, ← hf, hfb 0, hfb 1]
    have h2 : e (M 0 0 • b 0 + M 1 0 • b 1) (M 0 1 • b 0 + M 1 1 • b 1) =
        (ζ₀ ^ (M 0 0).val) ^ (M 1 1).val * ((ζ₀ ^ (M 0 1).val) ^ (M 1 0).val)⁻¹ := by
      rw [haddL, haddR, haddR, hsmulL, hsmulL, hsmulL, hsmulL, hsmulR, hsmulR, hsmulR, hsmulR,
        halt, halt, hskew (b 0) (b 1), ← hζ₀]
      simp only [one_pow, one_mul, mul_one, inv_pow, ← pow_mul]
      rw [Nat.mul_comm (M 1 1).val (M 0 0).val]
    have h3 : ζ₀ ^ (LinearMap.det f).val =
        (ζ₀ ^ (M 0 0).val) ^ (M 1 1).val * ((ζ₀ ^ (M 0 1).val) ^ (M 1 0).val)⁻¹ := by
      rw [hdet, sub_eq_add_neg, hvadd ζ₀ hζ₀n, hvneg ζ₀ hζ₀n, hvmul ζ₀ hζ₀n, hvmul ζ₀ hζ₀n]
    simp only [← pow_mul] at h2 h3
    have h4 := hgal σ (b 0) (b 1)
    rw [h1, h2, ← h3, Units.val_pow_eq_pow_val] at h4
    exact h4.symm
  have hζ₀1 : ζ₀ ≠ 1 := by
    intro h1
    apply b.ne_zero 0
    apply hnd
    intro Q'
    have hQ := b.sum_repr Q'
    rw [Fin.sum_univ_two] at hQ
    rw [← hQ, haddR, hsmulR, hsmulR, halt, one_pow, one_mul, ← hζ₀, h1, one_pow]
  have hprim : IsPrimitiveRoot (ζ₀ : K) n := by
    have hK1 : (ζ₀ : K) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hζ₀n, Units.val_one]
    have hK2 : (ζ₀ : K) ≠ 1 := fun h => hζ₀1 (Units.val_eq_one.mp h)
    have hord : orderOf (ζ₀ : K) = n := orderOf_eq_prime hK1 hK2
    have h := IsPrimitiveRoot.orderOf (ζ₀ : K)
    rwa [hord] at h

  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ
  rw [← hi, map_pow, hσζ₀, ← pow_mul, mul_comm, pow_mul]

end S_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one (solution)
