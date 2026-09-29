-- Prove2me | solution 1 for WeierstrassCurve.det_galoisRepModuleEnd_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b0e363ae-f12c-55ca-b1f1-81aba93e1803

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_WeilPairing
import Theorems.Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_WeierstrassCurve_exists_pairing_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace W7X

section Core

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

lemma neg_of_alternating (b : M →ₗ[F] M →ₗ[F] F) (halt : ∀ P, b P P = 0) (P Q : M) :
    b Q P = - b P Q := by
  have h := halt (P + Q)
  simp only [map_add, LinearMap.add_apply, halt P, halt Q, zero_add, add_zero] at h
  linear_combination h

lemma expand (e : Module.Basis (Fin 2) F M) (b : M →ₗ[F] M →ₗ[F] F) (halt : ∀ P, b P P = 0)
    (P Q : M) :
    b P Q = (e.repr P 0 * e.repr Q 1 - e.repr P 1 * e.repr Q 0) * b (e 0) (e 1) := by
  have hP : (e.repr P 0) • e 0 + (e.repr P 1) • e 1 = P := by
    have h := e.sum_repr P
    rwa [Fin.sum_univ_two] at h
  have hQ : (e.repr Q 0) • e 0 + (e.repr Q 1) • e 1 = Q := by
    have h := e.sum_repr Q
    rwa [Fin.sum_univ_two] at h
  calc b P Q = b ((e.repr P 0) • e 0 + (e.repr P 1) • e 1)
        ((e.repr Q 0) • e 0 + (e.repr Q 1) • e 1) := by rw [hP, hQ]
    _ = _ := by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, halt, neg_of_alternating b halt (e 0) (e 1)]
        ring

theorem det_eq_of_alternating_pairing
    (e : Module.Basis (Fin 2) F M) (g : M →ₗ[F] M) (χ : F)
    (b : M →ₗ[F] M →ₗ[F] F) (halt : ∀ P, b P P = 0) (hne : ∃ P Q, b P Q ≠ 0)
    (htwist : ∀ P Q, b (g P) (g Q) = χ * b P Q) :
    LinearMap.det g = χ := by
  classical
  obtain ⟨P, Q, hPQ⟩ := hne
  have hc : b (e 0) (e 1) ≠ 0 := by
    intro h
    exact hPQ (by rw [expand e b halt P Q, h, mul_zero])
  have h1 : b (g (e 0)) (g (e 1)) =
      (e.repr (g (e 0)) 0 * e.repr (g (e 1)) 1 - e.repr (g (e 0)) 1 * e.repr (g (e 1)) 0) *
        b (e 0) (e 1) := expand e b halt _ _
  have h2 : b (g (e 0)) (g (e 1)) = χ * b (e 0) (e 1) := htwist _ _
  have hdet : LinearMap.det g =
      e.repr (g (e 0)) 0 * e.repr (g (e 1)) 1 - e.repr (g (e 0)) 1 * e.repr (g (e 1)) 0 := by
    rw [← LinearMap.det_toMatrix e g, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply]
    ring
  have hkey := h1.symm.trans h2
  rw [hdet]
  exact mul_right_cancel₀ hc hkey

end Core

section General

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

theorem det_galoisRepModuleEnd_eq_of_isWeilPairing {p : ℕ} [hp : Fact p.Prime]
    (e : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (W'⁄K).Point p))
    {B : Submodule.torsionBy ℤ (W'⁄K).Point p → Submodule.torsionBy ℤ (W'⁄K).Point p → Kˣ}
    (hB : IsWeilPairing S W' p B) (σ : K ≃ₐ[S] K) (q : ℕ)
    (hσ : ∀ ζ : K, ζ ^ p = 1 → σ ζ = ζ ^ q) :
    LinearMap.det (galoisRepModuleEnd S W' p σ) = (q : ZMod p) := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩

  obtain ⟨P₀, Q₀, hζ_ne⟩ := hB.nondegenerate
  set ζ : Kˣ := B P₀ Q₀ with hζ_def
  have hζ_pow : ζ ^ p = 1 := (mem_rootsOfUnity p ζ).mp (hB.mem_rootsOfUnity P₀ Q₀)
  have horder : orderOf ζ = p := by
    rcases hp.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hζ_pow) with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hζ_ne
    · exact h
  have hζ_prim : IsPrimitiveRoot ζ p := by
    have h := IsPrimitiveRoot.orderOf ζ
    rwa [horder] at h
  have hmem' : ∀ P Q, B P Q ∈ Subgroup.zpowers ζ := fun P Q => by
    rw [hζ_prim.zpowers_eq]
    exact hB.mem_rootsOfUnity P Q

  set dlog : Subgroup.zpowers ζ → ZMod p :=
    fun x => hζ_prim.zmodEquivZPowers.symm (Additive.ofMul x) with hdlog_def
  have dlog_mul : ∀ x y : Subgroup.zpowers ζ, dlog (x * y) = dlog x + dlog y := by
    intro x y
    simp only [hdlog_def, ofMul_mul, map_add]
  have dlog_one : dlog 1 = 0 := by
    have h := dlog_mul 1 1
    rw [mul_one] at h
    exact (add_left_cancel (a := dlog 1) (b := 0) (c := dlog 1)
      (by rw [add_zero]; exact h)).symm
  have dlog_pow : ∀ (x : Subgroup.zpowers ζ) (m : ℕ), dlog (x ^ m) = (m : ZMod p) * dlog x := by
    intro x m
    induction m with
    | zero => simpa using dlog_one
    | succ k ih =>
        rw [pow_succ, dlog_mul, ih]
        push_cast
        ring
  have dlog_inj : Function.Injective dlog := by
    intro x y h
    exact Additive.ofMul.injective (hζ_prim.zmodEquivZPowers.symm.injective h)

  set B' : Submodule.torsionBy ℤ (W'⁄K).Point p → Submodule.torsionBy ℤ (W'⁄K).Point p →
      Subgroup.zpowers ζ := fun P Q => ⟨B P Q, hmem' P Q⟩ with hB'_def
  have bfun_add_left : ∀ P P' Q, dlog (B' (P + P') Q) = dlog (B' P Q) + dlog (B' P' Q) := by
    intro P P' Q
    have hmul : B' (P + P') Q = B' P Q * B' P' Q :=
      Subtype.ext (by simpa [hB'_def] using hB.add_left P P' Q)
    rw [hmul, dlog_mul]
  have bfun_add_right : ∀ P Q Q', dlog (B' P (Q + Q')) = dlog (B' P Q) + dlog (B' P Q') := by
    intro P Q Q'
    have hmul : B' P (Q + Q') = B' P Q * B' P Q' :=
      Subtype.ext (by simpa [hB'_def] using hB.add_right P Q Q')
    rw [hmul, dlog_mul]
  let brow : Submodule.torsionBy ℤ (W'⁄K).Point p →
      (Submodule.torsionBy ℤ (W'⁄K).Point p →ₗ[ZMod p] ZMod p) := fun P =>
    AddMonoidHom.toZModLinearMap p (AddMonoidHom.mk' (fun Q => dlog (B' P Q)) (bfun_add_right P))
  let b : Submodule.torsionBy ℤ (W'⁄K).Point p →ₗ[ZMod p]
      (Submodule.torsionBy ℤ (W'⁄K).Point p →ₗ[ZMod p] ZMod p) :=
    AddMonoidHom.toZModLinearMap p
      (AddMonoidHom.mk' brow (by
        intro P P'
        ext Q
        show dlog (B' (P + P') Q) = dlog (B' P Q) + dlog (B' P' Q)
        exact bfun_add_left P P' Q))
  have b_apply : ∀ P Q, b P Q = dlog (B' P Q) := fun _ _ => rfl
  have halt : ∀ P, b P P = 0 := by
    intro P
    have h1 : B' P P = 1 := Subtype.ext (by simpa [hB'_def] using hB.alternate P)
    rw [b_apply, h1, dlog_one]
  have hne : ∃ P Q, b P Q ≠ 0 := by
    refine ⟨P₀, Q₀, ?_⟩
    rw [b_apply]
    intro h0
    have h1 : B' P₀ Q₀ = 1 := dlog_inj (by rw [h0, dlog_one])
    have h2 : B P₀ Q₀ = 1 := by simpa [hB'_def] using congrArg Subtype.val h1
    exact hζ_ne h2

  have hKx : ∀ P Q, B (σ • P) (σ • Q) = (B P Q) ^ q := by
    intro P Q
    have hpow1 : ((B P Q : Kˣ) : K) ^ p = 1 := by
      have h := (mem_rootsOfUnity p (B P Q)).mp (hB.mem_rootsOfUnity P Q)
      have := congrArg (Units.val) h
      simpa using this
    have hequi := hB.equivariant σ P Q
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hequi]
    exact hσ _ hpow1
  have htwist : ∀ P Q,
      b (galoisRepModuleEnd S W' p σ P) (galoisRepModuleEnd S W' p σ Q) = (q : ZMod p) * b P Q := by
    intro P Q
    simp only [galoisRepModuleEnd_apply]
    rw [b_apply, b_apply]
    have hsub : B' (σ • P) (σ • Q) = (B' P Q) ^ q :=
      Subtype.ext (by simpa [hB'_def] using hKx P Q)
    rw [hsub, dlog_pow]

  exact det_eq_of_alternating_pairing e (galoisRepModuleEnd S W' p σ) (q : ZMod p) b halt hne htwist

end General

section AlgClosed

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]

theorem hasWeilPairing_of_isAlgClosed
    (E : WeierstrassCurve F) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) :
    HasWeilPairing F K E p := by
  have hpK : (p : K) ≠ 0 := by
    intro h
    apply hpF
    have h' : algebraMap F K (p : F) = algebraMap F K 0 := by
      rw [map_natCast, _root_.map_zero, h]
    exact (algebraMap F K).injective h'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, hl, hr, halt, hequi, hnd⟩ :=
    WeierstrassCurve.exists_pairing_torsionBy (K := K) E hpK

  have h0 : ∀ Q, e 0 Q = 1 := fun Q => by
    have h := hl 0 0 Q
    rw [zero_add] at h
    exact mul_right_injective (e 0 Q) (h.symm.trans (mul_one _).symm)

  have hpow : ∀ (m : ℕ) P Q, e (m • P) Q = (e P Q) ^ m := by
    intro m P Q
    induction m with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ k ih => rw [succ_nsmul, hl, ih, pow_succ]
  refine ⟨e, ⟨?_, hl, hr, halt, fun σ P Q => (hequi σ P Q).symm, ?_⟩⟩
  ·
    intro P Q
    rw [mem_rootsOfUnity, ← hpow]
    have hP : p • P = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℤ p P]
      exact Submodule.smul_torsionBy _ P
    rw [hP, h0]
  ·
    have hrank : Module.finrank (ZMod p)
        (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) = 2 :=
      WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two E hp hpF
    haveI : Nontrivial (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) :=
      Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
    obtain ⟨P, hP⟩ := exists_ne (0 : Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p)
    by_contra hcon
    push Not at hcon
    exact hP (hnd P fun Q => hcon P Q)

theorem det_galoisRepModuleEnd_eq_of_isAlgClosed
    (E : WeierstrassCurve F) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (σ : K ≃ₐ[F] K) (q : ℕ) (hσ : ∀ ζ : K, ζ ^ p = 1 → σ ζ = ζ ^ q) :
    LinearMap.det (galoisRepModuleEnd (K := K) F E p σ) = (q : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : Module.finrank (ZMod p)
      (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) = 2 :=
    WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two E hp hpF
  haveI : Module.Finite (ZMod p) (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) :=
    Module.finite_of_finrank_eq_succ hrank
  obtain ⟨B, hB⟩ := hasWeilPairing_of_isAlgClosed (K := K) E hp hpF
  exact det_galoisRepModuleEnd_eq_of_isWeilPairing (Module.finBasisOfFinrankEq _ _ hrank)
    hB σ q hσ

end AlgClosed

end W7X

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.det (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p σ) = (ℓ : ZMod p) := by
  refine W7X.det_galoisRepModuleEnd_eq_of_isAlgClosed E hp (by exact_mod_cast hp.ne_zero) σ ℓ ?_
  intro ζ hζ
  exact ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ ℓ p hA hσ
    ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp)) ζ hζ

end S_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq
end P2MW
export P2MW.S_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq (solution)
