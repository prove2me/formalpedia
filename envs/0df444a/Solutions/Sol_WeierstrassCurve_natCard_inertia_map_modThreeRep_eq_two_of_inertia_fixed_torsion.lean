-- Prove2me | solution 1 for WeierstrassCurve.natCard_inertia_map_modThreeRep_eq_two_of_inertia_fixed_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/40723859-6695-5214-a139-1a4fdb401ac4

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_DeligneOrdinaryShape
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_GaloisRep_exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible
import Theorems.Thm_WeierstrassCurve_exists_deligneOrdinaryShape_residualGaloisRepOf_of_ordinary_or_multiplicative
import Theorems.Thm_WeierstrassCurve_exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_inertia_map_modThreeRep_eq_two_of_inertia_fixed_torsion
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped MatrixGroups Matrix

namespace BridgeE4

theorem natCard_map_eq_of_det_injOn {Γ : Type*} [Group Γ] {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (f : Γ →* GL n R) (I : Subgroup Γ)
    (hinj : ∀ σ ∈ I, ∀ τ ∈ I, (f σ).val.det = (f τ).val.det → f σ = f τ) :
    Nat.card (I.map f) = Nat.card (I.map (Matrix.GeneralLinearGroup.det.comp f)) := by
  classical
  rw [← Subgroup.map_map]
  have hset : ((I.map f).map Matrix.GeneralLinearGroup.det : Set (Rˣ)) =
      Matrix.GeneralLinearGroup.det '' ((I.map f) : Set (GL n R)) := Subgroup.coe_map _ _
  have h1 : Nat.card ((I.map f).map (Matrix.GeneralLinearGroup.det) : Subgroup Rˣ)
      = Nat.card (Matrix.GeneralLinearGroup.det '' ((I.map f) : Set (GL n R))) := by
    rw [← hset]; rfl
  rw [h1, Nat.card_image_of_injOn]
  · rfl
  · rintro x ⟨σ, hσ, rfl⟩ y ⟨τ, hτ, rfl⟩ hdet
    apply hinj σ hσ τ hτ
    have := congrArg (fun u : Rˣ => (u : R)) hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this

theorem natCard_eq_two_of_neg_one_mem (S : Subgroup (ZMod 3)ˣ) (h : (-1 : (ZMod 3)ˣ) ∈ S) : Nat.card S = 2 := by
  have hG : Nat.card (ZMod 3)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide
  have hdvd : Nat.card S ∣ 2 := hG ▸ Subgroup.card_subgroup_dvd_card S
  have hne : Nat.card S ≠ 1 := by
    intro h1
    have hbot : S = ⊥ := Subgroup.eq_bot_of_card_eq S h1
    rw [hbot, Subgroup.mem_bot] at h
    exact absurd h (by decide)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd h1 hne
  · exact h2

theorem sq_eq_one_of_mulVec_eq_of_mulVec_eq_smul {K : Type*} [Field K] (N : Matrix (Fin 2) (Fin 2) K)
    (c v : Fin 2 → K) (hc : c ≠ 0) (hv : v ≠ 0) (hNc : N.mulVec c = c) (lam : K) (hNv : N.mulVec v = lam • v)
    (hdet : N.det ^ 2 = 1) : lam ^ 2 = 1 := by

  have hc0 := congrFun hNc 0
  have hc1 := congrFun hNc 1
  have hv0 := congrFun hNv 0
  have hv1 := congrFun hNv 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at hc0 hc1 hv0 hv1

  set d := c 0 * v 1 - c 1 * v 0 with hd
  have key : (N.det - lam) * d = 0 := by
    have e : N.det * d = (N 0 0 * c 0 + N 0 1 * c 1) * (N 1 0 * v 0 + N 1 1 * v 1)
        - (N 1 0 * c 0 + N 1 1 * c 1) * (N 0 0 * v 0 + N 0 1 * v 1) := by
      rw [Matrix.det_fin_two, hd]; ring
    rw [hc0, hc1, hv0, hv1] at e
    rw [sub_mul, e, hd]; ring
  rcases mul_eq_zero.mp key with h | h
  · rw [sub_eq_zero] at h; rw [← h]; exact hdet
  ·
    by_cases hl : lam = 1
    · rw [hl]; ring
    exfalso
    have hd0 : c 0 * v 1 = c 1 * v 0 := sub_eq_zero.mp h

    by_cases hc0z : c 0 = 0
    · have hc1z : c 1 ≠ 0 := by
        intro h1; apply hc; funext i; fin_cases i <;> simp [hc0z, h1]

      have hv0z : v 0 = 0 := by
        rw [hc0z, zero_mul] at hd0
        rcases mul_eq_zero.mp hd0.symm with h | h
        · exact absurd h hc1z
        · exact h

      rw [hc0z, mul_zero, zero_add] at hc0 hc1
      have hN11 : N 1 1 = 1 := by
        have : (N 1 1 - 1) * c 1 = 0 := by rw [sub_mul, one_mul, hc1, sub_self]
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hc1z

      have hv1z : v 1 ≠ 0 := by
        intro h1; apply hv; funext i; fin_cases i <;> simp [hv0z, h1]
      rw [hv0z, mul_zero, zero_add, hN11, one_mul] at hv1
      apply hl
      have : (lam - 1) * v 1 = 0 := by rw [sub_mul, one_mul, ← hv1, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact (sub_eq_zero.mp h)
      · exact absurd h hv1z
    ·
      have hprop : ∀ i, v i = (v 0 / c 0) * c i := by
        intro i; fin_cases i
        · show v 0 = v 0 / c 0 * c 0; field_simp
        · show v 1 = v 0 / c 0 * c 1; field_simp; linear_combination hd0
      have hNv' : ∀ i, (lam - 1) * v i = 0 := by
        intro i
        fin_cases i
        · show (lam - 1) * v 0 = 0
          have e := hv0
          rw [hprop 0, hprop 1] at e
          have : N 0 0 * (v 0 / c 0 * c 0) + N 0 1 * (v 0 / c 0 * c 1) = v 0 / c 0 * (N 0 0 * c 0 + N 0 1 * c 1) := by ring
          rw [this, hc0, ← hprop 0] at e
          rw [sub_mul, one_mul, ← e, sub_self]
        · show (lam - 1) * v 1 = 0
          have e := hv1
          rw [hprop 0, hprop 1] at e
          have : N 1 0 * (v 0 / c 0 * c 0) + N 1 1 * (v 0 / c 0 * c 1) = v 0 / c 0 * (N 1 0 * c 0 + N 1 1 * c 1) := by ring
          rw [this, hc1, ← hprop 1] at e
          rw [sub_mul, one_mul, ← e, sub_self]
      apply hv
      funext i
      rcases mul_eq_zero.mp (hNv' i) with h | h
      · exact absurd (sub_eq_zero.mp h) hl
      · simpa using h

theorem exists_nat_modThreeCyclotomicChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ a : ℕ, (∀ μ : AlgebraicClosure ℚ, μ ^ 3 = 1 → σ μ = μ ^ a) ∧
      ((WeierstrassCurve.modThreeCyclotomicChar σ : (ZMod 3)ˣ) : ZMod 3) = (a : ZMod 3) := by
  refine ⟨((WeierstrassCurve.modThreeCyclotomicChar σ : (ZMod 3)ˣ) : ZMod 3).val, ?_, ?_⟩
  · intro μ hμ
    have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ
    set t : (AlgebraicClosure ℚ)ˣ := Units.mk0 μ hμ0 with ht
    have htmem : t ∈ rootsOfUnity 3 (AlgebraicClosure ℚ) := by
      rw [mem_rootsOfUnity]; apply Units.ext; simp [ht, hμ]
    have spec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3) (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) htmem
    rw [WeierstrassCurve.modThreeCyclotomicChar_apply]

    simpa [ht] using spec
  · exact (ZMod.natCast_zmod_val _).symm

end BridgeE4

namespace Bridge

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

scoped instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

section Setup

variable (W : WeierstrassCurve ℤ)

theorem isElliptic_map (hΔ : W.Δ ≠ 0) : (W.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ, isUnit_iff_ne_zero]
  simpa using hΔ

theorem isElliptic_baseChange (hΔ : W.Δ ≠ 0) :
    ((W.map (Int.castRingHom ℚ)).baseChange Qb).IsElliptic :=
  haveI := isElliptic_map W hΔ
  inferInstanceAs (((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ Qb)).IsElliptic)

private abbrev _root_.Bridge.V : Type := Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄Qb).Point (3 : ℕ)

p2m_export "Bridge" "V"

noncomputable abbrev r : Γℚ →* Module.End (ZMod 3) (V W) :=
  galoisRepModuleEnd (K := Qb) ℚ (W.map (Int.castRingHom ℚ)) 3

theorem card_V (hΔ : W.Δ ≠ 0) : Nat.card (V W) = 3 ^ 2 := by
  haveI := isElliptic_baseChange W hΔ
  exact WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
    ((W.map (Int.castRingHom ℚ)).baseChange Qb) (n := 3) (by norm_num) (by norm_num)

theorem finite_V (hΔ : W.Δ ≠ 0) : Finite (V W) :=
  Nat.finite_of_card_ne_zero (by rw [card_V W hΔ]; norm_num)

theorem moduleFinite_V (hΔ : W.Δ ≠ 0) : Module.Finite (ZMod 3) (V W) :=
  haveI := finite_V W hΔ
  Module.Finite.of_finite

theorem finrank_V (hΔ : W.Δ ≠ 0) : Module.finrank (ZMod 3) (V W) = 2 := by
  haveI := moduleFinite_V W hΔ
  have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V W)
  rw [card_V W hΔ, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm

noncomputable def basisV (hΔ : W.Δ ≠ 0) : Module.Basis (Fin 2) (ZMod 3) (V W) :=
  haveI := moduleFinite_V W hΔ
  Module.finBasisOfFinrankEq (ZMod 3) (V W) (finrank_V W hΔ)

noncomputable def rho (hΔ : W.Δ ≠ 0) : Γℚ →* GL (Fin 2) (ZMod 3) :=
  (Units.map (LinearMap.toMatrixAlgEquiv (basisV W hΔ) :
      Module.End (ZMod 3) (V W) →* Matrix (Fin 2) (Fin 2) (ZMod 3))).comp (r W).toHomUnits

theorem rho_coe (hΔ : W.Δ ≠ 0) (σ : Γℚ) :
    ((rho W hΔ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      = LinearMap.toMatrix (basisV W hΔ) (basisV W hΔ) (r W σ) := rfl

theorem r_apply (σ : Γℚ) (x : V W) : r W σ x = σ • x := rfl

end Setup

open scoped Pointwise

section Clauses

variable (W : WeierstrassCurve ℤ)

theorem rho_eq_one_of_r_eq_one (hΔ : W.Δ ≠ 0) {σ : Γℚ} (h : r W σ = 1) : rho W hΔ σ = 1 := by
  apply Units.ext
  rw [rho_coe, h]
  exact LinearMap.toMatrix_id (basisV W hΔ)

theorem continuous_rho (hΔ : W.Δ ≠ 0) : Continuous (rho W hΔ) := by
  haveI := isElliptic_map W hΔ
  obtain ⟨L, hL, h1⟩ :=
    WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) 3
  haveI := hL

  have hle : L.fixingSubgroup ≤ (rho W hΔ).ker := fun τ hτ =>
    (MonoidHom.mem_ker).mpr
      (rho_eq_one_of_r_eq_one W hΔ (h1 τ ((IntermediateField.mem_fixingSubgroup_iff L τ).mp hτ)))
  have hker : IsOpen ((rho W hΔ).ker : Set Γℚ) :=
    Subgroup.isOpen_mono hle L.fixingSubgroup_isOpen

  refine continuous_of_continuousAt_one (rho W hΔ) ?_
  have hev : (rho W hΔ : Γℚ → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) =ᶠ[nhds 1] fun _ => 1 :=
    Filter.eventuallyEq_of_mem (hker.mem_nhds (rho W hΔ).ker.one_mem)
      (fun τ hτ => (MonoidHom.mem_ker).mp hτ)
  rw [ContinuousAt, Filter.tendsto_congr' hev, map_one]
  exact tendsto_const_nhds

theorem det_r_eq (hΔ : W.Δ ≠ 0) (σ : Γℚ) :
    (LinearMap.det (r W σ) : ZMod 3) = ((modThreeCyclotomicChar σ : (ZMod 3)ˣ) : ZMod 3) := by
  haveI := isElliptic_map W hΔ
  rw [modThreeCyclotomicChar_apply]
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht3 : ((t : Qbˣ) : Qb) ^ 3 = 1 := by
    have h := (mem_rootsOfUnity' 3 t).mp ht
    exact h
  have key := WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one (K := Qb)
    (W.map (Int.castRingHom ℚ)) Nat.prime_three (by norm_num) σ (t : Qb) ht3
  have hlin : (DistribSMul.toAddMonoidHom (V W) σ).toZModLinearMap 3 = r W σ :=
    LinearMap.ext fun _ => rfl
  rw [hlin] at key
  exact key

theorem det_rho (hΔ : W.Δ ≠ 0) (σ : Γℚ) :
    Matrix.GeneralLinearGroup.det (rho W hΔ σ) = modThreeCyclotomicChar σ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, rho_coe, LinearMap.det_toMatrix]
  exact det_r_eq W hΔ σ

theorem trace_rho (hΔ : W.Δ ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ)
    (hℓ3 : ℓ ≠ 3) (A : ValuationSubring Qb) (hA : A.LiesOverPrime ℓ) (σ : Γℚ)
    (hσ : A.IsFrobeniusAt σ ℓ) :
    ((rho W hΔ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace
      = (W.apOfModel ℓ : ZMod 3) := by
  rw [rho_coe, ← LinearMap.trace_eq_matrix_trace]
  exact WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel W 3 ℓ Nat.prime_three hℓ hℓ3 hgood
    A hA σ hσ

end Clauses

section More

variable (W : WeierstrassCurve ℤ)

theorem repr_r_apply (hΔ : W.Δ ≠ 0) (σ : Γℚ) (x : V W) :
    ⇑((basisV W hΔ).repr (r W σ x))
      = Matrix.mulVec ((rho W hΔ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
          ⇑((basisV W hΔ).repr x) := by
  rw [rho_coe, LinearMap.toMatrix_mulVec_repr]

theorem factorsThroughFiniteLevel_r (hΔ : W.Δ ≠ 0) : GaloisFactorsThroughFiniteLevel (r W) := by
  haveI := isElliptic_map W hΔ
  exact WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) 3

end More

section Identification

variable (W : WeierstrassCurve ℤ)

theorem factorsThroughFiniteLevel_of_continuous (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hρ : Continuous ρ) :
    GaloisFactorsThroughFiniteLevel ρ := by
  have hopen : IsOpen ((ρ.ker : Subgroup Γℚ) : Set Γℚ) := by
    have hset : ((ρ.ker : Subgroup Γℚ) : Set Γℚ) = ρ ⁻¹' {1} := by
      ext σ
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set (GL (Fin 2) (ZMod 3)))).preimage hρ
  obtain ⟨E, hE, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp (hopen.mem_nhds ρ.ker.one_mem)
  refine ⟨E, hE, fun σ hσ => ?_⟩
  have hmem : σ ∈ E.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff E σ).mpr hσ
  exact (MonoidHom.mem_ker).mp (hsub hmem)

theorem factorsThroughFiniteLevel_rho (hΔ : W.Δ ≠ 0) : GaloisFactorsThroughFiniteLevel (rho W hΔ) := by
  obtain ⟨L, hL, h1⟩ := factorsThroughFiniteLevel_r W hΔ
  exact ⟨L, hL, fun σ hσ => rho_eq_one_of_r_eq_one W hΔ (h1 σ hσ)⟩

theorem absIrred_of_surjective (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hs : Function.Surjective ρ)
    (u : Fin 2 → AlgebraicClosure (ZMod 3)) (hu : u ≠ 0) :
    ∃ σ : Γℚ, Matrix.mulVec ((ρ σ).val.map (algebraMap (ZMod 3) (AlgebraicClosure (ZMod 3)))) u ∉
      (AlgebraicClosure (ZMod 3)) ∙ u := by
  classical
  by_contra hall
  push Not at hall

  let U₁ : GL (Fin 2) (ZMod 3) :=
    ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩
  let U₂ : GL (Fin 2) (ZMod 3) :=
    ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩
  obtain ⟨σ₁, h₁⟩ := hs U₁
  obtain ⟨σ₂, h₂⟩ := hs U₂
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hall σ₁)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hall σ₂)
  rw [h₁] at ha
  rw [h₂] at hb
  have ha0 := congr_fun ha 0
  have ha1 := congr_fun ha 1
  have hb0 := congr_fun hb 0
  have hb1 := congr_fun hb 1
  simp [U₁, U₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at ha0 ha1 hb0 hb1

  have hu1 : u 1 = 0 := by
    by_contra h
    have ha' : a = 1 := by
      have := ha1
      field_simp at this
      linear_combination this
    rw [ha', one_mul] at ha0
    exact h (by linear_combination -ha0)
  have hu0 : u 0 = 0 := by
    rw [hu1] at hb1
    linear_combination -hb1
  exact hu (funext fun i => by fin_cases i <;> simp [hu0, hu1])

def badPrimes : Finset ℕ := (3 * W.Δ.natAbs).primeFactors

theorem not_mem_badPrimes (hΔ : W.Δ ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∉ badPrimes W) :
    ℓ ≠ 3 ∧ W.IsGoodPrimeFor ℓ := by
  have h3Δ : 3 * W.Δ.natAbs ≠ 0 := mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr hΔ)
  have hndvd : ¬ ℓ ∣ 3 * W.Δ.natAbs := fun hd => h (Nat.mem_primeFactors.mpr ⟨hℓ, hd, h3Δ⟩)
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hndvd (dvd_mul_right 3 _)
  · show ¬ ((ℓ : ℤ) ∣ W.Δ)
    intro hd
    exact hndvd (Dvd.dvd.mul_left (Int.natCast_dvd.mp hd) 3)

theorem charpoly_eq (hΔ : W.Δ ≠ 0) (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
          ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace = (W.apOfModel ℓ : ZMod 3))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hS : ℓ ∉ badPrimes W) (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Γℚ)
    (hA : A.LiesOverPrime ℓ) (hτ : A.IsFrobeniusAt τ ℓ) :
    (ρ τ).val.charpoly = (rho W hΔ τ).val.charpoly := by
  obtain ⟨hℓ3, hgood⟩ := not_mem_badPrimes W hΔ hℓ hS
  have htr1 : (ρ τ).val.trace = (W.apOfModel ℓ : ZMod 3) := htr ℓ hℓ hgood hℓ3 A hA τ hτ
  have htr2 : (rho W hΔ τ).val.trace = (W.apOfModel ℓ : ZMod 3) :=
    trace_rho W hΔ hℓ hgood hℓ3 A hA τ hτ
  have hdet1 : (ρ τ).val.det = ((modThreeCyclotomicChar τ : (ZMod 3)ˣ) : ZMod 3) := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet τ]
  have hdet2 : (rho W hΔ τ).val.det = ((modThreeCyclotomicChar τ : (ZMod 3)ˣ) : ZMod 3) := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_rho W hΔ τ]
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, htr1, htr2, hdet1, hdet2]

theorem exists_conj (hΔ : W.Δ ≠ 0) (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hρ : Continuous ρ)
    (hs : Function.Surjective ρ)
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
          ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace = (W.apOfModel ℓ : ZMod 3)) :
    ∃ g : GL (Fin 2) (ZMod 3), ∀ σ : Γℚ, (rho W hΔ σ).val = g.val * (ρ σ).val * (g⁻¹).val :=
  GaloisRep.exists_conj_of_charpoly_frobenius_eq_of_absolutelyIrreducible
    (fun M _ _ _ => FrobeniusDensity.statement M) ρ (rho W hΔ)
    (factorsThroughFiniteLevel_of_continuous ρ hρ) (factorsThroughFiniteLevel_rho W hΔ)
    (absIrred_of_surjective ρ hs) (badPrimes W)
    (fun ℓ hℓ hS A τ hA hτ => charpoly_eq W hΔ ρ hdet htr ℓ hℓ hS A τ hA hτ)

end Identification

section Conjugation

theorem natCard_map_eq_of_conj {Γ : Type*} [Group Γ] {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (f f' : Γ →* GL n R) (g : GL n R)
    (h : ∀ σ : Γ, (f' σ).val = g.val * (f σ).val * (g⁻¹).val) (I : Subgroup Γ) :
    Nat.card (I.map f') = Nat.card (I.map f) := by
  have hf' : f' = (MulAut.conj g).toMonoidHom.comp f := by
    refine MonoidHom.ext fun σ => Units.ext ?_
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
      Units.val_mul]
    exact h σ
  rw [hf', ← Subgroup.map_map]
  exact Nat.card_congr
    ((I.map f).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv.symm

end Conjugation

section Local

variable (W : WeierstrassCurve ℤ)

theorem exists_matrix_model (hΔ : W.Δ ≠ 0) :
    ∃ b : Module.Basis (Fin 2) (ZMod 3)
        ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf 3 (card_V W hΔ)
            (factorsThroughFiniteLevel_r W hΔ)).baseChangeAlong (RingHom.id (ZMod 3))).V),
      ∀ σ : Γℚ, (rho W hΔ σ).val = LinearMap.toMatrix b b
        (((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf 3 (card_V W hΔ)
            (factorsThroughFiniteLevel_r W hΔ)).baseChangeAlong (RingHom.id (ZMod 3))).ρ σ)) := by
  letI : Algebra (ZMod 3) (ZMod 3) := (RingHom.id (ZMod 3)).toAlgebra
  refine ⟨Algebra.TensorProduct.basis (ZMod 3) (basisV W hΔ), fun σ => ?_⟩
  show (rho W hΔ σ).val =
    LinearMap.toMatrix (Algebra.TensorProduct.basis (ZMod 3) (basisV W hΔ))
      (Algebra.TensorProduct.basis (ZMod 3) (basisV W hΔ)) ((r W σ).baseChange (ZMod 3))
  rw [LinearMap.toMatrix_baseChange, rho_coe]
  ext i j
  simp

theorem mulVec_coords_eq (hΔ : W.Δ ≠ 0) {σ : Γℚ} {x : V W} (h : σ • x = x) :
    (rho W hΔ σ).val *ᵥ ⇑((basisV W hΔ).repr x) = ⇑((basisV W hΔ).repr x) := by
  rw [← repr_r_apply, r_apply, h]

theorem coords_ne_zero (hΔ : W.Δ ≠ 0) {x : V W} (hx : x ≠ 0) : ⇑((basisV W hΔ).repr x) ≠ 0 := by
  intro h
  apply hx
  have h' : (basisV W hΔ).repr x = 0 := by
    ext i
    simpa using congr_fun h i
  simpa using h'

theorem det_rho_val (hΔ : W.Δ ≠ 0) (σ : Γℚ) :
    (rho W hΔ σ).val.det = ((modThreeCyclotomicChar σ : (ZMod 3)ˣ) : ZMod 3) := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_rho W hΔ σ]

theorem units_zmod_three_sq (u : (ZMod 3)ˣ) : ((u : ZMod 3)) ^ 2 = 1 := by
  revert u
  decide

theorem det_rho_val_sq (hΔ : W.Δ ≠ 0) (σ : Γℚ) : (rho W hΔ σ).val.det ^ 2 = 1 := by
  rw [det_rho_val]
  exact units_zmod_three_sq _

theorem exists_inertia_det_eq_neg_one (hΔ : W.Δ ≠ 0) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime 3) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, Matrix.GeneralLinearGroup.det (rho W hΔ σ) = -1 := by
  obtain ⟨σ, hσ, hdet⟩ := WeierstrassCurve.det_galoisRep_surjOn_inertia W 3 hΔ A hA (-1)
  refine ⟨σ, hσ, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, rho_coe, LinearMap.det_toMatrix]
  exact hdet

theorem natCard_map_det_rho (hΔ : W.Δ ≠ 0) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime 3) :
    Nat.card ((A.inertiaSubgroupIn ℚ).map (Matrix.GeneralLinearGroup.det.comp (rho W hΔ))) = 2 := by
  apply BridgeE4.natCard_eq_two_of_neg_one_mem
  obtain ⟨σ, hσ, hdet⟩ := exists_inertia_det_eq_neg_one W hΔ A hA
  exact Subgroup.mem_map.mpr ⟨σ, hσ, by simpa using hdet⟩

theorem det_of_shape {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) (h10 : M 1 0 = 0)
    (h11 : M 1 1 = 1) : M.det = M 0 0 := by
  rw [Matrix.det_fin_two, h10, h11]; ring

theorem entry_eq_one_of_shape {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K) (c : Fin 2 → K)
    (hc : c ≠ 0) (hc1 : c 1 = 0) (hMc : M *ᵥ c = c) : M 0 0 = 1 := by
  have hc0 : c 0 ≠ 0 := by
    intro h0; apply hc; funext i; fin_cases i <;> simp [h0, hc1]
  have e := congr_fun hMc 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc1, mul_zero, add_zero] at e
  have : (M 0 0 - 1) * c 0 = 0 := by rw [sub_mul, e, one_mul, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hc0

theorem eq_of_shape {K : Type*} [Field K] (M N : Matrix (Fin 2) (Fin 2) K) (c : Fin 2 → K) (hc1 : c 1 ≠ 0)
    (hM10 : M 1 0 = 0) (hM11 : M 1 1 = 1) (hN10 : N 1 0 = 0) (hN11 : N 1 1 = 1)
    (hMc : M *ᵥ c = c) (hNc : N *ᵥ c = c) (h00 : M 0 0 = N 0 0) : M = N := by
  have eM := congr_fun hMc 0
  have eN := congr_fun hNc 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at eM eN
  have h01 : M 0 1 = N 0 1 := by
    have : (M 0 1 - N 0 1) * c 1 = 0 := by rw [sub_mul]; linear_combination eM - eN - c 0 * h00
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc1
  rw [Matrix.eta_fin_two M, Matrix.eta_fin_two N, h00, h01, hM10, hN10, hM11, hN11]

theorem det_injOn_of_ordinary (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (hord : ((3 : ℕ) : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (3 ^ 2 - 1) / 2 ∧ ¬ ((3 : ℕ) : ℤ) ∣ (W.preΨ' 3).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 3)
    (c : Fin 2 → ZMod 3) (hc0 : c ≠ 0) (hc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (rho W hΔ σ).val *ᵥ c = c) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      (rho W hΔ σ).val.det = (rho W hΔ τ).val.det → rho W hΔ σ = rho W hΔ τ := by
  classical
  obtain ⟨b, hb⟩ := exists_matrix_model W hΔ
  obtain ⟨frob, hfrob⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime Nat.prime_three A hA

  let χ : ↥(A.decompositionSubgroup ℚ) →* ZMod 3 :=
    ((Units.coeHom (ZMod 3)).comp modThreeCyclotomicChar).comp (A.decompositionSubgroup ℚ).subtype
  have hχ : ∀ σ : ↥(A.decompositionSubgroup ℚ), ∃ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ 3 = 1 → (σ : Γℚ) μ = μ ^ a) ∧ χ σ = (a : ZMod 3) :=
    fun σ => BridgeE4.exists_nat_modThreeCyclotomicChar σ
  obtain ⟨ap, hshape⟩ :=
    WeierstrassCurve.exists_deligneOrdinaryShape_residualGaloisRepOf_of_ordinary_or_multiplicative W 3
      (by norm_num) (RingHom.id (ZMod 3)) hΔ hW hord (card_V W hΔ) (factorsThroughFiniteLevel_r W hΔ)
      (rho W hΔ) b hb A hA frob hfrob χ hχ
  obtain ⟨g, h10, h11, -, h00, -⟩ := hshape

  set R : ↥(A.decompositionSubgroup ℚ) →* GL (Fin 2) (ZMod 3) :=
    (rho W hΔ).comp (A.decompositionSubgroup ℚ).subtype with hR
  have R_apply : ∀ σ' : ↥(A.decompositionSubgroup ℚ), R σ' = rho W hΔ (σ' : Γℚ) := fun σ' => rfl

  have lift : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∃ σ' : ↥(A.decompositionSubgroup ℚ),
      σ' ∈ A.inertiaSubgroup ℚ ∧ (σ' : Γℚ) = σ := fun σ hσ =>
    Subgroup.mem_map.mp (show σ ∈ (A.inertiaSubgroup ℚ).map _ from hσ)

  set c' : Fin 2 → ZMod 3 := g.val *ᵥ c with hc'
  have hc'fix : ∀ σ' : ↥(A.decompositionSubgroup ℚ), (σ' : Γℚ) ∈ A.inertiaSubgroupIn ℚ →
      (g * R σ' * g⁻¹).val *ᵥ c' = c' := by
    intro σ' hσ'
    have e : (g * R σ' * g⁻¹).val * g.val = g.val * (R σ').val := by
      rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    rw [hc', Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, R_apply, hc _ hσ']
  have hc'0 : c' ≠ 0 := by
    intro h
    apply hc0
    have e : (g⁻¹).val *ᵥ c' = c := by
      rw [hc', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← e, h, Matrix.mulVec_zero]

  have hdetM : ∀ σ' : ↥(A.decompositionSubgroup ℚ), σ' ∈ A.inertiaSubgroup ℚ →
      (rho W hΔ (σ' : Γℚ)).val.det = (g * R σ' * g⁻¹).val 0 0 := by
    intro σ' hI
    rw [← det_of_shape _ (h10 σ') (h11 σ' hI), Units.val_mul, Units.val_mul, Matrix.det_units_conj, R_apply]

  have hc'1 : c' 1 ≠ 0 := by
    intro h1
    obtain ⟨σ₀, hσ₀, hdet₀⟩ := exists_inertia_det_eq_neg_one W hΔ A hA
    obtain ⟨σ₀', hI₀, rfl⟩ := lift σ₀ hσ₀
    have h1' : (g * R σ₀' * g⁻¹).val 0 0 = 1 :=
      entry_eq_one_of_shape _ c' hc'0 h1 (hc'fix σ₀' hσ₀)
    have : (rho W hΔ (σ₀' : Γℚ)).val.det = 1 := by rw [hdetM σ₀' hI₀, h1']
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet₀] at this
    exact absurd this (by decide)

  intro σ hσ τ hτ hdet
  obtain ⟨σ', hIσ, rfl⟩ := lift σ hσ
  obtain ⟨τ', hIτ, rfl⟩ := lift τ hτ
  have hMN : (g * R σ' * g⁻¹).val = (g * R τ' * g⁻¹).val :=
    eq_of_shape _ _ c' hc'1 (h10 σ') (h11 σ' hIσ) (h10 τ') (h11 τ' hIτ) (hc'fix σ' hσ) (hc'fix τ' hτ)
      (by rw [← hdetM σ' hIσ, ← hdetM τ' hIτ, hdet])
  have hMN' : g * R σ' * g⁻¹ = g * R τ' * g⁻¹ := Units.ext hMN
  have : R σ' = R τ' := by
    have := congrArg (fun u => g⁻¹ * u * g) hMN'
    simpa [mul_assoc] using this
  rwa [R_apply, R_apply] at this

theorem false_of_supersingular (hΔ : W.Δ ≠ 0) (hgood : W.IsGoodPrimeFor 3)
    (hss : ∀ i, 1 ≤ i → i < (3 ^ 2 - 1) / 2 → ((3 : ℕ) : ℤ) ∣ (W.preΨ' 3).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 3)
    (c : Fin 2 → ZMod 3) (hc0 : c ≠ 0) (hc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (rho W hΔ σ).val *ᵥ c = c) :
    False := by
  classical
  obtain ⟨b, hb⟩ := exists_matrix_model W hΔ
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (3 : AlgebraicClosure ℚ) (by norm_num : 0 < 3 ^ 2 - 1)
  obtain ⟨ψk, v, hv0, hv⟩ :=
    WeierstrassCurve.exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular W 3
      (by norm_num) (RingHom.id (ZMod 3)) hgood hss (card_V W hΔ) (factorsThroughFiniteLevel_r W hΔ)
      (rho W hΔ) b hb A hA π hπ
  have aux : ∀ e : ℕ, (∀ σ ∈ A.inertiaSubgroupIn ℚ,
      (Matrix.GeneralLinearGroup.map ψk (rho W hΔ σ)).val *ᵥ v = (A.tameCharacter π σ ^ e) • v) →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, (A.tameCharacter π σ ^ e) ^ 2 = 1 := by
    intro e he σ hσ
    have hmap : (Matrix.GeneralLinearGroup.map ψk (rho W hΔ σ)).val = (rho W hΔ σ).val.map ψk := rfl
    apply BridgeE4.sq_eq_one_of_mulVec_eq_of_mulVec_eq_smul ((rho W hΔ σ).val.map ψk) (ψk ∘ c) v
    · intro h
      apply hc0
      funext i
      exact ψk.injective (by simpa using congr_fun h i)
    · exact hv0
    · funext i
      rw [← RingHom.map_mulVec, hc σ hσ]
      rfl
    · rw [← hmap]
      exact he σ hσ
    · have hdet : ((rho W hΔ σ).val.map ψk).det = ψk (rho W hΔ σ).val.det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply]
      rw [hdet, ← map_pow, det_rho_val_sq, map_one]
  have main : ∃ e : ℕ, (e = 1 ∨ e = 3) ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, (A.tameCharacter π σ ^ e) ^ 2 = 1 := by
    rcases hv with h1 | h3
    · exact ⟨1, Or.inl rfl, aux 1 (fun σ hσ => by simpa using h1 σ hσ)⟩
    · exact ⟨3, Or.inr rfl, aux 3 h3⟩
  obtain ⟨e, he, hall⟩ := main
  have hπ8 : π ^ 8 = ((3 : ℕ) : AlgebraicClosure ℚ) := by norm_num at hπ ⊢; exact hπ
  obtain ⟨σ₀, hσ₀, hprim⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter A Nat.prime_three hA
      (m := 8) (by norm_num) hπ8
  have h1 : A.tameCharacter π σ₀ ^ (e * 2) = 1 := by rw [pow_mul]; exact hall σ₀ hσ₀
  have hdvd : 8 ∣ e * 2 := hprim.dvd_of_pow_eq_one _ h1
  rcases he with rfl | rfl <;> omega

theorem natCard_map_rho_eq_two (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 3)
    (x : V W) (hx : x ≠ 0) (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) :
    Nat.card ((A.inertiaSubgroupIn ℚ).map (rho W hΔ)) = 2 := by
  set c : Fin 2 → ZMod 3 := ⇑((basisV W hΔ).repr x) with hcdef
  have hc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (rho W hΔ σ).val *ᵥ c = c := fun σ hσ =>
    mulVec_coords_eq W hΔ (hfix σ hσ)
  have hc0 : c ≠ 0 := coords_ne_zero W hΔ hx
  by_cases hord : ((3 : ℕ) : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (3 ^ 2 - 1) / 2 ∧ ¬ ((3 : ℕ) : ℤ) ∣ (W.preΨ' 3).coeff i
  · rw [BridgeE4.natCard_map_eq_of_det_injOn (rho W hΔ) _ (det_injOn_of_ordinary W hΔ hW hord A hA c hc0 hc)]
    exact natCard_map_det_rho W hΔ A hA
  · exfalso
    push Not at hord
    obtain ⟨h3, hss⟩ := hord
    exact false_of_supersingular W hΔ h3 hss A hA c hc0 hc

end Local

theorem bridge (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hρ : Continuous ρ) (hsurj : Function.Surjective ρ)
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
          ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace
            = (W.apOfModel ℓ : ZMod 3))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 3)
    (x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (3 : ℕ))
    (hx : x ≠ 0) (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) :
    Nat.card ((A.inertiaSubgroupIn ℚ).map ρ) = 2 := by
  obtain ⟨g, hg⟩ := exists_conj W hΔ ρ hρ hsurj hdet htr
  rw [← natCard_map_eq_of_conj ρ (rho W hΔ) g hg (A.inertiaSubgroupIn ℚ)]
  exact natCard_map_rho_eq_two W hΔ hW A hA x hx hfix

end Bridge
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_inertia_map_modThreeRep_eq_two_of_inertia_fixed_torsion.Bridge"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (hirr : W.ModRepIsIrreducible 3)
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hcont : Continuous ρ) (hsurj : Function.Surjective ρ)
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
          ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace
            = (W.apOfModel ℓ : ZMod 3))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 3)
    (x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (3 : ℕ))
    (hx : x ≠ 0) (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) :
    Nat.card ((A.inertiaSubgroupIn ℚ).map ρ) = 2 :=
  Bridge.bridge W hΔ hW ρ hcont hsurj hdet htr A hA x hx hfix

end S_WeierstrassCurve_natCard_inertia_map_modThreeRep_eq_two_of_inertia_fixed_torsion
end P2MW
export P2MW.S_WeierstrassCurve_natCard_inertia_map_modThreeRep_eq_two_of_inertia_fixed_torsion (solution)
