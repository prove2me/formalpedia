-- Prove2me | solution 1 for WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isOrdinaryAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/547ed16b-09ef-5dc3-a8f9-480945bee170

import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_WeierstrassCurve_galoisRep_ordinaryLineAt
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isOrdinaryAt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open IsLocalRing Module Polynomial
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace LCMazur

private theorem exists_basis_of_ne_bot_of_ne_top {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (h2 : finrank k V = 2) (L : Submodule k V) (hbot : L ≠ ⊥)
    (htop : L ≠ ⊤) : ∃ b : Module.Basis (Fin 2) k V, L = k ∙ b 0 := by
  obtain ⟨w, hwL, hw0⟩ := (Submodule.ne_bot_iff L).mp hbot
  obtain ⟨u, huL⟩ : ∃ u : V, u ∉ L := not_forall.mp (mt Submodule.eq_top_iff'.mpr htop)
  have hli : LinearIndependent k ![w, u] :=
    (LinearIndependent.pair_iff' hw0).mpr fun a ha => huL (ha ▸ L.smul_mem a hwL)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h2, Fintype.card_fin]), ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero]
  refine (Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem w L).mpr hwL) ?_).symm
  rw [finrank_span_singleton hw0]
  have hlt : finrank k L < 2 := h2 ▸ Submodule.finrank_lt htop
  have hne : finrank k L ≠ 0 := fun h0 => hbot (Submodule.finrank_eq_zero.mp h0)
  omega

private theorem exists_isPrimitiveRoot (n : ℕ) [NeZero n] :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ n :=
  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n

private theorem modEq_of_forall_apply_eq_pow (n : ℕ) [NeZero n]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {a a' : ℕ} (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a)
    (ha' : ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a') : a ≡ a' [MOD n] := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot n
  have h : ζ ^ a = ζ ^ a' := by rw [← ha ζ hζ.pow_eq_one, ha' ζ hζ.pow_eq_one]
  have hmod := (hζ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mp h
  rwa [← hζ.eq_orderOf] at hmod

private theorem det_galoisRepModuleEnd_eq_natCast (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hΔ : W.Δ ≠ 0) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {a : ℕ}
    (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) :
    LinearMap.det (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p σ) = (a : ZMod p) := by
  have hp : p.Prime := Fact.out
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmod : a ≡ (LinearMap.det ((DistribSMul.toAddMonoidHom
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) σ).toZModLinearMap p)).val
      [MOD p] :=
    modEq_of_forall_apply_eq_pow p σ ha
      (fun ζ hζ => W.apply_eq_pow_det_galoisRep_of_pow_eq_one hp hpK σ ζ hζ)
  have hext : galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p σ =
      (DistribSMul.toAddMonoidHom
        (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) σ).toZModLinearMap p :=
    LinearMap.ext fun _ => rfl
  rw [hext, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod, ZMod.natCast_zmod_val]

private theorem exists_mem_inertiaSubgroupIn_apply_eq_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ 2 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h2 : ((ZMod.unitOfCoprime 2 hcop : (ZMod p)ˣ) : ZMod p).val = 2 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
    exact ZMod.val_ofNat_of_lt (Fact.out)
  obtain ⟨σ, hσ, h⟩ :=
    P.exists_mem_inertiaSubgroupIn_apply_eq_pow hp hP (ZMod.unitOfCoprime 2 hcop)
  refine ⟨σ, hσ, fun μ hμ => ?_⟩
  have h' := h μ hμ
  rw [h2] at h'
  exact h'

private theorem isOrdinaryAt_ofResidualGaloisRep {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    {p : ℕ}
    (hline : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule k ρ.V, L ≠ ⊤ ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
    (hne : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ₀ ≠ 1) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsOrdinaryAt p := by
  intro P hP
  obtain ⟨L, hLtop, hL⟩ := hline P hP
  obtain ⟨σ₀, hσ₀, hσ₀1⟩ := hne P hP
  have hgen : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈
      Submodule.span k {x : ρ.V | ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∃ v : ρ.V, x = ρ.ρ σ v - v} :=
    fun σ hσ v => Submodule.subset_span ⟨σ, hσ, v, rfl⟩
  have htop : Submodule.span k
      {x : ρ.V | ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∃ v : ρ.V, x = ρ.ρ σ v - v} ≠ ⊤ := by
    refine ne_top_of_le_ne_top hLtop (Submodule.span_le.mpr ?_)
    rintro _ ⟨σ, hσ, v, rfl⟩
    exact hL σ hσ v
  have hbot : Submodule.span k
      {x : ρ.V | ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∃ v : ρ.V, x = ρ.ρ σ v - v} ≠ ⊥ := by
    intro h
    apply hσ₀1
    refine LinearMap.ext fun v => ?_
    have hv := hgen σ₀ hσ₀ v
    rw [h, Submodule.mem_bot, sub_eq_zero] at hv
    exact hv
  have hstab : ∀ τ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ Submodule.span k
      {x : ρ.V | ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∃ v : ρ.V, x = ρ.ρ σ v - v},
      ρ.ρ τ v ∈ Submodule.span k
        {x : ρ.V | ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∃ v : ρ.V, x = ρ.ρ σ v - v} := by
    intro τ hτ v hv
    refine (Submodule.map_span_le (ρ.ρ τ) _ _).mpr ?_ (Submodule.mem_map_of_mem hv)
    rintro _ ⟨σ, hσ, w, rfl⟩
    have hconj : τ * σ * τ⁻¹ ∈ P.inertiaSubgroupIn ℚ := by
      obtain ⟨σ', hσ', rfl⟩ := Subgroup.mem_map.mp hσ
      refine Subgroup.mem_map.mpr ⟨⟨τ, hτ⟩ * σ' * ⟨τ, hτ⟩⁻¹, ?_, rfl⟩
      rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hσ' ⊢
      rw [map_mul, map_mul, map_inv, hσ', mul_one, mul_inv_cancel]
    have key : ρ.ρ τ (ρ.ρ σ w) = ρ.ρ (τ * σ * τ⁻¹) (ρ.ρ τ w) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]
    rw [(ρ.ρ τ).map_sub, key]
    exact hgen _ hconj _
  obtain ⟨b, hb⟩ := exists_basis_of_ne_bot_of_ne_top ρ.finrank_eq _ hbot htop
  exact ⟨_, ⟨b, hb⟩, hstab, hgen⟩

end LCMazur

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (hord : (p : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p)) :
    (GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).IsOrdinaryAt p := by
  have hp : p.Prime := Fact.out
  have hΔ' : (W.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    simpa [WeierstrassCurve.map_Δ] using hΔ
  refine LCMazur.isOrdinaryAt_ofResidualGaloisRep _
    (W.galoisRep_ordinaryLineAt p hp2 hΔ hW hord) (fun P hP => ?_)
  obtain ⟨σ₀, hσ₀, h2⟩ := LCMazur.exists_mem_inertiaSubgroupIn_apply_eq_sq hp hp2 P hP
  refine ⟨σ₀, hσ₀, fun h1 => ?_⟩
  have hdet := LCMazur.det_galoisRepModuleEnd_eq_natCast (W.map (Int.castRingHom ℚ)) p hΔ' σ₀ h2
  have h1' : galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ₀
      = 1 := h1
  rw [h1', map_one, Nat.cast_ofNat] at hdet
  have h10 : (2 : ZMod p) - 1 = 0 := by rw [← hdet, sub_self]
  norm_num at h10

end S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isOrdinaryAt
end P2MW
export P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isOrdinaryAt (solution)
