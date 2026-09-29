-- Prove2me | solution 1 for WeierstrassCurve.exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3faab08d-640f-5385-8582-e3ee3936106a

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one
import Theorems.Thm_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open CongruenceSubgroup

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (hN : 4 ≤ N) (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (hocc : HeckeEis.IsEigensystemH1 N (1 : Representation κ (Gamma0 N) κ) (fun _ => LinearMap.id) S₀
      (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ))) :
    ∃ φ₀ : CohCarrier.H1 N ⊥ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊥) ℤ ∧
      (¬ ∃ ψ : CohCarrier.H1 N ⊥ ℤ, φ₀ = (p : ℤ) • ψ) ∧
      (∀ σ : Gamma0 N, ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.diamondRaw N ⊥ ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.heckeT N ⊥ ℓ ℤ φ₀ - (W.apOfModel ℓ) • φ₀ = (p : ℤ) • ψ)  := by
  obtain ⟨φ, hφ0, hpar, hdia, heig⟩ := WeierstrassCurve.exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one p hp2 W hΔ hirr N M S₀ hS₀ κ hocc
  obtain ⟨φ₀, hpar₀, hnd, hdia₀, hT⟩ := CohCarrier.exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul p N hN κ φ hφ0 hpar hdia
    {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ ∣ N ∨ ℓ = p} (fun ℓ => W.apOfModel ℓ)
    (fun ℓ hℓ hℓE => by
      simp only [Set.mem_setOf_eq, not_or, not_not] at hℓE
      exact heig ℓ hℓ hℓE.1 hℓE.2.1 hℓE.2.2.1 hℓE.2.2.2)
  exact ⟨φ₀, hpar₀, hnd, hdia₀, fun ℓ hℓ hgood hℓM hℓN hℓp =>
    hT ℓ hℓ (by
      simp only [Set.mem_setOf_eq, not_or, not_not]
      exact ⟨hgood, hℓM, hℓN, hℓp⟩)⟩

end S_WeierstrassCurve_exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one
end P2MW
export P2MW.S_WeierstrassCurve_exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one (solution)
