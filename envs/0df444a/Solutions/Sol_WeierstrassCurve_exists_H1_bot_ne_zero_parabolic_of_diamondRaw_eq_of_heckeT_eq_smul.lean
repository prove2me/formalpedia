-- Prove2me | solution 1 for WeierstrassCurve.exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c2293187-92e1-5195-b3a0-c1f763f03c06

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Theorems.Thm_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open CongruenceSubgroup

namespace Ws23
namespace BoundaryExclusion

open scoped MatrixGroups

theorem mem_parabolicHoms_of_smul_mem {Γ : Subgroup SL(2, ℤ)} {κ : Type} [Field κ]
    {c : κ} (hc : c ≠ 0) {φ : Additive ↥Γ →+ κ}
    (h : c • φ ∈ ModularCurve.Period.parabolicHoms ℤ Γ κ) :
    φ ∈ ModularCurve.Period.parabolicHoms κ Γ κ := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at h ⊢
  intro γ hγ
  have := h γ hγ
  rw [AddMonoidHom.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

theorem main
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (v : CohCarrier.H1 N ⊥ κ) (hv : v ≠ 0)
    (hdia : ∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v = v)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊥ ℓ κ v = ((W.apOfModel ℓ : ℤ) : κ) • v) :
    ∃ v' : CohCarrier.H1 N ⊥ κ, v' ≠ 0 ∧
      v' ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ ∧
      (∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v' = v') ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT N ⊥ ℓ κ v' = ((W.apOfModel ℓ : ℤ) : κ) • v') := by
  classical

  have hnotS : ∀ ℓ : ℕ, W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p → ℓ ∉ S₀ := by
    intro ℓ hg hM hp hmem
    rcases hS₀ ℓ hmem with h | h | h
    · exact h hg
    · exact hM h
    · exact hp h
  refine ⟨v, hv, ?_, hdia, fun ℓ hℓ hg hM hN hp => heig ℓ hℓ hN (hnotS ℓ hg hM hp)⟩

  haveI : NeZero (N * M) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne M)⟩
  have hex := WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible p hp2 W hΔ hirr
    (N * M) {n : ℕ | n ≤ p * (N * M)} (Set.finite_le_nat _)
  push Not at hex
  obtain ⟨ℓ, hℓ, hℓS, hℓ1, hgood, ha2⟩ := hex
  have hbig : p * (N * M) < ℓ := not_le.1 hℓS
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hNM : N * M ≤ p * (N * M) := Nat.le_mul_of_pos_left (N * M) hp0
  have hN' : N ≤ N * M := Nat.le_mul_of_pos_right N hM0
  have hM' : M ≤ N * M := Nat.le_mul_of_pos_left M hN0
  have hp' : p ≤ p * (N * M) := Nat.le_mul_of_pos_right p (Nat.mul_pos hN0 hM0)
  have hℓN : ¬ ℓ ∣ N := fun h =>
    absurd (lt_of_le_of_lt ((Nat.le_of_dvd hN0 h).trans (hN'.trans hNM)) hbig) (lt_irrefl ℓ)
  have hℓM : ¬ ℓ ∣ M := fun h =>
    absurd (lt_of_le_of_lt ((Nat.le_of_dvd hM0 h).trans (hM'.trans hNM)) hbig) (lt_irrefl ℓ)
  have hℓp : ℓ ≠ p := fun h =>
    absurd (lt_of_le_of_lt (h.le.trans hp') hbig) (lt_irrefl ℓ)
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hT : CohCarrier.heckeT N ⊥ ℓ κ v = ((W.apOfModel ℓ : ℤ) : κ) • v :=
    heig ℓ hℓ hℓN (hnotS ℓ hgood hℓM hℓp)
  have h1N : ℓ ≡ 1 [MOD N] := (hℓ1.of_mul_left p).of_mul_right M
  have h1p : ℓ ≡ 1 [MOD p] := hℓ1.of_mul_right (N * M)
  have hpar := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one N ⊥ κ v ℓ hℓ hℓN h1N
  rw [hT] at hpar

  have hℓκ : ((ℓ + 1 : ℕ) : κ) = 2 := by
    rw [Nat.cast_add, Nat.cast_one, (CharP.natCast_eq_natCast κ p).2 h1p, Nat.cast_one]
    norm_num
  have hcoef : ((W.apOfModel ℓ : ℤ) : κ) • v - (ℓ + 1) • v = (((W.apOfModel ℓ : ℤ) : κ) - 2) • v := by
    rw [← Nat.cast_smul_eq_nsmul κ (ℓ + 1) v, hℓκ, sub_smul]
  rw [hcoef] at hpar

  have hc : ((W.apOfModel ℓ : ℤ) : κ) - 2 ≠ 0 := by

    generalize (W.apOfModel ℓ : ℤ) = a at ha2 ⊢
    intro h0
    apply ha2
    have h0' : ((a - 2 : ℤ) : κ) = 0 := by
      rw [Int.cast_sub, Int.cast_ofNat]; exact h0
    rw [CharP.intCast_eq_zero_iff κ p] at h0'
    have h2 : ((a - 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h0'
    rw [Int.cast_sub, Int.cast_ofNat, sub_eq_zero] at h2
    exact h2
  exact mem_parabolicHoms_of_smul_mem hc hpar

end Ws23.BoundaryExclusion

open CongruenceSubgroup in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (v : CohCarrier.H1 N ⊥ κ) (hv : v ≠ 0)
    (hdia : ∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v = v)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊥ ℓ κ v = ((W.apOfModel ℓ : ℤ) : κ) • v) :
    ∃ v' : CohCarrier.H1 N ⊥ κ, v' ≠ 0 ∧
      v' ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ ∧
      (∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v' = v') ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT N ⊥ ℓ κ v' = ((W.apOfModel ℓ : ℤ) : κ) • v') :=
  Ws23.BoundaryExclusion.main p hp2 W hΔ hirr N M S₀ hS₀ κ v hv hdia heig

end S_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul (solution)
