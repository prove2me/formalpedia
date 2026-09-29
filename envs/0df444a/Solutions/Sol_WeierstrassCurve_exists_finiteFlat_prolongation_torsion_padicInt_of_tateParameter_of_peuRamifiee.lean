-- Prove2me | solution 1 for WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_tateParameter_of_peuRamifiee
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0557609a-a621-5831-af96-474cf658cefe

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_tateParameter
import Theorems.Thm_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
import Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_tateParameter_of_peuRamifiee
p2m_attr_erase "instance" "PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (hpr : p ∣ padicValInt p W.Δ)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hj : (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
            * (TateCurve.curve qT).Δ)
    (hv : ‖qT‖₊ = ((p : ℝ≥0) ^ padicValInt p W.Δ)⁻¹) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by

  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _

  obtain ⟨d, hd, s, hs, φ, hφ⟩ :=
    WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_tateParameter
      W p hΔ hpΔ hpc₄ qT hqT0 hqT1 hj

  have hp1 : (1 : ℝ) < (p : ℝ) := mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
  have hval : Padic.valuation qT = (padicValInt p W.Δ : ℤ) := by
    have h1 : ‖qT‖ = (p : ℝ) ^ (-Padic.valuation qT) := Padic.norm_eq_zpow_neg_valuation hqT0
    have h2 : ‖qT‖ = (p : ℝ) ^ (-(padicValInt p W.Δ : ℤ)) := by
      have hcoe : (‖qT‖₊ : ℝ) = ((p : ℝ) ^ padicValInt p W.Δ)⁻¹ := by
        rw [hv]; push_cast; rfl
      rw [← coe_nnnorm, hcoe, ← zpow_natCast, ← zpow_neg]
    have heq : -Padic.valuation qT = -(padicValInt p W.Δ : ℤ) :=
      (zpow_right_inj₀ hp0 hp1.ne').mp (h1.symm.trans h2)
    omega
  have hpr' : (p : ℤ) ∣ Padic.valuation qT := hval ▸ Int.natCast_dvd_natCast.mpr hpr

  have hE₂ := TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation
    p qT hqT0 hqT1 hpr'

  exact WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv
    p (W.map (Int.castRingHom ℚ_[p])) (TateCurve.curve qT) d hd s hs φ hφ hE₂

end S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_tateParameter_of_peuRamifiee
end P2MW
export P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_tateParameter_of_peuRamifiee (solution)
