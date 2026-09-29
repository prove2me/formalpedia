-- Prove2me | solution 1 for TateCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cfb2cb7e-4b37-5c92-b37e-54f902e59c39

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
import Theorems.Thm_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
p2m_attr_erase "instance" "PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hpr : (p : ℤ) ∣ Padic.valuation qT) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  have hp := (Fact.out : p.Prime)
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hqT0' : (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) qT ≠ 0 :=
    fun h => hqT0 <| by
      have := (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
      exact this (h.trans (_root_.map_zero _).symm)

  obtain ⟨ζ, t, hζ, ht, φ, hφadd, hφG⟩ :=
    TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
      p hp5 qT hqT0 hqT1
  have ht0 : t ≠ 0 := fun h0 => hqT0' (by rw [← ht, h0, zero_pow hp.ne_zero])

  obtain ⟨k, hk⟩ := hpr
  set u : ℚ_[p] := qT * (p : ℚ_[p]) ^ (-Padic.valuation qT) with hu_def
  have hpnn : (p : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hu : ‖u‖₊ = 1 := by
    have hqT_nn : ‖qT‖₊ = (p : ℝ≥0) ^ (-Padic.valuation qT) := by
      rw [← NNReal.coe_inj, NNReal.coe_zpow]; push_cast
      exact Padic.norm_eq_zpow_neg_valuation hqT0
    have hp_nn : ‖(p : ℚ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by
      rw [← NNReal.coe_inj]; push_cast
      simpa using Padic.norm_p (p := p)
    rw [hu_def, nnnorm_mul, nnnorm_zpow, hqT_nn, hp_nn, inv_zpow, ← zpow_neg,
        ← zpow_add₀ hpnn, neg_neg, neg_add_cancel, zpow_zero]
  set η : AlgebraicClosure ℚ_[p] := t * algebraMap ℚ_[p] _ ((p : ℚ_[p]) ^ (-k)) with hη_def
  have hη : η ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) u := by
    rw [hη_def, mul_pow, ht, ← map_pow, ← zpow_natCast, ← zpow_mul, ← map_mul, hu_def, hk]
    ring_nf

  obtain ⟨H, instCR, instHA, hFin, hFlat, hCocomm, ψ, hψmul, hψG⟩ :=
    PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one p u hu ζ η hζ hη

  refine ⟨H, instCR, instHA, hFin, hFlat, hCocomm, ψ.symm.trans φ, ?_, ?_⟩
  ·
    intro f g
    have hsym : ψ.symm (f * g) = ψ.symm f + ψ.symm g := by
      apply ψ.injective
      rw [hψmul, ψ.apply_symm_apply, ψ.apply_symm_apply, ψ.apply_symm_apply]
    show φ (ψ.symm (f * g)) = φ (ψ.symm f) + φ (ψ.symm g)
    rw [hsym]
    exact Subtype.ext (by rw [Submodule.coe_add]; exact hφadd _ _)
  ·
    intro σ f g hgσ
    have hσζp : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨e, -, hσζ⟩ := hζ.eq_pow_of_pow_eq_one hσζp
    have hσtt : (σ t / t) ^ p = 1 := by
      rw [div_pow, ← map_pow, ht, AlgEquiv.commutes, div_self hqT0']
    obtain ⟨c, -, hσtc⟩ := hζ.eq_pow_of_pow_eq_one hσtt
    have hσt : σ t = ζ ^ c * t := ((eq_div_iff ht0).mp hσtc).symm
    have hση : σ η = ζ ^ c * η := by
      rw [hη_def, map_mul, hσt, AlgEquiv.commutes]; ring

    have hg_eq : g = ψ (e • (ψ.symm f).1 + c • (ψ.symm f).2, (ψ.symm f).2) := by
      have key : g.ofConv = (ψ (e • (ψ.symm f).1 + c • (ψ.symm f).2, (ψ.symm f).2)).ofConv := by
        ext h
        rw [hgσ h, hψG σ e c hσζ.symm hση (ψ.symm f).1 (ψ.symm f).2 h]
        simp only [Prod.mk.eta, ψ.apply_symm_apply]
      first
        | exact WithConv.ofConv_injective key
        | exact congrArg WithConv.toConv key
        | (rw [← WithConv.toConv_ofConv g, key, WithConv.toConv_ofConv])
    show φ (ψ.symm g) = σ • (φ (ψ.symm f))
    rw [hg_eq, ψ.symm_apply_apply,
        ← hφG σ e c hσζ.symm hσt (ψ.symm f).1 (ψ.symm f).2]

end S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le
end P2MW
export P2MW.S_TateCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_dvd_valuation_of_five_le (solution)
