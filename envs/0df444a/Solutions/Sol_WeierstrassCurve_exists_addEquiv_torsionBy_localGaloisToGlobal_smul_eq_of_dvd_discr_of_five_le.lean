-- Prove2me | solution 1 for WeierstrassCurve.exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b3bcdc75-f06d-5f9d-ae4b-27b19ebbed8c

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_tateParameter
import Theorems.Thm_TateCurve_exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul
import Theorems.Thm_Padic_forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open scoped NNReal WeierstrassCurve.Affine Classical
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace E87T0

theorem main
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    ∃ (qT : ℚ_[p]) (ζ t : AlgebraicClosure ℚ_[p])
      (Φ : (ZMod p × ZMod p) ≃+
        Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
      qT ≠ 0 ∧ ‖qT‖₊ = ((p : ℝ≥0) ^ padicValInt p W.Δ)⁻¹ ∧ IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
      ∀ τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ (e c : ℕ), τ ζ = ζ ^ e → τ t = ζ ^ c * t →
          ∀ i j : ZMod p, (localGaloisToGlobal p τ) • (Φ (i, j)) = Φ (e • i + c • j, j) := by
  have hp2 : p ≠ 2 := by omega

  obtain ⟨qT, hqT0, hqT1, hj, hv⟩ := W.exists_tateParameter_of_prime_dvd_discr p hΔ hpΔ hpc₄

  obtain ⟨d, hd, s, hs, φW, hφW⟩ :=
    W.exists_addEquiv_torsion_tateCurve_signTwist_of_tateParameter p hΔ hpΔ hpc₄ qT hqT0 hqT1 hj

  obtain ⟨ζ, t, hζ, ht, φT, hφTadd, hφTact⟩ :=
    TateCurve.exists_primitiveRoot_equiv_torsion_algebraicClosure_padic_of_five_le p hp5 qT hqT0 hqT1

  obtain ⟨ψ, hψinj, hψsmul⟩ :=
    W.exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul p p

  have hcardT : Nat.card (Submodule.torsionBy ℤ
      ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p) = p ^ 2 := by
    rw [← Nat.card_congr φT, Nat.card_prod, Nat.card_zmod, sq]
  have hcardW : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p) = p ^ 2 := by
    rw [Nat.card_congr φW.toEquiv, hcardT]
  haveI : Finite (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p) :=
    Nat.finite_of_card_ne_zero (by rw [hcardW]; positivity)
  haveI : Finite (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hψbij : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (by rw [hcard, hcardW])
  let ψE := AddEquiv.ofBijective ψ hψbij

  let φTa : (ZMod p × ZMod p) ≃+
      Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p :=
    { φT with map_add' := fun a b => by apply Subtype.ext; exact hφTadd a b }
  let Φ : (ZMod p × ZMod p) ≃+
      Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p :=
    φTa.trans (φW.symm.trans ψE.symm)
  refine ⟨qT, ζ, t, Φ, hqT0, hv, hζ, ht, ?_⟩
  intro τ hτ e c hτζ hτt i j

  have hτs : τ s = s := Padic.forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one p hp2 d hd s hs τ hτ

  apply ψE.injective
  show ψ ((localGaloisToGlobal p τ) • Φ (i, j)) = ψE (Φ (e • i + c • j, j))
  rw [hψsmul]
  have h1 : ψE (Φ (i, j)) = φW.symm (φT (i, j)) := by
    show ψE (ψE.symm (φW.symm (φTa (i, j)))) = _
    rw [AddEquiv.apply_symm_apply]; rfl
  have h2 : ψE (Φ (e • i + c • j, j)) = φW.symm (φT (e • i + c • j, j)) := by
    show ψE (ψE.symm (φW.symm (φTa (e • i + c • j, j)))) = _
    rw [AddEquiv.apply_symm_apply]; rfl
  change τ • ψE (Φ (i, j)) = ψE (Φ (e • i + c • j, j))
  rw [h1, h2]
  apply φW.injective
  rw [(hφW τ).1 hτs, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hφTact τ e c hτζ hτt i j]

end E87T0

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    ∃ (qT : ℚ_[p]) (ζ t : AlgebraicClosure ℚ_[p])
      (Φ : (ZMod p × ZMod p) ≃+
        Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
      qT ≠ 0 ∧ ‖qT‖₊ = ((p : ℝ≥0) ^ padicValInt p W.Δ)⁻¹ ∧ IsPrimitiveRoot ζ p ∧
      t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT ∧
      ∀ τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ (e c : ℕ), τ ζ = ζ ^ e → τ t = ζ ^ c * t →
          ∀ i j : ZMod p, (localGaloisToGlobal p τ) • (Φ (i, j)) = Φ (e • i + c • j, j) :=
  E87T0.main W p hp5 hΔ hpΔ hpc₄ hcard

end S_WeierstrassCurve_exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le
end P2MW
export P2MW.S_WeierstrassCurve_exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le (solution)
