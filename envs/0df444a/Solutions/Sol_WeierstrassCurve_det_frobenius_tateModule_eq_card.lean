-- Prove2me | solution 1 for WeierstrassCurve.det_frobenius_tateModule_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0de856e2-c360-59fa-907f-9260bdb1d365

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_pairing_torsionBy
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_det_frobenius_tateModule_eq_card
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace DetFrobeniusTateModule

section Pairing

variable {T : Type*} [AddCommGroup T] {G : Type*} [CommGroup G] (e : T → T → G)

theorem pair_left_zsmul (hl : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q)
    (m : ℤ) (P Q : T) : e (m • P) Q = e P Q ^ m := by
  let φ : T →+ Additive G :=
    AddMonoidHom.mk' (fun R => Additive.ofMul (e R Q)) fun R R' => by
      show Additive.ofMul (e (R + R') Q) = Additive.ofMul (e R Q) + Additive.ofMul (e R' Q)
      rw [hl, ofMul_mul]
  have h : φ (m • P) = m • φ P := map_zsmul φ m P
  change Additive.ofMul (e (m • P) Q) = m • Additive.ofMul (e P Q) at h
  rw [← ofMul_zpow] at h
  exact Additive.ofMul.injective h

theorem pair_right_zsmul (hr : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q')
    (m : ℤ) (P Q : T) : e P (m • Q) = e P Q ^ m := by
  let φ : T →+ Additive G :=
    AddMonoidHom.mk' (fun R => Additive.ofMul (e P R)) fun R R' => by
      show Additive.ofMul (e P (R + R')) = Additive.ofMul (e P R) + Additive.ofMul (e P R')
      rw [hr, ofMul_mul]
  have h : φ (m • Q) = m • φ Q := map_zsmul φ m Q
  change Additive.ofMul (e P (m • Q)) = m • Additive.ofMul (e P Q) at h
  rw [← ofMul_zpow] at h
  exact Additive.ofMul.injective h

theorem pair_swap (hl : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q)
    (hr : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q') (halt : ∀ P, e P P = 1) (P Q : T) :
    e Q P = (e P Q)⁻¹ := by
  have h := halt (P + Q)
  rw [hl, hr, hr, halt, halt, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

end Pairing

end DetFrobeniusTateModule

open DetFrobeniusTateModule in
theorem solution {F : Type*} [Field F] [Fintype F] {k : Type} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : F) ≠ 0) : LinearMap.det (TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ) = (Fintype.card F : ℤ_[ℓ]) := by

  have hℓk : ∀ n : ℕ, ((ℓ ^ n : ℕ) : k) ≠ 0 := fun n => by
    rw [Nat.cast_pow]
    refine pow_ne_zero _ fun h => hℓ ?_
    rw [← map_natCast (algebraMap F k), map_eq_zero] at h
    exact h
  have hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ 2 :=
    fun n => W.card_torsion_of_isAlgClosed (K := k) (hℓk n)

  set b := TateModule.basisOfCard hcard with hb
  set f := TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ with hf
  rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  set A := LinearMap.toMatrix b b f with hA
  have hcol : ∀ j : Fin 2, f (b j) = A 0 j • b 0 + A 1 j • b 1 := fun j => by
    have h := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at h
    rw [hA, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    exact h.symm

  have hlev : ∀ (j : Fin 2) (n : ℕ),
      σ • ((b j : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n
        = (((A 0 j).appr n : ℕ) : ℤ) • ((b 0 : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n
          + (((A 1 j).appr n : ℕ) : ℤ) • ((b 1 : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n :=
    fun j n => by
      have h := congrArg (fun z : TateModule ℓ (W⁄k).Point => (z : ℕ → (W⁄k).Point) n) (hcol j)
      simpa only [hf, TateModule.rep_apply, TateModule.coe_add, Pi.add_apply,
        TateModule.smul_apply] using h

  refine PadicInt.ext_of_toZModPow.mp fun n => ?_

  obtain ⟨e, hl, hr, halt, hgal, hnd⟩ :=
    W.exists_pairing_torsionBy (K := k) (n := ℓ ^ n) (hℓk n)
  have hPmem : ((b 0 : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n
      ∈ Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ) :=
    TateModule.proj_mem_torsionBy n (b 0)
  have hQmem : ((b 1 : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n
      ∈ Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ) :=
    TateModule.proj_mem_torsionBy n (b 1)
  set P : Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ) := ⟨_, hPmem⟩ with hP
  set Q : Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ) := ⟨_, hQmem⟩ with hQ

  set a : ℕ := (A 0 0).appr n with ha
  set b' : ℕ := (A 0 1).appr n with hb'
  set c : ℕ := (A 1 0).appr n with hc
  set d : ℕ := (A 1 1).appr n with hd
  set q : ℕ := Fintype.card F with hq
  have hσP : σ • P = (a : ℤ) • P + (c : ℤ) • Q := Subtype.ext (hlev 0 n)
  have hσQ : σ • Q = (b' : ℤ) • P + (d : ℤ) • Q := Subtype.ext (hlev 1 n)
  have hswap : e Q P = (e P Q)⁻¹ := pair_swap e hl hr halt P Q

  have h1 : e (σ • P) (σ • Q) = e P Q ^ (q : ℤ) := by
    apply Units.ext
    rw [hgal, hσ, zpow_natCast, Units.val_pow_eq_pow_val]

  have h2 : e (σ • P) (σ • Q) = e P Q ^ ((a : ℤ) * d - (b' : ℤ) * c) := by
    rw [hσP, hσQ, hl, pair_left_zsmul e hl, pair_left_zsmul e hl, hr, hr,
      pair_right_zsmul e hr, pair_right_zsmul e hr, pair_right_zsmul e hr, pair_right_zsmul e hr,
      halt, halt, hswap]
    simp only [one_zpow, one_mul, mul_one]
    rw [← zpow_mul, inv_zpow', ← zpow_mul, ← zpow_add]
    congr 1
    ring
  have hg : e P Q ^ (((a : ℤ) * d - (b' : ℤ) * c) - q) = 1 := by
    rw [zpow_sub, ← h2, h1, mul_inv_cancel]
  set m : ℤ := ((a : ℤ) * d - (b' : ℤ) * c) - q with hm

  have hmP : ∀ R, e (m • P) R = 1 := fun R => by
    obtain ⟨α, β, hR⟩ := TateModule.exists_eq_smul_basisOfCard_apply hcard n R.2
    have hR' : R = (α : ℤ) • P + (β : ℤ) • Q := Subtype.ext hR.symm
    rw [hR', hr, pair_right_zsmul e hr, pair_right_zsmul e hr, pair_left_zsmul e hl,
      pair_left_zsmul e hl, halt, hg]
    simp only [one_zpow, one_mul]
  have hmP0 : m • P = 0 := hnd _ hmP
  have hrel : m • ((b 0 : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n
      + (0 : ℤ) • ((b 1 : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n = 0 := by
    rw [zero_smul, add_zero]
    exact congrArg Subtype.val hmP0
  have hdvd : ((ℓ ^ n : ℕ) : ℤ) ∣ m := (TateModule.dvd_of_rel_basisOfCard_apply hcard n m 0 hrel).1

  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have h0 : ((m : ℤ) : ZMod (ℓ ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  rw [hm] at h0
  push_cast at h0
  simp only [map_sub, map_mul, map_natCast, TateModule.toZModPow_eq_appr]
  rw [← ha, ← hb', ← hc, ← hd]
  linear_combination h0

end S_WeierstrassCurve_det_frobenius_tateModule_eq_card
end P2MW
export P2MW.S_WeierstrassCurve_det_frobenius_tateModule_eq_card (solution)
