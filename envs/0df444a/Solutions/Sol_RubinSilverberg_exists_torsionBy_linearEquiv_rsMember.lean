-- Prove2me | solution 1 for RubinSilverberg.exists_torsionBy_linearEquiv_rsMember
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e2707d29-ca99-5c83-80c8-eff6498c7a8c

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Tower
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_RubinSilverberg_exists_polynomial_rsFamily
import Theorems.Thm_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember
import Theorems.Thm_RubinSilverberg_pt_rsMember_ne_zero_and_five_smul
import Theorems.Thm_RubinSilverberg_rsMember_sections_independent
import Theorems.Thm_RubinSilverberg_kleinCurve_Delta
import Theorems.Thm_RubinSilverberg_kleinVHom_one_right
import Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinH_ne_zero
import Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinT_ne_zero
import Theorems.Thm_RubinSilverberg_rsMember_zero
import Theorems.Thm_RubinSilverberg_rsFamilyA_eq_aeval
import Theorems.Thm_RubinSilverberg_rsFamilyB_eq_aeval
import Definitions.Def_FieldTheory_RatFuncTower
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light
import Theorems.Thm_WeierstrassCurve_exists_specializationHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_exists_torsionBy_linearEquiv_rsMember
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

noncomputable section

p2m_open "Polynomial WeierstrassCurve~specialize WeierstrassCurve.Affine WeierstrassCurve.Affine.Point RubinSilverberg"
open scoped Classical

open RatFuncTower

theorem RoadC.kleinV_div {K : Type*} [Field K] (n : K) {d : K} (hd : d ≠ 0) :
    kleinV (n / d) = kleinVHom n d / d ^ 12 := by
  unfold kleinV kleinVHom
  field_simp

namespace RoadC

local notation "Qb" => AlgebraicClosure ℚ
local notation "ι" => algebraMap ℚ (AlgebraicClosure ℚ)

section maps
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_kleinV (u : R) : f (kleinV u) = kleinV (f u) := by simp [kleinV, map_ofNat]
theorem map_kleinH (u : R) : f (kleinH u) = kleinH (f u) := by simp [kleinH, map_ofNat]
theorem map_kleinT (u : R) : f (kleinT u) = kleinT (f u) := by simp [kleinT, map_ofNat]
theorem map_kleinVHom (n d : R) : f (kleinVHom n d) = kleinVHom (f n) (f d) := by simp [kleinVHom, map_ofNat]
theorem map_kleinHHom (n d : R) : f (kleinHHom n d) = kleinHHom (f n) (f d) := by simp [kleinHHom, map_ofNat]
theorem map_kleinTHom (n d : R) : f (kleinTHom n d) = kleinTHom (f n) (f d) := by simp [kleinTHom, map_ofNat]
end maps

section fieldmaps
variable {K L : Type*} [Field K] [Field L] (f : K →+* L)

theorem map_rsBeta (u : K) : f (rsBeta u) = rsBeta (f u) := by
  simp [rsBeta, map_div₀, map_kleinT, map_ofNat]
theorem map_rsGamma (u : K) : f (rsGamma u) = rsGamma (f u) := by
  simp [rsGamma, map_div₀, map_kleinT, map_ofNat]
theorem map_rsNum (u₀ l t : K) : f (rsNum u₀ l t) = rsNum (f u₀) (f l) (f t) := by
  simp [rsNum, map_rsBeta]
theorem map_rsDen (u₀ l t : K) : f (rsDen u₀ l t) = rsDen (f u₀) (f l) (f t) := by
  simp [rsDen, map_rsGamma]
theorem map_rsFamilyA (a u₀ l t : K) : f (rsFamilyA a u₀ l t) = rsFamilyA (f a) (f u₀) (f l) (f t) := by
  simp [rsFamilyA, map_div₀, map_kleinHHom, map_kleinH, map_rsNum, map_rsDen]
theorem map_rsFamilyB (b u₀ l t : K) : f (rsFamilyB b u₀ l t) = rsFamilyB (f b) (f u₀) (f l) (f t) := by
  simp [rsFamilyB, map_div₀, map_kleinTHom, map_kleinT, map_rsNum, map_rsDen]
theorem map_rsMember (a b u₀ l t : K) :
    (rsMember a b u₀ l t).map f = rsMember (f a) (f b) (f u₀) (f l) (f t) := by
  ext <;> simp [rsMember, map_rsFamilyA, map_rsFamilyB]

theorem kd_map {a b u₀ : K} (h : IsKleinDatum a b u₀) : IsKleinDatum (f a) (f b) (f u₀) := by
  refine ⟨?_, ?_⟩
  · have := congrArg f h.1
    simpa [map_kleinH, map_kleinV, map_ofNat] using this
  · rw [← map_kleinV]
    exact (map_ne_zero f).mpr h.2
end fieldmaps

section datum
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem kleinHHom_one (n : K) : kleinHHom n 1 = kleinH n := by simp [kleinHHom, kleinH]
omit [CharZero K] in
theorem kleinTHom_one (n : K) : kleinTHom n 1 = kleinT n := by simp [kleinTHom, kleinT]

end datum

theorem iso_at (W : WeierstrassCurve (Polynomial ℚ)) (t : ℚ) (W₀ : WeierstrassCurve ℚ)
    (hW₀ : W.map (Polynomial.evalRingHom t) = W₀) (hΔ : W₀.Δ ≠ 0)
    (hbig : ∃ f : Fin 5 × Fin 5 → Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ), Function.Injective f) :
    ∃ e : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ) ≃ₗ[ZMod 5]
        Submodule.torsionBy ℤ (W₀⁄Qb).Point (5 : ℕ),
      ∀ (σ : Qb ≃ₐ[ℚ] Qb) (x : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ)),
        e (galLift σ • x) = σ • e x := by
  subst hW₀
  have hΔ' : W.Δ.eval t ≠ 0 := by simpa [WeierstrassCurve.map_Δ] using hΔ
  obtain ⟨s, hs_eq, hs_inj, -⟩ := WeierstrassCurve.exists_specializationHom W t hΔ'
  haveI : (W.map (Polynomial.evalRingHom t)).IsElliptic := ⟨hΔ.isUnit⟩
  have hcard : Nat.card (Submodule.torsionBy ℤ ((W.map (Polynomial.evalRingHom t))⁄Qb).Point (5 : ℕ)) = 25 := by
    rw [WeierstrassCurve.card_torsion_of_isAlgClosed_light (K := Qb) (W.map (Polynomial.evalRingHom t))
      (n := 5) (by norm_num)]
    norm_num
  haveI hfin : Finite (Submodule.torsionBy ℤ ((W.map (Polynomial.evalRingHom t))⁄Qb).Point (5 : ℕ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)

  let sV : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ) →+
      Submodule.torsionBy ℤ ((W.map (Polynomial.evalRingHom t))⁄Qb).Point (5 : ℕ) :=
    { toFun := fun x => ⟨s x, by
        have hx := x.2
        rw [Submodule.mem_torsionBy_iff] at hx ⊢
        rw [← s.map_zsmul, hx, s.map_zero]⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hsV : ∀ x, ((sV x : _) : ((W.map (Polynomial.evalRingHom t))⁄Qb).Point) = s x := fun x => rfl
  have hinj : Function.Injective sV := by
    intro x y hxy
    have h0 : sV (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hx : (5 : ℕ) • ((x - y : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ)) : (W⁄K0).Point) = 0 := by
      have := (x - y).2
      rw [Submodule.mem_torsionBy_iff] at this
      rw [← natCast_zsmul]
      exact this
    have := hs_inj 5 (by norm_num) _ hx (by
      have := congrArg Subtype.val h0
      simpa [hsV] using this)
    rw [← sub_eq_zero]
    exact Subtype.ext this
  haveI : Finite (Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ)) := Finite.of_injective sV hinj
  have h25 : 25 ≤ Nat.card (Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ)) := by
    obtain ⟨f, hf⟩ := hbig
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hbij : Function.Bijective sV :=
    hinj.bijective_of_nat_card_le (by rw [hcard]; exact h25)
  refine ⟨LinearEquiv.ofBijective (sV.toZModLinearMap 5) hbij, fun σ x => ?_⟩
  apply Subtype.ext
  change s ((galLift σ • x : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ)) : (W⁄K0).Point) = σ • s x
  exact hs_eq σ x

end RoadC

local notation "ι" => algebraMap ℚ (AlgebraicClosure ℚ)

open RoadC RatFuncTower in
/-!                                                                                                                                                                          -/

theorem solution (a b l t₀ : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (u₀ : AlgebraicClosure ℚ)
    (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀)
    (W₁ : WeierstrassCurve ℚ)
    (hW₁ : W₁.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      rsMember (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀
        (algebraMap ℚ (AlgebraicClosure ℚ) l) (algebraMap ℚ (AlgebraicClosure ℚ) t₀))
    (hΔ₁ : W₁.Δ ≠ 0) :
    ∃ φ : Submodule.torsionBy ℤ ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point (5 : ℕ)
        ≃ₗ[ZMod 5] Submodule.torsionBy ℤ (W₁⁄(AlgebraicClosure ℚ)).Point (5 : ℕ),
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x : Submodule.torsionBy ℤ ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point (5 : ℕ)),
        φ (σ • x) = σ • φ x := by

  have hι : Function.Injective ι := (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  have ha' : ι a ≠ 0 := (_root_.map_ne_zero ι).mpr ha
  have hb' : ι b ≠ 0 := (_root_.map_ne_zero ι).mpr hb
  have hV0 : kleinV u₀ ≠ 0 := h₀.2

  obtain ⟨pa, pb, -, -, hpapb⟩ := RubinSilverberg.exists_polynomial_rsFamily a b l ha hb u₀ h₀

  set W : WeierstrassCurve (Polynomial ℚ) := ⟨0, 0, 0, pa, pb⟩ with hW
  have hWt : ∀ t : ℚ, (W.map (Polynomial.evalRingHom t)).map ι = rsMember (ι a) (ι b) u₀ (ι l) (ι t) := by
    intro t
    ext
    · simp [W, rsMember]
    · simp [W, rsMember]
    · simp [W, rsMember]
    · simp only [W, WeierstrassCurve.map_a₄, rsMember, Polynomial.coe_evalRingHom]
      exact ((hpapb (ι t)).1.trans (by rw [Polynomial.eval_map]; exact Polynomial.eval₂_hom ι t)).symm
    · simp only [W, WeierstrassCurve.map_a₆, rsMember, Polynomial.coe_evalRingHom]
      exact ((hpapb (ι t)).2.trans (by rw [Polynomial.eval_map]; exact Polynomial.eval₂_hom ι t)).symm
  have hW1 : W.map (Polynomial.evalRingHom t₀) = W₁ := by
    apply WeierstrassCurve.map_injective hι
    change (W.map (Polynomial.evalRingHom t₀)).map ι = W₁.map ι
    rw [hWt, hW₁]
  have hW0 : W.map (Polynomial.evalRingHom 0) = ⟨0, 0, 0, a, b⟩ := by
    apply WeierstrassCurve.map_injective hι
    change (W.map (Polynomial.evalRingHom 0)).map ι = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ).map ι
    rw [hWt, _root_.map_zero, RubinSilverberg.rsMember_zero (ι a) (ι b) u₀ (ι l) (RubinSilverberg.IsKleinDatum.kleinH_ne_zero h₀ ha') (RubinSilverberg.IsKleinDatum.kleinT_ne_zero h₀ hb')]
    ext <;> simp

  have hΔt : ∀ t : ℚ, rsDen u₀ (ι l) (ι t) ≠ 0 →
      kleinV (rsNum u₀ (ι l) (ι t) / rsDen u₀ (ι l) (ι t)) ≠ 0 → (W.map (Polynomial.evalRingHom t)).Δ ≠ 0 := by
    intro t hd hv hzero
    obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq (-18 * (ι b / ι a) * kleinH u₀ / kleinT u₀) two_pos
    obtain ⟨C, -, -, -, -, hC⟩ :=
      RubinSilverberg.exists_variableChange_kleinCurve_eq_rsMember h₀ ha' hb' (ι l) (ι t) k hd hk
    have h1 : ((W.map (Polynomial.evalRingHom t)).map ι).Δ = 0 := by
      rw [WeierstrassCurve.map_Δ, hzero, _root_.map_zero]
    rw [hWt t, ← hC, WeierstrassCurve.variableChange_Δ, RubinSilverberg.kleinCurve_Delta] at h1
    have hu : ((↑C.u⁻¹ : AlgebraicClosure ℚ)) ≠ 0 := Units.ne_zero _
    apply hv
    simpa [hu] using h1

  have hbig : ∃ f : Fin 5 × Fin 5 → Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ), Function.Injective f := by
    let jK : AlgebraicClosure ℚ →+* K0 := algebraMap (AlgebraicClosure ℚ) K0
    have hj : Function.Injective jK := (algebraMap (AlgebraicClosure ℚ) K0).injective
    have hjC : ∀ c : AlgebraicClosure ℚ, jK c = algebraMap (Polynomial (AlgebraicClosure ℚ)) K0 (Polynomial.C c) :=
      fun c => by
        rw [IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ)) K0 c,
          ← Polynomial.C_eq_algebraMap]
    have hinjA : Function.Injective (algebraMap (Polynomial (AlgebraicClosure ℚ)) K0) :=
      IsFractionRing.injective _ _
    set T : K0 := algebraMap (Polynomial (AlgebraicClosure ℚ)) K0 Polynomial.X with hT
    have hd' : IsKleinDatum (jK (ι a)) (jK (ι b)) (jK u₀) := RoadC.kd_map jK h₀
    have ha'' : jK (ι a) ≠ 0 := (_root_.map_ne_zero jK).mpr ha'
    have hb'' : jK (ι b) ≠ 0 := (_root_.map_ne_zero jK).mpr hb'

    have hPA : Polynomial.C (ι a / kleinH u₀) * kleinHHom (Polynomial.C (rsBeta u₀ + ι l * u₀) * Polynomial.X +
        Polynomial.C u₀) (Polynomial.C (rsGamma u₀ + ι l) * Polynomial.X + 1) = pa.map ι := by
      apply Polynomial.funext
      intro r
      have h1 := RubinSilverberg.rsFamilyA_eq_aeval (K := AlgebraicClosure ℚ)
        (F := AlgebraicClosure ℚ) (ι a) u₀ (ι l) r
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.coe_aeval_eq_eval] at h1
      rw [← h1]
      exact (hpapb r).1
    have hPB : Polynomial.C (ι b / kleinT u₀) * kleinTHom (Polynomial.C (rsBeta u₀ + ι l * u₀) * Polynomial.X +
        Polynomial.C u₀) (Polynomial.C (rsGamma u₀ + ι l) * Polynomial.X + 1) = pb.map ι := by
      apply Polynomial.funext
      intro r
      have h1 := RubinSilverberg.rsFamilyB_eq_aeval (K := AlgebraicClosure ℚ)
        (F := AlgebraicClosure ℚ) (ι b) u₀ (ι l) r
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.coe_aeval_eq_eval] at h1
      rw [← h1]
      exact (hpapb r).2
    have hE : (W⁄K0) = rsMember (jK (ι a)) (jK (ι b)) (jK u₀) (jK (ι l)) T := by
      ext
      · simp [W, rsMember]
      · simp [W, rsMember]
      · simp [W, rsMember]
      · change algebraMap (Polynomial ℚ) K0 pa = rsFamilyA (jK (ι a)) (jK u₀) (jK (ι l)) T
        rw [RubinSilverberg.rsFamilyA_eq_aeval, hPA, hT, Polynomial.aeval_algebraMap_apply,
          Polynomial.aeval_X_left_apply, RatFuncTower.algebraMap_ratPoly_apply]
      · change algebraMap (Polynomial ℚ) K0 pb = rsFamilyB (jK (ι b)) (jK u₀) (jK (ι l)) T
        rw [RubinSilverberg.rsFamilyB_eq_aeval, hPB, hT, Polynomial.aeval_algebraMap_apply,
          Polynomial.aeval_X_left_apply, RatFuncTower.algebraMap_ratPoly_apply]

    set pd : Polynomial (AlgebraicClosure ℚ) := Polynomial.C (rsGamma u₀ + ι l) * Polynomial.X + 1 with hpd
    set pn : Polynomial (AlgebraicClosure ℚ) := Polynomial.C (rsBeta u₀ + ι l * u₀) * Polynomial.X +
      Polynomial.C u₀ with hpn
    have hden_eq : rsDen (jK u₀) (jK (ι l)) T = algebraMap (Polynomial (AlgebraicClosure ℚ)) K0 pd := by
      rw [hpd, map_add, map_mul, map_one, ← hjC, map_add, RoadC.map_rsGamma]
      rw [rsDen]
    have hnum_eq : rsNum (jK u₀) (jK (ι l)) T = algebraMap (Polynomial (AlgebraicClosure ℚ)) K0 pn := by
      rw [hpn, map_add, map_mul, ← hjC, ← hjC, map_add, map_mul, RoadC.map_rsBeta]
      rw [rsNum]
    have hpd0 : pd ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.eval 0) h0
      simp [hpd] at this
    have hdenK : rsDen (jK u₀) (jK (ι l)) T ≠ 0 := by
      rw [hden_eq]
      exact (map_ne_zero_iff _ hinjA).mpr hpd0
    have hVK : kleinV (rsNum (jK u₀) (jK (ι l)) T / rsDen (jK u₀) (jK (ι l)) T) ≠ 0 := by
      rw [RoadC.kleinV_div _ hdenK]
      refine div_ne_zero ?_ (pow_ne_zero _ hdenK)
      rw [hnum_eq, hden_eq, ← RoadC.map_kleinVHom]
      refine (map_ne_zero_iff _ hinjA).mpr ?_
      intro h0
      have := congrArg (Polynomial.evalRingHom 0) h0
      rw [RoadC.map_kleinVHom, _root_.map_zero] at this
      simp [hpn, hpd, RubinSilverberg.kleinVHom_one_right, hV0] at this

    obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq (-18 * (ι b / ι a) * kleinH u₀ / kleinT u₀) two_pos
    have hk' : (jK k) ^ 2 = -18 * (jK (ι b) / jK (ι a)) * kleinH (jK u₀) / kleinT (jK u₀) := by
      rw [← map_pow, hk]
      simp [map_div₀, RoadC.map_kleinH, RoadC.map_kleinT, map_ofNat]
    obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ 5 := by
      haveI : NeZero ((5 : ℕ) : AlgebraicClosure ℚ) := ⟨by norm_num⟩
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 5 (AlgebraicClosure ℚ)) (by
        rw [Polynomial.degree_cyclotomic]
        decide)
      exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
    have hζ' : IsPrimitiveRoot (jK ζ) 5 := hζ.map_of_injective hj

    set v : K0 := rsNum (jK u₀) (jK (ι l)) T / rsDen (jK u₀) (jK (ι l)) T with hv
    have hQ := RubinSilverberg.pt_rsMember_ne_zero_and_five_smul hd' ha'' hb'' (jK (ι l)) T (jK k) v
      hdenK hVK hk' rfl
    have hR := RubinSilverberg.pt_rsMember_ne_zero_and_five_smul hd' ha'' hb'' (jK (ι l)) T (jK k) (jK ζ * v)
      hdenK hVK hk' (by rw [mul_pow, hζ'.pow_eq_one, one_mul])
    have hind := RubinSilverberg.rsMember_sections_independent (jK ζ) hζ' hd' ha'' hb'' (jK (ι l)) T (jK k)
      hdenK hVK hk'
    rw [← hv] at hind
    rw [← hE] at hQ hR hind

    set P1 := pt (W⁄K0) (jK k ^ 2 * rsDen (jK u₀) (jK (ι l)) T ^ 10 * kleinX v)
      (jK k ^ 3 * rsDen (jK u₀) (jK (ι l)) T ^ 15 * kleinY v) with hP1
    set P2 := pt (W⁄K0) (jK k ^ 2 * rsDen (jK u₀) (jK (ι l)) T ^ 10 * kleinX (jK ζ * v))
      (jK k ^ 3 * rsDen (jK u₀) (jK (ι l)) T ^ 15 * kleinY (jK ζ * v)) with hP2
    have m1 : P1 ∈ Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ) := by
      rw [Submodule.mem_torsionBy_iff]; exact_mod_cast hQ.2
    have m2 : P2 ∈ Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ) := by
      rw [Submodule.mem_torsionBy_iff]; exact_mod_cast hR.2
    let x1 : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ) := ⟨P1, m1⟩
    let x2 : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ) := ⟨P2, m2⟩
    refine ⟨fun ij => ((ij.1 : ℕ) : ℤ) • x1 + ((ij.2 : ℕ) : ℤ) • x2, ?_⟩
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hc := congrArg (fun z : Submodule.torsionBy ℤ (W⁄K0).Point (5 : ℕ) => (z : (W⁄K0).Point)) hij
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower] at hc
    change ((i : ℕ) : ℤ) • P1 + ((j : ℕ) : ℤ) • P2 = ((i' : ℕ) : ℤ) • P1 + ((j' : ℕ) : ℤ) • P2 at hc
    have hz : (((i : ℕ) : ℤ) - (i' : ℕ)) • P1 + (((j : ℕ) : ℤ) - (j' : ℕ)) • P2 = 0 := by
      have : (((i : ℕ) : ℤ) - (i' : ℕ)) • P1 + (((j : ℕ) : ℤ) - (j' : ℕ)) • P2
          = (((i : ℕ) : ℤ) • P1 + ((j : ℕ) : ℤ) • P2) - (((i' : ℕ) : ℤ) • P1 + ((j' : ℕ) : ℤ) • P2) := by
        simp only [sub_smul]; abel
      rw [this, hc, sub_self]
    obtain ⟨h5i, h5j⟩ := hind _ _ hz
    have hi := i.isLt; have hi' := i'.isLt; have hj := j.isLt; have hj' := j'.isLt
    have e1 : (i : ℕ) = i' := by omega
    have e2 : (j : ℕ) = j' := by omega
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)

  have hden0 : rsDen u₀ (ι l) (ι 0) ≠ 0 := by simp [rsDen]
  have hns0 : kleinV (rsNum u₀ (ι l) (ι 0) / rsDen u₀ (ι l) (ι 0)) ≠ 0 := by simpa [rsNum, rsDen] using hV0
  have hΔ0 : ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ)).Δ ≠ 0 := by rw [← hW0]; exact hΔt 0 hden0 hns0
  have hΔ1 : W₁.Δ ≠ 0 := hΔ₁
  obtain ⟨e0, he0⟩ := RoadC.iso_at W 0 ⟨0, 0, 0, a, b⟩ hW0 hΔ0 hbig
  obtain ⟨e1, he1⟩ := RoadC.iso_at W t₀ W₁ hW1 hΔ1 hbig
  refine ⟨e0.symm.trans e1, fun σ x => ?_⟩
  have hx : e0.symm (σ • x) = galLift σ • e0.symm x := by
    apply e0.injective
    rw [he0, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hx, he1]

#print axioms solution

end
end S_RubinSilverberg_exists_torsionBy_linearEquiv_rsMember
end P2MW
export P2MW.S_RubinSilverberg_exists_torsionBy_linearEquiv_rsMember (solution)
