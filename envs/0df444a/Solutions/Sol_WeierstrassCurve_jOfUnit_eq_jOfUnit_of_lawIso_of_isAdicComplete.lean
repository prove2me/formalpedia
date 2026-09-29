-- Prove2me | solution 1 for WeierstrassCurve.jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0a46e0c2-02b1-5460-b24e-0233723af786

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace SerreTateJAux

universe u

theorem jOfUnit_congr {T : Type u} [CommRing T] {X Y : WeierstrassCurve T} (h : X = Y)
    (hX : IsUnit X.Δ) (hY : IsUnit Y.Δ) : X.jOfUnit hX = Y.jOfUnit hY := by
  subst h; rfl

theorem exists_lawIso_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {F G : FormalGroup R}
    (ψ : FormalGroup.LawIso F G) :
    ∃ ψ' : FormalGroup.LawIso (F.map f) (G.map f), ψ'.series = PowerSeries.map f ψ.series := by
  obtain ⟨θ, hθ⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map f ψ.toLawHom (F.map f) (G.map f)
    (FormalGroup.map_toPowerSeries F f) (FormalGroup.map_toPowerSeries G f)
  refine ⟨⟨θ, ?_⟩, hθ⟩
  rw [hθ, PowerSeries.coeff_map]
  exact ψ.isUnit_coeff_one.map f

theorem isLocalRing_quotient_pow {T : Type u} [CommRing T] [IsLocalRing T] (n : ℕ) :
    IsLocalRing (T ⧸ maximalIdeal T ^ (n + 1)) := by
  haveI : Nontrivial (T ⧸ maximalIdeal T ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal T).ne_top
        (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isArtinianRing_quotient_pow {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (n : ℕ) :
    @IsArtinianRing (T ⧸ maximalIdeal T ^ (n + 1)) _ := by
  haveI := isLocalRing_quotient_pow (T := T) n
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1)))
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]

end SerreTateJAux

open SerreTateJAux in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E E' : WeierstrassCurve T) (hE : E.map resT = E₀) (hE' : E'.map resT = E₀)
    (hΔ : IsUnit E.Δ) (hΔ' : IsUnit E'.Δ)
    (G : FormalGroup T) (hG : G.toPowerSeries = E.formalGroupLawFixed)
    (G' : FormalGroup T) (hG' : G'.toPowerSeries = E'.formalGroupLawFixed)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) :
    E.jOfUnit hΔ = E'.jOfUnit hΔ' := by
  classical

  have hmem : ∀ n : ℕ, E.jOfUnit hΔ - E'.jOfUnit hΔ' ∈ maximalIdeal T ^ (n + 1) := by
    intro n

    haveI hloc : IsLocalRing (T ⧸ maximalIdeal T ^ (n + 1)) := isLocalRing_quotient_pow n
    haveI hart : IsArtinianRing (T ⧸ maximalIdeal T ^ (n + 1)) := isArtinianRing_quotient_pow n
    set I : Ideal T := maximalIdeal T ^ (n + 1) with hI
    let π : T →+* T ⧸ I := Ideal.Quotient.mk I
    have hIker : ∀ a : T, a ∈ I → resT a = 0 := by
      intro a ha
      have : a ∈ maximalIdeal T := Ideal.pow_le_self (Nat.succ_ne_zero n) ha
      rw [← hkerT] at this
      exact this
    let resn : T ⧸ I →+* k := Ideal.Quotient.lift I resT hIker
    have hresn_mk : ∀ t : T, resn (π t) = resT t := fun t => Ideal.Quotient.lift_mk I resT hIker
    have hresn_comp : resn.comp π = resT := RingHom.ext hresn_mk
    have hresn : Function.Surjective resn :=
      Ideal.Quotient.lift_surjective_of_surjective I hIker hresT
    have hkern : RingHom.ker resn = maximalIdeal (T ⧸ I) := by
      rw [show RingHom.ker resn = (RingHom.ker resT).map π from Ideal.ker_quotient_lift resT hIker, hkerT]
      exact IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective

    have hEn : (E.map π).map resn = E₀ := by rw [WeierstrassCurve.map_map, hresn_comp, hE]
    have hE'n : (E'.map π).map resn = E₀ := by rw [WeierstrassCurve.map_map, hresn_comp, hE']

    have hGn : (G.map π).toPowerSeries = (E.map π).formalGroupLawFixed := by
      rw [FormalGroup.map_toPowerSeries, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E π).2, hG]
    have hG'n : (G'.map π).toPowerSeries = (E'.map π).formalGroupLawFixed := by
      rw [FormalGroup.map_toPowerSeries, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E' π).2, hG']

    obtain ⟨ψn, hψn⟩ := exists_lawIso_map π ψ
    have hψn' : ∀ m : ℕ, resn (PowerSeries.coeff m ψn.series) = if m = 1 then 1 else 0 := by
      intro m
      rw [hψn, PowerSeries.coeff_map, hresn_mk]
      exact hψ m

    obtain ⟨C, -, hC⟩ :=
      WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing q hq k E₀ hE₀
        (T ⧸ I) resn hresn hkern (E.map π) (E'.map π) hEn hE'n (G.map π) hGn (G'.map π) hG'n ψn hψn'

    have hΔn : IsUnit (E.map π).Δ := WeierstrassCurve.isUnit_Δ_map E π hΔ
    have hΔn' : IsUnit (E'.map π).Δ := WeierstrassCurve.isUnit_Δ_map E' π hΔ'
    have hCΔ : IsUnit (C • E.map π).Δ := WeierstrassCurve.isUnit_Δ_variableChange _ C hΔn
    have hj : π (E.jOfUnit hΔ) = π (E'.jOfUnit hΔ') := by
      rw [← WeierstrassCurve.jOfUnit_map E π hΔ hΔn, ← WeierstrassCurve.jOfUnit_map E' π hΔ' hΔn',
        ← WeierstrassCurve.jOfUnit_variableChange (E.map π) C hΔn hCΔ]
      exact jOfUnit_congr hC hCΔ hΔn'
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact hj

  have hH : IsHausdorff (maximalIdeal T) T := inferInstance
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hH _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (hmem n)

end S_WeierstrassCurve_jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
end P2MW
export P2MW.S_WeierstrassCurve_jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete (solution)
