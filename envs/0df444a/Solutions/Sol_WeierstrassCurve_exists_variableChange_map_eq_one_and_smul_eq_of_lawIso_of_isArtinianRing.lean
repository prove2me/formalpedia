-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/21e16be5-9282-5ac6-8435-ed24833949f5

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso
import Theorems.Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem isComm_of_toPowerSeries_eq {T : Type} [CommRing T] (E : WeierstrassCurve T) (G : FormalGroup T)
    (hG : G.toPowerSeries = E.formalGroupLawFixed) : G.IsComm :=
  ⟨by rw [hG]; exact WeierstrassCurve.formalGroupLawFixed_comm_of_commRing E⟩

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E E' : WeierstrassCurve T) (hE : E.map resT = E₀) (hE' : E'.map resT = E₀)
    (G : FormalGroup T) (hG : G.toPowerSeries = E.formalGroupLawFixed)
    (G' : FormalGroup T) (hG' : G'.toPowerSeries = E'.formalGroupLawFixed)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) :
    ∃ C : WeierstrassCurve.VariableChange T, C.map resT = 1 ∧ C • E = E' := by
  haveI : G.IsComm := isComm_of_toPowerSeries_eq E G hG
  haveI : G'.IsComm := isComm_of_toPowerSeries_eq E' G' hG'

  obtain ⟨N, hN⟩ : ∃ N : ℕ, maximalIdeal T ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T)
    exact ⟨N, by rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN⟩

  have hbase : (((1 : WeierstrassCurve.VariableChange T) • E).map (Ideal.Quotient.mk (maximalIdeal T ^ 1))) =
      E'.map (Ideal.Quotient.mk (maximalIdeal T ^ 1)) := by
    rw [one_smul]

    have hker1 : RingHom.ker resT = maximalIdeal T ^ 1 := by rw [pow_one]; exact hkerT
    let e : T ⧸ RingHom.ker resT ≃+* k := RingHom.quotientKerEquivOfSurjective hresT
    have hfac : ∀ t : T, resT t = e (Ideal.Quotient.mk (RingHom.ker resT) t) := fun t =>
      (RingHom.quotientKerEquivOfSurjective_apply_mk hresT t).symm
    have hcomp : resT = (e : T ⧸ RingHom.ker resT →+* k).comp (Ideal.Quotient.mk (RingHom.ker resT)) :=
      RingHom.ext hfac
    have hinj : Function.Injective (e : T ⧸ RingHom.ker resT →+* k) := e.injective
    have key : E.map (Ideal.Quotient.mk (RingHom.ker resT)) = E'.map (Ideal.Quotient.mk (RingHom.ker resT)) := by
      apply WeierstrassCurve.map_injective hinj
      show (E.map (Ideal.Quotient.mk (RingHom.ker resT))).map (e : T ⧸ RingHom.ker resT →+* k) =
        (E'.map (Ideal.Quotient.mk (RingHom.ker resT))).map (e : T ⧸ RingHom.ker resT →+* k)
      rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, ← hcomp, hE, hE']
    rw [← hker1]
    exact key

  have hind : ∀ n : ℕ, ∃ C : WeierstrassCurve.VariableChange T, C.map resT = 1 ∧
      (C • E).map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) =
        E'.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, ?_, by simpa using hbase⟩
      simp [WeierstrassCurve.VariableChange.map, WeierstrassCurve.VariableChange.one_def]
    | succ n ih =>
      obtain ⟨C, hC, hCE⟩ := ih
      exact WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso q hq k E₀ hE₀ T resT hresT hkerT E E' hE hE' G hG G' hG' ψ hψ (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) C hC hCE
  obtain ⟨C, hC, hCE⟩ := hind N
  refine ⟨C, hC, ?_⟩

  have hbot : maximalIdeal T ^ (N + 1) = ⊥ :=
    le_bot_iff.mp (hN ▸ Ideal.pow_le_pow_right (Nat.le_succ N))
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal T ^ (N + 1))) := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, hbot]
  exact WeierstrassCurve.map_injective hinj hCE

end S_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing (solution)
