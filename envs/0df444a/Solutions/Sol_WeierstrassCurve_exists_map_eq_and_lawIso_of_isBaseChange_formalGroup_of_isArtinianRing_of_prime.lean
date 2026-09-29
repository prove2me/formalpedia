-- Prove2me | solution 1 for WeierstrassCurve.exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a34cac1d-60ef-588e-b7ef-f2aa895f2780

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime
import Theorems.Thm_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime
import Theorems.Thm_WeierstrassCurve_exists_map_eq_and_lawIso_of_exists_quotient_of_pow_eq_bot_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast"
p2m_attr_erase "simp" "MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT E₀.formalGroup) :
    ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (G' : FormalGroup T) (_ : G'.toPowerSeries = E.formalGroupLawFixed) (ψ : FormalGroup.LawIso G' G),
      ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, maximalIdeal T ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T)
    exact ⟨N, by rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN⟩
  have hind : ∀ n : ℕ, ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (Gn : FormalGroup (T ⧸ maximalIdeal T ^ (n + 1)))
      (_ : Gn.toPowerSeries = (E.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1)))).formalGroupLawFixed)
      (ψ : FormalGroup.LawIso Gn (G.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))))),
      ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈
        (maximalIdeal T).map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) := by
    intro n
    induction n with
    | zero =>
      simpa using WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime q k E₀ hE₀ W₀ hW₀ res₀ hres₀ hker₀ T resT hresT hkerT hresT₀ G hG
    | succ n ih =>
      exact WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime q k E₀ hE₀ W₀ hW₀ res₀ hres₀ hker₀ T resT hresT hkerT hresT₀ G hG (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) ih
  have hbot : maximalIdeal T ^ (N + 1) = ⊥ :=
    le_bot_iff.mp (hN ▸ Ideal.pow_le_pow_right (Nat.le_succ N))
  exact WeierstrassCurve.exists_map_eq_and_lawIso_of_exists_quotient_of_pow_eq_bot_of_prime q k E₀ hE₀ W₀ hW₀ res₀ hres₀ hker₀ T resT hresT hkerT hresT₀ G hG (N + 1) hbot (hind N)

end S_WeierstrassCurve_exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_eq_and_lawIso_of_isBaseChange_formalGroup_of_isArtinianRing_of_prime (solution)
