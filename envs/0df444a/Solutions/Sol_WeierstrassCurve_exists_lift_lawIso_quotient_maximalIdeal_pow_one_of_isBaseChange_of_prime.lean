-- Prove2me | solution 1 for WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c8b4a742-5585-51ad-b8ce-2debe5b79805

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace STAux

noncomputable def idHom {R : Type*} [CommRing R] (G : FormalGroup R) : FormalGroup.LawHom G G where
  series := PowerSeries.X
  constantCoeff_series := PowerSeries.constantCoeff_X
  comm := by
    have hF : PowerSeries.HasSubst G.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff
    have hsx : ∀ i : Fin 2, FormalGroup.LawHom.substX i (PowerSeries.X : PowerSeries R) = MvPowerSeries.X i := by
      intro i; unfold FormalGroup.LawHom.substX
      exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))
    have hvec : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = MvPowerSeries.X := by
      funext i; fin_cases i <;> rfl
    rw [PowerSeries.subst_X hF, hsx, hsx, hvec, MvPowerSeries.subst_self, id]

@[scoped simp] theorem idHom_series {R : Type*} [CommRing R] (G : FormalGroup R) : (idHom G).series = PowerSeries.X := rfl

noncomputable def idIso {R : Type*} [CommRing R] (G : FormalGroup R) : FormalGroup.LawIso G G :=
  ⟨idHom G, by rw [idHom_series, PowerSeries.coeff_one_X]; exact isUnit_one⟩

end STAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime.STAux"

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT E₀.formalGroup)
    :
    ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (Gn : FormalGroup (T ⧸ maximalIdeal T ^ 1))
      (_ : Gn.toPowerSeries = (E.map (Ideal.Quotient.mk (maximalIdeal T ^ 1))).formalGroupLawFixed)
      (ψ : FormalGroup.LawIso Gn (G.map (Ideal.Quotient.mk (maximalIdeal T ^ 1)))),
      ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈
        (maximalIdeal T).map (Ideal.Quotient.mk (maximalIdeal T ^ 1)) := by
  classical

  choose a₁ ha₁ using hresT E₀.a₁
  choose a₂ ha₂ using hresT E₀.a₂
  choose a₃ ha₃ using hresT E₀.a₃
  choose a₄ ha₄ using hresT E₀.a₄
  choose a₆ ha₆ using hresT E₀.a₆
  let E : WeierstrassCurve T := ⟨a₁, a₂, a₃, a₄, a₆⟩
  have hE : E.map resT = E₀ := WeierstrassCurve.ext ha₁ ha₂ ha₃ ha₄ ha₆
  set π₁ : T →+* T ⧸ maximalIdeal T ^ 1 := Ideal.Quotient.mk (maximalIdeal T ^ 1) with hπ₁
  have hker : ∀ x : T, resT x = 0 → π₁ x = 0 := by
    intro x hx
    rw [hπ₁, Ideal.Quotient.eq_zero_iff_mem, pow_one, ← hkerT, RingHom.mem_ker]; exact hx
  refine ⟨E, hE, G.map π₁, ?_, STAux.idIso (G.map π₁), fun m => ?_⟩
  · rw [FormalGroup.map_toPowerSeries, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E π₁).2]
    ext n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← sub_eq_zero, ← map_sub]
    apply hker
    rw [map_sub, sub_eq_zero, ← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map,
      ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E resT).2, hE]
    exact congrArg (MvPowerSeries.coeff n) hG.symm
  · show PowerSeries.coeff m PowerSeries.X - (if m = 1 then 1 else 0) ∈ _
    rw [PowerSeries.coeff_X, sub_self]; exact Ideal.zero_mem _

end S_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime
end P2MW
export P2MW.S_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_one_of_isBaseChange_of_prime (solution)
