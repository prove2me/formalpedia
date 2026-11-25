-- Prove2me | solution 1 for PI.WGL.comp_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:03.340445+00:00
-- url     : https://prove2.me/submissions/d7de6478-542c-4d55-b198-0ecf066f25f2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_NablaSqLeOfGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowGraded
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (hW : EqvRowWt) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (z : ℂ)
    (hz : ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) (ν : Fin N → ℕ) (s : MvPolynomial (Fin n × Fin n) ℂ)
    (hs : s ∈ nablaSq ℂ n mu) :
    Z (weightedHomogeneousComponent (rowW N N) ν (φ s)) =
      weightedHomogeneousComponent (rowW N N) ν (Z (φ s)) := by

  have hterm : ∀ ω : Fin n → ℕ,
      Z (weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s))) =
        z • weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s)) := by
    intro ω
    have hc : weightedHomogeneousComponent (rowW n n) ω s ∈ nablaSq ℂ n mu :=
      dualWeylRowGraded ℂ n n mu.natW ω s hs
    have hhom : IsWeightedHomogeneous (rowW N N)
        (φ (weightedHomogeneousComponent (rowW n n) ω s)) (liftWt h lam mu ω) :=
      hW n N h lam mu hmu φ hφ ω _ hc (weightedHomogeneousComponent_isWeightedHomogeneous ω s)
    by_cases hν : ν = liftWt h lam mu ω
    · subst hν
      rw [hhom.weightedHomogeneousComponent_same]
      exact hz _ hc
    · rw [hhom.weightedHomogeneousComponent_ne ν hν, map_zero, smul_zero]
  have hsum : s = ∑ ω ∈ (weightedHomogeneousComponent_finsupp (w := rowW n n) s).toFinset,
      weightedHomogeneousComponent (rowW n n) ω s := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (rowW n n) s]
    exact finsum_eq_sum _ _
  rw [hz s hs, map_smul]
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]
  simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ω _ => hterm ω
end PI.WGL
