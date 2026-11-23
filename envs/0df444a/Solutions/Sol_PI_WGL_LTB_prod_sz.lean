-- Prove2me | solution 1 for PI.WGL.LTB.prod_sz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:53.261077+00:00
-- url     : https://prove2.me/submissions/3b1976a2-c8ad-4b6f-bf90-8397e681e476

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {M : Type*} [CommMonoid M] {K : ℕ} (sz : Fin K → ℕ) (s : Finset (Fin K)) (bnd : ℕ)
    (hb : ∀ k ∈ s, sz k < bnd) (F : ℕ → M) :
    ∏ k ∈ s, F (sz k) = ∏ y ∈ Finset.range bnd, F y ^ (s.filter fun k => sz k = y).card := by
  rw [Finset.prod_comp F sz]
  apply Finset.prod_subset
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact Finset.mem_range.mpr (hb k hk)
  · intro y _ hy
    rw [Finset.mem_image] at hy
    have e : s.filter (fun k => sz k = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk hky
      exact hy ⟨k, hk, hky⟩
    rw [e, Finset.card_empty, pow_zero]
end PI.WGL.LTB
