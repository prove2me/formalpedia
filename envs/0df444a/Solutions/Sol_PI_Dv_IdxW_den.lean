-- Prove2me | solution 1 for PI.Dv.IdxW.den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:12.458807+00:00
-- url     : https://prove2.me/submissions/dec89ace-756a-45c4-a62b-fbfdc5a166c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open Module
variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.Dv.IdxW
theorem _root_.solution (X Y : Submodule R V) (hX : X.FG) (hXY : ∀ x ∈ X, x ∈ Submodule.span K (Y : Set V)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hX
  have hc : ∀ a ∈ s, ∃ c : R, c ≠ 0 ∧ c • a ∈ Y := fun a ha =>
    eltDen (K := K) Y (hXY a (Submodule.subset_span ha))
  choose! c hc0 hcY using hc
  refine ⟨∏ a ∈ s, c a, Finset.prod_ne_zero_iff.mpr hc0, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem a ha =>
    rw [← Finset.prod_erase_mul s c ha, mul_smul]
    exact Y.smul_mem _ (hcY a ha)
  | zero => rw [smul_zero]; exact Y.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Y.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact Y.smul_mem r hx
end PI.Dv.IdxW
