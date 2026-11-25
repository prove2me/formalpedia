-- Prove2me | solution 1 for PI.Dv.RK.end_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:54.579883+00:00
-- url     : https://prove2.me/submissions/51c304b7-b018-49c6-9235-6e714a4e44ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.RK
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : Module.End K W) (hE : E ≠ 0) :
    ∃ (n : ℕ) (A B : Fin n → Module.End K W), ∑ i, A i * E * B i = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (LinearMap.ext h)
  have hex : ¬ ∀ φ : Module.Dual K W, φ (E v) = 0 := fun h =>
    hv ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  push Not at hex
  obtain ⟨f0, hf0⟩ := hex
  let f : Module.Dual K W := (f0 (E v))⁻¹ • f0
  have hf : f (E v) = 1 := by simp [f, hf0]
  let b := Module.finBasis K W
  refine ⟨Module.finrank K W, fun i => f.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply, Module.End.one_apply]
  conv_rhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smulRight_apply,
    LinearMap.smulRight_apply, map_smul, map_smul, hf, smul_eq_mul, mul_one, Module.Basis.coord_apply]
end PI.Dv.RK
