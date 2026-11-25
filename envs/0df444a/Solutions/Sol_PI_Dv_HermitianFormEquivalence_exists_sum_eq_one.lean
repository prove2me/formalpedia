-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.exists_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:54.80153+00:00
-- url     : https://prove2.me/submissions/9190b778-b180-41dc-bcf5-a1b2cbbbdd50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (p : Module.End K W) (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ f g : Fin n → Module.End K W, ∑ i, f i * p * g i = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, p v ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (LinearMap.ext h)
  let b := Module.finBasis K W
  obtain ⟨k, hk⟩ : ∃ k, b.coord k (p v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (b.ext_elem fun k => by simpa [Module.Basis.coord_apply] using h k)
  let ψ : Module.Dual K W := (b.coord k (p v))⁻¹ • b.coord k
  have hψ : ψ (p v) = 1 := by
    simp only [ψ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hk
  refine ⟨Module.finrank K W, fun i => ψ.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩
  ext u
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smulRight_apply, map_smul,
    hψ, Module.End.one_apply]
  conv_rhs => rw [← b.sum_repr u]
  simp [Module.Basis.coord_apply]
end PI.Dv.HermitianFormEquivalence
