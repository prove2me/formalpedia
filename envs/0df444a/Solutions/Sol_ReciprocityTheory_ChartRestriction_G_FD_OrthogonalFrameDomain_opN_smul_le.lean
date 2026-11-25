-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.opN_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:16.007521+00:00
-- url     : https://prove2.me/submissions/a148bdb1-db46-4aff-85ea-978edf0b0b6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
theorem _root_.solution {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) ≤ ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ,
      Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2) =
        ‖t‖ * (Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)) := by
    intro v
    have h1 : ∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2 = ‖t‖ ^ 2 * ∑ i, ‖Matrix.mulVec A v i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmv : Matrix.mulVec (t • A) v i = t * Matrix.mulVec A v i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [hmv, norm_mul, mul_pow]
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg t), mul_div_assoc]
  open scoped Pointwise in
  have hS : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
      rw [smul_eq_mul, key v]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [smul_eq_mul, key v]⟩
  refine le_of_eq ?_
  rw [hS, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
