-- Prove2me | solution 1 for PIW.FdPA.opN_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:21:58.263461+00:00
-- url     : https://prove2.me/submissions/e7648bca-4119-4d6f-92ab-3ddbc5ff0023

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) = ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ, √(∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) =
      ‖t‖ * √(∑ i, ‖Matrix.mulVec A v i‖ ^ 2) := by
    intro v
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  open scoped Pointwise in
  have hset : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = √(∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / √(∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧ s = √(∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / √(∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, by rw [key, mul_div_assoc]⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [key, mul_div_assoc]⟩
  open scoped Pointwise in
  rw [hset, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]
end PIW.FdPA
