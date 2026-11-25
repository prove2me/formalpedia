-- Prove2me | solution 1 for P2M_Formalism_EigenvalueLevelCeiling_localization_map__dea12fd01409
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:10.604015+00:00
-- url     : https://prove2.me/submissions/67012d58-6b49-4641-8d60-43774895617d

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_alg_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (p : Ideal R) [p.IsPrime] (φ : V →ₗ[K] V') (A : Submodule R V) :
    localization₂ p (A.map (φ.restrictScalars R)) = (localization₂ p A).map (φ.restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    have hs0 : algebraMap R K s ≠ 0 := idxRules_alg_ne (fun h => hs (h ▸ p.zero_mem))
    refine ⟨(algebraMap R K s)⁻¹ • y, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s, smul_smul, mul_inv_cancel₀ hs0, one_smul]
      exact hy
    · have h1 : φ y = s • x := hyx
      change φ ((algebraMap R K s)⁻¹ • y) = x
      rw [map_smul, h1, ← algebraMap_smul K s, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩
end Formalism.EigenvalueLevelCeiling
