-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_den_6be64aadeaa6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:27.936559+00:00
-- url     : https://prove2.me/submissions/9b2260f0-498c-4a7b-bf50-cd1e008a556f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.MainNotions.G
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)
local notation "π" => algebraMap W Q ϖ
include hϖ
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (q : Q) : ∃ N : ℕ, ∀ M, N ≤ M → π ^ M * q ∈ (algebraMap W Q).range := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) q
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  obtain ⟨u, hu⟩ := hN
  refine ⟨N, fun M hM => ⟨ϖ ^ (M - N) * a * u, ?_⟩⟩
  have hb0 : algebraMap W Q b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr (nonZeroDivisors.ne_zero hb)
  have h1 : algebraMap W Q b * algebraMap W Q u = π ^ N := by rw [← map_mul, hu, map_pow]
  rw [map_mul, map_mul, map_pow]
  have h2 : π ^ M = π ^ (M - N) * π ^ N := by rw [← pow_add, Nat.sub_add_cancel hM]
  rw [h2, ← h1]
  field_simp
end Formalism.BasicNotions.Examples₂.NZ
