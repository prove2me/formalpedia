-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_chartBundle_pow_smul_mem_e5a323984de9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:13.071706+00:00
-- url     : https://prove2.me/submissions/94b59ac8-7bcd-458d-98a9-2432b8774307

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {R : Type*} [CommRing R] [Algebra R Ω] {τ : Type*} {x : τ → Ω} {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (B : ChartBundle R x r E) {i : τ} {a : Ω}
    (ha : a ∈ chartRing R x i) (m : ℕ) {e : E} (he : e ∈ B.lat i) : a ^ m • e ∈ B.lat i :=
  B.stable i _ (pow_mem ha m) e he
end GroundTheory.Heights₂.Heights.Model
