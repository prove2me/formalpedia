-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:32.527522+00:00
-- url     : https://prove2.me/submissions/cf4988b7-b0bc-4f3f-9231-deeb4cca0d2a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {a b : ℝ} {x y : K} (hx : vge v a x) (hy : vge v b y) : vge v (a + b) (x * y) := by
  rw [vge_iff'] at *
  intro n hn
  rw [v.map_mul] at hn
  cases h1 : v x with
  | top => rw [h1] at hn; simp at hn
  | coe m =>
    cases h2 : v y with
    | top => rw [h2] at hn; simp at hn
    | coe k =>
      rw [h1, h2, ← WithTop.coe_add, WithTop.coe_inj] at hn
      have := hx m h1
      have := hy k h2
      rw [← hn]; push_cast; linarith
end Formalism.MainNotions.PlaneGram
