-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mem_range_of_conj_eq_538bfdb9709d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:13.248251+00:00
-- url     : https://prove2.me/submissions/4cd92e89-7047-431b-8f92-03279fc14bd0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_GroundTheory_Automorphic_add_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {x : E} (hx : conj F E x = x) :
    x ∈ Set.range (algebraMap F E) := by
  refine ⟨Algebra.trace F E x / 2, ?_⟩
  have h2 := add_conj (F := F) x
  rw [hx] at h2
  rw [map_div₀, ← h2, map_ofNat]
  field_simp
  ring
end GroundTheory.Heights₂.Theta
