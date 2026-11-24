-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_comp_perm_7eda8f43bc8a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:05.654737+00:00
-- url     : https://prove2.me/submissions/682ae3fb-68bf-4e0b-98dd-d2e52ee589d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n))
    (h : (K → ℤ) → ℤ) : mixedDiff (bs ∘ σ) h = mixedDiff bs h := by
  unfold mixedDiff
  exact (σ.ofFn_comp_perm bs).foldr_eq h
end GroundTheory.Heights₂.Heights.FieldNumbers
