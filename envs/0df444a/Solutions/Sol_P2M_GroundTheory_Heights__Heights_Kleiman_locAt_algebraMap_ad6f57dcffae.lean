-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locAt_algebraMap_ad6f57dcffae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:51.9328+00:00
-- url     : https://prove2.me/submissions/72bd537e-7b88-41ef-b14b-ccc56ca270fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : k) :
    algebraMap k Ω c ∈ locAt k x y ∧ redAt k x y (algebraMap k Ω c) = algebraMap k K' c := by
  have h1 : aeval y (1 : Poly k N) ≠ 0 := by simp
  have hc : algebraMap k Ω c = aeval x (C c : Poly k N) / aeval x (1 : Poly k N) := by
    simp
  rw [hc]
  refine ⟨mem_locAt (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1, ?_⟩
  rw [redAt_eq hsp (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1]
  simp
end GroundTheory.Heights₂.Heights.Kleiman
