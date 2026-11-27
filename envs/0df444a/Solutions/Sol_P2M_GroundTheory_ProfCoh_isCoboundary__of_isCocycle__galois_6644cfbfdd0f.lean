-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_isCoboundary__of_isCocycle__galois_6644cfbfdd0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:29.707393+00:00
-- url     : https://prove2.me/submissions/bbc5e16a-7d23-44cb-b514-f4a5748ca098

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_groupCohomology_galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory CategoryTheory.Limits
universe u
open groupCohomology
variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution (f : Gal(L/K) → L) (hf : IsCocycle₁ f) :
    IsCoboundary₁ f := by
  have := subsingleton_groupCohomology_galois K L one_ne_zero
  have h0 : H1π (Rep.ofDistribMulAction K Gal(L/K) L) (cocyclesOfIsCocycle₁ hf) = 0 :=
    Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at h0
  exact isCoboundary₁_of_mem_coboundaries₁ f h0
end GroundTheory.ProfCoh
