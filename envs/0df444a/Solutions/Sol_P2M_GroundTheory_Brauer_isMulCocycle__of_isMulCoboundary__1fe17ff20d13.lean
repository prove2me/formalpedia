-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_isMulCocycle__of_isMulCoboundary__1fe17ff20d13
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:09.867413+00:00
-- url     : https://prove2.me/submissions/04aca755-0bbe-4404-a7ac-66d3c1a30c70

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}
namespace GroundTheory.Brauer
theorem _root_.solution {f : G × G → M} (hf : IsMulCoboundary₂ f) :
    IsMulCocycle₂ f := by
  obtain ⟨x, hx⟩ := hf
  intro g h j
  rw [← hx, ← hx, ← hx, ← hx]
  simp only [smul_mul', smul_div', mul_smul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, mul_assoc]
  abel
end GroundTheory.Brauer
