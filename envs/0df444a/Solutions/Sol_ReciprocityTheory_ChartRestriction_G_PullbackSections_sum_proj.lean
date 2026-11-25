-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:29.088221+00:00
-- url     : https://prove2.me/submissions/c561c2ff-317a-453f-95c2-8015e7512753

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_sum_lagr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι] (ρ : O →+* Module.End S M) (χ : ι → O →+* K) (α : O)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution [Nonempty ι] (hα : Function.Injective fun τ => χ τ α) : ∑ τ, proj ρ χ α τ = 1 := by
  have h := sum_lagr (fun τ => χ τ α) hα
  calc ∑ τ, proj ρ χ α τ
      = aeval (ρ α) ((∑ τ, lagr (fun τ => χ τ α) τ).map (algebraMap K S)) := by
        simp only [proj, Polynomial.map_sum, map_sum]
    _ = 1 := by rw [h, Polynomial.map_one, map_one]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
