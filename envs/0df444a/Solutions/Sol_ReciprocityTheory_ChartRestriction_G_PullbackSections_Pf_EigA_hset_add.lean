-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.hset_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:03.77248+00:00
-- url     : https://prove2.me/submissions/ade2d2c0-fc94-4238-929f-2c8e7bf6853f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
theorem _root_.solution {ξ η : (Fin d → k) × (Fin d → k)} (hξ : ξ ∈ Hset (R := R) k h) (hη : η ∈ Hset (R := R) k h) :
    ξ + η ∈ Hset (R := R) k h := by
  obtain ⟨u, φ, rfl⟩ := hξ
  obtain ⟨u', φ', rfl⟩ := hη
  refine ⟨u + u', φ + φ', Prod.ext ?_ ?_⟩ <;> funext i
  · simp
  · simp only [Prod.snd_add, Pi.add_apply, map_add]
    rw [show (fun j => algebraMap R k (u j) + algebraMap R k (u' j)) =
        (fun j => algebraMap R k (u j)) + (fun j => algebraMap R k (u' j)) from rfl, Matrix.mulVec_add, Pi.add_apply]
    ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
