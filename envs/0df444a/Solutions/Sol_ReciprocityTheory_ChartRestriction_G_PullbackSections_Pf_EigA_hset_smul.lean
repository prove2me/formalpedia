-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.hset_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:19:10.85598+00:00
-- url     : https://prove2.me/submissions/c2734937-b83d-427f-ab1d-cd21a4a5bf52

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
theorem _root_.solution (c : R) {ξ : (Fin d → k) × (Fin d → k)} (hξ : ξ ∈ Hset (R := R) k h) :
    algebraMap R k c • ξ ∈ Hset (R := R) k h := by
  obtain ⟨u, φ, rfl⟩ := hξ
  refine ⟨c • u, c • φ, Prod.ext ?_ ?_⟩ <;> funext i
  · simp [Algebra.smul_def]
  · have hv : (fun j => algebraMap R k ((c • u) j)) = algebraMap R k c • fun j => algebraMap R k (u j) := by
      funext j
      simp
    rw [hv, Matrix.mulVec_smul]
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul]
    ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
