-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_of_mem_orig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:18:56.104371+00:00
-- url     : https://prove2.me/submissions/735e9016-8891-409f-bc50-f0b024cc1afd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {K : Type} [Field K] {ι : Type} {m : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {p : MvPolynomial ι K} (hp : p ∈ orig K ι) : MvPolynomial.constantCoeff p = 0 := by
  have hle : orig K ι ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ι K →+* K) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simp
  exact (RingHom.mem_ker).1 (hle hp)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
