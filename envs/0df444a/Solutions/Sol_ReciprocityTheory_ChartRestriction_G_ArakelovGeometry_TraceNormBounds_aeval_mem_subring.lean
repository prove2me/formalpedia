-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.aeval_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:31.756153+00:00
-- url     : https://prove2.me/submissions/dccffaf6-e736-4079-934d-6f02ff3b3b84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution {o σ : Type*} [CommRing o] [Algebra o Ω] (F : Subring Ω)
    (hc : ∀ a : o, algebraMap o Ω a ∈ F) (v : σ → Ω) (hv : ∀ k, v k ∈ F)
    (f : MvPolynomial σ o) : MvPolynomial.aeval v f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hc a
  | add p q hp hq => simpa using F.add_mem hp hq
  | mul_X p k hp => simpa using F.mul_mem hp (hv k)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
