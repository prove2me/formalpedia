-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isIntegral_of_mem_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:51.944853+00:00
-- url     : https://prove2.me/submissions/4c27290f-5ffb-4711-9c07-56149510b357

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
variable {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {S : Subalgebra ℤ (Polynomial Ω)} {v : (Polynomial Ω)} (hv : v ∈ S) : IsIntegral S v := isIntegral_algebraMap (x := (⟨v, hv⟩ : S))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
