-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.mem_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:05.417833+00:00
-- url     : https://prove2.me/submissions/c0e7a427-c1dd-48e5-b4fd-c822b1977a37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution {ρ : ℂ} :
    ρ ∈ (G.P.map (deh w 0)).roots ↔ G.P.eval₂ (deh w 0) ρ = 0 := by
  rw [Polynomial.mem_roots (G.monic.map _).ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map]
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
