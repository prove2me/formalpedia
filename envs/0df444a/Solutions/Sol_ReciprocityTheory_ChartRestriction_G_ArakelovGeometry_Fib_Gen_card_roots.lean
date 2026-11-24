-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.card_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:02.342521+00:00
-- url     : https://prove2.me/submissions/6d982a94-1dcd-4e4a-9405-eeea810d44fb

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
theorem _root_.solution : (G.P.map (deh w 0)).roots.card = G.P.natDegree := by
  have hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree := by
    first
    | exact G.monic.natDegree_map _
    | exact Polynomial.natDegree_map_of_monic G.monic _
  rw [← hd]
  first
  | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  | exact IsAlgClosed.card_roots_eq_natDegree
  | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  | simp
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
