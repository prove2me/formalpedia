-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:22.740291+00:00
-- url     : https://prove2.me/submissions/0c973049-4d44-4cda-842e-0e733dcec6a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {a b : Fin r} (hab : ¬((a : ℕ) < p0 ↔ (b : ℕ) < p0)) : sv p0 b ≠ sv p0 a := by
  unfold sv
  split_ifs with h1 h2
  · exact absurd (iff_of_true h2 h1) hab
  · norm_num
  · norm_num
  · exact absurd (iff_of_false ‹_› h1) hab
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
