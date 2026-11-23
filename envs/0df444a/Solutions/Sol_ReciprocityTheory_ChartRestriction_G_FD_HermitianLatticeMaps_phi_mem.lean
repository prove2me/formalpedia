-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:06.08915+00:00
-- url     : https://prove2.me/submissions/f8d24b26-053d-45ce-bc45-fffbb52cf424

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
open Matrix NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (f f' : Basis ι ℤ X.Λ)
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
theorem _root_.solution {x : Fin r → E} (hx : x ∈ X.Λ) : phi X f f' x ∈ X.Λ := by
  have e : x = ∑ i, f.repr ⟨x, hx⟩ i • (f i : Fin r → E) := coe_expand X f ⟨x, hx⟩
  rw [e, phi_zsum]
  exact Submodule.sum_mem _ fun i _ => zsmul_mem (f' i).2 _
end ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
