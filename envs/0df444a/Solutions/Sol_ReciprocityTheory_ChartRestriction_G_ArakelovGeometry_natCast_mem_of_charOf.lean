-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:12.449645+00:00
-- url     : https://prove2.me/submissions/64323be1-dbdd-4472-9ca0-04d58e187a03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  show (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : MRing ι) ∈ W
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
  have hn : (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : ℤ) ∈
      W.comap (C : ℤ →+* MRing ι) := by
    obtain ⟨u, hu⟩ : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ∣
        ((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℤ) :=
      Int.dvd_natAbs.2 dvd_rfl
    rw [hu]
    exact Ideal.mul_mem_right u _ hg
  have h := Ideal.mem_comap.1 hn
  rwa [map_natCast] at h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
