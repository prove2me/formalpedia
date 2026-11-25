-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.secOf_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:23:44.470211+00:00
-- url     : https://prove2.me/submissions/40f2d88e-bf84-4042-b92d-a053cf7a2b11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)} (hP : P.IsPrime) {i : ∀ k, ι k}
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ P) (b : K → ℕ) : secOf i b ∉ P := by
  rw [secOf]
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
  exact hi k (hP.mem_of_pow_mem _ hk)
end ReciprocityTheory.ChartRestriction.G.Geo
