-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.e_PolG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:27.820136+00:00
-- url     : https://prove2.me/submissions/ca968cde-f5f6-4e99-af96-5ed8ef10a37c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_foldr_iterate_eq_TG

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2 ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
open ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
theorem _root_.solution [Fintype ι] (e : S →+* k) (he : ∀ a, e (κ a) = a) (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P A) = (AddMonoidAlgebra.coeff P).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) := by
  simp only [PolG, map_sum, map_mul, he, foldr_iterate_eq_TG]
  rfl
end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
