-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.kill_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:40.223801+00:00
-- url     : https://prove2.me/submissions/1ee258bc-396e-4055-8e0a-80fc488598ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_foldr_iterate_eq_TG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_half_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_TG_add


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
theorem _root_.solution [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (hP : secondOrder k c P = 0) (G Y : S) :
    e (PolG D κ P (G * (1 + q * Y))) = e (PolG D κ P G) := by
  have hsplit : G * (1 + q * Y) = G + G * Y * q := by ring
  have hlin : ∀ A B, PolG D κ P (A + B) = PolG D κ P A + PolG D κ P B := by
    intro A B
    simp only [PolG, foldr_iterate_eq_TG]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [TG_add, mul_add]
    exact hadd
  rw [hsplit, hlin, map_add, half_gen D κ hadd hC hmul e he c q hc hq0 hq1 hq2 P (G * Y), hP]
  simp [PolG]
end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
