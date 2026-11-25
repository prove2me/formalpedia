-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.TG_replicate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:26.199741+00:00
-- url     : https://prove2.me/submissions/2359e0b1-5c8d-4451-ac04-5842670421b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG

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
theorem _root_.solution (n : ℕ) (l : ι) (A : S) : TG D (List.replicate n l) A = (D l)^[n] A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
    rfl
end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
