-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.foldr_iterate_eq_TG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:51.813616+00:00
-- url     : https://prove2.me/submissions/c4a4fb64-e466-43f1-bcc1-3668f948a107

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_TG_replicate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_TG_append


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
theorem _root_.solution (Ls : List ι) (m : ι →₀ ℕ) (A : S) :
    Ls.foldr (fun l g => (D l)^[m l] g) A = TG D (word Ls m) A := by
  induction Ls with
  | nil => rfl
  | cons l Ls ih =>
    rw [List.foldr_cons, ih]
    have e : word (l :: Ls) m = List.replicate (m l) l ++ word Ls m := by simp [word]
    rw [e, TG_append, TG_replicate]
end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
