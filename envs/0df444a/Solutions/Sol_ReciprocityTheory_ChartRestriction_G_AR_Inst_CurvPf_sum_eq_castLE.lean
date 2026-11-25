-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.sum_eq_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:31.766942+00:00
-- url     : https://prove2.me/submissions/1a94bb58-5fdf-4d57-a0a5-a85eb76ebbbb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviVReLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LminorMapConj

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
variable {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {m : ℕ} (hm : m ≤ r) {M : Type} [AddCommMonoid M] (g : Fin r → M)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → g k = 0) :
    ∑ k, g k = ∑ j : Fin m, g (Fin.castLE hm j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ g
    (fun k hk => hg k ?_) (fun j => rfl)
  by_contra h
  push_neg at h
  exact hk ⟨⟨k, h⟩, Fin.ext rfl⟩
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
