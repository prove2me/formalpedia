-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.perm_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:26.430741+00:00
-- url     : https://prove2.me/submissions/693c15bd-7679-4021-a484-637bc2a1c444

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_sideE_symm_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_side_inl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (s : ι → Bool) :
    ((Finset.univ : Finset ι).toList.filter (fun l => s l)).Perm
      (List.ofFn fun i => (sideE s).symm (Sum.inl i)) := by
  rw [List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _) ?_]
  · intro x
    simp only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and, List.mem_ofFn, Set.mem_range]
    constructor
    · intro hx
      exact ⟨Fintype.equivFin _ ⟨x, hx⟩, by rw [sideE_symm_inl]; simp⟩
    · rintro ⟨i, rfl⟩
      exact side_inl s i
  · rw [List.nodup_ofFn]
    intro i j hij
    simpa using congrArg (sideE s) hij
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
