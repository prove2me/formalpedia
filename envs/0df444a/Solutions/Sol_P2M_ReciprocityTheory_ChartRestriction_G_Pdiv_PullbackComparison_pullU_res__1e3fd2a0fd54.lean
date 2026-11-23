-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:46.137731+00:00
-- url     : https://prove2.me/submissions/9451eac5-00bf-4903-98ca-0b9faab74807

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU

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
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (fun _ hy => h hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U x) := by
  apply unit_ext
  intro y hy
  have hP : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := fun _ hz => h hz
  rw [gU_pullU, gU_res h (f.base y) hy x]
  exact (gU_pullU f U y (hP hy) x).symm.trans (gU_res hP y hy (pullU f U x)).symm
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
