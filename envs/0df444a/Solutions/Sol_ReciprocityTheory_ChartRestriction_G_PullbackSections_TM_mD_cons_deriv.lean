-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.mD_cons_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:19.752701+00:00
-- url     : https://prove2.me/submissions/73dda6c7-8726-4cce-9f0c-f6600fe490ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_mD_coe


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (t : Multiset (Fin g → ℂ)) :
    mD θ 0 (v ::ₘ t) = mD (fun y => fderiv ℂ θ y v) 0 t := by
  have ht : ((t.toList : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) = t := Multiset.coe_toList t
  have hperm : (v ::ₘ t) = ((t.toList ++ [v] : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) := by
    conv_lhs => rw [← ht]
    rw [Multiset.cons_coe, Multiset.coe_eq_coe]
    exact (List.perm_append_singleton v t.toList).symm
  have hlen : (t.toList ++ [v]).length = t.toList.length + 1 := by simp
  rw [hperm, mD_coe hθ, lD_eq θ 0 (t.toList ++ [v]) hlen, iteratedFDeriv_succ_apply_right]
  have hf : ContDiffAt ℂ ω (fderiv ℂ θ) 0 := hθ.fderiv_right (by simp)
  have hcomp : (fun y => fderiv ℂ θ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ (fderiv ℂ θ) := rfl
  unfold mD lD
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf le_top]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  congr 1
  · congr 1
    funext i
    simp only [Fin.init]
    exact List.getElem_append_left i.isLt
  · simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
