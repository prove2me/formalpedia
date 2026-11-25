-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.mD_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:43.783704+00:00
-- url     : https://prove2.me/submissions/120cf933-1e64-42eb-83da-7ddbe99c6ff6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_iter_comp_clm
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : W →L[ℂ] V) (S : Multiset W) :
    mD (f ∘ A) 0 S = mD f 0 (S.map A) := by
  have gen : ∀ (n m : ℕ) (h : n = m) (v : Fin n → V) (v' : Fin m → V), (∀ j, v j = v' (Fin.cast h j)) →
      iteratedFDeriv ℂ n f 0 v = iteratedFDeriv ℂ m f 0 v' := by
    intro n m h v v' hv
    subst h
    congr 1
    funext j
    exact hv j
  have hl : ∀ l : List W, lD (f ∘ A) 0 l = lD f 0 (l.map A) := by
    intro l
    unfold lD
    rw [iter_comp_clm hf A]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    refine gen _ _ (by simp) _ _ (fun j => ?_)
    simp [List.get_eq_getElem]
  have hS : S.map A = ((S.toList.map A : List V) : Multiset V) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  show lD (f ∘ A) 0 S.toList = _
  rw [hl, hS, mD_coe hf]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
