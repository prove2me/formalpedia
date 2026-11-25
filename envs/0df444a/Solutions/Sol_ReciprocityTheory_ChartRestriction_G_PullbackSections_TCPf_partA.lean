-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.partA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:32.184894+00:00
-- url     : https://prove2.me/submissions/e7e0b783-0645-4cf0-9964-6829ba0a0824

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_IsTayF_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_diagCLM_apply

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
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution (f : (Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω f 0) (c : Fin g → ℂ) :
    tay (fun z => f fun i => c i * z i) 0 = subst (fun p : Fin 1 × Fin g => C (c p.2) * X p) (tay f 0) := by
  have e : (fun z : Fin g → ℂ => f fun i => c i * z i) = f ∘ diagCLM c := by
    funext z
    simp only [Function.comp, diagCLM_apply]
  have hA : ContDiffAt ℂ ω (f ∘ diagCLM c) 0 :=
    ContDiffAt.comp (0 : Fin g → ℂ) (by rw [map_zero]; exact hf) (diagCLM c).contDiff.contDiffAt
  have h1 := isTayF_tay hA
  rw [← e] at h1
  apply IsTayF.eq h1
  have h2 := isTayF_subst f hf (fun p : Fin 1 × Fin g => C (c p.2) * X p)
    (fun p q => if p = q then c p.2 else 0) (fun p => by simp) (fun p q => by
      rw [← MvPowerSeries.smul_eq_C_mul]
      first
        | rw [Derivation.map_smul, MvPowerSeries.pderiv_X]
        | rw [LinearMap.map_smul_of_tower, MvPowerSeries.pderiv_X]
      by_cases h : p = q
      · subst h
        simp [MvPowerSeries.smul_eq_C_mul]
      · simp [h, Pi.single_apply, Ne.symm h])
  have hv : ∀ q : Fin 1 × Fin g, diagCLM c (Pi.single q.2 1) =
      ∑ p : Fin 1 × Fin g, (if p = q then c p.2 else 0) • (Pi.single p.2 1 : Fin g → ℂ) := by
    intro q
    rw [diagCLM_apply]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    funext i
    by_cases h : i = q.2 <;> simp [Pi.single_apply, h]
  have h3 := isTayF_comp hf (diagCLM c) (w := fun p : Fin 1 × Fin g => (Pi.single p.2 1 : Fin g → ℂ)) hv h2
  rw [← e] at h3
  exact h3
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
