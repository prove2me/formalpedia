-- Prove2me | solution 1 for PositivityTheory.KReal.gen_graded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:19.370716+00:00
-- url     : https://prove2.me/submissions/09e9074d-19bf-4ffd-b660-15e47008990f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Theorems.Thm_PositivityTheory_KReal_unit_homog
import Theorems.Thm_PositivityTheory_KReal_act_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {p q r : ℕ} (x : Pol p q r 0) (dx : ℕ) (hx : x ∈ homog (Ix p q × Ix r 0) dx) :
    ∀ d, ∀ z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}),
      homogeneousComponent d z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}) := by
  set L := genG (fockAct1 p q r 0) (Submodule.span ℂ {x}) with hLdef
  have hxL : x ∈ L := by
    rw [hLdef, genG, Submodule.mem_sInf]
    exact fun N hN => hN.1 (Submodule.mem_span_singleton_self x)
  have hst : ∀ W, ∀ z ∈ L, fockAct1 p q r 0 W z ∈ L := by
    intro W z hz
    rw [hLdef, genG, Submodule.mem_sInf] at hz ⊢
    exact fun N hN => hN.2 W z (hz N hN)
  have hhom : ∀ e d, ∀ w ∈ homog (Ix p q × Ix r 0) e, w ∈ L → homogeneousComponent d w ∈ L := by
    intro e d w hw hwL
    rw [homogeneousComponent_of_mem hw]
    split_ifs
    · exact hwL
    · exact L.zero_mem
  let L' : Submodule ℂ (Pol p q r 0) := ⨅ d, L.comap (homogeneousComponent d)
  have mem' : ∀ z, z ∈ L' ↔ ∀ d, homogeneousComponent d z ∈ L := fun z => by
    simp only [L', Submodule.mem_iInf, Submodule.mem_comap]
  have hle : L ≤ L' := by
    rw [hLdef, genG]
    refine sInf_le ⟨?_, ?_⟩
    · rw [Submodule.span_singleton_le_iff_mem, mem']
      exact fun d => hhom dx d x hx hxL
    · intro W z hz
      rw [act_eq_sum]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
      rw [← sum_homogeneousComponent z, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨e, he⟩ := unit_homog a b i _ (homogeneousComponent_mem i z)
      rw [mem']
      exact fun d => hhom e d _ he (hst _ _ ((mem' z).1 hz i))
  exact fun d z hz => (mem' z).1 (hle hz) d
end PositivityTheory.KReal
