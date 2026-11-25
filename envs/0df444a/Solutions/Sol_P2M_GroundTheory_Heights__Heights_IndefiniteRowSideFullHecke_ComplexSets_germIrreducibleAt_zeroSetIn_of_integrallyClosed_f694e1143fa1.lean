-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germIrreducibleAt_zeroSetIn_of_integrallyClosed_f694e1143fa1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:50.863109+00:00
-- url     : https://prove2.me/submissions/071b6d57-9680-41eb-9040-0098b735adf2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalZerosNowhereDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (hic : NormalGermIntegrallyClosed.Statement)
    {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (hI : I.IsPrime)
    (hn : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I)) (hw : w ∈ zeroSetIn I) :
    GermIrreducibleAt (zeroSetIn I) w := by
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfne, hgne⟩ := hcon
  set X := zeroSetIn I with hX
  set N : Set (σ → ℂ) :=
    ({z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z}) ∩ interior {z | z ∈ X → f z * g z = 0} with hNdef
  have hNo : IsOpen N := ((isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)).inter isOpen_interior
  have hwN : w ∈ N := ⟨⟨hf, hg⟩, mem_interior_iff_mem_nhds.mpr hfg⟩
  have hfd : DifferentiableOn ℂ f N := fun z hz => hz.1.1.differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℂ g N := fun z hz => hz.1.2.differentiableAt.differentiableWithinAt
  have hfgN : ∀ z ∈ X ∩ N, f z * g z = 0 := fun z hz => interior_subset hz.2.2 hz.1
  have hGne : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → (f + g) z = 0 := by
    intro hev
    apply hfne
    filter_upwards [hev, hfg] with z h1 h2 hz
    have hs : f z + g z = 0 := h1 hz
    have hp : f z * g z = 0 := h2 hz
    have hff : f z * f z = 0 := by linear_combination f z * hs - hp
    exact mul_self_eq_zero.mp hff
  have ha : ∀ j, DifferentiableOn ℂ ((![0, -1] : Fin 2 → (σ → ℂ) → ℂ) j) N := by
    intro j
    fin_cases j
    · exact differentiableOn_const (0 : ℂ)
    · exact differentiableOn_const (-1 : ℂ)
  obtain ⟨V, hV, hwV, H, hH, hfH⟩ := hic σ I w N f (f + g) 2 ![0, -1] hI hn hw hNo hwN hfd (hfd.add hgd)
    ha hGne (by
      intro z hz
      have hp := hfgN z hz.1
      simp [Fin.sum_univ_two]
      linear_combination -hp)
  have hHc : ContinuousAt H w := (hH.differentiableAt (hV.mem_nhds hwV)).continuousAt
  have hev : ∀ᶠ z in 𝓝 w, z ∈ V ∧ (z ∈ X → f z * g z = 0) := (show ∀ᶠ z in 𝓝 w, z ∈ V from hV.mem_nhds hwV).and hfg
  rw [Filter.not_eventually] at hfne hgne
  have h1 : H w = 1 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hfne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hg0 : g z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_left hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hg0, add_zero] at hfz
    exact hzH.2 (mul_left_cancel₀ hz.2 (hfz.symm.trans (mul_one _).symm))
  have h0 : H w = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hgne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hf0 : f z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_right hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hf0, zero_add] at hfz
    exact hzH.2 ((mul_eq_zero.mp hfz.symm).resolve_left hz.2)
  exact one_ne_zero (h1.symm.trans h0)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
