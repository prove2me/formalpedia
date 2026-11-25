-- Prove2me | solution 1 for PI.VolStabW.RPA.kap_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:53.364714+00:00
-- url     : https://prove2.me/submissions/8f515184-909e-4b61-af33-2063ac6ff3bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_KapIntegral
import Theorems.Thm_PI_VolStabW_RPA_Qm_integral
import Theorems.Thm_PI_VolStabW_RPA_eS_symm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]
namespace PI.VolStabW.RPA
theorem _root_.solution [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun x => ∏ i ∈ T, g i (x i)) (kap m L S) ∧
    ∫ x, ∏ i ∈ T, g i (x i) ∂kap m L S =
      (∏ i ∈ T, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  have hfun : ∀ p, (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ((eS S).symm p) =
      (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) := by
    intro p
    simp only
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => i ∈ S)]
    congr 1
    · rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hST, ← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [eS_symm_apply, dif_pos i.2]
    · rw [← Finset.prod_subtype_eq_prod_filter]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [eS_symm_apply, dif_neg j.2]
  have hR : Integrable (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (Rm m L S) := by
    unfold Rm; exact Integrable.fintype_prod_dep (fun i => (hg i.1).restrict)
  obtain ⟨hQi, hQ⟩ := Qm_integral hfin hT hST g hg
  rw [← hT'] at hQi hQ
  have hcomp : (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ∘ (eS S).symm =
      fun p => (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) :=
    funext hfun
  refine ⟨?_, ?_⟩
  · unfold kap
    rw [integrable_map_equiv, hcomp]
    exact Integrable.mul_prod (μ := Rm m L S) (ν := Qm m L S)
      (f := fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (g := fun z => ∏ j ∈ T', g j.1 (z j)) hR hQi
  · unfold kap
    rw [integral_map_equiv]
    refine (integral_congr_ae (ae_of_all _ hfun)).trans ?_
    rw [integral_prod_mul (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (fun z : (∀ i : {i // i ∉ S}, W i) => ∏ j ∈ T', g j.1 (z j)), hQ, Rm, integral_fintype_prod_eq_prod,
      ← Finset.prod_sdiff hST]
    have hS : ∏ i : {i // i ∈ S}, ∫ w, g i.1 w ∂(m i.1).restrict (L i.1)ᶜ =
        ∏ i ∈ S, ∫ w, g i w ∂(mu m L S i) := by
      rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [mu, if_pos i.2]
    rw [hS]
    ring
end PI.VolStabW.RPA
