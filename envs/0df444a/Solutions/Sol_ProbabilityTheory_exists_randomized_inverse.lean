-- Prove2me | solution 1 for ProbabilityTheory.exists_randomized_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:05.825868+00:00
-- url     : https://prove2.me/submissions/57dda454-002e-4415-862e-a232bda21214

module
public import Mathlib.Probability.Kernel.Representation
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Definitions.Def_LeanPool_Copula_Distribution_RandomizedInverse

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter Function
open scoped unitInterval
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution {B : Type*} [MeasurableSpace B] [StandardBorelSpace B]
    (q : I → B) (hq : Measurable q) :
    ∃ g : B → I → I, Measurable (uncurry g) ∧
      ((volume.map q).prod volume).map (uncurry g) = volume ∧
      ∀ᵐ p ∂((volume.map q).prod volume), q (g p.1 p.2) = p.1 := by
  let κ := condDistrib (id : I → I) q volume
  obtain ⟨g, hg, hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let H : B × I → B × I := fun p => (p.1, g p.1 p.2)
  have hH : Measurable H := measurable_fst.prodMk hg
  have hgraph : ((volume.map q).prod volume).map H = (volume.map q) ⊗ₘ κ := by
    ext s hs
    rw [Measure.map_apply hH hs, Measure.prod_apply (hH hs), Measure.compProd_apply hs]
    apply lintegral_congr
    intro b
    rw [← hmap b, Measure.map_apply hg.of_uncurry_left (measurable_prodMk_left hs)]
    rfl
  have hdis : (volume.map q) ⊗ₘ κ = volume.map (fun t : I => (q t, t)) := by
    exact compProd_map_condDistrib measurable_id.aemeasurable
  have hunif : ((volume.map q).prod volume).map (uncurry g) = volume := by
    have hp : Measurable (fun t : I => (q t, t)) := hq.prodMk measurable_id
    have h := congrArg (fun m : Measure (B × I) => m.map Prod.snd) (hgraph.trans hdis)
    rw [Measure.map_map measurable_snd hH,
      Measure.map_map measurable_snd hp] at h
    simpa only [comp_def, H, uncurry_def, Measure.map_id'] using h
  refine ⟨g, hg, hunif, ?_⟩
  have hae : ∀ᵐ p ∂(volume.map (fun t : I => (q t, t))), q p.2 = p.1 := by
    apply (ae_map_iff (hq.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hq.comp measurable_snd) measurable_fst)).mpr
    exact Eventually.of_forall fun _ => rfl
  rw [← hdis, ← hgraph] at hae
  exact ae_of_ae_map hH.aemeasurable hae
end ProbabilityTheory
