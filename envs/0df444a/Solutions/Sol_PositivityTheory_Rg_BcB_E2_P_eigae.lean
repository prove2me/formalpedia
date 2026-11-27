-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.eigae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:18:44.518103+00:00
-- url     : https://prove2.me/submissions/78452c1f-d7ae-4205-91a4-6b2fb954747f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Eigae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : WeakAE → EigAE := by
  intro hW X ι S _ _ ν _ F f Φ σ A hFc hrep hΦ hσ hσA hE
  have hfm : ∀ j, Measurable (Function.uncurry (f j)) := fun j => (hrep j).1
  have hfx : ∀ j x, Measurable (f j x) := fun j x => (hfm j).comp measurable_prodMk_left
  have key : ∀ i x, ∀ᵐ s ∂ν, ∑ j, ∫ y, Φ i j y * conj (f j (x * y) s) ∂X.μ = σ s * conj (f i x s) := by
    intro i x
    refine hW X.G S ι X.μ ν (fun j y => F j (x * y)) (fun j y => f j (x * y)) (fun j => Φ i j)
      (fun s => σ s * conj (f i x s)) (fun j => ⟨?_, fun y => (hrep j).2 (x * y)⟩)
      (fun j => (hΦ i j).1.aestronglyMeasurable) (fun j => ?_) ?_ (fun h => ?_)
    · exact (hfm j).comp ((measurable_const_mul x).prodMap measurable_id)
    · have hc : Continuous fun y => Φ i j y • F j (x * y) :=
        (hΦ i j).1.smul ((hFc j).comp (continuous_const.mul continuous_id))
      have hi := (hc.integrable_of_hasCompactSupport (μ := X.μ) ((hΦ i j).2.smul_right)).2
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hi)
      refine lintegral_congr fun y => ?_
      simp [enorm_smul]
    · have hm : MemLp (f i x) 2 ν := (Lp.memLp (F i x)).ae_eq ((hrep i).2 x).symm
      refine MemLp.of_le_mul (c := A) hm ?_ (ae_of_all _ fun s => ?_)
      · exact (hσ.mul (Complex.continuous_conj.measurable.comp (hfx i x))).aestronglyMeasurable
      · simp only [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hσA s) (norm_nonneg _)
    · rw [hE x i h]
      refine integral_congr_ae ?_
      filter_upwards [(hrep i).2 x] with s hs
      simp [hs]
  refine ae_all_iff.2 fun i => ?_
  have hmeas : MeasurableSet {p : X.G × S |
      ∑ j, ∫ y, Φ i j y * conj (f j (p.1 * y) p.2) ∂X.μ = σ p.2 * conj (f i p.1 p.2)} := by
    refine measurableSet_eq_fun ?_ ?_
    · refine Finset.measurable_sum _ fun j _ => ?_
      have : StronglyMeasurable fun q : (X.G × S) × X.G => Φ i j q.2 * conj (f j (q.1.1 * q.2) q.1.2) := by
        refine Measurable.stronglyMeasurable ?_
        refine ((hΦ i j).1.measurable.comp measurable_snd).mul (Complex.continuous_conj.measurable.comp ?_)
        exact (hfm j).comp ((measurable_fst.fst.mul measurable_snd).prodMk measurable_fst.snd)
      exact (this.integral_prod_right' (ν := X.μ)).measurable
    · exact (hσ.comp measurable_snd).mul (Complex.continuous_conj.measurable.comp (hfm i))
  exact (Measure.ae_ae_comm hmeas).1 (ae_of_all _ fun x => key i x)
end PositivityTheory.Rg.BcB.E2.P
