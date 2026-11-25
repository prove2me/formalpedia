-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_c7b2d23830f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:53.208119+00:00
-- url     : https://prove2.me/submissions/57933996-d50d-4ed7-9bc1-5e328685e9ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
variable (S : Type) [CommRing S] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution (y : (Σ k, ι k) → Ω) (m : ℕ) (t : Cell K ι m → Ω) (J : Cell K ι (m + 1))
    (hJ : CellMeets y J.1) :
    cellD S y m t J = ∑ k, ∑ i ∈ J.1 k, faceSign J.1 k i • ext m t (rem J.1 ⟨k, i⟩) := by
  simp only [cellD, LinearMap.pi_apply, if_pos hJ, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  unfold ext rem
  by_cases h : (∀ l, (Function.update J.1 k ((J.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update J.1 k ((J.1 k).erase i) l).card - 1) = m
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h, smul_zero]; rfl
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
