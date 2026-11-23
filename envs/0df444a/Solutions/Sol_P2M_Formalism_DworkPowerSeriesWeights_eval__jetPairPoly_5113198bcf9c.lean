-- Prove2me | solution 1 for P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:49.044166+00:00
-- url     : https://prove2.me/submissions/6725d7b0-0a4f-4b98-8020-8e037f8d77e9

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {F K : Type} [Field F] [Field K] {σ ι : Type} (φ : F →+* K) (x : σ → K)
    (P : MvPolynomial ι (MvPolynomial σ F)) (Th : MvPowerSeries ι F) :
    MvPolynomial.eval₂ φ x (jetPairPoly P Th) =
      jetPair (MvPolynomial.map (MvPolynomial.eval₂Hom φ x) P) (MvPowerSeries.map φ Th) := by
  classical
  unfold jetPairPoly jetPair
  rw [show MvPolynomial.eval₂ φ x = MvPolynomial.eval₂Hom φ x from rfl, map_sum]
  symm
  rw [Finset.sum_subset (MvPolynomial.support_map_subset _ P)]
  · refine Finset.sum_congr rfl fun κ _ => ?_
    simp [MvPolynomial.coeff_map, MvPowerSeries.coeff_map, mul_assoc]
  · intro κ _ hκ
    simp only [MvPolynomial.mem_support_iff, not_not] at hκ
    simp [hκ]
end Formalism.DworkPowerSeriesWeights
