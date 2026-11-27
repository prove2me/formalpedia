-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_proof_1c6f0c8295e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:29.632891+00:00
-- url     : https://prove2.me/submissions/62671445-536d-4081-9344-6669b7b85eae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_exists_contDiff_eqOn_559fbad3aef1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_varInt_congr_875943a43ccc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_smoothNear_weight_92c84333f07a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)
open LelongWeightLimit
namespace GroundTheory.Heights₂.Heights.Targets
namespace LelongWeightLimit
theorem _root_.solution (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement)
    (hS : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement) (hD : LelongWeightDiff.Statement) :
    LelongWeightLimit.Statement := by
  intro n d J u f k φ hJ hdim hu hf hfc hφ hk hk0
  obtain ⟨g, hg, hgc, hgf⟩ :=
    exists_contDiff_eqOn (GroundTheory.Heights₂.Heights.SheetSumMeasurable.isClosed_zeroSet J) hf hfc
  have hsum : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) =
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    refine finsum_congr fun W => finsum_congr fun hW => ?_
    rw [varInt_congr (fun x hx => hgf x fun q hq => hx q (le_sup_left.trans hW.1.2 hq)) φ]
  have hlim := (hL n d J u g φ hJ hdim hu hg hgc hφ).add (hD n d J u g k φ hJ hdim hu hg hgc hφ hk hk0)
  rw [hsum, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [varInt_congr (fun x hx => (hgf x hx).symm) (vecCons _ φ),
    hS n d J g _ φ hJ hdim (smoothNear_of_contDiff hg) (smoothNear_weight u hk hk0 hε) hφ (Or.inl hgc),
    hS n d J g (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hg)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hgc)]
  ring
end LelongWeightLimit
end GroundTheory.Heights₂.Heights.Targets
