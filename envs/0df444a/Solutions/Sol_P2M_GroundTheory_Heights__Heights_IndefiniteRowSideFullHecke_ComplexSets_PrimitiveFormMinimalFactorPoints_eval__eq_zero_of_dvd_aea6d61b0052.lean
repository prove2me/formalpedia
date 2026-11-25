-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_eval__eq_zero_of_dvd_aea6d61b0052
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:30.754286+00:00
-- url     : https://prove2.me/submissions/b79a583c-5bea-4b42-b685-9a990f988884

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormMinimalFactorPoints

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
open Topology Filter Polynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
theorem _root_.solution {d n : ℕ} {b : Fin n → (Fin d → ℂ) → ℂ} {y : Fin d → ℂ}
    {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (hd : (X ^ n + ∑ j, C (b j y) * X ^ (j : ℕ) : Polynomial ℂ) ∣ E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y))
    {τ : ℂ} (hτ : τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0) :
    E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) τ = 0 := by
  obtain ⟨G, hG⟩ := hd
  rw [← eval_map, hG, eval_mul]
  simp [eval_finsetSum, hτ]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
