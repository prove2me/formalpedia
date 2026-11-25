-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_dvd_of_dvd_map_eval_139eb59d4b54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:14.909114+00:00
-- url     : https://prove2.me/submissions/0420a64e-7641-4627-8bf1-e445beb3e442

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPrimeCoverPieceSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPrimeCoverPieceSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
theorem _root_.solution {d : ℕ} {G m : Polynomial (MvPolynomial (Fin d) ℂ)} (hG : G.Monic)
    {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    (h : ∀ y : Fin d → ℂ, eval y Q ≠ 0 → G.map (eval y) ∣ m.map (eval y)) : G ∣ m := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hG]
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  have hQr : Q * (m %ₘ G).coeff i = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_mul, map_zero]
    by_cases hy : eval y Q = 0
    · rw [hy, zero_mul]
    · have h1 : (m %ₘ G).map (eval y) = 0 := by
        rw [Polynomial.map_modByMonic _ hG,
          (Polynomial.modByMonic_eq_zero_iff_dvd (hG.map _)).mpr (h y hy)]
      have h2 := congrArg (fun p => p.coeff i) h1
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
      rw [h2, mul_zero]
  exact (mul_eq_zero.mp hQr).resolve_left hQ
end GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
