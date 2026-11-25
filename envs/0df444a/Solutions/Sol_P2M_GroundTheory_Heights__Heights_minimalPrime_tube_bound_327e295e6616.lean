-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_minimalPrime_tube_bound_327e295e6616
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:51.050799+00:00
-- url     : https://prove2.me/submissions/daeb3307-77a1-496e-b82b-816131f9cfb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetTubeVolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_withBot_enat_le_pred_3ed6693ab82f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : PrimeTubeVolume.Statement) {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)}
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ)) (hK : IsCompact K)
    {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P ∈ I.minimalPrimes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (Metric.thickening r (zeroSet P ∩ K)) ≤
        ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) := by
  have hprime : P.IsPrime := hP.1.1
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2) (Ideal.Quotient.factor_surjective hP.1.2)
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨hd, hk⟩ := withBot_enat_le_pred hnn (hle.trans_lt hdim)
  obtain ⟨C, hC, hCr⟩ := h n (d - 1) P K hprime hk hK
  refine ⟨C, hC, fun r hr => ?_⟩
  have he : ((2 * n : ℤ) - 2 * ((d - 1 : ℕ) : ℤ)) = (2 * n + 2 : ℤ) - 2 * d := by omega
  simpa [he] using hCr r hr
end GroundTheory.Heights₂.Heights
