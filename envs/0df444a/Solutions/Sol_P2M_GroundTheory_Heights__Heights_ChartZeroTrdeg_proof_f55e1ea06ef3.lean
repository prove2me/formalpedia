-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_proof_f55e1ea06ef3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:46.239917+00:00
-- url     : https://prove2.me/submissions/b22ab9df-1991-4f9a-aefe-72a0b484b533

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartZeroTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_homogAt_4d6830875c0c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_genPt_eq_zero_iff__37d6bbc6b064

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
open MvPolynomial
noncomputable section
open ChartZeroTrdeg
namespace GroundTheory.Heights₂.Heights
namespace ChartZeroTrdeg
theorem _root_.solution (hA : AffineChartTrdeg.Statement) : ChartZeroTrdeg.Statement := by
  intro F _ n d Q hQ hdim Ω _ _ y j hy hyj
  have := hQ.isPrime
  have hXj : X j ∉ Q := fun h => hyj (by simpa using hy _ h)
  set ξ := genPt Q
  have hξ : ξ j ≠ 0 := fun h => hXj ((aeval_genPt_eq_zero_iff' Q (X j)).1 (by simpa using h))
  set gξ := aeval (R := F) (fun m => ξ m * (ξ j)⁻¹)
  set gy := aeval (R := F) (fun m => y m * (y j)⁻¹)
  have hker : ∀ p, gξ p = 0 → gy p = 0 := by
    intro p hp
    have hH : homogAt p j p.totalDegree ∈ Q := by
      rw [← aeval_genPt_eq_zero_iff', aeval_homogAt p j _ le_rfl ξ hξ]
      simp [gξ] at hp
      simp [hp]
    have := hy _ hH
    rw [aeval_homogAt p j _ le_rfl y hyj] at this
    simpa [gy, hyj] using this
  have hAξ := hA F n d Q j hQ hdim hXj
  rw [Algebra.adjoin_range_eq_range_aeval] at hAξ ⊢
  let e := Ideal.quotientKerAlgEquivOfSurjective gξ.rangeRestrict_surjective
  let φ := Ideal.Quotient.liftₐ (RingHom.ker gξ.rangeRestrict) gy.rangeRestrict fun p hp => by
    apply Subtype.ext
    exact hker p (congrArg Subtype.val hp)
  have hφ : Function.Surjective φ := by
    intro b
    obtain ⟨p, hp⟩ := gy.rangeRestrict_surjective b
    exact ⟨Ideal.Quotient.mk _ p, hp⟩
  have := trdeg_le_of_surjective (φ.comp e.symm.toAlgHom) (hφ.comp e.symm.surjective)
  exact this.trans hAξ.le
end ChartZeroTrdeg
end GroundTheory.Heights₂.Heights
