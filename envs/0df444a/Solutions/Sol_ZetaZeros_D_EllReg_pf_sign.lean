-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:05:57.507327+00:00
-- url     : https://prove2.me/submissions/1c3051f4-b517-48d6-998e-8cfae68d72f2

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (n : ℕ) (w : Fin n → Fin d) (η : E d) :
    (-1 : ℂ) ^ n * ∏ l, (2 * Real.pi * Complex.I * (((-η) (w l) : ℝ) : ℂ)) = mono w η := by
  unfold mono
  have h : ∀ l, (2 * (Real.pi : ℂ) * Complex.I * (((-η) (w l) : ℝ) : ℂ)) =
      (-1) * (2 * Real.pi * Complex.I * ((η (w l) : ℝ) : ℂ)) := by
    intro l
    rw [PiLp.neg_apply]; push_cast; ring
  rw [Finset.prod_congr rfl (fun l _ => h l), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← mul_assoc, ← mul_pow]
  norm_num
end ZetaZeros.D.EllReg
