-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_fourier_dw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:10.365051+00:00
-- url     : https://prove2.me/submissions/df4ade59-4d13-41ed-a346-9e6e20741de3

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
import Theorems.Thm_ZetaZeros_D_EllReg_pf_dw_smooth
import Theorems.Thm_ZetaZeros_D_EllReg_pf_fourier_fderiv

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
theorem _root_.solution (L : List (Fin d)) (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (ζ : E d) :
    𝓕 (dw L k) ζ = (L.map fun j => 2 * Real.pi * Complex.I * ((ζ j : ℝ) : ℂ)).prod * 𝓕 k ζ := by
  induction L with
  | nil => simp [dw]
  | cons j w ih =>
    obtain ⟨h1, h2⟩ := pf_dw_smooth w k hk hkc
    show 𝓕 (fun x => fderiv ℝ (dw w k) x (ev j)) ζ = _
    rw [pf_fourier_fderiv _ h1 h2, ih, List.map_cons, List.prod_cons]
    have hb : inner ℝ ζ (ev j) = ζ j := by
      simp [ev, EuclideanSpace.inner_single_right]
    rw [hb]; ring
end ZetaZeros.D.EllReg
