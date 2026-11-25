-- Prove2me | solution 1 for ZetaZeros.D.EllReg.adjointPairingFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:29.567889+00:00
-- url     : https://prove2.me/submissions/d0a756d6-cd39-4864-a9b5-08ca1906cc2e

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
import Theorems.Thm_ZetaZeros_D_EllReg_pf_parseval
import Theorems.Thm_ZetaZeros_D_EllReg_pf_dw_smooth
import Theorems.Thm_ZetaZeros_D_EllReg_pf_fourier_dw
import Theorems.Thm_ZetaZeros_D_EllReg_pf_modulate
import Theorems.Thm_ZetaZeros_D_EllReg_pf_fourier_integrable
import Theorems.Thm_ZetaZeros_D_EllReg_pf_eF_smooth
import Theorems.Thm_ZetaZeros_D_EllReg_pf_sign

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
theorem _root_.solution : PairingFourier := by
  intro d m b g hb hg hgc ξ
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have term : ∀ n (w : Fin n → Fin d),
      ∫ y, g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) =
        conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ := by
    intro n w
    have hs : ContDiff ℝ ∞ (fun y => b n w y * eF ξ y) := (hb n w).1.mul (pf_eF_smooth ξ)
    have hc : HasCompactSupport (fun y => b n w y * eF ξ y) := (hb n w).2.mul_right
    obtain ⟨D1, D2⟩ := pf_dw_smooth (List.ofFn w) _ hs hc
    have hD := pf_parseval g _ hgi D1.continuous (D1.continuous.integrable_of_hasCompactSupport D2)
      (pf_fourier_integrable _ D1 D2)
    calc ∫ y, g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y)
        = (-1 : ℂ) ^ n * ∫ y, g y * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y := by
          rw [← integral_const_mul]
          congr 1
          ext y
          ring
      _ = ∫ η, (-1 : ℂ) ^ n * (𝓕 (dw (List.ofFn w) (fun y => b n w y * eF ξ y)) (-η) * 𝓕 g η) := by
          rw [hD, integral_const_mul]
      _ = conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ := by
          unfold conv
          congr 1
          ext η
          rw [pf_fourier_dw _ _ hs hc, pf_modulate, List.map_ofFn, List.prod_ofFn, neg_add_eq_sub]
          simp only [Function.comp_apply]
          rw [← pf_sign n w η]
          ring
  have hint : ∀ n (w : Fin n → Fin d),
      Integrable (fun y => g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y)) := by
    intro n w
    obtain ⟨D1, D2⟩ := pf_dw_smooth (List.ofFn w) _ ((hb n w).1.mul (pf_eF_smooth ξ)) (hb n w).2.mul_right
    exact (hg.mul (continuous_const.mul D1.continuous)).integrable_of_hasCompactSupport hgc.mul_right
  calc ∫ y, g y * trOp m b (eF ξ) y
      = ∫ y, ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) := by
        congr 1
        ext y
        simp only [trOp, Finset.mul_sum]
    _ = ∑ n ∈ Finset.range (m + 1), ∫ y, ∑ w : Fin n → Fin d,
          g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) :=
        integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun w _ => hint n w))
    _ = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          ∫ y, g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        exact integral_finsetSum _ (fun w _ => hint n w)
    _ = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
        exact term n w
end ZetaZeros.D.EllReg
