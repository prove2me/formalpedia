-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_parseval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:04.020894+00:00
-- url     : https://prove2.me/submissions/a0eaa0b0-2906-47c4-a833-42b83e6add8b

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
private theorem norm_eF_eq_one (ξ y : E d) : ‖eF ξ y‖ = 1 := by
  unfold eF
  have h : -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)) =
      ((-(2 * Real.pi * inner ℝ y ξ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _
private theorem fourier_eq_integral_eF_mul (f : E d → ℂ) (ζ : E d) :
    𝓕 f ζ = ∫ x, eF ζ x * f x := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  try dsimp only
  rw [smul_eq_mul]
  unfold eF
  congr 1; congr 1; push_cast; ring
private theorem fourierInv_eq_integral_eF_neg_mul (F : E d → ℂ) (y : E d) :
    𝓕⁻ F y = ∫ η, eF (-η) y * F η := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  try dsimp only
  rw [smul_eq_mul]
  unfold eF
  rw [inner_neg_right, real_inner_comm]
  congr 1; congr 1; push_cast; ring
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (g k : E d → ℂ) (hg : Integrable g) (hkc : Continuous k)
    (hk : Integrable k) (hK : Integrable (𝓕 k)) :
    ∫ y, g y * k y = ∫ η, 𝓕 k (-η) * 𝓕 g η := by
  have hinv : ∀ y, k y = ∫ η, eF (-η) y * 𝓕 k η := by
    intro y
    rw [← fourierInv_eq_integral_eF_neg_mul]
    exact (congrFun (hkc.fourierInv_fourier_eq hk hK) y).symm
  have hcχ : Continuous fun p : E d × E d => eF (-p.2) p.1 := by
    unfold eF
    fun_prop
  have hint_r : Integrable (fun p : E d × E d => g p.1 * (eF (-p.2) p.1 * 𝓕 k p.2))
      (volume.prod volume) := by
    have hprod : Integrable (fun p : E d × E d => g p.1 * 𝓕 k p.2) (volume.prod volume) := by
      exact hg.mul_prod hK
    refine hprod.mono ?_ (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    · first
      | exact hg.1.fst.mul (hcχ.aestronglyMeasurable.mul hK.1.snd)
      | exact hg.1.comp_fst.mul (hcχ.aestronglyMeasurable.mul hK.1.comp_snd)
    · try dsimp only
      rw [norm_mul, norm_mul, norm_mul, norm_eF_eq_one, one_mul]
  calc ∫ y, g y * k y = ∫ y, ∫ η, g y * (eF (-η) y * 𝓕 k η) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        try dsimp only
        rw [integral_const_mul, ← hinv y]
    _ = ∫ η, ∫ y, g y * (eF (-η) y * 𝓕 k η) := integral_integral_swap hint_r
    _ = ∫ η, 𝓕 k η * 𝓕 g (-η) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        try dsimp only
        rw [fourier_eq_integral_eF_mul g (-η), ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        try dsimp only
        ring
    _ = ∫ η, 𝓕 k (-η) * 𝓕 g η := by
        exact ((integral_neg_eq_self (fun η => 𝓕 k η * 𝓕 g (-η)) volume).symm).trans (by simp only [neg_neg])
end ZetaZeros.D.EllReg
