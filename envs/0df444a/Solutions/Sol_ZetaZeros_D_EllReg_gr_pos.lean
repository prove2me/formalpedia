-- Prove2me | solution 1 for ZetaZeros.D.EllReg.gr_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:00:26.438228+00:00
-- url     : https://prove2.me/submissions/97f42c17-a2d6-42f4-9e82-bd4adad84312

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernGr

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
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (k : ℕ) (hk0 : 0 < k) (M : ℝ)
    (hM : ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ M) (x0 y : E d) (r : ℝ) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ k (fun y => b (x0 + r • y) - b x0) y‖ ≤ M * r ^ k := by
  have hk : k ≠ 0 := hk0.ne'
  have hkle : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by exact_mod_cast (ENat.natCast_lt_top k).le
  obtain ⟨g, hg⟩ : ∃ g : E d →L[ℝ] E d, g = r • ContinuousLinearMap.id ℝ (E d) := ⟨_, rfl⟩
  have hshift : ContDiff ℝ ∞ (fun z => b (x0 + z)) := hb.comp (contDiff_const.add contDiff_id)
  have hfun : (fun y => b (x0 + r • y) - b x0) = ((fun z => b (x0 + z)) ∘ g) - fun _ => b x0 := by
    funext y; simp [hg]
  rw [hfun, iteratedFDeriv_sub_apply (((hshift.comp g.contDiff).of_le hkle).contDiffAt)
    contDiffAt_const, iteratedFDeriv_const_of_ne hk, Pi.zero_apply, sub_zero,
    g.iteratedFDeriv_comp_right hshift y hkle, iteratedFDeriv_comp_add_left]
  have hgn : ‖g‖ ≤ r := by
    rw [hg]
    refine (norm_smul_le r _).trans ?_
    rw [Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le ContinuousLinearMap.norm_id_le
  calc _ ≤ ‖iteratedFDeriv ℝ k b (x0 + g y)‖ * ∏ _i : Fin k, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ M * r ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (hM _) (pow_le_pow_left₀ (norm_nonneg _) hgn k) (by positivity)
        ((norm_nonneg _).trans (hM 0))
end ZetaZeros.D.EllReg
