-- Prove2me | solution 1 for PI.IsoInvMetricW.gen_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:49.991404+00:00
-- url     : https://prove2.me/submissions/9bc491d8-48ee-4527-b451-e183d8810717

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
import Theorems.Thm_PI_IsoInvMetricW_hv_scalar
import Theorems.Thm_PI_IsoInvMetricW_hvCols_of
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
namespace PI.IsoInvMetricW
theorem _root_.solution (hQ : QR) (hM : HvMap) : Gen := by
  intro Lt _ _ N nu x
  have hq := fun s => hQ N (Matrix.of fun a (j : Fin N) => x s a j)
  choose k hk htri using hq
  refine ⟨k, hk, ?_⟩
  let y := fr (fun s => star (k s)) x
  have hxy : x = fr k y := by
    funext s a j
    have hkk : k s * star (k s) = 1 := Matrix.mem_unitaryGroup_iff.mp (hk s)
    show x s a j = ∑ b, k s a b * ∑ c, star (k s) b c * x s c j
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have : ∀ c, ∑ b, k s a b * star (k s) b c = if a = c then 1 else 0 := fun c => by
      rw [← Matrix.one_apply, ← hkk, Matrix.mul_apply]
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have ytri : ∀ s (a : Fin N) (j : ℕ), j < a → y s a j = 0 := by
    intro s a j hja
    have hjN : j < N := lt_trans hja a.2
    have := htri s a ⟨j, hjN⟩ (Fin.lt_def.mpr hja)
    simpa [y, fr, Matrix.mul_apply] using this
  refine ⟨∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg y s i, ?_⟩
  rw [hxy, ← hM Lt N nu k y, hv_scalar nu y ytri, vnuMap_smul, ← hvCols_of hM Lt N nu k]
end PI.IsoInvMetricW
