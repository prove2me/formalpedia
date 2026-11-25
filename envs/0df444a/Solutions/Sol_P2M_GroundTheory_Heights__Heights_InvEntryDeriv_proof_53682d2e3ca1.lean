-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvEntryDeriv_proof_53682d2e3ca1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:08.62501+00:00
-- url     : https://prove2.me/submissions/e55ee2d8-f546-4bd7-9a07-b01b3b3c2009

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_det_6cbb36123359
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_inv_entry_edb20586853c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43


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
open Matrix Topology
namespace GroundTheory.Heights₂.Heights
namespace InvEntryDeriv
theorem _root_.solution (h₁ : InvEntryBound.Statement) : InvEntryDeriv.Statement := by
  intro E _ _ g Y p c b hc hpsd hY
  have hpd : (Y p).PosDef := MCBounds.posDef_of_ge hc hpsd
  have hdet : (Y p).det ≠ 0 := hpd.det_pos.ne'
  have hYd : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p := fun j l => (hY j l).1
  have hZd := MCInvEntryDeriv.differentiableAt_inv_entry hYd hdet
  have hnear : ∀ᶠ q in 𝓝 p, (Y q).det ≠ 0 :=
    (MCInvEntryDeriv.differentiableAt_det hYd).continuousAt.eventually_ne hdet

  have key : ∀ j m, ∑ s, Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p =
      -∑ s, (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p := by
    intro j m
    have hconst : (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) =ᶠ[𝓝 p]
        fun _ => (1 : Matrix (Fin g) (Fin g) ℝ) j m := by
      filter_upwards [hnear] with q hq
      rw [← mul_apply, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hq)]
    have h1 : fderiv ℝ (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) p =
        ∑ s, (Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p +
          (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p) := by
      rw [fderiv_fun_sum (u := Finset.univ) (A := fun s q => Y q j s * (Y q)⁻¹ s m)
        (fun s _ => (hYd j s).mul (hZd s m))]
      exact Finset.sum_congr rfl fun s _ => fderiv_fun_mul (hYd j s) (hZd s m)
    rw [hconst.fderiv_eq, fderiv_const_apply, Finset.sum_add_distrib] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  have form : ∀ j l, fderiv ℝ (fun q => (Y q)⁻¹ j l) p =
      -∑ m, ∑ s, ((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p := by
    intro j l
    have hZY : (Y p)⁻¹ * Y p = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
    calc fderiv ℝ (fun q => (Y q)⁻¹ j l) p
        = ∑ s, ((Y p)⁻¹ * Y p) j s • fderiv ℝ (fun q => (Y q)⁻¹ s l) p := by
          rw [hZY]; simp [one_apply]
      _ = ∑ m, (Y p)⁻¹ j m • ∑ s, Y p m s • fderiv ℝ (fun q => (Y q)⁻¹ s l) p := by
          simp only [mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          simp only [key, smul_neg, Finset.smul_sum, smul_smul, Finset.sum_neg_distrib]
  intro j l
  refine ⟨hZd j l, ?_⟩
  rw [form, norm_neg]
  have hinv := h₁ g (Y p) c hc hpsd
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  calc ‖∑ m, ∑ s, ((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p‖
      ≤ ∑ m, ∑ s, ‖((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
    _ ≤ ∑ _m : Fin g, ∑ _s : Fin g, c⁻¹ * c⁻¹ * b := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun s _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (mul_le_mul (hinv j m) (hinv s l) (abs_nonneg _) hci) (hY m s).2
          (norm_nonneg _) (mul_nonneg hci hci)
    _ = (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
end InvEntryDeriv
end GroundTheory.Heights₂.Heights
