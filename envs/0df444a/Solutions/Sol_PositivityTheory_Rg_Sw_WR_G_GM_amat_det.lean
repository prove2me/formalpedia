-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.amat_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:26.528661+00:00
-- url     : https://prove2.me/submissions/4541839b-dfee-454d-bc0a-6dc395644067

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_det_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_amat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : c ≠ 0) (s : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) :
    (Real.pi : ℂ) ^ n / (Amat ε c (s * c) b a).det = ((Real.pi : ℂ) / c) ^ n * ((Mm ε s b a)⁻¹).det := by
  have hM := det_ne_zero hb (s * sR ε a)
  rw [amat_eq, det_smul, det_transpose, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv']
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold Mm at hM ⊢
  rw [div_pow]
  field_simp
end PositivityTheory.Rg.Sw.WR.G.GM
