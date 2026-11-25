-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.amat_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:46.696896+00:00
-- url     : https://prove2.me/submissions/3a0c4246-c303-4ea4-b6d6-ed4622ed0b77

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
    (hb : b.IsHermitian) (a : Fin m) (i j : Fin n) :
    (Amat ε c (s * c) b a)⁻¹ j i = (c : ℂ)⁻¹ * ((Mm ε s b a)⁻¹) i j := by
  have hM : IsUnit (Mm ε s b a).det := isUnit_iff_ne_zero.mpr (det_ne_zero hb _)
  have hinv : (Amat ε c (s * c) b a)⁻¹ = (c : ℂ)⁻¹ • ((Mm ε s b a)⁻¹)ᵀ := by
    rw [amat_eq]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul,
      ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, transpose_one]
  rw [hinv]; simp
end PositivityTheory.Rg.Sw.WR.G.GM
