-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.gauss_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:55.071785+00:00
-- url     : https://prove2.me/submissions/58f3a9fe-da02-4579-8db5-c9436d785b2b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_herm_isHermitian
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_amat_det
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_mm_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_key

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
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (hI : IntegP) (hW : Wick) (hR : Rot) (hB : Base) : Gauss := by
  intro m n ε c t hc _ P
  have e : (t / c) * c = t := by field_simp
  obtain ⟨R, hR⟩ := key hI hW hR ε hc (t / c) P
  refine ⟨MvPolynomial.C (((Real.pi : ℂ) / c) ^ (n * m)) * R, fun y => ?_⟩
  have hy := hR y
  rw [e] at hy
  have hA : ∀ a, (Real.pi : ℂ) ^ n / (Amat ε c t (herm y) a).det =
      ((Real.pi : ℂ) / c) ^ n * (if ε a then uM ((t / c : ℝ) : ℂ) y else vM ((t / c : ℝ) : ℂ) y).det := by
    intro a
    have := GM.amat_det ε hc.ne' (t / c) (GM.herm_isHermitian y) a
    rw [e, mm_inv] at this
    exact this
  rw [hy, hB m n ε c t hc _ (GM.herm_isHermitian y)]
  simp_rw [hA]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [apply_ite Matrix.det]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  unfold cls
  simp only [neg_zero, Complex.cpow_zero, one_mul, evUV, map_mul, MvPolynomial.eval_C]
  rw [← pow_mul, mul_comm n m]
  have hf : (Finset.univ.filter fun a => ¬ ε a = true) = Finset.univ.filter fun a => ε a = false := by
    ext a; simp
  rw [hf]
  ring
end PositivityTheory.Rg.Sw.WR.G
