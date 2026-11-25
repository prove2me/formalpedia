-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_eq_of_span_eq_a780c4a08928
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:32.463214+00:00
-- url     : https://prove2.me/submissions/22758341-be91-4439-b1c7-9ae4f8c5e446

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_gram_comb_ddeda5d33b52

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
omit [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {n : ℕ} {b b' : Fin n → W} (hb : LinearIndependent ℤ b)
    (h : span ℤ (Set.range b) = span ℤ (Set.range b')) : (gram ℝ b).det = (gram ℝ b').det := by
  have hP : ∀ i, ∃ c : Fin n → ℤ, ∑ j, c j • b' j = b i := fun i =>
    (mem_span_range_iff_exists_fun ℤ).1 (h ▸ subset_span ⟨i, rfl⟩)
  have hQ : ∀ i, ∃ c : Fin n → ℤ, ∑ j, c j • b j = b' i := fun i =>
    (mem_span_range_iff_exists_fun ℤ).1 (h.symm ▸ subset_span ⟨i, rfl⟩)
  choose P hP using hP
  choose Q hQ using hQ
  have hPQ : (Matrix.of P) * (Matrix.of Q) = 1 := by
    ext i l
    have key : ∑ l, ((Matrix.of P * Matrix.of Q) i l - (1 : Matrix (Fin n) (Fin n) ℤ) i l) • b l
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_apply, of_apply, Finset.sum_smul,
        mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hQ, hP]
      simp [one_apply]
    have := Fintype.linearIndependent_iff.1 hb _ key l
    exact sub_eq_zero.1 this
  have hdet : (Matrix.of P).det = 1 ∨ (Matrix.of P).det = -1 := by
    have := congrArg Matrix.det hPQ
    rw [det_mul, det_one] at this
    exact Int.eq_one_or_neg_one_of_mul_eq_one this
  have hb_eq : b = fun i => ∑ j, ((Matrix.of P).map (Int.cast : ℤ → ℝ)) i j • b' j := by
    funext i
    rw [← hP i]
    simp [Int.cast_smul_eq_zsmul]
  rw [hb_eq, gram_comb, det_mul, det_mul, det_transpose]
  have : ((Matrix.of P).map (Int.cast : ℤ → ℝ)).det = ((Matrix.of P).det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) _).symm
  rw [this]
  rcases hdet with h1 | h1 <;> rw [h1] <;> push_cast <;> ring
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
