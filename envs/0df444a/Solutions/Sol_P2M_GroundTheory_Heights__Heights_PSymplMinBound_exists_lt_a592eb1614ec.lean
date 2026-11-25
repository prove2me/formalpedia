-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplMinBound_exists_lt_a592eb1614ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:21.34295+00:00
-- url     : https://prove2.me/submissions/f3fea3ae-bbe1-43fb-8a77-b232bd9a88ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinBound_prod_sqrt_eq_one_c058a3ee7a59

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplMinBound
namespace GroundTheory.Heights₂.Heights.PSymplMinBound
theorem _root_.solution (h2 : SymplMinkowskiBox.Statement) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (O : Matrix ι ι ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (hO : |O.det| = 1)
    (hprod : ∏ i, lam i = 1) (c : ℝ) (hc : 1 < c) :
    ∃ v : ι → ℤ, v ≠ 0 ∧
      ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < (Fintype.card ι : ℝ) * c ^ 2 := by
  have hc0 : 0 < c := by linarith
  have ha : ∀ i, 0 < c / Real.sqrt (lam i) := fun i => div_pos hc0 (Real.sqrt_pos.2 (hlam i))
  have hpa : 1 < ∏ i, c / Real.sqrt (lam i) := by
    rw [Finset.prod_div_distrib, prod_sqrt_eq_one lam hlam hprod, div_one, Finset.prod_const,
      Finset.card_univ]
    exact one_lt_pow₀ hc Fintype.card_ne_zero
  obtain ⟨v, hv, hbox⟩ := h2 ι O (fun i => c / Real.sqrt (lam i)) hO ha hpa
  refine ⟨v, hv, ?_⟩
  have hlt : ∀ i ∈ (Finset.univ : Finset ι), lam i * (O *ᵥ intVec v) i ^ 2 < c ^ 2 := by
    intro i _
    have hs := Real.sqrt_pos.2 (hlam i)
    have h1 : |(O *ᵥ intVec v) i| * Real.sqrt (lam i) < c := (lt_div_iff₀ hs).1 (hbox i)
    have h2' : (|(O *ᵥ intVec v) i| * Real.sqrt (lam i)) ^ 2 < c ^ 2 :=
      pow_lt_pow_left₀ h1 (mul_nonneg (abs_nonneg _) hs.le) two_ne_zero
    rw [mul_pow, sq_abs, Real.sq_sqrt (hlam i).le] at h2'
    linarith
  calc ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < ∑ _i : ι, c ^ 2 :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
    _ = (Fintype.card ι : ℝ) * c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end GroundTheory.Heights₂.Heights.PSymplMinBound
