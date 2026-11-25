-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.homog_coeff_isMH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:36:41.581196+00:00
-- url     : https://prove2.me/submissions/6b8a51d3-d5e7-4ba8-af9d-66a559b51252

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_isMH_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_isMH_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_isMH_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_isMH_mul_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_castAdd_ne_natAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    ∀ γ : Fin (N + 1 + D) →₀ ℕ,
    IsMultiHomogeneous (fun i => γ (Fin.natAdd (N + 1) i)) (coeff γ (homog q)) := by
  classical
  induction q using MvPolynomial.induction_on
  · rename_i a
    intro γ
    rw [show homog (C a) = C (C a) from by simp [homog, MvPolynomial.algebraMap_eq], coeff_C]
    split_ifs with h
    · subst h
      intro s hs b
      simpa using isMH_C (B := D) (n := N + 1) a s hs b
    · exact isMH_zero _
  · rename_i p q hp hq
    intro γ
    rw [map_add, coeff_add]; exact isMH_add (hp γ) (hq γ)
  · rename_i p v hp
    intro γ
    obtain ⟨i, j⟩ := v
    rw [map_mul, show homog (X (i, j)) = hImg (K := K) (i, j) from aeval_X _ _]
    cases i using Fin.cases with
    | zero =>
      rw [hImg_zero, coeff_mul_X']
      split_ifs with h
      · have := hp (γ - Finsupp.single (Fin.castAdd D j) 1)
        convert this using 2 with b
        simp [castAdd_ne_natAdd j b]
      · exact isMH_zero _
    | succ i =>
      rw [hImg_succ, ← mul_assoc, mul_comm _ (C (X (i, j))), coeff_C_mul, coeff_mul_X']
      split_ifs with h
      · rw [mul_comm]
        have := isMH_mul_X (hp (γ - Finsupp.single (Fin.natAdd (N + 1) i) 1)) i j
        convert this using 1
        funext b
        have hpos : 1 ≤ γ (Fin.natAdd (N + 1) i) := by
          rw [Finsupp.mem_support_iff] at h; omega
        by_cases hb : b = i
        · subst hb; simp [Finsupp.single_apply]; omega
        · simp [Finsupp.single_apply, Pi.single_apply, hb, Ne.symm hb]
      · rw [mul_zero]; exact isMH_zero _
end ReciprocityTheory.ChartRestriction.G.T0.NPB
