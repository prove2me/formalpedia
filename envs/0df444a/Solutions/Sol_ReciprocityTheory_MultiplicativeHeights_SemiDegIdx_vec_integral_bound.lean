-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.vec_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:10.086364+00:00
-- url     : https://prove2.me/submissions/cb5828d3-acd7-437b-af6b-775b5fc91189

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_split_norm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors Pointwise
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (X : Submodule (𝓞 K) (Fin k → K)) (hfg : X.FG) (hstd : intVec K k ≤ X)
    (hint : IsIntegralOn S X) (hG : S.G.det ≠ 0) :
    (vecIdx X : ℚ) ^ 2 ≤ |Algebra.norm ℚ S.G.det| := by
  obtain ⟨J, hJ1, -, hJ⟩ := split_norm S X hfg hstd hint
  have hN : (0 : ℚ) < |Algebra.norm ℚ S.G.det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hG)
  have hpos : (0 : ℚ) < FractionalIdeal.absNorm J * (vecIdx X : ℚ) ^ 2 := by
    rw [hJ]; exact hN
  obtain ⟨I, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  rw [FractionalIdeal.coeIdeal_absNorm] at hJ hpos
  have hI : Ideal.absNorm I ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have h1 : (1 : ℚ) ≤ (Ideal.absNorm I : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hI
  have hv : (0 : ℚ) ≤ (vecIdx X : ℚ) ^ 2 := by positivity
  rw [← hJ]
  nlinarith
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
