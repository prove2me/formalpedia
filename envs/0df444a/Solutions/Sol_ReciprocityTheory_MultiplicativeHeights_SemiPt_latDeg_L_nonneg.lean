-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.latDeg_L_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:44.640278+00:00
-- url     : https://prove2.me/submissions/9e9d2371-a56a-4b4f-97ed-b52f7e196296

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gram_det_majorant
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_spanIdx_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_sum_log_norm_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution (hS : SelfDualIndexStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (M : Majorant S) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : IsLattice L) (hSD : IsSelfDual S L) (hG : S.G.det ≠ 0) (b : Fin r → Fin r → K)
    (hb : IsKBasisIn L b) : 0 ≤ latDeg M.H L b := by
  unfold latDeg
  rw [Finset.sum_congr rfl fun σ _ => by rw [gram_det_majorant S M hG σ b], sum_log_norm_emb]
  have h1 := hS K r S L b hL hSD hb
  have hone : 1 ≤ (spanIdx L b : ℝ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero L b hL.1 hb))
  have hlog1 := Real.log_nonneg hone
  by_cases hN0 : |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| = 0
  · rw [hN0, Real.log_zero]
    unfold spanIdx at hlog1
    linarith
  · have h2 := Real.log_le_log (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hN0)) h1
    rw [Real.log_pow] at h2
    unfold spanIdx at h2
    push_cast at h2
    linarith
end ReciprocityTheory.MultiplicativeHeights.SemiPt
