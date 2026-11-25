-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.eq_zero_of_eval_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:29:05.702037+00:00
-- url     : https://prove2.me/submissions/117e568b-a104-4312-b4a6-531bce939b2a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {B : Type} [CommRing B] [Algebra ℂ B]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
theorem _root_.solution (D : B[X]) (h : ∀ u : ℂ, D.eval (algebraMap ℂ B u) = 0) : D = 0 := by
  ext k
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff k)).1 fun φ => ?_
  let q : ℂ[X] := ∑ i ∈ Finset.range (D.natDegree + 1), monomial i (φ (D.coeff i))
  have hq : q = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 : φ (D.eval (algebraMap ℂ B u)) = 0 := by rw [h u, map_zero]
    rw [eval_eq_sum_range, map_sum] at h1
    rw [eval_zero, ← h1, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hc : q.coeff k = φ (D.coeff k) := by
    simp only [q, finsetSum_coeff, coeff_monomial]
    by_cases hk : k ∈ Finset.range (D.natDegree + 1)
    · rw [Finset.sum_ite_eq']
      simp [hk]
    · rw [Finset.sum_eq_zero]
      · have : D.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk)
        simp [this]
      · intro i hi
        rw [if_neg]
        rintro rfl
        exact hk hi
  rw [← hc, hq, coeff_zero]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
