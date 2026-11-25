-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_decompose_smul_4dfe6150b6e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:59.348195+00:00
-- url     : https://prove2.me/submissions/9d79cf20-e7e3-4f0d-b648-40bc672fe8af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_homog_smul_mem_798312d8528d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution (hM : IsMultigrading ι M piece) (f : MRing ι F) {c : K → ℤ} {x : M}
    (hx : x ∈ piece c) (m : K → ℤ) :
    (DirectSum.decompose piece (f • x) m : M) =
      (∑ d ∈ f.support with c + degZ (Finsupp.weight (blockWeight ι) d) = m,
        monomial d (coeff d f)) • x := by
  have ef := f.as_sum
  conv_lhs => rw [ef]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
    AddSubmonoidClass.coe_finsetSum, Finset.sum_filter, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hd : (monomial d (coeff d f) : MRing ι F) • x ∈
      piece (c + degZ (Finsupp.weight (blockWeight ι) d)) :=
    homog_smul_mem hM (isWeightedHomogeneous_monomial _ _ _ rfl) hx
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same piece hd
  · rw [zero_smul]; exact DirectSum.decompose_of_mem_ne piece hd h
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
