-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_smul_f065e44fd581
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:48.548184+00:00
-- url     : https://prove2.me/submissions/1415faac-cdb2-4274-8c6b-f34a12e8b3c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_monomial_smul_mem_50a714013970
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_apply_c807c9273bfc

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
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
open Classical
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
theorem _root_.solution (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece] {c : K → ℤ}
    {x : M} (hx : x ∈ piece c) (s : MRing ι F) (m : K → ℤ) :
    comp (piece := piece) m (s • x) =
      (∑ d ∈ s.support with (fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) = m - c,
        monomial d (coeff d s)) • x := by
  conv_lhs => rw [s.as_sum]
  rw [Finset.sum_smul, map_sum, Finset.sum_filter, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := monomial_smul_mem hM d (coeff d s) hx
  rw [comp_apply]
  split_ifs with hd
  · rw [hd, add_sub_cancel] at h
    exact DirectSum.decompose_of_mem_same piece h
  · rw [zero_smul]
    refine DirectSum.decompose_of_mem_ne piece h fun h' => hd ?_
    rw [← h', add_sub_cancel_left]
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
