-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_form_smul_mem_50a6c960c889
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:36.196049+00:00
-- url     : https://prove2.me/submissions/a4ddb9e2-1412-4ef5-b12e-a149674b97ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_monomial_smul_mem_50a714013970

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
theorem _root_.solution (hM : IsMultigrading ι M piece) {b : K → ℕ} {f : MRing ι F}
    (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) b) {m : K → ℤ} {y : M}
    (hy : y ∈ piece m) : f • y ∈ piece (m + fun k => (b k : ℤ)) := by
  rw [f.as_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight (blockWeight ι) d = b :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hd)
  have h := monomial_smul_mem hM d (coeff d f) hy
  rwa [hw] at h
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
