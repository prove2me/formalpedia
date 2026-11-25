-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_homog_smul_mem_798312d8528d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:06.523888+00:00
-- url     : https://prove2.me/submissions/14588174-fbd6-4260-8274-791ea825e12e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_monomial_smul_mem_cf15e5d2941f

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution (hM : IsMultigrading ι M piece) {f : MRing ι F} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f b) {m : K → ℤ} {x : M} (hx : x ∈ piece m) :
    f • x ∈ piece (m + degZ b) := by
  have ef := f.as_sum
  rw [ef]
  rw [Finset.sum_smul]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight (blockWeight ι) d = b := hf (mem_support_iff.mp hd)
  have e : (monomial d (coeff d f) : MRing ι F) = coeff d f • monomial d (1 : F) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, smul_assoc]
  exact Submodule.smul_mem _ _ (hw ▸ monomial_smul_mem hM d m x hx)
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
