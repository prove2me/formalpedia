-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFinite_linePoly_natDegree_coeff_9c7308ab0736
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:23.085144+00:00
-- url     : https://prove2.me/submissions/d2661f8f-f0c2-4a9d-a924-cfe0c76a79a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFinite_natDegree_coeff_prod_pow_fd7bed4b50a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFinite_lineVar_natDegree_coeff_0f4cef3db7dd

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFinite
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartFinite
theorem _root_.solution {δ : ℕ} {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) (t : Fin n → F) (m : Fin n) :
    (linePoly f t m).natDegree ≤ δ ∧ (linePoly f t m).coeff δ = specFirst f t := by
  classical
  have hw : ∀ d ∈ f.support, ∑ ij ∈ d.support, d ij * groupWeight (e + 1) n ij 0 = δ := by
    intro d hd
    have h := congrFun (hf (mem_support_iff.mp hd)) 0
    simpa [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] using h
  have key : ∀ d ∈ f.support, (∏ ij ∈ d.support, lineVar t m ij ^ d ij).natDegree ≤ δ ∧
      (∏ ij ∈ d.support, lineVar t m ij ^ d ij).coeff δ =
        ∏ ij ∈ d.support, specFirstVar t ij ^ d ij := by
    intro d hd
    obtain ⟨h1, h2⟩ := natDegree_coeff_prod_pow d.support (lineVar t m)
      (fun ij => groupWeight (e + 1) n ij 0) d (fun ij _ => (lineVar_natDegree_coeff t m ij).1)
    rw [hw d hd] at h1 h2
    exact ⟨h1, h2.trans (Finset.prod_congr rfl fun ij _ => by rw [(lineVar_natDegree_coeff t m ij).2])⟩
  have hs : linePoly f t m = ∑ d ∈ f.support,
      Polynomial.C (C (coeff d f)) * ∏ ij ∈ d.support, lineVar t m ij ^ d ij := by
    conv_lhs => rw [linePoly, f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod]
  have hs' : specFirst f t = ∑ d ∈ f.support, C (coeff d f) * ∏ ij ∈ d.support, specFirstVar t ij ^ d ij := by
    conv_lhs => rw [specFirst, f.as_sum, map_sum]
    exact Finset.sum_congr rfl fun d _ => bind₁_monomial _ _ _
  rw [hs, hs']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd =>
    (Polynomial.natDegree_C_mul_le _ _).trans (key d hd).1, ?_⟩
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun d hd => by rw [Polynomial.coeff_C_mul, (key d hd).2]
end GroundTheory.Heights₂.Heights.ChartFinite
