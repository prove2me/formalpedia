-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.compSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:14.323215+00:00
-- url     : https://prove2.me/submissions/f771f1e2-7250-42b0-b6a3-28451af95ddb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_sum_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inr_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inr_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_k2
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_dvE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_decomp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_good_mul_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_good_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_good_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution : CompSt := by
  intro m n ε u v d₁ d₂ hu hv hue hve
  classical
  have key : ∀ t ∈ v.support, ∃ r, Good ε (d₁ + d₂) r ∧
      ∀ f, op u (opMono t f) = op (u * monomial t 1) f + op r f := by
    intro t ht
    have hγ : ∀ k ∈ (t.comapDomain Sum.inl Sum.inl_injective.injOn).support, inF1 ε k := by
      intro k hk
      apply hv t ht k
      left
      simpa [Finsupp.comapDomain_apply] using hk
    obtain ⟨r, hr, e⟩ := k2 _ hγ d₁ u hu hue
    have hs : ∀ k, (((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ)
        (Sum.inl k) ≠ 0 ∨ ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
          Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inr_inl, mapDomain_inr_inr] at hk
      apply hv t ht k
      right
      simpa [Finsupp.comapDomain_apply] using hk
    have he : (∑ k, ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
        Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ d₂ := by
      simp only [mapDomain_inr_inr, Finsupp.comapDomain_apply]
      exact hve t ht
    refine ⟨r * monomial ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr) 1,
      good_mul_monomial hr _ hs he, fun f => ?_⟩
    rw [opMono_eq, e]
    have hδ : (fun k : Ix m n => t (Sum.inr k)) =
        fun k => (t.comapDomain Sum.inr Sum.inr_injective.injOn) k := by
      ext k; simp [Finsupp.comapDomain_apply]
    rw [hδ, op_dvE, op_dvE, mul_assoc, monomial_mul, mul_one, decomp]
  choose! R hR using key
  refine ⟨∑ t ∈ v.support, coeff t v • R t, ?_, ?_, fun f => ?_⟩
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).1
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).2
  · rw [show op v f = ∑ t ∈ v.support, coeff t v • opMono t f from rfl, op_sum_f]
    have huv : u * v = ∑ t ∈ v.support, coeff t v • (u * monomial t 1) := by
      conv_lhs => rw [v.as_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    rw [huv, op_sum, op_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(hR t ht).2, op_smul, op_smul, smul_add]
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
