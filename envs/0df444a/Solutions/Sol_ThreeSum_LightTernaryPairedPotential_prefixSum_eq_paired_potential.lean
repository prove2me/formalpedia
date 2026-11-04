-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.prefixSum_eq_paired_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:57.402193+00:00
-- url     : https://prove2.me/submissions/6cae91c4-d3a8-40f6-8ec6-77e4c0280901

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_TernaryPairedColumnEnumeration_sum_digits_eq_sum_columns
import Theorems.Thm_ThreeSum_TernaryPairedTensor_full_potential_tensor_expansion


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution {P₀ : Type*} [Fintype P₀]
    (m base Λ : ℕ) (μ : ℕ → ℤ) (L R' : P₀ → Fin Λ → ℤ)
    (hTensor : ∀ a b c d : Fin Λ, μ (base+tensorIndex Λ a.val b.val c.val d.val)=tensor L R' a b c d) :
    prefixSum m base Λ μ (Λ^width m) =
      ((∑ e : Fin m → P₀, TernaryPairedPotential.rowWeight
        (Sum.elim (fun i => L (e i)) (fun i => R' (e i)))) : ℤ) := by
  unfold prefixSum term
  change (∑ i ∈ Finset.range (Λ^width m),
    (fun cols : PairedIndex m → ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
      (fun r => WeightEnumeration.digit Λ (width m) i (Fintype.equivFin (PairedIndex m) r).val)) = _
  have he := sum_digits_eq_sum_columns m Λ
    (fun cols : PairedIndex m → ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
  refine he.trans ?_
  have hformula := full_potential_tensor_expansion (m := m) L R'
  refine Eq.trans ?_ hformula.symm
  apply Finset.sum_congr rfl
  intro cols hcols
  unfold value
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact hTensor _ _ _ _
end ThreeSum.LightTernaryPairedPotential
