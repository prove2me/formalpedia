-- Prove2me | solution 1 for ThreeSum.TernaryPairedColumnEnumeration.sum_digits_eq_sum_columns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:40:28.21178+00:00
-- url     : https://prove2.me/submissions/ad13bf10-92ea-45e7-a5db-c4bf52ed9223

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Theorems.Thm_ThreeSum_TernaryPairedColumnEnumeration_equiv_symm_digit
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedColumnEnumeration
open TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.TernaryPairedColumnEnumeration
theorem _root_.solution {R : Type*} [AddCommMonoid R] (m Λ : ℕ)
    (f : (PairedIndex m → ℕ) → R) :
    (∑ i ∈ Finset.range (Λ^width m), f (fun r =>
      WeightEnumeration.digit Λ (width m) i (Fintype.equivFin (PairedIndex m) r).val)) =
      ∑ cols : PairedIndex m → Fin Λ, f (fun r => (cols r).val) := by
  rw [Finset.sum_range]
  have hh := (equiv m Λ).symm.sum_comp (fun cols : PairedIndex m → Fin Λ => f (fun r => (cols r).val))
  rw [←hh]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext r
  exact (equiv_symm_digit m Λ i r).symm
end ThreeSum.TernaryPairedColumnEnumeration
