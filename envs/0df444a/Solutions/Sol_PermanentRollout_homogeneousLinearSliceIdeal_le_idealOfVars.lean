-- Prove2me | solution 1 for PermanentRollout.homogeneousLinearSliceIdeal_le_idealOfVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/7aaafab6-6bf5-4e6f-9648-9fe712bb154b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousIdeal_le_idealOfVars_of_ne_top

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {t n : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hproper : I ≠ ⊤) (c : Fin n → Fin t → ℂ) :
    homogeneousLinearSliceIdeal I c ≤
      MvPolynomial.idealOfVars (Fin t) ℂ := by
  unfold homogeneousLinearSliceIdeal
  apply sup_le
  · exact homogeneousIdeal_le_idealOfVars_of_ne_top I hI hproper
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    change (∑ i, c j i • MvPolynomial.X i) ∈
      (MvPolynomial.idealOfVars (Fin t) ℂ).restrictScalars ℂ
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Ideal.subset_span ⟨i, rfl⟩
end PermanentRollout
