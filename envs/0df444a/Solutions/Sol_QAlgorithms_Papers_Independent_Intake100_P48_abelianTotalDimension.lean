-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P48.abelianTotalDimension
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:55:08.201401+00:00
-- url     : https://prove2.me/submissions/4427de4b-6dd1-4b19-8746-4ae9bcbd3839

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P48

noncomputable section

open Filter

open scoped Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Intake100.P48 in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (dim : A → ℝ)
    (habelian : ∀ a, dim a = 1) :
    totalDimension dim ^ 2 = (Fintype.card A : ℝ) := by
  unfold totalDimension
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg (dim a)))]
  simp [habelian]

end
