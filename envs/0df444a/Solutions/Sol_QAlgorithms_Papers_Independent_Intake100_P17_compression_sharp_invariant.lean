-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P17.compression_sharp_invariant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:23:39.608845+00:00
-- url     : https://prove2.me/submissions/87d7cd09-9ddb-49b0-872a-8ef74c040368

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Intake100.P17 in
theorem solution
    {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (tau : G ≃* G) (htau : Function.Involutive tau) (htaucont : Continuous tau)
    (r : X ≃ₜ X) (hr : Function.Involutive r)
    (hrcov : ∀ g x, r (g • r x) = tau g • x)
    (D : Set X) (hopen : IsOpen D) (hcomplement : r '' D = interior Dᶜ) :
    (∀ g ∈ compressionSet (G := G) D, ∀ h ∈ compressionSet (G := G) D,
      g * h ∈ compressionSet (G := G) D) ∧
    (∀ g ∈ compressionSet (G := G) D, (tau g)⁻¹ ∈ compressionSet (G := G) D) := by
  refine ⟨?_, ?_⟩
  · intro g hg h hh x hx
    rw [mul_smul]
    exact hg _ (hh x hx)
  · intro g hg x hx
    have hrx : r x ∈ interior Dᶜ := hcomplement ▸ Set.mem_image_of_mem r hx
    have hV : IsOpen ((fun w => g • w) ⁻¹' interior Dᶜ) :=
      isOpen_interior.preimage (continuous_const_smul g)
    have hVsub : (fun w => g • w) ⁻¹' interior Dᶜ ⊆ Dᶜ := by
      intro w hw hwD
      exact (interior_subset hw) (hg w hwD)
    have hmem : g⁻¹ • r x ∈ interior Dᶜ := by
      apply interior_maximal hVsub hV
      show g • (g⁻¹ • r x) ∈ interior Dᶜ
      rw [smul_inv_smul]
      exact hrx
    rw [← hcomplement] at hmem
    obtain ⟨y, hyD, hy⟩ := hmem
    have h1 := hrcov g⁻¹ x
    rw [← hy, hr y, map_inv] at h1
    rw [← h1]
    exact hyD

end
