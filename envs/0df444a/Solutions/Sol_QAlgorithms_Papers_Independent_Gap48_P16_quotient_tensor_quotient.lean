-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.quotient_tensor_quotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:57:54.306842+00:00
-- url     : https://prove2.me/submissions/b0aad83f-fd16-42f8-bc43-0707699f9c5f

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section TensorQuotients

variable {R M N : Type u} [CommRing R]

variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Lemma 4.8, PDF p.14, retaining the printed purity hypotheses and the canonical map. -/
theorem solution [IsNoetherianRing R] (I : Submodule R M) (J : Submodule R N)
    (hI : IsTensorInjective I.subtype N) (hJ : IsTensorInjective J.subtype M) :
    ∃ e : (M ⧸ I) ⊗[R] (N ⧸ J) ≃ₗ[R] (M ⊗[R] N) ⧸ tensorSubmoduleSum I J,
      ∀ (m : M) (n : N), e (I.mkQ m ⊗ₜ[R] J.mkQ n) =
        (tensorSubmoduleSum I J).mkQ (m ⊗ₜ[R] n) :=
  ⟨TensorProduct.quotientTensorQuotientEquiv I J, fun m n => rfl⟩

end TensorQuotients



end
