-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_exists_comp_eq_b7eb0fc85b9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:19.366406+00:00
-- url     : https://prove2.me/submissions/293ea8f8-966f-4b8a-a9a6-9db4574187be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution [FiniteDimensional E L] [Algebra.IsSeparable E L] [IsAlgClosed K]
    [Algebra.IsAlgebraic E K] (σ σ' : L →ₐ[E] K) : ∃ τ : K →ₐ[E] K, τ.comp σ = σ' := by
  let pb := Field.powerBasisOfFiniteOfSeparable E L
  have hy : Polynomial.aeval (σ' pb.gen) (minpoly E (σ pb.gen)) = 0 := by
    rw [minpoly.algHom_eq σ σ.injective, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (fun s => ⟨Algebra.IsIntegral.isIntegral (R := E) s, IsAlgClosed.splits _⟩) hy
  exact ⟨τ, pb.algHom_ext (by simpa using hτ)⟩
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
