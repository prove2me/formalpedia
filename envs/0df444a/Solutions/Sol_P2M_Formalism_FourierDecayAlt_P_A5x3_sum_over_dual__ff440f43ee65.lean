-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_A5x3_sum_over_dual__ff440f43ee65
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:04.154171+00:00
-- url     : https://prove2.me/submissions/195c661d-34b6-4bf3-8a08-750331ec2382

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_sum_over_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable {C : Type} [AddCommGroup C] [Module R C]
open Classical
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) [Finite C]
    (hsep : ∀ c : C, (∀ α : C →ₗ[R] KR R, α c = 0) → c = 0) (x : C) :
    ∑ᶠ α : C →ₗ[R] KR R, psiKR R ψ (α x) =
      if x = 0 then (Nat.card (C →ₗ[R] KR R) : ℂ) else 0 := by
  have h1 := sum_over_S h (⊤ : Submodule R (C →ₗ[R] KR R)) x
  have h2 : ∑ᶠ α : (⊤ : Submodule R (C →ₗ[R] KR R)), psiKR R ψ ((α : C →ₗ[R] KR R) x) =
      ∑ᶠ α : C →ₗ[R] KR R, psiKR R ψ (α x) :=
    finsum_comp_equiv (Submodule.topEquiv (R := R) (M := C →ₗ[R] KR R)).toEquiv
      (f := fun α : C →ₗ[R] KR R => psiKR R ψ (α x))
  rw [← h2, h1, Nat.card_congr (Submodule.topEquiv (R := R) (M := C →ₗ[R] KR R)).toEquiv]
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos]
    intro α _
    rw [hx, map_zero]
  · rw [if_neg hx, if_neg]
    intro hcon
    exact hx (hsep x fun α => hcon α Submodule.mem_top)
end Formalism.FourierDecayAlt.P.A5x3
