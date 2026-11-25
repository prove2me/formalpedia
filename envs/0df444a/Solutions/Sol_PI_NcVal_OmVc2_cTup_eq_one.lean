-- Prove2me | solution 1 for PI.NcVal.OmVc2.cTup_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:32.479903+00:00
-- url     : https://prove2.me/submissions/76e236e9-9918-4daa-a315-acd887c83bfa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal
import Theorems.Thm_PI_NcVal_OmVc2_char_eq_one
import Theorems.Thm_PI_NcVal_OmVc2_mulTup_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc2
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R]
namespace PI.NcVal.OmVc2
theorem _root_.solution (d : Fin n → (R ⊗[F] E)ˣ) (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i)
    (hd : ∀ i, d (π i) = (d i)⁻¹) : cTup (M := M) R (diagUnit d) = 1 := by
  rw [cTup, char_eq_one (tupEquiv (M := M) (diagUnit d)) (permTup R π) ?_ ?_, inv_one]
  · intro X
    funext j
    show X (π (π j)) = X j
    rw [hπ]
  · intro X
    show (fun j => mulTup (Matrix.diagonal fun i => (d i : R ⊗[F] E)) (fun j => X (π j)) (π j)) =
      mulTup (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) X
    rw [mulTup_diagonal, mulTup_diagonal]
    funext j i
    simp [hπ, hd]
end PI.NcVal.OmVc2
