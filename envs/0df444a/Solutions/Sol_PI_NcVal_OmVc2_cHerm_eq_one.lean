-- Prove2me | solution 1 for PI.NcVal.OmVc2.cHerm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:25.204625+00:00
-- url     : https://prove2.me/submissions/52ccd557-c904-47c8-8381-d7f96edbecba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal
import Theorems.Thm_PI_NcVal_OmVc2_char_eq_one
import Theorems.Thm_PI_NcVal_OmVc2_conjT_diagonal

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
theorem _root_.solution [SecondCountableTopology (HermR R σ n)] (d : Fin n → (R ⊗[F] E)ˣ)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i) (hd : ∀ i, d (π i) = (d i)⁻¹) :
    cHerm σ hσ R (diagUnit d) = 1 := by
  rw [cHerm, char_eq_one (hermEquiv R σ hσ (diagUnit d)) (permHerm σ R π) ?_ ?_]
  · intro S
    apply Subtype.ext
    ext i j
    show (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (π (π i)) (π (π j)) = _
    rw [hπ, hπ]
  · intro S
    apply Subtype.ext
    ext i j
    show (conjT R σ (Matrix.diagonal fun i => (d i : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π *
          Matrix.diagonal fun i => (d i : R ⊗[F] E)) (π i) (π j) =
      (conjT R σ (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) *
          Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) i j
    rw [conjT_diagonal, conjT_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [hπ, hd]
end PI.NcVal.OmVc2
