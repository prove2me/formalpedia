-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.fib_image_mulTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:09.533566+00:00
-- url     : https://prove2.me/submissions/9c82ce12-b543-40f1-906b-2de694846901

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_fib_map_mulTup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (hJ : ∀ i j, σ (J j i) = J i j) {n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R] [SecondCountableTopology (HermR R σ n)]
include hJ
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀)
    (A : Set (Fin n → Fin M → R ⊗[F] E)) :
    ((cTup (M := M) R D : ℝ≥0∞) * (cHerm σ hσ R D : ℝ≥0∞)) *
      fib S₀ (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) '' A) = fib S₀ A := by
  have hmap := fib_map_mulTup (hJ := hJ) (hG := hG) (hU := hU) (hL := hL) (hfib := hfib) (hS₀ := hS₀)
  have inj : Function.Injective (tupEquiv (M := M) D) := (tupEquiv (M := M) D).injective
  have e1 := MeasurableEquiv.map_apply (μ := fib S₀)
    ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv) ((tupEquiv (M := M) D) '' A)
  have e2 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) ⁻¹'
      ((tupEquiv (M := M) D) '' A) = A := Set.preimage_image_eq A inj
  rw [e2] at e1
  have e3 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) =
      mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  have e4 : ((tupEquiv (M := M) D) : _ → _) = mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  rw [e3, e4, hmap, Measure.smul_apply, smul_eq_mul] at e1
  exact e1
end PI.DegenerateSiegelWeil.Scale
