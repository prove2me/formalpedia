-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.fib_map_mulTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:14.484446+00:00
-- url     : https://prove2.me/submissions/a33fd8e4-d65b-4077-ae8c-61aed51b9563

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_map_eq_smul
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_fib_map_fixed
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_gramH_mulTup_of
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_preimage_linIndep
import Theorems.Thm_PI_VolStabSW_TensAllW_isOpen_linIndep
import Theorems.Thm_PI_VolStabSW_continuous_gramH


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
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀) :
    (fib S₀).map (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ((cTup (M := M) R D : ℝ≥0∞) *
        (cHerm σ hσ R D : ℝ≥0∞)) • fib S₀ := by
  let e := tupEquiv (M := M) D
  let h := hermEquiv R σ hσ D
  have hμ : μ.map e.toHomeomorph = (cTup (M := M) R D : ℝ≥0∞) • μ :=
    map_eq_smul μ e
  have hν : ν.map h.toHomeomorph.symm = (cHerm σ hσ R D : ℝ≥0∞) • ν := by
    have := map_eq_smul ν h.symm
    rw [addEquivAddHaarChar_symm, inv_inv] at this
    exact this
  have := fib_map_fixed e.toHomeomorph h.toHomeomorph (f' := gramH R σ hσ J hJ)
    (continuous_gramH R σ hσ J hJ) (fun _ => rfl) Subtype.val_injective
    (isOpen_linIndep (Module.finBasis F E) R hU hL)
    (fun X => gramH_mulTup_of hG R σ hσ J hJ _ X) (preimage_linIndep D) ENNReal.coe_ne_top
    ENNReal.coe_ne_top hμ hν hfib S₀ hS₀
  exact this
end PI.DegenerateSiegelWeil.Scale
