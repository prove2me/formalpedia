-- Prove2me | solution 1 for PI.VolStabW.TopoFibInv.linIndep_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:21.148593+00:00
-- url     : https://prove2.me/submissions/71efb724-8044-4f34-991e-937c0e8549a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoFibInv
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.TopoFibInv
theorem _root_.solution {A : Type} [CommRing A] (G : GL (Fin M) A) (X : Fin a → Fin M → A) :
    LinearIndependent A (fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) ↔ LinearIndependent A X := by
  have inj : ∀ H : GL (Fin M) A, LinearMap.ker (mulVecLin (H : Matrix (Fin M) (Fin M) A)) = ⊥ :=
    fun H => by
      refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
      have := congrArg (fun z => ((H⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) *ᵥ z) hxy
      simpa [mulVecLin_apply, mulVec_mulVec] using this
  constructor
  · intro hl
    have h2 := hl.map' (mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) (inj G⁻¹)
    have e : (⇑(mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) ∘
        fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) = X := by
      funext x
      simp [mulVec_mulVec]
    rw [e] at h2
    exact h2
  · intro hl
    exact hl.map' (mulVecLin (G : Matrix (Fin M) (Fin M) A)) (inj G)
end PI.VolStabW.TopoFibInv
