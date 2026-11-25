-- Prove2me | solution 1 for PI.VolStabW.TopoFibInv.gramR_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:58.859502+00:00
-- url     : https://prove2.me/submissions/f3acf9c0-fb1c-4a5a-9ce4-e617c457ed60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Theorems.Thm_Formalism_UG_P_hform_mulVec
import Theorems.Thm_PI_VolStabW_TopoGram_hform_mulVec


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
theorem _root_.solution (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (h • X) = gramR R σ J X := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  funext x y
  change hR R σ J (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR R σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl
end PI.VolStabW.TopoFibInv
