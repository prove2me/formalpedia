-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.Bf_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:05.116623+00:00
-- url     : https://prove2.me/submissions/856fc15f-05ac-42ac-9f5d-b1312da391d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {A : Type} [CommRing A] [Algebra F A]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (g : HA A σ J) (u v : Fin M → A ⊗[F] E) :
    Bf σ J (lin A σ J g u) (lin A σ J g v) = Bf σ J u v := by
  have hf : ∀ x y : Fin M → A ⊗[F] E, hR A σ J x y =
      dotProduct (Matrix.vecMul (fun i => sigR A σ (x i)) (JR A J)) y := by
    intro x y
    simp only [hR, Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
    exact Finset.sum_comm
  have hs : ∀ (P : Matrix (Fin M) (Fin M) (A ⊗[F] E)) (x : Fin M → A ⊗[F] E),
      (fun i => sigR A σ (P.mulVec x i)) =
        Matrix.vecMul (fun i => sigR A σ (x i)) (Formalism.UG.cT (sigR A σ) P) := by
    intro P x
    funext j
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, _root_.map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hg : (HA.mat A σ J g) ∈ HR A σ J := (show ↥(HR A σ J) from g).2
  have hg' : Formalism.UG.cT (sigR A σ) ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) * JR A J *
      ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) = JR A J := hg
  unfold Bf lin
  congr 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hf, hf, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']
end PI.VolSemiDirect.W.Cj
