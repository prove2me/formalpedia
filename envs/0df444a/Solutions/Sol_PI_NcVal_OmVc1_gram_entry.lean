-- Prove2me | solution 1 for PI.NcVal.OmVc1.gram_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:43.8738+00:00
-- url     : https://prove2.me/submissions/d452ccb1-ac8d-437c-ac02-0217f514e832

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_GramMulTupHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc1
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale
open scoped TensorProduct
namespace PI.NcVal.OmVc1
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) (a b : Fin n) :
    gramR R σ J (mulTup D X) a b = (conjT R σ D * gramR R σ J X * D) a b := by
  simp only [gramR, hR, Formalism.UG.hform, mulTup, conjT, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  have h1 : ∀ f : Fin M → Fin M → Fin n → Fin n → R ⊗[F] E,
      (∑ i, ∑ j, ∑ l, ∑ k, f i j l k) = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := by
    intro f
    calc _ = ∑ i, ∑ l, ∑ j, ∑ k, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, ∑ k, f i j l k := Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ k, ∑ j, f i j l k :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  refine (h1 _).trans ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.NcVal.OmVc1
