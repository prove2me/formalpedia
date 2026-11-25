-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.projD_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:07.423792+00:00
-- url     : https://prove2.me/submissions/d3d8ffe6-cc10-4aec-b282-8b54e46e7e23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.ExC
theorem _root_.solution {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) (c : R ⊗[F] E)
    (y : Fin n → R ⊗[F] E) :
    projD R σ J Y D s (c • y) = c • projD R σ J Y D s y := by
  unfold projD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [dotProduct_smul, smul_eq_mul, mul_smul]
  · rw [zero_smul, smul_zero]
end PI.LevelKSplit.W.ExC
