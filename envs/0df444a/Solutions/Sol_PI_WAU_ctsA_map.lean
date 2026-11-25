-- Prove2me | solution 1 for PI.WAU.ctsA_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:19:24.48127+00:00
-- url     : https://prove2.me/submissions/927b3eda-0b81-493e-93fc-c2a9348f5ffb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Theorems.Thm_PI_WAU_coord_map
import Theorems.Thm_PI_WAU_cont_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
variable [TopologicalSpace B] [IsTopologicalRing B]
variable {b}
variable {X : Type*} [TopologicalSpace X]
namespace PI.WAU
theorem _root_.solution (σ : E →ₐ[F] E) {f : X → E ⊗[F] B} (hf : CtsA b f) :
    CtsA b (fun x => Algebra.TensorProduct.map σ (AlgHom.id F B) (f x)) := by
  unfold CtsA
  simp only [coord_map]
  exact continuous_pi fun k => continuous_finset_sum _ fun i _ => cont_smul _ ((continuous_apply i).comp hf)
end PI.WAU
