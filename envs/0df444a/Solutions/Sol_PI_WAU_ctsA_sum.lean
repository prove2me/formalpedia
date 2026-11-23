-- Prove2me | solution 1 for PI.WAU.ctsA_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:03.406366+00:00
-- url     : https://prove2.me/submissions/49028375-2bcf-47ad-b94e-68668502eb90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul

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
theorem _root_.solution {κ : Type*} (s : Finset κ) {f : κ → X → E ⊗[F] B} (hf : ∀ i ∈ s, CtsA b (f i)) :
    CtsA b (fun x => ∑ i ∈ s, f i x) := by
  unfold CtsA
  simp only [map_sum]
  exact continuous_finset_sum _ hf
end PI.WAU
