-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_psi_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:38.934449+00:00
-- url     : https://prove2.me/submissions/edfe9ab4-8b89-4378-b5ef-883bc8f239c4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (S : Set E) (hS : ∀ (o : 𝓞 E) (s : E), s ∈ S → (o : E) * s ∈ S)
    {y : Fv F v ⊗[F] E} (hy : y ∈ DiffLoc_psi v S) (o : 𝓞 E) :
    inclR (F := F) (Fv F v) (o : E) * y ∈ DiffLoc_psi v S := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rw [← map_mul]
    exact Submodule.subset_span ⟨_, hS o s hs, rfl⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx
end PI.LocFramePrimWork
