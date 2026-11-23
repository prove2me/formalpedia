-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_span_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:40.871244+00:00
-- url     : https://prove2.me/submissions/fb6f9132-3b8e-4247-a674-ef2c5769a4ed

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
theorem _root_.solution (Q : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E))
    (hQ : ∀ (o : 𝓞 E) (y : Fv F v ⊗[F] E), y ∈ Q → inclR (F := F) (Fv F v) (o : E) * y ∈ Q)
    (T : Set E) (hT : ∀ t ∈ T, inclR (F := F) (Fv F v) t ∈ Q) :
    DiffLoc_psi v (Submodule.span (𝓞 E) T : Set E) ≤ Q := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hT x hx
  | zero => rw [SetLike.mem_coe, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [SetLike.mem_coe, map_add]; exact add_mem hx hy
  | smul o x _ hx => rw [SetLike.mem_coe, Algebra.smul_def, map_mul]; exact hQ o _ hx
end PI.LocFramePrimWork
