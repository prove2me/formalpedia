-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_bc_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:54.897389+00:00
-- url     : https://prove2.me/submissions/4d18c089-c555-4a02-bd69-b807d5a11ae8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
import Theorems.Thm_PI_LocFramePrimWork_Assemble_bc_ratV
import Theorems.Thm_PI_LocFramePrimWork_Assemble_smul_eq
import Theorems.Thm_P2M_PI_LocFramePrimWork_Assemble_smul_eq__803d2b5b4bfc

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
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution (ψ : (Fin n → E) →ₗ[E] E) (Λ : Set (Fin n → E)) (S : Set E)
    (hS : ∀ l ∈ Λ, ψ l ∈ S) (x : Fin n → Fv F v ⊗[F] E) (hx : x ∈ latLoc (E := E) v Λ) :
    Assemble_bc v ψ x ∈ Submodule.span (v.adicCompletionIntegers F) (inclR (F := F) (Fv F v) '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    rw [Assemble_bc_ratV]
    exact Submodule.subset_span ⟨_, hS l hl, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul t x _ hx =>
    rw [Assemble_smul_eq, map_smul, smul_eq_mul, ← Assemble_smul_eq']
    exact Submodule.smul_mem _ t hx
end PI.LocFramePrimWork
