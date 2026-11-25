-- Prove2me | solution 1 for PI.VolSemiDirect.W.ratV_mem_spanR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:49:55.683506+00:00
-- url     : https://prove2.me/submissions/ce27cbb5-8b02-4932-9055-c98e91b00a95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_Closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R}
namespace PI.VolSemiDirect.W
theorem _root_.solution {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Y '' s)) : ratV (F := F) R x ∈ spanR (F := F) R Y s := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    have h0 : ratV (F := F) R (0 : Fin n → E) = 0 := by
      funext i
      simp [ratV]
    rw [h0]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have h0 : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
      funext i
      simp [ratV]
    rw [h0]
    exact add_mem hx hy
  | smul c x _ hx =>
    have h0 : ratV (F := F) R (c • x) = inclR (F := F) R c • ratV (F := F) R x := by
      funext i
      simp [ratV]
    rw [h0]
    exact Submodule.smul_mem _ _ hx
end PI.VolSemiDirect.W
