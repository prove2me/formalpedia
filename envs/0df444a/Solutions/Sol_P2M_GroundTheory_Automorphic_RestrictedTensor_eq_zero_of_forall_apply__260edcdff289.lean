-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply__260edcdff289
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:25.484472+00:00
-- url     : https://prove2.me/submissions/e9cd6f97-7a77-4403-b2b2-b4bd2fa33c0f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_mOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ : Representation ℂ M V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Dual ℂ V} (h : ∀ m, l (ρ m v) = 0) : l = 0 := by
  ext x
  have hx := mem_span_mOrbit (ρ := ρ) hv x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact h m
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]
end GroundTheory.Automorphic.RestrictedTensor
