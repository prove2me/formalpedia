-- Prove2me | solution 1 for PI.VolSemiDirect.W.norm_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:36.606805+00:00
-- url     : https://prove2.me/submissions/b628f8e9-bb48-4ad1-acf6-4d3ec9014ce1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
import Theorems.Thm_PI_VolSemiDirect_W_stabilizer_fixes_frame_vector
import Theorems.Thm_PI_VolSemiDirect_W_stabilizer_fixes_frame_span
import Theorems.Thm_PI_VolSemiDirect_W_heisenberg_le_stabilizer


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolSemiDirect.W
theorem _root_.solution {r : ℕ} (P : Frame E M r) (h : HA R σ J) (hh : h ∈ Hsub R σ J P)
    (n : HA R σ J) (hn : n ∈ FrameUnipotentSubgroup R σ J P) : h * n * h⁻¹ ∈ FrameUnipotentSubgroup R σ J P := by
  have hHS := heisenberg_le_stabilizer R σ J P hh
  rw [FrameUnipotentSubgroup, Subgroup.mem_inf] at hn ⊢
  have hS : h * n * h⁻¹ ∈ S0 R σ J P :=
    (S0 R σ J P).mul_mem ((S0 R σ J P).mul_mem hHS hn.2) ((S0 R σ J P).inv_mem hHS)
  refine ⟨?_, hS⟩
  have hnN := hn.1
  show UniC R σ J P.e (h * n * h⁻¹) ∧ ∀ v, InXperp R σ J P v →
    lin R σ J (h * n * h⁻¹) v - v ∈ spanR (F := F) R P.e Set.univ
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [stabilizer_fixes_frame_vector R σ J P hS b, sub_self]
    exact Submodule.zero_mem _
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      have e1 := stabilizer_fixes_frame_vector R σ J P ((S0 R σ J P).inv_mem hHS) a
      rw [← e1, hR_lin]
      exact hv a
    have hnu : lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v ∈ spanR (F := F) R P.e Set.univ :=
      hnN.2 _ hu
    have key : lin R σ J (h * n * h⁻¹) v - v =
        lin R σ J h (lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v) := by
      rw [map_sub, lin_mul, lin_mul, lin_lin_inv]
    rw [key, stabilizer_fixes_frame_span R σ J P hHS _ hnu]
    exact hnu
end PI.VolSemiDirect.W
