-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_span_of_local_c35ca71026c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:46.433686+00:00
-- url     : https://prove2.me/submissions/756e3905-f62a-4baf-b804-2e7b8fb4e3f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt.mulBy_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
theorem _root_.solution [NumberField L] {B : Subring L} [Module.Finite ℤ B] {M : AddSubgroup L} {ι : Type}
    {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span (𝓞 L) (Set.range a) := by
  set S := Submodule.span (𝓞 L) (Set.range a)
  let J : Ideal B :=
    { carrier := {b | (b : L) * z ∈ S}
      add_mem' := fun {x y} hx hy => by
        show ((x : L) + y) * z ∈ S
        rw [add_mul]
        exact S.add_mem hx hy
      zero_mem' := by
        show ((0 : B) : L) * z ∈ S
        simp
      smul_mem' := fun c x hx => by
        show ((c : L) * x) * z ∈ S
        rw [mul_assoc]
        exact mul_mem_of_mem c.2 hx }
  by_contra hzS
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ J := h ▸ Submodule.mem_top
    have h2 : ((1 : B) : L) * z ∈ S := h1
    apply hzS
    simpa using h2
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨i, hi⟩ := hloc m hm
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  apply hbm
  apply hJm
  show (b : L) * z ∈ S
  rw [hbc]
  exact mul_mem_of_mem c.2 (Submodule.subset_span ⟨i, rfl⟩)
end GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
