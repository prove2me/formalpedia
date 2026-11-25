-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:54.906553+00:00
-- url     : https://prove2.me/submissions/e2d51f3d-f6fe-46ef-911b-e8125094bd4f

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
theorem _root_.solution : ∃ d, IsDiffVal v d := by
  classical
  have hD : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (differentIdeal ℤ (𝓞 F)) : (differentIdeal ℤ (𝓞 F)).FG)
  let val : 𝓞 F → _ := fun x => Valued.v (algebraMap F (Fv F v) (x : F))
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hD
    rw [← hs]
    simp
  obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image s val hsne
  have hle : ∀ x ∈ differentIdeal ℤ (𝓞 F), val x ≤ val g := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hmax x hx
    | zero => simp [val]
    | add x y _ _ hx hy =>
      calc val (x + y) = Valued.v (algebraMap F (Fv F v) (x : F) + algebraMap F (Fv F v) (y : F)) := by
            simp [val]
        _ ≤ max (val x) (val y) := Valuation.map_add _ _ _
        _ ≤ val g := max_le hx hy
    | smul o x _ hx =>
      have ho : val o ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1
          (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v o)
      calc val (o • x) = val o * val x := by simp [val]
        _ ≤ 1 * val x := mul_le_mul_left ho _
        _ = val x := one_mul _
        _ ≤ val g := hx
  have hg0 : val g ≠ 0 := by
    intro h0
    apply hD
    rw [eq_bot_iff]
    intro x hx
    have h1 : val x = 0 := le_antisymm (h0 ▸ hle x hx) zero_le
    have h2 : (x : F) = 0 := (algebraMap F (Fv F v)).injective (by
      rw [map_zero]; exact (Valuation.zero_iff _).1 h1)
    rw [Submodule.mem_bot]
    exact_mod_cast h2
  refine ⟨algebraMap F (Fv F v) (g : F), ?_, ?_, ?_⟩
  · intro h; apply hg0; simp [val, h]
  · intro x hx; exact hle x hx
  · exact ⟨g, hs ▸ Submodule.subset_span hg, rfl⟩
end PI.LocFramePrimWork
