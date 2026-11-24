-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.norming
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:44.794786+00:00
-- url     : https://prove2.me/submissions/c932f8c8-e378-48a5-bf8e-f524eaf92aa2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
variable {S : Type} [AddCommGroup S] [Module ℂ S]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (q : Seminorm ℂ S) (g : S) : ∃ T : S →ₗ[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg], fun x => by simp⟩
  let f : Module.Dual ℂ (Submodule.span ℂ {g}) := (q g : ℂ) • (LinearEquiv.coord ℂ S g hg).toLinearMap
  have hf : ∀ x : Submodule.span ℂ {g}, ‖f x‖ ≤ q x := fun x => by
    have h := LinearEquiv.coord_apply_smul ℂ S g hg x
    have : q x = ‖LinearEquiv.coord ℂ S g hg x‖ * q g := by rw [← map_smul_eq_mul, h]
    rw [this]
    simp [f, mul_comm, abs_of_nonneg (apply_nonneg q g)]
  obtain ⟨T, hT, hle⟩ := Module.Dual.exists_extension_of_le_seminorm _ f hf
  refine ⟨T, ?_, hle⟩
  have := hT ⟨g, Submodule.mem_span_singleton_self g⟩
  simp only at this
  rw [this]
  simp [f, abs_of_nonneg (apply_nonneg q g), LinearEquiv.coord_self]
end PositivityTheory.ThKG.Loc.Bump
