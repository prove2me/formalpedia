-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:13.092462+00:00
-- url     : https://prove2.me/submissions/f251be12-7179-4a56-9b15-d59e7f67ac3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
namespace PI.IsoDetW.Loc
theorem _root_.solution {X Y Z : Submodule R W} (h1 : X ≤ Y) (h2 : Y ≤ Z) :
    relative₂ X Z = relative₂ X Y + relative₂ Y Z := by
  unfold relative₂
  let f : (Y ⧸ X.comap Y.subtype) →ₗ[R] (Z ⧸ X.comap Z.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion h2) (fun y hy => by simpa using hy)
  let g : (Z ⧸ X.comap Z.subtype) →ₗ[R] (Z ⧸ Y.comap Z.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun z hz => by
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.id_apply] at hz ⊢
      exact h1 hz)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, Submodule.coe_inclusion] at hq ⊢
      exact hq
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H z => exact ⟨Submodule.Quotient.mk z, rfl⟩
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · intro hz
        exact ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩
      · rintro ⟨q', hq'⟩
        induction q' using Submodule.Quotient.induction_on with
        | H y =>
          simp only [f, Submodule.mapQ_apply] at hq'
          rw [Submodule.Quotient.eq] at hq'
          simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
            Submodule.coe_inclusion] at hq'
          have h3 : (z : W) = (y : W) - ((y : W) - (z : W)) := by abel
          rw [h3]
          exact Y.sub_mem y.2 (h1 hq')
end PI.IsoDetW.Loc
