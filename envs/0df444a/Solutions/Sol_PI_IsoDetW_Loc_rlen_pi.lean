-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:40.14528+00:00
-- url     : https://prove2.me/submissions/78a87de5-a624-4657-8663-7adcbe4111ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi

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
namespace PI.IsoDetW.Loc
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (X Z : ∀ i, Submodule R (M i)) :
    relative₂ (Submodule.pi Set.univ X) (Submodule.pi Set.univ Z) = ∑ i, relative₂ (X i) (Z i) := by
  classical
  let φ : (Submodule.pi Set.univ Z) →ₗ[R] (Π i, Z i ⧸ (X i).comap (Z i).subtype) :=
    LinearMap.pi fun i => ((X i).comap (Z i).subtype).mkQ ∘ₗ
      (LinearMap.codRestrict (Z i) (LinearMap.proj i ∘ₗ (Submodule.pi Set.univ Z).subtype)
        (fun z => z.2 i (Set.mem_univ i)))
  have hsurj : Function.Surjective φ := by
    intro q
    choose z hz using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨⟨fun i => (z i).1, fun i _ => (z i).2⟩, ?_⟩
    funext i
    rw [← hz i]
    rfl
  have hker : LinearMap.ker φ = (Submodule.pi Set.univ X).comap (Submodule.pi Set.univ Z).subtype := by
    ext z
    simp [φ, funext_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_pi]
    rfl
  unfold relative₂
  rw [((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)).length_eq,
    Module.length_pi_of_fintype]
end PI.IsoDetW.Loc
