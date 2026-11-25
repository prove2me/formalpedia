-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductGluing.measurableSet_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:17.334817+00:00
-- url     : https://prove2.me/submissions/6a37affb-57e2-4bf9-b37b-0dff2d57d773

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isClopen_latV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct
open PI.VolStabW.RestrictedProductGluing
open PositiveNearLattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.RestrictedProductGluing
theorem _root_.solution :
    MeasurableSet (good (F := F) (E := E) (M := M) (a := a) b) := by
  have e : good (F := F) (E := E) (M := M) (a := a) b = ⋃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ⋂ v, ⋂ (_ : v ∉ S), {p | p.2 v ∈ latV b v} := by
    ext p
    simp only [good, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_cofinite]
    constructor
    · intro h
      exact ⟨h.toFinset, fun v hv => by
        by_contra hc
        exact hv (h.mem_toFinset.2 hc)⟩
    · rintro ⟨S, hS⟩
      exact S.finite_toSet.subset fun v hv => by
        by_contra hc
        exact hv (hS v hc)
  rw [e]
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine MeasurableSet.iUnion fun S => MeasurableSet.iInter fun v =>
    MeasurableSet.iInter fun _ => ?_
  exact ((measurable_pi_apply v).comp measurable_snd)
    (isClopen_latV b v a M).isOpen.measurableSet
end PI.VolStabW.RestrictedProductGluing
