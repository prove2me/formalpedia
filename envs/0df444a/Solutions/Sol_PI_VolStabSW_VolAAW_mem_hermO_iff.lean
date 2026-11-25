-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.mem_hermO_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:40.530851+00:00
-- url     : https://prove2.me/submissions/54b4d8d8-1471-464f-868c-8b3721151d8f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) {a : ℕ} (T : HermR (Fv F v) σ a) :
    T ∈ hermO b v σ a ↔
      (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) ∈ latV (M := a) (n := a) b v := by
  constructor
  · intro h p i k
    exact h i p k
  · intro h i j k
    exact h j i k
end PI.VolStabSW.VolAAW
