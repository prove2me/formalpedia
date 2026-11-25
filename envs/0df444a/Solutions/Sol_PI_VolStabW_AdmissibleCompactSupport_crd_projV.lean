-- Prove2me | solution 1 for PI.VolStabW.AdmissibleCompactSupport.crd_projV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:43.460803+00:00
-- url     : https://prove2.me/submissions/eac36559-f122-446a-a619-55d2aa90e963

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_AdmCpt
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_crd_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.AdmissibleCompactSupport
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabW PI.VolStabW.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.AdmissibleCompactSupport
theorem _root_.solution {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F))
    (i : Fin a) (j : Fin M) (k : Fin d) :
    crd b (Fv F v) (projV v Y i j) k = (crd b (Af F) (Y i j) k) v := by
  simp only [projV]
  rw [crd_map]
  rfl
end PI.VolStabW.AdmissibleCompactSupport
