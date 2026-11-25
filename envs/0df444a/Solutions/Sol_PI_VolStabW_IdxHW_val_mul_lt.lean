-- Prove2me | solution 1 for PI.VolStabW.IdxHW.val_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:14:36.721517+00:00
-- url     : https://prove2.me/submissions/0691f5d3-7fd2-46ca-a2ef-9227cd31ac65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxE

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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
namespace PI.VolStabW.IdxHW
theorem _root_.solution {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (hy : Valued.v y < 1) :
    Valued.v (x * y) < 1 := by
  rw [map_mul]
  have hx' : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hx
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hx') hy
end PI.VolStabW.IdxHW
