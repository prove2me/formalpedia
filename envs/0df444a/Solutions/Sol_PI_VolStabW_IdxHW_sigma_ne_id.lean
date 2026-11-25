-- Prove2me | solution 1 for PI.VolStabW.IdxHW.sigma_ne_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:29.25981+00:00
-- url     : https://prove2.me/submissions/996abed0-a2b0-4613-b379-ec30e66da7c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxC

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
namespace PI.VolStabW.IdxHW
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra h
  push Not at h
  have hc := hCM.2.1
  let w : InfinitePlace E := Classical.arbitrary _
  have hcw : w.IsComplex := hc.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hcw
  rw [InfinitePlace.isReal_iff]
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq]
  have h1 := hCM.2.2.2 w.embedding x
  rw [h x] at h1
  exact h1.symm
end PI.VolStabW.IdxHW
