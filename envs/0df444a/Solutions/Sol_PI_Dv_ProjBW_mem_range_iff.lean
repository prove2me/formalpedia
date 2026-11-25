-- Prove2me | solution 1 for PI.Dv.ProjBW.mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:43.330055+00:00
-- url     : https://prove2.me/submissions/ab322d3c-0aeb-4b01-b368-60f057d1eda0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjBW
open NumberField Formalism.HN
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.Dv.ProjBW
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (e : Module.End K V) (he : e * e = e) (x : V) :
    x ∈ LinearMap.range e ↔ e x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Module.End.mul_apply, he]
  · intro h
    exact ⟨x, h⟩
end PI.Dv.ProjBW
