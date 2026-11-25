-- Prove2me | solution 1 for PI.LocHaarRRW.mem_ordR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:13.45477+00:00
-- url     : https://prove2.me/submissions/c6c22bee-ad97-48a6-be85-f72b53a3cc96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocHaarRR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_IntegralMemNhdsAndSubsetCompactOfFinrankTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_MemOrdR
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology IsDedekindDomain NumberField
open PI PI.LocHaarRRW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}
namespace PI.LocHaarRRW
theorem _root_.solution (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (h1 : (sg.e x).1 ∈ 𝒪[A.Fp]) (h2 : (sg.e x).2 ∈ 𝒪[A.Fp])
    (h12 : Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).1, h1⟩ =
      Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).2, h2⟩) :
    x ∈ PI.LocHaarRR.ordR sg := by
  simp only [PI.LocHaarRR.ordR]
  rw [Subring.mem_comap, Subring.mem_map]
  exact ⟨(⟨_, h1⟩, ⟨_, h2⟩), h12, rfl⟩
end PI.LocHaarRRW
