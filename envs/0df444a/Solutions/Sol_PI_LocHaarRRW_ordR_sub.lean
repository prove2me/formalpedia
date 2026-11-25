-- Prove2me | solution 1 for PI.LocHaarRRW.ordR_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:19.100619+00:00
-- url     : https://prove2.me/submissions/ce15257d-a0c9-4c36-8b67-00785791ed7d

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
    (hx : x ∈ PI.LocHaarRR.ordR sg) : (sg.e x).1 ∈ 𝒪[A.Fp] ∧ (sg.e x).2 ∈ 𝒪[A.Fp] := by
  simp only [PI.LocHaarRR.ordR] at hx
  rw [Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨y, -, hy⟩ := hx
  have hy' : sg.e x = ((y.1 : A.Fp), (y.2 : A.Fp)) := hy.symm
  rw [hy']
  exact ⟨y.1.2, y.2.2⟩
end PI.LocHaarRRW
