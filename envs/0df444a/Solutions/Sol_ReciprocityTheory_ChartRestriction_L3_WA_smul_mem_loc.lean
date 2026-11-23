-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.smul_mem_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:38.449875+00:00
-- url     : https://prove2.me/submissions/6f5e6b4f-3cea-4453-81e4-ce021c11834d

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFrame
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_IsHermSemilocalLocRing
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_GmapLocEqOfFrame
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨s, hs, hsa⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR p a).mp ha
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hsa
  obtain ⟨t, ht, htm⟩ := hm
  show ∃ u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, u • (a • m) ∈ L
  refine ⟨s * t, (Formalism.HermitianLatticesTheory.hcompl (K := K) p).mul_mem hs ht, ?_⟩
  have key : (s * t) • (a • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t) (a • m), ← algebraMap_smul K r (t • m),
      ← algebraMap_smul K t m, smul_smul, smul_smul, hr, map_mul]
    congr 1
    ring
  rw [key]
  exact L.smul_mem r htm
end ReciprocityTheory.ChartRestriction.L3.WA
