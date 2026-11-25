-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__exists_short_vector_minkowski_88a123bac9a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:10.646912+00:00
-- url     : https://prove2.me/submissions/bf3ec138-2622-41f3-a96a-f054ced5ba6a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
open MeasureTheory
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (R : ℝ) (hR : 0 ≤ R)
    (hvol : ZLattice.covolume Λ * 2 ^ N < R ^ N * (√Real.pi ^ N / Real.Gamma ((N : ℝ) / 2 + 1))) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ < R := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b := Module.Free.chooseBasis ℤ Λ
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℝ (Fin N)))
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF
  have hfin : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  haveI : Countable Λ.toAddSubgroup := Countable.of_equiv _ b.equivFun.toEquiv.symm
  have hc0 : 0 ≤ ZLattice.covolume Λ := by rw [hcov]; exact measureReal_nonneg
  have hvolF : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) = ENNReal.ofReal (ZLattice.covolume Λ) := by
    rw [hcov, measureReal_def, ENNReal.ofReal_toReal hfin]
  have hq : 0 < R ^ N * (√Real.pi ^ N / Real.Gamma ((N : ℝ) / 2 + 1)) :=
    lt_of_le_of_lt (mul_nonneg hc0 (by positivity)) hvol
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := Λ.toAddSubgroup) (s := Metric.ball (0 : EuclideanSpace ℝ (Fin N)) R) hF
    (fun x hx => by simpa using hx) (convex_ball 0 R) (by
      rw [EuclideanSpace.volume_ball, finrank_euclideanSpace_fin, Fintype.card_fin, hvolF]
      have h2 : (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) := by
        rw [ENNReal.ofReal_pow (by norm_num)]; simp
      rw [h2, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff hq).2 hvol)
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), by simpa using hxs⟩
end Formalism.MainNotions.BridgeLemma₂
