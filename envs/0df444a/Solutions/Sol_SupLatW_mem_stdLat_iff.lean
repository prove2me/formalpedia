-- Prove2me | solution 1 for SupLatW.mem_stdLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:45.443299+00:00
-- url     : https://prove2.me/submissions/51d97c21-a6fb-456c-866b-9ae5110d2e98

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SupLatW
open Formalism.MainNotions.Ext.CutC
namespace SupLatW
theorem _root_.solution {R K : Type} [CommRing R] [Field K] [Algebra R K] {r : ℕ}
    (v : Fin r → K) : v ∈ stdLat R K r ↔ ∃ x : Fin r → R, v = vecK R K x := by
  constructor
  · intro hv
    unfold stdLat at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      refine ⟨Pi.single i 1, ?_⟩
      funext j
      by_cases h : j = i
      · subst h; simp [vecK]
      · simp [vecK, h]
    | zero => exact ⟨0, by funext j; simp [vecK]⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, by funext j; simp [vecK]⟩
    | smul a b _ hb =>
      obtain ⟨y, rfl⟩ := hb
      exact ⟨a • y, by funext j; simp [vecK, Algebra.smul_def]⟩
  · rintro ⟨x, rfl⟩
    have hx : vecK R K x = ∑ i, x i • (Pi.single i (1 : K) : Fin r → K) := by
      funext j
      simp [vecK, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [hx]
    unfold stdLat
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end SupLatW
