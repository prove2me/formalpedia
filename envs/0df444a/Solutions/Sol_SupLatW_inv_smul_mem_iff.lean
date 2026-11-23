-- Prove2me | solution 1 for SupLatW.inv_smul_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:25.941591+00:00
-- url     : https://prove2.me/submissions/3574a079-43a0-491b-8903-457126f4a669

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy
import Theorems.Thm_SupLatW_mem_stdLat_iff
import Theorems.Thm_SupLatW_alg_ne_zero

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
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ} (x : Fin r → R) :
    (algebraMap R K ϖ)⁻¹ • vecK R K x ∈ stdLat R K r ↔ ∀ i, ϖ ∣ x i := by
  have h0 := alg_ne_zero (K := K) hϖ
  have hinj := IsFractionRing.injective R K
  rw [mem_stdLat_iff]
  constructor
  · rintro ⟨z, hz⟩ i
    refine ⟨z i, hinj ?_⟩
    have e := congrFun hz i
    simp only [vecK, Pi.smul_apply, smul_eq_mul] at e
    rw [map_mul, ← e, mul_inv_cancel_left₀ h0]
  · intro h
    choose z hz using h
    refine ⟨z, funext fun i => ?_⟩
    simp only [vecK, Pi.smul_apply, smul_eq_mul]
    rw [hz i, map_mul, inv_mul_cancel_left₀ h0]
end SupLatW
