-- Prove2me | solution 1 for SupLatW.supLat_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:46.801139+00:00
-- url     : https://prove2.me/submissions/78048dce-c53d-4664-96fa-326b646f38fb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy
import Theorems.Thm_SupLatW_inv_smul_mem_iff

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
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ} (x y : Fin r → R) (c : R)
    (h : ∀ i, ϖ ∣ x i - c * y i) : supLat R K ϖ x ≤ supLat R K ϖ y := by
  unfold supLat
  refine sup_le le_sup_left ?_
  rw [Submodule.span_singleton_le_iff_mem]
  have h1 : (algebraMap R K ϖ)⁻¹ • vecK R K (fun i => x i - c * y i) ∈ stdLat R K r :=
    (inv_smul_mem_iff hϖ _).mpr h
  have h2 : (algebraMap R K ϖ)⁻¹ • vecK R K x =
      (algebraMap R K ϖ)⁻¹ • vecK R K (fun i => x i - c * y i) +
        c • ((algebraMap R K ϖ)⁻¹ • vecK R K y) := by
    funext i
    simp only [vecK, Pi.add_apply, Pi.smul_apply]
    simp only [smul_eq_mul]
    simp only [Algebra.smul_def, map_sub, map_mul]
    ring
  rw [h2]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h1)
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
end SupLatW
