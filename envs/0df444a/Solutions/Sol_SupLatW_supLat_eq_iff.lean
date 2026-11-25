-- Prove2me | solution 1 for SupLatW.supLat_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:47.310989+00:00
-- url     : https://prove2.me/submissions/3e91d724-1eab-4ab9-8f6c-2162c76f119e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy
import Theorems.Thm_SupLatW_mem_stdLat_iff
import Theorems.Thm_SupLatW_alg_ne_zero
import Theorems.Thm_SupLatW_dvd_of_not_isUnit
import Theorems.Thm_SupLatW_supLat_le_of_dvd

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
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ}
    (x y : Fin r → R) (hx : ∃ i, ¬ ϖ ∣ x i) :
    supLat R K ϖ x = supLat R K ϖ y ↔ ∃ c : R, IsUnit c ∧ ∀ i, ϖ ∣ x i - c * y i := by
  constructor
  · intro hxy
    have hm : (algebraMap R K ϖ)⁻¹ • vecK R K x ∈
        stdLat R K r ⊔ Submodule.span R {(algebraMap R K ϖ)⁻¹ • vecK R K y} := by
      have : (algebraMap R K ϖ)⁻¹ • vecK R K x ∈ supLat R K ϖ x :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      rw [hxy] at this
      exact this
    obtain ⟨l, hl, t, ht, hsum⟩ := Submodule.mem_sup.mp hm
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ht
    obtain ⟨z, rfl⟩ := (mem_stdLat_iff (R := R) l).mp hl
    have hw : algebraMap R K ϖ * (algebraMap R K ϖ)⁻¹ = 1 := mul_inv_cancel₀ (alg_ne_zero hϖ)
    have hxi : ∀ i, x i = ϖ * z i + s * y i := by
      intro i
      apply IsFractionRing.injective R K
      have e := congrFun hsum i
      simp only [vecK, Pi.add_apply, Pi.smul_apply] at e
      simp only [smul_eq_mul] at e
      simp only [Algebra.smul_def] at e
      rw [map_add, map_mul, map_mul]
      linear_combination (-(algebraMap R K ϖ)) * e +
        (algebraMap R K s * algebraMap R K (y i) - algebraMap R K (x i)) * hw
    refine ⟨s, ?_, fun i => ⟨z i, by rw [hxi i]; ring⟩⟩
    by_contra hs
    obtain ⟨i, hi⟩ := hx
    exact hi (by
      rw [hxi i]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (dvd_of_not_isUnit hϖ hs) _))
  · rintro ⟨c, hc, h⟩
    refine le_antisymm (supLat_le_of_dvd hϖ x y c h)
      (supLat_le_of_dvd hϖ y x (↑hc.unit⁻¹) fun i => ?_)
    obtain ⟨d, hd⟩ := h i
    refine ⟨-(↑hc.unit⁻¹ : R) * d, ?_⟩
    have hcc : (↑hc.unit⁻¹ : R) * c = 1 := hc.val_inv_mul
    linear_combination (-(↑hc.unit⁻¹ : R)) * hd + (-(y i)) * hcc
end SupLatW
