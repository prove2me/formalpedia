-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_of_reads_9f0e0ab7957e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:38.218328+00:00
-- url     : https://prove2.me/submissions/6f83a059-6dcb-455b-ab65-02c133394b83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_of_homog_159b62054b52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.AddBlockBridge
theorem _root_.solution {a : ι → ℤ} (t : IntegralSection P a) {s : Ω} (ht : P.Reads y a s t.toFun) :
    funHom P y hP t.toFun = constMap ι s * ∏ k, varT k ^ a k := by
  have hden : P.mkF t.den ≠ 0 := fun h ↦ t.den_not_mem ((P.mkF_eq_zero_iff _).mp h)
  have hnum : P.mkF t.num = t.toFun * P.mkF t.den := by
    rw [IntegralSection.toFun, div_mul_cancel₀ _ hden]
  have hval : aeval y t.num = s * aeval y t.den :=
    (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
      (fun k ↦ by have := t.deg_eq k; omega)).mpr hnum
  have hden' : funHom P y hP (P.mkF t.den) ≠ 0 := (map_ne_zero_iff _ (funHom P y hP).injective).mpr hden
  rw [funHom_mkF, coneHom_of_homog y t.den_isHomogeneous] at hden'
  have hc : constMap ι (aeval y t.den) ≠ 0 := left_ne_zero_of_mul hden'
  have hp : ∏ k, varT (Ω := Ω) k ^ t.denDeg k ≠ 0 := right_ne_zero_of_mul hden'
  have hPa : ∏ k, varT (Ω := Ω) k ^ a k = (∏ k, varT k ^ t.numDeg k) / ∏ k, varT k ^ t.denDeg k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← t.deg_eq k, zpow_sub₀ (varT_ne_zero k), zpow_natCast, zpow_natCast]
  rw [IntegralSection.toFun, map_div₀, funHom_mkF, funHom_mkF, coneHom_of_homog y t.num_isHomogeneous,
    coneHom_of_homog y t.den_isHomogeneous, hval, map_mul, hPa]
  field_simp
end GroundTheory.Heights₂.Heights.AddBlockBridge
