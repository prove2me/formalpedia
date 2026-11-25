-- Prove2me | solution 1 for PositivityTheory.RgUd.Exp.Rpow.norm_eq_nabs_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:11.034316+00:00
-- url     : https://prove2.me/submissions/5826c6ee-3237-44ec-8d5a-4cca0f214ca7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_GenericIrreducibility_GenericUnitary_NormEqOneOfValuationEqOne
import Theorems.Thm_PositivityTheory_RgUd_Exp_Rpow_exists_unit_uniformizer
import Theorems.Thm_PositivityTheory_RgUd_Exp_Rpow_norm_eq_one_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SmGL_nabs_eq_one
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_zero_iff
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Exp PositivityTheory.RgUd.Exp.Rpow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.RgUd.Exp.Rpow
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  obtain ⟨ϖ, hϖ⟩ := exists_unit_uniformizer k
  set a := ‖(χ ϖ : ℂ)‖
  set b := nabs k ϖ
  have ha : 0 < a := norm_pos_iff.2 (χ ϖ).ne_zero
  have hb : 0 < b := nabs_pos' k ϖ
  have hb1 : b ≠ 1 := fun e => (uniformizer_lt_one (R := k)).ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hlb : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb hb1
  refine ⟨Real.log a / Real.log b, fun z => ?_⟩
  have hbt : b ^ (Real.log a / Real.log b) = a := by
    rw [Real.rpow_def_of_pos hb, mul_div_cancel₀ _ hlb, Real.exp_log ha]
  set m : ℤ := ord k z
  set u : kˣ := z * ϖ ^ (-m)
  have hord1 : ord k ϖ = 1 := ord_eq_one hϖ
  have hordu : ord k u = 0 := by
    have e1 : ordHom k u = ordHom k z * ordHom k ϖ ^ (-m) := by rw [map_mul, map_zpow]
    have e2 := congrArg Multiplicative.toAdd e1
    simp only [ordHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_mul, toAdd_zpow, toAdd_ofAdd, hord1] at e2
    rw [e2]
    simp [m]
  have hu : valuation k (u : k) = 1 := ord_eq_zero_iff.1 hordu
  have hz : z = u * ϖ ^ m := by
    simp only [u, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hnorm : ‖(χ z : ℂ)‖ = a ^ m := by
    have := congrArg (normHom χ) hz
    rw [map_mul, map_zpow] at this
    simpa [normHom, norm_eq_one_of_valuation_eq_one χ hχ hu, a] using this
  have hnabs : nabs k z = b ^ m := by
    have := congrArg (nabsHom k) hz
    rw [map_mul, map_zpow] at this
    simpa [nabsHom, nabs_eq_one k hu, b] using this
  rw [hnorm, hnabs, ← Real.rpow_intCast b m, ← Real.rpow_mul hb.le, mul_comm, Real.rpow_mul hb.le, hbt,
    Real.rpow_intCast]
end PositivityTheory.RgUd.Exp.Rpow
