-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.int_ind_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:49.625781+00:00
-- url     : https://prove2.me/submissions/edca7294-4fc0-4e53-bf2e-6948d8b8aade

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_vol_smul
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_GLDoubling_nabs_unif
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_PositivityTheory_ThKG_Std_int_ind
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (hϖ : IsUnif ϖ) (c : ℕ) : ∫ x, ind ((ϖ : k) ^ c) x ∂m = ((resCard k : ℂ) ^ c)⁻¹ := by
  rw [int_ind (pow_ne_zero _ ϖ.ne_zero)]
  have : {x : k | valuation k x ≤ valuation k ((ϖ : k) ^ c)} = (ϖ ^ c) • {x : k | valuation k x ≤ valuation k 1} := by
    ext x
    have h0 : 0 < valuation k ((ϖ : k) ^ c) := zero_lt_iff.2 (by simp)
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_setOf_eq, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul,
      map_inv₀, map_one]
    rw [inv_mul_le_iff₀ h0, mul_one]
  have hn : nabs k (ϖ ^ c) = ((resCard k : ℝ) ^ c)⁻¹ := by
    clear this
    induction c with
    | zero => simp [nabs_one]
    | succ c ih => rw [pow_succ, nabs_mul, ih, GlobalTheory.GLDoubling.nabs_unif hϖ, pow_succ, mul_inv]
  rw [Measure.real, this, vol_smul hm, hm.one, mul_one, ENNReal.toReal_ofReal (nabs_pos k _).le, hn]
  simp
end PositivityTheory.ThKG.Std
