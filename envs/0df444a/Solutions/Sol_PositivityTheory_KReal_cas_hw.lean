-- Prove2me | solution 1 for PositivityTheory.KReal.cas_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:33.165328+00:00
-- url     : https://prove2.me/submissions/ad03de53-e732-49ae-9e3c-262a96aed3fd

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_sb_refl
import Theorems.Thm_PositivityTheory_KReal_sb_of_pos
import Theorems.Thm_PositivityTheory_KReal_pos_irrefl
import Theorems.Thm_PositivityTheory_KReal_pos_asymm
import Theorems.Thm_PositivityTheory_KReal_sb_tri
import Theorems.Thm_PositivityTheory_KReal_hw_comm
import Theorems.Thm_PI_FockOneDegW_Core_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : M} (hf : HwK ρ μ f) : casK ρ f = ((casW μ : ℚ) : ℂ) • f := by
  have key : ∀ a b : Ix r s, (if sameBlock a b then ρ a b * ρ b a else 0) f =
      (((if a = b then μ a ^ 2 else 0) + (if posC a b then μ a - μ b else 0) : ℚ) : ℂ) • f := by
    intro a b
    by_cases hab : sameBlock a b
    · rw [if_pos hab]
      rcases sb_tri hab with h | h | h
      · subst h
        rw [if_pos rfl, if_neg (pos_irrefl a), Module.End.mul_apply, hf.1 a, map_smul, hf.1 a, smul_smul]
        congr 1
        push_cast
        ring
      · rw [if_neg (fun e : a = b => pos_irrefl b (by subst e; exact h)), if_pos h, Module.End.mul_apply, hw_comm hρ hf h, zero_add]
      · rw [if_neg (fun e : a = b => pos_irrefl b (by subst e; exact h)), if_neg (pos_asymm h), Module.End.mul_apply, hf.2 b a h]
        simp
    · rw [if_neg hab, if_neg (fun e : a = b => hab (by subst e; exact sb_refl a)), if_neg (fun h => hab (sb_of_pos h))]
      simp
  unfold casK casW
  simp only [LinearMap.sum_apply, key, ← Finset.sum_smul]
  congr 1
  simp only [← Rat.cast_sum, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end PositivityTheory.KReal
