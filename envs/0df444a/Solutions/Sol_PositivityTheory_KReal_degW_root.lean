-- Prove2me | solution 1 for PositivityTheory.KReal.degW_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:56.461444+00:00
-- url     : https://prove2.me/submissions/59b454e1-8866-4860-a9c2-50501336a499

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Theorems.Thm_PositivityTheory_KReal_cw_two
import Theorems.Thm_PositivityTheory_KReal_cw_root
import Theorems.Thm_PI_FockOneDegW_Core_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
private theorem shiftNu_sub_lemma {r s : ℕ} (c : ℚ) (μ μ' : Ix r s → ℚ) (x : Ix r s) :
    shiftNu c μ x = shiftNu c μ' x + (μ x - μ' x) := by
  cases x <;> simp only [shiftNu] <;> ring
end PositivityTheory.KReal
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {r s : ℕ} (c : ℚ) {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    degW c ν = degW c La + (|shiftNu c La b + 1| - |shiftNu c La b|) + (|shiftNu c La a - 1| - |shiftNu c La a|) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  have key := cw_two (fun x => |shiftNu c ν x|) (fun x => |shiftNu c La x|) hab
    (fun x h1 h2 => by
      show |shiftNu c ν x| = |shiftNu c La x|
      rw [shiftNu_sub_lemma c ν La x, hx x h1 h2, sub_self, add_zero])
  have e1 : shiftNu c ν b = shiftNu c La b + 1 := by
    rw [shiftNu_sub_lemma c ν La b, hb]
    ring
  have e2 : shiftNu c ν a = shiftNu c La a - 1 := by
    rw [shiftNu_sub_lemma c ν La a, ha]
    ring
  simp only [e1, e2] at key
  unfold degW
  exact key
end PositivityTheory.KReal
