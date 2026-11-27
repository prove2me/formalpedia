-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_LowerBoundComponentConjugate_proof_f10fcba1ad3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:06:24.073516+00:00
-- url     : https://prove2.me/submissions/fe7db529-0f69-4ce3-92ef-d40a337108b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagSectionNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_MUConjInv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_sl_eq_8eea8789824b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open ComponentData
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
namespace LowerBoundComponentConjugate
theorem _root_.solution (hF : FdegNeZero.Statement) : LowerBoundComponentConjugate.Statement := by
  intro Ψ _ _ K _ _ ι _ D II Ch Cu B hC hII hK hZ _hX hpos hconj hint hbd hS hmean hP _hH hj1 hj3 hB1 hB2 vol hvol

  have hyp : ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
      ((D.n + 1 : ℕ) : ℝ) * (-Ch * D.f * D.jp * D.abelian₂ B - eps * D.Kamp) * (D.MU B eps t').geomDeg D.P D.n ≤
        (D.MU B eps t').top II D.P (D.n + 1) := by
    intro eps t' he0 he1 ht0 ht1
    obtain ⟨h1, h2, h3⟩ := hpos B hB2 eps t' he0 he1 ht0 ht1
    refine hZ Ψ K ι D II (D.MU B eps t') _ hII h1 h2 h3 (hconj B hB2 eps t' he0 he1 ht0 ht1) ?_
    intro W hW
    by_cases hb : OnBd D.Bd W
    · exact hbd B hB1 eps t' he0 he1 ht0 ht1 W hW hb
    · exact hint B hB1 eps t' he0 he1 ht0 ht1 W hW hb
  have hlim := hS Ψ K ι D II hC hII hK B hB2 (-Ch * D.f * D.jp * D.abelian₂ B) hyp
  have hU := hmean hj1 hj3 B hB1
  obtain ⟨hPP, -, hdeg⟩ := hP Ψ K ι D II hC hII B
  have hc : ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) ≠ 0 := by
    refine mul_ne_zero (by simp [cf]) ?_
    exact_mod_cast hF Ψ D.N D.j D.j_le_N
  rw [sl_eq hPP hc hvol]
  have hm : (0 : ℝ) < ((D.n + 1 : ℕ) : ℝ) * D.degMu := mul_pos (by positivity) hdeg
  rw [le_div_iff₀ hm]
  have hU' := mul_le_mul_of_nonneg_left hU hm.le
  nlinarith [hlim, hU']
end LowerBoundComponentConjugate
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
