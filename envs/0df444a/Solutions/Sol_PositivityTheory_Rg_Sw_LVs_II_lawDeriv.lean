-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.lawDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:55.541975+00:00
-- url     : https://prove2.me/submissions/ee80c7e9-f9e5-4059-ab78-eb5ca1cf0458

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_pieceN
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_pieceOff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_pieceDiag
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_lam_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_lam_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_mem_span_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution : LawDeriv := by
  intro n Θ Ω hΩ hsub hdiff hlaw x hx Y hY
  have hd : DifferentiableAt ℂ Θ x := hdiff.differentiableAt (hΩ.mem_nhds (hsub hx))
  show fderiv ℂ Θ x (Y * x) = lam Y * Θ x
  refine Submodule.span_induction (p := fun Y _ => fderiv ℂ Θ x (Y * x) = lam Y * Θ x)
    ?_ ?_ ?_ ?_ (mem_span_gen Y hY)
  · intro Z hZ
    rcases hZ with ⟨β, hβ, rfl⟩ | ⟨c, i, j, rfl⟩
    · exact pieceN Θ hlaw x hx hd β hβ
    · by_cases hij : i = j
      · subst hij
        exact pieceDiag Θ hlaw x hx hd c i
      · exact pieceOff Θ hlaw x hx hd c i j hij
  · have h0 : lam (0 : M2 n) = 0 := by simpa using lam_smul 0 (0 : M2 n)
    rw [zero_mul, map_zero, h0, zero_mul]
  · intro a b _ _ ha hb
    rw [add_mul, map_add, ha, hb, lam_add, add_mul]
  · intro a b _ hb
    rw [smul_mul_assoc, map_smul, hb, lam_smul, smul_eq_mul, mul_assoc]
end PositivityTheory.Rg.Sw.LVs.II
