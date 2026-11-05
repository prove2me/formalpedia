-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaArgumentBudget.polyNeed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:59:42.915941+00:00
-- url     : https://prove2.me/submissions/5e7ca209-7806-4655-a424-8407e81f6160

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceControlBudget_budget_polyNeed

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaArgumentBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaArgumentWords WeightedGlobalArenaSourceControlBudget
open WeightedGlobalLocalParameters
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaArgumentBudget
theorem _root_.solution (m p F M : ℕ) (hM : 1<M) : PolyNeed (need m p F M) := by
  obtain ⟨s,k,h⟩ := budget_polyNeed m p F 1 M 0 0 hM
  refine ⟨2*s+8,2*k,?_⟩
  intro n U
  let X := polyBound s k [n,U]
  have hX : 1≤X := Nat.succ_le_of_lt (by
    simp only [X,polyBound,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    positivity)
  have hx : (budget m p F 1 M 0 0 n U).word+(budget m p F 1 M 0 0 n U).depth+1≤3*X := by
    have hw := (h n U).1
    have hd := (h n U).2.2
    change _≤X at hw hd
    omega
  have he : polyBound (2*s+8) (2*k) [n,U]=256*X^2 := by
    dsimp [X,polyBound]
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    rw [show 2*s+8=s*2+8 by omega,pow_add,show 2*k=k*2 by omega,pow_mul,pow_mul,mul_pow]
    norm_num
    ring
  refine ⟨?_,Nat.zero_le _,Nat.zero_le _⟩
  change 16*((budget m p F 1 M 0 0 n U).word+(budget m p F 1 M 0 0 n U).depth+1)^2≤_
  rw [he]
  exact (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hx 2)).trans (by nlinarith)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaArgumentBudget
