-- Prove2me | solution 1 for R03CoreBranchV7.old_single_bad
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:27:12.1826+00:00
-- url     : https://prove2.me/submissions/b980b16a-6ca5-4360-9915-f9ab214e7056

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_c874916438_v7_CoreBranch

/- Candidate-only fixed 9-vertex relative-boundary core. Not the root graph.
   The 11 coordinates follow v7_core_branches.observation.json edge order.
   Codes on external ports 4,5,6,7,8 are 0,0,1,2,0 (incoming convention).
   Independent graph interpretation and admission remain separate. -/
namespace R03CoreBranchV7
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 100000

private theorem add2 : ∀ a b : Fin 3, a+b=2 → a=2+2*b := by decide +kernel
private theorem add1 : ∀ a b : Fin 3, a+b=1 → a=1+2*b := by decide +kernel
private theorem signed2 : ∀ a b : Fin 3, a+2*b=2 → a=2+b := by decide +kernel
private theorem signed0 : ∀ a b : Fin 3, a+2*b=0 → a=b := by decide +kernel
private theorem twosigned : ∀ a b c : Fin 3, a+2*b+2*c=2 → a=2+b+c := by decide +kernel
private theorem three1 : ∀ a b c : Fin 3, a+b+c=1 → a=1+2*b+2*c := by decide +kernel
private theorem norm : ∀ a b c : Fin 3,
    (2+(1+2*b)+(2+2*c)=2+2*b+2*c) ∧
    (1+2*(2+b)+2*c=2+2*b+2*c) ∧
    (1+2*(2+2*b+2*c)+2*(2+2*a)=a+b+c) := by decide +kernel
private theorem cases11 : ∀ i : Fin 11,
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 := by decide +kernel

theorem core_complete (x : Fin 11 → Fin 3) (h : Core x) :
    x = state (x 6) (x 9) (x 10) := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hx2 := add2 (x 2) (x 6) h4
  have hx4 := signed2 (x 4) (x 9) h5
  have hx7 := add1 (x 7) (x 9) h6
  have hx5 := signed0 (x 5) (x 10) h7
  have hx8 := add2 (x 8) (x 10) h8
  have hx1 : x 1 = 2+2*x 9+2*x 10 := by
    calc
      x 1 = 2+x 7+x 8 := twosigned _ _ _ h3
      _ = 2+2*x 9+2*x 10 := by
        rw [hx7,hx8]
        exact (norm (x 6) (x 9) (x 10)).1
  have hx3 : x 3 = 2+2*x 9+2*x 10 := by
    calc
      x 3 = 1+2*x 4+2*x 5 := three1 _ _ _ h1
      _ = 2+2*x 9+2*x 10 := by
        rw [hx4,hx5]
        exact (norm (x 6) (x 9) (x 10)).2.1
  have hx0 : x 0 = x 6+x 9+x 10 := by
    calc
      x 0 = 1+2*x 1+2*x 2 := three1 _ _ _ h0
      _ = x 6+x 9+x 10 := by
        rw [hx1,hx2]
        exact (norm (x 6) (x 9) (x 10)).2.2
  funext i
  rcases cases11 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx0
  · exact hx1
  · exact hx2
  · exact hx3
  · exact hx4
  · exact hx5
  · rfl
  · exact hx7
  · exact hx8
  · rfl
  · rfl

theorem state_satisfies_core : ∀ a b c : Fin 3, Core (state a b c) := by
  unfold Core state
  decide +kernel

theorem unique_good_state : ∀ a b c : Fin 3,
    Good (state a b c) ↔ a=2 ∧ b=1 ∧ c=0 := by
  unfold Good ins outs codes state
  decide +kernel


end R03CoreBranchV7

open R03CoreBranchV7
theorem solution : ∀ v : Fin 9, BadAt (state 0 0 2) v ↔ v=7 := by
  unfold BadAt ins outs codes state
  decide +kernel
