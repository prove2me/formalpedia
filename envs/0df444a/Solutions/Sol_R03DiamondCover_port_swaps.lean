-- Prove2me | solution 1 for R03DiamondCover.port_swaps
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:27:29.059131+00:00
-- url     : https://prove2.me/submissions/e3412d28-ed0b-4fe0-b664-ed637e776078

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_09e80204d5_R03DiamondCover_v1

/- Candidate-only exact finite relations and arbitrary finite chain induction.
   The relation's interpretation as a physical diamond cover, switching-class
   classification and graph connectivity are separate graph proof candidates. -/
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 100000
namespace R03DiamondCover

theorem two_diamonds : ∀ a b c d : Fin 3,
    Compose Diamond Diamond a b c d ↔ Full 2 a b c d := by
  unfold Compose Diamond Full forbidden
  decide +kernel

theorem full_step : ∀ r a b c d : Fin 3,
    Compose (Full r) Diamond a b c d ↔ Full (r+1) a b c d := by
  unfold Compose Diamond Full forbidden
  decide +kernel

theorem long_chain (n : Nat) : ∀ a b c d : Fin 3,
    Chain (n+1) a b c d ↔ Full (phase n) a b c d := by
  induction n with
  | zero => exact two_diamonds
  | succ n ih =>
    intro a b c d
    change (∃ x y : Fin 3, Chain (n+1) a b x y ∧ Diamond (2*x) (2*y) c d) ↔
      Full (phase n+1) a b c d
    constructor
    · rintro ⟨x,y,hx,hy⟩
      exact (full_step (phase n) a b c d).mp ⟨x,y,(ih a b x y).mp hx,hy⟩
    · intro h
      obtain ⟨x,y,hx,hy⟩ := (full_step (phase n) a b c d).mpr h
      exact ⟨x,y,(ih a b x y).mpr hx,hy⟩

theorem phase_period (n : Nat) : phase (n+3)=phase n := by
  have h : ∀ r : Fin 3, r+1+1+1=r := by decide +kernel
  exact h (phase n)


end R03DiamondCover

open R03DiamondCover
theorem solution : ∀ a b c d : Fin 3,
    (Diamond a b c d ↔ Diamond b a c d) ∧
    (Diamond a b c d ↔ Diamond a b d c) := by
  unfold Diamond forbidden
  decide +kernel
