-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.OrderStream.field_size_spec
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:09:59.939567+00:00
-- url     : https://prove2.me/submissions/0ccf136d-18ff-4d36-b877-81c07db19b56

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream
set_option maxHeartbeats 1600000
open scoped Classical

theorem solution (m : ℕ) : (fieldSize m).Prime ∧ 8193 ≤ fieldSize m ∧ 4*m^2 ≤ fieldSize m ∧ fieldSize m ≤ 2*lower m := by
  classical
  obtain ⟨r,rp,hr,rb⟩ := Nat.exists_prime_lt_and_le_two_mul (lower m) (by simp [lower])
  have hex : ∃ j, (lower m ≤ j ∧ Nat.Prime j) := ⟨r,hr.le,rp⟩
  let p := Nat.find hex
  have good : lower m ≤ p ∧ p.Prime := Nat.find_spec hex
  have pr : p ≤ r := Nat.find_min' hex ⟨hr.le,rp⟩
  have uniq (j : ℕ) : (Nat.Prime j ∧ lower m ≤ j ∧ (∀k < j,lower m ≤ k → ¬Nat.Prime k)) ↔ j=p := by
    constructor
    · rintro ⟨a,b,c⟩
      exact le_antisymm (le_of_not_gt (fun h => c p h good.1 good.2)) (Nat.find_min' hex ⟨b,a⟩)
    · rintro rfl
      exact ⟨good.2,good.1,fun k h lk pk => Nat.find_min hex h ⟨lk,pk⟩⟩
  have f : fieldSize m=p := by
    simp only [fieldSize,uniq]
    simp [Finset.mem_range,show p < 2*lower m+1 by omega]
  rw [f]
  have h := good.1
  unfold lower at h
  exact ⟨good.2,by omega,by omega,pr.trans rb⟩

