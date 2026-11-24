-- Prove2me | solution 1 for Psi.areaAux_eq_areaH
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:30:23.187109+00:00
-- url     : https://prove2.me/submissions/294e4bcb-5fe0-45e7-be55-e955c279f1a6

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (i e : ℕ) (le : Bool)
    (hle : e ≤ i) (hv : validFrom p ((i : Int) - e)) :
    (areaAux p i e le : Int) = areaH p ((i : Int) - e) le := by
  induction p generalizing i e le with
  | nil => simp [areaAux, areaH]
  | cons a t ih =>
    cases a with
    | true =>
      simp only [areaAux, areaH, validFrom] at *
      have hcast : ((if le then i - e else 0 : ℕ) : Int) = (if le then ((i:Int) - e) else 0) := by
        cases le <;> simp [Int.ofNat_sub hle]
      rw [Nat.cast_add, hcast]
      have key := ih (i+1) e false (by omega)
        (by rw [Nat.cast_add, Nat.cast_one, show (i:Int)+1-↑e = ((i:Int)-↑e)+1 from by ring]; exact hv)
      rw [key, show ((i+1:ℕ):Int) - ↑e = ((i:Int)-↑e)+1 from by push_cast; ring]
    | false =>
      simp only [areaAux, areaH, validFrom] at *
      obtain ⟨hpos, hv2⟩ := hv
      have hei : e + 1 ≤ i := by have : (0:Int) < (i:Int) - e := hpos; omega
      have hv2' : validFrom t ((i:Int) - ↑(e+1)) := by
        push_cast; rw [show (i:Int)-(↑e+1)=(i:Int)-↑e-1 from by ring]; exact hv2
      rw [ih i (e+1) true hei hv2', show (i:Int)-(↑(e+1))=(i:Int)-↑e-1 from by push_cast; ring]
end Psi
