-- Prove2me | solution 1 for ResourceScheduling.Graph.emit_cell_safe
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:22.261512+00:00
-- url     : https://prove2.me/submissions/bdf79a37-5d5f-4b05-9e89-13bb94137e7b

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_if_eq_safe
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s) (hpos : 1 ≤ B) :
    RAMSafe emitCell B s := by
  let P := fun x : RAMState GraphReg => x.val num = 0
  have hd : ∀ x a, P x → P (x.set delta a) := by intro x a hx; simpa [P, RAMState.set] using hx
  have ha : ∀ x a, P x → P (x.set aux a) := by intro x a hx; simpa [P, RAMState.set] using hx
  have hinc : ∀ x, RAMBound B x → P x → RAMSafe (.inc num : Code) B x := by
    intro x hx hP
    exact ⟨hx, ram_bound_set B x hx num _ (by dsimp [P] at hP; omega)⟩
  have hskip : ∀ x, RAMBound B x → P x → RAMSafe (.skip : Code) B x := fun _ hx _ => ⟨hx,hx⟩
  let q := ifEq k j (.inc num) .skip
  have hq : ∀ x, RAMBound B x → P x → RAMSafe q B x :=
    fun x hx hP => if_eq_safe k j (.inc num) .skip B P hd ha hinc hskip x hx hP
  let p := ifEq k i (.inc num) q
  let x := s.set num 0
  have hx : RAMBound B x := ram_bound_set B s hs num 0 (Nat.zero_le _)
  have hp : RAMSafe p B x := if_eq_safe k i (.inc num) q B P hd ha hinc hq x hx
    (by simp [P, x, RAMState.set])
  have hemit : RAMSafe (.emit num : Code) B (p.eval x) := ⟨hp.2,hp.2⟩
  have hend := (ram_safe_laws (.emit num) .skip n B (p.eval x)).2.1 hemit ⟨hemit.2,hemit.2⟩
  have hmid := (ram_safe_laws p ((RAMCode.emit num).seq .skip) n B x).2.1 hp hend
  exact (ram_safe_laws (.zero num) (p.seq ((RAMCode.emit num).seq .skip)) n B s).2.1 ⟨hs,hx⟩ hmid

#print axioms solution
