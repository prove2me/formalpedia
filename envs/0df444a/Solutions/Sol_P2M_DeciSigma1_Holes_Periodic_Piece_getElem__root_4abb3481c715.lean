-- Prove2me | solution 1 for P2M_DeciSigma1_Holes_Periodic_Piece_getElem__root_4abb3481c715
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:44.824724+00:00
-- url     : https://prove2.me/submissions/1ee34c3a-f815-4f79-a2d1-1883765d5554

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_len_ge
public import Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_Piece_getElem__eq_of_mod_eddd45ef4561
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic.Piece
theorem _root_.solution (P : Piece W d) {o : ℕ} (h : o < P.len) :
    (W P.coordinate)[P.start + o]? = P.root[o % d]? := by
  have hd := P.period_pos
  rw [P.getElem?_eq_of_mod h (by have := P.len_ge; have := Nat.mod_lt o hd; omega)
    (Nat.mod_mod o d).symm]
  unfold root
  rw [List.getElem?_take_of_lt (Nat.mod_lt _ hd), List.getElem?_drop]
end DeciSigma1.Holes.Periodic.Piece
