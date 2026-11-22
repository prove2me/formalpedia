-- Prove2me | solution 1 for P2M_DeciSigma1_Holes_Periodic_getElem__eq_of_root_eq_400ed337ec00
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:51.174601+00:00
-- url     : https://prove2.me/submissions/260b7731-76d3-4b0b-946a-bc7e8515d032

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_len_ge
public import Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_Piece_getElem__root_4abb3481c715


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
variable [DecidableEq α] {W : Fin k → List α} {d : ℕ}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (P Q : Piece W d) (h : P.root = Q.root) :
    ∀ t < d, t < P.len - 0 → (W P.coordinate)[P.start + 0 + t]? =
        (W Q.coordinate)[Q.start + 0 + t]? := by
  intro t ht _
  have hP := P.getElem?_root (o := t) (by have := P.len_ge; omega)
  have hQ := Q.getElem?_root (o := t) (by have := Q.len_ge; omega)
  rw [Nat.add_zero, Nat.add_zero, hP, hQ, h]
end DeciSigma1.Holes.Periodic
