-- Prove2me | solution 1 for P2M_DeciSigma1_Holes_Periodic_AdmissibleDeletion_getElem__imagePiece_5b6104921581
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:46.76617+00:00
-- url     : https://prove2.me/submissions/61fb56a4-3bf2-474e-b0f3-7e9cc2b4bc20

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution (P : Piece W ρ.length) {o : ℕ}
    (ho : o < retainedLength (N := N) (x := x) P) :
    (editedTuple W ρ N x P.coordinate)[(hx.imagePiece P).start + o]? =
        (W P.coordinate)[P.start + o]? := hx.getElem?_new P ho
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
