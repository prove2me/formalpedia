-- Prove2me | solution 1 for P2M_Egrs75_MoveDigits_mem_badIndexSet_iff__e33fc9bbbd0e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:37.454173+00:00
-- url     : https://prove2.me/submissions/2a12c154-a1e7-4f03-aec1-3bb02b541562

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.MoveDigits
theorem _root_.solution {q n i : ℕ} (hq : 1 < q) :
    i ∈ badIndexSet q n ↔ BadAt q i n := by
  unfold BadAt digitAt badIndexSet
  simp only [Finset.mem_filter, Finset.mem_range, bigQ, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hbig⟩
    rwa [getD_digits n i (by omega)] at hbig
  · intro hbig
    have hlen : i < (Nat.digits q n).length := by
      by_contra hcon
      push Not at hcon
      rw [← getD_digits n i (by omega), List.getD_eq_default _ 0 hcon] at hbig
      omega
    refine ⟨hlen, ?_⟩
    rwa [getD_digits n i (by omega)]
end Egrs75.MoveDigits
