-- Prove2me | solution 1 for SCCThm8.cntRank_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:05.104016+00:00
-- url     : https://prove2.me/submissions/93a1adc7-7799-406d-9b96-ea4ab039a14d

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} (v : Finset (Fin n)) {i j : Fin n} (h : i < j) :
    cntRank v i ≤ cntRank v j := by
  unfold cntRank
  exact card_le_card fun x hx => by
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩
end SCCThm8
