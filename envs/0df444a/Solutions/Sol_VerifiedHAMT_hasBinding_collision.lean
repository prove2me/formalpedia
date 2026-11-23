-- Prove2me | solution 1 for VerifiedHAMT.hasBinding_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:25:31.297073+00:00
-- url     : https://prove2.me/submissions/a8d4d9be-6c45-4b33-95d1-166382c00a55

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} {key : α} {value : β} :
    HasBinding key value (.collision keys vals hsz) ↔
      ∃ (i : Nat) (hi : i < keys.size), keys[i] = key ∧ vals[i]'(hsz ▸ hi) = value := by
  constructor
  · intro h; cases h with | collision hi hk hv => exact ⟨_, hi, hk, hv⟩
  · rintro ⟨i, hi, hk, hv⟩; exact .collision hi hk hv
end VerifiedHAMT
