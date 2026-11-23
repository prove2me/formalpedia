-- Prove2me | solution 1 for VerifiedHAMT.HasBinding.hasKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:25:26.896559+00:00
-- url     : https://prove2.me/submissions/83f10c0c-dd87-4d21-9b03-baa738252e6c

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
namespace HasBinding
theorem _root_.solution {key : α} {value : β} {node : Node α β}
    (hb : HasBinding key value node) : HasKey key node := by
  induction hb with
  | entry h => exact .entry h
  | ref h _ ih => exact .ref h ih
  | collision hi hk _ => exact .collision (Array.mem_iff_getElem.mpr ⟨_, hi, hk⟩)
end HasBinding
end VerifiedHAMT
