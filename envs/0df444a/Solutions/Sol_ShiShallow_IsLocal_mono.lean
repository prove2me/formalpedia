-- Prove2me | solution 1 for ShiShallow.IsLocal.mono
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:46:25.65109+00:00
-- url     : https://prove2.me/submissions/8ce7f16f-0125-4f56-9ef4-db38c2bce864

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit
import Definitions.Def_ShiShallow_Operator

section
open ShiShallow

theorem solution {n : ℕ} {S S' : Finset (Fin n)} {A : Op n} (hSS : S ⊆ S')
    (h : IsLocal S A) : IsLocal S' A := by
  have out : ∀ {k : Fin n}, k ∉ S' → k ∉ S := fun {_} hk hk' => hk (hSS hk')
  refine ⟨fun y z hne => h.vanish (fun hag => hne (fun k hk => hag k (out hk))),
    fun y z y' z' hy hz hyz hyz' => ?_⟩
  have hequiv : (∀ k, k ∉ S → y k = z k) ↔ (∀ k, k ∉ S → y' k = z' k) := by
    constructor
    · intro hag k hk
      by_cases hk' : k ∈ S'
      · rw [← hy k hk', ← hz k hk']; exact hag k hk
      · exact hyz' k hk'
    · intro hag k hk
      by_cases hk' : k ∈ S'
      · rw [hy k hk', hz k hk']; exact hag k hk
      · exact hyz k hk'
  by_cases hoff : ∀ k, k ∉ S → y k = z k
  · exact h.entry_congr (fun k hk => hy k (hSS hk)) (fun k hk => hz k (hSS hk))
      hoff (hequiv.1 hoff)
  · rw [h.vanish hoff, h.vanish (fun hc => hoff (hequiv.2 hc))]

end
