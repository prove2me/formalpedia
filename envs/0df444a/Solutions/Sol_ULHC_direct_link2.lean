-- Prove2me | solution 1 for ULHC.direct_link2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:17:15.874749+00:00
-- url     : https://prove2.me/submissions/658f7c48-6fb8-475c-a758-8f124953b6cd

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_endCell_mk2
import Theorems.Thm_ULHC_besideB_not_mem
import Theorems.Thm_ULHC_besideB_ne
import Theorems.Thm_ULHC_besideB_not_mid
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hk : k % 2 = 0) {σ τ : StripSpec} (hl : CR2 V G σ τ)
    (hσe : endCell σ = cellJ c s (k + 1)) (hd : τ.c = nb (cellJ c s (k + 1)) (latB s))
    (ht : τ.s = s ∨ (τ.s = s.opp ∧ τ.n = 1)) : CR2 V G ⟨c, s, k + 2⟩ τ := by
  obtain ⟨_, _, h1, hp, hc, _, _, _, _, _, hcg, hcu⟩ := hl
  rw [hσe] at hp hcu
  have hcellτ : ∀ j < τ.n, cellJ τ.c τ.s j = cellJ (nb (cellJ c s (k + 1)) (latB s)) s j := by
    intro j hj
    rcases ht with h | ⟨h, h1'⟩
    · rw [hd, h]
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero, cellJ_zero, hd]
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, h1, hp, hc, fun j hj i hi x hx => ?_, fun j hj => ?_, fun hev x hx => ?_,
    ?_, ?_, hcg, hcu⟩
  · rw [hcellτ j hj] at hx
    exact besideB_not_mem c s (show i < k + 1 by simp only at hi; omega) hx
  · rw [hcellτ j hj, endCell_mk2]; exact besideB_ne c s _ _ _
  · rcases ht with h | ⟨_, h1'⟩
    · have hn : 2 ≤ τ.n := by omega
      unfold endCell at hx; rw [hcellτ _ (by omega), show k + 1 + 0 = k + 1 from rfl] at hx
      rw [endCell_mk2]
      have : cellJ (nb (cellJ c s (k + 1)) (latB s)) s (τ.n - 1) =
          cellJ (nb (cellJ c s (k + 1 + (τ.n - 1))) (latB s)) s 0 := by
        obtain ⟨p, q⟩ := c; cases s <;> simp [nb, latB, cellJ] <;> omega
      rw [this] at hx
      exact besideB_not_mem c s (show k + 1 < k + 1 + (τ.n - 1) by omega) hx
    · omega
  · rw [show k + 2 - 2 = k from rfl, hd]
    exact (besideB_not_mid c s k (ht.elim Or.inl (fun h => Or.inr h.1))).1
  · rw [show k + 2 - 2 = k from rfl, hd]
    exact (besideB_not_mid c s k (ht.elim Or.inl (fun h => Or.inr h.1))).2
end ULHC
