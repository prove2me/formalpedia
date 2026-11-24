-- Prove2me | solution 1 for ULHC.seq_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:31:55.050951+00:00
-- url     : https://prove2.me/submissions/c13fcaf2-60f3-4122-9f3f-806abf7d278f

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_even_strip_count
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_strip_odd
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} :
    ∀ (L : List StripSpec) (F : Finset Edge), Deg2 V F → ValidSeq V F L →
      ncomp V (applySeq F L) + 1 = ncomp V F := by
  intro L
  induction L with
  | nil => intro F _ h; exact h.elim
  | cons σ L ih =>
    intro F hF hv
    rcases L with _ | ⟨τ, L⟩
    · obtain ⟨⟨hn, hpat, hcell, hsep⟩, hodd⟩ := hv
      obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 1 := ⟨σ.n - 1, by omega⟩
      simp only [applySeq, applyS]
      rw [hk] at hpat hcell ⊢
      exact (strip_odd k (by omega) F hF (fun j hj => hcell j (by omega)) hpat hsep).1
    · obtain ⟨⟨hn, hpat, hcell, hsep⟩, hev, hT, hrest⟩ := hv
      obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
      have hF' : Deg2 V (applyS F σ) := deg2_flipCol _ F hF hpat hcell
      have := ih (applyS F σ) hF' hrest
      simp only [applySeq] at this ⊢
      rw [this]
      exact even_strip_count hF hT ⟨hn, hpat, hcell, hsep⟩ hev
end ULHC
