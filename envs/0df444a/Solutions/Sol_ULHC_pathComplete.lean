-- Prove2me | solution 1 for ULHC.pathComplete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:47:55.800845+00:00
-- url     : https://prove2.me/submissions/5a5b3ac6-7c9a-48bd-9a93-84949242e504

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_comp_clean
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_swap
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_conn_of_ncomp_one
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_even_strip_count
import Theorems.Thm_ULHC_exists_not_conn
import Theorems.Thm_ULHC_mem_GE
import Theorems.Thm_ULHC_one_strip
import Theorems.Thm_ULHC_t3_link
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) : PathComplete V := by
  suffices h : ∀ m (G : Finset Edge), mu V G H = m → Deg2 V G → NoTypeIII V G → 2 ≤ ncomp V G →
      ∃ σ L, CRPathCA V G σ L from fun G hG hT h2 => h _ G rfl hG hT h2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G hm hG hT h2
  obtain ⟨x0, hx0, _, _, _⟩ := exists_not_conn h2
  have hconn : ∀ z ∈ V, Conn (GE V) x0 z := fun z hz =>
    (conn_of_ncomp_one hHam hx0 hz).mono (fun e he => mem_GE.2 (hH.1 e he))
  obtain ⟨σ, hv, hn, hmu⟩ := one_strip hs hH hHam hG hT h2
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
  swap
  · exact ⟨σ, [], ⟨hv, hodd⟩, trivial⟩
  obtain ⟨c, d, n⟩ := σ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by simp only at hn; omega⟩
  have hk : k % 2 = 0 := by simp only at hev; omega
  obtain ⟨_, hpat, hcellS, hsep⟩ := hv
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j) := fun j hj => hcellS j (by simp only; omega)
  by_cases hT' : NoTypeIII V (flipCol G c d (k + 2))
  · have hF : Deg2 V (flipCol G c d (k + 2)) := deg2_flipCol (k + 2) G hG hpat hcellS
    have hcnt := even_strip_count hG hT ⟨by simp only; omega, hpat, hcellS, hsep⟩ hev
    change ncomp V (flipCol G c d (k + 2)) = ncomp V G at hcnt
    change mu V (flipCol G c d (k + 2)) H + 2 * (k + 2) = mu V G H at hmu
    have hex := ih _ (by omega) _ rfl hF hT' (by omega)
    classical
    have hP : ∃ w, ∃ σ' L', CRPathCA V (flipCol G c d (k + 2)) σ' L' ∧ wt σ' L' = w := by
      obtain ⟨σ', L', h⟩ := hex; exact ⟨_, σ', L', h, rfl⟩
    obtain ⟨q, L, hQ, hw⟩ := Nat.find_spec hP
    exact comp_clean hs x0 hconn hG hT hk hcell hpat hsep hT' hQ (fun σ' L' h' => by
      rw [hw]; exact Nat.find_min' hP ⟨σ', L', h', rfl⟩)
  · obtain ⟨τ, hτ1, hl, hok⟩ := t3_link hG hT hk hcell hpat hsep hT'
    exact ⟨_, [τ], ⟨⟨by simp only; omega, hpat, hcellS, hsep⟩, hev, hl, show τ.n % 2 = 1 by rw [hτ1]⟩, hok, trivial⟩
end ULHC
