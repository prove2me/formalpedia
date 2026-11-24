-- Prove2me | solution 1 for ULHC.link_of_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:21:14.696854+00:00
-- url     : https://prove2.me/submissions/e090a89c-96e3-427d-8284-291c369c5273

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_flipCol_off
import Theorems.Thm_ULHC_stripPat_congr
import Theorems.Thm_ULHC_strip_even_rel


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d))
include hG hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution {q : StripSpec} (hq1 : 1 ≤ q.n)
    (hpatF : StripPat (flipCol G c d (k + 2)) q.c q.s q.n)
    (hcq : ∀ j < q.n, IsCell V (cellJ q.c q.s j)) (hso : SideOff ⟨c, d, k + 2⟩ q)
    (hne : ∀ j < q.n, cellJ q.c q.s j ≠ cellJ c d (k + 1))
    (hen : q.n % 2 = 0 → ∀ x ∈ cellE (endCell q), x ∉ cellE (cellJ c d (k + 1)))
    (hm1 : ¬ IsMid c d k (back1 q.c q.s)) (hm2 : ¬ IsMid c d k (front1 q.c q.s))
    (hcg : Conn G (back1 q.c q.s) (front1 q.c q.s))
    (hsepF : ¬ Conn (flipCol G c d (k + 2)) (back1 q.c q.s) (front1 q.c q.s)) :
    CR2 V G ⟨c, d, k + 2⟩ q := by
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ :=
    strip_even_rel k hk G hG hcell hpat hsep (end_same hT hk hcell hpat)
  obtain ⟨m, hm⟩ : ∃ m, q.n = m + 1 := ⟨q.n - 1, by omega⟩
  have hpat' : StripPat (flip G (cellJ c d (k + 1))) q.c q.s q.n := by
    rw [hm] at hpatF ⊢
    refine (stripPat_congr (fun j hj y hy => ?_)).2 hpatF
    exact (flipCol_off G c d (k + 1) (fun i hi => hso j (by omega) i hi y hy)).symm
  refine ⟨by show 2 ≤ k + 2; omega, by show (k + 2) % 2 = 0; omega, hq1, hpat', hcq, hso, hne,
    hen, hm1, hm2, hcg, fun h => hsepF ((hodd _ _ hm1 hm2).2 (Or.inl (hF1 ▸ h)))⟩
end ULHC
