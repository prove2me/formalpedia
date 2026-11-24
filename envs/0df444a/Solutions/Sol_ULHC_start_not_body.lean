-- Prove2me | solution 1 for ULHC.start_not_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:16:57.623113+00:00
-- url     : https://prove2.me/submissions/3e9085f6-937d-420c-bba9-1375c0bac47e

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_start_frame
import Theorems.Thm_P2M_ULHC_body_not_alt__d3691623e2ed
import Theorems.Thm_ULHC_perp_x
import Theorems.Thm_ULHC_u_across
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_strip_sig


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {d u : Pt} {tf tu : Side} {x : Edge}
  (hb : back d tf ∈ F) (hxd : x ∈ F) (hxlat : x = lat1 d tf ∨ x = lat2 d tf)
  (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F))
  (lu1 : lat1 u tu ∈ F) (lu2 : lat2 u tu ∈ F) (bu : back u tu ∉ F) (fu : front u tu ∉ F)
  (hxu : x ∈ cellE u) (hdu : d ≠ u)
include hk hpat hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k + 1) (hd : d = cellJ c s j) : False := by
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  rw [← hd] at a1 a2 ab af
  rcases start_frame s hb hxl with ⟨_, hdiff⟩ | ⟨ht, hlat, hbf⟩
  · rw [a1, a2] at hdiff; omega
  · by_cases hjk : j = k + 1
    · subst hjk
      rw [ab, af] at hbf; omega
    · have hodd : j % 2 = 1 := by rcases hlat with h | h; exacts [a1.1 h, a2.1 h]
      have hbF : back d s ∉ F := fun h => by have := ab.1 h; omega
      have hxf : x = front d s := by
        rcases perp_x hxlat ht with h | h
        · exact absurd (h ▸ hxd) hbF
        · exact h
      have hu' := u_across hxu hdu hxf
      rw [hd, nb_cellJ] at hu'
      rw [hu'] at lu1 lu2 bu fu
      exact body_not_alt' hk hpat (j := j + 1) (by omega) lu1 lu2 bu fu
end ULHC
