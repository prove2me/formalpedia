-- Prove2me | solution 1 for ULHC.start_not_behind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:23:40.606019+00:00
-- url     : https://prove2.me/submissions/21109b35-b587-4a53-83cf-9a0566fbdaea

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_start_frame
import Theorems.Thm_P2M_ULHC_body_not_alt__d3691623e2ed
import Theorems.Thm_ULHC_perp_x
import Theorems.Thm_ULHC_u_across
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_down
import Theorems.Thm_ULHC_back_down2
import Theorems.Thm_ULHC_behind_up
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_front_nb_opp


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
include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu
namespace ULHC
theorem _root_.solution (hd : d = nb c s.opp) : False := by
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have d1 := back_down hF hT hpat (by omega) hc0 hsep
  have d2 := back_down2 hF hT hpat (by omega) hc0 hsep
  have df : front d s ∈ F := by rw [hd, front_nb_opp]; exact hpat.1
  rw [← hd] at d1 d2
  rcases start_frame s hb hxl with ⟨_, hdiff⟩ | ⟨ht, _, hbf⟩
  · exact (hdiff.1 d1) d2
  · have hbF : back d s ∉ F := fun h => hbf.1 h df
    have hxf : x = front d s := by
      rcases perp_x hxlat ht with h | h
      · exact absurd (h ▸ hxd) hbF
      · exact h
    have hu' := u_across hxu hdu hxf
    rw [hd, behind_up] at hu'
    rw [hu', ← cellJ_zero c s] at lu1 lu2 bu fu
    exact body_not_alt' hk hpat (j := 0) (by omega) lu1 lu2 bu fu
end ULHC
