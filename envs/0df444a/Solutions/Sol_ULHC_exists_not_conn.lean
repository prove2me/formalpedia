-- Prove2me | solution 1 for ULHC.exists_not_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:33.657966+00:00
-- url     : https://prove2.me/submissions/fda9f5cd-615d-49ed-91ea-276bce3cfaa7

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cls_eq_of_conn


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h2 : 2 ≤ ncomp V F) :
    ∃ x ∈ V, ∃ y ∈ V, ¬ Conn F x y := by
  by_contra hall
  push Not at hall
  have : (V.image (cls V F)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro A hA B hB
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hB
    exact cls_eq_of_conn (hall x hx y hy)
  unfold ncomp at h2
  omega
end ULHC
