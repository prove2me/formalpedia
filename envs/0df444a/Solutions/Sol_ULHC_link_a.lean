-- Prove2me | solution 1 for ULHC.link_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:39:03.278974+00:00
-- url     : https://prove2.me/submissions/3d9973bc-3cf5-4d34-b038-d7359ca150fd

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_pat_flip_off
import Theorems.Thm_ULHC_start_corner_edges
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mid_touch
import Theorems.Thm_ULHC_side_mem_self


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hG : Deg2 V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
include hG ha hae ha2
namespace ULHC
theorem _root_.solution {w : StripSpec} (hw1 : 1 ≤ w.n) (hpw : StripPat G w.c w.s w.n)
    (hcw : ∀ j < w.n, IsCell V (cellJ w.c w.s j)) (hnt : ¬ Touches a w)
    (hcg : Conn G (back1 w.c w.s) (front1 w.c w.s))
    (hcu : ¬ Conn (flip G (endCell a)) (back1 w.c w.s) (front1 w.c w.s)) : CR2 V G a w := by
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  obtain ⟨_, hpa, hca, _⟩ := ha
  rw [hk] at hpa hca
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hoff : ∀ j < w.n, ∀ i < a.n, ∀ x ∈ cellE (cellJ w.c w.s j), x ∉ cellE (cellJ a.c a.s i) :=
    fun j hj i hi x hx hx' => hnt ⟨j, hj, i, hi, x, hx, hx'⟩
  have hend : endCell a = cellJ a.c a.s (a.n - 1) := rfl
  have hmid : ∀ p, (∃ j < w.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ w.c w.s j)) →
      ¬ IsMid a.c a.s (a.n - 2) p := by
    rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
    rw [hk, show k + 2 - 2 = k by omega] at hm
    obtain ⟨i, hi, hxi⟩ := mid_touch hG hpa hcell hm hx hxp
    exact hoff j hj i (by omega) x hxw hxi
  obtain ⟨⟨hb, hbp, hb0⟩, hfr⟩ := start_corner_edges hpw hw1
  refine ⟨ha2, hae, hw1, (pat_flip_off hw1 (fun j hj x hx => by
      rw [hend]; exact hoff j hj _ (by omega) x hx)).2 hpw, hcw,
    fun j hj i hi x hx => hoff j hj i (by omega) x hx, ?_, ?_,
    hmid _ ⟨0, by omega, _, hb, hbp, hb0⟩, hmid _ hfr, hcg, hcu⟩
  · intro j hj heq
    have := side_mem_self (cellJ w.c w.s j) .b
    exact hoff j hj (a.n - 1) (by omega) _ this (by rw [← hend, ← heq]; exact this)
  · intro _ x hx
    rw [hend]; exact hoff _ (by omega) _ (by omega) x hx
end ULHC
