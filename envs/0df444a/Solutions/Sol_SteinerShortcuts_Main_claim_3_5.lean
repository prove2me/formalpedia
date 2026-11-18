-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:19:45.610098+00:00
-- url     : https://prove2.me/submissions/60533d4f-8acf-4118-9a44-944697755f23

import Definitions.Def_SteinerShortcuts_Main_TestFunctions
open SteinerShortcuts.Main

private theorem layer_counters (L q ell : ℕ) (scale : ℤ) (v : Point)
    (hv : v ∈ layerBox L q ell scale) :
    v 0 = (ell:ℤ) ∧ v 1 = ((ell / 2 : ℕ):ℤ) ∧
      v 2 = (((ell-1)/2:ℕ):ℤ) := by
  have hm := Fintype.mem_piFinset.mp hv
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  norm_num [Fin.ext_iff] at h0 h1 h2
  exact ⟨h0,h1,h2⟩

private theorem vertex_counters (L q : ℕ) (v : Point) (hv : v ∈ vertices L q) :
    v 1 = v 0 / 2 ∧ v 2 = (v 0 - 1) / 2 := by
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases layer_counters L q 1 1 v hv with ⟨h0,h1,h2⟩
    norm_num [h0, h1, h2]
  · rcases Finset.mem_biUnion.mp hv with ⟨ell, hell, hv⟩
    rcases layer_counters L q ell 2 v hv with ⟨h0,h1,h2⟩
    have he : 1 ≤ ell := by have := (Finset.mem_Icc.mp hell).1; omega
    simp [h0, h1, h2, Int.natCast_ediv, Nat.cast_sub he]

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    (P.a ≠ Q.a → T3prime L q (testROdd P Q)) ∧
    (P.b ≠ Q.b → T3prime L q (testREven P Q)) := by
  constructor
  · intro ha
    let d : ℝ := (Q.a.val:ℝ) - (P.a.val:ℝ)
    let x : ℝ := P.source 3
    let y : ℝ := Q.source 3
    refine ⟨![0,0,0,0,0,0,0,0,0,0,0,0,
      -(x+y)/d/d, -((P.a.val:ℝ)+(Q.a.val:ℝ))/d/d, 1/d/d,
      0,0,0,0,0,0],
      fun ell => if ell % 2 = 1 then
        (x + (P.a.val:ℝ)*((ell/2:ℤ):ℝ)) *
          (y + (Q.a.val:ℝ)*((ell/2:ℤ):ℝ))/d/d else 0, ?_⟩
    intro v hv t
    have hc := vertex_counters L q v hv
    by_cases ho : v 0 % 2 = 1
    · simp [testROdd, ha, position, update, ho, psi, Fin.sum_univ_succ]
      rw [hc.1]
      push_cast
      dsimp [x,y,d]
      ring
    · simp [testROdd, ha, position, update, ho, Fin.sum_univ_succ]
  · intro hb
    let d : ℝ := (Q.b.val:ℝ) - (P.b.val:ℝ)
    let x : ℝ := P.source 7
    let y : ℝ := Q.source 7
    refine ⟨![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
      -(x+y)/d/d, -((P.b.val:ℝ)+(Q.b.val:ℝ))/d/d, 1/d/d,
      0,0,0],
      fun ell => if ell % 2 = 0 then
        (x + (P.b.val:ℝ)*(((ell-1)/2:ℤ):ℝ)) *
          (y + (Q.b.val:ℝ)*(((ell-1)/2:ℤ):ℝ))/d/d else 0, ?_⟩
    intro v hv t
    have hc := vertex_counters L q v hv
    by_cases ho : v 0 % 2 = 1
    · have he : v 0 % 2 ≠ 0 := by omega
      simp [testREven, hb, position, update, ho, he, Fin.sum_univ_succ]
    · have he : v 0 % 2 = 0 := by omega
      simp [testREven, hb, position, update, ho, he, psi, Fin.sum_univ_succ]
      rw [hc.2]
      push_cast
      dsimp [x,y,d]
      ring
