-- Prove2me | solution 1 for RHHeight1000.close_from_656_intervals_and_gram
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:00:54.317152+00:00
-- url     : https://prove2.me/submissions/59caa15a-4be9-42da-adfd-2f7addef2c46

import Definitions.Def_RHT1000_Support_20261118_S005

/- Based on the finite-height certificate of Salvatore Mercuri and Bhavik Mehta. -/
open Zeta.Certificates

theorem FiniteHeightPortable.close
    (hGram : ∃ G : CertifiedGramBlockSeq, G.minIdx = 655 ∧ G.blocks.length = 11 ∧
      (G.blocks.head G.non_empty).left.fst = (1009.14258 : ℝ))
    (hzeros : BatchSpec 656 1000 1000 1008988 1000)
    (s : ℂ) (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hi : |s.im| ≤ 1000) : s.re = 1 / 2 := by
  obtain ⟨G, hidx, _, hleft⟩ := hGram
  have hhead := G.head_left_le_gramPoint
  rw [hleft] at hhead
  have hcount : G.minIdx + 1 = 656 := by rw [hidx]
  have hbelow : Enclosure.sfrac false 1008988 1000 ≤ gramPoint G.minIdx :=
    le_trans (by norm_num [Enclosure.sfrac] :
      Enclosure.sfrac false 1008988 1000 ≤ (1009.14258 : ℝ)) hhead
  have rh := riemannHypothesisUpTo_of_batchSpec G hzeros hcount hbelow
  refine rh s hz ?_ ?_ (by linarith)
  · rintro ⟨n, rfl⟩
    norm_num [Complex.mul_re, Complex.mul_im] at h0
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    simp at h1

theorem solution : (∃ G : Zeta.Certificates.CertifiedGramBlockSeq, G.minIdx = 655 ∧ G.blocks.length = 11 ∧ (G.blocks.head G.non_empty).left.fst = (1009.14258 : ℝ)) → Zeta.Certificates.BatchSpec 656 1000 1000 1008988 1000 → ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → |s.im| ≤ 1000 → s.re = 1 / 2 := FiniteHeightPortable.close
#print axioms solution
