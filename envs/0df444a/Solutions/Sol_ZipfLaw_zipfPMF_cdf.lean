-- Prove2me | solution 1 for ZipfLaw.zipfPMF_cdf
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:39.280029+00:00
-- url     : https://prove2.me/submissions/9668ee27-9b34-4aea-9b15-071c25184569

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (n : ℕ) (hn : n ≤ N) :
    ∑ k ∈ Finset.Icc 1 n, zipfPMF N s k = genHarmonic n s / genHarmonic N s := by
  rw [genHarmonic, Finset.sum_div]
  exact Finset.sum_congr rfl (fun k hk => by
    rw [zipfPMF, if_pos ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 hn⟩])

#print axioms solution

