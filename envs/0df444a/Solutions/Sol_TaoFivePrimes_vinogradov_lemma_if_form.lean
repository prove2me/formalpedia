-- Prove2me | solution 1 for TaoFivePrimes.vinogradov_lemma_if_form
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:48:09.618973+00:00
-- url     : https://prove2.me/submissions/290514f9-a72e-4376-acc3-2cc879b55e0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TaoFivePrimes_vinogradov_block_if_form
import Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block

open Finset

theorem solution (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' u v : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (huv : u < v) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :=
  TaoFivePrimes.vinogradov_lemma_if_form_from_block B hB q hq A' alpha' theta' u v hA' huv
    (fun m => TaoFivePrimes.vinogradov_block_if_form B hB q hq A' alpha' beta' theta' a'
      hA' halpha' hbeta' m)
