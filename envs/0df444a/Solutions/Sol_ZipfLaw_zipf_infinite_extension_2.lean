-- Prove2me | solution 2 for ZipfLaw.zipf_infinite_extension
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:34:14.39296+00:00
-- url     : https://prove2.me/submissions/864ba4aa-33c5-4a50-8698-4eb1a78c4b18

import Theorems.Thm_ZipfLaw_zipf_summable_iff
import Theorems.Thm_ZipfLaw_zipf_genHarmonic_tendsto_zeta
import Theorems.Thm_ZipfLaw_zipf_genHarmonic_tendsto_atTop
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    (Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s) ∧
      (1 < s → Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
        (nhds (riemannZeta s))) ∧
      (s ≤ 1 → Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop) := by
  exact ⟨zipf_summable_iff s hs,
    fun hs1 => zipf_genHarmonic_tendsto_zeta s hs1,
    fun hs1 => zipf_genHarmonic_tendsto_atTop s hs hs1⟩

#print axioms solution
