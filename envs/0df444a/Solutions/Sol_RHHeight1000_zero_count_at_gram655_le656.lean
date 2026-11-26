-- Prove2me | solution 1 for RHHeight1000.zero_count_at_gram655_le656
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T18:23:13.453817+00:00
-- url     : https://prove2.me/submissions/dcfbddc0-51ba-4493-a099-81aaebb83bcd

import Theorems.Thm_RHHeight1000_certified_gram_sequence_655
import Definitions.Def_RHT1000_Support_20261118_S003
set_option Elab.async false
theorem solution : riemannZeta.N (gramPoint 655) ≤ 656 := by
  obtain ⟨C, hC, _hlen, _hhead⟩ := RHHeight1000.certified_gram_sequence_655
  have h := riemannZeta.N_le_of_certifiedGramBlockSeq C
  norm_num [hC] at h
  exact h
#print axioms solution
