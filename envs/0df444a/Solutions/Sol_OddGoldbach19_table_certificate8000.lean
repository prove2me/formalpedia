-- Prove2me | solution 1 for OddGoldbach19.table_certificate8000
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:49:36.15811+00:00
-- url     : https://prove2.me/submissions/b90f608e-5c9e-4964-86f3-563f57864f1c

import Theorems.Thm_OddGoldbach19_table_block8000_0
import Theorems.Thm_OddGoldbach19_table_block8000_1
import Theorems.Thm_OddGoldbach19_table_block8000_2
import Theorems.Thm_OddGoldbach19_table_block8000_3
import Theorems.Thm_OddGoldbach19_table_block8000_4
set_option autoImplicit false
theorem solution (d : ℕ) (hd : d<40909) :
    OddGoldbach19.Cert8000.WC d≤OddGoldbach19.Cert8000.WP d := by
  by_cases h0 : d<10000
  · exact OddGoldbach19.table_block8000_0 d (by omega) h0
  by_cases h1 : d<20000
  · exact OddGoldbach19.table_block8000_1 d (by omega) h1
  by_cases h2 : d<30000
  · exact OddGoldbach19.table_block8000_2 d (by omega) h2
  by_cases h3 : d<40000
  · exact OddGoldbach19.table_block8000_3 d (by omega) h3
  exact OddGoldbach19.table_block8000_4 d (by omega) hd
#print axioms solution
