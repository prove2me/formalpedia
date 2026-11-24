-- Prove2me | solution 1 for TaoFivePrimes.clbZ_table_bounds
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-29T12:57:45.56267+00:00
-- url     : https://prove2.me/submissions/6ee2b72c-7cf6-43fa-9c69-7bd07eb1bab6

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log

open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

open TaoFivePrimes

private lemma clbZ_pos_aux (p : Nat) (hp : p ∈ pl521) : 0 < clbZ p := by
  simp only [pl521, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide

  · decide



private lemma lum_le_log_aux (p : Nat) (hp : p ∈ pl521) :
    ((clbZ p : Nat) : Real)/10000 ≤ Real.log (p : Real) := by
  simp only [pl521, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ((clbZ 2 : Nat) : Real) ≤ Real.log ((2 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 2 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (2 : Nat) ∈ plist1))))
    have hc' : ((clbZ 2 : Nat) : Real) ≤ Real.log ((2 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 3 : Nat) : Real) ≤ Real.log ((3 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 3 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (3 : Nat) ∈ plist1))))
    have hc' : ((clbZ 3 : Nat) : Real) ≤ Real.log ((3 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 5 : Nat) : Real) ≤ Real.log ((5 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 5 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (5 : Nat) ∈ plist1))))
    have hc' : ((clbZ 5 : Nat) : Real) ≤ Real.log ((5 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 7 : Nat) : Real) ≤ Real.log ((7 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 7 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (7 : Nat) ∈ plist1))))
    have hc' : ((clbZ 7 : Nat) : Real) ≤ Real.log ((7 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 11 : Nat) : Real) ≤ Real.log ((11 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 11 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (11 : Nat) ∈ plist1))))
    have hc' : ((clbZ 11 : Nat) : Real) ≤ Real.log ((11 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 13 : Nat) : Real) ≤ Real.log ((13 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 13 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (13 : Nat) ∈ plist1))))
    have hc' : ((clbZ 13 : Nat) : Real) ≤ Real.log ((13 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 17 : Nat) : Real) ≤ Real.log ((17 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 17 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (17 : Nat) ∈ plist1))))
    have hc' : ((clbZ 17 : Nat) : Real) ≤ Real.log ((17 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 19 : Nat) : Real) ≤ Real.log ((19 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 19 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (19 : Nat) ∈ plist1))))
    have hc' : ((clbZ 19 : Nat) : Real) ≤ Real.log ((19 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 23 : Nat) : Real) ≤ Real.log ((23 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 23 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (23 : Nat) ∈ plist1))))
    have hc' : ((clbZ 23 : Nat) : Real) ≤ Real.log ((23 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 29 : Nat) : Real) ≤ Real.log ((29 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 29 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (29 : Nat) ∈ plist1))))
    have hc' : ((clbZ 29 : Nat) : Real) ≤ Real.log ((29 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 31 : Nat) : Real) ≤ Real.log ((31 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 31 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (31 : Nat) ∈ plist1))))
    have hc' : ((clbZ 31 : Nat) : Real) ≤ Real.log ((31 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 37 : Nat) : Real) ≤ Real.log ((37 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 37 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (37 : Nat) ∈ plist1))))
    have hc' : ((clbZ 37 : Nat) : Real) ≤ Real.log ((37 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 41 : Nat) : Real) ≤ Real.log ((41 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 41 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (41 : Nat) ∈ plist1))))
    have hc' : ((clbZ 41 : Nat) : Real) ≤ Real.log ((41 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 43 : Nat) : Real) ≤ Real.log ((43 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 43 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (43 : Nat) ∈ plist1))))
    have hc' : ((clbZ 43 : Nat) : Real) ≤ Real.log ((43 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 47 : Nat) : Real) ≤ Real.log ((47 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 47 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (47 : Nat) ∈ plist1))))
    have hc' : ((clbZ 47 : Nat) : Real) ≤ Real.log ((47 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 53 : Nat) : Real) ≤ Real.log ((53 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 53 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (53 : Nat) ∈ plist1))))
    have hc' : ((clbZ 53 : Nat) : Real) ≤ Real.log ((53 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 59 : Nat) : Real) ≤ Real.log ((59 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 59 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (59 : Nat) ∈ plist1))))
    have hc' : ((clbZ 59 : Nat) : Real) ≤ Real.log ((59 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 61 : Nat) : Real) ≤ Real.log ((61 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 61 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (61 : Nat) ∈ plist1))))
    have hc' : ((clbZ 61 : Nat) : Real) ≤ Real.log ((61 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 67 : Nat) : Real) ≤ Real.log ((67 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 67 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (67 : Nat) ∈ plist1))))
    have hc' : ((clbZ 67 : Nat) : Real) ≤ Real.log ((67 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 71 : Nat) : Real) ≤ Real.log ((71 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 71 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (71 : Nat) ∈ plist1))))
    have hc' : ((clbZ 71 : Nat) : Real) ≤ Real.log ((71 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 73 : Nat) : Real) ≤ Real.log ((73 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 73 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (73 : Nat) ∈ plist1))))
    have hc' : ((clbZ 73 : Nat) : Real) ≤ Real.log ((73 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 79 : Nat) : Real) ≤ Real.log ((79 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 79 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (79 : Nat) ∈ plist1))))
    have hc' : ((clbZ 79 : Nat) : Real) ≤ Real.log ((79 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 83 : Nat) : Real) ≤ Real.log ((83 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 83 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (83 : Nat) ∈ plist1))))
    have hc' : ((clbZ 83 : Nat) : Real) ≤ Real.log ((83 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 89 : Nat) : Real) ≤ Real.log ((89 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 89 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (89 : Nat) ∈ plist1))))
    have hc' : ((clbZ 89 : Nat) : Real) ≤ Real.log ((89 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 97 : Nat) : Real) ≤ Real.log ((97 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 97 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (97 : Nat) ∈ plist1))))
    have hc' : ((clbZ 97 : Nat) : Real) ≤ Real.log ((97 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 101 : Nat) : Real) ≤ Real.log ((101 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 101 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (101 : Nat) ∈ plist1))))
    have hc' : ((clbZ 101 : Nat) : Real) ≤ Real.log ((101 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 103 : Nat) : Real) ≤ Real.log ((103 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 103 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (103 : Nat) ∈ plist1))))
    have hc' : ((clbZ 103 : Nat) : Real) ≤ Real.log ((103 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 107 : Nat) : Real) ≤ Real.log ((107 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 107 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (107 : Nat) ∈ plist1))))
    have hc' : ((clbZ 107 : Nat) : Real) ≤ Real.log ((107 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 109 : Nat) : Real) ≤ Real.log ((109 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 109 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (109 : Nat) ∈ plist1))))
    have hc' : ((clbZ 109 : Nat) : Real) ≤ Real.log ((109 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 113 : Nat) : Real) ≤ Real.log ((113 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 113 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (113 : Nat) ∈ plist1))))
    have hc' : ((clbZ 113 : Nat) : Real) ≤ Real.log ((113 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 127 : Nat) : Real) ≤ Real.log ((127 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 127 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (127 : Nat) ∈ plist1))))
    have hc' : ((clbZ 127 : Nat) : Real) ≤ Real.log ((127 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 131 : Nat) : Real) ≤ Real.log ((131 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 131 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (131 : Nat) ∈ plist1))))
    have hc' : ((clbZ 131 : Nat) : Real) ≤ Real.log ((131 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 137 : Nat) : Real) ≤ Real.log ((137 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 137 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (137 : Nat) ∈ plist1))))
    have hc' : ((clbZ 137 : Nat) : Real) ≤ Real.log ((137 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 139 : Nat) : Real) ≤ Real.log ((139 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 139 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (139 : Nat) ∈ plist1))))
    have hc' : ((clbZ 139 : Nat) : Real) ≤ Real.log ((139 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 149 : Nat) : Real) ≤ Real.log ((149 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 149 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (149 : Nat) ∈ plist1))))
    have hc' : ((clbZ 149 : Nat) : Real) ≤ Real.log ((149 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 151 : Nat) : Real) ≤ Real.log ((151 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 151 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (151 : Nat) ∈ plist1))))
    have hc' : ((clbZ 151 : Nat) : Real) ≤ Real.log ((151 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 157 : Nat) : Real) ≤ Real.log ((157 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 157 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (157 : Nat) ∈ plist1))))
    have hc' : ((clbZ 157 : Nat) : Real) ≤ Real.log ((157 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 163 : Nat) : Real) ≤ Real.log ((163 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 163 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (163 : Nat) ∈ plist1))))
    have hc' : ((clbZ 163 : Nat) : Real) ≤ Real.log ((163 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 167 : Nat) : Real) ≤ Real.log ((167 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 167 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (167 : Nat) ∈ plist1))))
    have hc' : ((clbZ 167 : Nat) : Real) ≤ Real.log ((167 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 173 : Nat) : Real) ≤ Real.log ((173 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 173 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (173 : Nat) ∈ plist1))))
    have hc' : ((clbZ 173 : Nat) : Real) ≤ Real.log ((173 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 179 : Nat) : Real) ≤ Real.log ((179 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 179 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (179 : Nat) ∈ plist1))))
    have hc' : ((clbZ 179 : Nat) : Real) ≤ Real.log ((179 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 181 : Nat) : Real) ≤ Real.log ((181 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 181 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (181 : Nat) ∈ plist1))))
    have hc' : ((clbZ 181 : Nat) : Real) ≤ Real.log ((181 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 191 : Nat) : Real) ≤ Real.log ((191 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 191 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (191 : Nat) ∈ plist1))))
    have hc' : ((clbZ 191 : Nat) : Real) ≤ Real.log ((191 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 193 : Nat) : Real) ≤ Real.log ((193 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 193 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (193 : Nat) ∈ plist1))))
    have hc' : ((clbZ 193 : Nat) : Real) ≤ Real.log ((193 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 197 : Nat) : Real) ≤ Real.log ((197 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 197 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (197 : Nat) ∈ plist1))))
    have hc' : ((clbZ 197 : Nat) : Real) ≤ Real.log ((197 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 199 : Nat) : Real) ≤ Real.log ((199 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 199 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (199 : Nat) ∈ plist1))))
    have hc' : ((clbZ 199 : Nat) : Real) ≤ Real.log ((199 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 211 : Nat) : Real) ≤ Real.log ((211 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 211 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (211 : Nat) ∈ plist1))))
    have hc' : ((clbZ 211 : Nat) : Real) ≤ Real.log ((211 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 223 : Nat) : Real) ≤ Real.log ((223 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 223 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (223 : Nat) ∈ plist1))))
    have hc' : ((clbZ 223 : Nat) : Real) ≤ Real.log ((223 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 227 : Nat) : Real) ≤ Real.log ((227 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 227 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (227 : Nat) ∈ plist1))))
    have hc' : ((clbZ 227 : Nat) : Real) ≤ Real.log ((227 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 229 : Nat) : Real) ≤ Real.log ((229 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 229 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (229 : Nat) ∈ plist1))))
    have hc' : ((clbZ 229 : Nat) : Real) ≤ Real.log ((229 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 233 : Nat) : Real) ≤ Real.log ((233 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 233 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (233 : Nat) ∈ plist1))))
    have hc' : ((clbZ 233 : Nat) : Real) ≤ Real.log ((233 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 239 : Nat) : Real) ≤ Real.log ((239 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 239 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (239 : Nat) ∈ plist1))))
    have hc' : ((clbZ 239 : Nat) : Real) ≤ Real.log ((239 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 241 : Nat) : Real) ≤ Real.log ((241 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 241 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (241 : Nat) ∈ plist1))))
    have hc' : ((clbZ 241 : Nat) : Real) ≤ Real.log ((241 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 251 : Nat) : Real) ≤ Real.log ((251 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 251 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (251 : Nat) ∈ plist1))))
    have hc' : ((clbZ 251 : Nat) : Real) ≤ Real.log ((251 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 257 : Nat) : Real) ≤ Real.log ((257 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 257 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (257 : Nat) ∈ plist1))))
    have hc' : ((clbZ 257 : Nat) : Real) ≤ Real.log ((257 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 263 : Nat) : Real) ≤ Real.log ((263 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 263 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (263 : Nat) ∈ plist2))))
    have hc' : ((clbZ 263 : Nat) : Real) ≤ Real.log ((263 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 269 : Nat) : Real) ≤ Real.log ((269 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 269 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (269 : Nat) ∈ plist2))))
    have hc' : ((clbZ 269 : Nat) : Real) ≤ Real.log ((269 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 271 : Nat) : Real) ≤ Real.log ((271 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 271 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (271 : Nat) ∈ plist2))))
    have hc' : ((clbZ 271 : Nat) : Real) ≤ Real.log ((271 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 277 : Nat) : Real) ≤ Real.log ((277 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 277 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (277 : Nat) ∈ plist2))))
    have hc' : ((clbZ 277 : Nat) : Real) ≤ Real.log ((277 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 281 : Nat) : Real) ≤ Real.log ((281 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 281 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (281 : Nat) ∈ plist2))))
    have hc' : ((clbZ 281 : Nat) : Real) ≤ Real.log ((281 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 283 : Nat) : Real) ≤ Real.log ((283 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 283 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (283 : Nat) ∈ plist2))))
    have hc' : ((clbZ 283 : Nat) : Real) ≤ Real.log ((283 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 293 : Nat) : Real) ≤ Real.log ((293 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 293 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (293 : Nat) ∈ plist2))))
    have hc' : ((clbZ 293 : Nat) : Real) ≤ Real.log ((293 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 307 : Nat) : Real) ≤ Real.log ((307 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 307 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (307 : Nat) ∈ plist2))))
    have hc' : ((clbZ 307 : Nat) : Real) ≤ Real.log ((307 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 311 : Nat) : Real) ≤ Real.log ((311 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 311 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (311 : Nat) ∈ plist2))))
    have hc' : ((clbZ 311 : Nat) : Real) ≤ Real.log ((311 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 313 : Nat) : Real) ≤ Real.log ((313 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 313 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (313 : Nat) ∈ plist2))))
    have hc' : ((clbZ 313 : Nat) : Real) ≤ Real.log ((313 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 317 : Nat) : Real) ≤ Real.log ((317 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 317 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (317 : Nat) ∈ plist2))))
    have hc' : ((clbZ 317 : Nat) : Real) ≤ Real.log ((317 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 331 : Nat) : Real) ≤ Real.log ((331 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 331 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (331 : Nat) ∈ plist2))))
    have hc' : ((clbZ 331 : Nat) : Real) ≤ Real.log ((331 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 337 : Nat) : Real) ≤ Real.log ((337 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 337 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (337 : Nat) ∈ plist2))))
    have hc' : ((clbZ 337 : Nat) : Real) ≤ Real.log ((337 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 347 : Nat) : Real) ≤ Real.log ((347 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 347 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (347 : Nat) ∈ plist2))))
    have hc' : ((clbZ 347 : Nat) : Real) ≤ Real.log ((347 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 349 : Nat) : Real) ≤ Real.log ((349 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 349 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (349 : Nat) ∈ plist2))))
    have hc' : ((clbZ 349 : Nat) : Real) ≤ Real.log ((349 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 353 : Nat) : Real) ≤ Real.log ((353 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 353 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (353 : Nat) ∈ plist2))))
    have hc' : ((clbZ 353 : Nat) : Real) ≤ Real.log ((353 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 359 : Nat) : Real) ≤ Real.log ((359 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 359 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (359 : Nat) ∈ plist2))))
    have hc' : ((clbZ 359 : Nat) : Real) ≤ Real.log ((359 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 367 : Nat) : Real) ≤ Real.log ((367 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 367 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (367 : Nat) ∈ plist2))))
    have hc' : ((clbZ 367 : Nat) : Real) ≤ Real.log ((367 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 373 : Nat) : Real) ≤ Real.log ((373 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 373 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (373 : Nat) ∈ plist2))))
    have hc' : ((clbZ 373 : Nat) : Real) ≤ Real.log ((373 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 379 : Nat) : Real) ≤ Real.log ((379 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 379 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (379 : Nat) ∈ plist2))))
    have hc' : ((clbZ 379 : Nat) : Real) ≤ Real.log ((379 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 383 : Nat) : Real) ≤ Real.log ((383 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 383 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (383 : Nat) ∈ plist2))))
    have hc' : ((clbZ 383 : Nat) : Real) ≤ Real.log ((383 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 389 : Nat) : Real) ≤ Real.log ((389 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 389 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (389 : Nat) ∈ plist2))))
    have hc' : ((clbZ 389 : Nat) : Real) ≤ Real.log ((389 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 397 : Nat) : Real) ≤ Real.log ((397 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 397 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (397 : Nat) ∈ plist2))))
    have hc' : ((clbZ 397 : Nat) : Real) ≤ Real.log ((397 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 401 : Nat) : Real) ≤ Real.log ((401 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 401 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (401 : Nat) ∈ plist2))))
    have hc' : ((clbZ 401 : Nat) : Real) ≤ Real.log ((401 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 409 : Nat) : Real) ≤ Real.log ((409 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 409 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (409 : Nat) ∈ plist2))))
    have hc' : ((clbZ 409 : Nat) : Real) ≤ Real.log ((409 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 419 : Nat) : Real) ≤ Real.log ((419 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 419 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (419 : Nat) ∈ plist2))))
    have hc' : ((clbZ 419 : Nat) : Real) ≤ Real.log ((419 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 421 : Nat) : Real) ≤ Real.log ((421 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 421 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (421 : Nat) ∈ plist2))))
    have hc' : ((clbZ 421 : Nat) : Real) ≤ Real.log ((421 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 431 : Nat) : Real) ≤ Real.log ((431 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 431 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (431 : Nat) ∈ plist2))))
    have hc' : ((clbZ 431 : Nat) : Real) ≤ Real.log ((431 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 433 : Nat) : Real) ≤ Real.log ((433 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 433 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (433 : Nat) ∈ plist2))))
    have hc' : ((clbZ 433 : Nat) : Real) ≤ Real.log ((433 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 439 : Nat) : Real) ≤ Real.log ((439 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 439 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (439 : Nat) ∈ plist2))))
    have hc' : ((clbZ 439 : Nat) : Real) ≤ Real.log ((439 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 443 : Nat) : Real) ≤ Real.log ((443 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 443 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (443 : Nat) ∈ plist2))))
    have hc' : ((clbZ 443 : Nat) : Real) ≤ Real.log ((443 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 449 : Nat) : Real) ≤ Real.log ((449 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 449 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (449 : Nat) ∈ plist2))))
    have hc' : ((clbZ 449 : Nat) : Real) ≤ Real.log ((449 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 457 : Nat) : Real) ≤ Real.log ((457 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 457 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (457 : Nat) ∈ plist2))))
    have hc' : ((clbZ 457 : Nat) : Real) ≤ Real.log ((457 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 461 : Nat) : Real) ≤ Real.log ((461 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 461 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (461 : Nat) ∈ plist2))))
    have hc' : ((clbZ 461 : Nat) : Real) ≤ Real.log ((461 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 463 : Nat) : Real) ≤ Real.log ((463 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 463 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (463 : Nat) ∈ plist2))))
    have hc' : ((clbZ 463 : Nat) : Real) ≤ Real.log ((463 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 467 : Nat) : Real) ≤ Real.log ((467 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 467 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (467 : Nat) ∈ plist2))))
    have hc' : ((clbZ 467 : Nat) : Real) ≤ Real.log ((467 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 479 : Nat) : Real) ≤ Real.log ((479 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 479 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (479 : Nat) ∈ plist2))))
    have hc' : ((clbZ 479 : Nat) : Real) ≤ Real.log ((479 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 487 : Nat) : Real) ≤ Real.log ((487 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 487 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (487 : Nat) ∈ plist2))))
    have hc' : ((clbZ 487 : Nat) : Real) ≤ Real.log ((487 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 491 : Nat) : Real) ≤ Real.log ((491 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 491 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (491 : Nat) ∈ plist2))))
    have hc' : ((clbZ 491 : Nat) : Real) ≤ Real.log ((491 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 499 : Nat) : Real) ≤ Real.log ((499 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 499 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (499 : Nat) ∈ plist2))))
    have hc' : ((clbZ 499 : Nat) : Real) ≤ Real.log ((499 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 503 : Nat) : Real) ≤ Real.log ((503 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 503 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (503 : Nat) ∈ plist2))))
    have hc' : ((clbZ 503 : Nat) : Real) ≤ Real.log ((503 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 509 : Nat) : Real) ≤ Real.log ((509 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 509 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (509 : Nat) ∈ plist2))))
    have hc' : ((clbZ 509 : Nat) : Real) ≤ Real.log ((509 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'

  · have hc : ((clbZ 521 : Nat) : Real) ≤ Real.log ((521 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 521 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (521 : Nat) ∈ plist2))))
    have hc' : ((clbZ 521 : Nat) : Real) ≤ Real.log ((521 : Nat) : Real) * 10000 := by
      simpa only [show (10:Real)^4 = 10000 by norm_num] using hc
    rw [div_le_iff₀ (by norm_num : (0:Real) < 10000)]
    exact hc'



theorem solution (p : Nat) (hp : p ∈ pl521) :
    0 < clbZ p ∧ ((clbZ p : Nat) : Real)/10000 ≤ Real.log (p : Real) :=
  ⟨clbZ_pos_aux p hp, lum_le_log_aux p hp⟩
