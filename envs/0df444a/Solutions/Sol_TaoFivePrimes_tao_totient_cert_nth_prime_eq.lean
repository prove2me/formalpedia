-- Prove2me | solution 1 for TaoFivePrimes.tao_totient_cert_nth_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T20:46:34.900176+00:00
-- url     : https://prove2.me/submissions/6a27d6f7-fb24-45fa-9607-a2694c65aadb

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Count
import Mathlib.NumberTheory.PrimeCounting
import Definitions.Def_TaoFivePrimes_totient_cert_tables
import Mathlib.Tactic
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false

namespace TaoFivePrimes

lemma cnt_0 : Nat.count Nat.Prime 0 = 0 := by decide
lemma cnt_1 : Nat.count Nat.Prime 1 = 0 := by
  rw [show (1:ℕ) = 0 + 1 by norm_num, Nat.count_succ, cnt_0]
  norm_num
lemma cnt_2 : Nat.count Nat.Prime 2 = 0 := by
  rw [show (2:ℕ) = 1 + 1 by norm_num, Nat.count_succ, cnt_1]
  norm_num
lemma cnt_3 : Nat.count Nat.Prime 3 = 1 := by
  rw [show (3:ℕ) = 2 + 1 by norm_num, Nat.count_succ, cnt_2]
  norm_num
lemma cnt_4 : Nat.count Nat.Prime 4 = 2 := by
  rw [show (4:ℕ) = 3 + 1 by norm_num, Nat.count_succ, cnt_3]
  norm_num
lemma cnt_5 : Nat.count Nat.Prime 5 = 2 := by
  rw [show (5:ℕ) = 4 + 1 by norm_num, Nat.count_succ, cnt_4]
  norm_num
lemma cnt_6 : Nat.count Nat.Prime 6 = 3 := by
  rw [show (6:ℕ) = 5 + 1 by norm_num, Nat.count_succ, cnt_5]
  norm_num
lemma cnt_7 : Nat.count Nat.Prime 7 = 3 := by
  rw [show (7:ℕ) = 6 + 1 by norm_num, Nat.count_succ, cnt_6]
  norm_num
lemma cnt_8 : Nat.count Nat.Prime 8 = 4 := by
  rw [show (8:ℕ) = 7 + 1 by norm_num, Nat.count_succ, cnt_7]
  norm_num
lemma cnt_9 : Nat.count Nat.Prime 9 = 4 := by
  rw [show (9:ℕ) = 8 + 1 by norm_num, Nat.count_succ, cnt_8]
  norm_num
lemma cnt_10 : Nat.count Nat.Prime 10 = 4 := by
  rw [show (10:ℕ) = 9 + 1 by norm_num, Nat.count_succ, cnt_9]
  norm_num
lemma cnt_11 : Nat.count Nat.Prime 11 = 4 := by
  rw [show (11:ℕ) = 10 + 1 by norm_num, Nat.count_succ, cnt_10]
  norm_num
lemma cnt_12 : Nat.count Nat.Prime 12 = 5 := by
  rw [show (12:ℕ) = 11 + 1 by norm_num, Nat.count_succ, cnt_11]
  norm_num
lemma cnt_13 : Nat.count Nat.Prime 13 = 5 := by
  rw [show (13:ℕ) = 12 + 1 by norm_num, Nat.count_succ, cnt_12]
  norm_num
lemma cnt_14 : Nat.count Nat.Prime 14 = 6 := by
  rw [show (14:ℕ) = 13 + 1 by norm_num, Nat.count_succ, cnt_13]
  norm_num
lemma cnt_15 : Nat.count Nat.Prime 15 = 6 := by
  rw [show (15:ℕ) = 14 + 1 by norm_num, Nat.count_succ, cnt_14]
  norm_num
lemma cnt_16 : Nat.count Nat.Prime 16 = 6 := by
  rw [show (16:ℕ) = 15 + 1 by norm_num, Nat.count_succ, cnt_15]
  norm_num
lemma cnt_17 : Nat.count Nat.Prime 17 = 6 := by
  rw [show (17:ℕ) = 16 + 1 by norm_num, Nat.count_succ, cnt_16]
  norm_num
lemma cnt_18 : Nat.count Nat.Prime 18 = 7 := by
  rw [show (18:ℕ) = 17 + 1 by norm_num, Nat.count_succ, cnt_17]
  norm_num
lemma cnt_19 : Nat.count Nat.Prime 19 = 7 := by
  rw [show (19:ℕ) = 18 + 1 by norm_num, Nat.count_succ, cnt_18]
  norm_num
lemma cnt_20 : Nat.count Nat.Prime 20 = 8 := by
  rw [show (20:ℕ) = 19 + 1 by norm_num, Nat.count_succ, cnt_19]
  norm_num
lemma cnt_21 : Nat.count Nat.Prime 21 = 8 := by
  rw [show (21:ℕ) = 20 + 1 by norm_num, Nat.count_succ, cnt_20]
  norm_num
lemma cnt_22 : Nat.count Nat.Prime 22 = 8 := by
  rw [show (22:ℕ) = 21 + 1 by norm_num, Nat.count_succ, cnt_21]
  norm_num
lemma cnt_23 : Nat.count Nat.Prime 23 = 8 := by
  rw [show (23:ℕ) = 22 + 1 by norm_num, Nat.count_succ, cnt_22]
  norm_num
lemma cnt_24 : Nat.count Nat.Prime 24 = 9 := by
  rw [show (24:ℕ) = 23 + 1 by norm_num, Nat.count_succ, cnt_23]
  norm_num
lemma cnt_25 : Nat.count Nat.Prime 25 = 9 := by
  rw [show (25:ℕ) = 24 + 1 by norm_num, Nat.count_succ, cnt_24]
  norm_num
lemma cnt_26 : Nat.count Nat.Prime 26 = 9 := by
  rw [show (26:ℕ) = 25 + 1 by norm_num, Nat.count_succ, cnt_25]
  norm_num
lemma cnt_27 : Nat.count Nat.Prime 27 = 9 := by
  rw [show (27:ℕ) = 26 + 1 by norm_num, Nat.count_succ, cnt_26]
  norm_num
lemma cnt_28 : Nat.count Nat.Prime 28 = 9 := by
  rw [show (28:ℕ) = 27 + 1 by norm_num, Nat.count_succ, cnt_27]
  norm_num
lemma cnt_29 : Nat.count Nat.Prime 29 = 9 := by
  rw [show (29:ℕ) = 28 + 1 by norm_num, Nat.count_succ, cnt_28]
  norm_num
lemma cnt_30 : Nat.count Nat.Prime 30 = 10 := by
  rw [show (30:ℕ) = 29 + 1 by norm_num, Nat.count_succ, cnt_29]
  norm_num
lemma cnt_31 : Nat.count Nat.Prime 31 = 10 := by
  rw [show (31:ℕ) = 30 + 1 by norm_num, Nat.count_succ, cnt_30]
  norm_num
lemma cnt_32 : Nat.count Nat.Prime 32 = 11 := by
  rw [show (32:ℕ) = 31 + 1 by norm_num, Nat.count_succ, cnt_31]
  norm_num
lemma cnt_33 : Nat.count Nat.Prime 33 = 11 := by
  rw [show (33:ℕ) = 32 + 1 by norm_num, Nat.count_succ, cnt_32]
  norm_num
lemma cnt_34 : Nat.count Nat.Prime 34 = 11 := by
  rw [show (34:ℕ) = 33 + 1 by norm_num, Nat.count_succ, cnt_33]
  norm_num
lemma cnt_35 : Nat.count Nat.Prime 35 = 11 := by
  rw [show (35:ℕ) = 34 + 1 by norm_num, Nat.count_succ, cnt_34]
  norm_num
lemma cnt_36 : Nat.count Nat.Prime 36 = 11 := by
  rw [show (36:ℕ) = 35 + 1 by norm_num, Nat.count_succ, cnt_35]
  norm_num
lemma cnt_37 : Nat.count Nat.Prime 37 = 11 := by
  rw [show (37:ℕ) = 36 + 1 by norm_num, Nat.count_succ, cnt_36]
  norm_num
lemma cnt_38 : Nat.count Nat.Prime 38 = 12 := by
  rw [show (38:ℕ) = 37 + 1 by norm_num, Nat.count_succ, cnt_37]
  norm_num
lemma cnt_39 : Nat.count Nat.Prime 39 = 12 := by
  rw [show (39:ℕ) = 38 + 1 by norm_num, Nat.count_succ, cnt_38]
  norm_num
lemma cnt_40 : Nat.count Nat.Prime 40 = 12 := by
  rw [show (40:ℕ) = 39 + 1 by norm_num, Nat.count_succ, cnt_39]
  norm_num
lemma cnt_41 : Nat.count Nat.Prime 41 = 12 := by
  rw [show (41:ℕ) = 40 + 1 by norm_num, Nat.count_succ, cnt_40]
  norm_num
lemma cnt_42 : Nat.count Nat.Prime 42 = 13 := by
  rw [show (42:ℕ) = 41 + 1 by norm_num, Nat.count_succ, cnt_41]
  norm_num
lemma cnt_43 : Nat.count Nat.Prime 43 = 13 := by
  rw [show (43:ℕ) = 42 + 1 by norm_num, Nat.count_succ, cnt_42]
  norm_num
lemma cnt_44 : Nat.count Nat.Prime 44 = 14 := by
  rw [show (44:ℕ) = 43 + 1 by norm_num, Nat.count_succ, cnt_43]
  norm_num
lemma cnt_45 : Nat.count Nat.Prime 45 = 14 := by
  rw [show (45:ℕ) = 44 + 1 by norm_num, Nat.count_succ, cnt_44]
  norm_num
lemma cnt_46 : Nat.count Nat.Prime 46 = 14 := by
  rw [show (46:ℕ) = 45 + 1 by norm_num, Nat.count_succ, cnt_45]
  norm_num
lemma cnt_47 : Nat.count Nat.Prime 47 = 14 := by
  rw [show (47:ℕ) = 46 + 1 by norm_num, Nat.count_succ, cnt_46]
  norm_num
lemma cnt_48 : Nat.count Nat.Prime 48 = 15 := by
  rw [show (48:ℕ) = 47 + 1 by norm_num, Nat.count_succ, cnt_47]
  norm_num
lemma cnt_49 : Nat.count Nat.Prime 49 = 15 := by
  rw [show (49:ℕ) = 48 + 1 by norm_num, Nat.count_succ, cnt_48]
  norm_num
lemma cnt_50 : Nat.count Nat.Prime 50 = 15 := by
  rw [show (50:ℕ) = 49 + 1 by norm_num, Nat.count_succ, cnt_49]
  norm_num
lemma cnt_51 : Nat.count Nat.Prime 51 = 15 := by
  rw [show (51:ℕ) = 50 + 1 by norm_num, Nat.count_succ, cnt_50]
  norm_num
lemma cnt_52 : Nat.count Nat.Prime 52 = 15 := by
  rw [show (52:ℕ) = 51 + 1 by norm_num, Nat.count_succ, cnt_51]
  norm_num
lemma cnt_53 : Nat.count Nat.Prime 53 = 15 := by
  rw [show (53:ℕ) = 52 + 1 by norm_num, Nat.count_succ, cnt_52]
  norm_num
lemma cnt_54 : Nat.count Nat.Prime 54 = 16 := by
  rw [show (54:ℕ) = 53 + 1 by norm_num, Nat.count_succ, cnt_53]
  norm_num
lemma cnt_55 : Nat.count Nat.Prime 55 = 16 := by
  rw [show (55:ℕ) = 54 + 1 by norm_num, Nat.count_succ, cnt_54]
  norm_num
lemma cnt_56 : Nat.count Nat.Prime 56 = 16 := by
  rw [show (56:ℕ) = 55 + 1 by norm_num, Nat.count_succ, cnt_55]
  norm_num
lemma cnt_57 : Nat.count Nat.Prime 57 = 16 := by
  rw [show (57:ℕ) = 56 + 1 by norm_num, Nat.count_succ, cnt_56]
  norm_num
lemma cnt_58 : Nat.count Nat.Prime 58 = 16 := by
  rw [show (58:ℕ) = 57 + 1 by norm_num, Nat.count_succ, cnt_57]
  norm_num
lemma cnt_59 : Nat.count Nat.Prime 59 = 16 := by
  rw [show (59:ℕ) = 58 + 1 by norm_num, Nat.count_succ, cnt_58]
  norm_num
lemma cnt_60 : Nat.count Nat.Prime 60 = 17 := by
  rw [show (60:ℕ) = 59 + 1 by norm_num, Nat.count_succ, cnt_59]
  norm_num
lemma cnt_61 : Nat.count Nat.Prime 61 = 17 := by
  rw [show (61:ℕ) = 60 + 1 by norm_num, Nat.count_succ, cnt_60]
  norm_num
lemma cnt_62 : Nat.count Nat.Prime 62 = 18 := by
  rw [show (62:ℕ) = 61 + 1 by norm_num, Nat.count_succ, cnt_61]
  norm_num
lemma cnt_63 : Nat.count Nat.Prime 63 = 18 := by
  rw [show (63:ℕ) = 62 + 1 by norm_num, Nat.count_succ, cnt_62]
  norm_num
lemma cnt_64 : Nat.count Nat.Prime 64 = 18 := by
  rw [show (64:ℕ) = 63 + 1 by norm_num, Nat.count_succ, cnt_63]
  norm_num
lemma cnt_65 : Nat.count Nat.Prime 65 = 18 := by
  rw [show (65:ℕ) = 64 + 1 by norm_num, Nat.count_succ, cnt_64]
  norm_num
lemma cnt_66 : Nat.count Nat.Prime 66 = 18 := by
  rw [show (66:ℕ) = 65 + 1 by norm_num, Nat.count_succ, cnt_65]
  norm_num
lemma cnt_67 : Nat.count Nat.Prime 67 = 18 := by
  rw [show (67:ℕ) = 66 + 1 by norm_num, Nat.count_succ, cnt_66]
  norm_num
lemma cnt_68 : Nat.count Nat.Prime 68 = 19 := by
  rw [show (68:ℕ) = 67 + 1 by norm_num, Nat.count_succ, cnt_67]
  norm_num
lemma cnt_69 : Nat.count Nat.Prime 69 = 19 := by
  rw [show (69:ℕ) = 68 + 1 by norm_num, Nat.count_succ, cnt_68]
  norm_num
lemma cnt_70 : Nat.count Nat.Prime 70 = 19 := by
  rw [show (70:ℕ) = 69 + 1 by norm_num, Nat.count_succ, cnt_69]
  norm_num
lemma cnt_71 : Nat.count Nat.Prime 71 = 19 := by
  rw [show (71:ℕ) = 70 + 1 by norm_num, Nat.count_succ, cnt_70]
  norm_num
lemma cnt_72 : Nat.count Nat.Prime 72 = 20 := by
  rw [show (72:ℕ) = 71 + 1 by norm_num, Nat.count_succ, cnt_71]
  norm_num
lemma cnt_73 : Nat.count Nat.Prime 73 = 20 := by
  rw [show (73:ℕ) = 72 + 1 by norm_num, Nat.count_succ, cnt_72]
  norm_num
lemma cnt_74 : Nat.count Nat.Prime 74 = 21 := by
  rw [show (74:ℕ) = 73 + 1 by norm_num, Nat.count_succ, cnt_73]
  norm_num
lemma cnt_75 : Nat.count Nat.Prime 75 = 21 := by
  rw [show (75:ℕ) = 74 + 1 by norm_num, Nat.count_succ, cnt_74]
  norm_num
lemma cnt_76 : Nat.count Nat.Prime 76 = 21 := by
  rw [show (76:ℕ) = 75 + 1 by norm_num, Nat.count_succ, cnt_75]
  norm_num
lemma cnt_77 : Nat.count Nat.Prime 77 = 21 := by
  rw [show (77:ℕ) = 76 + 1 by norm_num, Nat.count_succ, cnt_76]
  norm_num
lemma cnt_78 : Nat.count Nat.Prime 78 = 21 := by
  rw [show (78:ℕ) = 77 + 1 by norm_num, Nat.count_succ, cnt_77]
  norm_num
lemma cnt_79 : Nat.count Nat.Prime 79 = 21 := by
  rw [show (79:ℕ) = 78 + 1 by norm_num, Nat.count_succ, cnt_78]
  norm_num
lemma cnt_80 : Nat.count Nat.Prime 80 = 22 := by
  rw [show (80:ℕ) = 79 + 1 by norm_num, Nat.count_succ, cnt_79]
  norm_num
lemma cnt_81 : Nat.count Nat.Prime 81 = 22 := by
  rw [show (81:ℕ) = 80 + 1 by norm_num, Nat.count_succ, cnt_80]
  norm_num
lemma cnt_82 : Nat.count Nat.Prime 82 = 22 := by
  rw [show (82:ℕ) = 81 + 1 by norm_num, Nat.count_succ, cnt_81]
  norm_num
lemma cnt_83 : Nat.count Nat.Prime 83 = 22 := by
  rw [show (83:ℕ) = 82 + 1 by norm_num, Nat.count_succ, cnt_82]
  norm_num
lemma cnt_84 : Nat.count Nat.Prime 84 = 23 := by
  rw [show (84:ℕ) = 83 + 1 by norm_num, Nat.count_succ, cnt_83]
  norm_num
lemma cnt_85 : Nat.count Nat.Prime 85 = 23 := by
  rw [show (85:ℕ) = 84 + 1 by norm_num, Nat.count_succ, cnt_84]
  norm_num
lemma cnt_86 : Nat.count Nat.Prime 86 = 23 := by
  rw [show (86:ℕ) = 85 + 1 by norm_num, Nat.count_succ, cnt_85]
  norm_num
lemma cnt_87 : Nat.count Nat.Prime 87 = 23 := by
  rw [show (87:ℕ) = 86 + 1 by norm_num, Nat.count_succ, cnt_86]
  norm_num
lemma cnt_88 : Nat.count Nat.Prime 88 = 23 := by
  rw [show (88:ℕ) = 87 + 1 by norm_num, Nat.count_succ, cnt_87]
  norm_num
lemma cnt_89 : Nat.count Nat.Prime 89 = 23 := by
  rw [show (89:ℕ) = 88 + 1 by norm_num, Nat.count_succ, cnt_88]
  norm_num
lemma cnt_90 : Nat.count Nat.Prime 90 = 24 := by
  rw [show (90:ℕ) = 89 + 1 by norm_num, Nat.count_succ, cnt_89]
  norm_num
lemma cnt_91 : Nat.count Nat.Prime 91 = 24 := by
  rw [show (91:ℕ) = 90 + 1 by norm_num, Nat.count_succ, cnt_90]
  norm_num
lemma cnt_92 : Nat.count Nat.Prime 92 = 24 := by
  rw [show (92:ℕ) = 91 + 1 by norm_num, Nat.count_succ, cnt_91]
  norm_num
lemma cnt_93 : Nat.count Nat.Prime 93 = 24 := by
  rw [show (93:ℕ) = 92 + 1 by norm_num, Nat.count_succ, cnt_92]
  norm_num
lemma cnt_94 : Nat.count Nat.Prime 94 = 24 := by
  rw [show (94:ℕ) = 93 + 1 by norm_num, Nat.count_succ, cnt_93]
  norm_num
lemma cnt_95 : Nat.count Nat.Prime 95 = 24 := by
  rw [show (95:ℕ) = 94 + 1 by norm_num, Nat.count_succ, cnt_94]
  norm_num
lemma cnt_96 : Nat.count Nat.Prime 96 = 24 := by
  rw [show (96:ℕ) = 95 + 1 by norm_num, Nat.count_succ, cnt_95]
  norm_num
lemma cnt_97 : Nat.count Nat.Prime 97 = 24 := by
  rw [show (97:ℕ) = 96 + 1 by norm_num, Nat.count_succ, cnt_96]
  norm_num
lemma cnt_98 : Nat.count Nat.Prime 98 = 25 := by
  rw [show (98:ℕ) = 97 + 1 by norm_num, Nat.count_succ, cnt_97]
  norm_num
lemma cnt_99 : Nat.count Nat.Prime 99 = 25 := by
  rw [show (99:ℕ) = 98 + 1 by norm_num, Nat.count_succ, cnt_98]
  norm_num
lemma cnt_100 : Nat.count Nat.Prime 100 = 25 := by
  rw [show (100:ℕ) = 99 + 1 by norm_num, Nat.count_succ, cnt_99]
  norm_num
lemma cnt_101 : Nat.count Nat.Prime 101 = 25 := by
  rw [show (101:ℕ) = 100 + 1 by norm_num, Nat.count_succ, cnt_100]
  norm_num
lemma cnt_102 : Nat.count Nat.Prime 102 = 26 := by
  rw [show (102:ℕ) = 101 + 1 by norm_num, Nat.count_succ, cnt_101]
  norm_num
lemma cnt_103 : Nat.count Nat.Prime 103 = 26 := by
  rw [show (103:ℕ) = 102 + 1 by norm_num, Nat.count_succ, cnt_102]
  norm_num
lemma cnt_104 : Nat.count Nat.Prime 104 = 27 := by
  rw [show (104:ℕ) = 103 + 1 by norm_num, Nat.count_succ, cnt_103]
  norm_num
lemma cnt_105 : Nat.count Nat.Prime 105 = 27 := by
  rw [show (105:ℕ) = 104 + 1 by norm_num, Nat.count_succ, cnt_104]
  norm_num
lemma cnt_106 : Nat.count Nat.Prime 106 = 27 := by
  rw [show (106:ℕ) = 105 + 1 by norm_num, Nat.count_succ, cnt_105]
  norm_num
lemma cnt_107 : Nat.count Nat.Prime 107 = 27 := by
  rw [show (107:ℕ) = 106 + 1 by norm_num, Nat.count_succ, cnt_106]
  norm_num
lemma cnt_108 : Nat.count Nat.Prime 108 = 28 := by
  rw [show (108:ℕ) = 107 + 1 by norm_num, Nat.count_succ, cnt_107]
  norm_num
lemma cnt_109 : Nat.count Nat.Prime 109 = 28 := by
  rw [show (109:ℕ) = 108 + 1 by norm_num, Nat.count_succ, cnt_108]
  norm_num
lemma cnt_110 : Nat.count Nat.Prime 110 = 29 := by
  rw [show (110:ℕ) = 109 + 1 by norm_num, Nat.count_succ, cnt_109]
  norm_num
lemma cnt_111 : Nat.count Nat.Prime 111 = 29 := by
  rw [show (111:ℕ) = 110 + 1 by norm_num, Nat.count_succ, cnt_110]
  norm_num
lemma cnt_112 : Nat.count Nat.Prime 112 = 29 := by
  rw [show (112:ℕ) = 111 + 1 by norm_num, Nat.count_succ, cnt_111]
  norm_num
lemma cnt_113 : Nat.count Nat.Prime 113 = 29 := by
  rw [show (113:ℕ) = 112 + 1 by norm_num, Nat.count_succ, cnt_112]
  norm_num
lemma cnt_114 : Nat.count Nat.Prime 114 = 30 := by
  rw [show (114:ℕ) = 113 + 1 by norm_num, Nat.count_succ, cnt_113]
  norm_num
lemma cnt_115 : Nat.count Nat.Prime 115 = 30 := by
  rw [show (115:ℕ) = 114 + 1 by norm_num, Nat.count_succ, cnt_114]
  norm_num
lemma cnt_116 : Nat.count Nat.Prime 116 = 30 := by
  rw [show (116:ℕ) = 115 + 1 by norm_num, Nat.count_succ, cnt_115]
  norm_num
lemma cnt_117 : Nat.count Nat.Prime 117 = 30 := by
  rw [show (117:ℕ) = 116 + 1 by norm_num, Nat.count_succ, cnt_116]
  norm_num
lemma cnt_118 : Nat.count Nat.Prime 118 = 30 := by
  rw [show (118:ℕ) = 117 + 1 by norm_num, Nat.count_succ, cnt_117]
  norm_num
lemma cnt_119 : Nat.count Nat.Prime 119 = 30 := by
  rw [show (119:ℕ) = 118 + 1 by norm_num, Nat.count_succ, cnt_118]
  norm_num
lemma cnt_120 : Nat.count Nat.Prime 120 = 30 := by
  rw [show (120:ℕ) = 119 + 1 by norm_num, Nat.count_succ, cnt_119]
  norm_num
lemma cnt_121 : Nat.count Nat.Prime 121 = 30 := by
  rw [show (121:ℕ) = 120 + 1 by norm_num, Nat.count_succ, cnt_120]
  norm_num
lemma cnt_122 : Nat.count Nat.Prime 122 = 30 := by
  rw [show (122:ℕ) = 121 + 1 by norm_num, Nat.count_succ, cnt_121]
  norm_num
lemma cnt_123 : Nat.count Nat.Prime 123 = 30 := by
  rw [show (123:ℕ) = 122 + 1 by norm_num, Nat.count_succ, cnt_122]
  norm_num
lemma cnt_124 : Nat.count Nat.Prime 124 = 30 := by
  rw [show (124:ℕ) = 123 + 1 by norm_num, Nat.count_succ, cnt_123]
  norm_num
lemma cnt_125 : Nat.count Nat.Prime 125 = 30 := by
  rw [show (125:ℕ) = 124 + 1 by norm_num, Nat.count_succ, cnt_124]
  norm_num
lemma cnt_126 : Nat.count Nat.Prime 126 = 30 := by
  rw [show (126:ℕ) = 125 + 1 by norm_num, Nat.count_succ, cnt_125]
  norm_num
lemma cnt_127 : Nat.count Nat.Prime 127 = 30 := by
  rw [show (127:ℕ) = 126 + 1 by norm_num, Nat.count_succ, cnt_126]
  norm_num
lemma cnt_128 : Nat.count Nat.Prime 128 = 31 := by
  rw [show (128:ℕ) = 127 + 1 by norm_num, Nat.count_succ, cnt_127]
  norm_num
lemma cnt_129 : Nat.count Nat.Prime 129 = 31 := by
  rw [show (129:ℕ) = 128 + 1 by norm_num, Nat.count_succ, cnt_128]
  norm_num
lemma cnt_130 : Nat.count Nat.Prime 130 = 31 := by
  rw [show (130:ℕ) = 129 + 1 by norm_num, Nat.count_succ, cnt_129]
  norm_num
lemma cnt_131 : Nat.count Nat.Prime 131 = 31 := by
  rw [show (131:ℕ) = 130 + 1 by norm_num, Nat.count_succ, cnt_130]
  norm_num
lemma cnt_132 : Nat.count Nat.Prime 132 = 32 := by
  rw [show (132:ℕ) = 131 + 1 by norm_num, Nat.count_succ, cnt_131]
  norm_num
lemma cnt_133 : Nat.count Nat.Prime 133 = 32 := by
  rw [show (133:ℕ) = 132 + 1 by norm_num, Nat.count_succ, cnt_132]
  norm_num
lemma cnt_134 : Nat.count Nat.Prime 134 = 32 := by
  rw [show (134:ℕ) = 133 + 1 by norm_num, Nat.count_succ, cnt_133]
  norm_num
lemma cnt_135 : Nat.count Nat.Prime 135 = 32 := by
  rw [show (135:ℕ) = 134 + 1 by norm_num, Nat.count_succ, cnt_134]
  norm_num
lemma cnt_136 : Nat.count Nat.Prime 136 = 32 := by
  rw [show (136:ℕ) = 135 + 1 by norm_num, Nat.count_succ, cnt_135]
  norm_num
lemma cnt_137 : Nat.count Nat.Prime 137 = 32 := by
  rw [show (137:ℕ) = 136 + 1 by norm_num, Nat.count_succ, cnt_136]
  norm_num
lemma cnt_138 : Nat.count Nat.Prime 138 = 33 := by
  rw [show (138:ℕ) = 137 + 1 by norm_num, Nat.count_succ, cnt_137]
  norm_num
lemma cnt_139 : Nat.count Nat.Prime 139 = 33 := by
  rw [show (139:ℕ) = 138 + 1 by norm_num, Nat.count_succ, cnt_138]
  norm_num
lemma cnt_140 : Nat.count Nat.Prime 140 = 34 := by
  rw [show (140:ℕ) = 139 + 1 by norm_num, Nat.count_succ, cnt_139]
  norm_num
lemma cnt_141 : Nat.count Nat.Prime 141 = 34 := by
  rw [show (141:ℕ) = 140 + 1 by norm_num, Nat.count_succ, cnt_140]
  norm_num
lemma cnt_142 : Nat.count Nat.Prime 142 = 34 := by
  rw [show (142:ℕ) = 141 + 1 by norm_num, Nat.count_succ, cnt_141]
  norm_num
lemma cnt_143 : Nat.count Nat.Prime 143 = 34 := by
  rw [show (143:ℕ) = 142 + 1 by norm_num, Nat.count_succ, cnt_142]
  norm_num
lemma cnt_144 : Nat.count Nat.Prime 144 = 34 := by
  rw [show (144:ℕ) = 143 + 1 by norm_num, Nat.count_succ, cnt_143]
  norm_num
lemma cnt_145 : Nat.count Nat.Prime 145 = 34 := by
  rw [show (145:ℕ) = 144 + 1 by norm_num, Nat.count_succ, cnt_144]
  norm_num
lemma cnt_146 : Nat.count Nat.Prime 146 = 34 := by
  rw [show (146:ℕ) = 145 + 1 by norm_num, Nat.count_succ, cnt_145]
  norm_num
lemma cnt_147 : Nat.count Nat.Prime 147 = 34 := by
  rw [show (147:ℕ) = 146 + 1 by norm_num, Nat.count_succ, cnt_146]
  norm_num
lemma cnt_148 : Nat.count Nat.Prime 148 = 34 := by
  rw [show (148:ℕ) = 147 + 1 by norm_num, Nat.count_succ, cnt_147]
  norm_num
lemma cnt_149 : Nat.count Nat.Prime 149 = 34 := by
  rw [show (149:ℕ) = 148 + 1 by norm_num, Nat.count_succ, cnt_148]
  norm_num
lemma cnt_150 : Nat.count Nat.Prime 150 = 35 := by
  rw [show (150:ℕ) = 149 + 1 by norm_num, Nat.count_succ, cnt_149]
  norm_num
lemma cnt_151 : Nat.count Nat.Prime 151 = 35 := by
  rw [show (151:ℕ) = 150 + 1 by norm_num, Nat.count_succ, cnt_150]
  norm_num
lemma cnt_152 : Nat.count Nat.Prime 152 = 36 := by
  rw [show (152:ℕ) = 151 + 1 by norm_num, Nat.count_succ, cnt_151]
  norm_num
lemma cnt_153 : Nat.count Nat.Prime 153 = 36 := by
  rw [show (153:ℕ) = 152 + 1 by norm_num, Nat.count_succ, cnt_152]
  norm_num
lemma cnt_154 : Nat.count Nat.Prime 154 = 36 := by
  rw [show (154:ℕ) = 153 + 1 by norm_num, Nat.count_succ, cnt_153]
  norm_num
lemma cnt_155 : Nat.count Nat.Prime 155 = 36 := by
  rw [show (155:ℕ) = 154 + 1 by norm_num, Nat.count_succ, cnt_154]
  norm_num
lemma cnt_156 : Nat.count Nat.Prime 156 = 36 := by
  rw [show (156:ℕ) = 155 + 1 by norm_num, Nat.count_succ, cnt_155]
  norm_num
lemma cnt_157 : Nat.count Nat.Prime 157 = 36 := by
  rw [show (157:ℕ) = 156 + 1 by norm_num, Nat.count_succ, cnt_156]
  norm_num
lemma cnt_158 : Nat.count Nat.Prime 158 = 37 := by
  rw [show (158:ℕ) = 157 + 1 by norm_num, Nat.count_succ, cnt_157]
  norm_num
lemma cnt_159 : Nat.count Nat.Prime 159 = 37 := by
  rw [show (159:ℕ) = 158 + 1 by norm_num, Nat.count_succ, cnt_158]
  norm_num
lemma cnt_160 : Nat.count Nat.Prime 160 = 37 := by
  rw [show (160:ℕ) = 159 + 1 by norm_num, Nat.count_succ, cnt_159]
  norm_num
lemma cnt_161 : Nat.count Nat.Prime 161 = 37 := by
  rw [show (161:ℕ) = 160 + 1 by norm_num, Nat.count_succ, cnt_160]
  norm_num
lemma cnt_162 : Nat.count Nat.Prime 162 = 37 := by
  rw [show (162:ℕ) = 161 + 1 by norm_num, Nat.count_succ, cnt_161]
  norm_num
lemma cnt_163 : Nat.count Nat.Prime 163 = 37 := by
  rw [show (163:ℕ) = 162 + 1 by norm_num, Nat.count_succ, cnt_162]
  norm_num
lemma cnt_164 : Nat.count Nat.Prime 164 = 38 := by
  rw [show (164:ℕ) = 163 + 1 by norm_num, Nat.count_succ, cnt_163]
  norm_num
lemma cnt_165 : Nat.count Nat.Prime 165 = 38 := by
  rw [show (165:ℕ) = 164 + 1 by norm_num, Nat.count_succ, cnt_164]
  norm_num
lemma cnt_166 : Nat.count Nat.Prime 166 = 38 := by
  rw [show (166:ℕ) = 165 + 1 by norm_num, Nat.count_succ, cnt_165]
  norm_num
lemma cnt_167 : Nat.count Nat.Prime 167 = 38 := by
  rw [show (167:ℕ) = 166 + 1 by norm_num, Nat.count_succ, cnt_166]
  norm_num
lemma cnt_168 : Nat.count Nat.Prime 168 = 39 := by
  rw [show (168:ℕ) = 167 + 1 by norm_num, Nat.count_succ, cnt_167]
  norm_num
lemma cnt_169 : Nat.count Nat.Prime 169 = 39 := by
  rw [show (169:ℕ) = 168 + 1 by norm_num, Nat.count_succ, cnt_168]
  norm_num
lemma cnt_170 : Nat.count Nat.Prime 170 = 39 := by
  rw [show (170:ℕ) = 169 + 1 by norm_num, Nat.count_succ, cnt_169]
  norm_num
lemma cnt_171 : Nat.count Nat.Prime 171 = 39 := by
  rw [show (171:ℕ) = 170 + 1 by norm_num, Nat.count_succ, cnt_170]
  norm_num
lemma cnt_172 : Nat.count Nat.Prime 172 = 39 := by
  rw [show (172:ℕ) = 171 + 1 by norm_num, Nat.count_succ, cnt_171]
  norm_num
lemma cnt_173 : Nat.count Nat.Prime 173 = 39 := by
  rw [show (173:ℕ) = 172 + 1 by norm_num, Nat.count_succ, cnt_172]
  norm_num
lemma cnt_174 : Nat.count Nat.Prime 174 = 40 := by
  rw [show (174:ℕ) = 173 + 1 by norm_num, Nat.count_succ, cnt_173]
  norm_num
lemma cnt_175 : Nat.count Nat.Prime 175 = 40 := by
  rw [show (175:ℕ) = 174 + 1 by norm_num, Nat.count_succ, cnt_174]
  norm_num
lemma cnt_176 : Nat.count Nat.Prime 176 = 40 := by
  rw [show (176:ℕ) = 175 + 1 by norm_num, Nat.count_succ, cnt_175]
  norm_num
lemma cnt_177 : Nat.count Nat.Prime 177 = 40 := by
  rw [show (177:ℕ) = 176 + 1 by norm_num, Nat.count_succ, cnt_176]
  norm_num
lemma cnt_178 : Nat.count Nat.Prime 178 = 40 := by
  rw [show (178:ℕ) = 177 + 1 by norm_num, Nat.count_succ, cnt_177]
  norm_num
lemma cnt_179 : Nat.count Nat.Prime 179 = 40 := by
  rw [show (179:ℕ) = 178 + 1 by norm_num, Nat.count_succ, cnt_178]
  norm_num
lemma cnt_180 : Nat.count Nat.Prime 180 = 41 := by
  rw [show (180:ℕ) = 179 + 1 by norm_num, Nat.count_succ, cnt_179]
  norm_num
lemma cnt_181 : Nat.count Nat.Prime 181 = 41 := by
  rw [show (181:ℕ) = 180 + 1 by norm_num, Nat.count_succ, cnt_180]
  norm_num
lemma cnt_182 : Nat.count Nat.Prime 182 = 42 := by
  rw [show (182:ℕ) = 181 + 1 by norm_num, Nat.count_succ, cnt_181]
  norm_num
lemma cnt_183 : Nat.count Nat.Prime 183 = 42 := by
  rw [show (183:ℕ) = 182 + 1 by norm_num, Nat.count_succ, cnt_182]
  norm_num
lemma cnt_184 : Nat.count Nat.Prime 184 = 42 := by
  rw [show (184:ℕ) = 183 + 1 by norm_num, Nat.count_succ, cnt_183]
  norm_num
lemma cnt_185 : Nat.count Nat.Prime 185 = 42 := by
  rw [show (185:ℕ) = 184 + 1 by norm_num, Nat.count_succ, cnt_184]
  norm_num
lemma cnt_186 : Nat.count Nat.Prime 186 = 42 := by
  rw [show (186:ℕ) = 185 + 1 by norm_num, Nat.count_succ, cnt_185]
  norm_num
lemma cnt_187 : Nat.count Nat.Prime 187 = 42 := by
  rw [show (187:ℕ) = 186 + 1 by norm_num, Nat.count_succ, cnt_186]
  norm_num
lemma cnt_188 : Nat.count Nat.Prime 188 = 42 := by
  rw [show (188:ℕ) = 187 + 1 by norm_num, Nat.count_succ, cnt_187]
  norm_num
lemma cnt_189 : Nat.count Nat.Prime 189 = 42 := by
  rw [show (189:ℕ) = 188 + 1 by norm_num, Nat.count_succ, cnt_188]
  norm_num
lemma cnt_190 : Nat.count Nat.Prime 190 = 42 := by
  rw [show (190:ℕ) = 189 + 1 by norm_num, Nat.count_succ, cnt_189]
  norm_num
lemma cnt_191 : Nat.count Nat.Prime 191 = 42 := by
  rw [show (191:ℕ) = 190 + 1 by norm_num, Nat.count_succ, cnt_190]
  norm_num
lemma cnt_192 : Nat.count Nat.Prime 192 = 43 := by
  rw [show (192:ℕ) = 191 + 1 by norm_num, Nat.count_succ, cnt_191]
  norm_num
lemma cnt_193 : Nat.count Nat.Prime 193 = 43 := by
  rw [show (193:ℕ) = 192 + 1 by norm_num, Nat.count_succ, cnt_192]
  norm_num
lemma cnt_194 : Nat.count Nat.Prime 194 = 44 := by
  rw [show (194:ℕ) = 193 + 1 by norm_num, Nat.count_succ, cnt_193]
  norm_num
lemma cnt_195 : Nat.count Nat.Prime 195 = 44 := by
  rw [show (195:ℕ) = 194 + 1 by norm_num, Nat.count_succ, cnt_194]
  norm_num
lemma cnt_196 : Nat.count Nat.Prime 196 = 44 := by
  rw [show (196:ℕ) = 195 + 1 by norm_num, Nat.count_succ, cnt_195]
  norm_num
lemma cnt_197 : Nat.count Nat.Prime 197 = 44 := by
  rw [show (197:ℕ) = 196 + 1 by norm_num, Nat.count_succ, cnt_196]
  norm_num
lemma cnt_198 : Nat.count Nat.Prime 198 = 45 := by
  rw [show (198:ℕ) = 197 + 1 by norm_num, Nat.count_succ, cnt_197]
  norm_num
lemma cnt_199 : Nat.count Nat.Prime 199 = 45 := by
  rw [show (199:ℕ) = 198 + 1 by norm_num, Nat.count_succ, cnt_198]
  norm_num
lemma cnt_200 : Nat.count Nat.Prime 200 = 46 := by
  rw [show (200:ℕ) = 199 + 1 by norm_num, Nat.count_succ, cnt_199]
  norm_num
lemma cnt_201 : Nat.count Nat.Prime 201 = 46 := by
  rw [show (201:ℕ) = 200 + 1 by norm_num, Nat.count_succ, cnt_200]
  norm_num
lemma cnt_202 : Nat.count Nat.Prime 202 = 46 := by
  rw [show (202:ℕ) = 201 + 1 by norm_num, Nat.count_succ, cnt_201]
  norm_num
lemma cnt_203 : Nat.count Nat.Prime 203 = 46 := by
  rw [show (203:ℕ) = 202 + 1 by norm_num, Nat.count_succ, cnt_202]
  norm_num
lemma cnt_204 : Nat.count Nat.Prime 204 = 46 := by
  rw [show (204:ℕ) = 203 + 1 by norm_num, Nat.count_succ, cnt_203]
  norm_num
lemma cnt_205 : Nat.count Nat.Prime 205 = 46 := by
  rw [show (205:ℕ) = 204 + 1 by norm_num, Nat.count_succ, cnt_204]
  norm_num
lemma cnt_206 : Nat.count Nat.Prime 206 = 46 := by
  rw [show (206:ℕ) = 205 + 1 by norm_num, Nat.count_succ, cnt_205]
  norm_num
lemma cnt_207 : Nat.count Nat.Prime 207 = 46 := by
  rw [show (207:ℕ) = 206 + 1 by norm_num, Nat.count_succ, cnt_206]
  norm_num
lemma cnt_208 : Nat.count Nat.Prime 208 = 46 := by
  rw [show (208:ℕ) = 207 + 1 by norm_num, Nat.count_succ, cnt_207]
  norm_num
lemma cnt_209 : Nat.count Nat.Prime 209 = 46 := by
  rw [show (209:ℕ) = 208 + 1 by norm_num, Nat.count_succ, cnt_208]
  norm_num
lemma cnt_210 : Nat.count Nat.Prime 210 = 46 := by
  rw [show (210:ℕ) = 209 + 1 by norm_num, Nat.count_succ, cnt_209]
  norm_num
lemma cnt_211 : Nat.count Nat.Prime 211 = 46 := by
  rw [show (211:ℕ) = 210 + 1 by norm_num, Nat.count_succ, cnt_210]
  norm_num
lemma cnt_212 : Nat.count Nat.Prime 212 = 47 := by
  rw [show (212:ℕ) = 211 + 1 by norm_num, Nat.count_succ, cnt_211]
  norm_num
lemma cnt_213 : Nat.count Nat.Prime 213 = 47 := by
  rw [show (213:ℕ) = 212 + 1 by norm_num, Nat.count_succ, cnt_212]
  norm_num
lemma cnt_214 : Nat.count Nat.Prime 214 = 47 := by
  rw [show (214:ℕ) = 213 + 1 by norm_num, Nat.count_succ, cnt_213]
  norm_num
lemma cnt_215 : Nat.count Nat.Prime 215 = 47 := by
  rw [show (215:ℕ) = 214 + 1 by norm_num, Nat.count_succ, cnt_214]
  norm_num
lemma cnt_216 : Nat.count Nat.Prime 216 = 47 := by
  rw [show (216:ℕ) = 215 + 1 by norm_num, Nat.count_succ, cnt_215]
  norm_num
lemma cnt_217 : Nat.count Nat.Prime 217 = 47 := by
  rw [show (217:ℕ) = 216 + 1 by norm_num, Nat.count_succ, cnt_216]
  norm_num
lemma cnt_218 : Nat.count Nat.Prime 218 = 47 := by
  rw [show (218:ℕ) = 217 + 1 by norm_num, Nat.count_succ, cnt_217]
  norm_num
lemma cnt_219 : Nat.count Nat.Prime 219 = 47 := by
  rw [show (219:ℕ) = 218 + 1 by norm_num, Nat.count_succ, cnt_218]
  norm_num
lemma cnt_220 : Nat.count Nat.Prime 220 = 47 := by
  rw [show (220:ℕ) = 219 + 1 by norm_num, Nat.count_succ, cnt_219]
  norm_num
lemma cnt_221 : Nat.count Nat.Prime 221 = 47 := by
  rw [show (221:ℕ) = 220 + 1 by norm_num, Nat.count_succ, cnt_220]
  norm_num
lemma cnt_222 : Nat.count Nat.Prime 222 = 47 := by
  rw [show (222:ℕ) = 221 + 1 by norm_num, Nat.count_succ, cnt_221]
  norm_num
lemma cnt_223 : Nat.count Nat.Prime 223 = 47 := by
  rw [show (223:ℕ) = 222 + 1 by norm_num, Nat.count_succ, cnt_222]
  norm_num
lemma cnt_224 : Nat.count Nat.Prime 224 = 48 := by
  rw [show (224:ℕ) = 223 + 1 by norm_num, Nat.count_succ, cnt_223]
  norm_num
lemma cnt_225 : Nat.count Nat.Prime 225 = 48 := by
  rw [show (225:ℕ) = 224 + 1 by norm_num, Nat.count_succ, cnt_224]
  norm_num
lemma cnt_226 : Nat.count Nat.Prime 226 = 48 := by
  rw [show (226:ℕ) = 225 + 1 by norm_num, Nat.count_succ, cnt_225]
  norm_num
lemma cnt_227 : Nat.count Nat.Prime 227 = 48 := by
  rw [show (227:ℕ) = 226 + 1 by norm_num, Nat.count_succ, cnt_226]
  norm_num
lemma cnt_228 : Nat.count Nat.Prime 228 = 49 := by
  rw [show (228:ℕ) = 227 + 1 by norm_num, Nat.count_succ, cnt_227]
  norm_num
lemma cnt_229 : Nat.count Nat.Prime 229 = 49 := by
  rw [show (229:ℕ) = 228 + 1 by norm_num, Nat.count_succ, cnt_228]
  norm_num
lemma cnt_230 : Nat.count Nat.Prime 230 = 50 := by
  rw [show (230:ℕ) = 229 + 1 by norm_num, Nat.count_succ, cnt_229]
  norm_num
lemma cnt_231 : Nat.count Nat.Prime 231 = 50 := by
  rw [show (231:ℕ) = 230 + 1 by norm_num, Nat.count_succ, cnt_230]
  norm_num
lemma cnt_232 : Nat.count Nat.Prime 232 = 50 := by
  rw [show (232:ℕ) = 231 + 1 by norm_num, Nat.count_succ, cnt_231]
  norm_num
lemma cnt_233 : Nat.count Nat.Prime 233 = 50 := by
  rw [show (233:ℕ) = 232 + 1 by norm_num, Nat.count_succ, cnt_232]
  norm_num
lemma cnt_234 : Nat.count Nat.Prime 234 = 51 := by
  rw [show (234:ℕ) = 233 + 1 by norm_num, Nat.count_succ, cnt_233]
  norm_num
lemma cnt_235 : Nat.count Nat.Prime 235 = 51 := by
  rw [show (235:ℕ) = 234 + 1 by norm_num, Nat.count_succ, cnt_234]
  norm_num
lemma cnt_236 : Nat.count Nat.Prime 236 = 51 := by
  rw [show (236:ℕ) = 235 + 1 by norm_num, Nat.count_succ, cnt_235]
  norm_num
lemma cnt_237 : Nat.count Nat.Prime 237 = 51 := by
  rw [show (237:ℕ) = 236 + 1 by norm_num, Nat.count_succ, cnt_236]
  norm_num
lemma cnt_238 : Nat.count Nat.Prime 238 = 51 := by
  rw [show (238:ℕ) = 237 + 1 by norm_num, Nat.count_succ, cnt_237]
  norm_num
lemma cnt_239 : Nat.count Nat.Prime 239 = 51 := by
  rw [show (239:ℕ) = 238 + 1 by norm_num, Nat.count_succ, cnt_238]
  norm_num
lemma cnt_240 : Nat.count Nat.Prime 240 = 52 := by
  rw [show (240:ℕ) = 239 + 1 by norm_num, Nat.count_succ, cnt_239]
  norm_num
lemma cnt_241 : Nat.count Nat.Prime 241 = 52 := by
  rw [show (241:ℕ) = 240 + 1 by norm_num, Nat.count_succ, cnt_240]
  norm_num
lemma cnt_242 : Nat.count Nat.Prime 242 = 53 := by
  rw [show (242:ℕ) = 241 + 1 by norm_num, Nat.count_succ, cnt_241]
  norm_num
lemma cnt_243 : Nat.count Nat.Prime 243 = 53 := by
  rw [show (243:ℕ) = 242 + 1 by norm_num, Nat.count_succ, cnt_242]
  norm_num
lemma cnt_244 : Nat.count Nat.Prime 244 = 53 := by
  rw [show (244:ℕ) = 243 + 1 by norm_num, Nat.count_succ, cnt_243]
  norm_num
lemma cnt_245 : Nat.count Nat.Prime 245 = 53 := by
  rw [show (245:ℕ) = 244 + 1 by norm_num, Nat.count_succ, cnt_244]
  norm_num
lemma cnt_246 : Nat.count Nat.Prime 246 = 53 := by
  rw [show (246:ℕ) = 245 + 1 by norm_num, Nat.count_succ, cnt_245]
  norm_num
lemma cnt_247 : Nat.count Nat.Prime 247 = 53 := by
  rw [show (247:ℕ) = 246 + 1 by norm_num, Nat.count_succ, cnt_246]
  norm_num
lemma cnt_248 : Nat.count Nat.Prime 248 = 53 := by
  rw [show (248:ℕ) = 247 + 1 by norm_num, Nat.count_succ, cnt_247]
  norm_num
lemma cnt_249 : Nat.count Nat.Prime 249 = 53 := by
  rw [show (249:ℕ) = 248 + 1 by norm_num, Nat.count_succ, cnt_248]
  norm_num
lemma cnt_250 : Nat.count Nat.Prime 250 = 53 := by
  rw [show (250:ℕ) = 249 + 1 by norm_num, Nat.count_succ, cnt_249]
  norm_num
lemma cnt_251 : Nat.count Nat.Prime 251 = 53 := by
  rw [show (251:ℕ) = 250 + 1 by norm_num, Nat.count_succ, cnt_250]
  norm_num
lemma cnt_252 : Nat.count Nat.Prime 252 = 54 := by
  rw [show (252:ℕ) = 251 + 1 by norm_num, Nat.count_succ, cnt_251]
  norm_num
lemma cnt_253 : Nat.count Nat.Prime 253 = 54 := by
  rw [show (253:ℕ) = 252 + 1 by norm_num, Nat.count_succ, cnt_252]
  norm_num
lemma cnt_254 : Nat.count Nat.Prime 254 = 54 := by
  rw [show (254:ℕ) = 253 + 1 by norm_num, Nat.count_succ, cnt_253]
  norm_num
lemma cnt_255 : Nat.count Nat.Prime 255 = 54 := by
  rw [show (255:ℕ) = 254 + 1 by norm_num, Nat.count_succ, cnt_254]
  norm_num
lemma cnt_256 : Nat.count Nat.Prime 256 = 54 := by
  rw [show (256:ℕ) = 255 + 1 by norm_num, Nat.count_succ, cnt_255]
  norm_num
lemma cnt_257 : Nat.count Nat.Prime 257 = 54 := by
  rw [show (257:ℕ) = 256 + 1 by norm_num, Nat.count_succ, cnt_256]
  norm_num
lemma cnt_258 : Nat.count Nat.Prime 258 = 55 := by
  rw [show (258:ℕ) = 257 + 1 by norm_num, Nat.count_succ, cnt_257]
  norm_num
lemma cnt_259 : Nat.count Nat.Prime 259 = 55 := by
  rw [show (259:ℕ) = 258 + 1 by norm_num, Nat.count_succ, cnt_258]
  norm_num
lemma cnt_260 : Nat.count Nat.Prime 260 = 55 := by
  rw [show (260:ℕ) = 259 + 1 by norm_num, Nat.count_succ, cnt_259]
  norm_num
lemma cnt_261 : Nat.count Nat.Prime 261 = 55 := by
  rw [show (261:ℕ) = 260 + 1 by norm_num, Nat.count_succ, cnt_260]
  norm_num
lemma cnt_262 : Nat.count Nat.Prime 262 = 55 := by
  rw [show (262:ℕ) = 261 + 1 by norm_num, Nat.count_succ, cnt_261]
  norm_num
lemma cnt_263 : Nat.count Nat.Prime 263 = 55 := by
  rw [show (263:ℕ) = 262 + 1 by norm_num, Nat.count_succ, cnt_262]
  norm_num
lemma cnt_264 : Nat.count Nat.Prime 264 = 56 := by
  rw [show (264:ℕ) = 263 + 1 by norm_num, Nat.count_succ, cnt_263]
  norm_num
lemma cnt_265 : Nat.count Nat.Prime 265 = 56 := by
  rw [show (265:ℕ) = 264 + 1 by norm_num, Nat.count_succ, cnt_264]
  norm_num
lemma cnt_266 : Nat.count Nat.Prime 266 = 56 := by
  rw [show (266:ℕ) = 265 + 1 by norm_num, Nat.count_succ, cnt_265]
  norm_num
lemma cnt_267 : Nat.count Nat.Prime 267 = 56 := by
  rw [show (267:ℕ) = 266 + 1 by norm_num, Nat.count_succ, cnt_266]
  norm_num
lemma cnt_268 : Nat.count Nat.Prime 268 = 56 := by
  rw [show (268:ℕ) = 267 + 1 by norm_num, Nat.count_succ, cnt_267]
  norm_num
lemma cnt_269 : Nat.count Nat.Prime 269 = 56 := by
  rw [show (269:ℕ) = 268 + 1 by norm_num, Nat.count_succ, cnt_268]
  norm_num
lemma cnt_270 : Nat.count Nat.Prime 270 = 57 := by
  rw [show (270:ℕ) = 269 + 1 by norm_num, Nat.count_succ, cnt_269]
  norm_num
lemma cnt_271 : Nat.count Nat.Prime 271 = 57 := by
  rw [show (271:ℕ) = 270 + 1 by norm_num, Nat.count_succ, cnt_270]
  norm_num
lemma cnt_272 : Nat.count Nat.Prime 272 = 58 := by
  rw [show (272:ℕ) = 271 + 1 by norm_num, Nat.count_succ, cnt_271]
  norm_num
lemma cnt_273 : Nat.count Nat.Prime 273 = 58 := by
  rw [show (273:ℕ) = 272 + 1 by norm_num, Nat.count_succ, cnt_272]
  norm_num
lemma cnt_274 : Nat.count Nat.Prime 274 = 58 := by
  rw [show (274:ℕ) = 273 + 1 by norm_num, Nat.count_succ, cnt_273]
  norm_num
lemma cnt_275 : Nat.count Nat.Prime 275 = 58 := by
  rw [show (275:ℕ) = 274 + 1 by norm_num, Nat.count_succ, cnt_274]
  norm_num
lemma cnt_276 : Nat.count Nat.Prime 276 = 58 := by
  rw [show (276:ℕ) = 275 + 1 by norm_num, Nat.count_succ, cnt_275]
  norm_num
lemma cnt_277 : Nat.count Nat.Prime 277 = 58 := by
  rw [show (277:ℕ) = 276 + 1 by norm_num, Nat.count_succ, cnt_276]
  norm_num
lemma cnt_278 : Nat.count Nat.Prime 278 = 59 := by
  rw [show (278:ℕ) = 277 + 1 by norm_num, Nat.count_succ, cnt_277]
  norm_num
lemma cnt_279 : Nat.count Nat.Prime 279 = 59 := by
  rw [show (279:ℕ) = 278 + 1 by norm_num, Nat.count_succ, cnt_278]
  norm_num
lemma cnt_280 : Nat.count Nat.Prime 280 = 59 := by
  rw [show (280:ℕ) = 279 + 1 by norm_num, Nat.count_succ, cnt_279]
  norm_num
lemma cnt_281 : Nat.count Nat.Prime 281 = 59 := by
  rw [show (281:ℕ) = 280 + 1 by norm_num, Nat.count_succ, cnt_280]
  norm_num
lemma cnt_282 : Nat.count Nat.Prime 282 = 60 := by
  rw [show (282:ℕ) = 281 + 1 by norm_num, Nat.count_succ, cnt_281]
  norm_num
lemma cnt_283 : Nat.count Nat.Prime 283 = 60 := by
  rw [show (283:ℕ) = 282 + 1 by norm_num, Nat.count_succ, cnt_282]
  norm_num
lemma cnt_284 : Nat.count Nat.Prime 284 = 61 := by
  rw [show (284:ℕ) = 283 + 1 by norm_num, Nat.count_succ, cnt_283]
  norm_num
lemma cnt_285 : Nat.count Nat.Prime 285 = 61 := by
  rw [show (285:ℕ) = 284 + 1 by norm_num, Nat.count_succ, cnt_284]
  norm_num
lemma cnt_286 : Nat.count Nat.Prime 286 = 61 := by
  rw [show (286:ℕ) = 285 + 1 by norm_num, Nat.count_succ, cnt_285]
  norm_num
lemma cnt_287 : Nat.count Nat.Prime 287 = 61 := by
  rw [show (287:ℕ) = 286 + 1 by norm_num, Nat.count_succ, cnt_286]
  norm_num
lemma cnt_288 : Nat.count Nat.Prime 288 = 61 := by
  rw [show (288:ℕ) = 287 + 1 by norm_num, Nat.count_succ, cnt_287]
  norm_num
lemma cnt_289 : Nat.count Nat.Prime 289 = 61 := by
  rw [show (289:ℕ) = 288 + 1 by norm_num, Nat.count_succ, cnt_288]
  norm_num
lemma cnt_290 : Nat.count Nat.Prime 290 = 61 := by
  rw [show (290:ℕ) = 289 + 1 by norm_num, Nat.count_succ, cnt_289]
  norm_num
lemma cnt_291 : Nat.count Nat.Prime 291 = 61 := by
  rw [show (291:ℕ) = 290 + 1 by norm_num, Nat.count_succ, cnt_290]
  norm_num
lemma cnt_292 : Nat.count Nat.Prime 292 = 61 := by
  rw [show (292:ℕ) = 291 + 1 by norm_num, Nat.count_succ, cnt_291]
  norm_num
lemma cnt_293 : Nat.count Nat.Prime 293 = 61 := by
  rw [show (293:ℕ) = 292 + 1 by norm_num, Nat.count_succ, cnt_292]
  norm_num
lemma cnt_294 : Nat.count Nat.Prime 294 = 62 := by
  rw [show (294:ℕ) = 293 + 1 by norm_num, Nat.count_succ, cnt_293]
  norm_num
lemma cnt_295 : Nat.count Nat.Prime 295 = 62 := by
  rw [show (295:ℕ) = 294 + 1 by norm_num, Nat.count_succ, cnt_294]
  norm_num
lemma cnt_296 : Nat.count Nat.Prime 296 = 62 := by
  rw [show (296:ℕ) = 295 + 1 by norm_num, Nat.count_succ, cnt_295]
  norm_num
lemma cnt_297 : Nat.count Nat.Prime 297 = 62 := by
  rw [show (297:ℕ) = 296 + 1 by norm_num, Nat.count_succ, cnt_296]
  norm_num
lemma cnt_298 : Nat.count Nat.Prime 298 = 62 := by
  rw [show (298:ℕ) = 297 + 1 by norm_num, Nat.count_succ, cnt_297]
  norm_num
lemma cnt_299 : Nat.count Nat.Prime 299 = 62 := by
  rw [show (299:ℕ) = 298 + 1 by norm_num, Nat.count_succ, cnt_298]
  norm_num
lemma cnt_300 : Nat.count Nat.Prime 300 = 62 := by
  rw [show (300:ℕ) = 299 + 1 by norm_num, Nat.count_succ, cnt_299]
  norm_num
lemma cnt_301 : Nat.count Nat.Prime 301 = 62 := by
  rw [show (301:ℕ) = 300 + 1 by norm_num, Nat.count_succ, cnt_300]
  norm_num
lemma cnt_302 : Nat.count Nat.Prime 302 = 62 := by
  rw [show (302:ℕ) = 301 + 1 by norm_num, Nat.count_succ, cnt_301]
  norm_num
lemma cnt_303 : Nat.count Nat.Prime 303 = 62 := by
  rw [show (303:ℕ) = 302 + 1 by norm_num, Nat.count_succ, cnt_302]
  norm_num
lemma cnt_304 : Nat.count Nat.Prime 304 = 62 := by
  rw [show (304:ℕ) = 303 + 1 by norm_num, Nat.count_succ, cnt_303]
  norm_num
lemma cnt_305 : Nat.count Nat.Prime 305 = 62 := by
  rw [show (305:ℕ) = 304 + 1 by norm_num, Nat.count_succ, cnt_304]
  norm_num
lemma cnt_306 : Nat.count Nat.Prime 306 = 62 := by
  rw [show (306:ℕ) = 305 + 1 by norm_num, Nat.count_succ, cnt_305]
  norm_num
lemma cnt_307 : Nat.count Nat.Prime 307 = 62 := by
  rw [show (307:ℕ) = 306 + 1 by norm_num, Nat.count_succ, cnt_306]
  norm_num
lemma cnt_308 : Nat.count Nat.Prime 308 = 63 := by
  rw [show (308:ℕ) = 307 + 1 by norm_num, Nat.count_succ, cnt_307]
  norm_num
lemma cnt_309 : Nat.count Nat.Prime 309 = 63 := by
  rw [show (309:ℕ) = 308 + 1 by norm_num, Nat.count_succ, cnt_308]
  norm_num
lemma cnt_310 : Nat.count Nat.Prime 310 = 63 := by
  rw [show (310:ℕ) = 309 + 1 by norm_num, Nat.count_succ, cnt_309]
  norm_num
lemma cnt_311 : Nat.count Nat.Prime 311 = 63 := by
  rw [show (311:ℕ) = 310 + 1 by norm_num, Nat.count_succ, cnt_310]
  norm_num
lemma cnt_312 : Nat.count Nat.Prime 312 = 64 := by
  rw [show (312:ℕ) = 311 + 1 by norm_num, Nat.count_succ, cnt_311]
  norm_num
lemma cnt_313 : Nat.count Nat.Prime 313 = 64 := by
  rw [show (313:ℕ) = 312 + 1 by norm_num, Nat.count_succ, cnt_312]
  norm_num
lemma cnt_314 : Nat.count Nat.Prime 314 = 65 := by
  rw [show (314:ℕ) = 313 + 1 by norm_num, Nat.count_succ, cnt_313]
  norm_num
lemma cnt_315 : Nat.count Nat.Prime 315 = 65 := by
  rw [show (315:ℕ) = 314 + 1 by norm_num, Nat.count_succ, cnt_314]
  norm_num
lemma cnt_316 : Nat.count Nat.Prime 316 = 65 := by
  rw [show (316:ℕ) = 315 + 1 by norm_num, Nat.count_succ, cnt_315]
  norm_num
lemma cnt_317 : Nat.count Nat.Prime 317 = 65 := by
  rw [show (317:ℕ) = 316 + 1 by norm_num, Nat.count_succ, cnt_316]
  norm_num
lemma cnt_318 : Nat.count Nat.Prime 318 = 66 := by
  rw [show (318:ℕ) = 317 + 1 by norm_num, Nat.count_succ, cnt_317]
  norm_num

lemma nth_ptab_0 : Nat.nth Nat.Prime 0 = ptab 0 := by
  have hpn : Nat.Prime (ptab 0) := by decide
  have hc : Nat.count Nat.Prime (ptab 0) = 0 := by
    rw [show ptab 0 = 2 by rfl]
    exact cnt_2
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 0)) = ptab 0 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_1 : Nat.nth Nat.Prime 1 = ptab 1 := by
  have hpn : Nat.Prime (ptab 1) := by decide
  have hc : Nat.count Nat.Prime (ptab 1) = 1 := by
    rw [show ptab 1 = 3 by rfl]
    exact cnt_3
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 1)) = ptab 1 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_2 : Nat.nth Nat.Prime 2 = ptab 2 := by
  have hpn : Nat.Prime (ptab 2) := by decide
  have hc : Nat.count Nat.Prime (ptab 2) = 2 := by
    rw [show ptab 2 = 5 by rfl]
    exact cnt_5
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 2)) = ptab 2 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_3 : Nat.nth Nat.Prime 3 = ptab 3 := by
  have hpn : Nat.Prime (ptab 3) := by decide
  have hc : Nat.count Nat.Prime (ptab 3) = 3 := by
    rw [show ptab 3 = 7 by rfl]
    exact cnt_7
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 3)) = ptab 3 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_4 : Nat.nth Nat.Prime 4 = ptab 4 := by
  have hpn : Nat.Prime (ptab 4) := by decide
  have hc : Nat.count Nat.Prime (ptab 4) = 4 := by
    rw [show ptab 4 = 11 by rfl]
    exact cnt_11
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 4)) = ptab 4 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_5 : Nat.nth Nat.Prime 5 = ptab 5 := by
  have hpn : Nat.Prime (ptab 5) := by decide
  have hc : Nat.count Nat.Prime (ptab 5) = 5 := by
    rw [show ptab 5 = 13 by rfl]
    exact cnt_13
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 5)) = ptab 5 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_6 : Nat.nth Nat.Prime 6 = ptab 6 := by
  have hpn : Nat.Prime (ptab 6) := by decide
  have hc : Nat.count Nat.Prime (ptab 6) = 6 := by
    rw [show ptab 6 = 17 by rfl]
    exact cnt_17
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 6)) = ptab 6 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_7 : Nat.nth Nat.Prime 7 = ptab 7 := by
  have hpn : Nat.Prime (ptab 7) := by decide
  have hc : Nat.count Nat.Prime (ptab 7) = 7 := by
    rw [show ptab 7 = 19 by rfl]
    exact cnt_19
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 7)) = ptab 7 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_8 : Nat.nth Nat.Prime 8 = ptab 8 := by
  have hpn : Nat.Prime (ptab 8) := by decide
  have hc : Nat.count Nat.Prime (ptab 8) = 8 := by
    rw [show ptab 8 = 23 by rfl]
    exact cnt_23
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 8)) = ptab 8 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_9 : Nat.nth Nat.Prime 9 = ptab 9 := by
  have hpn : Nat.Prime (ptab 9) := by decide
  have hc : Nat.count Nat.Prime (ptab 9) = 9 := by
    rw [show ptab 9 = 29 by rfl]
    exact cnt_29
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 9)) = ptab 9 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_10 : Nat.nth Nat.Prime 10 = ptab 10 := by
  have hpn : Nat.Prime (ptab 10) := by decide
  have hc : Nat.count Nat.Prime (ptab 10) = 10 := by
    rw [show ptab 10 = 31 by rfl]
    exact cnt_31
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 10)) = ptab 10 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_11 : Nat.nth Nat.Prime 11 = ptab 11 := by
  have hpn : Nat.Prime (ptab 11) := by decide
  have hc : Nat.count Nat.Prime (ptab 11) = 11 := by
    rw [show ptab 11 = 37 by rfl]
    exact cnt_37
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 11)) = ptab 11 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_12 : Nat.nth Nat.Prime 12 = ptab 12 := by
  have hpn : Nat.Prime (ptab 12) := by decide
  have hc : Nat.count Nat.Prime (ptab 12) = 12 := by
    rw [show ptab 12 = 41 by rfl]
    exact cnt_41
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 12)) = ptab 12 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_13 : Nat.nth Nat.Prime 13 = ptab 13 := by
  have hpn : Nat.Prime (ptab 13) := by decide
  have hc : Nat.count Nat.Prime (ptab 13) = 13 := by
    rw [show ptab 13 = 43 by rfl]
    exact cnt_43
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 13)) = ptab 13 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_14 : Nat.nth Nat.Prime 14 = ptab 14 := by
  have hpn : Nat.Prime (ptab 14) := by decide
  have hc : Nat.count Nat.Prime (ptab 14) = 14 := by
    rw [show ptab 14 = 47 by rfl]
    exact cnt_47
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 14)) = ptab 14 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_15 : Nat.nth Nat.Prime 15 = ptab 15 := by
  have hpn : Nat.Prime (ptab 15) := by decide
  have hc : Nat.count Nat.Prime (ptab 15) = 15 := by
    rw [show ptab 15 = 53 by rfl]
    exact cnt_53
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 15)) = ptab 15 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_16 : Nat.nth Nat.Prime 16 = ptab 16 := by
  have hpn : Nat.Prime (ptab 16) := by decide
  have hc : Nat.count Nat.Prime (ptab 16) = 16 := by
    rw [show ptab 16 = 59 by rfl]
    exact cnt_59
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 16)) = ptab 16 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_17 : Nat.nth Nat.Prime 17 = ptab 17 := by
  have hpn : Nat.Prime (ptab 17) := by decide
  have hc : Nat.count Nat.Prime (ptab 17) = 17 := by
    rw [show ptab 17 = 61 by rfl]
    exact cnt_61
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 17)) = ptab 17 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_18 : Nat.nth Nat.Prime 18 = ptab 18 := by
  have hpn : Nat.Prime (ptab 18) := by decide
  have hc : Nat.count Nat.Prime (ptab 18) = 18 := by
    rw [show ptab 18 = 67 by rfl]
    exact cnt_67
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 18)) = ptab 18 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_19 : Nat.nth Nat.Prime 19 = ptab 19 := by
  have hpn : Nat.Prime (ptab 19) := by decide
  have hc : Nat.count Nat.Prime (ptab 19) = 19 := by
    rw [show ptab 19 = 71 by rfl]
    exact cnt_71
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 19)) = ptab 19 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_20 : Nat.nth Nat.Prime 20 = ptab 20 := by
  have hpn : Nat.Prime (ptab 20) := by decide
  have hc : Nat.count Nat.Prime (ptab 20) = 20 := by
    rw [show ptab 20 = 73 by rfl]
    exact cnt_73
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 20)) = ptab 20 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_21 : Nat.nth Nat.Prime 21 = ptab 21 := by
  have hpn : Nat.Prime (ptab 21) := by decide
  have hc : Nat.count Nat.Prime (ptab 21) = 21 := by
    rw [show ptab 21 = 79 by rfl]
    exact cnt_79
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 21)) = ptab 21 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_22 : Nat.nth Nat.Prime 22 = ptab 22 := by
  have hpn : Nat.Prime (ptab 22) := by decide
  have hc : Nat.count Nat.Prime (ptab 22) = 22 := by
    rw [show ptab 22 = 83 by rfl]
    exact cnt_83
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 22)) = ptab 22 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_23 : Nat.nth Nat.Prime 23 = ptab 23 := by
  have hpn : Nat.Prime (ptab 23) := by decide
  have hc : Nat.count Nat.Prime (ptab 23) = 23 := by
    rw [show ptab 23 = 89 by rfl]
    exact cnt_89
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 23)) = ptab 23 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_24 : Nat.nth Nat.Prime 24 = ptab 24 := by
  have hpn : Nat.Prime (ptab 24) := by decide
  have hc : Nat.count Nat.Prime (ptab 24) = 24 := by
    rw [show ptab 24 = 97 by rfl]
    exact cnt_97
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 24)) = ptab 24 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_25 : Nat.nth Nat.Prime 25 = ptab 25 := by
  have hpn : Nat.Prime (ptab 25) := by decide
  have hc : Nat.count Nat.Prime (ptab 25) = 25 := by
    rw [show ptab 25 = 101 by rfl]
    exact cnt_101
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 25)) = ptab 25 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_26 : Nat.nth Nat.Prime 26 = ptab 26 := by
  have hpn : Nat.Prime (ptab 26) := by decide
  have hc : Nat.count Nat.Prime (ptab 26) = 26 := by
    rw [show ptab 26 = 103 by rfl]
    exact cnt_103
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 26)) = ptab 26 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_27 : Nat.nth Nat.Prime 27 = ptab 27 := by
  have hpn : Nat.Prime (ptab 27) := by decide
  have hc : Nat.count Nat.Prime (ptab 27) = 27 := by
    rw [show ptab 27 = 107 by rfl]
    exact cnt_107
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 27)) = ptab 27 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_28 : Nat.nth Nat.Prime 28 = ptab 28 := by
  have hpn : Nat.Prime (ptab 28) := by decide
  have hc : Nat.count Nat.Prime (ptab 28) = 28 := by
    rw [show ptab 28 = 109 by rfl]
    exact cnt_109
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 28)) = ptab 28 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_29 : Nat.nth Nat.Prime 29 = ptab 29 := by
  have hpn : Nat.Prime (ptab 29) := by decide
  have hc : Nat.count Nat.Prime (ptab 29) = 29 := by
    rw [show ptab 29 = 113 by rfl]
    exact cnt_113
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 29)) = ptab 29 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_30 : Nat.nth Nat.Prime 30 = ptab 30 := by
  have hpn : Nat.Prime (ptab 30) := by decide
  have hc : Nat.count Nat.Prime (ptab 30) = 30 := by
    rw [show ptab 30 = 127 by rfl]
    exact cnt_127
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 30)) = ptab 30 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_31 : Nat.nth Nat.Prime 31 = ptab 31 := by
  have hpn : Nat.Prime (ptab 31) := by decide
  have hc : Nat.count Nat.Prime (ptab 31) = 31 := by
    rw [show ptab 31 = 131 by rfl]
    exact cnt_131
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 31)) = ptab 31 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_32 : Nat.nth Nat.Prime 32 = ptab 32 := by
  have hpn : Nat.Prime (ptab 32) := by decide
  have hc : Nat.count Nat.Prime (ptab 32) = 32 := by
    rw [show ptab 32 = 137 by rfl]
    exact cnt_137
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 32)) = ptab 32 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_33 : Nat.nth Nat.Prime 33 = ptab 33 := by
  have hpn : Nat.Prime (ptab 33) := by decide
  have hc : Nat.count Nat.Prime (ptab 33) = 33 := by
    rw [show ptab 33 = 139 by rfl]
    exact cnt_139
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 33)) = ptab 33 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_34 : Nat.nth Nat.Prime 34 = ptab 34 := by
  have hpn : Nat.Prime (ptab 34) := by decide
  have hc : Nat.count Nat.Prime (ptab 34) = 34 := by
    rw [show ptab 34 = 149 by rfl]
    exact cnt_149
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 34)) = ptab 34 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_35 : Nat.nth Nat.Prime 35 = ptab 35 := by
  have hpn : Nat.Prime (ptab 35) := by decide
  have hc : Nat.count Nat.Prime (ptab 35) = 35 := by
    rw [show ptab 35 = 151 by rfl]
    exact cnt_151
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 35)) = ptab 35 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_36 : Nat.nth Nat.Prime 36 = ptab 36 := by
  have hpn : Nat.Prime (ptab 36) := by decide
  have hc : Nat.count Nat.Prime (ptab 36) = 36 := by
    rw [show ptab 36 = 157 by rfl]
    exact cnt_157
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 36)) = ptab 36 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_37 : Nat.nth Nat.Prime 37 = ptab 37 := by
  have hpn : Nat.Prime (ptab 37) := by decide
  have hc : Nat.count Nat.Prime (ptab 37) = 37 := by
    rw [show ptab 37 = 163 by rfl]
    exact cnt_163
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 37)) = ptab 37 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_38 : Nat.nth Nat.Prime 38 = ptab 38 := by
  have hpn : Nat.Prime (ptab 38) := by decide
  have hc : Nat.count Nat.Prime (ptab 38) = 38 := by
    rw [show ptab 38 = 167 by rfl]
    exact cnt_167
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 38)) = ptab 38 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_39 : Nat.nth Nat.Prime 39 = ptab 39 := by
  have hpn : Nat.Prime (ptab 39) := by decide
  have hc : Nat.count Nat.Prime (ptab 39) = 39 := by
    rw [show ptab 39 = 173 by rfl]
    exact cnt_173
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 39)) = ptab 39 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_40 : Nat.nth Nat.Prime 40 = ptab 40 := by
  have hpn : Nat.Prime (ptab 40) := by decide
  have hc : Nat.count Nat.Prime (ptab 40) = 40 := by
    rw [show ptab 40 = 179 by rfl]
    exact cnt_179
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 40)) = ptab 40 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_41 : Nat.nth Nat.Prime 41 = ptab 41 := by
  have hpn : Nat.Prime (ptab 41) := by decide
  have hc : Nat.count Nat.Prime (ptab 41) = 41 := by
    rw [show ptab 41 = 181 by rfl]
    exact cnt_181
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 41)) = ptab 41 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_42 : Nat.nth Nat.Prime 42 = ptab 42 := by
  have hpn : Nat.Prime (ptab 42) := by decide
  have hc : Nat.count Nat.Prime (ptab 42) = 42 := by
    rw [show ptab 42 = 191 by rfl]
    exact cnt_191
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 42)) = ptab 42 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_43 : Nat.nth Nat.Prime 43 = ptab 43 := by
  have hpn : Nat.Prime (ptab 43) := by decide
  have hc : Nat.count Nat.Prime (ptab 43) = 43 := by
    rw [show ptab 43 = 193 by rfl]
    exact cnt_193
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 43)) = ptab 43 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_44 : Nat.nth Nat.Prime 44 = ptab 44 := by
  have hpn : Nat.Prime (ptab 44) := by decide
  have hc : Nat.count Nat.Prime (ptab 44) = 44 := by
    rw [show ptab 44 = 197 by rfl]
    exact cnt_197
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 44)) = ptab 44 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_45 : Nat.nth Nat.Prime 45 = ptab 45 := by
  have hpn : Nat.Prime (ptab 45) := by decide
  have hc : Nat.count Nat.Prime (ptab 45) = 45 := by
    rw [show ptab 45 = 199 by rfl]
    exact cnt_199
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 45)) = ptab 45 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_46 : Nat.nth Nat.Prime 46 = ptab 46 := by
  have hpn : Nat.Prime (ptab 46) := by decide
  have hc : Nat.count Nat.Prime (ptab 46) = 46 := by
    rw [show ptab 46 = 211 by rfl]
    exact cnt_211
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 46)) = ptab 46 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_47 : Nat.nth Nat.Prime 47 = ptab 47 := by
  have hpn : Nat.Prime (ptab 47) := by decide
  have hc : Nat.count Nat.Prime (ptab 47) = 47 := by
    rw [show ptab 47 = 223 by rfl]
    exact cnt_223
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 47)) = ptab 47 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_48 : Nat.nth Nat.Prime 48 = ptab 48 := by
  have hpn : Nat.Prime (ptab 48) := by decide
  have hc : Nat.count Nat.Prime (ptab 48) = 48 := by
    rw [show ptab 48 = 227 by rfl]
    exact cnt_227
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 48)) = ptab 48 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_49 : Nat.nth Nat.Prime 49 = ptab 49 := by
  have hpn : Nat.Prime (ptab 49) := by decide
  have hc : Nat.count Nat.Prime (ptab 49) = 49 := by
    rw [show ptab 49 = 229 by rfl]
    exact cnt_229
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 49)) = ptab 49 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_50 : Nat.nth Nat.Prime 50 = ptab 50 := by
  have hpn : Nat.Prime (ptab 50) := by decide
  have hc : Nat.count Nat.Prime (ptab 50) = 50 := by
    rw [show ptab 50 = 233 by rfl]
    exact cnt_233
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 50)) = ptab 50 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_51 : Nat.nth Nat.Prime 51 = ptab 51 := by
  have hpn : Nat.Prime (ptab 51) := by decide
  have hc : Nat.count Nat.Prime (ptab 51) = 51 := by
    rw [show ptab 51 = 239 by rfl]
    exact cnt_239
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 51)) = ptab 51 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_52 : Nat.nth Nat.Prime 52 = ptab 52 := by
  have hpn : Nat.Prime (ptab 52) := by decide
  have hc : Nat.count Nat.Prime (ptab 52) = 52 := by
    rw [show ptab 52 = 241 by rfl]
    exact cnt_241
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 52)) = ptab 52 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_53 : Nat.nth Nat.Prime 53 = ptab 53 := by
  have hpn : Nat.Prime (ptab 53) := by decide
  have hc : Nat.count Nat.Prime (ptab 53) = 53 := by
    rw [show ptab 53 = 251 by rfl]
    exact cnt_251
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 53)) = ptab 53 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_54 : Nat.nth Nat.Prime 54 = ptab 54 := by
  have hpn : Nat.Prime (ptab 54) := by decide
  have hc : Nat.count Nat.Prime (ptab 54) = 54 := by
    rw [show ptab 54 = 257 by rfl]
    exact cnt_257
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 54)) = ptab 54 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_55 : Nat.nth Nat.Prime 55 = ptab 55 := by
  have hpn : Nat.Prime (ptab 55) := by decide
  have hc : Nat.count Nat.Prime (ptab 55) = 55 := by
    rw [show ptab 55 = 263 by rfl]
    exact cnt_263
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 55)) = ptab 55 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_56 : Nat.nth Nat.Prime 56 = ptab 56 := by
  have hpn : Nat.Prime (ptab 56) := by decide
  have hc : Nat.count Nat.Prime (ptab 56) = 56 := by
    rw [show ptab 56 = 269 by rfl]
    exact cnt_269
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 56)) = ptab 56 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_57 : Nat.nth Nat.Prime 57 = ptab 57 := by
  have hpn : Nat.Prime (ptab 57) := by decide
  have hc : Nat.count Nat.Prime (ptab 57) = 57 := by
    rw [show ptab 57 = 271 by rfl]
    exact cnt_271
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 57)) = ptab 57 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_58 : Nat.nth Nat.Prime 58 = ptab 58 := by
  have hpn : Nat.Prime (ptab 58) := by decide
  have hc : Nat.count Nat.Prime (ptab 58) = 58 := by
    rw [show ptab 58 = 277 by rfl]
    exact cnt_277
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 58)) = ptab 58 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_59 : Nat.nth Nat.Prime 59 = ptab 59 := by
  have hpn : Nat.Prime (ptab 59) := by decide
  have hc : Nat.count Nat.Prime (ptab 59) = 59 := by
    rw [show ptab 59 = 281 by rfl]
    exact cnt_281
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 59)) = ptab 59 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_60 : Nat.nth Nat.Prime 60 = ptab 60 := by
  have hpn : Nat.Prime (ptab 60) := by decide
  have hc : Nat.count Nat.Prime (ptab 60) = 60 := by
    rw [show ptab 60 = 283 by rfl]
    exact cnt_283
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 60)) = ptab 60 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_61 : Nat.nth Nat.Prime 61 = ptab 61 := by
  have hpn : Nat.Prime (ptab 61) := by decide
  have hc : Nat.count Nat.Prime (ptab 61) = 61 := by
    rw [show ptab 61 = 293 by rfl]
    exact cnt_293
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 61)) = ptab 61 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_62 : Nat.nth Nat.Prime 62 = ptab 62 := by
  have hpn : Nat.Prime (ptab 62) := by decide
  have hc : Nat.count Nat.Prime (ptab 62) = 62 := by
    rw [show ptab 62 = 307 by rfl]
    exact cnt_307
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 62)) = ptab 62 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_63 : Nat.nth Nat.Prime 63 = ptab 63 := by
  have hpn : Nat.Prime (ptab 63) := by decide
  have hc : Nat.count Nat.Prime (ptab 63) = 63 := by
    rw [show ptab 63 = 311 by rfl]
    exact cnt_311
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 63)) = ptab 63 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_64 : Nat.nth Nat.Prime 64 = ptab 64 := by
  have hpn : Nat.Prime (ptab 64) := by decide
  have hc : Nat.count Nat.Prime (ptab 64) = 64 := by
    rw [show ptab 64 = 313 by rfl]
    exact cnt_313
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 64)) = ptab 64 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key
lemma nth_ptab_65 : Nat.nth Nat.Prime 65 = ptab 65 := by
  have hpn : Nat.Prime (ptab 65) := by decide
  have hc : Nat.count Nat.Prime (ptab 65) = 65 := by
    rw [show ptab 65 = 317 by rfl]
    exact cnt_317
  have key : Nat.nth Nat.Prime (Nat.count Nat.Prime (ptab 65)) = ptab 65 := Nat.nth_count hpn
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans key

/-- The table `ptab` agrees with the `(i+1)`-st prime `Nat.nth Nat.Prime i`. -/
theorem solution (i : ℕ) (hi : i < 66) : Nat.nth Nat.Prime i = ptab i := by
  interval_cases i
  · exact nth_ptab_0
  · exact nth_ptab_1
  · exact nth_ptab_2
  · exact nth_ptab_3
  · exact nth_ptab_4
  · exact nth_ptab_5
  · exact nth_ptab_6
  · exact nth_ptab_7
  · exact nth_ptab_8
  · exact nth_ptab_9
  · exact nth_ptab_10
  · exact nth_ptab_11
  · exact nth_ptab_12
  · exact nth_ptab_13
  · exact nth_ptab_14
  · exact nth_ptab_15
  · exact nth_ptab_16
  · exact nth_ptab_17
  · exact nth_ptab_18
  · exact nth_ptab_19
  · exact nth_ptab_20
  · exact nth_ptab_21
  · exact nth_ptab_22
  · exact nth_ptab_23
  · exact nth_ptab_24
  · exact nth_ptab_25
  · exact nth_ptab_26
  · exact nth_ptab_27
  · exact nth_ptab_28
  · exact nth_ptab_29
  · exact nth_ptab_30
  · exact nth_ptab_31
  · exact nth_ptab_32
  · exact nth_ptab_33
  · exact nth_ptab_34
  · exact nth_ptab_35
  · exact nth_ptab_36
  · exact nth_ptab_37
  · exact nth_ptab_38
  · exact nth_ptab_39
  · exact nth_ptab_40
  · exact nth_ptab_41
  · exact nth_ptab_42
  · exact nth_ptab_43
  · exact nth_ptab_44
  · exact nth_ptab_45
  · exact nth_ptab_46
  · exact nth_ptab_47
  · exact nth_ptab_48
  · exact nth_ptab_49
  · exact nth_ptab_50
  · exact nth_ptab_51
  · exact nth_ptab_52
  · exact nth_ptab_53
  · exact nth_ptab_54
  · exact nth_ptab_55
  · exact nth_ptab_56
  · exact nth_ptab_57
  · exact nth_ptab_58
  · exact nth_ptab_59
  · exact nth_ptab_60
  · exact nth_ptab_61
  · exact nth_ptab_62
  · exact nth_ptab_63
  · exact nth_ptab_64
  · exact nth_ptab_65

end TaoFivePrimes

open TaoFivePrimes

/-- The verification harness looks for `solution` at the root;
the namespaced proof is re-exported here. -/
theorem solution (i : ℕ) (hi : i < 66) : Nat.nth Nat.Prime i = TaoFivePrimes.ptab i :=
  TaoFivePrimes.solution i hi

#print axioms solution
