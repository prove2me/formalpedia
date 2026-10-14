-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp161
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T11:25:26.786388+00:00
-- url     : https://prove2.me/submissions/3469938f-387b-4b0b-b7a7-a2462452209e

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08000
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08031

theorem solution (n : Nat)
    (hn : 14269908471619535531 < n) (hupper : n <= 16390314104476856209) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 15271801284184879387 n with h2 | h2
  · -- n > 15271801284184879387
    rcases Nat.lt_or_ge 15798826682548590827 n with h4 | h4
    · -- n > 15798826682548590827
      rcases Nat.lt_or_ge 16069120641075406439 n with h6 | h6
      · -- n > 16069120641075406439
        rcases Nat.lt_or_ge 16205996910550782989 n with h8 | h8
        · -- n > 16205996910550782989
          rcases Nat.lt_or_ge 16297894842467947003 n with h10 | h10
          · -- n > 16297894842467947003
            rcases Nat.lt_or_ge 16344039117479780521 n with h12 | h12
            · -- n > 16344039117479780521
              exact RamareSaouter2003.prime_interval_nat_ladder_c08031 n (by omega) (by omega)
            · -- n <= 16344039117479780521
              exact RamareSaouter2003.prime_interval_nat_ladder_c08030 n (by omega) (by omega)
          · -- n <= 16297894842467947003
            rcases Nat.lt_or_ge 16251881043084108001 n with h12 | h12
            · -- n > 16251881043084108001
              exact RamareSaouter2003.prime_interval_nat_ladder_c08029 n (by omega) (by omega)
            · -- n <= 16251881043084108001
              exact RamareSaouter2003.prime_interval_nat_ladder_c08028 n (by omega) (by omega)
        · -- n <= 16205996910550782989
          rcases Nat.lt_or_ge 16114617232935139543 n with h10 | h10
          · -- n > 16114617232935139543
            rcases Nat.lt_or_ge 16160242588501649633 n with h12 | h12
            · -- n > 16160242588501649633
              exact RamareSaouter2003.prime_interval_nat_ladder_c08027 n (by omega) (by omega)
            · -- n <= 16160242588501649633
              exact RamareSaouter2003.prime_interval_nat_ladder_c08026 n (by omega) (by omega)
          · -- n <= 16114617232935139543
            exact RamareSaouter2003.prime_interval_nat_ladder_c08025 n (by omega) (by omega)
      · -- n <= 16069120641075406439
        rcases Nat.lt_or_ge 15933400752715994903 n with h8 | h8
        · -- n > 15933400752715994903
          rcases Nat.lt_or_ge 15978512773415347213 n with h10 | h10
          · -- n > 15978512773415347213
            rcases Nat.lt_or_ge 16023752677663978967 n with h12 | h12
            · -- n > 16023752677663978967
              exact RamareSaouter2003.prime_interval_nat_ladder_c08024 n (by omega) (by omega)
            · -- n <= 16023752677663978967
              exact RamareSaouter2003.prime_interval_nat_ladder_c08023 n (by omega) (by omega)
          · -- n <= 15978512773415347213
            exact RamareSaouter2003.prime_interval_nat_ladder_c08022 n (by omega) (by omega)
        · -- n <= 15933400752715994903
          rcases Nat.lt_or_ge 15843557845043213213 n with h10 | h10
          · -- n > 15843557845043213213
            rcases Nat.lt_or_ge 15888415778604756263 n with h12 | h12
            · -- n > 15888415778604756263
              exact RamareSaouter2003.prime_interval_nat_ladder_c08021 n (by omega) (by omega)
            · -- n <= 15888415778604756263
              exact RamareSaouter2003.prime_interval_nat_ladder_c08020 n (by omega) (by omega)
          · -- n <= 15843557845043213213
            exact RamareSaouter2003.prime_interval_nat_ladder_c08019 n (by omega) (by omega)
    · -- n <= 15798826682548590827
      rcases Nat.lt_or_ge 15533079237488244037 n with h6 | h6
      · -- n > 15533079237488244037
        rcases Nat.lt_or_ge 15665389585041363439 n with h8 | h8
        · -- n > 15665389585041363439
          rcases Nat.lt_or_ge 15709743081669687307 n with h10 | h10
          · -- n > 15709743081669687307
            rcases Nat.lt_or_ge 15754221927181151809 n with h12 | h12
            · -- n > 15754221927181151809
              exact RamareSaouter2003.prime_interval_nat_ladder_c08018 n (by omega) (by omega)
            · -- n <= 15754221927181151809
              exact RamareSaouter2003.prime_interval_nat_ladder_c08017 n (by omega) (by omega)
          · -- n <= 15709743081669687307
            exact RamareSaouter2003.prime_interval_nat_ladder_c08016 n (by omega) (by omega)
        · -- n <= 15665389585041363439
          rcases Nat.lt_or_ge 15577058006919041683 n with h10 | h10
          · -- n > 15577058006919041683
            rcases Nat.lt_or_ge 15621161386612046921 n with h12 | h12
            · -- n > 15621161386612046921
              exact RamareSaouter2003.prime_interval_nat_ladder_c08015 n (by omega) (by omega)
            · -- n <= 15621161386612046921
              exact RamareSaouter2003.prime_interval_nat_ladder_c08014 n (by omega) (by omega)
          · -- n <= 15577058006919041683
            exact RamareSaouter2003.prime_interval_nat_ladder_c08013 n (by omega) (by omega)
      · -- n <= 15533079237488244037
        rcases Nat.lt_or_ge 15401886157403916481 n with h8 | h8
        · -- n > 15401886157403916481
          rcases Nat.lt_or_ge 15445493614295482483 n with h10 | h10
          · -- n > 15445493614295482483
            rcases Nat.lt_or_ge 15489224529924177559 n with h12 | h12
            · -- n > 15489224529924177559
              exact RamareSaouter2003.prime_interval_nat_ladder_c08012 n (by omega) (by omega)
            · -- n <= 15489224529924177559
              exact RamareSaouter2003.prime_interval_nat_ladder_c08011 n (by omega) (by omega)
          · -- n <= 15445493614295482483
            exact RamareSaouter2003.prime_interval_nat_ladder_c08010 n (by omega) (by omega)
        · -- n <= 15401886157403916481
          rcases Nat.lt_or_ge 15315040417339063253 n with h10 | h10
          · -- n > 15315040417339063253
            rcases Nat.lt_or_ge 15358401874179732787 n with h12 | h12
            · -- n > 15358401874179732787
              exact RamareSaouter2003.prime_interval_nat_ladder_c08009 n (by omega) (by omega)
            · -- n <= 15358401874179732787
              exact RamareSaouter2003.prime_interval_nat_ladder_c08008 n (by omega) (by omega)
          · -- n <= 15315040417339063253
            exact RamareSaouter2003.prime_interval_nat_ladder_c08007 n (by omega) (by omega)
  · -- n <= 15271801284184879387
    rcases Nat.lt_or_ge 14762357600579079871 n with h4 | h4
    · -- n > 14762357600579079871
      rcases Nat.lt_or_ge 15014918739926099567 n with h6 | h6
      · -- n > 15014918739926099567
        rcases Nat.lt_or_ge 15142815341642308361 n with h8 | h8
        · -- n > 15142815341642308361
          rcases Nat.lt_or_ge 15185689258373044651 n with h10 | h10
          · -- n > 15185689258373044651
            rcases Nat.lt_or_ge 15228684192908482963 n with h12 | h12
            · -- n > 15228684192908482963
              exact RamareSaouter2003.prime_interval_nat_ladder_c08006 n (by omega) (by omega)
            · -- n <= 15228684192908482963
              exact RamareSaouter2003.prime_interval_nat_ladder_c08005 n (by omega) (by omega)
          · -- n <= 15185689258373044651
            exact RamareSaouter2003.prime_interval_nat_ladder_c08004 n (by omega) (by omega)
        · -- n <= 15142815341642308361
          rcases Nat.lt_or_ge 15057430540609381013 n with h10 | h10
          · -- n > 15057430540609381013
            rcases Nat.lt_or_ge 15100062700166024341 n with h12 | h12
            · -- n > 15100062700166024341
              exact RamareSaouter2003.prime_interval_nat_ladder_c08003 n (by omega) (by omega)
            · -- n <= 15100062700166024341
              exact RamareSaouter2003.prime_interval_nat_ladder_c08002 n (by omega) (by omega)
          · -- n <= 15057430540609381013
            exact RamareSaouter2003.prime_interval_nat_ladder_c08001 n (by omega) (by omega)
      · -- n <= 15014918739926099567
        rcases Nat.lt_or_ge 14888102581408030693 n with h8 | h8
        · -- n > 14888102581408030693
          rcases Nat.lt_or_ge 14930255281222193191 n with h10 | h10
          · -- n > 14930255281222193191
            rcases Nat.lt_or_ge 14972527244191140941 n with h12 | h12
            · -- n > 14972527244191140941
              exact RamareSaouter2003.prime_interval_nat_ladder_c08000 n (by omega) (by omega)
            · -- n <= 14972527244191140941
              exact RamareSaouter2003.prime_interval_nat_ladder_c07999 n (by omega) (by omega)
          · -- n <= 14930255281222193191
            exact RamareSaouter2003.prime_interval_nat_ladder_c07998 n (by omega) (by omega)
        · -- n <= 14888102581408030693
          rcases Nat.lt_or_ge 14804153761962378461 n with h10 | h10
          · -- n > 14804153761962378461
            rcases Nat.lt_or_ge 14846068799674940263 n with h12 | h12
            · -- n > 14846068799674940263
              exact RamareSaouter2003.prime_interval_nat_ladder_c07997 n (by omega) (by omega)
            · -- n <= 14846068799674940263
              exact RamareSaouter2003.prime_interval_nat_ladder_c07996 n (by omega) (by omega)
          · -- n <= 14804153761962378461
            exact RamareSaouter2003.prime_interval_nat_ladder_c07995 n (by omega) (by omega)
    · -- n <= 14762357600579079871
      rcases Nat.lt_or_ge 14514044301265969321 n with h6 | h6
      · -- n > 14514044301265969321
        rcases Nat.lt_or_ge 14637674411326848767 n with h8 | h8
        · -- n > 14637674411326848767
          rcases Nat.lt_or_ge 14679118112268031157 n with h10 | h10
          · -- n > 14679118112268031157
            rcases Nat.lt_or_ge 14720679048889350167 n with h12 | h12
            · -- n > 14720679048889350167
              exact RamareSaouter2003.prime_interval_nat_ladder_c07994 n (by omega) (by omega)
            · -- n <= 14720679048889350167
              exact RamareSaouter2003.prime_interval_nat_ladder_c07993 n (by omega) (by omega)
          · -- n <= 14679118112268031157
            exact RamareSaouter2003.prime_interval_nat_ladder_c07992 n (by omega) (by omega)
        · -- n <= 14637674411326848767
          rcases Nat.lt_or_ge 14555137921307939533 n with h10 | h10
          · -- n > 14555137921307939533
            rcases Nat.lt_or_ge 14596347995587320271 n with h12 | h12
            · -- n > 14596347995587320271
              exact RamareSaouter2003.prime_interval_nat_ladder_c07991 n (by omega) (by omega)
            · -- n <= 14596347995587320271
              exact RamareSaouter2003.prime_interval_nat_ladder_c07990 n (by omega) (by omega)
          · -- n <= 14555137921307939533
            exact RamareSaouter2003.prime_interval_nat_ladder_c07989 n (by omega) (by omega)
      · -- n <= 14514044301265969321
        rcases Nat.lt_or_ge 14391459288117049777 n with h8 | h8
        · -- n > 14391459288117049777
          rcases Nat.lt_or_ge 14432204888938689227 n with h10 | h10
          · -- n > 14432204888938689227
            rcases Nat.lt_or_ge 14473066820212510519 n with h12 | h12
            · -- n > 14473066820212510519
              exact RamareSaouter2003.prime_interval_nat_ladder_c07988 n (by omega) (by omega)
            · -- n <= 14473066820212510519
              exact RamareSaouter2003.prime_interval_nat_ladder_c07987 n (by omega) (by omega)
          · -- n <= 14432204888938689227
            exact RamareSaouter2003.prime_interval_nat_ladder_c07986 n (by omega) (by omega)
        · -- n <= 14391459288117049777
          rcases Nat.lt_or_ge 14310310870821001889 n with h10 | h10
          · -- n > 14310310870821001889
            rcases Nat.lt_or_ge 14350827723683880967 n with h12 | h12
            · -- n > 14350827723683880967
              exact RamareSaouter2003.prime_interval_nat_ladder_c07985 n (by omega) (by omega)
            · -- n <= 14350827723683880967
              exact RamareSaouter2003.prime_interval_nat_ladder_c07984 n (by omega) (by omega)
          · -- n <= 14310310870821001889
            exact RamareSaouter2003.prime_interval_nat_ladder_c07983 n (by omega) (by omega)
