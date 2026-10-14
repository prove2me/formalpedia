-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T13:58:51.612505+00:00
-- url     : https://prove2.me/submissions/538d2d8d-46d7-4556-902c-ada5d8118903

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04982
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05000

theorem solution (n : Nat)
    (hn : 2701984647071959 < n) (hupper : n <= 3112164993040603) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2899818166799293 n with h2 | h2
  · -- n > 2899818166799293
    rcases Nat.lt_or_ge 2999871931905053 n with h4 | h4
    · -- n > 2999871931905053
      rcases Nat.lt_or_ge 3051186552281107 n with h6 | h6
      · -- n > 3051186552281107
        rcases Nat.lt_or_ge 3077172689224993 n with h8 | h8
        · -- n > 3077172689224993
          rcases Nat.lt_or_ge 3094619298626279 n with h10 | h10
          · -- n > 3094619298626279
            rcases Nat.lt_or_ge 3103378424980133 n with h12 | h12
            · -- n > 3103378424980133
              exact RamareSaouter2003.prime_interval_nat_ladder_c05000 n (by omega) (by omega)
            · -- n <= 3103378424980133
              exact RamareSaouter2003.prime_interval_nat_ladder_c04999 n (by omega) (by omega)
          · -- n <= 3094619298626279
            rcases Nat.lt_or_ge 3085884215536537 n with h12 | h12
            · -- n > 3085884215536537
              exact RamareSaouter2003.prime_interval_nat_ladder_c04998 n (by omega) (by omega)
            · -- n <= 3085884215536537
              exact RamareSaouter2003.prime_interval_nat_ladder_c04997 n (by omega) (by omega)
        · -- n <= 3077172689224993
          rcases Nat.lt_or_ge 3059825291032001 n with h10 | h10
          · -- n > 3059825291032001
            rcases Nat.lt_or_ge 3068485878735337 n with h12 | h12
            · -- n > 3068485878735337
              exact RamareSaouter2003.prime_interval_nat_ladder_c04996 n (by omega) (by omega)
            · -- n <= 3068485878735337
              exact RamareSaouter2003.prime_interval_nat_ladder_c04995 n (by omega) (by omega)
          · -- n <= 3059825291032001
            exact RamareSaouter2003.prime_interval_nat_ladder_c04994 n (by omega) (by omega)
      · -- n <= 3051186552281107
        rcases Nat.lt_or_ge 3025419840754397 n with h8 | h8
        · -- n > 3025419840754397
          rcases Nat.lt_or_ge 3033984488751361 n with h10 | h10
          · -- n > 3033984488751361
            rcases Nat.lt_or_ge 3042572933811899 n with h12 | h12
            · -- n > 3042572933811899
              exact RamareSaouter2003.prime_interval_nat_ladder_c04993 n (by omega) (by omega)
            · -- n <= 3042572933811899
              exact RamareSaouter2003.prime_interval_nat_ladder_c04992 n (by omega) (by omega)
          · -- n <= 3033984488751361
            exact RamareSaouter2003.prime_interval_nat_ladder_c04991 n (by omega) (by omega)
        · -- n <= 3025419840754397
          rcases Nat.lt_or_ge 3008365043651951 n with h10 | h10
          · -- n > 3008365043651951
            rcases Nat.lt_or_ge 3016879935453221 n with h12 | h12
            · -- n > 3016879935453221
              exact RamareSaouter2003.prime_interval_nat_ladder_c04990 n (by omega) (by omega)
            · -- n <= 3016879935453221
              exact RamareSaouter2003.prime_interval_nat_ladder_c04989 n (by omega) (by omega)
          · -- n <= 3008365043651951
            exact RamareSaouter2003.prime_interval_nat_ladder_c04988 n (by omega) (by omega)
    · -- n <= 2999871931905053
      rcases Nat.lt_or_ge 2949421721589631 n with h6 | h6
      · -- n > 2949421721589631
        rcases Nat.lt_or_ge 2974539899057179 n with h8 | h8
        · -- n > 2974539899057179
          rcases Nat.lt_or_ge 2982960397086623 n with h10 | h10
          · -- n > 2982960397086623
            rcases Nat.lt_or_ge 2991404501831491 n with h12 | h12
            · -- n > 2991404501831491
              exact RamareSaouter2003.prime_interval_nat_ladder_c04987 n (by omega) (by omega)
            · -- n <= 2991404501831491
              exact RamareSaouter2003.prime_interval_nat_ladder_c04986 n (by omega) (by omega)
          · -- n <= 2982960397086623
            exact RamareSaouter2003.prime_interval_nat_ladder_c04985 n (by omega) (by omega)
        · -- n <= 2974539899057179
          rcases Nat.lt_or_ge 2957771156503403 n with h10 | h10
          · -- n > 2957771156503403
            rcases Nat.lt_or_ge 2966143611327929 n with h12 | h12
            · -- n > 2966143611327929
              exact RamareSaouter2003.prime_interval_nat_ladder_c04984 n (by omega) (by omega)
            · -- n <= 2966143611327929
              exact RamareSaouter2003.prime_interval_nat_ladder_c04983 n (by omega) (by omega)
          · -- n <= 2957771156503403
            exact RamareSaouter2003.prime_interval_nat_ladder_c04982 n (by omega) (by omega)
      · -- n <= 2949421721589631
        rcases Nat.lt_or_ge 2924514742109861 n with h8 | h8
        · -- n > 2924514742109861
          rcases Nat.lt_or_ge 2932792697289341 n with h10 | h10
          · -- n > 2932792697289341
            rcases Nat.lt_or_ge 2941095690909847 n with h12 | h12
            · -- n > 2941095690909847
              exact RamareSaouter2003.prime_interval_nat_ladder_c04981 n (by omega) (by omega)
            · -- n <= 2941095690909847
              exact RamareSaouter2003.prime_interval_nat_ladder_c04980 n (by omega) (by omega)
          · -- n <= 2932792697289341
            exact RamareSaouter2003.prime_interval_nat_ladder_c04979 n (by omega) (by omega)
        · -- n <= 2924514742109861
          rcases Nat.lt_or_ge 2908026283224541 n with h10 | h10
          · -- n > 2908026283224541
            rcases Nat.lt_or_ge 2916258854263723 n with h12 | h12
            · -- n > 2916258854263723
              exact RamareSaouter2003.prime_interval_nat_ladder_c04978 n (by omega) (by omega)
            · -- n <= 2916258854263723
              exact RamareSaouter2003.prime_interval_nat_ladder_c04977 n (by omega) (by omega)
          · -- n <= 2908026283224541
            exact RamareSaouter2003.prime_interval_nat_ladder_c04976 n (by omega) (by omega)
  · -- n <= 2899818166799293
    rcases Nat.lt_or_ge 2795199560787373 n with h4 | h4
    · -- n > 2795199560787373
      rcases Nat.lt_or_ge 2843001693506207 n with h6 | h6
      · -- n > 2843001693506207
        rcases Nat.lt_or_ge 2867212755303437 n with h8 | h8
        · -- n > 2867212755303437
          rcases Nat.lt_or_ge 2883468630454849 n with h10 | h10
          · -- n > 2883468630454849
            rcases Nat.lt_or_ge 2891632405311037 n with h12 | h12
            · -- n > 2891632405311037
              exact RamareSaouter2003.prime_interval_nat_ladder_c04975 n (by omega) (by omega)
            · -- n <= 2891632405311037
              exact RamareSaouter2003.prime_interval_nat_ladder_c04974 n (by omega) (by omega)
          · -- n <= 2883468630454849
            rcases Nat.lt_or_ge 2875328188922737 n with h12 | h12
            · -- n > 2875328188922737
              exact RamareSaouter2003.prime_interval_nat_ladder_c04973 n (by omega) (by omega)
            · -- n <= 2875328188922737
              exact RamareSaouter2003.prime_interval_nat_ladder_c04972 n (by omega) (by omega)
        · -- n <= 2867212755303437
          rcases Nat.lt_or_ge 2851050460916731 n with h10 | h10
          · -- n > 2851050460916731
            rcases Nat.lt_or_ge 2859119692979783 n with h12 | h12
            · -- n > 2859119692979783
              exact RamareSaouter2003.prime_interval_nat_ladder_c04971 n (by omega) (by omega)
            · -- n <= 2859119692979783
              exact RamareSaouter2003.prime_interval_nat_ladder_c04970 n (by omega) (by omega)
          · -- n <= 2851050460916731
            exact RamareSaouter2003.prime_interval_nat_ladder_c04969 n (by omega) (by omega)
      · -- n <= 2843001693506207
        rcases Nat.lt_or_ge 2818996391891503 n with h8 | h8
        · -- n > 2818996391891503
          rcases Nat.lt_or_ge 2826975933248191 n with h10 | h10
          · -- n > 2826975933248191
            rcases Nat.lt_or_ge 2834977720847071 n with h12 | h12
            · -- n > 2834977720847071
              exact RamareSaouter2003.prime_interval_nat_ladder_c04968 n (by omega) (by omega)
            · -- n <= 2834977720847071
              exact RamareSaouter2003.prime_interval_nat_ladder_c04967 n (by omega) (by omega)
          · -- n <= 2826975933248191
            exact RamareSaouter2003.prime_interval_nat_ladder_c04966 n (by omega) (by omega)
        · -- n <= 2818996391891503
          rcases Nat.lt_or_ge 2803107780168799 n with h10 | h10
          · -- n > 2803107780168799
            rcases Nat.lt_or_ge 2811039051220031 n with h12 | h12
            · -- n > 2811039051220031
              exact RamareSaouter2003.prime_interval_nat_ladder_c04965 n (by omega) (by omega)
            · -- n <= 2811039051220031
              exact RamareSaouter2003.prime_interval_nat_ladder_c04964 n (by omega) (by omega)
          · -- n <= 2803107780168799
            exact RamareSaouter2003.prime_interval_nat_ladder_c04963 n (by omega) (by omega)
    · -- n <= 2795199560787373
      rcases Nat.lt_or_ge 2748196505051539 n with h6 | h6
      · -- n > 2748196505051539
        rcases Nat.lt_or_ge 2771596041661831 n with h8 | h8
        · -- n > 2771596041661831
          rcases Nat.lt_or_ge 2779440247952383 n with h10 | h10
          · -- n > 2779440247952383
            rcases Nat.lt_or_ge 2787309057300953 n with h12 | h12
            · -- n > 2787309057300953
              exact RamareSaouter2003.prime_interval_nat_ladder_c04962 n (by omega) (by omega)
            · -- n <= 2787309057300953
              exact RamareSaouter2003.prime_interval_nat_ladder_c04961 n (by omega) (by omega)
          · -- n <= 2779440247952383
            exact RamareSaouter2003.prime_interval_nat_ladder_c04960 n (by omega) (by omega)
        · -- n <= 2771596041661831
          rcases Nat.lt_or_ge 2755971533884421 n with h10 | h10
          · -- n > 2755971533884421
            rcases Nat.lt_or_ge 2763773534632931 n with h12 | h12
            · -- n > 2763773534632931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04959 n (by omega) (by omega)
            · -- n <= 2763773534632931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04958 n (by omega) (by omega)
          · -- n <= 2755971533884421
            exact RamareSaouter2003.prime_interval_nat_ladder_c04957 n (by omega) (by omega)
      · -- n <= 2748196505051539
        rcases Nat.lt_or_ge 2724992105966161 n with h8 | h8
        · -- n > 2724992105966161
          rcases Nat.lt_or_ge 2732704155454979 n with h10 | h10
          · -- n > 2732704155454979
            rcases Nat.lt_or_ge 2740438524373079 n with h12 | h12
            · -- n > 2740438524373079
              exact RamareSaouter2003.prime_interval_nat_ladder_c04956 n (by omega) (by omega)
            · -- n <= 2740438524373079
              exact RamareSaouter2003.prime_interval_nat_ladder_c04955 n (by omega) (by omega)
          · -- n <= 2732704155454979
            exact RamareSaouter2003.prime_interval_nat_ladder_c04954 n (by omega) (by omega)
        · -- n <= 2724992105966161
          rcases Nat.lt_or_ge 2709634114698067 n with h10 | h10
          · -- n > 2709634114698067
            rcases Nat.lt_or_ge 2717302629305941 n with h12 | h12
            · -- n > 2717302629305941
              exact RamareSaouter2003.prime_interval_nat_ladder_c04953 n (by omega) (by omega)
            · -- n <= 2717302629305941
              exact RamareSaouter2003.prime_interval_nat_ladder_c04952 n (by omega) (by omega)
          · -- n <= 2709634114698067
            exact RamareSaouter2003.prime_interval_nat_ladder_c04951 n (by omega) (by omega)
