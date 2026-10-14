-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T13:20:28.581927+00:00
-- url     : https://prove2.me/submissions/f71aa05d-291e-4146-8f0d-69d35f508640

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04884
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04900

theorem solution (n : Nat)
    (hn : 2036672748741173 < n) (hupper : n <= 2345869641159829) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2185806506961919 n with h2 | h2
  · -- n > 2185806506961919
    rcases Nat.lt_or_ge 2261222523413881 n with h4 | h4
    · -- n > 2261222523413881
      rcases Nat.lt_or_ge 2299905645072487 n with h6 | h6
      · -- n > 2299905645072487
        rcases Nat.lt_or_ge 2319492369144409 n with h8 | h8
        · -- n > 2319492369144409
          rcases Nat.lt_or_ge 2332644300692257 n with h10 | h10
          · -- n > 2332644300692257
            rcases Nat.lt_or_ge 2339248428049867 n with h12 | h12
            · -- n > 2339248428049867
              exact RamareSaouter2003.prime_interval_nat_ladder_c04900 n (by omega) (by omega)
            · -- n <= 2339248428049867
              exact RamareSaouter2003.prime_interval_nat_ladder_c04899 n (by omega) (by omega)
          · -- n <= 2332644300692257
            rcases Nat.lt_or_ge 2326058960805109 n with h12 | h12
            · -- n > 2326058960805109
              exact RamareSaouter2003.prime_interval_nat_ladder_c04898 n (by omega) (by omega)
            · -- n <= 2326058960805109
              exact RamareSaouter2003.prime_interval_nat_ladder_c04897 n (by omega) (by omega)
        · -- n <= 2319492369144409
          rcases Nat.lt_or_ge 2306416712095981 n with h10 | h10
          · -- n > 2306416712095981
            rcases Nat.lt_or_ge 2312943810856139 n with h12 | h12
            · -- n > 2312943810856139
              exact RamareSaouter2003.prime_interval_nat_ladder_c04896 n (by omega) (by omega)
            · -- n <= 2312943810856139
              exact RamareSaouter2003.prime_interval_nat_ladder_c04895 n (by omega) (by omega)
          · -- n <= 2306416712095981
            exact RamareSaouter2003.prime_interval_nat_ladder_c04894 n (by omega) (by omega)
      · -- n <= 2299905645072487
        rcases Nat.lt_or_ge 2280481241461609 n with h8 | h8
        · -- n > 2280481241461609
          rcases Nat.lt_or_ge 2286937707783341 n with h10 | h10
          · -- n > 2286937707783341
            rcases Nat.lt_or_ge 2293412398252853 n with h12 | h12
            · -- n > 2293412398252853
              exact RamareSaouter2003.prime_interval_nat_ladder_c04893 n (by omega) (by omega)
            · -- n <= 2293412398252853
              exact RamareSaouter2003.prime_interval_nat_ladder_c04892 n (by omega) (by omega)
          · -- n <= 2286937707783341
            exact RamareSaouter2003.prime_interval_nat_ladder_c04891 n (by omega) (by omega)
        · -- n <= 2280481241461609
          rcases Nat.lt_or_ge 2267624546492117 n with h10 | h10
          · -- n > 2267624546492117
            rcases Nat.lt_or_ge 2274042862498723 n with h12 | h12
            · -- n > 2274042862498723
              exact RamareSaouter2003.prime_interval_nat_ladder_c04890 n (by omega) (by omega)
            · -- n <= 2274042862498723
              exact RamareSaouter2003.prime_interval_nat_ladder_c04889 n (by omega) (by omega)
          · -- n <= 2267624546492117
            exact RamareSaouter2003.prime_interval_nat_ladder_c04888 n (by omega) (by omega)
    · -- n <= 2261222523413881
      rcases Nat.lt_or_ge 2223196110868153 n with h6 | h6
      · -- n > 2223196110868153
        rcases Nat.lt_or_ge 2242127483720749 n with h8 | h8
        · -- n > 2242127483720749
          rcases Nat.lt_or_ge 2248474079913623 n with h10 | h10
          · -- n > 2248474079913623
            rcases Nat.lt_or_ge 2254839618761057 n with h12 | h12
            · -- n > 2254839618761057
              exact RamareSaouter2003.prime_interval_nat_ladder_c04887 n (by omega) (by omega)
            · -- n <= 2254839618761057
              exact RamareSaouter2003.prime_interval_nat_ladder_c04886 n (by omega) (by omega)
          · -- n <= 2248474079913623
            exact RamareSaouter2003.prime_interval_nat_ladder_c04885 n (by omega) (by omega)
        · -- n <= 2242127483720749
          rcases Nat.lt_or_ge 2229485560658569 n with h10 | h10
          · -- n > 2229485560658569
            rcases Nat.lt_or_ge 2235797610972907 n with h12 | h12
            · -- n > 2235797610972907
              exact RamareSaouter2003.prime_interval_nat_ladder_c04884 n (by omega) (by omega)
            · -- n <= 2235797610972907
              exact RamareSaouter2003.prime_interval_nat_ladder_c04883 n (by omega) (by omega)
          · -- n <= 2229485560658569
            exact RamareSaouter2003.prime_interval_nat_ladder_c04882 n (by omega) (by omega)
      · -- n <= 2223196110868153
        rcases Nat.lt_or_ge 2204421906185417 n with h8 | h8
        · -- n > 2204421906185417
          rcases Nat.lt_or_ge 2210663042975489 n with h10 | h10
          · -- n > 2210663042975489
            rcases Nat.lt_or_ge 2216919875121349 n with h12 | h12
            · -- n > 2216919875121349
              exact RamareSaouter2003.prime_interval_nat_ladder_c04881 n (by omega) (by omega)
            · -- n <= 2216919875121349
              exact RamareSaouter2003.prime_interval_nat_ladder_c04880 n (by omega) (by omega)
          · -- n <= 2210663042975489
            exact RamareSaouter2003.prime_interval_nat_ladder_c04879 n (by omega) (by omega)
        · -- n <= 2204421906185417
          rcases Nat.lt_or_ge 2191995131101781 n with h10 | h10
          · -- n > 2191995131101781
            rcases Nat.lt_or_ge 2198199251391131 n with h12 | h12
            · -- n > 2198199251391131
              exact RamareSaouter2003.prime_interval_nat_ladder_c04878 n (by omega) (by omega)
            · -- n <= 2198199251391131
              exact RamareSaouter2003.prime_interval_nat_ladder_c04877 n (by omega) (by omega)
          · -- n <= 2191995131101781
            exact RamareSaouter2003.prime_interval_nat_ladder_c04876 n (by omega) (by omega)
  · -- n <= 2185806506961919
    rcases Nat.lt_or_ge 2106945476388787 n with h4 | h4
    · -- n > 2106945476388787
      rcases Nat.lt_or_ge 2142984048579103 n with h6 | h6
      · -- n > 2142984048579103
        rcases Nat.lt_or_ge 2161231274409871 n with h8 | h8
        · -- n > 2161231274409871
          rcases Nat.lt_or_ge 2173484788501493 n with h10 | h10
          · -- n > 2173484788501493
            rcases Nat.lt_or_ge 2179635314656411 n with h12 | h12
            · -- n > 2179635314656411
              exact RamareSaouter2003.prime_interval_nat_ladder_c04875 n (by omega) (by omega)
            · -- n <= 2179635314656411
              exact RamareSaouter2003.prime_interval_nat_ladder_c04874 n (by omega) (by omega)
          · -- n <= 2173484788501493
            rcases Nat.lt_or_ge 2167350303745069 n with h12 | h12
            · -- n > 2167350303745069
              exact RamareSaouter2003.prime_interval_nat_ladder_c04873 n (by omega) (by omega)
            · -- n <= 2167350303745069
              exact RamareSaouter2003.prime_interval_nat_ladder_c04872 n (by omega) (by omega)
        · -- n <= 2161231274409871
          rcases Nat.lt_or_ge 2149047817084489 n with h10 | h10
          · -- n > 2149047817084489
            rcases Nat.lt_or_ge 2155131946736149 n with h12 | h12
            · -- n > 2155131946736149
              exact RamareSaouter2003.prime_interval_nat_ladder_c04871 n (by omega) (by omega)
            · -- n <= 2155131946736149
              exact RamareSaouter2003.prime_interval_nat_ladder_c04870 n (by omega) (by omega)
          · -- n <= 2149047817084489
            exact RamareSaouter2003.prime_interval_nat_ladder_c04869 n (by omega) (by omega)
      · -- n <= 2142984048579103
        rcases Nat.lt_or_ge 2124890422964339 n with h8 | h8
        · -- n > 2124890422964339
          rcases Nat.lt_or_ge 2130904458163171 n with h10 | h10
          · -- n > 2130904458163171
            rcases Nat.lt_or_ge 2136934391964481 n with h12 | h12
            · -- n > 2136934391964481
              exact RamareSaouter2003.prime_interval_nat_ladder_c04868 n (by omega) (by omega)
            · -- n <= 2136934391964481
              exact RamareSaouter2003.prime_interval_nat_ladder_c04867 n (by omega) (by omega)
          · -- n <= 2130904458163171
            exact RamareSaouter2003.prime_interval_nat_ladder_c04866 n (by omega) (by omega)
        · -- n <= 2124890422964339
          rcases Nat.lt_or_ge 2112908982506779 n with h10 | h10
          · -- n > 2112908982506779
            rcases Nat.lt_or_ge 2118891235965607 n with h12 | h12
            · -- n > 2118891235965607
              exact RamareSaouter2003.prime_interval_nat_ladder_c04865 n (by omega) (by omega)
            · -- n <= 2118891235965607
              exact RamareSaouter2003.prime_interval_nat_ladder_c04864 n (by omega) (by omega)
          · -- n <= 2112908982506779
            exact RamareSaouter2003.prime_interval_nat_ladder_c04863 n (by omega) (by omega)
    · -- n <= 2106945476388787
      rcases Nat.lt_or_ge 2071513528167973 n with h6 | h6
      · -- n > 2071513528167973
        rcases Nat.lt_or_ge 2089153318518457 n with h8 | h8
        · -- n > 2089153318518457
          rcases Nat.lt_or_ge 2095066899937001 n with h10 | h10
          · -- n > 2095066899937001
            rcases Nat.lt_or_ge 2100998186873057 n with h12 | h12
            · -- n > 2100998186873057
              exact RamareSaouter2003.prime_interval_nat_ladder_c04862 n (by omega) (by omega)
            · -- n <= 2100998186873057
              exact RamareSaouter2003.prime_interval_nat_ladder_c04861 n (by omega) (by omega)
          · -- n <= 2095066899937001
            exact RamareSaouter2003.prime_interval_nat_ladder_c04860 n (by omega) (by omega)
        · -- n <= 2089153318518457
          rcases Nat.lt_or_ge 2077377219049729 n with h10 | h10
          · -- n > 2077377219049729
            rcases Nat.lt_or_ge 2083258418142787 n with h12 | h12
            · -- n > 2083258418142787
              exact RamareSaouter2003.prime_interval_nat_ladder_c04859 n (by omega) (by omega)
            · -- n <= 2083258418142787
              exact RamareSaouter2003.prime_interval_nat_ladder_c04858 n (by omega) (by omega)
          · -- n <= 2077377219049729
            exact RamareSaouter2003.prime_interval_nat_ladder_c04857 n (by omega) (by omega)
      · -- n <= 2071513528167973
        rcases Nat.lt_or_ge 2054019400492403 n with h8 | h8
        · -- n > 2054019400492403
          rcases Nat.lt_or_ge 2059834062960259 n with h10 | h10
          · -- n > 2059834062960259
            rcases Nat.lt_or_ge 2065665940130281 n with h12 | h12
            · -- n > 2065665940130281
              exact RamareSaouter2003.prime_interval_nat_ladder_c04856 n (by omega) (by omega)
            · -- n <= 2065665940130281
              exact RamareSaouter2003.prime_interval_nat_ladder_c04855 n (by omega) (by omega)
          · -- n <= 2059834062960259
            exact RamareSaouter2003.prime_interval_nat_ladder_c04854 n (by omega) (by omega)
        · -- n <= 2054019400492403
          rcases Nat.lt_or_ge 2042438596690997 n with h10 | h10
          · -- n > 2042438596690997
            rcases Nat.lt_or_ge 2048220563876863 n with h12 | h12
            · -- n > 2048220563876863
              exact RamareSaouter2003.prime_interval_nat_ladder_c04853 n (by omega) (by omega)
            · -- n <= 2048220563876863
              exact RamareSaouter2003.prime_interval_nat_ladder_c04852 n (by omega) (by omega)
          · -- n <= 2042438596690997
            exact RamareSaouter2003.prime_interval_nat_ladder_c04851 n (by omega) (by omega)
