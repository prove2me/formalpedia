-- Prove2me | solution 1 for RHX100000.bands
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:02:36.533533+00:00
-- url     : https://prove2.me/submissions/8b60d332-eb07-4b45-98a2-33b2ca7d1436

import Theorems.Thm_RH1E5_group_000
import Theorems.Thm_RH1E5_group_001
import Theorems.Thm_RH1E5_group_002
import Theorems.Thm_RH1E5_group_003
import Theorems.Thm_RH1E5_group_004
import Theorems.Thm_RH1E5_group_005
import Theorems.Thm_RH1E5_group_006
import Theorems.Thm_RH1E5_group_007
import Theorems.Thm_RH1E5_group_008
import Theorems.Thm_RH1E5_group_009
import Theorems.Thm_RH1E5_group_010
import Theorems.Thm_RH1E5_group_011
import Theorems.Thm_RH1E5_group_012
import Theorems.Thm_RH1E5_group_013
import Theorems.Thm_RH1E5_group_014
import Theorems.Thm_RH1E5_group_015
import Theorems.Thm_RH1E5_group_016
import Theorems.Thm_RH1E5_group_017
import Theorems.Thm_RH1E5_group_018
import Theorems.Thm_RH1E5_group_019
import Theorems.Thm_RH1E5_group_020
import Theorems.Thm_RH1E5_group_021
import Theorems.Thm_RH1E5_group_022
import Theorems.Thm_RH1E5_group_023
import Theorems.Thm_RH1E5_group_024
import Theorems.Thm_RH1E5_group_025
import Theorems.Thm_RH1E5_group_026
import Theorems.Thm_RH1E5_group_027
import Theorems.Thm_RH1E5_group_028
import Theorems.Thm_RH1E5_group_029
import Theorems.Thm_RH1E5_group_030
import Theorems.Thm_RH1E5_group_031
import Theorems.Thm_RH1E5_group_032
import Theorems.Thm_RH1E5_group_033
import Theorems.Thm_RH1E5_group_034
import Theorems.Thm_RH1E5_group_035
import Theorems.Thm_RH1E5_group_036
import Theorems.Thm_RH1E5_group_037
import Theorems.Thm_RH1E5_group_038
import Theorems.Thm_RH1E5_group_039
import Theorems.Thm_RH1E5_group_040
import Theorems.Thm_RH1E5_group_041
import Theorems.Thm_RH1E5_group_042
import Theorems.Thm_RH1E5_group_043
import Theorems.Thm_RH1E5_group_044
import Theorems.Thm_RH1E5_group_045
import Theorems.Thm_RH1E5_group_046
import Theorems.Thm_RH1E5_group_047
import Theorems.Thm_RH1E5_group_048
import Theorems.Thm_RH1E5_group_049
import Theorems.Thm_RH1E5_group_050
import Theorems.Thm_RH1E5_group_051
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.bands : RS5.BandZeros ((4259840000 : ℝ) / 65536) ((6553600000 : ℝ) / 65536) 52781 := by
  have a0 := RH1E5.group_000
  have a1 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0007.sL.t) (c := RH1E5_0015.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0007.sL]) (by norm_num [RS5.Sample.t, RH1E5_0007.sL, RH1E5_0015.sL]) a0 RH1E5.group_001
  have a2 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0015.sL.t) (c := RH1E5_0023.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0015.sL]) (by norm_num [RS5.Sample.t, RH1E5_0015.sL, RH1E5_0023.sL]) a1 RH1E5.group_002
  have a3 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0023.sL.t) (c := RH1E5_0031.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0023.sL]) (by norm_num [RS5.Sample.t, RH1E5_0023.sL, RH1E5_0031.sL]) a2 RH1E5.group_003
  have a4 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0031.sL.t) (c := RH1E5_0039.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0031.sL]) (by norm_num [RS5.Sample.t, RH1E5_0031.sL, RH1E5_0039.sL]) a3 RH1E5.group_004
  have a5 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0039.sL.t) (c := RH1E5_0047.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0039.sL]) (by norm_num [RS5.Sample.t, RH1E5_0039.sL, RH1E5_0047.sL]) a4 RH1E5.group_005
  have a6 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0047.sL.t) (c := RH1E5_0055.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0047.sL]) (by norm_num [RS5.Sample.t, RH1E5_0047.sL, RH1E5_0055.sL]) a5 RH1E5.group_006
  have a7 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0055.sL.t) (c := RH1E5_0063.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0055.sL]) (by norm_num [RS5.Sample.t, RH1E5_0055.sL, RH1E5_0063.sL]) a6 RH1E5.group_007
  have a8 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0063.sL.t) (c := RH1E5_0071.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0063.sL]) (by norm_num [RS5.Sample.t, RH1E5_0063.sL, RH1E5_0071.sL]) a7 RH1E5.group_008
  have a9 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0071.sL.t) (c := RH1E5_0079.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0071.sL]) (by norm_num [RS5.Sample.t, RH1E5_0071.sL, RH1E5_0079.sL]) a8 RH1E5.group_009
  have a10 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0079.sL.t) (c := RH1E5_0087.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0079.sL]) (by norm_num [RS5.Sample.t, RH1E5_0079.sL, RH1E5_0087.sL]) a9 RH1E5.group_010
  have a11 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0087.sL.t) (c := RH1E5_0095.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0087.sL]) (by norm_num [RS5.Sample.t, RH1E5_0087.sL, RH1E5_0095.sL]) a10 RH1E5.group_011
  have a12 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0095.sL.t) (c := RH1E5_0103.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0095.sL]) (by norm_num [RS5.Sample.t, RH1E5_0095.sL, RH1E5_0103.sL]) a11 RH1E5.group_012
  have a13 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0103.sL.t) (c := RH1E5_0111.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0103.sL]) (by norm_num [RS5.Sample.t, RH1E5_0103.sL, RH1E5_0111.sL]) a12 RH1E5.group_013
  have a14 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0111.sL.t) (c := RH1E5_0119.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0111.sL]) (by norm_num [RS5.Sample.t, RH1E5_0111.sL, RH1E5_0119.sL]) a13 RH1E5.group_014
  have a15 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0119.sL.t) (c := RH1E5_0127.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0119.sL]) (by norm_num [RS5.Sample.t, RH1E5_0119.sL, RH1E5_0127.sL]) a14 RH1E5.group_015
  have a16 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0127.sL.t) (c := RH1E5_0135.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0127.sL]) (by norm_num [RS5.Sample.t, RH1E5_0127.sL, RH1E5_0135.sL]) a15 RH1E5.group_016
  have a17 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0135.sL.t) (c := RH1E5_0143.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0135.sL]) (by norm_num [RS5.Sample.t, RH1E5_0135.sL, RH1E5_0143.sL]) a16 RH1E5.group_017
  have a18 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0143.sL.t) (c := RH1E5_0151.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0143.sL]) (by norm_num [RS5.Sample.t, RH1E5_0143.sL, RH1E5_0151.sL]) a17 RH1E5.group_018
  have a19 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0151.sL.t) (c := RH1E5_0159.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0151.sL]) (by norm_num [RS5.Sample.t, RH1E5_0151.sL, RH1E5_0159.sL]) a18 RH1E5.group_019
  have a20 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0159.sL.t) (c := RH1E5_0167.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0159.sL]) (by norm_num [RS5.Sample.t, RH1E5_0159.sL, RH1E5_0167.sL]) a19 RH1E5.group_020
  have a21 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0167.sL.t) (c := RH1E5_0175.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0167.sL]) (by norm_num [RS5.Sample.t, RH1E5_0167.sL, RH1E5_0175.sL]) a20 RH1E5.group_021
  have a22 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0175.sL.t) (c := RH1E5_0183.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0175.sL]) (by norm_num [RS5.Sample.t, RH1E5_0175.sL, RH1E5_0183.sL]) a21 RH1E5.group_022
  have a23 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0183.sL.t) (c := RH1E5_0191.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0183.sL]) (by norm_num [RS5.Sample.t, RH1E5_0183.sL, RH1E5_0191.sL]) a22 RH1E5.group_023
  have a24 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0191.sL.t) (c := RH1E5_0199.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0191.sL]) (by norm_num [RS5.Sample.t, RH1E5_0191.sL, RH1E5_0199.sL]) a23 RH1E5.group_024
  have a25 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0199.sL.t) (c := RH1E5_0207.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0199.sL]) (by norm_num [RS5.Sample.t, RH1E5_0199.sL, RH1E5_0207.sL]) a24 RH1E5.group_025
  have a26 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0207.sL.t) (c := RH1E5_0215.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0207.sL]) (by norm_num [RS5.Sample.t, RH1E5_0207.sL, RH1E5_0215.sL]) a25 RH1E5.group_026
  have a27 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0215.sL.t) (c := RH1E5_0223.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0215.sL]) (by norm_num [RS5.Sample.t, RH1E5_0215.sL, RH1E5_0223.sL]) a26 RH1E5.group_027
  have a28 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0223.sL.t) (c := RH1E5_0231.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0223.sL]) (by norm_num [RS5.Sample.t, RH1E5_0223.sL, RH1E5_0231.sL]) a27 RH1E5.group_028
  have a29 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0231.sL.t) (c := RH1E5_0239.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0231.sL]) (by norm_num [RS5.Sample.t, RH1E5_0231.sL, RH1E5_0239.sL]) a28 RH1E5.group_029
  have a30 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0239.sL.t) (c := RH1E5_0247.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0239.sL]) (by norm_num [RS5.Sample.t, RH1E5_0239.sL, RH1E5_0247.sL]) a29 RH1E5.group_030
  have a31 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0247.sL.t) (c := RH1E5_0255.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0247.sL]) (by norm_num [RS5.Sample.t, RH1E5_0247.sL, RH1E5_0255.sL]) a30 RH1E5.group_031
  have a32 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0255.sL.t) (c := RH1E5_0263.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0255.sL]) (by norm_num [RS5.Sample.t, RH1E5_0255.sL, RH1E5_0263.sL]) a31 RH1E5.group_032
  have a33 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0263.sL.t) (c := RH1E5_0271.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0263.sL]) (by norm_num [RS5.Sample.t, RH1E5_0263.sL, RH1E5_0271.sL]) a32 RH1E5.group_033
  have a34 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0271.sL.t) (c := RH1E5_0279.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0271.sL]) (by norm_num [RS5.Sample.t, RH1E5_0271.sL, RH1E5_0279.sL]) a33 RH1E5.group_034
  have a35 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0279.sL.t) (c := RH1E5_0287.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0279.sL]) (by norm_num [RS5.Sample.t, RH1E5_0279.sL, RH1E5_0287.sL]) a34 RH1E5.group_035
  have a36 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0287.sL.t) (c := RH1E5_0295.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0287.sL]) (by norm_num [RS5.Sample.t, RH1E5_0287.sL, RH1E5_0295.sL]) a35 RH1E5.group_036
  have a37 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0295.sL.t) (c := RH1E5_0303.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0295.sL]) (by norm_num [RS5.Sample.t, RH1E5_0295.sL, RH1E5_0303.sL]) a36 RH1E5.group_037
  have a38 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0303.sL.t) (c := RH1E5_0311.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0303.sL]) (by norm_num [RS5.Sample.t, RH1E5_0303.sL, RH1E5_0311.sL]) a37 RH1E5.group_038
  have a39 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0311.sL.t) (c := RH1E5_0319.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0311.sL]) (by norm_num [RS5.Sample.t, RH1E5_0311.sL, RH1E5_0319.sL]) a38 RH1E5.group_039
  have a40 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0319.sL.t) (c := RH1E5_0327.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0319.sL]) (by norm_num [RS5.Sample.t, RH1E5_0319.sL, RH1E5_0327.sL]) a39 RH1E5.group_040
  have a41 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0327.sL.t) (c := RH1E5_0335.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0327.sL]) (by norm_num [RS5.Sample.t, RH1E5_0327.sL, RH1E5_0335.sL]) a40 RH1E5.group_041
  have a42 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0335.sL.t) (c := RH1E5_0343.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0335.sL]) (by norm_num [RS5.Sample.t, RH1E5_0335.sL, RH1E5_0343.sL]) a41 RH1E5.group_042
  have a43 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0343.sL.t) (c := RH1E5_0351.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0343.sL]) (by norm_num [RS5.Sample.t, RH1E5_0343.sL, RH1E5_0351.sL]) a42 RH1E5.group_043
  have a44 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0351.sL.t) (c := RH1E5_0359.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0351.sL]) (by norm_num [RS5.Sample.t, RH1E5_0351.sL, RH1E5_0359.sL]) a43 RH1E5.group_044
  have a45 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0359.sL.t) (c := RH1E5_0367.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0359.sL]) (by norm_num [RS5.Sample.t, RH1E5_0359.sL, RH1E5_0367.sL]) a44 RH1E5.group_045
  have a46 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0367.sL.t) (c := RH1E5_0375.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0367.sL]) (by norm_num [RS5.Sample.t, RH1E5_0367.sL, RH1E5_0375.sL]) a45 RH1E5.group_046
  have a47 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0375.sL.t) (c := RH1E5_0383.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0375.sL]) (by norm_num [RS5.Sample.t, RH1E5_0375.sL, RH1E5_0383.sL]) a46 RH1E5.group_047
  have a48 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0383.sL.t) (c := RH1E5_0391.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0383.sL]) (by norm_num [RS5.Sample.t, RH1E5_0383.sL, RH1E5_0391.sL]) a47 RH1E5.group_048
  have a49 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0391.sL.t) (c := RH1E5_0399.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0391.sL]) (by norm_num [RS5.Sample.t, RH1E5_0391.sL, RH1E5_0399.sL]) a48 RH1E5.group_049
  have a50 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0399.sL.t) (c := RH1E5_0407.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0399.sL]) (by norm_num [RS5.Sample.t, RH1E5_0399.sL, RH1E5_0407.sL]) a49 RH1E5.group_050
  have a51 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0407.sL.t) (c := RH1E5_0415.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0407.sL]) (by norm_num [RS5.Sample.t, RH1E5_0407.sL, RH1E5_0415.sL]) a50 RH1E5.group_051
  have e0 : RH1E5_0000.s0.t = ((4259840000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E5_0000.s0]
  have e1 : RH1E5_0415.sL.t = ((6553600000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E5_0415.sL]
  rw [e0, e1] at a51
  exact a51
theorem solution : RS5.BandZeros ((4259840000 : ℝ) / 65536) ((6553600000 : ℝ) / 65536) 52781 := by
  apply RHX100000.bands <;> assumption
