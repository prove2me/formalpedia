-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp27
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T07:04:32.862243+00:00
-- url     : https://prove2.me/submissions/f79236df-02ad-43c3-888b-e87bd9ae62a5

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1300
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1301
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1302
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1303
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1304
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1305
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1306
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1307
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1308
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1309
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1310
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1311
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1312
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1313
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1314
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1315
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1316
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1317
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1318
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1319
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1320
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1321
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1322
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1323
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1324
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1325
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1326
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1327
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1328
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1329
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1330
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1331
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1332
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1333
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1334
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1335
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1336
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1337
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1338
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1339
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1340
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1341
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1342
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1343
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1344
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1345
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1346
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1347
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1348

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp27` (the range 9661975292 <= n <= 10000000000 with its carry in and carry out) from the 49 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1300` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1348`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (10623356848875818030645 : Real) / 2 ^ 40 <= Chebyshev.theta (9661975292 : Real))
    (n : Nat) (h1 : 9661975292 <= n) (h2 : n <= 10000000000) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((10995041617401890452312 : Real) / 2 ^ 40 <= Chebyshev.theta (10000000001 : Real)) := by
  have hb0 := hbase
  have hb1 : (10630937140831516763675 : Real) / 2 ^ 40 <= Chebyshev.theta (9668864198 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1300 hb0 9661975292 le_rfl (by norm_num)).2
  have hb2 : (10638517667843296921379 : Real) / 2 ^ 40 <= Chebyshev.theta (9675763568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1301 hb1 9668864198 le_rfl (by norm_num)).2
  have hb3 : (10646098429680251491997 : Real) / 2 ^ 40 <= Chebyshev.theta (9682652940 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1302 hb2 9675763568 le_rfl (by norm_num)).2
  have hb4 : (10653679426142360300154 : Real) / 2 ^ 40 <= Chebyshev.theta (9689541300 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1303 hb3 9682652940 le_rfl (by norm_num)).2
  have hb5 : (10661260657113518611493 : Real) / 2 ^ 40 <= Chebyshev.theta (9696442434 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1304 hb4 9689541300 le_rfl (by norm_num)).2
  have hb6 : (10668842122445246333038 : Real) / 2 ^ 40 <= Chebyshev.theta (9703326948 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1305 hb5 9696442434 le_rfl (by norm_num)).2
  have hb7 : (10676423821778437475509 : Real) / 2 ^ 40 <= Chebyshev.theta (9710212050 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1306 hb6 9703326948 le_rfl (by norm_num)).2
  have hb8 : (10684005755046480668875 : Real) / 2 ^ 40 <= Chebyshev.theta (9717109968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1307 hb7 9710212050 le_rfl (by norm_num)).2
  have hb9 : (10691587922389110937980 : Real) / 2 ^ 40 <= Chebyshev.theta (9724010568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1308 hb8 9717109968 le_rfl (by norm_num)).2
  have hb10 : (10699170323639427727185 : Real) / 2 ^ 40 <= Chebyshev.theta (9730903902 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1309 hb9 9724010568 le_rfl (by norm_num)).2
  have hb11 : (10706752958451535682049 : Real) / 2 ^ 40 <= Chebyshev.theta (9737795988 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1310 hb10 9730903902 le_rfl (by norm_num)).2
  have hb12 : (10714335826690909605553 : Real) / 2 ^ 40 <= Chebyshev.theta (9744694668 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1311 hb11 9737795988 le_rfl (by norm_num)).2
  have hb13 : (10721918928326290530755 : Real) / 2 ^ 40 <= Chebyshev.theta (9751595142 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1312 hb12 9744694668 le_rfl (by norm_num)).2
  have hb14 : (10729502263236549960753 : Real) / 2 ^ 40 <= Chebyshev.theta (9758496038 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1313 hb13 9751595142 le_rfl (by norm_num)).2
  have hb15 : (10737085831400476453693 : Real) / 2 ^ 40 <= Chebyshev.theta (9765397574 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1314 hb14 9758496038 le_rfl (by norm_num)).2
  have hb16 : (10744669632363512531955 : Real) / 2 ^ 40 <= Chebyshev.theta (9772291092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1315 hb15 9765397574 le_rfl (by norm_num)).2
  have hb17 : (10752253665906659361662 : Real) / 2 ^ 40 <= Chebyshev.theta (9779185304 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1316 hb16 9772291092 le_rfl (by norm_num)).2
  have hb18 : (10759837932166674923188 : Real) / 2 ^ 40 <= Chebyshev.theta (9786088190 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1317 hb17 9779185304 le_rfl (by norm_num)).2
  have hb19 : (10767422430772545049371 : Real) / 2 ^ 40 <= Chebyshev.theta (9792979430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1318 hb18 9786088190 le_rfl (by norm_num)).2
  have hb20 : (10775007161466755393495 : Real) / 2 ^ 40 <= Chebyshev.theta (9799882662 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1319 hb19 9792979430 le_rfl (by norm_num)).2
  have hb21 : (10782592124065287394215 : Real) / 2 ^ 40 <= Chebyshev.theta (9806767194 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1320 hb20 9799882662 le_rfl (by norm_num)).2
  have hb22 : (10790177318600330344870 : Real) / 2 ^ 40 <= Chebyshev.theta (9813674094 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1321 hb21 9806767194 le_rfl (by norm_num)).2
  have hb23 : (10797762745039881017401 : Real) / 2 ^ 40 <= Chebyshev.theta (9820578390 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1322 hb22 9813674094 le_rfl (by norm_num)).2
  have hb24 : (10805348403153962726445 : Real) / 2 ^ 40 <= Chebyshev.theta (9827473892 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1323 hb23 9820578390 le_rfl (by norm_num)).2
  have hb25 : (10812934292941273015047 : Real) / 2 ^ 40 <= Chebyshev.theta (9834380598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1324 hb24 9827473892 le_rfl (by norm_num)).2
  have hb26 : (10820520413836545564332 : Real) / 2 ^ 40 <= Chebyshev.theta (9841271114 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1325 hb25 9834380598 le_rfl (by norm_num)).2
  have hb27 : (10828106765865085252301 : Real) / 2 ^ 40 <= Chebyshev.theta (9848178912 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1326 hb26 9841271114 le_rfl (by norm_num)).2
  have hb28 : (10835693349082711662779 : Real) / 2 ^ 40 <= Chebyshev.theta (9855084288 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1327 hb27 9848178912 le_rfl (by norm_num)).2
  have hb29 : (10843280163136458960709 : Real) / 2 ^ 40 <= Chebyshev.theta (9861977982 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1328 hb28 9855084288 le_rfl (by norm_num)).2
  have hb30 : (10850867207819050424818 : Real) / 2 ^ 40 <= Chebyshev.theta (9868878704 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1329 hb29 9861977982 le_rfl (by norm_num)).2
  have hb31 : (10858454483049547658559 : Real) / 2 ^ 40 <= Chebyshev.theta (9875775908 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1330 hb30 9868878704 le_rfl (by norm_num)).2
  have hb32 : (10866041988570808445775 : Real) / 2 ^ 40 <= Chebyshev.theta (9882677714 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1331 hb31 9875775908 le_rfl (by norm_num)).2
  have hb33 : (10873629724118806154970 : Real) / 2 ^ 40 <= Chebyshev.theta (9889579604 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1332 hb32 9882677714 le_rfl (by norm_num)).2
  have hb34 : (10881217690001850954142 : Real) / 2 ^ 40 <= Chebyshev.theta (9896482692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1333 hb33 9889579604 le_rfl (by norm_num)).2
  have hb35 : (10888805885589553676619 : Real) / 2 ^ 40 <= Chebyshev.theta (9903379038 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1334 hb34 9896482692 le_rfl (by norm_num)).2
  have hb36 : (10896394311097936111806 : Real) / 2 ^ 40 <= Chebyshev.theta (9910290920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1335 hb35 9903379038 le_rfl (by norm_num)).2
  have hb37 : (10903982966548767897396 : Real) / 2 ^ 40 <= Chebyshev.theta (9917196090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1336 hb36 9910290920 le_rfl (by norm_num)).2
  have hb38 : (10911571851264771416304 : Real) / 2 ^ 40 <= Chebyshev.theta (9924091254 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1337 hb37 9917196090 le_rfl (by norm_num)).2
  have hb39 : (10919160965216734419660 : Real) / 2 ^ 40 <= Chebyshev.theta (9930987162 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1338 hb38 9924091254 le_rfl (by norm_num)).2
  have hb40 : (10926750308214126061340 : Real) / 2 ^ 40 <= Chebyshev.theta (9937892778 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1339 hb39 9930987162 le_rfl (by norm_num)).2
  have hb41 : (10934339880134887518045 : Real) / 2 ^ 40 <= Chebyshev.theta (9944795124 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1340 hb40 9937892778 le_rfl (by norm_num)).2
  have hb42 : (10941929680946829496436 : Real) / 2 ^ 40 <= Chebyshev.theta (9951694704 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1341 hb41 9944795124 le_rfl (by norm_num)).2
  have hb43 : (10949519710378668819120 : Real) / 2 ^ 40 <= Chebyshev.theta (9958597610 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1342 hb42 9951694704 le_rfl (by norm_num)).2
  have hb44 : (10957109968321929428195 : Real) / 2 ^ 40 <= Chebyshev.theta (9965498580 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1343 hb43 9958597610 le_rfl (by norm_num)).2
  have hb45 : (10964700454619944358391 : Real) / 2 ^ 40 <= Chebyshev.theta (9972400328 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1344 hb44 9965498580 le_rfl (by norm_num)).2
  have hb46 : (10972291169396819151080 : Real) / 2 ^ 40 <= Chebyshev.theta (9979318278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1345 hb45 9972400328 le_rfl (by norm_num)).2
  have hb47 : (10979882112279306855748 : Real) / 2 ^ 40 <= Chebyshev.theta (9986216810 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1346 hb46 9979318278 le_rfl (by norm_num)).2
  have hb48 : (10987473282984588247678 : Real) / 2 ^ 40 <= Chebyshev.theta (9993116228 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1347 hb47 9986216810 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1348 hb48 9993116228 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 9827473892 with hc24 | hc24
  · rcases Nat.lt_or_ge n 9744694668 with hc12 | hc12
    · rcases Nat.lt_or_ge n 9703326948 with hc6 | hc6
      · rcases Nat.lt_or_ge n 9682652940 with hc3 | hc3
        · rcases Nat.lt_or_ge n 9668864198 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1300 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9675763568 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1301 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1302 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9689541300 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1303 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9696442434 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1304 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1305 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9724010568 with hc9 | hc9
        · rcases Nat.lt_or_ge n 9710212050 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1306 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9717109968 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1307 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1308 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9730903902 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1309 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9737795988 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1310 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1311 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 9786088190 with hc18 | hc18
      · rcases Nat.lt_or_ge n 9765397574 with hc15 | hc15
        · rcases Nat.lt_or_ge n 9751595142 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1312 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9758496038 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1313 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1314 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9772291092 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1315 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9779185304 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1316 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1317 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9806767194 with hc21 | hc21
        · rcases Nat.lt_or_ge n 9792979430 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1318 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9799882662 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1319 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1320 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9813674094 with hc22 | hc22
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1321 hb21 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9820578390 with hc23 | hc23
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1322 hb22 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1323 hb23 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 9910290920 with hc36 | hc36
    · rcases Nat.lt_or_ge n 9868878704 with hc30 | hc30
      · rcases Nat.lt_or_ge n 9848178912 with hc27 | hc27
        · rcases Nat.lt_or_ge n 9834380598 with hc25 | hc25
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1324 hb24 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9841271114 with hc26 | hc26
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1325 hb25 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1326 hb26 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9855084288 with hc28 | hc28
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1327 hb27 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9861977982 with hc29 | hc29
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1328 hb28 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1329 hb29 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9889579604 with hc33 | hc33
        · rcases Nat.lt_or_ge n 9875775908 with hc31 | hc31
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1330 hb30 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9882677714 with hc32 | hc32
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1331 hb31 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1332 hb32 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9896482692 with hc34 | hc34
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1333 hb33 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9903379038 with hc35 | hc35
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1334 hb34 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1335 hb35 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 9951694704 with hc42 | hc42
      · rcases Nat.lt_or_ge n 9930987162 with hc39 | hc39
        · rcases Nat.lt_or_ge n 9917196090 with hc37 | hc37
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1336 hb36 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9924091254 with hc38 | hc38
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1337 hb37 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1338 hb38 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9937892778 with hc40 | hc40
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1339 hb39 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9944795124 with hc41 | hc41
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1340 hb40 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1341 hb41 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9972400328 with hc45 | hc45
        · rcases Nat.lt_or_ge n 9958597610 with hc43 | hc43
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1342 hb42 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9965498580 with hc44 | hc44
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1343 hb43 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1344 hb44 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9986216810 with hc47 | hc47
          · rcases Nat.lt_or_ge n 9979318278 with hc46 | hc46
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1345 hb45 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1346 hb46 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9993116228 with hc48 | hc48
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1347 hb47 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1348 hb48 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (10623356848875818030645 : Real) / 2 ^ 40 <= Chebyshev.theta (9661975292 : Real))
    (n : Nat) (h1 : 9661975292 <= n) (h2 : n <= 10000000000) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((10995041617401890452312 : Real) / 2 ^ 40 <= Chebyshev.theta (10000000001 : Real)) :=
  TFPLink.blk hbase n h1 h2
