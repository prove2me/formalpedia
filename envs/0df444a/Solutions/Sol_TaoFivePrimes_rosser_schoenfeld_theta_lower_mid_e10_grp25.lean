-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp25
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T04:57:34.441386+00:00
-- url     : https://prove2.me/submissions/4d1a634e-071e-4640-a40f-92ed208ea661

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1201
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1202
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1203
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1204
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1205
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1206
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1207
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1208
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1209
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1210
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1211
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1212
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1213
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1214
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1215
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1216
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1217
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1218
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1219
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1220
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1221
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1222
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1223
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1224
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1225
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1226
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1227
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1228
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1229
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1230
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1231
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1232
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1233
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1234
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1235
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1236
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1237
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1238
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1239
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1240
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1241
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1242
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1243
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1244
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1245
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1246
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1247
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1248
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1249
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1250

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp25` (the range 8980547700 <= n <= 9324426323 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1201` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1250`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (9874099226388381058938 : Real) / 2 ^ 40 <= Chebyshev.theta (8980547700 : Real))
    (n : Nat) (h1 : 8980547700 <= n) (h2 : n <= 9324426323) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((10252213892257269854204 : Real) / 2 ^ 40 <= Chebyshev.theta (9324426324 : Real)) := by
  have hb0 := hbase
  have hb1 : (9881655414129511357186 : Real) / 2 ^ 40 <= Chebyshev.theta (8987433584 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1201 hb0 8980547700 le_rfl (by norm_num)).2
  have hb2 : (9889211853952254342780 : Real) / 2 ^ 40 <= Chebyshev.theta (8994297380 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1202 hb1 8987433584 le_rfl (by norm_num)).2
  have hb3 : (9896768545560952286722 : Real) / 2 ^ 40 <= Chebyshev.theta (9001174080 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1203 hb2 8994297380 le_rfl (by norm_num)).2
  have hb4 : (9904325489029845235501 : Real) / 2 ^ 40 <= Chebyshev.theta (9008042384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1204 hb3 9001174080 le_rfl (by norm_num)).2
  have hb5 : (9911882683944751877130 : Real) / 2 ^ 40 <= Chebyshev.theta (9014911598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1205 hb4 9008042384 le_rfl (by norm_num)).2
  have hb6 : (9919440130035505425892 : Real) / 2 ^ 40 <= Chebyshev.theta (9021775928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1206 hb5 9014911598 le_rfl (by norm_num)).2
  have hb7 : (9926997826962722812128 : Real) / 2 ^ 40 <= Chebyshev.theta (9028644110 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1207 hb6 9021775928 le_rfl (by norm_num)).2
  have hb8 : (9934555775093324766852 : Real) / 2 ^ 40 <= Chebyshev.theta (9035526524 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1208 hb7 9028644110 le_rfl (by norm_num)).2
  have hb9 : (9942113974086811828727 : Real) / 2 ^ 40 <= Chebyshev.theta (9042405140 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1209 hb8 9035526524 le_rfl (by norm_num)).2
  have hb10 : (9949672423865594776235 : Real) / 2 ^ 40 <= Chebyshev.theta (9049279040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1210 hb9 9042405140 le_rfl (by norm_num)).2
  have hb11 : (9957231124146110123542 : Real) / 2 ^ 40 <= Chebyshev.theta (9056154578 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1211 hb10 9049279040 le_rfl (by norm_num)).2
  have hb12 : (9964790074732617196699 : Real) / 2 ^ 40 <= Chebyshev.theta (9063028202 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1212 hb11 9056154578 le_rfl (by norm_num)).2
  have hb13 : (9972349275426584342566 : Real) / 2 ^ 40 <= Chebyshev.theta (9069906032 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1213 hb12 9063028202 le_rfl (by norm_num)).2
  have hb14 : (9979908726075624097299 : Real) / 2 ^ 40 <= Chebyshev.theta (9076783034 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1214 hb13 9069906032 le_rfl (by norm_num)).2
  have hb15 : (9987468426407522957108 : Real) / 2 ^ 40 <= Chebyshev.theta (9083658920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1215 hb14 9076783034 le_rfl (by norm_num)).2
  have hb16 : (9995028376274917220694 : Real) / 2 ^ 40 <= Chebyshev.theta (9090531098 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1216 hb15 9083658920 le_rfl (by norm_num)).2
  have hb17 : (10002588575376381135397 : Real) / 2 ^ 40 <= Chebyshev.theta (9097406828 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1217 hb16 9090531098 le_rfl (by norm_num)).2
  have hb18 : (10010149023633953349141 : Real) / 2 ^ 40 <= Chebyshev.theta (9104283972 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1218 hb17 9097406828 le_rfl (by norm_num)).2
  have hb19 : (10017709721158528768460 : Real) / 2 ^ 40 <= Chebyshev.theta (9111164874 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1219 hb18 9104283972 le_rfl (by norm_num)).2
  have hb20 : (10025270667291250238931 : Real) / 2 ^ 40 <= Chebyshev.theta (9118027448 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1220 hb19 9111164874 le_rfl (by norm_num)).2
  have hb21 : (10032831862002533381127 : Real) / 2 ^ 40 <= Chebyshev.theta (9124918974 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1221 hb20 9118027448 le_rfl (by norm_num)).2
  have hb22 : (10040393305521424554012 : Real) / 2 ^ 40 <= Chebyshev.theta (9131795400 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1222 hb21 9124918974 le_rfl (by norm_num)).2
  have hb23 : (10047954997227768181283 : Real) / 2 ^ 40 <= Chebyshev.theta (9138668168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1223 hb22 9131795400 le_rfl (by norm_num)).2
  have hb24 : (10055516937083606945939 : Real) / 2 ^ 40 <= Chebyshev.theta (9145551720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1224 hb23 9138668168 le_rfl (by norm_num)).2
  have hb25 : (10063079125131177666408 : Real) / 2 ^ 40 <= Chebyshev.theta (9152435768 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1225 hb24 9145551720 le_rfl (by norm_num)).2
  have hb26 : (10070641561147388072666 : Real) / 2 ^ 40 <= Chebyshev.theta (9159316148 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1226 hb25 9152435768 le_rfl (by norm_num)).2
  have hb27 : (10078204244751734668302 : Real) / 2 ^ 40 <= Chebyshev.theta (9166193448 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1227 hb26 9159316148 le_rfl (by norm_num)).2
  have hb28 : (10085767176106652442248 : Real) / 2 ^ 40 <= Chebyshev.theta (9173087018 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1228 hb27 9166193448 le_rfl (by norm_num)).2
  have hb29 : (10093330354723347905471 : Real) / 2 ^ 40 <= Chebyshev.theta (9179954402 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1229 hb28 9173087018 le_rfl (by norm_num)).2
  have hb30 : (10100893780326444444431 : Real) / 2 ^ 40 <= Chebyshev.theta (9186847080 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1230 hb29 9179954402 le_rfl (by norm_num)).2
  have hb31 : (10108457453207692417256 : Real) / 2 ^ 40 <= Chebyshev.theta (9193733412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1231 hb30 9186847080 le_rfl (by norm_num)).2
  have hb32 : (10116021373020080077831 : Real) / 2 ^ 40 <= Chebyshev.theta (9200618430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1232 hb31 9193733412 le_rfl (by norm_num)).2
  have hb33 : (10123585539273883610724 : Real) / 2 ^ 40 <= Chebyshev.theta (9207484262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1233 hb32 9200618430 le_rfl (by norm_num)).2
  have hb34 : (10131149951448864494681 : Real) / 2 ^ 40 <= Chebyshev.theta (9214361940 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1234 hb33 9207484262 le_rfl (by norm_num)).2
  have hb35 : (10138714609836959153109 : Real) / 2 ^ 40 <= Chebyshev.theta (9221241164 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1235 hb34 9214361940 le_rfl (by norm_num)).2
  have hb36 : (10146279514253218698266 : Real) / 2 ^ 40 <= Chebyshev.theta (9228121380 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1236 hb35 9221241164 le_rfl (by norm_num)).2
  have hb37 : (10153844664113956348615 : Real) / 2 ^ 40 <= Chebyshev.theta (9234989228 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1237 hb36 9228121380 le_rfl (by norm_num)).2
  have hb38 : (10161410059451733528055 : Real) / 2 ^ 40 <= Chebyshev.theta (9241868660 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1238 hb37 9234989228 le_rfl (by norm_num)).2
  have hb39 : (10168975700263201061555 : Real) / 2 ^ 40 <= Chebyshev.theta (9248751654 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1239 hb38 9241868660 le_rfl (by norm_num)).2
  have hb40 : (10176541586299217539974 : Real) / 2 ^ 40 <= Chebyshev.theta (9255626330 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1240 hb39 9248751654 le_rfl (by norm_num)).2
  have hb41 : (10184107717464889670808 : Real) / 2 ^ 40 <= Chebyshev.theta (9262504412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1241 hb40 9255626330 le_rfl (by norm_num)).2
  have hb42 : (10191674092956601512247 : Real) / 2 ^ 40 <= Chebyshev.theta (9269371688 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1242 hb41 9262504412 le_rfl (by norm_num)).2
  have hb43 : (10199240713185371266527 : Real) / 2 ^ 40 <= Chebyshev.theta (9276253070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1243 hb42 9269371688 le_rfl (by norm_num)).2
  have hb44 : (10206807577955830390258 : Real) / 2 ^ 40 <= Chebyshev.theta (9283135560 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1244 hb43 9276253070 le_rfl (by norm_num)).2
  have hb45 : (10214374687058469378815 : Real) / 2 ^ 40 <= Chebyshev.theta (9290009514 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1245 hb44 9283135560 le_rfl (by norm_num)).2
  have hb46 : (10221942040123204391433 : Real) / 2 ^ 40 <= Chebyshev.theta (9296893778 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1246 hb45 9290009514 le_rfl (by norm_num)).2
  have hb47 : (10229509637426714498608 : Real) / 2 ^ 40 <= Chebyshev.theta (9303781118 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1247 hb46 9296893778 le_rfl (by norm_num)).2
  have hb48 : (10237077478768049198568 : Real) / 2 ^ 40 <= Chebyshev.theta (9310665348 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1248 hb47 9303781118 le_rfl (by norm_num)).2
  have hb49 : (10244645563806150834138 : Real) / 2 ^ 40 <= Chebyshev.theta (9317543868 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1249 hb48 9310665348 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1250 hb49 9317543868 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 9152435768 with hc25 | hc25
  · rcases Nat.lt_or_ge n 9063028202 with hc12 | hc12
    · rcases Nat.lt_or_ge n 9021775928 with hc6 | hc6
      · rcases Nat.lt_or_ge n 9001174080 with hc3 | hc3
        · rcases Nat.lt_or_ge n 8987433584 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1201 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8994297380 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1202 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1203 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9008042384 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1204 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9014911598 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1205 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1206 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9042405140 with hc9 | hc9
        · rcases Nat.lt_or_ge n 9028644110 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1207 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9035526524 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1208 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1209 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9049279040 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1210 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9056154578 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1211 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1212 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 9104283972 with hc18 | hc18
      · rcases Nat.lt_or_ge n 9083658920 with hc15 | hc15
        · rcases Nat.lt_or_ge n 9069906032 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1213 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9076783034 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1214 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1215 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9090531098 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1216 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9097406828 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1217 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1218 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9124918974 with hc21 | hc21
        · rcases Nat.lt_or_ge n 9111164874 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1219 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9118027448 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1220 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1221 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9138668168 with hc23 | hc23
          · rcases Nat.lt_or_ge n 9131795400 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1222 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1223 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9145551720 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1224 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1225 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 9234989228 with hc37 | hc37
    · rcases Nat.lt_or_ge n 9193733412 with hc31 | hc31
      · rcases Nat.lt_or_ge n 9173087018 with hc28 | hc28
        · rcases Nat.lt_or_ge n 9159316148 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1226 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9166193448 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1227 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1228 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9179954402 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1229 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9186847080 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1230 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1231 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9214361940 with hc34 | hc34
        · rcases Nat.lt_or_ge n 9200618430 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1232 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9207484262 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1233 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1234 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9221241164 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1235 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9228121380 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1236 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1237 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 9276253070 with hc43 | hc43
      · rcases Nat.lt_or_ge n 9255626330 with hc40 | hc40
        · rcases Nat.lt_or_ge n 9241868660 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1238 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9248751654 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1239 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1240 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9262504412 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1241 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9269371688 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1242 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1243 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9296893778 with hc46 | hc46
        · rcases Nat.lt_or_ge n 9283135560 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1244 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9290009514 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1245 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1246 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9310665348 with hc48 | hc48
          · rcases Nat.lt_or_ge n 9303781118 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1247 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1248 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9317543868 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1249 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1250 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (9874099226388381058938 : Real) / 2 ^ 40 <= Chebyshev.theta (8980547700 : Real))
    (n : Nat) (h1 : 8980547700 <= n) (h2 : n <= 9324426323) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((10252213892257269854204 : Real) / 2 ^ 40 <= Chebyshev.theta (9324426324 : Real)) :=
  TFPLink.blk hbase n h1 h2
