-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp26
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T05:55:54.547009+00:00
-- url     : https://prove2.me/submissions/3e6ce909-a1a1-4ff6-8677-95a5f5cdee2c

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1251
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1252
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1253
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1254
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1255
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1256
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1257
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1258
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1259
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1260
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1261
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1262
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1263
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1264
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1265
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1266
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1267
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1268
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1269
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1270
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1271
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1272
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1273
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1274
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1275
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1276
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1277
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1278
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1279
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1280
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1281
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1282
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1283
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1284
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1285
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1286
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1287
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1288
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1289
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1290
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1291
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1292
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1293
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1294
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1295
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1296
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1297
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1298
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1299

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp26` (the range 9324426324 <= n <= 9661975291 with its carry in and carry out) from the 49 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1251` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1299`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (10252213892257269854204 : Real) / 2 ^ 40 <= Chebyshev.theta (9324426324 : Real))
    (n : Nat) (h1 : 9324426324 <= n) (h2 : n <= 9661975291) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((10623356848875818030645 : Real) / 2 ^ 40 <= Chebyshev.theta (9661975292 : Real)) := by
  have hb0 := hbase
  have hb1 : (10259782464110242342001 : Real) / 2 ^ 40 <= Chebyshev.theta (9331303454 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1251 hb0 9324426324 le_rfl (by norm_num)).2
  have hb2 : (10267351278968377121807 : Real) / 2 ^ 40 <= Chebyshev.theta (9338194602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1252 hb1 9331303454 le_rfl (by norm_num)).2
  have hb3 : (10274920337239901416668 : Real) / 2 ^ 40 <= Chebyshev.theta (9345087710 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1253 hb2 9338194602 le_rfl (by norm_num)).2
  have hb4 : (10282489638511192110435 : Real) / 2 ^ 40 <= Chebyshev.theta (9351972468 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1254 hb3 9345087710 le_rfl (by norm_num)).2
  have hb5 : (10290059182652375638074 : Real) / 2 ^ 40 <= Chebyshev.theta (9358860108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1255 hb4 9351972468 le_rfl (by norm_num)).2
  have hb6 : (10297628969308811577013 : Real) / 2 ^ 40 <= Chebyshev.theta (9365747922 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1256 hb5 9358860108 le_rfl (by norm_num)).2
  have hb7 : (10305198998631398868860 : Real) / 2 ^ 40 <= Chebyshev.theta (9372642594 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1257 hb6 9365747922 le_rfl (by norm_num)).2
  have hb8 : (10312769270345877291752 : Real) / 2 ^ 40 <= Chebyshev.theta (9379525592 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1258 hb7 9372642594 le_rfl (by norm_num)).2
  have hb9 : (10320339783969593510876 : Real) / 2 ^ 40 <= Chebyshev.theta (9386409890 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1259 hb8 9379525592 le_rfl (by norm_num)).2
  have hb10 : (10327910539367650198653 : Real) / 2 ^ 40 <= Chebyshev.theta (9393292058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1260 hb9 9386409890 le_rfl (by norm_num)).2
  have hb11 : (10335481536118609497200 : Real) / 2 ^ 40 <= Chebyshev.theta (9400168008 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1261 hb10 9393292058 le_rfl (by norm_num)).2
  have hb12 : (10343052774424352234686 : Real) / 2 ^ 40 <= Chebyshev.theta (9407056340 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1262 hb11 9400168008 le_rfl (by norm_num)).2
  have hb13 : (10350624254141980276517 : Real) / 2 ^ 40 <= Chebyshev.theta (9413947200 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1263 hb12 9407056340 le_rfl (by norm_num)).2
  have hb14 : (10358195974808005011660 : Real) / 2 ^ 40 <= Chebyshev.theta (9420824004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1264 hb13 9413947200 le_rfl (by norm_num)).2
  have hb15 : (10365767936371630618834 : Real) / 2 ^ 40 <= Chebyshev.theta (9427709202 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1265 hb14 9420824004 le_rfl (by norm_num)).2
  have hb16 : (10373340138937053654514 : Real) / 2 ^ 40 <= Chebyshev.theta (9434601774 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1266 hb15 9427709202 le_rfl (by norm_num)).2
  have hb17 : (10380912581982174944651 : Real) / 2 ^ 40 <= Chebyshev.theta (9441476868 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1267 hb16 9434601774 le_rfl (by norm_num)).2
  have hb18 : (10388485265504761705891 : Real) / 2 ^ 40 <= Chebyshev.theta (9448369374 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1268 hb17 9441476868 le_rfl (by norm_num)).2
  have hb19 : (10396058189442109939070 : Real) / 2 ^ 40 <= Chebyshev.theta (9455266004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1269 hb18 9448369374 le_rfl (by norm_num)).2
  have hb20 : (10403631353722398446332 : Real) / 2 ^ 40 <= Chebyshev.theta (9462151394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1270 hb19 9455266004 le_rfl (by norm_num)).2
  have hb21 : (10411204757833761643996 : Real) / 2 ^ 40 <= Chebyshev.theta (9469036394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1271 hb20 9462151394 le_rfl (by norm_num)).2
  have hb22 : (10418778401857137928609 : Real) / 2 ^ 40 <= Chebyshev.theta (9475928588 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1272 hb21 9469036394 le_rfl (by norm_num)).2
  have hb23 : (10426352285741173283052 : Real) / 2 ^ 40 <= Chebyshev.theta (9482820228 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1273 hb22 9475928588 le_rfl (by norm_num)).2
  have hb24 : (10433926409206211592357 : Real) / 2 ^ 40 <= Chebyshev.theta (9489717398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1274 hb23 9482820228 le_rfl (by norm_num)).2
  have hb25 : (10441500772009251601604 : Real) / 2 ^ 40 <= Chebyshev.theta (9496598984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1275 hb24 9489717398 le_rfl (by norm_num)).2
  have hb26 : (10449075373976880470374 : Real) / 2 ^ 40 <= Chebyshev.theta (9503493668 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1276 hb25 9496598984 le_rfl (by norm_num)).2
  have hb27 : (10456650215123053094624 : Real) / 2 ^ 40 <= Chebyshev.theta (9510382854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1277 hb26 9503493668 le_rfl (by norm_num)).2
  have hb28 : (10464225295065963520986 : Real) / 2 ^ 40 <= Chebyshev.theta (9517274112 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1278 hb27 9510382854 le_rfl (by norm_num)).2
  have hb29 : (10471800613695833234602 : Real) / 2 ^ 40 <= Chebyshev.theta (9524161812 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1279 hb28 9517274112 le_rfl (by norm_num)).2
  have hb30 : (10479376170712725005050 : Real) / 2 ^ 40 <= Chebyshev.theta (9531044400 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1280 hb29 9524161812 le_rfl (by norm_num)).2
  have hb31 : (10486951965843867132701 : Real) / 2 ^ 40 <= Chebyshev.theta (9537932618 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1281 hb30 9531044400 le_rfl (by norm_num)).2
  have hb32 : (10494527999209085657501 : Real) / 2 ^ 40 <= Chebyshev.theta (9544831890 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1282 hb31 9537932618 le_rfl (by norm_num)).2
  have hb33 : (10502104270870154252217 : Real) / 2 ^ 40 <= Chebyshev.theta (9551725194 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1283 hb32 9544831890 le_rfl (by norm_num)).2
  have hb34 : (10509680780560813502001 : Real) / 2 ^ 40 <= Chebyshev.theta (9558624738 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1284 hb33 9551725194 le_rfl (by norm_num)).2
  have hb35 : (10517257527858323092012 : Real) / 2 ^ 40 <= Chebyshev.theta (9565503980 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1285 hb34 9558624738 le_rfl (by norm_num)).2
  have hb36 : (10524834512387389353663 : Real) / 2 ^ 40 <= Chebyshev.theta (9572392652 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1286 hb35 9565503980 le_rfl (by norm_num)).2
  have hb37 : (10532411734363103749962 : Real) / 2 ^ 40 <= Chebyshev.theta (9579289764 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1287 hb36 9572392652 le_rfl (by norm_num)).2
  have hb38 : (10539989193502833121472 : Real) / 2 ^ 40 <= Chebyshev.theta (9586172360 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1288 hb37 9579289764 le_rfl (by norm_num)).2
  have hb39 : (10547566889579391762022 : Real) / 2 ^ 40 <= Chebyshev.theta (9593066420 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1289 hb38 9586172360 le_rfl (by norm_num)).2
  have hb40 : (10555144822433879922988 : Real) / 2 ^ 40 <= Chebyshev.theta (9599956548 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1290 hb39 9593066420 le_rfl (by norm_num)).2
  have hb41 : (10562722992002663278809 : Real) / 2 ^ 40 <= Chebyshev.theta (9606849438 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1291 hb40 9599956548 le_rfl (by norm_num)).2
  have hb42 : (10570301398077906912374 : Real) / 2 ^ 40 <= Chebyshev.theta (9613737320 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1292 hb41 9606849438 le_rfl (by norm_num)).2
  have hb43 : (10577880040440053793969 : Real) / 2 ^ 40 <= Chebyshev.theta (9620631452 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1293 hb42 9613737320 le_rfl (by norm_num)).2
  have hb44 : (10585458918893921445484 : Real) / 2 ^ 40 <= Chebyshev.theta (9627512618 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1294 hb43 9620631452 le_rfl (by norm_num)).2
  have hb45 : (10593038033154085728289 : Real) / 2 ^ 40 <= Chebyshev.theta (9634410032 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1295 hb44 9627512618 le_rfl (by norm_num)).2
  have hb46 : (10600617383499086365675 : Real) / 2 ^ 40 <= Chebyshev.theta (9641307624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1296 hb45 9634410032 le_rfl (by norm_num)).2
  have hb47 : (10608196969828262041476 : Real) / 2 ^ 40 <= Chebyshev.theta (9648209708 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1297 hb46 9641307624 le_rfl (by norm_num)).2
  have hb48 : (10615776791792926422061 : Real) / 2 ^ 40 <= Chebyshev.theta (9655094888 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1298 hb47 9648209708 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1299 hb48 9655094888 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 9489717398 with hc24 | hc24
  · rcases Nat.lt_or_ge n 9407056340 with hc12 | hc12
    · rcases Nat.lt_or_ge n 9365747922 with hc6 | hc6
      · rcases Nat.lt_or_ge n 9345087710 with hc3 | hc3
        · rcases Nat.lt_or_ge n 9331303454 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1251 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9338194602 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1252 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1253 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9351972468 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1254 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9358860108 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1255 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1256 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9386409890 with hc9 | hc9
        · rcases Nat.lt_or_ge n 9372642594 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1257 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9379525592 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1258 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1259 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9393292058 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1260 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9400168008 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1261 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1262 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 9448369374 with hc18 | hc18
      · rcases Nat.lt_or_ge n 9427709202 with hc15 | hc15
        · rcases Nat.lt_or_ge n 9413947200 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1263 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9420824004 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1264 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1265 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9434601774 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1266 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9441476868 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1267 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1268 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9469036394 with hc21 | hc21
        · rcases Nat.lt_or_ge n 9455266004 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1269 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9462151394 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1270 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1271 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9475928588 with hc22 | hc22
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1272 hb21 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9482820228 with hc23 | hc23
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1273 hb22 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1274 hb23 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 9572392652 with hc36 | hc36
    · rcases Nat.lt_or_ge n 9531044400 with hc30 | hc30
      · rcases Nat.lt_or_ge n 9510382854 with hc27 | hc27
        · rcases Nat.lt_or_ge n 9496598984 with hc25 | hc25
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1275 hb24 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9503493668 with hc26 | hc26
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1276 hb25 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1277 hb26 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9517274112 with hc28 | hc28
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1278 hb27 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9524161812 with hc29 | hc29
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1279 hb28 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1280 hb29 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9551725194 with hc33 | hc33
        · rcases Nat.lt_or_ge n 9537932618 with hc31 | hc31
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1281 hb30 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9544831890 with hc32 | hc32
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1282 hb31 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1283 hb32 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9558624738 with hc34 | hc34
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1284 hb33 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9565503980 with hc35 | hc35
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1285 hb34 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1286 hb35 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 9613737320 with hc42 | hc42
      · rcases Nat.lt_or_ge n 9593066420 with hc39 | hc39
        · rcases Nat.lt_or_ge n 9579289764 with hc37 | hc37
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1287 hb36 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9586172360 with hc38 | hc38
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1288 hb37 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1289 hb38 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9599956548 with hc40 | hc40
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1290 hb39 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9606849438 with hc41 | hc41
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1291 hb40 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1292 hb41 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9634410032 with hc45 | hc45
        · rcases Nat.lt_or_ge n 9620631452 with hc43 | hc43
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1293 hb42 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9627512618 with hc44 | hc44
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1294 hb43 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1295 hb44 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9648209708 with hc47 | hc47
          · rcases Nat.lt_or_ge n 9641307624 with hc46 | hc46
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1296 hb45 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1297 hb46 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 9655094888 with hc48 | hc48
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1298 hb47 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1299 hb48 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (10252213892257269854204 : Real) / 2 ^ 40 <= Chebyshev.theta (9324426324 : Real))
    (n : Nat) (h1 : 9324426324 <= n) (h2 : n <= 9661975291) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((10623356848875818030645 : Real) / 2 ^ 40 <= Chebyshev.theta (9661975292 : Real)) :=
  TFPLink.blk hbase n h1 h2
