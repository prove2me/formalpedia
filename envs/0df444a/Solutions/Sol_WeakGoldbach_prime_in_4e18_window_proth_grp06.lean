-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp06
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:47:34.638536+00:00
-- url     : https://prove2.me/submissions/89d753c0-f8dc-4822-bdd7-95bf08744da5

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg246
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg247
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg248
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg249
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg250
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg251
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg252
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg253
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg254
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg255
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg256
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg257
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg258
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg259
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg260
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg261
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg262
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg263
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg264
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg265
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg266
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg267
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg268
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg269
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg270
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg271
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg272
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg273
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg274
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg275
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg276
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg277
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg278
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg279
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg280
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg281
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg282
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg283
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg284
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg285
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg286
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg287
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg288
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg289
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg290
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg291
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg292
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg293
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg294

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp06` (31329926130109707370627073 <= x < 37595910556489387507449857) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg246` .. `WeakGoldbach.prime_in_4e18_window_proth_seg294`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 31329926130109707370627073 ≤ x) (hx : x < 37595910556489387507449857) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 34398979726713171046563841 with hc24 | hc24
  · rcases Nat.lt_or_ge x 32864452927338315859886081 with hc12 | hc12
    · rcases Nat.lt_or_ge x 32097189529410106870988801 with hc6 | hc6
      · rcases Nat.lt_or_ge x 31713557828572434562809857 with hc3 | hc3
        · rcases Nat.lt_or_ge x 31457803363018577364910081 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg246 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 31585680596490397312614401 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg247 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg248 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 31841435063134970045267969 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg249 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 31969312296202169713950721 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg250 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg251 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 32480821228717258993303553 with hc9 | hc9
        · rcases Nat.lt_or_ge x 32225066762107870632738817 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg252 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 32352943995738020254842881 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg253 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg254 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 32608698461942788336386049 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg255 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 32736575695203502051557377 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg256 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg257 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 33631716327465548104335361 with hc18 | hc18
      · rcases Nat.lt_or_ge x 33248084628158395982020609 with hc15 | hc15
        · rcases Nat.lt_or_ge x 32992330161619376365633537 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg258 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 33120207394985643197071361 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg259 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg260 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 33375961860733014441459713 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg261 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 33503839094609454668185601 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg262 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg263 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 34015348026403264319717377 with hc21 | hc21
        · rcases Nat.lt_or_ge x 33759593560884591493906433 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg264 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 33887470793494394325434369 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg265 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg266 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 34143225259822307709288449 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg267 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 34271102493382088587214849 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg268 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg269 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 35933506525067679442665473 with hc36 | hc36
    · rcases Nat.lt_or_ge x 35166243125116369058660353 with hc30 | hc30
      · rcases Nat.lt_or_ge x 34782611425650887261945857 with hc27 | hc27
        · rcases Nat.lt_or_ge x 34526856958953537971159041 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg270 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 34654734193252190662950913 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg271 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg272 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 34910488659685657163071489 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg273 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 35038365892682488087576577 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg274 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg275 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 35549874825338314855284737 with hc33 | hc33
        · rcases Nat.lt_or_ge x 35294120359168731145830401 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg276 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 35421997592341483930779649 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg277 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg278 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 35677752058475883268145153 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg279 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 35805629291701412611227649 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg280 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg281 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 36700769924192157082583041 with hc42 | hc42
      · rcases Nat.lt_or_ge x 36317138224480384681246721 with hc39 | hc39
        · rcases Nat.lt_or_ge x 36061383758293208785747969 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg282 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 36189260990850235059142657 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg283 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg284 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 36445015457389254675529729 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg285 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 36572892691124957413900289 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg286 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg287 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 37084401623780784181608449 with hc45 | hc45
        · rcases Nat.lt_or_ge x 36828647156749183355977729 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg288 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 36956524390625623582703617 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg289 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg290 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 37340156090091105379418113 with hc47 | hc47
          · rcases Nat.lt_or_ge x 37212278856812799478202369 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg291 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg292 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 37468033322929606629523457 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg293 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg294 x (by omega) (by omega)
