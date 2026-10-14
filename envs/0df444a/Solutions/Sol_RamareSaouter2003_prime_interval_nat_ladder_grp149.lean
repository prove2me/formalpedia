-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp149
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T07:07:54.372332+00:00
-- url     : https://prove2.me/submissions/8d78afd7-edc0-470b-8495-161bc994cd39

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07400
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07443

theorem solution (n : Nat)
    (hn : 2706634033163334233 < n) (hupper : n <= 3108818837989423529) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2896666323243109367 n with h2 | h2
  · -- n > 2896666323243109367
    rcases Nat.lt_or_ge 2996629048991725729 n with h4 | h4
    · -- n > 2996629048991725729
      rcases Nat.lt_or_ge 3047896911951497423 n with h6 | h6
      · -- n > 3047896911951497423
        rcases Nat.lt_or_ge 3073858816910052817 n with h8 | h8
        · -- n > 3073858816910052817
          rcases Nat.lt_or_ge 3091289308628252729 n with h10 | h10
          · -- n > 3091289308628252729
            rcases Nat.lt_or_ge 3100041669999851509 n with h12 | h12
            · -- n > 3100041669999851509
              exact RamareSaouter2003.prime_interval_nat_ladder_c07443 n (by omega) (by omega)
            · -- n <= 3100041669999851509
              exact RamareSaouter2003.prime_interval_nat_ladder_c07442 n (by omega) (by omega)
          · -- n <= 3091289308628252729
            rcases Nat.lt_or_ge 3082561673370477211 n with h12 | h12
            · -- n > 3082561673370477211
              exact RamareSaouter2003.prime_interval_nat_ladder_c07441 n (by omega) (by omega)
            · -- n <= 3082561673370477211
              exact RamareSaouter2003.prime_interval_nat_ladder_c07440 n (by omega) (by omega)
        · -- n <= 3073858816910052817
          rcases Nat.lt_or_ge 3056526442310759849 n with h10 | h10
          · -- n > 3056526442310759849
            rcases Nat.lt_or_ge 3065180385219156229 n with h12 | h12
            · -- n > 3065180385219156229
              exact RamareSaouter2003.prime_interval_nat_ladder_c07439 n (by omega) (by omega)
            · -- n <= 3065180385219156229
              exact RamareSaouter2003.prime_interval_nat_ladder_c07438 n (by omega) (by omega)
          · -- n <= 3056526442310759849
            exact RamareSaouter2003.prime_interval_nat_ladder_c07437 n (by omega) (by omega)
      · -- n <= 3047896911951497423
        rcases Nat.lt_or_ge 3022154268822828437 n with h8 | h8
        · -- n > 3022154268822828437
          rcases Nat.lt_or_ge 3030710888912114623 n with h10 | h10
          · -- n > 3030710888912114623
            rcases Nat.lt_or_ge 3039291759844546163 n with h12 | h12
            · -- n > 3039291759844546163
              exact RamareSaouter2003.prime_interval_nat_ladder_c07436 n (by omega) (by omega)
            · -- n <= 3039291759844546163
              exact RamareSaouter2003.prime_interval_nat_ladder_c07435 n (by omega) (by omega)
          · -- n <= 3030710888912114623
            exact RamareSaouter2003.prime_interval_nat_ladder_c07434 n (by omega) (by omega)
        · -- n <= 3022154268822828437
          rcases Nat.lt_or_ge 3005113412050048549 n with h10 | h10
          · -- n > 3005113412050048549
            rcases Nat.lt_or_ge 3013621799183563639 n with h12 | h12
            · -- n > 3013621799183563639
              exact RamareSaouter2003.prime_interval_nat_ladder_c07433 n (by omega) (by omega)
            · -- n <= 3013621799183563639
              exact RamareSaouter2003.prime_interval_nat_ladder_c07432 n (by omega) (by omega)
          · -- n <= 3005113412050048549
            exact RamareSaouter2003.prime_interval_nat_ladder_c07431 n (by omega) (by omega)
    · -- n <= 2996629048991725729
      rcases Nat.lt_or_ge 2946223809378193291 n with h6 | h6
      · -- n > 2946223809378193291
        rcases Nat.lt_or_ge 2971319503450983637 n with h8 | h8
        · -- n > 2971319503450983637
          rcases Nat.lt_or_ge 2979732105633888919 n with h10 | h10
          · -- n > 2979732105633888919
            rcases Nat.lt_or_ge 2988168624687091711 n with h12 | h12
            · -- n > 2988168624687091711
              exact RamareSaouter2003.prime_interval_nat_ladder_c07430 n (by omega) (by omega)
            · -- n <= 2988168624687091711
              exact RamareSaouter2003.prime_interval_nat_ladder_c07429 n (by omega) (by omega)
          · -- n <= 2979732105633888919
            exact RamareSaouter2003.prime_interval_nat_ladder_c07428 n (by omega) (by omega)
        · -- n <= 2971319503450983637
          rcases Nat.lt_or_ge 2954565412330053307 n with h10 | h10
          · -- n > 2954565412330053307
            rcases Nat.lt_or_ge 2962930601691924323 n with h12 | h12
            · -- n > 2962930601691924323
              exact RamareSaouter2003.prime_interval_nat_ladder_c07427 n (by omega) (by omega)
            · -- n <= 2962930601691924323
              exact RamareSaouter2003.prime_interval_nat_ladder_c07426 n (by omega) (by omega)
          · -- n <= 2954565412330053307
            exact RamareSaouter2003.prime_interval_nat_ladder_c07425 n (by omega) (by omega)
      · -- n <= 2946223809378193291
        rcases Nat.lt_or_ge 2921339949033833339 n with h8 | h8
        · -- n > 2921339949033833339
          rcases Nat.lt_or_ge 2929611112165747133 n with h10 | h10
          · -- n > 2929611112165747133
            rcases Nat.lt_or_ge 2937905743067099087 n with h12 | h12
            · -- n > 2937905743067099087
              exact RamareSaouter2003.prime_interval_nat_ladder_c07424 n (by omega) (by omega)
            · -- n <= 2937905743067099087
              exact RamareSaouter2003.prime_interval_nat_ladder_c07423 n (by omega) (by omega)
          · -- n <= 2929611112165747133
            exact RamareSaouter2003.prime_interval_nat_ladder_c07422 n (by omega) (by omega)
        · -- n <= 2921339949033833339
          rcases Nat.lt_or_ge 2904867581880912623 n with h10 | h10
          · -- n > 2904867581880912623
            rcases Nat.lt_or_ge 2913092115369593041 n with h12 | h12
            · -- n > 2913092115369593041
              exact RamareSaouter2003.prime_interval_nat_ladder_c07421 n (by omega) (by omega)
            · -- n <= 2913092115369593041
              exact RamareSaouter2003.prime_interval_nat_ladder_c07420 n (by omega) (by omega)
          · -- n <= 2904867581880912623
            exact RamareSaouter2003.prime_interval_nat_ladder_c07419 n (by omega) (by omega)
  · -- n <= 2896666323243109367
    rcases Nat.lt_or_ge 2800038518111129311 n with h4 | h4
    · -- n > 2800038518111129311
      rcases Nat.lt_or_ge 2847942479940769667 n with h6 | h6
      · -- n > 2847942479940769667
        rcases Nat.lt_or_ge 2872201119084651577 n with h8 | h8
        · -- n > 2872201119084651577
          rcases Nat.lt_or_ge 2880333191648730563 n with h10 | h10
          · -- n > 2880333191648730563
            rcases Nat.lt_or_ge 2888488167541803847 n with h12 | h12
            · -- n > 2888488167541803847
              exact RamareSaouter2003.prime_interval_nat_ladder_c07418 n (by omega) (by omega)
            · -- n <= 2888488167541803847
              exact RamareSaouter2003.prime_interval_nat_ladder_c07417 n (by omega) (by omega)
          · -- n <= 2880333191648730563
            exact RamareSaouter2003.prime_interval_nat_ladder_c07416 n (by omega) (by omega)
        · -- n <= 2872201119084651577
          rcases Nat.lt_or_ge 2856005842252770343 n with h10 | h10
          · -- n > 2856005842252770343
            rcases Nat.lt_or_ge 2864092043674648529 n with h12 | h12
            · -- n > 2864092043674648529
              exact RamareSaouter2003.prime_interval_nat_ladder_c07415 n (by omega) (by omega)
            · -- n <= 2864092043674648529
              exact RamareSaouter2003.prime_interval_nat_ladder_c07414 n (by omega) (by omega)
          · -- n <= 2856005842252770343
            exact RamareSaouter2003.prime_interval_nat_ladder_c07413 n (by omega) (by omega)
      · -- n <= 2847942479940769667
        rcases Nat.lt_or_ge 2823889122037303577 n with h8 | h8
        · -- n > 2823889122037303577
          rcases Nat.lt_or_ge 2831884341429528173 n with h10 | h10
          · -- n > 2831884341429528173
            rcases Nat.lt_or_ge 2839901924870547613 n with h12 | h12
            · -- n > 2839901924870547613
              exact RamareSaouter2003.prime_interval_nat_ladder_c07412 n (by omega) (by omega)
            · -- n <= 2839901924870547613
              exact RamareSaouter2003.prime_interval_nat_ladder_c07411 n (by omega) (by omega)
          · -- n <= 2831884341429528173
            exact RamareSaouter2003.prime_interval_nat_ladder_c07410 n (by omega) (by omega)
        · -- n <= 2823889122037303577
          rcases Nat.lt_or_ge 2807966251281773719 n with h10 | h10
          · -- n > 2807966251281773719
            rcases Nat.lt_or_ge 2815916451245376257 n with h12 | h12
            · -- n > 2815916451245376257
              exact RamareSaouter2003.prime_interval_nat_ladder_c07409 n (by omega) (by omega)
            · -- n <= 2815916451245376257
              exact RamareSaouter2003.prime_interval_nat_ladder_c07408 n (by omega) (by omega)
          · -- n <= 2807966251281773719
            exact RamareSaouter2003.prime_interval_nat_ladder_c07407 n (by omega) (by omega)
    · -- n <= 2800038518111129311
      rcases Nat.lt_or_ge 2752940124603708433 n with h6 | h6
      · -- n > 2752940124603708433
        rcases Nat.lt_or_ge 2776389440363833207 n with h8 | h8
        · -- n > 2776389440363833207
          rcases Nat.lt_or_ge 2784250225134880109 n with h10 | h10
          · -- n > 2784250225134880109
            rcases Nat.lt_or_ge 2792133267761319277 n with h12 | h12
            · -- n > 2792133267761319277
              exact RamareSaouter2003.prime_interval_nat_ladder_c07406 n (by omega) (by omega)
            · -- n <= 2792133267761319277
              exact RamareSaouter2003.prime_interval_nat_ladder_c07405 n (by omega) (by omega)
          · -- n <= 2784250225134880109
            exact RamareSaouter2003.prime_interval_nat_ladder_c07404 n (by omega) (by omega)
        · -- n <= 2776389440363833207
          rcases Nat.lt_or_ge 2760734472067239821 n with h10 | h10
          · -- n > 2760734472067239821
            rcases Nat.lt_or_ge 2768550932780229437 n with h12 | h12
            · -- n > 2768550932780229437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07403 n (by omega) (by omega)
            · -- n <= 2768550932780229437
              exact RamareSaouter2003.prime_interval_nat_ladder_c07402 n (by omega) (by omega)
          · -- n <= 2760734472067239821
            exact RamareSaouter2003.prime_interval_nat_ladder_c07401 n (by omega) (by omega)
      · -- n <= 2752940124603708433
        rcases Nat.lt_or_ge 2729688886108246991 n with h8 | h8
        · -- n > 2729688886108246991
          rcases Nat.lt_or_ge 2737417376567205391 n with h10 | h10
          · -- n > 2737417376567205391
            rcases Nat.lt_or_ge 2745167793785881823 n with h12 | h12
            · -- n > 2745167793785881823
              exact RamareSaouter2003.prime_interval_nat_ladder_c07400 n (by omega) (by omega)
            · -- n <= 2745167793785881823
              exact RamareSaouter2003.prime_interval_nat_ladder_c07399 n (by omega) (by omega)
          · -- n <= 2737417376567205391
            exact RamareSaouter2003.prime_interval_nat_ladder_c07398 n (by omega) (by omega)
        · -- n <= 2729688886108246991
          rcases Nat.lt_or_ge 2714297341305680693 n with h10 | h10
          · -- n > 2714297341305680693
            rcases Nat.lt_or_ge 2721982170212032661 n with h12 | h12
            · -- n > 2721982170212032661
              exact RamareSaouter2003.prime_interval_nat_ladder_c07397 n (by omega) (by omega)
            · -- n <= 2721982170212032661
              exact RamareSaouter2003.prime_interval_nat_ladder_c07396 n (by omega) (by omega)
          · -- n <= 2714297341305680693
            exact RamareSaouter2003.prime_interval_nat_ladder_c07395 n (by omega) (by omega)
