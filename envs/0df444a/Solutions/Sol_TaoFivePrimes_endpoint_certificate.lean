-- Prove2me | solution 1 for TaoFivePrimes.endpoint_certificate
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-29T12:57:53.667984+00:00
-- url     : https://prove2.me/submissions/2d33b734-d82a-45ab-bae0-44a2da20dc14

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables
import Definitions.Def_TaoFivePrimes_theta_cert_tables

open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

open TaoFivePrimes

theorem solution (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (T n : Rat) ≤ llb (lastP n) + rho n + 4/(lub (firstP n))^3 + Mq := by
  interval_cases n
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 2 = (1/2) by rfl, show lastP 2 = 2 by rfl, show firstP 2 = 3 by rfl,
        show llb 2 = (-366597/1000000) by rfl, show lub 2 = (693163/1000000) by rfl,
        show lub 3 = (274657/250000) by rfl, show clbZ 2 = 6931 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 3 = (5/6) by rfl, show lastP 3 = 3 by rfl, show firstP 3 = 5 by rfl,
        show llb 3 = (94021/1000000) by rfl, show lub 3 = (274657/250000) by rfl,
        show lub 5 = (804727/500000) by rfl, show clbZ 3 = 10986 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 4 = (5/6) by rfl, show lastP 4 = 3 by rfl, show firstP 4 = 5 by rfl,
        show llb 3 = (94021/1000000) by rfl, show lub 3 = (274657/250000) by rfl,
        show lub 5 = (804727/500000) by rfl, show clbZ 3 = 10986 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 5 = (31/30) by rfl, show lastP 5 = 5 by rfl, show firstP 5 = 7 by rfl,
        show llb 5 = (237923/500000) by rfl, show lub 5 = (804727/500000) by rfl,
        show lub 7 = (972963/500000) by rfl, show clbZ 5 = 16094 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 6 = (31/30) by rfl, show lastP 6 = 5 by rfl, show firstP 6 = 7 by rfl,
        show llb 5 = (237923/500000) by rfl, show lub 5 = (804727/500000) by rfl,
        show lub 7 = (972963/500000) by rfl, show clbZ 5 = 16094 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 7 = (247/210) by rfl, show lastP 7 = 7 by rfl, show firstP 7 = 11 by rfl,
        show llb 7 = (665709/1000000) by rfl, show lub 7 = (972963/500000) by rfl,
        show lub 11 = (2397911/1000000) by rfl, show clbZ 7 = 19459 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 8 = (247/210) by rfl, show lastP 8 = 7 by rfl, show firstP 8 = 11 by rfl,
        show llb 7 = (665709/1000000) by rfl, show lub 7 = (972963/500000) by rfl,
        show lub 11 = (2397911/1000000) by rfl, show clbZ 7 = 19459 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 9 = (247/210) by rfl, show lastP 9 = 7 by rfl, show firstP 9 = 11 by rfl,
        show llb 7 = (665709/1000000) by rfl, show lub 7 = (972963/500000) by rfl,
        show lub 11 = (2397911/1000000) by rfl, show clbZ 7 = 19459 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 10 = (247/210) by rfl, show lastP 10 = 7 by rfl, show firstP 10 = 11 by rfl,
        show llb 7 = (665709/1000000) by rfl, show lub 7 = (972963/500000) by rfl,
        show lub 11 = (2397911/1000000) by rfl, show clbZ 7 = 19459 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 11 = (2927/2310) by rfl, show lastP 11 = 11 by rfl, show firstP 11 = 13 by rfl,
        show llb 11 = (109317/125000) by rfl, show lub 11 = (2397911/1000000) by rfl,
        show lub 13 = (512993/200000) by rfl, show clbZ 11 = 23978 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 12 = (2927/2310) by rfl, show lastP 12 = 11 by rfl, show firstP 12 = 13 by rfl,
        show llb 11 = (109317/125000) by rfl, show lub 11 = (2397911/1000000) by rfl,
        show lub 13 = (512993/200000) by rfl, show clbZ 11 = 23978 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 13 = (40361/30030) by rfl, show lastP 13 = 13 by rfl, show firstP 13 = 17 by rfl,
        show llb 13 = (58869/62500) by rfl, show lub 13 = (512993/200000) by rfl,
        show lub 17 = (2833229/1000000) by rfl, show clbZ 13 = 25649 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 14 = (40361/30030) by rfl, show lastP 14 = 13 by rfl, show firstP 14 = 17 by rfl,
        show llb 13 = (58869/62500) by rfl, show lub 13 = (512993/200000) by rfl,
        show lub 17 = (2833229/1000000) by rfl, show clbZ 13 = 25649 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 15 = (40361/30030) by rfl, show lastP 15 = 13 by rfl, show firstP 15 = 17 by rfl,
        show llb 13 = (58869/62500) by rfl, show lub 13 = (512993/200000) by rfl,
        show lub 17 = (2833229/1000000) by rfl, show clbZ 13 = 25649 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 16 = (40361/30030) by rfl, show lastP 16 = 13 by rfl, show firstP 16 = 17 by rfl,
        show llb 13 = (58869/62500) by rfl, show lub 13 = (512993/200000) by rfl,
        show lub 17 = (2833229/1000000) by rfl, show clbZ 13 = 25649 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 17 = (716167/510510) by rfl, show lastP 17 = 17 by rfl, show firstP 17 = 19 by rfl,
        show llb 17 = (1041391/1000000) by rfl, show lub 17 = (2833229/1000000) by rfl,
        show lub 19 = (588891/200000) by rfl, show clbZ 17 = 28332 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 18 = (716167/510510) by rfl, show lastP 18 = 17 by rfl, show firstP 18 = 19 by rfl,
        show llb 17 = (1041391/1000000) by rfl, show lub 17 = (2833229/1000000) by rfl,
        show lub 19 = (588891/200000) by rfl, show clbZ 17 = 28332 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 19 = (14117683/9699690) by rfl, show lastP 19 = 19 by rfl, show firstP 19 = 23 by rfl,
        show llb 19 = (1079889/1000000) by rfl, show lub 19 = (588891/200000) by rfl,
        show lub 23 = (313551/100000) by rfl, show clbZ 19 = 29444 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 20 = (14117683/9699690) by rfl, show lastP 20 = 19 by rfl, show firstP 20 = 23 by rfl,
        show llb 19 = (1079889/1000000) by rfl, show lub 19 = (588891/200000) by rfl,
        show lub 23 = (313551/100000) by rfl, show clbZ 19 = 29444 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 21 = (14117683/9699690) by rfl, show lastP 21 = 19 by rfl, show firstP 21 = 23 by rfl,
        show llb 19 = (1079889/1000000) by rfl, show lub 19 = (588891/200000) by rfl,
        show lub 23 = (313551/100000) by rfl, show clbZ 19 = 29444 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 22 = (14117683/9699690) by rfl, show lastP 22 = 19 by rfl, show firstP 22 = 23 by rfl,
        show llb 19 = (1079889/1000000) by rfl, show lub 19 = (588891/200000) by rfl,
        show lub 23 = (313551/100000) by rfl, show clbZ 19 = 29444 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 23 = (334406399/223092870) by rfl, show lastP 23 = 23 by rfl, show firstP 23 = 29 by rfl,
        show llb 23 = (1142741/1000000) by rfl, show lub 23 = (313551/100000) by rfl,
        show lub 29 = (210457/62500) by rfl, show clbZ 23 = 31354 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 24 = (334406399/223092870) by rfl, show lastP 24 = 23 by rfl, show firstP 24 = 29 by rfl,
        show llb 23 = (1142741/1000000) by rfl, show lub 23 = (313551/100000) by rfl,
        show lub 29 = (210457/62500) by rfl, show clbZ 23 = 31354 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 25 = (334406399/223092870) by rfl, show lastP 25 = 23 by rfl, show firstP 25 = 29 by rfl,
        show llb 23 = (1142741/1000000) by rfl, show lub 23 = (313551/100000) by rfl,
        show lub 29 = (210457/62500) by rfl, show clbZ 23 = 31354 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 26 = (334406399/223092870) by rfl, show lastP 26 = 23 by rfl, show firstP 26 = 29 by rfl,
        show llb 23 = (1142741/1000000) by rfl, show lub 23 = (313551/100000) by rfl,
        show lub 29 = (210457/62500) by rfl, show clbZ 23 = 31354 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 27 = (334406399/223092870) by rfl, show lastP 27 = 23 by rfl, show firstP 27 = 29 by rfl,
        show llb 23 = (1142741/1000000) by rfl, show lub 23 = (313551/100000) by rfl,
        show lub 29 = (210457/62500) by rfl, show clbZ 23 = 31354 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 28 = (334406399/223092870) by rfl, show lastP 28 = 23 by rfl, show firstP 28 = 29 by rfl,
        show llb 23 = (1142741/1000000) by rfl, show lub 23 = (313551/100000) by rfl,
        show lub 29 = (210457/62500) by rfl, show clbZ 23 = 31354 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 29 = (9920878441/6469693230) by rfl, show lastP 29 = 29 by rfl, show firstP 29 = 31 by rfl,
        show llb 29 = (607033/500000) by rfl, show lub 29 = (210457/62500) by rfl,
        show lub 31 = (3434003/1000000) by rfl, show clbZ 29 = 33672 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 30 = (9920878441/6469693230) by rfl, show lastP 30 = 29 by rfl, show firstP 30 = 31 by rfl,
        show llb 29 = (607033/500000) by rfl, show lub 29 = (210457/62500) by rfl,
        show lub 31 = (3434003/1000000) by rfl, show clbZ 29 = 33672 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 31 = (314016924901/200560490130) by rfl, show lastP 31 = 31 by rfl, show firstP 31 = 37 by rfl,
        show llb 31 = (1233681/1000000) by rfl, show lub 31 = (3434003/1000000) by rfl,
        show lub 37 = (1805467/500000) by rfl, show clbZ 31 = 34339 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 32 = (314016924901/200560490130) by rfl, show lastP 32 = 31 by rfl, show firstP 32 = 37 by rfl,
        show llb 31 = (1233681/1000000) by rfl, show lub 31 = (3434003/1000000) by rfl,
        show lub 37 = (1805467/500000) by rfl, show clbZ 31 = 34339 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 33 = (314016924901/200560490130) by rfl, show lastP 33 = 31 by rfl, show firstP 33 = 37 by rfl,
        show llb 31 = (1233681/1000000) by rfl, show lub 31 = (3434003/1000000) by rfl,
        show lub 37 = (1805467/500000) by rfl, show clbZ 31 = 34339 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 34 = (314016924901/200560490130) by rfl, show lastP 34 = 31 by rfl, show firstP 34 = 37 by rfl,
        show llb 31 = (1233681/1000000) by rfl, show lub 31 = (3434003/1000000) by rfl,
        show lub 37 = (1805467/500000) by rfl, show clbZ 31 = 34339 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 35 = (314016924901/200560490130) by rfl, show lastP 35 = 31 by rfl, show firstP 35 = 37 by rfl,
        show llb 31 = (1233681/1000000) by rfl, show lub 31 = (3434003/1000000) by rfl,
        show lub 37 = (1805467/500000) by rfl, show clbZ 31 = 34339 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 36 = (314016924901/200560490130) by rfl, show lastP 36 = 31 by rfl, show firstP 36 = 37 by rfl,
        show llb 31 = (1233681/1000000) by rfl, show lub 31 = (3434003/1000000) by rfl,
        show lub 37 = (1805467/500000) by rfl, show clbZ 31 = 34339 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 37 = (11819186711467/7420738134810) by rfl, show lastP 37 = 37 by rfl, show firstP 37 = 41 by rfl,
        show llb 37 = (1283941/1000000) by rfl, show lub 37 = (1805467/500000) by rfl,
        show lub 41 = (928397/250000) by rfl, show clbZ 37 = 36109 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 38 = (11819186711467/7420738134810) by rfl, show lastP 38 = 37 by rfl, show firstP 38 = 41 by rfl,
        show llb 37 = (1283941/1000000) by rfl, show lub 37 = (1805467/500000) by rfl,
        show lub 41 = (928397/250000) by rfl, show clbZ 37 = 36109 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 39 = (11819186711467/7420738134810) by rfl, show lastP 39 = 37 by rfl, show firstP 39 = 41 by rfl,
        show llb 37 = (1283941/1000000) by rfl, show lub 37 = (1805467/500000) by rfl,
        show lub 41 = (928397/250000) by rfl, show clbZ 37 = 36109 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 40 = (11819186711467/7420738134810) by rfl, show lastP 40 = 37 by rfl, show firstP 40 = 41 by rfl,
        show llb 37 = (1283941/1000000) by rfl, show lub 37 = (1805467/500000) by rfl,
        show lub 41 = (928397/250000) by rfl, show clbZ 37 = 36109 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 41 = (492007393304957/304250263527210) by rfl, show lastP 41 = 41 by rfl, show firstP 41 = 43 by rfl,
        show llb 41 = (1311959/1000000) by rfl, show lub 41 = (928397/250000) by rfl,
        show lub 43 = (58769/15625) by rfl, show clbZ 41 = 37135 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 42 = (492007393304957/304250263527210) by rfl, show lastP 42 = 41 by rfl, show firstP 42 = 43 by rfl,
        show llb 41 = (1311959/1000000) by rfl, show lub 41 = (928397/250000) by rfl,
        show lub 43 = (58769/15625) by rfl, show clbZ 41 = 37135 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 43 = (21460568175640361/13082761331670030) by rfl, show lastP 43 = 43 by rfl, show firstP 43 = 47 by rfl,
        show llb 43 = (662361/500000) by rfl, show lub 43 = (58769/15625) by rfl,
        show lub 47 = (3850163/1000000) by rfl, show clbZ 43 = 37612 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 44 = (21460568175640361/13082761331670030) by rfl, show lastP 44 = 43 by rfl, show firstP 44 = 47 by rfl,
        show llb 43 = (662361/500000) by rfl, show lub 43 = (58769/15625) by rfl,
        show lub 47 = (3850163/1000000) by rfl, show clbZ 43 = 37612 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 45 = (21460568175640361/13082761331670030) by rfl, show lastP 45 = 43 by rfl, show firstP 45 = 47 by rfl,
        show llb 43 = (662361/500000) by rfl, show lub 43 = (58769/15625) by rfl,
        show lub 47 = (3850163/1000000) by rfl, show clbZ 43 = 37612 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 46 = (21460568175640361/13082761331670030) by rfl, show lastP 46 = 43 by rfl, show firstP 46 = 47 by rfl,
        show llb 43 = (662361/500000) by rfl, show lub 43 = (58769/15625) by rfl,
        show lub 47 = (3850163/1000000) by rfl, show clbZ 43 = 37612 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 47 = (1021729465586766997/614889782588491410) by rfl, show lastP 47 = 47 by rfl, show firstP 47 = 53 by rfl,
        show llb 47 = (1348083/1000000) by rfl, show lub 47 = (3850163/1000000) by rfl,
        show lub 53 = (992577/250000) by rfl, show clbZ 47 = 38501 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 48 = (1021729465586766997/614889782588491410) by rfl, show lastP 48 = 47 by rfl, show firstP 48 = 53 by rfl,
        show llb 47 = (1348083/1000000) by rfl, show lub 47 = (3850163/1000000) by rfl,
        show lub 53 = (992577/250000) by rfl, show clbZ 47 = 38501 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 49 = (1021729465586766997/614889782588491410) by rfl, show lastP 49 = 47 by rfl, show firstP 49 = 53 by rfl,
        show llb 47 = (1348083/1000000) by rfl, show lub 47 = (3850163/1000000) by rfl,
        show lub 53 = (992577/250000) by rfl, show clbZ 47 = 38501 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 50 = (1021729465586766997/614889782588491410) by rfl, show lastP 50 = 47 by rfl, show firstP 50 = 53 by rfl,
        show llb 47 = (1348083/1000000) by rfl, show lub 47 = (3850163/1000000) by rfl,
        show lub 53 = (992577/250000) by rfl, show clbZ 47 = 38501 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 51 = (1021729465586766997/614889782588491410) by rfl, show lastP 51 = 47 by rfl, show firstP 51 = 53 by rfl,
        show llb 47 = (1348083/1000000) by rfl, show lub 47 = (3850163/1000000) by rfl,
        show lub 53 = (992577/250000) by rfl, show clbZ 47 = 38501 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 52 = (1021729465586766997/614889782588491410) by rfl, show lastP 52 = 47 by rfl, show firstP 52 = 53 by rfl,
        show llb 47 = (1348083/1000000) by rfl, show lub 47 = (3850163/1000000) by rfl,
        show lub 53 = (992577/250000) by rfl, show clbZ 47 = 38501 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 53 = (54766551458687142251/32589158477190044730) by rfl, show lastP 53 = 53 by rfl, show firstP 53 = 59 by rfl,
        show llb 53 = (1378801/1000000) by rfl, show lub 53 = (992577/250000) by rfl,
        show lub 59 = (4077553/1000000) by rfl, show clbZ 53 = 39702 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 54 = (54766551458687142251/32589158477190044730) by rfl, show lastP 54 = 53 by rfl, show firstP 54 = 59 by rfl,
        show llb 53 = (1378801/1000000) by rfl, show lub 53 = (992577/250000) by rfl,
        show lub 59 = (4077553/1000000) by rfl, show clbZ 53 = 39702 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 55 = (54766551458687142251/32589158477190044730) by rfl, show lastP 55 = 53 by rfl, show firstP 55 = 59 by rfl,
        show llb 53 = (1378801/1000000) by rfl, show lub 53 = (992577/250000) by rfl,
        show lub 59 = (4077553/1000000) by rfl, show clbZ 53 = 39702 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 56 = (54766551458687142251/32589158477190044730) by rfl, show lastP 56 = 53 by rfl, show firstP 56 = 59 by rfl,
        show llb 53 = (1378801/1000000) by rfl, show lub 53 = (992577/250000) by rfl,
        show lub 59 = (4077553/1000000) by rfl, show clbZ 53 = 39702 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 57 = (54766551458687142251/32589158477190044730) by rfl, show lastP 57 = 53 by rfl, show firstP 57 = 59 by rfl,
        show llb 53 = (1378801/1000000) by rfl, show lub 53 = (992577/250000) by rfl,
        show lub 59 = (4077553/1000000) by rfl, show clbZ 53 = 39702 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 58 = (54766551458687142251/32589158477190044730) by rfl, show lastP 58 = 53 by rfl, show firstP 58 = 59 by rfl,
        show llb 53 = (1378801/1000000) by rfl, show lub 53 = (992577/250000) by rfl,
        show lub 59 = (4077553/1000000) by rfl, show clbZ 53 = 39702 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 59 = (3263815694539731437539/1922760350154212639070) by rfl, show lastP 59 = 59 by rfl, show firstP 59 = 61 by rfl,
        show llb 59 = (351367/250000) by rfl, show lub 59 = (4077553/1000000) by rfl,
        show lub 61 = (411089/100000) by rfl, show clbZ 59 = 40775 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 60 = (3263815694539731437539/1922760350154212639070) by rfl, show lastP 60 = 59 by rfl, show firstP 60 = 61 by rfl,
        show llb 59 = (351367/250000) by rfl, show lub 59 = (4077553/1000000) by rfl,
        show lub 61 = (411089/100000) by rfl, show clbZ 59 = 40775 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 61 = (201015517717077830328949/117288381359406970983270) by rfl, show lastP 61 = 61 by rfl, show firstP 61 = 67 by rfl,
        show llb 61 = (706801/500000) by rfl, show lub 61 = (411089/100000) by rfl,
        show lub 67 = (1051177/250000) by rfl, show clbZ 61 = 41108 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 62 = (201015517717077830328949/117288381359406970983270) by rfl, show lastP 62 = 61 by rfl, show firstP 62 = 67 by rfl,
        show llb 61 = (706801/500000) by rfl, show lub 61 = (411089/100000) by rfl,
        show lub 67 = (1051177/250000) by rfl, show clbZ 61 = 41108 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 63 = (201015517717077830328949/117288381359406970983270) by rfl, show lastP 63 = 61 by rfl, show firstP 63 = 67 by rfl,
        show llb 61 = (706801/500000) by rfl, show lub 61 = (411089/100000) by rfl,
        show lub 67 = (1051177/250000) by rfl, show clbZ 61 = 41108 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 64 = (201015517717077830328949/117288381359406970983270) by rfl, show lastP 64 = 61 by rfl, show firstP 64 = 67 by rfl,
        show llb 61 = (706801/500000) by rfl, show lub 61 = (411089/100000) by rfl,
        show lub 67 = (1051177/250000) by rfl, show clbZ 61 = 41108 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 65 = (201015517717077830328949/117288381359406970983270) by rfl, show lastP 65 = 61 by rfl, show firstP 65 = 67 by rfl,
        show llb 61 = (706801/500000) by rfl, show lub 61 = (411089/100000) by rfl,
        show lub 67 = (1051177/250000) by rfl, show clbZ 61 = 41108 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 66 = (201015517717077830328949/117288381359406970983270) by rfl, show lastP 66 = 61 by rfl, show firstP 66 = 67 by rfl,
        show llb 61 = (706801/500000) by rfl, show lub 61 = (411089/100000) by rfl,
        show lub 67 = (1051177/250000) by rfl, show clbZ 61 = 41108 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 67 = (13585328068403621603022853/7858321551080267055879090) by rfl, show lastP 67 = 67 by rfl, show firstP 67 = 71 by rfl,
        show llb 67 = (1436163/1000000) by rfl, show lub 67 = (1051177/250000) by rfl,
        show lub 71 = (532837/125000) by rfl, show clbZ 67 = 42046 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 68 = (13585328068403621603022853/7858321551080267055879090) by rfl, show lastP 68 = 67 by rfl, show firstP 68 = 71 by rfl,
        show llb 67 = (1436163/1000000) by rfl, show lub 67 = (1051177/250000) by rfl,
        show lub 71 = (532837/125000) by rfl, show clbZ 67 = 42046 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 69 = (13585328068403621603022853/7858321551080267055879090) by rfl, show lastP 69 = 67 by rfl, show firstP 69 = 71 by rfl,
        show llb 67 = (1436163/1000000) by rfl, show lub 67 = (1051177/250000) by rfl,
        show lub 71 = (532837/125000) by rfl, show clbZ 67 = 42046 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 70 = (13585328068403621603022853/7858321551080267055879090) by rfl, show lastP 70 = 67 by rfl, show firstP 70 = 71 by rfl,
        show llb 67 = (1436163/1000000) by rfl, show lub 67 = (1051177/250000) by rfl,
        show lub 71 = (532837/125000) by rfl, show clbZ 67 = 42046 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 71 = (972416614407737400870501653/557940830126698960967415390) by rfl, show lastP 71 = 71 by rfl, show firstP 71 = 73 by rfl,
        show llb 71 = (181233/125000) by rfl, show lub 71 = (532837/125000) by rfl,
        show lub 73 = (171619/40000) by rfl, show clbZ 71 = 42626 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 72 = (972416614407737400870501653/557940830126698960967415390) by rfl, show lastP 72 = 71 by rfl, show firstP 72 = 73 by rfl,
        show llb 71 = (181233/125000) by rfl, show lub 71 = (532837/125000) by rfl,
        show lub 73 = (171619/40000) by rfl, show clbZ 71 = 42626 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 73 = (71544353681891529224514036059/40729680599249024150621323470) by rfl, show lastP 73 = 73 by rfl, show firstP 73 = 79 by rfl,
        show llb 73 = (364091/250000) by rfl, show lub 73 = (171619/40000) by rfl,
        show lub 79 = (546183/125000) by rfl, show clbZ 73 = 42904 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 74 = (71544353681891529224514036059/40729680599249024150621323470) by rfl, show lastP 74 = 73 by rfl, show firstP 74 = 79 by rfl,
        show llb 73 = (364091/250000) by rfl, show lub 73 = (171619/40000) by rfl,
        show lub 79 = (546183/125000) by rfl, show clbZ 73 = 42904 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 75 = (71544353681891529224514036059/40729680599249024150621323470) by rfl, show lastP 75 = 73 by rfl, show firstP 75 = 79 by rfl,
        show llb 73 = (364091/250000) by rfl, show lub 73 = (171619/40000) by rfl,
        show lub 79 = (546183/125000) by rfl, show clbZ 73 = 42904 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 76 = (71544353681891529224514036059/40729680599249024150621323470) by rfl, show lastP 76 = 73 by rfl, show firstP 76 = 79 by rfl,
        show llb 73 = (364091/250000) by rfl, show lub 73 = (171619/40000) by rfl,
        show lub 79 = (546183/125000) by rfl, show clbZ 73 = 42904 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 77 = (71544353681891529224514036059/40729680599249024150621323470) by rfl, show lastP 77 = 73 by rfl, show firstP 77 = 79 by rfl,
        show llb 73 = (364091/250000) by rfl, show lub 73 = (171619/40000) by rfl,
        show lub 79 = (546183/125000) by rfl, show clbZ 73 = 42904 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 78 = (71544353681891529224514036059/40729680599249024150621323470) by rfl, show lastP 78 = 73 by rfl, show firstP 78 = 79 by rfl,
        show llb 73 = (364091/250000) by rfl, show lub 73 = (171619/40000) by rfl,
        show lub 79 = (546183/125000) by rfl, show clbZ 73 = 42904 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 79 = (5692733621468679832887230172131/3217644767340672907899084554130) by rfl, show lastP 79 = 79 by rfl, show firstP 79 = 83 by rfl,
        show llb 79 = (147461/100000) by rfl, show lub 79 = (546183/125000) by rfl,
        show lub 83 = (552357/125000) by rfl, show clbZ 79 = 43694 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 80 = (5692733621468679832887230172131/3217644767340672907899084554130) by rfl, show lastP 80 = 79 by rfl, show firstP 80 = 83 by rfl,
        show llb 79 = (147461/100000) by rfl, show lub 79 = (546183/125000) by rfl,
        show lub 83 = (552357/125000) by rfl, show clbZ 79 = 43694 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 81 = (5692733621468679832887230172131/3217644767340672907899084554130) by rfl, show lastP 81 = 79 by rfl, show firstP 81 = 83 by rfl,
        show llb 79 = (147461/100000) by rfl, show lub 79 = (546183/125000) by rfl,
        show lub 83 = (552357/125000) by rfl, show clbZ 79 = 43694 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 82 = (5692733621468679832887230172131/3217644767340672907899084554130) by rfl, show lastP 82 = 79 by rfl, show firstP 82 = 83 by rfl,
        show llb 79 = (147461/100000) by rfl, show lub 79 = (546183/125000) by rfl,
        show lub 83 = (552357/125000) by rfl, show clbZ 79 = 43694 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 83 = (475714535349241099037539188841003/267064515689275851355624017992790) by rfl, show lastP 83 = 83 by rfl, show firstP 83 = 89 by rfl,
        show llb 83 = (371463/250000) by rfl, show lub 83 = (552357/125000) by rfl,
        show lub 89 = (1122163/250000) by rfl, show clbZ 83 = 44188 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 84 = (475714535349241099037539188841003/267064515689275851355624017992790) by rfl, show lastP 84 = 83 by rfl, show firstP 84 = 89 by rfl,
        show llb 83 = (371463/250000) by rfl, show lub 83 = (552357/125000) by rfl,
        show lub 89 = (1122163/250000) by rfl, show clbZ 83 = 44188 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 85 = (475714535349241099037539188841003/267064515689275851355624017992790) by rfl, show lastP 85 = 83 by rfl, show firstP 85 = 89 by rfl,
        show llb 83 = (371463/250000) by rfl, show lub 83 = (552357/125000) by rfl,
        show lub 89 = (1122163/250000) by rfl, show clbZ 83 = 44188 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 86 = (475714535349241099037539188841003/267064515689275851355624017992790) by rfl, show lastP 86 = 83 by rfl, show firstP 86 = 89 by rfl,
        show llb 83 = (371463/250000) by rfl, show lub 83 = (552357/125000) by rfl,
        show lub 89 = (1122163/250000) by rfl, show clbZ 83 = 44188 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 87 = (475714535349241099037539188841003/267064515689275851355624017992790) by rfl, show lastP 87 = 83 by rfl, show firstP 87 = 89 by rfl,
        show llb 83 = (371463/250000) by rfl, show lub 83 = (552357/125000) by rfl,
        show lub 89 = (1122163/250000) by rfl, show clbZ 83 = 44188 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 88 = (475714535349241099037539188841003/267064515689275851355624017992790) by rfl, show lastP 88 = 83 by rfl, show firstP 88 = 89 by rfl,
        show llb 83 = (371463/250000) by rfl, show lub 83 = (552357/125000) by rfl,
        show lub 89 = (1122163/250000) by rfl, show clbZ 83 = 44188 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 89 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 89 = 89 by rfl, show firstP 89 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 90 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 90 = 89 by rfl, show firstP 90 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 91 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 91 = 89 by rfl, show firstP 91 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 92 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 92 = 89 by rfl, show firstP 92 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 93 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 93 = 89 by rfl, show firstP 93 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 94 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 94 = 89 by rfl, show firstP 94 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 95 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 95 = 89 by rfl, show firstP 95 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 96 = (42605658161771733665696611824842057/23768741896345550770650537601358310) by rfl, show lastP 96 = 89 by rfl, show firstP 96 = 97 by rfl,
        show llb 89 = (60061/40000) by rfl, show lub 89 = (1122163/250000) by rfl,
        show lub 97 = (4574727/1000000) by rfl, show clbZ 89 = 44886 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 97 = (4156517583588203716343221884611037839/2305567963945518424753102147331756070) by rfl, show lastP 97 = 97 by rfl, show firstP 97 = 101 by rfl,
        show llb 97 = (60821/40000) by rfl, show lub 97 = (4574727/1000000) by rfl,
        show lub 101 = (144223/31250) by rfl, show clbZ 97 = 45747 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 98 = (4156517583588203716343221884611037839/2305567963945518424753102147331756070) by rfl, show lastP 98 = 97 by rfl, show firstP 98 = 101 by rfl,
        show llb 97 = (60821/40000) by rfl, show lub 97 = (4574727/1000000) by rfl,
        show lub 101 = (144223/31250) by rfl, show clbZ 97 = 45747 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 99 = (4156517583588203716343221884611037839/2305567963945518424753102147331756070) by rfl, show lastP 99 = 97 by rfl, show firstP 99 = 101 by rfl,
        show llb 97 = (60821/40000) by rfl, show lub 97 = (4574727/1000000) by rfl,
        show lub 101 = (144223/31250) by rfl, show clbZ 97 = 45747 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 100 = (4156517583588203716343221884611037839/2305567963945518424753102147331756070) by rfl, show lastP 100 = 97 by rfl, show firstP 100 = 101 by rfl,
        show llb 97 = (60821/40000) by rfl, show lub 97 = (4574727/1000000) by rfl,
        show lub 101 = (144223/31250) by rfl, show clbZ 97 = 45747 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 101 = (422113843906354093775418512493046577809/232862364358497360900063316880507363070) by rfl, show lastP 101 = 101 by rfl, show firstP 101 = 103 by rfl,
        show llb 101 = (764659/500000) by rfl, show lub 101 = (144223/31250) by rfl,
        show lub 103 = (926949/200000) by rfl, show clbZ 101 = 46151 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 102 = (422113843906354093775418512493046577809/232862364358497360900063316880507363070) by rfl, show lastP 102 = 101 by rfl, show firstP 102 = 103 by rfl,
        show llb 101 = (764659/500000) by rfl, show lub 101 = (144223/31250) by rfl,
        show lub 103 = (926949/200000) by rfl, show clbZ 101 = 46151 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 103 = (43710588286712969019768170103664304877397/23984823528925228172706521638692258396210) by rfl, show lastP 103 = 103 by rfl, show firstP 103 = 107 by rfl,
        show llb 103 = (383389/250000) by rfl, show lub 103 = (926949/200000) by rfl,
        show lub 107 = (934569/200000) by rfl, show clbZ 103 = 46347 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 104 = (43710588286712969019768170103664304877397/23984823528925228172706521638692258396210) by rfl, show lastP 104 = 103 by rfl, show firstP 104 = 107 by rfl,
        show llb 103 = (383389/250000) by rfl, show lub 103 = (926949/200000) by rfl,
        show lub 107 = (934569/200000) by rfl, show clbZ 103 = 46347 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 105 = (43710588286712969019768170103664304877397/23984823528925228172706521638692258396210) by rfl, show lastP 105 = 103 by rfl, show firstP 105 = 107 by rfl,
        show llb 103 = (383389/250000) by rfl, show lub 103 = (926949/200000) by rfl,
        show lub 107 = (934569/200000) by rfl, show clbZ 103 = 46347 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 106 = (43710588286712969019768170103664304877397/23984823528925228172706521638692258396210) by rfl, show lastP 106 = 103 by rfl, show firstP 106 = 107 by rfl,
        show llb 103 = (383389/250000) by rfl, show lub 103 = (926949/200000) by rfl,
        show lub 107 = (934569/200000) by rfl, show clbZ 103 = 46347 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 107 = (4701017770207212913287900722730772880277689/2566376117594999414479597815340071648394470) by rfl, show lastP 107 = 107 by rfl, show firstP 107 = 109 by rfl,
        show llb 107 = (1541743/1000000) by rfl, show lub 107 = (934569/200000) by rfl,
        show lub 109 = (1172841/250000) by rfl, show clbZ 107 = 46728 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 108 = (4701017770207212913287900722730772880277689/2566376117594999414479597815340071648394470) by rfl, show lastP 108 = 107 by rfl, show firstP 108 = 109 by rfl,
        show llb 107 = (1541743/1000000) by rfl, show lub 107 = (934569/200000) by rfl,
        show lub 109 = (1172841/250000) by rfl, show clbZ 107 = 46728 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 109 = (514977313070181206962860776592994315598662571/279734996817854936178276161872067809674997230) by rfl, show lastP 109 = 109 by rfl, show firstP 109 = 113 by rfl,
        show llb 109 = (772847/500000) by rfl, show lub 109 = (1172841/250000) by rfl,
        show lub 113 = (1181851/250000) by rfl, show clbZ 109 = 46913 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 110 = (514977313070181206962860776592994315598662571/279734996817854936178276161872067809674997230) by rfl, show lastP 110 = 109 by rfl, show firstP 110 = 113 by rfl,
        show llb 109 = (772847/500000) by rfl, show lub 109 = (1172841/250000) by rfl,
        show lub 113 = (1181851/250000) by rfl, show clbZ 109 = 46913 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 111 = (514977313070181206962860776592994315598662571/279734996817854936178276161872067809674997230) by rfl, show lastP 111 = 109 by rfl, show firstP 111 = 113 by rfl,
        show llb 109 = (772847/500000) by rfl, show lub 109 = (1172841/250000) by rfl,
        show lub 113 = (1181851/250000) by rfl, show clbZ 109 = 46913 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 112 = (514977313070181206962860776592994315598662571/279734996817854936178276161872067809674997230) by rfl, show lastP 112 = 109 by rfl, show firstP 112 = 113 by rfl,
        show llb 109 = (772847/500000) by rfl, show lub 109 = (1172841/250000) by rfl,
        show lub 113 = (1181851/250000) by rfl, show clbZ 109 = 46913 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 113 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 113 = 113 by rfl, show firstP 113 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 114 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 114 = 113 by rfl, show firstP 114 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 115 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 115 = 113 by rfl, show firstP 115 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 116 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 116 = 113 by rfl, show firstP 116 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 117 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 117 = 113 by rfl, show firstP 117 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 118 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 118 = 113 by rfl, show firstP 118 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 119 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 119 = 113 by rfl, show firstP 119 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 120 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 120 = 113 by rfl, show firstP 120 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 121 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 121 = 113 by rfl, show firstP 121 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 122 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 122 = 113 by rfl, show firstP 122 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 123 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 123 = 113 by rfl, show firstP 123 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 124 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 124 = 113 by rfl, show firstP 124 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 125 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 125 = 113 by rfl, show firstP 125 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 126 = (58472171373748331322981543916880425472323867753/31610054640417607788145206291543662493274686990) by rfl, show lastP 126 = 113 by rfl, show firstP 126 = 127 by rfl,
        show llb 113 = (776669/500000) by rfl, show lub 113 = (1181851/250000) by rfl,
        show lub 127 = (4844203/1000000) by rfl, show clbZ 113 = 47273 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 127 = (7457575819106455685806801283735357697478405891621/4014476939333036189094441199026045136645885247730) by rfl, show lastP 127 = 127 by rfl, show firstP 127 = 131 by rfl,
        show llb 127 = (788873/500000) by rfl, show lub 127 = (4844203/1000000) by rfl,
        show lub 131 = (4875213/1000000) by rfl, show clbZ 127 = 48441 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 128 = (7457575819106455685806801283735357697478405891621/4014476939333036189094441199026045136645885247730) by rfl, show lastP 128 = 127 by rfl, show firstP 128 = 131 by rfl,
        show llb 127 = (788873/500000) by rfl, show lub 127 = (4844203/1000000) by rfl,
        show lub 131 = (4875213/1000000) by rfl, show clbZ 127 = 48441 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 129 = (7457575819106455685806801283735357697478405891621/4014476939333036189094441199026045136645885247730) by rfl, show lastP 129 = 127 by rfl, show firstP 129 = 131 by rfl,
        show llb 127 = (788873/500000) by rfl, show lub 127 = (4844203/1000000) by rfl,
        show lub 131 = (4875213/1000000) by rfl, show clbZ 127 = 48441 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 130 = (7457575819106455685806801283735357697478405891621/4014476939333036189094441199026045136645885247730) by rfl, show lastP 130 = 127 by rfl, show firstP 130 = 131 by rfl,
        show llb 127 = (788873/500000) by rfl, show lub 127 = (4844203/1000000) by rfl,
        show lub 131 = (4875213/1000000) by rfl, show clbZ 127 = 48441 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 131 = (980956909242278731029785409368357903506317057050081/525896479052627740771371797072411912900610967452630) by rfl, show lastP 131 = 131 by rfl, show firstP 131 = 137 by rfl,
        show llb 131 = (12673/8000) by rfl, show lub 131 = (4875213/1000000) by rfl,
        show lub 137 = (4919997/1000000) by rfl, show clbZ 131 = 48751 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 132 = (980956909242278731029785409368357903506317057050081/525896479052627740771371797072411912900610967452630) by rfl, show lastP 132 = 131 by rfl, show firstP 132 = 137 by rfl,
        show llb 131 = (12673/8000) by rfl, show lub 131 = (4875213/1000000) by rfl,
        show lub 137 = (4919997/1000000) by rfl, show clbZ 131 = 48751 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 133 = (980956909242278731029785409368357903506317057050081/525896479052627740771371797072411912900610967452630) by rfl, show lastP 133 = 131 by rfl, show firstP 133 = 137 by rfl,
        show llb 131 = (12673/8000) by rfl, show lub 131 = (4875213/1000000) by rfl,
        show lub 137 = (4919997/1000000) by rfl, show clbZ 131 = 48751 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 134 = (980956909242278731029785409368357903506317057050081/525896479052627740771371797072411912900610967452630) by rfl, show lastP 134 = 131 by rfl, show firstP 134 = 137 by rfl,
        show llb 131 = (12673/8000) by rfl, show lub 131 = (4875213/1000000) by rfl,
        show lub 137 = (4919997/1000000) by rfl, show clbZ 131 = 48751 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 135 = (980956909242278731029785409368357903506317057050081/525896479052627740771371797072411912900610967452630) by rfl, show lastP 135 = 131 by rfl, show firstP 135 = 137 by rfl,
        show llb 131 = (12673/8000) by rfl, show lub 131 = (4875213/1000000) by rfl,
        show lub 137 = (4919997/1000000) by rfl, show clbZ 131 = 48751 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 136 = (980956909242278731029785409368357903506317057050081/525896479052627740771371797072411912900610967452630) by rfl, show lastP 136 = 131 by rfl, show firstP 136 = 137 by rfl,
        show llb 131 = (12673/8000) by rfl, show lub 131 = (4875213/1000000) by rfl,
        show lub 137 = (4919997/1000000) by rfl, show clbZ 131 = 48751 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 137 = (134916993045244813891851972880537444693266047783313727/72047817630210000485677936198920432067383702541010310) by rfl, show lastP 137 = 137 by rfl, show firstP 137 = 139 by rfl,
        show llb 137 = (199159/125000) by rfl, show lub 137 = (4919997/1000000) by rfl,
        show lub 139 = (493449/100000) by rfl, show clbZ 137 = 49199 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 138 = (134916993045244813891851972880537444693266047783313727/72047817630210000485677936198920432067383702541010310) by rfl, show lastP 138 = 137 by rfl, show firstP 138 = 139 by rfl,
        show llb 137 = (199159/125000) by rfl, show lub 137 = (4919997/1000000) by rfl,
        show lub 139 = (493449/100000) by rfl, show clbZ 137 = 49199 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 139 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 139 = 139 by rfl, show firstP 139 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 140 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 140 = 139 by rfl, show firstP 140 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 141 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 141 = 139 by rfl, show firstP 141 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 142 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 142 = 139 by rfl, show firstP 142 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 143 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 143 = 139 by rfl, show firstP 143 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 144 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 144 = 139 by rfl, show firstP 144 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 145 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 145 = 139 by rfl, show firstP 145 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 146 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 146 = 139 by rfl, show firstP 146 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 147 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 147 = 139 by rfl, show firstP 147 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 148 = (18825509850919239131453102166593625244431364344421618363/10014646650599190067509233131649940057366334653200433090) by rfl, show lastP 148 = 139 by rfl, show firstP 148 = 149 by rfl,
        show llb 139 = (319243/200000) by rfl, show lub 139 = (493449/100000) by rfl,
        show lub 149 = (2501981/500000) by rfl, show clbZ 139 = 49344 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 149 = (2815015614437565820654021455954100101477639621972021569177/1492182350939279320058875736615841068547583863326864530410) by rfl, show lastP 149 = 149 by rfl, show firstP 149 = 151 by rfl,
        show llb 149 = (805101/500000) by rfl, show lub 149 = (2501981/500000) by rfl,
        show lub 151 = (313581/62500) by rfl, show clbZ 149 = 50039 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 150 = (2815015614437565820654021455954100101477639621972021569177/1492182350939279320058875736615841068547583863326864530410) by rfl, show lastP 150 = 149 by rfl, show firstP 150 = 151 by rfl,
        show llb 149 = (805101/500000) by rfl, show lub 149 = (2501981/500000) by rfl,
        show lub 151 = (313581/62500) by rfl, show clbZ 149 = 50039 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 151 = (426559540131011718238816115585684956391671166781102121476137/225319534991831177328890236228992001350685163362356544091910) by rfl, show lastP 151 = 151 by rfl, show firstP 151 = 157 by rfl,
        show llb 151 = (201607/125000) by rfl, show lub 151 = (313581/62500) by rfl,
        show lub 157 = (2528131/500000) by rfl, show clbZ 151 = 50172 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 152 = (426559540131011718238816115585684956391671166781102121476137/225319534991831177328890236228992001350685163362356544091910) by rfl, show lastP 152 = 151 by rfl, show firstP 152 = 157 by rfl,
        show llb 151 = (201607/125000) by rfl, show lub 151 = (313581/62500) by rfl,
        show lub 157 = (2528131/500000) by rfl, show clbZ 151 = 50172 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 153 = (426559540131011718238816115585684956391671166781102121476137/225319534991831177328890236228992001350685163362356544091910) by rfl, show lastP 153 = 151 by rfl, show firstP 153 = 157 by rfl,
        show llb 151 = (201607/125000) by rfl, show lub 151 = (313581/62500) by rfl,
        show lub 157 = (2528131/500000) by rfl, show clbZ 151 = 50172 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 154 = (426559540131011718238816115585684956391671166781102121476137/225319534991831177328890236228992001350685163362356544091910) by rfl, show lastP 154 = 151 by rfl, show firstP 154 = 157 by rfl,
        show llb 151 = (201607/125000) by rfl, show lub 151 = (313581/62500) by rfl,
        show lub 157 = (2528131/500000) by rfl, show clbZ 151 = 50172 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 155 = (426559540131011718238816115585684956391671166781102121476137/225319534991831177328890236228992001350685163362356544091910) by rfl, show lastP 155 = 151 by rfl, show firstP 155 = 157 by rfl,
        show llb 151 = (201607/125000) by rfl, show lub 151 = (313581/62500) by rfl,
        show lub 157 = (2528131/500000) by rfl, show clbZ 151 = 50172 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 156 = (426559540131011718238816115585684956391671166781102121476137/225319534991831177328890236228992001350685163362356544091910) by rfl, show lastP 156 = 151 by rfl, show firstP 156 = 157 by rfl,
        show llb 151 = (201607/125000) by rfl, show lub 151 = (313581/62500) by rfl,
        show lub 157 = (2528131/500000) by rfl, show clbZ 151 = 50172 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 157 = (67195167335560670940823020383181530154843058347995389615845419/35375166993717494840635767087951744212057570647889977422429870) by rfl, show lastP 157 = 157 by rfl, show firstP 157 = 163 by rfl,
        show llb 157 = (1620599/1000000) by rfl, show lub 157 = (2528131/500000) by rfl,
        show lub 163 = (2546883/500000) by rfl, show clbZ 157 = 50562 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 158 = (67195167335560670940823020383181530154843058347995389615845419/35375166993717494840635767087951744212057570647889977422429870) by rfl, show lastP 158 = 157 by rfl, show firstP 158 = 163 by rfl,
        show llb 157 = (1620599/1000000) by rfl, show lub 157 = (2528131/500000) by rfl,
        show lub 163 = (2546883/500000) by rfl, show clbZ 157 = 50562 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 159 = (67195167335560670940823020383181530154843058347995389615845419/35375166993717494840635767087951744212057570647889977422429870) by rfl, show lastP 159 = 157 by rfl, show firstP 159 = 163 by rfl,
        show llb 157 = (1620599/1000000) by rfl, show lub 157 = (2528131/500000) by rfl,
        show lub 163 = (2546883/500000) by rfl, show clbZ 157 = 50562 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 160 = (67195167335560670940823020383181530154843058347995389615845419/35375166993717494840635767087951744212057570647889977422429870) by rfl, show lastP 160 = 157 by rfl, show firstP 160 = 163 by rfl,
        show llb 157 = (1620599/1000000) by rfl, show lub 157 = (2528131/500000) by rfl,
        show lub 163 = (2546883/500000) by rfl, show clbZ 157 = 50562 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 161 = (67195167335560670940823020383181530154843058347995389615845419/35375166993717494840635767087951744212057570647889977422429870) by rfl, show lastP 161 = 157 by rfl, show firstP 161 = 163 by rfl,
        show llb 157 = (1620599/1000000) by rfl, show lub 157 = (2528131/500000) by rfl,
        show lub 163 = (2546883/500000) by rfl, show clbZ 157 = 50562 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 162 = (67195167335560670940823020383181530154843058347995389615845419/35375166993717494840635767087951744212057570647889977422429870) by rfl, show lastP 162 = 157 by rfl, show firstP 162 = 163 by rfl,
        show llb 157 = (1620599/1000000) by rfl, show lub 157 = (2528131/500000) by rfl,
        show lub 163 = (2546883/500000) by rfl, show clbZ 157 = 50562 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 163 = (10988187442690106858194788089546541159451476081371138484805233167/5766152219975951659023630035336134306565384015606066319856068810) by rfl, show lastP 163 = 163 by rfl, show firstP 163 = 167 by rfl,
        show llb 163 = (1627989/1000000) by rfl, show lub 163 = (2546883/500000) by rfl,
        show lub 167 = (511801/100000) by rfl, show clbZ 163 = 50937 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 164 = (10988187442690106858194788089546541159451476081371138484805233167/5766152219975951659023630035336134306565384015606066319856068810) by rfl, show lastP 164 = 163 by rfl, show firstP 164 = 167 by rfl,
        show llb 163 = (1627989/1000000) by rfl, show lub 163 = (2546883/500000) by rfl,
        show lub 167 = (511801/100000) by rfl, show clbZ 163 = 50937 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 165 = (10988187442690106858194788089546541159451476081371138484805233167/5766152219975951659023630035336134306565384015606066319856068810) by rfl, show lastP 165 = 163 by rfl, show firstP 165 = 167 by rfl,
        show llb 163 = (1627989/1000000) by rfl, show lub 163 = (2546883/500000) by rfl,
        show lub 167 = (511801/100000) by rfl, show clbZ 163 = 50937 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 166 = (10988187442690106858194788089546541159451476081371138484805233167/5766152219975951659023630035336134306565384015606066319856068810) by rfl, show lastP 166 = 163 by rfl, show firstP 166 = 167 by rfl,
        show llb 163 = (1627989/1000000) by rfl, show lub 163 = (2546883/500000) by rfl,
        show lub 167 = (511801/100000) by rfl, show clbZ 163 = 50937 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 167 = (1840793455149223796977553240989608507934961889604586193282330007699/962947420735983927056946215901134429196419130606213075415963491270) by rfl, show lastP 167 = 167 by rfl, show firstP 167 = 173 by rfl,
        show llb 167 = (204091/125000) by rfl, show lub 167 = (511801/100000) by rfl,
        show lub 173 = (5153307/1000000) by rfl, show clbZ 167 = 51179 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 168 = (1840793455149223796977553240989608507934961889604586193282330007699/962947420735983927056946215901134429196419130606213075415963491270) by rfl, show lastP 168 = 167 by rfl, show firstP 168 = 173 by rfl,
        show llb 167 = (204091/125000) by rfl, show lub 167 = (511801/100000) by rfl,
        show lub 173 = (5153307/1000000) by rfl, show clbZ 167 = 51179 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 169 = (1840793455149223796977553240989608507934961889604586193282330007699/962947420735983927056946215901134429196419130606213075415963491270) by rfl, show lastP 169 = 167 by rfl, show firstP 169 = 173 by rfl,
        show llb 167 = (204091/125000) by rfl, show lub 167 = (511801/100000) by rfl,
        show lub 173 = (5153307/1000000) by rfl, show clbZ 167 = 51179 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 170 = (1840793455149223796977553240989608507934961889604586193282330007699/962947420735983927056946215901134429196419130606213075415963491270) by rfl, show lastP 170 = 167 by rfl, show firstP 170 = 173 by rfl,
        show llb 167 = (204091/125000) by rfl, show lub 167 = (511801/100000) by rfl,
        show lub 173 = (5153307/1000000) by rfl, show clbZ 167 = 51179 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 171 = (1840793455149223796977553240989608507934961889604586193282330007699/962947420735983927056946215901134429196419130606213075415963491270) by rfl, show lastP 171 = 167 by rfl, show firstP 171 = 173 by rfl,
        show llb 167 = (204091/125000) by rfl, show lub 167 = (511801/100000) by rfl,
        show lub 173 = (5153307/1000000) by rfl, show clbZ 167 = 51179 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 172 = (1840793455149223796977553240989608507934961889604586193282330007699/962947420735983927056946215901134429196419130606213075415963491270) by rfl, show lastP 172 = 167 by rfl, show firstP 172 = 173 by rfl,
        show llb 167 = (204091/125000) by rfl, show lub 167 = (511801/100000) by rfl,
        show lub 173 = (5153307/1000000) by rfl, show clbZ 167 = 51179 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 173 = (319420215161551700804173656907103406301944826032199624513259054823197/166589903787325219380851695350896256250980509594874862046961683989710) by rfl, show lastP 173 = 173 by rfl, show firstP 173 = 179 by rfl,
        show llb 173 = (819801/500000) by rfl, show lub 173 = (5153307/1000000) by rfl,
        show lub 179 = (2593701/500000) by rfl, show clbZ 173 = 51532 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 174 = (319420215161551700804173656907103406301944826032199624513259054823197/166589903787325219380851695350896256250980509594874862046961683989710) by rfl, show lastP 174 = 173 by rfl, show firstP 174 = 179 by rfl,
        show llb 173 = (819801/500000) by rfl, show lub 173 = (5153307/1000000) by rfl,
        show lub 179 = (2593701/500000) by rfl, show clbZ 173 = 51532 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 175 = (319420215161551700804173656907103406301944826032199624513259054823197/166589903787325219380851695350896256250980509594874862046961683989710) by rfl, show lastP 175 = 173 by rfl, show firstP 175 = 179 by rfl,
        show llb 173 = (819801/500000) by rfl, show lub 173 = (5153307/1000000) by rfl,
        show lub 179 = (2593701/500000) by rfl, show clbZ 173 = 51532 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 176 = (319420215161551700804173656907103406301944826032199624513259054823197/166589903787325219380851695350896256250980509594874862046961683989710) by rfl, show lastP 176 = 173 by rfl, show firstP 176 = 179 by rfl,
        show llb 173 = (819801/500000) by rfl, show lub 173 = (5153307/1000000) by rfl,
        show lub 179 = (2593701/500000) by rfl, show clbZ 173 = 51532 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 177 = (319420215161551700804173656907103406301944826032199624513259054823197/166589903787325219380851695350896256250980509594874862046961683989710) by rfl, show lastP 177 = 173 by rfl, show firstP 177 = 179 by rfl,
        show llb 173 = (819801/500000) by rfl, show lub 173 = (5153307/1000000) by rfl,
        show lub 179 = (2593701/500000) by rfl, show clbZ 173 = 51532 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 178 = (319420215161551700804173656907103406301944826032199624513259054823197/166589903787325219380851695350896256250980509594874862046961683989710) by rfl, show lastP 178 = 173 by rfl, show firstP 178 = 179 by rfl,
        show llb 173 = (819801/500000) by rfl, show lub 173 = (5153307/1000000) by rfl,
        show lub 179 = (2593701/500000) by rfl, show clbZ 173 = 51532 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 179 = (57342808417705079663327936281722405984299104369358607649920332497341973/29819592777931214269172453467810429868925511217482600306406141434158090) by rfl, show lastP 179 = 179 by rfl, show firstP 179 = 181 by rfl,
        show llb 179 = (823099/500000) by rfl, show lub 179 = (2593701/500000) by rfl,
        show lub 181 = (5198513/1000000) by rfl, show clbZ 179 = 51873 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 180 = (57342808417705079663327936281722405984299104369358607649920332497341973/29819592777931214269172453467810429868925511217482600306406141434158090) by rfl, show lastP 180 = 179 by rfl, show firstP 180 = 181 by rfl,
        show llb 179 = (823099/500000) by rfl, show lub 179 = (2593701/500000) by rfl,
        show lub 181 = (5198513/1000000) by rfl, show clbZ 179 = 51873 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 181 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 181 = 181 by rfl, show firstP 181 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 182 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 182 = 181 by rfl, show firstP 182 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 183 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 183 = 181 by rfl, show firstP 183 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 184 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 184 = 181 by rfl, show firstP 184 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 185 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 185 = 181 by rfl, show firstP 185 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 186 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 186 = 181 by rfl, show firstP 186 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 187 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 187 = 181 by rfl, show firstP 187 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 188 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 188 = 181 by rfl, show firstP 188 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 189 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 189 = 181 by rfl, show firstP 189 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 190 = (10408867916382550633331528920459565913027063402071390584941986323453055203/5397346292805549782720214077673687806275517530364350655459511599582614290) by rfl, show lastP 190 = 181 by rfl, show firstP 190 = 191 by rfl,
        show llb 181 = (329667/200000) by rfl, show lub 181 = (5198513/1000000) by rfl,
        show lub 191 = (5252289/1000000) by rfl, show clbZ 181 = 51984 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 191 = (1993491118321872720749042237885450777194444627325999952379378899379116158063/1030893141925860008499560888835674370998623848299590975192766715520279329390) by rfl, show lastP 191 = 191 by rfl, show firstP 191 = 193 by rfl,
        show llb 191 = (1658631/1000000) by rfl, show lub 191 = (5252289/1000000) by rfl,
        show lub 193 = (2631353/500000) by rfl, show clbZ 191 = 52522 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 192 = (1993491118321872720749042237885450777194444627325999952379378899379116158063/1030893141925860008499560888835674370998623848299590975192766715520279329390) by rfl, show lastP 192 = 191 by rfl, show firstP 192 = 193 by rfl,
        show llb 191 = (1658631/1000000) by rfl, show lub 191 = (5252289/1000000) by rfl,
        show lub 193 = (2631353/500000) by rfl, show clbZ 191 = 52522 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 193 = (385774678978047295113064712800727674369526436922217581784412894295689697835549/198962376391690981640415251545285153602734402721821058212203976095413910572270) by rfl, show lastP 193 = 193 by rfl, show firstP 193 = 197 by rfl,
        show llb 193 = (1660609/1000000) by rfl, show lub 193 = (2631353/500000) by rfl,
        show lub 197 = (5283219/1000000) by rfl, show clbZ 193 = 52626 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 194 = (385774678978047295113064712800727674369526436922217581784412894295689697835549/198962376391690981640415251545285153602734402721821058212203976095413910572270) by rfl, show lastP 194 = 193 by rfl, show firstP 194 = 197 by rfl,
        show llb 193 = (1660609/1000000) by rfl, show lub 193 = (2631353/500000) by rfl,
        show lub 197 = (5283219/1000000) by rfl, show clbZ 193 = 52626 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 195 = (385774678978047295113064712800727674369526436922217581784412894295689697835549/198962376391690981640415251545285153602734402721821058212203976095413910572270) by rfl, show lastP 195 = 193 by rfl, show firstP 195 = 197 by rfl,
        show llb 193 = (1660609/1000000) by rfl, show lub 193 = (2631353/500000) by rfl,
        show lub 197 = (5283219/1000000) by rfl, show clbZ 193 = 52626 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 196 = (385774678978047295113064712800727674369526436922217581784412894295689697835549/198962376391690981640415251545285153602734402721821058212203976095413910572270) by rfl, show lastP 196 = 193 by rfl, show firstP 196 = 197 by rfl,
        show llb 193 = (1660609/1000000) by rfl, show lub 193 = (2631353/500000) by rfl,
        show lub 197 = (5283219/1000000) by rfl, show clbZ 193 = 52626 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 197 = (76196574135067008118914163673288637004399442476398684669741544152346284384175423/39195588149163123383161804554421175259738677336198748467804183290796540382737190) by rfl, show lastP 197 = 197 by rfl, show firstP 197 = 199 by rfl,
        show llb 197 = (416129/250000) by rfl, show lub 197 = (5283219/1000000) by rfl,
        show lub 199 = (5293321/1000000) by rfl, show clbZ 197 = 52832 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 198 = (76196574135067008118914163673288637004399442476398684669741544152346284384175423/39195588149163123383161804554421175259738677336198748467804183290796540382737190) by rfl, show lastP 198 = 197 by rfl, show firstP 198 = 199 by rfl,
        show llb 197 = (416129/250000) by rfl, show lub 197 = (5283219/1000000) by rfl,
        show lub 199 = (5293321/1000000) by rfl, show clbZ 197 = 52832 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 199 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 199 = 199 by rfl, show firstP 199 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 200 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 200 = 199 by rfl, show firstP 200 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 201 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 201 = 199 by rfl, show firstP 201 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 202 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 202 = 199 by rfl, show firstP 202 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 203 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 203 = 199 by rfl, show firstP 203 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 204 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 204 = 199 by rfl, show firstP 204 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 205 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 205 = 199 by rfl, show firstP 205 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 206 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 206 = 199 by rfl, show firstP 206 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 207 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 207 = 199 by rfl, show firstP 207 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 208 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 208 = 199 by rfl, show firstP 208 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 209 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 209 = 199 by rfl, show firstP 209 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 210 = (15202313841027497739047080375538859939135227730139536997746371469607707132833646367/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) by rfl, show lastP 210 = 199 by rfl, show firstP 210 = 211 by rfl,
        show llb 199 = (833213/500000) by rfl, show lub 199 = (5293321/1000000) by rfl,
        show lub 211 = (2675937/500000) by rfl, show clbZ 199 = 52933 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 211 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 211 = 211 by rfl, show firstP 211 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 212 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 212 = 211 by rfl, show firstP 212 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 213 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 213 = 211 by rfl, show firstP 213 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 214 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 214 = 211 by rfl, show firstP 214 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 215 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 215 = 211 by rfl, show firstP 215 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 216 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 216 = 211 by rfl, show firstP 216 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 217 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 217 = 211 by rfl, show firstP 217 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 218 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 218 = 211 by rfl, show firstP 218 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 219 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 219 = 211 by rfl, show firstP 219 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 220 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 220 = 211 by rfl, show firstP 220 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 221 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 221 = 211 by rfl, show firstP 221 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 222 = (3215488142498485484492183158345029261034221047849345857469577412562094716564064084247/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) by rfl, show lastP 222 = 211 by rfl, show firstP 222 = 223 by rfl,
        show llb 211 = (1677417/1000000) by rfl, show lub 211 = (2675937/500000) by rfl,
        show lub 223 = (1351797/250000) by rfl, show clbZ 211 = 53518 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 223 = (718699639327957473429492425322377115938612460993073775465130392853544377727917042657991/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) by rfl, show lastP 223 = 223 by rfl, show firstP 223 = 227 by rfl,
        show llb 223 = (1687697/1000000) by rfl, show lub 223 = (1351797/250000) by rfl,
        show lub 227 = (2712483/500000) by rfl, show clbZ 223 = 54071 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 224 = (718699639327957473429492425322377115938612460993073775465130392853544377727917042657991/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) by rfl, show lastP 224 = 223 by rfl, show firstP 224 = 227 by rfl,
        show llb 223 = (1687697/1000000) by rfl, show lub 223 = (1351797/250000) by rfl,
        show lub 227 = (2712483/500000) by rfl, show clbZ 223 = 54071 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 225 = (718699639327957473429492425322377115938612460993073775465130392853544377727917042657991/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) by rfl, show lastP 225 = 223 by rfl, show firstP 225 = 227 by rfl,
        show llb 223 = (1687697/1000000) by rfl, show lub 223 = (1351797/250000) by rfl,
        show lub 227 = (2712483/500000) by rfl, show clbZ 223 = 54071 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 226 = (718699639327957473429492425322377115938612460993073775465130392853544377727917042657991/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) by rfl, show lastP 226 = 223 by rfl, show firstP 226 = 227 by rfl,
        show llb 223 = (1687697/1000000) by rfl, show lub 223 = (1351797/250000) by rfl,
        show lub 227 = (2712483/500000) by rfl, show clbZ 223 = 54071 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 227 = (163511827859273678384959815113729742050404828958383078813204061634794561817548326350576887/83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110) by rfl, show lastP 227 = 227 by rfl, show firstP 227 = 229 by rfl,
        show llb 227 = (211373/125000) by rfl, show lub 227 = (2712483/500000) by rfl,
        show lub 229 = (2716869/500000) by rfl, show clbZ 227 = 54249 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 228 = (163511827859273678384959815113729742050404828958383078813204061634794561817548326350576887/83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110) by rfl, show lastP 228 = 227 by rfl, show firstP 228 = 229 by rfl,
        show llb 227 = (211373/125000) by rfl, show lub 227 = (2712483/500000) by rfl,
        show lub 229 = (2716869/500000) by rfl, show clbZ 227 = 54249 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 229 = (37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) by rfl, show lastP 229 = 229 by rfl, show firstP 229 = 233 by rfl,
        show llb 229 = (338521/200000) by rfl, show lub 229 = (2716869/500000) by rfl,
        show lub 233 = (2725527/500000) by rfl, show clbZ 229 = 54337 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 230 = (37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) by rfl, show lastP 230 = 229 by rfl, show firstP 230 = 233 by rfl,
        show llb 229 = (338521/200000) by rfl, show lub 229 = (2716869/500000) by rfl,
        show lub 233 = (2725527/500000) by rfl, show clbZ 229 = 54337 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 231 = (37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) by rfl, show lastP 231 = 229 by rfl, show firstP 231 = 233 by rfl,
        show llb 229 = (338521/200000) by rfl, show lub 229 = (2716869/500000) by rfl,
        show lub 233 = (2725527/500000) by rfl, show clbZ 229 = 54337 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 232 = (37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) by rfl, show lastP 232 = 229 by rfl, show firstP 232 = 233 by rfl,
        show llb 229 = (338521/200000) by rfl, show lub 229 = (2716869/500000) by rfl,
        show lub 233 = (2725527/500000) by rfl, show clbZ 229 = 54337 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 233 = (8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) by rfl, show lastP 233 = 233 by rfl, show firstP 233 = 239 by rfl,
        show llb 233 = (1695783/1000000) by rfl, show lub 233 = (2725527/500000) by rfl,
        show lub 239 = (5476479/1000000) by rfl, show clbZ 233 = 54510 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 234 = (8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) by rfl, show lastP 234 = 233 by rfl, show firstP 234 = 239 by rfl,
        show llb 233 = (1695783/1000000) by rfl, show lub 233 = (2725527/500000) by rfl,
        show lub 239 = (5476479/1000000) by rfl, show clbZ 233 = 54510 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 235 = (8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) by rfl, show lastP 235 = 233 by rfl, show firstP 235 = 239 by rfl,
        show llb 233 = (1695783/1000000) by rfl, show lub 233 = (2725527/500000) by rfl,
        show lub 239 = (5476479/1000000) by rfl, show clbZ 233 = 54510 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 236 = (8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) by rfl, show lastP 236 = 233 by rfl, show firstP 236 = 239 by rfl,
        show llb 233 = (1695783/1000000) by rfl, show lub 233 = (2725527/500000) by rfl,
        show lub 239 = (5476479/1000000) by rfl, show clbZ 233 = 54510 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 237 = (8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) by rfl, show lastP 237 = 233 by rfl, show firstP 237 = 239 by rfl,
        show llb 233 = (1695783/1000000) by rfl, show lub 233 = (2725527/500000) by rfl,
        show lub 239 = (5476479/1000000) by rfl, show clbZ 233 = 54510 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 238 = (8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) by rfl, show lastP 238 = 233 by rfl, show firstP 238 = 239 by rfl,
        show llb 233 = (1695783/1000000) by rfl, show lub 233 = (2725527/500000) by rfl,
        show lub 239 = (5476479/1000000) by rfl, show clbZ 233 = 54510 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 239 = (2098799936456271323771652759516428422371386490386771476792994918184499649543226735989117756998751/1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530) by rfl, show lastP 239 = 239 by rfl, show firstP 239 = 241 by rfl,
        show llb 239 = (106277/62500) by rfl, show lub 239 = (5476479/1000000) by rfl,
        show lub 241 = (5484813/1000000) by rfl, show clbZ 239 = 54764 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 240 = (2098799936456271323771652759516428422371386490386771476792994918184499649543226735989117756998751/1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530) by rfl, show lastP 240 = 239 by rfl, show firstP 240 = 241 by rfl,
        show llb 239 = (106277/62500) by rfl, show lub 239 = (5476479/1000000) by rfl,
        show lub 241 = (5484813/1000000) by rfl, show clbZ 239 = 54764 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 241 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 241 = 241 by rfl, show firstP 241 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 242 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 242 = 241 by rfl, show firstP 242 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 243 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 243 = 241 by rfl, show firstP 243 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 244 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 244 = 241 by rfl, show firstP 244 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 245 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 245 = 241 by rfl, show firstP 245 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 246 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 246 = 241 by rfl, show firstP 246 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 247 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 247 = 241 by rfl, show firstP 247 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 248 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 248 = 241 by rfl, show firstP 248 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 249 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 249 = 241 by rfl, show firstP 249 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 250 = (506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) by rfl, show lastP 250 = 241 by rfl, show firstP 250 = 251 by rfl,
        show llb 241 = (1701947/1000000) by rfl, show lub 241 = (5484813/1000000) by rfl,
        show lub 251 = (5525469/1000000) by rfl, show clbZ 241 = 54847 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 251 = (127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) by rfl, show lastP 251 = 251 by rfl, show firstP 251 = 257 by rfl,
        show llb 251 = (85467/50000) by rfl, show lub 251 = (5525469/1000000) by rfl,
        show lub 257 = (1387273/250000) by rfl, show clbZ 251 = 55254 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 252 = (127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) by rfl, show lastP 252 = 251 by rfl, show firstP 252 = 257 by rfl,
        show llb 251 = (85467/50000) by rfl, show lub 251 = (5525469/1000000) by rfl,
        show lub 257 = (1387273/250000) by rfl, show clbZ 251 = 55254 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 253 = (127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) by rfl, show lastP 253 = 251 by rfl, show firstP 253 = 257 by rfl,
        show llb 251 = (85467/50000) by rfl, show lub 251 = (5525469/1000000) by rfl,
        show lub 257 = (1387273/250000) by rfl, show clbZ 251 = 55254 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 254 = (127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) by rfl, show lastP 254 = 251 by rfl, show firstP 254 = 257 by rfl,
        show llb 251 = (85467/50000) by rfl, show lub 251 = (5525469/1000000) by rfl,
        show lub 257 = (1387273/250000) by rfl, show clbZ 251 = 55254 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 255 = (127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) by rfl, show lastP 255 = 251 by rfl, show firstP 255 = 257 by rfl,
        show llb 251 = (85467/50000) by rfl, show lub 251 = (5525469/1000000) by rfl,
        show lub 257 = (1387273/250000) by rfl, show clbZ 251 = 55254 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 256 = (127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) by rfl, show lastP 256 = 251 by rfl, show firstP 256 = 257 by rfl,
        show llb 251 = (85467/50000) by rfl, show lub 251 = (5525469/1000000) by rfl,
        show lub 257 = (1387273/250000) by rfl, show clbZ 251 = 55254 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 257 = (32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) by rfl, show lastP 257 = 257 by rfl, show firstP 257 = 263 by rfl,
        show llb 257 = (856801/500000) by rfl, show lub 257 = (1387273/250000) by rfl,
        show lub 263 = (557217/100000) by rfl, show clbZ 257 = 55490 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 258 = (32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) by rfl, show lastP 258 = 257 by rfl, show firstP 258 = 263 by rfl,
        show llb 257 = (856801/500000) by rfl, show lub 257 = (1387273/250000) by rfl,
        show lub 263 = (557217/100000) by rfl, show clbZ 257 = 55490 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 259 = (32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) by rfl, show lastP 259 = 257 by rfl, show firstP 259 = 263 by rfl,
        show llb 257 = (856801/500000) by rfl, show lub 257 = (1387273/250000) by rfl,
        show lub 263 = (557217/100000) by rfl, show clbZ 257 = 55490 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 260 = (32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) by rfl, show lastP 260 = 257 by rfl, show firstP 260 = 263 by rfl,
        show llb 257 = (856801/500000) by rfl, show lub 257 = (1387273/250000) by rfl,
        show lub 263 = (557217/100000) by rfl, show clbZ 257 = 55490 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 261 = (32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) by rfl, show lastP 261 = 257 by rfl, show firstP 261 = 263 by rfl,
        show llb 257 = (856801/500000) by rfl, show lub 257 = (1387273/250000) by rfl,
        show lub 263 = (557217/100000) by rfl, show clbZ 257 = 55490 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 262 = (32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) by rfl, show lastP 262 = 257 by rfl, show firstP 262 = 263 by rfl,
        show llb 257 = (856801/500000) by rfl, show lub 257 = (1387273/250000) by rfl,
        show lub 263 = (557217/100000) by rfl, show clbZ 257 = 55490 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 263 = (8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) by rfl, show lastP 263 = 263 by rfl, show firstP 263 = 269 by rfl,
        show llb 263 = (429439/250000) by rfl, show lub 263 = (557217/100000) by rfl,
        show lub 269 = (5594727/1000000) by rfl, show clbZ 263 = 55721 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 264 = (8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) by rfl, show lastP 264 = 263 by rfl, show firstP 264 = 269 by rfl,
        show llb 263 = (429439/250000) by rfl, show lub 263 = (557217/100000) by rfl,
        show lub 269 = (5594727/1000000) by rfl, show clbZ 263 = 55721 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 265 = (8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) by rfl, show lastP 265 = 263 by rfl, show firstP 265 = 269 by rfl,
        show llb 263 = (429439/250000) by rfl, show lub 263 = (557217/100000) by rfl,
        show lub 269 = (5594727/1000000) by rfl, show clbZ 263 = 55721 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 266 = (8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) by rfl, show lastP 266 = 263 by rfl, show firstP 266 = 269 by rfl,
        show llb 263 = (429439/250000) by rfl, show lub 263 = (557217/100000) by rfl,
        show lub 269 = (5594727/1000000) by rfl, show clbZ 263 = 55721 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 267 = (8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) by rfl, show lastP 267 = 263 by rfl, show firstP 267 = 269 by rfl,
        show llb 263 = (429439/250000) by rfl, show lub 263 = (557217/100000) by rfl,
        show lub 269 = (5594727/1000000) by rfl, show clbZ 263 = 55721 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 268 = (8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) by rfl, show lastP 268 = 263 by rfl, show firstP 268 = 269 by rfl,
        show llb 263 = (429439/250000) by rfl, show lub 263 = (557217/100000) by rfl,
        show lub 269 = (5594727/1000000) by rfl, show clbZ 263 = 55721 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 269 = (2331194144670278837283204579381538477535705838283915254740719173058496204621946749769200968569514576046142809/1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170) by rfl, show lastP 269 = 269 by rfl, show firstP 269 = 271 by rfl,
        show llb 269 = (430451/250000) by rfl, show lub 269 = (5594727/1000000) by rfl,
        show lub 271 = (1120427/200000) by rfl, show clbZ 269 = 55947 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 270 = (2331194144670278837283204579381538477535705838283915254740719173058496204621946749769200968569514576046142809/1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170) by rfl, show lastP 270 = 269 by rfl, show firstP 270 = 271 by rfl,
        show llb 269 = (430451/250000) by rfl, show lub 269 = (5594727/1000000) by rfl,
        show lub 271 = (1120427/200000) by rfl, show clbZ 269 = 55947 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 271 = (632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) by rfl, show lastP 271 = 271 by rfl, show firstP 271 = 277 by rfl,
        show llb 271 = (861563/500000) by rfl, show lub 271 = (1120427/200000) by rfl,
        show lub 277 = (5624033/1000000) by rfl, show clbZ 271 = 56021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 272 = (632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) by rfl, show lastP 272 = 271 by rfl, show firstP 272 = 277 by rfl,
        show llb 271 = (861563/500000) by rfl, show lub 271 = (1120427/200000) by rfl,
        show lub 277 = (5624033/1000000) by rfl, show clbZ 271 = 56021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 273 = (632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) by rfl, show lastP 273 = 271 by rfl, show firstP 273 = 277 by rfl,
        show llb 271 = (861563/500000) by rfl, show lub 271 = (1120427/200000) by rfl,
        show lub 277 = (5624033/1000000) by rfl, show clbZ 271 = 56021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 274 = (632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) by rfl, show lastP 274 = 271 by rfl, show firstP 274 = 277 by rfl,
        show llb 271 = (861563/500000) by rfl, show lub 271 = (1120427/200000) by rfl,
        show lub 277 = (5624033/1000000) by rfl, show clbZ 271 = 56021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 275 = (632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) by rfl, show lastP 275 = 271 by rfl, show firstP 275 = 277 by rfl,
        show llb 271 = (861563/500000) by rfl, show lub 271 = (1120427/200000) by rfl,
        show lub 277 = (5624033/1000000) by rfl, show clbZ 271 = 56021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 276 = (632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) by rfl, show lastP 276 = 271 by rfl, show firstP 276 = 277 by rfl,
        show llb 271 = (861563/500000) by rfl, show lub 271 = (1120427/200000) by rfl,
        show lub 277 = (5624033/1000000) by rfl, show clbZ 271 = 56021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 277 = (175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) by rfl, show lastP 277 = 277 by rfl, show firstP 277 = 281 by rfl,
        show llb 277 = (1727027/1000000) by rfl, show lub 277 = (5624033/1000000) by rfl,
        show lub 281 = (563837/100000) by rfl, show clbZ 277 = 56240 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 278 = (175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) by rfl, show lastP 278 = 277 by rfl, show firstP 278 = 281 by rfl,
        show llb 277 = (1727027/1000000) by rfl, show lub 277 = (5624033/1000000) by rfl,
        show lub 281 = (563837/100000) by rfl, show clbZ 277 = 56240 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 279 = (175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) by rfl, show lastP 279 = 277 by rfl, show firstP 279 = 281 by rfl,
        show llb 277 = (1727027/1000000) by rfl, show lub 277 = (5624033/1000000) by rfl,
        show lub 281 = (563837/100000) by rfl, show clbZ 277 = 56240 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 280 = (175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) by rfl, show lastP 280 = 277 by rfl, show firstP 280 = 281 by rfl,
        show llb 277 = (1727027/1000000) by rfl, show lub 277 = (5624033/1000000) by rfl,
        show lub 281 = (563837/100000) by rfl, show clbZ 277 = 56240 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 281 = (49441454257114018087468904381200200306187114716596773051146578349540075761623088834753270866109105006229897931204393/24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590) by rfl, show lastP 281 = 281 by rfl, show firstP 281 = 283 by rfl,
        show llb 281 = (1729567/1000000) by rfl, show lub 281 = (563837/100000) by rfl,
        show lub 283 = (5645463/1000000) by rfl, show clbZ 281 = 56383 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 282 = (49441454257114018087468904381200200306187114716596773051146578349540075761623088834753270866109105006229897931204393/24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590) by rfl, show lastP 282 = 281 by rfl, show firstP 282 = 283 by rfl,
        show llb 281 = (1729567/1000000) by rfl, show lub 281 = (563837/100000) by rfl,
        show lub 283 = (5645463/1000000) by rfl, show clbZ 281 = 56383 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 283 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 283 = 283 by rfl, show firstP 283 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 284 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 284 = 283 by rfl, show firstP 284 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 285 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 285 = 283 by rfl, show firstP 285 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 286 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 286 = 283 by rfl, show firstP 286 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 287 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 287 = 283 by rfl, show firstP 287 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 288 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 288 = 283 by rfl, show firstP 288 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 289 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 289 = 283 by rfl, show firstP 289 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 290 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 290 = 283 by rfl, show firstP 290 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 291 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 291 = 283 by rfl, show firstP 291 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 292 = (14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) by rfl, show lastP 292 = 283 by rfl, show firstP 292 = 293 by rfl,
        show llb 283 = (69233/40000) by rfl, show lub 283 = (5645463/1000000) by rfl,
        show lub 293 = (1420047/250000) by rfl, show clbZ 283 = 56454 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 293 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 293 = 293 by rfl, show firstP 293 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 294 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 294 = 293 by rfl, show firstP 294 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 295 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 295 = 293 by rfl, show firstP 295 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 296 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 296 = 293 by rfl, show firstP 296 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 297 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 297 = 293 by rfl, show firstP 297 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 298 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 298 = 293 by rfl, show firstP 298 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 299 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 299 = 293 by rfl, show firstP 299 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 300 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 300 = 293 by rfl, show firstP 300 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 301 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 301 = 293 by rfl, show firstP 301 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 302 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 302 = 293 by rfl, show firstP 302 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 303 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 303 = 293 by rfl, show firstP 303 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 304 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 304 = 293 by rfl, show firstP 304 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 305 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 305 = 293 by rfl, show firstP 305 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 306 = (4113833139682215962857995185458754473726261999740600533015012265871989587568219741355981669001717996164329457116644923007/2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210) by rfl, show lastP 306 = 293 by rfl, show firstP 306 = 307 by rfl,
        show llb 293 = (1736953/1000000) by rfl, show lub 293 = (1420047/250000) by rfl,
        show lub 307 = (357929/62500) by rfl, show clbZ 293 = 56801 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 307 = (1264990553640445455079661909966730427490191025109036916876478126983196093689001560933556526340443016176803464063647950790359/627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470) by rfl, show lastP 307 = 307 by rfl, show firstP 307 = 311 by rfl,
        show llb 307 = (1745141/1000000) by rfl, show lub 307 = (357929/62500) by rfl,
        show lub 311 = (5739809/1000000) by rfl, show clbZ 307 = 57268 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 308 = (1264990553640445455079661909966730427490191025109036916876478126983196093689001560933556526340443016176803464063647950790359/627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470) by rfl, show lastP 308 = 307 by rfl, show firstP 308 = 311 by rfl,
        show llb 307 = (1745141/1000000) by rfl, show lub 307 = (357929/62500) by rfl,
        show lub 311 = (5739809/1000000) by rfl, show clbZ 307 = 57268 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 309 = (1264990553640445455079661909966730427490191025109036916876478126983196093689001560933556526340443016176803464063647950790359/627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470) by rfl, show lastP 309 = 307 by rfl, show firstP 309 = 311 by rfl,
        show llb 307 = (1745141/1000000) by rfl, show lub 307 = (357929/62500) by rfl,
        show lub 311 = (5739809/1000000) by rfl, show clbZ 307 = 57268 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 310 = (1264990553640445455079661909966730427490191025109036916876478126983196093689001560933556526340443016176803464063647950790359/627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470) by rfl, show lastP 310 = 307 by rfl, show firstP 310 = 311 by rfl,
        show llb 307 = (1745141/1000000) by rfl, show lub 307 = (357929/62500) by rfl,
        show lub 311 = (5739809/1000000) by rfl, show clbZ 307 = 57268 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 311 = (394039502567886118955827872125137253794711586303832954993531591429446039261085822253878016956650864576772653787547766239955119/195133959955058134502488637025552252876537200920889365778484014616008832503770745901542489344429915739687480227261852231729170) by rfl, show lastP 311 = 311 by rfl, show firstP 311 = 313 by rfl,
        show llb 311 = (1747391/1000000) by rfl, show lub 311 = (5739809/1000000) by rfl,
        show lub 313 = (5746219/1000000) by rfl, show clbZ 311 = 57397 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 312 = (394039502567886118955827872125137253794711586303832954993531591429446039261085822253878016956650864576772653787547766239955119/195133959955058134502488637025552252876537200920889365778484014616008832503770745901542489344429915739687480227261852231729170) by rfl, show lastP 312 = 311 by rfl, show firstP 312 = 313 by rfl,
        show llb 311 = (1747391/1000000) by rfl, show lub 311 = (5739809/1000000) by rfl,
        show lub 313 = (5746219/1000000) by rfl, show clbZ 311 = 57397 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 313 = (123529498263703413367676612612193512690621263714020604278753872132032619121223633111365361796776150528269528115729712685337681417/61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210) by rfl, show lastP 313 = 313 by rfl, show firstP 313 = 317 by rfl,
        show llb 313 = (1748523/1000000) by rfl, show lub 313 = (5746219/1000000) by rfl,
        show lub 317 = (2879459/500000) by rfl, show clbZ 313 = 57462 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 314 = (123529498263703413367676612612193512690621263714020604278753872132032619121223633111365361796776150528269528115729712685337681417/61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210) by rfl, show lastP 314 = 313 by rfl, show firstP 314 = 317 by rfl,
        show llb 313 = (1748523/1000000) by rfl, show lub 313 = (5746219/1000000) by rfl,
        show lub 317 = (2879459/500000) by rfl, show clbZ 313 = 57462 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 315 = (123529498263703413367676612612193512690621263714020604278753872132032619121223633111365361796776150528269528115729712685337681417/61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210) by rfl, show lastP 315 = 313 by rfl, show firstP 315 = 317 by rfl,
        show llb 313 = (1748523/1000000) by rfl, show lub 313 = (5746219/1000000) by rfl,
        show lub 317 = (2879459/500000) by rfl, show clbZ 313 = 57462 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 316 = (123529498263703413367676612612193512690621263714020604278753872132032619121223633111365361796776150528269528115729712685337681417/61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210) by rfl, show lastP 316 = 313 by rfl, show firstP 316 = 317 by rfl,
        show llb 313 = (1748523/1000000) by rfl, show lub 313 = (5746219/1000000) by rfl,
        show lub 317 = (2879459/500000) by rfl, show clbZ 313 = 57462 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 317 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 317 = 317 by rfl, show firstP 317 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 318 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 318 = 317 by rfl, show firstP 318 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 319 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 319 = 317 by rfl, show firstP 319 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 320 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 320 = 317 by rfl, show firstP 320 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 321 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 321 = 317 by rfl, show firstP 321 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 322 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 322 = 317 by rfl, show firstP 322 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 323 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 323 = 317 by rfl, show firstP 323 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 324 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 324 = 317 by rfl, show firstP 324 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 325 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 325 = 317 by rfl, show firstP 325 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 326 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 326 = 317 by rfl, show firstP 326 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 327 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 327 = 317 by rfl, show firstP 327 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 328 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 328 = 317 by rfl, show firstP 328 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 329 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 329 = 317 by rfl, show firstP 329 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 330 = (39219927879059915233652765141454341378077296741232769927853642962429151026001571939770002488742846281087962593997451881000576239399/19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570) by rfl, show lastP 330 = 317 by rfl, show firstP 330 = 331 by rfl,
        show llb 317 = (1750731/1000000) by rfl, show lub 317 = (2879459/500000) by rfl,
        show lub 331 = (2901067/500000) by rfl, show clbZ 317 = 57589 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 331 = (13001157514609532765502536686875699316226248118960618409881462782978264001976376949242967771109125799709723150088785720851475135217639/6408618978071972467109041692977377947361419109761187605191204559105169094422546906281089567965658301640092918433248067534136392244670) by rfl, show lastP 331 = 331 by rfl, show firstP 331 = 337 by rfl,
        show llb 331 = (439551/250000) by rfl, show lub 331 = (2901067/500000) by rfl,
        show lub 337 = (5820099/1000000) by rfl, show clbZ 331 = 58021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 332 = (13001157514609532765502536686875699316226248118960618409881462782978264001976376949242967771109125799709723150088785720851475135217639/6408618978071972467109041692977377947361419109761187605191204559105169094422546906281089567965658301640092918433248067534136392244670) by rfl, show lastP 332 = 331 by rfl, show firstP 332 = 337 by rfl,
        show llb 331 = (439551/250000) by rfl, show lub 331 = (2901067/500000) by rfl,
        show lub 337 = (5820099/1000000) by rfl, show clbZ 331 = 58021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 333 = (13001157514609532765502536686875699316226248118960618409881462782978264001976376949242967771109125799709723150088785720851475135217639/6408618978071972467109041692977377947361419109761187605191204559105169094422546906281089567965658301640092918433248067534136392244670) by rfl, show lastP 333 = 331 by rfl, show firstP 333 = 337 by rfl,
        show llb 331 = (439551/250000) by rfl, show lub 331 = (2901067/500000) by rfl,
        show lub 337 = (5820099/1000000) by rfl, show clbZ 331 = 58021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 334 = (13001157514609532765502536686875699316226248118960618409881462782978264001976376949242967771109125799709723150088785720851475135217639/6408618978071972467109041692977377947361419109761187605191204559105169094422546906281089567965658301640092918433248067534136392244670) by rfl, show lastP 334 = 331 by rfl, show firstP 334 = 337 by rfl,
        show llb 331 = (439551/250000) by rfl, show lub 331 = (2901067/500000) by rfl,
        show lub 337 = (5820099/1000000) by rfl, show clbZ 331 = 58021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 335 = (13001157514609532765502536686875699316226248118960618409881462782978264001976376949242967771109125799709723150088785720851475135217639/6408618978071972467109041692977377947361419109761187605191204559105169094422546906281089567965658301640092918433248067534136392244670) by rfl, show lastP 335 = 331 by rfl, show firstP 335 = 337 by rfl,
        show llb 331 = (439551/250000) by rfl, show lub 331 = (2901067/500000) by rfl,
        show lub 337 = (5820099/1000000) by rfl, show clbZ 331 = 58021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 336 = (13001157514609532765502536686875699316226248118960618409881462782978264001976376949242967771109125799709723150088785720851475135217639/6408618978071972467109041692977377947361419109761187605191204559105169094422546906281089567965658301640092918433248067534136392244670) by rfl, show lastP 336 = 331 by rfl, show firstP 336 = 337 by rfl,
        show llb 331 = (439551/250000) by rfl, show lub 331 = (2901067/500000) by rfl,
        show lub 337 = (5820099/1000000) by rfl, show clbZ 331 = 58021 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 337 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 337 = 337 by rfl, show firstP 337 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 338 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 338 = 337 by rfl, show firstP 338 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 339 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 339 = 337 by rfl, show firstP 339 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 340 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 340 = 337 by rfl, show firstP 340 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 341 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 341 = 337 by rfl, show firstP 341 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 342 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 342 = 337 by rfl, show firstP 342 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 343 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 343 = 337 by rfl, show firstP 343 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 344 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 344 = 337 by rfl, show firstP 344 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 345 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 345 = 337 by rfl, show firstP 345 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 346 = (4387798701401484514441463905170088047515607035199489591735244162422780137760461578801161228431741052803816794498354035994481256960589013/2159704595610254721415747050533376368260798239989520222949435936418441984820398307416727184404426847652711313512004598759003964186453790) by rfl, show lastP 346 = 337 by rfl, show firstP 346 = 347 by rfl,
        show llb 337 = (440321/250000) by rfl, show lub 337 = (5820099/1000000) by rfl,
        show lub 347 = (5849341/1000000) by rfl, show clbZ 337 = 58200 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 347 = (1524725853981925381232603722144553928856176439454212408555079160297123149787700566151419673450218572170577139004440855088844000129510841301/749417494676758388331264226535081599786496989276363517363454269937199368732678212673604332988336116135490825788665595769374375572699465130) by rfl, show lastP 347 = 347 by rfl, show firstP 347 = 349 by rfl,
        show llb 347 = (883153/500000) by rfl, show lub 347 = (5849341/1000000) by rfl,
        show lub 349 = (365943/62500) by rfl, show clbZ 347 = 58493 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 348 = (1524725853981925381232603722144553928856176439454212408555079160297123149787700566151419673450218572170577139004440855088844000129510841301/749417494676758388331264226535081599786496989276363517363454269937199368732678212673604332988336116135490825788665595769374375572699465130) by rfl, show lastP 348 = 347 by rfl, show firstP 348 = 349 by rfl,
        show llb 347 = (883153/500000) by rfl, show lub 347 = (5849341/1000000) by rfl,
        show lub 349 = (365943/62500) by rfl, show clbZ 347 = 58493 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 349 = (532878740534368716438509963254984402770592074358796494103086081213633178644640175799519070367114617803666912338338524021775930420771983079179/261546705642188677527611215060743478325487449257450867559845540208082579687704696223087912212929304531286298200244292923511657074872113330370) by rfl, show lastP 349 = 349 by rfl, show firstP 349 = 353 by rfl,
        show llb 349 = (22091/12500) by rfl, show lub 349 = (365943/62500) by rfl,
        show lub 353 = (1466621/250000) by rfl, show clbZ 349 = 58550 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 350 = (532878740534368716438509963254984402770592074358796494103086081213633178644640175799519070367114617803666912338338524021775930420771983079179/261546705642188677527611215060743478325487449257450867559845540208082579687704696223087912212929304531286298200244292923511657074872113330370) by rfl, show lastP 350 = 349 by rfl, show firstP 350 = 353 by rfl,
        show llb 349 = (22091/12500) by rfl, show lub 349 = (365943/62500) by rfl,
        show lub 353 = (1466621/250000) by rfl, show clbZ 349 = 58550 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 351 = (532878740534368716438509963254984402770592074358796494103086081213633178644640175799519070367114617803666912338338524021775930420771983079179/261546705642188677527611215060743478325487449257450867559845540208082579687704696223087912212929304531286298200244292923511657074872113330370) by rfl, show lastP 351 = 349 by rfl, show firstP 351 = 353 by rfl,
        show llb 349 = (22091/12500) by rfl, show lub 349 = (365943/62500) by rfl,
        show lub 353 = (1466621/250000) by rfl, show clbZ 349 = 58550 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 352 = (532878740534368716438509963254984402770592074358796494103086081213633178644640175799519070367114617803666912338338524021775930420771983079179/261546705642188677527611215060743478325487449257450867559845540208082579687704696223087912212929304531286298200244292923511657074872113330370) by rfl, show lastP 352 = 349 by rfl, show firstP 352 = 353 by rfl,
        show llb 349 = (22091/12500) by rfl, show lub 349 = (365943/62500) by rfl,
        show lub 353 = (1466621/250000) by rfl, show clbZ 349 = 58550 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 353 = (188367742114274345580321628244070237656344489697912613285949232208620594641245686753453319751804389389225706353633743272610415095607382140280557/92325987091692603167246758916442447848897069587880156248625475693453150629759757766750033011164044499544063264686235401999614947429856005620610) by rfl, show lastP 353 = 353 by rfl, show firstP 353 = 359 by rfl,
        show llb 353 = (70769/40000) by rfl, show lub 353 = (1466621/250000) by rfl,
        show lub 359 = (2941669/500000) by rfl, show clbZ 353 = 58664 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 354 = (188367742114274345580321628244070237656344489697912613285949232208620594641245686753453319751804389389225706353633743272610415095607382140280557/92325987091692603167246758916442447848897069587880156248625475693453150629759757766750033011164044499544063264686235401999614947429856005620610) by rfl, show lastP 354 = 353 by rfl, show firstP 354 = 359 by rfl,
        show llb 353 = (70769/40000) by rfl, show lub 353 = (1466621/250000) by rfl,
        show lub 359 = (2941669/500000) by rfl, show clbZ 353 = 58664 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 355 = (188367742114274345580321628244070237656344489697912613285949232208620594641245686753453319751804389389225706353633743272610415095607382140280557/92325987091692603167246758916442447848897069587880156248625475693453150629759757766750033011164044499544063264686235401999614947429856005620610) by rfl, show lastP 355 = 353 by rfl, show firstP 355 = 359 by rfl,
        show llb 353 = (70769/40000) by rfl, show lub 353 = (1466621/250000) by rfl,
        show lub 359 = (2941669/500000) by rfl, show clbZ 353 = 58664 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 356 = (188367742114274345580321628244070237656344489697912613285949232208620594641245686753453319751804389389225706353633743272610415095607382140280557/92325987091692603167246758916442447848897069587880156248625475693453150629759757766750033011164044499544063264686235401999614947429856005620610) by rfl, show lastP 356 = 353 by rfl, show firstP 356 = 359 by rfl,
        show llb 353 = (70769/40000) by rfl, show lub 353 = (1466621/250000) by rfl,
        show lub 359 = (2941669/500000) by rfl, show clbZ 353 = 58664 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 357 = (188367742114274345580321628244070237656344489697912613285949232208620594641245686753453319751804389389225706353633743272610415095607382140280557/92325987091692603167246758916442447848897069587880156248625475693453150629759757766750033011164044499544063264686235401999614947429856005620610) by rfl, show lastP 357 = 353 by rfl, show firstP 357 = 359 by rfl,
        show llb 353 = (70769/40000) by rfl, show lub 353 = (1466621/250000) by rfl,
        show lub 359 = (2941669/500000) by rfl, show clbZ 353 = 58664 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 358 = (188367742114274345580321628244070237656344489697912613285949232208620594641245686753453319751804389389225706353633743272610415095607382140280557/92325987091692603167246758916442447848897069587880156248625475693453150629759757766750033011164044499544063264686235401999614947429856005620610) by rfl, show lastP 358 = 353 by rfl, show firstP 358 = 359 by rfl,
        show llb 353 = (70769/40000) by rfl, show lub 353 = (1466621/250000) by rfl,
        show lub 359 = (2941669/500000) by rfl, show clbZ 353 = 58664 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 359 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 359 = 359 by rfl, show firstP 359 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 360 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 360 = 359 by rfl, show firstP 360 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 361 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 361 = 359 by rfl, show firstP 361 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 362 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 362 = 359 by rfl, show firstP 362 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 363 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 363 = 359 by rfl, show firstP 363 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 364 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 364 = 359 by rfl, show firstP 364 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 365 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 365 = 359 by rfl, show firstP 365 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 366 = (67716345406116182666502711298537657766476568871138508325904399838588246626836961302256491823908939835231572644219200070269138634270480044366340573/33145029365917644537041586451002838777754047982048976093256545773949681076083753038263261851007891975336318712022358509317861766127318306017798990) by rfl, show lastP 366 = 359 by rfl, show firstP 366 = 367 by rfl,
        show llb 359 = (886051/500000) by rfl, show lub 359 = (2941669/500000) by rfl,
        show lub 367 = (2952689/500000) by rfl, show clbZ 359 = 58833 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 367 = (24885043793410556683143536633014323239074654823689881531700171286535836193125248550966395761225588811505323479140468784298091740543393494588464789281/12164225777291775545094262227518041831435735609411974226225152299039532954922737365042617099319896354948428967312205572919655268168725818308532229330) by rfl, show lastP 367 = 367 by rfl, show firstP 367 = 373 by rfl,
        show llb 367 = (887917/500000) by rfl, show lub 367 = (2952689/500000) by rfl,
        show lub 373 = (2960797/500000) by rfl, show clbZ 367 = 59053 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 368 = (24885043793410556683143536633014323239074654823689881531700171286535836193125248550966395761225588811505323479140468784298091740543393494588464789281/12164225777291775545094262227518041831435735609411974226225152299039532954922737365042617099319896354948428967312205572919655268168725818308532229330) by rfl, show lastP 368 = 367 by rfl, show firstP 368 = 373 by rfl,
        show llb 367 = (887917/500000) by rfl, show lub 367 = (2952689/500000) by rfl,
        show lub 373 = (2960797/500000) by rfl, show clbZ 367 = 59053 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 369 = (24885043793410556683143536633014323239074654823689881531700171286535836193125248550966395761225588811505323479140468784298091740543393494588464789281/12164225777291775545094262227518041831435735609411974226225152299039532954922737365042617099319896354948428967312205572919655268168725818308532229330) by rfl, show lastP 369 = 367 by rfl, show firstP 369 = 373 by rfl,
        show llb 367 = (887917/500000) by rfl, show lub 367 = (2952689/500000) by rfl,
        show lub 373 = (2960797/500000) by rfl, show clbZ 367 = 59053 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 370 = (24885043793410556683143536633014323239074654823689881531700171286535836193125248550966395761225588811505323479140468784298091740543393494588464789281/12164225777291775545094262227518041831435735609411974226225152299039532954922737365042617099319896354948428967312205572919655268168725818308532229330) by rfl, show lastP 370 = 367 by rfl, show firstP 370 = 373 by rfl,
        show llb 367 = (887917/500000) by rfl, show lub 367 = (2952689/500000) by rfl,
        show lub 373 = (2960797/500000) by rfl, show clbZ 367 = 59053 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 371 = (24885043793410556683143536633014323239074654823689881531700171286535836193125248550966395761225588811505323479140468784298091740543393494588464789281/12164225777291775545094262227518041831435735609411974226225152299039532954922737365042617099319896354948428967312205572919655268168725818308532229330) by rfl, show lastP 371 = 367 by rfl, show firstP 371 = 373 by rfl,
        show llb 367 = (887917/500000) by rfl, show lub 367 = (2952689/500000) by rfl,
        show lub 373 = (2960797/500000) by rfl, show clbZ 367 = 59053 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 372 = (24885043793410556683143536633014323239074654823689881531700171286535836193125248550966395761225588811505323479140468784298091740543393494588464789281/12164225777291775545094262227518041831435735609411974226225152299039532954922737365042617099319896354948428967312205572919655268168725818308532229330) by rfl, show lastP 372 = 367 by rfl, show firstP 372 = 373 by rfl,
        show llb 367 = (887917/500000) by rfl, show lub 367 = (2952689/500000) by rfl,
        show lub 373 = (2960797/500000) by rfl, show clbZ 367 = 59053 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 373 = (9294285560719429418357633426341860610006281984845737785550389042176906432990640446875508236036464523046434086686707062116107874490854499299805898631143/4537256214929832278320159810864229603125529382310666386381981807541745792186181037160896178046321340395764004807452678699031415026934730229082521540090) by rfl, show lastP 373 = 373 by rfl, show firstP 373 = 379 by rfl,
        show llb 373 = (889287/500000) by rfl, show lub 373 = (2960797/500000) by rfl,
        show lub 379 = (371097/62500) by rfl, show clbZ 373 = 59215 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 374 = (9294285560719429418357633426341860610006281984845737785550389042176906432990640446875508236036464523046434086686707062116107874490854499299805898631143/4537256214929832278320159810864229603125529382310666386381981807541745792186181037160896178046321340395764004807452678699031415026934730229082521540090) by rfl, show lastP 374 = 373 by rfl, show firstP 374 = 379 by rfl,
        show llb 373 = (889287/500000) by rfl, show lub 373 = (2960797/500000) by rfl,
        show lub 379 = (371097/62500) by rfl, show clbZ 373 = 59215 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 375 = (9294285560719429418357633426341860610006281984845737785550389042176906432990640446875508236036464523046434086686707062116107874490854499299805898631143/4537256214929832278320159810864229603125529382310666386381981807541745792186181037160896178046321340395764004807452678699031415026934730229082521540090) by rfl, show lastP 375 = 373 by rfl, show firstP 375 = 379 by rfl,
        show llb 373 = (889287/500000) by rfl, show lub 373 = (2960797/500000) by rfl,
        show lub 379 = (371097/62500) by rfl, show clbZ 373 = 59215 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 376 = (9294285560719429418357633426341860610006281984845737785550389042176906432990640446875508236036464523046434086686707062116107874490854499299805898631143/4537256214929832278320159810864229603125529382310666386381981807541745792186181037160896178046321340395764004807452678699031415026934730229082521540090) by rfl, show lastP 376 = 373 by rfl, show firstP 376 = 379 by rfl,
        show llb 373 = (889287/500000) by rfl, show lub 373 = (2960797/500000) by rfl,
        show lub 379 = (371097/62500) by rfl, show clbZ 373 = 59215 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 377 = (9294285560719429418357633426341860610006281984845737785550389042176906432990640446875508236036464523046434086686707062116107874490854499299805898631143/4537256214929832278320159810864229603125529382310666386381981807541745792186181037160896178046321340395764004807452678699031415026934730229082521540090) by rfl, show lastP 377 = 373 by rfl, show firstP 377 = 379 by rfl,
        show llb 373 = (889287/500000) by rfl, show lub 373 = (2960797/500000) by rfl,
        show lub 379 = (371097/62500) by rfl, show clbZ 373 = 59215 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 378 = (9294285560719429418357633426341860610006281984845737785550389042176906432990640446875508236036464523046434086686707062116107874490854499299805898631143/4537256214929832278320159810864229603125529382310666386381981807541745792186181037160896178046321340395764004807452678699031415026934730229082521540090) by rfl, show lastP 378 = 373 by rfl, show firstP 378 = 379 by rfl,
        show llb 373 = (889287/500000) by rfl, show lub 373 = (2960797/500000) by rfl,
        show lub 379 = (371097/62500) by rfl, show clbZ 373 = 59215 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 379 = (3527071483727593581835863228394429400795506401638845287109979428792589283895638910402978517635866375574994282859069429220703915847060789964855518102743287/1719620105458406433483340568317543019584575635895742560438771105058321655238562613083979651479555788009994557822024565226932906295208262756822275663694110) by rfl, show lastP 379 = 379 by rfl, show firstP 379 = 383 by rfl,
        show llb 379 = (222659/125000) by rfl, show lub 379 = (371097/62500) by rfl,
        show lub 383 = (118961/20000) by rfl, show clbZ 379 = 59375 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 380 = (3527071483727593581835863228394429400795506401638845287109979428792589283895638910402978517635866375574994282859069429220703915847060789964855518102743287/1719620105458406433483340568317543019584575635895742560438771105058321655238562613083979651479555788009994557822024565226932906295208262756822275663694110) by rfl, show lastP 380 = 379 by rfl, show firstP 380 = 383 by rfl,
        show llb 379 = (222659/125000) by rfl, show lub 379 = (371097/62500) by rfl,
        show lub 383 = (118961/20000) by rfl, show clbZ 379 = 59375 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 381 = (3527071483727593581835863228394429400795506401638845287109979428792589283895638910402978517635866375574994282859069429220703915847060789964855518102743287/1719620105458406433483340568317543019584575635895742560438771105058321655238562613083979651479555788009994557822024565226932906295208262756822275663694110) by rfl, show lastP 381 = 379 by rfl, show firstP 381 = 383 by rfl,
        show llb 379 = (222659/125000) by rfl, show lub 379 = (371097/62500) by rfl,
        show lub 383 = (118961/20000) by rfl, show clbZ 379 = 59375 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 382 = (3527071483727593581835863228394429400795506401638845287109979428792589283895638910402978517635866375574994282859069429220703915847060789964855518102743287/1719620105458406433483340568317543019584575635895742560438771105058321655238562613083979651479555788009994557822024565226932906295208262756822275663694110) by rfl, show lastP 382 = 379 by rfl, show firstP 382 = 383 by rfl,
        show llb 379 = (222659/125000) by rfl, show lub 379 = (371097/62500) by rfl,
        show lub 383 = (118961/20000) by rfl, show clbZ 379 = 59375 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 383 = (1352587998373126748276618957043384003524263527463573487523560892332620017387268265297424751906016377633232804892845615956756532675719490819296485709014373031/658614500390569664024119437665618976500892468548069400648049333237337193956369480811164206516669866807827915645835408481915303111064764635862931579194844130) by rfl, show lastP 383 = 383 by rfl, show firstP 383 = 389 by rfl,
        show llb 383 = (1783039/1000000) by rfl, show lub 383 = (118961/20000) by rfl,
        show lub 389 = (1192719/200000) by rfl, show clbZ 383 = 59480 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 384 = (1352587998373126748276618957043384003524263527463573487523560892332620017387268265297424751906016377633232804892845615956756532675719490819296485709014373031/658614500390569664024119437665618976500892468548069400648049333237337193956369480811164206516669866807827915645835408481915303111064764635862931579194844130) by rfl, show lastP 384 = 383 by rfl, show firstP 384 = 389 by rfl,
        show llb 383 = (1783039/1000000) by rfl, show lub 383 = (118961/20000) by rfl,
        show lub 389 = (1192719/200000) by rfl, show clbZ 383 = 59480 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 385 = (1352587998373126748276618957043384003524263527463573487523560892332620017387268265297424751906016377633232804892845615956756532675719490819296485709014373031/658614500390569664024119437665618976500892468548069400648049333237337193956369480811164206516669866807827915645835408481915303111064764635862931579194844130) by rfl, show lastP 385 = 383 by rfl, show firstP 385 = 389 by rfl,
        show llb 383 = (1783039/1000000) by rfl, show lub 383 = (118961/20000) by rfl,
        show lub 389 = (1192719/200000) by rfl, show clbZ 383 = 59480 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 386 = (1352587998373126748276618957043384003524263527463573487523560892332620017387268265297424751906016377633232804892845615956756532675719490819296485709014373031/658614500390569664024119437665618976500892468548069400648049333237337193956369480811164206516669866807827915645835408481915303111064764635862931579194844130) by rfl, show lastP 386 = 383 by rfl, show firstP 386 = 389 by rfl,
        show llb 383 = (1783039/1000000) by rfl, show lub 383 = (118961/20000) by rfl,
        show lub 389 = (1192719/200000) by rfl, show clbZ 383 = 59480 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 387 = (1352587998373126748276618957043384003524263527463573487523560892332620017387268265297424751906016377633232804892845615956756532675719490819296485709014373031/658614500390569664024119437665618976500892468548069400648049333237337193956369480811164206516669866807827915645835408481915303111064764635862931579194844130) by rfl, show lastP 387 = 383 by rfl, show firstP 387 = 389 by rfl,
        show llb 383 = (1783039/1000000) by rfl, show lub 383 = (118961/20000) by rfl,
        show lub 389 = (1192719/200000) by rfl, show clbZ 383 = 59480 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 388 = (1352587998373126748276618957043384003524263527463573487523560892332620017387268265297424751906016377633232804892845615956756532675719490819296485709014373031/658614500390569664024119437665618976500892468548069400648049333237337193956369480811164206516669866807827915645835408481915303111064764635862931579194844130) by rfl, show lastP 388 = 383 by rfl, show firstP 388 = 389 by rfl,
        show llb 383 = (1783039/1000000) by rfl, show lub 383 = (118961/20000) by rfl,
        show lub 389 = (1192719/200000) by rfl, show clbZ 383 = 59480 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 389 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 389 = 389 by rfl, show firstP 389 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 390 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 390 = 389 by rfl, show firstP 390 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 391 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 391 = 389 by rfl, show firstP 391 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 392 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 392 = 389 by rfl, show firstP 392 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 393 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 393 = 389 by rfl, show firstP 393 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 394 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 394 = 389 by rfl, show firstP 394 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 395 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 395 = 389 by rfl, show firstP 395 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 396 = (526815345867536874743628893727541996347439404651878156047313236450626523957603724681509392697957040766135389018962780015660206513965946693342195872385785953189/256201040651931599305382461251925781858847170265198996852091190629324168449027728035542876334984578188245059186229973899465052910204193443350680384306794366570) by rfl, show lastP 396 = 389 by rfl, show firstP 396 = 397 by rfl,
        show llb 389 = (892821/500000) by rfl, show lub 389 = (1192719/200000) by rfl,
        show lub 397 = (373997/62500) by rfl, show clbZ 389 = 59635 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 397 = (209401893350064070872526053271086098331792290817060826947635446061528054179617706426594771777423929762343994499714453640116567038954685030700202441721463817782603/101711813138816844924236837117014535397962326595284001750280202679841694874264008030110521904988877540733288496933299638087626005351064797010220112569797363528290) by rfl, show lastP 397 = 397 by rfl, show firstP 397 = 401 by rfl,
        show llb 397 = (1789057/1000000) by rfl, show lub 397 = (373997/62500) by rfl,
        show lub 401 = (5993977/1000000) by rfl, show clbZ 397 = 59839 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 398 = (209401893350064070872526053271086098331792290817060826947635446061528054179617706426594771777423929762343994499714453640116567038954685030700202441721463817782603/101711813138816844924236837117014535397962326595284001750280202679841694874264008030110521904988877540733288496933299638087626005351064797010220112569797363528290) by rfl, show lastP 398 = 397 by rfl, show firstP 398 = 401 by rfl,
        show llb 397 = (1789057/1000000) by rfl, show lub 397 = (373997/62500) by rfl,
        show lub 401 = (5993977/1000000) by rfl, show clbZ 397 = 59839 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 399 = (209401893350064070872526053271086098331792290817060826947635446061528054179617706426594771777423929762343994499714453640116567038954685030700202441721463817782603/101711813138816844924236837117014535397962326595284001750280202679841694874264008030110521904988877540733288496933299638087626005351064797010220112569797363528290) by rfl, show lastP 399 = 397 by rfl, show firstP 399 = 401 by rfl,
        show llb 397 = (1789057/1000000) by rfl, show lub 397 = (373997/62500) by rfl,
        show lub 401 = (5993977/1000000) by rfl, show clbZ 397 = 59839 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 400 = (209401893350064070872526053271086098331792290817060826947635446061528054179617706426594771777423929762343994499714453640116567038954685030700202441721463817782603/101711813138816844924236837117014535397962326595284001750280202679841694874264008030110521904988877540733288496933299638087626005351064797010220112569797363528290) by rfl, show lastP 400 = 397 by rfl, show firstP 400 = 401 by rfl,
        show llb 397 = (1789057/1000000) by rfl, show lub 397 = (373997/62500) by rfl,
        show lub 401 = (5993977/1000000) by rfl, show clbZ 397 = 59839 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 401 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 401 = 401 by rfl, show firstP 401 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 402 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 402 = 401 by rfl, show firstP 402 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 403 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 403 = 401 by rfl, show firstP 403 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 404 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 404 = 401 by rfl, show firstP 404 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 405 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 405 = 401 by rfl, show firstP 405 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 406 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 406 = 401 by rfl, show firstP 406 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 407 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 407 = 401 by rfl, show firstP 407 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 408 = (84071871046514509264807184198822539966446670944236675607752094073352591420900964285094614004651984712240675082882429209324831008626179762107791399242876788294352093/40786437068665554814618971683922828694582892964708884701862361274616519644579867220074319283900539893834048687270253154873138028145776983601098265140488742774844290) by rfl, show lastP 408 = 401 by rfl, show firstP 408 = 409 by rfl,
        show llb 401 = (895363/500000) by rfl, show lub 401 = (5993977/1000000) by rfl,
        show lub 409 = (6013731/1000000) by rfl, show clbZ 401 = 59939 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 409 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 409 = 409 by rfl, show firstP 409 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 410 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 410 = 409 by rfl, show firstP 410 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 411 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 411 = 409 by rfl, show firstP 411 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 412 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 412 = 409 by rfl, show firstP 412 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 413 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 413 = 409 by rfl, show firstP 413 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 414 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 414 = 409 by rfl, show firstP 414 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 415 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 415 = 409 by rfl, show firstP 415 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 416 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 416 = 409 by rfl, show firstP 416 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 417 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 417 = 409 by rfl, show firstP 417 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 418 = (34426181695093099844120757309002341674971271309157509208272468837275826410793074259823771447186562287200270157586183799768729020556253299685687780555477095155164850327/16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610) by rfl, show lastP 418 = 409 by rfl, show firstP 418 = 419 by rfl,
        show llb 409 = (224253/125000) by rfl, show lub 409 = (6013731/1000000) by rfl,
        show lub 419 = (6037887/1000000) by rfl, show clbZ 409 = 60137 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 419 = (14441251783005093046605776471890705598749047081759562292109226148579889422656931280559170632958284919153491321941704545643440573066581755354596029243187362765808983601623/6989612506894284794136067796445539076219364950255126280242854713992307588011296425371356170001319422146234757586190553403764537021369947456703810795390696338067840821590) by rfl, show lastP 419 = 419 by rfl, show firstP 419 = 421 by rfl,
        show llb 419 = (224753/125000) by rfl, show lub 419 = (6037887/1000000) by rfl,
        show lub 421 = (6042649/1000000) by rfl, show clbZ 419 = 60378 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 420 = (14441251783005093046605776471890705598749047081759562292109226148579889422656931280559170632958284919153491321941704545643440573066581755354596029243187362765808983601623/6989612506894284794136067796445539076219364950255126280242854713992307588011296425371356170001319422146234757586190553403764537021369947456703810795390696338067840821590) by rfl, show lastP 420 = 419 by rfl, show firstP 420 = 421 by rfl,
        show llb 419 = (224753/125000) by rfl, show lub 419 = (6037887/1000000) by rfl,
        show lub 421 = (6042649/1000000) by rfl, show clbZ 419 = 60378 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 421 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 421 = 421 by rfl, show firstP 421 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 422 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 422 = 421 by rfl, show firstP 422 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 423 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 423 = 421 by rfl, show firstP 423 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 424 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 424 = 421 by rfl, show firstP 424 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 425 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 425 = 421 by rfl, show firstP 425 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 426 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 426 = 421 by rfl, show firstP 426 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 427 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 427 = 421 by rfl, show firstP 427 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 428 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 428 = 421 by rfl, show firstP 428 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 429 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 429 = 421 by rfl, show firstP 429 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 430 = (6086756613152038457415167962462432596149568186371030851258227063266125754526579365540782192645439270385766081295043804269292245798052288951741632122177270420743649937104873/2942626865402493898331284542303571951088352644057408163982241834590761494552755795081340947570555476723564832943786222982984870085996747879272304344859483158326560985889390) by rfl, show lastP 430 = 421 by rfl, show firstP 430 = 431 by rfl,
        show llb 421 = (1798819/1000000) by rfl, show lub 421 = (6042649/1000000) by rfl,
        show lub 431 = (1516531/250000) by rfl, show clbZ 421 = 60426 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 431 = (2626334727133931069044268676363612020891552240969971705056278106102290961695508462343158465977754881012988745871107665863047942809046533286079915749003263034498839683878089653/1268272178988474870180783637732839510919079989588742918676346230708618204152237747680057948402909410467856442998771862105666479007064598335966363172634437241238747784918327090) by rfl, show lastP 431 = 431 by rfl, show firstP 431 = 433 by rfl,
        show llb 431 = (18027/10000) by rfl, show lub 431 = (1516531/250000) by rfl,
        show lub 433 = (6070753/1000000) by rfl, show clbZ 431 = 60661 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 432 = (2626334727133931069044268676363612020891552240969971705056278106102290961695508462343158465977754881012988745871107665863047942809046533286079915749003263034498839683878089653/1268272178988474870180783637732839510919079989588742918676346230708618204152237747680057948402909410467856442998771862105666479007064598335966363172634437241238747784918327090) by rfl, show lastP 432 = 431 by rfl, show firstP 432 = 433 by rfl,
        show llb 431 = (18027/10000) by rfl, show lub 431 = (1516531/250000) by rfl,
        show lub 433 = (6070753/1000000) by rfl, show clbZ 431 = 60661 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 433 = (1138471209027980627766349120503176844556961200329586491208044766173000604618307401942267673716770772889091983405188391180805425715324213511208569882491047331179236330904131146839/549161853502009618788279315138319508227961635491925683786857917896831682397918944745465091658459774732581839818468216291753585410058971079473435253750711325456377790869635629970) by rfl, show lastP 433 = 433 by rfl, show firstP 433 = 439 by rfl,
        show llb 433 = (901729/500000) by rfl, show lub 433 = (6070753/1000000) by rfl,
        show lub 439 = (1216903/200000) by rfl, show clbZ 433 = 60707 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 434 = (1138471209027980627766349120503176844556961200329586491208044766173000604618307401942267673716770772889091983405188391180805425715324213511208569882491047331179236330904131146839/549161853502009618788279315138319508227961635491925683786857917896831682397918944745465091658459774732581839818468216291753585410058971079473435253750711325456377790869635629970) by rfl, show lastP 434 = 433 by rfl, show firstP 434 = 439 by rfl,
        show llb 433 = (901729/500000) by rfl, show lub 433 = (6070753/1000000) by rfl,
        show lub 439 = (1216903/200000) by rfl, show clbZ 433 = 60707 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 435 = (1138471209027980627766349120503176844556961200329586491208044766173000604618307401942267673716770772889091983405188391180805425715324213511208569882491047331179236330904131146839/549161853502009618788279315138319508227961635491925683786857917896831682397918944745465091658459774732581839818468216291753585410058971079473435253750711325456377790869635629970) by rfl, show lastP 435 = 433 by rfl, show firstP 435 = 439 by rfl,
        show llb 433 = (901729/500000) by rfl, show lub 433 = (6070753/1000000) by rfl,
        show lub 439 = (1216903/200000) by rfl, show clbZ 433 = 60707 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 436 = (1138471209027980627766349120503176844556961200329586491208044766173000604618307401942267673716770772889091983405188391180805425715324213511208569882491047331179236330904131146839/549161853502009618788279315138319508227961635491925683786857917896831682397918944745465091658459774732581839818468216291753585410058971079473435253750711325456377790869635629970) by rfl, show lastP 436 = 433 by rfl, show firstP 436 = 439 by rfl,
        show llb 433 = (901729/500000) by rfl, show lub 433 = (6070753/1000000) by rfl,
        show lub 439 = (1216903/200000) by rfl, show clbZ 433 = 60707 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 437 = (1138471209027980627766349120503176844556961200329586491208044766173000604618307401942267673716770772889091983405188391180805425715324213511208569882491047331179236330904131146839/549161853502009618788279315138319508227961635491925683786857917896831682397918944745465091658459774732581839818468216291753585410058971079473435253750711325456377790869635629970) by rfl, show lastP 437 = 433 by rfl, show firstP 437 = 439 by rfl,
        show llb 433 = (901729/500000) by rfl, show lub 433 = (6070753/1000000) by rfl,
        show lub 439 = (1216903/200000) by rfl, show clbZ 433 = 60707 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 438 = (1138471209027980627766349120503176844556961200329586491208044766173000604618307401942267673716770772889091983405188391180805425715324213511208569882491047331179236330904131146839/549161853502009618788279315138319508227961635491925683786857917896831682397918944745465091658459774732581839818468216291753585410058971079473435253750711325456377790869635629970) by rfl, show lastP 438 = 433 by rfl, show firstP 438 = 439 by rfl,
        show llb 433 = (901729/500000) by rfl, show lub 433 = (6070753/1000000) by rfl,
        show lub 439 = (1216903/200000) by rfl, show clbZ 433 = 60707 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 439 = (500338022616785505208215543216032954268733928580180395324118510267844097109834868397400973853320829073043962554696171944665335474437388702500035613667320489713141127057783209092291/241082053687382222648054619345722264112075157980955375182430625956709108572686416743259175238063841107603427680307546952079823995015888303888838076396562271875349850191770041556830) by rfl, show lastP 439 = 439 by rfl, show firstP 439 = 443 by rfl,
        show llb 439 = (112857/62500) by rfl, show lub 439 = (1216903/200000) by rfl,
        show lub 443 = (3046793/500000) by rfl, show clbZ 439 = 60844 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 440 = (500338022616785505208215543216032954268733928580180395324118510267844097109834868397400973853320829073043962554696171944665335474437388702500035613667320489713141127057783209092291/241082053687382222648054619345722264112075157980955375182430625956709108572686416743259175238063841107603427680307546952079823995015888303888838076396562271875349850191770041556830) by rfl, show lastP 440 = 439 by rfl, show firstP 440 = 443 by rfl,
        show llb 439 = (112857/62500) by rfl, show lub 439 = (1216903/200000) by rfl,
        show lub 443 = (3046793/500000) by rfl, show clbZ 439 = 60844 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 441 = (500338022616785505208215543216032954268733928580180395324118510267844097109834868397400973853320829073043962554696171944665335474437388702500035613667320489713141127057783209092291/241082053687382222648054619345722264112075157980955375182430625956709108572686416743259175238063841107603427680307546952079823995015888303888838076396562271875349850191770041556830) by rfl, show lastP 441 = 439 by rfl, show firstP 441 = 443 by rfl,
        show llb 439 = (112857/62500) by rfl, show lub 439 = (1216903/200000) by rfl,
        show lub 443 = (3046793/500000) by rfl, show clbZ 439 = 60844 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 442 = (500338022616785505208215543216032954268733928580180395324118510267844097109834868397400973853320829073043962554696171944665335474437388702500035613667320489713141127057783209092291/241082053687382222648054619345722264112075157980955375182430625956709108572686416743259175238063841107603427680307546952079823995015888303888838076396562271875349850191770041556830) by rfl, show lastP 442 = 439 by rfl, show firstP 442 = 443 by rfl,
        show llb 439 = (112857/62500) by rfl, show lub 439 = (1216903/200000) by rfl,
        show lub 443 = (3046793/500000) by rfl, show clbZ 439 = 60844 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 443 = (221890826072923361029887540264048321005161205519000870503766930674611644128229533116791890592259191120466078839410711718438823439170779083511404614931019539214796869136789731669441743/106799349783510324633088196370154963001649294985563231205816767298822135097700082617263814630462281610668318462376243299771362029792038518622755267843677086440779983634954128409675690) by rfl, show lastP 443 = 443 by rfl, show firstP 443 = 449 by rfl,
        show llb 443 = (1807207/1000000) by rfl, show lub 443 = (3046793/500000) by rfl,
        show lub 449 = (6107039/1000000) by rfl, show clbZ 443 = 60935 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 444 = (221890826072923361029887540264048321005161205519000870503766930674611644128229533116791890592259191120466078839410711718438823439170779083511404614931019539214796869136789731669441743/106799349783510324633088196370154963001649294985563231205816767298822135097700082617263814630462281610668318462376243299771362029792038518622755267843677086440779983634954128409675690) by rfl, show lastP 444 = 443 by rfl, show firstP 444 = 449 by rfl,
        show llb 443 = (1807207/1000000) by rfl, show lub 443 = (3046793/500000) by rfl,
        show lub 449 = (6107039/1000000) by rfl, show clbZ 443 = 60935 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 445 = (221890826072923361029887540264048321005161205519000870503766930674611644128229533116791890592259191120466078839410711718438823439170779083511404614931019539214796869136789731669441743/106799349783510324633088196370154963001649294985563231205816767298822135097700082617263814630462281610668318462376243299771362029792038518622755267843677086440779983634954128409675690) by rfl, show lastP 445 = 443 by rfl, show firstP 445 = 449 by rfl,
        show llb 443 = (1807207/1000000) by rfl, show lub 443 = (3046793/500000) by rfl,
        show lub 449 = (6107039/1000000) by rfl, show clbZ 443 = 60935 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 446 = (221890826072923361029887540264048321005161205519000870503766930674611644128229533116791890592259191120466078839410711718438823439170779083511404614931019539214796869136789731669441743/106799349783510324633088196370154963001649294985563231205816767298822135097700082617263814630462281610668318462376243299771362029792038518622755267843677086440779983634954128409675690) by rfl, show lastP 446 = 443 by rfl, show firstP 446 = 449 by rfl,
        show llb 443 = (1807207/1000000) by rfl, show lub 443 = (3046793/500000) by rfl,
        show lub 449 = (6107039/1000000) by rfl, show clbZ 443 = 60935 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 447 = (221890826072923361029887540264048321005161205519000870503766930674611644128229533116791890592259191120466078839410711718438823439170779083511404614931019539214796869136789731669441743/106799349783510324633088196370154963001649294985563231205816767298822135097700082617263814630462281610668318462376243299771362029792038518622755267843677086440779983634954128409675690) by rfl, show lastP 447 = 443 by rfl, show firstP 447 = 449 by rfl,
        show llb 443 = (1807207/1000000) by rfl, show lub 443 = (3046793/500000) by rfl,
        show lub 449 = (6107039/1000000) by rfl, show clbZ 443 = 60935 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 448 = (221890826072923361029887540264048321005161205519000870503766930674611644128229533116791890592259191120466078839410711718438823439170779083511404614931019539214796869136789731669441743/106799349783510324633088196370154963001649294985563231205816767298822135097700082617263814630462281610668318462376243299771362029792038518622755267843677086440779983634954128409675690) by rfl, show lastP 448 = 443 by rfl, show firstP 448 = 449 by rfl,
        show llb 443 = (1807207/1000000) by rfl, show lub 443 = (3046793/500000) by rfl,
        show lub 449 = (6107039/1000000) by rfl, show clbZ 443 = 60935 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 449 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 449 = 449 by rfl, show firstP 449 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 450 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 450 = 449 by rfl, show firstP 450 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 451 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 451 = 449 by rfl, show firstP 451 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 452 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 452 = 449 by rfl, show firstP 452 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 453 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 453 = 449 by rfl, show firstP 453 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 454 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 454 = 449 by rfl, show firstP 454 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 455 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 455 = 449 by rfl, show firstP 455 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 456 = (99735780256526099427052593774927851094319030573016954087397168640199450348672760452056822690554839094699937717357785804878803086217471847015243427371871450193884574226053543647989018297/47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810) by rfl, show lastP 456 = 449 by rfl, show firstP 456 = 457 by rfl,
        show llb 449 = (90471/50000) by rfl, show lub 449 = (6107039/1000000) by rfl,
        show lub 457 = (6124699/1000000) by rfl, show clbZ 449 = 61070 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 457 = (45627204485285223573923291955312227528491537505317265908751917797088319948002318863685119422352639030721061611822115046071210351952761259380827863424207063750417160633958563850786925746539/21914478980127834042437266277781207323197423785972676100815159932347210367102373052484213915468446950537864270250368491409985088979117759751759021674647632398042967182007142470766583858170) by rfl, show lastP 457 = 457 by rfl, show firstP 457 = 461 by rfl,
        show llb 457 = (906149/500000) by rfl, show lub 457 = (6124699/1000000) by rfl,
        show lub 461 = (3066707/500000) by rfl, show clbZ 457 = 61246 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 458 = (45627204485285223573923291955312227528491537505317265908751917797088319948002318863685119422352639030721061611822115046071210351952761259380827863424207063750417160633958563850786925746539/21914478980127834042437266277781207323197423785972676100815159932347210367102373052484213915468446950537864270250368491409985088979117759751759021674647632398042967182007142470766583858170) by rfl, show lastP 458 = 457 by rfl, show firstP 458 = 461 by rfl,
        show llb 457 = (906149/500000) by rfl, show lub 457 = (6124699/1000000) by rfl,
        show lub 461 = (3066707/500000) by rfl, show clbZ 457 = 61246 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 459 = (45627204485285223573923291955312227528491537505317265908751917797088319948002318863685119422352639030721061611822115046071210351952761259380827863424207063750417160633958563850786925746539/21914478980127834042437266277781207323197423785972676100815159932347210367102373052484213915468446950537864270250368491409985088979117759751759021674647632398042967182007142470766583858170) by rfl, show lastP 459 = 457 by rfl, show firstP 459 = 461 by rfl,
        show llb 457 = (906149/500000) by rfl, show lub 457 = (6124699/1000000) by rfl,
        show lub 461 = (3066707/500000) by rfl, show clbZ 457 = 61246 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 460 = (45627204485285223573923291955312227528491537505317265908751917797088319948002318863685119422352639030721061611822115046071210351952761259380827863424207063750417160633958563850786925746539/21914478980127834042437266277781207323197423785972676100815159932347210367102373052484213915468446950537864270250368491409985088979117759751759021674647632398042967182007142470766583858170) by rfl, show lastP 460 = 457 by rfl, show firstP 460 = 461 by rfl,
        show llb 457 = (906149/500000) by rfl, show lub 457 = (6124699/1000000) by rfl,
        show lub 461 = (3066707/500000) by rfl, show clbZ 457 = 61246 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 461 = (21056055746696615901621074857676718097957796213737232260035449264390062706396171369211324267620035040112947267320245404730237957339202058334313404060234104021340354019436905077683539353012649/10102574809838931493563579754057136575994012365333403682475788728812063979234193977195222615030954044197955428585419874540003126019373287245560908992012558535497807870905292679023395158616370) by rfl, show lastP 461 = 461 by rfl, show firstP 461 = 463 by rfl,
        show llb 461 = (1813717/1000000) by rfl, show lub 461 = (3066707/500000) by rfl,
        show lub 463 = (6137743/1000000) by rfl, show clbZ 461 = 61333 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 462 = (21056055746696615901621074857676718097957796213737232260035449264390062706396171369211324267620035040112947267320245404730237957339202058334313404060234104021340354019436905077683539353012649/10102574809838931493563579754057136575994012365333403682475788728812063979234193977195222615030954044197955428585419874540003126019373287245560908992012558535497807870905292679023395158616370) by rfl, show lastP 462 = 461 by rfl, show firstP 462 = 463 by rfl,
        show llb 461 = (1813717/1000000) by rfl, show lub 461 = (3066707/500000) by rfl,
        show lub 463 = (6137743/1000000) by rfl, show clbZ 461 = 61333 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 463 = (9759056385530372093944121238858377615930453659325671940078888798141411097040661537922038358523107177616492540197859042264640177374069926296032666988880402720416081718870192343646502115603472857/4677492136955425281519937426128454234685227725149365904986290181439985622385431811441388070759331722463653363435049401912021447346969831994694700863301814601935485044229150510387831958439379310) by rfl, show lastP 463 = 463 by rfl, show firstP 463 = 467 by rfl,
        show llb 463 = (907217/500000) by rfl, show lub 463 = (6137743/1000000) by rfl,
        show lub 467 = (1229269/200000) by rfl, show clbZ 463 = 61377 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 464 = (9759056385530372093944121238858377615930453659325671940078888798141411097040661537922038358523107177616492540197859042264640177374069926296032666988880402720416081718870192343646502115603472857/4677492136955425281519937426128454234685227725149365904986290181439985622385431811441388070759331722463653363435049401912021447346969831994694700863301814601935485044229150510387831958439379310) by rfl, show lastP 464 = 463 by rfl, show firstP 464 = 467 by rfl,
        show llb 463 = (907217/500000) by rfl, show lub 463 = (6137743/1000000) by rfl,
        show lub 467 = (1229269/200000) by rfl, show clbZ 463 = 61377 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 465 = (9759056385530372093944121238858377615930453659325671940078888798141411097040661537922038358523107177616492540197859042264640177374069926296032666988880402720416081718870192343646502115603472857/4677492136955425281519937426128454234685227725149365904986290181439985622385431811441388070759331722463653363435049401912021447346969831994694700863301814601935485044229150510387831958439379310) by rfl, show lastP 465 = 463 by rfl, show firstP 465 = 467 by rfl,
        show llb 463 = (907217/500000) by rfl, show lub 463 = (6137743/1000000) by rfl,
        show lub 467 = (1229269/200000) by rfl, show clbZ 463 = 61377 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 466 = (9759056385530372093944121238858377615930453659325671940078888798141411097040661537922038358523107177616492540197859042264640177374069926296032666988880402720416081718870192343646502115603472857/4677492136955425281519937426128454234685227725149365904986290181439985622385431811441388070759331722463653363435049401912021447346969831994694700863301814601935485044229150510387831958439379310) by rfl, show lastP 466 = 463 by rfl, show firstP 466 = 467 by rfl,
        show llb 463 = (907217/500000) by rfl, show lub 463 = (6137743/1000000) by rfl,
        show lub 467 = (1229269/200000) by rfl, show clbZ 463 = 61377 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 467 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 467 = 467 by rfl, show firstP 467 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 468 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 468 = 467 by rfl, show firstP 468 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 469 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 469 = 467 by rfl, show firstP 469 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 470 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 470 = 467 by rfl, show firstP 470 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 471 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 471 = 467 by rfl, show firstP 471 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 472 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 472 = 467 by rfl, show firstP 472 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 473 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 473 = 467 by rfl, show firstP 473 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 474 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 474 = 467 by rfl, show firstP 474 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 475 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 475 = 467 by rfl, show firstP 475 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 476 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 476 = 467 by rfl, show firstP 476 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 477 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 477 = 467 by rfl, show firstP 477 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 478 = (4562156824179639193153424555972990800874207086630238161921827358913478967940374370021033301501050383669365669635835222139498984281037625412241950184670449885036245647756608974993304319945261203529/2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770) by rfl, show lastP 478 = 467 by rfl, show firstP 478 = 479 by rfl,
        show llb 467 = (363167/200000) by rfl, show lub 467 = (1229269/200000) by rfl,
        show lub 479 = (1542929/250000) by rfl, show clbZ 467 = 61463 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 479 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 479 = 479 by rfl, show firstP 479 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 480 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 480 = 479 by rfl, show firstP 480 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 481 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 481 = 479 by rfl, show firstP 481 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 482 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 482 = 479 by rfl, show firstP 482 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 483 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 483 = 479 by rfl, show firstP 483 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 484 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 484 = 479 by rfl, show firstP 484 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 485 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 485 = 479 by rfl, show firstP 485 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 486 = (2187457507610005357126960173089064581746343195843528833438183902434288898929093319896018079648047741692016681876289239475512927486528057484005416563760307442351465536791070712310143886778371306628161/1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830) by rfl, show lastP 486 = 479 by rfl, show firstP 486 = 487 by rfl,
        show llb 479 = (1819959/1000000) by rfl, show lub 479 = (1542929/250000) by rfl,
        show lub 487 = (154707/25000) by rfl, show clbZ 479 = 61717 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 487 = (1066338128454664578868328643657037403623588579021320378991779658695055548482296711187557563210311617395005186085579736130436701499560549717339027108271484297238914470873250188260160258155346006403906237/509558935064289364432032169616857776489168568369134671296055828054188240764364761921821351373922822013621199759688858354748131233614846920025560717744496960296617420071391914813530238313960697008021210) by rfl, show lastP 487 = 487 by rfl, show firstP 487 = 491 by rfl,
        show llb 487 = (455657/250000) by rfl, show lub 487 = (154707/25000) by rfl,
        show lub 491 = (309823/50000) by rfl, show clbZ 487 = 61882 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 488 = (1066338128454664578868328643657037403623588579021320378991779658695055548482296711187557563210311617395005186085579736130436701499560549717339027108271484297238914470873250188260160258155346006403906237/509558935064289364432032169616857776489168568369134671296055828054188240764364761921821351373922822013621199759688858354748131233614846920025560717744496960296617420071391914813530238313960697008021210) by rfl, show lastP 488 = 487 by rfl, show firstP 488 = 491 by rfl,
        show llb 487 = (455657/250000) by rfl, show lub 487 = (154707/25000) by rfl,
        show lub 491 = (309823/50000) by rfl, show clbZ 487 = 61882 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 489 = (1066338128454664578868328643657037403623588579021320378991779658695055548482296711187557563210311617395005186085579736130436701499560549717339027108271484297238914470873250188260160258155346006403906237/509558935064289364432032169616857776489168568369134671296055828054188240764364761921821351373922822013621199759688858354748131233614846920025560717744496960296617420071391914813530238313960697008021210) by rfl, show lastP 489 = 487 by rfl, show firstP 489 = 491 by rfl,
        show llb 487 = (455657/250000) by rfl, show lub 487 = (154707/25000) by rfl,
        show lub 491 = (309823/50000) by rfl, show clbZ 487 = 61882 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 490 = (1066338128454664578868328643657037403623588579021320378991779658695055548482296711187557563210311617395005186085579736130436701499560549717339027108271484297238914470873250188260160258155346006403906237/509558935064289364432032169616857776489168568369134671296055828054188240764364761921821351373922822013621199759688858354748131233614846920025560717744496960296617420071391914813530238313960697008021210) by rfl, show lastP 490 = 487 by rfl, show firstP 490 = 491 by rfl,
        show llb 487 = (455657/250000) by rfl, show lub 487 = (154707/25000) by rfl,
        show lub 491 = (309823/50000) by rfl, show clbZ 487 = 61882 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 491 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 491 = 491 by rfl, show firstP 491 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 492 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 492 = 491 by rfl, show firstP 492 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 493 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 493 = 491 by rfl, show firstP 493 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 494 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 494 = 491 by rfl, show firstP 494 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 495 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 495 = 491 by rfl, show firstP 495 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 496 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 496 = 491 by rfl, show firstP 496 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 497 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 497 = 491 by rfl, show firstP 497 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 498 = (524081580006304597588781396205222222955671160867837440756259868247326462545572049955012584887636926962961167567779339298399168567517844758133487870879043286904603622618837234350552216992588849841325983577/250193437116566077936127795281877168256181767069245123606363411574606426215303098103614283524596105608688009082007229452181332435704889837732550312412548007505639153255053430173443347012154702230938414110) by rfl, show lastP 498 = 491 by rfl, show firstP 498 = 499 by rfl,
        show llb 491 = (1823953/1000000) by rfl, show lub 491 = (309823/50000) by rfl,
        show lub 499 = (3106311/500000) by rfl, show clbZ 491 = 61964 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 499 = (261766901860262560274738044501687766423136091040120128060980037666990511236455756025654894142455422660126310625403897539353366447627109424146342997881055148172902846840054833371098999626313990773052604219033/124846525121166472890127769845656706959834701767553316679575342375728606681436245953703527478773456698735316531921607496638484885416740029028542605893861455745313937474271661656548230159065196413238268640890) by rfl, show lastP 499 = 499 by rfl, show firstP 499 = 503 by rfl,
        show llb 499 = (456641/250000) by rfl, show lub 499 = (3106311/500000) by rfl,
        show lub 503 = (3110303/500000) by rfl, show clbZ 499 = 62126 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 500 = (261766901860262560274738044501687766423136091040120128060980037666990511236455756025654894142455422660126310625403897539353366447627109424146342997881055148172902846840054833371098999626313990773052604219033/124846525121166472890127769845656706959834701767553316679575342375728606681436245953703527478773456698735316531921607496638484885416740029028542605893861455745313937474271661656548230159065196413238268640890) by rfl, show lastP 500 = 499 by rfl, show firstP 500 = 503 by rfl,
        show llb 499 = (456641/250000) by rfl, show lub 499 = (3106311/500000) by rfl,
        show lub 503 = (3110303/500000) by rfl, show clbZ 499 = 62126 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 501 = (261766901860262560274738044501687766423136091040120128060980037666990511236455756025654894142455422660126310625403897539353366447627109424146342997881055148172902846840054833371098999626313990773052604219033/124846525121166472890127769845656706959834701767553316679575342375728606681436245953703527478773456698735316531921607496638484885416740029028542605893861455745313937474271661656548230159065196413238268640890) by rfl, show lastP 501 = 499 by rfl, show firstP 501 = 503 by rfl,
        show llb 499 = (456641/250000) by rfl, show lub 499 = (3106311/500000) by rfl,
        show lub 503 = (3110303/500000) by rfl, show clbZ 499 = 62126 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 502 = (261766901860262560274738044501687766423136091040120128060980037666990511236455756025654894142455422660126310625403897539353366447627109424146342997881055148172902846840054833371098999626313990773052604219033/124846525121166472890127769845656706959834701767553316679575342375728606681436245953703527478773456698735316531921607496638484885416740029028542605893861455745313937474271661656548230159065196413238268640890) by rfl, show lastP 502 = 499 by rfl, show firstP 502 = 503 by rfl,
        show llb 499 = (456641/250000) by rfl, show lub 499 = (3106311/500000) by rfl,
        show lub 503 = (3110303/500000) by rfl, show clbZ 499 = 62126 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 503 = (131793598160833234291083364154194603217797288494947977731352534288871955758618681526858115281133851054742269561110082069791381808041852780374639070540064600986715445898021852847319345042195002555258698190814489/62797802135946735863734268232365323600796854989079318289826397214991489160762431714712874321823048719463864215556568570809157897364620234601356930764612312239892910549558645813243759770009793795858849126367670) by rfl, show lastP 503 = 503 by rfl, show firstP 503 = 509 by rfl,
        show llb 503 = (365567/200000) by rfl, show lub 503 = (3110303/500000) by rfl,
        show lub 509 = (389529/62500) by rfl, show clbZ 503 = 62205 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 504 = (131793598160833234291083364154194603217797288494947977731352534288871955758618681526858115281133851054742269561110082069791381808041852780374639070540064600986715445898021852847319345042195002555258698190814489/62797802135946735863734268232365323600796854989079318289826397214991489160762431714712874321823048719463864215556568570809157897364620234601356930764612312239892910549558645813243759770009793795858849126367670) by rfl, show lastP 504 = 503 by rfl, show firstP 504 = 509 by rfl,
        show llb 503 = (365567/200000) by rfl, show lub 503 = (3110303/500000) by rfl,
        show lub 509 = (389529/62500) by rfl, show clbZ 503 = 62205 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 505 = (131793598160833234291083364154194603217797288494947977731352534288871955758618681526858115281133851054742269561110082069791381808041852780374639070540064600986715445898021852847319345042195002555258698190814489/62797802135946735863734268232365323600796854989079318289826397214991489160762431714712874321823048719463864215556568570809157897364620234601356930764612312239892910549558645813243759770009793795858849126367670) by rfl, show lastP 505 = 503 by rfl, show firstP 505 = 509 by rfl,
        show llb 503 = (365567/200000) by rfl, show lub 503 = (3110303/500000) by rfl,
        show lub 509 = (389529/62500) by rfl, show clbZ 503 = 62205 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 506 = (131793598160833234291083364154194603217797288494947977731352534288871955758618681526858115281133851054742269561110082069791381808041852780374639070540064600986715445898021852847319345042195002555258698190814489/62797802135946735863734268232365323600796854989079318289826397214991489160762431714712874321823048719463864215556568570809157897364620234601356930764612312239892910549558645813243759770009793795858849126367670) by rfl, show lastP 506 = 503 by rfl, show firstP 506 = 509 by rfl,
        show llb 503 = (365567/200000) by rfl, show lub 503 = (3110303/500000) by rfl,
        show lub 509 = (389529/62500) by rfl, show clbZ 503 = 62205 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 507 = (131793598160833234291083364154194603217797288494947977731352534288871955758618681526858115281133851054742269561110082069791381808041852780374639070540064600986715445898021852847319345042195002555258698190814489/62797802135946735863734268232365323600796854989079318289826397214991489160762431714712874321823048719463864215556568570809157897364620234601356930764612312239892910549558645813243759770009793795858849126367670) by rfl, show lastP 507 = 503 by rfl, show firstP 507 = 509 by rfl,
        show llb 503 = (365567/200000) by rfl, show lub 503 = (3110303/500000) by rfl,
        show lub 509 = (389529/62500) by rfl, show clbZ 503 = 62205 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 508 = (131793598160833234291083364154194603217797288494947977731352534288871955758618681526858115281133851054742269561110082069791381808041852780374639070540064600986715445898021852847319345042195002555258698190814489/62797802135946735863734268232365323600796854989079318289826397214991489160762431714712874321823048719463864215556568570809157897364620234601356930764612312239892910549558645813243759770009793795858849126367670) by rfl, show lastP 508 = 503 by rfl, show firstP 508 = 509 by rfl,
        show llb 503 = (365567/200000) by rfl, show lub 503 = (3110303/500000) by rfl,
        show lub 509 = (389529/62500) by rfl, show clbZ 503 = 62205 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 509 = (67145739266000062990025166622717418361459616698917599983548266350250816970297671328885493552418953235583279070820588342094622498190667685445292643835657494214478054872642681745098790386247266094422536228250942571/31964081287196888554640742530273949712805599189441373009521636182430667982828077742788853029807931798207106885718293402541861369758591699412090677759187666930105491469725350718941073722934985042092154205321144030) by rfl, show lastP 509 = 509 by rfl, show firstP 509 = 521 by rfl,
        show llb 509 = (914873/500000) by rfl, show lub 509 = (389529/62500) by rfl,
        show lub 521 = (3127883/500000) by rfl, show clbZ 509 = 62324 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 510 = (67145739266000062990025166622717418361459616698917599983548266350250816970297671328885493552418953235583279070820588342094622498190667685445292643835657494214478054872642681745098790386247266094422536228250942571/31964081287196888554640742530273949712805599189441373009521636182430667982828077742788853029807931798207106885718293402541861369758591699412090677759187666930105491469725350718941073722934985042092154205321144030) by rfl, show lastP 510 = 509 by rfl, show firstP 510 = 521 by rfl,
        show llb 509 = (914873/500000) by rfl, show lub 509 = (389529/62500) by rfl,
        show lub 521 = (3127883/500000) by rfl, show clbZ 509 = 62324 by rfl]
    norm_num
  · unfold rho rho1 rho1f rho2 rho2f Mq
    rw [show T 511 = (67145739266000062990025166622717418361459616698917599983548266350250816970297671328885493552418953235583279070820588342094622498190667685445292643835657494214478054872642681745098790386247266094422536228250942571/31964081287196888554640742530273949712805599189441373009521636182430667982828077742788853029807931798207106885718293402541861369758591699412090677759187666930105491469725350718941073722934985042092154205321144030) by rfl, show lastP 511 = 509 by rfl, show firstP 511 = 521 by rfl,
        show llb 509 = (914873/500000) by rfl, show lub 509 = (389529/62500) by rfl,
        show lub 521 = (3127883/500000) by rfl, show clbZ 509 = 62324 by rfl]
    norm_num

