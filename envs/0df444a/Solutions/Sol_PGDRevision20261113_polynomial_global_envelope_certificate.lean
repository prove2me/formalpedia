-- Prove2me | solution 1 for PGDRevision20261113.polynomial_global_envelope_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:29:21.351274+00:00
-- url     : https://prove2.me/submissions/128167d7-b666-420d-8539-c59910dc3a10

import Definitions.Def_PGDRevision20261113_NumericalCertificates
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 2000000
noncomputable section
open PGDRevision20261113

private def numerator (u : ℝ) : ℝ :=
  (polynomialNumericalCandidate.2 * (1 + polynomialNumericalCandidate.1 * u) - (1 + u ^ 2)) * (1 - u)
private def denominator (u : ℝ) : ℝ :=
  polynomialNumericalCandidate.2 * (1 + polynomialNumericalCandidate.1 * u) * (1 - u) + 1
private def upperGap (u : ℝ) : ℝ := polynomialNumericalUpper * denominator u - numerator u
private def lowerGap (u : ℝ) : ℝ := polynomialNumericalUpper * denominator u + numerator u

private lemma bernstein_nonnegative (a b b0 b1 b2 b3 : ℝ) (P : ℝ → ℝ) (u : ℝ)
    (hab : a < b) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (hu : u ∈ Set.Icc a b)
    (identity : (b - a) ^ 3 * P u =
      b0 * (b - u) ^ 3 + 3 * b1 * (u - a) * (b - u) ^ 2 +
      3 * b2 * (u - a) ^ 2 * (b - u) + b3 * (u - a) ^ 3) : 0 ≤ P u := by
  have hl : 0 ≤ u - a := sub_nonneg.mpr hu.1
  have hr : 0 ≤ b - u := sub_nonneg.mpr hu.2
  have hproduct : 0 ≤ (b - a) ^ 3 * P u := by
    rw [identity]
    positivity
  exact nonneg_of_mul_nonneg_right hproduct (pow_pos (sub_pos.mpr hab) 3)

private lemma interval_0 (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (1 / 4 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (0 : ℝ)) (b := (1 / 4 : ℝ))
      (b0 := (239252854283867058947 / 2500000000000000000000 : ℝ)) (b1 := (8817002946572426503684570292122799 / 250000000000000000000000000000000000 : ℝ)) (b2 := (27880155415443927051400976134578779 / 3000000000000000000000000000000000000 : ℝ)) (b3 := (2152261770121632585986132629105191 / 1000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (0 : ℝ)) (b := (1 / 4 : ℝ))
      (b0 := (43011967058947 / 2500000000000000000000 : ℝ)) (b1 := (14820572489126579838785557992122799 / 250000000000000000000000000000000000 : ℝ)) (b2 := (250263966235588647088521717834578779 / 3000000000000000000000000000000000000 : ℝ)) (b3 := (88042113570856512601895021929105191 / 1000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_1 (u : ℝ) (hu : u ∈ Set.Icc (1 / 4 : ℝ) (9 / 32 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (1 / 4 : ℝ)) (b := (9 / 32 : ℝ))
      (b0 := (2152261770121632585986132629105191 / 1000000000000000000000000000000000000 : ℝ)) (b1 := (15115456188920076385112302425630689 / 12000000000000000000000000000000000000 : ℝ)) (b2 := (42320282673478383171209167318538993 / 64000000000000000000000000000000000000 : ℝ)) (b3 := (20905177285498412854943151408258179 / 64000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (1 / 4 : ℝ)) (b := (9 / 32 : ℝ))
      (b0 := (88042113570856512601895021929105191 / 1000000000000000000000000000000000000 : ℝ)) (b1 := (1063436550088768596581321937125630689 / 12000000000000000000000000000000000000 : ℝ)) (b2 := (5689109691782351957577508701218538993 / 64000000000000000000000000000000000000 : ℝ)) (b3 := (5688992667461575133952656513108258179 / 64000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_2 (u : ℝ) (hu : u ∈ Set.Icc (9 / 32 : ℝ) (19 / 64 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (9 / 32 : ℝ)) (b := (19 / 64 : ℝ))
      (b0 := (20905177285498412854943151408258179 / 64000000000000000000000000000000000000 : ℝ)) (b1 := (2549406147877106924202535863279443 / 16000000000000000000000000000000000000 : ℝ)) (b2 := (44521997608567472163496915099359983 / 768000000000000000000000000000000000000 : ℝ)) (b3 := (958929830491998244309559858995887 / 51200000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (9 / 32 : ℝ)) (b := (19 / 64 : ℝ))
      (b0 := (5688992667461575133952656513108258179 / 64000000000000000000000000000000000000 : ℝ)) (b1 := (1422233538825296680535057604763279443 / 16000000000000000000000000000000000000 : ℝ)) (b2 := (68213812370800490925627720225999359983 / 768000000000000000000000000000000000000 : ℝ)) (b3 := (4540709947906510159151116249958995887 / 51200000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_3 (u : ℝ) (hu : u ∈ Set.Icc (19 / 64 : ℝ) (77 / 256 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (19 / 64 : ℝ)) (b := (77 / 256 : ℝ))
      (b0 := (958929830491998244309559858995887 / 51200000000000000000000000000000000000 : ℝ)) (b1 := (13698869839166198079860037162665771 / 1536000000000000000000000000000000000000 : ℝ)) (b2 := (36750205446925752342837517567271059 / 12288000000000000000000000000000000000000 : ℝ)) (b3 := (3629492547956027248722008985615851 / 4096000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (19 / 64 : ℝ)) (b := (77 / 256 : ℝ))
      (b0 := (4540709947906510159151116249958995887 / 51200000000000000000000000000000000000 : ℝ)) (b1 := (136169716861093885505352999260462665771 / 1536000000000000000000000000000000000000 : ℝ)) (b2 := (1088895316620550641091074156503267271059 / 12288000000000000000000000000000000000000 : ℝ)) (b3 := (362794621704945369780339462416285615851 / 4096000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_4 (u : ℝ) (hu : u ∈ Set.Icc (77 / 256 : ℝ) (309 / 1024 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (77 / 256 : ℝ)) (b := (309 / 1024 : ℝ))
      (b0 := (3629492547956027248722008985615851 / 4096000000000000000000000000000000000000 : ℝ)) (b1 := (8846091386207328193996308608483353 / 24576000000000000000000000000000000000000 : ℝ)) (b2 := (4766948446924701621551931849934801 / 65536000000000000000000000000000000000000 : ℝ)) (b3 := (308591972432383058447494090358239 / 13107200000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (77 / 256 : ℝ)) (b := (309 / 1024 : ℝ))
      (b0 := (362794621704945369780339462416285615851 / 4096000000000000000000000000000000000000 : ℝ)) (b1 := (2176512004476814952807008889870508483353 / 24576000000000000000000000000000000000000 : ℝ)) (b2 := (5803333732184715802219180703424149934801 / 65536000000000000000000000000000000000000 : ℝ)) (b3 := (1160523833810781990137380477993790358239 / 13107200000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_5 (u : ℝ) (hu : u ∈ Set.Icc (309 / 1024 : ℝ) (1237 / 4096 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (309 / 1024 : ℝ)) (b := (1237 / 4096 : ℝ))
      (b0 := (308591972432383058447494090358239 / 13107200000000000000000000000000000000000 : ℝ)) (b1 := (1473925431942437419817710204510587 / 131072000000000000000000000000000000000000 : ℝ)) (b2 := (43482267344061223823222797254162419 / 3145728000000000000000000000000000000000000 : ℝ)) (b3 := (32780155982970870423397279574567451 / 1048576000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (309 / 1024 : ℝ)) (b := (1237 / 4096 : ℝ))
      (b0 := (1160523833810781990137380477993790358239 / 13107200000000000000000000000000000000000 : ℝ)) (b1 := (11604881056542416975607665623210304510587 / 131072000000000000000000000000000000000000 : ℝ)) (b2 := (278508521749316291857398329263910954162419 / 3145728000000000000000000000000000000000000 : ℝ)) (b3 := (92833283112419632716304792546366874567451 / 1048576000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_6 (u : ℝ) (hu : u ∈ Set.Icc (1237 / 4096 : ℝ) (619 / 2048 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (1237 / 4096 : ℝ)) (b := (619 / 2048 : ℝ))
      (b0 := (32780155982970870423397279574567451 / 1048576000000000000000000000000000000000000 : ℝ)) (b1 := (153198668553763998717160880193242287 / 3145728000000000000000000000000000000000000 : ℝ)) (b2 := (995339893695406436966801604634429 / 12288000000000000000000000000000000000000 : ℝ)) (b3 := (33593310356542104892434402541934747 / 262144000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (1237 / 4096 : ℝ)) (b := (619 / 2048 : ℝ))
      (b0 := (92833283112419632716304792546366874567451 / 1048576000000000000000000000000000000000000 : ℝ)) (b1 := (278491176925201504440430426014290293242287 / 3145728000000000000000000000000000000000000 : ℝ)) (b2 := (1087822092612454814768156908038304634429 / 12288000000000000000000000000000000000000 : ℝ)) (b3 := (23206140477816337479755633747470641934747 / 262144000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_7 (u : ℝ) (hu : u ∈ Set.Icc (619 / 2048 : ℝ) (155 / 512 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (619 / 2048 : ℝ)) (b := (155 / 512 : ℝ))
      (b0 := (33593310356542104892434402541934747 / 262144000000000000000000000000000000000000 : ℝ)) (b1 := (174936286815866920100159017484205811 / 786432000000000000000000000000000000000000 : ℝ)) (b2 := (36974626227791085902798264558279873 / 98304000000000000000000000000000000000000 : ℝ)) (b3 := (1930293947310985900183268769049599 / 3276800000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (619 / 2048 : ℝ)) (b := (155 / 512 : ℝ))
      (b0 := (23206140477816337479755633747470641934747 / 262144000000000000000000000000000000000000 : ℝ)) (b1 := (69614036445952821027476619498332784205811 / 786432000000000000000000000000000000000000 : ℝ)) (b2 := (8701200337484664831486003977822458279873 / 98304000000000000000000000000000000000000 : ℝ)) (b3 := (290021334528230165364588075896469049599 / 3276800000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_8 (u : ℝ) (hu : u ∈ Set.Icc (155 / 512 : ℝ) (39 / 128 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (155 / 512 : ℝ)) (b := (39 / 128 : ℝ))
      (b0 := (1930293947310985900183268769049599 / 3276800000000000000000000000000000000000 : ℝ)) (b1 := (70822793592741770708148628562160179 / 49152000000000000000000000000000000000000 : ℝ)) (b2 := (6637666354236038108871646446341999 / 2048000000000000000000000000000000000000 : ℝ)) (b3 := (6125662395811129587855451874705987 / 1024000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (155 / 512 : ℝ)) (b := (39 / 128 : ℝ))
      (b0 := (290021334528230165364588075896469049599 / 3276800000000000000000000000000000000000 : ℝ)) (b1 := (4349199414647932739372097736590262160179 / 49152000000000000000000000000000000000000 : ℝ)) (b2 := (181167922681076517061544516794146341999 / 2048000000000000000000000000000000000000 : ℝ)) (b3 := (90558595275585437307994440371974705987 / 1024000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_9 (u : ℝ) (hu : u ∈ Set.Icc (39 / 128 : ℝ) (5 / 16 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (39 / 128 : ℝ)) (b := (5 / 16 : ℝ))
      (b0 := (6125662395811129587855451874705987 / 1024000000000000000000000000000000000000 : ℝ)) (b1 := (17352979270583571721533966480845937 / 1024000000000000000000000000000000000000 : ℝ)) (b2 := (8249218251525887704063045774036829 / 192000000000000000000000000000000000000 : ℝ)) (b3 := (267393547995233180275819640052367 / 3200000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (39 / 128 : ℝ)) (b := (5 / 16 : ℝ))
      (b0 := (90558595275585437307994440371974705987 / 1024000000000000000000000000000000000000 : ℝ)) (b1 := (90457131015774152416883168271580845937 / 1024000000000000000000000000000000000000 : ℝ)) (b2 := (16938668715765594611188109802474036829 / 192000000000000000000000000000000000000 : ℝ)) (b3 := (281894968630507793238608413740052367 / 3200000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_10 (u : ℝ) (hu : u ∈ Set.Icc (5 / 16 : ℝ) (3 / 8 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (5 / 16 : ℝ)) (b := (3 / 8 : ℝ))
      (b0 := (267393547995233180275819640052367 / 3200000000000000000000000000000000000 : ℝ)) (b1 := (19599692476304703929109559858995887 / 48000000000000000000000000000000000000 : ℝ)) (b2 := (1666046699396397330280273213350789 / 1000000000000000000000000000000000000 : ℝ)) (b3 := (2890063341734926691286132629105191 / 800000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (5 / 16 : ℝ)) (b := (3 / 8 : ℝ))
      (b0 := (281894968630507793238608413740052367 / 3200000000000000000000000000000000000 : ℝ)) (b1 := (4178483333587362864835916249958995887 / 48000000000000000000000000000000000000 : ℝ)) (b2 := (85035545121417084016391137913350789 / 1000000000000000000000000000000000000 : ℝ)) (b3 := (65830196269659806707195021929105191 / 800000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_11 (u : ℝ) (hu : u ∈ Set.Icc (3 / 8 : ℝ) (1 / 2 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (3 / 8 : ℝ)) (b := (1 / 2 : ℝ))
      (b0 := (2890063341734926691286132629105191 / 800000000000000000000000000000000000 : ℝ)) (b1 := (30022576530852721727049803729771553 / 4000000000000000000000000000000000000 : ℝ)) (b2 := (10615469931089911980773632629105191 / 750000000000000000000000000000000000 : ℝ)) (b3 := (5401100375847191247978710876368397 / 250000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (3 / 8 : ℝ)) (b := (1 / 2 : ℝ))
      (b0 := (65830196269659806707195021929105191 / 800000000000000000000000000000000000 : ℝ)) (b1 := (307168583073560428476796225629771553 / 4000000000000000000000000000000000000 : ℝ)) (b2 := (51277583281711041996682521929105191 / 750000000000000000000000000000000000 : ℝ)) (b3 := (14743691539687151253281673976368397 / 250000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_12 (u : ℝ) (hu : u ∈ Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (1 / 2 : ℝ)) (b := (3 / 4 : ℝ))
      (b0 := (5401100375847191247978710876368397 / 250000000000000000000000000000000000 : ℝ)) (b1 := (27378963520444897270261132629105191 / 750000000000000000000000000000000000 : ℝ)) (b2 := (54614671163913014961905273213350789 / 1000000000000000000000000000000000000 : ℝ)) (b3 := (60307560913348220796586132629105191 / 1000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (1 / 2 : ℝ)) (b := (3 / 4 : ℝ))
      (b0 := (14743691539687151253281673976368397 / 250000000000000000000000000000000000 : ℝ)) (b1 := (30138057293762277286170021929105191 / 750000000000000000000000000000000000 : ℝ)) (b2 := (17500145994921201648016137913350789 / 1000000000000000000000000000000000000 : ℝ)) (b3 := (6547974968463100812495021929105191 / 1000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_13 (u : ℝ) (hu : u ∈ Set.Icc (3 / 4 : ℝ) (13 / 16 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (3 / 4 : ℝ)) (b := (13 / 16 : ℝ))
      (b0 := (60307560913348220796586132629105191 / 1000000000000000000000000000000000000 : ℝ)) (b1 := (123461566701414044510512694966087583 / 2000000000000000000000000000000000000 : ℝ)) (b2 := (2994142787665505699967846281298786419 / 48000000000000000000000000000000000000 : ℝ)) (b3 := (992079911445140164460919724178367483 / 16000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (3 / 4 : ℝ)) (b := (13 / 16 : ℝ))
      (b0 := (6547974968463100812495021929105191 / 1000000000000000000000000000000000000 : ℝ)) (b1 := (7619864423697151207229485866087583 / 2000000000000000000000000000000000000 : ℝ)) (b2 := (86645971962145620641322594998786419 / 48000000000000000000000000000000000000 : ℝ)) (b3 := (12443075288823604667735285078367483 / 16000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_14 (u : ℝ) (hu : u ∈ Set.Icc (13 / 16 : ℝ) (53 / 64 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (13 / 16 : ℝ)) (b := (53 / 64 : ℝ))
      (b0 := (992079911445140164460919724178367483 / 16000000000000000000000000000000000000 : ℝ)) (b1 := (5943527942005798383472974790688362913 / 96000000000000000000000000000000000000 : ℝ)) (b2 := (47427643082564392403142821179575799027 / 768000000000000000000000000000000000000 : ℝ)) (b3 := (15751721567140247966733738440922775451 / 256000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (13 / 16 : ℝ)) (b := (53 / 64 : ℝ))
      (b0 := (12443075288823604667735285078367483 / 16000000000000000000000000000000000000 : ℝ)) (b1 := (50000078685104224687353340588362913 / 96000000000000000000000000000000000000 : ℝ)) (b2 := (249647673209045772640428091675799027 / 768000000000000000000000000000000000000 : ℝ)) (b3 := (49712810849389649825365928222775451 / 256000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_15 (u : ℝ) (hu : u ∈ Set.Icc (53 / 64 : ℝ) (107 / 128 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (53 / 64 : ℝ)) (b := (107 / 128 : ℝ))
      (b0 := (15751721567140247966733738440922775451 / 256000000000000000000000000000000000000 : ℝ)) (b1 := (737014461107014369511412693661946719 / 12000000000000000000000000000000000000 : ℝ)) (b2 := (188278847353446727750737809152967046319 / 3072000000000000000000000000000000000000 : ℝ)) (b3 := (62609543297362041022751113339199788059 / 1024000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (53 / 64 : ℝ)) (b := (107 / 128 : ℝ))
      (b0 := (49712810849389649825365928222775451 / 256000000000000000000000000000000000000 : ℝ)) (b1 := (1545059565902039654592697361946719 / 12000000000000000000000000000000000000 : ℝ)) (b2 := (244360483160079706941138236667046319 / 3072000000000000000000000000000000000000 : ℝ)) (b3 := (48164758936716154666871424899788059 / 1024000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_16 (u : ℝ) (hu : u ∈ Set.Icc (107 / 128 : ℝ) (215 / 256 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (107 / 128 : ℝ)) (b := (215 / 256 : ℝ))
      (b0 := (62609543297362041022751113339199788059 / 1024000000000000000000000000000000000000 : ℝ)) (b1 := (93801760580702910363505552724957761553 / 1536000000000000000000000000000000000000 : ℝ)) (b2 := (749460286951490419704774854818050359743 / 12288000000000000000000000000000000000000 : ℝ)) (b3 := (49896826270938060177546977275037483911 / 819200000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (107 / 128 : ℝ)) (b := (215 / 256 : ℝ))
      (b0 := (48164758936716154666871424899788059 / 1024000000000000000000000000000000000000 : ℝ)) (b1 := (47280586817591421265176146857761553 / 1536000000000000000000000000000000000000 : ℝ)) (b2 := (229820841201780085934429576950359743 / 12288000000000000000000000000000000000000 : ℝ)) (b3 := (8895864606582666896101220337483911 / 819200000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_17 (u : ℝ) (hu : u ∈ Set.Icc (215 / 256 : ℝ) (431 / 512 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (215 / 256 : ℝ)) (b := (431 / 512 : ℝ))
      (b0 := (49896826270938060177546977275037483911 / 819200000000000000000000000000000000000 : ℝ)) (b1 := (373974223810180572071209780639659104063 / 6144000000000000000000000000000000000000 : ℝ)) (b2 := (2989723909513318888648237225021420261951 / 49152000000000000000000000000000000000000 : ℝ)) (b3 := (995866522380323015629498525404897107667 / 16384000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (215 / 256 : ℝ)) (b := (431 / 512 : ℝ))
      (b0 := (8895864606582666896101220337483911 / 819200000000000000000000000000000000000 : ℝ)) (b1 := (42623266523609981097531334559104063 / 6144000000000000000000000000000000000000 : ℝ)) (b2 := (200261369218710885488496458720261951 / 49152000000000000000000000000000000000000 : ℝ)) (b3 := (37314599473984374630270188997107667 / 16384000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_18 (u : ℝ) (hu : u ∈ Set.Icc (431 / 512 : ℝ) (863 / 1024 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (431 / 512 : ℝ)) (b := (863 / 1024 : ℝ))
      (b0 := (995866522380323015629498525404897107667 / 16384000000000000000000000000000000000000 : ℝ)) (b1 := (1493268697977397063004312375905663426763 / 24576000000000000000000000000000000000000 : ℝ)) (b2 := (11941846437670252666676715080920973167807 / 196608000000000000000000000000000000000000 : ℝ)) (b3 := (3979162882337211975160210175295254184371 / 65536000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (431 / 512 : ℝ)) (b := (863 / 1024 : ℝ))
      (b0 := (37314599473984374630270188997107667 / 16384000000000000000000000000000000000000 : ℝ)) (b1 := (33892506511787121545983810563426763 / 24576000000000000000000000000000000000000 : ℝ)) (b2 := (146912102674192650866567027073167807 / 196608000000000000000000000000000000000000 : ℝ)) (b3 := (25091483632083177019777298554184371 / 65536000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_19 (u : ℝ) (hu : u ∈ Set.Icc (863 / 1024 : ℝ) (1727 / 2048 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (863 / 1024 : ℝ)) (b := (1727 / 2048 : ℝ))
      (b0 := (3979162882337211975160210175295254184371 / 65536000000000000000000000000000000000000 : ℝ)) (b1 := (5967654875841163777441294124184078622883 / 98304000000000000000000000000000000000000 : ℝ)) (b2 := (47732468780902383833299883254691331385279 / 786432000000000000000000000000000000000000 : ℝ)) (b3 := (15907881273004343389410370962399719139699 / 262144000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (863 / 1024 : ℝ)) (b := (1727 / 2048 : ℝ))
      (b0 := (25091483632083177019777298554184371 / 65536000000000000000000000000000000000000 : ℝ)) (b1 := (19727812503638985577857164978622883 / 98304000000000000000000000000000000000000 : ℝ)) (b2 := (67137494115386846702455383031385279 / 786432000000000000000000000000000000000000 : ℝ)) (b3 := (9711446192732670158707257419139699 / 262144000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_20 (u : ℝ) (hu : u ∈ Set.Icc (1727 / 2048 : ℝ) (3455 / 4096 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (1727 / 2048 : ℝ)) (b := (3455 / 4096 : ℝ))
      (b0 := (15907881273004343389410370962399719139699 / 262144000000000000000000000000000000000000 : ℝ)) (b1 := (23859615669034176667848363851726535218003 / 393216000000000000000000000000000000000000 : ℝ)) (b2 := (190859220692432278733811069450117057443263 / 3145728000000000000000000000000000000000000 : ℝ)) (b3 := (12722764083383489977233128497180730451607 / 209715200000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (1727 / 2048 : ℝ)) (b := (3455 / 4096 : ℝ))
      (b0 := (9711446192732670158707257419139699 / 262144000000000000000000000000000000000000 : ℝ)) (b1 := (5066380404801796181477483435218003 / 393216000000000000000000000000000000000000 : ℝ)) (b2 := (17206582540572898693220971957443263 / 3145728000000000000000000000000000000000000 : ℝ)) (b3 := (3107316572430341975246026830451607 / 209715200000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_21 (u : ℝ) (hu : u ∈ Set.Icc (3455 / 4096 : ℝ) (27 / 32 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (3455 / 4096 : ℝ)) (b := (27 / 32 : ℝ))
      (b0 := (12722764083383489977233128497180730451607 / 209715200000000000000000000000000000000000 : ℝ)) (b1 := (190823701809072420583182785465304856104947 / 3145728000000000000000000000000000000000000 : ℝ)) (b2 := (248445166127023043022825967245036300869 / 4096000000000000000000000000000000000000 : ℝ)) (b3 := (776318434791747281274575193661946719 / 12800000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (3455 / 4096 : ℝ)) (b := (27 / 32 : ℝ))
      (b0 := (3107316572430341975246026830451607 / 209715200000000000000000000000000000000000 : ℝ)) (b1 := (76012914632337360564159832956104947 / 3145728000000000000000000000000000000000000 : ℝ)) (b2 := (205916285705655329679293736300869 / 4096000000000000000000000000000000000000 : ℝ)) (b3 := (1192414971201417755197361946719 / 12800000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_22 (u : ℝ) (hu : u ∈ Set.Icc (27 / 32 : ℝ) (7 / 8 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (27 / 32 : ℝ)) (b := (7 / 8 : ℝ))
      (b0 := (776318434791747281274575193661946719 / 12800000000000000000000000000000000000 : ℝ)) (b1 := (3835058186630910376449065421883032017 / 64000000000000000000000000000000000000 : ℝ)) (b2 := (282768624568689980031878397887315573 / 4800000000000000000000000000000000000 : ℝ)) (b3 := (230325591988350279893800976134578779 / 4000000000000000000000000000000000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (27 / 32 : ℝ)) (b := (7 / 8 : ℝ))
      (b0 := (1192414971201417755197361946719 / 12800000000000000000000000000000000000 : ℝ)) (b1 := (357275085013603792743710983032017 / 64000000000000000000000000000000000000 : ℝ)) (b2 := (1372479184910620079605065787315573 / 4800000000000000000000000000000000000 : ℝ)) (b3 := (3486651826014999930921717834578779 / 4000000000000000000000000000000000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma interval_23 (u : ℝ) (hu : u ∈ Set.Icc (7 / 8 : ℝ) (1 : ℝ)) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  constructor
  · apply bernstein_nonnegative (a := (7 / 8 : ℝ)) (b := (1 : ℝ))
      (b0 := (230325591988350279893800976134578779 / 4000000000000000000000000000000000000 : ℝ)) (b1 := (125439526827670879617646132629105191 / 2400000000000000000000000000000000000 : ℝ)) (b2 := (62841437768750514774303710876368397 / 1500000000000000000000000000000000000 : ℝ)) (b3 := (1225587 / 50000000 : ℝ))
      (P := upperGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [upperGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring
  · apply bernstein_nonnegative (a := (7 / 8 : ℝ)) (b := (1 : ℝ))
      (b0 := (3486651826014999930921717834578779 / 4000000000000000000000000000000000000 : ℝ)) (b1 := (7714997108223759633555021929105191 / 2400000000000000000000000000000000000 : ℝ)) (b2 := (15665349214387974779606673976368397 / 1500000000000000000000000000000000000 : ℝ)) (b3 := (1225587 / 50000000 : ℝ))
      (P := lowerGap) (u := u) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu
    norm_num [lowerGap, numerator, denominator, polynomialNumericalCandidate, polynomialNumericalUpper]
    ring

private lemma all_gaps_nonnegative (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ upperGap u ∧ 0 ≤ lowerGap u := by
  by_cases h0 : u ≤ (1 / 4 : ℝ)
  · exact interval_0 u ⟨hu.1, h0⟩
  have l0 : (1 / 4 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h0)
  by_cases h1 : u ≤ (9 / 32 : ℝ)
  · exact interval_1 u ⟨l0, h1⟩
  have l1 : (9 / 32 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : u ≤ (19 / 64 : ℝ)
  · exact interval_2 u ⟨l1, h2⟩
  have l2 : (19 / 64 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : u ≤ (77 / 256 : ℝ)
  · exact interval_3 u ⟨l2, h3⟩
  have l3 : (77 / 256 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : u ≤ (309 / 1024 : ℝ)
  · exact interval_4 u ⟨l3, h4⟩
  have l4 : (309 / 1024 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h4)
  by_cases h5 : u ≤ (1237 / 4096 : ℝ)
  · exact interval_5 u ⟨l4, h5⟩
  have l5 : (1237 / 4096 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h5)
  by_cases h6 : u ≤ (619 / 2048 : ℝ)
  · exact interval_6 u ⟨l5, h6⟩
  have l6 : (619 / 2048 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h6)
  by_cases h7 : u ≤ (155 / 512 : ℝ)
  · exact interval_7 u ⟨l6, h7⟩
  have l7 : (155 / 512 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h7)
  by_cases h8 : u ≤ (39 / 128 : ℝ)
  · exact interval_8 u ⟨l7, h8⟩
  have l8 : (39 / 128 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h8)
  by_cases h9 : u ≤ (5 / 16 : ℝ)
  · exact interval_9 u ⟨l8, h9⟩
  have l9 : (5 / 16 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h9)
  by_cases h10 : u ≤ (3 / 8 : ℝ)
  · exact interval_10 u ⟨l9, h10⟩
  have l10 : (3 / 8 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h10)
  by_cases h11 : u ≤ (1 / 2 : ℝ)
  · exact interval_11 u ⟨l10, h11⟩
  have l11 : (1 / 2 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h11)
  by_cases h12 : u ≤ (3 / 4 : ℝ)
  · exact interval_12 u ⟨l11, h12⟩
  have l12 : (3 / 4 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h12)
  by_cases h13 : u ≤ (13 / 16 : ℝ)
  · exact interval_13 u ⟨l12, h13⟩
  have l13 : (13 / 16 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h13)
  by_cases h14 : u ≤ (53 / 64 : ℝ)
  · exact interval_14 u ⟨l13, h14⟩
  have l14 : (53 / 64 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h14)
  by_cases h15 : u ≤ (107 / 128 : ℝ)
  · exact interval_15 u ⟨l14, h15⟩
  have l15 : (107 / 128 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h15)
  by_cases h16 : u ≤ (215 / 256 : ℝ)
  · exact interval_16 u ⟨l15, h16⟩
  have l16 : (215 / 256 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h16)
  by_cases h17 : u ≤ (431 / 512 : ℝ)
  · exact interval_17 u ⟨l16, h17⟩
  have l17 : (431 / 512 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h17)
  by_cases h18 : u ≤ (863 / 1024 : ℝ)
  · exact interval_18 u ⟨l17, h18⟩
  have l18 : (863 / 1024 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h18)
  by_cases h19 : u ≤ (1727 / 2048 : ℝ)
  · exact interval_19 u ⟨l18, h19⟩
  have l19 : (1727 / 2048 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h19)
  by_cases h20 : u ≤ (3455 / 4096 : ℝ)
  · exact interval_20 u ⟨l19, h20⟩
  have l20 : (3455 / 4096 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h20)
  by_cases h21 : u ≤ (27 / 32 : ℝ)
  · exact interval_21 u ⟨l20, h21⟩
  have l21 : (27 / 32 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h21)
  by_cases h22 : u ≤ (7 / 8 : ℝ)
  · exact interval_22 u ⟨l21, h22⟩
  have l22 : (7 / 8 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h22)
  exact interval_23 u ⟨l22, hu.2⟩

theorem solution : PolynomialGlobalEnvelopeClaim := by
  constructor
  · intro u hu
    have hg := all_gaps_nonnegative u hu
    have hleft : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
    have hnonneg : 0 ≤ u := hu.1
    have hd : 0 < denominator u := by
      dsimp [denominator, polynomialNumericalCandidate]
      positivity
    change |numerator u / denominator u| ≤ polynomialNumericalUpper
    apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hd).mpr
      dsimp [lowerGap] at hg
      linarith [hg.2]
    · apply (div_le_iff₀ hd).mpr
      dsimp [upperGap] at hg
      linarith [hg.1]
  · intro i
    fin_cases i <;> norm_num [rationalPolynomialError, polynomialNumericalCandidate,
      polynomialNumericalSquaredContacts, polynomialNumericalLower, alternatingSign]
