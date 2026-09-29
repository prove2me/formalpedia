-- Prove2me | solution 1 for RamareAnalytic.global_logarithmic_constant_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T21:21:04.655903+00:00
-- url     : https://prove2.me/submissions/81621b66-11ea-4202-baea-00979781dad7

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
open scoped BigOperators

/-! A standalone proof of convergence and an explicit upper bound for the
prime logarithmic correction constant. All component certificates are
proved below before the final unconditional theorem. -/

-- BEGIN COMPONENT FinitePrimeLogSum.lean
namespace RamareFiniteConstants

private def logSeries (x : ℚ) (terms : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range terms,
    ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

private def logUpper (x : ℚ) (terms : ℕ) : ℚ :=
  logSeries x terms +
    2 * ((x - 1) / (x + 1)) ^ (2 * terms + 1) /
      (1 - ((x - 1) / (x + 1)) ^ 2)

private theorem log_le_upper (x : ℚ) (hx : 1 ≤ x) (terms : ℕ) :
    Real.log (x : ℝ) ≤ (logUpper x terms : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.log_div_le_sum_range_add hnonneg hlt terms
  rw [hratio] at h
  calc
    Real.log (x : ℝ) = 2 * ((1 / 2 : ℝ) * Real.log (x : ℝ)) := by ring
    _ ≤ 2 * ((∑ i ∈ Finset.range terms,
        (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ (2 * terms + 1) /
          (1 - (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (logUpper x terms : ℝ) := by
      unfold logUpper logSeries
      push_cast
      ring

private def logUpperNat (N k terms : ℕ) : ℚ :=
  (k : ℚ) * logUpper 2 terms + logUpper ((N : ℚ) / 2 ^ k) terms

private theorem log_le_upperNat (N k terms : ℕ) (hN : 2 ^ k ≤ N) :
    Real.log (N : ℝ) ≤ (logUpperNat N k terms : ℝ) := by
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have hpowR : (0 : ℝ) < 2 ^ k := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hratio : (1 : ℚ) ≤ (N : ℚ) / 2 ^ k := by
    apply (le_div_iff₀ hpow).2
    simpa using (show (2 : ℚ) ^ k ≤ N by exact_mod_cast hN)
  have htwo := log_le_upper 2 (by norm_num) terms
  norm_num at htwo
  have hrest := log_le_upper ((N : ℚ) / 2 ^ k) hratio terms
  have hmult := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ k by positivity)
  have hid : (2 : ℝ) ^ k * ((N : ℝ) / 2 ^ k) = N := by field_simp
  have hlog := Real.log_mul hpowR.ne' (div_pos hNposR hpowR).ne'
  rw [hid, Real.log_pow] at hlog
  unfold logUpperNat
  push_cast at hrest ⊢
  linarith

private structure LogRow where
  prime : ℕ
  exponent : ℕ
  rounded : ℕ
  deriving DecidableEq

private def scale : ℕ := 1000000000000

private noncomputable def logWeight (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / ((p * (p - 1) : ℕ) : ℝ)

private theorem logWeight_nonneg (p : ℕ) : 0 ≤ logWeight p :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)

private abbrev rowValid (r : LogRow) : Prop :=
  2 ≤ r.prime ∧ 2 ^ r.exponent ≤ r.prime ∧
    logUpperNat r.prime r.exponent 9 / ((r.prime * (r.prime - 1) : ℕ) : ℚ) ≤
      (r.rounded : ℚ) / (scale : ℚ)

private theorem rowValid_sound (r : LogRow) (h : rowValid r) :
    logWeight r.prime ≤ (r.rounded : ℝ) / (scale : ℝ) := by
  have hlog := log_le_upperNat r.prime r.exponent 9 h.2.1
  have hcert : (logUpperNat r.prime r.exponent 9 : ℝ) /
      ((r.prime * (r.prime - 1) : ℕ) : ℝ) ≤
        (r.rounded : ℝ) / (scale : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).2 h.2.2
    simpa only [Rat.cast_div, Rat.cast_natCast] using hc
  exact (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg _)).trans hcert

private theorem rows_sum_le (rs : List LogRow) (h : List.Forall rowValid rs) :
    (rs.map (fun r => logWeight r.prime)).sum ≤
      (((rs.map LogRow.rounded).sum : ℕ) : ℝ) / (scale : ℝ) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      have hparts := (List.forall_cons rowValid r rs).mp h
      have hr : rowValid r := hparts.1
      have ht : List.Forall rowValid rs := hparts.2
      simpa only [List.map_cons, List.sum_cons, Nat.cast_add, add_div] using
        add_le_add (rowValid_sound r hr) (ih ht)

-- Literal prime index, power-of-two exponent, and upward-rounded log weight.
private def rows : List LogRow :=
  [
    ⟨2, 1, 346573591198⟩,
    ⟨3, 1, 183102048418⟩,
    ⟨5, 2, 80471895806⟩,
    ⟨7, 2, 46331194114⟩,
    ⟨11, 3, 21799047985⟩,
    ⟨13, 3, 16441983096⟩,
    ⟨17, 4, 10416225557⟩,
    ⟨19, 4, 8609470721⟩,
    ⟨23, 4, 6196628900⟩,
    ⟨29, 4, 4146916056⟩,
    ⟨31, 4, 3692459369⟩,
    ⟨37, 5, 2710899341⟩,
    ⟨41, 5, 2264373218⟩,
    ⟨43, 5, 2082613580⟩,
    ⟨47, 5, 1780826833⟩,
    ⟨53, 5, 1440599392⟩,
    ⟨59, 5, 1191565592⟩,
    ⟨61, 5, 1123189584⟩,
    ⟨67, 6, 950857674⟩,
    ⟨71, 6, 857682071⟩,
    ⟨73, 6, 816297461⟩,
    ⟨79, 6, 709095726⟩,
    ⟨83, 6, 649256630⟩,
    ⟨89, 6, 573114962⟩,
    ⟨97, 6, 491270511⟩,
    ⟨101, 6, 456942627⟩,
    ⟨103, 6, 441150676⟩,
    ⟨107, 6, 411993374⟩,
    ⟨109, 6, 398517491⟩,
    ⟨113, 6, 373529380⟩,
    ⟨127, 6, 302723854⟩,
    ⟨131, 7, 286271130⟩,
    ⟨137, 7, 264060807⟩,
    ⟨139, 7, 257245019⟩,
    ⟨149, 7, 226915760⟩,
    ⟨151, 7, 221513460⟩,
    ⟨157, 7, 206444791⟩,
    ⟨163, 7, 192901243⟩,
    ⟨167, 7, 184618492⟩,
    ⟨173, 7, 173184958⟩,
    ⟨179, 7, 162807916⟩,
    ⟨181, 7, 159560990⟩,
    ⟨191, 7, 144730600⟩,
    ⟨193, 7, 142019922⟩,
    ⟨197, 7, 136828027⟩,
    ⟨199, 7, 134341020⟩,
    ⟨211, 7, 120782175⟩,
    ⟨223, 7, 109222555⟩,
    ⟨227, 7, 105745391⟩,
    ⟨229, 7, 104070368⟩,
    ⟨233, 7, 100840582⟩,
    ⟨239, 7, 96277620⟩,
    ⟨241, 7, 94827057⟩,
    ⟨251, 7, 88055028⟩,
    ⟨257, 8, 84342718⟩,
    ⟨263, 8, 80866022⟩,
    ⟨269, 8, 77605163⟩,
    ⟨271, 8, 76563057⟩,
    ⟨277, 8, 73562726⟩,
    ⟨281, 8, 71661855⟩,
    ⟨283, 8, 70739631⟩,
    ⟨293, 8, 66391284⟩,
    ⟨307, 8, 60961527⟩,
    ⟨311, 8, 59535245⟩,
    ⟨313, 8, 58841272⟩,
    ⟨317, 8, 57490135⟩,
    ⟨331, 8, 53118360⟩,
    ⟨337, 8, 51399631⟩,
    ⟨347, 8, 48719202⟩,
    ⟨349, 8, 48208938⟩,
    ⟨353, 8, 47212755⟩,
    ⟨359, 8, 45776773⟩,
    ⟨367, 8, 43964220⟩,
    ⟨373, 8, 42676198⟩,
    ⟨379, 8, 41445298⟩,
    ⟨383, 8, 40654758⟩,
    ⟨389, 8, 39511697⟩,
    ⟨397, 8, 38062847⟩,
    ⟨401, 8, 37368837⟩,
    ⟨409, 8, 36037893⟩,
    ⟨419, 8, 34474147⟩,
    ⟨421, 8, 34173922⟩,
    ⟨431, 8, 32731388⟩,
    ⟨433, 8, 32454120⟩,
    ⟨439, 8, 31643625⟩,
    ⟨443, 8, 31120445⟩,
    ⟨449, 8, 30360240⟩,
    ⟨457, 8, 29390205⟩,
    ⟨461, 8, 28922938⟩,
    ⟨463, 8, 28693572⟩,
    ⟨467, 8, 28243144⟩,
    ⟨479, 8, 26955131⟩,
    ⟨487, 8, 26145901⟩,
    ⟨491, 8, 25755203⟩,
    ⟨499, 8, 25000226⟩,
    ⟨503, 8, 24635416⟩,
    ⟨509, 8, 24103337⟩,
    ⟨521, 9, 23090766⟩,
    ⟨523, 9, 22928366⟩,
    ⟨541, 9, 21542478⟩,
    ⟨547, 9, 21108976⟩,
    ⟨557, 9, 20415656⟩,
    ⟨563, 9, 20016308⟩,
    ⟨569, 9, 19628829⟩,
    ⟨571, 9, 19502226⟩,
    ⟨577, 9, 19129846⟩,
    ⟨587, 9, 18533019⟩,
    ⟨593, 9, 18188536⟩,
    ⟨599, 9, 17853786⟩,
    ⟨601, 9, 17744302⟩,
    ⟨607, 9, 17421961⟩,
    ⟨613, 9, 17108523⟩,
    ⟨617, 9, 16904348⟩,
    ⟨619, 9, 16803659⟩,
    ⟨631, 9, 16218414⟩,
    ⟨641, 9, 15754265⟩,
    ⟨643, 9, 15663883⟩,
    ⟨647, 9, 15485490⟩,
    ⟨653, 9, 15223690⟩,
    ⟨659, 9, 14968622⟩,
    ⟨661, 9, 14885055⟩,
    ⟨673, 9, 14398362⟩,
    ⟨677, 9, 14241545⟩,
    ⟨683, 9, 14011187⟩,
    ⟨691, 9, 13712830⟩,
    ⟨701, 9, 13353389⟩,
    ⟨709, 9, 13076139⟩,
    ⟨719, 9, 12741818⟩,
    ⟨727, 9, 12483709⟩,
    ⟨733, 9, 12295354⟩,
    ⟨739, 9, 12111324⟩,
    ⟨743, 9, 11990975⟩,
    ⟨751, 9, 11755714⟩,
    ⟨757, 9, 11583883⟩,
    ⟨761, 9, 11471460⟩,
    ⟨769, 9, 11251577⟩,
    ⟨773, 9, 11144051⟩,
    ⟨787, 9, 10779862⟩,
    ⟨797, 9, 10530783⟩,
    ⟨809, 9, 10243363⟩,
    ⟨811, 9, 10196630⟩,
    ⟨821, 9, 9967802⟩,
    ⟨823, 9, 9922982⟩,
    ⟨827, 9, 9834263⟩,
    ⟨829, 9, 9790360⟩,
    ⟨839, 9, 9575286⟩,
    ⟨853, 9, 9286143⟩,
    ⟨857, 9, 9205987⟩,
    ⟨859, 9, 9166306⟩,
    ⟨863, 9, 9087728⟩,
    ⟨877, 9, 8820683⟩,
    ⟨881, 9, 8746592⟩,
    ⟨883, 9, 8709904⟩,
    ⟨887, 9, 8637232⟩,
    ⟨907, 9, 8287447⟩,
    ⟨911, 9, 8220098⟩,
    ⟨919, 9, 8087893⟩,
    ⟨929, 9, 7927171⟩,
    ⟨937, 9, 7802091⟩,
    ⟨941, 9, 7740683⟩,
    ⟨947, 9, 7649950⟩,
    ⟨953, 9, 7560838⟩,
    ⟨967, 9, 7358995⟩,
    ⟨971, 9, 7302841⟩,
    ⟨977, 9, 7219834⟩,
    ⟨983, 9, 7138265⟩,
    ⟨991, 9, 7031684⟩,
    ⟨997, 9, 6953341⟩
  ]

private theorem row_000 : rowValid ⟨2, 1, 346573591198⟩ := by
  decide +kernel

private theorem row_001 : rowValid ⟨3, 1, 183102048418⟩ := by
  decide +kernel

private theorem row_002 : rowValid ⟨5, 2, 80471895806⟩ := by
  decide +kernel

private theorem row_003 : rowValid ⟨7, 2, 46331194114⟩ := by
  decide +kernel

private theorem row_004 : rowValid ⟨11, 3, 21799047985⟩ := by
  decide +kernel

private theorem row_005 : rowValid ⟨13, 3, 16441983096⟩ := by
  decide +kernel

private theorem row_006 : rowValid ⟨17, 4, 10416225557⟩ := by
  decide +kernel

private theorem row_007 : rowValid ⟨19, 4, 8609470721⟩ := by
  decide +kernel

private theorem row_008 : rowValid ⟨23, 4, 6196628900⟩ := by
  decide +kernel

private theorem row_009 : rowValid ⟨29, 4, 4146916056⟩ := by
  decide +kernel

private theorem row_010 : rowValid ⟨31, 4, 3692459369⟩ := by
  decide +kernel

private theorem row_011 : rowValid ⟨37, 5, 2710899341⟩ := by
  decide +kernel

private theorem row_012 : rowValid ⟨41, 5, 2264373218⟩ := by
  decide +kernel

private theorem row_013 : rowValid ⟨43, 5, 2082613580⟩ := by
  decide +kernel

private theorem row_014 : rowValid ⟨47, 5, 1780826833⟩ := by
  decide +kernel

private theorem row_015 : rowValid ⟨53, 5, 1440599392⟩ := by
  decide +kernel

private theorem row_016 : rowValid ⟨59, 5, 1191565592⟩ := by
  decide +kernel

private theorem row_017 : rowValid ⟨61, 5, 1123189584⟩ := by
  decide +kernel

private theorem row_018 : rowValid ⟨67, 6, 950857674⟩ := by
  decide +kernel

private theorem row_019 : rowValid ⟨71, 6, 857682071⟩ := by
  decide +kernel

private theorem row_020 : rowValid ⟨73, 6, 816297461⟩ := by
  decide +kernel

private theorem row_021 : rowValid ⟨79, 6, 709095726⟩ := by
  decide +kernel

private theorem row_022 : rowValid ⟨83, 6, 649256630⟩ := by
  decide +kernel

private theorem row_023 : rowValid ⟨89, 6, 573114962⟩ := by
  decide +kernel

private theorem row_024 : rowValid ⟨97, 6, 491270511⟩ := by
  decide +kernel

private theorem row_025 : rowValid ⟨101, 6, 456942627⟩ := by
  decide +kernel

private theorem row_026 : rowValid ⟨103, 6, 441150676⟩ := by
  decide +kernel

private theorem row_027 : rowValid ⟨107, 6, 411993374⟩ := by
  decide +kernel

private theorem row_028 : rowValid ⟨109, 6, 398517491⟩ := by
  decide +kernel

private theorem row_029 : rowValid ⟨113, 6, 373529380⟩ := by
  decide +kernel

private theorem row_030 : rowValid ⟨127, 6, 302723854⟩ := by
  decide +kernel

private theorem row_031 : rowValid ⟨131, 7, 286271130⟩ := by
  decide +kernel

private theorem row_032 : rowValid ⟨137, 7, 264060807⟩ := by
  decide +kernel

private theorem row_033 : rowValid ⟨139, 7, 257245019⟩ := by
  decide +kernel

private theorem row_034 : rowValid ⟨149, 7, 226915760⟩ := by
  decide +kernel

private theorem row_035 : rowValid ⟨151, 7, 221513460⟩ := by
  decide +kernel

private theorem row_036 : rowValid ⟨157, 7, 206444791⟩ := by
  decide +kernel

private theorem row_037 : rowValid ⟨163, 7, 192901243⟩ := by
  decide +kernel

private theorem row_038 : rowValid ⟨167, 7, 184618492⟩ := by
  decide +kernel

private theorem row_039 : rowValid ⟨173, 7, 173184958⟩ := by
  decide +kernel

private theorem row_040 : rowValid ⟨179, 7, 162807916⟩ := by
  decide +kernel

private theorem row_041 : rowValid ⟨181, 7, 159560990⟩ := by
  decide +kernel

private theorem row_042 : rowValid ⟨191, 7, 144730600⟩ := by
  decide +kernel

private theorem row_043 : rowValid ⟨193, 7, 142019922⟩ := by
  decide +kernel

private theorem row_044 : rowValid ⟨197, 7, 136828027⟩ := by
  decide +kernel

private theorem row_045 : rowValid ⟨199, 7, 134341020⟩ := by
  decide +kernel

private theorem row_046 : rowValid ⟨211, 7, 120782175⟩ := by
  decide +kernel

private theorem row_047 : rowValid ⟨223, 7, 109222555⟩ := by
  decide +kernel

private theorem row_048 : rowValid ⟨227, 7, 105745391⟩ := by
  decide +kernel

private theorem row_049 : rowValid ⟨229, 7, 104070368⟩ := by
  decide +kernel

private theorem row_050 : rowValid ⟨233, 7, 100840582⟩ := by
  decide +kernel

private theorem row_051 : rowValid ⟨239, 7, 96277620⟩ := by
  decide +kernel

private theorem row_052 : rowValid ⟨241, 7, 94827057⟩ := by
  decide +kernel

private theorem row_053 : rowValid ⟨251, 7, 88055028⟩ := by
  decide +kernel

private theorem row_054 : rowValid ⟨257, 8, 84342718⟩ := by
  decide +kernel

private theorem row_055 : rowValid ⟨263, 8, 80866022⟩ := by
  decide +kernel

private theorem row_056 : rowValid ⟨269, 8, 77605163⟩ := by
  decide +kernel

private theorem row_057 : rowValid ⟨271, 8, 76563057⟩ := by
  decide +kernel

private theorem row_058 : rowValid ⟨277, 8, 73562726⟩ := by
  decide +kernel

private theorem row_059 : rowValid ⟨281, 8, 71661855⟩ := by
  decide +kernel

private theorem row_060 : rowValid ⟨283, 8, 70739631⟩ := by
  decide +kernel

private theorem row_061 : rowValid ⟨293, 8, 66391284⟩ := by
  decide +kernel

private theorem row_062 : rowValid ⟨307, 8, 60961527⟩ := by
  decide +kernel

private theorem row_063 : rowValid ⟨311, 8, 59535245⟩ := by
  decide +kernel

private theorem row_064 : rowValid ⟨313, 8, 58841272⟩ := by
  decide +kernel

private theorem row_065 : rowValid ⟨317, 8, 57490135⟩ := by
  decide +kernel

private theorem row_066 : rowValid ⟨331, 8, 53118360⟩ := by
  decide +kernel

private theorem row_067 : rowValid ⟨337, 8, 51399631⟩ := by
  decide +kernel

private theorem row_068 : rowValid ⟨347, 8, 48719202⟩ := by
  decide +kernel

private theorem row_069 : rowValid ⟨349, 8, 48208938⟩ := by
  decide +kernel

private theorem row_070 : rowValid ⟨353, 8, 47212755⟩ := by
  decide +kernel

private theorem row_071 : rowValid ⟨359, 8, 45776773⟩ := by
  decide +kernel

private theorem row_072 : rowValid ⟨367, 8, 43964220⟩ := by
  decide +kernel

private theorem row_073 : rowValid ⟨373, 8, 42676198⟩ := by
  decide +kernel

private theorem row_074 : rowValid ⟨379, 8, 41445298⟩ := by
  decide +kernel

private theorem row_075 : rowValid ⟨383, 8, 40654758⟩ := by
  decide +kernel

private theorem row_076 : rowValid ⟨389, 8, 39511697⟩ := by
  decide +kernel

private theorem row_077 : rowValid ⟨397, 8, 38062847⟩ := by
  decide +kernel

private theorem row_078 : rowValid ⟨401, 8, 37368837⟩ := by
  decide +kernel

private theorem row_079 : rowValid ⟨409, 8, 36037893⟩ := by
  decide +kernel

private theorem row_080 : rowValid ⟨419, 8, 34474147⟩ := by
  decide +kernel

private theorem row_081 : rowValid ⟨421, 8, 34173922⟩ := by
  decide +kernel

private theorem row_082 : rowValid ⟨431, 8, 32731388⟩ := by
  decide +kernel

private theorem row_083 : rowValid ⟨433, 8, 32454120⟩ := by
  decide +kernel

private theorem row_084 : rowValid ⟨439, 8, 31643625⟩ := by
  decide +kernel

private theorem row_085 : rowValid ⟨443, 8, 31120445⟩ := by
  decide +kernel

private theorem row_086 : rowValid ⟨449, 8, 30360240⟩ := by
  decide +kernel

private theorem row_087 : rowValid ⟨457, 8, 29390205⟩ := by
  decide +kernel

private theorem row_088 : rowValid ⟨461, 8, 28922938⟩ := by
  decide +kernel

private theorem row_089 : rowValid ⟨463, 8, 28693572⟩ := by
  decide +kernel

private theorem row_090 : rowValid ⟨467, 8, 28243144⟩ := by
  decide +kernel

private theorem row_091 : rowValid ⟨479, 8, 26955131⟩ := by
  decide +kernel

private theorem row_092 : rowValid ⟨487, 8, 26145901⟩ := by
  decide +kernel

private theorem row_093 : rowValid ⟨491, 8, 25755203⟩ := by
  decide +kernel

private theorem row_094 : rowValid ⟨499, 8, 25000226⟩ := by
  decide +kernel

private theorem row_095 : rowValid ⟨503, 8, 24635416⟩ := by
  decide +kernel

private theorem row_096 : rowValid ⟨509, 8, 24103337⟩ := by
  decide +kernel

private theorem row_097 : rowValid ⟨521, 9, 23090766⟩ := by
  decide +kernel

private theorem row_098 : rowValid ⟨523, 9, 22928366⟩ := by
  decide +kernel

private theorem row_099 : rowValid ⟨541, 9, 21542478⟩ := by
  decide +kernel

private theorem row_100 : rowValid ⟨547, 9, 21108976⟩ := by
  decide +kernel

private theorem row_101 : rowValid ⟨557, 9, 20415656⟩ := by
  decide +kernel

private theorem row_102 : rowValid ⟨563, 9, 20016308⟩ := by
  decide +kernel

private theorem row_103 : rowValid ⟨569, 9, 19628829⟩ := by
  decide +kernel

private theorem row_104 : rowValid ⟨571, 9, 19502226⟩ := by
  decide +kernel

private theorem row_105 : rowValid ⟨577, 9, 19129846⟩ := by
  decide +kernel

private theorem row_106 : rowValid ⟨587, 9, 18533019⟩ := by
  decide +kernel

private theorem row_107 : rowValid ⟨593, 9, 18188536⟩ := by
  decide +kernel

private theorem row_108 : rowValid ⟨599, 9, 17853786⟩ := by
  decide +kernel

private theorem row_109 : rowValid ⟨601, 9, 17744302⟩ := by
  decide +kernel

private theorem row_110 : rowValid ⟨607, 9, 17421961⟩ := by
  decide +kernel

private theorem row_111 : rowValid ⟨613, 9, 17108523⟩ := by
  decide +kernel

private theorem row_112 : rowValid ⟨617, 9, 16904348⟩ := by
  decide +kernel

private theorem row_113 : rowValid ⟨619, 9, 16803659⟩ := by
  decide +kernel

private theorem row_114 : rowValid ⟨631, 9, 16218414⟩ := by
  decide +kernel

private theorem row_115 : rowValid ⟨641, 9, 15754265⟩ := by
  decide +kernel

private theorem row_116 : rowValid ⟨643, 9, 15663883⟩ := by
  decide +kernel

private theorem row_117 : rowValid ⟨647, 9, 15485490⟩ := by
  decide +kernel

private theorem row_118 : rowValid ⟨653, 9, 15223690⟩ := by
  decide +kernel

private theorem row_119 : rowValid ⟨659, 9, 14968622⟩ := by
  decide +kernel

private theorem row_120 : rowValid ⟨661, 9, 14885055⟩ := by
  decide +kernel

private theorem row_121 : rowValid ⟨673, 9, 14398362⟩ := by
  decide +kernel

private theorem row_122 : rowValid ⟨677, 9, 14241545⟩ := by
  decide +kernel

private theorem row_123 : rowValid ⟨683, 9, 14011187⟩ := by
  decide +kernel

private theorem row_124 : rowValid ⟨691, 9, 13712830⟩ := by
  decide +kernel

private theorem row_125 : rowValid ⟨701, 9, 13353389⟩ := by
  decide +kernel

private theorem row_126 : rowValid ⟨709, 9, 13076139⟩ := by
  decide +kernel

private theorem row_127 : rowValid ⟨719, 9, 12741818⟩ := by
  decide +kernel

private theorem row_128 : rowValid ⟨727, 9, 12483709⟩ := by
  decide +kernel

private theorem row_129 : rowValid ⟨733, 9, 12295354⟩ := by
  decide +kernel

private theorem row_130 : rowValid ⟨739, 9, 12111324⟩ := by
  decide +kernel

private theorem row_131 : rowValid ⟨743, 9, 11990975⟩ := by
  decide +kernel

private theorem row_132 : rowValid ⟨751, 9, 11755714⟩ := by
  decide +kernel

private theorem row_133 : rowValid ⟨757, 9, 11583883⟩ := by
  decide +kernel

private theorem row_134 : rowValid ⟨761, 9, 11471460⟩ := by
  decide +kernel

private theorem row_135 : rowValid ⟨769, 9, 11251577⟩ := by
  decide +kernel

private theorem row_136 : rowValid ⟨773, 9, 11144051⟩ := by
  decide +kernel

private theorem row_137 : rowValid ⟨787, 9, 10779862⟩ := by
  decide +kernel

private theorem row_138 : rowValid ⟨797, 9, 10530783⟩ := by
  decide +kernel

private theorem row_139 : rowValid ⟨809, 9, 10243363⟩ := by
  decide +kernel

private theorem row_140 : rowValid ⟨811, 9, 10196630⟩ := by
  decide +kernel

private theorem row_141 : rowValid ⟨821, 9, 9967802⟩ := by
  decide +kernel

private theorem row_142 : rowValid ⟨823, 9, 9922982⟩ := by
  decide +kernel

private theorem row_143 : rowValid ⟨827, 9, 9834263⟩ := by
  decide +kernel

private theorem row_144 : rowValid ⟨829, 9, 9790360⟩ := by
  decide +kernel

private theorem row_145 : rowValid ⟨839, 9, 9575286⟩ := by
  decide +kernel

private theorem row_146 : rowValid ⟨853, 9, 9286143⟩ := by
  decide +kernel

private theorem row_147 : rowValid ⟨857, 9, 9205987⟩ := by
  decide +kernel

private theorem row_148 : rowValid ⟨859, 9, 9166306⟩ := by
  decide +kernel

private theorem row_149 : rowValid ⟨863, 9, 9087728⟩ := by
  decide +kernel

private theorem row_150 : rowValid ⟨877, 9, 8820683⟩ := by
  decide +kernel

private theorem row_151 : rowValid ⟨881, 9, 8746592⟩ := by
  decide +kernel

private theorem row_152 : rowValid ⟨883, 9, 8709904⟩ := by
  decide +kernel

private theorem row_153 : rowValid ⟨887, 9, 8637232⟩ := by
  decide +kernel

private theorem row_154 : rowValid ⟨907, 9, 8287447⟩ := by
  decide +kernel

private theorem row_155 : rowValid ⟨911, 9, 8220098⟩ := by
  decide +kernel

private theorem row_156 : rowValid ⟨919, 9, 8087893⟩ := by
  decide +kernel

private theorem row_157 : rowValid ⟨929, 9, 7927171⟩ := by
  decide +kernel

private theorem row_158 : rowValid ⟨937, 9, 7802091⟩ := by
  decide +kernel

private theorem row_159 : rowValid ⟨941, 9, 7740683⟩ := by
  decide +kernel

private theorem row_160 : rowValid ⟨947, 9, 7649950⟩ := by
  decide +kernel

private theorem row_161 : rowValid ⟨953, 9, 7560838⟩ := by
  decide +kernel

private theorem row_162 : rowValid ⟨967, 9, 7358995⟩ := by
  decide +kernel

private theorem row_163 : rowValid ⟨971, 9, 7302841⟩ := by
  decide +kernel

private theorem row_164 : rowValid ⟨977, 9, 7219834⟩ := by
  decide +kernel

private theorem row_165 : rowValid ⟨983, 9, 7138265⟩ := by
  decide +kernel

private theorem row_166 : rowValid ⟨991, 9, 7031684⟩ := by
  decide +kernel

private theorem row_167 : rowValid ⟨997, 9, 6953341⟩ := by
  decide +kernel

private theorem all_rows_valid : List.Forall rowValid rows := by
  exact ⟨row_000, row_001, row_002, row_003, row_004, row_005, row_006, row_007, row_008, row_009, row_010, row_011, row_012, row_013, row_014, row_015, row_016, row_017, row_018, row_019, row_020, row_021, row_022, row_023, row_024, row_025, row_026, row_027, row_028, row_029, row_030, row_031, row_032, row_033, row_034, row_035, row_036, row_037, row_038, row_039, row_040, row_041, row_042, row_043, row_044, row_045, row_046, row_047, row_048, row_049, row_050, row_051, row_052, row_053, row_054, row_055, row_056, row_057, row_058, row_059, row_060, row_061, row_062, row_063, row_064, row_065, row_066, row_067, row_068, row_069, row_070, row_071, row_072, row_073, row_074, row_075, row_076, row_077, row_078, row_079, row_080, row_081, row_082, row_083, row_084, row_085, row_086, row_087, row_088, row_089, row_090, row_091, row_092, row_093, row_094, row_095, row_096, row_097, row_098, row_099, row_100, row_101, row_102, row_103, row_104, row_105, row_106, row_107, row_108, row_109, row_110, row_111, row_112, row_113, row_114, row_115, row_116, row_117, row_118, row_119, row_120, row_121, row_122, row_123, row_124, row_125, row_126, row_127, row_128, row_129, row_130, row_131, row_132, row_133, row_134, row_135, row_136, row_137, row_138, row_139, row_140, row_141, row_142, row_143, row_144, row_145, row_146, row_147, row_148, row_149, row_150, row_151, row_152, row_153, row_154, row_155, row_156, row_157, row_158, row_159, row_160, row_161, row_162, row_163, row_164, row_165, row_166, row_167⟩

private def listed : List ℕ := rows.map LogRow.prime
private def smallDivisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

private theorem listed_nodup : listed.Nodup := by decide +kernel

private theorem checked_coverage :
    ∀ n : Fin 1001, 2 ≤ n.val → n.val ∈ listed ∨
      (smallDivisors.any (fun d => decide (2 ≤ d ∧ d < n.val ∧ n.val % d = 0))) = true := by
  decide +kernel

private theorem prime_mem_listed (p : ℕ) (hp : p.Prime) (hbound : p ≤ 1000) :
    p ∈ listed := by
  have hc := checked_coverage ⟨p, by omega⟩ hp.two_le
  rcases hc with hc | hc
  · exact hc
  · obtain ⟨d, _, hd⟩ := List.any_eq_true.mp hc
    have hdiv : 2 ≤ d ∧ d < p ∧ p % d = 0 := of_decide_eq_true hd
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hdiv.2.2) with he | he
    · omega
    · omega

private theorem rounded_sum_checked : (rows.map LogRow.rounded).sum ≤ 754400000000 := by
  decide +kernel

private theorem listed_weight_sum_le :
    (listed.map logWeight).sum ≤ (943 : ℝ) / 1250 := by
  have h := rows_sum_le rows all_rows_valid
  have hc : (((rows.map LogRow.rounded).sum : ℕ) : ℝ) ≤ 754400000000 := by
    exact_mod_cast rounded_sum_checked
  have hb : (((rows.map LogRow.rounded).sum : ℕ) : ℝ) / (scale : ℝ) ≤
      (943 : ℝ) / 1250 := by
    calc
      (((rows.map LogRow.rounded).sum : ℕ) : ℝ) / (scale : ℝ) ≤
          754400000000 / (scale : ℝ) :=
        div_le_div_of_nonneg_right hc (Nat.cast_nonneg scale)
      _ = (943 : ℝ) / 1250 := by norm_num [scale]
  simpa only [listed, List.map_map, Function.comp_def] using h.trans hb

/-- The finite prime logarithmic moment through 1000, with no numerical-bound premise. -/
theorem finite_prime_log_sum_le :
    (∑ p ∈ (Finset.range 1001).filter Nat.Prime,
      Real.log (p : ℝ) / ((p * (p - 1) : ℕ) : ℝ)) ≤ (943 : ℝ) / 1250 := by
  have hsubset : (Finset.range 1001).filter Nat.Prime ⊆ listed.toFinset := by
    intro p hp
    obtain ⟨hrange, hprime⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr
      (prime_mem_listed p hprime (by have := Finset.mem_range.mp hrange; omega))
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := logWeight) hsubset
    (fun p _ _ => logWeight_nonneg p)
  rw [List.sum_toFinset logWeight listed_nodup] at hs
  exact hs.trans listed_weight_sum_le

/-- The logarithm constant needed for the Chebyshev tail specialization. -/
theorem log_four_le : Real.log 4 ≤ (7 : ℝ) / 5 := by
  have h := log_le_upperNat 4 2 9 (by decide +kernel)
  have hc : logUpperNat 4 2 9 ≤ (7 : ℚ) / 5 := by decide +kernel
  have hcr : (logUpperNat 4 2 9 : ℝ) ≤ (7 : ℝ) / 5 := by
    have hcR := (Rat.cast_le (K := ℝ)).2 hc
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcR
  simpa only [Nat.cast_ofNat] using h.trans hcr

end RamareFiniteConstants
-- END COMPONENT FinitePrimeLogSum.lean

-- BEGIN COMPONENT GammaCertificate.lean
namespace RamareFiniteConstants

/-- A rational lower bound from the nonnegative odd-power logarithm series. -/
private def logLower (x : ℚ) (terms : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range terms,
    ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

private theorem logLower_le (x : ℚ) (hx : 1 ≤ x) (terms : ℕ) :
    (logLower x terms : ℝ) ≤ Real.log (x : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div hnonneg hlt terms
  rw [hratio] at h
  unfold logLower
  push_cast
  linarith

/-- Range reduction keeps the logarithm-series argument at most one third
when `2^k ≤ N ≤ 2^(k+1)`. Only the lower inequality is needed for soundness. -/
private def logLowerNat (N k terms : ℕ) : ℚ :=
  (k : ℚ) * logLower 2 terms + logLower ((N : ℚ) / 2 ^ k) terms

private theorem logLowerNat_le (N k terms : ℕ) (hN : 2 ^ k ≤ N) :
    (logLowerNat N k terms : ℝ) ≤ Real.log (N : ℝ) := by
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have hpowR : (0 : ℝ) < 2 ^ k := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hratio : (1 : ℚ) ≤ (N : ℚ) / 2 ^ k := by
    apply (le_div_iff₀ hpow).2
    simpa using (show (2 : ℚ) ^ k ≤ N by exact_mod_cast hN)
  have htwo := logLower_le 2 (by norm_num) terms
  norm_num at htwo
  have hrest := logLower_le ((N : ℚ) / 2 ^ k) hratio terms
  have hmult := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ k by positivity)
  have hid : (2 : ℝ) ^ k * ((N : ℝ) / 2 ^ k) = N := by
    field_simp
  have hlog := Real.log_mul hpowR.ne' (div_pos hNposR hpowR).ne'
  rw [hid, Real.log_pow] at hlog
  unfold logLowerNat
  push_cast at hrest ⊢
  linarith


private theorem gamma_rational_certificate :
    harmonic 100 - logLowerNat 100 6 9 ≤ (233 : ℚ) / 400 := by
  decide +kernel

/-- A finite harmonic/logarithm certificate for Euler's constant. -/
theorem euler_mascheroni_le : Real.eulerMascheroniConstant ≤ (233 : ℝ) / 400 := by
  have hlog : (logLowerNat 100 6 9 : ℝ) ≤ Real.log (100 : ℝ) := by
    simpa only [Nat.cast_ofNat] using logLowerNat_le 100 6 9 (by decide +kernel)
  have hrat : (harmonic 100 : ℝ) - (logLowerNat 100 6 9 : ℝ) ≤
      (233 : ℝ) / 400 := by
    have hcR := (Rat.cast_le (K := ℝ)).2 gamma_rational_certificate
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] using hcR
  have hgamma : Real.eulerMascheroniConstant <
      (harmonic 100 : ℝ) - Real.log (100 : ℝ) := by
    simpa only [Real.eulerMascheroniSeq', show (100 : ℕ) ≠ 0 by decide,
      if_false, Nat.cast_ofNat] using Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 100
  exact hgamma.le.trans ((sub_le_sub_left hlog (harmonic 100 : ℝ)).trans hrat)

end RamareFiniteConstants
-- END COMPONENT GammaCertificate.lean

-- BEGIN COMPONENT PrimeLogTail.lean
namespace RamareAnalytic


private noncomputable def reciprocalQuadratic (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * ((n : ℝ) - 1))

private noncomputable def reciprocalPair (n : ℕ) : ℝ :=
  1 / ((n : ℝ) - 1) + 1 / (n : ℝ)

private theorem reciprocalQuadratic_nonneg (n : ℕ) :
    0 ≤ reciprocalQuadratic n := by
  by_cases hn : n = 0
  · simp [hn, reciprocalQuadratic]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1))

private theorem reciprocalQuadratic_drop (n : ℕ) (hn : 2 ≤ n) :
    reciprocalQuadratic n - reciprocalQuadratic (n + 1) =
      2 / (((n : ℝ) - 1) * (n : ℝ) * ((n : ℝ) + 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hm0 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (n : ℝ) + 1 ≠ 0 := by linarith
  simp only [reciprocalQuadratic, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  field_simp
  <;> ring

private theorem reciprocalQuadratic_drop_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ reciprocalQuadratic n - reciprocalQuadratic (n + 1) := by
  rw [reciprocalQuadratic_drop n hn]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 0 ≤ (n : ℝ) - 1 := by linarith
  positivity

private theorem reciprocalQuadratic_telescope (n : ℕ) (hn : 2 ≤ n) :
    (reciprocalQuadratic n - reciprocalQuadratic (n + 1)) * (n : ℝ) =
      reciprocalPair n - reciprocalPair (n + 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hm0 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (n : ℝ) + 1 ≠ 0 := by linarith
  simp only [reciprocalQuadratic, reciprocalPair, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right]
  field_simp
  <;> ring

private theorem reciprocalPair_sum (X N : ℕ) (hXN : X + 1 ≤ N) :
    (∑ i ∈ Finset.Ico (X + 1) N,
      (reciprocalPair i - reciprocalPair (i + 1))) =
      reciprocalPair (X + 1) - reciprocalPair N := by
  calc
    (∑ i ∈ Finset.Ico (X + 1) N,
        (reciprocalPair i - reciprocalPair (i + 1))) =
        -(∑ i ∈ Finset.Ico (X + 1) N,
          (reciprocalPair (i + 1) - reciprocalPair i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = reciprocalPair (X + 1) - reciprocalPair N := by
      rw [Finset.sum_Ico_sub reciprocalPair hXN]
      ring

/-- Discrete Abel bound for a sequence vanishing up to X with linear prefix control. -/
private theorem weighted_partial_sum_le
    (a : ℕ → ℝ) (A : ℝ) (X : ℕ) (hA : 0 ≤ A) (hX : 1 ≤ X)
    (hzero : ∀ i, i ≤ X → a i = 0)
    (hprefix : ∀ N, (∑ i ∈ Finset.range (N + 1), a i) ≤ A * (N : ℝ))
    (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i) ≤
      A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
  have hC : 0 ≤ A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
    positivity
  by_cases hNX : N ≤ X
  · have hz : (∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (by have := Finset.mem_range.mp hi; omega), mul_zero]
    simpa only [hz] using hC
  · have hXN : X + 1 ≤ N := by omega
    have hN2 : 2 ≤ N := by omega
    have hGzero : (∑ i ∈ Finset.range (X + 1), a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hzero i (by have := Finset.mem_range.mp hi; omega)
    have hWzero : (∑ i ∈ Finset.range (X + 1), reciprocalQuadratic i * a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (by have := Finset.mem_range.mp hi; omega), mul_zero]
    have hIco : (∑ i ∈ Finset.Ico (X + 1) (N + 1), reciprocalQuadratic i * a i) =
        ∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i := by
      rw [Finset.sum_Ico_eq_sub _ (by omega), hWzero, sub_zero]
    have hAbel := Finset.sum_Ico_by_parts reciprocalQuadratic a
      (show X + 1 < N + 1 by omega)
    simp only [smul_eq_mul, Nat.add_sub_cancel, hGzero, mul_zero, sub_zero, hIco] at hAbel
    have hAbel' : (∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i) =
        reciprocalQuadratic N * (∑ i ∈ Finset.range (N + 1), a i) +
        ∑ i ∈ Finset.Ico (X + 1) N,
          (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) *
            (∑ j ∈ Finset.range (i + 1), a j) := by
      rw [hAbel, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hcorrection :
        (∑ i ∈ Finset.Ico (X + 1) N,
          (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) *
            (∑ j ∈ Finset.range (i + 1), a j)) ≤
        A * (reciprocalPair (X + 1) - reciprocalPair N) := by
      calc
        _ ≤ ∑ i ∈ Finset.Ico (X + 1) N,
            (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) * (A * (i : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi2 : 2 ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
          exact mul_le_mul_of_nonneg_left (hprefix i)
            (reciprocalQuadratic_drop_nonneg i hi2)
        _ = A * ∑ i ∈ Finset.Ico (X + 1) N,
            (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) * (i : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = A * ∑ i ∈ Finset.Ico (X + 1) N,
            (reciprocalPair i - reciprocalPair (i + 1)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact reciprocalQuadratic_telescope i
            (by have := (Finset.mem_Ico.mp hi).1; omega)
        _ = _ := by rw [reciprocalPair_sum X N hXN]
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hN0 : (N : ℝ) ≠ 0 := by linarith
    have hNm0 : (N : ℝ) - 1 ≠ 0 := by linarith
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
    have hXp0 : (X : ℝ) + 1 ≠ 0 := by positivity
    calc
      _ = _ := hAbel'
      _ ≤ reciprocalQuadratic N * (A * (N : ℝ)) +
          A * (reciprocalPair (X + 1) - reciprocalPair N) :=
        add_le_add (mul_le_mul_of_nonneg_left (hprefix N)
          (reciprocalQuadratic_nonneg N)) hcorrection
      _ = A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) - A / (N : ℝ) := by
        simp only [reciprocalQuadratic, reciprocalPair, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_right]
        field_simp
        <;> ring
      _ ≤ _ := sub_le_self _ (div_nonneg hA (Nat.cast_nonneg N))

/-- A bounded-prefix argument establishes convergence before taking the infinite bound. -/
theorem summable_weighted_tail_of_prefix_le
    (a : ℕ → ℝ) (A : ℝ) (X : ℕ) (hA : 0 ≤ A) (hX : 1 ≤ X)
    (ha : ∀ i, 0 ≤ a i) (hzero : ∀ i, i ≤ X → a i = 0)
    (hprefix : ∀ N, (∑ i ∈ Finset.range (N + 1), a i) ≤ A * (N : ℝ)) :
    Summable (fun i => a i / ((i : ℝ) * ((i : ℝ) - 1))) ∧
      (∑' i, a i / ((i : ℝ) * ((i : ℝ) - 1))) ≤
        A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
  have hpos : ∀ i, 0 ≤ reciprocalQuadratic i * a i :=
    fun i => mul_nonneg (reciprocalQuadratic_nonneg i) (ha i)
  have hbound : ∀ N, (∑ i ∈ Finset.range N, reciprocalQuadratic i * a i) ≤
      A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
    intro N
    cases N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
    | succ N => exact weighted_partial_sum_le a A X hA hX hzero hprefix N
  have hs := summable_of_sum_range_le hpos hbound
  have hb := Real.tsum_le_of_sum_range_le hpos hbound
  simpa only [reciprocalQuadratic, div_eq_mul_inv, one_mul, mul_comm] using And.intro hs hb

noncomputable def primeLogAfter (X n : ℕ) : ℝ :=
  if X < n ∧ n.Prime then Real.log (n : ℝ) else 0

theorem primeLogAfter_nonneg (X n : ℕ) : 0 ≤ primeLogAfter X n := by
  unfold primeLogAfter
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.2.one_lt.le)
  · exact le_rfl

theorem primeLogAfter_prefix_le (X N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), primeLogAfter X i) ≤ Real.log 4 * (N : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (N + 1), if i.Prime then Real.log (i : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hp : i.Prime
      · have hlog : 0 ≤ Real.log (i : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
        by_cases hXi : X < i <;> simp [primeLogAfter, hXi, hp, hlog]
      · simp [primeLogAfter, hp]
    _ = Chebyshev.theta (N : ℝ) := by
      rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
        ← Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
    _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)

/-- The exact prime logarithmic-moment tail needed for Ramare's constant. -/
theorem prime_log_moment_tail (X : ℕ) (hX : 1 ≤ X) :
    Summable (fun p : ℕ =>
      if X < p ∧ p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
    (∑' p : ℕ, if X < p ∧ p.Prime then
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤
      Real.log 4 * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
  have h := summable_weighted_tail_of_prefix_le
    (primeLogAfter X) (Real.log 4) X (Real.log_nonneg (by norm_num)) hX
    (primeLogAfter_nonneg X)
    (fun i hi => by simp [primeLogAfter, not_lt_of_ge hi])
    (primeLogAfter_prefix_le X)
  simpa only [primeLogAfter, ite_div, zero_div] using h

/-- Rational specialization; the remaining log(4) premise has an independent finite certificate. -/
theorem prime_log_moment_tail_1000 (hlog4 : Real.log 4 ≤ (7 / 5 : ℝ)) :
    (∑' p : ℕ, if 1000 < p ∧ p.Prime then
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤ (14 / 4995 : ℝ) := by
  have h := (prime_log_moment_tail 1000 (by omega)).2
  calc
    _ ≤ Real.log 4 * (1 / (1000 : ℝ) + 1 / ((1000 : ℝ) + 1)) := h
    _ ≤ (7 / 5 : ℝ) * (1 / (1000 : ℝ) + 1 / ((1000 : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hlog4 (by norm_num)
    _ ≤ _ := by norm_num

end RamareAnalytic
-- END COMPONENT PrimeLogTail.lean

-- BEGIN COMPONENT GlobalLogConstant.lean
namespace RamareAnalytic

private noncomputable def globalLogTerm (p : ℕ) : ℝ :=
  if p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0

private noncomputable def smallLogTerm (p : ℕ) : ℝ :=
  if p < 1001 then globalLogTerm p else 0

private noncomputable def tailLogTerm (p : ℕ) : ℝ :=
  if 1000 < p ∧ p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0

private theorem logTerm_split (p : ℕ) :
    globalLogTerm p = smallLogTerm p + tailLogTerm p := by
  by_cases hp : p.Prime
  · by_cases hcut : p < 1001
    · have htail : ¬ 1000 < p := by omega
      simp [globalLogTerm, smallLogTerm, tailLogTerm, hp, hcut, htail]
    · have htail : 1000 < p := by omega
      simp [globalLogTerm, smallLogTerm, tailLogTerm, hp, hcut, htail]
  · simp [globalLogTerm, smallLogTerm, tailLogTerm, hp]

private theorem smallLogTerm_sum :
    (∑ p ∈ Finset.range 1001, smallLogTerm p) =
      ∑ p ∈ (Finset.range 1001).filter Nat.Prime,
        Real.log (p : ℝ) / ((p * (p - 1) : ℕ) : ℝ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hcut : p < 1001 := Finset.mem_range.mp hp
  by_cases hprime : p.Prime
  · have hden : ((p * (p - 1) : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hprime.one_lt.le, Nat.cast_one]
    simp only [smallLogTerm, hcut, if_true, globalLogTerm, hprime, hden]
  · simp [smallLogTerm, globalLogTerm, hcut, hprime]

private theorem smallLogTerm_hasSum :
    HasSum smallLogTerm
      (∑ p ∈ (Finset.range 1001).filter Nat.Prime,
        Real.log (p : ℝ) / ((p * (p - 1) : ℕ) : ℝ)) := by
  have h : HasSum smallLogTerm (∑ p ∈ Finset.range 1001, smallLogTerm p) := by
    apply hasSum_sum_of_ne_finset_zero
    intro p hp
    have hcut : ¬ p < 1001 := by simpa only [Finset.mem_range] using hp
    simp only [smallLogTerm, hcut, if_false]
  rw [smallLogTerm_sum] at h
  exact h

/-- Assembly from four explicit component certificates. This statement proves
global summability as well as the bound; it does not assume the global bound. -/
theorem global_log_constant_of_certificates
    (hfinite :
      (∑ p ∈ (Finset.range 1001).filter Nat.Prime,
        Real.log (p : ℝ) / ((p * (p - 1) : ℕ) : ℝ)) ≤ (943 : ℝ) / 1250)
    (hgamma : Real.eulerMascheroniConstant ≤ (233 : ℝ) / 400)
    (hlog4 : Real.log 4 ≤ (7 : ℝ) / 5)
    (htail : ∀ (X : ℕ), 1 ≤ X →
      Summable (fun p : ℕ =>
        if X < p ∧ p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
      (∑' p : ℕ, if X < p ∧ p.Prime then
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤
        Real.log 4 * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1))) :
    Summable (fun p : ℕ =>
      if p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
      Real.eulerMascheroniConstant +
        (∑' p : ℕ, if p.Prime then
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤ (67 : ℝ) / 50 := by
  have ht := htail 1000 (by norm_num)
  have htailHas : HasSum tailLogTerm (∑' p, tailLogTerm p) := ht.1.hasSum
  have hfull : HasSum globalLogTerm
      ((∑ p ∈ (Finset.range 1001).filter Nat.Prime,
        Real.log (p : ℝ) / ((p * (p - 1) : ℕ) : ℝ)) +
          (∑' p, tailLogTerm p)) := by
    apply (smallLogTerm_hasSum.add htailHas).congr_fun
    exact logTerm_split
  have htailBound : (∑' p, tailLogTerm p) ≤ (14 : ℝ) / 4995 := by
    calc
      _ ≤ Real.log 4 * (1 / (1000 : ℝ) + 1 / ((1000 : ℝ) + 1)) := ht.2
      _ ≤ (7 : ℝ) / 5 * (1 / (1000 : ℝ) + 1 / ((1000 : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hlog4 (by norm_num)
      _ ≤ (14 : ℝ) / 4995 := by norm_num
  constructor
  · exact hfull.summable
  · change Real.eulerMascheroniConstant + (∑' p, globalLogTerm p) ≤ (67 : ℝ) / 50
    rw [hfull.tsum_eq]
    calc
      _ ≤ (233 : ℝ) / 400 + ((943 : ℝ) / 1250 + (14 : ℝ) / 4995) :=
        add_le_add hgamma (add_le_add hfinite htailBound)
      _ ≤ (67 : ℝ) / 50 := by norm_num

end RamareAnalytic
-- END COMPONENT GlobalLogConstant.lean

theorem solution :
    Summable (fun p : ℕ =>
      if p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
      Real.eulerMascheroniConstant +
        (∑' p : ℕ, if p.Prime then
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤ (67 : ℝ) / 50 := by
  exact RamareAnalytic.global_log_constant_of_certificates
    RamareFiniteConstants.finite_prime_log_sum_le
    RamareFiniteConstants.euler_mascheroni_le
    RamareFiniteConstants.log_four_le
    RamareAnalytic.prime_log_moment_tail

#print axioms solution
