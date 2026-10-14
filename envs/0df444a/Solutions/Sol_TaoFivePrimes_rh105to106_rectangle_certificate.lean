-- Prove2me | solution 1 for TaoFivePrimes.rh105to106_rectangle_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T05:16:44.32038+00:00
-- url     : https://prove2.me/submissions/def57d6f-d08d-4246-b77a-98383e27ad52

import Mathlib
import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH105To106RoundedCoefficients
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.ambiguousOpen false
namespace RH106Proof
section Height100Module0

open Finset
namespace CertifiedPackedConvolution

end CertifiedPackedConvolution

end Height100Module0

section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution

end CertifiedMomentConvolution

end Height100Module1

section Height100Module2

open Complex MeasureTheory Finset Metric Set

namespace CertifiedTaylorQuadrature

end CertifiedTaylorQuadrature

end Height100Module2

section Height100Module3

set_option autoImplicit false
open Complex Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module3

section Height100Module4

open Complex Finset
namespace CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedExponentialJets

end Height100Module4

section Height100Module5

open Complex Finset
namespace CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedIntegerExponentialJets

end Height100Module5

section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets

end CertifiedSignedODEConvolution

end Height100Module6

section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

end CertifiedListODEVectors

end Height100Module7

section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedPackedConvolution

end CertifiedPackedHorner

namespace CertifiedPackedHorner

end CertifiedPackedHorner

end Height100Module8

section Height100Module9

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaSix

end ZetaSix

end Height100Module9

section Height100Module10

open Real MeasureTheory Set HurwitzZeta HurwitzKernelBounds

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module10

section Height100Module11

open Real MeasureTheory Set Filter
open scoped Topology

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module11

section Height100Module12

open Real MeasureTheory Set Filter Finset HurwitzZeta HurwitzKernelBounds

namespace CertifiedZetaQuadrature
open TaoZetaBounds

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Complex Finset Metric

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

open Real MeasureTheory Set Filter HurwitzZeta
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Complex MeasureTheory Metric Set Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Real MeasureTheory Set Filter Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module16

section Height100Module17

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256
open ZetaSix

end TaoZetaWide256

end Height100Module17

section Height100Module18

open Complex Finset Metric
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

end TaoZetaGlobal

end Height100Module18

section Height100Module19

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module19

section Height100Module20

open Complex MeasureTheory Set HurwitzZeta
set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module20

section Height100Module21

open Complex MeasureTheory Set
open scoped ComplexConjugate
set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module21

section Height100Module22

open Complex Finset Metric Filter
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false

namespace TaoZetaWide
open ZetaSix

end TaoZetaWide

end Height100Module23

section Height100Module24

open Complex Metric TaoZetaCertificate
namespace CertifiedLocalXi

noncomputable def center (T : ℝ) : ℂ := 1/2+(T:ℂ)*I

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Complex MeasureTheory Set Finset
namespace CertifiedGlobalMoments
open CertifiedZetaQuadrature TaoZetaCertificate

end CertifiedGlobalMoments

end Height100Module25

section Height100Module26

open Complex Finset
namespace CertifiedEvenPolynomial

end CertifiedEvenPolynomial

end Height100Module26

section Height100Module27

open Complex Metric Set
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module27

section Height100Module28

open Complex Metric
open scoped ComplexConjugate
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Complex Finset
namespace CertifiedLocalXi

noncomputable def rotatedVariable (T : ℝ) (z : ℂ) : ℂ := -I*(z-center T)
noncomputable def rotatedPolynomial (b : ℕ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ range 40, (b n : ℂ)*rotatedVariable T z^n

end CertifiedLocalXi

end Height100Module29

section Height100Module30

open Complex Finset
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module30

section Height100Module31

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

end CertifiedPolynomialTranslation

end Height100Module32

section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open Complex Finset CertifiedPolynomialTranslation

end CertifiedDenseGlobalPolynomial

end Height100Module33

section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module34

section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module35

section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module36

section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module37

section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module38

section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module39

section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi

end CertifiedThetaPoints

end Height100Module40

section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module41

section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint

end CertifiedThetaCandidates

end Height100Module42

section Height100Module43

namespace CertifiedStreamingODE
open CertifiedSignedODEConvolution

end CertifiedStreamingODE

end Height100Module43

section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE

end CertifiedJetRecords

end Height100Module44

section Height100Module45
namespace CertifiedJetRecords
end CertifiedJetRecords
end Height100Module45

section Height100Module46

end Height100Module46

section Height100Module47

namespace CertifiedJetRecords

end CertifiedJetRecords

end Height100Module47

section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets

end CertifiedJetRecords

end Height100Module48

section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module49

section Height100Module50

open Complex Metric Real
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Complex Metric Finset
namespace CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Complex Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedZetaQuadrature

end Height100Module52

section Height100Module53

open Complex Finset
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedJetRecords

end Height100Module53

section Height100Module54

open Complex Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module54

section Height100Module55

open Complex Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

end CertifiedMomentConvolution

end Height100Module55

section Height100Module56

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
open Complex Metric MeasureTheory
namespace CertifiedZetaQuadrature
end CertifiedZetaQuadrature

end Height100Module58

section Height100Module59

open Complex MeasureTheory Finset
namespace CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature

end CertifiedGlobalQuadrature

end Height100Module59

section Height100Module60

open Complex Finset
namespace CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Complex Metric Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution
set_option exponentiation.threshold 1024

end CertifiedZetaQuadrature

end Height100Module61

section Height100Module62

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset Complex
open scoped BigOperators

namespace CertifiedGlobalJetCenters
open CertifiedJetRecords CertifiedThetaPoints CertifiedFixedPoint
open CertifiedMomentConvolution CertifiedZetaQuadrature

end CertifiedGlobalJetCenters

end Height100Module62

section Height100Module63

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedPackedCorrelation
open CertifiedSignedODEConvolution CertifiedListODEVectors CertifiedPackedConvolution

end CertifiedPackedCorrelation

end Height100Module63

section Height100Module64

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentWeights
open CertifiedMomentConvolution

end CertifiedMomentWeights

end Height100Module64

section Height100Module65

namespace CertifiedExponentialIntegerSequence

end CertifiedExponentialIntegerSequence

end Height100Module65

section Height100Module66

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Finset
open scoped BigOperators
namespace CertifiedMomentArithmetic
open CertifiedFixedPoint CertifiedExponentialIntegerSequence
open CertifiedMomentConvolution

end CertifiedMomentArithmetic

end Height100Module66

section Height100Module67

set_option autoImplicit false
namespace CertifiedPackedExtraction
open CertifiedSignedODEConvolution

end CertifiedPackedExtraction

end Height100Module67

section Height100Module68

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentRecords
open CertifiedGlobalJetCenters CertifiedThetaCandidates CertifiedThetaPoints
open CertifiedJetRecords CertifiedFixedPoint CertifiedPackedConvolution
open CertifiedMomentArithmetic CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentRecords

end Height100Module68

section Height100Module69

namespace CertifiedExponentialSequenceCheck
open CertifiedExponentialIntegerSequence

end CertifiedExponentialSequenceCheck

end Height100Module69

section Height100Module70

namespace CertifiedPackedExponentialSequence
open CertifiedPackedConvolution CertifiedExponentialSequenceCheck

end CertifiedPackedExponentialSequence

end Height100Module70

section Height100Module71

namespace CertifiedChunkedExponentialSequence
open CertifiedPackedConvolution CertifiedPackedExponentialSequence

end CertifiedChunkedExponentialSequence

end Height100Module71

section Height100Module72

namespace CertifiedChunkedEncoding
open CertifiedPackedConvolution CertifiedPackedExponentialSequence
open CertifiedChunkedExponentialSequence

end CertifiedChunkedEncoding

end Height100Module72

section Height100Module73

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentSequenceCache
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedPackedConvolution
open CertifiedExponentialIntegerSequence CertifiedExponentialSequenceCheck
open CertifiedChunkedEncoding CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentSequenceCache

end Height100Module73

section Height100Module76

end Height100Module76

section Height100Module77
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLocalCandidates

end CertifiedLocalCandidates

end Height100Module77

section Height100Module78

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedGlobalTranslation
open CertifiedMomentRecords CertifiedPackedHorner CertifiedSignedODEConvolution
open CertifiedPackedExtraction CertifiedListODEVectors

end CertifiedGlobalTranslation

end Height100Module78

section Height100Module79

open Finset
namespace CertifiedPolynomialTranslation

end CertifiedPolynomialTranslation

end Height100Module79

section Height100Module80

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000
namespace CertifiedTranslationConvolution
open CertifiedGlobalTranslation CertifiedPackedConvolution CertifiedListODEVectors
open CertifiedExponentialIntegerSequence CertifiedPackedExtraction

end CertifiedTranslationConvolution

end Height100Module80

section Height100Module81

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedPackedTranslation

end Height100Module81

section Height100Module82

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedLiteralTranslation

end Height100Module82

section Height100Module83
namespace CertifiedLiteralTranslation
end CertifiedLiteralTranslation
end Height100Module83

section Height100Module84

namespace CertifiedExponentialSequenceBound
open CertifiedExponentialSequenceCheck CertifiedPackedExponentialSequence
open CertifiedPackedConvolution
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

end CertifiedExponentialSequenceBound

end Height100Module84

section Height100Module85

set_option autoImplicit false
open Complex Finset
namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

end Height100Module85

section Height100Module86

set_option autoImplicit false
open Finset Complex
namespace CertifiedTranslationAlgebra
open CertifiedPolynomialTranslation CertifiedPackedHorner CertifiedListODEVectors
open CertifiedPackedCorrelation CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

namespace CertifiedTranslationAlgebra
open CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

end Height100Module86

section Height100Module87

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset Complex
namespace CertifiedMomentRecords
open CertifiedPackedCorrelation CertifiedMomentArithmetic CertifiedMomentConvolution
open CertifiedListODEVectors CertifiedPackedExtraction CertifiedSignedODEConvolution
open CertifiedGlobalJetCenters CertifiedFixedPoint CertifiedPackedConvolution

end CertifiedMomentRecords

end Height100Module87

section Height100Module88

set_option autoImplicit false
namespace CertifiedIntegerRounding

end CertifiedIntegerRounding

end Height100Module88

section Height100Module89
namespace CertifiedGlobalMomentEnclosure
end CertifiedGlobalMomentEnclosure
end Height100Module89

section Height100Module90

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset
namespace CertifiedGlobalTranslation
open CertifiedPackedHorner CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedGlobalTranslation

end Height100Module90

section Height100Module91

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTranslationAlgebra CertifiedPackedExponentialSequence

end CertifiedPackedTranslation

end Height100Module91

section Height100Module92

namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation CertifiedPolynomialTranslation

end CertifiedPackedTranslation

end Height100Module92

section Height100Module93

set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction

end CertifiedLiteralTranslation

end Height100Module93

section Height100Module94

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaPoly

end TaoZetaPoly

end Height100Module94

section Height100Module95

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module95

section Height100Module96

namespace CertifiedIntegerLocalPolynomial
open Complex Finset

end CertifiedIntegerLocalPolynomial

end Height100Module96

section Height100Module97

open Finset Polynomial
open scoped unitInterval
set_option autoImplicit false

namespace TaoZetaNumerics

lemma bernstein_lower_bound (n : ℕ) (c : Fin (n + 1) → ℝ) (L : ℝ)
    (hc : ∀ i, L ≤  c i) (x : I) :
    L ≤  ∑ i : Fin (n + 1), c i * bernstein n i x := by
  calc
    L = ∑ i : Fin (n + 1), L * bernstein n i x := by
      rw [← Finset.mul_sum, bernstein.probability, mul_one]
    _ ≤  ∑ i : Fin (n + 1), c i * bernstein n i x := by
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) bernstein_nonneg

lemma bernstein_lower_bound_two (m n : ℕ) (c : Fin (m + 1) → Fin (n + 1) → ℝ)
    (L : ℝ) (hc : ∀ i j, L ≤  c i j) (x y : I) :
    L ≤  ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
      c i j * bernstein m i x * bernstein n j y := by
  have h := bernstein_lower_bound m
    (fun i => ∑ j : Fin (n + 1), c i j * bernstein n j y) L
    (fun i => bernstein_lower_bound n (c i) L (hc i) y) x
  convert h using 1
  apply sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  ring

end TaoZetaNumerics

end Height100Module97

section Height100Module98

open Finset
open scoped unitInterval
set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaNumerics

noncomputable def bernsteinValue (n i : ℕ) (x : ℝ) : ℝ :=
  (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)

lemma monomial_bernstein (n j : ℕ) (hj : j ≤  n) (x : ℝ) :
    x ^ j = ∑ i ∈ range (n + 1),
      ((i.choose j : ℝ) / n.choose j) * bernsteinValue n i x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hnz : ((j + m).choose j : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.le_add_right j m)
  have hsum0 : (∑ i ∈ range j,
      ((i.choose j : ℝ) / (j + m).choose j) * bernsteinValue (j + m) i x) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]
  have hshift : j + m + 1 = j + (m + 1) := by omega
  rw [hshift, Finset.sum_range_add, hsum0, zero_add]
  have hterm (i : ℕ) :
      (((j + i).choose j : ℝ) / (j + m).choose j) * bernsteinValue (j + m) (j + i) x =
        (m.choose i : ℝ) * x ^ (j + i) * (1 - x) ^ (m - i) := by
    have hc : ((j + m).choose (j + i) : ℝ) * ((j + i).choose j : ℝ) =
        ((j + m).choose j : ℝ) * (m.choose i : ℝ) := by
      exact_mod_cast (by simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul (n := j + m) (Nat.le_add_right j i)))
    have hcoef : (((j + i).choose j : ℝ) / (j + m).choose j) *
        ((j + m).choose (j + i) : ℝ) = (m.choose i : ℝ) := by
      field_simp
      nlinarith [hc]
    unfold bernsteinValue
    have hsub : j + m - (j + i) = m - i := by omega
    rw [hsub, ← mul_assoc, ← mul_assoc, hcoef]
  simp_rw [hterm]
  calc
    x ^ j = x ^ j * (x + (1 - x)) ^ m := by simp
    _ = ∑ i ∈ range (m + 1), (m.choose i : ℝ) * x ^ (j + i) * (1 - x) ^ (m - i) := by
      rw [add_pow, Finset.mul_sum]
      apply sum_congr rfl
      intro i _
      rw [pow_add]
      ring

noncomputable def chooseFast (n k : ℕ) : ℕ :=
  if k ≤  n then n.factorial / (k.factorial * (n - k).factorial) else 0

lemma chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k := by
  by_cases h : k ≤  n
  · simp only [chooseFast, if_pos h, Nat.choose_eq_factorial_div_factorial h]
  · simp only [chooseFast, if_neg h, Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]

noncomputable def bernsteinTransform (n : ℕ) (a : Fin (n + 1) → ℚ) (i : Fin (n + 1)) : ℚ :=
  ∑ j : Fin (n + 1), a j * (chooseFast i j : ℚ) / chooseFast n j

lemma bernsteinTransform_sound (n : ℕ) (a : Fin (n + 1) → ℚ) (x : I) :
    (∑ j : Fin (n + 1), (a j : ℝ) * (x : ℝ) ^ (j : ℕ)) =
      ∑ i : Fin (n + 1), (bernsteinTransform n a i : ℝ) * bernstein n i x := by
  have hm (j : Fin (n + 1)) : (x : ℝ) ^ (j : ℕ) =
      ∑ i : Fin (n + 1), ((i.val.choose j : ℝ) / n.choose j) * bernstein n i x := by
    simpa only [Finset.sum_range, bernstein_apply, bernsteinValue] using
      monomial_bernstein n j (Nat.le_of_lt_succ j.isLt) x
  simp_rw [hm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [bernsteinTransform, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    chooseFast_eq, Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  ring

end TaoZetaNumerics

end Height100Module98

section Height100Module99

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset TaoZetaNumerics
open scoped unitInterval

noncomputable def bivariatePowerValue (m n : ℕ)
    (a : Fin (m+1) → Fin (n+1) → ℚ) (x y : ℝ) : ℝ :=
  ∑ i : Fin (m+1), ∑ j : Fin (n+1), (a i j:ℝ)*x^(i:ℕ)*y^(j:ℕ)

lemma bivariate_bernstein_identity (m n : ℕ)
    (a row result : Fin (m+1) → Fin (n+1) → ℚ)
    (hr : ∀ i, row i=bernsteinTransform n (a i))
    (hc : ∀ j, (fun i => result i j)=bernsteinTransform m (fun i => row i j))
    (x y : I) :
    bivariatePowerValue m n a x y=
      ∑ i : Fin (m+1), ∑ j : Fin (n+1),
        (result i j:ℝ)*bernstein m i x*bernstein n j y := by
  have hrow (i : Fin (m+1)) := bernsteinTransform_sound n (a i) y
  simp only [←hr] at hrow
  have hcol (j : Fin (n+1)) := bernsteinTransform_sound m (fun i => row i j) x
  simp only [←hc] at hcol
  unfold bivariatePowerValue
  calc
    _ = ∑ i : Fin (m+1), (x:ℝ)^(i:ℕ)*
        (∑ j : Fin (n+1), (a i j:ℝ)*(y:ℝ)^(j:ℕ)) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin (n+1),
        (∑ i : Fin (m+1), (row i j:ℝ)*(x:ℝ)^(i:ℕ))*bernstein n j y := by
      simp_rw [hrow,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp_rw [hcol,sum_mul]
      rw [sum_comm]

lemma bivariate_bernstein_lower (m n : ℕ)
    (a row result : Fin (m+1) → Fin (n+1) → ℚ)
    (hr : ∀ i, row i=bernsteinTransform n (a i))
    (hc : ∀ j, (fun i => result i j)=bernsteinTransform m (fun i => row i j))
    (L : ℝ) (hL : ∀ i j, L≤ (result i j:ℝ)) (x y : I) :
    L≤ bivariatePowerValue m n a x y := by
  rw [bivariate_bernstein_identity m n a row result hr hc x y]
  exact bernstein_lower_bound_two m n (fun i j => (result i j:ℝ)) L hL x y

end CertifiedLocalPolynomial

end Height100Module99

section Height100Module100

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset CertifiedLocalXi
open scoped unitInterval

end CertifiedLocalPolynomial

end Height100Module100

section Height100Module101

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0
namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module101

section Height100Module102

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial TaoZetaPoly TaoZetaNumerics
open Finset
open scoped unitInterval

end CertifiedLocalBoxes

end Height100Module102

section Height100Module103

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module103

section Height100Module104

namespace CertifiedStreamingBernstein
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedStreamingBernstein

end Height100Module104

section Height100Module105

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein
open TaoZetaNumerics

end CertifiedStreamingLocalBoxes

end Height100Module105

section Height100Module106

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes
open CertifiedLocalPolynomial CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset
open scoped unitInterval

end CertifiedFastLocalBoxes

end Height100Module106

section Height100Module107

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedLocalBoxes

end Height100Module107

section Height100Module108

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial CertifiedLocalPolynomial CertifiedLocalXi
open scoped unitInterval

end CertifiedFastLocalBoxes

end Height100Module108

section Height100Module109

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein

end CertifiedStreamingLocalBoxes

end Height100Module109

section Height100Module110
namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes
end CertifiedStreamingLocalBoxes
end Height100Module110

section Height100Module111

namespace CertifiedStreamingLocalBoxes
open CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedStreamingLocalBoxes

end Height100Module111

section Height100Module112

namespace CertifiedHeight100
open CertifiedPolynomialTranslation CertifiedGlobalMoments CertifiedLocalXi

end CertifiedHeight100

end Height100Module112

section Height100Module113

set_option autoImplicit false
namespace TaoFivePrimes

end TaoFivePrimes

end Height100Module113

end RH106Proof

namespace RH106Numerical
open Finset
noncomputable def roundedNumerators : List ℤ := [4033988397, 72614060488, -56265857887, -13631584038, 19781941696, -4345029406, -654966908, 419557367, -50537588, -6331152, 2378275, -179411, -22774, 5447, -261, -39, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def rounded (n : ℕ) : ℤ := roundedNumerators.getD n 0
end RH106Numerical

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH106Numerical
open Finset

noncomputable def proposed (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
end RH106Numerical

open Complex Metric MeasureTheory Set Finset
open scoped ComplexConjugate Topology
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH106Proof
namespace TaoZetaCertificate
open RH106Proof.ZetaSix

end TaoZetaCertificate
namespace CertifiedLocalXi
open RH106Proof.ZetaSix

end CertifiedLocalXi
end RH106Proof

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH106Proof.CertifiedLocalXi
open Complex Metric
end RH106Proof.CertifiedLocalXi
namespace RH106Numerical
open Complex
end RH106Numerical

namespace RH106Numerical
noncomputable def powerMatrix : List (List ℚ) := [
  [(1762574679806191:ℚ)/1638400000000, (-13300059642591:ℚ)/409600000000, (-754790949431091:ℚ)/409600000000, (53585647982409:ℚ)/51200000000, (109156292011:ℚ)/20480000000, (-3651537505953:ℚ)/25600000000, (942714683869:ℚ)/25600000000, (956789141:ℚ)/1600000000, (-11408824971:ℚ)/6400000000, (17808743:ℚ)/64000000, (12527471:ℚ)/1600000000, (-1469199:ℚ)/200000000, (303173:ℚ)/400000000, (2961:ℚ)/100000000, (-261:ℚ)/20000000, (3:ℚ)/3125000],
  [(251596983143697:ℚ)/1638400000000, (-53585647982409:ℚ)/204800000000, (-109156292011:ℚ)/40960000000, (1217179168651:ℚ)/10240000000, (-942714683869:ℚ)/20480000000, (-6697523987:ℚ)/6400000000, (26620591599:ℚ)/6400000000, (-53426229:ℚ)/64000000, (-37582413:ℚ)/1280000000, (5387063:ℚ)/160000000, (-3334903:ℚ)/800000000, (-38493:ℚ)/200000000, (7917:ℚ)/80000000, (-21:ℚ)/2500000, 0, 0],
  [(109156292011:ℚ)/1638400000000, (-3651537505953:ℚ)/409600000000, (2828144051607:ℚ)/409600000000, (6697523987:ℚ)/25600000000, (-79861774797:ℚ)/51200000000, (1121950809:ℚ)/2560000000, (263076891:ℚ)/12800000000, (-48483567:ℚ)/1600000000, (30014127:ℚ)/6400000000, (423423:ℚ)/1600000000, (-261261:ℚ)/1600000000, (819:ℚ)/50000000, 0, 0, 0, 0],
  [(-134673526267:ℚ)/1638400000000, (-956789141:ℚ)/102400000000, (11408824971:ℚ)/102400000000, (-53426229:ℚ)/1024000000, (-37582413:ℚ)/10240000000, (48483567:ℚ)/6400000000, (-10004709:ℚ)/6400000000, (-181467:ℚ)/1600000000, (111969:ℚ)/1280000000, (-429:ℚ)/40000000, 0, 0, 0, 0, 0, 0],
  [(-1267647219:ℚ)/1638400000000, (17808743:ℚ)/16384000000, (12527471:ℚ)/81920000000, (-5387063:ℚ)/10240000000, (3334903:ℚ)/20480000000, (423423:ℚ)/25600000000, (-87087:ℚ)/5120000000, (429:ℚ)/160000000, 0, 0, 0, 0, 0, 0, 0, 0],
  [(-1138861:ℚ)/1638400000000, (1469199:ℚ)/204800000000, (-909519:ℚ)/204800000000, (-38493:ℚ)/51200000000, (23751:ℚ)/20480000000, (-819:ℚ)/3200000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(23321:ℚ)/1638400000000, (2961:ℚ)/409600000000, (-1827:ℚ)/81920000000, (21:ℚ)/2560000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(87:ℚ)/1638400000000, (-3:ℚ)/51200000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
noncomputable def rowMatrix : List (List ℚ) := [
  [(1762574679806191:ℚ)/1638400000000, (8795139986174167:ℚ)/8192000000000, (12087091616129373:ℚ)/11468800000000, (759595868966934137:ℚ)/745472000000000, (2171640396201943763:ℚ)/2236416000000000, (641330389453617943:ℚ)/702873600000000, (6931923878656162423:ℚ)/8200192000000000, (739728092994866143:ℚ)/958464000000000, (7313789281402970941:ℚ)/10543104000000000, (1005098909922593011:ℚ)/1640038400000000, (124364594858428037:ℚ)/234291200000000, (334711970423642793:ℚ)/745472000000000, (39256519967152247:ℚ)/106496000000000, (16672034633029193:ℚ)/57344000000000, (1771267375732559:ℚ)/8192000000000, (47767256271627:ℚ)/327680000000],
  [(251596983143697:ℚ)/1638400000000, (1115089854432061:ℚ)/8192000000000, (20411724404377937:ℚ)/172032000000000, (75604262994326823:ℚ)/745472000000000, (189309474264397477:ℚ)/2236416000000000, (30655021080890377:ℚ)/447283200000000, (12473706398113159:ℚ)/234291200000000, (27333678698193997:ℚ)/702873600000000, (3595578958352729:ℚ)/140574720000000, (21937530403020289:ℚ)/1640038400000000, (11446171146471283:ℚ)/4920115200000000, (-1299303853364663:ℚ)/172032000000000, (-932553466322797:ℚ)/57344000000000, (-585448175128297:ℚ)/24576000000000, (-743798235896441:ℚ)/24576000000000, (-58390305077023:ℚ)/1638400000000],
  [(109156292011:ℚ)/1638400000000, (-4322935214549:ℚ)/8192000000000, (-1730591556817:ℚ)/1638400000000, (-32342897345233:ℚ)/21299200000000, (-203936724016317:ℚ)/106496000000000, (-526507904227527:ℚ)/234291200000000, (-2949390649349523:ℚ)/1171456000000000, (-3197498801673199:ℚ)/1171456000000000, (-3381152559080471:ℚ)/1171456000000000, (-701025409152463:ℚ)/234291200000000, (-714907058523887:ℚ)/234291200000000, (-326790319967237:ℚ)/106496000000000, (-324636502920269:ℚ)/106496000000000, (-24537333976797:ℚ)/8192000000000, (-4774092178857:ℚ)/1638400000000, (-4601401089117:ℚ)/1638400000000],
  [(-134673526267:ℚ)/1638400000000, (-2035411520261:ℚ)/24576000000000, (-14172499826083:ℚ)/172032000000000, (-60381985813213:ℚ)/745472000000000, (-25170755218673:ℚ)/319488000000000, (-33930663111899:ℚ)/447283200000000, (-53926101107181:ℚ)/745472000000000, (-4366278044989:ℚ)/63897600000000, (-20430692385073:ℚ)/319488000000000, (-44195310562157:ℚ)/745472000000000, (-24347654224219:ℚ)/447283200000000, (-22131751119083:ℚ)/447283200000000, (-33171687005917:ℚ)/745472000000000, (-972036611333:ℚ)/24576000000000, (-852838395781:ℚ)/24576000000000, (-49145591547:ℚ)/1638400000000],
  [(-1267647219:ℚ)/1638400000000, (-3446766797:ℚ)/4915200000000, (-863361347:ℚ)/1376256000000, (-82464942193:ℚ)/149094400000000, (-214526744539:ℚ)/447283200000000, (-12159744617:ℚ)/29818880000000, (-50451437613:ℚ)/149094400000000, (-17385144589:ℚ)/63897600000000, (-892012059:ℚ)/4259840000000, (-4495848993:ℚ)/29818880000000, (-43164011903:ℚ)/447283200000000, (-20933486051:ℚ)/447283200000000, (-266201497:ℚ)/149094400000000, (1324972973:ℚ)/34406400000000, (121436793:ℚ)/1638400000000, (172262853:ℚ)/1638400000000],
  [(-1138861:ℚ)/1638400000000, (-1776441:ℚ)/8192000000000, (12564577:ℚ)/57344000000000, (7008821:ℚ)/11468800000000, (10991493:ℚ)/11468800000000, (159065407:ℚ)/126156800000000, (958274123:ℚ)/630784000000000, (156307461:ℚ)/90112000000000, (6880349:ℚ)/3604480000000, (257873503:ℚ)/126156800000000, (270330351:ℚ)/126156800000000, (126604873:ℚ)/57344000000000, (128565337:ℚ)/57344000000000, (25786269:ℚ)/11468800000000, (3653579:ℚ)/1638400000000, (717511:ℚ)/327680000000],
  [(23321:ℚ)/1638400000000, (120553:ℚ)/8192000000000, (122761:ℚ)/8192000000000, (1603897:ℚ)/106496000000000, (1593121:ℚ)/106496000000000, (313097:ℚ)/21299200000000, (1522909:ℚ)/106496000000000, (1467313:ℚ)/106496000000000, (1400617:ℚ)/106496000000000, (1324741:ℚ)/106496000000000, (248321:ℚ)/21299200000000, (1153129:ℚ)/106496000000000, (1061233:ℚ)/106496000000000, (74449:ℚ)/8192000000000, (67297:ℚ)/8192000000000, (2413:ℚ)/327680000000],
  [(87:ℚ)/1638400000000, (403:ℚ)/8192000000000, (371:ℚ)/8192000000000, (339:ℚ)/8192000000000, (307:ℚ)/8192000000000, (11:ℚ)/327680000000, (243:ℚ)/8192000000000, (211:ℚ)/8192000000000, (179:ℚ)/8192000000000, (147:ℚ)/8192000000000, (23:ℚ)/1638400000000, (83:ℚ)/8192000000000, (51:ℚ)/8192000000000, (19:ℚ)/8192000000000, (-13:ℚ)/8192000000000, (-9:ℚ)/1638400000000]]
noncomputable def bernsteinMatrix : List (List ℚ) := [
  [(1762574679806191:ℚ)/1638400000000, (8795139986174167:ℚ)/8192000000000, (12087091616129373:ℚ)/11468800000000, (759595868966934137:ℚ)/745472000000000, (2171640396201943763:ℚ)/2236416000000000, (641330389453617943:ℚ)/702873600000000, (6931923878656162423:ℚ)/8200192000000000, (739728092994866143:ℚ)/958464000000000, (7313789281402970941:ℚ)/10543104000000000, (1005098909922593011:ℚ)/1640038400000000, (124364594858428037:ℚ)/234291200000000, (334711970423642793:ℚ)/745472000000000, (39256519967152247:ℚ)/106496000000000, (16672034633029193:ℚ)/57344000000000, (1771267375732559:ℚ)/8192000000000, (47767256271627:ℚ)/327680000000],
  [(6294809870893517:ℚ)/5734400000000, (6268106975765123:ℚ)/5734400000000, (644778172048981051:ℚ)/602112000000000, (2696387672881432891:ℚ)/2609152000000000, (2565132041279667303:ℚ)/2609152000000000, (5293732385852845559:ℚ)/5740134400000000, (3497146205323364109:ℚ)/4100096000000000, (28684534170538801483:ℚ)/36900864000000000, (25733096695848625631:ℚ)/36900864000000000, (3528814949930585683:ℚ)/5740134400000000, (9146520807667696361:ℚ)/17220403200000000, (3506030214401379017:ℚ)/7827456000000000, (955723141664131871:ℚ)/2609152000000000, (24715327861979641:ℚ)/86016000000000, (18226408327243649:ℚ)/86016000000000, (806731832214961:ℚ)/5734400000000],
  [(9630939832771051:ℚ)/8601600000000, (47846038975258831:ℚ)/43008000000000, (327476874449462861:ℚ)/301056000000000, (820200341243224733:ℚ)/782745600000000, (3894668541218571769:ℚ)/3913728000000000, (8023978497919318703:ℚ)/8610201600000000, (1763919453105211043:ℚ)/2050048000000000, (2063195750898053333:ℚ)/2635776000000000, (12931429588974116131:ℚ)/18450432000000000, (5308448778232126931:ℚ)/8610201600000000, (1524956953089349733:ℚ)/2870067200000000, (582740162205770563:ℚ)/1304576000000000, (284784840463888013:ℚ)/782745600000000, (1743595364816221:ℚ)/6144000000000, (8921286989424143:ℚ)/43008000000000, (77676977949493:ℚ)/573440000000],
  [(8183059956038241:ℚ)/7168000000000, (121700232819748973:ℚ)/107520000000000, (831372028933304359:ℚ)/752640000000000, (494896410173863717:ℚ)/465920000000000, (757937177208901441:ℚ)/752640000000000, (20266045915905648377:ℚ)/21525504000000000, (31132776219016960123:ℚ)/35875840000000000, (7270019640704109931:ℚ)/9225216000000000, (4640621876772204901:ℚ)/6589440000000000, (22176807302707804231:ℚ)/35875840000000000, (11438042090350025237:ℚ)/21525504000000000, (124489175002586531:ℚ)/279552000000000, (1178075502091267471:ℚ)/3261440000000000, (30116220602781269:ℚ)/107520000000000, (21808398895207753:ℚ)/107520000000000, (932544890042781:ℚ)/7168000000000],
  [(4170162816078653:ℚ)/3584000000000, (20630359226622077:ℚ)/17920000000000, (422005229218834313:ℚ)/376320000000000, (1755398669961902243:ℚ)/1630720000000000, (712054203451184903:ℚ)/698880000000000, (10234874277406857059:ℚ)/10762752000000000, (15696256085182040301:ℚ)/17937920000000000, (332619045350309689:ℚ)/419328000000000, (16316811906074447399:ℚ)/23063040000000000, (11114922347095577237:ℚ)/17937920000000000, (5717856149374626251:ℚ)/10762752000000000, (2226786486264407:ℚ)/5017600000000, (584532890464057707:ℚ)/1630720000000000, (34654600862806747:ℚ)/125440000000000, (1521317735492233:ℚ)/7680000000000, (89315666562497:ℚ)/716800000000],
  [(60696879078523:ℚ)/51200000000, (6293030316104437:ℚ)/5376000000000, (14276761268368041:ℚ)/12544000000000, (76222739512126111:ℚ)/69888000000000, (72024112105188011:ℚ)/69888000000000, (206710070065636561:ℚ)/215255040000000, (4747158516582238633:ℚ)/5381376000000000, (368198252279445839:ℚ)/461260800000000, (1638815058615991727:ℚ)/2306304000000000, (1113879383813382103:ℚ)/1793792000000000, (571507708941932393:ℚ)/1076275200000000, (216293746421791601:ℚ)/489216000000000, (173935528799697109:ℚ)/489216000000000, (209114047211087:ℚ)/768000000000, (1038662977030841:ℚ)/5376000000000, (127918717759411:ℚ)/1075200000000],
  [(216368874057257:ℚ)/179200000000, (3198383120364631:ℚ)/2688000000000, (21728896747979357:ℚ)/18816000000000, (90076467026626131:ℚ)/81536000000000, (3399003805885651:ℚ)/3261440000000, (173914782233599333:ℚ)/179379200000000, (797458371461970877:ℚ)/896896000000000, (132304277868151349:ℚ)/164736000000000, (822807503151956851:ℚ)/1153152000000000, (557999375682267021:ℚ)/896896000000000, (285533352029181439:ℚ)/538137600000000, (107700777431440913:ℚ)/244608000000000, (28739614734752403:ℚ)/81536000000000, (5045629492113901:ℚ)/18816000000000, (101163633695227:ℚ)/537600000000, (2898011328591:ℚ)/25600000000],
  [(3147101370239:ℚ)/2560000000, (77384552254829:ℚ)/64000000000, (524797151440463:ℚ)/448000000000, (1303136463610133:ℚ)/1164800000000, (18410077605614263:ℚ)/17472000000000, (5373979971763717:ℚ)/5491200000000, (57400483739675777:ℚ)/64064000000000, (5118697973683057:ℚ)/6336000000000, (59002741640102033:ℚ)/82368000000000, (5703302393300227:ℚ)/9152000000000, (162988832909011:ℚ)/307507200000, (589105532449927:ℚ)/1344000000000, (2034115764439037:ℚ)/5824000000000, (70931070963469:ℚ)/268800000000, (11712347778073:ℚ)/64000000000, (1373403167679:ℚ)/12800000000]]
noncomputable def entry (m : List (List ℚ)) (i j : ℕ) : ℚ := (m.getD i []).getD j 0
noncomputable def a (i : Fin 8) (j : Fin 16) : ℚ := entry powerMatrix i j
noncomputable def r (i : Fin 8) (j : Fin 16) : ℚ := entry rowMatrix i j
noncomputable def b (i : Fin 8) (j : Fin 16) : ℚ := entry bernsteinMatrix i j
theorem bernstein_checked :
    (∀ i : Fin 8, ∀ j : Fin 16, r i j=RH106Proof.TaoZetaNumerics.bernsteinTransform 15 (a i) j) ∧
    (∀ i : Fin 8, ∀ j : Fin 16, b i j=RH106Proof.TaoZetaNumerics.bernsteinTransform 7 (fun u => r u j) i) ∧
    (∀ i : Fin 8, ∀ j : Fin 16, (1:ℚ) ≤ b i j) := by decide +kernel
end RH106Numerical

namespace RH106Numerical
noncomputable def c (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
noncomputable def realValue (x y : ℝ) : ℝ :=
  (4033988397:ℝ)/100000000*x^0*y^0 +
  (9076757561:ℝ)/12500000*x^0*y^1 +
  (-56265857887:ℝ)/100000000*x^0*y^2 +
  (56265857887:ℝ)/100000000*x^2*y^0 +
  (-6815792019:ℝ)/50000000*x^0*y^3 +
  (20447376057:ℝ)/50000000*x^2*y^1 +
  (309092839:ℝ)/1562500*x^0*y^4 +
  (-927278517:ℝ)/781250*x^2*y^2 +
  (309092839:ℝ)/1562500*x^4*y^0 +
  (-2172514703:ℝ)/50000000*x^0*y^5 +
  (2172514703:ℝ)/5000000*x^2*y^3 +
  (-2172514703:ℝ)/10000000*x^4*y^1 +
  (-163741727:ℝ)/25000000*x^0*y^6 +
  (491225181:ℝ)/5000000*x^2*y^4 +
  (-491225181:ℝ)/5000000*x^4*y^2 +
  (163741727:ℝ)/25000000*x^6*y^0 +
  (419557367:ℝ)/100000000*x^0*y^7 +
  (-8810704707:ℝ)/100000000*x^2*y^5 +
  (2936901569:ℝ)/20000000*x^4*y^3 +
  (-2936901569:ℝ)/100000000*x^6*y^1 +
  (-12634397:ℝ)/25000000*x^0*y^8 +
  (88440779:ℝ)/6250000*x^2*y^6 +
  (-88440779:ℝ)/2500000*x^4*y^4 +
  (88440779:ℝ)/6250000*x^6*y^2 +
  (-12634397:ℝ)/25000000*x^8*y^0 +
  (-395697:ℝ)/6250000*x^0*y^9 +
  (3561273:ℝ)/1562500*x^2*y^7 +
  (-24928911:ℝ)/3125000*x^4*y^5 +
  (8309637:ℝ)/1562500*x^6*y^3 +
  (-3561273:ℝ)/6250000*x^8*y^1 +
  (95131:ℝ)/4000000*x^0*y^10 +
  (-856179:ℝ)/800000*x^2*y^8 +
  (1997751:ℝ)/400000*x^4*y^6 +
  (-1997751:ℝ)/400000*x^6*y^4 +
  (856179:ℝ)/800000*x^8*y^2 +
  (-95131:ℝ)/4000000*x^10*y^0 +
  (-179411:ℝ)/100000000*x^0*y^11 +
  (1973521:ℝ)/20000000*x^2*y^9 +
  (-5920563:ℝ)/10000000*x^4*y^7 +
  (41443941:ℝ)/50000000*x^6*y^5 +
  (-5920563:ℝ)/20000000*x^8*y^3 +
  (1973521:ℝ)/100000000*x^10*y^1 +
  (-11387:ℝ)/50000000*x^0*y^12 +
  (375771:ℝ)/25000000*x^2*y^10 +
  (-1127313:ℝ)/10000000*x^4*y^8 +
  (2630397:ℝ)/12500000*x^6*y^6 +
  (-1127313:ℝ)/10000000*x^8*y^4 +
  (375771:ℝ)/25000000*x^10*y^2 +
  (-11387:ℝ)/50000000*x^12*y^0 +
  (5447:ℝ)/100000000*x^0*y^13 +
  (-212433:ℝ)/50000000*x^2*y^11 +
  (778921:ℝ)/20000000*x^4*y^9 +
  (-2336763:ℝ)/25000000*x^6*y^7 +
  (7010289:ℝ)/100000000*x^8*y^5 +
  (-778921:ℝ)/50000000*x^10*y^3 +
  (70811:ℝ)/100000000*x^12*y^1 +
  (-261:ℝ)/100000000*x^0*y^14 +
  (23751:ℝ)/100000000*x^2*y^12 +
  (-261261:ℝ)/100000000*x^4*y^10 +
  (783783:ℝ)/100000000*x^6*y^8 +
  (-783783:ℝ)/100000000*x^8*y^6 +
  (261261:ℝ)/100000000*x^10*y^4 +
  (-23751:ℝ)/100000000*x^12*y^2 +
  (261:ℝ)/100000000*x^14*y^0 +
  (-39:ℝ)/100000000*x^0*y^15 +
  (819:ℝ)/20000000*x^2*y^13 +
  (-10647:ℝ)/20000000*x^4*y^11 +
  (39039:ℝ)/20000000*x^6*y^9 +
  (-50193:ℝ)/20000000*x^8*y^7 +
  (117117:ℝ)/100000000*x^10*y^5 +
  (-3549:ℝ)/20000000*x^12*y^3 +
  (117:ℝ)/20000000*x^14*y^1 +
  (3:ℝ)/50000000*x^0*y^16 +
  (-9:ℝ)/1250000*x^2*y^14 +
  (273:ℝ)/2500000*x^4*y^12 +
  (-3003:ℝ)/6250000*x^6*y^10 +
  (3861:ℝ)/5000000*x^8*y^8 +
  (-3003:ℝ)/6250000*x^10*y^6 +
  (273:ℝ)/2500000*x^12*y^4 +
  (-9:ℝ)/1250000*x^14*y^2 +
  (3:ℝ)/50000000*x^16*y^0
lemma complex_identity (x y : ℝ) :
    (∑ n ∈ Finset.range 40, (c n:ℂ)*((y:ℂ)-Complex.I*x)^n)-(realValue x y:ℂ)=
      Complex.I*(-x*RH106Proof.CertifiedLocalPolynomial.bivariatePowerValue 7 15 a
        (4*x^2) (y+1/2):ℂ) := by
  norm_num [c,rounded,roundedNumerators,Finset.sum_range_succ,realValue,
    RH106Proof.CertifiedLocalPolynomial.bivariatePowerValue,a,entry,powerMatrix,Fin.sum_univ_succ]
  push_cast
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod]
  try simp only [Complex.I_sq,Complex.I_pow_three,pow_zero,pow_one]
  apply Complex.ext <;> simp [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im] <;> ring
lemma rotated_variable (s : ℂ) :
    RH106Proof.CertifiedLocalXi.rotatedVariable (211/2) s=
      ((s.im-211/2:ℝ):ℂ)-Complex.I*((s.re-1/2:ℝ):ℂ) := by
  apply Complex.ext <;> simp [RH106Proof.CertifiedLocalXi.rotatedVariable,
    RH106Proof.CertifiedLocalXi.center] <;> ring
lemma imaginary_identity (s : ℂ) :
    (RH106Proof.CertifiedLocalXi.rotatedPolynomial c (211/2) s).im=
      -(s.re-1/2)*RH106Proof.CertifiedLocalPolynomial.bivariatePowerValue 7 15 a
        (4*(s.re-1/2)^2) (s.im-105) := by
  have h := congrArg Complex.im (complex_identity (s.re-1/2) (s.im-211/2))
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,sub_zero,zero_add] at h
  have he : (s.im-211/2)+1/2=s.im-105 := by ring
  rw [he] at h
  unfold RH106Proof.CertifiedLocalXi.rotatedPolynomial
  simp only [rotated_variable]
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,mul_zero,sub_zero] using h
attribute [local irreducible] a r b
lemma candidate_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 105 ≤ s.im) (hb : s.im ≤ 106) :
    1 ≤ |(RH106Proof.CertifiedLocalXi.rotatedPolynomial proposed (211/2) s).re| ∨
      |s.re-1/2| ≤ |(RH106Proof.CertifiedLocalXi.rotatedPolynomial proposed (211/2) s).im| := by
  right
  let x : Set.Icc (0:ℝ) 1 := ⟨4*(s.re-1/2)^2,⟨by positivity,by
    nlinarith [mul_nonneg h0 (show 0 ≤ 1-s.re by linarith)]⟩⟩
  let y : Set.Icc (0:ℝ) 1 := ⟨s.im-105,⟨by linarith,by linarith⟩⟩
  have hr : ∀ i, r i=RH106Proof.TaoZetaNumerics.bernsteinTransform 15 (a i) := by
    intro i; funext j; exact bernstein_checked.1 i j
  have hc : ∀ j, (fun i => b i j)=RH106Proof.TaoZetaNumerics.bernsteinTransform 7
      (fun i => r i j) := by intro j; funext i; exact bernstein_checked.2.1 i j
  have hl : ∀ i j, (1:ℝ) ≤ (b i j:ℝ) := by intro i j; exact_mod_cast bernstein_checked.2.2 i j
  have h := RH106Proof.CertifiedLocalPolynomial.bivariate_bernstein_lower 7 15 a r b hr hc 1 hl x y
  change 1 ≤ RH106Proof.CertifiedLocalPolynomial.bivariatePowerValue 7 15 a
    (4*(s.re-1/2)^2) (s.im-105) at h
  have he : c=proposed := rfl
  rw [←he,imaginary_identity,abs_mul,abs_neg,abs_of_nonneg (by linarith :
    0 ≤ RH106Proof.CertifiedLocalPolynomial.bivariatePowerValue 7 15 a
      (4*(s.re-1/2)^2) (s.im-105))]
  exact le_mul_of_one_le_right (abs_nonneg _) h
end RH106Numerical


theorem solution (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ha : 105 ≤ s.im) (hb : s.im ≤ 106) :
    1 ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH105To106RoundedCoefficients 40 (211/2) s).re| ∨ |s.re-1/2| ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH105To106RoundedCoefficients 40 (211/2) s).im| := by
  have h := RH106Numerical.candidate_certificate s h0 h1 ha hb
  simpa only [RH106Numerical.proposed,RH106Numerical.rounded,RH106Numerical.roundedNumerators,
    RH106Proof.CertifiedLocalXi.rotatedPolynomial,RH106Proof.CertifiedLocalXi.rotatedVariable,
    RH106Proof.CertifiedLocalXi.center,TaoFivePrimes_RHLocalRoundedPolynomial,
    RH1000Analytic.CertifiedLocalXi.center,TaoFivePrimes_RH105To106RoundedCoefficients,Complex.ofReal_div] using h
