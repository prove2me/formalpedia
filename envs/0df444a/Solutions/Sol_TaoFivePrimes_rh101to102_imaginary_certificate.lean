-- Prove2me | solution 1 for TaoFivePrimes.rh101to102_imaginary_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T05:02:17.449925+00:00
-- url     : https://prove2.me/submissions/c4a11cb1-7f59-48ad-887a-6b9941dfc11b

import Mathlib
import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH101To102RoundedCoefficients

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.ambiguousOpen false
namespace RH102Proof
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
  ∑ n ∈ range 32, (b n : ℂ)*rotatedVariable T z^n

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

end RH102Proof

namespace RH102Numerical
open Finset
noncomputable def roundedNumerators : List ℤ := [4866968715, 22013961324, -25022939073, 5053576357, 2992204322, -1551557643, 160404139, 53205217, -16609352, 915159, 315029, -62270, 1777, 773, -104, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def rounded (n : ℕ) : ℤ := roundedNumerators.getD n 0
end RH102Numerical

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH102Numerical
open Finset

noncomputable def proposed (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
end RH102Numerical

open Complex Metric MeasureTheory Set Finset
open scoped ComplexConjugate Topology
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH102Proof
namespace TaoZetaCertificate
open RH102Proof.ZetaSix

end TaoZetaCertificate
namespace CertifiedLocalXi
open RH102Proof.ZetaSix

end CertifiedLocalXi
end RH102Proof

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH102Proof.CertifiedLocalXi
open Complex Metric
end RH102Proof.CertifiedLocalXi
namespace RH102Numerical
open Complex
end RH102Numerical

namespace RH102Numerical
noncomputable def imPower : List (List ℚ) := [
  [(799914814886891:ℚ)/1638400000000, (-42709072194657:ℚ)/163840000000, (-62231578477419:ℚ)/1638400000000, (14673445388677:ℚ)/409600000000, (-334419434733:ℚ)/65536000000, (-225240429723:ℚ)/819200000000, (218353119229:ℚ)/1638400000000, (-508165297:ℚ)/51200000000, (-877839687:ℚ)/1638400000000, (4177437:ℚ)/32768000000, (-9359273:ℚ)/1638400000000, (-133359:ℚ)/409600000000, (75777:ℚ)/1638400000000, (-1141:ℚ)/819200000000, (-21:ℚ)/327680000000, (1:ℚ)/204800000000],
  [(20743859492473:ℚ)/1638400000000, (-14673445388677:ℚ)/409600000000, (334419434733:ℚ)/32768000000, (75080143241:ℚ)/81920000000, (-218353119229:ℚ)/327680000000, (3557157079:ℚ)/51200000000, (2048292603:ℚ)/409600000000, (-12532311:ℚ)/8192000000, (28077819:ℚ)/327680000000, (488983:ℚ)/81920000000, (-833547:ℚ)/819200000000, (14833:ℚ)/409600000000, (637:ℚ)/327680000000, (-7:ℚ)/40960000000, 0, 0],
  [(-334419434733:ℚ)/327680000000, (-225240429723:ℚ)/819200000000, (655059357687:ℚ)/1638400000000, (-3557157079:ℚ)/51200000000, (-6144877809:ℚ)/819200000000, (263178531:ℚ)/81920000000, (-196544733:ℚ)/819200000000, (-4400847:ℚ)/204800000000, (7501923:ℚ)/1638400000000, (-163163:ℚ)/819200000000, (-21021:ℚ)/1638400000000, (273:ℚ)/204800000000, 0, 0, 0, 0],
  [(-31193302747:ℚ)/1638400000000, (508165297:ℚ)/51200000000, (877839687:ℚ)/409600000000, (-12532311:ℚ)/8192000000, (28077819:ℚ)/163840000000, (4400847:ℚ)/204800000000, (-2500641:ℚ)/409600000000, (69927:ℚ)/204800000000, (9009:ℚ)/327680000000, (-143:ℚ)/40960000000, 0, 0, 0, 0, 0, 0],
  [(-97537743:ℚ)/1638400000000, (4177437:ℚ)/32768000000, (-9359273:ℚ)/327680000000, (-488983:ℚ)/81920000000, (833547:ℚ)/327680000000, (-163163:ℚ)/819200000000, (-7007:ℚ)/327680000000, (143:ℚ)/40960000000, 0, 0, 0, 0, 0, 0, 0, 0],
  [(850843:ℚ)/1638400000000, (133359:ℚ)/409600000000, (-227331:ℚ)/819200000000, (14833:ℚ)/409600000000, (1911:ℚ)/327680000000, (-273:ℚ)/204800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(5829:ℚ)/1638400000000, (-1141:ℚ)/819200000000, (-147:ℚ)/327680000000, (7:ℚ)/40960000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(7:ℚ)/1638400000000, (-1:ℚ)/204800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
noncomputable def imRows : List (List ℚ) := [
  [(799914814886891:ℚ)/1638400000000, (771442100090453:ℚ)/1638400000000, (6495796156449513:ℚ)/14336000000000, (11583773869205207:ℚ)/26624000000000, (303471549903517:ℚ)/728000000000, (20423015820307031:ℚ)/51251200000000, (33444485784301:ℚ)/88000000000, (59569718332352671:ℚ)/164736000000000, (14135028414472847:ℚ)/41184000000000, (10408299261526923:ℚ)/32032000000000, (245695396530191:ℚ)/800800000000, (210317883514779:ℚ)/728000000000, (49364864501531:ℚ)/182000000000, (3554103024413:ℚ)/14000000000, (118410786311:ℚ)/500000000, (5503490331:ℚ)/25000000],
  [(20743859492473:ℚ)/1638400000000, (252464110832387:ℚ)/24576000000000, (1373113276680403:ℚ)/172032000000000, (4316196183038057:ℚ)/745472000000000, (344666457731347:ℚ)/93184000000000, (150191836301119:ℚ)/87859200000000, (-11367086836603:ℚ)/64064000000000, (-215442228298631:ℚ)/109824000000000, (-50018507309093:ℚ)/13728000000000, (-10457425115661:ℚ)/2002000000000, (-9908893128181:ℚ)/1478400000000, (-70600920043939:ℚ)/8736000000000, (-851984711043:ℚ)/91000000000, (-885929804723:ℚ)/84000000000, (-69819236711:ℚ)/6000000000, (-5053576357:ℚ)/400000000],
  [(-334419434733:ℚ)/327680000000, (-8510646154807:ℚ)/8192000000000, (-4314806569271:ℚ)/4096000000000, (-56671144971697:ℚ)/53248000000000, (-114127203955497:ℚ)/106496000000000, (-4582281225987:ℚ)/4259840000000, (-28662362577391:ℚ)/26624000000000, (-28605600581439:ℚ)/26624000000000, (-444898388953:ℚ)/416000000000, (-1766912136407:ℚ)/1664000000000, (-43752236213:ℚ)/41600000000, (-864703837591:ℚ)/832000000000, (-426286591993:ℚ)/416000000000, (-6452236151:ℚ)/6400000000, (-3959096177:ℚ)/4000000000, (-1551557643:ℚ)/1600000000],
  [(-31193302747:ℚ)/1638400000000, (-451638251701:ℚ)/24576000000000, (-3044127376631:ℚ)/172032000000000, (-12670034203497:ℚ)/745472000000000, (-7283131931213:ℚ)/447283200000000, (-6959453772013:ℚ)/447283200000000, (-11053853997751:ℚ)/745472000000000, (-4502121443459:ℚ)/319488000000000, (-53326991669:ℚ)/3993600000000, (-587750105823:ℚ)/46592000000000, (-2594416831:ℚ)/218400000000, (-5993402449:ℚ)/537600000000, (-2335117387:ℚ)/224000000000, (-116516213:ℚ)/12000000000, (-864515663:ℚ)/96000000000, (-53205217:ℚ)/6400000000],
  [(-97537743:ℚ)/1638400000000, (-83612953:ℚ)/1638400000000, (-26300191:ℚ)/614400000000, (-324880839:ℚ)/9318400000000, (-405819803:ℚ)/14909440000000, (-127024441:ℚ)/6389760000000, (-479090723:ℚ)/37273600000000, (-58916711:ℚ)/9584640000000, (45086143:ℚ)/191692800000000, (133976561:ℚ)/21299200000000, (1343689871:ℚ)/111820800000000, (1947209003:ℚ)/111820800000000, (233821:ℚ)/10400000000, (29273381:ℚ)/1075200000000, (151903:ℚ)/4800000000, (915159:ℚ)/25600000000],
  [(850843:ℚ)/1638400000000, (4432027:ℚ)/8192000000000, (32117319:ℚ)/57344000000000, (33063459:ℚ)/57344000000000, (16933709:ℚ)/28672000000000, (37987647:ℚ)/63078400000000, (192880057:ℚ)/315392000000000, (27875131:ℚ)/45056000000000, (56201787:ℚ)/90112000000000, (395304313:ℚ)/630784000000000, (79198087:ℚ)/126156800000000, (35957709:ℚ)/57344000000000, (4477293:ℚ)/7168000000000, (4448363:ℚ)/7168000000000, (39363:ℚ)/64000000000, (6227:ℚ)/10240000000],
  [(5829:ℚ)/1638400000000, (85153:ℚ)/24576000000000, (41383:ℚ)/12288000000000, (173947:ℚ)/53248000000000, (1010281:ℚ)/319488000000000, (7807:ℚ)/2555904000000, (39191:ℚ)/13312000000000, (56533:ℚ)/19968000000000, (867827:ℚ)/319488000000000, (276867:ℚ)/106496000000000, (79297:ℚ)/31948800000000, (377527:ℚ)/159744000000000, (238991:ℚ)/106496000000000, (52219:ℚ)/24576000000000, (12323:ℚ)/6144000000000, (773:ℚ)/409600000000],
  [(7:ℚ)/1638400000000, (97:ℚ)/24576000000000, (89:ℚ)/24576000000000, (27:ℚ)/8192000000000, (73:ℚ)/24576000000000, (13:ℚ)/4915200000000, (19:ℚ)/8192000000000, (49:ℚ)/24576000000000, (41:ℚ)/24576000000000, (11:ℚ)/8192000000000, (1:ℚ)/983040000000, (17:ℚ)/24576000000000, (3:ℚ)/8192000000000, (1:ℚ)/24576000000000, (-7:ℚ)/24576000000000, (-1:ℚ)/1638400000000]]
noncomputable def imBern : List (List ℚ) := [
  [(799914814886891:ℚ)/1638400000000, (771442100090453:ℚ)/1638400000000, (6495796156449513:ℚ)/14336000000000, (11583773869205207:ℚ)/26624000000000, (303471549903517:ℚ)/728000000000, (20423015820307031:ℚ)/51251200000000, (33444485784301:ℚ)/88000000000, (59569718332352671:ℚ)/164736000000000, (14135028414472847:ℚ)/41184000000000, (10408299261526923:ℚ)/32032000000000, (245695396530191:ℚ)/800800000000, (210317883514779:ℚ)/728000000000, (49364864501531:ℚ)/182000000000, (3554103024413:ℚ)/14000000000, (118410786311:ℚ)/500000000, (5503490331:ℚ)/25000000],
  [(562014756370071:ℚ)/1146880000000, (2539183894385311:ℚ)/5376000000000, (109403998083687899:ℚ)/240844800000000, (174979682657481433:ℚ)/401408000000000, (272255175171282579:ℚ)/652288000000000, (245226381679985491:ℚ)/615014400000000, (170421732469961293:ℚ)/448448000000000, (64102286920618577:ℚ)/177408000000000, (1975902867587653:ℚ)/5765760000000, (14538155205767577:ℚ)/44844800000000, (8229602201281147:ℚ)/26906880000000, (17596101295197497:ℚ)/61152000000000, (343850082088631:ℚ)/1274000000000, (148386397220623:ℚ)/588000000000, (1410955259059:ℚ)/6000000000, (122267468143:ℚ)/560000000],
  [(201440502052451:ℚ)/409600000000, (6791486507083961:ℚ)/14336000000000, (68541587050393763:ℚ)/150528000000000, (68363628161612863:ℚ)/156549120000000, (436106487244576383:ℚ)/1043660800000000, (392552112532572719:ℚ)/984023040000000, (16357188074861511133:ℚ)/43051008000000000, (6660523241445977377:ℚ)/18450432000000000, (49315203105309961:ℚ)/144144000000000, (870145434489344369:ℚ)/2690688000000000, (2050622877568129:ℚ)/6726720000000, (35044947823443979:ℚ)/122304000000000, (16420029401850209:ℚ)/61152000000000, (78651860737461:ℚ)/313600000000, (19609776057227:ℚ)/84000000000, (2424617871551:ℚ)/11200000000],
  [(3537473091782151:ℚ)/7168000000000, (3648803150708927:ℚ)/7680000000000, (686980482838019491:ℚ)/1505280000000000, (2853215421096112857:ℚ)/6522880000000000, (3274132119833444951:ℚ)/7827456000000000, (17180238767663249263:ℚ)/43051008000000000, (109011097278861218279:ℚ)/287006720000000000, (133069144596561071033:ℚ)/369008640000000000, (143201276229965713:ℚ)/419328000000000, (5785763564069707807:ℚ)/17937920000000000, (204350602951031987:ℚ)/672672000000000, (69783202345027817:ℚ)/244608000000000, (1046939272011959:ℚ)/3920000000000, (5861187555559877:ℚ)/23520000000000, (778487911142377:ℚ)/3360000000000, (48067330682003:ℚ)/224000000000],
  [(1774690616775329:ℚ)/3584000000000, (8537484532756047:ℚ)/17920000000000, (43029253884527339:ℚ)/94080000000000, (27477013579467657:ℚ)/62720000000000, (819264712724873633:ℚ)/1956864000000000, (2864013181289747477:ℚ)/7175168000000000, (425622333680995021:ℚ)/1121120000000000, (2373368704696342757:ℚ)/6589440000000000, (25153650428632101109:ℚ)/73801728000000000, (8392200178475510963:ℚ)/26091520000000000, (1861529348909270899:ℚ)/6150144000000000, (370475986574284217:ℚ)/1304576000000000, (13534546241858043:ℚ)/50960000000000, (46578747063710089:ℚ)/188160000000000, (1724162254811:ℚ)/7500000000, (190527416134887:ℚ)/896000000000],
  [(534139393178009:ℚ)/1075200000000, (128402703243509:ℚ)/268800000000, (34493892188673359:ℚ)/75264000000000, (429249494987212351:ℚ)/978432000000000, (58563842750215181:ℚ)/139776000000000, (214820708716975987:ℚ)/538137600000000, (544462295673307523:ℚ)/1435033600000000, (1106073539495573503:ℚ)/3075072000000000, (4183338878820878417:ℚ)/12300288000000000, (2301034112356271841:ℚ)/7175168000000000, (798816762832315499:ℚ)/2649292800000000, (48620978212791263:ℚ)/172032000000000, (73817690554727407:ℚ)/279552000000000, (37007043519360527:ℚ)/150528000000000, (306480208394719:ℚ)/1344000000000, (226492198776121:ℚ)/1075200000000],
  [(89302832987157:ℚ)/179200000000, (429097579131549:ℚ)/896000000000, (1440018877640393:ℚ)/3136000000000, (35817173719817187:ℚ)/81536000000000, (136736562083633569:ℚ)/326144000000000, (26037806649075947:ℚ)/65228800000000, (34003250166388381:ℚ)/89689600000000, (828309548089451993:ℚ)/2306304000000000, (6260636250198490631:ℚ)/18450432000000000, (131076573363859659:ℚ)/410009600000000, (430954162876969461:ℚ)/1435033600000000, (366875960313572481:ℚ)/1304576000000000, (1369662080737615993:ℚ)/5218304000000000, (97983190842723183:ℚ)/401408000000000, (3241875407067681:ℚ)/14336000000000, (85447936578899:ℚ)/409600000000],
  [(6398088181421:ℚ)/12800000000, (15362123430547:ℚ)/32000000000, (1236537404432297:ℚ)/2688000000000, (146364184329809:ℚ)/332800000000, (4187961829470413:ℚ)/9984000000000, (2789277099352399:ℚ)/6988800000000, (194130392236280663:ℚ)/512512000000000, (7159664911477817:ℚ)/19968000000000, (29739473179566977:ℚ)/87859200000000, (163305016711973007:ℚ)/512512000000000, (367835667667612723:ℚ)/1230028800000000, (156418371627084473:ℚ)/559104000000000, (19444736662949229:ℚ)/74547200000000, (10420833007653251:ℚ)/43008000000000, (5509602165176837:ℚ)/24576000000000, (338374937581747:ℚ)/1638400000000]]
noncomputable def rePower : List (List ℚ) := [
  [(973393743:ℚ)/20000000, (5503490331:ℚ)/50000000, (-25022939073:ℚ)/400000000, (5053576357:ℚ)/800000000, (1496102161:ℚ)/800000000, (-1551557643:ℚ)/3200000000, (160404139:ℚ)/6400000000, (53205217:ℚ)/12800000000, (-2076169:ℚ)/3200000000, (915159:ℚ)/51200000000, (315029:ℚ)/102400000000, (-6227:ℚ)/20480000000, (1777:ℚ)/409600000000, (773:ℚ)/819200000000, (-13:ℚ)/204800000000, (1:ℚ)/3276800000000, (1:ℚ)/6553600000000],
  [(25022939073:ℚ)/400000000, (-15160729071:ℚ)/800000000, (-4488306483:ℚ)/400000000, (1551557643:ℚ)/320000000, (-481212417:ℚ)/1280000000, (-1117309557:ℚ)/12800000000, (14533183:ℚ)/800000000, (-8236431:ℚ)/12800000000, (-2835261:ℚ)/20480000000, (68497:ℚ)/4096000000, (-58641:ℚ)/204800000000, (-30147:ℚ)/409600000000, (1183:ℚ)/204800000000, (-21:ℚ)/655360000000, (-3:ℚ)/163840000000, 0, 0],
  [(1496102161:ℚ)/800000000, (-1551557643:ℚ)/640000000, (481212417:ℚ)/1280000000, (372436519:ℚ)/2560000000, (-14533183:ℚ)/320000000, (57655017:ℚ)/25600000000, (6615609:ℚ)/10240000000, (-205491:ℚ)/2048000000, (175923:ℚ)/81920000000, (110539:ℚ)/163840000000, (-13013:ℚ)/204800000000, (273:ℚ)/655360000000, (91:ℚ)/327680000000, 0, 0, 0, 0],
  [(-160404139:ℚ)/6400000000, (-372436519:ℚ)/12800000000, (14533183:ℚ)/800000000, (-19218339:ℚ)/12800000000, (-6615609:ℚ)/10240000000, (1438437:ℚ)/10240000000, (-410487:ℚ)/102400000000, (-331617:ℚ)/204800000000, (39039:ℚ)/204800000000, (-1001:ℚ)/655360000000, (-1001:ℚ)/819200000000, 0, 0, 0, 0, 0, 0],
  [(-2076169:ℚ)/3200000000, (8236431:ℚ)/51200000000, (2835261:ℚ)/20480000000, (-205491:ℚ)/4096000000, (175923:ℚ)/81920000000, (994851:ℚ)/819200000000, (-39039:ℚ)/204800000000, (1287:ℚ)/655360000000, (1287:ℚ)/655360000000, 0, 0, 0, 0, 0, 0, 0, 0],
  [(-315029:ℚ)/102400000000, (68497:ℚ)/20480000000, (-58641:ℚ)/204800000000, (-110539:ℚ)/409600000000, (13013:ℚ)/204800000000, (-3003:ℚ)/3276800000000, (-1001:ℚ)/819200000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(1777:ℚ)/409600000000, (10049:ℚ)/819200000000, (-1183:ℚ)/204800000000, (91:ℚ)/655360000000, (91:ℚ)/327680000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(13:ℚ)/204800000000, (-3:ℚ)/655360000000, (-3:ℚ)/163840000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(1:ℚ)/6553600000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
noncomputable def entry (m : List (List ℚ)) (i j : ℕ) : ℚ := (m.getD i []).getD j 0
noncomputable def aim (i : Fin 8) (j : Fin 16) : ℚ := entry imPower i j
noncomputable def rim (i : Fin 8) (j : Fin 16) : ℚ := entry imRows i j
noncomputable def bim (i : Fin 8) (j : Fin 16) : ℚ := entry imBern i j
theorem im_checked :
    (∀ i : Fin 8, ∀ j : Fin 16, rim i j=RH102Proof.TaoZetaNumerics.bernsteinTransform 15 (aim i) j) ∧
    (∀ i : Fin 8, ∀ j : Fin 16, bim i j=RH102Proof.TaoZetaNumerics.bernsteinTransform 7 (fun u => rim u j) i) ∧
    (∀ i : Fin 8, ∀ j : Fin 16, (1:ℚ)≤bim i j) := by decide +kernel
noncomputable def are (i : Fin 9) (j : Fin 17) : ℚ := entry rePower i j
noncomputable def c (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
noncomputable def imaginaryValue (x y : ℝ) : ℝ :=
  (-5503490331:ℝ)/25000000*x^1*y^0 +
  (25022939073:ℝ)/50000000*x^1*y^1 +
  (-15160729071:ℝ)/100000000*x^1*y^2 +
  (5053576357:ℝ)/100000000*x^3*y^0 +
  (-1496102161:ℝ)/12500000*x^1*y^3 +
  (1496102161:ℝ)/12500000*x^3*y^1 +
  (1551557643:ℝ)/20000000*x^1*y^4 +
  (-1551557643:ℝ)/10000000*x^3*y^2 +
  (1551557643:ℝ)/100000000*x^5*y^0 +
  (-481212417:ℝ)/50000000*x^1*y^5 +
  (160404139:ℝ)/5000000*x^3*y^3 +
  (-481212417:ℝ)/50000000*x^5*y^1 +
  (-372436519:ℝ)/100000000*x^1*y^6 +
  (372436519:ℝ)/20000000*x^3*y^4 +
  (-1117309557:ℝ)/100000000*x^5*y^2 +
  (53205217:ℝ)/100000000*x^7*y^0 +
  (2076169:ℝ)/1562500*x^1*y^7 +
  (-14533183:ℝ)/1562500*x^3*y^5 +
  (14533183:ℝ)/1562500*x^5*y^3 +
  (-2076169:ℝ)/1562500*x^7*y^1 +
  (-8236431:ℝ)/100000000*x^1*y^8 +
  (19218339:ℝ)/25000000*x^3*y^6 +
  (-57655017:ℝ)/50000000*x^5*y^4 +
  (8236431:ℝ)/25000000*x^7*y^2 +
  (-915159:ℝ)/100000000*x^9*y^0 +
  (-315029:ℝ)/10000000*x^1*y^9 +
  (945087:ℝ)/2500000*x^3*y^7 +
  (-19846827:ℝ)/25000000*x^5*y^5 +
  (945087:ℝ)/2500000*x^7*y^3 +
  (-315029:ℝ)/10000000*x^9*y^1 +
  (68497:ℝ)/10000000*x^1*y^10 +
  (-205491:ℝ)/2000000*x^3*y^8 +
  (1438437:ℝ)/5000000*x^5*y^6 +
  (-205491:ℝ)/1000000*x^7*y^4 +
  (68497:ℝ)/2000000*x^9*y^2 +
  (-6227:ℝ)/10000000*x^11*y^0 +
  (-5331:ℝ)/25000000*x^1*y^11 +
  (19547:ℝ)/5000000*x^3*y^9 +
  (-175923:ℝ)/12500000*x^5*y^7 +
  (175923:ℝ)/12500000*x^7*y^5 +
  (-19547:ℝ)/5000000*x^9*y^3 +
  (5331:ℝ)/25000000*x^11*y^1 +
  (-10049:ℝ)/100000000*x^1*y^12 +
  (110539:ℝ)/50000000*x^3*y^10 +
  (-994851:ℝ)/100000000*x^5*y^8 +
  (331617:ℝ)/25000000*x^7*y^6 +
  (-110539:ℝ)/20000000*x^9*y^4 +
  (30147:ℝ)/50000000*x^11*y^2 +
  (-773:ℝ)/100000000*x^13*y^0 +
  (91:ℝ)/6250000*x^1*y^13 +
  (-1183:ℝ)/3125000*x^3*y^11 +
  (13013:ℝ)/6250000*x^5*y^9 +
  (-5577:ℝ)/1562500*x^7*y^7 +
  (13013:ℝ)/6250000*x^9*y^5 +
  (-1183:ℝ)/3125000*x^11*y^3 +
  (91:ℝ)/6250000*x^13*y^1 +
  (-3:ℝ)/20000000*x^1*y^14 +
  (91:ℝ)/20000000*x^3*y^12 +
  (-3003:ℝ)/100000000*x^5*y^10 +
  (1287:ℝ)/20000000*x^7*y^8 +
  (-1001:ℝ)/20000000*x^9*y^6 +
  (273:ℝ)/20000000*x^11*y^4 +
  (-21:ℝ)/20000000*x^13*y^2 +
  (1:ℝ)/100000000*x^15*y^0 +
  (-1:ℝ)/6250000*x^1*y^15 +
  (7:ℝ)/1250000*x^3*y^13 +
  (-273:ℝ)/6250000*x^5*y^11 +
  (143:ℝ)/1250000*x^7*y^9 +
  (-143:ℝ)/1250000*x^9*y^7 +
  (273:ℝ)/6250000*x^11*y^5 +
  (-7:ℝ)/1250000*x^13*y^3 +
  (1:ℝ)/6250000*x^15*y^1
lemma complex_identity (x y : ℝ) :
    (∑ n ∈ Finset.range 32, (c n:ℂ)*((y:ℂ)-Complex.I*x)^n)-
      (RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue 8 16 are
        (4*x^2) (2*y):ℂ)=Complex.I*(imaginaryValue x y:ℂ) := by
  norm_num [c,rounded,roundedNumerators,Finset.sum_range_succ,
    RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue,
    are,entry,rePower,Fin.sum_univ_succ,imaginaryValue]
  push_cast
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod]
  try simp only [Complex.I_sq,Complex.I_pow_three,pow_zero,pow_one]
  apply Complex.ext <;> simp [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im] <;> ring
lemma quotient_identity (x y : ℝ) :
    imaginaryValue x y=-x*RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue
      7 15 aim (4*x^2) (2*y+1) := by
  norm_num [imaginaryValue,RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue,
    aim,entry,imPower,Fin.sum_univ_succ]
  ring
lemma rotated_variable (s : ℂ) :
    RH102Proof.CertifiedLocalXi.rotatedVariable (203/2) s=
      ((s.im-203/2:ℝ):ℂ)-Complex.I*((s.re-1/2:ℝ):ℂ) := by
  apply Complex.ext <;> simp [RH102Proof.CertifiedLocalXi.rotatedVariable,
    RH102Proof.CertifiedLocalXi.center] <;> ring
lemma imaginary_identity (s : ℂ) :
    (RH102Proof.CertifiedLocalXi.rotatedPolynomial c (203/2) s).im=
      -(s.re-1/2)*RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue 7 15 aim
        (4*(s.re-1/2)^2) (2*(s.im-101)) := by
  have h := congrArg Complex.im (complex_identity (s.re-1/2) (s.im-203/2))
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,sub_zero,zero_add] at h
  rw [quotient_identity] at h
  have he : 2*(s.im-203/2)+1=2*(s.im-101) := by ring
  rw [he] at h
  unfold RH102Proof.CertifiedLocalXi.rotatedPolynomial
  simp only [rotated_variable]
  exact h
end RH102Numerical

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace RH102Numerical
end RH102Numerical


set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH102Numerical
lemma imaginary_half_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 101 ≤ s.im) (hb : s.im ≤ 203/2) :
    |s.re-1/2| ≤ |(RH102Proof.CertifiedLocalXi.rotatedPolynomial proposed (203/2) s).im| := by
  let x : Set.Icc (0:ℝ) 1 := ⟨4*(s.re-1/2)^2,⟨by positivity,by
    nlinarith [mul_nonneg h0 (show 0 ≤ 1-s.re by linarith)]⟩⟩
  let y : Set.Icc (0:ℝ) 1 := ⟨2*(s.im-101),⟨by linarith,by linarith⟩⟩
  have hr : ∀ i, rim i=RH102Proof.TaoZetaNumerics.bernsteinTransform 15 (aim i) := by
    intro i; funext j; exact im_checked.1 i j
  have hc : ∀ j, (fun i => bim i j)=RH102Proof.TaoZetaNumerics.bernsteinTransform 7
      (fun i => rim i j) := by intro j; funext i; exact im_checked.2.1 i j
  have hl : ∀ i j, (1:ℝ) ≤ (bim i j:ℝ) := by intro i j; exact_mod_cast im_checked.2.2 i j
  have h := RH102Proof.CertifiedLocalPolynomial.bivariate_bernstein_lower 7 15 aim rim bim hr hc 1 hl x y
  change 1 ≤ RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue 7 15 aim
    (4*(s.re-1/2)^2) (2*(s.im-101)) at h
  have he : c=proposed := rfl
  rw [←he,imaginary_identity,abs_mul,abs_neg,abs_of_nonneg (by linarith :
    0 ≤ RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue 7 15 aim
      (4*(s.re-1/2)^2) (2*(s.im-101)))]
  exact le_mul_of_one_le_right (abs_nonneg _) h
end RH102Numerical

theorem solution (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ha : 101 ≤ s.im) (hb : s.im ≤ 203/2) :
    |s.re-1/2| ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH101To102RoundedCoefficients 32 (203/2) s).im| := by
  simpa only [RH102Numerical.proposed,RH102Numerical.rounded,RH102Numerical.roundedNumerators,
    RH102Proof.CertifiedLocalXi.rotatedPolynomial,RH102Proof.CertifiedLocalXi.rotatedVariable,
    RH102Proof.CertifiedLocalXi.center,TaoFivePrimes_RHLocalRoundedPolynomial,
    RH1000Analytic.CertifiedLocalXi.center,TaoFivePrimes_RH101To102RoundedCoefficients,
    Complex.ofReal_div] using RH102Numerical.imaginary_half_certificate s h0 h1 ha hb
