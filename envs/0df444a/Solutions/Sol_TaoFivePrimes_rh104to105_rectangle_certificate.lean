-- Prove2me | solution 1 for TaoFivePrimes.rh104to105_rectangle_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T05:16:45.470327+00:00
-- url     : https://prove2.me/submissions/d2f75b6d-13fd-49fb-9315-5e981c71a2da

import Mathlib
import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH104To105RoundedCoefficients
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.ambiguousOpen false
namespace RH105Proof
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

end RH105Proof

namespace RH105Numerical
open Finset
noncomputable def roundedNumerators : List ℤ := [-88203576297, 50586724471, 127063442307, -106435864734, 14801450400, 9771068448, -3923706726, 279294347, 124333424, -30822014, 1197646, 532787, -88111, 1533, 1033, -118, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def rounded (n : ℕ) : ℤ := roundedNumerators.getD n 0
end RH105Numerical

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH105Numerical
open Finset

noncomputable def proposed (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
end RH105Numerical

open Complex Metric MeasureTheory Set Finset
open scoped ComplexConjugate Topology
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH105Proof
namespace TaoZetaCertificate
open RH105Proof.ZetaSix

end TaoZetaCertificate
namespace CertifiedLocalXi
open RH105Proof.ZetaSix

end CertifiedLocalXi
end RH105Proof

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace RH105Proof.CertifiedLocalXi
open Complex Metric
end RH105Proof.CertifiedLocalXi
namespace RH105Numerical
open Complex
end RH105Numerical

namespace RH105Numerical
noncomputable def powerMatrix : List (List ℚ) := [
  [(1779165907994589:ℚ)/2621440000000, (10478781165768503:ℚ)/6553600000000, (-1199747193320937:ℚ)/409600000000, (811597199231:ℚ)/800000000, (50983584849063:ℚ)/204800000000, (-22415759076769:ℚ)/102400000000, (189466840237:ℚ)/5120000000, (32014222513:ℚ)/6400000000, (-13454542761:ℚ)/5120000000, (3464527921:ℚ)/12800000000, (50652321:ℚ)/1600000000, (-2068943:ℚ)/200000000, (108891:ℚ)/160000000, (34587:ℚ)/400000000, (-1833:ℚ)/100000000, (21:ℚ)/25000000, (17:ℚ)/200000000, (-1:ℚ)/100000000],
  [(1199747193320937:ℚ)/1638400000000, (-2434791597693:ℚ)/3200000000, (-152950754547189:ℚ)/409600000000, (22415759076769:ℚ)/40960000000, (-568400520711:ℚ)/4096000000, (-672298672773:ℚ)/25600000000, (94181799327:ℚ)/5120000000, (-31180751289:ℚ)/12800000000, (-455870889:ℚ)/1280000000, (22758373:ℚ)/160000000, (-3593403:ℚ)/320000000, (-1348893:ℚ)/800000000, (166803:ℚ)/400000000, (-441:ℚ)/20000000, (-51:ℚ)/20000000, (17:ℚ)/50000000, 0, 0],
  [(50983584849063:ℚ)/3276800000000, (-22415759076769:ℚ)/327680000000, (568400520711:ℚ)/16384000000, (224099557591:ℚ)/20480000000, (-94181799327:ℚ)/8192000000, (218265259023:ℚ)/102400000000, (1063698741:ℚ)/2560000000, (-68275119:ℚ)/320000000, (10780209:ℚ)/512000000, (4945941:ℚ)/1280000000, (-1834833:ℚ)/1600000000, (5733:ℚ)/80000000, (1547:ℚ)/160000000, (-119:ℚ)/80000000, 0, 0, 0, 0],
  [(-189466840237:ℚ)/327680000000, (-224099557591:ℚ)/409600000000, (94181799327:ℚ)/81920000000, (-72755086341:ℚ)/204800000000, (-1063698741:ℚ)/10240000000, (477925833:ℚ)/6400000000, (-25153821:ℚ)/2560000000, (-14837823:ℚ)/6400000000, (5504499:ℚ)/6400000000, (-21021:ℚ)/320000000, (-17017:ℚ)/1600000000, (1547:ℚ)/800000000, 0, 0, 0, 0, 0, 0],
  [(-13454542761:ℚ)/1310720000000, (31180751289:ℚ)/3276800000000, (455870889:ℚ)/81920000000, (-68275119:ℚ)/10240000000, (10780209:ℚ)/8192000000, (44513469:ℚ)/102400000000, (-5504499:ℚ)/25600000000, (27027:ℚ)/1280000000, (21879:ℚ)/5120000000, (-2431:ℚ)/2560000000, 0, 0, 0, 0, 0, 0, 0, 0],
  [(-50652321:ℚ)/1638400000000, (22758373:ℚ)/204800000000, (-3593403:ℚ)/81920000000, (-4945941:ℚ)/204800000000, (1834833:ℚ)/102400000000, (-63063:ℚ)/25600000000, (-17017:ℚ)/25600000000, (2431:ℚ)/12800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(108891:ℚ)/655360000000, (449631:ℚ)/1638400000000, (-166803:ℚ)/409600000000, (1911:ℚ)/20480000000, (1547:ℚ)/40960000000, (-1547:ℚ)/102400000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(1833:ℚ)/1638400000000, (-63:ℚ)/81920000000, (-51:ℚ)/81920000000, (17:ℚ)/40960000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [(17:ℚ)/13107200000000, (-17:ℚ)/6553600000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
noncomputable def rowMatrix : List (List ℚ) := [
  [(1779165907994589:ℚ)/2621440000000, (172186664511077071:ℚ)/222822400000000, (188345238069330329:ℚ)/222822400000000, (1000186265335524283:ℚ)/1114112000000000, (427449742791751971:ℚ)/458752000000000, (19242858150509987477:ℚ)/20276838400000000, (19286651203722118707:ℚ)/20276838400000000, (29950385953928975793:ℚ)/31863603200000000, (146105354677257228299:ℚ)/159318016000000000, (28172284663793274913:ℚ)/31863603200000000, (5370955074733807851:ℚ)/6372720640000000, (16110760064954499429:ℚ)/20276838400000000, (3004180092474329711:ℚ)/4055367680000000, (1065144182549511209:ℚ)/1559756800000000, (138611385909645033:ℚ)/222822400000000, (124658865819339071:ℚ)/222822400000000, (110531668261765921:ℚ)/222822400000000, (5672415930791391:ℚ)/13107200000000],
  [(1199747193320937:ℚ)/1638400000000, (19149088988437113:ℚ)/27852800000000, (7130400125257881:ℚ)/11141120000000, (32897704039310933:ℚ)/55705600000000, (3096148560556147:ℚ)/5734400000000, (47648304902081861:ℚ)/97484800000000, (17751812855345489:ℚ)/40553676800000, (3085637343654558809:ℚ)/7965900800000000, (1346716661168543869:ℚ)/3982950400000000, (1156844685166133173:ℚ)/3982950400000000, (8820056763517243:ℚ)/36044800000000, (1019708688413338003:ℚ)/5069209600000000, (101425337683234671:ℚ)/633651200000000, (174325951544937:ℚ)/1433600000000, (4784697202538811:ℚ)/55705600000000, (2953819728183819:ℚ)/55705600000000, (641740442621517:ℚ)/27852800000000, (-6650029815219:ℚ)/1638400000000],
  [(50983584849063:ℚ)/3276800000000, (642563351666381:ℚ)/55705600000000, (216307886958233:ℚ)/27852800000000, (23777460741469:ℚ)/5570560000000, (58667159536197:ℚ)/55705600000000, (-271255829115569:ℚ)/144834560000000, (-40798193468351:ℚ)/9052160000000, (-248040474269989:ℚ)/36208640000000, (-6450280403217033:ℚ)/724172800000000, (-7737491480934291:ℚ)/724172800000000, (-4414725807809573:ℚ)/362086400000000, (-4867332589502113:ℚ)/362086400000000, (-10462854104370931:ℚ)/724172800000000, (-848053497875829:ℚ)/55705600000000, (-219838020387029:ℚ)/13926400000000, (-5622775290599:ℚ)/348160000000, (-181972890611581:ℚ)/11141120000000, (-10717129598687:ℚ)/655360000000],
  [(-189466840237:ℚ)/327680000000, (-17001079650509:ℚ)/27852800000000, (-35324046765111:ℚ)/55705600000000, (-181020636335527:ℚ)/278528000000000, (-22921208845591:ℚ)/34816000000000, (-5974598472807:ℚ)/9052160000000, (-474721360873841:ℚ)/724172800000000, (-93495259718801:ℚ)/144834560000000, (-1141719539982111:ℚ)/1810432000000000, (-65118446417467:ℚ)/106496000000000, (-426267830430471:ℚ)/724172800000000, (-407498348182971:ℚ)/724172800000000, (-7440409408037:ℚ)/13926400000000, (-35082587032479:ℚ)/69632000000000, (-131434260292869:ℚ)/278528000000000, (-24449509356341:ℚ)/55705600000000, (-11288737549869:ℚ)/27852800000000, (-121717916421:ℚ)/327680000000],
  [(-13454542761:ℚ)/1310720000000, (-1081274632107:ℚ)/111411200000000, (-1014354420639:ℚ)/111411200000000, (-188793580437:ℚ)/22282240000000, (-6098021142183:ℚ)/779878400000000, (-5577948035937:ℚ)/779878400000000, (-5053758376917:ℚ)/779878400000000, (-647299825941:ℚ)/111411200000000, (-573577612581:ℚ)/111411200000000, (-501441024323:ℚ)/111411200000000, (-431450030567:ℚ)/111411200000000, (-509717648539:ℚ)/155975680000000, (-2098211665631:ℚ)/779878400000000, (-1671309835529:ℚ)/779878400000000, (-10669580251:ℚ)/6553600000000, (-127808586413:ℚ)/111411200000000, (-78166202669:ℚ)/111411200000000, (-382715759:ℚ)/1310720000000],
  [(-50652321:ℚ)/1638400000000, (-679022473:ℚ)/27852800000000, (-1011877993:ℚ)/55705600000000, (-3428282157:ℚ)/278528000000000, (-476174059:ℚ)/69632000000000, (-24722053:ℚ)/13926400000000, (159706949:ℚ)/55705600000000, (394400941:ℚ)/55705600000000, (1512658449:ℚ)/139264000000000, (1979619777:ℚ)/139264000000000, (191032103:ℚ)/11141120000000, (1095627539:ℚ)/55705600000000, (75879:ℚ)/3481600000, (819651691:ℚ)/34816000000000, (6944323669:ℚ)/278528000000000, (1447531817:ℚ)/55705600000000, (744360587:ℚ)/27852800000000, (44522451:ℚ)/1638400000000],
  [(108891:ℚ)/655360000000, (10154997:ℚ)/55705600000000, (340233:ℚ)/1740800000000, (2865189:ℚ)/13926400000000, (27961:ℚ)/131072000000, (12164739:ℚ)/55705600000000, (6157293:ℚ)/27852800000000, (1234333:ℚ)/5570560000000, (28851:ℚ)/131072000000, (12080529:ℚ)/55705600000000, (2952717:ℚ)/13926400000000, (28659:ℚ)/139264000000, (11049429:ℚ)/55705600000000, (10578719:ℚ)/55705600000000, (5030679:ℚ)/27852800000000, (4753311:ℚ)/27852800000000, (8923039:ℚ)/55705600000000, (489309:ℚ)/3276800000000],
  [(1833:ℚ)/1638400000000, (29901:ℚ)/27852800000000, (57027:ℚ)/55705600000000, (54031:ℚ)/55705600000000, (1589:ℚ)/1740800000000, (5939:ℚ)/6963200000000, (44057:ℚ)/55705600000000, (40517:ℚ)/55705600000000, (18463:ℚ)/27852800000000, (16659:ℚ)/27852800000000, (29727:ℚ)/55705600000000, (26187:ℚ)/55705600000000, (5683:ℚ)/13926400000000, (4849:ℚ)/13926400000000, (16213:ℚ)/55705600000000, (13217:ℚ)/55705600000000, (5221:ℚ)/27852800000000, (233:ℚ)/1638400000000],
  [(17:ℚ)/13107200000000, (3:ℚ)/2621440000000, (13:ℚ)/13107200000000, (11:ℚ)/13107200000000, (9:ℚ)/13107200000000, (7:ℚ)/13107200000000, (1:ℚ)/2621440000000, (3:ℚ)/13107200000000, (1:ℚ)/13107200000000, (-1:ℚ)/13107200000000, (-3:ℚ)/13107200000000, (-1:ℚ)/2621440000000, (-7:ℚ)/13107200000000, (-9:ℚ)/13107200000000, (-11:ℚ)/13107200000000, (-13:ℚ)/13107200000000, (-3:ℚ)/2621440000000, (-17:ℚ)/13107200000000]]
noncomputable def bernsteinMatrix : List (List ℚ) := [
  [(1779165907994589:ℚ)/2621440000000, (172186664511077071:ℚ)/222822400000000, (188345238069330329:ℚ)/222822400000000, (1000186265335524283:ℚ)/1114112000000000, (427449742791751971:ℚ)/458752000000000, (19242858150509987477:ℚ)/20276838400000000, (19286651203722118707:ℚ)/20276838400000000, (29950385953928975793:ℚ)/31863603200000000, (146105354677257228299:ℚ)/159318016000000000, (28172284663793274913:ℚ)/31863603200000000, (5370955074733807851:ℚ)/6372720640000000, (16110760064954499429:ℚ)/20276838400000000, (3004180092474329711:ℚ)/4055367680000000, (1065144182549511209:ℚ)/1559756800000000, (138611385909645033:ℚ)/222822400000000, (124658865819339071:ℚ)/222822400000000, (110531668261765921:ℚ)/222822400000000, (5672415930791391:ℚ)/13107200000000],
  [(5047788366646941:ℚ)/6553600000000, (23916969187439273:ℚ)/27852800000000, (412342476764950063:ℚ)/445644800000000, (2164861050867603231:ℚ)/2228224000000000, (458411228397313441:ℚ)/458752000000000, (20481714077964115863:ℚ)/20276838400000000, (40792279014362423539:ℚ)/40553676800000000, (12597281850302502079:ℚ)/12745441280000000, (2939210345828845147:ℚ)/3063808000000000, (14664564674479704043:ℚ)/15931801600000000, (55658783292075389213:ℚ)/63727206400000000, (4748746974046048123:ℚ)/5793382400000000, (15426601813104587239:ℚ)/20276838400000000, (155550358851374663:ℚ)/222822400000000, (282007469021828877:ℚ)/445644800000000, (252271551366861961:ℚ)/445644800000000, (55586704352193719:ℚ)/111411200000000, (1416441475244043:ℚ)/3276800000000],
  [(19779562767788199:ℚ)/22937600000000, (73701823038366273:ℚ)/77987840000000, (56014760237259093:ℚ)/55705600000000, (4076956185880813043:ℚ)/3899392000000000, (148564812032974187:ℚ)/139264000000000, (5429803431568166601:ℚ)/5069209600000000, (1343897747197677297:ℚ)/1267302400000000, (10508981553579333847:ℚ)/10138419200000000, (279163220900105433027:ℚ)/278806528000000000, (53329176458147127903:ℚ)/55761305600000000, (2015309314610726391:ℚ)/2230452224000000, (658489772622647431:ℚ)/779878400000000, (988865019358322187:ℚ)/1267302400000000, (277928196967964561:ℚ)/389939200000000, (7374214924292197:ℚ)/11468800000000, (89238915478616439:ℚ)/155975680000000, (39089808978800239:ℚ)/77987840000000, (9890056362533309:ℚ)/22937600000000],
  [(10952187657487037:ℚ)/11468800000000, (100584263081879219:ℚ)/97484800000000, (847021429179858949:ℚ)/779878400000000, (174638188564110931:ℚ)/155975680000000, (2211617428975269767:ℚ)/1949696000000000, (163965129367833763:ℚ)/144834560000000, (11302543593493278367:ℚ)/10138419200000000, (120942807976607619139:ℚ)/111522611200000000, (72691617311376693167:ℚ)/69701632000000000, (138276223991421797597:ℚ)/139403264000000000, (1351666577656118427:ℚ)/1448345600000000, (1761091535286340227:ℚ)/2027683840000000, (4051605625403185713:ℚ)/5069209600000000, (1417138721564256283:ℚ)/1949696000000000, (2544669555808747779:ℚ)/3899392000000000, (450458005493568953:ℚ)/779878400000000, (19611433625767243:ℚ)/38993920000000, (615717114935277:ℚ)/1433600000000],
  [(6010364181908983:ℚ)/5734400000000, (545396344621952653:ℚ)/487424000000000, (568771724666390131:ℚ)/487424000000000, (290966043533821961:ℚ)/243712000000000, (4100870835659781079:ℚ)/3411968000000000, (52913844764130250119:ℚ)/44355584000000000, (51852653048134926119:ℚ)/44355584000000000, (5636471162305495053:ℚ)/4978688000000000, (75568681568123581681:ℚ)/69701632000000000, (185939296536254579:ℚ)/181043200000000, (67087671626135755129:ℚ)/69701632000000000, (3957396079742064311:ℚ)/4435558400000000, (36269087222294019487:ℚ)/44355584000000000, (2526197185994432147:ℚ)/3411968000000000, (64496046233317493:ℚ)/97484800000000, (141956054386022181:ℚ)/243712000000000, (245683141538742651:ℚ)/487424000000000, (2449797628231801:ℚ)/5734400000000],
  [(3273820429036127:ℚ)/2867200000000, (7350700417731807:ℚ)/6092800000000, (48661880002258909:ℚ)/38993920000000, (247270796660594537:ℚ)/194969600000000, (4331418024882269683:ℚ)/3411968000000000, (11121763973795388517:ℚ)/8871116800000000, (4339837455611937609:ℚ)/3548446720000000, (32884982801995690169:ℚ)/27880652800000000, (784212028239028461:ℚ)/697016320000000, (406627758612732363:ℚ)/382976000000000, (27637531388891754483:ℚ)/27880652800000000, (191065441787356043:ℚ)/208732160000000, (7412492622394628757:ℚ)/8871116800000000, (2570454088497648463:ℚ)/3411968000000000, (5488901085334761:ℚ)/8192000000000, (22879627272050743:ℚ)/38993920000000, (4918568649976217:ℚ)/9748480000000, (608315878549927:ℚ)/1433600000000],
  [(1771965529163927:ℚ)/1433600000000, (31544743279468869:ℚ)/24371200000000, (32394400463913707:ℚ)/24371200000000, (9349617411538383:ℚ)/6963200000000, (142560337864243189:ℚ)/106624000000000, (2914935490297609679:ℚ)/2217779200000000, (1415851053117854273:ℚ)/1108889600000000, (1709880327597812703:ℚ)/1394032640000000, (4062419040429355483:ℚ)/3485081600000000, (19099051558944291339:ℚ)/17425408000000000, (3553334021822374851:ℚ)/3485081600000000, (4160576221512543219:ℚ)/4435558400000000, (945781216393521661:ℚ)/1108889600000000, (653183115984790547:ℚ)/852992000000000, (5162620375513113:ℚ)/7616000000000, (822234589430871:ℚ)/1392640000000, (2458752515162743:ℚ)/4874240000000, (603307004353821:ℚ)/1433600000000],
  [(136267238692471:ℚ)/102400000000, (1203405815567847:ℚ)/870400000000, (9822992550151819:ℚ)/6963200000000, (9868783928870949:ℚ)/6963200000000, (171155984177286011:ℚ)/121856000000000, (87118533803300833:ℚ)/63365120000000, (843004845723668087:ℚ)/633651200000000, (74583569610261561:ℚ)/58572800000000, (150088232442690793:ℚ)/124467200000000, (1406352013950004131:ℚ)/1244672000000000, (1042935422525499873:ℚ)/995737600000000, (86911376354907477:ℚ)/90521600000000, (275535814042558301:ℚ)/316825600000000, (13535720438402633:ℚ)/17408000000000, (23852167727225373:ℚ)/34816000000000, (4132407916479019:ℚ)/6963200000000, (876857331164069:ℚ)/1740800000000, (10668093848969:ℚ)/25600000000],
  [(73007921108881:ℚ)/51200000000, (256102697849571:ℚ)/174080000000, (1298985838947337:ℚ)/870400000000, (6492821494386097:ℚ)/4352000000000, (1281297509988581:ℚ)/870400000000, (113680474981596773:ℚ)/79206400000000, (4384022835130527:ℚ)/3168256000000, (164273069761649107:ℚ)/124467200000000, (70473604284603017:ℚ)/56576000000000, (723964182197779141:ℚ)/622336000000000, (133766918185187439:ℚ)/124467200000000, (77756048357589839:ℚ)/79206400000000, (70166656287737951:ℚ)/79206400000000, (24028831334723101:ℚ)/30464000000000, (602059616466461:ℚ)/870400000000, (20746487612453:ℚ)/34816000000, (437248725579377:ℚ)/870400000000, (4218750714547:ℚ)/10240000000]]
noncomputable def entry (m : List (List ℚ)) (i j : ℕ) : ℚ := (m.getD i []).getD j 0
noncomputable def a (i : Fin 9) (j : Fin 18) : ℚ := entry powerMatrix i j
noncomputable def r (i : Fin 9) (j : Fin 18) : ℚ := entry rowMatrix i j
noncomputable def b (i : Fin 9) (j : Fin 18) : ℚ := entry bernsteinMatrix i j
theorem bernstein_checked :
    (∀ i : Fin 9, ∀ j : Fin 18, r i j=RH105Proof.TaoZetaNumerics.bernsteinTransform 17 (a i) j) ∧
    (∀ i : Fin 9, ∀ j : Fin 18, b i j=RH105Proof.TaoZetaNumerics.bernsteinTransform 8 (fun u => r u j) i) ∧
    (∀ i : Fin 9, ∀ j : Fin 18, (1:ℚ) ≤ b i j) := by decide +kernel
end RH105Numerical

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace RH105Numerical
noncomputable def c (n : ℕ) : ℝ := (rounded n:ℝ)/(10^8:ℝ)
noncomputable def imaginaryValue (x y : ℝ) : ℝ :=
  (-50586724471:ℝ)/100000000*x^1*y^0 +
  (-127063442307:ℝ)/50000000*x^1*y^1 +
  (159653797101:ℝ)/50000000*x^1*y^2 +
  (-53217932367:ℝ)/50000000*x^3*y^0 +
  (-18501813:ℝ)/31250*x^1*y^3 +
  (18501813:ℝ)/31250*x^3*y^1 +
  (-305345889:ℝ)/625000*x^1*y^4 +
  (305345889:ℝ)/312500*x^3*y^2 +
  (-305345889:ℝ)/3125000*x^5*y^0 +
  (5885560089:ℝ)/25000000*x^1*y^5 +
  (-1961853363:ℝ)/2500000*x^3*y^3 +
  (5885560089:ℝ)/25000000*x^5*y^1 +
  (-1955060429:ℝ)/100000000*x^1*y^6 +
  (1955060429:ℝ)/20000000*x^3*y^4 +
  (-5865181287:ℝ)/100000000*x^5*y^2 +
  (279294347:ℝ)/100000000*x^7*y^0 +
  (-7770839:ℝ)/781250*x^1*y^7 +
  (54395873:ℝ)/781250*x^3*y^5 +
  (-54395873:ℝ)/781250*x^5*y^3 +
  (7770839:ℝ)/781250*x^7*y^1 +
  (138699063:ℝ)/50000000*x^1*y^8 +
  (-323631147:ℝ)/12500000*x^3*y^6 +
  (970893441:ℝ)/25000000*x^5*y^4 +
  (-138699063:ℝ)/12500000*x^7*y^2 +
  (15411007:ℝ)/50000000*x^9*y^0 +
  (-598823:ℝ)/5000000*x^1*y^9 +
  (1796469:ℝ)/1250000*x^3*y^7 +
  (-37725849:ℝ)/12500000*x^5*y^5 +
  (1796469:ℝ)/1250000*x^7*y^3 +
  (-598823:ℝ)/5000000*x^9*y^1 +
  (-5860657:ℝ)/100000000*x^1*y^10 +
  (17581971:ℝ)/20000000*x^3*y^8 +
  (-123073797:ℝ)/50000000*x^5*y^6 +
  (17581971:ℝ)/10000000*x^7*y^4 +
  (-5860657:ℝ)/20000000*x^9*y^2 +
  (532787:ℝ)/100000000*x^11*y^0 +
  (264333:ℝ)/25000000*x^1*y^11 +
  (-969221:ℝ)/5000000*x^3*y^9 +
  (8722989:ℝ)/12500000*x^5*y^7 +
  (-8722989:ℝ)/12500000*x^7*y^5 +
  (969221:ℝ)/5000000*x^9*y^3 +
  (-264333:ℝ)/25000000*x^11*y^1 +
  (-19929:ℝ)/100000000*x^1*y^12 +
  (219219:ℝ)/50000000*x^3*y^10 +
  (-1972971:ℝ)/100000000*x^5*y^8 +
  (657657:ℝ)/25000000*x^7*y^6 +
  (-219219:ℝ)/20000000*x^9*y^4 +
  (59787:ℝ)/50000000*x^11*y^2 +
  (-1533:ℝ)/100000000*x^13*y^0 +
  (-7231:ℝ)/50000000*x^1*y^13 +
  (94003:ℝ)/25000000*x^3*y^11 +
  (-1034033:ℝ)/50000000*x^5*y^9 +
  (443157:ℝ)/12500000*x^7*y^7 +
  (-1034033:ℝ)/50000000*x^9*y^5 +
  (94003:ℝ)/25000000*x^11*y^3 +
  (-7231:ℝ)/50000000*x^13*y^1 +
  (177:ℝ)/10000000*x^1*y^14 +
  (-5369:ℝ)/10000000*x^3*y^12 +
  (177177:ℝ)/50000000*x^5*y^10 +
  (-75933:ℝ)/10000000*x^7*y^8 +
  (59059:ℝ)/10000000*x^9*y^6 +
  (-16107:ℝ)/10000000*x^11*y^4 +
  (1239:ℝ)/10000000*x^13*y^2 +
  (-59:ℝ)/50000000*x^15*y^0 +
  (-17:ℝ)/100000000*x^1*y^16 +
  (17:ℝ)/2500000*x^3*y^14 +
  (-1547:ℝ)/25000000*x^5*y^12 +
  (2431:ℝ)/12500000*x^7*y^10 +
  (-2431:ℝ)/10000000*x^9*y^8 +
  (1547:ℝ)/12500000*x^11*y^6 +
  (-119:ℝ)/5000000*x^13*y^4 +
  (17:ℝ)/12500000*x^15*y^2 +
  (-1:ℝ)/100000000*x^17*y^0
lemma complex_identity (x y : ℝ) :
    (∑ n ∈ Finset.range 40, (c n:ℂ)*((y:ℂ)-Complex.I*x)^n)+
      (RH105Proof.CertifiedLocalPolynomial.bivariatePowerValue 8 17 a
        (4*x^2) (y+1/2):ℂ)=Complex.I*(imaginaryValue x y:ℂ) := by
  norm_num [c,rounded,roundedNumerators,Finset.sum_range_succ,
    RH105Proof.CertifiedLocalPolynomial.bivariatePowerValue,
    a,entry,powerMatrix,Fin.sum_univ_succ,imaginaryValue]
  push_cast
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod]
  try simp only [Complex.I_sq,Complex.I_pow_three,pow_zero,pow_one]
  apply Complex.ext <;>
    simp [←Complex.ofReal_pow,Complex.mul_re,Complex.mul_im] <;> ring
lemma power_identity (s : ℂ) :
    -(RH105Proof.CertifiedLocalXi.rotatedPolynomial c (209/2) s).re=
      RH105Proof.CertifiedLocalPolynomial.bivariatePowerValue 8 17 a
        (4*(s.re-1/2)^2) (s.im-104) := by
  have h := complex_identity (s.re-1/2) (s.im-209/2)
  have hw : RH105Proof.CertifiedLocalXi.rotatedVariable (209/2) s=
      ((s.im-209/2:ℝ):ℂ)-Complex.I*((s.re-1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [RH105Proof.CertifiedLocalXi.rotatedVariable,
      RH105Proof.CertifiedLocalXi.center] <;> ring
  unfold RH105Proof.CertifiedLocalXi.rotatedPolynomial
  simp only [hw]
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero] at hr
  have he : s.im-209/2+1/2=s.im-104 := by ring
  rw [he] at hr
  linarith
end RH105Numerical

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace RH105Numerical
attribute [local irreducible] a r b
lemma candidate_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 104 ≤ s.im) (hb : s.im ≤ 105) :
    1≤-(RH105Proof.CertifiedLocalXi.rotatedPolynomial proposed (209/2) s).re := by
  let x : Set.Icc (0:ℝ) 1 := ⟨4*(s.re-1/2)^2,⟨by positivity,by
    nlinarith [mul_nonneg h0 (show 0≤1-s.re by linarith)]⟩⟩
  let y : Set.Icc (0:ℝ) 1 := ⟨s.im-104,⟨by linarith,by linarith⟩⟩
  have hr : ∀ i, r i=RH105Proof.TaoZetaNumerics.bernsteinTransform 17 (a i) := by
    intro i
    funext j
    exact bernstein_checked.1 i j
  have hc : ∀ j, (fun i => b i j)=RH105Proof.TaoZetaNumerics.bernsteinTransform 8
      (fun i => r i j) := by
    intro j
    funext i
    exact bernstein_checked.2.1 i j
  have hl : ∀ i j, (1:ℝ)≤(b i j:ℝ) := by
    intro i j
    exact_mod_cast bernstein_checked.2.2 i j
  have h := RH105Proof.CertifiedLocalPolynomial.bivariate_bernstein_lower
    8 17 a r b hr hc 1 hl x y
  have he : c=proposed := rfl
  rw [←he,power_identity]
  exact h
end RH105Numerical


theorem solution (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ha : 104 ≤ s.im) (hb : s.im ≤ 105) :
    1 ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH104To105RoundedCoefficients 40 (209/2) s).re| := by
  have h := RH105Numerical.candidate_negative s h0 h1 ha hb
  have hh : 1 ≤ |(RH105Proof.CertifiedLocalXi.rotatedPolynomial RH105Numerical.proposed (209/2) s).re| := h.trans (neg_le_abs _)
  simpa only [RH105Numerical.proposed,RH105Numerical.rounded,RH105Numerical.roundedNumerators,
    RH105Proof.CertifiedLocalXi.rotatedPolynomial,RH105Proof.CertifiedLocalXi.rotatedVariable,
    RH105Proof.CertifiedLocalXi.center,TaoFivePrimes_RHLocalRoundedPolynomial,
    RH1000Analytic.CertifiedLocalXi.center,TaoFivePrimes_RH104To105RoundedCoefficients,Complex.ofReal_div] using hh
