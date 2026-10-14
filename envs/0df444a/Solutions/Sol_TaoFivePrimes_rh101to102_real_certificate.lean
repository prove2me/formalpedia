-- Prove2me | solution 1 for TaoFivePrimes.rh101to102_real_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T05:05:33.572721+00:00
-- url     : https://prove2.me/submissions/8e17d297-9ddf-4ab0-97e0-117201c7c941

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
noncomputable def reRows : List (List ℚ) := [
  [(973393743:ℚ)/20000000, (44439240051:ℚ)/800000000, (990513627949:ℚ)/16000000000, (30354294881593:ℚ)/448000000000, (26610372945899:ℚ)/364000000000, (363283504337631:ℚ)/4659200000000, (603054950863119:ℚ)/7321600000000, (229781513873039:ℚ)/2662400000000, (14794178313188423:ℚ)/164736000000000, (54402448355190343:ℚ)/585728000000000, (78349929397097367:ℚ)/820019200000000, (43753768178901397:ℚ)/447283200000000, (74339244675918809:ℚ)/745472000000000, (46454630644608589:ℚ)/458752000000000, (2014530432759091:ℚ)/19660800000000, (5418093405812317:ℚ)/52428800000000, (681004067224731:ℚ)/6553600000000],
  [(25022939073:ℚ)/400000000, (157114664253:ℚ)/2560000000, (1923039276163:ℚ)/32000000000, (52624043043777:ℚ)/896000000000, (667348956673167:ℚ)/11648000000000, (1039666070696529:ℚ)/18636800000000, (222299451711613:ℚ)/4100096000000, (3851022115815431:ℚ)/73216000000000, (7458229760707751:ℚ)/146432000000000, (57670973558890801:ℚ)/1171456000000000, (77895731194784981:ℚ)/1640038400000000, (27277109421680983:ℚ)/596377600000000, (4681726754301331:ℚ)/106496000000000, (77387541172573319:ℚ)/1835008000000000, (5292376963599907:ℚ)/131072000000000, (2022763796532757:ℚ)/52428800000000, (4821935940763:ℚ)/131072000000],
  [(1496102161:ℚ)/800000000, (87992750089:ℚ)/51200000000, (80395366013:ℚ)/51200000000, (291886749521:ℚ)/204800000000, (854538592083:ℚ)/665600000000, (6103998144193:ℚ)/5324800000000, (5393117087343:ℚ)/5324800000000, (9409071093983:ℚ)/10649600000000, (8078008005393:ℚ)/10649600000000, (108709043845329:ℚ)/170393600000000, (44472331008809:ℚ)/85196800000000, (279873441614717:ℚ)/681574400000000, (51790271384601:ℚ)/170393600000000, (1058998157729:ℚ)/5242880000000, (1373383526143:ℚ)/13107200000000, (646543089669:ℚ)/52428800000000, (-246960849561:ℚ)/3276800000000],
  [(-160404139:ℚ)/6400000000, (-5505368967:ℚ)/204800000000, (-43851010217:ℚ)/1536000000000, (-15394446823:ℚ)/512000000000, (-32194614311:ℚ)/1024000000000, (-80291060021:ℚ)/2457600000000, (-359555179569:ℚ)/10649600000000, (-7394947790851:ℚ)/212992000000000, (-354889356767:ℚ)/9984000000000, (-123521657169543:ℚ)/3407872000000000, (-12549281379387:ℚ)/340787200000000, (-76238945665199:ℚ)/2044723200000000, (-32063555201797:ℚ)/851968000000000, (-9929026431473:ℚ)/262144000000000, (-14948205184589:ℚ)/393216000000000, (-1995269536963:ℚ)/52428800000000, (-124537166129:ℚ)/3276800000000],
  [(-2076169:ℚ)/3200000000, (-523262833:ℚ)/819200000000, (-102816263:ℚ)/163840000000, (-1411278679:ℚ)/2293760000000, (-12822565859:ℚ)/21299200000000, (-100171775521:ℚ)/170393600000000, (-341691400709:ℚ)/596377600000000, (-379830946207:ℚ)/681574400000000, (-23045117033:ℚ)/42598400000000, (-89307737863:ℚ)/170393600000000, (-30223392131:ℚ)/59637760000000, (-166654910303:ℚ)/340787200000000, (-20061135079:ℚ)/42598400000000, (-1297614923:ℚ)/2867200000000, (-2844274349:ℚ)/6553600000000, (-21773021257:ℚ)/52428800000000, (-649605971:ℚ)/1638400000000],
  [(-315029:ℚ)/102400000000, (-4697979:ℚ)/1638400000000, (-21797017:ℚ)/8192000000000, (-563573747:ℚ)/229376000000000, (-129397851:ℚ)/57344000000000, (-755942429:ℚ)/367001600000000, (-342622627:ℚ)/183500800000000, (-440129299:ℚ)/262144000000000, (-49005701:ℚ)/32768000000000, (-172641433:ℚ)/131072000000000, (-104967063:ℚ)/91750400000000, (-179180111:ℚ)/183500800000000, (-186838091:ℚ)/229376000000000, (-1208346711:ℚ)/1835008000000000, (-66641003:ℚ)/131072000000000, (-3821653:ℚ)/10485760000000, (-29711:ℚ)/131072000000],
  [(1777:ℚ)/409600000000, (66913:ℚ)/13107200000000, (572483:ℚ)/98304000000000, (1702429:ℚ)/262144000000000, (466447:ℚ)/65536000000000, (605053:ℚ)/78643200000000, (107789:ℚ)/13107200000000, (2282823:ℚ)/262144000000000, (899339:ℚ)/98304000000000, (312791:ℚ)/32768000000000, (32443:ℚ)/3276800000000, (64271:ℚ)/6291456000000, (687577:ℚ)/65536000000000, (1406477:ℚ)/131072000000000, (2149801:ℚ)/196608000000000, (582239:ℚ)/52428800000000, (36849:ℚ)/3276800000000],
  [(13:ℚ)/204800000000, (3313:ℚ)/52428800000000, (329:ℚ)/5242880000000, (3259:ℚ)/52428800000000, (161:ℚ)/2621440000000, (3173:ℚ)/52428800000000, (1559:ℚ)/26214400000000, (611:ℚ)/10485760000000, (373:ℚ)/6553600000000, (581:ℚ)/10485760000000, (1409:ℚ)/26214400000000, (2723:ℚ)/52428800000000, (131:ℚ)/2621440000000, (2509:ℚ)/52428800000000, (239:ℚ)/5242880000000, (2263:ℚ)/52428800000000, (133:ℚ)/3276800000000],
  [(1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000, (1:ℚ)/6553600000000]]
noncomputable def reBern : List (List ℚ) := [
  [(973393743:ℚ)/20000000, (44439240051:ℚ)/800000000, (990513627949:ℚ)/16000000000, (30354294881593:ℚ)/448000000000, (26610372945899:ℚ)/364000000000, (363283504337631:ℚ)/4659200000000, (603054950863119:ℚ)/7321600000000, (229781513873039:ℚ)/2662400000000, (14794178313188423:ℚ)/164736000000000, (54402448355190343:ℚ)/585728000000000, (78349929397097367:ℚ)/820019200000000, (43753768178901397:ℚ)/447283200000000, (74339244675918809:ℚ)/745472000000000, (46454630644608589:ℚ)/458752000000000, (2014530432759091:ℚ)/19660800000000, (5418093405812317:ℚ)/52428800000000, (681004067224731:ℚ)/6553600000000],
  [(180765937953:ℚ)/3200000000, (6473796047793:ℚ)/102400000000, (17771257323347:ℚ)/256000000000, (107658552229853:ℚ)/1433600000000, (7479604430823311:ℚ)/93184000000000, (12664738209500721:ℚ)/149094400000000, (73099640789459653:ℚ)/820019200000000, (4184842705221847:ℚ)/45056000000000, (1013951479890428831:ℚ)/10543104000000000, (928110147241936289:ℚ)/9371648000000000, (1331494601548342853:ℚ)/13120307200000000, (1481951909989887653:ℚ)/14313062400000000, (48268157283650753:ℚ)/458752000000000, (1563935721800048167:ℚ)/14680064000000000, (338202000132254281:ℚ)/3145728000000000, (45367511043031293:ℚ)/419430400000000, (2844564667417999:ℚ)/26214400000000],
  [(1442018241343:ℚ)/22400000000, (101719163916901:ℚ)/1433600000000, (110368456323269:ℚ)/1433600000000, (337875235788539:ℚ)/4096000000000, (1164460868636699:ℚ)/13312000000000, (13710508278341443:ℚ)/149094400000000, (157373578452460729:ℚ)/1640038400000000, (1631628862853753441:ℚ)/16400384000000000, (3027811256455569959:ℚ)/29520691200000000, (424736159689763871:ℚ)/4037017600000000, (256297260102486597:ℚ)/2385510400000000, (6255972573344566559:ℚ)/57252249600000000, (2641291479227199429:ℚ)/23855104000000000, (820714581394197193:ℚ)/7340032000000000, (1239318160086473297:ℚ)/11010048000000000, (41466652120390961:ℚ)/367001600000000, (5188824384965099:ℚ)/45875200000000],
  [(25922575902677:ℚ)/358400000000, (180627980389869:ℚ)/2293760000000, (7277852169098251:ℚ)/86016000000000, (644631573935817:ℚ)/7168000000000, (70616544854421077:ℚ)/745472000000000, (177147544360136023:ℚ)/1789132800000000, (674424843348876441:ℚ)/6560153600000000, (13923858494909689751:ℚ)/131203072000000000, (16086696769262179003:ℚ)/147603456000000000, (17990415872017213607:ℚ)/161480704000000000, (23808179676297757359:ℚ)/209924915200000000, (2633975603032637623:ℚ)/22900899840000000, (5545763398567763617:ℚ)/47710208000000000, (107438660910380127:ℚ)/917504000000000, (647481523556624303:ℚ)/5505024000000000, (3458931544416787:ℚ)/29360128000000, (5399505987232387:ℚ)/45875200000000],
  [(5142227401481:ℚ)/64000000000, (4966096595868467:ℚ)/57344000000000, (15876664415237471:ℚ)/172032000000000, (78213921346586821:ℚ)/802816000000000, (152113238275230629:ℚ)/1490944000000000, (3796802695291563437:ℚ)/35782656000000000, (50370929429200770001:ℚ)/459210752000000000, (59194649379536814811:ℚ)/524812288000000000, (2621253438137771021:ℚ)/22708224000000000, (61733277104610672947:ℚ)/524812288000000000, (43865213743242957477:ℚ)/367368601600000000, (4321667764516259863:ℚ)/35782656000000000, (726174661663301191:ℚ)/5963776000000000, (786053595772994803:ℚ)/6422528000000000, (33765852979450981:ℚ)/275251200000000, (3516116963368341:ℚ)/28672000000000, (3506250987905901:ℚ)/28672000000000],
  [(507101078892299:ℚ)/5734400000000, (1734377356395049:ℚ)/18350080000000, (137656033561863853:ℚ)/1376256000000000, (1348298499509734429:ℚ)/12845056000000000, (4565657606196241389:ℚ)/41746432000000000, (18153210580046379713:ℚ)/160306298880000000, (171353244035255133251:ℚ)/1469474406400000000, (35833963463597737769:ℚ)/299892736000000000, (287892992671666861861:ℚ)/2361655296000000000, (1477468858303442699:ℚ)/11927552000000000, (23036114542229934487:ℚ)/183684300800000000, (12678963324760495849:ℚ)/100191436800000000, (5314270444406736937:ℚ)/41746432000000000, (32802789593959351:ℚ)/256901120000000, (175790470694140331:ℚ)/1376256000000000, (23387678416210419:ℚ)/183500800000000, (41573425078959:ℚ)/327680000000],
  [(1107661997482869:ℚ)/11468800000000, (37613877330645241:ℚ)/367001600000000, (19783073413274561:ℚ)/183500800000000, (1156639853823374631:ℚ)/10276044800000000, (19495851182025106237:ℚ)/166985728000000000, (16085771592075839799:ℚ)/133588582400000000, (90784526161229218907:ℚ)/734737203200000000, (6623945606575177011:ℚ)/52481228800000000, (75808374906982614541:ℚ)/590413824000000000, (17073639514061769141:ℚ)/131203072000000000, (928559824656619247:ℚ)/7064780800000000, (3314613800369725829:ℚ)/25047859200000000, (693207189006646883:ℚ)/5218304000000000, (427057294928213877:ℚ)/3211264000000000, (91376519190785531:ℚ)/688128000000000, (606794593268869:ℚ)/4587520000000, (53842034500799:ℚ)/409600000000],
  [(214618054917:ℚ)/2048000000, (46356364733685209:ℚ)/419430400000000, (121267516248248057:ℚ)/1048576000000000, (1764479249329212639:ℚ)/14680064000000000, (5924641549462518053:ℚ)/47710208000000000, (152222642282574571:ℚ)/1192755200000000, (1370239033490769703:ℚ)/10496245760000000, (9969195315555506659:ℚ)/74973184000000000, (11379653785722376459:ℚ)/84344832000000000, (2556810946472661149:ℚ)/18743296000000000, (1803700245695949109:ℚ)/13120307200000000, (988505417970402169:ℚ)/7156531200000000, (58952598489464737:ℚ)/425984000000000, (2265774579868129:ℚ)/16384000000000, (6775571410450621:ℚ)/49152000000000, (898404837263093:ℚ)/6553600000000, (55714772009409:ℚ)/409600000000],
  [(741025038415729:ℚ)/6553600000000, (6218739922633693:ℚ)/52428800000000, (16193044098452169:ℚ)/131072000000000, (58666057511863231:ℚ)/458752000000000, (392566288390291987:ℚ)/2981888000000000, (160866829641521229:ℚ)/1192755200000000, (902435422173100317:ℚ)/6560153600000000, (327427781547351423:ℚ)/2342912000000000, (745718350121308039:ℚ)/5271552000000000, (334360337707245687:ℚ)/2342912000000000, (235390455941017257:ℚ)/1640038400000000, (32189185377564401:ℚ)/223641600000000, (5365475355665253:ℚ)/37273600000000, (4117287160298029:ℚ)/28672000000000, (175605693732859:ℚ)/1228800000000, (29060494860753:ℚ)/204800000000, (899761004293:ℚ)/6400000000]]
noncomputable def entry (m : List (List ℚ)) (i j : ℕ) : ℚ := (m.getD i []).getD j 0
noncomputable def are (i : Fin 9) (j : Fin 17) : ℚ := entry rePower i j
noncomputable def rre (i : Fin 9) (j : Fin 17) : ℚ := entry reRows i j
noncomputable def bre (i : Fin 9) (j : Fin 17) : ℚ := entry reBern i j
theorem re_checked :
    (∀ i : Fin 9, ∀ j : Fin 17, rre i j=RH102Proof.TaoZetaNumerics.bernsteinTransform 16 (are i) j) ∧
    (∀ i : Fin 9, ∀ j : Fin 17, bre i j=RH102Proof.TaoZetaNumerics.bernsteinTransform 8 (fun u => rre u j) i) ∧
    (∀ i : Fin 9, ∀ j : Fin 17, (1:ℚ)≤bre i j) := by decide +kernel
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
lemma rotated_variable (s : ℂ) :
    RH102Proof.CertifiedLocalXi.rotatedVariable (203/2) s=
      ((s.im-203/2:ℝ):ℂ)-Complex.I*((s.re-1/2:ℝ):ℂ) := by
  apply Complex.ext <;> simp [RH102Proof.CertifiedLocalXi.rotatedVariable,
    RH102Proof.CertifiedLocalXi.center] <;> ring
lemma real_identity (s : ℂ) :
    (RH102Proof.CertifiedLocalXi.rotatedPolynomial c (203/2) s).re=
      RH102Proof.CertifiedLocalPolynomial.bivariatePowerValue 8 16 are
        (4*(s.re-1/2)^2) (2*(s.im-203/2)) := by
  have h := congrArg Complex.re (complex_identity (s.re-1/2) (s.im-203/2))
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero] at h
  unfold RH102Proof.CertifiedLocalXi.rotatedPolynomial
  simp only [rotated_variable]
  linarith
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
lemma real_half_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 203/2 ≤ s.im) (hb : s.im ≤ 102) :
    1 ≤ |(RH102Proof.CertifiedLocalXi.rotatedPolynomial proposed (203/2) s).re| := by
  let x : Set.Icc (0:ℝ) 1 := ⟨4*(s.re-1/2)^2,⟨by positivity,by
    nlinarith [mul_nonneg h0 (show 0 ≤ 1-s.re by linarith)]⟩⟩
  let y : Set.Icc (0:ℝ) 1 := ⟨2*(s.im-203/2),⟨by linarith,by linarith⟩⟩
  have hr : ∀ i, rre i=RH102Proof.TaoZetaNumerics.bernsteinTransform 16 (are i) := by
    intro i; funext j; exact re_checked.1 i j
  have hc : ∀ j, (fun i => bre i j)=RH102Proof.TaoZetaNumerics.bernsteinTransform 8
      (fun i => rre i j) := by intro j; funext i; exact re_checked.2.1 i j
  have hl : ∀ i j, (1:ℝ) ≤ (bre i j:ℝ) := by intro i j; exact_mod_cast re_checked.2.2 i j
  have h := RH102Proof.CertifiedLocalPolynomial.bivariate_bernstein_lower 8 16 are rre bre hr hc 1 hl x y
  have he : c=proposed := rfl
  rw [←he,real_identity]
  exact h.trans (le_abs_self _)
end RH102Numerical

theorem solution (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ha : 203/2 ≤ s.im) (hb : s.im ≤ 102) :
    1 ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH101To102RoundedCoefficients 32 (203/2) s).re| := by
  simpa only [RH102Numerical.proposed,RH102Numerical.rounded,RH102Numerical.roundedNumerators,
    RH102Proof.CertifiedLocalXi.rotatedPolynomial,RH102Proof.CertifiedLocalXi.rotatedVariable,
    RH102Proof.CertifiedLocalXi.center,TaoFivePrimes_RHLocalRoundedPolynomial,
    RH1000Analytic.CertifiedLocalXi.center,TaoFivePrimes_RH101To102RoundedCoefficients,
    Complex.ofReal_div] using RH102Numerical.real_half_certificate s h0 h1 ha hb
