-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_14_1e2
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T02:22:12.248997+00:00
-- url     : https://prove2.me/submissions/30db8e24-e604-49d7-ab5c-f7b6f516651a

/-
Compact certificate adaptation of sometik179's height-14–100 proof,
Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03).
The theta/Mellin attribution to Gabewhigham is retained in the source.
Large records are reconstructed by ordinary Lean definitions. The original
kernel validators still establish every numerical certificate condition.
-/
import Theorems.Thm_TaoFivePrimes_rh14to100_theta_checks
import Theorems.Thm_TaoFivePrimes_rh14to100_moments_enclosed
import Theorems.Thm_TaoFivePrimes_rh14to100_translation_checks
import Theorems.Thm_TaoFivePrimes_rh14to100_bernstein_checks
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.GCongr

/- Ordinary finite arithmetic definitions extracted from sometik179's
height-14–100 certificate, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a.
Theta/Mellin attribution to Gabewhigham is retained. No certificate assertion
or RH theorem is supplied in this definition interface. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

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

open Finset

namespace CertifiedTaylorQuadrature

end CertifiedTaylorQuadrature

end Height100Module2

section Height100Module3

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module3

section Height100Module4

open Finset
namespace CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedExponentialJets

end Height100Module4

section Height100Module5

open Finset
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

namespace ZetaSix

end ZetaSix

end Height100Module9

section Height100Module10

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module10

section Height100Module11

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module11

section Height100Module12

open Finset

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Finset

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module16

section Height100Module17

set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256

end TaoZetaWide256

end Height100Module17

section Height100Module18

open Finset
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

end TaoZetaGlobal

end Height100Module18

section Height100Module19

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module19

section Height100Module20

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module20

section Height100Module21

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module21

section Height100Module22

open Finset
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

set_option autoImplicit false

namespace TaoZetaWide

end TaoZetaWide

end Height100Module23

section Height100Module24

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Finset
namespace CertifiedGlobalMoments
open CertifiedZetaQuadrature

end CertifiedGlobalMoments

end Height100Module25

section Height100Module26

open Finset
namespace CertifiedEvenPolynomial

end CertifiedEvenPolynomial

end Height100Module26

section Height100Module27

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module27

section Height100Module28

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Finset
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module29

section Height100Module30

open Finset
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module30

section Height100Module31

open Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

end CertifiedPolynomialTranslation

end Height100Module32

section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open Finset CertifiedPolynomialTranslation

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

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedJetRecords
open CertifiedThetaPoints

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

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Finset
namespace CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedZetaQuadrature

end Height100Module52

section Height100Module53

open Finset
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedJetRecords

end Height100Module53

section Height100Module54

open Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module54

section Height100Module55

open Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

end CertifiedMomentConvolution

end Height100Module55

section Height100Module56

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
namespace CertifiedZetaQuadrature
end CertifiedZetaQuadrature

end Height100Module58

section Height100Module59

open Finset
namespace CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature

end CertifiedGlobalQuadrature

end Height100Module59

section Height100Module60

open Finset
namespace CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Finset
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
open Finset
open scoped BigOperators

namespace CertifiedGlobalJetCenters
open CertifiedJetRecords CertifiedThetaPoints CertifiedFixedPoint
open CertifiedMomentConvolution CertifiedZetaQuadrature

noncomputable def addLists : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x::xs,y::ys => (x+y)::addLists xs ys

noncomputable def sumLists : List (List ℤ) → List ℤ
  | [] => []
  | xs::xss => addLists xs (sumLists xss)

noncomputable def centerNumerators (i : Fin 16) : List ℤ :=
  addLists (List.replicate 184 0)
    (sumLists (List.ofFn (fun n : Fin 8 => (recordAt i n).fs)))

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

noncomputable def denominator : ℕ := 233398525209048950364126761403658816544333459669051688264166752003070906265328000

noncomputable def weight (j : ℕ) : ℕ := if j%2=0 then 2*(denominator/(j+1)) else 0
noncomputable def weights : List ℕ := List.ofFn (fun j : Fin 184 => weight j.val)

end CertifiedMomentWeights

end Height100Module64

section Height100Module65

namespace CertifiedExponentialIntegerSequence

end CertifiedExponentialIntegerSequence

end Height100Module65

section Height100Module66

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace CertifiedMomentArithmetic
open CertifiedFixedPoint CertifiedExponentialIntegerSequence
open CertifiedMomentConvolution

noncomputable def qSequence : List ℕ := expSeq 12 184 0 (Nat.factorial 184)
noncomputable def centerSequence (p : ℕ) : List ℕ := expSeq p 512 0 (Nat.factorial 512)
noncomputable def scaledCorrelations (B : List ℤ) : List ℤ :=
  List.zipWith (fun b e => b*(e:ℤ)) B qSequence

noncomputable def momentDenominator : ℕ :=
  16*scale310*CertifiedMomentWeights.denominator*(Nat.factorial 184)*(Nat.factorial 512)

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

structure Record where
  h : List ℤ
  b : List ℤ
  z : List ℤ
  cp : ℕ
  cm : ℕ
  pp : ℕ
  pm : ℕ
  deriving Repr

noncomputable def correlationBits : ℕ := 1536
noncomputable def momentBits : ℕ := 7168

noncomputable def correlationProduct (h : List ℕ) : ℕ :=
  encode correlationBits h.reverse * encode correlationBits CertifiedMomentWeights.weights

noncomputable def panelParameter (i : Fin 16) : ℕ := 12*(2*i.val+1)

noncomputable def momentProduct (c : List ℕ) (p : ℕ) : ℕ :=
  (encode momentBits c*encode momentBits (centerSequence p)) %
    Nat.shiftLeft 1 (momentBits*512)

noncomputable def initialCondition (d : Record) : Prop :=
  d.h.length=184 ∧ d.b.length=184 ∧ d.z.length=256
noncomputable instance (d : Record) : Decidable (initialCondition d) := inferInstanceAs (Decidable (_∧_∧_))

noncomputable def correlationCarry (d : Record) : Prop :=
  (positiveList d.h).reverse.sum*CertifiedMomentWeights.weights.sum<2^correlationBits ∧
  (negativeList d.h).reverse.sum*CertifiedMomentWeights.weights.sum<2^correlationBits
noncomputable instance (d : Record) : Decidable (correlationCarry d) := inferInstanceAs (Decidable (_∧_))

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

structure Aux where
  e : List ℕ
  chunks : List ℕ
  c : List ℤ

noncomputable def checkAux (i : Fin 16) (d : Record) (a : Aux) : Bool :=
  decide (a.e.length = 512) && decide (a.e.headD 0 = Nat.factorial 512) &&
  checkSteps (panelParameter i) 0 a.e &&
  checkChunks momentBits 32 a.e a.chunks &&
  decide (a.c = scaledCorrelations d.b)

noncomputable def checkCore (i : Fin 16) (d : Record) (a : Aux) : Bool :=
  decide (initialCondition d) && decide (d.h = CertifiedGlobalJetCenters.centerNumerators i) &&
  decide (correlationCarry d) &&
  decide (d.cp = correlationProduct (positiveList d.h)) &&
  decide (d.cm = correlationProduct (negativeList d.h)) &&
  decide (d.b = extract correlationBits 1 184
    (d.cp >>> (correlationBits*183)) (d.cm >>> (correlationBits*183))) &&
  decide ((positiveList a.c).sum*a.e.sum < 2^momentBits ∧
    (negativeList a.c).sum*a.e.sum < 2^momentBits) &&
  decide (d.pp = (encode momentBits (positiveList a.c)*encode (momentBits*32) a.chunks) %
    Nat.shiftLeft 1 (momentBits*512)) &&
  decide (d.pm = (encode momentBits (negativeList a.c)*encode (momentBits*32) a.chunks) %
    Nat.shiftLeft 1 (momentBits*512)) &&
  decide (d.z = extract momentBits 2 256 d.pp d.pm)

noncomputable def checkCached (i : Fin 16) (d : Record) (a : Aux) : Bool :=
  checkAux i d a && checkCore i d a

end CertifiedMomentSequenceCache

end Height100Module73

section Height100Module74

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedMomentRecords

noncomputable def cacheChunks : ℕ → List ℕ → List ℕ
  | 0,_ => []
  | n+1,xs => CertifiedPackedConvolution.encode momentBits (xs.take 32)::cacheChunks n (xs.drop 32)

open CertifiedListODEVectors CertifiedPackedExtraction CertifiedMomentArithmetic

noncomputable def compactMomentRecord (i : Fin 16) : Record :=
  let h := CertifiedGlobalJetCenters.centerNumerators i
  let cp := correlationProduct (positiveList h)
  let cm := correlationProduct (negativeList h)
  let b := extract correlationBits 1 184
    (cp >>> (correlationBits*183)) (cm >>> (correlationBits*183))
  let c := scaledCorrelations b
  let pp := momentProduct (positiveList c) (panelParameter i)
  let pm := momentProduct (negativeList c) (panelParameter i)
  let z := extract momentBits 2 256 pp pm
  ⟨h,b,z,cp,cm,pp,pm⟩
@[noinline] noncomputable def pointRecord.«0» : Record := compactMomentRecord (0 : Fin 16)
@[noinline] noncomputable def sequenceCache.«0» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (0 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«0».b⟩
@[noinline] noncomputable def pointRecord.«1» : Record := compactMomentRecord (1 : Fin 16)
@[noinline] noncomputable def sequenceCache.«1» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (1 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«1».b⟩
@[noinline] noncomputable def pointRecord.«2» : Record := compactMomentRecord (2 : Fin 16)
@[noinline] noncomputable def sequenceCache.«2» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (2 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«2».b⟩
@[noinline] noncomputable def pointRecord.«3» : Record := compactMomentRecord (3 : Fin 16)
@[noinline] noncomputable def sequenceCache.«3» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (3 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«3».b⟩
@[noinline] noncomputable def pointRecord.«4» : Record := compactMomentRecord (4 : Fin 16)
@[noinline] noncomputable def sequenceCache.«4» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (4 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«4».b⟩
@[noinline] noncomputable def pointRecord.«5» : Record := compactMomentRecord (5 : Fin 16)
@[noinline] noncomputable def sequenceCache.«5» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (5 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«5».b⟩
@[noinline] noncomputable def pointRecord.«6» : Record := compactMomentRecord (6 : Fin 16)
@[noinline] noncomputable def sequenceCache.«6» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (6 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«6».b⟩
@[noinline] noncomputable def pointRecord.«7» : Record := compactMomentRecord (7 : Fin 16)
@[noinline] noncomputable def sequenceCache.«7» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (7 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«7».b⟩
@[noinline] noncomputable def pointRecord.«8» : Record := compactMomentRecord (8 : Fin 16)
@[noinline] noncomputable def sequenceCache.«8» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (8 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«8».b⟩
@[noinline] noncomputable def pointRecord.«9» : Record := compactMomentRecord (9 : Fin 16)
@[noinline] noncomputable def sequenceCache.«9» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (9 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«9».b⟩
@[noinline] noncomputable def pointRecord.«10» : Record := compactMomentRecord (10 : Fin 16)
@[noinline] noncomputable def sequenceCache.«10» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (10 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«10».b⟩
@[noinline] noncomputable def pointRecord.«11» : Record := compactMomentRecord (11 : Fin 16)
@[noinline] noncomputable def sequenceCache.«11» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (11 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«11».b⟩
@[noinline] noncomputable def pointRecord.«12» : Record := compactMomentRecord (12 : Fin 16)
@[noinline] noncomputable def sequenceCache.«12» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (12 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«12».b⟩
@[noinline] noncomputable def pointRecord.«13» : Record := compactMomentRecord (13 : Fin 16)
@[noinline] noncomputable def sequenceCache.«13» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (13 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«13».b⟩
@[noinline] noncomputable def pointRecord.«14» : Record := compactMomentRecord (14 : Fin 16)
@[noinline] noncomputable def sequenceCache.«14» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (14 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«14».b⟩
@[noinline] noncomputable def pointRecord.«15» : Record := compactMomentRecord (15 : Fin 16)
@[noinline] noncomputable def sequenceCache.«15» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (15 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«15».b⟩
@[noinline] noncomputable def _root_.CertifiedMomentRecords.panelBank : (@_root_.List (@_root_.CertifiedMomentRecords.Record)) :=
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«0»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«1»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«2»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«3»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«4»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«5»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«6»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«7»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«8»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«9»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«10»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«11»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«12»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«13»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«14»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentRecords.Record)
  (@_root_.CertifiedMomentRecords.pointRecord.«15»)
  (@_root_.List.nil
  (@_root_.CertifiedMomentRecords.Record))))))))))))))))))

@[noinline] noncomputable def _root_.CertifiedMomentRecords.sequenceCacheBank : (@_root_.List (@_root_.CertifiedMomentSequenceCache.Aux)) :=
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«0»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«1»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«2»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«3»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«4»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«5»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«6»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«7»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«8»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«9»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«10»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«11»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«12»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«13»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«14»)
  (@_root_.List.cons
  (@_root_.CertifiedMomentSequenceCache.Aux)
  (@_root_.CertifiedMomentRecords.sequenceCache.«15»)
  (@_root_.List.nil
  (@_root_.CertifiedMomentSequenceCache.Aux))))))))))))))))))

@[noinline] noncomputable def sumRow.«16» : List ℤ := []
@[noinline] noncomputable def sumRow.«15» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«15».z sumRow.«16»
@[noinline] noncomputable def sumRow.«14» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«14».z sumRow.«15»
@[noinline] noncomputable def sumRow.«13» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«13».z sumRow.«14»
@[noinline] noncomputable def sumRow.«12» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«12».z sumRow.«13»
@[noinline] noncomputable def sumRow.«11» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«11».z sumRow.«12»
@[noinline] noncomputable def sumRow.«10» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«10».z sumRow.«11»
@[noinline] noncomputable def sumRow.«9» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«9».z sumRow.«10»
@[noinline] noncomputable def sumRow.«8» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«8».z sumRow.«9»
@[noinline] noncomputable def sumRow.«7» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«7».z sumRow.«8»
@[noinline] noncomputable def sumRow.«6» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«6».z sumRow.«7»
@[noinline] noncomputable def sumRow.«5» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«5».z sumRow.«6»
@[noinline] noncomputable def sumRow.«4» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«4».z sumRow.«5»
@[noinline] noncomputable def sumRow.«3» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«3».z sumRow.«4»
@[noinline] noncomputable def sumRow.«2» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«2».z sumRow.«3»
@[noinline] noncomputable def sumRow.«1» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«1».z sumRow.«2»
@[noinline] noncomputable def sumRow.«0» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«0».z sumRow.«1»
@[noinline] noncomputable def _root_.CertifiedMomentRecords.roundingDenominator : (@_root_.Nat) :=
  2893671829256903287775149279986680275576207929722149942016313863928229622022351649898261517842351367059355569095640548067363387637659642536091542526049691714196375808235239377045601498065176752035665706867800577867464162465193609646728952243984331164468281241477844085267793637488463106923068575269529320065192261712507620278503482639697552950616141348602313408425778582736496962557777002169075586745724082445021762829254286418512847481898765273026834984345878140254899702662896223349512469226199663431617223502077769431359391993372288773862926167493598911720148399724171334388351244887101865378255187801159125191038639778044251529721036546524123931909024906432831464460384602368914906023553307607102298160480833674504136511842610788688681867047365648930524207391754531631144019549417947796056645690316681492247338435415955460314611387351720591430689909492005841392338281013631878765345791161870324810639425579232212446941714649115639793905205459221937040159643492058247640701892541321770048418947796870069150166996419933743738917826923753407188361326501288819448430581363851953638087511497550785130485876945132026033536905188042761900836198516699896027986167432626925207606022322766951156466204153000542866929316578271237634261715036151750206698831641360028013414365088218402238595139882975276508416211687794828074582067120706407932388023470928294142026338472054405777781494598807309723455965037246660208006004736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

@[noinline] noncomputable def _root_.CertifiedMomentRecords.roundedNumerators : (@_root_.List (@_root_.Int)) :=
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  230337744934871206978100825168182415416511235383585125341261280)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  40521025678005477415456616733783672132802773496266119565479671793)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4474037647682628329675671257143783483010223849002749953812275576994)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  351481606056109814371215101276232647382890680092901678739777715030727)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21079322957780478348614085877194415708902446857461078509372025895219048)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1009906114954808594635649856423182566693468066012802252484490411697737673)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  39903750943173106741665468822383755693987872165751985529597445144845680539)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1331470276361406723382990211054507272438448335323970548523937999689088179798)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  38210603612544347746315297629478780370009798584563038472487139984253116180534)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  957002659355094357051996352730687697044637763073824082397908009095374325090813)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21169112240876900122895473916783501561578580865741024483646570063992924488197112)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  417707216394437395069182164041149338016821602508332594906122329231102621263511994)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7414448651866805443080890666142606697008549203242062339680258167052349871440493647)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  119251079574613808442263180612819754528069143272698342764324606930311890518183788945)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1748827836515974891785470840690180915227738473359199733984814329944979037706203206215)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  23513723985769920939217262691957387645837874121950613396068533358212430466909663734953)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  291270693313355443376206815370169006340788048154649240517879787074749061828146378513085)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3338518131038545549138164387804051538738418214480060569168393458696955129363494882040444)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  35544985229591172625684774299524936842802041283057434755286810486152610397600730676270022)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  352769653373032509609294502733122625725691175349819236585001236636052871362825144240626591)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3273942665769892066201192175725157345610380961494525744239269899064956498739987174598171564)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  28495341128344223264466382890880235996054876098944147947017153717987076374357885201505864504)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  233210830796486179752541507992613355223459727378496691445694279470086198699800967116313064979)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1799082808553918074328921290271516627531882269244807441711139435166392296396227287227260877117)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  13111555063527463899658137982623050846424460849761654802608628406121496667428135423995979666172)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  90460258395567983297826010561080796586035155156165822644366792665546611035938819704943792696021)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  591966227421235819961939370242284921900605584099330505613232297216647356213622414218353866061424)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3680851328381476238093626711503856449769026470186667050464951856397664754592000951305749289737319)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21783938234617465080465127501663179183803511947053137835933650329491848105998827901501454613760898)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  122896286345298928202889691868195211018389050672765997938259510159468210422008747289629807082647581)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  661896764059095544418944509051882905440391939571062170853784862967738469690496177016535758832757507)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3407902375649385423255931472837615584956129100135229867353169374123845800389531134558494071019059342)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16795405641116791769934676225690695569672686211415590869989697594699871268080253179556179036897751009)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  79328504834735992797961735483857995183186360903777911376594540590744634700654477288783620592366924670)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  359503402400251072302632420442272446033649605800195348037908812570660365117829316867924629309956614099)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1564891578809607683837439345958753793693489138324228564605133413470409915656456978041071303134103249258)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6549689607050495289748831679864012911033094229985282350613899131183797739851433544424314683038868332273)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26383790673483976500802973951375480799101840989213513544639973606510202222807435321190830414439171669686)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  102385224069815496424048117347336775593083111413716788412394968958275130923522935816824924157860649531804)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  383093681304377101691157527548427416104242535409492481225575791167407445709517213576338822897395161226712)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1383267233012268096728763043982505147210531055195534803842484055609078069845426765276971794093832361387402)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4823801669256233717509961639779626798180498814081390138875458993263767919832791832099673248596818563159920)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16258786912812242851070023368221738286650130503766421712302217438297804186103604983098180301577585905467889)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  53005453321238144063475135375553213102108249789666361835289818298916112267130272552203426619277441277344180)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  167259699739909746586097975739608894466640887421980309589859051356015158300103430632898041582321425576128576)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  511201569199618328388682035642015183716223428657078761898530422970635251622387085480862514343916963521077446)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1514268360033576699239629210702377404203157316318801040737917153348240908029663237214898033548070250584733811)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4350024466032531736137485651158028549124851735541798791494414684336922034796622944044073832763356867556942868)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  12125969447371700538144145523858465768072390111850709665141931270113182005634337628419551349269330031662963366)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  32818965027713334774607672466550353878562293347435903669565112216134936692058699526343165169275653890933439669)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  86288957294445055453723896102565961035526299123475221068609509920240769688194119818758828575657862598883674965)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  220514359448124013124360309693042963618313305251717885468867657801667275549776073439190573376017655961643565449)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  548012950584713318471240374180930833187282403868929268726136061469816186554298556635017901922413077283474191585)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1325043362697313661267273124401190889083615877032306762592870194947488991977360359051896126781680612887009017353)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3118603695531478887931894731224078196241574803072467660459290885064421736913864638145833839019274111024284178871)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7147916901257877142451613994534244498891099975609559706458204629373123562644743662953505755920004710191712756016)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15961717749099447270220922223775485461823794648968745871376060444538355296492143824801841686549146792872238636673)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  34741277717018998441055817119538311887331505553002022821256599645183350195301304725940839221873166398824406255724)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  73732180885805818997195033400198578417488576000375397042723824904020656267752346541585961063534657631169786041169)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  152646486618753505797712642726787604838126950708161968694527464265762385133015854388207189859135513562504335527355)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  308391766521426586150620190528414116333451354928206260327662435502671379948002469750059156354308268726793350292723)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  608229524880516581095696726084999815537489900506554426024281557583402842240547443625026397508703078707024412270470)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1171489780547940326466838979833870263082176599874865247882354536210955207753067997058796643245282944398760353931680)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2204289008369331614211393192734969310993912795935596010424838156469634079887456127982902722961703777789873768480800)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4053272171115841125896038746079161026203787208888575616201569194886653253250115135638516581780654873154752919733383)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7286081356399804410160825762798926719343870265243834117930823813855264120555140941345143137203971444012418987732555)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  12807752599681632682594465631968923341882774085929257005367947208425015821862785875704479277157417194951509064851554)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  22023085559476589648315906949873989177570956203642298778304535176403880895601429389498726489101536252388787443069479)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  37054551713705799431963597350577060771485155049770234531134872484328507438646736753642822364035197057628436606185227)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  61022683659403032432002100378529671339726819561070662378704454026256648512252694334542358434747243494807425892910799)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  98390248774068934267818496253608159345669527825577705641147623001679881612399922307052470703199684162013657401011607)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  155362120504156392253006756819371502102861726633411812665843332583965484456445617692055288014314955685357000879132586)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  240319288647697787465250087363441510160595712827731040046055083334949488764089353082400005936884487491991342670001249)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  364248280011243983928797243522795257841133934717581745518237469613634674608997694881711842161524294553001711362349831)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  541107787007418697784410183201362294013501196179903694285905223858669966419416449768821043307339417314748895183543560)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  788055116748299936781383114393733450895207237085888709262836318213897820100190754347406783931034451016357600308195398)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1125439944043561652792779094446107559017022660671637247540184756636004062239697789015159637919979694881578422773395940)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1576466392591880596347199661982691471137965810011608752063057918239854687430762539239506937852725634307541914456967142)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2166431465244016535258128801836656334132133849122055142594873758332598963983219213131361100894413176725852844603534717)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2921472264772708457662769876573055850874158803435613538737788515162063294914296659613122157034663860123284769475102159)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3866798274909779750378055930680577087707182518092710812078820332062061610144690701018715392851875319483457861788565354)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5024447094416485861170639375149215236523823673073569482122014224502665642438287774083100379864705927284553385868245589)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6410677462716058256830386674163337664583441535138435840987126266048393328101290064509314879101735491193198555649041922)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  8033193236813446749855158340740884468890791939824631423641032097492682601375716611501805580601185352745911567540370250)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9888463992892261026294399053302050353315475755986770043146024921981751181573528907016258458696004950479378982133934344)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11959458355805667432840357083911271779243644253904285353297505408346295891788543248174284203189065026354757519898461126)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  14214122009168935492411437611278131328892767265799177436345601839295380919886842683727210518722209651174934101709415441)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16604904102785954468612350603108138951522203916254430092706955436179017489435843836894531335025626336091447025454085867)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  19069559934555604974272203556854497191679987078795605860357947493854713111245860525506225114474583435991010916615538655)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21533338488066587164394371988267857042086587760873074203424439347967880800321413106237897063512771708831624360098066115)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  23912512827567368520471245946349022060662646536742222538662198688126551288707656235987546918074812350659353424398720060)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26119048469582367014988263488255144442775100970635030486929259871895764787873083662704672194888052583349584279025495951)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  28066052736065570155910996473431311562695168169936040290420597647273733027223147204134799510380805402299634636973088997)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  29673530122311393504673243590584568917775152462440663883020155148884218775544068780749032414317681680851346014662324924)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  30873904418246021375508235302891495972536309292439648952355343855120366032945067167079339323237329862993950325768156985)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  31616769736638708498485330717603240395631976551395580032763282800241942160595581701264757530264366886817991084104754222)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  31872401853628104556682396338515436084415629360127184333764883027551715987188171490159605085528753830484618024383083395)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  31633689961338423795524837129142484707100960356733319867405068202285497053189176103942739918717739211535212223311035615)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  30916319474063644929093298891980903097400265550750296554278385658800961810071064937323249376826867178222643985715472643)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  29757225120046884352371459059332046256328854231758780953161282104759368970069694311566051451638609037760381035606472228)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  28211514250876815925070829636244409132019321224818761063927215945801499961477186047300747881032585585197972117238257682)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26348209340089073455502688921264956471113530343208911202852767530395999551093900924914267382432742076796253308723124053)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  24245258146092610141417955823902796228146542823828446491405190889214568825838575574944571757921313966461982947712186691)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21984300471538932719014158205683329480515331440037348623648165494525900336376354971565810031874668106204673722403591305)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  19645661563473902849622212119234762090192892736824460045757115798855759825972767722205302170999291058154928294410808391)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  17303972086882990323347546994630570986381389383150177448531080322087827998216413415331616626748808246991738244020703427)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15024707681771443125228122817061082970304835954624598181834779529296532559599966890044946529984599157163083972762964315)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  12861815158134630571814639260113417124123533051006205795871069473099645877468926637509083386436492322031698224795879472)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  10856465426923995844148268577020183218910516313331689568430848289913452548213222422114343357044101462560043691928382155)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9036860879065487806368715471363029470570340033033666499983088167548642203675725409729224351270421962103748712506200999)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7418938305539314973164751917034906166089750341845617578379201791312644816269906264863651249751131508729451077711335286)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6007753516400793449864977883785246682598153650004064162729661575917763140706103782026762892886531136508243760980395238)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4799311283444681351323325635120794438156327909124966865128343046689550714342820801947252457868227820991338080957981657)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3782610492737314363585041922809291142303162768195030715034604995776496649488237622638069013662080912617744810433363740)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2941702883719540247753618494519485391372258014759462620867620811061959885937975917230257685345598793502195846336844532)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2257606480431147015634527243756413241092724517247810393168459660617037098489921245838683690770426137041152705415001897)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1709963786594029934198148238161219942785634838863411701208172989743005906745803797948514281033620633312478943475591334)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1278383102108132602914421361878262378158352979339386496251673552331256302548278850874604727649696315422970207826971988)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  943443763558944612318017707610808411273887314735250432224416427802887561567347223675471118089514646927394817877515471)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  687379563251394684755067780715941995323445651468136693575339997585136956681214036120488521458135739594657030439537169)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  494477812054412051850217461144623224737510897609951119568730385848780066648952390895154674654194847261363653201510939)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  351244789036113620270913445498910441870570534242033732902968911487802793610087389836905272625600865367917833372786896)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  246393057296385527927625321801261584958429554665349433629837825203149306004573134099703916107541845397820854118182731)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  170704306511498144832131365133348094690576538087043079584676446264136204386565688161873242797837624176850679225618006)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  116815160441825511579597983372462433697761608772487210730254955409765946275095566513344232870818847525772280647190139)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  78964758551213488567191741501448918974074810491770403187942454495016129340408120865933118055438818901596375352400124)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  52733525787778959850093870273125969060751345987106333399282340713222661814000048079714128034946992652815449139207094)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  34793580278346091081561925170229068398788469309261747585284095701998834829406913551667770423511983416414489431588675)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  22683447823210819510840556670341483911283287054625912140906130879751010151406524119083066874989610438225058271674139)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  14613521773999908153576242585867167705748049021504075955887079974772880637663896698379791832865959290753102610359217)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9304097786168062233919889702895019864127394590317242394183882927491824365101373899113482989434491834341249875394142)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5854695471590296594889268485516069710624502931626792698643369273633070248946396071107965676660081652159775479677374)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3641510768964107417180507143758806896272182343659176857733024908494371024894190125898556739215964365407358287805250)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2238938551548087204043180353426761744867432305741688037386512686964575599373813756749606195915481205729546298344035)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1360885421330486093682026502271488948212604237540682412072580849542756178111097563063528042102124898118787448570536)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  817814442757512222191498690548480755255908110387124058086076137406343528204424030574211684453019871896896485385327)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  485932935304902485532170910497585908805188414244843874851724444621448721353524033401848093861107235095246531882998)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  285509307783714983951466760154658945128542251471548036259267581372277817257527323122444062964170876560291183093961)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  165889973386589654877158296650175768336046352771272056895425710234530369314682757151126263140977580729158438175944)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  95325484777461657595177313088853274881009194580162690699427886083499598193650976792720736744279178530089542077821)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  54177574428624942806329572906961615291850676073509562539302795042159473769008174255146586362645538606613036575596)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  30456775763927113466073714225469630453135090212335782121720343984871294520034649202655590328680543320866097004887)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16936898050875261249102959812866180441801909978744473925308521906586332475592442117343579794686059022012701588370)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9317528210135331745884269504579959252549755746191899203994783915592278645937426361319676857122436776526076593905)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5071253851409451194529197009000903828500390748571667978434131758119884995335124312752267541980288874352600902642)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2730915483896227844291346380728564275966996781699100837078740352126306404706831244432968819696621582179789353986)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1455155899101426667562329508852122212401563629446993923938819029776785019679114132599142345164519453291371396850)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  767271078112243542872014583274611064826529388547039749236929573309609013846595080955271359518759363838254688122)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  400364412855510914705351579923493252269719224169127031331058385937738738722804181457111247525881769265725012549)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  206756112848320950299126263066873832337706173026969870983750191987947494592287962740177768376060718343683745802)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  105678355003605692066794025514549455806012201220062138851900921351412831646318793911879824061609488473686071150)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  53464646831642376647760878621640675417407056521717965017467225622273550580502346884310850968099206718651731163)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26774918106615866193036307190810755244898150238624382293098356671627280189477945355937315554942734635720191340)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  13273879099850554908931965571781108787668622397939498185378583368143511526558818357815268334652659122428222404)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6514827842479392165031781418775183687880260186024336708113265137112123439289265245887832825786622276993332118)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3165703179774824618086768989640998123745923155894566626852580956614691239826936451631752133053985423195554778)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1523091711261223364068703398571961436126544028045975800154231033484571374940418360436581853832763232946509370)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  725598966115632643891052880061095851796853223215076616625309797677360375538038964581349381103467892646913777)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  342300709155401550254929486278323892647613868640702992553576620034732212487899071298259805629037777553886196)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  159913443840765758647254087712649319839494340822775911838391191982702433349259917353376849153848601404280854)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  73986650981835381262877710348956892281457683674913100289706824914159828407701304084401946042543369618586808)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  33902978772603085559596380624168863702614844091091365457344330328324635085280554632014188452404079317475776)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15387321335580810055720039958490666664152019075782669011076303451419272284438251729996094032758834944962391)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6917563526809352821660728922599506854507371885081832380572043324121401129842343124659841649268636865448261)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3080578353422031391087923828966453956408314324983125302078899635582350534130147055876842329965119154660134)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1359014387758804552797279302384167444186322963556937131272306014488640427451808723143888038531316477116082)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  593952871734669351352614675366201680438326404109783533863605871378540181710918909004191933764580691660237)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  257181205609381363445474742255526888919011444656487668987937061184880954029124176110164821981500675200467)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  110333827571476178283805974572422078241923994869405228823571824976813835443464159149617092454601443846856)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  46901096849359548598030680892988600441945956833899401006836693275901420201442377073625181036969722002401)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  19755342244704333562853842753561747862367681632745902144886839983216306792444025802084499395764742337696)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  8245851158358469345831580273399339388878368624409501035288102986958210435536871351748583632669473652001)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3410811212489669455387005762578972016401218506714583352046524601265310812167666205970074317356767488210)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1398211169295878244953717693619777455700273627219000854373461124757180789801012323138332582661781135955)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  568070376924269854258908334669388668339020728965513199837951168077962876904314029570652046087170143636)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  228753089573969858797539365414537630455718843484395797755581041643323701890505222030291484736930509413)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  91303656490973206429870244988201108681940160409246801292555423368916752806781704737771709294173274326)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  36123219135367658635354255660358276393724511694550236673574519457168694368623170425579131030450443032)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  14167142634018493661728131641245212439054101759777379865676285226039498762611842360757890130796016317)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5508024743594246970220057476792118666813498790747765443471363665982435928922200540054110167403127826)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2122986958788415678036076216755721467920224495089087434457396677308891001315768419817478101313173333)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  811253185948006252156337030880053540675415404880160201386596766203745964611164179453393158826618382)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  307356750554571663111671953857747333623712185976516135243833759786556378019769281026411291637668679)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  115458456482844912278364916051942933587315365338516480858036415783544939131370493459272978994569008)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  43005557640193437513758370485790451828343922428909937834340925228009171326936765425702338164717394)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15883940722434315555583526513098283513428158550630296853696526294727739372165299661373887480197655)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5817622880100087289706471368268897823925865461094279778685530167794735633184587586512605554094139)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2113027292388215383384902730748577800965869698254445976104928225671717828483657681964463901815814)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  761123778402704116290219071467663639037645253999010817405412392379819402620129089770796174579985)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  271903210325061929562216655058598158652380701216334257562881898232453000901024256602841866154467)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  96338587819901656764277777811343395898370623624615114974481554932817621444371573457547156043027)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  33855634887481753601934627470482488249490093978944039022978218200323715028386602618333004613559)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11801142784660292186534810895891576637620037023985003722554303488879101684409685068181512409756)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4080346797004230778284237670592229353363951694847475434032435654359930307364639214392562719754)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1399481989559843430660920757181499912956361150288886898083540907610469273025768568401200092913)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  476158918311473346377755538381091878761081950130130398354706346638323919655542280116848758666)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  160719243492927760573229511524478280117459965816923882158044386161166424281530519837520022895)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  53818549913498936685516959468622130449770070432897552830458261816568092357816117751735593512)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  17879727850704803165154005146105716568141667156875353452403019822385690549854063241717431229)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5893470274131850050455164699819786557069644888091093665784854499907028684197178150140971172)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1927431238333024601928975790464443931942664671629763405595811934073370469604414666977622512)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  625461318901260630002780142214188309568333154119687878014743394258733320466146951484989487)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  201396442462929629780557831201350302328678907688739924332273516443432730099118970359446013)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  64350031595480698195187632786846164018625605752032864882432663738108508088856005377758103)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  20403612659279058811629855164303095980734681564212864555437616704918751116012388731887185)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6420107032673464067478586260827535025706505865952476985262515704982045321421165234013162)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2004794067396725613361889452711807529277381113755822137760056210265476119880015404391831)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  621304981178716779407428360038480251682997731531771054440456066314969110343334819320524)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  191100838271598461840789183587450734318889830718539672128266077179380698983292398735863)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  58338871041528099446932901933760742666997727692004285454098931991285546534192575253936)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  17676894272764358334185761536639304230478036761916155469457036277860228943145444805485)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5316442618057808921118398829027243898708000398300859133430232367136929134823185601661)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1587150433662812134344451743489804325493537934508286475132215825087676638419440387552)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  470339321087277591251779861881261768728636751086183134497247586403883568139259036115)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  138361425199269938520982181645980820222504917244541730707410310752765026122598399639)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  40405779369493323177137705013206813864205895197663672005725192975235532378489814027)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11714148454305351304191858180993050318476430519134695562887480798295624085425732765)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3371558188074921700297922131675114341827848694791383519806308740969539028810304320)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  963423193803261889964685815714152664253103249045141373192704022569284709107148512)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  273327744485321878291024431974313056605948782996938525567546754792227199366933444)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  76991730027329504458982487871966581527445582610250072824890164569643179984196778)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21533351016136120329387220052748946269276628929434789521261721162634530079868402)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5979979070509533048027262821970493939428762559133625902558835247014974159029670)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1649002889983821557129845325778487549188142351077220989216756344679693659455306)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  451533492660709838490739461029255520118855101183326720183669979697827493940374)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  122777363042472423826084446518287987115484367901030976983025887857476007241166)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  33152728650116463955828458361552583058210906932268057411888423622642813614057)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  8890079792316428993241760103418812617948744664767479591869701656345062229588)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2367500555302219402185818776098054525625249822058751604606595557624219621297)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  626159698251605642668385708271183572281544077736147167710314788759171553110)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  164476236405621721362112883438033227096563530243274144786589079769382128734)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  42909807333401513096470074960289146104365468314301453696369014344470201044)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11118790639712553134222831610813443944024426202288570094142463800943945858)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2861661426727762745451724033243470304714019204925753100645534500993743574)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  731561226051720630884607364036597580679771404906355180620191204655841534)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  185766229493032334041489795924184659589824975660773452165571304662300350)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  46857416268228191555039384647565203313294710460675863181564794322218593)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11740784677081729058657595546216437665062844022753008790870201803910499)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2922367010278589810234328714192591214787659798010120363397893230811162)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  722608019498618097701432100076492212567464681928526784019444539472502)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  177505833604297376144512225956684151282906999547666033753469454064308)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  43318725458201218833627979739151936843150513501542850079746761125724)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  10502753157728905916634305693036038530276826035185762025063070003612)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2529916967615284321400157210514678263046911751565233817624981825749)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  605474811966852462774833090487881352146598353546103511944758143083)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  143973841767317043597185403333825897348073231886751391407822883105)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  34015723555222151979559668184750159455109614228037050647815289054)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7985374033618188486601203600617152286198413367844692610875450818)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1862691705350919262500260844422122112753419971266193632064575628)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  431745201371402506008809968055918255176220123123484430029717402)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  99440992463567904872281968953405115938970789177988452222455195)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  22759633378880396049095860353839022177629066086599119650132626)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5176513643619638944048951873943423628269559975807630345639002)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1170016755389539788380436228117947796418712408852049646995106)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  262808656082222555837306081210618205835764028970434795591968)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  58666514479806482326929441881640849167599909289675930492757)
  (@_root_.List.nil
  (@_root_.Int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

noncomputable def panelAt (i : Fin 16) : Record := panelBank.getD i.val ⟨[],[],[],0,0,0,0⟩

noncomputable def sequenceCacheAt (i : Fin 16) : CertifiedMomentSequenceCache.Aux :=
  sequenceCacheBank.getD i.val ⟨[],[],[]⟩

noncomputable def totalNumerators : List ℤ :=
  CertifiedGlobalJetCenters.sumLists (List.ofFn (fun i : Fin 16 => (panelAt i).z))

end CertifiedMomentRecords

end Height100Module74

section Height100Module75
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentRecords

end CertifiedMomentRecords

end Height100Module75

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
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
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
open Finset
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
open Finset
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
open Finset
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

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset
open scoped BigOperators

namespace CertifiedGlobalMomentEnclosure
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedGlobalJetCenters
open CertifiedZetaQuadrature CertifiedIntegerRounding

end CertifiedGlobalMomentEnclosure

end Height100Module89

section Height100Module90

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset
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
open Finset
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
open Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module95

section Height100Module96

namespace CertifiedIntegerLocalPolynomial
open Finset

end CertifiedIntegerLocalPolynomial

end Height100Module96

section Height100Module97

open Finset
set_option autoImplicit false

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module97

section Height100Module98

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module98

section Height100Module99

namespace CertifiedLocalPolynomial
open Finset TaoZetaNumerics

end CertifiedLocalPolynomial

end Height100Module99

section Height100Module100

namespace CertifiedLocalPolynomial
open Finset CertifiedLocalXi

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
open CertifiedLocalCandidates CertifiedLocalPolynomial TaoZetaNumerics
open Finset

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

end CertifiedFastLocalBoxes

end Height100Module108

section Height100Module109

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein

end CertifiedStreamingLocalBoxes

end Height100Module109

section Height100Module110

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

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


noncomputable def TaoFivePrimes_RH14To100MomentInterfaceV2 : Nat := 14

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/- Source module: PackedConvolution. -/
section Height100Module0

open Finset
namespace CertifiedPackedConvolution

noncomputable def coefficient : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x::_, 0 => x
  | _::xs, n+1 => coefficient xs n

noncomputable def addLists : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::addLists xs ys

noncomputable def convolution : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x::xs, ys => addLists (ys.map (x*·)) (0::convolution xs ys)

lemma coefficient_eq_getD (xs : List ℕ) (k : ℕ) : coefficient xs k=xs.getD k 0 := by
  induction xs generalizing k with
  | nil => simp [coefficient,List.getD]
  | cons x xs ih => cases k <;> simp [coefficient,List.getD,ih]

lemma coefficient_add (xs ys : List ℕ) (k : ℕ) :
    coefficient (addLists xs ys) k=coefficient xs k+coefficient ys k := by
  induction xs generalizing ys k with
  | nil => simp [addLists,coefficient]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists,coefficient]
    | cons y ys => cases k <;> simp [addLists,coefficient,ih]

lemma coefficient_map (a : ℕ) (xs : List ℕ) (k : ℕ) :
    coefficient (xs.map (a*·)) k=a*coefficient xs k := by
  induction xs generalizing k with
  | nil => simp [coefficient]
  | cons x xs ih => cases k <;> simp [coefficient,ih]

lemma ofDigits_add (B : ℕ) (xs ys : List ℕ) :
    Nat.ofDigits B (addLists xs ys)=Nat.ofDigits B xs+Nat.ofDigits B ys := by
  induction xs generalizing ys with
  | nil => simp [addLists]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists]
    | cons y ys => simp only [addLists,Nat.ofDigits_cons,ih]; ring

lemma ofDigits_map_mul (B a : ℕ) (xs : List ℕ) :
    Nat.ofDigits B (xs.map (a*·))=a*Nat.ofDigits B xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,Nat.ofDigits_cons,ih]; ring

lemma ofDigits_convolution (B : ℕ) (xs ys : List ℕ) :
    Nat.ofDigits B (convolution xs ys)=Nat.ofDigits B xs*Nat.ofDigits B ys := by
  induction xs with
  | nil => simp [convolution]
  | cons x xs ih =>
    rw [convolution,ofDigits_add,ofDigits_map_mul,Nat.ofDigits_cons,ih,Nat.ofDigits_cons]
    ring

lemma sum_convolution (xs ys : List ℕ) : (convolution xs ys).sum=xs.sum*ys.sum := by
  simpa only [Nat.ofDigits_one] using ofDigits_convolution 1 xs ys

lemma coefficient_convolution (xs ys : List ℕ) (k : ℕ) :
    coefficient (convolution xs ys) k=
      ∑ i ∈ range (k+1), coefficient xs i*coefficient ys (k-i) := by
  induction xs generalizing k with
  | nil => simp [convolution,coefficient]
  | cons x xs ih =>
    cases k with
    | zero => simp [convolution,coefficient_add,coefficient_map,coefficient]
    | succ k =>
      rw [convolution,coefficient_add,coefficient_map,coefficient,ih]
      conv_rhs => rw [sum_range_succ']
      simp only [coefficient,Nat.add_sub_add_right,Nat.sub_zero]
      rw [add_comm]

lemma member_le_sum (xs : List ℕ) (x : ℕ) (hx : x∈xs) : x≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · simp
    · have h := ih hx
      simp only [List.sum_cons]
      omega

lemma digit_ofDigits (B : ℕ) (hB : 0< B) (xs : List ℕ)
    (hsmall : ∀ x∈xs,x< B) (k : ℕ) :
    (Nat.ofDigits B xs/B^k)%B=coefficient xs k := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [coefficient]
    | cons x xs =>
      have hx := hsmall x List.mem_cons_self
      simp [Nat.ofDigits_cons,coefficient,Nat.add_mod,Nat.mod_eq_of_lt hx]
  | succ k ih =>
    rw [Nat.pow_succ',← Nat.div_div_eq_div_mul,
      Nat.ofDigits_div_eq_ofDigits_tail hB xs hsmall]
    rw [ih xs.tail (fun x hx => hsmall x (List.mem_of_mem_tail hx))]
    cases xs <;> simp [coefficient]

/-- One scalar no-carry check suffices for every convolution digit. -/
theorem packed_product_digit (B : ℕ) (hB : 0< B) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum< B) (k : ℕ) :
    ((Nat.ofDigits B xs*Nat.ofDigits B ys)/B^k)%B =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [← ofDigits_convolution]
  have hs : ∀ x∈convolution xs ys,x< B := by
    intro x hx
    have h := member_le_sum (convolution xs ys) x hx
    rw [sum_convolution] at h
    exact h.trans_lt hcarry
  rw [digit_ofDigits B hB _ hs,coefficient_convolution]
  simp_rw [coefficient_eq_getD]

lemma encode_eq_ofDigits (bits : ℕ) (xs : List ℕ) :
    encode bits xs=Nat.ofDigits (2^bits) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [encode,Nat.ofDigits_cons,Nat.shiftLeft_eq',Nat.shiftLeft_eq,ih]; ring

/-- Binary-stride encoding has the same verified digit-extraction rule. -/
theorem shift_product_digit (bits : ℕ) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum<2^bits) (k : ℕ) :
    ((encode bits xs*encode bits ys)/(2^bits)^k)%(2^bits) =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [encode_eq_ofDigits,encode_eq_ofDigits]
  exact packed_product_digit _ (by positivity) xs ys hcarry k

/-- Direct bit-shift extraction avoids constructing a large divisor in executable checks. -/
theorem shiftRight_product_digit (bits : ℕ) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum<2^bits) (k : ℕ) :
    ((encode bits xs*encode bits ys) >>> (bits*k))%(2^bits) =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [Nat.shiftRight_eq_div_pow,pow_mul]
  exact shift_product_digit bits xs ys hcarry k

end CertifiedPackedConvolution

end Height100Module0

/- Source module: ScalarPanelIdentity. -/
section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution

lemma sum_triangle {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ j ∈ range N, ∑ m ∈ range (j+1), f m (j-m)) =
      ∑ m ∈ range N, ∑ l ∈ range (N-m), f m l := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun x _ => ⟨x.2, x.1-x.2⟩)
  · intro x hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · intro x hx y hy hxy
    simp only [mem_sigma, mem_range] at hx hy
    have h1 := congrArg Sigma.fst hxy
    have h2 := congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) hxy
    apply Sigma.ext <;> simp_all
    omega
  · intro y hy
    simp only [mem_sigma, mem_range] at hy
    refine ⟨⟨y.1+y.2, y.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · simp
  · intro x hx
    rfl

/-- A truncated convolution can be integrated by first correlating the base
coefficients with the integration weights. -/
theorem integrated_convolution {R : Type*} [CommSemiring R]
    (N : ℕ) (a h w : ℕ → R) :
    (∑ j ∈ range N, (∑ m ∈ range (j+1), a m * h (j-m)) * w j) =
      ∑ m ∈ range N, a m * (∑ l ∈ range (N-m), h l * w (m+l)) := by
  simp_rw [sum_mul]
  calc
    (∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w j) =
        ∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w (m+(j-m)) := by
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro m hm
      congr 2
      have hmj : m≤ j := by simpa using mem_range.mp hm
      omega
    _ = ∑ m ∈ range N, ∑ l ∈ range (N-m), a m * h l * w (m+l) :=
      sum_triangle N (fun m l => a m * h l * w (m+l))
    _ = _ := by simp_rw [mul_sum, mul_assoc]

/-- The common base correlation is independent of the moment order. -/
noncomputable def correlation {R : Type*} [Semiring R] (N : ℕ) (h w : ℕ → R) (m : ℕ) : R :=
  ∑ l ∈ range (N-m), h l * w (m+l)

end CertifiedMomentConvolution

end Height100Module1

/- Source module: TaylorQuadrature. -/
section Height100Module2

open Complex MeasureTheory Finset Metric Set

namespace CertifiedTaylorQuadrature

noncomputable def coefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial:ℂ)

noncomputable def polynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n * (x:ℂ)^n

noncomputable def panel (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n *
    (((h:ℂ)^(n+1)-(-h:ℂ)^(n+1))/(n+1))

lemma coefficient_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M : ℝ) (hR : 0< R) (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (n : ℕ) :
    ‖coefficient f c n‖ ≤  M/R^n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    hf.diffContOnCl hb
  rw [coefficient, norm_div, Complex.norm_natCast]
  have hn : (0:ℝ)< n.factorial := by positivity
  apply (div_le_iff₀ hn).mpr
  calc
    ‖iteratedDeriv n f c‖ ≤  n.factorial*M/R^n := hd
    _ = M/R^n*n.factorial := by ring

lemma series_sum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (x : ℝ) :
    HasSum (fun n : ℕ => coefficient f c n*(x:ℂ)^n) (f (c+x)) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf c (c+x)
  convert! h using 1
  ext n
  simp only [coefficient, add_sub_cancel_left, smul_eq_mul]
  ring

lemma point_error (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M h : ℝ) (hR : 0< R) (hM : 0≤ M) (hh : 0≤ h) (hhR : h< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) (x : ℝ) (hx : |x|≤ h) :
    ‖f (c+x)-polynomial f c N x‖ ≤  M*(h/R)^N/(1-h/R) := by
  have hq0 : 0≤ h/R := div_nonneg hh hR.le
  have hq1 : h/R<1 := (div_lt_one hR).mpr hhR
  have hs := series_sum f hf c x
  have he : f (c+x)-polynomial f c N x =
      ∑' n : ℕ, coefficient f c (n+N)*(x:ℂ)^(n+N) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    unfold polynomial
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using h.symm
  rw [he]
  have hgeo : HasSum (fun n : ℕ => (M*(h/R)^N)*(h/R)^n)
      ((M*(h/R)^N)*(1-h/R)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M*(h/R)^N)
  have hterms : ∀ n : ℕ, ‖coefficient f c (n+N)*(x:ℂ)^(n+N)‖ ≤  (M*(h/R)^N)*(h/R)^n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖coefficient f c (n+N)‖*|x|^(n+N) ≤  (M/R^(n+N))*h^(n+N) := by
        gcongr
        exact coefficient_bound f hf c R M hR hb (n+N)
      _ = (M*(h/R)^N)*(h/R)^n := by rw [div_pow, div_pow, pow_add, pow_add]; ring
  have ht := tsum_of_norm_bounded hgeo hterms
  simpa only [div_eq_mul_inv] using ht

lemma polynomial_integrable (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (polynomial f c N) volume a b := by
  apply Continuous.intervalIntegrable
  unfold polynomial
  fun_prop

lemma integral_polynomial (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) :
    (∫ x in -h..h, polynomial f c N x) = panel f c h N := by
  unfold polynomial panel
  rw [intervalIntegral.integral_finsetSum (fun n _ => (by
    apply Continuous.intervalIntegrable
    fun_prop))]
  apply sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [show (fun x : ℝ => (x:ℂ)^n) = (fun x : ℝ => ((x^n:ℝ):ℂ)) by ext x; push_cast; rfl,
    intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  rfl

/-- A complex analytic function can be integrated by a finite Taylor polynomial with a
geometric, arbitrarily high-order error bound. Every coefficient remains exact. -/
theorem panel_error (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M h : ℝ) (hR : 0< R) (hM : 0≤ M) (hh : 0≤ h) (hhR : h< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) :
    ‖(∫ x in -h..h, f (c+x))-panel f c h N‖ ≤ 
      2*h*M*(h/R)^N/(1-h/R) := by
  rw [← integral_polynomial]
  have hfint : IntervalIntegrable (fun x : ℝ => f (c+x)) volume (-h) h :=
    (hf.continuous.comp (by fun_prop)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hfint (polynomial_integrable f c N (-h) h)]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a:=-h) (b:=h)
    (f:=fun x : ℝ => f (c+x)-polynomial f c N x) (C:=M*(h/R)^N/(1-h/R)) (by
      intro x hx
      rw [uIoc_of_le (by linarith : -h≤ h)] at hx
      exact point_error f hf c R M h hR hM hh hhR hb N x
        (abs_le.mpr ⟨hx.1.le,hx.2⟩))
  have ha : |h-(-h)|=2*h := by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring
  rw [ha] at he
  convert he using 1
  ring

end CertifiedTaylorQuadrature

end Height100Module2

/- Source module: MomentJetIdentity. -/
section Height100Module3

set_option autoImplicit false
open Complex Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

lemma coefficient_mul (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z * g z) c n =
      ∑ m ∈ range (n+1), coefficient f c m * coefficient g c (n-m) := by
  unfold coefficient
  rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt, sum_div]
  apply sum_congr rfl
  intro m hm
  have hmn : m≤ n := by simpa using mem_range.mp hm
  rw [Nat.cast_choose ℂ hmn]
  have h0 : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have h1 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n-m).factorial:ℂ)≠0 := by exact_mod_cast (n-m).factorial_ne_zero
  field_simp

lemma power_moment_coefficient (a c : ℂ) (k m : ℕ) :
    coefficient (fun z => (a*z)^k / (k.factorial:ℂ)) c m =
      if m≤ k then a^k*c^(k-m)/(((k-m).factorial:ℂ)*m.factorial) else 0 := by
  have he : (fun z : ℂ => (a*z)^k/(k.factorial:ℂ)) =
      (fun z => (a^k/(k.factorial:ℂ))*z^k) := by ext z; simp [mul_pow]; ring
  rw [he, coefficient, iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  by_cases hmk : m≤ k
  · rw [if_pos hmk]
    have hf : ((k-m).factorial:ℂ)*(k.descFactorial m:ℂ) = k.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial hmk
    have h0 : (k.factorial:ℂ)≠0 := by exact_mod_cast k.factorial_ne_zero
    have h1 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
    have h2 : ((k-m).factorial:ℂ)≠0 := by exact_mod_cast (k-m).factorial_ne_zero
    field_simp
    linear_combination (a^k*c^(k-m))*hf
  · rw [if_neg hmk, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

noncomputable def scaledCoefficient (f : ℂ → ℂ) (c h : ℂ) (n : ℕ) : ℂ :=
  coefficient f c n * h^n

lemma scaled_power_moment_coefficient (a c h : ℂ) (k m : ℕ) :
    scaledCoefficient (fun z => (a*z)^k / (k.factorial:ℂ)) c h m =
      if m≤ k then (a*c)^(k-m)*(a*h)^m/(((k-m).factorial:ℂ)*m.factorial) else 0 := by
  rw [scaledCoefficient, power_moment_coefficient]
  by_cases hmk : m≤ k
  · rw [if_pos hmk, if_pos hmk]
    have hk : k = (k-m)+m := by omega
    conv_lhs => rw [hk]
    simp only [Nat.add_sub_cancel_right, pow_add, mul_pow]
    ring
  · simp [hmk]

lemma scaled_coefficient_mul (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c h : ℂ) (n : ℕ) :
    scaledCoefficient (fun z => f z * g z) c h n =
      ∑ m ∈ range (n+1), scaledCoefficient f c h m * scaledCoefficient g c h (n-m) := by
  unfold scaledCoefficient
  rw [coefficient_mul f g hf hg, sum_mul]
  apply sum_congr rfl
  intro m hm
  have hmn : m≤ n := by simpa using mem_range.mp hm
  have hn : n=m+(n-m) := by omega
  conv_lhs => rw [hn]
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

noncomputable def integrationWeight (j : ℕ) : ℂ :=
  (1 - (-1:ℂ)^(j+1)) / (j+1)

lemma panel_eq_scaled (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) :
    panel f c h N = (h:ℂ) *
      ∑ j ∈ range N, scaledCoefficient f c h j * integrationWeight j := by
  unfold panel
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  unfold scaledCoefficient integrationWeight
  rw [show (-h:ℂ) = (-1:ℂ)*(h:ℂ) by ring, mul_pow, pow_succ]
  ring

lemma sum_restrict_swap {R : Type*} [AddCommMonoid R] (N k : ℕ) (f : ℕ → R) :
    (∑ m ∈ range N, if m≤ k then f m else 0) =
      ∑ m ∈ range (k+1), if m< N then f m else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  congr 1
  ext m
  simp only [mem_filter, mem_range]
  omega

/-- All panel moments are a scalar convolution of a common correlation vector
and the exponential coefficients of the center. -/
theorem power_moment_panel (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a c : ℂ) (h : ℝ) (N k : ℕ) :
    panel (fun z => (a*z)^k / (k.factorial:ℂ) * f z) c h N =
      (h:ℂ) * ∑ m ∈ range (k+1),
        (if m< N then
          (a*(h:ℂ))^m/(m.factorial:ℂ) *
            correlation N (scaledCoefficient f c h) integrationWeight m
          else 0) * ((a*c)^(k-m)/((k-m).factorial:ℂ)) := by
  rw [panel_eq_scaled]
  congr 1
  have hp : Differentiable ℂ (fun z : ℂ => (a*z)^k / (k.factorial:ℂ)) := by fun_prop
  simp_rw [scaled_coefficient_mul _ _ hp hf,
    scaled_power_moment_coefficient]
  rw [integrated_convolution]
  simp only [correlation]
  simp_rw [ite_mul, zero_mul]
  rw [sum_restrict_swap]
  apply sum_congr rfl
  intro m hm
  by_cases hmn : m< N
  · simp only [if_pos hmn]
    ring
  · simp [hmn]

end CertifiedMomentConvolution

end Height100Module3

/- Source module: ExponentialJetEnclosure. -/
section Height100Module4

open Complex Finset
namespace CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution

lemma coefficient_deriv (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (deriv f) c n=(n+1:ℂ)*coefficient f c (n+1) := by
  unfold coefficient
  rw [← iteratedDeriv_succ',Nat.factorial_succ]
  push_cast
  have h0 : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h1 : (n+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

lemma exp_coefficient_recurrence (g : ℂ → ℂ) (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    (n+1:ℂ)*coefficient (fun z => Complex.exp (g z)) c (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*coefficient g c (k+1)*
        coefficient (fun z => Complex.exp (g z)) c (n-k) := by
  have hf : Differentiable ℂ (fun z => Complex.exp (g z)) := by fun_prop
  have he : deriv (fun z => Complex.exp (g z)) =
      (fun z => deriv g z*Complex.exp (g z)) := by
    funext z
    exact ((hg z).hasDerivAt.cexp).deriv.trans (mul_comm _ _)
  rw [← coefficient_deriv,he,coefficient_mul _ _ hg.deriv hf]
  simp_rw [coefficient_deriv]

lemma scaled_exp_coefficient_recurrence (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (c h : ℂ) (n : ℕ) :
    (n+1:ℂ)*scaledCoefficient (fun z => Complex.exp (g z)) c h (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*scaledCoefficient g c h (k+1)*
        scaledCoefficient (fun z => Complex.exp (g z)) c h (n-k) := by
  unfold scaledCoefficient
  rw [← mul_assoc,exp_coefficient_recurrence g hg c n,sum_mul]
  apply sum_congr rfl
  intro k hk
  have he : n+1=(k+1)+(n-k) := by have := mem_range.mp hk; omega
  conv_lhs => rw [he,pow_add]
  ring

lemma product_error (a b x y : ℂ) (r s : ℝ)
    (ha : ‖a-x‖≤ r) (hb : ‖b-y‖≤ s) :
    ‖a*b-x*y‖≤ ‖x‖*s+r*‖y‖+r*s := by
  have hr : 0≤ r := (norm_nonneg _).trans ha
  have hs : 0≤ s := (norm_nonneg _).trans hb
  have he : a*b-x*y=x*(b-y)+(a-x)*y+(a-x)*(b-y) := by ring
  rw [he]
  calc
    _ ≤  ‖x*(b-y)+(a-x)*y‖+‖(a-x)*(b-y)‖ := norm_add_le _ _
    _ ≤  (‖x*(b-y)‖+‖(a-x)*y‖)+‖(a-x)*(b-y)‖ := by gcongr; exact norm_add_le _ _
    _ = (‖x‖*‖b-y‖+‖a-x‖*‖y‖)+‖a-x‖*‖b-y‖ := by simp only [norm_mul]
    _ ≤  _ := by gcongr

noncomputable def residual (G F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n+1:ℂ)*F (n+1)-∑ k ∈ range (n+1), (k+1:ℂ)*G (k+1)*F (n-k)

noncomputable def errorSum (G F : ℕ → ℂ) (r s : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), (k+1:ℝ)*
    (‖G (k+1)‖*s (n-k)+r (k+1)*‖F (n-k)‖+r (k+1)*s (n-k))

/- A finite ODE residual certificate proves every coefficient enclosure by induction.
The residual and its error bound are convolutions, so they support packed-integer verification. -/
theorem enclosure_of_recurrence (A F G C : ℕ → ℂ) (r s : ℕ → ℝ) (N : ℕ)
    (hrec : ∀ n : ℕ, (n+1:ℂ)*F (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*A (k+1)*F (n-k))
    (hG : ∀ j< N, ‖A j-G j‖≤ r j)
    (h0 : ‖F 0-C 0‖≤ s 0)
    (hcheck : ∀ n, n+1< N → ‖residual G C n‖+errorSum G C r s n≤ (n+1:ℝ)*s (n+1)) :
    ∀ n< N, ‖F n-C n‖≤ s n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact h0
    | succ n =>
      have hp (k : ℕ) (hk : k∈range (n+1)) :
          ‖A (k+1)*F (n-k)-G (k+1)*C (n-k)‖ ≤ 
            ‖G (k+1)‖*s (n-k)+r (k+1)*‖C (n-k)‖+r (k+1)*s (n-k) := by
        have hk' := mem_range.mp hk
        exact product_error _ _ _ _ _ _ (hG (k+1) (by omega))
          (ih (n-k) (by omega) (by omega))
      have he : (n+1:ℂ)*(F (n+1)-C (n+1)) =
          (∑ k ∈ range (n+1), (k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))) - residual G C n := by
        unfold residual
        simp_rw [mul_sub,sum_sub_distrib]
        rw [hrec n]
        simp only [mul_assoc]
        ring
      have hm : (n+1:ℝ)*‖F (n+1)-C (n+1)‖≤ (n+1:ℝ)*s (n+1) := by
        calc
          _ = ‖(n+1:ℂ)*(F (n+1)-C (n+1))‖ := by rw [norm_mul]; norm_cast
          _ ≤  ‖∑ k ∈ range (n+1), (k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))‖+
              ‖residual G C n‖ := by rw [he]; exact norm_sub_le _ _
          _ ≤  (∑ k ∈ range (n+1), ‖(k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))‖)+
              ‖residual G C n‖ := by gcongr; exact norm_sum_le _ _
          _ ≤  errorSum G C r s n+‖residual G C n‖ := by
            gcongr
            unfold errorSum
            apply sum_le_sum
            intro k hk
            rw [norm_mul]
            have hc : ‖(k+1:ℂ)‖=(k+1:ℝ) := by norm_cast
            rw [hc]
            exact mul_le_mul_of_nonneg_left (hp k hk) (by positivity)
          _ ≤  _ := by linarith [hcheck n hn]
      have hpos : (0:ℝ)< n+1 := by positivity
      nlinarith

/- Specialized soundness for the Taylor jet of exp(g), with arbitrary complex panel scale. -/
end CertifiedExponentialJets

end Height100Module4

/- Source module: IntegerExponentialJet. -/
section Height100Module5

open Complex Finset
namespace CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets

noncomputable def integerResidual (D : ℕ) (G C : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n+1:ℤ)*C (n+1)*D-∑ k ∈ range (n+1), (k+1:ℤ)*G (k+1)*C (n-k)

noncomputable def integerErrorSum (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (k+1:ℤ)*
    (|G (k+1)| *(s (n-k):ℤ)+(r (k+1):ℤ) * |C (n-k)|+(r (k+1):ℤ)*s (n-k))

noncomputable def fixedCenter (D : ℕ) (G : ℕ → ℤ) (n : ℕ) : ℂ := (G n:ℂ)/D
noncomputable def fixedRadius (D : ℕ) (r : ℕ → ℕ) (n : ℕ) : ℝ := (r n:ℝ)/D

lemma residual_scale (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (n : ℕ) :
    CertifiedExponentialJets.residual (fixedCenter D G) (fixedCenter D C) n =
      (integerResidual D G C n:ℂ)/(D:ℂ)^2 := by
  have hd : (D:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hs : (∑ k ∈ range (n+1), (k+1:ℂ)*((G (k+1):ℂ)/D)*((C (n-k):ℂ)/D)) =
      (∑ k ∈ range (n+1), (k+1:ℂ)*(G (k+1):ℂ)*(C (n-k):ℂ))/(D:ℂ)^2 := by
    rw [sum_div]
    apply sum_congr rfl
    intro k _
    field_simp
  unfold CertifiedExponentialJets.residual fixedCenter integerResidual
  push_cast
  rw [hs]
  field_simp

lemma errorSum_scale (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) :
    errorSum (fixedCenter D G) (fixedCenter D C) (fixedRadius D r) (fixedRadius D s) n =
      (integerErrorSum G C r s n:ℝ)/(D:ℝ)^2 := by
  have hd : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  unfold errorSum fixedCenter fixedRadius integerErrorSum
  simp only [norm_div,Complex.norm_intCast,Complex.norm_natCast,
    Int.cast_sum,Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_abs]
  rw [sum_div]
  apply sum_congr rfl
  intro k _
  field_simp

lemma integer_check_sound (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ)
    (hc : |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D) :
    ‖CertifiedExponentialJets.residual (fixedCenter D G) (fixedCenter D C) n‖+
      errorSum (fixedCenter D G) (fixedCenter D C) (fixedRadius D r) (fixedRadius D s) n ≤ 
      (n+1:ℝ)*fixedRadius D s (n+1) := by
  have hd : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hnum : |(integerResidual D G C n:ℝ)|+(integerErrorSum G C r s n:ℝ) ≤ 
      (n+1:ℝ)*(s (n+1):ℝ)*D := by exact_mod_cast hc
  rw [residual_scale D hD,errorSum_scale D hD,norm_div,norm_pow,
    Complex.norm_intCast,Complex.norm_natCast]
  calc
    _ = (|(integerResidual D G C n:ℝ)|+(integerErrorSum G C r s n:ℝ))/(D:ℝ)^2 := by ring
    _ ≤  ((n+1:ℝ)*(s (n+1):ℝ)*D)/(D:ℝ)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = _ := by unfold fixedRadius; field_simp

/- Integer residual certificates also apply to any sequence satisfying the same ODE,
including a constant multiple of exp(g). -/
theorem fixed_enclosure_of_recurrence (A F : ℕ → ℂ)
    (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (N : ℕ)
    (hrec : ∀ n : ℕ, (n+1:ℂ)*F (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*A (k+1)*F (n-k))
    (hG : ∀ j< N, ‖A j-fixedCenter D G j‖≤ fixedRadius D r j)
    (h0 : ‖F 0-fixedCenter D C 0‖≤ fixedRadius D s 0)
    (hcheck : ∀ n : ℕ, n+1< N →
      |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D) :
    ∀ n< N, ‖F n-fixedCenter D C n‖≤ fixedRadius D s n := by
  apply enclosure_of_recurrence A F (fixedCenter D G) (fixedCenter D C)
    (fixedRadius D r) (fixedRadius D s) N hrec hG h0
  intro n hn
  exact integer_check_sound D hD G C r s n (hcheck n hn)

/- Entirely integer residual checks certify scaled Taylor coefficients of exp(g).
Only the input coefficient and initial-value enclosures involve the analytic function. -/
end CertifiedIntegerExponentialJets

end Height100Module5

/- Source module: SignedODEConvolution. -/
section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets

noncomputable def conv (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), a k*b (n-k)

noncomputable def absDerivative (G : ℕ → ℤ) (k : ℕ) : ℕ := (k+1)*(G (k+1)).natAbs
noncomputable def radiusDerivative (r : ℕ → ℕ) (k : ℕ) : ℕ := (k+1)*r (k+1)

noncomputable def positive (C : ℕ → ℤ) (k : ℕ) : ℕ := (C k).toNat
noncomputable def negative (C : ℕ → ℤ) (k : ℕ) : ℕ := (-C k).toNat

lemma signed_product (G C : ℕ → ℤ) (n : ℕ)
    (hG : ∀ k, k≤ n → G (k+1)≤ 0) :
    (∑ k ∈ range (n+1), (k+1:ℤ)*G (k+1)*C (n-k)) =
      -(conv (absDerivative G) (positive C) n:ℤ) +
        (conv (absDerivative G) (negative C) n:ℤ) := by
  unfold conv absDerivative positive negative
  push_cast
  rw [←sum_neg_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hkg := hG k (by simpa using mem_range.mp hk)
  calc
    _ = (k+1:ℤ)*G (k+1)*((C (n-k)).toNat-((-C (n-k)).toNat:ℤ)) := by
      rw [Int.toNat_sub_toNat_neg]
    _ = _ := by rw [abs_of_nonpos hkg]; ring

lemma error_product (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) :
    integerErrorSum G C r s n =
      (conv (absDerivative G) s n:ℤ) +
        (conv (radiusDerivative r) (fun j => (C j).natAbs+s j) n:ℤ) := by
  unfold integerErrorSum conv absDerivative radiusDerivative
  push_cast
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  ring

lemma residual_product (D : ℕ) (G C : ℕ → ℤ) (n : ℕ)
    (hG : ∀ k, k≤ n → G (k+1)≤ 0) :
    integerResidual D G C n = (n+1:ℤ)*C (n+1)*D +
      (conv (absDerivative G) (positive C) n:ℤ) -
        (conv (absDerivative G) (negative C) n:ℤ) := by
  rw [integerResidual,signed_product G C n hG]
  ring

/- Four nonnegative convolutions suffice for the complete signed ODE check
when the exponent's nonconstant Taylor coefficients are nonpositive. -/
theorem residual_check_of_convolutions (D : ℕ) (G C : ℕ → ℤ) (r s : ℕ → ℕ)
    (n cp cm es er : ℕ) (hG : ∀ k, k≤ n → G (k+1)≤ 0)
    (hp : cp=conv (absDerivative G) (positive C) n)
    (hm : cm=conv (absDerivative G) (negative C) n)
    (hes : es=conv (absDerivative G) s n)
    (her : er=conv (radiusDerivative r) (fun j => (C j).natAbs+s j) n)
    (hc : (((n+1:ℤ)*C (n+1)*D+(cp:ℤ)-(cm:ℤ)).natAbs+es+er)≤ (n+1)*s (n+1)*D) :
    |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D := by
  rw [residual_product D G C n hG,error_product,←hp,←hm,←hes,←her]
  have hh : (((((n+1:ℤ)*C (n+1)*D+(cp:ℤ)-(cm:ℤ)).natAbs+es+er):ℕ):ℤ) ≤ 
      (((n+1)*s (n+1)*D:ℕ):ℤ) := by exact_mod_cast hc
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Int.natCast_natAbs,add_assoc] using hh

noncomputable def vector (N : ℕ) (f : ℕ → ℕ) : List ℕ := List.ofFn (fun j : Fin N => f j.val)
noncomputable def packed (bits N : ℕ) (a b : ℕ → ℕ) : ℕ :=
  CertifiedPackedConvolution.encode bits (vector N a) *
    CertifiedPackedConvolution.encode bits (vector N b)
noncomputable def digit (bits p k : ℕ) : ℕ := (p >>> (bits*k)) % (2^bits)

end CertifiedSignedODEConvolution

end Height100Module6

/- Source module: ListODEVectors. -/
section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

lemma getD_mapIdx_zero {α β : Type*} [Zero α] [Zero β]
    (l : List α) (f : ℕ → α → β) (hf : ∀ j,f j 0=0) (j : ℕ) :
    (l.mapIdx f).getD j 0=f j (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_mapIdx]
  cases l[j]? <;> simp [hf]

lemma getD_tail {α : Type*} (l : List α) (j : ℕ) (d : α) :
    l.tail.getD j d=l.getD (j+1) d := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_tail]

lemma absDerivativeList_getD (g : List ℤ) (j : ℕ) :
    (absDerivativeList g).getD j 0=(j+1)*(g.getD (j+1) 0).natAbs := by
  rw [absDerivativeList,←List.mapIdx_eq_zipIdx_map (l := g.tail)
    (f := fun k (x : ℤ) => (k+1)*x.natAbs),
    getD_mapIdx_zero _ _ (by intro k; simp),getD_tail]

lemma radiusDerivativeList_getD (r : List ℕ) (j : ℕ) :
    (radiusDerivativeList r).getD j 0=(j+1)*r.getD (j+1) 0 := by
  rw [radiusDerivativeList,←List.mapIdx_eq_zipIdx_map (l := r.tail)
    (f := fun k (x : ℕ) => (k+1)*x),
    getD_mapIdx_zero _ _ (by intro k; simp),getD_tail]

lemma positiveList_getD (f : List ℤ) (j : ℕ) :
    (positiveList f).getD j 0=(f.getD j 0).toNat := by
  exact List.getD_map f 0 Int.toNat

lemma negativeList_getD (f : List ℤ) (j : ℕ) :
    (negativeList f).getD j 0=(-f.getD j 0).toNat := by
  exact List.getD_map f 0 (fun x : ℤ => (-x).toNat)

lemma radiusFactorList_getD (f : List ℤ) (s : List ℕ) (h : f.length=s.length) (j : ℕ) :
    (radiusFactorList f s).getD j 0=(f.getD j 0).natAbs+s.getD j 0 := by
  induction f generalizing s j with
  | nil => cases s <;> simp_all [radiusFactorList]
  | cons x xs ih =>
    cases s with
    | nil => simp at h
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j => exact ih ys (by simpa using h) j

lemma list_all_nonpos (g : List ℤ) (h : g.all (fun x => decide (x≤ 0))=true) (j : ℕ) :
    g.getD j 0≤ 0 := by
  induction g generalizing j with
  | nil => simp
  | cons x xs ih =>
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at h
    cases j with
    | zero => exact h.1
    | succ j => exact ih h.2 j

lemma digit_lists (bits : ℕ) (xs ys : List ℕ) (a b : ℕ → ℕ) (n : ℕ)
    (hx : ∀ k≤ n,xs.getD k 0=a k) (hy : ∀ k≤ n,ys.getD k 0=b k)
    (hc : xs.sum*ys.sum<2^bits) :
    digit bits (CertifiedPackedConvolution.encode bits xs*CertifiedPackedConvolution.encode bits ys) n=
      conv a b n := by
  rw [digit,CertifiedPackedConvolution.shiftRight_product_digit bits xs ys hc]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  rw [hx k (by omega),hy (n-k) (by omega)]

lemma digit_truncate (bits p N k : ℕ) (hk : k< N) :
    digit bits (p % 2^(bits*N)) k = digit bits p k := by
  unfold digit
  rw [Nat.shiftRight_eq_div_pow,Nat.shiftRight_eq_div_pow,
    show bits*N=bits*k+bits*(N-k) by
      rw [←Nat.mul_add]; congr 1; omega,pow_add,
    Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  have he : bits*(N-k)=bits+bits*(N-k-1) := by
    calc
      _ = bits*(1+(N-k-1)) := by congr 1; omega
      _ = _ := by ring
  rw [he,pow_add]
  exact Nat.dvd_mul_right _ _

end CertifiedListODEVectors

end Height100Module7

/- Source module: PackedHorner. -/
section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedPackedConvolution

/-- Coefficients of a polynomial after a nonnegative affine substitution. -/
noncomputable def translated (b q : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::as => addLists [a] (CertifiedPackedConvolution.convolution [b,q] (translated b q as))

lemma translated_evaluation (B b q : ℕ) (as : List ℕ) :
    Nat.ofDigits B (translated b q as)=Nat.ofDigits (b+q*B) as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [translated,ofDigits_add,ofDigits_convolution,ih]
    simp only [Nat.ofDigits_cons,Nat.ofDigits_nil]
    ring

lemma translated_sum (b q : ℕ) (as : List ℕ) :
    (translated b q as).sum=Nat.ofDigits (b+q) as := by
  simpa only [Nat.ofDigits_one,mul_one] using translated_evaluation 1 b q as

/-- Horner arithmetic reduced modulo a fixed window at every step. -/
noncomputable def modularHorner (a M : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => (x+a*modularHorner a M xs)%M

lemma modularHorner_eq (a M : ℕ) (xs : List ℕ) :
    modularHorner a M xs=Nat.ofDigits a xs%M := by
  induction xs with
  | nil => simp [modularHorner]
  | cons x xs ih => simp only [modularHorner,ih,Nat.ofDigits_cons,Nat.add_mod,Nat.mul_mod,Nat.mod_mod]

/-- A single scalar carry bound certifies every digit of the affine Horner expansion. -/
theorem modularHorner_digit (bits N b q : ℕ) (xs : List ℕ)
    (hcarry : Nat.ofDigits (b+q) xs<2^bits) (k : ℕ) (hk : k< N) :
    ((modularHorner (b+q*2^bits) (2^(bits*N)) xs) >>> (bits*k))%2^bits=
      (translated b q xs).getD k 0 := by
  rw [modularHorner_eq]
  change CertifiedSignedODEConvolution.digit bits
    (Nat.ofDigits (b+q*2^bits) xs%2^(bits*N)) k=_
  rw [CertifiedListODEVectors.digit_truncate bits _ N k hk]
  unfold CertifiedSignedODEConvolution.digit
  rw [Nat.shiftRight_eq_div_pow,pow_mul,←translated_evaluation]
  rw [digit_ofDigits _ (by positivity),coefficient_eq_getD]
  intro x hx
  exact (member_le_sum _ _ hx).trans_lt ((translated_sum b q xs) ▸ hcarry)

lemma ofDigits_add_complex (z : ℂ) (xs ys : List ℕ) :
    Nat.ofDigits z (addLists xs ys)=Nat.ofDigits z xs+Nat.ofDigits z ys := by
  induction xs generalizing ys with
  | nil => simp [addLists,Nat.ofDigits]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists,Nat.ofDigits]
    | cons y ys => simp only [addLists,Nat.ofDigits,Nat.cast_add,ih]; ring

lemma ofDigits_map_complex (z : ℂ) (a : ℕ) (xs : List ℕ) :
    Nat.ofDigits z (xs.map (a*·))=(a:ℂ)*Nat.ofDigits z xs := by
  induction xs with
  | nil => simp [Nat.ofDigits]
  | cons x xs ih => simp only [List.map_cons,Nat.ofDigits,Nat.cast_mul,ih]; ring

lemma ofDigits_convolution_complex (z : ℂ) (xs ys : List ℕ) :
    Nat.ofDigits z (CertifiedPackedConvolution.convolution xs ys)=Nat.ofDigits z xs*Nat.ofDigits z ys := by
  induction xs with
  | nil => simp [CertifiedPackedConvolution.convolution,Nat.ofDigits]
  | cons x xs ih =>
    rw [CertifiedPackedConvolution.convolution,ofDigits_add_complex,ofDigits_map_complex]
    simp only [Nat.ofDigits,Nat.cast_zero,ih]
    ring

lemma translated_complex (z : ℂ) (b q : ℕ) (xs : List ℕ) :
    Nat.ofDigits z (translated b q xs)=Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [translated,ofDigits_add_complex,ofDigits_convolution_complex,ih]
    simp only [Nat.ofDigits]
    ring

end CertifiedPackedHorner

namespace CertifiedPackedHorner
/-- Matching the recursive Nat forces the kernel to evaluate it once before the
small-multiple and shift branches reuse its literal value. -/
noncomputable def bitStep (bits b q mask x : ℕ) : ℕ → ℕ
  | 0 => x &&& mask
  | n+1 => (x+b*(n+1)+q*((n+1) <<< bits)) &&& mask

noncomputable def bitHorner (bits N b q : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => bitStep bits b q ((1 <<< (bits*N))-1) x (bitHorner bits N b q xs)

lemma bitStep_eq (bits N b q x n : ℕ) :
    bitStep bits b q ((1 <<< (bits*N))-1) x n=
      (x+(b+q*2^bits)*n)%2^(bits*N) := by
  cases n <;>
    simp only [bitStep,Nat.shiftLeft_eq,one_mul,
      Nat.and_two_pow_sub_one_eq_mod,mul_zero,add_zero]
  congr 1
  ring

lemma bitHorner_eq (bits N b q : ℕ) (xs : List ℕ) :
    bitHorner bits N b q xs=modularHorner (b+q*2^bits) (2^(bits*N)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitHorner,bitStep_eq,ih,modularHorner]

lemma bitHorner_digit (bits N b q : ℕ) (xs : List ℕ)
    (hcarry : Nat.ofDigits (b+q) xs<2^bits) (k : ℕ) (hk : k< N) :
    ((bitHorner bits N b q xs) >>> (bits*k))%2^bits=(translated b q xs).getD k 0 := by
  rw [bitHorner_eq]
  exact modularHorner_digit bits N b q xs hcarry k hk
end CertifiedPackedHorner

end Height100Module8

/- Source module: ZetaSix. -/
section Height100Module9
/- Reused accepted theta-kernel and Mellin lemmas by @Gabewhigham.
Original accepted proof: https://prove2.me/submissions/7ab19408-190a-439f-81f8-63e983ebb00b
Published September6,2026. The unused height-six conclusion is omitted. -/

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaSix

/-- The Jacobi-theta functional-equation pair underlying Mathlib's completed zeta function. -/
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0

/-! ### Bounds for the theta kernel -/

lemma evenKernel_zero_eq_F_int {t : ℝ} (ht : 0 < t) :
    evenKernel 0 t = HurwitzKernelBounds.F_int 0 0 t := by
  have h := (hasSum_int_evenKernel 0 ht).tsum_eq
  have h2 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = ∑' n : ℤ, HurwitzKernelBounds.f_int 0 0 t n := by
    simp only [HurwitzKernelBounds.F_int, Function.Periodic.lift_coe]
  simp only [QuotientAddGroup.mk_zero] at h2 h
  rw [h2, ← h]
  simp [HurwitzKernelBounds.f_int]

/-- Explicit bound for the theta kernel: `|θ t - 1| ≤  2 e ^ (-π t) / (1 - e ^ (-π t))`. -/
lemma abs_evenKernel_zero_sub_one_le {t : ℝ} (ht : 0 < t) :
    |evenKernel 0 t - 1| ≤  2 * rexp (-π * t) / (1 - rexp (-π * t)) := by
  have h1 := HurwitzKernelBounds.F_nat_zero_zero_sub_le ht
  have h2 := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one ht
  have h3 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 (1 - 0) t :=
    HurwitzKernelBounds.F_int_eq_of_mem_Icc 0 (by simp) ht
  simp only [QuotientAddGroup.mk_zero, sub_zero] at h3
  simp only [Real.norm_eq_abs, one_pow, mul_one] at h1 h2
  rw [evenKernel_zero_eq_F_int ht, h3,
    show HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 1 t - 1
      = (HurwitzKernelBounds.F_nat 0 0 t - 1) + HurwitzKernelBounds.F_nat 0 1 t from by ring]
  calc |_| ≤  |HurwitzKernelBounds.F_nat 0 0 t - 1| + |HurwitzKernelBounds.F_nat 0 1 t| :=
        abs_add_le _ _
    _ ≤  rexp (-π * t) / (1 - rexp (-π * t)) + rexp (-π * t) / (1 - rexp (-π * t)) :=
        add_le_add h1 h2
    _ = 2 * rexp (-π * t) / (1 - rexp (-π * t)) := by ring
/-- The theta functional equation in the form we need. -/
lemma evenKernel_eq_of_pos {t : ℝ} (h0 : 0 < t) :
    evenKernel 0 t = t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) := by
  have h := evenKernel_functional_equation 0 t
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  rw [h]
  congr 1
  rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul h0.le]
  norm_num

/-! ### The modified kernel appearing in the Mellin transform -/

lemma f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, ht, not_lt.2 ht.le, Set.indicator_of_notMem]

lemma f_modif_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, h0, h1, not_lt.2 h1.le]
  norm_num

lemma f_modif_one : P.f_modif 1 = 0 := by
  simp [P, WeakFEPair.f_modif]
/-! ### Numerical input: `e ^ π ≥  23` -/

lemma exp_pi_ge_23 : (23 : ℝ) ≤  rexp π := by
  have h1 : (0.7853 : ℝ) < π / 4 := by nlinarith [Real.pi_gt_d4]
  have hp : (0 : ℝ) < π / 4 := by positivity
  have h2 : (2.19 : ℝ) ≤  rexp (π / 4) := by
    have h := Real.sum_le_exp_of_nonneg (x := π / 4) hp.le 6
    simp [Finset.sum_range_succ, Nat.factorial] at h
    nlinarith [h1, pow_pos hp 2, pow_pos hp 3, pow_pos hp 4, pow_pos hp 5]
  have h3 : (rexp (π / 4)) ^ 4 = rexp π := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : (2.19 : ℝ) ^ 4 ≤  (rexp (π / 4)) ^ 4 := by gcongr
  rw [← h3]; nlinarith [h4]

lemma exp_neg_pi_le_23 : rexp (-π) ≤  1 / 23 := by
  have h := exp_pi_ge_23
  have hprod : rexp (-π) * rexp π = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-π), Real.exp_pos π]
/-! ### The theta kernel with the sharper constant `21/10` -/

lemma abs_evenKernel_sub_one_le_of_one_le {t : ℝ} (ht : 1 ≤  t) :
    |evenKernel 0 t - 1| ≤  21 / 10 * rexp (-π * t) := by
  have hexp : rexp (-π * t) ≤  rexp (-π) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  have h23 : rexp (-π * t) ≤  1 / 23 := le_trans hexp exp_neg_pi_le_23
  have hpos : 0 < rexp (-π * t) := Real.exp_pos _
  have hd : (0 : ℝ) < 1 - rexp (-π * t) := by linarith
  refine (abs_evenKernel_zero_sub_one_le (by linarith)).trans ?_
  rw [div_le_iff₀ hd]
  nlinarith

lemma norm_f_modif_le_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖P.f_modif t‖ ≤  21 / 10 * rexp (-π * t) := by
  rw [f_modif_of_one_lt ht,
    show ((evenKernel 0 t : ℝ) : ℂ) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_evenKernel_sub_one_le_of_one_le ht.le

lemma norm_f_modif_le_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ‖P.f_modif t‖ ≤  21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t) := by
  have ht1 : (1 : ℝ) ≤  1 / t := by rw [le_div_iff₀ h0]; linarith
  have hrpow : (0 : ℝ) < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos h0 _
  rw [f_modif_of_lt_one h0 h1,
    show ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
      = ((evenKernel 0 t - t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, evenKernel_eq_of_pos h0,
    show t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) - t ^ (-(1 : ℝ) / 2)
      = t ^ (-(1 : ℝ) / 2) * (evenKernel 0 (1 / t) - 1) from by ring,
    abs_mul, abs_of_pos hrpow, mul_comm (21 / 10 : ℝ), mul_assoc]
  have h := abs_evenKernel_sub_one_le_of_one_le ht1
  rw [show -π * (1 / t) = -π / t by ring] at h
  exact mul_le_mul_of_nonneg_left h hrpow.le

/-! ### The tail integral `J = ∫_1^∞ u^{-1/2} e^{-π u} du` -/

/-- `∫_0^∞ x^k e^{-π x} dx = k! / π^{k+1}`. -/
lemma integral_pow_mul_exp (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x)) = (Nat.factorial k) / π ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := π) (by positivity)
    Real.pi_pos
  have hc : (∫ x in Ioi (0 : ℝ), x ^ ((k : ℝ) + 1 - 1) * rexp (-(π * x)))
      = ∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.rpow_natCast]
    ring_nf
  rw [hc, Real.Gamma_nat_eq_factorial k,
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
  rw [h, div_pow, one_pow]
  field_simp

/-- Translation of an integral over `(1,∞)` to one over `(0,∞)`. -/
lemma integral_Ioi_one_shift (g : ℝ → ℝ) :
    (∫ u in Ioi (1 : ℝ), g u) = ∫ x in Ioi (0 : ℝ), g (x + 1) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_add_right_eq_self (fun x => (Ioi (1 : ℝ)).indicator g x) 1]
  congr 1
  ext x
  by_cases h : (0 : ℝ) < x
  · rw [Set.indicator_of_mem (by simp; linarith : x + 1 ∈ Ioi (1 : ℝ)),
      Set.indicator_of_mem (by simpa using h)]
  · rw [Set.indicator_of_notMem (by simp; linarith [not_lt.1 h] : x + 1 ∉ Ioi (1 : ℝ)),
      Set.indicator_of_notMem (by simpa using h)]

lemma integrableOn_pow_mul_exp (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * rexp (-π * x)) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) 0 Real.pi_pos).mpr (by simpa using hg)
  have hc : IntegrableOn
      (fun x : ℝ => (π ^ k)⁻¹ * (rexp (-(π * x)) * (π * x) ^ ((k : ℝ) + 1 - 1))) (Ioi 0) :=
    hs.const_mul _
  refine hc.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  dsimp only
  rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.mul_rpow Real.pi_pos.le hx0.le,
    Real.rpow_natCast, Real.rpow_natCast]
  have hne : (π : ℝ) ^ k ≠ 0 := by positivity
  field_simp

end ZetaSix

end Height100Module9

/- Source module: KernelTail. -/
section Height100Module10

open Real MeasureTheory Set HurwitzZeta HurwitzKernelBounds

namespace TaoZetaBounds

lemma F_nat_zero_shift (a : ℝ) {t : ℝ} (ht : 0 < t) :
    F_nat 0 a t = exp (-π * a ^ 2 * t) + F_nat 0 (a + 1) t := by
  rw [F_nat, (summable_f_nat 0 a ht).tsum_eq_zero_add]
  simp only [f_nat, Nat.cast_zero, zero_add, pow_zero, one_mul]
  congr 1
  unfold F_nat
  apply tsum_congr
  intro n
  simp only [f_nat, pow_zero, one_mul, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

end TaoZetaBounds

end Height100Module10

/- Source module: PolynomialTail. -/
section Height100Module11

open Real MeasureTheory Set Filter
open scoped Topology

namespace TaoZetaBounds

lemma exp_neg_nat_pi_le (n : ℕ) : exp (-(n : ℝ) * π) ≤  (1 / 23 : ℝ)^n := by
  have he : -(n : ℝ) * π = n * (-π) := by ring
  rw [he, exp_nat_mul]
  exact pow_le_pow_left₀ (exp_nonneg _) ZetaSix.exp_neg_pi_le_23 n

end TaoZetaBounds

end Height100Module11

/- Source module: GeneralThetaTail. -/
section Height100Module12

open Real MeasureTheory Set Filter Finset HurwitzZeta HurwitzKernelBounds

namespace CertifiedZetaQuadrature
open TaoZetaBounds

lemma polynomial_exp_majorant_general (m : ℕ) (A c t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    t ^ m * exp (-c * t) ≤ 
      (A ^ m * exp (-m)) * exp (-(c - m / A) * t) := by
  have hl := log_le_sub_one_of_pos (div_pos ht hA)
  rw [log_div ht.ne' hA.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m : (0:ℝ)≤ m)
  have hle : (m:ℝ) * log t - c * t ≤  m * log A - m - (c - m / A) * t := by
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith
  have et : exp ((m:ℝ) * log t) = t ^ m := by
    rw [exp_nat_mul, exp_log ht]
  have ea : exp ((m:ℝ) * log A) = A ^ m := by
    rw [exp_nat_mul, exp_log hA]
  calc
    t ^ m * exp (-c * t) = exp ((m:ℝ) * log t - c * t) := by
      rw [sub_eq_add_neg, exp_add, et]; congr 1; ring
    _ ≤  exp (m * log A - m - (c - m / A) * t) := exp_le_exp.mpr hle
    _ = (A ^ m * exp (-m)) * exp (-(c - m / A) * t) := by
      rw [sub_eq_add_neg, exp_add, sub_eq_add_neg, exp_add, ea]
      congr 1
      ring

lemma polynomial_exp_tail_general (m : ℕ) (A c : ℝ) (hA : 0 < A) (hd : 0 < c - m / A) :
    IntegrableOn (fun t : ℝ => t ^ m * exp (-c * t)) (Ioi A) ∧
    (∫ t in Ioi A, t ^ m * exp (-c * t)) ≤ 
      A ^ m * exp (-c * A) / (c - m / A) := by
  let d := c - m / A
  have hd0 : 0 < d := hd
  have hg : IntegrableOn
      (fun t : ℝ => (A ^ m * exp (-m)) * exp (-d * t)) (Ioi A) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd0) A).const_mul _
  have hi : IntegrableOn (fun t : ℝ => t ^ m * exp (-c * t)) (Ioi A) := by
    apply hg.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0< t := hA.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact polynomial_exp_majorant_general m A c t hA (hA.trans ht)
  refine ⟨hi, ?_⟩
  have hb := integral_mono_ae hi hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact polynomial_exp_majorant_general m A c t hA (hA.trans ht))
  refine hb.trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hd0)]
  have he : -(m:ℝ) + -d * A = -c * A := by dsimp [d]; field_simp; ring
  calc
    A ^ m * exp (-(m:ℝ)) * (-exp (-d * A) / -d) =
        A ^ m * (exp (-m) * exp (-d * A)) / d := by ring
    _ = A ^ m * exp (-c * A) / d := by rw [← exp_add, he]

lemma kernel_finite_remainder_eq (N : ℕ) {t : ℝ} (ht : 0< t) :
    evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t)) =
      2*F_nat 0 (N+1) t := by
  induction N with
  | zero =>
    have hF : F_int 0 0 t = F_nat 0 0 t + F_nat 0 1 t := by
      simpa only [QuotientAddGroup.mk_zero, sub_zero] using
        F_int_eq_of_mem_Icc 0 (by simp : (0:ℝ) ∈ Set.Icc 0 1) ht
    rw [ZetaSix.evenKernel_zero_eq_F_int ht,hF,F_nat_zero_shift 0 ht]
    simp
    ring
  | succ N ih =>
    rw [sum_range_succ]
    calc
      _ = (evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t))) -
          2*exp (-π*(N+1:ℝ)^2*t) := by ring
      _ = 2*F_nat 0 (N+1) t - 2*exp (-π*(N+1:ℝ)^2*t) := by rw [ih]
      _ = _ := by rw [F_nat_zero_shift (N+1) ht]; push_cast; ring

lemma kernel_finite_remainder_bound (N : ℕ) {t : ℝ} (ht : 1≤ t) :
    |evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t))| ≤ 
      (21/10:ℝ)*exp (-π*(N+1:ℝ)^2*t) := by
  rw [kernel_finite_remainder_eq N (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hb := F_nat_zero_le (a := (N+1:ℝ)) (by positivity) (by linarith : 0< t)
  rw [Real.norm_eq_abs] at hb
  have he : exp (-π*t)≤ 1/23 :=
    (exp_le_exp.mpr (by nlinarith [pi_pos])).trans ZetaSix.exp_neg_pi_le_23
  have hd : 0<1-exp (-π*t) := by linarith
  calc
    2*|F_nat 0 (N+1) t| ≤  2*(exp (-π*(N+1:ℝ)^2*t)/(1-exp (-π*t))) := by gcongr
    _ ≤  _ := by
      rw [← mul_div_assoc, div_le_iff₀ hd]
      nlinarith [exp_pos (-π*(N+1:ℝ)^2*t)]

lemma theta_eight_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (1:ℝ), t^64*exp (-81*π*t)) ≤  1/10^100 := by
  have hb := (polynomial_exp_tail_general 64 1 (81*π) (by norm_num)
    (by nlinarith [pi_gt_three])).2
  have hn : exp (-81*π)≤ (1/23:ℝ)^81 := by simpa using exp_neg_nat_pi_le 81
  calc
    _ ≤  (21/10:ℝ)*(exp (-81*π)/(81*π-64)) := by simpa using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤ 21/10)
    _ ≤  (21/10:ℝ)*((1/23:ℝ)^81/179) := by gcongr; nlinarith [pi_gt_three]
    _ ≤  1/10^100 := by norm_num

lemma large_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (400:ℝ), t^64*exp (-π*t)) ≤  1/10^100 := by
  have hb := (polynomial_exp_tail_general 64 400 π (by norm_num)
    (by nlinarith [pi_gt_three])).2
  norm_num only [Nat.cast_ofNat] at hb
  have hn : exp (-π*400)≤ (1/23:ℝ)^(400:ℕ) := by
    rw [show -π*400=-(400:ℝ)*π by ring]
    exact exp_neg_nat_pi_le 400
  calc
    _ ≤  (21/10:ℝ)*((400:ℝ)^(64:ℕ)*exp (-π*400)/(π-64/400)) := by
      have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤ 21/10)
      convert! hh using 1
      norm_num
    _ ≤  (21/10:ℝ)*((400:ℝ)^(64:ℕ)*(1/23:ℝ)^(400:ℕ)/(71/25)) := by gcongr; nlinarith [pi_gt_three]
    _ ≤  1/10^100 := by
      rw [show (400:ℕ)=200+200 by rfl, pow_add]
      norm_num

end CertifiedZetaQuadrature

end Height100Module12

/- Source module: ExponentialKernelBound. -/
section Height100Module13

open Complex Finset Metric

namespace CertifiedZetaQuadrature

noncomputable def thetaTruncation (z : ℂ) : ℂ :=
  ∑ n ∈ range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

noncomputable def kernelMoment (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * ((8*z)^k/(k.factorial:ℂ)) *
    Complex.exp (I*(τ:ℂ)*z) * thetaTruncation z

end CertifiedZetaQuadrature

end Height100Module13

/- Source module: TwistedCutoff. -/
section Height100Module14

open Real MeasureTheory Set Filter HurwitzZeta
namespace CertifiedZetaQuadrature

noncomputable def phase (τ t : ℝ) : ℂ := Complex.exp (Complex.I*(τ:ℂ)*(log t:ℂ))
noncomputable def twistedRaw (a : ℕ) (τ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (momentWeight a k t*(evenKernel 0 t-1):ℝ)*phase τ t
noncomputable def twistedFinite (a : ℕ) (τ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (2*momentWeight a k t*(∑ n ∈ Finset.range 8, exp (-π*(n+1:ℝ)^2*t)):ℝ)*phase τ t

lemma norm_phase (τ t : ℝ) : ‖phase τ t‖=1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

lemma momentWeight_nonneg (a k : ℕ) {t : ℝ} (ht : 1≤ t) : 0≤ momentWeight a k t := by
  have hl := log_nonneg ht
  unfold momentWeight
  positivity

lemma momentWeight_bound (a k : ℕ) (ha : a≤ 64) {t : ℝ} (ht : 1≤ t) :
    momentWeight a k t≤ t^64 := by
  have ht0 : 0< t := by linarith
  have hl := log_nonneg ht
  have hp := pow_div_factorial_le_exp (a*log t) (by positivity) k
  rw [exp_nat_mul,exp_log ht0] at hp
  have hr : t^(-3/4:ℝ)≤ 1 := rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have hta : t^a≤ t^64 := pow_le_pow_right₀ ht ha
  unfold momentWeight
  rw [mul_div_assoc]
  calc
    _ ≤  t^(-3/4:ℝ)*t^a := by gcongr
    _ ≤  t^a := by nlinarith [pow_nonneg ht0.le a]
    _ ≤  _ := hta

lemma momentWeight_continuousOn (a k : ℕ) : ContinuousOn (momentWeight a k) (Ici 1) := by
  intro t ht
  have ht0 : t≠0 := by linarith [show 1≤ t from ht]
  apply ContinuousAt.continuousWithinAt
  unfold momentWeight
  exact (((continuousAt_id.rpow_const (Or.inl ht0)).mul
    ((continuousAt_const.mul (Real.continuousAt_log ht0)).pow k)).div_const _)

lemma phase_continuousOn (τ : ℝ) : ContinuousOn (phase τ) (Ici 1) := by
  intro t ht
  have ht0 : t≠0 := by linarith [show 1≤ t from ht]
  have hl := Real.continuousAt_log ht0
  apply ContinuousAt.continuousWithinAt
  unfold phase
  fun_prop

lemma twistedRaw_continuousOn (a : ℕ) (τ : ℝ) (k : ℕ) :
    ContinuousOn (twistedRaw a τ k) (Ici 1) := by
  apply ContinuousOn.mul _ (phase_continuousOn τ)
  apply Complex.continuous_ofReal.comp_continuousOn
  apply (momentWeight_continuousOn a k).mul
  exact ((continuousOn_evenKernel 0).mono (fun t ht => by
    change 0< t; linarith [show 1≤ t from ht])).sub continuousOn_const

lemma twistedFinite_continuousOn (a : ℕ) (τ : ℝ) (k : ℕ) :
    ContinuousOn (twistedFinite a τ k) (Ici 1) := by
  apply ContinuousOn.mul _ (phase_continuousOn τ)
  apply Complex.continuous_ofReal.comp_continuousOn
  exact (continuousOn_const.mul (momentWeight_continuousOn a k)).mul (by fun_prop)

lemma norm_twistedRaw_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) {t : ℝ} (ht : 1≤ t) :
    ‖twistedRaw a τ k t‖≤ (21/10:ℝ)*(t^64*exp (-π*t)) := by
  rw [twistedRaw,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg (momentWeight_nonneg a k ht)]
  calc
    _ ≤  t^64*((21/10:ℝ)*exp (-π*t)) := mul_le_mul (momentWeight_bound a k ha ht)
      (ZetaSix.abs_evenKernel_sub_one_le_of_one_le ht) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma norm_twisted_difference_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64)
    {t : ℝ} (ht : 1≤ t) :
    ‖twistedRaw a τ k t-twistedFinite a τ k t‖≤ (21/10:ℝ)*(t^64*exp (-81*π*t)) := by
  have he : twistedRaw a τ k t-twistedFinite a τ k t =
      ((momentWeight a k t*(evenKernel 0 t-1-2*(∑ n ∈ Finset.range 8,
        exp (-π*(n+1:ℝ)^2*t))):ℝ):ℂ)*phase τ t := by
    unfold twistedRaw twistedFinite
    push_cast
    ring
  rw [he,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg (momentWeight_nonneg a k ht)]
  have hb := kernel_finite_remainder_bound 8 ht
  norm_num only [Nat.cast_ofNat] at hb
  have hexp : -π*81*t=-81*π*t := by ring
  rw [hexp] at hb
  calc
    _ ≤  t^64*((21/10:ℝ)*exp (-81*π*t)) := mul_le_mul (momentWeight_bound a k ha ht)
      hb (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma twistedRaw_integrable (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) :
    IntegrableOn (twistedRaw a τ k) (Ioi 1) := by
  have hg := ((ZetaSix.integrableOn_pow_mul_exp 64).mono_set
    (Ioi_subset_Ioi (show (0:ℝ)≤ 1 by norm_num))).const_mul (21/10:ℝ)
  apply hg.mono' (((twistedRaw_continuousOn a τ k).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_twistedRaw_bound a τ k ha ht.le

lemma integral_twisted_difference_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) (B : ℝ) :
    ‖∫ t in Ioc (1:ℝ) B, twistedRaw a τ k t-twistedFinite a τ k t‖ ≤  1/10^100 := by
  have hg : IntegrableOn (fun t : ℝ => (21/10:ℝ)*(t^64*exp (-81*π*t))) (Ioi 1) :=
    by
      simpa only [neg_mul,IntegrableOn] using ((polynomial_exp_tail_general 64 1 (81*π) (by norm_num)
        (by nlinarith [pi_gt_three])).1).const_mul (21/10:ℝ)
  have hb := norm_integral_le_of_norm_le
    (hg.mono_set (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact norm_twisted_difference_bound a τ k ha ht.1.le)
  have hm := setIntegral_mono_set hg
    (Filter.Eventually.of_forall (fun t => by positivity : ∀t:ℝ,0≤ (21/10:ℝ)*(t^64*exp (-81*π*t))))
    (Filter.Eventually.of_forall (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1))
  apply hb.trans (hm.trans _)
  rw [integral_const_mul]
  exact theta_eight_moment_tail

lemma integral_twisted_tail_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64)
    (B : ℝ) (hB : 400≤ B) :
    ‖∫ t in Ioi B, twistedRaw a τ k t‖≤ 1/10^100 := by
  have hg : IntegrableOn (fun t : ℝ => (21/10:ℝ)*(t^64*exp (-π*t))) (Ioi 400) :=
    ((polynomial_exp_tail_general 64 400 π (by norm_num)
      (by nlinarith [pi_gt_three])).1).const_mul _
  have hb := norm_integral_le_of_norm_le (hg.mono_set (Ioi_subset_Ioi hB)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_twistedRaw_bound a τ k ha (by linarith [show B< t from ht]))
  have hm := setIntegral_mono_set hg
    (Filter.Eventually.of_forall (fun t => by positivity : ∀t:ℝ,0≤ (21/10:ℝ)*(t^64*exp (-π*t))))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi hB))
  apply hb.trans (hm.trans _)
  rw [integral_const_mul]
  exact large_moment_tail

lemma twisted_cutoff (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) (B : ℝ) (hB : 400≤ B) :
    ‖(∫ t in Ioi (1:ℝ), twistedRaw a τ k t) -
      ∫ t in Ioc (1:ℝ) B, twistedFinite a τ k t‖≤ 2/10^100 := by
  have h1B : (1:ℝ)≤ B := by linarith
  have hr := twistedRaw_integrable a τ k ha
  have hf : IntegrableOn (twistedFinite a τ k) (Ioc (1:ℝ) B) :=
    (((twistedFinite_continuousOn a τ k).mono
      (Icc_subset_Ici_self : Icc (1:ℝ) B ⊆ Ici 1)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hs := setIntegral_union
    (show Disjoint (Ioc (1:ℝ) B) (Ioi B) from by simp [Set.disjoint_left]) measurableSet_Ioi
    (hr.mono_set Ioc_subset_Ioi_self) (hr.mono_set (Ioi_subset_Ioi h1B))
  rw [Ioc_union_Ioi_eq_Ioi h1B] at hs
  have he : (∫ t in Ioi (1:ℝ), twistedRaw a τ k t) - ∫ t in Ioc (1:ℝ) B, twistedFinite a τ k t =
      (∫ t in Ioc (1:ℝ) B, twistedRaw a τ k t-twistedFinite a τ k t)+
        ∫ t in Ioi B, twistedRaw a τ k t := by
    rw [integral_sub (hr.mono_set Ioc_subset_Ioi_self) hf]
    rw [hs]
    ring
  rw [he]
  have hdiff := integral_twisted_difference_bound a τ k ha B
  have htail := integral_twisted_tail_bound a τ k ha B hB
  exact (norm_add_le _ _).trans (by linarith)

end CertifiedZetaQuadrature

end Height100Module14

/- Source module: GlobalMomentQuadrature. -/
section Height100Module15

open Complex MeasureTheory Metric Set Finset
namespace CertifiedZetaQuadrature

noncomputable def globalKernelMoment (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * ((64*z)^k/(k.factorial:ℂ)) * thetaTruncation z

lemma globalKernelMoment_entire (k : ℕ) : Differentiable ℂ (globalKernelMoment k) := by
  unfold globalKernelMoment thetaTruncation
  fun_prop

end CertifiedZetaQuadrature

end Height100Module15

/- Source module: LogSubstitution. -/
section Height100Module16

open Real MeasureTheory Set Filter Finset
namespace CertifiedZetaQuadrature

noncomputable def transformedMoment (a : ℕ) (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * (((a:ℂ)*z)^k/(k.factorial:ℂ)) *
    Complex.exp (Complex.I*(τ:ℂ)*z) * thetaTruncation z

lemma exp_six_ge_four_hundred : (400:ℝ)≤ exp 6 := by
  have h1 : (2718/1000:ℝ)≤ exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤ 2718/1000) h1 6
  norm_num at hp
  linarith

lemma finite_theta_cast (u : ℝ) :
    ((∑ n ∈ range 8, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ)=thetaTruncation (u:ℂ) := by
  unfold thetaTruncation
  push_cast
  rfl

lemma weight_exp_identity (a k : ℕ) (u : ℝ) :
    exp u*momentWeight a k (exp u)=exp (u/4)*(a*u)^k/(k.factorial:ℝ) := by
  unfold momentWeight
  rw [log_exp,← Real.exp_mul]
  have he : u+u*(-3/4:ℝ)=u/4 := by ring
  calc
    _ = (exp u*exp (u*(-3/4)))*(a*u)^k/(k.factorial:ℝ) := by ring
    _ = _ := by rw [← exp_add,he]

lemma transformedMoment_point (a : ℕ) (τ : ℝ) (k : ℕ) (u : ℝ) :
    exp u • twistedFinite a τ k (exp u)=transformedMoment a τ k (u:ℂ) := by
  have hw := congrArg (fun x : ℝ => (x:ℂ)) (weight_exp_identity a k u)
  push_cast at hw
  rw [Complex.real_smul]
  unfold twistedFinite transformedMoment phase
  rw [log_exp]
  push_cast
  rw [← finite_theta_cast u]
  calc
    _ = 2*((exp u:ℂ)*(momentWeight a k (exp u):ℂ))*
        Complex.exp (Complex.I*(τ:ℂ)*(u:ℂ))*
        ((∑ n ∈ range 8, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ) := by push_cast; ring
    _ = _ := by rw [Complex.ofReal_exp,hw]; push_cast; ring

lemma transformedMoment_integral (a : ℕ) (τ : ℝ) (k : ℕ) :
    (∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)) =
      ∫ t in Ioc (1:ℝ) (exp 6), twistedFinite a τ k t := by
  have he := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a:=0) (b:=6) (f:=exp) (f':=exp) (g:=twistedFinite a τ k)
    Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => (Real.exp_pos x).le)
  simp only [Function.comp_apply,exp_zero] at he
  rw [intervalIntegral.integral_of_le (by linarith [exp_six_ge_four_hundred] : (1:ℝ)≤ exp 6)] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro u _
  exact (transformedMoment_point a τ k u).symm

lemma twisted_cutoff_transformed (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) :
    ‖(∫ t in Ioi (1:ℝ), twistedRaw a τ k t) -
      ∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)‖ ≤  2/10^100 := by
  rw [transformedMoment_integral]
  exact twisted_cutoff a τ k ha (exp 6) exp_six_ge_four_hundred

lemma transformedMoment_sixtyfour (k : ℕ) (z : ℂ) :
    transformedMoment 64 0 k z=globalKernelMoment k z := by
  simp [transformedMoment,globalKernelMoment]

end CertifiedZetaQuadrature

end Height100Module16

/- Source module: WideStrip256. -/
section Height100Module17

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256
open ZetaSix

noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤  1 then 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t))

lemma integrableOn_outer :
    IntegrableOn (fun t : ℝ => t ^ (128 : ℝ) * rexp (-π * t)) (Ioi 1) := by
  simpa only [Real.rpow_ofNat] using
    (ZetaSix.integrableOn_pow_mul_exp 128).mono_set (Ioi_subset_Ioi zero_le_one)

lemma outer_le :
    (∫ t in Ioi (1 : ℝ), t ^ (128 : ℝ) * rexp (-π * t)) ≤  ((10^155) : ℝ) / (21 / 10) := by
  have h := MeasureTheory.setIntegral_mono_set
    (ZetaSix.integrableOn_pow_mul_exp 128)
    (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
      ∀ x : ℝ, 0 ≤  x ^ 128 * rexp (-π * x)))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num)))
  simp only [Real.rpow_ofNat] at *
  rw [ZetaSix.integral_pow_mul_exp] at h
  have hp : (3 : ℝ) ^ 129 ≤  π ^ 129 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 129
  have hpi : (0 : ℝ) < π ^ 129 := by positivity
  have hb : (Nat.factorial 128 : ℝ) / π ^ 129 ≤  (10^155) / (21 / 10) := by
    rw [div_le_iff₀ hpi]
    norm_num [Nat.factorial] at *
    nlinarith
  exact h.trans hb

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (128 : ℝ) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_outer.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-130 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (128 : ℝ) = x ^ (-128 : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ (-128 : ℝ) = x ^ (-130 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-130 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-130 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-130 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-130 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_outer.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤  (2*10^155) := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := outer_le
  linarith

lemma norm_integrand_le {s : ℂ} (h0 : -256 ≤  s.re) (h1 : s.re ≤  257) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤  maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 21 / 10 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤  t ^ (-130 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-130 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-130 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤  t ^ (128 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (128 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤  (10^155)`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -256 ≤  s.re) (h1 : s.re ≤  257) :
    ‖completedRiemannZeta₀ s‖ ≤  (10^155) := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤  ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

end TaoZetaWide256

end Height100Module17

/- Source module: GlobalTaylorCertificate. -/
section Height100Module18

open Complex Finset Metric
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

lemma norm_iteratedDeriv_completedZeta (n : ℕ) :
    ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖ ≤ 
      n.factorial * (10^155) / (256 : ℝ) ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    differentiable_completedZeta₀.diffContOnCl
  intro z hz
  have habs : |z.re - 1 / 2| ≤  (256 : ℝ) := by
    have h := Complex.abs_re_le_norm (z - (1 / 2 : ℂ))
    rw [mem_sphere_iff_norm.mp hz] at h
    simpa using h
  apply TaoZetaWide256.norm_completedRiemannZeta₀_le <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2]

noncomputable def taylorTerm (z : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ • (z - 1 / 2) ^ n •
    iteratedDeriv n completedRiemannZeta₀ (1 / 2)

lemma norm_taylorTerm_le (z : ℂ) (n : ℕ) :
    ‖taylorTerm z n‖ ≤  (10^155) * (‖z - 1 / 2‖ / 256) ^ n := by
  have h := norm_iteratedDeriv_completedZeta n
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  unfold taylorTerm
  simp only [norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖) ≤ 
      (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        (n.factorial * (10^155) / (256 : ℝ) ^ n)) := by gcongr
    _ = (10^155) * (‖z - 1 / 2‖ / 256) ^ n := by
      rw [div_pow]
      field_simp

/-- A uniform certified truncation bound, with no assumptions about computed coefficients. -/
lemma norm_taylor_remainder_le (z : ℂ) (hz : ‖z - 1 / 2‖ < 256) (N : ℕ) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range N, taylorTerm z n‖ ≤ 
      (10^155) * (‖z - 1 / 2‖ / 256) ^ N / (1 - ‖z - 1 / 2‖ / 256) := by
  let q : ℝ := ‖z - 1 / 2‖ / 256
  have hq0 : 0 ≤  q := by positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hs : HasSum (taylorTerm z) (completedRiemannZeta₀ z) :=
    Complex.hasSum_taylorSeries_of_entire differentiable_completedZeta₀ (1 / 2) z
  have htail : completedRiemannZeta₀ z - ∑ n ∈ range N, taylorTerm z n =
      ∑' n : ℕ, taylorTerm z (n + N) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using h.symm
  rw [htail]
  have hgeo : HasSum (fun n : ℕ => ((10^155) * q ^ N) * q ^ n)
      (((10^155) * q ^ N) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((10^155) * q ^ N)
  have hbound := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    calc ‖taylorTerm z (n + N)‖ ≤  (10^155) * q ^ (n + N) := norm_taylorTerm_le z (n + N)
      _ = ((10^155) * q ^ N) * q ^ n := by rw [pow_add]; ring)
  simpa only [q, div_eq_mul_inv] using hbound

lemma norm_taylor_remainder_512 (z : ℂ) (hz : ‖z - 1 / 2‖ ≤  104) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range 512, taylorTerm z n‖ ≤  1 / 10 ^ 45 := by
  have hr := norm_taylor_remainder_le z (by linarith) 512
  have hq : ‖z - 1 / 2‖ / 256 ≤  (13 / 32 : ℝ) := by linarith
  have hq0 : 0 ≤  ‖z - 1 / 2‖ / 256 := by positivity
  apply hr.trans
  calc
    (10^155) * (‖z - 1 / 2‖ / 256) ^ 512 / (1 - ‖z - 1 / 2‖ / 256) ≤ 
        (10^155) * (13 / 32 : ℝ) ^ 512 / (1 - 13 / 32) := by
      gcongr
    _ ≤  1 / 10 ^ 45 := by norm_num

end TaoZetaGlobal

end Height100Module18

/- Source module: MellinMoments. -/
section Height100Module19

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
set_option autoImplicit false

namespace TaoZetaCertificate

noncomputable def logKernel : ℕ → ℝ → ℂ
  | 0 => ZetaSix.P.f_modif
  | n + 1 => fun t => Real.log t • logKernel n t

lemma logKernel_eq (n : ℕ) (t : ℝ) :
    logKernel n t = (Real.log t) ^ n • ZetaSix.P.f_modif t := by
  induction n with
  | zero => simp [logKernel]
  | succ n ih => simp only [logKernel, ih, pow_succ]; rw [smul_smul]; congr 1; ring

lemma logKernel_locallyIntegrable (n : ℕ) :
    LocallyIntegrableOn (logKernel n) (Ioi 0) := by
  induction n with
  | zero => exact ZetaSix.P.hf_modif_int
  | succ n ih =>
    exact MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed ih
      (fun t ht => (Real.continuousAt_log (ne_of_gt ht)).continuousWithinAt)

lemma logKernel_top (n : ℕ) (r : ℝ) :
    logKernel n =O[atTop] (fun t : ℝ => t ^ r) := by
  induction n generalizing r with
  | zero =>
    exact ZetaSix.P.isStrongFEPair_toStrongFEPair.hf_top r
  | succ n ih =>
    have h := isBigO_rpow_top_log_smul (a := -(r - 1)) (b := -r) (by linarith)
      (by simpa only [neg_neg] using ih (r - 1))
    simpa only [neg_neg, logKernel] using h

lemma logKernel_zero (n : ℕ) (r : ℝ) :
    logKernel n =O[𝓝[>] 0] (fun t : ℝ => t ^ r) := by
  induction n generalizing r with
  | zero =>
    exact ZetaSix.P.isStrongFEPair_toStrongFEPair.hf_zero r
  | succ n ih =>
    have h := isBigO_rpow_zero_log_smul (a := -(r + 1)) (b := -r) (by linarith)
      (by simpa only [neg_neg] using ih (r + 1))
    simpa only [neg_neg, logKernel] using h

lemma logKernel_mellin_hasDerivAt (n : ℕ) (s : ℂ) :
    HasDerivAt (mellin (logKernel n)) (mellin (logKernel (n + 1)) s) s := by
  exact (mellin_hasDerivAt_of_isBigO_rpow (logKernel_locallyIntegrable n)
    (logKernel_top n (-(s.re + 1))) (by linarith)
    (logKernel_zero n (-(s.re - 1))) (by linarith)).2

lemma logKernel_mellin_convergent (n : ℕ) (s : ℂ) :
    MellinConvergent (logKernel n) s := by
  exact mellinConvergent_of_isBigO_rpow (logKernel_locallyIntegrable n)
    (logKernel_top n (-(s.re + 1))) (by linarith)
    (logKernel_zero n (-(s.re - 1))) (by linarith)

lemma iteratedDeriv_mellin_kernel (n : ℕ) :
    iteratedDeriv n (mellin ZetaSix.P.f_modif) = mellin (logKernel n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun s => (logKernel_mellin_hasDerivAt n s).deriv

lemma completedZeta_derivative_moment (n : ℕ) (s : ℂ) :
    iteratedDeriv n completedRiemannZeta₀ s =
      mellin (logKernel n) (s / 2) / (2 : ℂ) ^ (n + 1) := by
  have hf : Differentiable ℂ (mellin ZetaSix.P.f_modif) :=
    fun s => (logKernel_mellin_hasDerivAt 0 s).differentiableAt
  have he : completedRiemannZeta₀ =
      (fun s : ℂ => mellin ZetaSix.P.f_modif ((1 / 2 : ℂ) * s) / 2) := by
    ext z
    change mellin ZetaSix.P.f_modif (z / 2) / 2 = _
    congr 2
    ring
  rw [he, iteratedDeriv_div_const]
  rw [iteratedDeriv_comp_const_mul hf.contDiff, iteratedDeriv_mellin_kernel]
  have hs : (1 / 2 : ℂ) * s = s / 2 := by ring
  dsimp only
  rw [hs]
  rw [pow_succ, div_pow, one_pow]
  field_simp

end TaoZetaCertificate

end Height100Module19

/- Source module: FoldedMoments. -/
section Height100Module20

open Complex MeasureTheory Set HurwitzZeta
set_option autoImplicit false

namespace TaoZetaCertificate

noncomputable def momentIntegrand (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • logKernel (2 * n) t

noncomputable def outerIntegrand (n : ℕ) (t : ℝ) : ℂ :=
  ((t ^ (-3 / 4 : ℝ) * Real.log t ^ (2 * n) * (evenKernel 0 t - 1) : ℝ) : ℂ)

lemma momentIntegrand_outer (n : ℕ) {t : ℝ} (ht : 1 < t) :
    momentIntegrand n t = outerIntegrand n t := by
  have ht0 : 0 ≤  t := by linarith
  unfold momentIntegrand outerIntegrand
  rw [logKernel_eq, ZetaSix.f_modif_of_one_lt ht]
  have he : (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) := by norm_num
  rw [he, ← Complex.ofReal_cpow ht0]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

lemma momentIntegrand_inner (n : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    momentIntegrand n t =
      ((t ^ (-5 / 4 : ℝ) * Real.log t ^ (2 * n) *
        (evenKernel 0 (1 / t) - 1) : ℝ) : ℂ) := by
  unfold momentIntegrand
  rw [logKernel_eq, ZetaSix.f_modif_of_lt_one ht ht1, ZetaSix.evenKernel_eq_of_pos ht]
  have he : (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) := by norm_num
  rw [he, ← Complex.ofReal_cpow ht.le]
  have hpow : t ^ (-5 / 4 : ℝ) = t ^ (-3 / 4 : ℝ) * t ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add ht]
    norm_num
  rw [hpow]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private noncomputable def outerIndicator (n : ℕ) : ℝ → ℂ :=
  (Ioi 1).indicator (outerIntegrand n)

private lemma integral_outerIndicator (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), outerIndicator n t) = ∫ t in Ioi 1, outerIntegrand n t := by
  rw [outerIndicator, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi]
  norm_num

private lemma reciprocal_integrand (n : ℕ) (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • outerIndicator n (t ^ (-1 : ℝ)) =
      (Ioo (0 : ℝ) 1).indicator (momentIntegrand n) t := by
  have ht0 : 0 < t := ht
  rw [Real.rpow_neg_one]
  rcases lt_or_ge t 1 with h | h
  · have hinv : 1 < t⁻¹ := by rw [lt_inv_comm₀ (by norm_num) ht0]; simpa using h
    rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, h⟩),
      outerIndicator, indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hinv), momentIntegrand_inner n ht0 h]
    unfold outerIntegrand
    have hpow : (t⁻¹) ^ (-3 / 4 : ℝ) = t ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_neg_one t, ← Real.rpow_mul ht0.le]
      norm_num
    have hlog : Real.log (t⁻¹) ^ (2 * n) = Real.log t ^ (2 * n) := by
      rw [Real.log_inv, Even.neg_pow (even_two_mul n)]
    rw [hpow, hlog]
    have he : t ^ (-2 : ℝ) * t ^ (3 / 4 : ℝ) = t ^ (-(5 / 4) : ℝ) := by
      rw [← Real.rpow_add ht0]
      norm_num
    norm_num only [abs_neg, abs_one, one_mul]
    rw [Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, he]
    simp only [one_div]
  · have hinv : t⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [indicator_of_notMem (by simp; intro _; exact h), outerIndicator,
      indicator_of_notMem (by simpa using not_lt.mpr hinv)]
    simp

lemma integral_moment_inner (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, momentIntegrand n t) = ∫ t in Ioi 1, outerIntegrand n t := by
  have h := integral_comp_rpow_Ioi (outerIndicator n) (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_outerIndicator, setIntegral_congr_fun measurableSet_Ioi (reciprocal_integrand n)] at h
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by ext t; simp; tauto] at h
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h

lemma mellin_even_moment_folded (n : ℕ) :
    mellin (logKernel (2 * n)) (1 / 4) = 2 * ∫ t in Ioi 1, outerIntegrand n t := by
  have hi : IntegrableOn (momentIntegrand n) (Ioi (0 : ℝ)) :=
    logKernel_mellin_convergent (2 * n) (1 / 4)
  have hi0 := hi.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)
  have hi1 := hi.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num))
  change (∫ t in Ioi (0 : ℝ), momentIntegrand n t) = _
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  rw [setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi hi0 hi1,
    integral_moment_inner n,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => momentIntegrand_outer n ht)]
  ring

lemma even_derivative_moment_folded (n : ℕ) :
    iteratedDeriv (2 * n) completedRiemannZeta₀ (1 / 2) =
      (∫ t in Ioi 1, outerIntegrand n t) / (2 : ℂ) ^ (2 * n) := by
  rw [completedZeta_derivative_moment]
  have hc : (1 / 2 : ℂ) / 2 = 1 / 4 := by norm_num
  rw [hc, mellin_even_moment_folded, pow_succ]
  field_simp

end TaoZetaCertificate

end Height100Module20

/- Source module: Symmetry. -/
section Height100Module21

open Complex MeasureTheory Set
open scoped ComplexConjugate
set_option autoImplicit false

namespace TaoZetaCertificate

lemma conj_kernel {t : ℝ} (ht : 0 < t) :
    conj (ZetaSix.P.f_modif t) = ZetaSix.P.f_modif t := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · rw [ZetaSix.f_modif_of_lt_one ht h]
    simp
  · rw [ZetaSix.f_modif_one]
    simp
  · rw [ZetaSix.f_modif_of_one_lt h]
    simp

lemma completedZeta_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  change mellin ZetaSix.P.f_modif (conj s / 2) / 2 =
    conj (mellin ZetaSix.P.f_modif (s / 2) / 2)
  rw [map_div₀, map_ofNat]
  congr 1
  rw [mellin, mellin, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  have htarg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact ne_of_lt Real.pi_pos
  have he : conj s / 2 - 1 = conj (s / 2 - 1) := by
    simp only [map_sub, map_div₀, map_one, map_ofNat]
  dsimp only
  rw [he, Complex.cpow_conj _ _ htarg]
  simp only [smul_eq_mul, map_mul, conj_ofReal, conj_kernel ht0]

lemma odd_taylor_derivative_zero (n : ℕ) :
    iteratedDeriv (2 * n + 1) completedRiemannZeta₀ (1 / 2) = 0 := by
  have hf : (fun z => completedRiemannZeta₀ (1 - z)) = completedRiemannZeta₀ :=
    funext completedRiemannZeta₀_one_sub
  have h := congrFun (congrArg (iteratedDeriv (2 * n + 1)) hf) (1 / 2)
  rw [iteratedDeriv_comp_const_sub] at h
  norm_num [pow_add, pow_mul] at h
  linear_combination -h / 2

end TaoZetaCertificate

end Height100Module21

/- Source module: ComplexTaylorBounds. -/
section Height100Module22

open Complex Finset Metric Filter
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature

noncomputable def polynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n*(z-c)^n
noncomputable def remainder (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  f z-polynomial f c N z

lemma series_sum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) :
    HasSum (fun n : ℕ => coefficient f c n*(z-c)^n) (f z) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf c z
  convert! h using 1
  ext n
  simp only [coefficient,smul_eq_mul]
  ring

lemma remainder_eq_tsum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) (N : ℕ) :
    remainder f c N z = ∑' n : ℕ, coefficient f c (n+N)*(z-c)^(n+N) := by
  have hs := series_sum f hf c z
  have h := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at h
  unfold remainder polynomial
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using h.symm

lemma remainder_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M r : ℝ) (hR : 0< R) (hM : 0≤ M) (hr : 0≤ r) (hrR : r< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) (z : ℂ) (hz : ‖z-c‖≤ r) :
    ‖remainder f c N z‖≤ M*(r/R)^N/(1-r/R) := by
  have hq0 : 0≤ r/R := div_nonneg hr hR.le
  have hq1 : r/R<1 := (div_lt_one hR).mpr hrR
  rw [remainder_eq_tsum f hf c z N]
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M*(r/R)^N)
  have hterms : ∀ n : ℕ, ‖coefficient f c (n+N)*(z-c)^(n+N)‖ ≤  (M*(r/R)^N)*(r/R)^n := by
    intro n
    rw [norm_mul,norm_pow]
    calc
      _ ≤  (M/R^(n+N))*r^(n+N) := by
        gcongr
        exact coefficient_bound f hf c R M hR hb (n+N)
      _ = _ := by rw [div_pow,div_pow,pow_add,pow_add]; ring
  simpa only [div_eq_mul_inv] using tsum_of_norm_bounded hgeo hterms

lemma coefficient_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z-g z) c n = coefficient f c n-coefficient g c n := by
  unfold coefficient
  change iteratedDeriv n (f-g) c/(n.factorial:ℂ)=_
  rw [iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt,sub_div]

/-- Uniform global approximation on one circle transfers to every local Taylor coefficient. -/
lemma coefficient_error (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (R δ : ℝ) (hR : 0< R) (hb : ∀ z ∈ sphere c R, ‖f z-g z‖≤ δ) (n : ℕ) :
    ‖coefficient f c n-coefficient g c n‖≤ δ/R^n := by
  rw [← coefficient_sub f g hf hg]
  exact coefficient_bound _ (hf.sub hg) c R δ hR hb n

end CertifiedComplexTaylor

end Height100Module22

/- Source module: WideStrip. -/
section Height100Module23

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false

namespace TaoZetaWide
open ZetaSix

noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤  1 then 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t))

lemma integrableOn_outer :
    IntegrableOn (fun t : ℝ => t ^ (12 : ℝ) * rexp (-π * t)) (Ioi 1) := by
  simpa only [Real.rpow_ofNat] using
    (ZetaSix.integrableOn_pow_mul_exp 12).mono_set (Ioi_subset_Ioi zero_le_one)

lemma outer_le :
    (∫ t in Ioi (1 : ℝ), t ^ (12 : ℝ) * rexp (-π * t)) ≤  (640 : ℝ) / (21 / 10) := by
  have h := MeasureTheory.setIntegral_mono_set
    (ZetaSix.integrableOn_pow_mul_exp 12)
    (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
      ∀ x : ℝ, 0 ≤  x ^ 12 * rexp (-π * x)))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num)))
  simp only [Real.rpow_ofNat] at *
  rw [ZetaSix.integral_pow_mul_exp] at h
  have hp : (3 : ℝ) ^ 13 ≤  π ^ 13 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 13
  have hpi : (0 : ℝ) < π ^ 13 := by positivity
  have hb : (Nat.factorial 12 : ℝ) / π ^ 13 ≤  640 / (21 / 10) := by
    rw [div_le_iff₀ hpi]
    norm_num [Nat.factorial] at *
    nlinarith
  exact h.trans hb

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (12 : ℝ) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_outer.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-14 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (12 : ℝ) = x ^ (-12 : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ (-12 : ℝ) = x ^ (-14 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-14 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-14 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-14 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-14 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_outer.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤  1280 := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := outer_le
  linarith

lemma norm_integrand_le {s : ℂ} (h0 : -24 ≤  s.re) (h1 : s.re ≤  25) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤  maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 21 / 10 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤  t ^ (-14 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-14 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-14 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤  t ^ (12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (12 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤  640`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -24 ≤  s.re) (h1 : s.re ≤  25) :
    ‖completedRiemannZeta₀ s‖ ≤  640 := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤  ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

end TaoZetaWide

end Height100Module23

/- Source module: LocalXiBounds. -/
section Height100Module24

open Complex Metric TaoZetaCertificate
namespace CertifiedLocalXi

noncomputable def xi (s : ℂ) : ℂ :=
  1/2+s*(s-1)/2*completedRiemannZeta₀ s
noncomputable def center (T : ℝ) : ℂ := 1/2+(T:ℂ)*I

lemma xi_entire : Differentiable ℂ xi := by
  unfold xi
  have hΛ := differentiable_completedZeta₀
  fun_prop

lemma center_norm_bound (T : ℝ) (hT : |T|≤ 100) : ‖center T‖≤ 101 := by
  have h := Complex.norm_le_abs_re_add_abs_im (center T)
  norm_num [center] at h
  unfold center
  linarith

lemma center_sub_one_norm_bound (T : ℝ) (hT : |T|≤ 100) : ‖center T-1‖≤ 101 := by
  have h := Complex.norm_le_abs_re_add_abs_im (center T-1)
  norm_num [center] at h
  unfold center
  linarith

lemma xi_circle_bound (T : ℝ) (hT : |T|≤ 100) (z : ℂ) (hz : z ∈ sphere (center T) 24) :
    ‖xi z‖≤ 6000000 := by
  have hzdist : ‖z-center T‖=24 := mem_sphere_iff_norm.mp hz
  have hre : |z.re-1/2|≤ 24 := by
    have h := Complex.abs_re_le_norm (z-center T)
    rw [hzdist] at h
    simpa [center] using h
  have hΛ := TaoZetaWide.norm_completedRiemannZeta₀_le (s:=z)
    (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2])
  have hz0 : ‖z‖≤ 125 := by
    have h := norm_add_le (z-center T) (center T)
    rw [sub_add_cancel,hzdist] at h
    linarith [center_norm_bound T hT]
  have hz1 : ‖z-1‖≤ 125 := by
    have h := norm_add_le (z-center T) (center T-1)
    rw [sub_add_sub_cancel,hzdist] at h
    linarith [center_sub_one_norm_bound T hT]
  unfold xi
  calc
    _ ≤  ‖(1/2:ℂ)‖+‖z*(z-1)/2*completedRiemannZeta₀ z‖ := norm_add_le _ _
    _ = 1/2+‖z‖*‖z-1‖/2*‖completedRiemannZeta₀ z‖ := by
      simp only [norm_mul,norm_div]
      norm_num
    _ ≤  1/2+125*125/2*(640:ℝ) := by gcongr
    _ ≤  _ := by norm_num

lemma local_tail_norm (T : ℝ) (hT : |T|≤ 100) (z : ℂ) (hz : ‖z-center T‖≤ 1) :
    ‖CertifiedComplexTaylor.remainder xi (center T) 32 z‖≤ 1/10^36 := by
  have h := CertifiedComplexTaylor.remainder_bound xi xi_entire (center T) 24 6000000 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (xi_circle_bound T hT) 32 z hz
  apply h.trans
  norm_num

end CertifiedLocalXi

end Height100Module24

/- Source module: GlobalMomentBridge. -/
section Height100Module25

open Complex MeasureTheory Set Finset
namespace CertifiedGlobalMoments
open CertifiedZetaQuadrature TaoZetaCertificate

noncomputable def scaledVariable (z : ℂ) : ℂ := (z-1/2)/128
noncomputable def polynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ range 256, (b j:ℂ)*(scaledVariable z)^(2*j)
noncomputable def xiPolynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  1/2+z*(z-1)/2*polynomial b z

lemma moment_complex (j : ℕ) :
    (moment j:ℂ)=∫ t in Ioi (1:ℝ), twistedRaw 64 0 (2*j) t := by
  unfold moment twistedRaw
  simp only [phase,ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one]
  exact (integral_complex_ofReal).symm

lemma moment_scaled_integral (j : ℕ) :
    (moment j:ℂ)=(64:ℂ)^(2*j)/((2*j).factorial:ℂ)*∫ t in Ioi (1:ℝ), outerIntegrand j t := by
  unfold moment outerIntegrand
  rw [← integral_complex_ofReal,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  unfold momentWeight
  push_cast
  rw [mul_pow]
  ring

lemma even_term (z : ℂ) (j : ℕ) :
    TaoZetaGlobal.taylorTerm z (2*j)=(moment j:ℂ)*(scaledVariable z)^(2*j) := by
  rw [TaoZetaGlobal.taylorTerm,even_derivative_moment_folded,moment_scaled_integral]
  simp only [smul_eq_mul,scaledVariable,div_pow]
  rw [show (128:ℂ)=64*2 by norm_num,mul_pow]
  have hf : ((2*j).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*j)
  field_simp

lemma odd_term (z : ℂ) (j : ℕ) : TaoZetaGlobal.taylorTerm z (2*j+1)=0 := by
  unfold TaoZetaGlobal.taylorTerm
  rw [odd_taylor_derivative_zero]
  simp

lemma sum_even_odd (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range (2*N), f n)=∑ j ∈ range N, (f (2*j)+f (2*j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega]
    simp only [sum_range_succ,ih]
    ring

lemma taylor_sum_eq (z : ℂ) :
    (∑ n ∈ range 512, TaoZetaGlobal.taylorTerm z n)=polynomial moment z := by
  rw [show 512=2*256 by norm_num,sum_even_odd]
  simp_rw [even_term,odd_term,add_zero]
  rfl

lemma polynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (polynomial b) := by
  unfold polynomial scaledVariable
  fun_prop

lemma xiPolynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (xiPolynomial b) := by
  have h := polynomial_entire b
  unfold xiPolynomial
  fun_prop

lemma scaledVariable_norm (z : ℂ) (hz : ‖z-1/2‖≤ 104) : ‖scaledVariable z‖≤ 13/16 := by
  rw [scaledVariable,norm_div]
  norm_num
  linarith

lemma polynomial_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<256, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖polynomial moment z-polynomial b z‖≤ 3*ε := by
  have hv := scaledVariable_norm z hz
  have hgeo := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤ 169/256) (by norm_num : (169/256:ℝ)<1)
  have hs := sum_le_hasSum (range 256) (fun n _ => pow_nonneg (by norm_num : (0:ℝ)≤ 169/256) n) hgeo
  have he : polynomial moment z-polynomial b z =
      ∑ j ∈ range 256, ((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j) := by
    unfold polynomial
    simp_rw [ofReal_sub,sub_mul,sum_sub_distrib]
  rw [he]
  calc
    _ ≤  ∑ j ∈ range 256, ‖((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j)‖ := norm_sum_le _ _
    _ ≤  ε*∑ j ∈ range 256, (169/256:ℝ)^j := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
      have hp : ‖scaledVariable z‖^(2*j)≤ (169/256:ℝ)^j := by
        calc
          _ ≤  (13/16:ℝ)^(2*j) := pow_le_pow_left₀ (norm_nonneg _) hv _
          _ = _ := by rw [pow_mul]; norm_num
      exact mul_le_mul (hb j (mem_range.mp hj)) hp (by positivity) hε
    _ ≤  ε*(1-(169/256:ℝ))⁻¹ := mul_le_mul_of_nonneg_left hs hε
    _ ≤  3*ε := by norm_num; linarith

lemma completedZeta_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<256, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖completedRiemannZeta₀ z-polynomial b z‖≤ 1/10^45+3*ε := by
  have ht := TaoZetaGlobal.norm_taylor_remainder_512 z hz
  rw [taylor_sum_eq] at ht
  have hp := polynomial_error b ε hε hb z hz
  have he : completedRiemannZeta₀ z-polynomial b z =
      (completedRiemannZeta₀ z-polynomial moment z)+(polynomial moment z-polynomial b z) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ht hp)

lemma xi_error (b : ℕ → ℝ)
    (hb : ∀ j<256, |moment j-b j|≤ 1/10^46) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ 1/10^41 := by
  have h0 : ‖z‖≤ 105 := by
    have h := norm_add_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [sub_add_cancel] at h
    norm_num at h
    linarith
  have h1 : ‖z-1‖≤ 105 := by
    have h := norm_sub_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [show z-(1/2:ℂ)-1/2=z-1 by ring] at h
    norm_num at h
    linarith
  have hp : ‖z*(z-1)/2‖≤ 6000 := by
    rw [norm_div,norm_mul]
    norm_num
    nlinarith [norm_nonneg z,norm_nonneg (z-1),mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  have he : CertifiedLocalXi.xi z-xiPolynomial b z=
      (z*(z-1)/2)*(completedRiemannZeta₀ z-polynomial b z) := by
    unfold CertifiedLocalXi.xi xiPolynomial
    ring
  rw [he,norm_mul]
  have hc := completedZeta_error b (1/10^46) (by positivity) hb z hz
  calc
    _ ≤  6000*((1/10^45)+3*(1/10^46:ℝ)) := mul_le_mul hp hc (norm_nonneg _) (by norm_num)
    _ ≤  _ := by norm_num

lemma local_coefficient_error (b : ℕ → ℝ)
    (hb : ∀ j<256, |moment j-b j|≤ 1/10^46) (T : ℝ) (hT : |T|≤ 100) (n : ℕ) :
    ‖CertifiedTaylorQuadrature.coefficient CertifiedLocalXi.xi (CertifiedLocalXi.center T) n-
      CertifiedTaylorQuadrature.coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n‖≤ 1/10^41 := by
  have hs : ∀ z ∈ Metric.sphere (CertifiedLocalXi.center T) (1:ℝ),
      ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ 1/10^41 := by
    intro z hz
    apply xi_error b hb
    have h := norm_add_le (z-CertifiedLocalXi.center T) (CertifiedLocalXi.center T-(1/2:ℂ))
    rw [sub_add_sub_cancel,mem_sphere_iff_norm.mp hz] at h
    have hc : ‖CertifiedLocalXi.center T-(1/2:ℂ)‖=|T| := by
      simp [CertifiedLocalXi.center,Real.norm_eq_abs]
    rw [hc] at h
    linarith
  have h := CertifiedComplexTaylor.coefficient_error CertifiedLocalXi.xi (xiPolynomial b)
    CertifiedLocalXi.xi_entire (xiPolynomial_entire b) (CertifiedLocalXi.center T) 1 (1/10^41)
    (by norm_num) hs n
  simpa using h

end CertifiedGlobalMoments

end Height100Module25

/- Source module: EvenPolynomialRecurrence. -/
section Height100Module26

open Complex Finset
namespace CertifiedEvenPolynomial

lemma recurrence_eval (E : ℕ → ℂ) (H : ℂ) (N : ℕ) (hE : E N=0) (z : ℂ) :
    (∑ j ∈ range (N+1),
      ((if j=0 then H else 0)-E j-(if j=0 then 0 else 4*E (j-1)))*z^(2*j)) =
      H-∑ j ∈ range N, E j*(z^(2*j)+4*z^(2*j+2)) := by
  have hconst : (∑ j ∈ range (N+1), (if j=0 then H else 0)*z^(2*j))=H := by
    rw [sum_range_succ']
    simp
  have hmain : (∑ j ∈ range (N+1), E j*z^(2*j))=∑ j ∈ range N, E j*z^(2*j) := by
    rw [sum_range_succ,hE,zero_mul,add_zero]
  have hshift : (∑ j ∈ range (N+1), (if j=0 then 0 else 4*E (j-1))*z^(2*j))=
      ∑ j ∈ range N, 4*E j*z^(2*j+2) := by
    rw [sum_range_succ']
    simp [Nat.mul_add]
  simp_rw [sub_mul]
  rw [sum_sub_distrib,sum_sub_distrib,hconst,hmain,hshift]
  rw [sub_sub,←sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  ring

lemma dense_even_eval (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (∑ m ∈ range (2*N+1), (if m%2=0 then a (m/2) else 0)*z^m)=
      ∑ j ∈ range (N+1), a j*z^(2*j) := by
  have he := CertifiedGlobalMoments.sum_even_odd
    (fun m => (if m%2=0 then a (m/2) else 0)*z^m) (N+1)
  have hlen : 2*(N+1)=(2*N+1)+1 := by omega
  rw [hlen,sum_range_succ] at he
  simpa using he

end CertifiedEvenPolynomial

end Height100Module26

/- Source module: CauchyStability. -/
section Height100Module27

open Complex Metric Set
namespace CertifiedLocalXi

lemma deriv_bound_from_unit_ball (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (δ : ℝ)
    (hb : ∀ z, ‖z-c‖≤ 1 → ‖f z‖≤ δ) (z : ℂ) (hz : ‖z-c‖≤ 3/4) :
    ‖deriv f z‖≤ 4*δ := by
  have hcircle : ∀ w ∈ sphere z (1/4:ℝ), ‖f w‖≤ δ := by
    intro w hw
    apply hb
    calc
      ‖w-c‖ = ‖(w-z)+(z-c)‖ := by congr 1; ring
      _ ≤  ‖w-z‖+‖z-c‖ := norm_add_le _ _
      _ ≤  1 := by rw [mem_sphere_iff_norm.mp hw]; linarith
  have h := CertifiedTaylorQuadrature.coefficient_bound f hf z (1/4) δ (by norm_num) hcircle 1
  norm_num [CertifiedTaylorQuadrature.coefficient] at h
  linarith

lemma lipschitz_from_unit_ball (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (δ : ℝ)
    (hb : ∀ z, ‖z-c‖≤ 1 → ‖f z‖≤ δ) (z w : ℂ)
    (hz : ‖z-c‖≤ 3/4) (hw : ‖w-c‖≤ 3/4) :
    ‖f z-f w‖≤ 4*δ*‖z-w‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hf x)
    (fun x hx => deriv_bound_from_unit_ball f hf c δ hb x (mem_closedBall_iff_norm.mp hx))
    (convex_closedBall c (3/4)) (mem_closedBall_iff_norm.mpr hw) (mem_closedBall_iff_norm.mpr hz)

lemma critical_projection_distance (z : ℂ) : ‖z-center z.im‖=|z.re-1/2| := by
  have he : z-center z.im=((z.re-1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [center]
  rw [he,Complex.norm_real,Real.norm_eq_abs]

lemma critical_projection_in_ball (T : ℝ) (z : ℂ) :
    ‖center z.im-center T‖≤ ‖z-center T‖ := by
  have he : center z.im-center T=((z.im-T:ℝ):ℂ)*I := by unfold center; push_cast; ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  simpa [center] using Complex.abs_im_le_norm (z-center T)

lemma imaginary_error_from_critical_reality (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (T δ : ℝ) (hb : ∀ z, ‖z-center T‖≤ 1 → ‖f z‖≤ δ)
    (hcritical : ∀ y : ℝ, ‖center y-center T‖≤ 3/4 → (f (center y)).im=0)
    (z : ℂ) (hz : ‖z-center T‖≤ 3/4) :
    |(f z).im|≤ 4*δ*|z.re-1/2| := by
  have hw := (critical_projection_in_ball T z).trans hz
  have hl := lipschitz_from_unit_ball f hf (center T) δ hb z (center z.im) hz hw
  rw [critical_projection_distance] at hl
  have he : (f z).im=(f z-f (center z.im)).im := by
    rw [sub_im,hcritical z.im hw,sub_zero]
  rw [he]
  exact (Complex.abs_im_le_norm _).trans hl

end CertifiedLocalXi

end Height100Module27

/- Source module: LocalExclusion. -/
section Height100Module28

open Complex Metric
open scoped ComplexConjugate
namespace CertifiedLocalXi

lemma xi_critical_real (T : ℝ) : (xi (center T)).im=0 := by
  have hc : conj (center T)=1-center T := by
    apply Complex.ext <;> simp [center]
    ring
  have he := TaoZetaCertificate.completedZeta_conj (center T)
  rw [hc,completedRiemannZeta₀_one_sub] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  have hΛ : (completedRiemannZeta₀ (center T)).im=0 := by linarith
  have hf : (center T*(center T-1)/2).im=0 := by
    norm_num [center,mul_im]
    ring
  unfold xi
  simp [mul_im,hf,hΛ]

lemma rectangle_in_three_quarter_ball (T : ℝ) (z : ℂ)
    (hr0 : 0≤ z.re) (hr1 : z.re≤ 1) (hi : |z.im-T|≤ 1/2) :
    ‖z-center T‖≤ 3/4 := by
  have he : ‖z-center T‖^2=(z.re-1/2)^2+(z.im-T)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [center]
    ring
  have hr : (z.re-1/2)^2≤ 1/4 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have him : (z.im-T)^2≤ 1/4 := by
    have h := abs_le.mp hi
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (sub_nonneg.mpr h.1)]
  nlinarith [norm_nonneg (z-center T)]

/-- A real-part certificate or a normalized imaginary-part certificate excludes a zero
away from the critical line; uniform approximation on the unit disk supplies both error bounds. -/
lemma nonzero_of_local_certificate (F P : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hP : Differentiable ℂ P) (T : ℝ)
    (happrox : ∀ z, ‖z-center T‖≤ 1 → ‖F z-P z‖≤ 1/100)
    (hcritical : ∀ y : ℝ, (F (center y)-P (center y)).im=0)
    (z : ℂ) (hr0 : 0≤ z.re) (hr1 : z.re≤ 1) (hi : |z.im-T|≤ 1/2)
    (hneq : z.re≠1/2)
    (hcertificate : 1≤ |(P z).re| ∨ |z.re-1/2|≤ |(P z).im|) : F z≠0 := by
  have hz := rectangle_in_three_quarter_ball T z hr0 hr1 hi
  have hz1 : ‖z-center T‖≤ 1 := by linarith
  intro hzero
  rcases hcertificate with hreal | himag
  · have h := happrox z hz1
    rw [hzero,zero_sub,norm_neg] at h
    have hc := (Complex.abs_re_le_norm (P z)).trans h
    linarith
  · have h := imaginary_error_from_critical_reality (fun w => F w-P w) (hF.sub hP)
      T (1/100) happrox (fun y _ => hcritical y) z hz
    rw [hzero,zero_sub,neg_im,abs_neg] at h
    have ha : 0 < |z.re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hneq)
    linarith

end CertifiedLocalXi

end Height100Module28

/- Source module: RoundedLocalApproximation. -/
section Height100Module29

open Complex Finset
namespace CertifiedLocalXi

noncomputable def rotatedVariable (T : ℝ) (z : ℂ) : ℂ := -I*(z-center T)
noncomputable def rotatedPolynomial (b : ℕ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ range 32, (b n : ℂ)*rotatedVariable T z^n

lemma rotatedVariable_norm (T : ℝ) (z : ℂ) :
    ‖rotatedVariable T z‖=‖z-center T‖ := by
  simp [rotatedVariable]

lemma rotatedVariable_center (T y : ℝ) : rotatedVariable T (center y)=(y-T:ℝ) := by
  apply Complex.ext <;> simp [rotatedVariable,center,mul_re,mul_im]

lemma rotatedPolynomial_entire (b : ℕ → ℝ) (T : ℝ) :
    Differentiable ℂ (rotatedPolynomial b T) := by
  unfold rotatedPolynomial rotatedVariable
  fun_prop

lemma rotatedPolynomial_critical_real (b : ℕ → ℝ) (T y : ℝ) :
    (rotatedPolynomial b T (center y)).im=0 := by
  have he : rotatedPolynomial b T (center y) =
      ((∑ n ∈ range 32, b n*(y-T)^n : ℝ):ℂ) := by
    simp only [rotatedPolynomial,rotatedVariable_center,ofReal_sum,ofReal_mul,ofReal_pow]
  rw [he]
  exact Complex.ofReal_im _

lemma scaled_taylor_rotated (S T : ℝ) (z : ℂ) :
    (S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z=
      ∑ n ∈ range 32,
        ((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n)*
          rotatedVariable T z^n := by
  unfold CertifiedComplexTaylor.polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : I*rotatedVariable T z=z-center T := by
    simp [rotatedVariable,← mul_assoc]
  rw [mul_assoc,← mul_pow,he]
  ring

lemma rounded_polynomial_error (S T : ℝ) (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-center T‖≤ 1) :
    ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
      rotatedPolynomial b T z‖≤ 32/10^6 := by
  rw [scaled_taylor_rotated]
  unfold rotatedPolynomial
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤  ∑ n ∈ range 32,
      ‖((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ))*
        rotatedVariable T z^n‖ := by
      simpa only [sub_mul] using
        (norm_sum_le (s:=range 32) (f:=fun n =>
          ((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n)*
            rotatedVariable T z^n-(b n:ℂ)*rotatedVariable T z^n))
    _ ≤  ∑ _n ∈ range 32, (1/10^6:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,norm_pow]
      have hp : ‖rotatedVariable T z‖^n≤ 1 := by
        apply pow_le_one₀ (norm_nonneg _)
        simpa only [rotatedVariable_norm] using hz
      calc
        _ ≤  (1/10^6:ℝ)*1 := mul_le_mul (hb n (mem_range.mp hn)) hp
          (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by norm_num

lemma rounded_xi_error (S T : ℝ) (hS0 : 0≤ S) (hS1 : S≤ 10^33)
    (hT : |T|≤ 100) (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-center T‖≤ 1) :
    ‖(S:ℂ)*xi z-rotatedPolynomial b T z‖≤ 1/100 := by
  have he : (S:ℂ)*xi z-rotatedPolynomial b T z=
      (S:ℂ)*CertifiedComplexTaylor.remainder xi (center T) 32 z+
      ((S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
        rotatedPolynomial b T z) := by
    unfold CertifiedComplexTaylor.remainder
    ring
  rw [he]
  calc
    _ ≤  ‖(S:ℂ)*CertifiedComplexTaylor.remainder xi (center T) 32 z‖+
      ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
        rotatedPolynomial b T z‖ := norm_add_le _ _
    _ = S*‖CertifiedComplexTaylor.remainder xi (center T) 32 z‖+
      ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
        rotatedPolynomial b T z‖ := by simp [Real.norm_eq_abs,abs_of_nonneg hS0]
    _ ≤  (10^33:ℝ)*(1/10^36)+32/10^6 := by
      exact add_le_add (mul_le_mul hS1 (local_tail_norm T hT z hz)
        (norm_nonneg _) (by positivity)) (rounded_polynomial_error S T b hb z hz)
    _ ≤  _ := by norm_num

lemma xi_nonzero_of_rounded_certificate (S T : ℝ) (hS0 : 0≤ S) (hS1 : S≤ 10^33)
    (hT : |T|≤ 100) (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ 1/10^6)
    (z : ℂ) (hr0 : 0≤ z.re) (hr1 : z.re≤ 1) (hi : |z.im-T|≤ 1/2)
    (hneq : z.re≠1/2)
    (hcertificate : 1≤ |(rotatedPolynomial b T z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial b T z).im|) : xi z≠0 := by
  have h := nonzero_of_local_certificate (fun w => (S:ℂ)*xi w)
    (rotatedPolynomial b T) (xi_entire.const_mul _) (rotatedPolynomial_entire b T)
    T (rounded_xi_error S T hS0 hS1 hT b hb) (by
      intro y
      simp [mul_im,xi_critical_real,rotatedPolynomial_critical_real])
    z hr0 hr1 hi hneq hcertificate
  intro hz
  apply h
  simp [hz]

end CertifiedLocalXi

end Height100Module29

/- Source module: LocalSlabAssembly. -/
section Height100Module30

open Complex Finset
namespace CertifiedLocalXi

lemma local_coefficients_from_global (global : ℕ → ℝ)
    (hglobal : ∀ j<256, |CertifiedGlobalMoments.moment j-global j|≤ 1/10^46)
    (S T : ℝ) (hS0 : 0≤ S) (hS1 : S≤ 10^33) (hT : |T|≤ 100)
    (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center T) n*I^n-(b n:ℂ)‖≤ 1/10^7) :
    ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖≤ 1/10^6 := by
  intro n hn
  have h := CertifiedGlobalMoments.local_coefficient_error global hglobal T hT n
  have he : (S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)=
      (S:ℂ)*(CertifiedTaylorQuadrature.coefficient xi (center T) n-
        CertifiedTaylorQuadrature.coefficient (CertifiedGlobalMoments.xiPolynomial global)
          (center T) n)*I^n+
      ((S:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center T) n*I^n-(b n:ℂ)) := by ring
  rw [he]
  calc
    _ ≤  ‖(S:ℂ)*(CertifiedTaylorQuadrature.coefficient xi (center T) n-
        CertifiedTaylorQuadrature.coefficient (CertifiedGlobalMoments.xiPolynomial global)
          (center T) n)*I^n‖+
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center T) n*I^n-(b n:ℂ)‖ := norm_add_le _ _
    _ ≤  (10^33:ℝ)*(1/10^41)+1/10^7 := by
      apply add_le_add _ (hb n hn)
      simp only [norm_mul,norm_pow,norm_I,one_pow,mul_one,norm_real,Real.norm_eq_abs,
        abs_of_nonneg hS0]
      exact mul_le_mul hS1 h (norm_nonneg _) (by positivity)
    _ ≤  _ := by norm_num

lemma xi_nonzero_implies_zeta {s : ℂ} (h0 : 0< s.re) (h1 : s.re<1)
    (hXi : xi s≠0) : riemannZeta s≠0 := by
  have hs0 : s≠0 := fun h => by simp [h] at h0
  have hs1 : s≠1 := fun h => by simp [h] at h1
  have h1s : (1:ℂ)-s≠0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with hz | hz
  · apply hXi
    have hh := completedRiemannZeta_eq s
    rw [hz] at hh
    have hsum : completedRiemannZeta₀ s=1/s+1/(1-s) := by linear_combination -hh
    unfold xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

noncomputable def slabCenter (i : Fin 86) : ℝ := 29/2+(i.val:ℝ)

lemma slabCenter_bound (i : Fin 86) : |slabCenter i|≤ 100 := by
  have hi : (i.val:ℝ)≤ 85 := by
    have h : i.val≤ 85 := by omega
    exact_mod_cast h
  have hi0 : (0 : ℝ) ≤  (i.val : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  unfold slabCenter
  constructor <;> linarith

lemma slabs_cover (t : ℝ) (ht0 : 14≤ t) (ht1 : t≤ 100) :
    ∃ i : Fin 86, |t-slabCenter i|≤ 1/2 := by
  by_cases he : t=100
  · refine ⟨⟨85,by norm_num⟩,?_⟩
    norm_num [slabCenter,he]
  · have hlt : t<100 := lt_of_le_of_ne ht1 he
    have hnonneg : 0≤ t-14 := by linarith
    have hi : Nat.floor (t-14)<86 := (Nat.floor_lt hnonneg).mpr (by norm_num; linarith)
    refine ⟨⟨Nat.floor (t-14),hi⟩,?_⟩
    have hlo := Nat.floor_le hnonneg
    have hup := Nat.lt_floor_add_one (t-14)
    rw [abs_le]
    unfold slabCenter
    constructor <;> dsimp <;> linarith

/-- The analytic root assembly. All finite coefficient and nonvanishing certificates
remain explicit hypotheses until they have been checked. -/
lemma rh_block_of_local_certificates
    (S : Fin 86 → ℝ) (b : Fin 86 → ℕ → ℝ)
    (hS0 : ∀ i, 0≤ S i) (hS1 : ∀ i, S i≤ 10^33)
    (hcoeff : ∀ i n, n<32 →
      ‖(S i:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center (slabCenter i)) n*I^n-
        (b i n:ℂ)‖≤ 1/10^6)
    (hcert : ∀ i z, 0≤ z.re → z.re≤ 1 → |z.im-slabCenter i|≤ 1/2 →
      1≤ |(rotatedPolynomial (b i) (slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial (b i) (slabCenter i) z).im|)
    (s : ℂ) (hs : riemannZeta s=0) (h0 : 0< s.re) (h1 : s.re<1)
    (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  by_contra hneq
  obtain ⟨i,hi⟩ := slabs_cover s.im ha (by norm_num at hb ⊢; exact hb)
  have hxi := xi_nonzero_of_rounded_certificate (S i) (slabCenter i) (hS0 i) (hS1 i)
    (slabCenter_bound i) (b i) (hcoeff i) s h0.le h1.le hi hneq
    (hcert i s h0.le h1.le hi)
  exact xi_nonzero_implies_zeta h0 h1 hxi hs

lemma rh_block_of_global_certificates
    (global : ℕ → ℝ)
    (hglobal : ∀ j<256, |CertifiedGlobalMoments.moment j-global j|≤ 1/10^46)
    (S : Fin 86 → ℝ) (b : Fin 86 → ℕ → ℝ)
    (hS0 : ∀ i, 0≤ S i) (hS1 : ∀ i, S i≤ 10^33)
    (hcoeff : ∀ i n, n<32 →
      ‖(S i:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center (slabCenter i)) n*I^n-
        (b i n:ℂ)‖≤ 1/10^7)
    (hcert : ∀ i z, 0≤ z.re → z.re≤ 1 → |z.im-slabCenter i|≤ 1/2 →
      1≤ |(rotatedPolynomial (b i) (slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial (b i) (slabCenter i) z).im|)
    (s : ℂ) (hs : riemannZeta s=0) (h0 : 0< s.re) (h1 : s.re<1)
    (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  apply rh_block_of_local_certificates S b hS0 hS1 _ hcert s hs h0 h1 ha hb
  intro i
  exact local_coefficients_from_global global hglobal (S i) (slabCenter i)
    (hS0 i) (hS1 i) (slabCenter_bound i) (b i) (hcoeff i)

end CertifiedLocalXi

end Height100Module30

/- Source module: PolynomialTranslation. -/
section Height100Module31

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature

lemma coefficient_affine (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c a : ℂ) (n : ℕ) :
    coefficient (fun z => f (c+a*z)) 0 n=a^n*coefficient f c n := by
  have hg : Differentiable ℂ (fun z => f (c+z)) := by fun_prop
  unfold coefficient
  rw [iteratedDeriv_comp_const_mul hg.contDiff,iteratedDeriv_comp_const_add]
  simp only [mul_zero,add_zero]
  ring

lemma coefficient_power (m n : ℕ) (c : ℂ) :
    coefficient (fun z : ℂ => z^m) c n=(m.choose n:ℂ)*c^(m-n) := by
  unfold coefficient
  rw [iteratedDeriv_pow,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

noncomputable def powerPolynomial (b : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ range N, (b m:ℂ)*z^m

noncomputable def translatedCoefficient (b : ℕ → ℝ) (N n : ℕ) (T : ℝ) : ℝ :=
  ∑ m ∈ range N, b m*(m.choose n:ℝ)*T^(m-n)

lemma coefficient_powerPolynomial (b : ℕ → ℝ) (N n : ℕ) (T : ℝ) :
    coefficient (powerPolynomial b N) T n=(translatedCoefficient b N n T:ℂ) := by
  unfold coefficient powerPolynomial translatedCoefficient
  rw [iteratedDeriv_fun_sum (fun m _ => by fun_prop),sum_div]
  simp only [ofReal_sum,ofReal_mul,ofReal_pow,ofReal_natCast]
  apply sum_congr rfl
  intro m hm
  rw [iteratedDeriv_const_mul_field]
  have h := coefficient_power m n (T:ℂ)
  unfold coefficient at h
  rw [mul_div_assoc,h]
  ring

end CertifiedPolynomialTranslation

end Height100Module31

/- Source module: GlobalPolynomialTranslation. -/
section Height100Module32

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

noncomputable def criticalMomentCoefficient (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  b j*(-1)^j/(128:ℝ)^(2*j)

noncomputable def criticalXiPolynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  1/2-∑ j ∈ range 256, (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)

lemma scaledVariable_critical (z : ℂ) : scaledVariable (1/2+I*z)=I*(z/128) := by
  unfold scaledVariable
  ring

lemma even_I_power (j : ℕ) : I^(2*j)=(-1:ℂ)^j := by rw [pow_mul,I_sq]

lemma global_critical_identity (b : ℕ → ℝ) (z : ℂ) :
    xiPolynomial b (1/2+I*z)=criticalXiPolynomial b z := by
  have hf : (1/2+I*z)*(1/2+I*z-1)/2=-(z^2/2+1/8) := by
    ring_nf
    rw [I_sq]
    ring
  unfold xiPolynomial criticalXiPolynomial CertifiedGlobalMoments.polynomial
  rw [hf,mul_sum,sub_eq_add_neg,←sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [scaledVariable_critical,mul_pow,even_I_power,div_pow]
  unfold criticalMomentCoefficient
  push_cast
  rw [pow_add]
  ring

lemma coefficient_const (a c : ℂ) (n : ℕ) :
    coefficient (fun _ : ℂ => a) c n=if n=0 then a else 0 := by
  unfold coefficient
  rw [iteratedDeriv_const]
  by_cases hn : n=0 <;> simp [hn]

noncomputable def localGlobalCoefficient (b : ℕ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  (if n=0 then 1/2 else 0)-∑ j ∈ range 256, criticalMomentCoefficient b j*
    ((Nat.choose (2*j+2) n:ℝ)*T^(2*j+2-n)/2+(Nat.choose (2*j) n:ℝ)*T^(2*j-n)/8)

lemma coefficient_criticalXi (b : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    coefficient (criticalXiPolynomial b) T n=(localGlobalCoefficient b T n:ℂ) := by
  have hf : ∀ j : ℕ, Differentiable ℂ (fun z : ℂ =>
      (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)) := by intro j; fun_prop
  unfold criticalXiPolynomial coefficient
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),sub_div,
    iteratedDeriv_fun_sum (fun j _ => (hf j).contDiff.contDiffAt),sum_div]
  change coefficient (fun _ : ℂ => 1/2) T n-
    (∑ j ∈ range 256,
      coefficient (fun z : ℂ => (criticalMomentCoefficient b j:ℂ)*
        (z^(2*j+2)/2+z^(2*j)/8)) T n)=(localGlobalCoefficient b T n:ℂ)
  rw [coefficient_const]
  unfold localGlobalCoefficient
  push_cast
  apply congrArg₂ (· - ·)
  · split_ifs <;> norm_num
  · apply sum_congr rfl
    intro j hj
    unfold coefficient
    rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_div_const,iteratedDeriv_div_const]
    have h0 := coefficient_power (2*j+2) n (T:ℂ)
    have h1 := coefficient_power (2*j) n (T:ℂ)
    unfold coefficient at h0 h1
    calc
      _ = (criticalMomentCoefficient b j:ℂ)*
        ((iteratedDeriv n (fun z : ℂ => z^(2*j+2)) T/(n.factorial:ℂ))/2+
          (iteratedDeriv n (fun z : ℂ => z^(2*j)) T/(n.factorial:ℂ))/8) := by ring
      _ = _ := by rw [h0,h1]

lemma global_rotated_coefficient (b : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n*I^n=
      (localGlobalCoefficient b T n:ℂ) := by
  have he : (fun z : ℂ => xiPolynomial b (CertifiedLocalXi.center T+I*z))=
      (fun z : ℂ => criticalXiPolynomial b ((T:ℂ)+z)) := by
    funext z
    rw [←global_critical_identity]
    congr 1
    unfold CertifiedLocalXi.center
    ring
  have hh := congrArg (fun F : ℂ → ℂ => coefficient F 0 n) he
  rw [coefficient_affine _ (xiPolynomial_entire b)] at hh
  unfold coefficient at hh
  rw [iteratedDeriv_comp_const_add] at hh
  simp only [add_zero] at hh
  change I^n*coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n=
    coefficient (criticalXiPolynomial b) T n at hh
  rw [coefficient_criticalXi] at hh
  simpa only [mul_comm] using hh

lemma global_rotated_error (global : ℕ → ℝ) (S T v ε : ℝ) (n : ℕ)
    (h : |S*localGlobalCoefficient global T n-v|≤ ε) :
    ‖(S:ℂ)*coefficient (xiPolynomial global) (CertifiedLocalXi.center T) n*I^n-(v:ℂ)‖≤ ε := by
  rw [mul_assoc,global_rotated_coefficient,←ofReal_mul,←ofReal_sub,norm_real,Real.norm_eq_abs]
  exact h

lemma rh_block_of_real_translation_certificates
    (global : ℕ → ℝ)
    (hglobal : ∀ j<256, |moment j-global j|≤ 1/10^46)
    (S : Fin 86 → ℝ) (b : Fin 86 → ℕ → ℝ)
    (hS0 : ∀ i, 0≤ S i) (hS1 : ∀ i, S i≤ 10^33)
    (hcoeff : ∀ i n, n<32 →
      |S i*localGlobalCoefficient global (CertifiedLocalXi.slabCenter i) n-b i n|≤ 1/10^7)
    (hcert : ∀ i z, 0≤ z.re → z.re≤ 1 → |z.im-CertifiedLocalXi.slabCenter i|≤ 1/2 →
      1≤ |(CertifiedLocalXi.rotatedPolynomial (b i) (CertifiedLocalXi.slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(CertifiedLocalXi.rotatedPolynomial (b i) (CertifiedLocalXi.slabCenter i) z).im|)
    (s : ℂ) (hs : riemannZeta s=0) (h0 : 0< s.re) (h1 : s.re<1)
    (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  apply CertifiedLocalXi.rh_block_of_global_certificates global hglobal S b hS0 hS1 _
    hcert s hs h0 h1 ha hb
  intro i n hn
  exact global_rotated_error global (S i) (CertifiedLocalXi.slabCenter i) (b i n)
    (1/10^7) n (hcoeff i n hn)

end CertifiedPolynomialTranslation

end Height100Module32

/- Source module: DenseGlobalPolynomial. -/
section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open Complex Finset CertifiedPolynomialTranslation

noncomputable def halfDenominator : ℕ := 4*momentScale*128^510

noncomputable def scaledMoment (C : ℕ → ℤ) (j : ℕ) : ℤ :=
  if j<256 then (-1)^j*C j*(128:ℤ)^(510-2*j) else 0

noncomputable def evenCoefficient (C : ℕ → ℤ) (j : ℕ) : ℤ :=
  (if j=0 then (halfDenominator:ℤ) else 0)-scaledMoment C j-
    (if j=0 then 0 else 4*scaledMoment C (j-1))

noncomputable def coefficient (C : ℕ → ℤ) (m : ℕ) : ℤ :=
  if m%2=0 then evenCoefficient C (m/2) else 0

noncomputable def moments (C : ℕ → ℤ) (j : ℕ) : ℝ := (C j:ℝ)/momentScale
noncomputable def denseCoefficients (C : ℕ → ℤ) (m : ℕ) : ℝ :=
  (coefficient C m:ℝ)/denominator

lemma denominator_pos : 0< denominator := by unfold denominator momentScale; positivity
lemma denominator_half : denominator=2*halfDenominator := by
  unfold denominator halfDenominator
  ring

lemma scaled_moment_identity (C : ℕ → ℤ) (j : ℕ) (hj : j<256) :
    (denominator:ℂ)*(criticalMomentCoefficient (moments C) j:ℂ)=8*(scaledMoment C j:ℂ) := by
  have hj2 : 2*j≤ 510 := by omega
  have hp : (128:ℂ)^510=(128:ℂ)^(2*j)*(128:ℂ)^(510-2*j) := by
    rw [←pow_add,Nat.add_sub_of_le hj2]
  unfold denominator criticalMomentCoefficient moments scaledMoment
  rw [if_pos hj]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_intCast,Complex.ofReal_natCast,
    Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat,Int.cast_mul,Int.cast_pow,
    Int.cast_neg,Int.cast_one,Int.cast_ofNat]
  rw [hp]
  have hs : (momentScale:ℂ)≠0 := by
    exact_mod_cast (by unfold momentScale; positivity : momentScale≠0)
  field_simp

lemma integer_polynomial_identity (C : ℕ → ℤ) (z : ℂ) :
    (∑ m ∈ range 513, (coefficient C m:ℂ)*z^m)=
      (denominator:ℂ)*criticalXiPolynomial (moments C) z := by
  have he : ∀ j,
      (evenCoefficient C j:ℂ)=
        (if j=0 then (halfDenominator:ℂ) else 0)-(scaledMoment C j:ℂ)-
          (if j=0 then 0 else 4*(scaledMoment C (j-1):ℂ)) := by
    intro j
    unfold evenCoefficient
    by_cases hj : j=0
    · simp only [if_pos hj,Int.cast_sub,Int.cast_zero,Int.cast_natCast]
    · simp only [if_neg hj,Int.cast_sub,Int.cast_zero,Int.cast_mul,Int.cast_ofNat]
  have hc : ∀ m, (coefficient C m:ℂ)=if m%2=0 then (evenCoefficient C (m/2):ℂ) else 0 := by
    intro m
    unfold coefficient
    split_ifs <;> simp only [Int.cast_zero]
  simp_rw [hc]
  rw [show 513=2*256+1 by norm_num,
    CertifiedEvenPolynomial.dense_even_eval (fun j => (evenCoefficient C j:ℂ)) 256 z]
  simp_rw [he]
  rw [CertifiedEvenPolynomial.recurrence_eval _ _ 256 (by simp [scaledMoment])]
  unfold criticalXiPolynomial
  rw [mul_sub,mul_sum]
  have hh : (halfDenominator:ℂ)=(denominator:ℂ)*(1/2) := by
    rw [denominator_half]
    push_cast
    ring
  rw [hh]
  congr 1
  apply sum_congr rfl
  intro j hj
  have h := scaled_moment_identity C j (mem_range.mp hj)
  calc
    _ = (8*(scaledMoment C j:ℂ))*(z^(2*j+2)/2+z^(2*j)/8) := by ring
    _ = _ := by rw [←h]; ring

end CertifiedDenseGlobalPolynomial

end Height100Module33

/- Source module: FixedPointIntervals. -/
section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint

noncomputable def Contains (S : ℕ) (b : Box) (x : ℝ) : Prop :=
  (b.lo:ℝ)/S ≤  x ∧ x ≤  (b.hi:ℝ)/S

noncomputable def oneBox (S : ℕ) : Box := ⟨S,S⟩
noncomputable def addBox (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩

lemma contains_nonneg {S : ℕ} {b : Box} {x : ℝ} (h : Contains S b x) : 0≤ x :=
  (by positivity : (0:ℝ)≤ b.lo/S).trans h.1

lemma quotient_bounds (m n : ℕ) (hn : 0< n) :
    ((m/n:ℕ):ℝ) ≤  (m:ℝ)/n ∧ (m:ℝ)/n ≤  ((m/n+1:ℕ):ℝ) := by
  refine ⟨Nat.cast_div_le, ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ)< n)).mpr
  have h := (Nat.lt_mul_div_succ m hn).le
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

lemma oneBox_sound {S : ℕ} (hS : 0< S) : Contains S (oneBox S) 1 := by
  have h : (S:ℝ)≠0 := by exact_mod_cast hS.ne'
  simp [Contains,oneBox,h]

lemma addBox_sound {S : ℕ} {a b : Box} {x y : ℝ}
    (ha : Contains S a x) (hb : Contains S b y) : Contains S (addBox a b) (x+y) := by
  constructor <;> dsimp [Contains,addBox] at *
  · push_cast
    rw [add_div]
    linarith [ha.1,hb.1]
  · push_cast
    rw [add_div]
    linarith [ha.2,hb.2]

lemma mulDivBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d)
    {a b : Box} {x y : ℝ} (ha : Contains S a x) (hb : Contains S b y) :
    Contains S (mulDivBox S d a b) (x*y/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have hx := contains_nonneg ha
  have hy := contains_nonneg hb
  have hlo := (quotient_bounds (a.lo*b.lo) (S*d) (Nat.mul_pos hS hd)).1
  have hhi := (quotient_bounds (a.hi*b.hi) (S*d) (Nat.mul_pos hS hd)).2
  simp only [Nat.cast_mul] at hlo hhi
  constructor
  · calc
      _ ≤  (((a.lo:ℝ)*b.lo)/(S*d))/S := div_le_div_of_nonneg_right hlo hSr.le
      _ = ((a.lo:ℝ)/S*((b.lo:ℝ)/S))/d := by ring
      _ ≤  _ := by gcongr; exact ha.1; exact hb.1
  · calc
      _ ≤  ((a.hi:ℝ)/S*((b.hi:ℝ)/S))/d := by gcongr; exact ha.2; exact hb.2
      _ = (((a.hi:ℝ)*b.hi)/(S*d))/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right hhi hSr.le

/-- Fixed-point term recurrence, retaining both the current Taylor term and sum. -/
noncomputable def expTaylorRun (S : ℕ) (a : Box) : ℕ → Box × Box
  | 0 => (oneBox S,oneBox S)
  | n+1 =>
    let prev := expTaylorRun S a n
    let next := mulDivBox S (n+1) prev.1 a
    (next, addBox prev.2 next)

lemma expTaylorRun_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (n : ℕ) :
    Contains S (expTaylorRun S a n).1 (x^n/(n.factorial:ℝ)) ∧
    Contains S (expTaylorRun S a n).2 (∑ k ∈ range (n+1),x^k/(k.factorial:ℝ)) := by
  induction n with
  | zero => simpa [expTaylorRun] using And.intro (oneBox_sound hS) (oneBox_sound hS)
  | succ n ih =>
    have ht := mulDivBox_sound hS (Nat.succ_pos n) ih.1 ha
    have he : (x^n/(n.factorial:ℝ))*x/((n+1:ℕ):ℝ) = x^(n+1)/((n+1).factorial:ℝ) := by
      rw [Nat.factorial_succ,pow_succ]
      push_cast
      field_simp
    rw [he] at ht
    refine ⟨ht, ?_⟩
    have hs := addBox_sound ih.2 ht
    simpa only [expTaylorRun,sum_range_succ] using hs

noncomputable def expBox (S : ℕ) (a : Box) (N : ℕ) : Box :=
  let b := (expTaylorRun S a N).2
  ⟨b.lo,b.hi+1⟩

lemma expBox_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (hx1 : x≤ 1) (N : ℕ)
    (htail : ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1)) ≤  1/(S:ℝ)) :
    Contains S (expBox S a N) (Real.exp x) := by
  have hx0 := contains_nonneg ha
  have hx : |x|≤ 1 := by rwa [abs_of_nonneg hx0]
  have hsum := (expTaylorRun_sound hS ha N).2
  have hl := Real.sum_le_exp_of_nonneg hx0 (N+1)
  have he := Real.exp_bound hx (Nat.succ_pos N)
  have hp : |x|^(N+1)≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hr : Real.exp x-(∑ k ∈ range (N+1),x^k/(k.factorial:ℝ))≤ 1/(S:ℝ) := by
    calc
      _ ≤  |Real.exp x-(∑ k ∈ range (N+1),x^k/(k.factorial:ℝ))| := le_abs_self _
      _ ≤  _ := he
      _ ≤  ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1)) := by
        have hh := mul_le_of_le_one_left
          (by positivity : (0:ℝ)≤ ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1))) hp
        simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_ofNat] using hh
      _ ≤  _ := htail
  constructor
  · exact hsum.1.trans hl
  · dsimp [expBox]
    push_cast
    rw [add_div]
    linarith [hsum.2]

noncomputable def inverseBox (S : ℕ) (a : Box) : Box :=
  ⟨S*S/a.hi,S*S/a.lo+1⟩

lemma inverseBox_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (hl : 0< a.lo) : Contains S (inverseBox S a) (1/x) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hlr : (0:ℝ)< a.lo := by exact_mod_cast hl
  have hx : 0< x := (div_pos hlr hSr).trans_le ha.1
  have hh : 0< a.hi := by
    by_contra hh
    have hz : a.hi=0 := by omega
    have hhx := ha.2
    simp only [hz,Nat.cast_zero,zero_div] at hhx
    linarith
  have hhr : (0:ℝ)< a.hi := by exact_mod_cast hh
  have hlo := (quotient_bounds (S*S) a.hi hh).1
  have hhi := (quotient_bounds (S*S) a.lo hl).2
  simp only [Nat.cast_mul] at hlo hhi
  constructor
  · calc
      _ ≤  ((S:ℝ)*S/a.hi)/S := div_le_div_of_nonneg_right hlo hSr.le
      _ = 1/((a.hi:ℝ)/S) := by field_simp
      _ ≤  _ := one_div_le_one_div_of_le hx ha.2
  · calc
      _ ≤  1/((a.lo:ℝ)/S) := one_div_le_one_div_of_le (div_pos hlr hSr) ha.1
      _ = ((S:ℝ)*S/a.lo)/S := by field_simp
      _ ≤  _ := div_le_div_of_nonneg_right hhi hSr.le

lemma repeatedSquare_sound {S : ℕ} (hS : 0< S) (n : ℕ) {a : Box} {x : ℝ}
    (ha : Contains S a x) : Contains S (repeatedSquare S n a) (x^(2^n)) := by
  induction n generalizing a x with
  | zero => simpa [repeatedSquare] using ha
  | succ n ih =>
    have hs : Contains S (mulDivBox S 1 a a) (x^2) := by
      simpa [pow_two] using mulDivBox_sound hS (by decide : 0<1) ha ha
    have h := ih hs
    simpa [repeatedSquare,pow_succ,pow_mul,Nat.mul_comm] using h

noncomputable def rationalBox (S m d : ℕ) : Box := ⟨S*m/d,S*m/d+1⟩

lemma rationalBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d) (m : ℕ) :
    Contains S (rationalBox S m d) ((m:ℝ)/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have h := quotient_bounds (S*m) d hd
  constructor
  · calc
      _ ≤  ((S*m:ℕ):ℝ)/d/S := div_le_div_of_nonneg_right h.1 hSr.le
      _ = (m:ℝ)/d := by push_cast; field_simp
  · calc
      (m:ℝ)/d = ((S*m:ℕ):ℝ)/d/S := by push_cast; field_simp
      _ ≤  _ := div_le_div_of_nonneg_right h.2 hSr.le

end CertifiedFixedPoint

end Height100Module34

/- Source module: FixedPointExp310. -/
section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint

noncomputable def expUnit310 (a : Box) : Box := expBox scale310 a 200

lemma expUnit310_sound {a : Box} {x : ℝ} (ha : Contains scale310 a x) (hx : x≤ 1) :
    Contains scale310 (expUnit310 a) (Real.exp x) := by
  apply expBox_sound (by norm_num [scale310]) ha hx 200
  norm_num [scale310,Nat.factorial]

end CertifiedFixedPoint

end Height100Module35

/- Source module: PointExponentials. -/
section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

noncomputable def center (i : Fin 16) : ℝ := (6*i.val+3)/16

noncomputable def pointInput (i : Fin 16) : Box := rationalBox scale310 (6*i.val+3) 128
noncomputable def pointExp (i : Fin 16) : Box := expUnit310 (pointInput i)
noncomputable def pointExpValues : List Box := List.ofFn pointExp

theorem _root_.CertifiedThetaPoints.pointExpCache_correct : CertifiedThetaPoints.pointExpValues = CertifiedThetaPoints.pointExpCache :=
  Eq.refl CertifiedThetaPoints.pointExpCache

lemma cachedPointExp_eq (i : Fin 16) : cachedPointExp i = pointExp i := by
  rw [cachedPointExp,←pointExpCache_correct]
  simp only [pointExpValues,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos i.isLt,Option.getD_some]

lemma pointExp_sound (i : Fin 16) :
    Contains scale310 (cachedPointExp i) (Real.exp (center i/8)) := by
  rw [cachedPointExp_eq]
  have ha := rationalBox_sound (by norm_num [scale310] : 0< scale310)
    (by decide : 0<128) (6*i.val+3)
  have he : (((6*i.val+3:ℕ):ℝ)/128) = center i/8 := by
    simp [center]
    ring
  norm_num only [Nat.cast_ofNat] at ha
  rw [he] at ha
  apply expUnit310_sound ha
  have hi : (i.val:ℝ)<16 := by exact_mod_cast i.isLt
  unfold center
  linarith

end CertifiedThetaPoints

end Height100Module36

/- Source module: ArctanCertificate. -/
section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi

noncomputable def atanSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma atan_remainder (x : ℝ) (hx0 : 0≤ x) (hx1 : x<1) (N : ℕ) :
    |Real.arctan x - atanSum x N| ≤  x^(2*N+1)/(1-x^2) := by
  have hx : ‖x‖<1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hx0]
  have hs := Real.hasSum_arctan hx
  have htail : Real.arctan x - atanSum x N =
      ∑' n : ℕ, (-1)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    exact sub_eq_iff_eq_add.mpr (by simpa [atanSum,add_comm] using h.symm)
  rw [htail, ← Real.norm_eq_abs]
  have hq0 : 0≤ x^2 := sq_nonneg x
  have hq1 : x^2<1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (x^(2*N+1))
  have he := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    have hd : (1:ℝ)≤ 2*(n+N)+1 := by
      have hn : (0:ℝ)≤ n := Nat.cast_nonneg n
      have hN : (0:ℝ)≤ N := Nat.cast_nonneg N
      linarith
    calc
      ‖(-1:ℝ)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1)‖ =
          x^(2*(n+N)+1)/(2*(n+N)+1) := by
        simp [norm_div,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg hx0,
          abs_of_nonneg (by positivity : (0:ℝ)≤ 2*(n+N)+1)]
      _ ≤  x^(2*(n+N)+1) := div_le_self (by positivity) hd
      _ = x^(2*N+1)*(x^2)^n := by
        rw [show 2*(n+N)+1=(2*N+1)+2*n by ring,pow_add,pow_mul])
  simpa only [div_eq_mul_inv] using he

noncomputable def rationalAtanSum (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma rationalAtanSum_cast (x : ℚ) (N : ℕ) :
    (rationalAtanSum x N : ℝ) = atanSum x N := by
  simp [rationalAtanSum,atanSum]

noncomputable def machinApprox (N M : ℕ) : ℚ :=
  16*rationalAtanSum (1/5) N - 4*rationalAtanSum (1/239) M

lemma machin_error (N M : ℕ) :
    |Real.pi-(machinApprox N M:ℝ)| ≤ 
      16*((1/5:ℝ)^(2*N+1)/(1-(1/5:ℝ)^2)) +
        4*((1/239:ℝ)^(2*M+1)/(1-(1/239:ℝ)^2)) := by
  have h5 := atan_remainder (1/5) (by norm_num) (by norm_num) N
  have h239 := atan_remainder (1/239) (by norm_num) (by norm_num) M
  have hm : Real.pi = 16*Real.arctan (1/5)-4*Real.arctan (1/239) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    norm_num at h
    linarith
  rw [hm,machinApprox]
  push_cast
  rw [rationalAtanSum_cast,rationalAtanSum_cast]
  calc
    _ = |16*(Real.arctan (1/5)-atanSum (1/5) N) -
        4*(Real.arctan (1/239)-atanSum (1/239) M)| := by congr 1; ring
    _ ≤  |16*(Real.arctan (1/5)-atanSum (1/5) N)| +
        |4*(Real.arctan (1/239)-atanSum (1/239) M)| := abs_sub _ _
    _ ≤  _ := by
      rw [abs_mul,abs_mul]
      norm_num at h5 h239 ⊢
      linarith

end CertifiedHighPrecisionPi

end Height100Module37

/- Source module: Pi310. -/
section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi

lemma machin_error_320 : |Real.pi-(machinApprox 230 70:ℝ)|≤ 1/10^320 := by
  apply (machin_error 230 70).trans
  norm_num

lemma machin_lower_check : (piFloor310:ℚ)/10^310 + 1/10^320 ≤  machinApprox 230 70 := by
  decide +kernel

lemma machin_upper_check : machinApprox 230 70 + 1/10^320 ≤  (piFloor310+1:ℚ)/10^310 := by
  decide +kernel

theorem pi_enclosure_310 :
    (piFloor310:ℝ)/10^310 ≤  Real.pi ∧ Real.pi ≤  (piFloor310+1:ℝ)/10^310 := by
  have hl : (piFloor310:ℝ)/10^310 + 1/10^320 ≤  (machinApprox 230 70:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_lower_check
    push_cast at h
    exact h
  have hu : (machinApprox 230 70:ℝ) + 1/10^320 ≤  (piFloor310+1:ℝ)/10^310 := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_upper_check
    push_cast at h
    exact h
  have he := abs_le.mp machin_error_320
  constructor <;> linarith

end CertifiedHighPrecisionPi

end Height100Module38

/- Source module: FixedPointTransforms. -/
section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint

noncomputable def divideBox (d : ℕ) (a : Box) : Box := ⟨a.lo/d,a.hi/d+1⟩

lemma scaleBox_sound {S : ℕ} (m : ℕ) {a : Box} {x : ℝ}
    (ha : Contains S a x) : Contains S (scaleBox m a) ((m:ℝ)*x) := by
  constructor <;> dsimp [scaleBox]
  · push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha.1 (Nat.cast_nonneg m)
  · push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha.2 (Nat.cast_nonneg m)

lemma divideBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d)
    {a : Box} {x : ℝ} (ha : Contains S a x) :
    Contains S (divideBox d a) (x/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  constructor
  · calc
      _ ≤  ((a.lo:ℝ)/d)/S := div_le_div_of_nonneg_right (quotient_bounds a.lo d hd).1 hSr.le
      _ = ((a.lo:ℝ)/S)/d := by ring
      _ ≤  _ := div_le_div_of_nonneg_right ha.1 hdr.le
  · calc
      _ ≤  ((a.hi:ℝ)/S)/d := div_le_div_of_nonneg_right ha.2 hdr.le
      _ = ((a.hi:ℝ)/d)/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right (quotient_bounds a.hi d hd).2 hSr.le

lemma expTaylorRun_sum_lower (S : ℕ) (a : Box) (n : ℕ) :
    S≤ (expTaylorRun S a n).2.lo := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.trans (Nat.le_add_right _ _)

lemma expUnit310_lo_pos (a : Box) : 0<(expUnit310 a).lo := by
  have h := expTaylorRun_sum_lower scale310 a 200
  exact (by norm_num [scale310] : 0< scale310).trans_le h

noncomputable def expNegative310 (a : Box) : Box :=
  repeatedSquare scale310 10 (inverseBox scale310 (expUnit310 (divideBox 1024 a)))

lemma expNegative310_sound {a : Box} {x : ℝ}
    (ha : Contains scale310 a x) (hx : x≤ 1024) :
    Contains scale310 (expNegative310 a) (Real.exp (-x)) := by
  have hS : 0< scale310 := by norm_num [scale310]
  have hq := divideBox_sound hS (by decide : 0<1024) ha
  have he := expUnit310_sound hq (by norm_num; linarith)
  have hi := inverseBox_sound hS he (expUnit310_lo_pos _)
  have hp := repeatedSquare_sound hS 10 hi
  have hv : (1/Real.exp (x/1024))^(1024:ℕ) = Real.exp (-x) := by
    rw [one_div,←Real.exp_neg,←Real.exp_nat_mul]
    norm_num
    ring
  norm_num only [Nat.cast_ofNat] at hp
  simpa only [expNegative310,hv] using hp

end CertifiedFixedPoint

end Height100Module39

/- Source module: ThetaPointModel. -/
section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi

noncomputable def quarterExpBox (i : Fin 16) : Box := repeatedSquare scale310 1 (cachedPointExp i)
noncomputable def lambda (i : Fin 16) (n : Fin 8) : ℝ :=
  Real.pi*(n.val+1:ℝ)^2*Real.exp (center i)

noncomputable instance (i : Fin 16) (n : Fin 8) : Decidable (active i n) := inferInstanceAs
  (Decidable ((lambdaBox i n).lo < 800*scale310))

lemma piBox_sound : Contains scale310 piBox Real.pi := by
  simpa only [Contains,piBox,scale310,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using pi_enclosure_310

lemma centerExpBox_sound (i : Fin 16) :
    Contains scale310 (centerExpBox i) (Real.exp (center i)) := by
  have h := repeatedSquare_sound (by norm_num [scale310] : 0< scale310) 3 (pointExp_sound i)
  have he : (Real.exp (center i/8))^(2^3)=Real.exp (center i) := by
    rw [←Real.exp_nat_mul]
    norm_num
    ring
  simpa only [centerExpBox,he] using h

lemma quarterExpBox_sound (i : Fin 16) :
    Contains scale310 (quarterExpBox i) (Real.exp (center i/4)) := by
  have h := repeatedSquare_sound (by norm_num [scale310] : 0< scale310) 1 (pointExp_sound i)
  have he : (Real.exp (center i/8))^(2^1)=Real.exp (center i/4) := by
    rw [←Real.exp_nat_mul]
    norm_num
    ring
  simpa only [quarterExpBox,he] using h

lemma lambdaBox_sound (i : Fin 16) (n : Fin 8) :
    Contains scale310 (lambdaBox i n) (lambda i n) := by
  have h := scaleBox_sound ((n.val+1)^2)
    (mulDivBox_sound (by norm_num [scale310] : 0< scale310) (by decide : 0<1)
      piBox_sound (centerExpBox_sound i))
  simpa [lambdaBox,lambda,mul_comm,mul_left_comm,mul_assoc] using h

lemma active_bound_check : ∀ i : Fin 16, ∀ n : Fin 8,
    active i n → (lambdaBox i n).hi ≤  1024*scale310 := by decide +kernel

lemma active_lambda_le (i : Fin 16) (n : Fin 8) (h : active i n) : lambda i n≤ 1024 := by
  have hb := (lambdaBox_sound i n).2
  have hc := active_bound_check i n h
  have hSr : (0:ℝ)< scale310 := by norm_num [scale310]
  have he : ((lambdaBox i n).hi:ℝ)/scale310 ≤  1024 := by
    apply (div_le_iff₀ hSr).mpr
    exact_mod_cast hc
  exact hb.trans he

lemma inactive_lambda_ge (i : Fin 16) (n : Fin 8) (h : ¬active i n) : 800≤ lambda i n := by
  have hb := (lambdaBox_sound i n).1
  have hc : 800*scale310 ≤  (lambdaBox i n).lo := Nat.le_of_not_gt h
  have hSr : (0:ℝ)< scale310 := by norm_num [scale310]
  have he : (800:ℝ) ≤  ((lambdaBox i n).lo:ℝ)/scale310 := by
    apply (le_div_iff₀ hSr).mpr
    exact_mod_cast hc
  exact he.trans hb

noncomputable def thetaInitialBox (i : Fin 16) (n : Fin 8) : Box :=
  if active i n then expNegative310 (lambdaBox i n) else ⟨0,0⟩

noncomputable def fullInitialBox (i : Fin 16) (n : Fin 8) : Box :=
  scaleBox 2 (mulDivBox scale310 1 (quarterExpBox i) (thetaInitialBox i n))

lemma thetaInitialBox_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (thetaInitialBox i n) (Real.exp (-lambda i n)) := by
  rw [thetaInitialBox,if_pos h]
  exact expNegative310_sound (lambdaBox_sound i n) (active_lambda_le i n h)

lemma fullInitialBox_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (fullInitialBox i n) (2*Real.exp (center i/4-lambda i n)) := by
  have he := mulDivBox_sound (by norm_num [scale310] : 0< scale310) (by decide : 0<1)
    (quarterExpBox_sound i) (thetaInitialBox_sound i n h)
  have hs := scaleBox_sound 2 he
  simpa [fullInitialBox,←Real.exp_add,sub_eq_add_neg] using hs

end CertifiedThetaPoints

end Height100Module40

/- Source module: ThetaInitialCertificate. -/
section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

noncomputable def initialValues : List (List Box) := List.ofFn (fun i : Fin 16 => List.ofFn (fullInitialBox i))

theorem _root_.CertifiedThetaPoints.initialCache_correct : CertifiedThetaPoints.initialValues = CertifiedThetaPoints.initialCache :=
  Eq.refl CertifiedThetaPoints.initialCache

lemma cachedInitial_eq (i : Fin 16) (n : Fin 8) : cachedInitial i n=fullInitialBox i n := by
  rw [cachedInitial,←initialCache_correct]
  simp only [initialValues,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos i.isLt,dif_pos n.isLt,Option.getD_some]

lemma cachedInitial_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (cachedInitial i n) (2*Real.exp (center i/4-lambda i n)) := by
  rw [cachedInitial_eq]
  exact fullInitialBox_sound i n h

end CertifiedThetaPoints

end Height100Module41

/- Source module: JetCandidate. -/
section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint

structure Candidate where
  lambdaLo : Array ℕ
  lambdaHi : Array ℕ
  g : Array ℤ
  r : Array ℕ
  f : Array ℤ
  s : Array ℕ
  deriving Repr

/-- This is only a candidate generator. Every result must separately satisfy the
kernel-checked integer enclosure and ODE residual conditions. -/
noncomputable def propose (i : Fin 16) (n : Fin 8) (N : ℕ := 184) : Candidate := Id.run do
  let lam := lambdaBox i n
  let mut l := lam.lo
  let mut u := lam.hi
  let mut ls := #[]
  let mut us := #[]
  let mut gs := #[]
  let mut rs := #[]
  for j in List.range N do
    if j>0 then
      l := 3*l/(16*j)
      u := 3*u/(16*j)+1
    ls := ls.push l
    us := us.push u
    let offset := if j=0 then scale310*(6*i.val+3)/64 else if j=1 then scale310*3/64 else 0
    gs := gs.push ((offset:ℤ)-(l:ℤ))
    rs := rs.push (u-l+1)
  let initial := cachedInitial i n
  let mut fs := #[(initial.lo:ℤ)]
  let mut ss := #[initial.hi-initial.lo]
  for j in (List.range (N-1)).map (·+1) do
    let mut v : ℤ := 0
    let mut e : ℕ := 0
    for k in (List.range j).map (·+1) do
      let g := gs[k]?.getD 0
      let r := rs[k]?.getD 0
      let f := fs[j-k]?.getD 0
      let s := ss[j-k]?.getD 0
      v := v+(k:ℤ)*g*f
      e := e+k*(g.natAbs*s+r*f.natAbs+r*s)
    let denominator := scale310*j
    let c := v/(denominator:ℤ)
    let residual := ((denominator:ℤ)*c-v).natAbs
    fs := fs.push c
    ss := ss.push ((residual+e)/denominator+1)
  return ⟨ls,us,gs,rs,fs,ss⟩

end CertifiedThetaCandidates

end Height100Module42

/- Source module: StreamingODECheck. -/
section Height100Module43

namespace CertifiedStreamingODE
open CertifiedSignedODEConvolution

lemma digit_shift (bits p j : ℕ) : digit bits (p>>>bits) j=digit bits p (j+1) := by
  unfold digit
  rw [←Nat.shiftRight_add]
  congr 2
  simp [Nat.mul_add,add_comm]

lemma tail_getD {α : Type*} (xs : List α) (j : ℕ) (d : α) :
    xs.tail.getD j d=xs.getD (j+1) d := by
  cases xs <;> simp

/-- The streaming checker verifies each coefficient inequality while consuming
each list and each packed integer exactly once. -/
theorem checkSteps_sound (bits D i n : ℕ) (fs : List ℤ) (ss : List ℕ)
    (pp pm pe pr : ℕ) (hc : checkSteps bits D i n fs ss pp pm pe pr=true) :
    ∀ j< n,
      (((i+j+1:ℕ):ℤ)*fs.getD j 0*D+(digit bits pp j:ℤ)-(digit bits pm j:ℤ)).natAbs+
        digit bits pe j+digit bits pr j≤ (i+j+1)*ss.getD j 0*D := by
  induction n generalizing i fs ss pp pm pe pr with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkSteps,Bool.and_eq_true,decide_eq_true_eq] at hc
    obtain ⟨hhead,htail⟩ := hc
    intro j hj
    cases j with
    | zero =>
      simpa only [digit,Nat.mul_zero,Nat.shiftRight_zero,Nat.add_zero,Nat.cast_add,
        Nat.cast_one,Int.natCast_emod,Nat.cast_pow,Nat.cast_ofNat,List.headD_eq_getD] using hhead
    | succ j =>
      have h := ih (i+1) fs.tail ss.tail (pp>>>bits) (pm>>>bits) (pe>>>bits) (pr>>>bits)
        htail j (by omega)
      simpa only [digit_shift,tail_getD,Nat.succ_eq_add_one,add_assoc,add_left_comm] using h

end CertifiedStreamingODE

end Height100Module43

/- Source module: JetRecordData. -/
section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE

noncomputable def makeRecord (i : Fin 16) (n : Fin 8) : Record :=
  if active i n then
    let d := propose i n
    let entries := List.ofFn (fun j : Fin 184 =>
      Entry.mk (d.lambdaLo[j.val]?.getD 0) (d.lambdaHi[j.val]?.getD 0)
        (d.g[j.val]?.getD 0) (d.r[j.val]?.getD 0)
        (d.f[j.val]?.getD 0) (d.s[j.val]?.getD 0))
    let r : Record := ⟨entries,0,0,0,0⟩
    ⟨entries, lowProduct r.ad r.fp, lowProduct r.ad r.fm,
      lowProduct r.ad r.ss, lowProduct r.rd r.fr⟩
  else ⟨[],0,0,0,0⟩

end CertifiedJetRecords

end Height100Module44

/- Source module: JetRecordCertificateNoCode. -/
section Height100Module45
namespace CertifiedJetRecords
theorem records_checked (i : Fin 16) (n : Fin 8)
    (ha : CertifiedThetaPoints.active i n) : checkRecord i n (recordAt i n)=true :=
  TaoFivePrimes.rh14to100_theta_checks i n ha
end CertifiedJetRecords
end Height100Module45

/- Source module: JetRecordCertificate. -/
section Height100Module46

end Height100Module46

/- Source module: JetInputCheck. -/
section Height100Module47

namespace CertifiedJetRecords

lemma checkInputs_head (D p limit j : ℕ) (e : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::es)=true) : entryCondition D p limit j e := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  exact of_decide_eq_true h

lemma checkInputs_tail (D p limit j : ℕ) (e : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::es)=true) : checkInputs D p limit (j+1) es=true :=
  (Bool.and_eq_true_iff.mp hc).2

lemma checkInputs_next (D p limit j : ℕ) (e f : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::f::es)=true) : nextCondition j e f := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  exact of_decide_eq_true h

theorem checkInputs_entry (D p limit j : ℕ) (es : List Entry)
    (hc : checkInputs D p limit j es=true) :
    ∀ k< es.length, entryCondition D p limit (j+k) (es.getD k zeroEntry) := by
  induction es generalizing j with
  | nil => intro k hk; simp at hk
  | cons e es ih =>
    intro k hk
    cases k with
    | zero => simpa using checkInputs_head D p limit j e es hc
    | succ k =>
      have h := ih (j+1) (checkInputs_tail D p limit j e es hc) k (by simpa using hk)
      change entryCondition D p limit (j+(k+1)) (es.getD k zeroEntry)
      simpa only [add_assoc,add_comm,add_left_comm] using h

theorem checkInputs_adjacent (D p limit j : ℕ) (es : List Entry)
    (hc : checkInputs D p limit j es=true) :
    ∀ k, k+1< es.length → nextCondition (j+k) (es.getD k zeroEntry) (es.getD (k+1) zeroEntry) := by
  induction es generalizing j with
  | nil => intro k hk; simp at hk
  | cons e es ih =>
    intro k hk
    cases k with
    | zero =>
      cases es with
      | nil => simp at hk
      | cons f es => simpa using checkInputs_next D p limit j e f es hc
    | succ k =>
      have h := ih (j+1) (checkInputs_tail D p limit j e es hc) k (by simpa using hk)
      change nextCondition (j+(k+1)) (es.getD k zeroEntry) (es.getD (k+1) zeroEntry)
      simpa only [add_assoc,add_comm,add_left_comm] using h

end CertifiedJetRecords

end Height100Module47

/- Source module: JetRecordODE. -/
section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets

noncomputable def Record.G (d : Record) (j : ℕ) : ℤ := d.gs.getD j 0
noncomputable def Record.F (d : Record) (j : ℕ) : ℤ := d.fs.getD j 0
noncomputable def Record.R (d : Record) (j : ℕ) : ℕ := d.rs.getD j 0
noncomputable def Record.S (d : Record) (j : ℕ) : ℕ := d.ss.getD j 0

theorem checkRecord_conditions (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) :
    initialCondition i n d ∧ checkInputs scale310 i.val (10^75) 0 d.entries=true ∧
    d.gs.tail.all (fun g => decide (g≤ 0))=true ∧ carryCondition d ∧ productCondition d ∧
    checkSteps bits scale310 0 (precision-1) d.fs.tail d.ss.tail d.pp d.pm d.pe d.pr=true := by
  simpa only [checkRecord,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc

theorem checked_record_ode (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j+1<184) :
    |integerResidual scale310 d.G d.F j|+integerErrorSum d.G d.F d.R d.S j ≤ 
      (j+1:ℤ)*d.S (j+1)*scale310 := by
  obtain ⟨_hi,_hin,hsign,hcarry,hprod,hstream⟩ := checkRecord_conditions i n d hc
  obtain ⟨hcp,hcm,hce,hcr⟩ := hcarry
  obtain ⟨hpp,hpm,hpe,hpr⟩ := hprod
  have hj' : j< precision-1 := by dsimp [precision]; omega
  have hlen : d.fs.length=d.ss.length := by simp [Record.fs,Record.ss]
  have hp : digit bits d.pp j=conv (absDerivative d.G) (positive d.F) j := by
    rw [hpp,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcp
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      simp only [Record.fp,positiveList_getD,positive,Record.F]
  have hm : digit bits d.pm j=conv (absDerivative d.G) (negative d.F) j := by
    rw [hpm,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcm
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      simp only [Record.fm,negativeList_getD,negative,Record.F]
  have he : digit bits d.pe j=conv (absDerivative d.G) d.S j := by
    rw [hpe,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hce
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      rfl
  have hr : digit bits d.pr j=conv (radiusDerivative d.R) (fun k => (d.F k).natAbs+d.S k) j := by
    rw [hpr,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcr
    · intro k hk
      simp only [Record.rd,radiusDerivativeList_getD,radiusDerivative,Record.R]
    · intro k hk
      simp only [Record.fr,radiusFactorList_getD _ _ hlen,Record.F,Record.S]
  have hneg : ∀ k, k≤ j → d.G (k+1)≤ 0 := by
    intro k hk
    have hh := list_all_nonpos d.gs.tail hsign k
    simpa only [CertifiedListODEVectors.getD_tail,Record.G] using hh
  apply residual_check_of_convolutions scale310 d.G d.F d.R d.S j
    (digit bits d.pp j) (digit bits d.pm j) (digit bits d.pe j) (digit bits d.pr j)
    hneg hp hm he hr
  have hh := checkSteps_sound bits scale310 0 (precision-1) d.fs.tail d.ss.tail
    d.pp d.pm d.pe d.pr hstream j hj'
  simpa only [zero_add,Nat.cast_add,Nat.cast_one,CertifiedStreamingODE.tail_getD,Record.F,Record.S] using hh

end CertifiedJetRecords

end Height100Module48

/- Source module: RationalJetIntervals. -/
section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint

lemma rationalStep_sound {S d : ℕ} (hS : 0< S) (hd : 0< d) (p : ℕ)
    {a b : Box} {x : ℝ} (ha : Contains S a x)
    (hl : b.lo*d≤ p*a.lo) (hh : p*a.hi≤ b.hi*d) :
    Contains S b ((p:ℝ)*x/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have hlr : (b.lo:ℝ)≤ (p:ℝ)*a.lo/d := by
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast hl
  have hhr : (p:ℝ)*a.hi/d≤ (b.hi:ℝ) := by
    apply (div_le_iff₀ hdr).mpr
    exact_mod_cast hh
  constructor
  · calc
      _ ≤  ((p:ℝ)*a.lo/d)/S := div_le_div_of_nonneg_right hlr hSr.le
      _ = (p:ℝ)*((a.lo:ℝ)/S)/d := by ring
      _ ≤  _ := by gcongr; exact ha.1
  · calc
      _ ≤  (p:ℝ)*((a.hi:ℝ)/S)/d := by gcongr; exact ha.2
      _ = ((p:ℝ)*a.hi/d)/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right hhr hSr.le

/-- Linear integer inequalities certify a whole normalized power jet. The
proposed boxes may be generated by any method; their construction is not trusted. -/
theorem powerJet_enclosure {S d : ℕ} (hS : 0< S) (hd : 0< d) (p N : ℕ)
    (b : ℕ → Box) (x : ℝ) (h0 : Contains S (b 0) x)
    (hstep : ∀ j, j+1< N →
      (b (j+1)).lo*(d*(j+1))≤ p*(b j).lo ∧
      p*(b j).hi≤ (b (j+1)).hi*(d*(j+1))) :
    ∀ j< N, Contains S (b j) (x*((p:ℝ)/d)^j/(j.factorial:ℝ)) := by
  intro j
  induction j with
  | zero => intro hj; simpa using h0
  | succ j ih =>
    intro hj
    have hc := hstep j hj
    have hs := rationalStep_sound hS (Nat.mul_pos hd (Nat.succ_pos j)) p
      (ih (by omega)) hc.1 hc.2
    convert hs using 1
    push_cast
    rw [Nat.factorial_succ,pow_succ]
    push_cast
    field_simp

end CertifiedFixedPoint

end Height100Module49

/- Source module: SmallThetaJet. -/
section Height100Module50

open Complex Metric Real
namespace CertifiedZetaQuadrature

noncomputable def thetaTerm (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

end CertifiedZetaQuadrature

end Height100Module50

/- Source module: FullThetaTerms. -/
section Height100Module51

open Complex Metric Finset
namespace CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

noncomputable def fullThetaTerm (n : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

lemma fullThetaTerm_factor (n : ℕ) (z : ℂ) :
    fullThetaTerm n z=2*Complex.exp (z/4)*thetaTerm n z := by
  unfold fullThetaTerm thetaTerm
  rw [show z/4-(Real.pi:ℂ)*(n+1)^2*Complex.exp z =
    z/4+(-(Real.pi:ℂ)*(n+1)^2*Complex.exp z) by ring,Complex.exp_add]
  ring

lemma fullThetaTerm_entire (n : ℕ) : Differentiable ℂ (fullThetaTerm n) := by
  unfold fullThetaTerm
  fun_prop

noncomputable def baseKernel (z : ℂ) : ℂ := ∑ n ∈ range 8, fullThetaTerm n z

lemma baseKernel_entire : Differentiable ℂ baseKernel := by
  unfold baseKernel fullThetaTerm
  fun_prop

lemma baseKernel_eq (z : ℂ) : baseKernel z=2*Complex.exp (z/4)*thetaTruncation z := by
  unfold baseKernel
  simp_rw [fullThetaTerm_factor]
  rw [← mul_sum]
  rfl

lemma globalKernelMoment_base (k : ℕ) (z : ℂ) :
    globalKernelMoment k z=((64*z)^k/(k.factorial:ℂ))*baseKernel z := by
  rw [baseKernel_eq]
  unfold globalKernelMoment
  ring

end CertifiedZetaQuadrature

end Height100Module51

/- Source module: FullThetaODE. -/
section Height100Module52

open Complex Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets

noncomputable def thetaExponent (m : ℕ) (z : ℂ) : ℂ :=
  z/4-(Real.pi:ℂ)*(m+1)^2*Complex.exp z

lemma thetaExponent_entire (m : ℕ) : Differentiable ℂ (thetaExponent m) := by
  unfold thetaExponent
  fun_prop

lemma scaled_linear_quarter (c h : ℂ) (j : ℕ) :
    scaledCoefficient (fun z : ℂ => z/4) c h j =
      if j=0 then c/4 else if j=1 then h/4 else 0 := by
  unfold scaledCoefficient coefficient
  rw [iteratedDeriv_div_const,iteratedDeriv_fun_id]
  rcases j with _|j
  · simp
  rcases j with _|j
  · simp; ring
  · simp

lemma scaled_const_exp (a c h : ℂ) (j : ℕ) :
    scaledCoefficient (fun z => a*Complex.exp z) c h j =
      a*Complex.exp c*h^j/(j.factorial:ℂ) := by
  unfold scaledCoefficient coefficient
  rw [iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate,Complex.iter_deriv_exp]
  ring

lemma thetaExponent_scaled (m j : ℕ) (c h : ℝ) :
    scaledCoefficient (thetaExponent m) c h j =
      (if j=0 then (c:ℂ)/4 else if j=1 then (h:ℂ)/4 else 0) -
        ((Real.pi*(m+1:ℝ)^2*Real.exp c:ℝ):ℂ)*(h:ℂ)^j/(j.factorial:ℂ) := by
  have hlin : Differentiable ℂ (fun z : ℂ => z/4) := by fun_prop
  have hexp : Differentiable ℂ (fun z : ℂ => (Real.pi:ℂ)*(m+1)^2*Complex.exp z) := by fun_prop
  have hsplit : scaledCoefficient (thetaExponent m) c h j =
      scaledCoefficient (fun z : ℂ => z/4) c h j-
      scaledCoefficient (fun z : ℂ => (Real.pi:ℂ)*(m+1)^2*Complex.exp z) c h j := by
    unfold scaledCoefficient thetaExponent
    rw [CertifiedComplexTaylor.coefficient_sub _ _ hlin hexp]
    ring
  rw [hsplit,scaled_linear_quarter,scaled_const_exp]
  push_cast
  ring

lemma fullThetaTerm_scaled (m : ℕ) (c h : ℂ) (j : ℕ) :
    scaledCoefficient (fullThetaTerm m) c h j =
      2*scaledCoefficient (fun z => Complex.exp (thetaExponent m z)) c h j := by
  unfold scaledCoefficient coefficient fullThetaTerm thetaExponent
  rw [iteratedDeriv_const_mul_field]
  ring

lemma fullThetaTerm_ode (m : ℕ) (c h : ℂ) (n : ℕ) :
    (n+1:ℂ)*scaledCoefficient (fullThetaTerm m) c h (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*scaledCoefficient (thetaExponent m) c h (k+1)*
        scaledCoefficient (fullThetaTerm m) c h (n-k) := by
  simp_rw [fullThetaTerm_scaled]
  have hr := scaled_exp_coefficient_recurrence (thetaExponent m) (thetaExponent_entire m) c h n
  have h2 := congrArg (fun z : ℂ => 2*z) hr
  rw [mul_sum] at h2
  convert! h2 using 1
  · ring
  · apply sum_congr rfl
    intro k _
    ring

end CertifiedZetaQuadrature

end Height100Module52

/- Source module: JetRecordEnclosure. -/
section Height100Module53

open Complex Finset
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature

noncomputable def Record.E (d : Record) (j : ℕ) : Entry := d.entries.getD j zeroEntry
noncomputable def Record.lambdaJet (d : Record) (j : ℕ) : Box := ⟨(d.E j).lo,(d.E j).hi⟩

lemma Record.E_g (d : Record) (j : ℕ) : (d.E j).g=d.G j :=
  (List.getD_map d.entries zeroEntry Entry.g).symm
lemma Record.E_r (d : Record) (j : ℕ) : (d.E j).r=d.R j :=
  (List.getD_map d.entries zeroEntry Entry.r).symm
lemma Record.E_f (d : Record) (j : ℕ) : (d.E j).f=d.F j :=
  (List.getD_map d.entries zeroEntry Entry.f).symm
lemma Record.E_s (d : Record) (j : ℕ) : (d.E j).s=d.S j :=
  (List.getD_map d.entries zeroEntry Entry.s).symm

lemma checked_record_entry (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    entryCondition scale310 i.val (10^75) j (d.E j) := by
  obtain ⟨hinit,hinputs,_⟩ := checkRecord_conditions i n d hc
  have hlen := hinit.1
  have h := checkInputs_entry scale310 i.val (10^75) 0 d.entries hinputs j (by omega)
  simpa only [zero_add,Record.E] using h

lemma checked_record_lambda (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    Contains scale310 (d.lambdaJet j) (lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ)) := by
  obtain ⟨hinit,hinputs,_⟩ := checkRecord_conditions i n d hc
  obtain ⟨hlen,hlo,hhi,_⟩ := hinit
  have hD : 0< scale310 := by norm_num [scale310]
  have hDr : (0:ℝ)< scale310 := by exact_mod_cast hD
  have hstart : Contains scale310 (d.lambdaJet 0) (lambda i n) := by
    have hl := (lambdaBox_sound i n).1
    have hh := (lambdaBox_sound i n).2
    have hel : (d.E 0).lo≤ (lambdaBox i n).lo := by
      simpa only [Record.E,←List.headD_eq_getD] using hlo
    have heh : (lambdaBox i n).hi≤ (d.E 0).hi := by
      simpa only [Record.E,←List.headD_eq_getD] using hhi
    constructor
    · exact (div_le_div_of_nonneg_right (by exact_mod_cast hel) hDr.le).trans hl
    · exact hh.trans (div_le_div_of_nonneg_right (by exact_mod_cast heh) hDr.le)
  apply powerJet_enclosure hD (by decide : 0<16) 3 184 d.lambdaJet (lambda i n) hstart _ j hj
  intro k hk
  have h := checkInputs_adjacent scale310 i.val (10^75) 0 d.entries hinputs k (by omega)
  simpa only [zero_add,Record.lambdaJet,Record.E,nextCondition] using h

noncomputable def quarterCoefficient (p j : ℕ) : ℝ :=
  if j=0 then (6*p+3)/64 else if j=1 then 3/64 else 0

lemma quotient_scaled_bounds (D m : ℕ) (hD : 0< D) :
    ((D*m/64:ℕ):ℝ)/D≤ (m:ℝ)/64 ∧
      (m:ℝ)/64≤ ((D*m/64+1:ℕ):ℝ)/D := by
  have h := quotient_bounds (D*m) 64 (by decide)
  have hDr : (0:ℝ)< D := by exact_mod_cast hD
  constructor
  · apply (div_le_iff₀ hDr).mpr
    calc
      _ ≤  ((D*m:ℕ):ℝ)/64 := h.1
      _ = _ := by push_cast; ring
  · apply (le_div_iff₀ hDr).mpr
    calc
      _ = ((D*m:ℕ):ℝ)/64 := by push_cast; ring
      _ ≤  _ := h.2

lemma offset_scaled_bounds (D p j : ℕ) (hD : 0< D) :
    (offset D p j:ℝ)/D≤ quarterCoefficient p j ∧
      quarterCoefficient p j≤ ((offset D p j:ℝ)+1)/D := by
  unfold offset quarterCoefficient
  by_cases hj0 : j=0
  · simp only [if_pos hj0]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      quotient_scaled_bounds D (6*p+3) hD
  · simp only [if_neg hj0]
    by_cases hj1 : j=1
    · simp only [if_pos hj1]
      simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using quotient_scaled_bounds D 3 hD
    · simp only [if_neg hj1,Nat.cast_zero,zero_div,zero_add]
      constructor
      · rfl
      · positivity

lemma entry_exponent_error (D p j : ℕ) (hD : 0< D) (e : Entry) (x : ℝ)
    (he : entryCondition D p (10^75) j e)
    (hx : Contains D ⟨e.lo,e.hi⟩ x) :
    |quarterCoefficient p j-x-(e.g:ℝ)/D|≤ (e.r:ℝ)/D := by
  obtain ⟨hlh,hg,hr,_⟩ := he
  have hDr : (0:ℝ)< D := by exact_mod_cast hD
  have ho := offset_scaled_bounds D p j hD
  have hwidth : (e.hi:ℝ)-(e.lo:ℝ)+1≤ e.r := by
    have h' : e.hi+1≤ e.r+e.lo := by omega
    have h'' : (e.hi:ℝ)+1≤ (e.r:ℝ)+(e.lo:ℝ) := by exact_mod_cast h'
    linarith
  have hrad : ((e.hi:ℝ)-(e.lo:ℝ)+1)/D≤ (e.r:ℝ)/D :=
    div_le_div_of_nonneg_right hwidth hDr.le
  rw [hg]
  push_cast
  rw [abs_le]
  have hpos : (0:ℝ)≤ 1/D := by positivity
  dsimp [Contains] at hx
  constructor
  · have heq : ((offset D p j:ℝ)-(e.lo:ℝ))/D=(offset D p j:ℝ)/D-(e.lo:ℝ)/D := by ring
    rw [heq]
    have hwidthEq : ((e.hi:ℝ)-(e.lo:ℝ)+1)/D=(e.hi:ℝ)/D-(e.lo:ℝ)/D+1/D := by ring
    rw [hwidthEq] at hrad
    linarith [ho.1,hx.2]
  · have heq : ((offset D p j:ℝ)-(e.lo:ℝ))/D=(offset D p j:ℝ)/D-(e.lo:ℝ)/D := by ring
    rw [heq]
    have hoff : ((offset D p j:ℝ)+1)/D=(offset D p j:ℝ)/D+1/D := by ring
    rw [hoff] at ho
    have hR1 : 1≤ e.r := by omega
    have hR1r : (1:ℝ)/D≤ e.r/D := div_le_div_of_nonneg_right (by exact_mod_cast hR1) hDr.le
    linarith [ho.2,hx.1]

lemma thetaExponent_record_formula (i : Fin 16) (n : Fin 8) (j : ℕ) :
    scaledCoefficient (thetaExponent n.val) (center i) (3/16) j=
      ((quarterCoefficient i.val j-lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ):ℝ):ℂ) := by
  have hh := thetaExponent_scaled n.val j (center i) (3/16)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hh
  rw [hh]
  unfold quarterCoefficient lambda
  push_cast
  by_cases hj0 : j=0
  · simp only [if_pos hj0]
    unfold center
    push_cast
    ring
  · simp only [if_neg hj0]
    by_cases hj1 : j=1
    · simp only [if_pos hj1]
      push_cast
      ring
    · simp only [if_neg hj1]
      push_cast
      ring

lemma checked_record_exponent (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient (thetaExponent n.val) (center i) (3/16) j-
      fixedCenter scale310 d.G j‖≤ fixedRadius scale310 d.R j := by
  have he := checked_record_entry i n d hc j hj
  have hl := checked_record_lambda i n d hc j hj
  have h := entry_exponent_error scale310 i.val j (by norm_num [scale310]) (d.E j)
    (lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ)) he hl
  rw [Record.E_g,Record.E_r] at h
  rw [thetaExponent_record_formula]
  unfold fixedCenter fixedRadius
  have heq : ((quarterCoefficient i.val j-lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ):ℝ):ℂ)-
      (d.G j:ℂ)/scale310=
      ((quarterCoefficient i.val j-lambda i n*(3/16:ℝ)^j/(j.factorial:ℝ)-
        (d.G j:ℝ)/scale310:ℝ):ℂ) := by push_cast; rfl
  rw [heq,norm_real,Real.norm_eq_abs]
  exact h

lemma contains_lower_error (D : ℕ) (hD : 0< D) (b : Box) (x : ℝ) (s : ℕ)
    (hx : Contains D b x) (hs : b.hi-b.lo≤ s) : |x-(b.lo:ℝ)/D|≤ (s:ℝ)/D := by
  have hDr : (0:ℝ)< D := by exact_mod_cast hD
  have hlh : b.lo≤ b.hi := by
    have h : (b.lo:ℝ)≤ b.hi := (div_le_div_iff_of_pos_right hDr).mp (hx.1.trans hx.2)
    exact_mod_cast h
  have hw : (b.hi:ℝ)-(b.lo:ℝ)≤ s := by
    have h' : b.hi≤ s+b.lo := by omega
    have h'' : (b.hi:ℝ)≤ (s:ℝ)+(b.lo:ℝ) := by exact_mod_cast h'
    linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  calc
    _ ≤  (b.hi:ℝ)/D-(b.lo:ℝ)/D := sub_le_sub_right hx.2 _
    _ = ((b.hi:ℝ)-(b.lo:ℝ))/D := by ring
    _ ≤  _ := div_le_div_of_nonneg_right hw hDr.le

lemma checked_record_initial (i : Fin 16) (n : Fin 8) (d : Record)
    (ha : active i n) (hc : checkRecord i n d=true) :
    ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) 0-
      fixedCenter scale310 d.F 0‖≤ fixedRadius scale310 d.S 0 := by
  obtain ⟨hinit,_⟩ := checkRecord_conditions i n d hc
  obtain ⟨_hlen,_hlo,_hhi,hf,hs⟩ := hinit
  have hf' : d.F 0=((cachedInitial i n).lo:ℤ) := by
    simpa only [←Record.E_f,Record.E,←List.headD_eq_getD] using hf
  have hs' : (cachedInitial i n).hi-(cachedInitial i n).lo≤ d.S 0 := by
    simpa only [←Record.E_s,Record.E,←List.headD_eq_getD] using hs
  have h := contains_lower_error scale310 (by norm_num [scale310]) (cachedInitial i n)
    (2*Real.exp (center i/4-lambda i n)) (d.S 0) (cachedInitial_sound i n ha) hs'
  have he : fullThetaTerm n.val (center i)=((2*Real.exp (center i/4-lambda i n):ℝ):ℂ) := by
    unfold fullThetaTerm lambda
    push_cast
    ring
  unfold scaledCoefficient coefficient
  simp only [iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,pow_zero,mul_one]
  rw [he]
  unfold fixedCenter fixedRadius
  rw [hf']
  have heq : ((2*Real.exp (center i/4-lambda i n):ℝ):ℂ)-
      (((cachedInitial i n).lo:ℤ):ℂ)/scale310=
      ((2*Real.exp (center i/4-lambda i n)-((cachedInitial i n).lo:ℝ)/scale310:ℝ):ℂ) := by
    push_cast
    rfl
  rw [heq,norm_real,Real.norm_eq_abs]
  exact h

set_option exponentiation.threshold 512 in
theorem checked_record_enclosure (i : Fin 16) (n : Fin 8) (d : Record)
    (ha : active i n) (hc : checkRecord i n d=true) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
      (d.F j:ℂ)/scale310‖≤ 1/10^235 := by
  have h := fixed_enclosure_of_recurrence
    (scaledCoefficient (thetaExponent n.val) (center i) (3/16))
    (scaledCoefficient (fullThetaTerm n.val) (center i) (3/16)) scale310
    (by norm_num [scale310]) d.G d.F d.R d.S 184
    (fullThetaTerm_ode n.val (center i) (3/16))
    (checked_record_exponent i n d hc) (checked_record_initial i n d ha hc)
    (checked_record_ode i n d hc) j hj
  change ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
    (d.F j:ℂ)/scale310‖≤ (d.S j:ℝ)/scale310 at h
  apply h.trans
  have hs := (checked_record_entry i n d hc j hj).2.2.2
  rw [Record.E_s] at hs
  calc
    _ ≤  (10^75:ℝ)/scale310 := div_le_div_of_nonneg_right (by exact_mod_cast hs) (by positivity)
    _ ≤  _ := by norm_num [scale310]

end CertifiedJetRecords

end Height100Module53

/- Source module: JetPanelStability. -/
section Height100Module54

open Complex Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

noncomputable def scalarPanel (q : ℕ → ℂ) (a c : ℂ) (h : ℝ) (N k : ℕ) : ℂ :=
  (h:ℂ) * ∑ m ∈ range (k+1),
    (if m< N then (a*(h:ℂ))^m/(m.factorial:ℂ) *
      correlation N q integrationWeight m else 0) *
        ((a*c)^(k-m)/((k-m).factorial:ℂ))

lemma integrationWeight_norm (j : ℕ) : ‖integrationWeight j‖≤ 2 := by
  unfold integrationWeight
  rw [norm_div]
  have hn : ‖(j+1:ℂ)‖=(j+1:ℝ) := by
    rw [show (j+1:ℂ)=((j+1:ℝ):ℂ) by push_cast; rfl,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [hn]
  apply (div_le_iff₀ (by positivity : (0:ℝ)< j+1)).mpr
  have hh := norm_sub_le (1:ℂ) ((-1:ℂ)^(j+1))
  norm_num only [norm_one,norm_pow,norm_neg,one_pow] at hh
  have hj : (0:ℝ)≤ j := Nat.cast_nonneg j
  linarith

lemma correlation_error (p q : ℕ → ℂ) (N : ℕ) (ε : ℝ) (hε : 0≤ ε)
    (hpq : ∀ j< N, ‖p j-q j‖≤ ε) (m : ℕ) :
    ‖correlation N p integrationWeight m-correlation N q integrationWeight m‖≤ 2*N*ε := by
  unfold correlation
  rw [←sum_sub_distrib]
  calc
    _ ≤  ∑ j ∈ range (N-m), ‖(p j-q j)*integrationWeight (m+j)‖ := by
      simpa only [sub_mul] using norm_sum_le (s:=range (N-m))
        (f:=fun j => p j*integrationWeight (m+j)-q j*integrationWeight (m+j))
    _ ≤  ∑ _j ∈ range (N-m), ε*2 := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hpq j (by have := mem_range.mp hj; omega))
        (integrationWeight_norm (m+j)) (norm_nonneg _) hε
    _ = (N-m:ℕ)*(ε*2) := by simp
    _ ≤  (N:ℝ)*(ε*2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N m) (by positivity)
    _ = _ := by ring

lemma real_power_factorial_norm (x : ℝ) (hx : 0≤ x) (n : ℕ) :
    ‖(x:ℂ)^n/(n.factorial:ℂ)‖≤ Real.exp x := by
  have he : (x:ℂ)^n/(n.factorial:ℂ)=((x^n/n.factorial:ℝ):ℂ) := by push_cast; rfl
  rw [he,norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact Real.pow_div_factorial_le_exp x hx n

end CertifiedMomentConvolution

end Height100Module54

/- Source module: SharperJetPanelStability. -/
section Height100Module55

open Complex Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

lemma exp396_bound : Real.exp 396≤ 10^172 := by
  have he : Real.exp 1≤ (27183:ℝ)/10000 := Real.exp_one_lt_d9.le.trans (by norm_num)
  rw [show Real.exp 396=(Real.exp 1)^396 by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 396]
  exact (pow_le_pow_left₀ (Real.exp_nonneg _) he 396).trans (by norm_num)

/- Summing the normalized powers removes the degree factor from the error bound. -/
lemma scalarPanel_error_sharp (p q : ℕ → ℂ) (c : ℝ) (hc0 : 0≤ c) (hc1 : c≤ 6)
    (k : ℕ) (ε : ℝ) (hε : 0≤ ε) (hpq : ∀ j<184, ‖p j-q j‖≤ ε) :
    ‖scalarPanel p 64 c (3/16) 184 k-scalarPanel q 64 c (3/16) 184 k‖≤ 10^174*ε := by
  have ha (m : ℕ) : ‖((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)‖=
      (12:ℝ)^m/(m.factorial:ℝ) := by
    have he : (64:ℂ)*((3/16:ℝ):ℂ)=12 := by norm_num
    rw [he,norm_div,norm_pow]
    norm_num
  have hc (m : ℕ) : ‖((64:ℂ)*(c:ℂ))^m/(m.factorial:ℂ)‖≤ Real.exp 384 := by
    have h := real_power_factorial_norm (64*c) (by positivity) m
    have he : ((64*c:ℝ):ℂ)=(64:ℂ)*(c:ℂ) := by push_cast; rfl
    rw [he] at h
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have hs :
      ‖∑ m ∈ range (k+1),
        (if m<184 then ((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
          (correlation 184 p integrationWeight m-correlation 184 q integrationWeight m)
        else 0)*(((64:ℂ)*(c:ℂ))^(k-m)/((k-m).factorial:ℂ))‖≤ 
      Real.exp 12*(2*184*ε)*Real.exp 384 := by
    calc
      _ ≤  ∑ m ∈ range (k+1),
          ‖(if m<184 then ((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
            (correlation 184 p integrationWeight m-correlation 184 q integrationWeight m)
          else 0)*(((64:ℂ)*(c:ℂ))^(k-m)/((k-m).factorial:ℂ))‖ := norm_sum_le _ _
      _ ≤  ∑ m ∈ range (k+1), ((12:ℝ)^m/m.factorial)*(2*184*ε)*Real.exp 384 := by
        apply sum_le_sum
        intro m _hm
        by_cases hm : m<184
        · simp only [if_pos hm,norm_mul,ha]
          exact mul_le_mul (mul_le_mul_of_nonneg_left
            (correlation_error p q 184 ε hε hpq m) (by positivity)) (hc (k-m))
              (norm_nonneg _) (by positivity)
        · simp only [if_neg hm,zero_mul,norm_zero]
          positivity
      _ = (∑ m ∈ range (k+1), (12:ℝ)^m/m.factorial)*(2*184*ε)*Real.exp 384 := by
        rw [sum_mul,sum_mul]
      _ ≤  _ := by
        gcongr
        exact Real.sum_le_exp_of_nonneg (by norm_num) (k+1)
  have hd : scalarPanel p 64 c (3/16) 184 k-scalarPanel q 64 c (3/16) 184 k=
      ((3/16:ℝ):ℂ)*∑ m ∈ range (k+1),
        (if m<184 then ((64:ℂ)*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
          (correlation 184 p integrationWeight m-correlation 184 q integrationWeight m)
        else 0)*(((64:ℂ)*(c:ℂ))^(k-m)/((k-m).factorial:ℂ)) := by
    unfold scalarPanel
    rw [←mul_sub,←sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro m _hm
    by_cases hm : m<184 <;> simp only [hm,ite_true,ite_false,zero_mul]
    · ring
    · simp
  rw [hd,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<3/16)]
  calc
    _ ≤  (3/16:ℝ)*(Real.exp 12*(2*184*ε)*Real.exp 384) := by gcongr
    _ = 69*ε*Real.exp 396 := by
      rw [show (396:ℝ)=12+384 by norm_num,Real.exp_add]
      ring
    _ ≤  69*ε*(10^172) := mul_le_mul_of_nonneg_left exp396_bound (by positivity)
    _ ≤  _ := by nlinarith [hε]

end CertifiedMomentConvolution

end Height100Module55

/- Source module: UnitDiskMomentBound. -/
section Height100Module56

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature

lemma theta_term_unit_bound (n : ℕ) (z : ℂ) (hi : |z.im|≤ 1) :
    ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ ≤ 
      Real.exp (-(3/2)*Real.exp z.re) := by
  have hc : (1/2:ℝ)≤ Real.cos z.im := by
    have h := Real.one_sub_sq_div_two_le_cos (x:=z.im)
    have hs : z.im^2≤ 1 := by
      have ha := abs_le.mp hi
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr ha.1)]
    linarith
  have hn : (1:ℝ)≤ (n+1:ℝ)^2 := by have : (0:ℝ)≤ n := Nat.cast_nonneg n; nlinarith
  have hp : (3/2:ℝ)≤ Real.pi*(n+1:ℝ)^2*Real.cos z.im := by
    have h1 : (3:ℝ)≤ Real.pi*(n+1:ℝ)^2 :=
      Real.pi_gt_three.le.trans (le_mul_of_one_le_right Real.pi_pos.le hn)
    have hm := mul_le_mul h1 hc (by norm_num : (0:ℝ)≤ 1/2)
      (by positivity : (0:ℝ)≤ Real.pi*(n+1:ℝ)^2)
    linarith
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_re,neg_re,ofReal_re,neg_im,ofReal_im,neg_zero,mul_im,
    natCast_re,natCast_im,add_re,one_re,add_im,one_im,pow_two,Complex.exp_re,Complex.exp_im]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (Real.exp_pos z.re).le]

end CertifiedZetaQuadrature

end Height100Module56

/- Source module: SharperUnitDisk84. -/
section Height100Module57

open Complex Metric Finset MeasureTheory
namespace CertifiedZetaQuadrature

lemma exp_three_ge_twenty : (20:ℝ)≤ Real.exp 3 := by
  have hbase : (2718/1000:ℝ)≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤ 2718/1000) hbase 3
  have he : Real.exp 3=(Real.exp 1)^3 := by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 3
  rw [he]
  norm_num at h ⊢
  linarith

lemma log_fortythree_le_377 : Real.log 43≤ 377/100 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<43)).mpr
  have hsmall := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤ 77/100) 5
  norm_num [Finset.sum_range_succ] at hsmall
  have hmul := mul_le_mul exp_three_ge_twenty hsmall
    (by norm_num) (Real.exp_pos 3).le
  have he : Real.exp (377/100)=Real.exp 3*Real.exp (77/100) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith

lemma exp_tangent_fortythree_fine (r : ℝ) : 43*r-11911/100≤ Real.exp r := by
  have he := Real.add_one_le_exp (r-Real.log 43)
  rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<43)] at he
  nlinarith [log_fortythree_le_377]

lemma exp_tangent_twenty (r : ℝ) (hr : 2≤ r) : 20*r-40≤ Real.exp r := by
  have he := Real.add_one_le_exp (r-3)
  have hmul := mul_le_mul exp_three_ge_twenty he (by linarith) (Real.exp_pos 3).le
  have hx : Real.exp 3*Real.exp (r-3)=Real.exp r := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hx] at hmul
  linarith

set_option exponentiation.threshold 512 in
lemma globalKernelMoment_unit_disk_84 (k : ℕ) (c : ℝ) (hc : 0≤ c) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖≤ 1) : ‖globalKernelMoment k z‖≤ 10^84 := by
  have hre : |z.re-c|≤ 1 := by
    simpa only [sub_re,ofReal_re] using (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
  have him : |z.im|≤ 1 := by
    simpa only [sub_im,ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  have hr : -(1:ℝ)≤ z.re := by linarith [(abs_le.mp hre).1]
  have himsq : z.im^2≤ 1 := by
    have hi := abs_le.mp him
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)]
  have hp : ‖(64*z)^k/(k.factorial:ℂ)‖ ≤  Real.exp (64*‖z‖) := by
    simpa [norm_div,norm_pow,norm_mul] using
      Real.pow_div_factorial_le_exp (64*‖z‖) (by positivity) k
  have ht : ‖thetaTruncation z‖≤ 8*Real.exp (-(3/2)*Real.exp z.re) := by
    calc
      _ ≤  ∑ n ∈ range 8, ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ := norm_sum_le _ _
      _ ≤  ∑ _n ∈ range 8, Real.exp (-(3/2)*Real.exp z.re) :=
        sum_le_sum (fun n _ => theta_term_unit_bound n z him)
      _ = _ := by simp
  have he : z.re/4+64*‖z‖-(3/2)*Real.exp z.re≤ 189 := by
    by_cases hr3 : 3≤ z.re
    · have hnorm : ‖z‖≤ z.re+1/6 := by
        have hs := Complex.sq_norm_sub_sq_re z
        apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0≤ z.re+1/6)).mp
        nlinarith
      have ht := exp_tangent_fortythree_fine z.re
      linarith
    · by_cases hr2 : 2≤ z.re
      · have hnorm : ‖z‖≤ z.re+1/4 := by
          have hs := Complex.sq_norm_sub_sq_re z
          apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0≤ z.re+1/4)).mp
          nlinarith
        have ht := exp_tangent_twenty z.re hr2
        linarith
      · have hrsq : z.re^2≤ 4 := by
          nlinarith [mul_nonneg (by linarith : 0≤ 2-z.re) (by linarith : 0≤ 2+z.re)]
        have hnorm : ‖z‖≤ 5/2 := by
          have hs := Complex.sq_norm_sub_sq_re z
          apply (sq_le_sq₀ (norm_nonneg z) (by norm_num : (0:ℝ)≤ 5/2)).mp
          nlinarith
        have hx := Real.exp_pos z.re
        linarith
  unfold globalKernelMoment
  simp only [norm_mul]
  rw [show ‖(2:ℂ)‖=2 by norm_num]
  calc
    _ ≤  2*Real.exp (z.re/4)*Real.exp (64*‖z‖)*(8*Real.exp (-(3/2)*Real.exp z.re)) := by
      gcongr
      rw [Complex.norm_exp]
      simp
    _ = 16*Real.exp (z.re/4+64*‖z‖-(3/2)*Real.exp z.re) := by
      rw [show z.re/4+64*‖z‖-(3/2)*Real.exp z.re =
        z.re/4+64*‖z‖+(-(3/2)*Real.exp z.re) by ring,Real.exp_add,Real.exp_add]
      ring
    _ ≤  16*Real.exp 189 := by gcongr
    _ ≤  16*(27183/10000:ℝ)^189 := by
      rw [show Real.exp 189=(Real.exp 1)^189 by
        simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 189]
      gcongr
      linarith [Real.exp_one_lt_d9]
    _ ≤  10^84 := by norm_num
end CertifiedZetaQuadrature

end Height100Module57

/- Source module: PanelQuadrature184. -/
section Height100Module58
open Complex Metric MeasureTheory
namespace CertifiedZetaQuadrature
lemma global_moment_panel_error_184 (k : ℕ) (c : ℝ) (hc : 0≤ c) :
    ‖(∫ x in -(3/16:ℝ)..(3/16:ℝ), globalKernelMoment k ((c:ℂ)+x)) -
      CertifiedTaylorQuadrature.panel (globalKernelMoment k) c (3/16) 184‖≤ 1/10^50 := by
  have hb : ∀ z ∈ sphere (c:ℂ) (1:ℝ), ‖globalKernelMoment k z‖≤ 10^84 := by
    intro z hz
    exact globalKernelMoment_unit_disk_84 k c hc z (mem_sphere_iff_norm.mp hz).le
  have he := CertifiedTaylorQuadrature.panel_error (globalKernelMoment k) (globalKernelMoment_entire k)
    c 1 (10^84) (3/16) (by norm_num) (by positivity) (by norm_num) (by norm_num) hb 184
  apply he.trans
  norm_num
end CertifiedZetaQuadrature

end Height100Module58

/- Source module: GlobalQuadratureAssembly. -/
section Height100Module59

open Complex MeasureTheory Finset
namespace CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature

noncomputable def grid (i : ℕ) : ℝ := 3*(i:ℝ)/8
noncomputable def panelCenter (i : ℕ) : ℝ := 3*(2*(i:ℝ)+1)/16
noncomputable def rule (k : ℕ) : ℂ :=
  ∑ i ∈ range 16, panel (globalKernelMoment k) (panelCenter i) (3/16) 184

lemma shifted_integral (k i : ℕ) :
    (∫ u in -(3/16:ℝ)..(3/16:ℝ), globalKernelMoment k ((panelCenter i:ℂ)+u)) =
      ∫ t in grid i..grid (i+1), globalKernelMoment k (t:ℂ) := by
  have h := intervalIntegral.integral_comp_add_left
    (fun t : ℝ => globalKernelMoment k (t:ℂ)) (a:=-(3/16:ℝ)) (b:=3/16) (panelCenter i)
  have hL : panelCenter i+(-(3/16:ℝ))=grid i := by unfold panelCenter grid; ring
  have hR : panelCenter i+(3/16:ℝ)=grid (i+1) := by unfold panelCenter grid; push_cast; ring
  simpa only [Complex.ofReal_add,hL,hR] using h

lemma integral_sum (k : ℕ) :
    (∑ i ∈ range 16, ∫ t in grid i..grid (i+1), globalKernelMoment k (t:ℂ)) =
      ∫ u in (0:ℝ)..6, globalKernelMoment k (u:ℂ) := by
  have hc : Continuous (fun t : ℝ => globalKernelMoment k (t:ℂ)) :=
    (globalKernelMoment_entire k).continuous.comp Complex.continuous_ofReal
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ:=volume) (a:=grid) (n:=16)
    (fun i _ => hc.intervalIntegrable (grid i) (grid (i+1)))
  have h0 : grid 0=0 := by norm_num [grid]
  have h16 : grid 16=6 := by norm_num [grid]
  rwa [h0,h16] at h

lemma integral_error (k : ℕ) :
    ‖(∫ u in (0:ℝ)..6, globalKernelMoment k (u:ℂ))-rule k‖≤ 16/10^50 := by
  rw [← integral_sum,rule,← sum_sub_distrib]
  calc
    _ ≤  ∑ i ∈ range 16, ‖(∫ t in grid i..grid (i+1), globalKernelMoment k (t:ℂ))-
        panel (globalKernelMoment k) (panelCenter i) (3/16) 184‖ := norm_sum_le _ _
    _ ≤  ∑ _i ∈ range 16, (1/10^50:ℝ) := by
      apply sum_le_sum
      intro i _
      rw [← shifted_integral]
      exact global_moment_panel_error_184 k (panelCenter i) (by unfold panelCenter; positivity)
    _ = _ := by simp; ring

/-- The complete analytic reduction of each true even moment to the16-panel packed rule. -/
lemma moment_rule_error (j : ℕ) :
    ‖(CertifiedGlobalMoments.moment j:ℂ)-rule (2*j)‖≤ 4/10^47 := by
  have hc := twisted_cutoff_transformed 64 0 (2*j) (by norm_num)
  rw [← CertifiedGlobalMoments.moment_complex] at hc
  have he : (fun u : ℝ => transformedMoment 64 0 (2*j) (u:ℂ)) =
      (fun u : ℝ => globalKernelMoment (2*j) (u:ℂ)) := by
    funext u
    exact transformedMoment_sixtyfour _ _
  rw [he] at hc
  have hq := integral_error (2*j)
  have hid : (CertifiedGlobalMoments.moment j:ℂ)-rule (2*j) =
      ((CertifiedGlobalMoments.moment j:ℂ)-(∫ u in (0:ℝ)..6, globalKernelMoment (2*j) (u:ℂ)))+
      ((∫ u in (0:ℝ)..6, globalKernelMoment (2*j) (u:ℂ))-rule (2*j)) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans (by linarith)

/-- A finite numerical rule enclosure at10^-47 yields the agreed10^-46 true-moment enclosure. -/
lemma coefficient_enclosure (j : ℕ) (a : ℝ)
    (hnum : ‖rule (2*j)-(a:ℂ)‖≤ 1/10^47) :
    |CertifiedGlobalMoments.moment j-a|≤ 1/10^46 := by
  have he : |CertifiedGlobalMoments.moment j-a|=‖(CertifiedGlobalMoments.moment j:ℂ)-(a:ℂ)‖ := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  have hid : (CertifiedGlobalMoments.moment j:ℂ)-(a:ℂ)=
      ((CertifiedGlobalMoments.moment j:ℂ)-rule (2*j))+(rule (2*j)-(a:ℂ)) := by ring
  rw [hid]
  have ha := moment_rule_error j
  exact (norm_add_le _ _).trans (by linarith)

end CertifiedGlobalQuadrature

end Height100Module59

/- Source module: KernelJetAssembly. -/
section Height100Module60

open Complex Finset
namespace CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature

lemma baseKernel_scaled_coefficient (c h : ℂ) (j : ℕ) :
    scaledCoefficient baseKernel c h j=
      ∑ n ∈ range 8, scaledCoefficient (fullThetaTerm n) c h j := by
  unfold scaledCoefficient coefficient baseKernel
  rw [iteratedDeriv_fun_sum (fun n _ => (fullThetaTerm_entire n).contDiff.contDiffAt)]
  rw [sum_div,sum_mul]

lemma global_moment_panel_eq (c : ℝ) (k : ℕ) :
    panel (globalKernelMoment k) c (3/16) 184=
      scalarPanel (scaledCoefficient baseKernel c (3/16)) 64 c (3/16) 184 k := by
  have he : globalKernelMoment k=(fun z => ((64*z)^k/(k.factorial:ℂ))*baseKernel z) := by
    funext z
    exact globalKernelMoment_base k z
  rw [he]
  simpa only [scalarPanel,Complex.ofReal_div,Complex.ofReal_ofNat] using
    power_moment_panel baseKernel baseKernel_entire 64 c (3/16) 184 k

lemma global_moment_panel_jet_error (c : ℝ) (hc0 : 0≤ c) (hc1 : c≤ 6)
    (q : ℕ → ℂ) (hq : ∀ j<184, ‖scaledCoefficient baseKernel c (3/16) j-q j‖≤ 1/10^234)
    (k : ℕ) (_hk : k<512) :
    ‖panel (globalKernelMoment k) c (3/16) 184-scalarPanel q 64 c (3/16) 184 k‖≤ 1/10^60 := by
  rw [global_moment_panel_eq]
  exact (scalarPanel_error_sharp _ _ c hc0 hc1 k (1/10^234) (by positivity) hq).trans_eq (by norm_num)

noncomputable def approximateRule (q : ℕ → ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ range 16, scalarPanel (q i) 64 (CertifiedGlobalQuadrature.panelCenter i) (3/16) 184 k

lemma global_rule_jet_error (q : ℕ → ℕ → ℂ)
    (hq : ∀ i<16, ∀ j<184,
      ‖scaledCoefficient baseKernel (CertifiedGlobalQuadrature.panelCenter i) (3/16) j-q i j‖
        ≤ 1/10^234) (k : ℕ) (hk : k<512) :
    ‖CertifiedGlobalQuadrature.rule k-approximateRule q k‖≤ 16/10^60 := by
  unfold CertifiedGlobalQuadrature.rule approximateRule
  rw [←sum_sub_distrib]
  calc
    _ ≤  ∑ i ∈ range 16,
      ‖panel (globalKernelMoment k) (CertifiedGlobalQuadrature.panelCenter i) (3/16) 184-
        scalarPanel (q i) 64 (CertifiedGlobalQuadrature.panelCenter i) (3/16) 184 k‖ :=
      norm_sum_le _ _
    _ ≤  ∑ _i ∈ range 16, (1/10^60:ℝ) := by
      apply sum_le_sum
      intro i hi
      have hi' : i<16 := mem_range.mp hi
      apply global_moment_panel_jet_error _ _ _ (q i) (hq i hi') k hk
      · unfold CertifiedGlobalQuadrature.panelCenter
        positivity
      · have hiR : (i:ℝ)≤ 15 := by
          have hiN : i≤ 15 := by omega
          exact_mod_cast hiN
        unfold CertifiedGlobalQuadrature.panelCenter
        linarith
    _ = _ := by simp; ring

lemma moment_enclosure_of_jet_rule (q : ℕ → ℕ → ℂ)
    (hq : ∀ i<16, ∀ j<184,
      ‖scaledCoefficient baseKernel (CertifiedGlobalQuadrature.panelCenter i) (3/16) j-q i j‖
        ≤ 1/10^234)
    (j : ℕ) (hj : j<256) (a : ℝ)
    (hnum : ‖approximateRule q (2*j)-(a:ℂ)‖≤ 1/10^62) :
    |CertifiedGlobalMoments.moment j-a|≤ 1/10^46 := by
  apply CertifiedGlobalQuadrature.coefficient_enclosure j a
  have h := global_rule_jet_error q hq (2*j) (by omega)
  have he : CertifiedGlobalQuadrature.rule (2*j)-(a:ℂ)=
      (CertifiedGlobalQuadrature.rule (2*j)-approximateRule q (2*j))+
      (approximateRule q (2*j)-(a:ℂ)) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

end CertifiedZetaQuadrature

end Height100Module60

/- Source module: FullThetaSmall800. -/
section Height100Module61

open Complex Metric Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution
set_option exponentiation.threshold 1024

lemma thetaTerm_quarter_disk_bound (n : ℕ) (c : ℝ) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖≤ 1/4) :
    ‖thetaTerm n z‖≤ Real.exp (-(18/25)*(Real.pi*(n+1:ℝ)^2*Real.exp c)) := by
  have hre : |z.re-c|≤ 1/4 := by
    simpa only [sub_re,ofReal_re] using (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
  have him : |z.im|≤ 1/4 := by
    simpa only [sub_im,ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  have hcos : (31/32:ℝ)≤ Real.cos z.im := by
    have hs : z.im^2≤ 1/16 := by
      have hi := abs_le.mp him
      nlinarith [mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)]
    linarith [Real.one_sub_sq_div_two_le_cos (x:=z.im)]
  have hexp : (3/4:ℝ)≤ Real.exp (z.re-c) := by
    have h := Real.add_one_le_exp (z.re-c)
    linarith [(abs_le.mp hre).1]
  have hprod : (18/25:ℝ)≤ Real.exp (z.re-c)*Real.cos z.im := by
    have h := mul_le_mul hexp hcos (by norm_num : (0:ℝ)≤ 31/32) (Real.exp_nonneg _)
    linarith
  have hscale := mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg c)
  have heq : Real.exp c*Real.exp (z.re-c)=Real.exp z.re := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [←mul_assoc,heq] at hscale
  have hm := mul_le_mul_of_nonneg_left hscale
    (show (0:ℝ)≤ Real.pi*(n+1:ℝ)^2 by positivity)
  rw [thetaTerm,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_re,neg_re,ofReal_re,neg_im,ofReal_im,neg_zero,mul_im,
    natCast_re,natCast_im,add_re,one_re,add_im,one_im,pow_two,Complex.exp_re,Complex.exp_im]
  nlinarith

lemma exp_neg_five_seventy_six_bound : Real.exp (-576)≤ (1/10^250:ℝ) := by
  rw [Real.exp_neg,show Real.exp (576:ℝ)=(Real.exp 1)^576 by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 576]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤ 2718/1000)
    (show (2718/1000:ℝ)≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 576
  calc
    _ ≤  ((2718/1000:ℝ)^576)⁻¹ := inv_anti₀ (by positivity) hp
    _ ≤  _ := by norm_num

lemma fullThetaTerm_quarter_small_disk (n : ℕ) (c : ℝ) (hc : c≤ 6)
    (hrate : 800≤ Real.pi*(n+1:ℝ)^2*Real.exp c) (z : ℂ) (hz : ‖z-(c:ℂ)‖≤ 1/4) :
    ‖fullThetaTerm n z‖≤ 18/10^250 := by
  have hθ : ‖thetaTerm n z‖≤ (1/10^250:ℝ) :=
    (thetaTerm_quarter_disk_bound n c z hz).trans
      ((Real.exp_le_exp.mpr (by linarith)).trans exp_neg_five_seventy_six_bound)
  have hre : z.re≤ 25/4 := by
    have h := (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
    simp only [sub_re,ofReal_re] at h
    linarith [(abs_le.mp h).2]
  have hexp : Real.exp 2≤ 9 := by
    have h := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show Real.exp 2=(Real.exp 1)^2 by
      simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 2]
    nlinarith
  have hpref : ‖2*Complex.exp (z/4)‖≤ 18 := by
    rw [norm_mul,Complex.norm_exp]
    norm_num
    have h := Real.exp_le_exp.mpr (show z.re/4≤ 2 by linarith)
    nlinarith
  rw [fullThetaTerm_factor,norm_mul]
  exact (mul_le_mul hpref hθ (norm_nonneg _) (by norm_num)).trans_eq (by ring)

lemma fullThetaTerm_small_jet_800 (n j : ℕ) (c : ℝ) (hc : c≤ 6)
    (hrate : 800≤ Real.pi*(n+1:ℝ)^2*Real.exp c) :
    ‖scaledCoefficient (fullThetaTerm n) c (3/16) j‖≤ 1/10^248 := by
  have hcoef := coefficient_bound (fullThetaTerm n) (fullThetaTerm_entire n) c (1/4) (18/10^250)
    (by norm_num) (fun z hz => fullThetaTerm_quarter_small_disk n c hc hrate z
      (mem_sphere_iff_norm.mp hz).le) j
  unfold scaledCoefficient
  rw [norm_mul,norm_pow]
  norm_num only [norm_div,Complex.norm_ofNat]
  have he : ((18/10^250:ℝ)/(1/4)^j)*(3/16)^j=(18/10^250:ℝ)*(3/4)^j := by
    rw [div_mul_eq_mul_div,mul_div_assoc,←div_pow]
    norm_num
  calc
    _ ≤  ((18/10^250)/(1/4)^j)*(3/16)^j := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (18/10^250:ℝ)*(3/4)^j := he
    _ ≤  (18/10^250:ℝ)*1 := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
    _ ≤  _ := by norm_num

end CertifiedZetaQuadrature

end Height100Module61

/- Source module: GlobalJetCenters. -/
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

lemma addLists_getD (xs ys : List ℤ) (j : ℕ) :
    (addLists xs ys).getD j 0=xs.getD j 0+ys.getD j 0 := by
  induction xs generalizing ys j with
  | nil => simp [addLists]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists]
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j => exact ih ys j

lemma sumLists_getD (rows : List (List ℤ)) (j : ℕ) :
    (sumLists rows).getD j 0=(rows.map (fun xs => xs.getD j 0)).sum := by
  induction rows with
  | nil => rfl
  | cons xs rows ih =>
    simp only [sumLists,List.map_cons,List.sum_cons]
    rw [addLists_getD,ih]

lemma centerNumerators_getD (i : Fin 16) (j : ℕ) :
    (centerNumerators i).getD j 0=∑ n : Fin 8, (recordAt i n).F j := by
  unfold centerNumerators
  rw [addLists_getD]
  have hz : (List.replicate 184 (0 : ℤ)).getD j 0 = 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]
  rw [hz, zero_add]
  rw [sumLists_getD,List.map_ofFn,List.sum_ofFn]
  rfl

noncomputable def baseCenter (i : Fin 16) (j : ℕ) : ℂ :=
  ((centerNumerators i).getD j 0:ℂ)/scale310

lemma baseCenter_eq_sum (i : Fin 16) (j : ℕ) :
    baseCenter i j=∑ n : Fin 8, ((recordAt i n).F j:ℂ)/scale310 := by
  rw [baseCenter,centerNumerators_getD,Int.cast_sum,Finset.sum_div]

theorem inactive_empty : ∀ i : Fin 16, ∀ n : Fin 8,
    ¬active i n → (recordAt i n).fs=[] := by decide +kernel

lemma center_le_six (i : Fin 16) : center i≤ 6 := by
  have hi : (i.val:ℝ)≤ 15 := by
    have hn : i.val≤ 15 := by omega
    exact_mod_cast hn
  unfold center
  linarith

lemma term_error (i : Fin 16) (n : Fin 8) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
      ((recordAt i n).F j:ℂ)/scale310‖≤ 1/10^235 := by
  by_cases ha : active i n
  · exact checked_record_enclosure i n (recordAt i n) ha (records_checked i n ha) j hj
  · have hzero : (recordAt i n).F j=0 := by
      simp [Record.F,inactive_empty i n ha]
    rw [hzero,Int.cast_zero,zero_div,sub_zero]
    have hsmall := fullThetaTerm_small_jet_800 n.val j (center i) (center_le_six i)
      (by simpa [lambda] using inactive_lambda_ge i n ha)
    exact hsmall.trans (by norm_num)

lemma base_error (i : Fin 16) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient baseKernel (center i) (3/16) j-baseCenter i j‖≤ 1/10^234 := by
  rw [baseKernel_scaled_coefficient,Finset.sum_range,baseCenter_eq_sum,←sum_sub_distrib]
  calc
    _ ≤  ∑ n : Fin 8, ‖scaledCoefficient (fullThetaTerm n.val) (center i) (3/16) j-
        ((recordAt i n).F j:ℂ)/scale310‖ := norm_sum_le _ _
    _ ≤  ∑ _n : Fin 8, (1/10^235:ℝ) := sum_le_sum (fun n _ => term_error i n j hj)
    _ ≤  _ := by norm_num

noncomputable def centers (i : ℕ) : List ℤ := if hi : i<16 then centerNumerators ⟨i,hi⟩ else []
noncomputable def jet (i j : ℕ) : ℂ := (centers i |>.getD j 0 : ℂ)/scale310

lemma center_eq_panelCenter (i : Fin 16) : center i=CertifiedGlobalQuadrature.panelCenter i.val := by
  unfold center CertifiedGlobalQuadrature.panelCenter
  ring

lemma jet_error (i : ℕ) (hi : i<16) (j : ℕ) (hj : j<184) :
    ‖scaledCoefficient baseKernel (CertifiedGlobalQuadrature.panelCenter i) (3/16) j-jet i j‖≤ 1/10^234 := by
  have h := base_error ⟨i,hi⟩ j hj
  simpa only [center_eq_panelCenter,jet,centers,dif_pos hi,baseCenter] using h

end CertifiedGlobalJetCenters

end Height100Module62

/- Source module: PackedCorrelation. -/
section Height100Module63

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedPackedCorrelation
open CertifiedSignedODEConvolution CertifiedListODEVectors CertifiedPackedConvolution

noncomputable def correlation (N : ℕ) (h w : List ℕ) (m : ℕ) : ℕ :=
  ∑ l ∈ range (N-m), h.getD l 0*w.getD (m+l) 0

lemma reversed_convolution (N : ℕ) (h w : List ℕ)
    (hh : h.length=N) (hw : w.length=N) (m : ℕ) (hm : m< N) :
    (∑ k ∈ range (N-1+m+1), h.reverse.getD k 0*w.getD (N-1+m-k) 0) =
      correlation N h w m := by
  have hshort : (∑ k ∈ range (N-1+m+1), h.reverse.getD k 0*w.getD (N-1+m-k) 0) =
      ∑ k ∈ range N, h.reverse.getD k 0*w.getD (N-1+m-k) 0 := by
    symm
    apply sum_subset (range_mono (by omega))
    intro k hk hkn
    have hn : N≤ k := by simpa using hkn
    rw [List.getD_eq_default _ _ (by simpa [hh] using hn),zero_mul]
  rw [hshort]
  calc
    _ = ∑ k ∈ range N, h.getD (N-1-k) 0*w.getD (m+(N-1-k)) 0 := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      rw [List.getD_reverse k (by omega)]
      simp only [hh]
      congr 2
      omega
    _ = ∑ k ∈ range N, h.getD k 0*w.getD (m+k) 0 :=
      sum_range_reflect (fun k => h.getD k 0*w.getD (m+k) 0) N
    _ = correlation N h w m := by
      symm
      apply sum_subset (range_mono (by omega))
      intro k hk hkn
      have hn : N-m≤ k := by simpa using hkn
      rw [List.getD_eq_default w 0 (by omega),mul_zero]

lemma packed_correlation (bits N : ℕ) (h w : List ℕ)
    (hh : h.length=N) (hw : w.length=N) (m : ℕ) (hm : m< N)
    (hc : h.reverse.sum*w.sum<2^bits) :
    digit bits (encode bits h.reverse*encode bits w) (N-1+m)=correlation N h w m := by
  rw [digit,shiftRight_product_digit bits h.reverse w hc]
  exact reversed_convolution N h w hh hw m hm

noncomputable def signedCorrelation (N : ℕ) (h : List ℤ) (w : List ℕ) (m : ℕ) : ℤ :=
  ∑ l ∈ range (N-m), h.getD l 0*(w.getD (m+l) 0:ℤ)

lemma signedCorrelation_split (N : ℕ) (h : List ℤ) (w : List ℕ) (m : ℕ) :
    signedCorrelation N h w m = (correlation N (positiveList h) w m:ℤ)-
      (correlation N (negativeList h) w m:ℤ) := by
  unfold signedCorrelation correlation
  push_cast
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro l hl
  rw [positiveList_getD,negativeList_getD,←sub_mul,Int.toNat_sub_toNat_neg]

/-- Fixed-window correlation for arbitrary nonnegative weight lists, useful for
packing several independent matrix rows into one multiplication. -/
lemma reversed_window (N : ℕ) (h w : List ℕ) (hh : h.length=N) (hN : 0< N) (m : ℕ) :
    (∑ k ∈ range (N-1+m+1), h.reverse.getD k 0*w.getD (N-1+m-k) 0) =
      ∑ k ∈ range N, h.getD k 0*w.getD (m+k) 0 := by
  have hshort : (∑ k ∈ range (N-1+m+1), h.reverse.getD k 0*w.getD (N-1+m-k) 0) =
      ∑ k ∈ range N, h.reverse.getD k 0*w.getD (N-1+m-k) 0 := by
    symm
    apply sum_subset (range_mono (by omega))
    intro k hk hkn
    have hn : N≤ k := by simpa using hkn
    rw [List.getD_eq_default _ _ (by simpa [hh] using hn),zero_mul]
  rw [hshort]
  calc
    _ = ∑ k ∈ range N, h.getD (N-1-k) 0*w.getD (m+(N-1-k)) 0 := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      rw [List.getD_reverse k (by omega)]
      simp only [hh]
      congr 2
      omega
    _ = _ := sum_range_reflect (fun k => h.getD k 0*w.getD (m+k) 0) N

lemma packed_window (bits N : ℕ) (h w : List ℕ) (hh : h.length=N) (hN : 0< N)
    (m : ℕ) (hc : h.reverse.sum*w.sum<2^bits) :
    digit bits (encode bits h.reverse*encode bits w) (N-1+m)=
      ∑ k ∈ range N, h.getD k 0*w.getD (m+k) 0 := by
  rw [digit,shiftRight_product_digit bits h.reverse w hc]
  exact reversed_window N h w hh hN m

end CertifiedPackedCorrelation

end Height100Module63

/- Source module: MomentWeights. -/
section Height100Module64

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentWeights
open CertifiedMomentConvolution

lemma denominator_pos : 0< denominator := by decide
lemma denominator_divisible : ∀ j : Fin 184, j.val+1 ∣ denominator := by decide +kernel

lemma weights_getD (j : ℕ) (hj : j<184) : weights.getD j 0=weight j := by
  simp only [weights,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hj,Option.getD_some]
lemma weights_length : weights.length=184 := by simp [weights]

lemma integrationWeight_eq (j : ℕ) :
    integrationWeight j=if j%2=0 then 2/(j+1:ℂ) else 0 := by
  unfold integrationWeight
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases h : j%2=0
  · have hh : (j+1)%2=1 := by omega
    simp [hh,h]
    ring
  · have hh : (j+1)%2=0 := by omega
    simp [hh,h]

lemma weight_scaled (j : ℕ) (hj : j<184) :
    (weight j:ℂ)/(denominator:ℂ)=integrationWeight j := by
  have hd := denominator_divisible ⟨j,hj⟩
  have hD : (denominator:ℂ)≠0 := by exact_mod_cast denominator_pos.ne'
  have hj0 : ((j+1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [integrationWeight_eq,weight]
  by_cases h : j%2=0
  · rw [if_pos h,if_pos h,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_div hd hj0]
    push_cast
    field_simp
  · simp [h]

lemma weights_scaled (j : ℕ) (hj : j<184) :
    (weights.getD j 0:ℂ)/(denominator:ℂ)=integrationWeight j := by
  rw [weights_getD j hj]
  exact weight_scaled j hj

end CertifiedMomentWeights

end Height100Module64

/- Source module: ExponentialIntegerSequence. -/
section Height100Module65

namespace CertifiedExponentialIntegerSequence

lemma factorial_ratio_step (K j : ℕ) (hj : j< K) :
    K.factorial/j.factorial=(j+1)*(K.factorial/(j+1).factorial) := by
  apply Nat.div_eq_of_eq_mul_right (Nat.factorial_pos j)
  have hd := Nat.factorial_dvd_factorial (show j+1≤ K by omega)
  have he := Nat.div_mul_cancel hd
  rw [Nat.factorial_succ] at he
  calc
    _ = (K.factorial/(j+1).factorial)*((j+1)*j.factorial) := by
      simpa only [Nat.factorial_succ] using he.symm
    _ = _ := by ring

lemma sequence_step (a K j : ℕ) (hj : j< K) :
    ((K.factorial/j.factorial)*a^j*a)/(j+1)=
      (K.factorial/(j+1).factorial)*a^(j+1) := by
  rw [factorial_ratio_step K j hj]
  apply Nat.div_eq_of_eq_mul_right (by omega)
  rw [pow_succ]
  ring

lemma expSeq_getD_aux (a K n j : ℕ) (h : j+n≤ K+1) (k : ℕ) (hk : k< n) :
    (expSeq a n j ((K.factorial/j.factorial)*a^j)).getD k 0=
      (K.factorial/(j+k).factorial)*a^(j+k) := by
  induction n generalizing j k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [expSeq]
    | succ k =>
      simp only [expSeq,List.getD_cons_succ]
      rw [sequence_step a K j (by omega)]
      have hh := ih (j+1) (by omega) k (by omega)
      simpa only [Nat.succ_eq_add_one,add_assoc,add_comm,add_left_comm] using hh

theorem expSeq_getD (a K n k : ℕ) (hn : n≤ K+1) (hk : k< n) :
    (expSeq a n 0 K.factorial).getD k 0=(K.factorial/k.factorial)*a^k := by
  simpa only [Nat.factorial_zero,Nat.div_one,pow_zero,mul_one,zero_add] using
    expSeq_getD_aux a K n 0 (by omega) k hk

theorem expSeq_real (a K n k : ℕ) (hn : n≤ K+1) (hk : k< n) :
    (((expSeq a n 0 K.factorial).getD k 0:ℕ):ℝ)/(K.factorial:ℝ)=
      (a:ℝ)^k/(k.factorial:ℝ) := by
  rw [expSeq_getD a K n k hn hk]
  have hdiv := Nat.factorial_dvd_factorial (show k≤ K by omega)
  have hK : (K.factorial:ℝ)≠0 := by exact_mod_cast K.factorial_ne_zero
  have hkf : (k.factorial:ℝ)≠0 := by exact_mod_cast k.factorial_ne_zero
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_div hdiv hkf]
  field_simp

lemma expSeq_length (a n j e : ℕ) : (expSeq a n j e).length=n := by
  induction n generalizing j e with
  | zero => rfl
  | succ n ih => simp [expSeq,ih]

end CertifiedExponentialIntegerSequence

end Height100Module65

/- Source module: MomentConvolutionModel. -/
section Height100Module66

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Finset
open scoped BigOperators
namespace CertifiedMomentArithmetic
open CertifiedFixedPoint CertifiedExponentialIntegerSequence
open CertifiedMomentConvolution

noncomputable def convolutionNumerator (C : List ℤ) (E : List ℕ) (k : ℕ) : ℤ :=
  ∑ m ∈ range (k+1), C.getD m 0*(E.getD (k-m) 0:ℤ)

lemma expSeq_complex (a K n k : ℕ) (hn : n≤ K+1) (hk : k< n) :
    (expSeq a n 0 K.factorial |>.getD k 0 : ℂ)/(K.factorial:ℂ)=
      (a:ℂ)^k/(k.factorial:ℂ) := by
  have h := congrArg (fun x : ℝ => (x:ℂ)) (expSeq_real a K n k hn hk)
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_pow] using h

lemma zipMul_getD (xs : List ℤ) (ys : List ℕ) (j : ℕ) :
    (List.zipWith (fun b e => b*(e:ℤ)) xs ys).getD j 0=xs.getD j 0*(ys.getD j 0:ℤ) := by
  induction xs generalizing ys j with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j => exact ih ys j

lemma scaledCorrelations_getD (B : List ℤ) (j : ℕ) :
    (scaledCorrelations B).getD j 0=B.getD j 0*(qSequence.getD j 0:ℤ) :=
  zipMul_getD B qSequence j

lemma correlation_scaled (H : List ℤ) (m : ℕ) (hm : m<184) :
    CertifiedMomentConvolution.correlation 184
      (fun j => (H.getD j 0:ℂ)/scale310) integrationWeight m =
      (CertifiedPackedCorrelation.signedCorrelation 184 H CertifiedMomentWeights.weights m:ℂ)/
        ((scale310:ℂ)*CertifiedMomentWeights.denominator) := by
  unfold CertifiedMomentConvolution.correlation CertifiedPackedCorrelation.signedCorrelation
  rw [Int.cast_sum,Finset.sum_div]
  apply sum_congr rfl
  intro j hj
  have hidx : m+j<184 := by have := mem_range.mp hj; omega
  rw [←CertifiedMomentWeights.weights_scaled (m+j) hidx]
  push_cast
  ring

lemma momentDenominator_pos : 0< momentDenominator := by
  unfold momentDenominator
  have hs : 0< scale310 := by norm_num [scale310]
  have hl := CertifiedMomentWeights.denominator_pos
  positivity

/-- The scalar quadrature panel is exactly an integer convolution divided by one
common positive denominator. No rounded arithmetic appears in this identity. -/
theorem scalarPanel_integer (H B : List ℤ) (hBlen : B.length=184)
    (hB : ∀ m<184, B.getD m 0=CertifiedPackedCorrelation.signedCorrelation 184 H
      CertifiedMomentWeights.weights m)
    (p : ℕ) (c : ℝ) (hpc : 64*c=p) (k : ℕ) (hk : k<512) :
    scalarPanel (fun j => (H.getD j 0:ℂ)/scale310) 64 c (3/16) 184 k =
      3*(convolutionNumerator (scaledCorrelations B) (centerSequence p) k:ℂ)/momentDenominator := by
  have hS : (scale310:ℂ)≠0 := by exact_mod_cast (by norm_num [scale310] : scale310≠0)
  have hL : (CertifiedMomentWeights.denominator:ℂ)≠0 := by
    exact_mod_cast CertifiedMomentWeights.denominator_pos.ne'
  have h208 : (Nat.factorial 184:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero 184
  have h512 : (Nat.factorial 512:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero 512
  have hpc' : (64:ℂ)*(c:ℂ)=(p:ℂ) := by exact_mod_cast hpc
  have hq : (64:ℂ)*((3/16:ℝ):ℂ)=12 := by norm_num
  have hterm (m : ℕ) (hmk : m∈range (k+1)) :
      (if m<184 then (64*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
        CertifiedMomentConvolution.correlation 184 (fun j => (H.getD j 0:ℂ)/scale310)
          integrationWeight m else 0)*
        ((64*(c:ℂ))^(k-m)/((k-m).factorial:ℂ)) =
      ((scaledCorrelations B).getD m 0:ℂ)*(centerSequence p |>.getD (k-m) 0:ℂ)/
        ((scale310:ℂ)*CertifiedMomentWeights.denominator*(Nat.factorial 184)*(Nat.factorial 512)) := by
    have hmle : m≤ k := by simpa using mem_range.mp hmk
    by_cases hm : m<184
    · rw [if_pos hm,hq,hpc',correlation_scaled H m hm,←hB m hm,
        scaledCorrelations_getD]
      have hQ := expSeq_complex 12 184 184 m (by decide) hm
      have hE := expSeq_complex p 512 512 (k-m) (by decide) (by omega)
      have hQeq : (qSequence.getD m 0:ℂ)=(12^m/(m.factorial:ℂ))*(Nat.factorial 184) :=
        (div_eq_iff h208).mp hQ
      have hEeq : (centerSequence p |>.getD (k-m) 0:ℂ)=
          ((p:ℂ)^(k-m)/((k-m).factorial:ℂ))*(Nat.factorial 512) :=
        (div_eq_iff h512).mp hE
      simp only [Int.cast_mul,Int.cast_natCast]
      rw [hQeq,hEeq]
      have hm0 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
      have hk0 : ((k-m).factorial:ℂ)≠0 := by exact_mod_cast (k-m).factorial_ne_zero
      field_simp
    · rw [if_neg hm,zero_mul,scaledCorrelations_getD,
        List.getD_eq_default B 0 (by omega)]
      simp only [zero_mul,Int.cast_zero,zero_div]
  unfold scalarPanel
  have hsum : (∑ m ∈ range (k+1),
      (if m<184 then (64*((3/16:ℝ):ℂ))^m/(m.factorial:ℂ)*
        CertifiedMomentConvolution.correlation 184 (fun j => (H.getD j 0:ℂ)/scale310)
          integrationWeight m else 0)*((64*(c:ℂ))^(k-m)/((k-m).factorial:ℂ))) =
      (convolutionNumerator (scaledCorrelations B) (centerSequence p) k:ℂ)/
        ((scale310:ℂ)*CertifiedMomentWeights.denominator*(Nat.factorial 184)*(Nat.factorial 512)) := by
    rw [convolutionNumerator,Int.cast_sum,Finset.sum_div]
    apply sum_congr rfl
    intro m hm
    simpa only [Int.cast_mul,Int.cast_natCast] using hterm m hm
  rw [hsum]
  simp only [momentDenominator,Nat.cast_mul,Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

lemma convolutionNumerator_split (C : List ℤ) (E : List ℕ) (k : ℕ) :
    convolutionNumerator C E k =
      ((∑ m ∈ range (k+1), (CertifiedListODEVectors.positiveList C).getD m 0*E.getD (k-m) 0:ℕ):ℤ) -
      ((∑ m ∈ range (k+1), (CertifiedListODEVectors.negativeList C).getD m 0*E.getD (k-m) 0:ℕ):ℤ) := by
  unfold convolutionNumerator
  push_cast
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [CertifiedListODEVectors.positiveList_getD,CertifiedListODEVectors.negativeList_getD,
    ←sub_mul,Int.toNat_sub_toNat_neg]

end CertifiedMomentArithmetic

end Height100Module66

/- Source module: ExtractPackedDigits. -/
section Height100Module67

set_option autoImplicit false
namespace CertifiedPackedExtraction
open CertifiedSignedODEConvolution

lemma digit_shift_by (bits p offset j : ℕ) :
    digit bits (p >>> (bits*offset)) j=digit bits p (offset+j) := by
  unfold digit
  rw [←Nat.shiftRight_add,Nat.mul_add]

lemma extract_length (bits step n p q : ℕ) : (extract bits step n p q).length=n := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih => simp [extract,ih]

lemma extract_getD (bits step n p q j : ℕ) (hj : j< n) :
    (extract bits step n p q).getD j 0=
      (digit bits p (step*j):ℤ)-(digit bits q (step*j):ℤ) := by
  induction n generalizing p q j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      simp [extract,digit,Nat.shiftLeft_eq',Nat.shiftLeft_eq,Nat.and_two_pow_sub_one_eq_mod]
    | succ j =>
      rw [extract,List.getD_cons_succ,ih _ _ j (by omega),digit_shift_by,digit_shift_by]
      rw [show step+step*j=step*(j+1) by ring]

end CertifiedPackedExtraction

end Height100Module67

/- Source module: MomentRecordData. -/
section Height100Module68

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentRecords
open CertifiedGlobalJetCenters CertifiedThetaCandidates CertifiedThetaPoints
open CertifiedJetRecords CertifiedFixedPoint CertifiedPackedConvolution
open CertifiedMomentArithmetic CertifiedListODEVectors CertifiedPackedExtraction

noncomputable def proposedCenters (i : Fin 16) : List ℤ :=
  addLists (List.replicate 184 0)
    (sumLists (List.ofFn (fun n : Fin 8 =>
      if active i n then (propose i n).f.toList else [])))

noncomputable def makeRecord (i : Fin 16) : Record :=
  let h := proposedCenters i
  let cp := correlationProduct (positiveList h)
  let cm := correlationProduct (negativeList h)
  let b := extract correlationBits 1 184
    (cp >>> (correlationBits*183)) (cm >>> (correlationBits*183))
  let c := scaledCorrelations b
  let pp := momentProduct (positiveList c) (panelParameter i)
  let pm := momentProduct (negativeList c) (panelParameter i)
  let z := extract momentBits 2 256 pp pm
  ⟨h,b,z,cp,cm,pp,pm⟩

noncomputable def momentCarry (i : Fin 16) (d : Record) : Prop :=
  (positiveList (scaledCorrelations d.b)).sum*(centerSequence (panelParameter i)).sum<2^momentBits ∧
  (negativeList (scaledCorrelations d.b)).sum*(centerSequence (panelParameter i)).sum<2^momentBits
noncomputable instance (i : Fin 16) (d : Record) : Decidable (momentCarry i d) := inferInstanceAs (Decidable (_∧_))

noncomputable def checkRecord (i : Fin 16) (d : Record) : Bool :=
  decide (initialCondition d) && decide (d.h=centerNumerators i) &&
  decide (correlationCarry d) &&
  decide (d.cp=correlationProduct (positiveList d.h)) &&
  decide (d.cm=correlationProduct (negativeList d.h)) &&
  decide (d.b=extract correlationBits 1 184
    (d.cp >>> (correlationBits*183)) (d.cm >>> (correlationBits*183))) &&
  decide (momentCarry i d) &&
  decide (d.pp=momentProduct (positiveList (scaledCorrelations d.b)) (panelParameter i)) &&
  decide (d.pm=momentProduct (negativeList (scaledCorrelations d.b)) (panelParameter i)) &&
  decide (d.z=extract momentBits 2 256 d.pp d.pm)

end CertifiedMomentRecords

end Height100Module68

/- Source module: ExponentialSequenceCheck. -/
section Height100Module69

namespace CertifiedExponentialSequenceCheck
open CertifiedExponentialIntegerSequence

lemma checkSteps_adjacent (a j : ℕ) (xs : List ℕ) (h : checkSteps a j xs=true) :
    ∀ k, k+1< xs.length → (j+k+1)*xs.getD (k+1) 0=a*xs.getD k 0 := by
  induction xs generalizing j with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    have hh := Bool.and_eq_true_iff.mp h
    intro k hk
    cases k with
    | zero =>
      cases xs with
      | nil => simp at hk
      | cons y ys => simpa using of_decide_eq_true hh.1
    | succ k =>
      have hi := ih (j+1) hh.2 k (by simpa using hk)
      change (j+(k+1)+1)*xs.getD (k+1) 0=a*xs.getD k 0
      simpa only [add_assoc,add_comm,add_left_comm] using hi

theorem checked_sequence_getD (a K : ℕ) (xs : List ℕ)
    (hlen : xs.length=K+1) (h0 : xs.headD 0=K.factorial)
    (hcheck : checkSteps a 0 xs=true) (j : ℕ) (hj : j≤ K) :
    xs.getD j 0=(K.factorial/j.factorial)*a^j := by
  induction j with
  | zero => simpa only [List.headD_eq_getD,Nat.factorial_zero,Nat.div_one,pow_zero,mul_one] using h0
  | succ j ih =>
    have he := checkSteps_adjacent a 0 xs hcheck j (by omega)
    simp only [zero_add] at he
    have hjK : j< K := by omega
    have hi := ih (by omega)
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos j)
    calc
      (j+1)*xs.getD (j+1) 0 = a*xs.getD j 0 := he
      _ = a*((K.factorial/j.factorial)*a^j) := by rw [hi]
      _ = (j+1)*((K.factorial/(j+1).factorial)*a^(j+1)) := by
        rw [factorial_ratio_step K j hjK,pow_succ]
        ring

theorem checked_sequence_real (a K : ℕ) (xs : List ℕ)
    (hlen : xs.length=K+1) (h0 : xs.headD 0=K.factorial)
    (hcheck : checkSteps a 0 xs=true) (j : ℕ) (hj : j≤ K) :
    (xs.getD j 0:ℝ)/(K.factorial:ℝ)=(a:ℝ)^j/(j.factorial:ℝ) := by
  rw [checked_sequence_getD a K xs hlen h0 hcheck j hj]
  have hd := Nat.factorial_dvd_factorial hj
  have hK : (K.factorial:ℝ)≠0 := by exact_mod_cast K.factorial_ne_zero
  have hjf : (j.factorial:ℝ)≠0 := by exact_mod_cast j.factorial_ne_zero
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_div hd hjf]
  field_simp

end CertifiedExponentialSequenceCheck

end Height100Module69

/- Source module: PackedExponentialSequenceCheck. -/
section Height100Module70

namespace CertifiedPackedExponentialSequence
open CertifiedPackedConvolution CertifiedExponentialSequenceCheck

noncomputable def maskDigit (bits p : ℕ) : ℕ := p &&& ((Nat.shiftLeft 1 bits)-1)
lemma maskDigit_eq_mod (bits p : ℕ) : maskDigit bits p=p%2^bits := by
  simp only [maskDigit,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,Nat.and_two_pow_sub_one_eq_mod]

/- The Nat match forces the packed value before its next shift. -/
noncomputable def decode (bits : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | n+1,0 => 0::decode bits n 0
  | n+1,p+1 => (maskDigit bits (p+1))::decode bits n ((p+1)>>>bits)

lemma decode_succ (bits n p : ℕ) :
    decode bits (n+1) p=(p%2^bits)::decode bits n (p>>>bits) := by
  cases p <;> simp [decode,maskDigit_eq_mod]

lemma decode_length (bits n p : ℕ) : (decode bits n p).length=n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [decode_succ,List.length_cons,ih]

lemma decode_getD (bits n p j : ℕ) (hj : j< n) :
    (decode bits n p).getD j 0=(p>>>(bits*j))%2^bits := by
  induction n generalizing p j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [decode_succ]
    | succ j =>
      rw [decode_succ,List.getD_cons_succ,ih _ _ (by omega)]
      simp only [←Nat.shiftRight_add,Nat.mul_add,Nat.mul_one,add_comm]

noncomputable def checkSteps (bits a bound : ℕ) : ℕ → ℕ → ℕ → Bool
  | _,0,p => decide (p=0)
  | j,n+1,0 => checkSteps bits a bound (j+1) n 0
  | j,n+1,p+1 =>
    let current := p+1
    let tail := current>>>bits
    let digit := maskDigit bits current
    decide (digit≤ bound) &&
      (if n=0 then true else decide ((j+1)*(maskDigit bits tail)=a*digit)) &&
      checkSteps bits a bound (j+1) n tail

lemma check_succ (bits a bound j n p : ℕ) :
    checkSteps bits a bound j (n+1) p=
      (decide (p%2^bits≤ bound) &&
        (if n=0 then true else decide ((j+1)*((p>>>bits)%2^bits)=a*(p%2^bits))) &&
        checkSteps bits a bound (j+1) n (p>>>bits)) := by
  cases p <;> simp [checkSteps,maskDigit_eq_mod]

lemma check_tail (bits a bound j n p : ℕ) (h : checkSteps bits a bound j (n+1) p=true) :
    checkSteps bits a bound (j+1) n (p>>>bits)=true := by
  rw [check_succ] at h
  exact (Bool.and_eq_true_iff.mp h).2

lemma check_digit (bits a bound j n p : ℕ) (h : checkSteps bits a bound j (n+1) p=true) :
    p%2^bits≤ bound := by
  rw [check_succ] at h
  exact of_decide_eq_true ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1)

lemma check_next (bits a bound j n p : ℕ) (hn : n≠0)
    (h : checkSteps bits a bound j (n+1) p=true) :
    (j+1)*((p>>>bits)%2^bits)=a*(p%2^bits) := by
  rw [check_succ] at h
  have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  rw [if_neg hn] at hh
  exact of_decide_eq_true hh

lemma check_high_zero (bits a bound j n p : ℕ) (h : checkSteps bits a bound j n p=true) :
    p>>>(bits*n)=0 := by
  induction n generalizing j p with
  | zero => simpa [checkSteps] using h
  | succ n ih =>
    have hh := ih (j+1) (p>>>bits) (check_tail bits a bound j n p h)
    simpa only [←Nat.shiftRight_add,Nat.mul_add,Nat.mul_one,add_comm] using hh

lemma check_sum_bound (bits a bound j n p : ℕ) (h : checkSteps bits a bound j n p=true) :
    (decode bits n p).sum≤ n*bound := by
  induction n generalizing j p with
  | zero => simp [decode]
  | succ n ih =>
    have hh := ih (j+1) (p>>>bits) (check_tail bits a bound j n p h)
    have hd := check_digit bits a bound j n p h
    rw [decode_succ,List.sum_cons,Nat.succ_mul]
    omega

lemma check_list (bits a bound j n p : ℕ) (h : checkSteps bits a bound j n p=true) :
    CertifiedExponentialSequenceCheck.checkSteps a j (decode bits n p)=true := by
  induction n generalizing j p with
  | zero => rfl
  | succ n ih =>
    have hh := ih (j+1) (p>>>bits) (check_tail bits a bound j n p h)
    rw [decode_succ,CertifiedExponentialSequenceCheck.checkSteps.eq_def]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_,hh⟩
    cases n with
    | zero => rfl
    | succ n =>
      rw [decode_succ]
      simpa only [decide_eq_true_eq] using
        check_next bits a bound j (n+1) p (by omega) h

lemma encode_decode (bits n p : ℕ) (h : p>>>(bits*n)=0) :
    encode bits (decode bits n p)=p := by
  induction n generalizing p with
  | zero => simpa [decode,encode] using h.symm
  | succ n ih =>
    have ht : (p>>>bits)>>>(bits*n)=0 := by
      simpa only [←Nat.shiftRight_add,Nat.mul_add,Nat.mul_one,add_comm] using h
    rw [decode_succ,encode,ih _ ht,Nat.shiftLeft_eq',Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    simpa only [mul_comm] using Nat.mod_add_div p (2^bits)

noncomputable def checkPacked (bits a K bound p : ℕ) : Bool :=
  decide (maskDigit bits p=K.factorial) && checkSteps bits a bound 0 (K+1) p

theorem packed_coefficient (bits a K bound p : ℕ) (h : checkPacked bits a K bound p=true)
    (j : ℕ) (hj : j≤ K) :
    (p>>>(bits*j))%2^bits=(K.factorial/j.factorial)*a^j := by
  obtain ⟨h0,hc⟩ := Bool.and_eq_true_iff.mp h
  have hi : (decode bits (K+1) p).headD 0=K.factorial := by
    rw [decode_succ]
    simpa only [maskDigit_eq_mod,List.headD_cons] using of_decide_eq_true h0
  have hh := checked_sequence_getD a K (decode bits (K+1) p) (decode_length _ _ _) hi
    (check_list bits a bound 0 (K+1) p hc) j hj
  rwa [decode_getD _ _ _ _ (by omega)] at hh

theorem packed_encode (bits a K bound p : ℕ) (h : checkPacked bits a K bound p=true) :
    p=encode bits (decode bits (K+1) p) := by
  exact (encode_decode bits (K+1) p
    (check_high_zero bits a bound 0 (K+1) p (Bool.and_eq_true_iff.mp h).2)).symm

theorem packed_sum_bound (bits a K bound p : ℕ) (h : checkPacked bits a K bound p=true) :
    (decode bits (K+1) p).sum≤ (K+1)*bound :=
  check_sum_bound bits a bound 0 (K+1) p (Bool.and_eq_true_iff.mp h).2

end CertifiedPackedExponentialSequence

end Height100Module70

/- Source module: ChunkedExponentialSequenceCheck. -/
section Height100Module71

namespace CertifiedChunkedExponentialSequence
open CertifiedPackedConvolution CertifiedPackedExponentialSequence

/- Small packed chunks avoid repeatedly shifting the complete coefficient bank. -/
noncomputable def decodeChunks (bits block : ℕ) (chunks : List ℕ) : List ℕ :=
  chunks.flatMap (decode bits block)

noncomputable def sequence (bits block K : ℕ) (chunks : List ℕ) : List ℕ :=
  (decodeChunks bits block chunks).take (K+1)

noncomputable def checkChunked (bits block a K bound : ℕ) (chunks : List ℕ) : Bool :=
  let xs := decodeChunks bits block chunks
  let ys := xs.take (K+1)
  decide (K+1≤ block*chunks.length) &&
    chunks.all (fun p => decide (p>>>(bits*block)=0)) &&
    (xs.drop (K+1)).all (fun x => decide (x=0)) &&
    decide (ys.headD 0=K.factorial) &&
    ys.all (fun x => decide (x≤ bound)) &&
    CertifiedExponentialSequenceCheck.checkSteps a 0 ys

lemma encode_append (bits : ℕ) (xs ys : List ℕ) :
    encode bits (xs++ys)=encode bits xs+2^(bits*xs.length)*encode bits ys := by
  simp only [encode_eq_ofDigits,Nat.ofDigits_append,pow_mul]

lemma decodeChunks_length (bits block : ℕ) (chunks : List ℕ) :
    (decodeChunks bits block chunks).length=block*chunks.length := by
  induction chunks with
  | nil => simp [decodeChunks]
  | cons x xs ih =>
    simp only [decodeChunks,List.flatMap_cons,List.length_append,decode_length,
      List.length_cons] at *
    rw [ih,Nat.mul_succ]
    omega

lemma encode_decodeChunks (bits block : ℕ) (chunks : List ℕ)
    (h : chunks.all (fun p => decide (p>>>(bits*block)=0))=true) :
    encode bits (decodeChunks bits block chunks)=encode (bits*block) chunks := by
  induction chunks with
  | nil => rfl
  | cons x xs ih =>
    have hh := Bool.and_eq_true_iff.mp h
    rw [decodeChunks,List.flatMap_cons,encode_append,decode_length,
      encode_decode bits block x (of_decide_eq_true hh.1)]
    change x+2^(bits*block)*encode bits (decodeChunks bits block xs)=_
    rw [ih hh.2,encode,Nat.shiftLeft_eq',Nat.shiftLeft_eq]
    rw [mul_comm]

lemma encode_zero_of_all (bits : ℕ) (xs : List ℕ)
    (h : xs.all (fun x => decide (x=0))=true) : encode bits xs=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := Bool.and_eq_true_iff.mp h
    have hx : x=0 := of_decide_eq_true hh.1
    rw [encode,hx,ih hh.2]
    simp only [Nat.shiftLeft_eq',Nat.shiftLeft_eq,zero_mul,Nat.zero_add]

lemma encode_take_of_zero_drop (bits n : ℕ) (xs : List ℕ)
    (h : (xs.drop n).all (fun x => decide (x=0))=true) :
    encode bits xs=encode bits (xs.take n) := by
  have he := encode_append bits (xs.take n) (xs.drop n)
  rw [List.take_append_drop,encode_zero_of_all bits _ h,mul_zero,add_zero] at he
  exact he

lemma conditions (bits block a K bound : ℕ) (chunks : List ℕ)
    (h : checkChunked bits block a K bound chunks=true) :
    K+1≤ block*chunks.length ∧
    chunks.all (fun p => decide (p>>>(bits*block)=0))=true ∧
    ((decodeChunks bits block chunks).drop (K+1)).all (fun x => decide (x=0))=true ∧
    (sequence bits block K chunks).headD 0=K.factorial ∧
    (sequence bits block K chunks).all (fun x => decide (x≤ bound))=true ∧
    CertifiedExponentialSequenceCheck.checkSteps a 0 (sequence bits block K chunks)=true := by
  simpa only [checkChunked,sequence,Bool.and_eq_true_iff,decide_eq_true_eq,and_assoc] using h

lemma sequence_length (bits block a K bound : ℕ) (chunks : List ℕ)
    (h : checkChunked bits block a K bound chunks=true) :
    (sequence bits block K chunks).length=K+1 := by
  have hh := (conditions bits block a K bound chunks h).1
  simp only [sequence,List.length_take,decodeChunks_length]
  exact min_eq_left hh

theorem checked_coefficient (bits block a K bound : ℕ) (chunks : List ℕ)
    (h : checkChunked bits block a K bound chunks=true) (j : ℕ) (hj : j≤ K) :
    (sequence bits block K chunks).getD j 0=(K.factorial/j.factorial)*a^j := by
  obtain ⟨_hl,_hp,_hz,h0,_hb,hc⟩ := conditions bits block a K bound chunks h
  exact CertifiedExponentialSequenceCheck.checked_sequence_getD a K _
    (sequence_length bits block a K bound chunks h) h0 hc j hj

theorem checked_encode (bits block a K bound : ℕ) (chunks : List ℕ)
    (h : checkChunked bits block a K bound chunks=true) :
    encode (bits*block) chunks=encode bits (sequence bits block K chunks) := by
  obtain ⟨_hl,hp,hz,_h0,_hb,_hc⟩ := conditions bits block a K bound chunks h
  rw [←encode_decodeChunks bits block chunks hp]
  exact encode_take_of_zero_drop bits (K+1) _ hz

lemma decode_digit_lt (bits n p : ℕ) : ∀ x∈decode bits n p, x<2^bits := by
  induction n generalizing p with
  | zero => simp [decode]
  | succ n ih =>
    rw [decode_succ]
    intro x hx
    rcases List.mem_cons.mp hx with hx|hx
    · rw [hx]
      exact Nat.mod_lt _ (by positivity)
    · exact ih _ _ hx

lemma sequence_digit_lt (bits block K : ℕ) (chunks : List ℕ) :
    ∀ x∈sequence bits block K chunks, x<2^bits := by
  intro x hx
  have hm : x∈decodeChunks bits block chunks := List.mem_of_mem_take hx
  obtain ⟨p,_hp,hx⟩ := List.mem_flatMap.mp hm
  exact decode_digit_lt bits block p x hx

lemma encode_mod_head (bits : ℕ) (xs : List ℕ) (hd : ∀ x∈xs, x<2^bits) :
    encode bits xs%2^bits=xs.headD 0 := by
  cases xs with
  | nil => simp [encode]
  | cons x xs =>
    have hx := hd x List.mem_cons_self
    simp only [encode,Nat.shiftLeft_eq',Nat.shiftLeft_eq,List.headD_cons,
      Nat.add_mod,Nat.mul_mod,Nat.mod_self,mul_zero,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]
    exact Nat.mod_eq_of_lt hx

lemma encode_shift_tail (bits : ℕ) (xs : List ℕ) (hd : ∀ x∈xs, x<2^bits) :
    encode bits xs>>>bits=encode bits xs.tail := by
  rw [Nat.shiftRight_eq_div_pow,encode_eq_ofDigits,
    Nat.ofDigits_div_eq_ofDigits_tail (by positivity) xs hd,encode_eq_ofDigits]

lemma check_encode (bits a bound j : ℕ) (xs : List ℕ)
    (hd : ∀ x∈xs, x<2^bits) (hb : xs.all (fun x => decide (x≤ bound))=true)
    (hc : CertifiedExponentialSequenceCheck.checkSteps a j xs=true) :
    CertifiedPackedExponentialSequence.checkSteps bits a bound j xs.length (encode bits xs)=true := by
  induction xs generalizing j with
  | nil => simp [encode,CertifiedPackedExponentialSequence.checkSteps]
  | cons x xs ih =>
    have hds : ∀ y∈xs, y<2^bits := fun y hy => hd y (List.mem_cons_of_mem _ hy)
    have hbs := Bool.and_eq_true_iff.mp hb
    have hcs := Bool.and_eq_true_iff.mp hc
    rw [List.length_cons,CertifiedPackedExponentialSequence.check_succ,
      encode_mod_head bits _ hd,encode_shift_tail bits _ hd,List.tail_cons,List.headD_cons]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨hbs.1,?_⟩,ih (j+1) hds hbs.2 hcs.2⟩
    cases xs with
    | nil => rfl
    | cons y ys =>
      rw [if_neg (by simp : (y::ys).length≠0),encode_mod_head bits _ hds]
      exact hcs.1

/- Transport the fast validator to the original interface without recomputing it. -/
theorem checked_original (bits block a K bound : ℕ) (chunks : List ℕ)
    (h : checkChunked bits block a K bound chunks=true) :
    checkPacked bits a K bound (encode (bits*block) chunks)=true := by
  obtain ⟨_hl,_hp,_hz,h0,hb,hc⟩ := conditions bits block a K bound chunks h
  have hd := sequence_digit_lt bits block K chunks
  rw [checked_encode bits block a K bound chunks h,checkPacked]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,?_⟩
  · rw [maskDigit_eq_mod,encode_mod_head bits _ hd,h0]
    exact decide_eq_true rfl
  · have hh := check_encode bits a bound 0 (sequence bits block K chunks) hd hb hc
    rwa [sequence_length bits block a K bound chunks h] at hh

end CertifiedChunkedExponentialSequence

end Height100Module71

/- Source module: ChunkedEncodingCheck. -/
section Height100Module72

namespace CertifiedChunkedEncoding
open CertifiedPackedConvolution CertifiedPackedExponentialSequence
open CertifiedChunkedExponentialSequence

lemma checked_encode (bits block : ℕ) (xs chunks : List ℕ)
    (h : checkChunks bits block xs chunks=true) :
    encode (bits*block) chunks=encode bits xs := by
  induction chunks generalizing xs with
  | nil =>
    have hx : xs=[] := of_decide_eq_true h
    rw [hx]
    rfl
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := Bool.and_eq_true_iff.mp h
    have hp' : p=encode bits (xs.take block) := of_decide_eq_true hp
    have he := ih (xs.drop block) ht
    rw [encode,hp',he,Nat.shiftLeft_eq',Nat.shiftLeft_eq]
    have hs := encode_append bits (xs.take block) (xs.drop block)
    rw [List.take_append_drop,List.length_take] at hs
    by_cases hb : block≤ xs.length
    · rw [min_eq_left hb] at hs
      simpa only [mul_comm] using hs.symm
    · have hd : xs.drop block=[] := List.drop_eq_nil_of_le (by omega)
      simp only [hd,encode,mul_zero,zero_mul,add_zero] at hs ⊢
      exact hs.symm

/-- Literal sequences and their local packed checks recover the original interface. -/
theorem checked_original (bits block a K bound : ℕ) (xs chunks : List ℕ)
    (hbase : bound<2^bits) (hlen : xs.length=K+1) (h0 : xs.headD 0=K.factorial)
    (hb : xs.all (fun x => decide (x≤ bound))=true)
    (hc : CertifiedExponentialSequenceCheck.checkSteps a 0 xs=true)
    (he : checkChunks bits block xs chunks=true) :
    checkPacked bits a K bound (encode (bits*block) chunks)=true := by
  have hd : ∀ x∈xs, x<2^bits := by
    intro x hx
    have hh := List.all_eq_true.mp hb x hx
    exact (of_decide_eq_true hh).trans_lt hbase
  rw [checked_encode bits block xs chunks he,checkPacked]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,?_⟩
  · rw [maskDigit_eq_mod,encode_mod_head bits xs hd,h0]
    exact decide_eq_true rfl
  · have hh := check_encode bits a bound 0 xs hd hb hc
    rwa [hlen] at hh

end CertifiedChunkedEncoding

end Height100Module72

/- Source module: MomentSequenceCache. -/
section Height100Module73

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentSequenceCache
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedPackedConvolution
open CertifiedExponentialIntegerSequence CertifiedExponentialSequenceCheck
open CertifiedChunkedEncoding CertifiedListODEVectors CertifiedPackedExtraction

lemma checked_prefix_getD (a K : ℕ) (xs : List ℕ)
    (hlen : xs.length ≤  K+1) (h0 : xs.headD 0 = K.factorial)
    (hcheck : checkSteps a 0 xs = true) (j : ℕ) (hj : j < xs.length) :
    xs.getD j 0 = (K.factorial/j.factorial)*a^j := by
  induction j with
  | zero => simpa only [List.headD_eq_getD, Nat.factorial_zero, Nat.div_one,
      pow_zero, mul_one] using h0
  | succ j ih =>
    have he := checkSteps_adjacent a 0 xs hcheck j hj
    simp only [zero_add] at he
    have hi := ih (by omega)
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos j)
    calc
      (j+1)*xs.getD (j+1) 0 = a*xs.getD j 0 := he
      _ = a*((K.factorial/j.factorial)*a^j) := by rw [hi]
      _ = (j+1)*((K.factorial/(j+1).factorial)*a^(j+1)) := by
        rw [factorial_ratio_step K j (by omega), pow_succ]
        ring

lemma checked_center_sequence (p : ℕ) (xs : List ℕ)
    (hlen : xs.length = 512) (h0 : xs.headD 0 = Nat.factorial 512)
    (hcheck : checkSteps p 0 xs = true) : xs = centerSequence p := by
  apply List.ext_getElem (by simp only [hlen, centerSequence, expSeq_length])
  intro j hx hy
  rw [← List.getD_eq_getElem xs 0 hx,
    ← List.getD_eq_getElem (centerSequence p) 0 hy,
    checked_prefix_getD p 512 xs (by omega) h0 hcheck j hx]
  exact (expSeq_getD p 512 512 j (by omega) (by omega)).symm

theorem checked_original (i : Fin 16) (d : Record) (a : Aux)
    (h : checkCached i d a = true) : checkRecord i d = true := by
  obtain ⟨ha,hc⟩ := Bool.and_eq_true_iff.mp h
  simp only [checkAux, Bool.and_eq_true_iff, decide_eq_true_eq] at ha
  obtain ⟨⟨⟨⟨hlen,hzero⟩,hseq⟩,hchunks⟩,hcor⟩ := ha
  have he := checked_center_sequence (panelParameter i) a.e hlen hzero hseq
  have hp := checked_encode momentBits 32 a.e a.chunks hchunks
  simp only [checkRecord, Bool.and_eq_true_iff, decide_eq_true_eq]
  simp only [checkCore, Bool.and_eq_true_iff, decide_eq_true_eq] at hc
  simpa only [hp, he, hcor, momentCarry, momentProduct] using hc

end CertifiedMomentSequenceCache

end Height100Module73

/- Source module: MomentRecordCertificateStagedCore. -/

/- Source module: MomentRecordCertificateStaged. -/

/- Source module: MomentRecordCertificate. -/
section Height100Module76

end Height100Module76

/- Source module: LocalCandidates. -/
section Height100Module77
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLocalCandidates

noncomputable def «at» (i j : ℕ) : ℤ := (coefficientNumerators.getD i []).getD j 0

end CertifiedLocalCandidates

end Height100Module77

/- Source module: TranslationData. -/
section Height100Module78

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedGlobalTranslation
open CertifiedMomentRecords CertifiedPackedHorner CertifiedSignedODEConvolution
open CertifiedPackedExtraction CertifiedListODEVectors

noncomputable def momentNumerator (j : ℕ) : ℤ := roundedNumerators.getD j 0

noncomputable def shiftedFormula : List ℤ := List.ofFn (fun m : Fin 513 =>
  CertifiedDenseGlobalPolynomial.coefficient momentNumerator m.val*
    ((Nat.shiftLeft 1 (512-m.val):ℕ):ℤ))

@[noinline] noncomputable def _root_.CertifiedGlobalTranslation.shifted : (@_root_.List (@_root_.Int)) :=
  [2535094792281881231276218427183416871053592204881144659440583687054154566454794467021097572655419257386243041496574466866893262496360235176402665215218847499473141000350140193671759931293318471364729380205064878094602728925606032693429505558254750810835715153639347114909538556942011276362093482069087176673184345495579598378896538015945818343060797849479163914853114253280400491818533901750274200752878168825394965652011626621593750077716082250490541441654809871807196554391068360404424404631496877979682571364615664945067367050658569561427546955811645047653743126929009950407304726697758446608945692220432898218827712083559215510093420447345061038102958321396668668356793168544651483537658642047552146265160824454319626154945883549461608253713239337052639383691162955959807113259294323781447944104132520439952749647115804536536452833853825861147033831250305751433516279483353630303852463110230561064986425439059592402171961584999450901404814834961183319732926405068610200068182531645668122728413871125328333580749887348583567270414604203786332731595143861775379288821387625548309858683947898550761095687515597029184130495355969954404623834661476055818067461350607609855586968209635828569976854294013917349331804310885061008356269147166126716896921878992021495337599469563860246156953916538880,
  0,
  (-14643336930651837913257270869957529989058988827761531614711368244287421513551140251413506960792100142719746075128998085426918718581642460574028771228125779675149513741923387342304134273071322953517202116519083262571118918433234067937850290612570365111737371479335626700934692345537726084036689404623968628772507044162725686213653977457131695372534246884960671782456483843547258404226266407238278478990760098521467892303299481228919964295148368477695687281593148281260114049633250758550332525733828783073504114890553943104469506168015701197150441389010733163827316439090298338812924634720812546063487876421772472278522464710787283583165281704574305647406369651804088339291615992063611885637805095241362071399299182166680917843214815477500018261234288063031361646608084000011639071089294556914521322318394642510615530379130803354971904561899692667085808350492853752474018943509069737704218853911595954975894037968872791747069934983410848881031801220375704648485121705190034013120461959183364803712531383978777333961765180055472974766525801788225834048909422405630547847174569516185384734936568757380333089040645690185466508745929702136432875340885269523629077613090089410438983708818624259468783424782495443453345379311133334642593242724974038426231453738308672776466858039849962821643736711168),
  0,
  39346897906694248429036245052984224376881565171764585859717203596494982445890037014416306386808799441899348207506693601841318510265793979987370661636544688630941783741975272441570783306490865113025416778895918143682896104789092977282789660595650621009297993723338623305532081522968393989521321549198912665303348504413975339210757201345770755612097252220776370823004197456405354767345016320682863330871207608534362322492608505878028801494012830127838733122772365747083222027803706353148746715695637575282730335371585888023764392232462230333828474780843004343495893689373259641302944599474278673726601784341887354767832122394663082700501717295283111174366980917434762191576309237948109393386322229481072430289660012691039209356237555927025047962515430150716748338222720682025585284762798908326398033289886556040286377651447391266754660400640749732809500815869164119892849450989549296730692232790131980215665636601531849964518090833835628059439715877973015468699498801713556430671561690227421691956032522133268530931453750963368471504818574433943605639084964432794436909405565384118526858982164527379872852452743450480945534212971591422926782918844554587764339473300269847410882265674829594429864859087864368595316633518537674355830072028059044137887127572907170673733673890017911583010717696,
  0,
  (-66322541057002006677193253693980167221858684939511859125158757370173055045886999123737411641026594195634117735141475107957318294594989624462524437624439246101965827438749158225697899554814942838290881461909686439608795680029248482855461289728251368849256069095272003102468066392695945230541810965518651398418579608587167409603651087831615508869294901703568738192531421789922127458540895329017906695750465062254273493840844393136114987749691937925904705465652499275607062842112720752924907557572513592473805664727252603603999817093981993184793365541202236707041743907434330650197389511443057444331579490648340300258422178744862613330366089115416223619088902254964318352111403211209535785258733705407148785958843769973383623156167637750303464149299630330622157851101125845566196014756414642669171262398756028474899728004440170649392352554599791898460763178299754156509797253829388399793298294526070294930621677135399010396974645125744198096524343861384106888294278547004479207484307540880900579331596411912644818765071838488343436137803428562695351178738494804454863756262323657061157674524480198466259509260959183525821910261777834425126624174515822397024322304880480209286396511201959222163647322970448930994258676488557219233787593678462083359344416094421503721023741591495886386495488),
  0,
  79525700040935342346020278420698695283905063220321659414327604892331058679119752338663698190628076356782992692666386773869744227041968578210145887116699634403807270112963386778785666942753828123616113147195929604740075192857214370851754050746685986121933317690450124949657535525144938788587155447144553141397111135540235059108635996017307699731877422879590161019525493158402499295475610217952837967107427309199994253357331071714545024626336929407558535825082502729893431180864029607733766620672390931947716348053101686165486068760990438291605412327778518789164024025712330373318143252318878190488406810608618543788281570017171847345208935359459768415487671338909712341691733623708277767098505173924301825493430165866745421724006150448833151787798910431596109013295244359211655032791520344487912196752842983066998090863787989353232521494852502434982830179910538027002390313163956247502606300204310292738653966263027739282617487778043544062908612880268962469650491148996804066233155326811785528158238851512495277875580250273211400395725127308992406454058993640891520343512212358278813749017448672195786086244136837082064849519896585657688612349684318751350809216126049741643967371279575146284333063481529707462111392569741651841814534134859975555517591536641759734676868163250585337856,
  0,
  (-72788309070148985536529953541905513676638233424204651309349243166975075543654388200758212297706247080466383356496372319767629544379187577903157067045667229038726551226727474281967333132288697796313340975108301358957131944108648555908728653499887000161964218581654064652680407727023050574692884076661434493333119622686597663339519959353586032976123691260933023092492977955275121833309294582832731148664021328750865885554196038278638685355831553159128342001084668948588362913260853076989712793319664340944086855748710047736746356018535958747512677425999932688484162856928923625496622640239496634165430642017960649306647632819463178915004948642681941698404367573797234266436921444324679266910374339119725544131103629993960525674110705630336871886750544909805048835067857881255832806040967289757560944908758129746523786941981429385057607125910686742056430030977467782773450834643125883044685674805536695203682519758380761867353195781658826548027654409498708713135839346812007798475204567224784741140978655805516200399180061807013233594332652081659276563719774402985087091216243637580315172394470022311467669360341179751238826444788310905465428824190122080991073214242895049314387897792700116248159637858963290993551195838005930847798040051257932189897461412130029816630213195040030720),
  0,
  53218389710354226641472950788239373607659355415929382137131514967084848515746765182548611144355866359609998262918170757888725359442357767957389083812093229442296541735874629767432013402876716886920239564346841055318873051870175358625919273689277181637422348113827044843953914056654827037507497361525629865361618322584907218073225956084591327461762720892436828653040116646024913768789149040486827432490265305045257859768394888134836601523406473088995780981258212188899186684105444075967647655006962638283303701855773695485932849425077749348393116836887159004278415832233023644107731254711195042780969482280249855305290165316853726856551714309456974415931909506171978996413223963803241730477924120397287626790020146834980384391887128595211718066962487606979948473368119667843422025880588227982621768984548552956690972873970672189400176307380768373133853722330423112989429416388152547363269310656605016494741983220568658884238287764835182805698208531996739570507369683206705308437144207399700559484278190805026198931367396209778648877080445538893728645779701841458209086290417002238479732238077459453631635229996015255997781834006518030944091799810591263356942626996540313552381352851974573475303914354388647473573762918167966589070568214654605335888038818683672076858838164176896,
  0,
  (-32088932116393754213236018096552454735813467603820330078313559955700175591110871231248138035252627866675864840528741259252472556813049330880859508560733920657917293611428224482986124152783557428633214509713005541148563961570199856324054796944086211859920436569268361872789170469146411073868923268883475846772657488859061693019183227382198497134038294176510374357172071720996910296544078123954889540167365908726166330775689589086013193779906175189677024627445150951005251368616718789205733097524027960411327815558820904724099149889144017689926904339724972839830211799237661370715579642118186894621216686705201326315986598486460601748259346250745622197875983647509603863262398002419374395569188516960446638201488088415534223337337250783765251062714255671558144459801687379206468264980366212711270776535612911040629402526550536038608485349233651683265363761534132935323854280749025932393122597458872322388818709969820933872478121809576083063670062096124041553448655546793669635026319259476858062782165903216237720140637786755400247949513437155941986273024719930608008736782699067852215783124206421037964077185503470629963450653889346118654154049027403514891257213886021685287628822990024083921435368850303776854070388839971994622148616460221405197372191558334496701761605074944),
  0,
  16338946231889696214744862645078404171336233412452831620146856998755942761984123049404259484410231476974729831233780309398180925787739397383644372125441335806086596849339031935076722132775020897485295739549493379003272217327485269490859997129015714484645196358859547274017207547208935310414622140940902354963503598121590628320764693274404736174191983949028124344864720994223586602836208243147076097444069117425942930460262058486445662376191963493898990492133356238973613771445127229142137141115463285115403917643953321977990386056060425545159264154145144717129422711546467370300957015729579508548720555693253844534180556732014862369620386530796697468187593613991159410292041821877678997438111604468252133812559378202032236172001776920370120909286965060144529816796324528224561807752764481259532285840429365671289238725933915472110515647014940330756713706863523317329192305321869502229501872334258319489698874583053527525569426077191647831162209888595361168890245961221795372820253683184411234854255461532614305494431647944381311038433042619661975393485458479478912101739004440129628956893977500658620891505921026338780078668159742468111577076755182667967595786131025151748910914267945054542595361776898554432712395048275874605449351615011052612883201991304251356947152896,
  0,
  (-7155183077621826369445810943582205612667543463445937684839864124994355822259982900897086285288350506811004466874417132847276870469135567602581745367847046624949026880327529002425481844760200146923247504029385392297784116739401624349222178726856111548339230661198211196225550937342714572138667112575443712461202439043188008218758925988065853644907069500933075078116655198505208350864155638868133927985166930216908754082090575173390808877137790756218670380381114372050621965698923939310511998845236515314485546382497396320879287219418003840157554447633331568143228208021466488548930881208494849015086540591580196330908516285650754922830040985976280801642535342277358284960912939899506179827831190285980117439982822313239967839036388876279599779373828872842067105609107710155200804732089886627882303885872019242586318028485443024467747946068368701162275516904552187319031139800763501627928512477692375121741052900064302665634702190521519135399503794651851448433114863020682490311408175557054793214950974670881348480776639426626986080004324302618842633030319613355123233480037644608437671473545988180140323819979813324636011011556109342550488770114511216815986574131070192382253825890612146117784281271239456345132630178515456384719009150933675527239763913462594597289984),
  0,
  2734572601490401850199583127535254682830286907786701060835203315588277638304274224686987786559863404574040008457923168726828291788764457753343036850050322662110127974952815569236764148711706052535068426047765380035602936339540486878151002525701612211959523307142973453939066663227881657676256047438245286021376498320163581307425229286129378572332502283828012941245790501952668683704749594588863832373545098632729448466701416910397062751602445221462319057926955615983412807529545213383748078395542106538853207477690384805350310734824080090209534319044937671290952436483468776608860803447682806364386057536750465789134559772306885859071356251135295848185454921857241953531443005759555453367096978063941426800191162864656479150404484578428694308192979483051428838374675307698359451638169652140207066005689438619113143016523905847684167486241352036310350751993935491436943255101937318603717489128563903838813061770067003990525743835522965585757131040350248859312554057927933568103866647872863899807442331089837275299493051506623398521521706284524683495875324867252471672096687949754532871852110758580850993503727159155137320920401609642799367886930570444893257959013789323890933795716498597533944504815181203630001710989232333220616414187906812713761265819897691111424,
  0,
  (-923027967865698828010892322873724503249965229580143220329391316729023955342104504505346558813642197587656751663951745685931567040933924053046220597143205388415817980927876158468374376768444366735178442535043329592131991388632840075291048952518726247544592546999143227315033404825635944825258134271605285144671367081096144704991301503916095997204968346748388032303046365425572828169268818152336018100825902793677089787566096501742801044451434536176228722509763661694759144557604709387467032723475529443576814892385985807050432027349754770975672909643718329724993342691108547364257525815849560044242965910642542080777407615477812507802363909599420128523540652141033515322903297062425215550102779574277308088892292522857203895515018267899935701577945722607804191443481758194841963636082627808748214135135968062730975844913806362652784119339427599723327856509282911489735683846292212526931099017103316847487521578216228780298835523476696799557596533203957592220733773153422513533283708025525965185982953598062777229383022356927873755425877808398292873947826293012965378686961367898240848369316806387788034334447590665111846664408127793762315622206095656643261934691216483564660524044957204823813655693974506403563464110969554981355433672486993959115044197270290432),
  0,
  277918461995346431530321701311673593632782193548584763010610944989210367972612832464978386370952659984108256235515387431896543799687949113493969424786947724319236390274872213352942323485004026726645398452815471026520915875412899476052556371967060936607489758966727322549446903879777761797256932772377343349953211197987069064659128594033630472518685719103103393772901299864005249247139127691558634623460557523972447293642644905653571077751039649641933226133735879568282938163240278089404746491157792706972182651667175319192565632575170580045086594979035879664036673399085833391968482599982854140330963285253952997722598821663820076628911807411886190573365573339274325402986168436700543176337861671192330464310125566910391794931232587510266737390682165706638876400390086800476388651669285504164698236783642645070047203208639152288983681578546205386425620021145885687379769829948828703438653962156113466555490301791508735861916621374558760192289701511589178217876778787283187370647498440866735269366507572730551853583867496346244966440361990689237644690738613127199954849957772212106686190980316291253282317528836705742466874815741170103977112839726109180324017629175591107605209435558285885628717994807395580512952664084183990667560850744814116441605367922688,
  0,
  (-75275803289345650092268654916443253357577272263133636012698036346984423827883744636066257831215128291682002388341455678703652964343181600758975743877684587286738764350648690323609632148759433416660103617769055491743451417349626554889030051252940196006360090667185000940291467000438918208462316815847170665867937120411873168985988970190089437380809997966401498137063743206550507562182185218881199029750343651176780361841066701585849154867022462838206901022934764990759408097364099157933747315928291024418622411745460822836390090617596566172512604536746647756109362807670063736845376438971096736010148782585344733752118092044134443409471713551956431906418968115411257251298923746519460489600725952084523234370258077578170282219511511055003393095024231020655725504305265948553276921023563580684613941976196360746767908803762009903791667963917625213266014623377934492247078109092739665179665054596955541682963400600224452964488763417636520910659857700303651206394928629628938382727879729845020104621509987932545093214131704782690542123877148216602350915124299981840178328145296239370814204634747538555463113406279144620987663142655892495446095482229019139892399278501923600636504472470162464712537359346849814400100610080269022143370907244489592311065346048),
  0,
  18474314304755457407558521816730070027255217244159682387609667327567500082931002841685782619662040880181193690920648181635917640440402083144266110659323257030494900229044231308052421822399698064077530803816870570580008221552578375214421201741879117906389810962889415198237566245633787773112306130302103082148059341884964745813179932710328079000797027715642097551817839281390029320771414212254846226925478435449248472755654063452582346830952552721996025328213715588089774695745836830263833037851057795927525969556601858806063360202007445366544965519047797166811921060458431327160200965156840292331727616383571850913719547592286442678325114426838836779174472919800363084474778035976153340229471715442680970379002652630159091182816600528081416628821220668442672322702252839790863456752824941583292147019361740251079813440792637172527950448479574916182917039975332006905681798390384596319141562739111478491971758173528682404294326922555971748484504492952860072730840104860860879268089010313741300521825483973178694235757189617667662326272386950313618605789676454744400513590118265856836648988098520666478897538842930164352985650169452534265252375033611015202874222401723061470771266267772205278084219969203456689563197707876954651798102085763407460433920,
  0,
  (-4134102304793764482918965118233837191277779548764220349830668314164126645438638765769605044575392552135087209409374958306505676248590995825103099367518223818935217338667290140691166186956411955503748966748368058177237984489722514407604873010209033885962637079120864637880866489120322166250055021858310521513765144073286517657201712175377045930800312033178063256343061602397300169232203645149382409424004482000352639353499836366271543226059198169389056591266820953173218844868657916931239852709398322286699625259943751660652784997801874271300315005185120147700970884402728185857439023379602122395993140868901824912125466687717116980526935384904061258220985443970982853387207543730463852627320355072636977440588839370935422849021313207770287677811291468859805277860654350335740835791145736269489744688459740469120200122349809762450633317042815048369829585177236175413411319790488419565864458805737165927197473188456362511926832676520436081603129778357258626384436148666282360772067227790304414916565827487738226599179064926821593644565077455980235832979231400777940373984006278219042339332069258091273309290916437990346992060667558938927605903219385043056477856755128629404447165515827766753222955835645299407260278578217639243304589788554983374848),
  0,
  848169519398894527713311651950181787389664469082599680775050139207660554276401454638238509520820751799258602657751173285165666727249953559226351039070423856471835187510860730873364266302318611422031864034474812933651882600849443592304040083685639974807706939796818173798442144934449098431244806926349263553777544052499021704174144686667996096118814769117694864743297848546119790827689964946381305882442810372924043298143900420491783518230311791605888418045202556968975454110144461724336746327605058571645393478874246442504299345755150214863812842572198805386293236163068204975233021892829763936210150072629983980192000909435575998066339668726550807366341702457572764880747143425880417558267597466320537370833277055096778681698583469946210604082421656747446800042757946932002006890226221365296789534420206290425907136092019612754868052540346888461763723035963950013391608250348625822912927481934831656305682369263790392558313023341292114728792483991146455904447012001786873631357020104196602237165914761487277700468833857517848080021894892050823130698225175226826762278298605823730904890080662212117830546720023625169036944702003028562924347308951021000195890947905939642958119000859664206537819965246325633312608667793913090208225271503388672,
  0,
  (-160318720255131499560810059592423541161298664898364184643583682977637501053142551081996454029630304478568089070693193085317096001134265361857734079842950991370258800451757706583705355359699265698038939762513460582775717985886373825785863720568387940409058678450014611923717119664128897742958311146025630125760945955875921549641639784631589068188710080688549882786684725317099985318857188348186510782820231223196525411688106563812130737514864616785200718612877954136395708745940599854938038030836999092837025983635637614911846790061899620870946700226703607129882616959046659078414681583288810287915789645364827202942530354499931641258272442756480291621347006154915269543652313523062617060391524933811257307090902291839891966839845540064543750857850601699010329211196166681678630835279407853629370372816280545008569746208047577764066056753022366709338693184584457380860385520067578532573529564686012592226177459956619111688804149730730084971649445492854257773125055256216773776599528605623080566256959069244512057598915618916243339328680773647294771228533486844847749494916061655314940297142167803405378466046216651153055177752476564330367835952350847111870744147252615847881881680191063995483350101213774077141693301583305179434980458102784),
  0,
  28039267120014877827315961797842355868125873033615691545602298869812722268636783998500651875772216070687777031714640561866736538169176181762936862169815481956907971328676750742553081809192882582867588662044735154347480662796777468523499581139068466645354280497730175332022115398391258221885249592086542896113265068651484954554326026121284072509816690915209455679360323356697343560351826267099476851010812337007243518011314942746896585252472991911803251999883253338590483719086529096981947539898003290849960979918417443547347657873416997312178271370589090821894605001190904739266351133764716343334529905887206126911315831700350741515835800588340566768759464738119475172707693481997100387777901064215855963732366451789533741059668188858143228312943331120262351119755848301373436910264187337855191628406617548337130775868876219816728248331438247356493887108034697040234275017126665726516725253471688509785598367735152525290501285623184402847296238380871990651772313574371285960780277387721830317535924203366936562142300509501166371132773981364928518455649510780038203509168103057934094593853595172384311132668722608294393331828185300379030207151438767367925892984439612744848944121135179117709480274453329207203535679674684566610858999808,
  0,
  (-4555290875949036416069200909897867790024930916685798294905899112374221155955509077595459741298556862813211303093472141599680864411166177645567692630963808540340108955406383450608547019049354906639272400325073613695735287578976048161864727356914947432224342553904864679907703170648183022409212567042440838467976327559806691542653785731964066777711900367020838287030474384145304259464425796004487149091956318078456641440818726105810962369852190431223782539682473228363134935849213413893964696742674503746966430698725732942024883966729697900119990651480011563347726093392295692042221322804147165262250813589526051089592059410310781731046509976055474918176122648155500752100911586979657477684059095909494993622938725000316966454291746061881141414487183428261962377864705507929314354158177164762073530727026421009659808132401464388566006635693877142833697122419177306481492243200400816670847476839830358931375830223791582132414486856962046704860120770148006100116731474231418784437576476520497431176906726459966037351566506476439828810001150226968537266490744944439442597629630294029822344501009819551309162497436956860637972785684119015242725919814388221163479225882934146936962543954276154971554619451901677208751687065220298617913344),
  0,
  689847875625641917583792176395205662394103247743986763545341982859142647211687232656849158104081665945035527002295110600368593167747705046408253774739525596613208506068567317670371740477994494031094864124337341742728258069939411598508624019330545873856493534006276234879963307896913694865372813657613296891370777821670964742209540813183505397592551036226151527386868105125678865826197480005823732554145758855288121745826743621055369298857567107288917300275759270458911449445580252466759328221311305264543546415987901096555753289644974061533704645503095470730989488492350698674037223669185641491339327965287233524367852352414733742460947079209366037076057580234781788286789670151029967475572132572934377816112078236934609935562825838112763358004122312236291625764090439107905346003427363208505590759591699868550871810030824022547185016407901633338251439959617651173050848137969916029347154820595721582522558542478901782935901594633817347583547009324193002950212399750979925179366331491397653407486234407919942032725916211082016363365114891061532159500774190515015780417399006760852708481267082155646230679728078740357844107783488344280060769509233138510451730124571187469229748170950489653151183450246009285122858786052162715648,
  0,
  (-97691567057684600125068840829022908268318245221185459290771821391602118427222457133635087190897817057494907813292705027043737018971829790374690715258606605272967503577484031681723420360337533129215424332430513891184723673031491137091951918495230214105737226653675349683874334878491358417175561849736443787617532016122072630409357164368723675259108845360970859274794069623028724590204487342726971728209837936433104363545186618975842692662051006829120455014134782268043843461220740097896290042722371852768589279353465359250174659404859528532679669565331293724745921333928691618167986759753248825310672092358002154395563251540321140735483499344577059244850135583524683382522844066453942756879884397718318124418816275420957787365626223977817577741991793291803412702444879254543250811554025940928269019480848176046781708242473044882360768502885104108979780648492435611706493576860261061916517737594944530426942657069275519924199144890732341088712576973994840372862601807552078408415385168499026376610001338289363794727606542045813883826560434317988028747104642366657885893625174715234634300924123328203659201242989047237295083021078753952747582121440950477088451459556663285267424284117517797147519328265111669292608345289523200),
  0,
  12974283378977833650351806164327477898544502167750331540679559773307196919747744574143804671229019935040249590935274269058942379497506505676691377286448876780002863586073559232065369620686149136979081320072368951796535499665725172035413222199983367793938846259898756588926224655485477700203559675169313403568739463608729586543980662274738457548123997777067889772787997757359681328065164502651339086863121326348206927079219846571268570020220092191135148497336343569283779010534241246226678300264452067055148013915769066724642301877012137619684553465262387909165599372251953820016777290064507002490214934041520271688413529683869709892408919065119348305924888147308066291796158625336673426680312781701641932001514246715989282790937884610164699482610766420004396099343427031306666831995642848321108479560387573173387713425793613378595701289555202417540748196579576863222905202482704962715368677006167175441650541261940525717477927986162567134571247082369104984707890864182697678676734585438898487306189886244645839614386372599828288282171415894351475900127397556006058690947808697065239102755341615541568796177050070758591171105381531098823987765901175382467459028337998204838510017477906274275844481663626333085494107176960,
  0,
  (-1620247715769335193162190488488981910920797520009265428000395653685893998674113985051194501497385334117893578208670407891360487362998577801147431755327930974721536005226706865068998625958487131097634803342869089354024406080078751855957918232808664239535853293145977260188750002652013335126674923724538799861991554913684299684627543518056445932167084865926790625134824500429879564494453851382352252939870304155709502561942659184554807529320838004184160944132891093934105226036293234454055183820972285960200598945665824046938525619948680350879562013835814685675498564052430804674237410130352193102082978232873883089354273013572927463015955744300482213249250380159356345435797863758243280454439383524082856960621806160048922679509004642828421931427085078162099879199167110818014934002047279879649900337952446208285356014058239207169197707400081547241290704916851396267090707070051055021029027858831765563539954132687124080200714468786680938391457300740649993483144769427651071762646273691235635755302820358085578997487661237783194716118555294190781362784818395570458234413658205584708611168096118406479271554929413438526908659069864727070708723565200964391214951153403397692322810228042852663547956097724365979955232768),
  0,
  190724616960049328078480635990335539697116322556016517806075128208812325928271219346002159824680611685741358632908631374269615660321665702394349498851083575211162691143750702470252381869803366334453349557804814388823417395513601598768852338619176483257074981386349510791049930764294094654893195439862675632757139472995657585383739951042529366505131115316216621202179324921244191858469594152468670507267360029893495384386838953176716488519156257991685987111408205951156476600742751142535238610287533998154435091051265402101979474168761955843359715785860451241983178598221130130332651530755592197927115624079844203508135449610654882510882759368621286186193539232223948770168694978429099099250354542621843868008570221006141926648572749608998531425349092066217461176723602462092135436817695123360058928641013246403389436168854195125628798915718800926386347243545012081470330895705169262107500525842412433426310462346649641660766378115645359322765255137761735339749374169683243033975723640654054676766859711551449703851008769002686397189195419214351059349643739013052773926002352921194007837795451254158273590438454497131848716135867191621537540405161182493922768583843630202317401653241503482637516824276218161397760,
  0,
  (-21209598432716295866864512552805564965722915079812638822477631042030894587177876047530637002773139229363891553530345496625996861599661425195280448474095265701026791557899898578202801928497756155405797102671853002029506795175386634859834598946671294196804138347135794927039240390698612844690673140575623172320002274908617818265847682284066096746288467253303026898031813120248541465577872579015407795321061036481385046300496551661673272960562774875284978663895924266745899434060364291943401899949567032465932574940560047609676142441033458890156372316739832967349220230902541863057906602540271420249454292549405794725856219529277397133013079769629423592783657317485746451793774958274139078172900290299241260933920481612977085698000036592825852355871444925460371610550796013113336074062439982125682608875881680125090860826661132209879842303029519998472940363633620751490937588168053444090990176442503244267602677608808822111417410468448222616223569136699901743633299151805512804564338500238768421547106594983168337521844149675193167314463643609393443363921063533349955114549536300763026371109694352248539096834209788040549728899460376847113419552860395542924300170469289243355700330442361611931639400254494736384),
  0,
  2232844562793416037306943114478974181396394574932904894955039190163780493143456025789836784465151366258902989681069834473774528137772725672935896775860903976001243220615631459253318698575986987797577009918105764323394452177729385113411238668388232526008609422658183703264687115607355067183015624166722160560229420401902651036219919431504446614025016330109945246623628667386089259417941035930259413829343623466684735885174653905090199898014431797263794612555799685093722169006201020500357785944220672017977170333564077205688497449585011169409405611094706441677944203917783954023259143992724859215431844181239371155904188342417785283378108298157514306588026854343490913113101849105799012985457603928231931202113367965197804135005588312985412040122560756506333636602562774342002591499910039547397238753379353672331590127684618131467148672247453928785882274814919240749556200483641431890751091938566099015989612108534423695268918003130021608943031250678673827340609617123286946153200139731450764139704475658002326947425947848916189047818301503078273455515973190838767380261952478891478763592855767568433439424422632904701595465664374787166087170621612805591777716928214994549902536074964985201393700121346048,
  0,
  (-222956340220145843550985276392631877198570416362987268403693718490777344219906276484530996331859935522639427121379997522044319956846214299261719200211908579856787143201800876137774584900453616202613927968575390122041499642484743667709970270387605199397659923379491366273059976617420840378388463975674663381399598021022924997555130823567374316978398689539644651511877317993581887817282152845951782207223659961140720313298362149302399014453338960327196382395644575040257906139893899359478682683409897809806915360983016441935216862157952116983420192960574038790688592836070476043995924912911772252080249826933882221339652176272632267249049077254965093229018682932682752242260884403390429268013604881582979437998073889715255997703573626642744511111912033315801347329522421546195399712884208960314102769647091604517751164597233013754522063062550880341251690803237352462540687905694081245426488745205360921023717352025376708269241814364234402699519209758920687342552191162249886087673462021799657431418926312984296356731355616174855049881338892548796432816362473844329504418097776561565732524435400590048318219789372952989973014258186373949646528079259621904905284523485615947823284226274733805518119239680),
  0,
  21154035533775515330029015881007425982161387516462520817026946075127684835560022348209649358441164324402468703815823412426085313545296813990323775625064334084515507193541213763576559645580382368824819735098253907788277376207089619575233383670411254620246709752661367540923535318583435632404345570636378022546071750203148230329900802884822333019983602363541192496074981928888815508716056256742430519215283740010433023500840709947863691776006548154444244865252733320905108510394552821805896119888473996290774257304308477393169925061543861569681278074588510559713601561999279171321956337643646209392116250471893001554162017681231502696414173464380528958271719915547999699354324698421743917072441299427387489928611693344434827859924081831463520905317714905160353228718778006473465191999327248584662627337899314990863480776445028666937920819239643036110626215475016524497694528236789502391456104182106222777118210475455789320692348445272656386633580916169296686270562726791045840216188470513440371308057589411767639827604511017137787257248089393825056721628952404088409366142234967463750236661873952147512147877390489161624620436883242577291916620134450032622041506551801551321656677483009090282061824,
  0,
  (-1910307375456496154405976529618307296820969351992825668928060998639540647298158767961985027878323572750140478046444928527924563361399359384778191957798832651335994179646223423122792413900250513650921361517830339467837401719639931706724386076327834521036420776231710521742611465741383512421688829829950176999404782129175655057248852293048210934849173597470684503209175333622700654843812558422547143606912908699609706660819144128511512391257753714708927846464375230600314718415239300859305954481489802160937623760507383041335119220743429444816082416929482005172670986292442445027829426553859120903102794719771145726476531129821871851991567490729900345665804507972762925061095913590602372411294904170308985843792271727990587487746140265122123641619118279947760848242955881822496783519743172565662677357152981777609456723234503856875687228692225457880467604236237756904861918239109384591346409453427597089433080612907020807484402553685659537655781506249124576879631202978461150730675130645872248016959928653277001746951133732756118720995789158344076871414450106066621340514470412595962769129652854006386762279077934888292217972679996341047553264190231163630390252517938725930608304761608305901568),
  0,
  164447539445293666700789882457941384902705608065148330250090782482689076694748180963530292805883960044222360495376110192043975022331135402993696425479168421312776179420201035332808265342130378170809887425910008463740351683441069474562677324209481927318631879491052727528752229151024788610788803115714800045440287682609111166708715080607412809525025380866204800523560896866501183515609055507059930779561965361558449941730761445602343483567252936050074524296196752956387197542241063781502983101820865285930928447543567741308551502290335364071990564115583546751864662816283819621590642848895155166027910961145265296265601461663214158210633778985140309526659658377991507013860376792474106182849200806436604184968352574579500744610100929378001153815807602185450500119516367099029127285877813982435445148377919685679759760757873287947032914018287128480632210000305005086377239994534506256764953812613871151212340724083715665804369575306464377531879868193050354219906468081079394032021327937885063622956651987590112416932092143741265648035656016337105048612137737909326395483146504399842840354301175345051458305452404983694437696919994521858042567114067872695979954162491612958556904547613147136,
  0,
  (-13514516685486956627270383647732131817439507843174168912792798038584008668603998201315757721317623119068108935952670385663455603950851156408013356016498281245010817175612534301569807811501345802587048632916488795225567097479733657534865031728825631516243892433479908366933941965575325739207846637223566849421075088571662742254687622495329181893475217617830789969716670662611932978878167824552337558751123626878066483850358274181663821632481720008755652711781675706757319719439920412320355006417049572429885204052751619342265436755896098696236096995688087990615459367491879954499632180454431611316273233107639101486092700970201120987723421958506504727738598417224994558514527363567721108786326421167160081336750854468116249218995249708214392752548598072264336652537237967740677368293676900374012876414982113644388012329539831283571786475406031933191088173392188723165423289422227935458951736669642688888601447481396738723468312492320340640582810929261892655765353410598486543042012934743496901133130528711191893767530034499456243843167162435065139820932933021300188331421231105535646288335027377584964838331786752924092341847586403180083227415017187978690644360338232509396907448074240),
  0,
  1061741849298453229175881016346009795647541965164804725721444161102648359689480420530580086760672837070329434139935395415517491753987868285968339649196864929429575754754861477824470367932939883200402020575402730779345577775372348478307168962525332265576245248193863075814248011678430041850172824490584896626755808754058730900033969332539612448948072738629018922604868554540583078686617488872832965498306423560878314062891503572711600832630702208454043807632614388224281070424815935995588501118809364649343461375568168268051585498310939663409830435370983043087624285861350422930575009328254677445083034516205715706509981501358890397630268157191758897041794590140864659982852929601788214386276898948284131267212527360744140208791760406565580565235394323267991320515954303176951213244411750585935550652085386486509612681293965029077039897248041174276341857092982823240321408689093873286188675502497774232397441552907564177234395377814286586765257271452314452535639111191549351924689303786291802646014663072409129595481234365341649887076843561861200500877793701549179903417283714555588238106925046748989406271536604462157184676745927653694803706226117768579733714131861536190310121472,
  0,
  (-79844263038708996533401082406278223947453486703917859574560619151337948644666837788666344749810330020661376982988560075491750365267500491951813417585205729504658069395393836064378925840211539471559287362689331550144289180940927446632118660536024985688480101969895875241024782372698988364998095619861942577674913581248162982562763415066866043881908696137364402888530193655593835733411804949304773721174851263673313485444817384385606697980787101029411570356143650140537312086287628381382770408020773036295498022754225461354265151926605969697089261741716499336271750630102163201091831198931712012972961906210883432519354890709853300199812927923705452146776798020988338536626808908980835246561291866686154158354903846734652680426955875570520818301080258936908756863915041526106062247753374026654127190882227682033772504137358635411239727757119600941829421539752024527631880483858687482872327909334251962154441763572017725849290926842097348896950265873888327415643168278836281083081811385686159435712549066965855494899818288239346360462949554045130754500152522209085086734404444467865747873733174924152848320126173969000273636956745043200251101175313475381294854662685246971969536),
  0,
  5754450068826461811772093203437572440492662401443992635338301731698962870591745720014098208063688643078688055031046564245973154608387626500309061851341448020310474498751398613896432347802114906231558962655841065153486782856751408960738965415134126127050609278754138634483648137446078523633804915915943213607187198167477368392185498431740759493512949470640289005022717136963537987135204223227100218030896212268868574693934103527147132242161219611657750901707144840511256967113358383649722831566293169855044807670119523227231391466588070129252585196994298375737379500808576016343278246994610625455248040544687033907009847064906008400710785781714641922679146936316987407171752331994228582935131229170281237004619465622843609804637222500851599268600380875543458853235536636907009837667957963957864637675142853823431184602984979243340394187518323244241132876434551213816694026526882548127580265396960345836673113135582507697345185268521659016684937022011953677282070609720483581666647237433703734495643737044723723002713283477065984104182857995175007956652709104317859138281107677942324822911121773013477376633610863949084905713634205166450999114728989405188676330865058381824,
  0,
  (-397922793872011728483922965209989790127550963211557406836290192725491926301101979749905284982012443452117000193077303776106925466152889311994184239940040383637132310985749576259770550014344870565618593433737138079877480747692715504855194722594157623062490496876955538224509536685792587571199546102320951621154378907508154789029830131453371107547616266308157228854796526935261901379128932187468357747519564997724408686131470818252616094915377455859256758611007921786297814990000868745003271429124865264423039153540125432758584032856831621135173987324241339884426380015779652172966516082202404117180698682110267934308099928326973728425644362159167431125211660653379889224358999835948141383967651044253474247291373655384208699439743714473336498644591728943023549195316067838287280240924894081642321263561011727158209933813161400870808642027723545827951474838038294369241026082978603618152854635474405618946345867663877194413759084025321504079034062598737174160654782047581123494493168400343916009417058820457092214835932962998253266261151314264598124826396069499085847651179295544093166193994366426443670514937786136179745230426920516542589993307289659794765000185217024),
  0,
  26430248432388547873201773060145791198515181679181124800563304474180429919829357588976536789747449594887516764291432060101858582538946927649937620823696152856988114316702547428717507786552291452419660408631987821536323270485226241022742359344804964441762792419020226994416667606507425865624724161700981183480273035139773486418638192668077331915947851427191645416812866908782123996626704919262563543563374979245692560749681412938002486610627249354638508910790647063821229703725871060603149510847276379465568903848928495314730339849020867296383033064109951226746657108393455038490021861073475209182040224453216910304883462845701409085226472592936754834041393586460617211141465785779935758157838419858925793966912215069639611964768219880253974741789859064342318477844128819692746704716432977668568507814597385313586532732975885968944941182394057239473306217730333472990772937934909751917082872637108419805896776836398369049218274166801267934131125250864870027673648839930198517879586538939221634010979308608173874254407571540129891878901945395143933200174559003268616660484986139492043177844698758704979627938409370769561497474042387979178525664426913058184453160960,
  0,
  (-1687947060855262574533219034356599623323861768331575551573108232377919587100815642459671087628446432432731284422078872705570788944455725340208415840281552227979936022413481816869875723655505664410821276251976208251306471352918689224504058661087658939871529390813324037369324529694112898602998241298953034915157265198582044479709852012812667321129268945678692962575049065286089295435082127931253933981798295567468761058834043232808622771370242513928485097439638928925336072675571290658366396108540524657399165779580471492213067998696913750874934525460837691002524916328425885028425526654256386575499527310294086666366684304132981853718503676783326290820795510835090080642920450947675662514972318655649118490603525164163312351291692452924485611186178566303813298178155212251550275781202351089836544892884641183730164577832530018792069455636429753867418427118634801069129369144555840330229677597046441819312070518190467286683458412489863633493352534719319577992221130086783876749231960345843182330100704740543155784480200015138957088924561740978936803966470288642983345351897816350915718977714180039356498514727202341469045662216130523728553630393576783565815808),
  0,
  103751967960867443755961869919012156445868966136133432808758196615126103089872716668793405373678390473169836142117911747526260958590343385019566588357897589221486849870260093211590299224290051287221526661048236174298088931515483122567152553482762253668624292909187890831052396379119901175329769492071201896895367975193924796967196852614563890059043552049868772705866774685517790983190530080179632810428024468489923294219065010208390236241722830445245124728433355662814714692132714431394863162350997465322302517955811580304178388643692426224296744854561568958542110143589675438644944221505442807665040212737064271513061477708522525012320026235575143434468295694208700629213570898453866451852489356638128535216002703906271186205341219257029107980646225286981501617719704077114205600864938139007650306649909264500985476936413042254064918991814727475690019385358796185040105540819161921262998517122728938149449671524467213347918635341032850743880301581823580912695314093520559221671433132000541977720125248958076881389598669705551672405488152092575933863616831474131375865804836955399246701627811084238250735071444211076308666300783903285074717627622598115328,
  0,
  (-6143522109783101347270885383238862817666895257604993230161897683845318754847765277908402519226582506241993311381185353645670893236068715920652056920973762547570803195273611673601527258956577775433681790431120944583518049512552226071696275410313333299000318996001013825987578031012806268949212885124465510457933564397471922938241953157684439073566553359182586694121017530550494649776390035924713910359251534672637797595425743984812504096076402726885217827560948907999873866311635479790666712284619604223518028849675592070136939796385934881712771392875918230369976579079661453615268080237093644967911984709243885140142148272421331283084827761546323731898536830071278153712879893139760781027701191260916564942952200363970905708867741996762998934353197099377741936380059504413851195473804104052433005451165665963030753381302554680546858435131284443495932031843024840140227388822453050021523651722646665745477156452349202176981892695198551081326913541006452523336979255525001618871937931514075947516518142572419696552289926964105555222269801828051927757690446204706516842442244319033769161666332634690347299020180171865712039123282393503165338136617156608),
  0,
  350756773337815183069576524530338612250820233553775947462840295476117635690965881296619521823625198394841463849837300858653126616636766730255059505068654567599433094897134000909287371506022233131142819547727999000538447391693292824224656579429815923228958829148171452961168553607870145339949156305858021616842892498573737987680035571513079216155435212360528549051587362654154256597471750717731990434055129251692973348658900488289649641325900507605503658537238612326314073830959208328617391131822909140625423935602050889722211986633564305980205340076218912987793822747347794537353544652643137970774651170830154849071200965868799849781378488504772905294551257520015382940629663432296200206645437297923802048626135246270753631905334130948452699576919799447982287942509505601002103002198839592164134577990168991126203470537157565915069598914466109610405019336364579962531447946501903122157429701635256840760184758533176109513024035841014336443176953108012749661237678517842206019619621342695244321024850704749532140442124888046223586421251930316273609733213042741607067334109802978609749785771487440706747940898265899872594686697300915027925973073920,
  0,
  (-19325380559919254708168608955099106037219679109093990848367745181624323352196397658687361863125538760291015021400925868758653847205066391339733602955836771361918186080609911301600265530127647023342908862447694744981685531514070416527994211224574105897080188645862612943558707650684173225368690881459686275613077855208270811436298985507090511095251616999011838646191913937374617483629119244714424597179511793955699096589375387236409659726644882052258575113192915788357759275635583633135733000629971116223056198813026712953831141411349388501111711723920632198652559576717963249654239198019816178879800529174067234387652841134099921200188054349035774388712946284178656158869912234436928316010668369563314103344790641262106578045939573911272620270560752346454357584592403415296669223926089512263675531357090460366937981193275123672847437023948346160665085226204943250009062073861829912570792678094300238513718161246960431383803750905019936270227264707103242034813866716746584860690002354881936862876086450665809740500375629468355537808974560477095383243507159510652572377292161644961857745667350308849740613929043453728298782045972920916066172928),
  0,
  1028329398404589436967515867210638303226788992974783372905890307503040387141198339957158979475300519973512458346298430764965218475306140058639320225232790540183458016147418649275834605761521322145540681821505746164411045041060200751920849077641469700973170297858432064652728275150653781285355279158312755515146811507053479203559828407523785625721481300944312734794451627869119232658695586966632226091821110482577920575840782871098857843499771115243428461235975489526512619917811948560110756487907718720328300237552849537496483414118895976554936518146129604287388558922400576392343773635798326879835928329758102571659212777069741846551065307522401849879233451459095599360075781959898795961608679795917279925907635990718713482589803609607007712443934931728800697240805410527499197382170369124401032743692598529421508700397437676567798851048876152127735557133044192483430212748402535755675731560412589503857210544532750587111151900809385667384832837292243746323305491585680503976312816686423836792704085348614270633005049585517676489679374398595830629280525748841599878939340655696792014234294910613565833416827134159857925909166857906028544,
  0,
  (-52887342957063904987205549184598815383420800109565970218686938403929756985109714693224032879945728116294126439434147482192955887665542168484921778354565886574640776992294645365625227940962799998524351697523370102995560074552528389474683374306760061223223279239106449154155496303027131879366207293436218338885488923526256428783911322886208808955496593156262140932067205984515330746385839466704536264008937833146010299044191691886836561518669623245177828011136179133989760412543417163789720303808852356291767525510126612496532448392106763358539790142539516847131369171453219828013674045016261008616214677759232923871380802975143052687249796102334157250036543688247011089916995280961878939118243908050219204233583323370993178197121261361114154965706558269870437716243897937431339399091865782524408015820394162215079003227560025546044584916077481864253534776942191836181617306526426546106039859539338843506647381725508663489479096358256183486422934734426420017173408023627192863482395130607210675478251885931138411461228297529621995534558133837533980650113109998870323183711546795382021956458156393693052770237945145151905491765445001216),
  0,
  2630903538906521549820105507863795041712068794385437233929500231966876232240068785840538764077674382716683375693520788418460366995143455281542511987621505187541180560533599356592646075098514370210050479177731968358614631443574330470274320380847847118133594768027388053293664604432288981716268423666173195993626883471164327550508543018897891907052200553531333514083154789838510977884682455280042645552301366703339770948807631872720953944132771371636856966732374565753430885015748098271777962213388871541871287051899806362962478936743327654201371757091145783161836102117244466359482091306044647344051900536413130139862622496914032399654562525844835620976208995386333510106020158210542440028141365326871330811772980900046360650487534165446562537520517511195804847298873513180222649136231938488568531360357204532989180648794313635606898807194325890189547608164314146273363480130306871857629227110768589797752659302267776979878470023286000820592566271538318904750368517929278800235366608066832350769010941692225476232075889959929743594297552024547639464134740589883842229028251454993410616353707458038248482565501551162441207461707776,
  0,
  (-126676603832433429444396475416102457475916633383168562340121481001825452993776937323611893643284077910937583744343357387901040824097358142532174920137656769698280546020487206591332764409534632209823505202415332845981780377676888616761337187961090921740790635490202122469443645176044730063076186397490829145449621279362965093125678256586700081253951596323327547577187137637590976638795325923003965017920661193923845289329947529975863575259293167503987215178003467204578094212437295220437401584529227123909645577690875382086022947818211585071048324551377269328917164491044387572682958848908359458332609235804575466506900705322819870075892866354774767543737961148861427415797986811046246612043062922361174055658046583405294360860339302538311467455303062521463759058940590399698144335776959629969361874502093300547137473094327121596666529708045313420870100594627486127011103360685873913788245903940461173875542740815222385999775506111452036808824600369399717236609541913856417962416845362052769719316975289986923218049246479276783787542983923968984459399146906221668560128468155709909737435338973792901295303885353716407242588160),
  0,
  5907693704029101290910037684390609292873342033955920158273619836865979158907465331927571390386006601838602826272027656818337577051639198029703703215382472431435919966892326185877615422754289356297786163244921234393146958408839547278396398420477384325278226370250749979810619446379768843739552044666509968579003088780442641406773922169631487180087892412087290552822197744782442662946718844706074486683680095928481082439672721753781436095297550284658112995201442049255420833859866595354385483335819986359361645962399410949697142046718925564784773007417813758745111691365588870084467833196102924719915453598073894537559713872521946720120559304646324496581081204091766903708328437588515732386550139832068334008076569297759409722896147646605343737257491995276448794915248992006595077021952181949042911855985408095358323577125873146695903255199903017235872871044828906474106140173534263070864785086916292157808891319200842116674737124634940408606855315805589946553450917469676579182473371158604804766189331714545401040906849188120406652594224809420766980701900459307309466388508932977614991938212857895917057630410479690055680,
  0,
  (-267023388371932416330179430684255914888810819390261363785499522028316250275256679044670071419400243624988977527559053579706627886113827369332609829468875984851710582804649176398943837796489564458659201857855140339728630891420792515079485329347365309020230219586875626082302071485340348663931561657603378542732610422616013864494332706312515742994073870680794636078247148687606986614069459889529567799499397139233694944516176453143417072238640104083011236508226752754051814999213603980534811310172678166978639915736023745303122333972616994481261780535715832475072598828332554990566061551071209298856927179160191775227210321696780333978321412326871978099232593629340045972328232132911258455480624454734855925511203956759247498762257328991837878998475895611397248750608194422017557709198962931569756444614416966620122518481373197150667875894505612746880141226855742689528754221291129748195592935542399265262543936668991725475416446440993565640823141481538633094580682556617211838798051553286204170606864250648692253825096382345369188603110548458237247272531353019152984902925138420821891591502334188629076976703763382272),
  0,
  11704659592568599254703562718725980271637410206627923122629920461081632966130010009260814200891625809007230483541698047251687935758034470663468217022353827722873520045807004344083899297882009974220433196522962460430241916511858586788836576010966769871651070593829700487630271633264820573424790977660390479190793668848555703388821601412870880285835426753500660850690865493268753472934362936440628199633692678039553508987848129765836973999214981763789407350583263494400106303340553208266324530409659946313687872701821630448590568193453106922016893194593938516454295058650683013180026996016589328969468558851951457264950313393558540588177639273961256724501367062487036289405955090504388207859541547752004739507376451675532770981240644387348953966743750355431626062608559380086846854582225450671791667379376274557510508145861387115354259829200130975262344543405371480076206293189959397026895816018232979383834902191556377305862542288048507159562908534674665605236919070521431399566557223420228095739406128958732920299945799475045827209519242015770894010776236457492249775039792471214622187488578826888702441121906688,
  0,
  (-497856480059470878780680075979337462301985795500051469557419214302915410231532081377134608678779786321444413920309142792686112291340690427464539919338725511445602085906979839880533445231233878887813485393392889854485694177459623868010764861526682382484492666222703663775197639737051164320950557484521473492902448435550070026383091969869161509468477190842535230665259262009021224787603588565243952840169943698386801947152354024704331184944574130075038838429248992843708398960584314103351695948864939974652044927864932276905299903885075333478124277046151242476585888704647909314747504285498008232625975240270209111300230266520392220697654019296725572384719480839145125454879766782625772275761022756989898042444260941684541844385945016511356306764634515160509029470141287997459886290765860014626360258158241300917177709930569525517198446636286573736793886394858978732672555743372512289503019559599763641770623792607411991086178564549667055942450682188515379377631471346791118780896705440745141997249004076712689926135700871894829415782244165056526379213682989343744848458395763313154209197572284555565264273408),
  0,
  20560475631330558885649532951711827265295332100832471836440063555620426759559969489633065671889027068079426962282955796441101976776178022333902273226454581657984776726713203849446975824357295593237141156960280770989059413168996151644536163911851602979332399504872141836676769980474103346045364355238079645554159735070006152976296688771962668206493347643785155594471502649504009875721368023385097784157025455129645023234031673779775101164929580613334856325611237433597689269228395800487545937491803627559283872770731301122986470646221608531653673493628216959806843562932782472395666474599616885559574215482788406458174770923869573524260842007763163357093772759246456248648003298061414967764916046852364057818530686852026076392825643200865574223628153509295645463003614471320212017997335914004426598742698212746935182728018596614998326635790690522698202737471147101522948630958759599898892593580314385774685021310447327467263610184655877250909467830420490227042620744966569590494335963236922835330915698978686954032037336079023916147100826675335112737477522353647758692795288760823937978328241429624651776,
  0,
  (-824867238384782236919615981105488150306833204338030924198194140293861194392452909177153786421230305204691815333518375337939675335863639809482944930812540877523957515128280285905078212862757530289453317536939995366098415464082209588268999197470385400710445482350106564873467229694156889568875624378676135407021857298385238949670854137292975069112350743164023852303482825843703881640585760405030849744148371545222163787815694304465130096516661269739497541321485227485509640315146380533613543519038157005315661216150118225898223971391525167448506586484413176739545444739096611764675368599695456954919237232365089408414640846347284087486058332992131453664705350952589082008160253707137925955642252339671723394101345067561109153301730425114350626629819099446766480599422903172148838569766630357515762863796101349616197304580152503006087478390555904689447164706482662477840937479476012365729264969048936490559407941299256735171174255791673359455913133777374531786710548632051705882264825115343855377731775690702418988835764440518628148433157318897949780252649411109308532438843338765227773137854371201024),
  0,
  32165199151568972006964273962934310495181495911944829607038436228211907311764143033854804596734838373145435528826073934656064152801802410948241552656449696491092009142857479105873372727717438042526918906899113497786785632744176969833650192116368811230167286092835498334960298184259459131990664264831637052099767945034724971780823773155827982875046991928169777126895413855632510604657040471339457209759130139502630843934476285559238867098675435516720212178096327644859936320958554098714122533694203623254888193851337867916778630323640603744472820989141388403952974747628020815250646307526892009268137825726895655461438982506244330786365010186973578771377538751601986022886118890747953932679555423133950148630008526047360745199728421354429053551959558384777677774371429622299282392768437985680837165496578838986529721147342879550981961178886618733448166119674319165190657814472922982696724375111985610414683404561730732758304043852947666246339663803310642682011206657242843342247445934122351000969889542143266769362157897091142947470388966862799615209423734721159925311402082992318974517152055296,
  0,
  (-1219721576602108826150088632971668106001195476829758913754516250856293269609287181624506675673896587050918142000261340531534744212982874224530427086516526382368924198303464318502254011527210079099085323921412417453077769653685502312549529445169606685238117226131325305338139427054253111022986399011566401574583890467153449239007803035739002570387643057737780074309689356174833785948456744070166222719575034145737317117552412665055493943900142960471580335698717229016619008080450286952643280012747364499600513253702925800229567944681303292404472743629224401079284141952879213353795755528481813762415021880363546144672977053283297460652903222317367824218420690041114001513633754305351793039759252109468608234614457069058591946295467213580138212292661891387204535074927767638711372963424148150117448087727955440097181386707078925700379408527095573070663508291144521438691308176104956784484105510090395674910815669792936517369870571688269877301858084705425613925564793736324223474030271840181466396855939104116941625080227006370767077824931038301882202662682896607369517429837562216894156505088),
  0,
  45000824534802224898992962916557103890380752561335590547529543422967846857314992077960548252639075059043082065340426632493019727220629715543214533815482446024505640713753979332968524329627407632382526511637296282106388123379159605333786553845466058673708728136083900158553444614950299223335378101856337881604943767813313550560228786626000522988604673669607983119558673772200610397188245067561527659463421972635196155361218826197761021928013960119586792683525316253165585876189617618234961058067900506576995345146507078380226554722637097551251388500462757159757986120883529455772017709921855105644058616034871757010491918242996475597742370453060488198581285537227066038715886900819844843542836724572664506987062736187050170168798602936056119279842850335777586689405721658580863521395498130210661432708153262869431489343321313089748316790341108258550025374131834817870198517431876139202577886364291378696483251010807678226663462562741332542644998179305191450928448255264436661560445429741890127097503711284492404389043090771309648655488063824777077187307838451266234267140612768586006528,
  0,
  (-1616110480979310286292532704804249893396839818193093804736456519211256516023551076712997975514235777066874367010818800069752582783984439816151264874084710717177558049196165218366228311235399667660920217768791797276065186966101412183825776363052762491088201831543644695237877570462873600799259790953655396645209609906533334446258844847823779630878141805724469802083991611088455293562877029085393311878205939522557820475856790663366374864621134229238115744154666283966065268672865455822709906043434983331294892042347716610778220798578489411669623368948396026353555508960522796537933841184552068836257869662093232872928865662439862806497122414931923869805809302926808203502863318987412317282429224992579250193086711617699813529564901345970501771443739961081418511143945868480806379791468710164031374046486281382526766163735850708192923789372225379944934831542116107429619235768530671427284463439084177194029783420347077438499740249634825229130326100168819970030478649902311300456068253094961787191441418572254781821836454216974027173710711386930090744342543695388076616232094515855360),
  0,
  56521126979736156449911388465662133899775318620377684041016339270620397617021735579925527277032304139195553993122235652166444513807839744913846931051047748747145238434014529648691072995097241739651326850321902758432939529525357690496837324141531897654867946095018604698403531442986276287642034984205568802473127729253806305883576238983608855965933719864371774682897771399063879270370110724402151791162208568569886089787410655005183837294962864590453739350724454611093783769856960687208890010707445536770294933070678480067910234373206003449740861753437665785899369680501788737261430203759658299353038886623207992725847466562196593084596086066340363070231470197499042535478092373088833317498168345321752913205495570775030500355776443010768766918749886710576958689850604832039626862333859163994804775208710709695205001170244926373443871417589586908721192429056030417818599071902571000381262218719052338863806540343333687585054869834294376188526642784955268909516869474776485992515716602735444336281540501399998542338454418766707972633405742841358350147618554392270683564400443392,
  0,
  (-1925889603047562159647364348388139231041028962290861651988134313334671797965796380592783154847658489571778424516845853329220637378348936749286318896263376870028888891719871266161810116354750699794025317824469745358826619307000288474947964496604295713314346898971961336560420917605442694028285540119110685678620842023197038135797719119545563656514792024734463084990608365500336401982019445451162687075072399732286814657787030548296185110733108396832779349278184667999607847964678539761069527903072087379051940104377374316495482686564918307188212546868755256509663541950983598448390835983833526884049013131565354274473373500851804346777228232948885238681403389597921401203681133456474174968365011858630703476486110229166352157693807953456461830023965402496909716526815052286246044868613605601263037271718840040471146960597293522844961882395936007498090161987623336656981991845128597167133630196978310555399203003751339542081461007814817469627128129008807313813124239911937421646012553465447742770437616883994017593536868247979192277261255952246795072690304051309414182813696),
  0,
  63961402383634196504246949203365090053759174893615111863067570355364474187601694139858242885820170555973278346611903797679903948930645836684692737305859490001991052137754700875700555403047882027942870804838011957692687070267031702441070816803103874263206439902769018845367631972456367506144281688883025064002032754850852683852604262480115070904752615956590095230436788424825823807799367879870131242444313452487702848095901770997645362749000154633698210349055965783229314264887904392690597703128264883721486664631593412786953842003446188437641164964662138331780515651224009404698045579675837954782024718206996162485930496688184970918229408767535334504442781387708809699775326258109897712543600406533604487327475177489980420104003315621362170439178320695075259165951856766980366679822591202302216816783999168221493471447682950326486179806870237590904510275741923947345328644404026147425286501315478007899779234478833048082317442463552659713751728341787283664029341258003516732205737619455920088941952059055079632098625342145219912942188036578307501964713032861540679680,
  0,
  (-2071331856129527125222073349228817339851093958719723907957207889622509547633630810528683343844656741861878586465686119703502722856954102074946054044819935612348106923343416029278266671937643980053995114287333329627074463753449492773974626878414876092019263479989837445850489374811416062353724612838569049795790664347757394929962792773793226410607069954282624375608992094027860312078902848269383285713245125750930514777028422148186804366749284157885091993589848334022102834896907231156147490675075349067508084218891727329005303685483650341876945865244102919958301236910127457085898628416228003587022867653130307842148408848725744620242958822796301457629735957670600741588772015739408550216220055849852390356577179382546522065727920749439924460014111172932289399353611285563993443615740831341055309516298695060759592673358132034202708444055562827875265290956408174882502648331329486563931982757467023883864415612982707629032464913156779097721188131400077803451230796762277525494709394017464088304651608249044457302815504691729938021558523363284794111009292787122176),
  0,
  65433449824159112138520424868126457853016478181968881271165178571083331393002804992848854377918478515282124334745488835762292674041412311750445438791996921622611614523889330264886057037799456395321418720437987649310013824372512003583895253468684964503663682258958002499309293306450144760027338160453607743997777746005786485655064021985539944324748214232570092480168913188129464183014851827193759092936680075599231888488053070773161256183205914919774638819856620206776333424704454520988359503703619012977299313649462757878302510374341857967351248990070797155399189558973237260208197569318101767561559141655841453273947322590132293509308828415505049549897969215887017428363288322490706565298050995455730824525069447289793530884115510096799559028914161715795077788121148132917704990067979601841317874735077109506838987325233526593208781707710681867274491851540067380095250137821644624423043623861153147605772673667563771577197503408734395330184658623013691908091888036965371809807425528097422209688825042406794185933280501787476977084015348630157919249999331328,
  0,
  (-2017140585617709323141273693555478357366776647515112636141225808883339807638627761440268186081153668367546982207646211623165018679898467561542349700918604429969319096788794753010707975592066456605131495343384074939317163858523034458617327599357925714013991225896228736438567419938457830309339196547144436649665767950772526213870078377105988030496256764677336547485087064355264676054357938114679116900119495419866739801834175079242540620771322876129909738534620346538514724314333541770304181999099747297711327416452510986935473662232672187523398899370204778788721647587151502947928295862854768570427858635884604385307943344505398609565589876549621506044945432667946373911038661651955881527964927225530767718963165476952252608950525928882156219462215966032841579743097312817023339790905409964752021737469929010635685249701281626050833702783447284863723326238584303475502658240867398643993630257210136946390502041270904734196933777786361366206825841278000507719417945628305312176098717661158219613135521299494133021820918499691744230381799500579205348851712),
  0,
  60704553131898951383436286041165251012902009778465576859847020019969699197086624199458771894846830045408445327879213570346202453420990661125612128417291540837012986785363265132409012919752917532104889495405538096767995300505535442243015254672175477435858098540576983662346099652114708233776408023070506937353128198080003958551661975816185447779470710994891811559540458257330782374873467426655259708416621486066297590544705520801521765844126142216012981124112821937780643951339969904929871259327294858676186347509649351483768477209292916247011667874317015696426302717500951678692734442877785407265256941956234661856452981592638582787625659715621128103660785759895529010442905874272009629163364528024864884392555874439506748017019096834502257911270570181613983987966180599687016006415887800134471062702265845529664478770852730842707978931388654392208220987857996114156892490176804802296226707426609676831882939679723438922608569069712932929816836311116464820812894103214728674607261087301719805791146658798707960377211607966916127172174989263382773760,
  0,
  (-1784073066318537230610082310983059156501416219411277294408024535602525341086513536376943022089941469086142494897128880765190391588903948827874748687313904843857084062765770832611195786044326217000658220570608260244632933257550577287899990421080256691851448787953096092009807964844551627262256278237617272220338173484663728161465287698408698555996162949477994093527969162662432377784828890417750522961434278887093790574664827289533463124444971083907236623957778721047873411979105131823641862423299723764924061424106409631271040625146948059038475684711927855998721881224059596599249230617957030514429594494279796957377079867857734021894526844261187569993669237391768754122502387470779412385828598134900363708169749807729533062844188617606625335884743354553384688428324447881001156065825606133942110434631828422019877216489373568475728680138207520273446352912053603257730421091516754690601722469240120408673895310615562601891260386677999296141948931391855739354940937225292005118820163570450777253240541169780861739042790305695015617735441902469120),
  0,
  51222765303573235091041671153576345223971732198049944094309081697369566593176228371610739129064938698931902870164194505518972826276097428965173329466390246154555888911948639642568225200747203300022974587263207374598837445876834463221205013670354740071047664641098411287070056640497830008370924022917657407748382639898914378834141033768281624434136106263780168059556056817697349142239901370175338083183167645799540248050556176059214468811326523638743423656805353777407886439839796631298906544931985504090570967644424541562196878703522922226001125543836289772128621581723035048515534908218614845128203200857528002039700095361701539047601361577449057876491030708220966671917224303358302894454600996153737711906151423707378363511516290267465104983875459817483072699563623979904838749916940555518406387281619954186078439530353782000481473095001511694261652901108543081950206574352096388047985200529085807509647089857085285303499845350032019662469938015890028964677240084918947857461287443434374602585018736683057448285106983568701833174736437248,
  0,
  (-1437211206842152242953751524977164520941470541267143376766171118586772888653257549782989804873898852720809898673163630625067691532992559056836921598686957862880711809751267146198071071122673477312894339538884446745440527515451083290575094696924114969592557494723340499489916259140230462010554670403403436290752755317968374528688088220338804641007080407257769634401760185629176522760950278257230654089060118170922412539733790076291712481197962052337998310530056431322536527670319541920552092533385836062842211836248348803822056858969997987379943114401302154443831363738339258171840036734135870246556119980784430849856745415157961537304276909309467382902655171260357488972491826041543708294170634955738267238202249189449863117463837607628694263063512121963236874766861536991015780310948125364875845007223960945532020377410105116983358737594693666919757929995247128382116222003456344673563505364521752780592405351107063098287661292621737578646477656142634026209254681707416003906331359508976554920331501845585331609201109725509430628319232),
  0,
  39421139801827839111926607702405344802306859948862979473767189882299093059237873153027322704236842220536544614999168884969040193127703967864701080875900088178896154594021074360413371308436531407146911115060680683655553028968469764686510735427548581236769094651302726955669262262717839574837409098425066840610526241517045899895390322168923848951939990890945512655352593093472128036194096513210340155859208618749372110389688453380255466117608217401310878656577666564521249529902096488361325399235423466098347128282283478622860044448211106151212442828472633752471535253612835140317530597908132919623340739284369285142410057074140590379129483387928798088647036439129231636873543652566543379578527519949162251703104350328789272884166310008508199472882002913127623801153493709124032832783533313426751833555524756810744450600216243962537434542240177802815381483023010452100405039249777920441817129492728934704181941217856399794591754522552318790479048282069538837128793129184037814879310466333547077699698441700210855196461981957896536064,
  0,
  (-1057373481184157596817272364534508370895622457575678231769363745065761762673608159657137978554478837315710427288814615800339030224120426943425872659897051727478416884096180712443381384318701110359349829901448234205334267112514491824198012396773516681969671403850635184382118049994559875302593530971342011690082161171276051211180672863688447037672074228444324096651816462063642712375727323771534568045006020003791615055055406732685857663528841143512232789377220749474733385807576631660389744158972496643763565116786242081586472558067762844626649445418305094174544138780580925666234763613562580799993618922045480267440831389927727105820632786350875697202515505420583137338851191192557728547830591927450811655013054745321580517834316353603685538590073717643685711241056346860362678197745523339715543407433823272211805611232256757258645410794332701131692504571204791772687529759677590448765166395766048330467399863551578092544541226884223511512534549721013256895967387417387782085301091458987887074353202466751991113423001915228160),
  0,
  27743034672424283837576539038330825461939670780323134521183594415090600481364430341056414034543700645667149011983727031751876450861936749956781563058684414925482957338237293693894099999446586317618031633472036956382951336850263096407992588786951689442430162835906362446495052915271496542771224915895845088758110345459697957188258947389420800259140628148447313111199853919809783869588483436050052611450094448391977301588036616895266789042125558342739792588321233824903422377628856388759077800281772690466929196949199154519568179870343321367906107178410648277647251530501891964472978455947125316103819037476505121296925679492855102045536171878422137857492631338981120948828514545859895882085429142395449117292139342237761196089435031627602441555319609746074392135312510022212696726720254389763141276630423396670132566420967715979542985904587431565071347431165777108719945909639471158535061962776471359421098890060159002836691060529646005983785535712584281536906918849260382225264008846959388847241833189126387380818100092928,
  0,
  (-712258544858488674898577618938846175344448979176231496147294286832752023634788340235380033169465404584205140576811835496197685409181858876808683905658876001217997893820400943310698511030080365053409325165081886114983473792487832271334105959527474981388527217005561504267731558589115747209537058472419349284090943035528600468519938326959151002522423548647400088787289274336700685736091206580769134483980173455460471282044697757990916479185464186553811216168727486816737964369871166302232457612370228394197927784057963201736799554333078481060866639804434999625340826084251669816331919209869201955565592182708052973215509590029964463458645379253201937845694327714608589259815186602674070729381114660389571487154316042138552475813122518334633102648923359423825260019322448037284998649400428597481212381791042159037300125880352496395101005964519154941345459464745019653025368598139839016471565752825574803790240724552422661643836025761239653879292091904851387226613712350362823297825969447573132708580508602260531982630912),
  0,
  17898131953908192921487437356895460547000390866050541009639379146345414461083068038820962643051231217161556552674882355528019188858928461200978122458247978602376591619775565318509187829374429595233657696967999775747761177168208015603352468864447358034425217569836228509632139569524689332085428623965953258924395972248883244849917989658605008727426019089483825728433829730096131789887490084022300727543812178124121642353076201731021565690492853238581217542037236722923461604749104229746556287583139224052270175523521942855749867235011408315335269003943339613630356830553835026146307932262629012136330597640149627151738310211729054900394808019949556792738209001070406515185305503866618686121699418861788716811469596170286280397772310601955995102537798987017113727174347109160770113867707877899705605171798592157085536681944146507718357624734460885533306882725816193427818512844711053072001301191541587554270185712135238802404974789106802043369522036533945833556701515773518720718529551702821639370506726005882748928,
  0,
  (-440340621705781949436964861624425942548940058833783003143292334396002853219683656644741087167702407100781768790464810615302159743059981693287296022928155509186020072149855127235177800453645985263977025988105967714365873485691234061957281850339006775719005294790616177597109698615060354282517641896211497093973350318286888855535570266806957018987055258682030993438902321414721710739183888563334280238319046245224959462568639293578428394183244072634104024431891333339384411201869669970898089339462185832268039796482807896778074158185501713266265748742517455544490522722445288748479810963810645375356358722097238980735362842269024110068870944526288810201542665709913278767260569257249378260493974658961426063024995675668637774109456179926196641098381868184512590309316706786723500671501634699670086359328205062735174101558829676926871287812246209628917316784521769857456823265462209659050128568274223601647197676263518355861117931899883203060910105029363496317257479328174149817205504201815835650644569304858624),
  0,
  10609675854609338044261680302408707163691580810045085906294517529876653052890272917238124205244154762589780546958508577389243965171626735335720219472220329226546722080296590434414446505211597060758717365677155283103627425477408842608382523915467672542085301199730072374556658878394245192921490608632568010693779823488179118572381695717324654195554052113517265232511441846460613810481067018677993181816843901928874183005893667429037881143388883902224415027294056078097889206122304557071949618834287119966094554021882924014545410390895918929519414586418822746818217856318029364588861184073015050941276128733982867413311363713023148926482329785964807671589969798458921995447891099204779847247559347615504427754817230122584124953176679785659855219278072666340443814943707514638919201184176819456634738390290933919463702376286274169509261076810749944007221361353828811485320143571794270358181555808649231113178957507454838108871992996431560501518347895839737899431085483506349747204426004228534336975355772928,
  0,
  (-250418195084207715547993055867292814574779362982613197297364575835166092505743653244642549356611520434599063526394812852120085858235820892930056321918723924345926279740148915093545311158543800796743596508622954213102214674380587719303163038279600550841559278239187237495223298121978156269123430761535715332548309643475943725248535047690523188707499119932590018794921602340862396102419349376687706173901545773821277874030317869023525911412763341229818501855334951414093728175369811627071945227796652167425913718001800253221328019888039059592486185691694926254647050490057809176486697593075414957299333755032032045923145354298211460398281455703099903706325560277366945916860679448528195697164075659383132788494477032149778633910409054935160924388314745645885096487499862745280178118681430050942865933233527644795311813082778764803723192573318010294498320057837748622665488685253450518233988789821736794584814093211950003304767411198865863669318959763885185249696688627081482786476857146741686452355072),
  0,
  5791552932749796097125935991604503162735186741782550170362566493603922363467013407510406051624955012210607115494642699273871487790373504372991810483096905546367303646262151282551771120234358595340548158923278425785529000780746675132752920514303901846679275973914549187420452029184091072121547843278062641478765620615502453453456923041724417807287370331462636314694628431297630310442725772229009094404930115678274916499395902642942353056002098839905216432443926957784729203668645618632378788019324479700150664886356376970714913309445370587671107694488545107629062459440754473573813394548184940403540627657439504895219449977679960857719912810807261671995591268965729243246378617779751903644432212937315539608377914243006073476738204504458522789452327792630311497328192746449612619092251573614052146820481624637417224814972687547227089489685091685611902574924871428753071851063257093203911360314123165297711554554412548663875305388877807614340728519386077063498667698081781804431899721018810302464,
  0,
  (-131280906492425308839045307620718181202752720395850129373438936979391070961390968665316754180947533729637120689454094492950638610030221375207792680617729469822991604148596397403463546183835766252758165659200276495512181919919549938178833117074722938630269717171036958896659808093598802936658008201101998196181374115379559957659128685372769448401787420653152567111652679095121885956488811032775350075291066430414418568305641583285819878377098891049244403376712042052490961390579668092781516528974438626481142736686636504247774327895055063380226200218456141738284053949000508665194107890252097138783887639926305512384025478783292197314824723365845005399581334601247810444683456765719926628718541638548795154859469444893676635885193125260560672356089384771001107944043098351186181770146932410618239942416228002257667484188504519437666262186708487526648756503260911010859242265150034069179396066735790266147041481972010343249518823598721940834682352562409477834215524703305446050924346577256448),
  0,
  2917390959357733669109288562910946636805631122570392812973151421888676577413118958228438925079374404475189732222084908459995143745117465588054336521934496518866856093256004911978254387615571098394839392175991739414116184363035933940362558469672183863535527246259948281410632433908612631249529044865319456347769317824992714109303418136491065783827801071327704675044025079960393727266889781309075213702480101317011202368503231018209703657775927586239815852745634759916330273784382014730392385689179393548832368496506076974262041759139884020518706170478007021402819476056610591460107871845537014618080137017529322046564034499747279822965953678407008777037564151863419149095368946540328929139075189366942542484644636893882634557218821831378491360065351889409189014881601868308346013522203210764840865227975945422739348569599574177973552392582963139355024467273139708695648127978244800809228677227262345174897226839429981818151471147789765905290264812685624149681311428080889334278528172032,
  0,
  (-63574157772991017461156035798671373273330419892206727624640988812796829055861178026323599573189153015172864961492067351771578841598811139084960112103377003917291852830932567902720159871355678821437972752717845108219350046273767910031954256300486887957417849941425061635413897116324531673647696134551816458878334225373924464579377598358973465862707648661926880215522875413364150159144100294242488007660451369987839483235787214001188181411085322733772916180870724831180132890987016067569086511576777672576175897188918635602191990469406381957879778821401276758974545540944939235521273683825515900542205612823570971036217613357725959547474831600937588179663202896514062801045066569164372430468306769784168259469366286162417014045100407812210222620448712633450021389413387060371002475330269250497464418169866767897161994927875270990611944007119674980731835871212783452550268129037934402516270383636778853725670214785488443965826609017433752489317342383149676889873268354395629842071552),
  0,
  1358824135689153534921360748604484552259183941960648122320393652281190279743603383371706419374611422037894353799180907182865268093319171585637703187798994203271705802088528429652318637247276168267502720261928650854606855814725520418994379040548668791511513003323307276495171525720539429997378209416933913996539932186407830257412344412712477873351681281323335351504424013541062222364838588427630638299673384396512704527600028589366266571541291333828120768547166891482310905896575560716368305321884026230434570320780121826745976546358283435057029500816790252906547951316544605280701997329776762959885926938254862097752725852300841748262611936602390745234381190082475944410128198428030596647961575734681648853695239374513608896060424425247503868272517321848488800459725546971480579917114532453553780739315610354885415606554654767896466476242409750161691358375168632909062216407694012568846057446572376170016465189840766725305775673488398913436375949211292121548272789811290439680,
  0,
  (-28493364249956000782717620140483750428102064866512528421401231008914812838907406784855713696237098954603906569676104634249980767325477541925508547204304868094226591228075723209766800649789973677099480119879011146190426207130336033923466754536717447772887386129737984803051533711319895105021706644006250089115243799883747086660650466682900633693083957872121494041939309815173816287647273884291894907102419025605741072622426822913138261962315361815187774443004082313459182489097355038592994689816174965438853092903795215944864971613853582110657312364296764095566661108979691379134497719707129403600618140911654388150296408329714234631436417818879290099311000725655469252657454668300998011326410047099117718529171914356118273395763171530932190135299005451179092934266185551304475841254110297867833832248555331536152244625549330539154060821970211217959109405790192855659730623987250849357620018300175530669175636357027260921928165386401106588414804038181847865075101736108032),
  0,
  586301192570871174518592128886076600871743027193164094386535386390576630264153457813530276150633511804530833622503467297151959086528399503344405924518294552555373700475932774137089519255789558857313068235689629128308196732900746927723150238463870577890500829040284754368837810693859609858592235208916408830042838453852876203489603504454030771538624286238813086956845669600933910863216073541795780608903119157605681918111533719948308216846036609122886097314556558080177885623706716554574277072841218344084868387269409949750311525347404180611664037071100042353430026789813711353786055247974517468449574413109439936874111984468167922360754542632864289748278137224150497105752441266010967328094759738605320803985316361068393296766306485736395203769916720272266650037372099352620021363706762404334783593435129652095003960565139217227973108083294727185947030282292479042944285886620122906995961061217356072159646269045620398670455171816348730769568002810301657337277972480,
  0,
  (-11841064745917993894415207140547774648956581234663684219304890654443801208982851125960215058603466091168154594819606573143727409979994432622253931619452574470597270338397305980918589591174233963808064402325829903406980507252513141072055621362564987769486440594541190318891591956915342359836223708373911614657727922031480901683704390169311180267885456216255809386770152793588708942441670324386588577610368480376735259233980923704408249865604710790672251520462207705703444924011361008742887894856967770489905315225594534452589284806657288065853519687662751780788948759276380790703443380857986387255412657499810465936824050831485574992862834667973852895887711952144469404024202913238275663444368921369663338134707994483130353049357872032574617821148648416777372899473775252712477722999221972489513817481134000784267151361408938247112423366477442708460289195099877014846534911222132415820443166150155279462433785984325343993288323505288258431637927481534639421521920),
  0,
  234772779836275926933125366883860547564295667988439203720769835417221923232872504086072903570493145573074775330723343625632189266817430972549950408217611621500457821244098234391849069304655696401194910786647336069419557723915948832660097252404442873539099819547570898477110598620689496422249675050730439472292488878138817622744890496462978769057650128681798544657170839643151772826848491310953564578707185008431186132049381999785013882752452282162498764484628005113329442887927497850369388597061199536269620653217674299804043268832791944488483719788387227499096149046953723924196919768432865441730680094445114957376241046447964051406935573763093233349399296779970082269185089465769078773216376808896522038273145672608983184402351866308592029749247629141751889501324231734157146198168325867136628957395457894091854414389983951076895860702430834822357002229021307098742244207596633438796173204202344812078318504588851399583779523103387735513016047616621805568,
  0,
  (-4570709419412871840539414563656657929460679725563283744993651635414357799008808141932455032601918580715174787432523259163193124996768164361613119819828857869936593773935447690196500418692418656072994294223527537539242547020725022394638054283712394665726177852890749028210970451910132722098369362865959164095710459619177389753021799330433650907003409314627328222493340139831667268490031351835202094598917215027390676846093059313343165697787349863393543667911791932780006407562955174725124134592474971737215830793233199848260086078407498892647593623217513316105194414833960017444468798016538690846135562661786431610806907797225450401958423628770008558353057461380614968834997137041608955423225836006131282497652418385447802986307687564951958346937432123472906751478330382424154873118318304108974531862693529523656250028009663806276553943334593760458573458492989058377822243327821280041729790135634482626227532339410600953970240740520806091215636610940928),
  0,
  87395307588663964833615361238469430195179194285338780878316983661168346237468466960569600561856118866065087681818264792936399510377037667464351388538003730847367431944407539599064992741907678694080216865285748744750096902520920841224769723826525564622988428250200604297041366882587931410765733641733572413413948460706915199817803992065686329824553783589828130471767461108269229255639209010084863924122468784352670295461199179338727780665698268430215817839056071795097017858099750823690331820213714686964361671458889908649064352506066236882497080830690320787857279730217756587991961084940104095578058293098795304090997205940846198410776518447888536765883078679847308043050833446500521003751555519465073818901087463198936608513042101523522179270235217527206524722531052012310929968986580632921334757183330729629479529613505507888491530649134715520326518153604153645320071921259531285375148967000166015910719019446261538185621851519522333671255179264,
  0,
  (-1641530474492539273178688548556173939159425874693595486157909914210910982463844488277016079223608012463200626443800079227740018235075806630455907063283705886013153111921753443842811365704810188651256734145872686412306588462271090949619765355199295459633699418178775022679478559168659947094191607885543029575589059542692795525134716699615679724565903656876636129096657038076383051057789122246775671795030329839403261312165351192982066610039626997158262668714003049341393348810994059400445304490111864205323692778954494435434414610346080737106263778671724241988159983221652669863324329802194023690376280686341063707920609648428519541822207274579970267474269750184703283111656680858035158331078430169485079719195033841027359227134134684979099332609159880647175938816286845903316518098570431340638308575437595962830355454595434234364134443379479401657694163943248314692584714366770553671966359197318132923297031330597056030716983078538075734802432),
  0,
  30293665945007402935271594669631479025521300455880692292008064348101154137702374047806353195842535949265765996798883221349969178078912836497826847392266010979415536313032908509722553260663084023754323353902420938347282572950473086507049422387950592134014897069369947992669276122789472843856520640345003979090861220234896323682749092235315161567194652759957003304587611448347893000124622954882731625242653021658582279822461829229444475704579167901562719823776229811110512474037970148404564916619345622296903013549911657867827281467796901375017489237141417886100340300762859957940333169890741307251843311461468002137885930297962647818575500854242962552035462977840809136039180565052550007743964597895011271456463807640223648482632365515311782472644278474676468575205719067048125222361139647979751401870992022672552336010103531091066622049652625266449354490178690452852287864788125684771585188633145542894769598171972849336899186051860398080,
  0,
  (-549389764801433059926979814865393553449605194823498002547226166311247592036778569295454375346483198915526926602775346583205761452042876127387762050370606419197350109973219861205654746797708549237276452270200717365796679289202295871350923925627450234351433635606319931452380661956038498702862250699811647316129391598815951867131650560802037290639364134311526442847448249809606991708377445192672042436886750352317414872963489906716387712517290108462947149445395380217726521917222665824270627255801668551857938370037844889560356697444138329800940549182644854321192338987420098338092353993704020371440489827576167027132906688446732434207750161215657023717407333818327829735034732296038897500452848588635783125207421531962212116511324230328431068822462698271433951528083267367591599847693083379398443898974185029294487830217515464004693273201882381942825688937054101678320460042275587300927075230131370122236825588987818395382892531286016),
  0,
  9793030281498897084680787098382500505028589440717257043612838526158983184015506123141344643732594022290292474002288554052665251593410696562438800960315521160173261223234877078414396403980693384686930509938510630265660018994737620008479302597595334442379585848212617671448360423491473200165410727036823523785754593997603521068851821935958081288575788362204075504242652623399361544339940250080135591782181955551366519507857883878948482534803343245145511756018573686102400181094417613785065004319778773167431710353080724693229433012169958340959938937398120763396397106351662157078872653853359452983371452173919498633686873113952133032675807431826551156439226188810031726502938100732293511932017223407988722312922127941664282693612051868049921594832224715220833809115690642540327888589431051254730192228977772857559518730224657509056328641761366671245998628213795538613900800827738147988727980769538178180097583084790893683763314688,
  0,
  (-171609605696540590190042640473524970666128967422909748980988040505868664415517023294572338808202043756799315417824804225498874113041170308153411849476339688597821189228367980557780289238385060406408846820375529389091888065275654434495154267300185644996275875522638501801600247756945765333377361513377508569485458707062179378439657933324154620687339988409768357657765223954633805214879058771695437976324632449785266020139834883416674133109650106644514291951022302907235492785268644064743678824218144638584200644289483311691029894726335370108463309109952064073940057884107186366084956708963608965033150110924728442017617769238754415208425771701610913866442812680695685408704218755660844556516392880285720533670662194743544651184186887023611172311500608259975982337782484262558649397877907482770926569354575062474731363619953347706765344804180266939662570837008250178368667555715429568896735893270624927748700711317824035880960),
  0,
  2956871715978741369504388150141818585698809701460426961340993845737891333431184660740004299933722697128744277566059993728834110471898056633296698894200745247620305979025014664474358215614774284115834413017319383585567591177721389828550831161044592312283417507967277990624565395155753350222232259730599474754101450793041976280586211203205104613603793598714191675890977367274400014295423875300382209057648038998281286598967952503421468531924577860960928315448094795721517290284606166019730691667121767824861093561250449906411070615783775131216932781814689820739021295190368002561310592501049389873683804563579080827821831436925975406361449247344068075987063558651284918784463065814541560376127916687934917773968436360825104947812181635723271127495097442410510129017695801345829079994138137475832940323696104842417864284967963634559627869076851016943692269701863134805631643854962670193215571543659986646755809463443128320,
  0,
  (-50103322004869444624103734133778391870662968454773191822525647275451421572917555475028772854658419502709833117857776345263975902887237493635107831209418039707642211550200917778201665304659744866178651746061777362214795231373909969817119122040319601792185011672641534639179942091313190915629488086165431644075896572474506177539056043026676703869644679626487480769371465123010453454038874190693456224508000732229647848245879580103299307286059637608403886724407725680191892666602535142696004811760204910253862011773166885269682977755826445548954498024952509016955695330987066163747510327802928245816120287830436558885340011160705869571258029171574856034950108899220256798059496424490044769785960396371688203034945469484097199607199771633452071783391009150994040799014202936819379281029284925866586780321897294473632892373297593753614906682065170268672838568685648994819839883607364018301744042968426209243083179032576),
  0,
  835062236082240319113211174718862155058278809963367739074462799331264825489858216578845003727479799223470644805741435695219168680570164396508958899460128474617485137656865160982144106984068798173106632110053204054159816934450844376959390654430189768810691767838371674149540279386236617197352819437613552794143301916684006835624698963318111254535263257572901454312838103046297645197621248885505526351925108788696679591052187699781699938129767631947074526989026372371362433494417067002575031044803371692691277568282633247729507396652228885068020895929187102103941767426187850988559106356863201087507499590328747122079083048414757937915644266343596126726735191095889041722146534041192696164199599682090407136079670910207436181247181328616230823471709326372227871737624364653949767596633930472970949011773132467215482087897579116135549661995527288704894104320747396233739178589404481869766578616365617797174132736,
  0,
  (-13691877771174768166535707556680998314261114463912873612640743442861376294816969805283169953310984878048871273064496188692013755297145407416367185102790305581718251149348852048436003763476914818449347083353512506060576931236940798276834588974574445328520574981620919708711543293379322899689480408141834748104959620242636110978202862045906581202331691505463848432978689823410405343024355748457093270571920755382352722246739857715425313872285277335135063984428431312952348534115403201406296670691370360491321122720276758691019739786823550694819584895818184869825025901713759412971809319724393951105671476324648543309190906232993044042976582991030748926363244615434065025231295616538813009275950495923878321310041564242389045001545666267592701878530167948715536281678834815719490265154414484780412501817036078807661936642355150647717886042918602449993933068858391535218524122190101206683509755353787963277312),
  0,
  220887465890052319733774571885685403512179071125255310510510588842613361553823127823490412524927316452395546793222591522641935035644231799185299732841358196217558361032172550089893608598135945778516542087996172490164447982900150185368312812763297591831388616351245699493969513355242621022078802843696305623058837691939952531748051024540397115908437820767363498734238564772371328645621689719441375046535025284693925352504667585597504975795894775731502436384701456783535640977950609637456823172722469555773966986878660564524217048567008817231547422072862078259997458633811354242327393035359501412838613592658663192063191067887226832259703057733115555521838392265005542348019745186801833835784176404046720143033313798525681079436809062472835157254147998660715707747595039647077312047777253558295544673118898845908016509220217245452512646317364363336729616247707848182928590035695358551165753207895883776,
  0,
  (-3506820936589612000829639442784309994578086827694896708416348948164360890071732186986988621140208810424173626457784373692901629016681024125827386528618682927582748759566846193360541694749993267425780144367648392824174259974815733360362455947755411497451636092226357368091214655160312653893025060773957982469883580402871482712821912852707908796730006218229811499445796936221249378700511292186349608578084775473108712367159089655772313094713480268003652350762171547888906229346359796446850815542641846697035925827985524037575102099892638566317928160989656737754402080989214738289734266736920522677383577404935020157100715478736368501657864898114470500279946242040674893359817779435176885955854565240266760088301890273131559310337229745304353727907760251234864092871717792785354899683843327465497609325564760624797104165572062293420274588811828371539272438724609837538200381781325771231514593329152),
  0,
  54797368985455034129082616321352495190653405041969429838190667042256305852606989566075112557394334203591536354364777860954874459516148390843175741754918132090088377562434749170476581680838765991270832159689006550382820716080153193391977373702193170730914724767505581235375042617600800272864127900576934447949321157050460488783498897420163922323874190153436673338595261926542291537694287022055487442937064451254582240111785217032106145958655130307756750908707686496130143436616684367027396936200572534085596321202972986768666113496230318198432278099022351854803317855373288415836997719452042368148606546249125461795749489174678898824326762593570440348814741233709837860459941321916652409256287372019308500975708657652541365847005553135893980204903392014018483140942040804937238094158012926490001989363778797069395715734540407658641943960880319815566766146332039214237516950681312158346641408,
  0,
  (-842902177409945727445391978393414346765478215088572679819819651124418768225586279908787961855842511872306178673899301421982536314753046103059180263531413304450208736182882467341977711966318836906717163383537672339103402774520879447290938106740554951685201247633789367916569778094146117730430779509198735762983239703362148270790949202963935731502131239338910370928771382906131333268992275180259255778463050620514508308054821546901021438727066733947530173791454766998111399507175417711545790698876074390904594405916331922586536770443308794276399925932508373800402802859790684253358683699016290107325695304815495018481751432048335273998051452407174983737758928244939078656852859230284535281113524040704054129142411709263835419534084463001480611701410874904589962666262705188290392878590761893973947424096624869883774159392475285525649289724185934313688883604604657739784147858351477227520),
  0,
  12765340604403252553323173755787740892921779795201976088578294655731537928636846767566688849895716009330282204961872154523098072455350657194326175869167582467045015375283531981021678221112030308777583780338915227606685077209931768700962280696881647583517812776073366252588603451033308984385068140776847749969770715329607112185542434835946557573887929920398912062612730046546243346430748852813425554089145592880819429351903876752872381092140239372616600087950076872780264109174498144484177490090035845735642091847841324053384526116480627345377725812446529072379377264460345507307037234495790496199793044355237986391830303960862376749952878708041421401326513619902134429892894291894778246032041353122140353620991248805662484397412227350342729687635135447807806346421236212059041562645293412498681548262741189905502416682569491579203745486991699783759786047320594926797637977110478848,
  0,
  (-190366492135504063671107288679486366176479097783013033617392947830559189838872012423920805834244269001111131132344183628950963277966682752744208938148751012646396382595933010766689305048561446459499102147180684943046455887623630122084759639297475285615835301223387187232805036052587980168869890343915479584884345577989055399917806517266058329578392874911460696874945875635071297517659843845850717006544374865138232615220527250196960192874387292798242531080427235867364508811845906251501066898536337383401335984310870171152192496272626856702934937675994456153515215511776192924043578838845606751901748494287373690482487087835980821373204752618225075301907147153701336088510551974493116312186153522412834010290266845523414717833561805027480340513308605332776324358388761610082125745976596183662478845869265916001612636809973297207333553746700735381058995613288672076040220180480),
  0,
  2795859329086295017853467823137637156033764262187916100181337392511162464169274717704358447837301272811180643515215632746330056403349687590837113565614253409946643729357383503907085100898270312125788131859082103717970784220058441723636052937517483595498813525802215221374031485065386111671250791312873137279764688044143624189909600468155319091733814109731771316262624005666048242907991316194524480920617517284281940319665381873222872318426555150805678520883725318941682664060647478454791505991709222775084389328804592622140551439816278872280201338679918905117846040950032545808358038406441292141176118614659749063899620800126490902923352166172117942345395460597061030055074884874166595857902702525327495113446051052760147523007793070479533049036033757638976621087966922702377896827867702571045684169728128721678586088165004667993801418646379565428459246506270373974114304,
  0,
  (-40445429004710352446544419204904452459656093624870679086175634239151899497000234304922552547799881224493452809686076494125328959271135187695675479680699376175904185132614383542594614269464221667383011595657577699025230545119501116374572696381466611244341354593449103998852880878687871247304220176346214217750468533834607846284459591609148932874411722711600720426773274892330540069656368140561160815488473135010712798778279070939361466308105402093381552579108773915990835100978049192434611582892412187150365969853569136731043796647491588050323043490142155202480261266045121678450916004934251719681710908964850200391744894321068253379696745292011774919185188260232172804060079294743261993623450976397209941239935337212745231947904106027379941206441572760461963518407220811455955884214904329389987231905815704050169797608093606404347213410838077975906796129506123841536),
  0,
  576387182754061893016990379334850308910707334234341573774007103601985031736251171189474853296114657745542748299218374697407396051838288812188182168211057850689956406478923719789481971339405636152631338541624427154102070873890664614409250109920967381389612933231081323153741154200254895254178955977976780214409672181513861164345647998192997700755784330334328719109456906008986395271398547253374182776702340454986307588923004319179070414000917973100469677854915144616264752761374764425388472690551734028368656098667189186245806114163181338286174539668648768597117448052108596786170071740092633962797945090282659096199891452963179056395999553733107864715551322534482283710258336335282352991153721523184449896573632723939715060873330848102634497651640393927801005622879544259326087900896967516382890257181657297140073563672270367764460025967439705041776693538193408,
  0,
  (-8093011926619768983424706440920122134950591107162025696965241751990591957661965608504313642805740564931436004193583310793518933560683350230142624853124352936957356397541349860507558628994393129741950293948315890790149059650038984091009375918575688666173945070590618612695500530050562064224190520044017999220660470121592359588155052099361311258886529536960084410322435840836412062127290782781099444728648901677256464841504620564533536921888520986311357596089869105589626193430301064045474798399242344461501032554607500081885915187216704861373764137246630105482234401862460606806027458079410852710465722373533683348126136985993165230281101695715579189127206633842312117600500483270618355429991961712439337318077001702946835755005050174067733566327469518613361924735054234509502041517291978557710891546366801017221744254882740320731890822080349636582979928064),
  0,
  111973737731816736602470583724873228697753267650364372233521113855355227986492967537578107819703748350444122280320961982637065256849739354947964351876598494360728452524692963039058608094311457059629437831105367331746255849636509345051786325429829992995191596769412946450929382869784599350130698561416195724142832742882525389162024341948700004219271305796175147509076938081838602111586282743346091808025694964577593629226348614780437892459146148806410106802446682184163189353786776200994118771085077543209679658083076973386759695221777453009405541993253241106128145753822512279680353721005377000424005453300377072881341715735240784263067698740989738598029576507971757408546151229923117034127389702241763169679431122533223294268407202096598483134740238374386590977503271461953323333283388775582843902871600150842497640327226899317534552026432994401058816,
  0,
  (-1526828776902137725626477067630112633968811921966768123645923786800214530345964073355306047015414183089368741771004900441148386198221073848135457457906820748897436840917832131089749714326766417281961443789966665440349241615169251134645545213587705736296707478311380615873662648915841780955637025475140532130132340739917412849090676667633776569753218554869343243991761640151363127165177245137468195417927272790038185064452716104521413849080165257802355245916619687565283880445986748716137929147412362778570555707730028943969378167517568778019746017880205783687987261397555403845916751236986492829875720732482514047905241198421005823349590337686668927226104080628115477665105263329627929918620200724890471680536507806174503038404952572300903486249287417865037570315988512765335466006497652421420411824879325070059314154811044402482598339238843908096),
  0,
  20520580242728616540812712765862375093894380266834840013649725099474548126763886006263618382631486248579540526787233964512439082907207144467494953393380370870155004267295849588414788663515565144062707062734413119625190055541605594220512066580215874554909697407277936145815474900384179802316612633886961733557192113062319125894049047530320428899344439526063810822237246425574377221703360257928379677652076031266909465463188565211126252381620746852961494703079043484911676776842664283841012923852772371973816714532888968853458023778646644410313758359865163691188548334113103140277104341119339045764004894230300225144861729816694908850505535562076311298629298181835127360080513458086007454016662229565528284005617367939516369240503049025753889592704390125619040907832852798426293774985514113468733074628510650024317505526430648029195180387074048,
  0,
  (-271875462173530865512237812338370628454435099206376421425526233981396562173295105618651823071972139635501790350536864661643230737841091200234716017405103256975746641710564863972238594059700387019801701055393248450924283584569298922330797882241138021425485658378755620726341520229090951554658711795343238083462562712993040369957299056942061788794542564093728120756230091724443226709955105395497280818594449934923677475352120326216828777475025809551239490170411167348028696349926573064217588436559379746638697287944180073909428076690376990589754652977678080782891131957947042804258810604296083530809026798250894475875491941711952995114395937013672043636683920903650191816066987942178662620581887252753200652650840028604960234969158492590160692025745285260793986797804464443949414816539194254183653191390657021614661333631396585483672748032),
  0,
  3551292088905736446709075378576198999217062999528484276946171671818051175378198471916691904274347194226923394041417175608735944244782384332055409940843201934504424884048721596478491752160251742349617668178029457979543297775625818928079051411958081095886503793300436010552343035713847688852161352457106586603724601240664646869674036188015012321852436722057303006456040922139421467612415363662925791394150604533793981693258085961916064560716973620192361655114927417634545391809416199468408020643547265204611200938374363555282433046690722854580819573267766020824519779986618259442599016987941157175973601511847173061269030965866993582369961698869554924836375404220899945220509337971424962794567142491192691419758751647388325567681262164394755520635313485730442740826424850030934139654925034562481723255269307376757609763790774083780608,
  0,
  (-45739638779704279246121261466812085958989288679655310166310687208294436324067476020132282281447457799738025691509730624993712191206401168096773594290542520318559981146884662315499066666553813912156222716121777733237628511161602822888432310842082885869378956039079700140027139975462722889363501813641499203500341039728094514123908915300980507442133159567396912609021692497742225955011208433630760599358356461119502321764506992221686296309516348429370956651156989805422461481405774127255575332498954819998110795251318752993961726236622426447822995623511509695354723090560710383299549919888621527744283064997215263530167484366642719689765897791667781757230925780827688827277873493600388118832032672781387216585226805432982273366059648707106365864039369330853734278334689317767849235824156741215238973957002996494259115725070270464),
  0,
  580954364063630586847154639792697901808705081024020839601807567580050039879486308902483928994505317749977997543210715548347092994578480958715484689873215386710951925283668068202117605394154632183121307298473894022293013289069775264732307092274040043301328371775856067564611676186727852616799322917059644851247750608631011261411992452299463312649383664462341839032153149072249951774344678824800781337999741193386718302020459130271219967428740493355563733297112528970947930618122548496031111243466778791734041778130148494010343587523451400312791854772989969880330081923639056196151831323242440104782887645509678587382133094513736761615122280114606914116773274952480178908062967005620482888903829262069643768575814197446303186892872387747857481042304285543166756701151270317057535111880370995290944424266899953840618693722112,
  0,
  (-7277568887101412909565093666488908394347830901705981497716745632246770521719664876479613148065080913577901783163092196016076091361609809460132719043457267273795854929058215811350650586735753116284095392995897362142842884844708041365217679640254883405480762236170730034147078760352520539827479157436628635205150736624082676534501496621890272893134664571122373866403306429610825329140581909085843665367712866880086104413863472664677054082699632496770126319852886234612745228636216491939483114734265769741427547305448867362533377695608711824231222156396925874365555183727550242014569498625138327077325647505568817859006349186490584805123123967411366188740911996194178743151327629732754694858913558138691473499562964856716678845402631278416595303133074993179645919813713903693767761797414125069583177213773946532724211712),
  0,
  89924247771350709730870770732267352486723468133840790422027855410830154015068125212103737684152469304175241148581638109606973161959919095225618023000943977787092889157317384896493499512592624378401631857274533245746343468081730760093009151640847471016491564013302508482990618582770164429839906817275915651209587726597953911435645424344007695694103874185633508769329452870368594096511037450874008802913829733147530306717399713817543039604546607526332117712744943975627268231939690191878146470149116731705441957726709828639538679752537361325477504302916227580161677456243398909350265321112168367335146612596077738517411362012460524721495419125845324768552475718077115530125648614095651972282659631263050289581360345778827844054675502735900962195828443804914142694384590789458805244516836928093556777636884396376064,
  0,
  (-1096134297236404215601371253265860175354837428605275002575463302714884701079098885693258624360419419252121793756942898724223055259123387154782714213754784502567425686789788690236661688224939086161529980599761105430682215076137957963673483977789449216232782113314371552899086930897567443377146718421610858165092586303864630815068193534137009084042779582634788283252191886707406522588744314827002879877511607446011465377670739060726675308153912984151366565707608437530456721063875307879919211044309530442924467178394078114099503732815197087236593925648764757093813037194257182804456135338922429034396061804620705551413840203645987786151172616787803322301726514753321117710924817704078972415765448794562046164828431941741406862125540582241732891630195702074078662615769843231698354405671789762493070578190123008),
  0,
  13182464461166159298838836485873886552722828490294618500908559219035799919342594172582502051261331879308086880344674043889123404131701332165156988171614421736796013947719549157427357124460719321399234502706957013548828197049005561240734073942645237781042858920575451545840955892638674443578433941332528939317713226289309279266128198961605898701107962985011416383529529815503269132965588644726791647103742221555746550337390718649013903972800508151663096063933608518783238333143319558270596460777428139970516108758802326927616731090678781815402719416988532887204533828904578291589365285593272739891718542036757472923097416963273816017984346290065257400080614069588586488469847998041491767093309699583827242818552163724142075907830076524536229964754074219710106489073432874108099339430932137914929199972352,
  0,
  (-156431399152582892763755416905867963289586396137880469260855583285216138939163436216533338322267008663105619792560187259774098172568173274112743385971947615020454164504022226369597283871928618656539667031176567910118633199362367054328442703509578992154681902575363932840079113301700776241290766877831005379116134684520986897094915916450416392736438355986254974647989548743696204403413470379667439073696091873929032830587988704867905717593501027505450173999242479344914636305958730669260786901139533550458553261993051832920679827742774741133433599608452465446529661424563275516397059136872457629024316857036242407913497437521667312776359150431183413074001473757868716247679668907530290385037930297837254472545223399802812741591044876001990985368830804773337243639271555568226079166218111943201259520),
  0,
  1831865157567506553944099650838151406425531132560839810941273689322692287826872121631696923312418801950848060701082835295715413336077304557002298800430462077421028304901679078120591602596092231055968037011999248451567036599165242294099465426463754570433378792328160352764593668660572900823095322332723445781593684607784482172712160112567602303423173561135773836156207037302327025102888766210978492841290933664883262265111735484090584910199848002205877074003845704207057511792121499125798040077100660630810251384386119355007722289079376986789994275828595820821999857962343850154297922497317186212914949011714373818097796534527048515681530646021433181236547186392529232823604653135919641433217982873007038838299681274386426010706930255919851891336193050577877979679778080710052973328930766323712,
  0,
  (-21171533048720783850300375286029201507617780120607666701032975092225131548821222940377644084627099870731869005325498302053150104280358609917808181965287915758780395794102177895019598586024882807991746445817521613426380457189397301049973183100359405430115888919062855152981480132211733905442946832645690967548687190817180394956505502865254978182495211698075964273447795199790066653794424642698128985786950259212713618593797463612397278812995206549818942417628071398396871604049431306525255328696685278435206869076039425621705696651234421482462557861553794823707986863339759017355145696711955383904960710883621974795150945988005073548069556602392062490207004665460259566539943569694169036048482579217412598794090184564012620396265607076876427946949943251550370796335273685497483601446436864),
  0,
  241516356446117559982686574715556822716492623741637401210152832014914054203459130710972330316240433387889974952065613808725661701888284455974598032533763503574379999442620395377855574756981633001144323121522739431881156718547677659145173450578521727584785072304177573246894146635358789899754605307299163352225313494651290413319743596211555631905750543721646723084998821097863711049785490206157572410633831815737877954042164698763604284575511485798380394250018517218218007563745714141429146917891627254808057643475807716210259111050451311626644695747715134535960111334679532188525597177693736355883957801834152908443980544874982538111294414886371571572467440481960345942079499249166814737994058594150367291958151416887056838698437625693888116662258152074723323772115920150480340123648,
  0,
  (-2719704228933615309634054972121957528287945916713391369435226794148633503550068378301062663257749585612725135444211347819973204021605652271917999583506433275693322259689701127261643790031084807817459076527552414894251923613480498377365714125782770884488635444142119914365139089454415055047981741468573155077144356118389848442004156653154001074432486158615317361903513258137084713951333859666091046491095799514219323519150015551769548816134839680372366876934340077694217864286626445105959850795665256301751670472778599916240294009609622039911397634244409023142551949899012725201912604065640168793573121406046715510229679160696546862731521553212218230009027144046289372067898117607713826458914484105075458925906046947978078593298430786111202177671541323507129255682590636536496128),
  0,
  30235865504250941513505307978306190105295568300842370628262131685057586825747761368461732214378693304235860063271221681556825209505631914553879865822561659667352536677180526582302420708831788952627061804799782656893030265851414843790709426092621189941968481341072622539552493834099389143696314622408590532122702958864324111517211441496888845065216172423865233220234606003580980807468722483480328321892905024305024653223262423497960240103701828701279874770705194008545645024833281608617650162066062941196021874762548361068733141473606719766836767788650302796161710119640046813373542352427844428716722576494575538950108317097517502224895694541758906937993584310650093606262044571517436920182935461013315256646854239552677416868217220131010766474098009046009264050668652462080,
  0,
  (-331888899606145035475777362413752883770192504344933823660260369307196897472315244994888212413710987481670907331306881562404117119381170138979975515512103225680146175642785356639991181519053801460079169407986989924173909312299722016913168415862989534047150664362081135490235656691265798394903896549123488352251387757355528410000269610188536984767608761410608961288178530350591416019151480258674079920142794846954412579338227338518982316486657168387880585702239687682411902953367925976881848406396748479570206892574716252275703845404636389211116850774624216834293495608366349230482014317354028345739965393936172414510318804571991057619512308487547740935379025942862978168718457531288960085367547719253658072994186349562558172790510923024206954285694319315061846847782912),
  0,
  3597294023485453665183988014048445750685044038734609193657050949477849587009250031035653485325658462863188735575517896905057685750029689484364334845068983886232328065061016859774371853287315945823041036680259501000384091905579260707003666389198231057089067596887502461299573237382281089184134747983249287065378934748516482381013552894112054735570663162719219210789354377602244039840131986442853089666323950722560409453899061175276828285363176143528949659278100233988828154041772315006542365947576631991499992846415416057769730486153412702437214916545216344470756593880556453210247439571163817251593379267479805802894473684975820610438159552180525363135418646455700244432272261605904428010128394729879180305714929080296683946227997416395578336274829131518679449600,
  0,
  (-38504779393072830891039375651257386349994093776156580584060351751116947440045936296706075050099651117987430398191582083545238609375526037967654319613778004645407413280036687590433678993124525880840789864514222418260626876278099562050798653069169375008285278440610425414915118387730932351304683578119696043180262968309375000841971298238745843413864272023777531513975113306251198624481274974217078492483063425646233573366326788335648961124114006459368852266493185257918036671750759427987226179150121129563317758782593674190853026757464038675706726619410800562731192454536158443744422862308935341347533599149731401901108622040707460629864690886381661644761755972104882626961001173351707200073999659920029743485768477639919593642396760521769616806725867840471040),
  0,
  407052828059316080652361350273825602910879414659436481920423146252690625642964643796443210324836628237756762812017553931517266373523028423224025892395692516434513360930301010060112442670323903941677833946339174916555021702501842026078224600072751576350815977344046503279318415183327880357798759427022374153467284361721845699038083528200917887893391954305588483002101193905307958503169410402403644771153618046960789723570229864832378807653489619425824121992532279177946735959899034050786323659087200820296675242566549250075338713612790269381794181259008443921231404666441142094045102906597353514586904711448949816461370506764422707555961193783623473201798901460427624273743695503896512933035123549788190652504062791316058483846009664802147936918975807488,
  0,
  (-4250359191929593284325653349494363253791286296331498381733285863112342686971733596545883170650198722292012090499609309133501370259436018674738574309144149911376962054881281588997482978345267469606495374088264190038895011281306961397783328160061951343815993693030446600479844871352877450874090191032750147606258704353168916785295401796159855338089477884718792613498458532991148446341125545315443999580090860669650819852318449425259101093001974659356714839367265850797841970621420878512604131136923122498949083816765654763435476628644955464733071186280326428011048814007383981719096421116457175888298399852814852807312030251769535751754870613798748538079901620936935341796299294569655594056503588112344485280556739481370645112269954030496749474283520),
  0,
  43840940137452024084519570986376338846264673215176454848961976906196031489370998424941599281714613567867909035008874644915771180526958017175377735383442796438093840767843297195844253750579536301283098493242002638310747899927398733576240623771383500215117250967693035051386969342972397469237700622712447648072229000470828764302613188505392213610255004478471539617545584084587227539328268736253830956773390811260783731285113807921151339027521303627024221371323420197244902003232919308017928061381516472966164386744402339022795842873648890742631151537708181952650604488492605035892474790689887754059108976007201020255048345142947566615074684287675947635807109830703829131216290944398131712261780580189972671385450217405535802311183817665864007680,
  0,
  (-446738599953403641896314202378708783764675267629059049660794774723802783035630349121126680131581304458190839199096207601518666286265737096888014761430288779392616365238916260452978698455939169278576721332056661460731832549817861350753654259863269776613202093226539775886346970517663302684216824721321104284422402210945335915208285991746484021896297947633366643324858731488586522127951577911733016339918006333128172213754826587020486594467980252958088410088598666317957598631348275983803862182269634218780611444519300265248582017251583348936639725392491621150119994486187703254437808904719982400659705372202157656271688079993271410812777071655240185527225818034770760510443689544409620177982321731620157117914579761156563980189827298492416),
  0,
  4497652637891767896131717422900095521426481133481648071646923890213442338927679312620266833616186885086386030795921412426563850552105390352213386907696478546203667904528191211154572802962927351565333918867585780601630167438713156907253796598136945404815808546248855518012993775152719439609305652261142299161891948041369248941496981992852179012767084041577841459750884682236252476332155888784738575264138055810403173289658109587039761206111947923241235545335648206456143848760899341071736786161269637160114256034604845948608502856465614317561235040215355460709710581524521943889756058378851643195750488726882726596319208824987339871679354295067321810828229266114153916797314855696280185966316380083698217397779802345873662520667930624,
  0,
  (-44742060231006172986675873021702913503235869995570255725194222323690961663772496427844373698892021921509542757289500007567123201564333353412893619524992104185282471535672786049574993514302402736167993124227407278952114936985781401336844698557983417290642745714187592415955335842906879257483206420440848036932641575519223390294546189736483900410983601393439975113651239741111366802669727690722786277959283401074672880564361296785121949842618072652091057608766541212467774220774557493040739391278865640522790236736446329431278585023753973062024191370725898224874321794548470568494853623872182101115792259267515622548361297065215252153832533366069358838843111237620598596303892496083468689709695410872008994319049502165223319011328),
  0,
  439827035993313758502755757921561642491416775101180884871875478493304436650821792554299272154054361081360863632898453439000316364191869606673935835202993833347742292056327688117337118159932415402435222951501964061236755724805481148828652198297221865564971407868932572988376288325263031019868544159011989925720930212001031150534318488207021388306320126730735009955173894174947815443865848862138276508505351420305447695714100644900162143521137618392253170443289713777520043047571373753181880872982618374218318968786463481211060874783271006938350462437509205124535225435120735908442007931050295408519207059057409227539480930329209492983064828145104726827724665029665913526434755084891705128208323277241502299001472652337479680,
  0,
  (-4272887076492188004466845625684989010349534820441136039086501915379385907089346447101366078517366184662760596782681621165256888738927241627650318787768318943669164080042740219998792096270976661229136974169061206988619754487793279178255939285933672001122289362909617398883128051189510392562639035816640597366191886110710896904677183987118498170041838768119895208803279451391028563947580594913342817453908774897504348871179079043749507991872645202759109837312248135467272625700300167010730809136236210629434195472302691968110690225010603018343178530154845413403436546929457131969914302726733593898914791750307953218227260133918951574749318250624278191916922461977128947824660412506148053657522337689619501442774002040832),
  0,
  41027171548355719136796046833564430300996801486369351893910358161863047448904307533540961812686168740824148867771973835054636220792222734468063742669949562005985239704809649202614008093317849963456972404874385153324589045991859489881325147585164037874106907119914421719167882215207297114157928482428873447542686336659744606076290510390056078201873155504389549401427163284669097417743056794869857500713102762316803985097291135730759331987705367236360284234889830471415942023784843211240332162050204099497978586259009465542415946961338937714163657689269721498717155665339263002575151357432436575246463939399091268147047661160995144136561260431453283790345294221446083667751063346740241668664961679603986893149044736,
  0,
  (-389375823258112831282302255867303644081424794841417165693888699701860550530355048201183130365068438545250724574746520358965684123793384721567665096841529656718331491755078406296913545546322087186060613612283053553212370219456569144999016939697855821846143453746999817609960481174840995377595552268038943554303202255177036235377584814194112539219011557568764204190849061758988459617304545999832310290703480890565000299272532253861056739380431147002823792840974084211839691722319651188013724671464389409240523320240546325031345753970719970015725281871787161756898489231453335762161368183607340585497118079541664382251444179949644407024293063887209417378264780582864406825528527768294725010591056918162765250560),
  0,
  3653000013626833124831326849393341977791398353405888312540842061876809076857996448791819059601596882266091466620939727448138697058472269815546415137813405288686820345675072492532942492752270678515589602284769808409998387007990776814021569512821748221410107492076601887774011915535959072649689807808114248703777863724254280195203047672009856519803316330166734895639062539688798456928314050115050806169537372250237061255664420853579400122135791304576509531695379882464817749926588421137803997579977117827555792419740320374064238245323325922728357099821063055755647308681817265143637246496430860900235404576651085837838438801767098318481646097849753333521736128130503574736301035837764121141477189621907456,
  0,
  (-33880450476842714272211052425393435655984128981929741793366449585683683183820203628344438032456998325261753788706123855491596117098372174848705129474490405860106642792441731312078087867593934337941143114816493505084567936427248762990045470772097115929574706203576666112382302468592151491869987652922915801131709430653603656184605751258451690072351513644910574286842563487892945380879840802647761663183786800828547062923962824504028517620061367555667319131497904150678743768121337217085684705071070189993880370933596439125534011470248806265505560281748914013425920718089525839737058319457638910333677586046432101769269019776396826102666011085624536215867367480884118580619169096741007730733876248576),
  0,
  310672279947784157717111593696576024382624651653553577015174502296823011245919685221176453398305165818195955591872572299863758058813397692017781900363490386392504502063533344393258477567340598991905558130684271356762376592479297520791524517404842738310337480875535748552648978326247246417809714185164742472335548991536647382508075539583981782370573263626190909504857060711134395608289489399775026042797830122609683995735265906046251757468875816412861982072004274497634410981640982116508936713496058744900917566164720266421204891697548560969593641035352086488783171081489777123147815922356933094400417386785906138041069394820195347108936487280229116889322099625473165638835393189693157105729536,
  0,
  (-2816723242350886183212096338155536395628351006135510433432941377473950491731118430206574340176815900735935624160364308221270783688205660076353119602226145351745706269122134918269009266599077679821663634958452323518351531508554593626952192864897756521558373458453410650620380179722910463677598379542802690396541682855250962811168029497103772321595036636294974730231635040651982095909909044244832951074419551997715688292693900930566600916382208081924004038907915374557400339589049186883625410705424378587982728148846124273627803603238057656639625241556678777480270714654676144713372351214742502006232387116197032974112322472452676898624377128895657576012626472278189458503951020744253636608),
  0,
  25252723620666978381214118629067061484950276203107120954557895856141081181158559486051365805811624048897208275753152085411148655814078840322486775025143955995318147766361349245899137841519907597786558051085992836984255486526526822937208385846584561614514896517278229776282735629138717670863378701509152929294421908318114257636751180974138932455954206584355127968447079504948322899915773513369872454532658068989169204919949855003556465277874132025208152937814173941595519414528502264886057639502166001770172115710392077707300888368531214541297702410138817951579112525426189191291960391302795518622000364324141939478514771801185142999262122757354430724493324079642669428217566795399168,
  0,
  (-223886652948362227010663490251190444643238429906070906906808958705245658212003996114494635935270433539994610162962073381217359885338508513316392584706131326678450824054706135256407748312173534446782562414853417825585788967860579227001712845860353533155167189585058835950729120088398131531987953291792239213634133698482044800951138204235189846189162643415568831830354733004183214398952296279004105257842979784990684211667287470173356625694919762694763684235841360928595683678032961327855494619239982607408868476469500777286945863656937577312682555421136855403997997729996837829842577649440807381528510511220402526947481293534987023474596520866115531785978603235723002479768502272),
  0,
  1963076390480999136755687702106719545302854874896239923243558491854310838097853015368486471148244126223107165510916297966400039311800707108208204464609315060561179852261544321708236811496847307185353440238789825526645909531497481917961709239051461255720487074679060652019315426107759501059246144695422705693877020368151773749280733384887559189040074792992918308671359642924888744579491279327826127193058772482409026105909043109204686599869148496222787734165917823654374908430105002451583742048245767641369750358613504316259619681691060485847767126883749212622689950328828165839410375206108302812428422489991024272299973470391065930950121541068111401975958168656888557731840,
  0,
  (-17024244389022334266517165761510642615650029268003369700462101703388384221735467497582384222481375059749466933650256851318162423793025866299163560994182338048838095658184142750693475124871060907282811057422324050549616036877571127267703506255292932137434613200077294168173165593760316434281988464989204344291277628338538819015085959112130917087889302335287121180201901545274845728385150344675040986256656090428592540119496544197317769214099892174016625827103311703503309597819513174813992669739208385187033601833070311983511823363487049268726478515038190884978395718362979431895027523413235681651018703383883924823023353809141016622006601622665812474048656064292847616),
  0,
  146033442503646856917468373681077603475282630593384336867646542067962918513920412221796165957803163227861838986485929110486933973611848050431232568601292936627111984237737331274967540823047554186544091587279058018758132311094004281090075296672858916545828254600561643883533713009885918141520282328086180490853134986369627074933375225825323548020880257905395485644133872892462524045421770203600996351637043699264475166785467072933521062202488945770961589584140196566394523634645769250255303721143363652313845186937590881588098208947980663108947992551157922534372889834213031569021476302299982355578613963977711959060515979195674801706119563264503650510786409791488,
  0,
  (-1239145715339113973333386872900013952750211517810616459990833681314589297478880432486310820524988001229265764461912277900987954258820411267003022096642433291497635359152876889876485657087991623983129620815750513326435526916235625346692341397319015706164534321834793314171720477401799391675353520483517600474135699173170974072109540728055644498753403166752794450039966202596948740388411805751256693154921938781850804730798523917316645656466090523705417148415641119744897422238802621265354579424699836370087493538175985782547950211739359054516535057268305842917823489712433402919156432205347594847025423410091347387885861674138593753090496555677513367798415360),
  0,
  10401819916762965051566217240733352210803292206192048335543140113629437620563933607656914715194765146059752498148994538776741487799903567946313677093908656052148465967736755214461768244198288471622915469197011005327175922192081521737241066236143715976387240968597877063428103670041536361392141189835336710058649233201558425035825694123743540837881688964615995755218830498694253434799832414230113101699973805530264304350121738159431346537785709758452796576005654344690698789328731780815336823978514021377323381861851897066228278953695573825405143331003194114793174879322659196345492862384066324531529418185286661950468010843196467499089768006358528950272,
  0,
  (-86386140730571669063109715207107334715666409205662694478918512342160606216753235187850768705063403473710068793207365605161071443514896971205447193060069615533924665375786857287211160120861821069592273937953298950967737241443439080442360572207120983551693360294136664199639821583372438379502209359203340240624794691562625886691576642968948139159070173125854962720420434866793428434605588561585625519064546476476136675836233610959211209959353144990685997096770747389486921738450842124471047632152742366689400392252342798134866630802634230502299656850335001096305500090291716227898044335327644551895162091858627170131210223153397924223948785035771904),
  0,
  709834475833529187556926527106372907026958399249260839556514024753339558557178103782248803594793800585950798573978313383222455587687020107369996346127978792023361078930993934811062373467748612555328046467368743645206744732198094351139423524752944181833424211558813668751951822270703372820239069028185526988998009558098935840392560494928376802238100176436562324148762913712362645418437893663002012902379266855878400192214039226320045485035771835803514094739016133263890305334167934696501230578226261329179557100695056141517216257769642316904821648504939279463797881782551203332576858880491568024166805627051488952542904028341362239723425234944,
  0,
  (-5771363910213649416282637617372781585010497385146223048458995924826730714009873851087748763766239100982232808999984598572567932024612212514872779241810657197950235913901197379192244186530735280439275746922573262603560444380144115299737570520453027646179393700143616293841620657346862902515568898568396775693020034441472758240605246490432413808441000844173182998252159267846903345955518988988321890001615894608214866565006080084851651822043780012850896476316793645938063203208382333547449721217535845496751968239722957653909474592141918836504475405646870650339869364789833955814979356461669658471805256450149366373407398709726381837647872),
  0,
  46434189432154680502442079232132949796244475291674580997298220735925449364262498642534717175935055773489982124091261227972908401577045515891118188903570837026675834012483719156073067749932834242828093879838669586004742017297913042347522750266354198489146258296298073720029675182125465648801882653992098971973915574408304072424954370408180479183511807665986191164694310134301796208654053002450158686293428184064884356233976117167687167155225481691051865988070850528920100358197149094802939922740344460478412376449907712102810825449957068950593322667492564600943867647011789402830474857320005031984126122400075859748237045677751795712,
  0,
  (-369712907714112664784143386684363717468437215171695794679250781538384678935629532080846354100147222633787966369787723008899019048100799195129889788069636193665743025034701643280136963492389354468349160269243241070932358482589335005753535874129920149399246453613163506023649064911534741793576497689047230177707551347019672420592644711261555879635505722438614534367070299342794884228455015813730616423835199541292129822912624474181065277885350847102462069148466242167538779931408237820700965785803453870087571793226745392507321181342416875261292915171179720378394824050088601051367932478220359409612295645544862744955722219388928),
  0,
  2913316099550541822772852905036867410244416011900396761409703654016552452357547138204964482104475088008907438289651118268616205412248079271599802788812622682302613839247654975168316706767839480629874942608295143560171431675469994228598977725270919804609035094710684966795106969854581415818513275438030215817191933921183422782311166874564377774185621428815667312106193494619013749004104789549887363341279899492067432420797204575855130892766292327307702263835583750225199127349219929598559378723997195663831132626265324021620133222493636935784681028681834777560690332026963608698214891237896163083649925662450998592602636288,
  0,
  (-22721416284584212653623668460229933680523198551985281101525036742438176219347540561015471605482647334627229938791367943328669850005360045701521205642134103397017372121587549699133206800304342353101185367541109313146579092423449985678422617419853769439554144893461060671398001754234633291618378669125780528011181674285102045020360539058922756045656899754493386648736795267642118355306117532893959937077628400687760336727289498488475047587173993690702518332084598493932894579482195604575801831205159563214031016010399260186647503070123345114177101923575001070808585136318732505351015711834045895045006521873490895699968),
  0,
  175402653808280598976113098928420738661909999152176846355884693280581181451445214398925561871942187047358626948471666915998420937076166602826451919921353649565285685681137199465697196366784000105763427437243038269520671091975347718389436306511634463859763340068930457560987421560413715505381020680843747036300552115643979584650177581461115496818396516471116009131849545303102435505775022159244787050883028290792705242499300043597465796803655705068528458734000556380937969797724639083698132196978503933240161984085075511153602522367892178586710443065272876725801911690340835179633674837516272830221735250962153472,
  0,
  (-1340348434532866325569615431099014684531066416389748153586313807037618550611957499385865843919919946549081363110366718527053815079735255225853527981679872667619845660423420726688539502898636407957965861860858345764424312918756660527218610311727616352151464722901615074219265338497188548313542697843745739557638597025861481402171995308083371920825432290723610025229556877843342958365837072297364917554626176742608721884912175877397177513707159665842358935006808104980812261302070086350837418594427877112851437209649726915414041026314189102975494230710702962884186992716936293115288413905642310271081931341824),
  0,
  10139289426946146393069599382544391800532890816678163146916800942251855739070723223898148420847425259562916309180890184776435995640557930385590503688180998446396659122174227021303107202342318561661367857698507157296322161638830768896294402228787039471120305094529774075704917991097143662953025069500454768458307267417401143356204849988979638926030684049965718487525877887129499174444754233116635556936287316439897770094535528927308659722919954785982970420759749427894810207585264293918888698651319504208168173256176499869270225700130882371987696116737394941593265260265047025725900977149929079747641344,
  0,
  (-75933375807063925723346383123604855247209179138858531041425723120810279423953927154884842819931237645933512101144837616594618582955297093213031740572034237919959828914587736248215835839683482524296168343247390840279589217854214144414530339177498972675585636590580933330682163859401324830333905911961414974825606680089211247859427189196487423346258315880604587863982295505843912659367028065928390488392883990835974542760292409431283039078616728299342428423289091685341067872350160718813877024064420024107531257558624025425405754581018560581211768347482666203542900185186339123822618841795400826880),
  0,
  563015119566625624343137980663382845020257132407411356764663231063298599338865392692899326064259815314273758537276013677930273409726542604861277691138643539863485503282917085745879334071398192189962726470664281038226479670897760615713669092196159807582990928741769955237218883387503313666211522932806669350397627448442677445225094995434855183382011960679080831214764634528474463681806093874289010779726899759280267227067694912477238349962095554098838732406950604332262875760202007319083356279592658232022466096802307709825607849040342569362482737105753145626085316688557956979057909334802432,
  0,
  (-4133291364845728424202230610916867369293073008860362080642463329326373103584743510864119835879315839956301043856682559271059146249734343226529247088869239807102608199832111898395609578788551863601157673907135698591077580200107829419567517465794137553971242834711940344803832764206728295993785909986805201242343508770101246612322785818881323152105824941105361175818732441555529096921767656390185071911116836217163525137054544807523704678189624855872696034390269979635276190861496228922428718101179674198875672155792216057161175010466591758062142453008241709771183451711681973155876831232),
  0,
  30046004052634620123214278200531133839952888780655425526116337075407967051458852845273019897397462379073105742284801074086187350341465496313716619783029057492033644656977867072333998398693197561760944891385002964354403580141345194727604582782310478723505553595654893944596740158751324272055832797440809090234319265050258652523175301783772583391237859759291580959681387755268558239589486628482250612363948700339413217879687072149775529471698379628980001061217258638818142759979968608388233544983349142922520596574851130170476844147745018077488501477182469162857343432085478345539584,
  0,
  (-216280798764131725154664867495184344083539875526656737269291542704560280183019299594526990679432553202612457896591128961805305442845121579362563344680379875445344225144104070823985456120483534332428508338237632597755169413526418320795648955013990374555673820037659878654075052601840347304757576737224936073018797651515211160595271057558496452553272398330213385962320882091675073266878124155935984854575859684856879755504732209834236318993376423291056149478027728671195781721906845165373666485421794095456559856346667433773037836068925650703826329773687596279458493799426162688),
  0,
  1541754559227496651082125747388441333908548218890967882332167615798113236337521337856383802683232295718610547906399616823851179276154214925331023199699219739309210276564192177186204898464329612719363165899396921066020481985567735990736293268026046688841902288897218475049734587849355918877842691447943976374982499695410669517234996624379418323853868673356102992552023121956976962507200949564245174695523884419520012752195696117561360401357756119589669933343669277334347985620118892966147968991907016547371223603459095057115409833598500735634002925469445287035224713068544,
  0,
  (-10884380944141527613188449413584363631971061689041605701958999646637564993240584097484435913888564523314150144717164373102446295515575360457889684944688179244176972372300416292208071115065788610322281374120304636258575797487048375002857000000909802723844558548542321244636288043118032571443230615712473001237372974403924150252885091251063013986207431800385275682383760176336346269598601476216328777340982723140673863552608116366997092339867953773721110150345694447542488142334843452376090197410892095148161261635980114246142996184414398102409635770095063831798611968),
  0,
  76104146543362913386059696726698948291438983037093902853263270986299060288911507794911881206953963266766306616393548977661607714515338989334945348844293558988200596682559217960343022941766959347200733484133740060381080516488581715015438551923440286441337142233698276920264037832691128218011556945074215247499425577412345566068664409435492142940103679016156728673158432375707254502966386366671449077473097234384448363789147847455559176790705769161227318065640786952796314600610614127182405780917771956130046283393119320622590831750616192292588798603079796654080,
  0,
  (-527052142941228446664028729201117498445759630566380605136042913112425205490563458603412319443894382196470448654269846635861226309099901536533232566525779591508837386790459550314972443208230822404561260578497294625352799365916686256775088496817674959938160892345625609846083178563427747783127290169928999559066355941130258989635204679089112918407363740016019210837317152172682071013549906839181959027657558326992357651654778406791690867603508203815192813394585227871140255520658914730288871527658658117208045707913117119194066485306037260965348782332968960),
  0,
  3615462103700729227182745076324020928492253578433474810790298561094726362073425186360787389918149258627762311080014110040036250018507584860217158746639843136963316384977602348097426351052891359729060433035742991083204301973909385853057847060694096484379791143469138928228188472793055558511896551511471611443806361444023949657598409163119190005994555392334293849332174956794768025416938406957719793319720276811198067542456506464573367214557980251454777556628410593791255441447211755355038340418666210498375483374090562422436608034940065039663841148928,
  0,
  (-24567615926286543935170717558051795083730681638138463064623674875316326125468514556673272736342947985553915637761200862888487042840705688041596019310265733678702662024895066440703766159250327833390566891698540915030531991233125781207779293754844056340494357411281481405254103766775086864025133475479484127211607036977010965782699872594153351471083900548616705089164197714053759864474745288631796274274032097107897874892658014431461065946812126256127410953460436104626146198820437389943008350738877477818909239717920694111048207119598501828231168),
  0,
  165376922476243822786535013488858091405873993630934866084617759030086344660626227881892458956052171937112328821609117374183401101400613585405193109261649416853594996028388374503210301409069933471048609963975511343683950931189750412259978736027867263470510722187152191183941068643122501926176625810570378462659941577394245952706263231165437685120930547373172953963957352590044891822787950796516061981257133708527718015405182626318602264700726751800616557191974054535729787514874960518942710136633389054631453494161771580805631731702704373760,
  0,
  (-1102866471641340038894393286802254305468342226692794945144171638882628663070570384955703070612919407238139211302942816774156259772783502595077934919039137946906992017165480044358574072746261611384187458009312677512874175276503767963580061175549457280730641094595494553105134540881209489056742823981394750701607897737890656061474447111909137533834623392107837980204495398531474303726848212089363477014672423798102340635129069623285598954703006612979167478572731455497718390067192023102181734967264070831327860597533761413849757054402560),
  0,
  7286689622537042400926069803114463134562699171679176063475409615145520350994522029375915796802703795113181784207472261902977320120474268867782591762221341222878336263265104119613570774406662311711984110993577535104840460800805009027414564303556928158473065961357466915392445951167177597085303397239324482079451490163289316966034051048669311484963093631414888979694246709689521374434663877798340132005144531576527165837665429589158795686111872670850428115115281940816742552063547568214601903620564256244435297862328738744111202304,
  0,
  (-47700158606936627606052178862211466165933463985526130245610881059694368559615770429445836120907684787898650416714941185051632490615631579137191596890596800563852815269015661318810385689952755080708719467572920533837223375077977435284507695248678620467556750724120009337531843428493013649527732914516181419778723751498751351899405063985220980540824590885026496845326681601615507984941889409531426803264670855054476086628232579347055225679151169782166949224408108178286844317780554414483223932817085669998535626330778380533760),
  0,
  309395671175147741177420031439468292646662232544733762195626192840603998207094882753210699804842351125940093973530786586971789304730171199675575791987159750600981320572430303670268809879543899475776760349463212601227273323969945051662717119362631444690998554799789802335350909152746389487090885805463174558836191358939498178199247289721014130617775957124919132490464503194087312778753861411681065726734164695142387871552533757081375178146669223887598490214103841347015596032796733728655742523031059094191854532385832960,
  0,
  (-1988547119226226727268186114006762258938348686874973979570544324442471002136692716772852935934052562254675879005637539985918944660808381861789192263455414574593097151829400420638508537432629287224488581650606598340146454099435320700938969742373383032581029241069858814337498658190856253100081597535195816149784740192938379159543951193489961406043997363390612463272619967890873504884719370496821971281348113283743361924856578899968547056429717687971083066953082996676937358501966521984296201512094637389826773483520),
  0,
  12665050152775579320447129394558538539813884076866443145610867853694274323248909144692168237353731013203411571006530983309907206623468082394911771100476888227657325112509652809622418122233747573994924954509600001978114324187836348760064493927500356751599108057122164029735093702816485257703713713918094383416450251572810051742987485148141240253417176334280487266410860326240178953836414721242836241604465164083199818808500816783271801121331509499552266017955557624374992440897506576434536202688806111751962624,
  0,
  (-79937249065450138992533136638704391515295446636719655208217316000257405829339154895207406434855866588006288636951711386920507234071081031147540299720164383727419018288757013690212313448764969347494504759289113349636390373935699723518849053491094201746196314672201467524990416789520879862283434954980028888047002251715778643002623875400766617311905256264619897569684953270191858221645548264017243082862480750971067214705760324586589062341952409887882648414645708361713996609623551915984593244047875768320),
  0,
  500016547610254927655852001309126775648496133948516534853185484844733795203247309203016472781566857951207563695173914581962925387189891551142197609196478744582267665792766573307326705655141610631077716930109692533096678515818790252478575855383733633599719235465180136258078569210236486854960252313032779601933073722263990304852831335459301275381928164430104270051542350767280000624210382742699650378525739183372163569349015907196154472203866299123450362424832104455988188721079274531385540069031936,
  0,
  (-3099801228929134961528587665934542737862349929652852983784152814124572519838802889561456307697734909383391422831179678597152849305042745647053565548452746277903024153840328471570585870446334908980377549290598288933187392449734506661172948345999884326202574528044623934711075355539594450770393883162952839821110940061523989349325944909953027888218512874861875076092268999418294641539295341713571230992860647112036733208101323613797265549701020139624685284978181469002310381874667805524761772032),
  0,
  19046657163593800300364563148166355556306912584679663981766718486669045853796805854207873113532502563817738694171381771771138652652400591278043315132083225597814027481245573049661779974389617533538357339479493536511924041057210964282630825204724247756702148079956272059273346379539109864368489794852972586347609891452824026347390569909120294471175682597115779843426877646364302316242531863430205618610767979917771547700984065659178625179197206574243421246151015667348309457489060836671488,
  0,
  (-116000552864543179142888478735666084702749580797341920095749355594924216679955072127742717869973096772273074512203993134343517754111882652839997371881405527635092409087559571691403023552596519700758391600913437879736042247600194156626564416031625459530281155895926238463225112192966869466178232345371116248863035972681722446964377388007254186981655180563390975955205401931480294302989058033269656957512281424976313542933170710983418455130587225237035594380752153011628857282890039296),
  0,
  700290809376897624500623690865014261730756108966368860359035167368968862115404536503547176186273110184313314585937651492564467597457747175161907867072052891240592181186569970216740446800890471074901590271772055716364526245329234798374793394270101268594202873012097756872837037113807260898637271170049649642509065885164645244678881461019366421915841114572395480432009877696260835357745347516998480776145216216338669219643543637627974768339448490068552024748052128441526009200640,
  0,
  (-4190774950079227969001111255775195616698675904049161377714315362812414363566612510276206558400589631669723853497737736992851597934942250723187576092098443395261736307473042878737577851556573604285662977049469244997320954975320953275239421487046071173537263500570664016954028677000801827580703276544697967881443325587882227106290060944408177782786147072559104280509007697818907996869073618673623836315054255255593323731849364310037839954582035811257542298057697480235024384),
  0,
  24861541168263811393055084808558034922244692821003547665354343312221299087766727876252222710476384680481762365456897718681534284307311031070101708122139217373683106474486582526652206398534125974995629206754401356552576378876702343890494801977389523643221253166240401532857427487865442604662014902198377141303351477465454203881118137676446941428686984858937942828563696186957711181723371103869045869756940274189284388521216699567879872467175880433985919467443151962112,
  0,
  (-146217576771885797142918876153709540185621747072650283693002007466967733648016319189800298976968554088238121417537599938096930265579791123394866005765670621846278621620638282395963213356645747324845458597035851234472034687967591644310148191988394906602055199057070307982321565958109611506056228625262874163601389650875399477654763559068224295537436658383853627695265496449620482085628726353748248141213763049559859908741502839712840204662996863247881182835113984),
  0,
  852567478232862353907954284393183753173411042872514084340279506524809158471122499244124113344736825784816300871323133196616460572361932630480880549305900478387795755477485091519059252517444436973675121959127524489212306210284615891144239666618943246667733895559455817253112776570396279930947207427293439088554358209274076090524044734578238518328249724989287636962015201998033056132233441281148094481373829109743932136585753078351533412620705436595180797952,
  0,
  (-4928731881493579199662329930977735274873917539785018869835226955228168963674931259061934471095077432289491275921557748575927540618157896085064400190574606385919640705469939647183489661712714397953410270051748720063234144983083721392006330488639775541459763678922404668513262422891987997810081373369085868335356296246088384117582013723158964283473700151437451687455993900343044813658552532246855486723046720332693352141719463855209010016530850878849024),
  0,
  28251289478908161810673748570522886095767728909842258653636931193459708494845834262232740272067734187218011393235084840956338438061899157343298983960660540443047959955623777825344533580330767195856370132659682344857359692599228086219800810026069715969650279056136585590197659787605688606332717380252470426954169469835427770488170475950127824128392999914752976209616796387198000640663801802865108841439566198509676652302398342047716200501986983936,
  0,
  (-160567335794659581898803624451726382392424112524039273832642249587378402376093031728804789561866480647291802620601496075636801476739959626870281901738081816194028037380622264454255549960745043305518494498143298358625111722889097628690204758944429827987350782681854354245069417740735272683946152642414686581556231601445636060630506819565208330066839712244660559048759072902122067900432090455227208472651253683745985292742115536574533458722816),
  0,
  904921622471444466225718156938851552235239648352936052259797477445020616051807497117871297402375717920232416680770240037777179177648648973685757234732243698905756288791412377581972243082134599992629503622597877939335010031567958811027646277153905407077843630085419155068828723656477944088430201311775612452019943832590177028786159407889722533383110933488495342021808668552590120897420854384239631608479194489413815035898400033130676224,
  0,
  (-5057295875852740859477466231009103442001363601261301263352856695073280232265993281350689874342813084158804007532910409525884215867058324771087319012555438696342437979580824733244935746691062242623776485284987584171502145668257303063717500109750031969817587910462656308349847801313821000995604424470777911747407382954770598120669584771000392720014787774445100943918939464637144260460716279588178948816491263155540340631415616962560),
  0,
  28028379766091185006492395473884013957761046017841391905725414161199426724711263688172414585405754084282982934639007251477428361471400518907205001478414755252869480584037491895022436209335293289430309631014208292363818437158629893194158611262437844453033521020077843632520825071059257183742158545373969524372714454559209694342484690640972676131744806274281067713304638767945865812886385347654536292069128423784674719847940096,
  0,
  (-154052328044993386191853244519516889562528605206429604184135808066158980869111902673118641247852002495596493780243135521813127656818671628847836747495078530960056762978006987600630428716242919462512586482758310192819971269580997943877964375755802349963350984297198590141799590908362002852655610438314356900353329609810258037655902148582630986148140854439511309075372419317372365549827145418091505822782337806385956257792),
  0,
  839744948088215255728225373369327421193990045680740969185427644318942416902890055948538523809415022902683092823539280430975886968538939955132242701514604972189394451140791981731577250515257931504543480385425355111667227726239460699781099427487613586640627803228032349535653964629446560825794441497590995169423080149207301994154884673134637092856276098610805827921922826758411132361097914530317413586648957599088640,
  0,
  (-4539974661311048743672128322198595429755018610336873559678374158794497289376770209101903082408673511364048222564553811922315523242843374992802131852162628865936044115554393708562458526978558466969555473198608620220725893506445298494757266907699356231213830281824865880928884386209952154138880922341212492226210112391523136021323669756573740073363680196006002730720242024883435617627300733240225611666352504832),
  0,
  24344687480385485020484071927270694233677813463610854077570874075222737566630750015097740088898592841233840606198111121841998989207707400403784828638959114404784508456329475487220472230005232265635304489914303191106537147069546682332711876109743686907624442413349418959973615201309383742339872827198152618045939769888058819022583238168511046375783968506998497507334013559638495620064217844310063114616832,
  0,
  (-129484383795592654956272714028197206948405878955423475086055835665619207254530054059244783586811992622537579528059644447348374997720295001879484735030127796316880526712986998442903511505991338172374025627236854211079281335517659871273111197159016043856850818505875486328901971958825001178341351708136957712236277759004992126251040821781471940723731522350359184042503297289155894552367805275263991808),
  0,
  683141223729849937698633655249420857796594075715195525112037951780469761022194555617380704725413149786337710684901940678995344342068306115183450245765179686725122161142413147783432634442557275820647753817605079551327590290312420619994064869185936028120417789463792110554172259380900185761890403815368482592093288205405048632988749303764188916247189040302783925850488100082417860758396064497664,
  0,
  (-3575203924783457698145096133893638006339054823453694936436272016384043927683495638412081561114954538089983392706314112559360696609593569935628619281196194646957959569953811666389782494633732720279321094688260188441268439078833332593953961910790828430297265480972215310206475063545226930421603059179007544094572531646441075546511096207300687315013888814342393990056349819582574184374468608),
  0,
  18561177116202438479143070615235784410322894191872815457090106216238340267611986459203675477778803967793486279562899241049564477376573123592699593433711723140633494947745718093017980097227694243857222327239478873597089181808485470710675598839488014114013196169302619920208494626326173695175952902789254988363773437174029638960826193178501164835814348534057960035127096107820105334784,
  0,
  (-95596404577872675858924496474906395958860410370795957497019210031681833735970701950754751434107240891688532651664353580186952638944101630698581155652703557681088735466605974802543418829799170320718037824125983246289890760943981264516500257041371173901264516828139048007234447759757193637416052753468435509297801700403704489124576998017325379628289170647897249748785847852859392),
  0,
  488456347770512195554568169335902788441708624556533816902269988691072380335852541849795671575650713058008600212960903618708532057594835408454935304365449389085871694025587633013460832414296347384879407898888887621020669168242370380832850660879348744970835195873438998349992514790755917651041745160370453583905191213249753756513796385185838905310244554339327558528062717952,
  0,
  (-2476137495570151041334706714418147872060247141283171269755387208037798719877907947228223033878929477162914452290735513596969473449785780814636505757042424632789350573689897003298231859643368167109915080097580498985942720275178195492915921051779284757054631635223959437249224577103596822932627177448961022828341366617243627625850698901718136411498545162062444802080768),
  0,
  12453890311805641409747459346456207835296089262615304389921763986598307842949828738147667559552655639819909500400163361576806361285347745272167219962421481593005508014296159158034282844903101916377971725443369129357783570983601731751726299150344236597004052689076869017725728408840043411643279416102869154841064431873913323541815445902862101558743064541627678720,
  0,
  (-62148824488730933406958443511752693139663682634321675425301901324508558426687213198195253974906861313942036306418063481240551203264214056227604107192682530529165106796445534069422631690671312624266283315888667166964792301585587770198154416627124576776213535827855573244680803881006078541764649799063382151735885248449156538028195809561379599101005901332480),
  0,
  307733352043258619053204950264668896990447159138257150562603330932284532946412052706591456820582982843566423910736131635862046044618842833196226851286683245752015774272668528250184787438636884823163764318503117860181697074665150120856291689731545675091110835956150582961630480042680719656749033449961646069415136132291187378479813151893007240953593856,
  0,
  (-1511979809394353670123731780968929933718387579429512152807363681257086619987451762441254215178822341425176417686620283614987277422983328841336429871145556573030920687176390851960960473669614192012571084352861803018814296539318494181828287344893735651989066234930238571242627002042185425890824630830731319244052014854944719228085969046751842140160),
  0,
  7371621822948842776239797482617910835632870531529234279769564470668134895329840097488839729048630523640388375328657490033710948827633571392527998755646388959887756220055856037713138869785781931661115924400588611603693869323583693326817415497873902117578985775564220984232430476842671999235953538290896730391833314276625118572026516117389312,
  0,
  (-35664935118666928245819555800618681939156646815391799940686434129966299569151432702147208008812390207198745982570013298070962537026129615897020417699820157323515026215084741453611157790445833274883289250935345394935375864142589427934082607289982522640441560954317530591404273439132134124331495795543395331938565127543382040061245652992),
  0,
  171236649500289491170399224551728385188021637363293794741862894566794970801224996213952268881663000211171990163247993726919357388351756399763478709869093389374182946635386895863442075346450057157902374323230303737612902710811985163535210017977977251769147969875615013912943638894048913808343283980842386564375482451092901948555264,
  0,
  (-815913852610165648726819573538622940998605821469623592955051374853335936915222941153247609685888426477058458950808197331051724939733227488577608948164193914024079840648925968808745522835768418873646430590823659724244427797991733438659547910657334650519555528751766349531698366592469258264067992085054421064503582373034590208),
  0,
  3858330788097575645150518487658881851639829055888714339523053154664955165907661334506102548174506055919370309738660352304632589121328113949378657369911397345182000507122236126530566877030681080479093607943866441906463858895907575924959959600513428625985646206952360489217497354537397617347551608764634183599933026729984,
  0,
  (-18108284109443005382820293286783855085338437381243032193706575327362658067084961988165335785110348453788297822916782117003170697606551677084406700253130917812552685775157874333821050854211288812150405552971328786555122838690714724752428316715655699184579528928204486774988784541085217129758199122893067961508036608),
  0,
  84351500513748026622979825919012532132959475828117795646915154686430005936155632267872332383064797837896177401499987963164847397183415023764462631815052493312402079880971767923219924282050299764382772332101089850237573524277938547278949576928379206369182791604778023889854048816754620583393586483096289542144,
  0,
  (-389996617827265402900644108522888776006354616971464549909753958949197730454986867479519992565653382271205542857055040386946082767514350816528033980670472762982446116098907828325843011119688708035783426011369228463540806569666785777196291199844565511703826753653521480954847142140637247500521624762843136),
  0,
  1789765330805100816454938211924528137660705831826584165242141503338994393190724374888912375594192073546723012194385058469610575614798941487319578483420331036042462009992249341544869769915392423198437696773701342454840093998957084563894435081479220869089910667367039860424788451326043459746745286656,
  0,
  (-8152919166288906834942169408600117675698594471337921187142583588657595274860536722235102394249124730857686772993818384297167445068231424140386753350152292334759794935785704042948870366750798988500132899339427001913309143550894066047456667293912352575056034179424709571429657049202650133823488),
  0,
  36866033724187639425433392678757300117968950526336682429613261801454674501106983833141182072078101993624508782493013428078340969792146396580529627583100466328072252324399765930337474541467041692287595144781047927998291875160725798751949459614800565914387360590264265841688988512885407744,
  0,
  (-165481800872548818456763126125746040893975764316781850418278130091018119020245293216412050810344207337884230300152304869435284066861727350431920069540683186061655489845962042940918164596755493400794527139466566699772170642665114379785731039117394705987864887995661312737777033412608),
  0,
  737392613897790316162467543082213501770912296527797234445321737545433660209613994869540063228742484204441195481938095625887803356740190624884075680992144530012396415132464672618458716373090261116763282771965747794426592293100542125980931414971516129088597876444141089716174848,
  0,
  (-3262016112667059497617887752854016108561300054537300848815692324247356577471604481116682221592143269666589209171856422728233227162139023573438329767094389903585150196437449985954478861975043108868666963176430834222647998413618335831083189592816236484732758860087196385280),
  0,
  14326038724752055021740102855533948314176107704656351066517870709103972404751665098887764159240518734837993506078021137678523951705295362121543170829454015973034198493316832622834074386375449877863833619042737370378498188529244883312253664166167498258090008271388672,
  0,
  (-62464409936389475069414350460603949397827098110654733994271128237915727755900633214554533925629813955190622766629269335463816884340317973925728922511447503431805491258666402983495076828976534561325577116188316901364535662349095521413942675660212888744830697472),
  0,
  270407880853586595305582677306072846635777077674136468049642921248148518481683103369065680898393678064221197116201022937836349916186906836139825192360533632125284991405817241711243104934502015824752004352984651031357336400655494140003745079625424226484224,
  0,
  (-1162250624494059354711245646654867557719814920351744460274188288982035109490730225632042378494544221147346603200781086441533750412910611506372869912245741957964574821133294493193628354837063003540440293267485630917738570971195445747452236925589520384),
  0,
  4960065506087538589423123679801688092687409066517735574954609558311233883124295861809767076915735925533833229513850918559227997752354466034910126357747393775364377664336102783078975244058691001883435633770155489486432517977790648534038738894848,
  0,
  (-21018200883346197455576261469895971349307139699095737573359182558480823906374547998888122621154900140513473949312289825239106927202078226593906180078235263039439580681654957545740410133320379962071932600080957836685113903818720438256664576),
  0,
  88437686587919864259505468859413115314362412453989482454396458972609645306996026697862146953633043265095779001902926400759663271643467645049038888363911395024425264683174425583175950156209843480050732628290137625095994278166132686848,
  0,
  (-369509840386306915104375627055864934452083539912285397142761933031348011024267200474717805568641356311293784730611678990749217036035452501017207620419175825780165935873734450630839267871221984900263975667752628536731143390625792),
  0,
  1533113903555917623872616378593096143792468847133883887054981277459760115928687795477876434987340317291858166591411535021147624585974257522794577971130309124909955194733994534297854772398798960816229746892479805131027644416,
  0,
  (-6316776070040726865447716067547140215967649946328566714026743556431087494186085061231599120501022541206911849418411383986856304118656811994710959758719535258833733331997788171058290141302571163034512469110248792129536),
  0,
  25846511991781060380682021645341008389557162529805921575717462447687565047039012347571798924709406634782589247173140216706763707586417303825849441647436910309246926314829482101935780669961493353151270207581323264,
  0,
  (-105028328787166136104423626836097855305921919757215833765198210725642359573019771823928204031497287301428660446255562336450494204437899760611783699168272278373080487372711212106510646830733698273862964215808),
  0,
  423859145612842271089277805731401311110832968901614165652296926660861105062341194975624307043158299824185607736749571394796948815386912251698450319481979947787817161063312767201071668318827327891963904,
  0,
  (-1698868202696463237838833362136490128430322985429873753156461738018328145604084094846239518610700453215863400847706719492314394156599506337231765106693333970121149575100121360928981046794723000320),
  0,
  6762903238082953551585349730887886377907129477179029027824218728895775289848436085985036466312809982245394021933236012365834656502784291026131747639476925747993798574119540123159346831949824,
  0,
  (-26739559153719183792098081604309785552971619777214667924842728488803449702032954676312545334233447184163174711939828531044830101640786535489711077581684841241281176481399379083422334976),
  0,
  105011054718514349069191439661195831328461001103908662216657040265431671250817507936393447886640079501629928221601648742902120116698490033725626666361411509352656317402992837918720,
  0,
  (-409626015230590706234592500909979629262104918359826212142822088378958432996098606681161489213505888206775071470402360402135779592804005626005651204632490710145261225111453696),
  0,
  1587170922820570154682880761368724844214283115660112480733970309485956145951493420554877204029129314419764570349467607984512740508582420305718726812314511367941755240448,
  0,
  (-6108792176713410941466677910056079106721198321562450631198076959513798934315211548063562830778382218649109505653089527127915240965581107801875618911779015335346176),
  0,
  23355771428269954435884620598421879299311989700504275278835127365358384553010527732614201578989555170955987754675093953877210422361278263979005323928317984768,
  0,
  (-88705782225439075901615743480247848041504382299465931697440129479899029030953841460123331482763205103211027376144061644313090314963447271804466909675520),
  0,
  334687914606892893291649821671692526969327031606006535672476123946452130061588746979577027206608170190035516573459238734629333781801264170145939456,
  0,
  (-1254497972857060296262076090530172903583198950928743697351150103945574694561336814537894317955588096113482225072336962834616723183854992490496),
  0,
  4671464829839996623066836071414113670177026789918378084473687327874974282199256155332409635296596763267088540136399970581758778537934848,
  0,
  (-17282264663277851021529711339042290636244700240403350338478804738950017815602901717538875304058507069645848640183526164398994358272),
  0,
  63521952779346079553951122131415669981252212653214408595789534085399141336616604725762279612686673478692133668328162421899264,
  0,
  (-231971020689431577168003307436158296916122624116212657792911636644581847537098089116004435436349640071908705530892255232),
  0,
  841668987599081792142655737297023674576615006751079550300348906631394713296806297142586523736238261679703734616064,
  0,
  (-3034293065866754060308249676185400894470191951296534949035450596580710365657932032979721580552359500603981824),
  0,
  10869089221041234796385678813377680428187803237606651525774918168855490894336069895319086641244411002880,
  0,
  (-38686456334933919417152536192363475781276312901702623283225772517191160542709275515652390585892864),
  0,
  136825035048895770378941331065295458546649771285155171490125139514022744034965340613412651008,
  0,
  (-480865453904715362102558161482549380470702534629286690389319243106829430547384228642816),
  0,
  1679358700370427054428795917104666731088549135482065861910690921856844532040073216,
  0,
  (-5828216128386122938879482480924104615490914896227309189556082924797762207744),
  0,
  20100665906968080508189260209155372788715592263270126119990244107354112,
  0,
  (-68893477673960230451485457635108772387213855210788500351938888364),
  0,
  234666057919225929307717767526563396670399637158703721971028]

theorem shifted_checked : shifted=shiftedFormula := by decide +kernel

noncomputable def bits : ℕ := 6144
noncomputable def packedPlus (i : Fin 86) : ℕ := bitHorner bits 32 (parameter i) 2 (positiveList shifted)
noncomputable def packedMinus (i : Fin 86) : ℕ := bitHorner bits 32 (parameter i) 2 (negativeList shifted)

structure Record where
  pp : ℕ
  pm : ℕ
  z : List ℤ
  deriving Repr

noncomputable def makeRecord (i : Fin 86) : Record :=
  let p := packedPlus i
  let m := packedMinus i
  ⟨p,m,extract bits 1 32 p m⟩

noncomputable def carry (i : Fin 86) : Prop :=
  Nat.ofDigits (parameter i+2) (positiveList shifted)< Nat.shiftLeft 1 bits ∧
  Nat.ofDigits (parameter i+2) (negativeList shifted)< Nat.shiftLeft 1 bits
noncomputable instance (i : Fin 86) : Decidable (carry i) := inferInstanceAs (Decidable (_∧_))

noncomputable def checkErrors (ν D : ℕ) : ℕ → List ℤ → List ℤ → Bool
  | 0,_,_ => true
  | n+1,z::zs,c::cs => decide (|((ν:ℤ)*z*100000000-c*D)|≤ 10*(D:ℤ)) && checkErrors ν D n zs cs
  | n+1,z::zs,[] => decide (|((ν:ℤ)*z*100000000)|≤ 10*(D:ℤ)) && checkErrors ν D n zs []
  | _+1,[],_ => false

noncomputable def checkRecord (i : Fin 86) (r : Record) : Bool :=
  decide (carry i) && decide (r.pp=packedPlus i) && decide (r.pm=packedMinus i) &&
  decide (r.z=extract bits 1 32 r.pp r.pm) &&
  checkErrors (normalization i) denominator 32 r.z
    (CertifiedLocalCandidates.coefficientNumerators.getD i.val [])

end CertifiedGlobalTranslation

end Height100Module78

/- Source module: PolynomialTranslationConvolution. -/
section Height100Module79

open Finset
namespace CertifiedPolynomialTranslation

/-- A binomial shift is a single factorial-weighted correlation. This identity
permits one packed integer multiplication to certify all local coefficients. -/
lemma translatedCoefficient_factorial_correlation (a : ℕ → ℝ) (N n : ℕ) (T : ℝ) :
    translatedCoefficient a N n T=
      (1/(n.factorial:ℝ))*∑ l ∈ range (N-n),
        a (n+l)*((n+l).factorial:ℝ)*T^l/(l.factorial:ℝ) := by
  unfold translatedCoefficient
  by_cases hn : n≤ N
  · conv_lhs => rw [←Nat.add_sub_of_le hn,sum_range_add]
    have hzero : ∑ m ∈ range n, a m*(m.choose n:ℝ)*T^(m-n)=0 := by
      apply sum_eq_zero
      intro m hm
      rw [Nat.choose_eq_zero_of_lt (mem_range.mp hm)]
      simp
    rw [hzero,zero_add,mul_sum]
    apply sum_congr rfl
    intro l hl
    rw [Nat.cast_choose ℝ (Nat.le_add_right n l),Nat.add_sub_cancel_left]
    ring
  · have hN : N≤ n := by omega
    rw [Nat.sub_eq_zero_of_le hN,range_zero,sum_empty,mul_zero]
    apply sum_eq_zero
    intro m hm
    rw [Nat.choose_eq_zero_of_lt ((mem_range.mp hm).trans_le hN)]
    simp

end CertifiedPolynomialTranslation

end Height100Module79

/- Source module: TranslationFactorialBase. -/
section Height100Module80

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000
namespace CertifiedTranslationConvolution
open CertifiedGlobalTranslation CertifiedPackedConvolution CertifiedListODEVectors
open CertifiedExponentialIntegerSequence CertifiedPackedExtraction

noncomputable def weightFormula : List ℤ := shifted.zipIdx.map (fun (x,j) =>
  x*(j.factorial:ℤ)/(commonFactor:ℤ))

theorem weights_checked : weights=weightFormula := by decide +kernel
theorem weights_reconstruct :
    weights.map (fun x => x*(commonFactor:ℤ))=
      shifted.zipIdx.map (fun (x,j) => x*(j.factorial:ℤ)) := by decide +kernel
theorem encodedPlus_checked : encodedPlus=encode bits (positiveList weights).reverse := by rfl
theorem encodedMinus_checked : encodedMinus=encode bits (negativeList weights).reverse := by rfl

noncomputable def digitBound : ℕ := Nat.shiftLeft 1 4200

theorem global_carry_plus : (positiveList weights).sum*513*digitBound<1 <<< bits := by decide +kernel
theorem global_carry_minus : (negativeList weights).sum*513*digitBound<1 <<< bits := by decide +kernel

end CertifiedTranslationConvolution

end Height100Module80

/- Source module: PackedTranslationData. -/
section Height100Module81

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

noncomputable def makeRecord (i : Fin 86) : Record :=
  let e := expSeq (parameter i) 513 0 (512).factorial
  let ep := encode bits e
  let wp := productWindow encodedPlus ep
  let wm := productWindow encodedMinus ep
  ⟨ep,wp,wm,(extract bits 1 32 wp wm).reverse⟩

noncomputable def checkRecord (i : Fin 86) (r : Record) : Bool :=
  CertifiedPackedExponentialSequence.checkPacked bits (parameter i) 512 digitBound r.ep &&
  decide (r.wp=productWindow encodedPlus r.ep) &&
  decide (r.wm=productWindow encodedMinus r.ep) &&
  decide (r.z=(extract bits 1 32 r.wp r.wm).reverse) &&
  checkErrors (normalization i) 0 1 32 r.z
    (CertifiedLocalCandidates.coefficientNumerators.getD i.val [])
end CertifiedPackedTranslation

end Height100Module81

/- Source module: LiteralTranslationData. -/
section Height100Module82

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedLiteralTranslation

end Height100Module82

/- Source module: LiteralTranslationCertificate. -/
section Height100Module83
namespace CertifiedLiteralTranslation
theorem records_checked (i : Fin 86) : checkRecord i (recordAt i)=true :=
  TaoFivePrimes.rh14to100_translation_checks i
end CertifiedLiteralTranslation
end Height100Module83

/- Source module: ExponentialSequenceAnalyticBound. -/
section Height100Module84

namespace CertifiedExponentialSequenceBound
open CertifiedExponentialSequenceCheck CertifiedPackedExponentialSequence
open CertifiedPackedConvolution
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

lemma factorial_exp199_lt : ((512).factorial:ℝ)*Real.exp 199<(2:ℝ)^4200 := by
  have hbase : Real.exp 1≤ (27183:ℝ)/10000 :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  have hexp : Real.exp 199≤ ((27183:ℝ)/10000)^199 := by
    rw [show Real.exp 199=(Real.exp 1)^199 by
      simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 199]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hbase 199
  exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_lt (by norm_num)

lemma checked_digit_lt (a : ℕ) (ha : a≤ 199) (xs : List ℕ)
    (hlen : xs.length=513) (h0 : xs.headD 0=(512).factorial)
    (hc : CertifiedExponentialSequenceCheck.checkSteps a 0 xs=true)
    (j : ℕ) (hj : j<513) : xs.getD j 0<2^4200 := by
  have hratio := checked_sequence_real a 512 xs hlen h0 hc j (by omega)
  have ha' : (a:ℝ)≤ 199 := by exact_mod_cast ha
  have he : (xs.getD j 0:ℝ)/((512).factorial:ℝ)≤ Real.exp 199 := by
    rw [hratio]
    exact (Real.pow_div_factorial_le_exp (a:ℝ) (by positivity) j).trans
      (Real.exp_le_exp.mpr ha')
  have hf : (0:ℝ)<(512).factorial := by exact_mod_cast Nat.factorial_pos 512
  have hh := (div_le_iff₀ hf).mp he
  have hh' : (xs.getD j 0:ℝ)<(2:ℝ)^4200 :=
    hh.trans_lt (by simpa only [mul_comm] using factorial_exp199_lt)
  exact_mod_cast hh'

lemma checked_bounds (a : ℕ) (ha : a≤ 199) (xs : List ℕ)
    (hlen : xs.length=513) (h0 : xs.headD 0=(512).factorial)
    (hc : CertifiedExponentialSequenceCheck.checkSteps a 0 xs=true) :
    xs.all (fun x => decide (x≤ 2^4200))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨j,hj,hx⟩ := List.getElem_of_mem hx
  have hh := checked_digit_lt a ha xs hlen h0 hc j (by omega)
  rw [List.getD_eq_getElem xs 0 hj,hx] at hh
  exact decide_eq_true hh.le

/-- No concrete coefficient bound checks are needed for the translation sequences. -/
theorem checked_original (bits block a : ℕ) (hbits : 4200< bits) (ha : a≤ 199)
    (xs chunks : List ℕ) (hlen : xs.length=513) (h0 : xs.headD 0=(512).factorial)
    (hc : CertifiedExponentialSequenceCheck.checkSteps a 0 xs=true)
    (he : CertifiedChunkedEncoding.checkChunks bits block xs chunks=true) :
    checkPacked bits a 512 (2^4200) (encode (bits*block) chunks)=true := by
  exact CertifiedChunkedEncoding.checked_original bits block a 512 (2^4200) xs chunks
    (pow_lt_pow_right₀ (by norm_num : (1:ℕ)<2) hbits) hlen h0
    (checked_bounds a ha xs hlen h0 hc) hc he

end CertifiedExponentialSequenceBound

end Height100Module84

/- Source module: PackedHornerAnalytic. -/
section Height100Module85

set_option autoImplicit false
open Complex Finset
namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

lemma ofDigits_complex_sum (xs : List ℕ) (z : ℂ) :
    Nat.ofDigits z xs=∑ m ∈ range xs.length, (xs.getD m 0:ℂ)*z^m := by
  induction xs with
  | nil => simp [Nat.ofDigits]
  | cons a xs ih =>
    rw [List.length_cons,sum_range_succ',Nat.ofDigits,ih]
    simp only [List.getD_cons_zero,List.getD_cons_succ,pow_zero,mul_one]
    rw [add_comm]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [pow_succ]
    ring

lemma ofDigits_entire (xs : List ℕ) : Differentiable ℂ (fun z : ℂ => Nat.ofDigits z xs) := by
  have he : (fun z : ℂ => Nat.ofDigits z xs)=
      (fun z : ℂ => ∑ m ∈ range xs.length, (xs.getD m 0:ℂ)*z^m) :=
    funext (ofDigits_complex_sum xs)
  rw [he]
  fun_prop

lemma choose_zero_power (m n : ℕ) :
    (m.choose n:ℝ)*(0:ℝ)^(m-n)=if m=n then 1 else 0 := by
  rcases lt_trichotomy m n with h|rfl|h
  · rw [Nat.choose_eq_zero_of_lt h,if_neg (by omega)]
    simp
  · simp
  · rw [if_neg (by omega),zero_pow (by omega),mul_zero]

lemma coefficient_ofDigits (xs : List ℕ) (n : ℕ) :
    coefficient (fun z : ℂ => Nat.ofDigits z xs) 0 n=(xs.getD n 0:ℂ) := by
  have he : (fun z : ℂ => Nat.ofDigits z xs)=
      powerPolynomial (fun m => (xs.getD m 0:ℝ)) xs.length := by
    funext z
    simpa only [powerPolynomial,Complex.ofReal_natCast] using ofDigits_complex_sum xs z
  rw [he]
  have hh := coefficient_powerPolynomial (fun m => (xs.getD m 0:ℝ)) xs.length n 0
  rw [Complex.ofReal_zero] at hh
  rw [hh]
  unfold translatedCoefficient
  simp_rw [mul_assoc,choose_zero_power,mul_ite,mul_one,mul_zero]
  by_cases hn : n< xs.length
  · simp [hn]
  · rw [List.getD_eq_default xs 0 (by omega)]
    simp [hn]

lemma translated_analytic_coefficient (b q : ℕ) (xs : List ℕ) (n : ℕ) :
    coefficient (fun z : ℂ => Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) xs) 0 n=
      ((translated b q xs).getD n 0:ℂ) := by
  have he : (fun z : ℂ => Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) xs)=
      (fun z : ℂ => Nat.ofDigits z (translated b q xs)) := by
    funext z
    exact (translated_complex z b q xs).symm
  rw [he,coefficient_ofDigits]

end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
lemma coefficient_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z-g z) c n=coefficient f c n-coefficient g c n := by
  unfold coefficient
  rw [iteratedDeriv_fun_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt,sub_div]
lemma coefficient_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (fun z => a*f z) c n=a*coefficient f c n := by
  unfold coefficient
  rw [iteratedDeriv_const_mul_field,mul_div_assoc]
lemma coefficient_shift (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (fun z => f (c+z)) 0 n=coefficient f c n := by
  unfold coefficient
  rw [iteratedDeriv_comp_const_add]
  simp only [add_zero]
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
lemma signed_affine_coefficient (b q : ℕ) (xs ys : List ℕ)
    (F : ℂ → ℂ) (D T : ℂ) (n : ℕ)
    (he : ∀ z : ℂ, Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) xs-
      Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) ys=D*F (T+z)) :
    ((translated b q xs).getD n 0:ℂ)-((translated b q ys).getD n 0:ℂ)=
      D*coefficient F T n := by
  let f : ℂ → ℂ := fun z => Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) xs
  let g : ℂ → ℂ := fun z => Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) ys
  have hf : Differentiable ℂ f := (ofDigits_entire xs).comp (show Differentiable ℂ (fun z : ℂ => (b:ℂ)+(q:ℂ)*z) by fun_prop)
  have hg : Differentiable ℂ g := (ofDigits_entire ys).comp (show Differentiable ℂ (fun z : ℂ => (b:ℂ)+(q:ℂ)*z) by fun_prop)
  have h := congrArg (fun H : ℂ → ℂ => coefficient H 0 n) (funext he)
  change coefficient (fun z => f z-g z) 0 n=coefficient (fun z => D*F (T+z)) 0 n at h
  rw [coefficient_sub f g hf hg,coefficient_const_mul,coefficient_shift] at h
  have hfp : coefficient f 0 n=((translated b q xs).getD n 0:ℂ) :=
    translated_analytic_coefficient b q xs n
  have hgp : coefficient g 0 n=((translated b q ys).getD n 0:ℂ) :=
    translated_analytic_coefficient b q ys n
  rwa [hfp,hgp] at h
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation
lemma coefficient_ofDigits_at (xs : List ℕ) (T : ℝ) (n : ℕ) :
    coefficient (fun z : ℂ => Nat.ofDigits z xs) T n=
      (translatedCoefficient (fun m => (xs.getD m 0:ℝ)) xs.length n T:ℂ) := by
  have he : (fun z : ℂ => Nat.ofDigits z xs)=
      powerPolynomial (fun m => (xs.getD m 0:ℝ)) xs.length := by
    funext z
    simpa only [powerPolynomial,Complex.ofReal_natCast] using ofDigits_complex_sum xs z
  rw [he,coefficient_powerPolynomial]

lemma translated_real_coefficient (b q : ℕ) (xs : List ℕ) (n : ℕ) :
    ((translated b q xs).getD n 0:ℝ)=
      (q:ℝ)^n*translatedCoefficient (fun m => (xs.getD m 0:ℝ)) xs.length n b := by
  have h := coefficient_affine (fun z : ℂ => Nat.ofDigits z xs) (ofDigits_entire xs) b q n
  rw [translated_analytic_coefficient] at h
  have hc := coefficient_ofDigits_at xs (b:ℝ) n
  simp only [Complex.ofReal_natCast] at hc
  rw [hc] at h
  exact_mod_cast h

lemma translated_signed_coefficient (b q : ℕ) (xs : List ℤ) (n : ℕ) :
    (((translated b q (CertifiedListODEVectors.positiveList xs)).getD n 0:ℝ)-
      ((translated b q (CertifiedListODEVectors.negativeList xs)).getD n 0:ℝ))=
      (q:ℝ)^n*translatedCoefficient (fun m => (xs.getD m 0:ℝ)) xs.length n b := by
  rw [translated_real_coefficient,translated_real_coefficient,←mul_sub]
  congr 1
  unfold translatedCoefficient
  simp only [CertifiedListODEVectors.positiveList,CertifiedListODEVectors.negativeList,List.length_map]
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  change ((CertifiedListODEVectors.positiveList xs).getD m 0:ℝ)*(m.choose n:ℝ)*(b:ℝ)^(m-n)-
    ((CertifiedListODEVectors.negativeList xs).getD m 0:ℝ)*(m.choose n:ℝ)*(b:ℝ)^(m-n)=_
  rw [CertifiedListODEVectors.positiveList_getD,CertifiedListODEVectors.negativeList_getD,
    ←sub_mul,←sub_mul]
  have hs : ((xs.getD m 0).toNat:ℝ)-((-(xs.getD m 0)).toNat:ℝ)=(xs.getD m 0:ℝ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg (xs.getD m 0)
  rw [hs]
end CertifiedPackedHorner

end Height100Module85

/- Source module: TranslationConvolutionAlgebra. -/
section Height100Module86

set_option autoImplicit false
open Finset Complex
namespace CertifiedTranslationAlgebra
open CertifiedPolynomialTranslation CertifiedPackedHorner CertifiedListODEVectors
open CertifiedPackedCorrelation CertifiedPackedConvolution CertifiedSignedODEConvolution

noncomputable def signedTranslated (b q : ℕ) (xs : List ℤ) (n : ℕ) : ℝ :=
  ((translated b q (positiveList xs)).getD n 0:ℝ)-
    ((translated b q (negativeList xs)).getD n 0:ℝ)

noncomputable def correlation (N : ℕ) (w : List ℤ) (e : List ℕ) (n : ℕ) : ℝ :=
  ∑ l ∈ range (N-n), (w.getD (n+l) 0:ℝ)*(e.getD l 0:ℝ)

lemma factorial_correlation (K b q n : ℕ) (xs w : List ℤ) (e : List ℕ) (G : ℝ)
    (hx : xs.length=K+1) (hn : n< K+1)
    (hw : ∀ j< K+1, (w.getD j 0:ℝ)*G=(xs.getD j 0:ℝ)*(j.factorial:ℝ))
    (he : ∀ j< K+1, (e.getD j 0:ℝ)/(K.factorial:ℝ)=(b:ℝ)^j/(j.factorial:ℝ)) :
    (q:ℝ)^n*G*correlation (K+1) w e n=
      (K.factorial:ℝ)*(n.factorial:ℝ)*signedTranslated b q xs n := by
  have hK : (K.factorial:ℝ)≠0 := by exact_mod_cast K.factorial_ne_zero
  have hnF : (n.factorial:ℝ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have hsum : G*correlation (K+1) w e n=(K.factorial:ℝ)*
      ∑ l ∈ range (K+1-n), (xs.getD (n+l) 0:ℝ)*((n+l).factorial:ℝ)*
        (b:ℝ)^l/(l.factorial:ℝ) := by
    unfold correlation
    rw [mul_sum,mul_sum]
    apply sum_congr rfl
    intro l hl
    have hl' := mem_range.mp hl
    have hwl := hw (n+l) (by omega)
    have hel := (div_eq_iff hK).mp (he l (by omega))
    calc
      _ = ((w.getD (n+l) 0:ℝ)*G)*(e.getD l 0:ℝ) := by ring
      _ = _ := by rw [hwl,hel]; ring
  unfold signedTranslated
  rw [translated_signed_coefficient,hx,translatedCoefficient_factorial_correlation]
  rw [mul_assoc,hsum]
  field_simp

end CertifiedTranslationAlgebra

namespace CertifiedTranslationAlgebra
open CertifiedPackedConvolution CertifiedSignedODEConvolution
lemma reversed_tail (N : ℕ) (w e : List ℕ) (hw : w.length=N)
    (n : ℕ) (hn : n< N) :
    (∑ k ∈ range (N-1-n+1), w.reverse.getD k 0*e.getD (N-1-n-k) 0)=
      ∑ l ∈ range (N-n), w.getD (n+l) 0*e.getD l 0 := by
  have hN : N-1-n+1=N-n := by omega
  rw [hN]
  rw [←sum_range_reflect (fun k => w.reverse.getD k 0*e.getD (N-1-n-k) 0) (N-n)]
  apply sum_congr rfl
  intro l hl
  have hl' := mem_range.mp hl
  rw [List.getD_reverse (N-n-1-l) (by omega)]
  simp only [hw]
  congr 2 <;> omega

lemma packed_tail (bits N : ℕ) (w e : List ℕ) (hw : w.length=N)
    (n : ℕ) (hn : n< N) (hc : w.reverse.sum*e.sum<2^bits) :
    digit bits (encode bits w.reverse*encode bits e) (N-1-n)=
      ∑ l ∈ range (N-n), w.getD (n+l) 0*e.getD l 0 := by
  rw [digit,shiftRight_product_digit bits w.reverse e hc]
  exact reversed_tail N w e hw n hn
end CertifiedTranslationAlgebra

end Height100Module86

/- Source module: MomentRecordSound. -/
section Height100Module87

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset Complex
namespace CertifiedMomentRecords
open CertifiedPackedCorrelation CertifiedMomentArithmetic CertifiedMomentConvolution
open CertifiedListODEVectors CertifiedPackedExtraction CertifiedSignedODEConvolution
open CertifiedGlobalJetCenters CertifiedFixedPoint CertifiedPackedConvolution

theorem checkRecord_conditions (i : Fin 16) (d : Record) (hc : checkRecord i d=true) :
    initialCondition d ∧ d.h=centerNumerators i ∧ correlationCarry d ∧
    d.cp=correlationProduct (positiveList d.h) ∧ d.cm=correlationProduct (negativeList d.h) ∧
    d.b=extract correlationBits 1 184 (d.cp >>> (correlationBits*183)) (d.cm >>> (correlationBits*183)) ∧
    momentCarry i d ∧ d.pp=momentProduct (positiveList (scaledCorrelations d.b)) (panelParameter i) ∧
    d.pm=momentProduct (negativeList (scaledCorrelations d.b)) (panelParameter i) ∧
    d.z=extract momentBits 2 256 d.pp d.pm := by
  simpa only [checkRecord,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc

lemma checked_correlations (i : Fin 16) (d : Record) (hc : checkRecord i d=true)
    (m : ℕ) (hm : m<184) :
    d.b.getD m 0=signedCorrelation 184 d.h CertifiedMomentWeights.weights m := by
  obtain ⟨hs,_hh,hcarry,hcp,hcm,hb,_hm,_hpp,_hpm,_hz⟩ := checkRecord_conditions i d hc
  have hp : digit correlationBits d.cp (183+m)=
      CertifiedPackedCorrelation.correlation 184 (positiveList d.h) CertifiedMomentWeights.weights m := by
    rw [hcp,correlationProduct]
    exact packed_correlation correlationBits 184 _ _ (by simpa [positiveList] using hs.1)
      CertifiedMomentWeights.weights_length m hm hcarry.1
  have hn : digit correlationBits d.cm (183+m)=
      CertifiedPackedCorrelation.correlation 184 (negativeList d.h) CertifiedMomentWeights.weights m := by
    rw [hcm,correlationProduct]
    exact packed_correlation correlationBits 184 _ _ (by simpa [negativeList] using hs.1)
      CertifiedMomentWeights.weights_length m hm hcarry.2
  rw [hb,extract_getD _ _ _ _ _ m hm]
  simp only [one_mul,digit_shift_by]
  rw [hp,hn]
  exact (signedCorrelation_split 184 d.h CertifiedMomentWeights.weights m).symm

lemma checked_even_convolution (i : Fin 16) (d : Record) (hc : checkRecord i d=true)
    (j : ℕ) (hj : j<256) :
    d.z.getD j 0=convolutionNumerator (scaledCorrelations d.b) (centerSequence (panelParameter i)) (2*j) := by
  obtain ⟨_hs,_hh,_hcarry,_hcp,_hcm,_hb,hm,hpp,hpm,hz⟩ := checkRecord_conditions i d hc
  have hk : 2*j<512 := by omega
  have hp : digit momentBits d.pp (2*j)=
      ∑ m ∈ range (2*j+1), (positiveList (scaledCorrelations d.b)).getD m 0 *
        (centerSequence (panelParameter i)).getD (2*j-m) 0 := by
    rw [hpp,momentProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate _ _ _ _ hk,digit]
    exact shiftRight_product_digit _ _ _ hm.1 _
  have hn : digit momentBits d.pm (2*j)=
      ∑ m ∈ range (2*j+1), (negativeList (scaledCorrelations d.b)).getD m 0 *
        (centerSequence (panelParameter i)).getD (2*j-m) 0 := by
    rw [hpm,momentProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate _ _ _ _ hk,digit]
    exact shiftRight_product_digit _ _ _ hm.2 _
  rw [hz,extract_getD _ _ _ _ _ j hj,hp,hn]
  exact (convolutionNumerator_split (scaledCorrelations d.b) (centerSequence (panelParameter i)) (2*j)).symm

lemma checked_panel_integer (i : Fin 16) (d : Record) (hc : checkRecord i d=true)
    (j : ℕ) (hj : j<256) :
    scalarPanel (CertifiedGlobalJetCenters.jet i.val) 64
        (CertifiedGlobalQuadrature.panelCenter i.val) (3/16) 184 (2*j) =
      3*(d.z.getD j 0:ℂ)/momentDenominator := by
  obtain ⟨hs,hh,_rest⟩ := checkRecord_conditions i d hc
  have hp : (64:ℝ)*CertifiedGlobalQuadrature.panelCenter i.val=panelParameter i := by
    unfold CertifiedGlobalQuadrature.panelCenter panelParameter
    push_cast
    ring
  have he := scalarPanel_integer d.h d.b hs.2.1 (checked_correlations i d hc)
    (panelParameter i) (CertifiedGlobalQuadrature.panelCenter i.val) hp (2*j) (by omega)
  rw [←checked_even_convolution i d hc j hj] at he
  rw [hh] at he
  have hq : CertifiedGlobalJetCenters.jet i.val =
      (fun k => ((centerNumerators i).getD k 0:ℂ)/scale310) := by
    funext k
    simp only [CertifiedGlobalJetCenters.jet,centers,dif_pos i.isLt]
  rw [hq]
  exact he

end CertifiedMomentRecords

end Height100Module87

/- Source module: IntegerRounding. -/
section Height100Module88

set_option autoImplicit false
namespace CertifiedIntegerRounding

lemma integer_division_error (a : ℤ) (b : ℕ) (hb : 0< b) :
    |(a:ℝ)/b-((a/(b:ℤ):ℤ):ℝ)|≤ 1 := by
  have hbi : (0:ℤ)< b := by exact_mod_cast hb
  have hbr : (0:ℝ)< b := by exact_mod_cast hb
  have h0 : (0:ℝ)≤ ((a%(b:ℤ):ℤ):ℝ) := by
    exact_mod_cast Int.emod_nonneg a hbi.ne'
  have h1 : ((a%(b:ℤ):ℤ):ℝ)< b := by
    exact_mod_cast Int.emod_lt_of_pos a hbi
  have he : ((a/(b:ℤ):ℤ):ℝ)*(b:ℝ)+((a%(b:ℤ):ℤ):ℝ)=(a:ℝ) := by
    exact_mod_cast Int.ediv_mul_add_emod a (b:ℤ)
  have hq : (a:ℝ)/b-((a/(b:ℤ):ℤ):ℝ)=((a%(b:ℤ):ℤ):ℝ)/b := by
    apply (eq_div_iff hbr.ne').mpr
    field_simp
    linarith
  rw [hq,abs_of_nonneg (div_nonneg h0 hbr.le)]
  exact (div_le_one hbr).mpr h1.le

noncomputable def roundedNumerator (S D : ℕ) (z : ℤ) : ℤ := (3*z*S)/(D:ℤ)

lemma rounded_error (S D : ℕ) (hS : 0< S) (hD : 0< D) (z : ℤ) :
    |3*(z:ℝ)/D-(roundedNumerator S D z:ℝ)/S|≤ 1/(S:ℝ) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hDr : (0:ℝ)< D := by exact_mod_cast hD
  have he := integer_division_error (3*z*S) D hD
  have hq : 3*(z:ℝ)/D-(roundedNumerator S D z:ℝ)/S =
      (((3*z*S:ℤ):ℝ)/D-((3*z*S)/(D:ℤ):ℤ))/S := by
    unfold roundedNumerator
    push_cast
    field_simp
  rw [hq,abs_div,abs_of_pos hSr]
  exact div_le_div_of_nonneg_right he hSr.le

end CertifiedIntegerRounding

end Height100Module88

/- Source module: GlobalMomentEnclosure. -/
section Height100Module89
namespace CertifiedGlobalMomentEnclosure
theorem moments_enclosed (j : ℕ) (hj : j<256) :
    |CertifiedGlobalMoments.moment j-candidateMoment j|≤ 1/10^46 :=
  TaoFivePrimes.rh14to100_moments_enclosed j hj
end CertifiedGlobalMomentEnclosure
end Height100Module89

/- Source module: TranslationSound. -/
section Height100Module90

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset
namespace CertifiedGlobalTranslation
open CertifiedPackedHorner CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTaylorQuadrature CertifiedPolynomialTranslation

lemma shifted_length : shifted.length=513 := by rw [shifted_checked]; exact List.length_ofFn
lemma shifted_getD (m : ℕ) (hm : m<513) :
    shifted.getD m 0=CertifiedDenseGlobalPolynomial.coefficient momentNumerator m*(2:ℤ)^(512-m) := by
  rw [shifted_checked]
  simp only [shiftedFormula,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos hm,Option.getD_some,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma signed_digits_sum (xs : List ℤ) (z : ℂ) :
    Nat.ofDigits z (positiveList xs)-Nat.ofDigits z (negativeList xs)=
      ∑ m ∈ range xs.length, (xs.getD m 0:ℂ)*z^m := by
  rw [ofDigits_complex_sum,ofDigits_complex_sum]
  simp only [positiveList,negativeList,List.length_map]
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  change ((positiveList xs).getD m 0:ℂ)*z^m-((negativeList xs).getD m 0:ℂ)*z^m=_
  rw [positiveList_getD,negativeList_getD,←sub_mul]
  have hs : ((xs.getD m 0).toNat:ℂ)-((-(xs.getD m 0)).toNat:ℂ)=(xs.getD m 0:ℂ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg (xs.getD m 0)
  rw [hs]

lemma shifted_polynomial (z : ℂ) :
    Nat.ofDigits z (positiveList shifted)-Nat.ofDigits z (negativeList shifted)=
      (denominator:ℂ)*criticalXiPolynomial (CertifiedDenseGlobalPolynomial.moments momentNumerator) (z/2) := by
  rw [signed_digits_sum,shifted_length]
  have hD : (denominator:ℂ)=(2:ℂ)^512*(CertifiedDenseGlobalPolynomial.denominator:ℂ) := by
    unfold denominator
    rw [Nat.shiftLeft_eq',Nat.shiftLeft_eq,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    exact mul_comm _ _
  rw [hD,mul_assoc,←CertifiedDenseGlobalPolynomial.integer_polynomial_identity,mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm' := mem_range.mp hm
  rw [shifted_getD m hm']
  push_cast
  have hp : (2:ℂ)^512=(2:ℂ)^(512-m)*(2:ℂ)^m := by
    rw [←pow_add,Nat.sub_add_cancel (by omega)]
  rw [div_pow,hp]
  field_simp

lemma checkErrors_entry (ν D n : ℕ) (zs cs : List ℤ)
    (hc : checkErrors ν D n zs cs=true) (j : ℕ) (hj : j< n) :
    |(ν:ℤ)*zs.getD j 0*100000000-cs.getD j 0*D|≤ 10*(D:ℤ) := by
  induction n generalizing zs cs j with
  | zero => omega
  | succ n ih =>
    cases zs with
    | nil => simp [checkErrors] at hc
    | cons z zs =>
      cases cs with
      | nil =>
        simp only [checkErrors,Bool.and_eq_true,decide_eq_true_eq] at hc
        cases j with
        | zero => simpa using hc.1
        | succ j => simpa only [List.getD_cons_succ,List.getD_nil] using ih zs [] hc.2 j (by omega)
      | cons c cs =>
        simp only [checkErrors,Bool.and_eq_true,decide_eq_true_eq] at hc
        cases j with
        | zero => simpa using hc.1
        | succ j => exact ih zs cs hc.2 j (by omega)

lemma record_conditions (i : Fin 86) (r : Record) (hc : checkRecord i r=true) :
    carry i ∧ r.pp=packedPlus i ∧ r.pm=packedMinus i ∧
      r.z=extract bits 1 32 r.pp r.pm ∧
      checkErrors (normalization i) denominator 32 r.z
        (CertifiedLocalCandidates.coefficientNumerators.getD i.val [])=true := by
  simpa only [checkRecord,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc

lemma checked_digits (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (n : ℕ) (hn : n<32) :
    (r.z.getD n 0:ℂ)=
      ((translated (parameter i) 2 (positiveList shifted)).getD n 0:ℂ)-
      ((translated (parameter i) 2 (negativeList shifted)).getD n 0:ℂ) := by
  obtain ⟨hcarry,hp,hm,hz,_he⟩ := record_conditions i r hc
  have hcp : Nat.ofDigits (parameter i+2) (positiveList shifted)<2^bits := by
    simpa only [Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul] using hcarry.1
  have hcm : Nat.ofDigits (parameter i+2) (negativeList shifted)<2^bits := by
    simpa only [Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul] using hcarry.2
  rw [hz,extract_getD bits 1 32 _ _ n hn,hp,hm]
  simp only [one_mul,Int.cast_sub,Int.cast_natCast,digit,packedPlus,packedMinus]
  rw [bitHorner_digit bits 32 (parameter i) 2 _ hcp n hn,
    bitHorner_digit bits 32 (parameter i) 2 _ hcm n hn]

lemma checked_coefficient (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (n : ℕ) (hn : n<32) :
    (r.z.getD n 0:ℝ)=(denominator:ℝ)*
      localGlobalCoefficient (CertifiedDenseGlobalPolynomial.moments momentNumerator)
        ((parameter i:ℝ)/2) n := by
  have he : ∀ z : ℂ,
      Nat.ofDigits ((parameter i:ℂ)+(2:ℂ)*z) (positiveList shifted)-
        Nat.ofDigits ((parameter i:ℂ)+(2:ℂ)*z) (negativeList shifted)=
      (denominator:ℂ)*criticalXiPolynomial (CertifiedDenseGlobalPolynomial.moments momentNumerator)
        ((parameter i:ℂ)/2+z) := by
    intro z
    rw [shifted_polynomial]
    rw [show ((parameter i:ℂ)+2*z)/2=(parameter i:ℂ)/2+z by ring]
  have h := signed_affine_coefficient (parameter i) 2 (positiveList shifted)
    (negativeList shifted) (criticalXiPolynomial (CertifiedDenseGlobalPolynomial.moments momentNumerator))
    denominator ((parameter i:ℂ)/2) n he
  have hd := (checked_digits i r hc n hn).trans h
  have hT : (parameter i:ℂ)/2=Complex.ofReal ((parameter i:ℝ)/2) := by push_cast; rfl
  rw [hT,coefficient_criticalXi] at hd
  exact_mod_cast hd

lemma translated_value (b n : ℕ) :
    (((translated b 2 (positiveList shifted)).getD n 0:ℝ)-
      ((translated b 2 (negativeList shifted)).getD n 0:ℝ))=(denominator:ℝ)*
      localGlobalCoefficient (CertifiedDenseGlobalPolynomial.moments momentNumerator)
        ((b:ℝ)/2) n := by
  have he : ∀ z : ℂ,
      Nat.ofDigits ((b:ℂ)+(2:ℂ)*z) (positiveList shifted)-
        Nat.ofDigits ((b:ℂ)+(2:ℂ)*z) (negativeList shifted)=
      (denominator:ℂ)*criticalXiPolynomial (CertifiedDenseGlobalPolynomial.moments momentNumerator)
        ((b:ℂ)/2+z) := by
    intro z
    rw [shifted_polynomial]
    rw [show ((b:ℂ)+2*z)/2=(b:ℂ)/2+z by ring]
  have h := signed_affine_coefficient (b) 2 (positiveList shifted)
    (negativeList shifted) (criticalXiPolynomial (CertifiedDenseGlobalPolynomial.moments momentNumerator))
    denominator ((b:ℂ)/2) n he
  have hd := h
  have hT : (b:ℂ)/2=Complex.ofReal ((b:ℝ)/2) := by push_cast; rfl
  rw [hT,coefficient_criticalXi] at hd
  exact_mod_cast hd

lemma denominator_pos : 0< denominator := by
  unfold denominator
  rw [Nat.shiftLeft_eq',Nat.shiftLeft_eq]
  exact Nat.mul_pos CertifiedDenseGlobalPolynomial.denominator_pos (by positivity)

lemma parameter_center (i : Fin 86) : (parameter i:ℝ)/2=CertifiedLocalXi.slabCenter i := by
  unfold parameter CertifiedLocalXi.slabCenter
  push_cast
  ring

lemma moments_eq : CertifiedDenseGlobalPolynomial.moments momentNumerator=
    CertifiedGlobalMomentEnclosure.candidateMoment := by
  funext j
  simp only [CertifiedDenseGlobalPolynomial.moments,CertifiedDenseGlobalPolynomial.momentScale,
    momentNumerator,CertifiedGlobalMomentEnclosure.candidateMoment,Nat.cast_pow,Nat.cast_ofNat]
  rfl

lemma checked_translation (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (n : ℕ) (hn : n<32) :
    |(normalization i:ℝ)*
      localGlobalCoefficient CertifiedGlobalMomentEnclosure.candidateMoment
        (CertifiedLocalXi.slabCenter i) n-
      (CertifiedLocalCandidates.at i.val n:ℝ)/100000000|≤ 1/10^7 := by
  obtain ⟨_hc,_hp,_hm,_hz,he⟩ := record_conditions i r hc
  have h := checkErrors_entry (normalization i) denominator 32 r.z
    (CertifiedLocalCandidates.coefficientNumerators.getD i.val []) he n hn
  have hr : |(normalization i:ℝ)*(r.z.getD n 0:ℝ)*100000000-
      (CertifiedLocalCandidates.at i.val n:ℝ)*denominator|≤ 10*(denominator:ℝ) := by
    exact_mod_cast h
  have hD : (0:ℝ)< denominator := by exact_mod_cast denominator_pos
  rw [checked_coefficient i r hc n hn,moments_eq,parameter_center] at hr
  have hscale :
      (normalization i:ℝ)*((denominator:ℝ)*localGlobalCoefficient
        CertifiedGlobalMomentEnclosure.candidateMoment (CertifiedLocalXi.slabCenter i) n)*100000000-
          (CertifiedLocalCandidates.at i.val n:ℝ)*denominator =
      ((normalization i:ℝ)*localGlobalCoefficient CertifiedGlobalMomentEnclosure.candidateMoment
        (CertifiedLocalXi.slabCenter i) n-(CertifiedLocalCandidates.at i.val n:ℝ)/100000000)*
        (100000000*(denominator:ℝ)) := by ring
  rw [hscale,abs_mul,abs_of_pos (mul_pos (by norm_num) hD)] at hr
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<100000000) hD)).mpr at hr
  calc
    _ ≤  10*(denominator:ℝ)/(100000000*(denominator:ℝ)) := hr
    _ = 1/10^7 := by field_simp [hD.ne']; norm_num

end CertifiedGlobalTranslation

end Height100Module90

/- Source module: PackedTranslationSound. -/
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

lemma weight_length : weights.length=513 := by
  rw [weights_checked]
  simp only [weightFormula,List.length_map,List.length_zipIdx,shifted_length]

lemma weight_identity (j : ℕ) (_hj : j<513) :
    (weights.getD j 0:ℝ)*(commonFactor:ℝ)=(shifted.getD j 0:ℝ)*(j.factorial:ℝ) := by
  have h := congrArg (fun xs : List ℤ => xs.getD j 0) weights_reconstruct
  have hm := List.getD_map weights (0:ℤ) (fun x : ℤ => x*(commonFactor:ℤ)) (n:=j)
  simp only [zero_mul] at hm
  rw [hm] at h
  rw [←List.mapIdx_eq_zipIdx_map (l:=shifted) (f:=fun j (x : ℤ) => x*(j.factorial:ℤ))] at h
  rw [getD_mapIdx_zero _ _ (by intro k; simp) j] at h
  exact_mod_cast h

lemma window_digit (a b n : ℕ) (hn : n<32) :
    digit bits (productWindow a b) n=digit bits (a*b) (481+n) := by
  unfold productWindow
  rw [Nat.shiftLeft_eq,one_mul,Nat.and_two_pow_sub_one_eq_mod,
    digit_truncate bits _ 32 n hn]
  exact digit_shift_by bits (a*b) 481 n

lemma conditions (i : Fin 86) (r : Record) (hc : checkRecord i r=true) :
    CertifiedPackedExponentialSequence.checkPacked bits (parameter i) 512 digitBound r.ep=true ∧
    r.wp=productWindow encodedPlus r.ep ∧ r.wm=productWindow encodedMinus r.ep ∧
    r.z=(extract bits 1 32 r.wp r.wm).reverse ∧
    checkErrors (normalization i) 0 1 32 r.z
      (CertifiedLocalCandidates.coefficientNumerators.getD i.val [])=true := by
  simpa only [checkRecord,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc

noncomputable def sequence (r : Record) : List ℕ := decode bits 513 r.ep

lemma sequence_length (r : Record) : (sequence r).length=513 := decode_length _ _ _

lemma sequence_real (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (j : ℕ) (hj : j<513) :
    ((sequence r).getD j 0:ℝ)/((512).factorial:ℝ)=
      (parameter i:ℝ)^j/(j.factorial:ℝ) := by
  have hp := (conditions i r hc).1
  rw [sequence,decode_getD bits 513 r.ep j hj,
    packed_coefficient bits (parameter i) 512 digitBound r.ep hp j (by omega)]
  have hd := Nat.factorial_dvd_factorial (show j≤ 512 by omega)
  have hK : ((512).factorial:ℝ)≠0 := by exact_mod_cast (512).factorial_ne_zero
  have hjF : (j.factorial:ℝ)≠0 := by exact_mod_cast j.factorial_ne_zero
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_div hd hjF]
  field_simp

lemma sequence_encode (i : Fin 86) (r : Record) (hc : checkRecord i r=true) :
    r.ep=encode bits (sequence r) :=
  packed_encode bits (parameter i) 512 digitBound r.ep (conditions i r hc).1

lemma sequence_carry_plus (i : Fin 86) (r : Record) (hc : checkRecord i r=true) :
    (positiveList weights).reverse.sum*(sequence r).sum<2^bits := by
  have he := packed_sum_bound bits (parameter i) 512 digitBound r.ep (conditions i r hc).1
  rw [List.sum_reverse]
  have hm := Nat.mul_le_mul_left (positiveList weights).sum he
  have hg := global_carry_plus
  rw [Nat.shiftLeft_eq] at hg
  exact hm.trans_lt (by simpa only [sequence,bits,Nat.reduceAdd,mul_assoc,one_mul] using hg)

lemma sequence_carry_minus (i : Fin 86) (r : Record) (hc : checkRecord i r=true) :
    (negativeList weights).reverse.sum*(sequence r).sum<2^bits := by
  have he := packed_sum_bound bits (parameter i) 512 digitBound r.ep (conditions i r hc).1
  rw [List.sum_reverse]
  have hm := Nat.mul_le_mul_left (negativeList weights).sum he
  have hg := global_carry_minus
  rw [Nat.shiftLeft_eq] at hg
  exact hm.trans_lt (by simpa only [sequence,bits,Nat.reduceAdd,mul_assoc,one_mul] using hg)

lemma checked_correlation (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (n : ℕ) (hn : n<32) :
    (r.z.getD n 0:ℝ)=CertifiedTranslationAlgebra.correlation 513 weights (sequence r) n := by
  obtain ⟨_hs,hp,hm,hz,_he⟩ := conditions i r hc
  rw [hz,List.getD_reverse n (by rw [extract_length]; exact hn)]
  simp only [extract_length]
  rw [extract_getD bits 1 32 _ _ (32-1-n) (by omega),hp,hm]
  simp only [one_mul]
  rw [window_digit _ _ _ (by omega),window_digit _ _ _ (by omega)]
  have hindex : 481+(32-1-n)=513-1-n := by omega
  rw [hindex,encodedPlus_checked,encodedMinus_checked,sequence_encode i r hc]
  rw [packed_tail bits 513 (positiveList weights) (sequence r)
      (by simp only [positiveList,List.length_map,weight_length]) n (by omega) (sequence_carry_plus i r hc),
    packed_tail bits 513 (negativeList weights) (sequence r)
      (by simp only [negativeList,List.length_map,weight_length]) n (by omega) (sequence_carry_minus i r hc)]
  unfold CertifiedTranslationAlgebra.correlation
  push_cast
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro l hl
  rw [positiveList_getD,negativeList_getD,←sub_mul]
  have he : ((weights.getD (n+l) 0).toNat:ℝ)-((-(weights.getD (n+l) 0)).toNat:ℝ)=
      (weights.getD (n+l) 0:ℝ) := by exact_mod_cast Int.toNat_sub_toNat_neg _
  rw [he]

lemma checked_coefficient (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (n : ℕ) (hn : n<32) :
    (2:ℝ)^n*(commonFactor:ℝ)*(r.z.getD n 0:ℝ)=
      ((512).factorial:ℝ)*(n.factorial:ℝ)*(CertifiedGlobalTranslation.denominator:ℝ)*
        CertifiedPolynomialTranslation.localGlobalCoefficient CertifiedGlobalMomentEnclosure.candidateMoment
          (CertifiedLocalXi.slabCenter i) n := by
  rw [checked_correlation i r hc n hn]
  have h := factorial_correlation 512 (parameter i) 2 n shifted weights (sequence r) commonFactor
    shifted_length (by omega) weight_identity (sequence_real i r hc)
  unfold signedTranslated at h
  rw [CertifiedGlobalTranslation.translated_value,moments_eq,parameter_center] at h
  simpa only [mul_assoc,Nat.cast_ofNat,Nat.reduceAdd] using h

end CertifiedPackedTranslation

end Height100Module91

/- Source module: PackedTranslationErrors. -/
section Height100Module92

namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation CertifiedPolynomialTranslation

lemma checkErrors_getD (ν j N : ℕ) (zs cs : List ℤ)
    (h : checkErrors ν j j.factorial N zs cs=true) (k : ℕ) (hk : k< N) :
    |(ν:ℤ)*(Nat.shiftLeft 1 (j+k):ℕ)*commonFactor*zs.getD k 0*100000000-
      cs.getD k 0*scaleDenominator*(j+k).factorial|≤ 
        10*(scaleDenominator:ℤ)*(j+k).factorial := by
  induction N generalizing j zs cs k with
  | zero => omega
  | succ N ih =>
    cases zs with
    | nil => simp [checkErrors] at h
    | cons z zs =>
      have hf : j.factorial*(j+1)=(j+1).factorial := by rw [Nat.factorial_succ]; ring
      cases cs with
      | nil =>
        have hh := Bool.and_eq_true_iff.mp h
        rw [hf] at hh
        cases k with
        | zero => simpa only [Nat.add_zero,List.getD_cons_zero,List.getD_nil,zero_mul,sub_zero] using of_decide_eq_true hh.1
        | succ k =>
          have hi := ih (j+1) zs [] hh.2 k (by omega)
          simpa only [List.getD_cons_succ,List.getD_nil,Nat.succ_eq_add_one,
            add_assoc,add_comm,add_left_comm] using hi
      | cons c cs =>
        have hh := Bool.and_eq_true_iff.mp h
        rw [hf] at hh
        cases k with
        | zero => simpa only [Nat.add_zero,List.getD_cons_zero,List.getD_nil,zero_mul,sub_zero] using of_decide_eq_true hh.1
        | succ k =>
          have hi := ih (j+1) zs cs hh.2 k (by omega)
          simpa only [List.getD_cons_succ,Nat.succ_eq_add_one,
            add_assoc,add_comm,add_left_comm] using hi

lemma scaled_error_bound (ν A Z C D F L : ℝ) (hD : 0< D) (hF : 0< F)
    (he : A*Z=D*F*L)
    (h : |ν*A*Z*100000000-C*D*F|≤ 10*D*F) :
    |ν*L-C/100000000|≤ 1/10^7 := by
  have hscale : ν*A*Z*100000000-C*D*F=
      (ν*L-C/100000000)*(100000000*D*F) := by
    linear_combination (ν*100000000)*he
  have hp : (0:ℝ)<100000000*D*F := by positivity
  rw [hscale,abs_mul,abs_of_pos hp] at h
  apply (le_div_iff₀ (by positivity : (0:ℝ)<100000000*D*F)).mpr at h
  calc
    _ ≤  (10*D*F)/(100000000*D*F) := h
    _ = _ := by field_simp; norm_num

lemma checked_translation (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (n : ℕ) (hn : n<32) :
    |(normalization i:ℝ)*
      localGlobalCoefficient CertifiedGlobalMomentEnclosure.candidateMoment
        (CertifiedLocalXi.slabCenter i) n-
      (CertifiedLocalCandidates.at i.val n:ℝ)/100000000|≤ 1/10^7 := by
  obtain ⟨_hs,_hp,_hm,_hz,he⟩ := conditions i r hc
  have he' : checkErrors (normalization i) 0 (0).factorial 32 r.z
      (CertifiedLocalCandidates.coefficientNumerators.getD i.val [])=true := he
  have h := checkErrors_getD (normalization i) 0 32 r.z
    (CertifiedLocalCandidates.coefficientNumerators.getD i.val []) he' n hn
  simp only [zero_add,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul] at h
  have hr : |(normalization i:ℝ)*(2:ℝ)^n*(commonFactor:ℝ)*(r.z.getD n 0:ℝ)*100000000-
      (CertifiedLocalCandidates.at i.val n:ℝ)*(scaleDenominator:ℝ)*(n.factorial:ℝ)|≤ 
      10*(scaleDenominator:ℝ)*(n.factorial:ℝ) := by exact_mod_cast h
  have hD : (0:ℝ)< scaleDenominator := by
    unfold scaleDenominator
    push_cast
    exact mul_pos (by exact_mod_cast CertifiedGlobalTranslation.denominator_pos)
      (by exact_mod_cast Nat.factorial_pos 512)
  have hF : (0:ℝ)< n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hcoef := checked_coefficient i r hc n hn
  have hcoef' : ((2:ℝ)^n*(commonFactor:ℝ))*(r.z.getD n 0:ℝ)=
      (scaleDenominator:ℝ)*(n.factorial:ℝ)*
        localGlobalCoefficient CertifiedGlobalMomentEnclosure.candidateMoment
          (CertifiedLocalXi.slabCenter i) n := by
    rw [hcoef]
    unfold scaleDenominator
    push_cast
    ring
  apply scaled_error_bound (normalization i) ((2:ℝ)^n*(commonFactor:ℝ))
    (r.z.getD n 0) (CertifiedLocalCandidates.at i.val n) scaleDenominator n.factorial
    (localGlobalCoefficient CertifiedGlobalMomentEnclosure.candidateMoment
      (CertifiedLocalXi.slabCenter i) n) hD hF hcoef'
  convert! hr using 1
  ring

end CertifiedPackedTranslation

end Height100Module92

/- Source module: LiteralTranslationSound. -/
section Height100Module93

set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction

lemma checkRecord_sound (i : Fin 86) (r : Record) (hc : checkRecord i r=true) :
    CertifiedPackedTranslation.checkRecord i (toOriginal r)=true := by
  have h : r.e.length=513 ∧ r.e.headD 0=(512).factorial ∧
      CertifiedExponentialSequenceCheck.checkSteps (parameter i) 0 r.e=true ∧
      CertifiedChunkedEncoding.checkChunks bits 32 r.e r.chunks=true ∧
      r.wp=CertifiedPackedTranslation.productWindow encodedPlus (toOriginal r).ep ∧
      r.wm=CertifiedPackedTranslation.productWindow encodedMinus (toOriginal r).ep ∧
      r.z=(extract bits 1 32 r.wp r.wm).reverse ∧
      CertifiedPackedTranslation.checkErrors (normalization i) 0 1 32 r.z
        (CertifiedLocalCandidates.coefficientNumerators.getD i.val [])=true := by
    simpa only [checkRecord,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  have ha : parameter i≤ 199 := by unfold parameter; omega
  have hp := CertifiedExponentialSequenceBound.checked_original bits 32 (parameter i)
    (by decide : 4200< bits) ha r.e r.chunks h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hp' : CertifiedPackedExponentialSequence.checkPacked bits (parameter i) 512 digitBound
      (encode (bits*32) r.chunks)=true := by
    simpa only [digitBound,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul] using hp
  obtain ⟨hpp,hpm,hz,he⟩ := h.2.2.2.2
  unfold CertifiedPackedTranslation.checkRecord
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,he⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,decide_eq_true hz⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,decide_eq_true hpm⟩
  exact Bool.and_eq_true_iff.mpr ⟨hp',decide_eq_true hpp⟩

lemma checked_translation (i : Fin 86) (r : Record) (hc : checkRecord i r=true)
    (n : ℕ) (hn : n<32) :
    |(normalization i:ℝ)*
      CertifiedPolynomialTranslation.localGlobalCoefficient CertifiedGlobalMomentEnclosure.candidateMoment
        (CertifiedLocalXi.slabCenter i) n-
      (CertifiedLocalCandidates.at i.val n:ℝ)/100000000|≤ 1/10^7 :=
  CertifiedPackedTranslation.checked_translation i (toOriginal r) (checkRecord_sound i r hc) n hn
end CertifiedLiteralTranslation

end Height100Module93

/- Source module: BivariateAlgebra. -/
section Height100Module94

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaPoly

noncomputable abbrev Row := List ℚ
noncomputable abbrev Bi := List Row

noncomputable def rowAdd : Row → Row → Row
  | [],b => b
  | a,[] => a
  | a::as,b::bs => (a+b)::rowAdd as bs

noncomputable def biAdd : Bi → Bi → Bi
  | [],b => b
  | a,[] => a
  | a::as,b::bs => rowAdd a b::biAdd as bs

noncomputable def biScale (q : ℚ) (a : Bi) : Bi := a.map (fun r => r.map (q*·))
noncomputable def shiftX : Bi → Bi
  | [] => []
  | a::as => []::a::as
noncomputable def shiftY (a : Bi) : Bi := a.map (0::·)
noncomputable def biConst (q : ℚ) : Bi := [[q]]

noncomputable def rowEval (y : ℝ) : Row → ℝ
  | [] => 0
  | a::as => (a:ℝ)+y*rowEval y as
noncomputable def biEval (x y : ℝ) : Bi → ℝ
  | [] => 0
  | a::as => rowEval y a+x*biEval x y as

lemma rowEval_add (y : ℝ) (a b : Row) : rowEval y (rowAdd a b)=rowEval y a+rowEval y b := by
  induction a generalizing b with
  | nil => simp [rowAdd,rowEval]
  | cons a as ih => cases b <;> simp [rowAdd,rowEval,ih] <;> ring
lemma biEval_add (x y : ℝ) (a b : Bi) : biEval x y (biAdd a b)=biEval x y a+biEval x y b := by
  induction a generalizing b with
  | nil => simp [biAdd,biEval]
  | cons a as ih => cases b <;> simp [biAdd,biEval,ih,rowEval_add] <;> ring
lemma rowEval_scale (y : ℝ) (q : ℚ) (a : Row) :
    rowEval y (a.map (q*·))=(q:ℝ)*rowEval y a := by
  induction a with
  | nil => simp [rowEval]
  | cons a as ih => simp [rowEval,ih]; ring
lemma biEval_scale (x y : ℝ) (q : ℚ) (a : Bi) :
    biEval x y (biScale q a)=(q:ℝ)*biEval x y a := by
  induction a with
  | nil => simp [biScale,biEval]
  | cons a as ih =>
    simp only [biScale,List.map_cons,biEval,rowEval_scale]
    change (q:ℝ)*rowEval y a+x*biEval x y (biScale q as)=_
    rw [ih]; ring
lemma biEval_shiftX (x y : ℝ) (a : Bi) : biEval x y (shiftX a)=x*biEval x y a := by
  cases a <;> simp [shiftX,biEval,rowEval]
lemma biEval_shiftY (x y : ℝ) (a : Bi) : biEval x y (shiftY a)=y*biEval x y a := by
  induction a with
  | nil => simp [shiftY,biEval]
  | cons a as ih =>
    simp only [shiftY,List.map_cons,biEval,rowEval,Rat.cast_zero,zero_add]
    change y*rowEval y a+x*biEval x y (shiftY as)=_
    rw [ih]; ring
lemma biEval_const (x y : ℝ) (q : ℚ) : biEval x y (biConst q)=(q:ℝ) := by
  simp [biConst,biEval,rowEval]

noncomputable def complexPair : List ℚ → Bi × Bi
  | [] => ([],[])
  | c::cs =>
    let p:=complexPair cs
    (biAdd (biConst c) (biAdd (shiftX p.1)
        (biAdd (biScale (-1) (shiftY p.1)) (biScale (-2) (shiftX (shiftY p.2))))),
     biAdd (biScale 2 p.1) (biAdd (shiftX p.2) (biScale (-1) (shiftY p.2))))

noncomputable def complexEval (z : ℂ) : List ℚ → ℂ
  | [] => 0
  | c::cs => (c:ℂ)+z^2*complexEval z cs

lemma rowEval_eq_sum (y : ℝ) (a : Row) (n : ℕ) (hlen : a.length ≤  n) :
    rowEval y a = ∑ j : Fin n, (a.getD j 0 : ℝ)*y^(j:ℕ) := by
  induction n generalizing a with
  | zero => have ha : a=[] := List.eq_nil_of_length_eq_zero (by omega)
            subst ha; simp [rowEval]
  | succ n ih =>
    cases a with
    | nil => simp [rowEval,List.getD]
    | cons a as =>
      rw [rowEval, Fin.sum_univ_succ]
      simp only [Fin.val_zero,List.getD_cons_zero,pow_zero,mul_one]
      rw [ih as (by simpa using hlen),Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_succ,List.getD_cons_succ,pow_succ]
      ring

lemma biEval_eq_sum_rows (x y : ℝ) (a : Bi) (n : ℕ) (hlen : a.length ≤  n) :
    biEval x y a = ∑ i : Fin n, rowEval y (a.getD i [])*x^(i:ℕ) := by
  induction n generalizing a with
  | zero => have ha : a=[] := List.eq_nil_of_length_eq_zero (by omega)
            subst ha; simp [biEval]
  | succ n ih =>
    cases a with
    | nil => simp [biEval,List.getD,rowEval]
    | cons a as =>
      rw [biEval, Fin.sum_univ_succ]
      simp only [Fin.val_zero,List.getD_cons_zero,pow_zero,mul_one]
      rw [ih as (by simpa using hlen),Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ,List.getD_cons_succ,pow_succ]
      ring

lemma biEval_eq_sum (x y : ℝ) (a : Bi) (n m : ℕ) (hlen : a.length ≤  n)
    (hrows : ∀ i : Fin n, (a.getD i []).length ≤  m) :
    biEval x y a = ∑ i : Fin n, ∑ j : Fin m,
      ((a.getD i []).getD j 0 : ℝ)*x^(i:ℕ)*y^(j:ℕ) := by
  rw [biEval_eq_sum_rows x y a n hlen]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowEval_eq_sum y _ m (hrows i),Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end TaoZetaPoly

end Height100Module94

/- Source module: LocalPolynomialPair. -/
section Height100Module95

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset CertifiedLocalXi

noncomputable def linearPair : List ℚ → Bi × Bi
  | [] => ([],[])
  | c::cs =>
    let p := linearPair cs
    (biAdd (biConst c) (biAdd (shiftY p.1) (biScale (-1) (shiftX p.2))),
      biAdd p.1 (shiftY p.2))

noncomputable def linearEval (z : ℂ) : List ℚ → ℂ
  | [] => 0
  | c::cs => (c:ℂ)+z*linearEval z cs

lemma linearEval_eq_sum (cs : List ℚ) (N : ℕ) (hlen : cs.length≤ N) (z : ℂ) :
    linearEval z cs=∑ n ∈ range N, (cs.getD n 0:ℂ)*z^n := by
  induction N generalizing cs with
  | zero =>
    have hc : cs=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst hc
    simp [linearEval]
  | succ N ih =>
    cases cs with
    | nil => simp [linearEval]
    | cons c cs =>
      rw [linearEval,sum_range_succ']
      simp only [List.getD_cons_zero,pow_zero,mul_one,List.getD_cons_succ]
      rw [ih cs (by simpa using hlen),mul_sum,add_comm]
      congr 1
      apply sum_congr rfl
      intro n hn
      rw [pow_succ]
      ring

lemma rotatedVariable_cartesian (T : ℝ) (z : ℂ) :
    rotatedVariable T z=((z.im-T:ℝ):ℂ)-((z.re-1/2:ℝ):ℂ)*I := by
  apply Complex.ext <;> simp [rotatedVariable,center,mul_re,mul_im]

lemma rotatedPolynomial_list (cs : List ℚ) (hlen : cs.length≤ 32) (T : ℝ) (z : ℂ) :
    rotatedPolynomial (fun n => (cs.getD n 0:ℝ)) T z=linearEval (rotatedVariable T z) cs := by
  rw [linearEval_eq_sum cs 32 hlen]
  unfold rotatedPolynomial
  simp only [Complex.ofReal_ratCast]

end CertifiedLocalPolynomial

end Height100Module95

/- Source module: IntegerLocalPolynomial. -/
section Height100Module96

namespace CertifiedIntegerLocalPolynomial
open Complex Finset

noncomputable def rowEval (y : ℝ) : Row → ℝ
  | [] => 0
  | a::as => (a:ℝ)+y*rowEval y as
noncomputable def biEval (x y : ℝ) : Bi → ℝ
  | [] => 0
  | a::as => rowEval y a+x*biEval x y as

lemma rowEval_add (y : ℝ) (a b : Row) : rowEval y (rowAdd a b)=rowEval y a+rowEval y b := by
  induction a generalizing b with
  | nil => simp [rowAdd,rowEval]
  | cons a as ih => cases b <;> simp [rowAdd,rowEval,ih]; ring
lemma biEval_add (x y : ℝ) (a b : Bi) : biEval x y (biAdd a b)=biEval x y a+biEval x y b := by
  induction a generalizing b with
  | nil => simp [biAdd,biEval]
  | cons a as ih => cases b <;> simp [biAdd,biEval,ih,rowEval_add]; ring
lemma rowEval_scale (y : ℝ) (q : ℤ) (a : Row) :
    rowEval y (a.map (q*·))=(q:ℝ)*rowEval y a := by
  induction a with
  | nil => simp [rowEval]
  | cons a as ih => simp [rowEval,ih]; ring
lemma biEval_scale (x y : ℝ) (q : ℤ) (a : Bi) :
    biEval x y (biScale q a)=(q:ℝ)*biEval x y a := by
  induction a with
  | nil => simp [biScale,biEval]
  | cons a as ih =>
    simp only [biScale,List.map_cons,biEval,rowEval_scale]
    change (q:ℝ)*rowEval y a+x*biEval x y (biScale q as)=_
    rw [ih]
    ring
lemma biEval_shiftX (x y : ℝ) (a : Bi) : biEval x y (shiftX a)=x*biEval x y a := by
  cases a <;> simp [shiftX,biEval,rowEval]
lemma biEval_shiftY (x y : ℝ) (a : Bi) : biEval x y (shiftY a)=y*biEval x y a := by
  induction a with
  | nil => simp [shiftY,biEval]
  | cons a as ih =>
    simp only [shiftY,List.map_cons,biEval,rowEval,Int.cast_zero,zero_add]
    change y*rowEval y a+x*biEval x y (shiftY as)=_
    rw [ih]
    ring
lemma biEval_const (x y : ℝ) (q : ℤ) : biEval x y (biConst q)=(q:ℝ) := by
  simp [biConst,biEval,rowEval]

noncomputable def complexEval (z : ℂ) : List ℤ → ℂ
  | [] => 0
  | c::cs => (c:ℂ)+z*complexEval z cs

lemma normalizedPair_sound (a b : ℤ) (cs : List ℤ) (x v : ℝ) :
    biEval (4*x^2) v (normalizedPair a b cs).1=
      (4:ℝ)^cs.length*(complexEval ((((a:ℝ)+(b:ℝ)*v)/2:ℝ)-(x:ℂ)*I) cs).re ∧
    -x*biEval (4*x^2) v (normalizedPair a b cs).2=
      (4:ℝ)^cs.length*(complexEval ((((a:ℝ)+(b:ℝ)*v)/2:ℝ)-(x:ℂ)*I) cs).im := by
  induction cs with
  | nil => simp [normalizedPair,biEval,complexEval]
  | cons c cs ih =>
    simp only [normalizedPair,biEval_add,biEval_const,biEval_scale,biEval_shiftX,
      biEval_shiftY,complexEval,List.length_cons,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.intCast_re,Complex.intCast_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,add_zero,zero_add,sub_zero,zero_sub,
      Int.cast_mul,Int.cast_ofNat,Int.cast_pow,Int.cast_neg,Int.cast_one,pow_succ] at *
    constructor
    · linear_combination (2*(a:ℝ)+2*(b:ℝ)*v)*ih.1+4*x*ih.2
    · linear_combination (-4*x)*ih.1+(2*(a:ℝ)+2*(b:ℝ)*v)*ih.2

lemma complexEval_scaled (cs : List ℤ) (z : ℂ) :
    CertifiedLocalPolynomial.linearEval z (cs.map (fun c : ℤ => (c:ℚ)/100000000))=
      complexEval z cs/100000000 := by
  induction cs with
  | nil => simp [CertifiedLocalPolynomial.linearEval,complexEval]
  | cons c cs ih =>
    simp only [List.map_cons,CertifiedLocalPolynomial.linearEval,complexEval,ih,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
    ring

lemma normalizedPair_candidate (a b : ℤ) (cs : List ℤ) (x v : ℝ) :
    let w : ℂ := ((((a:ℝ)+(b:ℝ)*v)/2:ℝ):ℂ)-(x:ℂ)*I
    let P := CertifiedLocalPolynomial.linearEval w (cs.map (fun c : ℤ => (c:ℚ)/100000000))
    P.re=biEval (4*x^2) v (normalizedPair a b cs).1/(100000000*(4:ℝ)^cs.length) ∧
    P.im= -x*biEval (4*x^2) v (normalizedPair a b cs).2/(100000000*(4:ℝ)^cs.length) := by
  dsimp
  rw [complexEval_scaled]
  have h := normalizedPair_sound a b cs x v
  have hd : (4:ℝ)^cs.length≠0 := by positivity
  simp only [Complex.div_ofNat_re,Complex.div_ofNat_im]
  constructor
  · rw [h.1]
    field_simp
  · rw [h.2]
    field_simp

lemma rowEval_eq_sum (y : ℝ) (a : Row) (n : ℕ) (hlen : a.length ≤  n) :
    rowEval y a = ∑ j : Fin n, (a.getD j 0 : ℝ)*y^(j:ℕ) := by
  induction n generalizing a with
  | zero => have ha : a=[] := List.eq_nil_of_length_eq_zero (by omega)
            subst ha; simp [rowEval]
  | succ n ih =>
    cases a with
    | nil => simp [rowEval,List.getD]
    | cons a as =>
      rw [rowEval, Fin.sum_univ_succ]
      simp only [Fin.val_zero,List.getD_cons_zero,pow_zero,mul_one]
      rw [ih as (by simpa using hlen),Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_succ,List.getD_cons_succ,pow_succ]
      ring

lemma biEval_eq_sum_rows (x y : ℝ) (a : Bi) (n : ℕ) (hlen : a.length ≤  n) :
    biEval x y a = ∑ i : Fin n, rowEval y (a.getD i [])*x^(i:ℕ) := by
  induction n generalizing a with
  | zero => have ha : a=[] := List.eq_nil_of_length_eq_zero (by omega)
            subst ha; simp [biEval]
  | succ n ih =>
    cases a with
    | nil => simp [biEval,List.getD,rowEval]
    | cons a as =>
      rw [biEval, Fin.sum_univ_succ]
      simp only [Fin.val_zero,List.getD_cons_zero,pow_zero,mul_one]
      rw [ih as (by simpa using hlen),Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ,List.getD_cons_succ,pow_succ]
      ring

lemma biEval_eq_sum (x y : ℝ) (a : Bi) (n m : ℕ) (hlen : a.length ≤  n)
    (hrows : ∀ i : Fin n, (a.getD i []).length ≤  m) :
    biEval x y a = ∑ i : Fin n, ∑ j : Fin m,
      ((a.getD i []).getD j 0 : ℝ)*x^(i:ℕ)*y^(j:ℕ) := by
  rw [biEval_eq_sum_rows x y a n hlen]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowEval_eq_sum y _ m (hrows i),Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end CertifiedIntegerLocalPolynomial

end Height100Module96

/- Source module: BernsteinCertificate. -/
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

/- Source module: BernsteinConversion. -/
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

/- Source module: LocalPolynomialRectangles. -/
section Height100Module99

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset TaoZetaNumerics
open scoped unitInterval

noncomputable def rowAffine (a b : ℚ) : Row → Row
  | [] => []
  | c::cs =>
    let r := rowAffine a b cs
    rowAdd [c] (rowAdd (r.map (a*·)) (0::r.map (b*·)))

noncomputable def biAffine (sx a b : ℚ) : Bi → Bi
  | [] => []
  | r::rs => biAdd [rowAffine a b r] (biScale sx (shiftX (biAffine sx a b rs)))

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

/- Source module: LocalRectangleSound. -/
section Height100Module100

namespace CertifiedLocalPolynomial
open TaoZetaPoly Complex Finset CertifiedLocalXi
open scoped unitInterval

noncomputable def selectedPair (imaginary : Bool) (cs : List ℚ) : Bi :=
  if imaginary then (linearPair cs).2 else (linearPair cs).1

end CertifiedLocalPolynomial

end Height100Module100

/- Source module: IntegerBernstein. -/
section Height100Module101

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0
namespace TaoZetaNumerics

noncomputable def factorialWeight (n : ℕ) (i j : Fin (n+1)) : ℕ :=
  chooseFast i j * (j:ℕ).factorial * (n-j).factorial

noncomputable def integerBernstein (n : ℕ) (a : Fin (n+1) → ℤ) (i : Fin (n+1)) : ℤ :=
  ∑ j : Fin (n+1), a j * factorialWeight n i j

lemma factorialWeight_ratio (n : ℕ) (i j : Fin (n+1)) :
    (factorialWeight n i j : ℚ)/(n.factorial:ℚ) =
      (chooseFast i j : ℚ)/(chooseFast n j:ℚ) := by
  have hc : (chooseFast n j:ℚ)*(j.val.factorial:ℚ)*((n-j).factorial:ℚ) = n.factorial := by
    rw [chooseFast_eq]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ j.isLt)
  have hn : (n.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hd : (chooseFast n j:ℚ)≠0 := by
    rw [chooseFast_eq]
    exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt_succ j.isLt)
  simp only [factorialWeight,Nat.cast_mul]
  apply (div_eq_div_iff hn hd).mpr
  rw [←hc]
  ring

lemma integerBernstein_correct (n : ℕ) (a : Fin (n+1) → ℚ)
    (A : Fin (n+1) → ℤ) (D : ℕ) (h : ∀ j, a j = (A j:ℚ)/D) (i : Fin (n+1)) :
    bernsteinTransform n a i = (integerBernstein n A i:ℚ)/((D:ℚ)*n.factorial) := by
  simp only [bernsteinTransform,integerBernstein,Int.cast_sum,Int.cast_mul,Int.cast_natCast,
    Finset.sum_div]
  apply sum_congr rfl
  intro j _
  rw [h j]
  have hw := factorialWeight_ratio n i j
  calc
    (A j:ℚ)/D*chooseFast i j/chooseFast n j =
        (A j:ℚ)/D*((chooseFast i j:ℚ)/chooseFast n j) := by ring
    _ = (A j:ℚ)/D*((factorialWeight n i j:ℚ)/n.factorial) := by rw [hw]
    _ = _ := by ring

end TaoZetaNumerics

end Height100Module101

/- Source module: LocalBoxData. -/
section Height100Module102

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial TaoZetaPoly TaoZetaNumerics
open Finset
open scoped unitInterval

noncomputable def candidate (i : Fin 86) : List ℚ :=
  (coefficientNumerators.getD i.val []).map (fun x : ℤ => (x:ℚ)/100000000)
noncomputable def Spec.a (s : Spec) : ℚ := (s.a2:ℚ)/2
noncomputable def Spec.b (s : Spec) : ℚ := (s.b2:ℚ)/2

noncomputable def boxPower (i : Fin 86) (j : ℕ) : Bi :=
  let s := specAt i j
  biAffine (1/4) s.a (s.b-s.a) (biScale s.sign (selectedPair s.imaginary (candidate i)))

noncomputable def denominator : ℕ := 53687091200000000

noncomputable def matrixAt (a : List (List ℤ)) (i j : ℕ) : ℤ := (a.getD i []).getD j 0

noncomputable def makeCertificate (i : Fin 86) (j : ℕ) : Certificate := Id.run do
  let q := boxPower i j
  let p := List.ofFn (fun u : Fin 8 => List.ofFn (fun v : Fin 16 =>
    let x := (q.getD u.val []).getD v.val 0
    x.num*(denominator:ℤ)/(x.den:ℤ)))
  let row := List.ofFn (fun u : Fin 8 => List.ofFn (fun v : Fin 16 =>
    integerBernstein 15 (fun k => matrixAt p u.val k.val) v))
  let result := List.ofFn (fun u : Fin 8 => List.ofFn (fun v : Fin 16 =>
    integerBernstein 7 (fun k => matrixAt row k.val v.val) u))
  return ⟨p,row,result⟩

noncomputable def valid (i : Fin 86) (j : ℕ) (c : Certificate) : Prop :=
  let q := boxPower i j
  q.length≤ 8 ∧ (∀ u : Fin 8, (q.getD u.val []).length≤ 16) ∧
  (∀ u : Fin 8, ∀ v : Fin 16,
    ((q.getD u.val []).getD v.val 0).num*(denominator:ℤ)=
      matrixAt c.power u.val v.val*((q.getD u.val []).getD v.val 0).den) ∧
  (∀ u : Fin 8, ∀ v : Fin 16,
    matrixAt c.row u.val v.val=integerBernstein 15 (fun k => matrixAt c.power u.val k.val) v) ∧
  (∀ u : Fin 8, ∀ v : Fin 16,
    matrixAt c.result u.val v.val=integerBernstein 7 (fun k => matrixAt c.row k.val v.val) u) ∧
  (∀ u : Fin 8, ∀ v : Fin 16,
    (denominator*Nat.factorial 15*Nat.factorial 7:ℕ)≤ matrixAt c.result u.val v.val)

noncomputable instance (i : Fin 86) (j : ℕ) (c : Certificate) : Decidable (valid i j c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end CertifiedLocalBoxes

end Height100Module102

/- Source module: FastLocalBoxData. -/
section Height100Module103

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

noncomputable def denominator : ℕ := 100000000*4^16

noncomputable def makeCertificate (i : Fin 86) (j : ℕ) : Certificate := Id.run do
  let p := powerMatrix i j
  let row := List.ofFn (fun u : Fin 8 => List.ofFn (fun v : Fin 16 =>
    integerBernstein 15 (fun k => matrixAt p u.val k.val) v))
  let result := List.ofFn (fun u : Fin 8 => List.ofFn (fun v : Fin 16 =>
    integerBernstein 7 (fun k => matrixAt row k.val v.val) u))
  return ⟨p,row,result⟩

noncomputable def valid (i : Fin 86) (j : ℕ) (c : Certificate) : Prop :=
  c.power=powerMatrix i j ∧ c.power.length≤ 8 ∧
  (∀ u : Fin 8, (c.power.getD u.val []).length≤ 16) ∧
  (∀ u : Fin 8, ∀ v : Fin 16,
    matrixAt c.row u.val v.val=integerBernstein 15 (fun k => matrixAt c.power u.val k.val) v) ∧
  (∀ u : Fin 8, ∀ v : Fin 16,
    matrixAt c.result u.val v.val=integerBernstein 7 (fun k => matrixAt c.row k.val v.val) u) ∧
  (∀ u : Fin 8, ∀ v : Fin 16,
    (denominator*Nat.factorial 15*Nat.factorial 7:ℕ)≤ matrixAt c.result u.val v.val)

noncomputable instance (i : Fin 86) (j : ℕ) (c : Certificate) : Decidable (valid i j c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end CertifiedFastLocalBoxes

end Height100Module103

/- Source module: StreamingBernstein. -/
section Height100Module104

namespace CertifiedStreamingBernstein
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

lemma dot_eq_sum (xs : List ℤ) (ws : List ℕ) :
    dot xs ws=∑ k ∈ range ws.length, xs.getD k 0*(ws.getD k 0:ℤ) := by
  induction ws generalizing xs with
  | nil => cases xs <;> simp [dot]
  | cons w ws ih =>
    cases xs with
    | nil => simp [dot]
    | cons x xs =>
      rw [dot,List.length_cons,sum_range_succ']
      simp only [List.getD_cons_succ,List.getD_cons_zero]
      rw [ih,add_comm]

lemma rowAdd_getD (a b : Row) (k : ℕ) :
    (rowAdd a b).getD k 0=a.getD k 0+b.getD k 0 := by
  induction a generalizing b k with
  | nil => simp [rowAdd]
  | cons a as ih =>
    cases b with
    | nil => simp [rowAdd]
    | cons b bs =>
      cases k with
      | zero => rfl
      | succ k => exact ih bs k

lemma weightedRows_getD (ws : List ℕ) (rows : List (List ℤ)) (v : ℕ) :
    (weightedRows ws rows).getD v 0=
      ∑ k ∈ range ws.length, matrixAt rows k v*(ws.getD k 0:ℤ) := by
  induction ws generalizing rows with
  | nil => simp [weightedRows]
  | cons w ws ih =>
    cases rows with
    | nil => simp [weightedRows,matrixAt]
    | cons r rs =>
      rw [weightedRows,rowAdd_getD,List.length_cons,sum_range_succ']
      have hm : (r.map (fun x => x*(w:ℤ))).getD v 0=r.getD v 0*(w:ℤ) := by
        simpa using List.getD_map r 0 (fun x : ℤ => x*(w:ℤ)) (n:=v)
      rw [hm,ih]
      simp only [matrixAt,List.getD_cons_succ,List.getD_cons_zero]
      rw [add_comm]

noncomputable def weights (n : ℕ) : List (List ℕ) :=
  List.ofFn (fun i : Fin (n+1) => List.ofFn (fun j : Fin (n+1) => factorialWeight n i j))

lemma weights_length (n : ℕ) : (weights n).length=n+1 := by simp [weights]
lemma weights_row_length (n : ℕ) (i : Fin (n+1)) :
    ((weights n).getD i.val []).length=n+1 := by
  simp only [weights,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,
    Option.getD_some,List.length_ofFn]
lemma weights_entry (n : ℕ) (i j : Fin (n+1)) :
    ((weights n).getD i.val []).getD j.val 0=factorialWeight n i j := by
  simp only [weights,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,
    dif_pos j.isLt,Option.getD_some]

lemma getD_map_of_lt {α β : Type*} (f : α → β) (xs : List α) (da : α) (db : β)
    (k : ℕ) (hk : k< xs.length) : (xs.map f).getD k db=f (xs.getD k da) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hk,
    Option.map_some,Option.getD_some]

lemma transformRow_getD (n : ℕ) (r : List ℤ) (i : Fin (n+1)) :
    (transformRow (weights n) r).getD i.val 0=
      integerBernstein n (fun j => r.getD j.val 0) i := by
  rw [transformRow,getD_map_of_lt _ _ [] 0 _ (by simpa [weights_length] using i.isLt)]
  rw [dot_eq_sum,weights_row_length,Finset.sum_range]
  unfold integerBernstein
  apply sum_congr rfl
  intro j _
  rw [weights_entry]

lemma transformRows_getD (n : ℕ) (rows : List (List ℤ)) (u : ℕ) (hu : u< rows.length)
    (v : Fin (n+1)) :
    matrixAt (transformRows (weights n) rows) u v.val=
      integerBernstein n (fun j => matrixAt rows u j.val) v := by
  unfold transformRows matrixAt
  rw [getD_map_of_lt _ _ [] [] _ hu,transformRow_getD]

lemma transformColumns_getD (n : ℕ) (rows : List (List ℤ)) (u : Fin (n+1)) (v : ℕ) :
    matrixAt (transformColumns (weights n) rows) u.val v=
      integerBernstein n (fun j => matrixAt rows j.val v) u := by
  unfold transformColumns matrixAt
  rw [getD_map_of_lt _ _ [] [] _ (by simpa [weights_length] using u.isLt)]
  rw [weightedRows_getD,weights_row_length,Finset.sum_range]
  unfold integerBernstein
  apply sum_congr rfl
  intro j _
  rw [weights_entry]
  rfl

lemma all_getD_of_lt {α : Type*} (p : α → Bool) (xs : List α) (d : α)
    (h : xs.all p=true) (j : ℕ) (hj : j< xs.length) : p (xs.getD j d)=true := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    have hh := Bool.and_eq_true_iff.mp h
    cases j with
    | zero => exact hh.1
    | succ j => exact ih hh.2 j (by simpa using hj)

end CertifiedStreamingBernstein

end Height100Module104

/- Source module: StreamingLocalBoxData. -/
section Height100Module105

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein
open TaoZetaNumerics

theorem weights7_correct : weights7=weights 7 := by decide +kernel

theorem weights15_correct : weights15=weights 15 := by decide +kernel

theorem threshold_correct : threshold=(CertifiedFastLocalBoxes.denominator*Nat.factorial 15*Nat.factorial 7:ℕ) := by
  norm_num [threshold,CertifiedFastLocalBoxes.denominator]

noncomputable instance (i : Fin 86) (j : ℕ) (c : Certificate) : Decidable (valid i j c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

noncomputable def makeCertificate := CertifiedFastLocalBoxes.makeCertificate

end CertifiedStreamingLocalBoxes

end Height100Module105

/- Source module: FastLocalBoxSound. -/
section Height100Module106

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes
open CertifiedLocalPolynomial CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset
open scoped unitInterval

theorem valid_sound (i : Fin 86) (j : ℕ) (c : Certificate) (h : valid i j c) (x y : I) :
    1≤ biEval x y (powerMatrix i j)/(denominator:ℝ) := by
  obtain ⟨hpower,hlen,hrows,hrow,hcol,hpos⟩ := h
  let a : Fin 8 → Fin 16 → ℚ := fun u v => (matrixAt c.power u.val v.val:ℚ)/denominator
  let r : Fin 8 → Fin 16 → ℚ := fun u v =>
    (matrixAt c.row u.val v.val:ℚ)/(denominator*Nat.factorial 15:ℕ)
  let b : Fin 8 → Fin 16 → ℚ := fun u v =>
    (matrixAt c.result u.val v.val:ℚ)/(denominator*Nat.factorial 15*Nat.factorial 7:ℕ)
  have ha (u : Fin 8) (v : Fin 16) : a u v=(matrixAt c.power u.val v.val:ℚ)/denominator :=
    rfl
  have hr : ∀ u, r u=bernsteinTransform 15 (a u) := by
    intro u
    funext v
    have hh := integerBernstein_correct 15 (a u) (fun k => matrixAt c.power u.val k.val)
      denominator (ha u) v
    rw [←hrow u v] at hh
    simpa only [r,Nat.cast_mul] using hh.symm
  have hc : ∀ v, (fun u => b u v)=bernsteinTransform 7 (fun u => r u v) := by
    intro v
    funext u
    have hh := integerBernstein_correct 7 (fun k => r k v)
      (fun k => matrixAt c.row k.val v.val) (denominator*Nat.factorial 15) (by intro k; rfl) u
    rw [←hcol u v] at hh
    simpa only [b,Nat.cast_mul] using hh.symm
  have hbound : ∀ u v, (1:ℝ)≤ (b u v:ℝ) := by
    intro u v
    have hd : (0:ℝ)<(denominator*Nat.factorial 15*Nat.factorial 7:ℕ) := by
      norm_num [denominator]
    dsimp [b]
    push_cast
    apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
    have hh := hpos u v
    exact_mod_cast hh
  rw [←hpower,biEval_eq_sum (x:ℝ) (y:ℝ) c.power 8 16 hlen hrows]
  have he : (∑ u : Fin 8, ∑ v : Fin 16,
      (matrixAt c.power u.val v.val:ℝ)*(x:ℝ)^(u:ℕ)*(y:ℝ)^(v:ℕ))/(denominator:ℝ)=
      bivariatePowerValue 7 15 a x y := by
    unfold bivariatePowerValue
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    dsimp [a]
    push_cast
    ring
  change 1≤ (∑ u : Fin 8, ∑ v : Fin 16,
    (matrixAt c.power u.val v.val:ℝ)*(x:ℝ)^(u:ℕ)*(y:ℝ)^(v:ℕ))/(denominator:ℝ)
  rw [he]
  exact bivariate_bernstein_lower 7 15 a r b hr hc 1 hbound x y

end CertifiedFastLocalBoxes

end Height100Module106

/- Source module: LocalBoxCoverage. -/
section Height100Module107

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial CertifiedLocalXi

theorem candidate_length : ∀ i : Fin 86, (candidate i).length=16 := by decide +kernel

theorem specifications_valid : ∀ i : Fin 86, ∀ j : Fin 2,
    j.val<(rowSpecs i).length →
    |(specAt i j.val).sign|=1 ∧ (specAt i j.val).a2<(specAt i j.val).b2 := by decide +kernel

theorem row_shape : ∀ i : Fin 86,
    ((rowSpecs i).length=1 ∧ (specAt i 0).a2= -1 ∧ (specAt i 0).b2=1) ∨
    ((rowSpecs i).length=2 ∧ (specAt i 0).a2= -1 ∧ (specAt i 0).b2=0 ∧
      (specAt i 1).a2=0 ∧ (specAt i 1).b2=1) := by decide +kernel

lemma specifications_cover (i : Fin 86) (y : ℝ) (hy0 : -(1/2:ℝ)≤ y) (hy1 : y≤ 1/2) :
    ∃ j, j<(rowSpecs i).length ∧ ((specAt i j).a:ℝ)≤ y ∧ y≤ ((specAt i j).b:ℝ) := by
  rcases row_shape i with ⟨hlen,ha,hb⟩ | ⟨hlen,ha0,hb0,ha1,hb1⟩
  · refine ⟨0,by omega,?_,?_⟩
    · simpa [Spec.a,ha,neg_div] using hy0
    · simpa [Spec.b,hb] using hy1
  · by_cases hy : y≤ 0
    · refine ⟨0,by omega,?_,?_⟩
      · simpa [Spec.a,ha0,neg_div] using hy0
      · simpa [Spec.b,hb0] using hy
    · refine ⟨1,by omega,?_,?_⟩
      · have h : 0≤ y := le_of_lt (lt_of_not_ge hy)
        simpa [Spec.a,ha1] using h
      · simpa [Spec.b,hb1] using hy1

lemma candidate_coefficient (i : Fin 86) (j : ℕ) :
    (candidate i |>.getD j 0 : ℝ)=(CertifiedLocalCandidates.at i.val j:ℝ)/100000000 := by
  have h := List.getD_map (coefficientNumerators.getD i.val []) 0 (fun x : ℤ => (x:ℚ)/100000000)
    (n:=j)
  norm_num only [Int.cast_zero,zero_div] at h
  rw [candidate,h]
  unfold CertifiedLocalCandidates.at
  norm_cast

end CertifiedLocalBoxes

end Height100Module107

/- Source module: FastLocalBoxBridge. -/
section Height100Module108

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial CertifiedLocalPolynomial CertifiedLocalXi
open scoped unitInterval

theorem integer_candidate_length : ∀ i : Fin 86, (integerCandidate i).length=16 := by decide +kernel

lemma pair_at_point (i : Fin 86) (j : ℕ) (x v : ℝ) :
    let s := specAt i j
    let p := normalizedPair s.a2 (s.b2-s.a2) (integerCandidate i)
    let w : ℂ := (((s.a:ℝ)+((s.b:ℝ)-s.a)*v):ℝ)-(x:ℂ)*Complex.I
    let P := linearEval w (candidate i)
    P.re=biEval (4*x^2) v p.1/(denominator:ℝ) ∧
    P.im= -x*biEval (4*x^2) v p.2/(denominator:ℝ) := by
  have h := normalizedPair_candidate (specAt i j).a2 ((specAt i j).b2-(specAt i j).a2)
    (integerCandidate i) x v
  dsimp at h ⊢
  have he : (((specAt i j).a2:ℝ)+(((specAt i j).b2-(specAt i j).a2:ℤ):ℝ)*v)/2=
      ((specAt i j).a:ℝ)+(((specAt i j).b:ℝ)-(specAt i j).a)*v := by
    unfold Spec.a Spec.b
    push_cast
    ring
  rw [he,integer_candidate_length] at h
  simpa only [candidate,integerCandidate,denominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h

lemma signed_abs_bound (sgn t : ℝ) (hs : |sgn|=1) (h : 1≤ sgn*t) : 1≤ |t| := by
  have hh := h.trans (le_abs_self (sgn*t))
  simpa only [abs_mul,hs,one_mul] using hh

lemma valid_point (i : Fin 86) (j : ℕ) (c : Certificate) (hc : valid i j c)
    (hs : |((specAt i j).sign:ℝ)|=1) (hab : (specAt i j).a<(specAt i j).b)
    (T : ℝ) (z : ℂ) (h0 : 0≤ z.re) (h1 : z.re≤ 1)
    (ha : ((specAt i j).a:ℝ)≤ z.im-T) (hb : z.im-T≤ ((specAt i j).b:ℝ)) :
    1≤ |(rotatedPolynomial (fun n => (candidate i |>.getD n 0:ℝ)) T z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial (fun n => (candidate i |>.getD n 0:ℝ)) T z).im| := by
  let s := specAt i j
  let x : ℝ := z.re-1/2
  let y : ℝ := z.im-T
  have hd : (0:ℝ)<(s.b:ℝ)-s.a := sub_pos.mpr (by exact_mod_cast hab)
  have hx0 : 0≤ 4*x^2 := by positivity
  have hx1 : 4*x^2≤ 1 := by
    dsimp [x]
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hv0 : 0≤ (y-(s.a:ℝ))/((s.b:ℝ)-s.a) := div_nonneg (sub_nonneg.mpr ha) hd.le
  have hv1 : (y-(s.a:ℝ))/((s.b:ℝ)-s.a)≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  let u : I := ⟨4*x^2,hx0,hx1⟩
  let v : I := ⟨(y-(s.a:ℝ))/((s.b:ℝ)-s.a),hv0,hv1⟩
  have hY : (s.a:ℝ)+((s.b:ℝ)-s.a)*(v:ℝ)=y := by
    dsimp [v]
    field_simp
    ring
  have hp := pair_at_point i j x v
  dsimp only at hp
  have hw : ((((s.a:ℝ)+((s.b:ℝ)-s.a)*(v:ℝ)):ℝ):ℂ)-(x:ℂ)*Complex.I=rotatedVariable T z := by
    rw [hY,rotatedVariable_cartesian]
  change (linearEval ((((s.a:ℝ)+((s.b:ℝ)-s.a)*(v:ℝ)):ℝ)-(x:ℂ)*Complex.I) (candidate i)).re=_ ∧
    (linearEval ((((s.a:ℝ)+((s.b:ℝ)-s.a)*(v:ℝ)):ℝ)-(x:ℂ)*Complex.I) (candidate i)).im=_ at hp
  rw [hw,←rotatedPolynomial_list (candidate i) (by rw [candidate_length]; omega)] at hp
  have hbound := valid_sound i j c hc u v
  change 1≤ biEval (u:ℝ) (v:ℝ) (biScale s.sign
    (if s.imaginary then (normalizedPair s.a2 (s.b2-s.a2) (integerCandidate i)).2
      else (normalizedPair s.a2 (s.b2-s.a2) (integerCandidate i)).1))/(denominator:ℝ) at hbound
  rw [biEval_scale] at hbound
  have hcases : s.imaginary=true ∨ s.imaginary=false := by cases s.imaginary <;> simp
  rcases hcases with hyes | hno
  · right
    change s.imaginary=true at hyes
    simp only [hyes,ite_true] at hbound
    have hnorm : 1≤ |biEval (4*x^2) (v:ℝ)
      (normalizedPair s.a2 (s.b2-s.a2) (integerCandidate i)).2/(denominator:ℝ)| := by
      apply signed_abs_bound (s.sign:ℝ) _ hs
      convert! hbound using 1
      dsimp [u]
      ring
    rw [hp.2]
    change |x|≤ |-x*biEval (4*x^2) (v:ℝ)
      (normalizedPair s.a2 (s.b2-s.a2) (integerCandidate i)).2/(denominator:ℝ)|
    rw [mul_div_assoc,abs_mul,abs_neg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (abs_nonneg x)
  · left
    simp only [hno] at hbound
    rw [hp.1]
    apply signed_abs_bound (s.sign:ℝ) _ hs
    convert! hbound using 1
    dsimp [u]
    ring

end CertifiedFastLocalBoxes

end Height100Module108

/- Source module: StreamingLocalBoxSound. -/
section Height100Module109

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein

theorem valid_to_fast (i : Fin 86) (j : ℕ) (c : Certificate) (h : valid i j c) :
    CertifiedFastLocalBoxes.valid i j c := by
  obtain ⟨hpower,hlen,hrows,hrow,hcol,hresultlen,hpositive⟩ := h
  refine ⟨hpower,hlen.le,?_,?_,?_,?_⟩
  · intro u
    have hu : u.val< c.power.length := by rw [hlen]; exact u.isLt
    exact of_decide_eq_true (all_getD_of_lt _ c.power [] hrows u.val hu)
  · intro u v
    rw [hrow,weights15_correct]
    exact transformRows_getD 15 c.power u.val (by rw [hlen]; exact u.isLt) v
  · intro u v
    rw [hcol,weights7_correct]
    exact transformColumns_getD 7 c.row u v.val
  · intro u v
    have hu : u.val< c.result.length := by rw [hresultlen]; exact u.isLt
    have hr := all_getD_of_lt positiveRow c.result [] hpositive u.val hu
    obtain ⟨hrlen,hrall⟩ := Bool.and_eq_true_iff.mp hr
    have hrlen := of_decide_eq_true hrlen
    have hv : v.val<(c.result.getD u.val []).length := by rw [hrlen]; exact v.isLt
    have hp := of_decide_eq_true (all_getD_of_lt _ _ 0 hrall v.val hv)
    simpa only [threshold_correct,matrixAt] using hp

end CertifiedStreamingLocalBoxes

end Height100Module109

/- Source module: StreamingLocalBoxCertificate. -/
section Height100Module110
namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes
theorem row_lengths (i : Fin 86) : (rowSpecs i).length≤ 2 :=
  TaoFivePrimes.rh14to100_bernstein_checks.2 i
theorem certificates_valid (i : Fin 86) (j : ℕ) (hj : j<(rowSpecs i).length) :
    valid i j (certificateAt i j) :=
  TaoFivePrimes.rh14to100_bernstein_checks.1 i j hj
end CertifiedStreamingLocalBoxes
end Height100Module110

/- Source module: StreamingLocalCandidateNonvanishing. -/
section Height100Module111

namespace CertifiedStreamingLocalBoxes
open CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedLocalPolynomial CertifiedLocalXi

theorem candidate_nonvanishing_certificate (i : Fin 86) (z : ℂ)
    (h0 : 0≤ z.re) (h1 : z.re≤ 1) (him : |z.im-slabCenter i|≤ 1/2) :
    1≤ |(rotatedPolynomial (fun n => (candidate i |>.getD n 0:ℝ)) (slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial (fun n => (candidate i |>.getD n 0:ℝ)) (slabCenter i) z).im| := by
  obtain ⟨j,hj,ha,hb⟩ := specifications_cover i (z.im-slabCenter i)
    (abs_le.mp him).1 (abs_le.mp him).2
  have hj2 : j<2 := hj.trans_le (row_lengths i)
  obtain ⟨hsign,horder⟩ := specifications_valid i ⟨j,hj2⟩ hj
  have hs : |((specAt i j).sign:ℝ)|=1 := by exact_mod_cast hsign
  have hab : (specAt i j).a<(specAt i j).b := by
    unfold Spec.a Spec.b
    apply div_lt_div_of_pos_right _ (by norm_num)
    exact_mod_cast horder
  exact valid_point i j (certificateAt i j) (valid_to_fast i j (certificateAt i j) (certificates_valid i j hj)) hs hab
    (slabCenter i) z h0 h1 ha hb

theorem integer_candidates_nonvanishing (i : Fin 86) (z : ℂ)
    (h0 : 0≤ z.re) (h1 : z.re≤ 1) (him : |z.im-slabCenter i|≤ 1/2) :
    1≤ |(rotatedPolynomial
      (fun n => (CertifiedLocalCandidates.at i.val n:ℝ)/100000000) (slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial
        (fun n => (CertifiedLocalCandidates.at i.val n:ℝ)/100000000) (slabCenter i) z).im| := by
  simpa only [candidate_coefficient] using candidate_nonvanishing_certificate i z h0 h1 him

end CertifiedStreamingLocalBoxes

end Height100Module111

/- Source module: ClosedLocalAssembly. -/
section Height100Module112

namespace CertifiedHeight100
open CertifiedPolynomialTranslation CertifiedGlobalMoments CertifiedLocalXi

noncomputable def normalizationNat (i : Fin 86) : ℕ := 10^((14+i.val)/3)
noncomputable def normalization (i : Fin 86) : ℝ := normalizationNat i
noncomputable def candidateValue (i : Fin 86) (n : ℕ) : ℝ :=
  (CertifiedLocalCandidates.at i.val n:ℝ)/100000000

lemma normalization_nonneg (i : Fin 86) : 0≤ normalization i := Nat.cast_nonneg _
lemma normalization_le (i : Fin 86) : normalization i≤ 10^33 := by
  have hi : (14+i.val)/3≤ 33 := by omega
  have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤ 10) hi
  simpa only [normalization,normalizationNat,Nat.cast_pow,Nat.cast_ofNat] using h

/-- All local analytic estimates,93 finite positivity certificates and86-slab
coverage are closed. Only the actual moment and translation inequalities remain. -/
theorem rh_block_of_certified_global_data (global : ℕ → ℝ)
    (hglobal : ∀ j<256, |moment j-global j|≤ 1/10^46)
    (htranslation : ∀ i : Fin 86, ∀ n<32,
      |normalization i*localGlobalCoefficient global (slabCenter i) n-candidateValue i n|≤ 1/10^7)
    (s : ℂ) (hs : riemannZeta s=0) (h0 : 0< s.re) (h1 : s.re<1)
    (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  apply rh_block_of_real_translation_certificates global hglobal normalization candidateValue
    normalization_nonneg normalization_le htranslation _ s hs h0 h1 ha hb
  intro i z hz0 hz1 hzi
  exact CertifiedStreamingLocalBoxes.integer_candidates_nonvanishing i z hz0 hz1 hzi

end CertifiedHeight100

end Height100Module112

/- Source module: Height100LiteralRoot. -/
section Height100Module113

set_option autoImplicit false
namespace TaoFivePrimes

theorem rh_verified_block_14_1e2 (s : ℂ) (hs : riemannZeta s=0)
    (h0 : 0< s.re) (h1 : s.re<1) (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  apply CertifiedHeight100.rh_block_of_certified_global_data
    CertifiedGlobalMomentEnclosure.candidateMoment
    CertifiedGlobalMomentEnclosure.moments_enclosed _ s hs h0 h1 ha hb
  intro i n hn
  exact CertifiedLiteralTranslation.checked_translation i
    (CertifiedLiteralTranslation.recordAt i) (CertifiedLiteralTranslation.records_checked i) n hn

end TaoFivePrimes

end Height100Module113

theorem solution (s : ℂ) (hs : riemannZeta s=0)
    (h0 : 0< s.re) (h1 : s.re<1) (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 :=
  TaoFivePrimes.rh_verified_block_14_1e2 s hs h0 h1 ha hb
