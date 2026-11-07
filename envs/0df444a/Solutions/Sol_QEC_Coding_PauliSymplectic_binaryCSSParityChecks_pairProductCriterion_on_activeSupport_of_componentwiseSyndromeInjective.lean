-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:27:05.253104+00:00
-- url     : https://prove2.me/submissions/de876c12-0f62-4c80-8578-fd8bd2a0f95a

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_CSS_Correctability
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_eq_classicalSyndromes
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndrome_map_properties

section
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
universe u v
variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]
omit [DecidableEq iota] in
private theorem binaryUpToSign_of_equal_binaryCSSSyndrome_of_componentwiseBounds
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {tX tZ : Nat}
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    {E F : Binary iota}
    (hE : HammingWeight E.vector.xPart ≤ tX ∧ HammingWeight E.vector.zPart ≤ tZ)
    (hF : HammingWeight F.vector.xPart ≤ tX ∧ HammingWeight F.vector.zPart ≤ tZ)
    (hsyndrome : stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E =
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) F) :
    BinaryUpToSign E F := by
  rw [binaryCSSSyndrome_eq_classicalSyndromes P Q horth E,
    binaryCSSSyndrome_eq_classicalSyndromes P Q horth F] at hsyndrome
  have hxSyndrome : P E.vector.xPart = P F.vector.xPart := by
    funext p
    exact congrFun hsyndrome (Sum.inl p)
  have hzSyndrome : Q E.vector.zPart = Q F.vector.zPart := by
    funext q
    exact congrFun hsyndrome (Sum.inr q)
  have hx : E.vector.xPart = F.vector.xPart :=
    hP E.vector.xPart F.vector.xPart hE.1 hF.1 hxSyndrome
  have hz : E.vector.zPart = F.vector.zPart :=
    hQ E.vector.zPart F.vector.zPart hE.2 hF.2 hzSyndrome
  change E.vector = F.vector
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := iota)).injective
  exact Prod.ext hx hz
private theorem relative_inGeneratedGroupUpToSign_of_binaryUpToSign
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {E F : Binary iota} (hEF : BinaryUpToSign E F) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).InGeneratedGroupUpToSign
      (binaryMul (binaryDagger E) F) := by
  refine ⟨binaryOne, ?_, ?_⟩
  · rw [← binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth]
    exact GeneratedStabilizer.one
  · change (binaryMul (binaryDagger E) F).vector = (binaryOne (ι := iota)).vector
    calc
      (binaryMul (binaryDagger E) F).vector =
          (binaryMul (binaryDagger E) E).vector := by
            rcases E with ⟨ephase, evector⟩
            rcases F with ⟨fphase, fvector⟩
            change evector = fvector at hEF
            subst fvector
            rfl
      _ = (binaryOne (ι := iota)).vector := by
        rw [binaryMul_binaryDagger_left]
private theorem relative_not_inBinaryNormalizer_of_binaryCSSSyndrome_ne
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {E F : Binary iota}
    (hsyndrome : stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E ≠
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) F) :
    ¬ (binaryCSSStabilizerCodeOfParityChecks P Q horth).InBinaryNormalizer
      (binaryMul (binaryDagger E) F) := by
  let generators := binaryCSSParityCheckGenerators P Q
  let R := binaryMul (binaryDagger E) F
  have hmaps := stabilizerSyndrome_map_properties generators R E F
  have hrelativeSyndrome : stabilizerSyndrome generators R ≠ 0 := by
    intro hzero
    apply hsyndrome
    apply hmaps.2.1.2
    rw [hmaps.2.2]
    exact hzero
  have hnotGeneratorNormalizer : ¬ InStabilizerNormalizer generators R := by
    intro hnormalizer
    exact hrelativeSyndrome (hmaps.1.2 hnormalizer)
  intro hnormalizer
  apply hnotGeneratorNormalizer
  intro S hS
  apply hnormalizer S
  rw [← binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth]
  exact hS
end PauliSymplectic
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe u v
variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ) :
    ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth).1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (E a)) (E b)) ∨
        ¬ (binaryCSSSourceValidStabilizerOfParityChecks P Q horth).1.InBinaryNormalizer
          (binaryMul (binaryDagger (E a)) (E b)) := by
  intro a b ha hb
  by_cases hsyndrome :
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (E a) =
        stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (E b)
  · apply Or.inl
    exact relative_inGeneratedGroupUpToSign_of_binaryUpToSign P Q horth
      (binaryUpToSign_of_equal_binaryCSSSyndrome_of_componentwiseBounds
        P Q horth hP hQ (hbound a ha) (hbound b hb) hsyndrome)
  · exact Or.inr
      (relative_not_inBinaryNormalizer_of_binaryCSSSyndrome_ne P Q horth hsyndrome)
end QEC.Coding.PauliSymplectic
