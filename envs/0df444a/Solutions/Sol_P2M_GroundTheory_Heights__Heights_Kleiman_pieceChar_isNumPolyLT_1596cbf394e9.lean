-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_isNumPolyLT_1596cbf394e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:39.639671+00:00
-- url     : https://prove2.me/submissions/276f6683-0c0e-4b37-9ab1-46573e2e8d2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_of_irrelevant_74e81aeef1ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quotient_succ_le_of_lt_6f6a573dbbda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_one_le_ringKrullDim_of_relevant_82aa6fd299a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_of_succ_le_85c067b0ad94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isNumPolyLT_sum_9991b4d10672
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IsNumPolyLT_congr_525cd32145d8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {N : ℕ}
variable {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) {t : ℕ} (L : Fin t → LineBundle k x) (D : ℕ) :
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
      primeOf (S := k) x ≤ pp → ringKrullDim (Poly k N ⧸ pp) ≤ (D : WithBot ℕ∞) →
      ∀ a : ℤ, IsNumPolyLT t D (fun n c => (pieceChar k pp a L n c : ℚ)) := by
  induction D with
  | zero =>
    intro pp hp hh _ hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have := (one_le_ringKrullDim_of_relevant pp hh hrel).trans hdim
      exact absurd this (by simp)
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩
  | succ D ih =>
    intro pp hp hh hle hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have key : ∀ (qq : Ideal (Poly k N)) (b : ℤ), qq.IsPrime →
          (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) → pp < qq →
          IsNumPolyLT t D (fun n c => (pieceChar k qq b L n c : ℚ)) := fun qq b hq hqh hlt =>
        ih qq hq hqh (hle.trans hlt.le)
          (withBot_le_of_succ_le ((ringKrullDim_quotient_succ_le_of_lt hlt).trans hdim)) b
      obtain ⟨i, hi⟩ := hrel
      obtain ⟨r, qq, b, hqq, heq⟩ := hH k Ω N x pp hp hh hle i hi a
      have h0 : IsNumPolyLT t D
          (fun n c => (pieceChar k pp a L n (c + 1) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        (isNumPolyLT_sum _ fun m => key (qq m) (b m) (hqq m).1 (hqq m).2.1
          (lt_of_le_of_ne (hqq m).2.2.1 fun h => hi (h ▸ (hqq m).2.2.2))).congr
          fun n c => by exact_mod_cast (heq t L n c).symm
      choose μ r' qq' b' hqq' heq' using fun j => hS k Ω N x pp hp hh hle ⟨i, hi⟩ t L j a
      have hj : ∀ j, IsNumPolyLT t D (fun n c =>
          (pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ j) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        fun j => (isNumPolyLT_sum _ fun m => key (qq' j m) (b' j m) (hqq' j m).1 (hqq' j m).2.1
          (hqq' j m).2.2).congr fun n c => by exact_mod_cast (heq' j n c).symm
      exact hP t D (fun n c => (pieceChar k pp a L n c : ℚ)) μ h0 hj
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩
end GroundTheory.Heights₂.Heights.Kleiman
