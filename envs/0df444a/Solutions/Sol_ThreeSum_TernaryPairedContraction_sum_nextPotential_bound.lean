-- Prove2me | solution 1 for ThreeSum.TernaryPairedContraction.sum_nextPotential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:04.705677+00:00
-- url     : https://prove2.me/submissions/e42d84b6-2405-4009-bce9-809c89af6081

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
import Theorems.Thm_ThreeSum_TernaryPairedContraction_child_card_le
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_admissible_event_bound
import Theorems.Thm_ThreeSum_TernaryPairedPotential_mod_independent_of_minorWeight_pos
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedContraction
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {p : ℕ} [Fact p.Prime]
variable {E P : Type*} [Field E] [Algebra (ZMod p) E]
  [Fintype E] [DecidableEq E] [Fintype P]
namespace ThreeSum.TernaryPairedContraction
theorem _root_.solution {Λ L m F : ℕ} {α π : DigitType}
    (ℓ : E →ₗ[ZMod p] ZMod p) (hℓ : ℓ ≠ 0)
    (V : Submodule (ZMod p) (Fin Λ → ZMod p)) (hV : V ≠ ⊤) (hp : 3 ≤ p)
    (A : P → Matrix (Fin (m+m)) (Fin Λ) ℤ)
    (hsmall : ∀ a f, ((A a).submatrix id f).det.natAbs < p)
    (maps : Fin F → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (hsize1 : 8*Λ*p^2 ≤ Fintype.card E)
    (hsize : 8*Λ*p^(2*(m+m)) ≤ Fintype.card E) :
    p^(m+m) * (∑ seed ∈ admissible Λ ℓ V,
      nextPotential (α := α) (π := π) ℓ A maps seed) ≤
      3*(admissible Λ ℓ V).card*F*(vertices L π).card*
        (2^(π 1)*3^(π 2))^m*potential A := by
  let S := admissible Λ ℓ V
  have ht (a : P) (c : Child L m F α π) :
      p^(m+m) * (∑ seed ∈ S,
        if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
        then minorWeight (A a) else 0) ≤ 3*S.card*minorWeight (A a) := by
    by_cases hz : minorWeight (A a) = 0
    · simp [hz]
    · have hind := mod_independent_of_minorWeight_pos (A a) (Nat.pos_of_ne_zero hz) (hsmall a)
      have hc := admissible_event_bound ℓ hℓ V hV (by simpa using hp)
        (fun i j => (A a i j : ZMod p)) hind (childTarget maps c)
        (by simpa using hsize1) (by simpa using hsize)
      have he : (∑ seed ∈ S,
          if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
          then minorWeight (A a) else 0) =
          (S ∩ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)).card *
            minorWeight (A a) := by
        rw [← sum_filter]
        simp only [sum_const, smul_eq_mul]
        congr 1
      rw [he]
      have hh := Nat.mul_le_mul_right (minorWeight (A a)) hc
      simpa [S,Nat.mul_assoc] using hh
  have he : (∑ seed ∈ S, nextPotential (α := α) (π := π) ℓ A maps seed) =
      ∑ a : P, ∑ c : Child L m F α π, ∑ seed ∈ S,
        if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
        then minorWeight (A a) else 0 := by
    unfold nextPotential
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
  rw [he,mul_sum]
  calc
    _ ≤ ∑ a : P, ∑ _c : Child L m F α π, 3*S.card*minorWeight (A a) := by
      apply sum_le_sum
      intro a ha
      rw [mul_sum]
      exact sum_le_sum fun c hc => ht a c
    _ = 3*S.card*Fintype.card (Child L m F α π)*potential A := by
      simp only [sum_const,card_univ,smul_eq_mul,potential]
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      ring
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right (potential A)
        (Nat.mul_le_mul_left (3*S.card) (child_card_le L m F α π))
      simpa only [Nat.mul_assoc] using hh
end ThreeSum.TernaryPairedContraction
