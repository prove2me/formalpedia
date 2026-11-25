-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_48f55a7aabc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:42.032083+00:00
-- url     : https://prove2.me/submissions/897f24d9-7a65-4d27-841b-2f3e29b8d533

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_ordered_254d16ac3e24

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution (q : Ideal (MRing ι F)) (hq : IsMultiHomogIdeal q) (hne : q ≠ ⊤)
    (h : ∀ a b : MRing ι F, (∃ i, IsWeightedHomogeneous (blockWeight ι) a i) →
      (∃ j, IsWeightedHomogeneous (blockWeight ι) b j) → a * b ∈ q → a ∈ q ∨ b ∈ q) :
    q.IsPrime := by
  classical
  letI : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  haveI : WellFoundedLT K := Finite.to_wellFoundedLT
  have hw : ∀ d : (Σ k, ι k) →₀ ℕ, Finsupp.weight (fun v => toLex (blockWeight ι v)) d =
      toLex (Finsupp.weight (blockWeight ι) d) := by
    intro d
    induction d using Finsupp.induction with
    | zero => simp
    | single_add v n d _ _ ih =>
      rw [map_add, map_add, ih, Finsupp.weight_single, Finsupp.weight_single, toLex_add, toLex_smul]
      rfl
  have hc : ∀ (i : Lex (K → ℕ)) (r : MRing ι F),
      weightedHomogeneousComponent (fun v => toLex (blockWeight ι v)) i r =
        weightedHomogeneousComponent (blockWeight ι) (ofLex i) r := by
    intro i r
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, hw]
    exact if_congr ⟨fun e => by rw [← e]; rfl, fun e => by rw [e]; rfl⟩ rfl rfl
  have hh : ∀ (a : MRing ι F) (i : Lex (K → ℕ)),
      IsWeightedHomogeneous (fun v => toLex (blockWeight ι v)) a i →
        IsWeightedHomogeneous (blockWeight ι) a (ofLex i) := by
    intro a i ha d hd
    have := ha hd
    rw [hw] at this
    rw [← this, ofLex_toLex]
  refine isPrime_of_forms_ordered (fun v => toLex (blockWeight ι v)) q (fun r hr i => ?_) hne ?_
  · rw [hc]; exact hq r hr _
  · rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
    exact h a b ⟨_, hh a i hi⟩ ⟨_, hh b j hj⟩ hab
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
