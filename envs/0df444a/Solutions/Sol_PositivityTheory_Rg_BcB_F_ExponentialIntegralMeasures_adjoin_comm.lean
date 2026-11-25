-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.adjoin_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:22.766603+00:00
-- url     : https://prove2.me/submissions/48c1147e-3204-41ed-bc57-545eae8fe447

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
namespace PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
theorem _root_.solution {A : Type} [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : H →L[ℂ] H) (m : ℕ) (hβ : ∀ g, Commute β (R g)) :
    ∀ x ∈ StarAlgebra.adjoin ℂ (Set.range R ∪ {star (β ^ m) * β ^ m}),
      ∀ y ∈ StarAlgebra.adjoin ℂ (Set.range R ∪ {star (β ^ m) * β ^ m}), x * y = y * x := by
  have hB : ∀ g, Commute (star (β ^ m) * β ^ m) (R g) := by
    intro g
    have h1 : Commute (β ^ m) (R g) := (hβ g).pow_left m
    have h2 : Commute (star (β ^ m)) (R g) := by
      have h3 := ((hβ (star g)).pow_left m).star_star
      rwa [map_star, star_star] at h3
    exact h2.mul_left h1
  have hcomm : ∀ a ∈ Set.range R ∪ {star (β ^ m) * β ^ m},
      ∀ b ∈ Set.range R ∪ {star (β ^ m) * β ^ m}, a * b = b * a := by
    rintro a (⟨g, rfl⟩ | ha) b (⟨g', rfl⟩ | hb)
    · rw [← map_mul, ← map_mul, mul_comm]
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact ((hB g).eq).symm
    · rw [Set.mem_singleton_iff] at ha; subst ha; exact (hB g').eq
    · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  have hcs : ∀ a ∈ Set.range R ∪ {star (β ^ m) * β ^ m},
      ∀ b ∈ Set.range R ∪ {star (β ^ m) * β ^ m}, a * star b = star b * a := by
    intro a ha b hb
    rcases hb with ⟨g', rfl⟩ | hb
    · rw [← map_star]; exact hcomm a ha _ (Or.inl ⟨_, rfl⟩)
    · rw [Set.mem_singleton_iff] at hb; subst hb
      rw [star_mul, star_star]; exact hcomm a ha _ (Or.inr rfl)
  intro x hx y hy
  letI := StarAlgebra.adjoinCommRingOfComm ℂ hcomm hcs
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : StarAlgebra.adjoin ℂ _) ⟨y, hy⟩)
end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
