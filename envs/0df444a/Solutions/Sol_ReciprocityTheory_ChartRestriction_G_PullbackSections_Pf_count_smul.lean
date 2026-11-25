-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:25.414647+00:00
-- url     : https://prove2.me/submissions/034556be-cde6-43b2-9070-830c65104821

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (σ : E ≃ₐ[ℚ] E) {P X : Ideal (𝓞 E)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : (σ • P).IsPrime)
    (hQ0 : σ • P ≠ ⊥) (hX : X ≠ ⊥) :
    (normalizedFactors (σ • X)).count (σ • P) = (normalizedFactors X).count P := by
  let f := MulDistribMulAction.toMulEquiv (Ideal (𝓞 E)) σ
  have hf : ∀ I : Ideal (𝓞 E), f I = σ • I := fun _ => rfl
  have hX' : (normalizedFactors X).prod = X :=
    (associated_iff_eq.mp (prod_normalizedFactors (by simpa using hX)))
  have hprime : ∀ p ∈ (normalizedFactors X).map f, Prime p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact (MulEquiv.prime_iff f).mpr (prime_of_normalized_factor q hq)
  have hmap : normalizedFactors (σ • X) = (normalizedFactors X).map f := by
    have h1 : ((normalizedFactors X).map f).prod = σ • X := by
      rw [← map_multiset_prod f, hX'] <;> rfl
    rw [← h1, normalizedFactors_prod_of_prime hprime]
  rw [hmap, ← hf]
  exact Multiset.count_map_eq_count' f _ f.injective P
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
