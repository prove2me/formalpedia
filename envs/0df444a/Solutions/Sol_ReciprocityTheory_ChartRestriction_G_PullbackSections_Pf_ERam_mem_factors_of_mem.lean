-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.mem_factors_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:41.957954+00:00
-- url     : https://prove2.me/submissions/86521090-e79c-4f3d-9e49-bbe9c6ac81c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution {P : Ideal (𝓞 E)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {x : 𝓞 E} (hx0 : x ≠ 0) (hx : x ∈ P) :
    0 < (normalizedFactors (Ideal.span {x})).count P := by
  have hspan : Ideal.span {x} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx0
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hdvd : P ∣ Ideal.span {x} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hx)
  obtain ⟨Q, hQ, hPQ⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hspan hirr hdvd
  rw [associated_iff_eq] at hPQ
  rw [hPQ]
  exact Multiset.count_pos.2 hQ
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
