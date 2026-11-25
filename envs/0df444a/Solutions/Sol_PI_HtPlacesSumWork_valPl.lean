-- Prove2me | solution 1 for PI.HtPlacesSumWork.valPl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:54:25.089895+00:00
-- url     : https://prove2.me/submissions/f52bd24f-beeb-433c-bb07-1dec3d22c3f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_plOf_mem
import Theorems.Thm_PI_HtPlacesSumWork_plOf_injective
import Theorems.Thm_PI_HtPlacesSumWork_mem_range_plOf
import Theorems.Thm_PI_HtPlacesSumWork_plOf_e
import Theorems.Thm_PI_HtPlacesSumWork_plOf_f
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_dedekindRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
namespace PI.HtPlacesSumWork
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) (e : AddValuation L (WithTop ℤ) → ℤ)
    (he : ∀ w ∈ PlacesOver O L, (e w : WithTop ℤ) = w (algebraMap O L ϖ)) :
    (PlacesOver O L).Finite ∧
      ∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L), (fres F L w : ℤ) * e w =
        Module.finrank F L := by
  obtain ⟨hded, -, -, -, hmf, hsum⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F L
  have : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension F L
  have : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).mpr (by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F))
  have : Finite {Q : Ideal (integralClosure O L) // Q.IsMaximal} := hmf.to_subtype
  have hrange : PlacesOver O L = Set.range (plOf O L) := Set.ext fun w =>
    ⟨fun hw => mem_range_plOf hw, by rintro ⟨Q, rfl⟩; exact plOf_mem Q⟩
  refine ⟨hrange ▸ Set.finite_range _, ?_⟩
  rw [hrange, finsum_mem_range (plOf_injective (O := O) (L := L))]
  have hterm : ∀ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
      (fres F L (plOf O L Q) : ℤ) * e (plOf O L Q) =
        ((Q.1.ramificationIdx O * Q.1.inertiaDeg O : ℕ) : ℤ) := by
    intro Q
    have h1 := he _ (plOf_mem Q)
    rw [plOf_e Q hϖ] at h1
    have h2 : e (plOf O L Q) = (Q.1.ramificationIdx O : ℤ) := by exact_mod_cast h1
    rw [h2, plOf_f]; push_cast; ring
  simp_rw [hterm]
  have := Fintype.ofFinite {Q : Ideal (integralClosure O L) // Q.IsMaximal}
  rw [finsum_eq_sum_of_fintype] at hsum ⊢
  rw [← hsum]; push_cast; rfl
end PI.HtPlacesSumWork
