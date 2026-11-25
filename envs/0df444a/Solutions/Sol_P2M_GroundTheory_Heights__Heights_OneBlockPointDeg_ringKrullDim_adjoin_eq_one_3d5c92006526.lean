-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_ringKrullDim_adjoin_eq_one_3d5c92006526
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:43.556838+00:00
-- url     : https://prove2.me/submissions/8eba985f-616b-4be8-8c68-6fa1eb55ab41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_eq_of_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
open GroundTheory.Heights₂.Heights.OneBlockPointDeg
variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}
namespace GroundTheory.Heights₂.Heights.OneBlockPointDeg
theorem _root_.solution {σ : Type} (w : σ → Φ') (s : Set Φ') (x : Φ')
    [Module.Finite Φ (Algebra.adjoin Φ s)] (htr : Transcendental (Algebra.adjoin Φ s) x)
    (hx : x ∈ Algebra.adjoin Φ (Set.range w)) (hs : Set.range w ⊆ Algebra.adjoin Φ (s ∪ {x})) :
    ringKrullDim (Algebra.adjoin Φ (Set.range w)) = 1 := by
  have hAB : Algebra.adjoin Φ (Set.range w) ≤ (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ := by
    rw [← Algebra.adjoin_union_eq_adjoin_adjoin]; exact Algebra.adjoin_le hs
  let _ : Algebra (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) :=
    (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  let f : (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ →ₐ[Algebra.adjoin Φ (Set.range w)] Φ' :=
    { ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ).val.toRingHom with commutes' := fun _ => rfl }
  have hint : Algebra.IsIntegral (Algebra.adjoin Φ (Set.range w))
      ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) := ⟨fun b => by
    refine (isIntegral_algHom_iff f Subtype.val_injective).mp ?_
    have hb : (b : Φ') ∈ Algebra.adjoin Φ (s ∪ {x}) := by
      rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact b.2
    refine (Algebra.adjoin_le (S := (integralClosure (Algebra.adjoin Φ (Set.range w)) Φ').restrictScalars Φ) ?_) hb
    rintro y (hy | hy)
    · exact ((IsIntegral.of_finite Φ (⟨y, Algebra.subset_adjoin hy⟩ : Algebra.adjoin Φ s)).map
        (Algebra.adjoin Φ s).val).tower_top
    · rw [Set.mem_singleton_iff.mp hy]
      exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin Φ (Set.range w)))⟩
  have : IsArtinianRing (Algebra.adjoin Φ s) := IsArtinianRing.of_finite Φ _
  have : IsNoetherianRing (Algebra.adjoin Φ s) := IsNoetherianRing.of_finite Φ _
  rw [← GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Subalgebra.inclusion_injective hAB)]
  change ringKrullDim (Algebra.adjoin (Algebra.adjoin Φ s) {x}) = 1
  rw [← ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental (s := x) (h := htr)).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_isField (IsArtinianRing.isField_of_isDomain _)]
  rfl
end GroundTheory.Heights₂.Heights.OneBlockPointDeg
