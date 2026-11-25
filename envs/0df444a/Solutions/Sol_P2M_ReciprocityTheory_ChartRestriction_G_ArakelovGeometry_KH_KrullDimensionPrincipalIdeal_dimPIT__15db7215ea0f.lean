-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_KH_KrullDimensionPrincipalIdeal_dimPIT__15db7215ea0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:25.516637+00:00
-- url     : https://prove2.me/submissions/06413df1-ece7-43aa-ac33-36dbded16c74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_RingKrullDimQuotientAddOneLeOfLt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_DimFormulaOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_KH_KrullDimensionPrincipalIdeal_dimPIT_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
open ReciprocityTheory.CA
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
theorem _root_.solution : DimPITStatement := by
  intro F _ σ _ V W s hV hs hW
  let e : MvPolynomial σ F ≃+* MvPolynomial (Fin (Fintype.card σ)) F :=
    (MvPolynomial.renameEquiv F (Fintype.equivFin σ)).toRingEquiv
  let g : MvPolynomial (Fin (Fintype.card σ)) F →+* MvPolynomial σ F := e.symm
  let eh : MvPolynomial σ F →+* MvPolynomial (Fin (Fintype.card σ)) F := e
  have hcm : ∀ I : Ideal (MvPolynomial σ F), I.comap g = I.map eh := fun I => Ideal.comap_symm e
  have hV' : (V.map eh).IsPrime := by
    have h0 : (V.comap g).IsPrime := Ideal.comap_isPrime g V
    rwa [hcm] at h0
  have hs' : eh s ∉ V.map eh := by
    rw [← hcm, Ideal.mem_comap]
    simpa [g, eh] using hs
  have key := Ideal.comap_minimalPrimes_eq_of_surjective (f := g) e.symm.surjective
    (V ⊔ Ideal.span {s})
  have hmem : W.comap g ∈ ((V ⊔ Ideal.span {s}).comap g).minimalPrimes := key ▸ ⟨W, hW, rfl⟩
  rw [hcm, hcm, Ideal.map_sup, Ideal.map_span, Set.image_singleton] at hmem
  have := dimPIT_fin F _ _ _ _ hV' hs' hmem
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv W _ e rfl),
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ e rfl)]
  exact this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
