-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.inner_of_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:34.549571+00:00
-- url     : https://prove2.me/submissions/f7999857-3a21-4d34-b5c8-1e0225786a7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution {O W : Type} [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] [AddCommGroup W]
    [Module ℚ W] (L R : O →+* Module.End ℚ W) (hc : ∀ a b, L a * R b = R b * L a) (D : O →+ W)
    (hD : ∀ a b, D (a * b) = R b (D a) + L a (D b)) : ∃ β : W, ∀ a, D a = R a β - L a β := by
  let S := ℚ ⊗[ℤ] O
  let _ : Algebra O S := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)) S := IsLocalization.tensorRight _ _
  have : IsReduced S := isReduced_localizationPreserves (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)) S inferInstance
  have : IsArtinianRing S := IsArtinianRing.of_finite ℚ S
  have : ∀ I : MaximalSpectrum S, Algebra.FormallyUnramified ℚ (S ⧸ I.asIdeal) := fun I => by
    let _ := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable ℚ _
  have : Algebra.FormallyUnramified ℚ S := Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi S).restrictScalars ℚ).symm
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := S)).1 this
  let L' : S →ₗ[ℚ] Module.End ℚ W := LinearMap.liftBaseChange ℚ L.toAddMonoidHom.toIntLinearMap
  let D' : S →ₗ[ℚ] W := LinearMap.liftBaseChange ℚ D.toIntLinearMap
  let Φ : S ⊗[ℚ] S →ₗ[ℚ] W := TensorProduct.lift (L'.compl₂ D')
  have key : ∀ (a : O) (u : S ⊗[ℚ] S), Φ (((1 : S) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] a : S) - ((1 : ℚ) ⊗ₜ[ℤ] a : S) ⊗ₜ[ℚ] (1 : S)) * u) =
      R a (Φ u) - L a (Φ u) + L' (Algebra.TensorProduct.lmul' ℚ u) (D a) := by
    intro a u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [mul_add, map_add, hu, hv, LinearMap.add_apply]; abel
    | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => simp only [add_tmul, mul_add, map_add, hx, hx', LinearMap.add_apply]; abel
      | tmul p x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' hy hy' => simp only [tmul_add, mul_add, map_add, hy, hy', LinearMap.add_apply]; abel
        | tmul q y =>
          have c := LinearMap.congr_fun (hc x a) (D y)
          simp only [Module.End.mul_apply] at c
          simp only [S, sub_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sub, Φ, TensorProduct.lift.tmul,
            LinearMap.compl₂_apply, L', D', LinearMap.liftBaseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
            RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, LinearMap.smul_apply, map_smul,
            Algebra.TensorProduct.lmul'_apply_tmul, mul_comm a y, hD, map_add, c, map_mul, Module.End.mul_apply]
          module
  refine ⟨-Φ t, fun a => ?_⟩
  have := key a t
  rw [ht, map_zero, ht1, show L' 1 = 1 from by
    show L' ((1 : ℚ) ⊗ₜ[ℤ] (1 : O)) = 1
    exact (LinearMap.liftBaseChange_tmul ℚ _ _ _).trans ((one_smul _ _).trans (map_one L))] at this
  simp only [map_neg, Module.End.one_apply] at this ⊢
  linear_combination (norm := abel) -this
end ReciprocityTheory.ChartRestriction.G.TB.Canon
