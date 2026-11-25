-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HNm.local_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:17:14.615445+00:00
-- url     : https://prove2.me/submissions/3848293f-e73c-47a0-bce1-211b692cb409

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_norm_eq_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_iff_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_loc_dvr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HNm
open IsDedekindDomain IsLocalRing
variable {R F L : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L]
namespace ReciprocityTheory.ChartRestriction.G.T0.HNm
theorem _root_.solution [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (y : L) (hy : y ≠ 0) :
    (OverR R F L p).Finite ∧ ∃ a s : R, a ∉ p ∧ s ∉ p ∧
      Algebra.norm F y * algebraMap R F s = algebraMap R F g ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ OverR R F L p),
          (fz F w : ℤ) * WithTop.untopD 0 (w y)) * algebraMap R F a := by
  classical
  obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
  haveI := hdvr
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap R F s) := fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      (fun h0 => Ideal.mem_primeCompl_iff.mp s.2 (by rw [h0]; exact p.zero_mem)))
  letI : Algebra (Localization.AtPrime p) F :=
    (IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) F := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) (S := Localization.AtPrime p) hunit x).symm)
  haveI : IsFractionRing (Localization.AtPrime p) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl (Localization.AtPrime p) F
  letI : Algebra (Localization.AtPrime p) L :=
    ((algebraMap F L).comp (algebraMap (Localization.AtPrime p) F)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime p) F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) L := IsScalarTower.of_algebraMap_eq
    (fun x => congrArg (algebraMap F L)
      (IsLocalization.lift_eq (M := p.primeCompl) (S := Localization.AtPrime p) hunit x).symm)
  have hset : OverR R F L p = ValPl.PlacesOver (Localization.AtPrime p) L := by
    ext w
    simp only [OverR, ValPl.PlacesOver, Set.mem_setOf_eq]
    exact and_congr_right fun _ => ValPl.placesOver_iff_loc (R := R) (O := Localization.AtPrime p) (L := L) p w
  haveI : IsDedekindDomain (integralClosure (Localization.AtPrime p) L) :=
    integralClosure.isDedekindDomain (Localization.AtPrime p) F L
  haveI : IsFractionRing (integralClosure (Localization.AtPrime p) L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := Localization.AtPrime p) (K := F) (L := L)
  obtain ⟨u, hu, hN⟩ := ValPl.norm_eq_places (O := Localization.AtPrime p) (F := F) (L := L) y hy hirr
  obtain ⟨⟨a, s⟩, hus⟩ := IsLocalization.mk'_surjective p.primeCompl u
  have hus' : IsLocalization.mk' (Localization.AtPrime p) a s = u := hus
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime p) a s
  rw [hus'] at hspec
  have hs : (s : R) ∉ p := Ideal.mem_primeCompl_iff.mp s.2
  have ha : a ∉ p := by
    have h1 : IsUnit (algebraMap R (Localization.AtPrime p) a) := by
      rw [← hspec]
      exact hu.mul (IsLocalization.map_units (Localization.AtPrime p) s)
    exact Ideal.mem_primeCompl_iff.mp
      ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p a).mp h1)
  have e1 : algebraMap (Localization.AtPrime p) F (algebraMap R (Localization.AtPrime p) g) =
      algebraMap R F g := (IsScalarTower.algebraMap_apply R (Localization.AtPrime p) F g).symm
  have e2 : algebraMap (Localization.AtPrime p) F u * algebraMap R F (s : R) = algebraMap R F a := by
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) F (s : R),
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) F a, ← map_mul, hspec]
  refine ⟨by rw [hset]; exact ValPl.placesOver_finite (Localization.AtPrime p) (F := F) L, a, s, ha, hs, ?_⟩
  rw [hset, hN, e1, mul_assoc, e2]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.G.T0.HNm
