-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL.disc_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:23:51.454277+00:00
-- url     : https://prove2.me/submissions/d12ee831-82ae-4101-8fc4-ea501b3a8f08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscOmL_prod_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_lattice_main
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_exists_val_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_mem_integralClosure_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_norm_eq_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_iff_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_loc_dvr
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_dedekindRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL
open IsDedekindDomain IsLocalRing Module
variable {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL
theorem _root_.solution (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
    (hb : ∀ k c, ∀ w ∈ HNm.OverR R F (L c) p, 0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
    ∃ a s : R, s ∉ p ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
        algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
          (_ : w ∈ HNm.OverR R F (L c) p), (HNm.fz F w : ℤ) * n c w) * algebraMap R F s =
        algebraMap R F a := by
  classical
  let O := Localization.AtPrime p
  letI : Algebra O F := IsLocalization.localizationAlgebraOfSubmonoidLe O F p.primeCompl
    (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsScalarTower R O F := IsLocalization.localization_isScalarTower_of_submonoid_le O F
    p.primeCompl (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsFractionRing O F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl O F
  obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
  haveI := hdvr
  letI : ∀ c, Algebra O (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap O F)).toAlgebra
  haveI : ∀ c, IsScalarTower O F (L c) := fun c => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ c, Algebra R (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap R F)).toAlgebra
  haveI : ∀ c, IsScalarTower R O (L c) := fun c => IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap F (L c) (algebraMap R F x) =
      algebraMap F (L c) (algebraMap O F (algebraMap R O x))
    rw [IsScalarTower.algebraMap_apply R O F x])
  have hded : ∀ c, IsDedekindDomain (integralClosure O (L c)) := fun c =>
    (ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F (L c)).1
  have hfr : ∀ c, IsFractionRing (integralClosure O (L c)) (L c) := fun c =>
    integralClosure.isFractionRing_of_finite_extension F (L c)
  have hset : ∀ c, ValPl.PlacesOver O (L c) = HNm.OverR R F (L c) p := fun c => by
    ext w
    simp only [ValPl.PlacesOver, HNm.OverR, Set.mem_ofPred_eq]
    rw [← ValPl.placesOver_iff_loc (R := R) p w]
    rfl
  have hG : ∀ c, ∃ gc : L c, gc ≠ 0 ∧ (∀ w ∈ ValPl.PlacesOver O (L c), w gc = n c w) ∧
      ∀ y, (∀ w ∈ ValPl.PlacesOver O (L c), 0 ≤ w y + (n c w : WithTop ℤ)) ↔
        gc * y ∈ integralClosure O (L c) := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨gc, hg0, hgv⟩ := HDiscVal.exists_val_eq O F (n c)
    refine ⟨gc, hg0, hgv, fun y => ?_⟩
    rw [HDiscVal.mem_integralClosure_iff O F]
    refine forall₂_congr fun w hw => ?_
    rw [AddValuation.map_mul, hgv w hw, add_comm]
  choose gc hgc0 hgcv hgciff using hG
  have hbI : ∀ k c, gc c * b k c ∈ integralClosure O (L c) := fun k c =>
    (hgciff c _).mp (fun w hw => hb k c w (hset c ▸ hw))
  obtain ⟨nn, t, u, -, hdisc⟩ := HDiscLat.lattice_main (R := O) (F := F) hirr gc hgc0 hm b hbI hli
  set Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
    (_ : w ∈ HNm.OverR R F (L c) p), (HNm.fz F w : ℤ) * n c w with hNc
  have hN : ∀ c, ∃ uc : O, IsUnit uc ∧ Algebra.norm F (gc c) =
      algebraMap R F g ^ Nc c * algebraMap O F uc := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨uc, huc, hn⟩ := ValPl.norm_eq_places (O := O) (F := F) (gc c) (hgc0 c) hirr
    refine ⟨uc, huc, ?_⟩
    rw [hn, ← IsScalarTower.algebraMap_apply R O F g, hset c]
    congr 2
    refine finsum_congr fun w => finsum_congr fun hw => ?_
    rw [← hset c] at hw
    rw [hgcv c w hw, WithTop.untopD_coe]
    rfl
  choose uc huc hNe using hN
  set X := algebraMap R F g with hX
  have hX0 : X ≠ 0 := by
    rw [hX, map_ne_zero_iff _ (IsFractionRing.injective R F)]
    rintro rfl
    have : p = ⊥ := by rw [hg, Ideal.span_singleton_eq_bot]
    subst this
    simp at hp
  let U : Oˣ := ∏ c, (huc c).unit
  have hprod : ∏ c, Algebra.norm F (gc c) = X ^ (∑ c, Nc c) * algebraMap O F (U : O) := by
    rw [Finset.prod_congr rfl fun c _ => hNe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0,
      ← map_prod]
    congr 2
    simp only [U, Units.coe_prod, IsUnit.unit_spec]
  rw [hprod] at hdisc
  set Dt := (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det with hDt
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl
    ((u : O) * ((algebraMap R O g) ^ (2 * nn + t)) * ((U⁻¹ : Oˣ) : O) * ((U⁻¹ : Oˣ) : O))
  refine ⟨a, s, s.2, ?_⟩
  have hsF : algebraMap O F (IsLocalization.mk' O a s) * algebraMap R F s = algebraMap R F a := by
    rw [IsScalarTower.algebraMap_apply R O F s, IsScalarTower.algebraMap_apply R O F a, ← map_mul,
      IsLocalization.mk'_spec]
  simp only at has
  rw [← hsF, has]
  congr 1
  set V := algebraMap O F (U : O)
  set V' := algebraMap O F ((U⁻¹ : Oˣ) : O)
  have hU : V * V' = 1 := by
    simp only [V, V']
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : X ^ (2 * ∑ c, Nc c) = (X ^ (∑ c, Nc c)) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  have e1 : algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t) * ((U⁻¹ : Oˣ) : O) *
      ((U⁻¹ : Oˣ) : O)) = algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t)) * V' * V' := by
    simp only [V', map_mul]
  rw [h2, e1, ← hdisc]
  calc Dt * (X ^ ∑ c, Nc c) ^ 2 = Dt * (X ^ ∑ c, Nc c) ^ 2 * (V * V') * (V * V') := by
        rw [hU]; ring
    _ = Dt * ((X ^ ∑ c, Nc c) * V) ^ 2 * V' * V' := by ring
end ReciprocityTheory.ChartRestriction.G.T0.HDiscOmL
