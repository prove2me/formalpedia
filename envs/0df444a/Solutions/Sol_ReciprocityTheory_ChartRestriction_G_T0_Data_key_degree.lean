-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.key_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:47:48.102293+00:00
-- url     : https://prove2.me/submissions/ebbe7186-e9ed-4ed5-b189-61a206bf2890

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_factorization_clause
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_prod_zpow_eq_zpow_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_int_eq_zero_of_two_zpow
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply


section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private theorem sum_fst_lemma {D N : ℕ} [DecidablePred (fun v : TVar D N => v.1 = (1 : Fin (D + 1)))]
    (s : TVar D N →₀ ℕ) :
    ∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = (1 : Fin (D + 1))), s v = ∑ j, s (1, j) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single (1 : Fin (D + 1))]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h1
    exact absurd (Finset.mem_univ _) h1
private theorem scaleBlock_eq_C_pow_mul {D N : ℕ} (u : Kˣ) (q : KTp K D N) (m : ℕ)
    (hq : ∀ s ∈ q.support, ∑ j, s (1, j) = m) :
    sigP (N := N) (1 : Fin (D + 1)) u q = MvPolynomial.C ((u : K) ^ m) * q := by
  have hq' : q = ∑ s ∈ q.support, MvPolynomial.monomial s (q.coeff s) := q.as_sum
  rw [hq', map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [sigP, scaleEquiv_monomial, sum_fst_lemma, hq s hs]
private theorem key_lemma_3 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (r : Ω c) (hr : r ≠ 0)
    (n : Ideal (KTp K d.D d.N) → ℤ) (hfin : {p | p ∈ d.HtOne ∧ n p ≠ 0}.Finite)
    (hN : ∃ κ : K, κ ≠ 0 ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p)
    (hhom : ∀ p ∈ d.HtOne, n p ≠ 0 → ∀ s ∈ (d.gen p).support, ∑ j, s (1, j) = d.dg (d.gen p)) :
    (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), n p * (d.dg (d.gen p) : ℤ)) = 0 := by
  classical
  obtain ⟨κ, hκ, hN⟩ := hN
  have hb : (1 : Fin (d.D + 1)) ≠ 0 := by
    have := hd.D_ge
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  have hT : ∀ p, p ∈ hfin.toFinset ↔ p ∈ d.HtOne ∧ n p ≠ 0 := fun p => Set.Finite.mem_toFinset hfin
  have hprod : ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p =
      ∏ p ∈ hfin.toFinset, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p := by
    apply finprod_mem_eq_prod_of_subset
    · rintro p ⟨hp, hs⟩
      refine (hT p).mpr ⟨hp, fun h0 => hs ?_⟩
      simp [h0]
    · intro p hp
      exact ((hT p).mp hp).1
  have hsum : (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), n p * (d.dg (d.gen p) : ℤ)) =
      ∑ p ∈ hfin.toFinset, n p * (d.dg (d.gen p) : ℤ) := by
    apply finsum_mem_eq_sum_of_subset
    · rintro p ⟨hp, hs⟩
      refine (hT p).mpr ⟨hp, fun h0 => hs ?_⟩
      simp [h0]
    · intro p hp
      exact ((hT p).mp hp).1
  rw [hsum]
  rw [hprod] at hN
  have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) r ≠ 0 := by
    intro h0
    exact hr ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
  have hX : (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r)) ≠ 0 := by
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    by_cases hfd : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
    · exact Algebra.norm_ne_zero_iff.mpr hne
    · rw [Algebra.norm_eq_one_of_not_exists_basis]
      · exact one_ne_zero
      · rintro ⟨s, ⟨bs⟩⟩
        exact hfd (Module.Finite.of_basis bs)
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = 2 := ⟨Units.mk0 2 two_ne_zero, rfl⟩
  have hσ := d.sigF_norm h c 1 hb u r
  have hκσ : sigF (N := d.N) (1 : Fin (d.D + 1)) u (algebraMap K (KTf K d.D d.N) κ) =
      algebraMap K (KTf K d.D d.N) κ := by
    rw [IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N), sigF,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact (sigP (N := d.N) (1 : Fin (d.D + 1)) u).commutes κ
  have hgσ : ∀ p ∈ hfin.toFinset, sigF (N := d.N) (1 : Fin (d.D + 1)) u
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p) =
      algebraMap K (KTf K d.D d.N) 2 ^ (n p * (d.dg (d.gen p) : ℤ)) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (hT p).mp hp
    rw [map_zpow₀, sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have hs : (sigP (N := d.N) (1 : Fin (d.D + 1)) u).toRingEquiv (d.gen p) =
        MvPolynomial.C ((u : K) ^ d.dg (d.gen p)) * d.gen p :=
      scaleBlock_eq_C_pow_mul u (d.gen p) _ (hhom p hp1 hp2)
    rw [hs, map_mul, mul_zpow]
    congr 1
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, map_pow, hu,
      ← zpow_natCast, ← zpow_mul, mul_comm]
  have h2 : algebraMap K (KTf K d.D d.N) 2 ≠ 0 :=
    (map_ne_zero (algebraMap K (KTf K d.D d.N))).mpr two_ne_zero
  rw [hN] at hσ hX
  simp only [map_mul, map_prod] at hσ
  rw [hκσ, Finset.prod_congr rfl hgσ, Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum _ _ h2] at hσ
  have h1 : algebraMap K (KTf K d.D d.N) 2 ^ (∑ p ∈ hfin.toFinset, n p * (d.dg (d.gen p) : ℤ)) = 1 := by
    apply mul_right_cancel₀ hX
    rw [one_mul]
    linear_combination hσ
  rw [← map_zpow₀, map_eq_one_iff _ (algebraMap K (KTf K d.D d.N)).injective] at h1
  exact int_eq_zero_of_two_zpow h1
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (r : Ω c) (hr : r ≠ 0) :
    (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w r)) * (d.dg (d.gen p) : ℤ)) = 0 := by
  classical
  have hb : (1 : Fin (d.D + 1)) ≠ 0 := by
    have := hd.D_ge
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  refine key_lemma_3 d hd h c r hr (fun p => ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ d.GoodP c p), (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w r))
    ?_ (d.norm_factorization_clause hd h c r hr) ?_
  · obtain ⟨-, hy⟩ := d.norm_by_places hd h c
    have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) r ≠ 0 := by
      intro h0
      exact hr ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
    refine (hy _ hne).1.subset ?_
    rintro p ⟨hp, hsum⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push_neg at hcon
    apply hsum
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : w ∈ d.GoodP c p
    · have h0 : d.Wres c w r = 0 := hcon w hw.1
      simp [finsum_eq_if, hw, h0]
    · simp [finsum_eq_if, hw]
  intro p hp hn0 s hs
  have hex : ∃ w, w ∈ d.GoodP c p := by
    by_contra hne
    push_neg at hne
    apply hn0
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    simp [finsum_eq_if, hne w]
  have := (d.good_primes_properties hd h c).2.1 p hp hex s hs 1
  simpa [hb] using this
end ReciprocityTheory.ChartRestriction.G.T0.Data
