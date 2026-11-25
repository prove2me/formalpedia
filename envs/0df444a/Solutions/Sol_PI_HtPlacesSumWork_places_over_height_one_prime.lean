-- Prove2me | solution 1 for PI.HtPlacesSumWork.places_over_height_one_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:29:31.967681+00:00
-- url     : https://prove2.me/submissions/ca9c1047-5596-4a76-9cdb-b226375d9498

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_PlacesOverHeightOnePrime
import Theorems.Thm_PI_HtPlacesSumWork_gauss_dvr
import Theorems.Thm_PI_HtPlacesSumWork_gauss_frac
import Theorems.Thm_PI_HtPlacesSumWork_gauss_inj
import Theorems.Thm_PI_HtPlacesSumWork_gauss_lift
import Theorems.Thm_PI_HtPlacesSumWork_gauss_maximalIdeal
import Theorems.Thm_PI_HtPlacesSumWork_gauss_unif
import Theorems.Thm_PI_HtPlacesSumWork_valPl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_omS_finite
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_unif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type}
  [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type}
  [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
namespace PI.HtPlacesSumWork
theorem _root_.solution (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : Data K ι Ω WT A) : LeafSt.places_over_la 𝒜 d := by
  intro hd h la c
  letI : Algebra (Op d.D d.N la) (KTf K d.D d.N) := (OpToKT d.D d.N la).toAlgebra
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := (d.OpToS h la c).toAlgebra
  have : IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsDiscreteValuationRing (Op d.D d.N la) := gauss_dvr d.D d.N la
  have : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := gauss_frac d.D d.N la
  obtain ⟨hfd, hrk⟩ := d.omS_finite hd h c
  have : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := hfd
  have : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := inferInstance
  have hcomp : ∀ x : OT K d.D d.N,
      algebraMap (Op d.D d.N la) (OmS (Ω c) d.D d.N) (algebraMap (OT K d.D d.N) (Op d.D d.N la) x) =
        d.OTtoS c x := by
    intro x
    show d.KTtoS h c (OpToKT d.D d.N la (algebraMap _ _ x)) = _
    rw [gauss_lift]
    exact IsFractionRing.lift_algebraMap _ _
  have hset : d.PlOver la c = PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N) := by
    ext w
    constructor
    · rintro ⟨hnd, hw⟩
      refine ⟨hnd, fun a => ?_⟩
      obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl a
      have hm0 : w (d.OTtoS c m) = 0 :=
        le_antisymm (not_lt.mp fun hp => m.2 ((hw m).2.mp hp)) (hw m).1
      have hsp := congrArg (algebraMap (Op d.D d.N la) (OmS (Ω c) d.D d.N))
        (IsLocalization.mk'_spec (Op d.D d.N la) x m)
      rw [map_mul, hcomp, hcomp] at hsp
      have hv := congrArg w hsp
      rw [AddValuation.map_mul, hm0, add_zero] at hv
      rw [hv, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := Op d.D d.N la) (I := laT d.D d.N la)]
      exact hw x
    · rintro ⟨hnd, hO⟩
      refine ⟨hnd, fun x => ?_⟩
      rw [← hcomp x, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Op d.D d.N la) (laT d.D d.N la)]
      exact hO _
  obtain ⟨π, hπ, hπ0, s, hs, hps⟩ := gauss_unif la
  have hmax := gauss_maximalIdeal d.D d.N la hπ hs hps
  have hϖ : Irreducible (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hWres : ∀ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (a : 𝓞 K),
      d.Wres c w (algebraMap K (Ω c) (a : K)) = w (d.OTtoS c (MvPolynomial.C a)) := by
    intro w a
    show w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) (a : K))) = _
    congr 1
    show _ = d.sH c (MvPolynomial.map (algebraMap (𝓞 K) K) (MvPolynomial.C a))
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hne : d.OTtoS c (MvPolynomial.C π) ≠ 0 := by
    rw [← hcomp]
    intro h0
    have h1 : algebraMap (Op d.D d.N la) (KTf K d.D d.N)
        (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π)) = 0 :=
      (d.KTtoS h c).injective (by rw [map_zero]; exact h0)
    have h2 : algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π) = 0 :=
      (IsFractionRing.injective (Op d.D d.N la) (KTf K d.D d.N)) (by rw [h1, map_zero])
    have h3 : (MvPolynomial.C π : OT K d.D d.N) = 0 :=
      gauss_inj d.D d.N la (by rw [map_zero]; exact h2)
    exact hπ0 (by simpa using h3)
  have he : ∀ w ∈ PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N),
      ((ramIdx (d.Wres c w) la : ℤ) : WithTop ℤ) = w (algebraMap (Op d.D d.N la)
        (OmS (Ω c) d.D d.N) (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π))) := by
    intro w hw
    rw [hcomp]
    obtain ⟨n0, hn0⟩ := WithTop.ne_top_iff_exists.mp (hw.1.1 _ hne)
    rw [← hn0]
    suffices hr : ramIdx (d.Wres c w) la = n0 by rw [hr]
    apply IsLeast.csInf_eq
    refine ⟨⟨π, hπ, hπ0, by rw [hWres, hn0]⟩, ?_⟩
    rintro n ⟨a, ha, -, hna⟩
    rw [hWres] at hna
    have hmem : algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C a) ∈
        maximalIdeal (Op d.D d.N la) := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Op d.D d.N la) (laT d.D d.N la)]
      exact Ideal.mem_map_of_mem _ ha
    rw [hmax, Ideal.mem_span_singleton'] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hv := congrArg (fun t => w (algebraMap (Op d.D d.N la) (OmS (Ω c) d.D d.N) t)) hy
    simp only [map_mul, AddValuation.map_mul, hcomp] at hv
    rw [← hn0, hna] at hv
    have hle : (n0 : WithTop ℤ) ≤ n := by
      rw [← hv]; exact le_add_of_nonneg_left (hw.2 y).1
    exact_mod_cast hle
  have key := valPl (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) hϖ
    (fun w => ramIdx (d.Wres c w) la) he
  rw [hset]
  refine ⟨key.1, ?_⟩
  rw [← hrk]
  exact key.2
end PI.HtPlacesSumWork
