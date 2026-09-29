-- Prove2me | solution 1 for ValuationSubring.exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/eb3730c0-0ce6-52c2-9b35-1c3b23375732

import Mathlib
import Theorems.Thm_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal

set_option autoImplicit false

open IsLocalRing Polynomial

universe u

namespace WeierstrassPrep

theorem isUnit_of_isUnit_mk {S : Type*} [CommRing S] [IsLocalRing S] (I : Ideal S)
    (hI : I ≤ maximalIdeal S) (s : S) (hu : IsUnit (Ideal.Quotient.mk I s)) : IsUnit s := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I)] at hy
  have h1 : s * s' - 1 ∈ I := Ideal.Quotient.eq.mp hy
  by_contra hns
  have h2 : s * s' ∈ maximalIdeal S := Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hns)
  have h3 : (1 : S) ∈ maximalIdeal S := by
    have : (1 : S) = s * s' - (s * s' - 1) := by ring
    rw [this]; exact Ideal.sub_mem _ h2 (hI h1)
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 isUnit_one

theorem fibre_facts {S : Type*} [CommRing S] [IsLocalRing S] (I : Ideal S) [I.IsPrime]
    (hI : I ≤ maximalIdeal S) (hnoeth : IsNoetherianRing (S ⧸ I))
    (t : S) (ht : maximalIdeal S = Ideal.span {t} ⊔ I)
    (h : S) (hh : h ∉ I) (hhu : ¬ IsUnit h) :
    ∃ n : ℕ, n ≠ 0 ∧ t ^ n ∈ Ideal.span {h} ⊔ I ∧
      (∀ P : Ideal S, P.IsPrime → I ≤ P → h ∈ P → t ∈ P) ∧
      (∀ (m : ℕ) (v h' : S), IsUnit v → m ≤ n → t ^ m * v - h * h' ∈ I → m = n ∧ IsUnit h') := by
  classical
  have htmax : t ∈ maximalIdeal S := ht ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)
  have hhmax : h ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hhu
  set Sb := S ⧸ I with hSb
  set π : S →+* Sb := Ideal.Quotient.mk I with hπdef
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : Nontrivial Sb := Ideal.Quotient.nontrivial_iff.mpr (fun hI' => hh (hI' ▸ Submodule.mem_top))
  haveI : IsLocalRing Sb := IsLocalRing.of_surjective' π hπsurj
  haveI : IsDomain Sb := Ideal.Quotient.isDomain I
  haveI : IsNoetherianRing Sb := hnoeth
  have hπunit : ∀ s : S, IsUnit (π s) ↔ IsUnit s :=
    fun s => ⟨isUnit_of_isUnit_mk I hI s, fun hu => hu.map π⟩
  have hπmax : ∀ s : S, π s ∈ maximalIdeal Sb ↔ s ∈ maximalIdeal S := by
    intro s; rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, hπunit]
  have hmaxb : maximalIdeal Sb = Ideal.span {π t} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨s, rfl⟩ := hπsurj x
      have hs : s ∈ maximalIdeal S := (hπmax s).mp hx
      rw [ht] at hs
      obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.mp hs
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hi, add_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, hπmax]; exact htmax
  have hπt0 : π t ≠ 0 := by
    intro h0
    apply hh
    have : maximalIdeal S ≤ I := by
      intro s hs
      have h1 : π s ∈ maximalIdeal Sb := (hπmax s).mpr hs
      rw [hmaxb, h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at h1
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    exact this hhmax
  have hirr : Irreducible (π t) := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hπt0 hmaxb
  have hprinc : (maximalIdeal Sb).IsPrincipal := ⟨⟨π t, by rw [hmaxb, Ideal.submodule_span_eq]⟩⟩
  haveI hPIR : IsPrincipalIdealRing Sb :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain Sb).out 0 4).mpr hprinc
  haveI : IsDiscreteValuationRing Sb :=
    { not_a_field' := by
        intro hf
        have h1 : π t ∈ maximalIdeal Sb := by rw [hmaxb]; exact Ideal.mem_span_singleton_self _
        rw [hf] at h1
        exact hπt0 h1 }
  have hπh0 : π h ≠ 0 := fun h0 => hh (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  obtain ⟨n, ub, hub⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπh0 hirr
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hhu
    rw [← hπunit, hub, pow_zero, mul_one]; exact ub.isUnit
  refine ⟨n, hn0, ?_, ?_, ?_⟩
  ·
    obtain ⟨w, hw⟩ := hπsurj (↑ub⁻¹ : Sb)
    have e : π (t ^ n - w * h) = 0 := by
      rw [map_sub, map_mul, map_pow, hw, hub, ← mul_assoc, Units.inv_mul, one_mul, sub_self]
    have hmem : t ^ n - w * h ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp e
    have : t ^ n = w * h + (t ^ n - w * h) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.mpr ⟨w, rfl⟩)) (Ideal.mem_sup_right hmem)
  ·
    intro P hP hIP hhP
    have hπP : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hπsurj (by rw [Ideal.mk_ker]; exact hIP)
    have h1 : π h ∈ P.map π := Ideal.mem_map_of_mem _ hhP
    rw [hub] at h1
    have h2 : π t ^ n ∈ P.map π := by
      have := Ideal.mul_mem_left (P.map π) (↑ub⁻¹ : Sb) h1
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this
    have h3 : π t ∈ P.map π := hπP.mem_of_pow_mem n h2
    have h4 : t ∈ (P.map π).comap π := h3
    rwa [Ideal.comap_map_of_surjective _ hπsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hIP] at h4
  ·
    intro m v h' hv hmn hcong
    have e : π t ^ m * π v = π h * π h' := by
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hcong
      rw [map_sub, map_mul, map_mul, map_pow, sub_eq_zero] at this
      exact this
    rw [hub] at e
    have hvu : IsUnit (π v) := hv.map π
    by_cases hh'0 : π h' = 0
    · exfalso
      rw [hh'0, mul_zero, mul_eq_zero] at e
      rcases e with e | e
      · exact hπt0 (eq_zero_of_pow_eq_zero e)
      · exact hvu.ne_zero e
    obtain ⟨k, wu, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh'0 hirr
    rw [hwu] at e

    have e2 : (hvu.unit : Sb) * π t ^ m = ((ub * wu : Sbˣ) : Sb) * π t ^ (n + k) := by
      rw [IsUnit.unit_spec, Units.val_mul, pow_add]
      calc π v * π t ^ m = π t ^ m * π v := mul_comm _ _
        _ = ↑ub * π t ^ n * (↑wu * π t ^ k) := e
        _ = ↑ub * ↑wu * (π t ^ n * π t ^ k) := by ring
    have hmk : m = n + k := IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr _ _ _ _ e2
    have hk : k = 0 := by omega
    refine ⟨by omega, ?_⟩
    rw [← hπunit, hwu, hk, pow_zero, mul_one]
    exact wu.isUnit

theorem moduleFinite_quotient_span
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    {P : Type u} [CommRing P] [Algebra R P] [Algebra.FiniteType R P] [Algebra P S] [IsScalarTower R P S]
    (hloc : IsLocalization ((maximalIdeal S).comap (algebraMap P S)).primeCompl S)
    (hres' : ∀ s : S, ∃ a : R, s - algebraMap R S a ∈ maximalIdeal S)
    (t : S) (ht : maximalIdeal S = Ideal.span {t} ⊔ (maximalIdeal R).map (algebraMap R S))
    (h : S) (hhmax : h ∈ maximalIdeal S)
    (hprimes : ∀ Q : Ideal S, Q.IsPrime → (maximalIdeal R).map (algebraMap R S) ≤ Q → h ∈ Q → t ∈ Q)
    (h₀ : P) (hJ : (Ideal.span {h₀}).map (algebraMap P S) = Ideal.span {h}) :
    Module.Finite R (S ⧸ Ideal.span {h}) := by
  classical
  set I : Ideal S := (maximalIdeal R).map (algebraMap R S) with hIdef
  set 𝔭 : Ideal P := (maximalIdeal S).comap (algebraMap P S) with h𝔭def
  haveI h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  haveI := hloc
  have hunit𝔭 : ∀ y : P, y ∉ 𝔭 ↔ IsUnit (algebraMap P S y) := by
    intro y; rw [h𝔭def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  set J₀ : Ideal P := Ideal.span {h₀} with hJ₀def
  have hJmax : J₀.map (algebraMap P S) ≤ maximalIdeal S := by
    rw [hJ, Ideal.span_singleton_le_iff_mem]; exact hhmax
  haveI : Algebra.FiniteType R (P ⧸ J₀) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R J₀) (Ideal.Quotient.mkₐ_surjective _ _)

  let C : Type u := S ⧸ J₀.map (algebraMap P S)
  let πC : S →+* C := Ideal.Quotient.mk (J₀.map (algebraMap P S))
  have hπCsurj : Function.Surjective πC := Ideal.Quotient.mk_surjective
  haveI : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr (fun htop => by
    have := hJmax; rw [htop] at this; exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp this))
  haveI : IsLocalRing C := IsLocalRing.of_surjective' πC hπCsurj
  have hπCunit : ∀ s : S, IsUnit (πC s) ↔ IsUnit s :=
    fun s => ⟨isUnit_of_isUnit_mk _ hJmax s, fun hu => hu.map πC⟩
  have hπCmax : ∀ s : S, πC s ∈ maximalIdeal C ↔ s ∈ maximalIdeal S := by
    intro s; rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, hπCunit]
  have hcompat : ∀ y : P, algebraMap (P ⧸ J₀) C (Ideal.Quotient.mk J₀ y) = πC (algebraMap P S y) := fun _ => rfl
  have hAC : ∀ a : R, algebraMap R C a = πC (algebraMap R S a) := fun _ => rfl
  haveI : IsScalarTower R (P ⧸ J₀) C := IsScalarTower.of_algebraMap_eq (fun a => by
    have e1 : algebraMap R (P ⧸ J₀) a = Ideal.Quotient.mk J₀ (algebraMap R P a) := rfl
    rw [e1, hcompat, hAC]
    exact congrArg πC (IsScalarTower.algebraMap_apply R P S a))
  set 𝔮 : Ideal (P ⧸ J₀) := (maximalIdeal C).comap (algebraMap (P ⧸ J₀) C) with h𝔮def
  haveI h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hunit𝔮 : ∀ x : P ⧸ J₀, x ∉ 𝔮 ↔ IsUnit (algebraMap (P ⧸ J₀) C x) := by
    intro x; rw [h𝔮def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hNle : Algebra.algebraMapSubmonoid (P ⧸ J₀) 𝔭.primeCompl ≤ 𝔮.primeCompl := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Ideal.mem_primeCompl_iff, hunit𝔮, Ideal.Quotient.algebraMap_eq, hcompat, hπCunit]
    exact (hunit𝔭 y).mp hy
  haveI hloc𝔮 : IsLocalization 𝔮.primeCompl C :=
    IsLocalization.of_le (Algebra.algebraMapSubmonoid (P ⧸ J₀) 𝔭.primeCompl) _ hNle
      (fun x hx => (hunit𝔮 x).mp hx)

  haveI : IsLocalHom (algebraMap R C) := ⟨fun a ha => by
    rw [hAC, hπCunit, isUnit_map_iff] at ha
    exact ha⟩
  have h𝔮A : 𝔮.comap (algebraMap R (P ⧸ J₀)) = maximalIdeal R := by
    ext a
    rw [Ideal.mem_comap, h𝔮def, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

  have h𝔮max : 𝔮.IsMaximal := by
    let ρ : (P ⧸ J₀) →+* ResidueField C := (IsLocalRing.residue C).comp (algebraMap (P ⧸ J₀) C)
    have hkerρ : RingHom.ker ρ = 𝔮 := by
      ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, h𝔮def, Ideal.mem_comap]
    have hρsurj : Function.Surjective ρ := by
      intro z
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨s, rfl⟩ := hπCsurj c
      obtain ⟨a, ha⟩ := hres' s
      refine ⟨algebraMap R (P ⧸ J₀) a, ?_⟩
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hAC, eq_comm, ← sub_eq_zero, ← map_sub, ← map_sub,
        IsLocalRing.residue_eq_zero_iff, hπCmax]
      exact ha
    rw [← hkerρ]
    exact RingHom.ker_isMaximal_of_surjective ρ hρsurj

  have hπCmax_eq : (maximalIdeal S).map πC = maximalIdeal C := by
    have : (maximalIdeal C).comap πC = maximalIdeal S := by
      ext s; rw [Ideal.mem_comap, hπCmax]
    rw [← this, Ideal.map_comap_of_surjective _ hπCsurj]
  have hmin : ∀ Q : Ideal (P ⧸ J₀), Q.IsPrime → Q.comap (algebraMap R (P ⧸ J₀)) = maximalIdeal R →
      Q ≤ 𝔮 → Q = 𝔮 := by
    intro Q hQ hQA hQle
    have hdisj : Disjoint (𝔮.primeCompl : Set (P ⧸ J₀)) Q := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact (Ideal.mem_primeCompl_iff.mp hx) (hQle hxQ)
    set Q' : Ideal C := Q.map (algebraMap (P ⧸ J₀) C) with hQ'
    haveI hQ'p : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl C Q hQ hdisj
    have hQ'under : Q'.comap (algebraMap (P ⧸ J₀) C) = Q :=
      IsLocalization.under_map_of_isPrime_disjoint 𝔮.primeCompl C hQ hdisj
    set Q'' : Ideal S := Q'.comap πC with hQ''
    haveI hQ''p : Q''.IsPrime := Ideal.comap_isPrime _ _
    have hIQ'' : I ≤ Q'' := by
      rw [hIdef, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, hQ'', Ideal.mem_comap]
      have h1 : algebraMap R (P ⧸ J₀) a ∈ Q := by rw [← Ideal.mem_comap, hQA]; exact ha
      have h2 : algebraMap (P ⧸ J₀) C (algebraMap R (P ⧸ J₀) a) ∈ Q' := Ideal.mem_map_of_mem _ h1
      rw [← IsScalarTower.algebraMap_apply, hAC] at h2
      exact h2
    have hhQ'' : h ∈ Q'' := by
      rw [hQ'', Ideal.mem_comap]
      have : πC h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hJ]; exact Ideal.mem_span_singleton_self h)
      rw [this]; exact Q'.zero_mem
    have htQ'' : t ∈ Q'' := hprimes Q'' hQ''p hIQ'' hhQ''
    have hQ''max : Q'' = maximalIdeal S := by
      apply ((IsLocalRing.maximalIdeal.isMaximal S).eq_of_le hQ''p.ne_top ?_).symm
      rw [ht]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr htQ'') hIQ''
    have hQ'max : Q' = maximalIdeal C := by
      rw [← Ideal.map_comap_of_surjective πC hπCsurj Q', ← hQ'', hQ''max, hπCmax_eq]
    rw [← hQ'under, hQ'max]

  haveI : Algebra.QuasiFiniteAt R 𝔮 := by
    let q : PrimeSpectrum (P ⧸ J₀) := ⟨𝔮, h𝔮p⟩
    let p : PrimeSpectrum R := q.comap (algebraMap R (P ⧸ J₀))
    let X := ↥(PrimeSpectrum.comap (algebraMap R (P ⧸ J₀)) ⁻¹' {p})
    let x₀ : X := ⟨q, rfl⟩
    let e := PrimeSpectrum.preimageHomeomorphFiber R (P ⧸ J₀) p
    let eo := PrimeSpectrum.preimageOrderIsoFiber R (P ⧸ J₀) p
    have hee : ∀ y : X, e y = eo y := fun _ => rfl
    haveI : IsNoetherianRing (p.asIdeal.Fiber (P ⧸ J₀)) :=
      Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
    haveI : IsJacobsonRing (p.asIdeal.Fiber (P ⧸ J₀)) :=
      isJacobsonRing_of_finiteType (A := p.asIdeal.ResidueField)
    have hclosed : IsClosed ({e x₀} : Set (PrimeSpectrum (p.asIdeal.Fiber (P ⧸ J₀)))) := by
      rw [← Set.image_singleton, e.isClosed_image]
      have hq : IsClosed ({q} : Set (PrimeSpectrum (P ⧸ J₀))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr h𝔮max
      have h2 := hq.preimage (continuous_subtype_val (p := fun z => z ∈ PrimeSpectrum.comap (algebraMap R (P ⧸ J₀)) ⁻¹' {p}))
      convert h2 using 1
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun hy => by rw [hy], fun hy => Subtype.ext hy⟩
    have hstable : StableUnderGeneralization ({e x₀} : Set (PrimeSpectrum (p.asIdeal.Fiber (P ⧸ J₀)))) := by
      intro a b hba ha
      rw [Set.mem_singleton_iff] at ha ⊢
      obtain ⟨y, rfl⟩ := e.surjective b
      subst ha
      rw [← PrimeSpectrum.le_iff_specializes, hee, hee, eo.le_iff_le] at hba
      have hle : y.1.asIdeal ≤ 𝔮 := hba
      have hyA : y.1.asIdeal.comap (algebraMap R (P ⧸ J₀)) = maximalIdeal R := by
        have h1 : PrimeSpectrum.comap (algebraMap R (P ⧸ J₀)) y.1 = p := y.2
        have h2 := congrArg PrimeSpectrum.asIdeal h1
        rw [PrimeSpectrum.comap_asIdeal] at h2
        rw [h2]
        change (PrimeSpectrum.comap (algebraMap R (P ⧸ J₀)) q).asIdeal = _
        rw [PrimeSpectrum.comap_asIdeal]
        exact h𝔮A
      have hyq : y.1.asIdeal = 𝔮 := hmin _ y.1.2 hyA hle
      have : y = x₀ := Subtype.ext (PrimeSpectrum.ext hyq)
      rw [this]
    have h3 : IsClosed ({e x₀} : Set (PrimeSpectrum (p.asIdeal.Fiber (P ⧸ J₀)))) ∧
        StableUnderGeneralization ({e x₀} : Set (PrimeSpectrum (p.asIdeal.Fiber (P ⧸ J₀)))) := ⟨hclosed, hstable⟩
    have hopen : IsOpen ({e x₀} : Set (PrimeSpectrum (p.asIdeal.Fiber (P ⧸ J₀)))) :=
      ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing (e x₀)).out 0 2).mpr h3
    have hopenX : IsOpen ({x₀} : Set X) := by
      have h1 : e ⁻¹' {e x₀} = {x₀} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, e.injective.eq_iff]
      rw [← h1]; exact hopen.preimage e.continuous
    exact Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q hopenX
  haveI hLfin : Module.Finite R (Localization.AtPrime 𝔮) :=
    HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt 𝔮 h𝔮A
  haveI hCfin : Module.Finite R C := by
    let eC : Localization.AtPrime 𝔮 ≃ₐ[P ⧸ J₀] C := IsLocalization.algEquiv 𝔮.primeCompl _ _
    exact Module.Finite.equiv (eC.restrictScalars R).toLinearEquiv
  exact Module.Finite.equiv (Ideal.quotientEquivAlgOfEq R hJ).toLinearEquiv

end WeierstrassPrep

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L) [HenselianLocalRing ↥A]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra ↥A S] [IsLocalHom (algebraMap ↥A S)]
    [Algebra.EssFiniteType ↥A S]
    (hres : Function.Surjective (algebraMap ↥A (ResidueField S)))
    (t : S) (ht : maximalIdeal S = Ideal.span {t} ⊔ (maximalIdeal ↥A).map (algebraMap ↥A S))
    (hprime : ((maximalIdeal ↥A).map (algebraMap ↥A S)).IsPrime)
    (h : S) (hh : h ∉ (maximalIdeal ↥A).map (algebraMap ↥A S)) :
    ∃ (n : ℕ) (u : Sˣ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) ∧
      h = (u : S) * ∏ i, (t - algebraMap ↥A S (r i)) := by
  classical

  by_cases hhu : IsUnit h
  · exact ⟨0, hhu.unit, Fin.elim0, fun i => i.elim0, by simp⟩
  set I : Ideal S := (maximalIdeal ↥A).map (algebraMap ↥A S) with hIdef
  have hmm : ∀ a : ↥A, algebraMap ↥A S a ∈ maximalIdeal S ↔ a ∈ maximalIdeal ↥A := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff]
  have hImax : I ≤ maximalIdeal S := by
    rw [hIdef, Ideal.map_le_iff_le_comap]; intro a ha; rw [Ideal.mem_comap, hmm]; exact ha
  have htmax : t ∈ maximalIdeal S := ht ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)
  have hhmax : h ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hhu

  have hres' : ∀ s : S, ∃ a : ↥A, s - algebraMap ↥A S a ∈ maximalIdeal S := by
    intro s
    obtain ⟨a, ha⟩ := hres (IsLocalRing.residue S s)
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply ↥A S (ResidueField S), IsLocalRing.ResidueField.algebraMap_eq] at ha
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← ha, sub_self]
  have hnoeth : IsNoetherianRing (S ⧸ I) := by
    haveI : IsNoetherianRing (↥A ⧸ maximalIdeal ↥A) := inferInstanceAs (IsNoetherianRing (ResidueField ↥A))
    exact Algebra.EssFiniteType.isNoetherianRing (↥A ⧸ maximalIdeal ↥A) (S ⧸ I)

  haveI := hprime
  obtain ⟨n, hn0, htn, hprimes, hcompare⟩ := WeierstrassPrep.fibre_facts I hImax hnoeth t ht h hh hhu

  have hCfin : Module.Finite ↥A (S ⧸ Ideal.span {h}) := by
    let T₀ : Type u := ↥(Algebra.EssFiniteType.subalgebra ↥A S)
    let M₀ : Submonoid T₀ := Algebra.EssFiniteType.submonoid ↥A S
    haveI : IsLocalization M₀ S := Algebra.EssFiniteType.isLocalization ↥A S
    let 𝔭 : Ideal T₀ := (maximalIdeal S).comap (algebraMap T₀ S)
    haveI h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime _ _
    have hunit𝔭 : ∀ y : T₀, y ∉ 𝔭 ↔ IsUnit (algebraMap T₀ S y) := by
      intro y; rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have hM₀le : M₀ ≤ 𝔭.primeCompl := by
      intro y hy
      rw [Ideal.mem_primeCompl_iff, hunit𝔭]
      exact hy
    have hloc𝔭 : IsLocalization 𝔭.primeCompl S :=
      IsLocalization.of_le M₀ _ hM₀le (fun y hy => (hunit𝔭 y).mp hy)
    obtain ⟨⟨h₀, m⟩, ehm⟩ := @IsLocalization.surj _ _ 𝔭.primeCompl S _ _ hloc𝔭 h
    simp only at ehm
    have hJ : (Ideal.span {h₀}).map (algebraMap T₀ S) = Ideal.span {h} := by
      rw [Ideal.map_span, Set.image_singleton, ← ehm]
      exact Ideal.span_singleton_mul_right_unit (@IsLocalization.map_units _ _ 𝔭.primeCompl S _ _ hloc𝔭 m) h
    exact WeierstrassPrep.moduleFinite_quotient_span hloc𝔭 hres' t ht h hhmax
      (fun Q hQ hIQ hhQ => hprimes Q hQ hIQ hhQ) h₀ hJ

  obtain ⟨W, hWmonic, hWdeg, hWt⟩ : ∃ W : (↥A)[X], W.Monic ∧ W.natDegree = n ∧
      Polynomial.aeval t W ∈ Ideal.span {h} := by
    set J : Ideal S := Ideal.span {h} with hJdef
    let πC : S →ₐ[↥A] S ⧸ J := Ideal.Quotient.mkₐ ↥A J
    have hπC : ∀ s, πC s = Ideal.Quotient.mk J s := fun _ => rfl

    have hexp : ∀ (m : ℕ) (s : S), ∃ (a : Fin m → ↥A) (s' : S),
        s - ((∑ i, algebraMap ↥A S (a i) * t ^ (i : ℕ)) + t ^ m * s') ∈ I := by
      intro m
      induction m with
      | zero => intro s; exact ⟨Fin.elim0, s, by simp⟩
      | succ m ih =>
        intro s
        obtain ⟨a, s', hs⟩ := ih s
        obtain ⟨c, hc⟩ := hres' s'
        rw [ht] at hc
        obtain ⟨x, hx, i, hi, hxi⟩ := Submodule.mem_sup.mp hc
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        refine ⟨Fin.snoc a c, g, ?_⟩
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        have e : s - ((∑ i : Fin m, algebraMap ↥A S (a i) * t ^ (i : ℕ) + algebraMap ↥A S c * t ^ m) +
              t ^ (m + 1) * g)
            = (s - ((∑ i : Fin m, algebraMap ↥A S (a i) * t ^ (i : ℕ)) + t ^ m * s')) +
              t ^ m * (s' - algebraMap ↥A S c - g * t) := by ring
        rw [e]
        refine Ideal.add_mem _ hs (Ideal.mul_mem_left _ _ ?_)
        have : s' - algebraMap ↥A S c - g * t = i := by rw [← hxi]; ring
        rw [this]; exact hi

    have hIsmul : ∀ i ∈ I, πC i ∈ (maximalIdeal ↥A) • (⊤ : Submodule ↥A (S ⧸ J)) := by
      intro i hi
      have h1 : i ∈ (maximalIdeal ↥A) • (⊤ : Submodule ↥A S) := by
        rw [Ideal.smul_top_eq_map]; exact hi
      have h2 := Submodule.mem_map_of_mem (f := πC.toLinearMap) h1
      rw [Submodule.map_smul''] at h2
      exact Submodule.smul_mono le_rfl le_top h2
    have htn' : ∀ s' : S, πC (t ^ n * s') ∈ (maximalIdeal ↥A) • (⊤ : Submodule ↥A (S ⧸ J)) := by
      intro s'
      obtain ⟨x, hx, i, hi, hxi⟩ := Submodule.mem_sup.mp htn
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [← hxi, add_mul, map_add]
      have h0 : πC (g * h * s') = 0 := by
        rw [hπC, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self h))
      rw [h0, zero_add]
      exact hIsmul _ (Ideal.mul_mem_right _ _ hi)
    let N : Submodule ↥A (S ⧸ J) := Submodule.span ↥A (Set.range fun i : Fin n => πC t ^ (i : ℕ))
    have hle : (⊤ : Submodule ↥A (S ⧸ J)) ≤ N ⊔ (maximalIdeal ↥A) • ⊤ := by
      rintro x -
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, s', hs⟩ := hexp n s
      have e : s = ((∑ i, algebraMap ↥A S (a i) * t ^ (i : ℕ)) + t ^ n * s') +
          (s - ((∑ i, algebraMap ↥A S (a i) * t ^ (i : ℕ)) + t ^ n * s')) := by ring
      rw [← hπC, e, map_add, map_add]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ?_)
        (Submodule.mem_sup_right (htn' s'))) (Submodule.mem_sup_right (hIsmul _ hs))
      rw [map_sum]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [map_mul, map_pow, AlgHom.commutes, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hN : (⊤ : Submodule ↥A (S ⧸ J)) ≤ N :=
      Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) hle
    have hmem : πC t ^ n ∈ N := hN Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ↥A)).mp hmem
    set q : (↥A)[X] := ∑ i : Fin n, Polynomial.C (c i) * X ^ (i : ℕ) with hqdef
    have hqdeg : q.natDegree < n := by
      rcases eq_or_ne q 0 with hq0 | hq0
      · rw [hq0, natDegree_zero]; exact Nat.pos_of_ne_zero hn0
      · exact (natDegree_lt_iff_degree_lt hq0).mpr (degree_sum_fin_lt c)
    have hXn : (X ^ n : (↥A)[X]).natDegree = n := natDegree_X_pow n
    refine ⟨X ^ n - q, monic_X_pow_sub (degree_sum_fin_lt c), ?_, ?_⟩
    · rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hXn]; exact hqdeg), hXn]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← hπC, ← Polynomial.aeval_algHom_apply, map_sub, map_pow, aeval_X,
        hqdef, map_sum, sub_eq_zero, ← hc]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, map_pow, aeval_C, aeval_X, Algebra.smul_def]

  obtain ⟨h', hh'⟩ := Ideal.mem_span_singleton'.mp hWt

  set WL : L[X] := W.map (algebraMap ↥A L) with hWL
  have hWLmonic : WL.Monic := hWmonic.map _
  have hlift : ∀ a ∈ WL.roots, ∃ b : ↥A, algebraMap ↥A L b = a := by
    intro a ha
    have hint : a ∈ integralClosure ↥A L := roots_mem_integralClosure hWmonic ha
    exact IsIntegrallyClosed.isIntegral_iff.mp hint
  let f : L → ↥A := fun a => if hx : ∃ b : ↥A, algebraMap ↥A L b = a then hx.choose else 0
  have hf : ∀ a ∈ WL.roots, algebraMap ↥A L (f a) = a := by
    intro a ha
    simp only [f, dif_pos (hlift a ha)]
    exact (hlift a ha).choose_spec
  set rs : Multiset ↥A := WL.roots.map f with hrs
  have hrsmap : rs.map (algebraMap ↥A L) = WL.roots := by
    rw [hrs, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id WL.roots]
    exact Multiset.map_congr rfl (fun a ha => hf a ha)
  have hWprod : W = (rs.map fun b => X - Polynomial.C b).prod := by
    apply Polynomial.map_injective (algebraMap ↥A L) Subtype.val_injective
    rw [← hWL, (IsAlgClosed.splits WL).eq_prod_roots_of_monic hWLmonic, Polynomial.map_multiset_prod,
      Multiset.map_map]
    conv_lhs => rw [← hrsmap, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl (fun b _ => ?_))
    simp
  have hcard : rs.card = n := by
    rw [hrs, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hWL, hWmonic.natDegree_map, hWdeg]

  have haeval : Polynomial.aeval t W = (rs.map fun b => t - algebraMap ↥A S b).prod := by
    rw [hWprod, map_multiset_prod, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl (fun b _ => ?_))
    simp

  set rin := rs.filter (fun b => b ∈ maximalIdeal ↥A) with hrin
  set rout := rs.filter (fun b => b ∉ maximalIdeal ↥A) with hrout
  have hsplit : rs = rin + rout := (Multiset.filter_add_not _ rs).symm
  set v : S := (rout.map fun b => t - algebraMap ↥A S b).prod with hv
  have hvunit : IsUnit v := by
    have key : ∀ m : Multiset ↥A, (∀ b ∈ m, b ∉ maximalIdeal ↥A) →
        IsUnit (m.map fun b => t - algebraMap ↥A S b).prod := by
      intro m
      induction m using Multiset.induction_on with
      | empty => intro _; simp
      | cons b m ih =>
        intro hm
        rw [Multiset.map_cons, Multiset.prod_cons]
        refine IsUnit.mul ?_ (ih (fun b' hb' => hm b' (Multiset.mem_cons_of_mem hb')))
        have hb : IsUnit (algebraMap ↥A S b) := by
          have := hm b (Multiset.mem_cons_self b m)
          rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, ← isUnit_map_iff (algebraMap ↥A S)] at this
        by_contra hnu
        have h1 : t - algebraMap ↥A S b ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have h2 : algebraMap ↥A S b ∈ maximalIdeal S := by
          have : algebraMap ↥A S b = t - (t - algebraMap ↥A S b) := by ring
          rw [this]; exact Ideal.sub_mem _ htmax h1
        exact (IsLocalRing.mem_maximalIdeal _).mp h2 hb
    exact key rout (fun b hb => (Multiset.mem_filter.mp hb).2)
  have hincong : ∀ m : Multiset ↥A, (∀ b ∈ m, b ∈ maximalIdeal ↥A) →
      (m.map fun b => t - algebraMap ↥A S b).prod - t ^ m.card ∈ I := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | cons b m ih =>
      intro hm
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
      have h1 := ih (fun b' hb' => hm b' (Multiset.mem_cons_of_mem hb'))
      have h2 : algebraMap ↥A S b ∈ I := Ideal.mem_map_of_mem _ (hm b (Multiset.mem_cons_self b m))
      have e : (t - algebraMap ↥A S b) * (m.map fun b => t - algebraMap ↥A S b).prod - t ^ m.card * t =
          t * ((m.map fun b => t - algebraMap ↥A S b).prod - t ^ m.card) -
            algebraMap ↥A S b * (m.map fun b => t - algebraMap ↥A S b).prod := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_right _ _ h2)
  have hcong : t ^ rin.card * v - h * h' ∈ I := by
    have e1 : h * h' = (rin.map fun b => t - algebraMap ↥A S b).prod * v := by
      rw [mul_comm, hh', haeval, hsplit, Multiset.map_add, Multiset.prod_add]
    have e2 : t ^ rin.card * v - h * h' = -(((rin.map fun b => t - algebraMap ↥A S b).prod - t ^ rin.card) * v) := by
      rw [e1]; ring
    rw [e2]
    exact (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_right _ _
      (hincong rin (fun b hb => (Multiset.mem_filter.mp hb).2)))
  have hle : rin.card ≤ n := hcard ▸ Multiset.card_le_card (Multiset.filter_le _ rs)
  obtain ⟨hcardin, hh'unit⟩ := hcompare rin.card v h' hvunit hle hcong

  have hall : ∀ b ∈ rs, b ∈ maximalIdeal ↥A := by
    have : rin = rs := Multiset.eq_of_le_of_card_le (Multiset.filter_le _ rs) (by rw [hcardin, hcard])
    rw [hrin, Multiset.filter_eq_self] at this
    exact this

  set l : List ↥A := rs.toList with hl
  refine ⟨l.length, hh'unit.unit⁻¹, fun j => l.get j, fun j => hall _ ?_, ?_⟩
  · rw [← Multiset.coe_toList rs, ← hl]; exact Multiset.mem_coe.mpr (List.get_mem l j)
  · have e1 : h = ((hh'unit.unit⁻¹ : Sˣ) : S) * (h' * h) := by
      rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [e1, hh', haeval]
    congr 1
    have e2 : (List.ofFn fun i : Fin l.length => t - algebraMap ↥A S (l.get i)) =
        (List.ofFn l.get).map (fun b => t - algebraMap ↥A S b) := by
      rw [List.map_ofFn]; rfl
    rw [← List.prod_ofFn]
    change _ = (List.ofFn fun i : Fin l.length => t - algebraMap ↥A S (l.get i)).prod
    rw [e2, List.ofFn_get, ← Multiset.prod_coe, ← Multiset.map_coe, hl, Multiset.coe_toList]

end S_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
end P2MW
export P2MW.S_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal (solution)
