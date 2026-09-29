-- Prove2me | solution 1 for Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/02aeadfe-40b4-5a46-93fe-e78ae732fb1f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg

open scoped Pointwise

namespace Ideal
p2m_export "Ideal" "map_le_iff_le_comap Quotient.eq_zero_iff_mem comap_mono primeCompl mem_bot comap_lt_comap_of_integral_mem_sdiff comap_isMaximal_of_surjective IsMaximal Quotient.mk mul_mem_left map mk_ker Quotient.lift_mk exists_le_maximal mem_sup_left FG ext IsPrime mem_map_of_mem Quotient.lift comap_map_of_surjective mem_comap comap eq_top_iff_one mem_map_iff_of_surjective Quotient.mk_surjective exists_le_prime_disjoint"
p2m_open "Ideal"

theorem exists_not_mem_mul_pow_eq_zero_of_mem_minimalPrimes
    {R : Type*} [CommRing R] {P : Ideal R} (hP : P ∈ minimalPrimes R) {p : R} (hp : p ∈ P) :
    ∃ t ∉ P, ∃ n : ℕ, t * p ^ n = 0 := by
  classical
  haveI hPprime : P.IsPrime := hP.1.1

  have hnil : IsNilpotent (algebraMap R (Localization.AtPrime P) p) := by
    refine nilpotent_iff_mem_prime.mpr fun Q hQ => ?_
    haveI := hQ
    have hQle : Q.comap (algebraMap R (Localization.AtPrime P)) ≤ P :=
      calc Q.comap (algebraMap R (Localization.AtPrime P))
          ≤ (IsLocalRing.maximalIdeal _).comap (algebraMap R (Localization.AtPrime P)) :=
            Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
        _ = P := IsLocalization.AtPrime.comap_maximalIdeal _ P
    have hPle : P ≤ Q.comap (algebraMap R (Localization.AtPrime P)) :=
      hP.2 ⟨inferInstance, bot_le⟩ hQle
    exact hPle hp
  obtain ⟨n, hn⟩ := hnil
  rw [← map_pow, IsLocalization.map_eq_zero_iff P.primeCompl (Localization.AtPrime P)] at hn
  obtain ⟨⟨t, ht⟩, htp⟩ := hn
  exact ⟨t, ht, n, htp⟩

theorem sup_ne_top_of_mem_minimalPrimes_of_forall_mem
    {R : Type*} [CommRing R] (I : Ideal R) {P : Ideal R} (hP : P ∈ minimalPrimes R)
    (hγ : ∀ t : R, (∃ i ∈ I, (1 + i) * t = 0) → t ∈ P) :
    P ⊔ I ≠ ⊤ := by
  intro htop
  obtain ⟨p, hp, i, hi, hpi⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)

  obtain ⟨t, ht, n, htp⟩ := exists_not_mem_mul_pow_eq_zero_of_mem_minimalPrimes hP hp

  have h1 : p - 1 ∈ I := by
    have : p - 1 = -i := by linear_combination hpi
    rw [this]
    exact I.neg_mem hi
  have hmem : p ^ n - 1 ∈ I := by
    rw [← geom_sum_mul]
    exact I.mul_mem_left _ h1

  exact ht (hγ t ⟨p ^ n - 1, hmem, by linear_combination htp⟩)

end Ideal

namespace Module p2m_export "Module" "Injective support mem_annihilator annihilator mk Finite.of_injective End" end Module
p2m_open_scoped "Module" in

theorem Module.isOfFinAddOrder_of_forall_isMaximal_exists_isOfFinAddOrder_smul
    {R J M : Type*} [CommRing R] [AddCommGroup J] [Module R J] [AddCommGroup M] [Module R M]
    (hfin : Module.Finite ℤ (R ⧸ Module.annihilator R J))
    (I : Ideal R)
    (hγ : ∀ t : R, (∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0) → ∀ y : M, t • y = 0)
    (z : M)
    (hz : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → I ≤ 𝔪 → ∃ s ∉ 𝔪, IsOfFinAddOrder (s • z)) :
    IsOfFinAddOrder z := by
  classical
  set 𝔞 : Ideal R := Module.annihilator R J with h𝔞
  by_contra hzinf

  let Iz : Ideal R :=
    { carrier := {s | IsOfFinAddOrder (s • z)}
      add_mem' := fun {a b} ha hb => by
        simpa only [Set.mem_setOf_eq, add_smul] using IsOfFinAddOrder.add ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, zero_smul]
        exact IsOfFinAddOrder.zero
      smul_mem' := fun c {s} hs => by
        obtain ⟨n, hn, hns⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hs
        refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
        show n • ((c * s) • z) = 0
        rw [mul_smul, smul_comm n c (s • z), hns, smul_zero] }
  have hIz : ∀ s : R, s ∈ Iz ↔ IsOfFinAddOrder (s • z) := fun _ => Iff.rfl

  have h𝔞Iz : 𝔞 ≤ Iz := fun t ht => by
    rw [hIz]
    have h0 : t • z = 0 := hγ t ⟨0, I.zero_mem, fun x => by
      rw [add_zero, one_mul]; exact Module.mem_annihilator.mp ht x⟩ z
    rw [h0]
    exact IsOfFinAddOrder.zero

  have hnat : ∀ n : ℕ, 0 < n → ((n : R)) ∉ Iz := fun n hn hmem => by
    have h' : IsOfFinAddOrder (n • z) := by
      rw [← Nat.cast_smul_eq_nsmul R n z]; exact (hIz _).mp hmem
    exact hzinf (h'.of_nsmul hn.ne')

  haveI : @Module.Finite ℤ (R ⧸ 𝔞) _ _ Algebra.toModule := by convert hfin
  haveI : Algebra.IsIntegral ℤ (R ⧸ 𝔞) := Algebra.IsIntegral.of_finite ℤ (R ⧸ 𝔞)
  have hπ : Function.Surjective (Ideal.Quotient.mk 𝔞) := Ideal.Quotient.mk_surjective

  let S : Submonoid (R ⧸ 𝔞) :=
    { carrier := {x | ∃ n : ℕ, 0 < n ∧ (n : R ⧸ 𝔞) = x}
      one_mem' := ⟨1, Nat.one_pos, Nat.cast_one⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, Nat.mul_pos ha hb, Nat.cast_mul a b⟩ }
  have hcomap : (Iz.map (Ideal.Quotient.mk 𝔞)).comap (Ideal.Quotient.mk 𝔞) = Iz := by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr h𝔞Iz]
  have hdisj : Disjoint ((Iz.map (Ideal.Quotient.mk 𝔞) : Ideal (R ⧸ 𝔞)) : Set (R ⧸ 𝔞))
      (S : Set (R ⧸ 𝔞)) := by
    rw [Set.disjoint_left]
    rintro _ hx ⟨n, hn, rfl⟩
    have hnR : (n : R) ∈ Iz := by
      rw [← hcomap, Ideal.mem_comap, map_natCast]
      exact hx
    exact hnat n hn hnR

  obtain ⟨P, hPprime, hIzP, hPS⟩ :=
    Ideal.exists_le_prime_disjoint (Iz.map (Ideal.Quotient.mk 𝔞)) S hdisj

  have hPint : P.comap (algebraMap ℤ (R ⧸ 𝔞)) = ⊥ := by
    refine eq_bot_iff.mpr fun k hk => ?_
    rw [Submodule.mem_bot]
    by_contra hk0
    have hk' : (k : R ⧸ 𝔞) ∈ P := by simpa only [Ideal.mem_comap, eq_intCast] using hk
    have hmemP : ((k.natAbs : ℕ) : R ⧸ 𝔞) ∈ P := by
      rcases Int.natAbs_eq k with h | h
      · have e : ((k.natAbs : ℕ) : R ⧸ 𝔞) = (k : R ⧸ 𝔞) := by
          conv_rhs => rw [h]
          simp only [Int.cast_natCast]
        rw [e]
        exact hk'
      · have e : ((k.natAbs : ℕ) : R ⧸ 𝔞) = -(k : R ⧸ 𝔞) := by
          conv_rhs => rw [h]
          simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
        rw [e]
        exact P.neg_mem hk'
    exact Set.disjoint_left.mp hPS hmemP ⟨k.natAbs, Int.natAbs_pos.mpr hk0, rfl⟩

  have hPmin : P ∈ minimalPrimes (R ⧸ 𝔞) := by
    refine ⟨⟨hPprime, bot_le⟩, ?_⟩
    rintro Q ⟨hQprime, -⟩ hQP
    by_contra hPQ
    have hlt : Q < P := lt_of_le_of_ne hQP (fun h => hPQ h.ge)
    obtain ⟨-, x, hxP, hxQ⟩ := SetLike.lt_iff_le_and_exists.mp hlt
    haveI := hQprime
    have hlt' := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ℤ) hQP ⟨hxP, hxQ⟩
      (Algebra.IsIntegral.isIntegral x)
    rw [hPint] at hlt'
    exact not_lt_bot hlt'

  have hγ' : ∀ t : R ⧸ 𝔞, (∃ i ∈ I.map (Ideal.Quotient.mk 𝔞), (1 + i) * t = 0) → t ∈ P := by
    rintro tb ⟨ib, hib, h0⟩
    obtain ⟨t, rfl⟩ := hπ tb
    obtain ⟨i, hi, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hπ).mp hib
    have hmem : (1 + i) * t ∈ 𝔞 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_add, map_one]
      exact h0
    have hkill : ∀ y : M, t • y = 0 :=
      hγ t ⟨i, hi, fun x => Module.mem_annihilator.mp hmem x⟩
    refine hIzP (Ideal.mem_map_of_mem _ ?_)
    rw [hIz, hkill z]
    exact IsOfFinAddOrder.zero
  have hsup : P ⊔ I.map (Ideal.Quotient.mk 𝔞) ≠ ⊤ :=
    Ideal.sup_ne_top_of_mem_minimalPrimes_of_forall_mem _ hPmin hγ'

  obtain ⟨𝔪b, h𝔪b, hle⟩ := Ideal.exists_le_maximal _ hsup
  haveI := h𝔪b
  have h𝔪 : (𝔪b.comap (Ideal.Quotient.mk 𝔞)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hπ
  have hI𝔪 : I ≤ 𝔪b.comap (Ideal.Quotient.mk 𝔞) :=
    Ideal.map_le_iff_le_comap.mp (le_sup_right.trans hle)
  obtain ⟨s, hs𝔪, hs⟩ := hz _ h𝔪 hI𝔪
  refine hs𝔪 ?_
  rw [Ideal.mem_comap]
  exact hle (Submodule.mem_sup_left (hIzP (Ideal.mem_map_of_mem _ ((hIz s).mpr hs))))

namespace Module p2m_export "Module" "Injective support mem_annihilator annihilator mk Finite.of_injective End" namespace Finite p2m_export "Module.Finite" "of_finite trans map of_injective quotient" end Module.Finite
p2m_open_scoped "Module Module.Finite" in

theorem Module.Finite.int_quotient_annihilator_of_subalgebra_fg
    {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (ρ : R →+* Module.End ℤ J) (hρ : ∀ (t : R) (x : J), t • x = ρ t x)
    (S : Subalgebra ℤ (Module.End ℤ J)) (hS : (Subalgebra.toSubmodule S).FG)
    (hρS : ∀ t, ρ t ∈ S) :
    Module.Finite ℤ (R ⧸ Module.annihilator R J) := by

  have hker : ∀ a ∈ Module.annihilator R J, ρ a = 0 := fun a ha => by
    ext x
    rw [← hρ, LinearMap.zero_apply]
    exact Module.mem_annihilator.mp ha x
  have hkerle : RingHom.ker ρ ≤ Module.annihilator R J := fun a ha => by
    rw [Module.mem_annihilator]
    intro x
    rw [hρ, RingHom.mem_ker.mp ha, LinearMap.zero_apply]

  have hinj : Function.Injective (Ideal.Quotient.lift (Module.annihilator R J) ρ hker) :=
    RingHom.lift_injective_of_ker_le_ideal _ hker hkerle
  have hmemS : ∀ c, Ideal.Quotient.lift (Module.annihilator R J) ρ hker c ∈ S := fun c => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.Quotient.lift_mk]
    exact hρS t
  let ρS : (R ⧸ Module.annihilator R J) →+* S :=
    (Ideal.Quotient.lift (Module.annihilator R J) ρ hker).codRestrict S hmemS
  have hρS_inj : Function.Injective ρS := fun a b h =>
    hinj (congrArg Subtype.val h)

  haveI : IsNoetherian ℤ S := by
    have h := isNoetherian_of_fg_of_noetherian (Subalgebra.toSubmodule S) hS
    convert h
    rfl
    rfl
    rfl
    rfl
  exact Module.Finite.of_injective ρS.toAddMonoidHom.toIntLinearMap hρS_inj

namespace Submodule p2m_export "Submodule" "inclusion smul_mem' mk mem_bot torsion Quotient.mk mem_map_of_mem mem_comap mem_top smul_mem_smul zero one mem_annihilator Quotient.mk_surjective map Quotient.mk_smul mem_sup annihilator Quotient.mk_eq_zero module mk_eq_zero FG ext add comap comap_mono mem_sup_left map_le_iff_le_comap" namespace Quotient p2m_export "Submodule.Quotient" "mk module mk_surjective mk_smul mk_eq_zero" end Submodule.Quotient
p2m_open_scoped "Submodule Submodule.Quotient" in

theorem Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal
    {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (hfin : Module.Finite ℤ (R ⧸ Module.annihilator R J))
    (I γ : Ideal R) (hγ : ∀ t : R, (∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0) → t ∈ γ)
    (z : J ⧸ (γ • (⊤ : Submodule R J)))
    (hz : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → I ≤ 𝔪 → ∃ s ∉ 𝔪, IsOfFinAddOrder (s • z)) :
    IsOfFinAddOrder z :=
  Module.isOfFinAddOrder_of_forall_isMaximal_exists_isOfFinAddOrder_smul hfin I
    (fun t ht y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (hγ t ht) Submodule.mem_top)
    z hz

theorem solution
    {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (ρ : R →+* Module.End ℤ J) (hρ : ∀ (t : R) (x : J), t • x = ρ t x)
    (S : Subalgebra ℤ (Module.End ℤ J)) (hS : (Subalgebra.toSubmodule S).FG)
    (hρS : ∀ t, ρ t ∈ S)
    (I γ : Ideal R) (hγ : ∀ t : R, (∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0) → t ∈ γ)
    (z : J ⧸ (γ • (⊤ : Submodule R J)))
    (hz : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → I ≤ 𝔪 → ∃ s ∉ 𝔪, IsOfFinAddOrder (s • z)) :
    IsOfFinAddOrder z :=
  Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal
    (Module.Finite.int_quotient_annihilator_of_subalgebra_fg ρ hρ S hS hρS) I γ hγ z hz

end S_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
end P2MW
export P2MW.S_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg (solution)
