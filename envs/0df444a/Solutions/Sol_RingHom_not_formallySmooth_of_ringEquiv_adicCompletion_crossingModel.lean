-- Prove2me | solution 1 for RingHom.not_formallySmooth_of_ringEquiv_adicCompletion_crossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4f20f03b-0334-5925-92f8-c4352258671c

import Mathlib
import Theorems.Thm_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_not_formallySmooth_of_ringEquiv_adicCompletion_crossingModel

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open IsLocalRing

namespace RingHom
p2m_export "RingHom" "FormallySmooth ext comp_apply mk ker comp mem_ker toAlgebra"
namespace NodeNotSmoothAux
p2m_open "RingHom"

open MvPowerSeries

section LowIdeal

variable {S : Type} [CommRing S] [IsLocalRing S]

def lowIdeal (d : ℕ) : Ideal (MvPowerSeries (Fin 2) S) where
  carrier := {p | ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < d → coeff m p ∈ maximalIdeal S}
  zero_mem' := by
    intro m _
    simp
  add_mem' := by
    intro p q hp hq m hm
    rw [map_add]
    exact Ideal.add_mem _ (hp m hm) (hq m hm)
  smul_mem' := by
    classical
    intro c p hp m hm
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : x.2 0 + x.2 1 < d := by
      have h0 : x.2 0 ≤ m 0 := by rw [← hx, Finsupp.add_apply]; exact Nat.le_add_left _ _
      have h1 : x.2 1 ≤ m 1 := by rw [← hx, Finsupp.add_apply]; exact Nat.le_add_left _ _
      omega
    exact Ideal.mul_mem_left _ _ (hp x.2 hx2)

theorem mem_lowIdeal_iff (d : ℕ) (p : MvPowerSeries (Fin 2) S) :
    p ∈ lowIdeal (S := S) d ↔ ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < d → coeff m p ∈ maximalIdeal S := Iff.rfl

theorem lowIdeal_mono {a b : ℕ} (h : a ≤ b) : lowIdeal (S := S) b ≤ lowIdeal (S := S) a := by
  intro p hp m hm
  exact hp m (lt_of_lt_of_le hm h)

theorem lowIdeal_mul_le (a b : ℕ) :
    lowIdeal (S := S) a * lowIdeal (S := S) b ≤ lowIdeal (S := S) (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro p hp q hq m hm
  rw [mem_lowIdeal_iff] at hp hq
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hsum : (x.1 0 + x.1 1) + (x.2 0 + x.2 1) = m 0 + m 1 := by
    rw [← hx, Finsupp.add_apply, Finsupp.add_apply]; ring
  by_cases h1 : x.1 0 + x.1 1 < a
  · exact Ideal.mul_mem_right _ _ (hp x.1 h1)
  · have h2 : x.2 0 + x.2 1 < b := by omega
    exact Ideal.mul_mem_left _ _ (hq x.2 h2)

theorem maximalIdeal_le_lowIdeal_one :
    maximalIdeal (MvPowerSeries (Fin 2) S) ≤ lowIdeal (S := S) 1 := by
  intro p hp m hm
  have hm0 : m = 0 := by
    ext i
    fin_cases i <;> simp <;> omega
  subst hm0
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff] at hp
  rw [mem_maximalIdeal, mem_nonunits_iff]
  exact hp

theorem maximalIdeal_pow_three_le_lowIdeal :
    maximalIdeal (MvPowerSeries (Fin 2) S) ^ 3 ≤ lowIdeal (S := S) 3 := by
  have h1 := maximalIdeal_le_lowIdeal_one (S := S)
  calc maximalIdeal (MvPowerSeries (Fin 2) S) ^ 3
      = maximalIdeal _ * maximalIdeal _ * maximalIdeal _ := by rw [pow_three, mul_assoc]
    _ ≤ lowIdeal 1 * lowIdeal 1 * lowIdeal 1 := Ideal.mul_mono (Ideal.mul_mono h1 h1) h1
    _ ≤ lowIdeal 2 * lowIdeal 1 := Ideal.mul_mono_left (lowIdeal_mul_le 1 1)
    _ ≤ lowIdeal 3 := lowIdeal_mul_le 2 1

theorem C_mem_lowIdeal {c : S} (hc : c ∈ maximalIdeal S) (d : ℕ) :
    (C c : MvPowerSeries (Fin 2) S) ∈ lowIdeal (S := S) d := by
  classical
  intro m _
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact Ideal.zero_mem _

theorem X_zero_mul_X_one_eq :
    (X 0 * X 1 : MvPowerSeries (Fin 2) S) =
      monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) 1 := by
  rw [X_def, X_def, monomial_mul_monomial, one_mul]

theorem X_zero_mul_X_one_mem_lowIdeal_two :
    (X 0 * X 1 : MvPowerSeries (Fin 2) S) ∈ lowIdeal (S := S) 2 := by
  classical
  intro m hm
  rw [X_zero_mul_X_one_eq, coeff_monomial]
  split_ifs with h
  · exfalso
    subst h
    simp [Finsupp.add_apply, Finsupp.single_apply] at hm
  · exact Ideal.zero_mem _

end LowIdeal

section Completion

variable {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "R̂" => AdicCompletion (maximalIdeal R) R

theorem algebraMap_adicCompletion_eq_of (r : R) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) r = AdicCompletion.of (maximalIdeal R) R r := by
  rw [AdicCompletion.algebraMap_apply]
  simp

theorem exists_sub_algebraMap_mem_map_pow (n : ℕ) (z : AdicCompletion (maximalIdeal R) R) :
    ∃ r : R, z - algebraMap R _ r ∈
      Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R ^ n) := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal R) R n z)
  refine ⟨r, ?_⟩
  have hker : z - AdicCompletion.of (maximalIdeal R) R r ∈
      LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R n) := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of]
    change AdicCompletion.eval (maximalIdeal R) R n z - Submodule.Quotient.mk r = 0
    rw [hr]
    exact sub_self _
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian (maximalIdeal R))] at hker
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at hker
  rw [algebraMap_adicCompletion_eq_of]
  exact hker

theorem mem_pow_of_algebraMap_mem_map_pow (n : ℕ) (r : R)
    (hr : algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈
      Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R ^ n)) :
    r ∈ maximalIdeal R ^ n := by
  have hmem : AdicCompletion.of (maximalIdeal R) R r ∈
      (maximalIdeal R ^ n • ⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    rw [algebraMap_adicCompletion_eq_of] at hr
    exact hr
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian (maximalIdeal R)), LinearMap.mem_ker,
    AdicCompletion.eval_of] at hmem
  have : r ∈ (maximalIdeal R ^ n • ⊤ : Submodule R R) := (Submodule.Quotient.mk_eq_zero _).mp hmem
  simpa [smul_eq_mul, Ideal.mul_top] using this

end Completion

theorem map_ringEquiv_le_maximalIdeal {B D : Type} [CommRing B] [CommRing D] [IsLocalRing B] [IsLocalRing D]
    (e : B ≃+* D) : Ideal.map e.toRingHom (maximalIdeal B) ≤ maximalIdeal D := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hb
  intro hu
  apply hb
  have := hu.map e.symm.toRingHom
  simpa using this

end RingHom.NodeNotSmoothAux

namespace RingHom p2m_export "RingHom" "FormallySmooth ext comp_apply mk ker comp mem_ker toAlgebra" namespace NodeNotSmoothAux end RingHom.NodeNotSmoothAux
p2m_open_scoped "RingHom" in

abbrev RingHom.NodeNotSmoothAux.P2 (S : Type) [CommRing S] : Type := MvPowerSeries (Fin 2) S

p2m_open_scoped "RingHom" in
open RingHom.NodeNotSmoothAux MvPowerSeries in

theorem RingHom.NodeNotSmoothAux.core
    (A₀ : Type) [CommRing A₀] (S : Type) [CommRing S] [IsLocalRing S] [Algebra A₀ S]
    (c : S) (hcmem : c ∈ maximalIdeal S) (a₀ : A₀) (hca : algebraMap A₀ S a₀ = c)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (j : A₀ →+* R)
    (θ : P2 S) (hθ : θ = X 0 * X 1 - C c) (I : Ideal (P2 S)) (hI : I = Ideal.span {θ})
    (e : AdicCompletion (maximalIdeal R) R ≃+* (P2 S ⧸ I))
    (he : ∀ a : A₀,
      e (algebraMap R (AdicCompletion (maximalIdeal R) R) (j a)) =
        Ideal.Quotient.mk I (C (algebraMap A₀ S a))) :
    ¬ j.FormallySmooth := by
  classical
  intro hfs

  obtain ⟨instR, -, -, hmapR, -⟩ :=
    IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq R
  haveI : IsLocalRing (AdicCompletion (maximalIdeal R) R) := instR
  haveI : IsLocalRing (P2 S) := inferInstanceAs (IsLocalRing (MvPowerSeries (Fin 2) S))

  have hθconst : constantCoeff θ = -c := by
    rw [hθ]; simp
  have hθnu : ¬ IsUnit θ := by
    rw [isUnit_iff_constantCoeff, hθconst, IsUnit.neg_iff]
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hcmem) : ¬ IsUnit c)
  have hθmax : θ ∈ maximalIdeal (P2 S) := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hθnu)
  have hIle : I ≤ maximalIdeal (P2 S) := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]; exact hθmax

  have hItop : I ≠ ⊤ := by
    rw [hI, Ne, Ideal.span_singleton_eq_top]; exact hθnu
  haveI : Nontrivial (P2 S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (P2 S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

  have hmaxCq : maximalIdeal (P2 S ⧸ I) ≤ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal (P2 S)) := by
    intro q hq
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu => ?_))
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hq)) (hu.map _)

  set J : Ideal (P2 S) := lowIdeal (S := S) 3 with hJ
  have hmax3 : maximalIdeal (P2 S) ^ 3 ≤ J := maximalIdeal_pow_three_le_lowIdeal
  have hθlow2 : θ ∈ lowIdeal (S := S) 2 := by
    rw [hθ]
    exact Ideal.sub_mem _ X_zero_mul_X_one_mem_lowIdeal_two (C_mem_lowIdeal hcmem 2)
  have hθsqJ : θ ^ 2 ∈ J := by
    have : θ * θ ∈ lowIdeal (S := S) 2 * lowIdeal (S := S) 2 := Ideal.mul_mem_mul hθlow2 hθlow2
    have h4 := lowIdeal_mul_le (S := S) 2 2 this
    rw [pow_two]
    exact lowIdeal_mono (by norm_num) h4
  have hθnotJ : θ ∉ J := by
    intro h
    have h1 := h (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)
      (by simp [Finsupp.add_apply])
    have hcoeff : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) θ = 1 := by
      rw [hθ, map_sub, X_zero_mul_X_one_eq, coeff_monomial_same, coeff_C, if_neg]
      · simp
      · intro h0
        have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h0
        simp [Finsupp.add_apply] at this
    rw [hcoeff] at h1
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp h1)) isUnit_one
  set T := P2 S ⧸ J with hT
  set mkJ : P2 S →+* T := Ideal.Quotient.mk J with hmkJ
  set K : Ideal T := Ideal.map mkJ I with hK
  have hKspan : K = Ideal.span {mkJ θ} := by
    rw [hK, hI, Ideal.map_span, Set.image_singleton]
  have hKnil : IsNilpotent K := by
    refine ⟨2, ?_⟩
    rw [hKspan, Ideal.span_singleton_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, ← map_pow,
      hmkJ, Ideal.Quotient.eq_zero_iff_mem]
    exact hθsqJ
  set mkK : T →+* T ⧸ K := Ideal.Quotient.mk K with hmkK

  set N : Ideal T := Ideal.map mkJ (maximalIdeal (P2 S)) with hN
  have hN3 : N ^ 3 = ⊥ := by
    rw [hN, ← Ideal.map_pow, ← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_bot, hmkJ, Ideal.Quotient.eq_zero_iff_mem]
    exact hmax3 hp
  have hKN : K ≤ N := by
    rw [hK, hN]; exact Ideal.map_mono hIle
  have hNunit : ∀ t ∈ N, IsUnit (1 + t) := by
    intro t ht
    refine IsNilpotent.isUnit_one_add ⟨3, ?_⟩
    have : t ^ 3 ∈ N ^ 3 := Ideal.pow_mem_pow ht 3
    rwa [hN3, Ideal.mem_bot] at this

  have hlamI : ∀ p ∈ I, (mkK.comp mkJ) p = 0 := by
    intro p hp
    rw [RingHom.comp_apply, hmkK, Ideal.Quotient.eq_zero_iff_mem, hK]
    exact Ideal.mem_map_of_mem _ hp
  set lam : P2 S ⧸ I →+* T ⧸ K := Ideal.Quotient.lift I (mkK.comp mkJ) hlamI with hlam
  have hlam_mk : ∀ p : P2 S, lam (Ideal.Quotient.mk I p) = mkK (mkJ p) := by
    intro p; rw [hlam, Ideal.Quotient.lift_mk]; rfl
  have hlam_max3 : ∀ q ∈ maximalIdeal (P2 S ⧸ I) ^ 3, lam q = 0 := by
    intro q hq
    have hq' : q ∈ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal (P2 S)) ^ 3 :=
      Ideal.pow_right_mono hmaxCq 3 hq
    rw [← Ideal.map_pow] at hq'
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq'
    rw [hlam_mk, hmkK, Ideal.Quotient.eq_zero_iff_mem]
    have : mkJ p = 0 := by rw [hmkJ, Ideal.Quotient.eq_zero_iff_mem]; exact hmax3 hp
    rw [this]; exact Ideal.zero_mem _

  letI algR : Algebra A₀ R := j.toAlgebra
  have hfsA : Algebra.FormallySmooth A₀ R := hfs
  have halgP : ∀ a : A₀, algebraMap A₀ (P2 S) a = C (algebraMap A₀ S a) := fun a =>
    MvPowerSeries.algebraMap_apply

  let F'ring : R →+* T ⧸ K := lam.comp (e.toRingHom.comp (algebraMap R (AdicCompletion (maximalIdeal R) R)))
  have hF'ring : ∀ r : R, F'ring r = lam (e (algebraMap R _ r)) := fun r => rfl
  have hF'comm : ∀ a : A₀, F'ring (algebraMap A₀ R a) = algebraMap A₀ (T ⧸ K) a := by
    intro a
    rw [hF'ring, show algebraMap A₀ R a = j a from rfl, he a, hlam_mk, ← halgP,
      hmkK, hmkJ, Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_algebraMap]
  let F' : R →ₐ[A₀] T ⧸ K := { F'ring with commutes' := hF'comm }
  have hF' : ∀ r : R, F' r = lam (e (algebraMap R _ r)) := fun r => rfl

  let G : R →ₐ[A₀] T := Algebra.FormallySmooth.lift K hKnil F'
  have hG : ∀ r : R, mkK (G r) = F' r := fun r => Algebra.FormallySmooth.mk_lift K hKnil F' r
  have hGcomm : ∀ a : A₀, G (j a) = mkJ (C (algebraMap A₀ S a)) := by
    intro a
    rw [show j a = algebraMap A₀ R a from rfl, AlgHom.commutes, ← halgP, hmkJ, Ideal.Quotient.mk_algebraMap]

  have heMax : ∀ z ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), e z ∈ maximalIdeal (P2 S ⧸ I) := by
    intro z hz
    exact map_ringEquiv_le_maximalIdeal e (Ideal.mem_map_of_mem e.toRingHom hz)
  have hιmax : ∀ m ∈ maximalIdeal R,
      algebraMap R (AdicCompletion (maximalIdeal R) R) m ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
    intro m hm
    rw [← hmapR]
    exact Ideal.mem_map_of_mem _ hm

  have hGmax : ∀ m ∈ maximalIdeal R, G m ∈ N := by
    intro m hm
    have h1 : e (algebraMap R _ m) ∈ maximalIdeal (P2 S ⧸ I) := heMax _ (hιmax m hm)
    obtain ⟨p, hp, hpe⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hmaxCq h1)
    have h2 : mkK (G m) = mkK (mkJ p) := by
      rw [hG, hF', ← hpe, hlam_mk]
    have h3 : G m - mkJ p ∈ K := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hmkK, RingHom.map_sub, h2, sub_self]
    have h4 : mkJ p ∈ N := Ideal.mem_map_of_mem _ hp
    have := Ideal.add_mem _ (hKN h3) h4
    simpa using this
  have hGmax3 : ∀ δ ∈ maximalIdeal R ^ 3, G δ = 0 := by
    intro δ hδ
    have h1 : G δ ∈ Ideal.map G.toRingHom (maximalIdeal R ^ 3) := Ideal.mem_map_of_mem _ hδ
    rw [Ideal.map_pow] at h1
    have h2 : Ideal.map G.toRingHom (maximalIdeal R) ≤ N := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      exact hGmax m hm
    have h3 := Ideal.pow_right_mono h2 3 h1
    rwa [hN3, Ideal.mem_bot] at h3

  have happrox : ∀ p : P2 S, ∃ (r : R) (a : P2 S ⧸ I), a ∈ maximalIdeal (P2 S ⧸ I) ^ 3 ∧
      e (algebraMap R _ r) = Ideal.Quotient.mk I p - a := by
    intro p
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_pow 3 (e.symm (Ideal.Quotient.mk I p))
    refine ⟨r, Ideal.Quotient.mk I p - e (algebraMap R _ r), ?_, by ring⟩
    rw [Ideal.map_pow, hmapR] at hr
    have h1 : e (e.symm (Ideal.Quotient.mk I p) - algebraMap R _ r) ∈
        Ideal.map e.toRingHom (maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ 3) :=
      Ideal.mem_map_of_mem e.toRingHom hr
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono (map_ringEquiv_le_maximalIdeal e) 3 h1
    simpa using h2
  obtain ⟨ru, a, ha, hru⟩ := happrox (X 0)
  obtain ⟨rv, b, hb, hrv⟩ := happrox (X 1)

  have huv : Ideal.Quotient.mk I (X 0 : P2 S) * Ideal.Quotient.mk I (X 1) = Ideal.Quotient.mk I (C c) := by
    rw [← map_mul, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton']
    exact ⟨1, by rw [hθ]; ring⟩

  set δ : R := ru * rv - j a₀ with hδ
  have heδ : e (algebraMap R _ δ) =
      -(a * Ideal.Quotient.mk I (X 1)) - Ideal.Quotient.mk I (X 0) * b + a * b := by
    have h1 : e (algebraMap R _ (j a₀)) = Ideal.Quotient.mk I (C c) := by
      rw [he a₀, hca]
    rw [hδ, map_sub, map_mul, map_sub, map_mul, hru, hrv, h1, ← huv]
    ring
  have heδmem : e (algebraMap R _ δ) ∈ maximalIdeal (P2 S ⧸ I) ^ 3 := by
    rw [heδ]
    refine Ideal.add_mem _ (Ideal.sub_mem _ ((Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_right _ _ ha))
      (Ideal.mul_mem_left _ _ hb)) (Ideal.mul_mem_left _ _ hb)
  have hδmem : δ ∈ maximalIdeal R ^ 3 := by
    apply mem_pow_of_algebraMap_mem_map_pow 3 δ
    rw [Ideal.map_pow, hmapR]
    have h1 : e.symm (e (algebraMap R _ δ)) ∈
        Ideal.map e.symm.toRingHom (maximalIdeal (P2 S ⧸ I) ^ 3) :=
      Ideal.mem_map_of_mem e.symm.toRingHom heδmem
    rw [Ideal.map_pow, RingEquiv.symm_apply_apply] at h1
    exact Ideal.pow_right_mono (map_ringEquiv_le_maximalIdeal e.symm) 3 h1

  have hGprod : G ru * G rv = mkJ (C c) := by
    have h1 : G δ = 0 := hGmax3 δ hδmem
    rw [hδ, map_sub, map_mul, hGcomm a₀, hca, sub_eq_zero] at h1
    exact h1

  have hGmod : ∀ (r : R) (p : P2 S) (a' : P2 S ⧸ I), a' ∈ maximalIdeal (P2 S ⧸ I) ^ 3 →
      e (algebraMap R _ r) = Ideal.Quotient.mk I p - a' → ∃ α : T, G r = mkJ p + α * mkJ θ := by
    intro r p a' ha' hr
    have h1 : mkK (G r) = mkK (mkJ p) := by
      rw [hG, hF', hr, map_sub, hlam_mk, hlam_max3 a' ha', sub_zero]
    have h2 : G r - mkJ p ∈ K := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hmkK, RingHom.map_sub, h1, sub_self]
    rw [hKspan, Ideal.mem_span_singleton'] at h2
    obtain ⟨α, hα⟩ := h2
    exact ⟨α, by rw [hα]; ring⟩
  obtain ⟨α, hα⟩ := hGmod ru (X 0) a ha hru
  obtain ⟨β, hβ⟩ := hGmod rv (X 1) b hb hrv

  have hθT : mkJ (X 0) * mkJ (X 1) = mkJ θ + mkJ (C c) := by
    rw [← map_mul, ← map_add, hθ]; congr 1; ring
  have hkey : mkJ θ * (1 + (β * mkJ (X 0) + α * mkJ (X 1) + α * β * mkJ θ)) = 0 := by
    have h1 := hGprod
    rw [hα, hβ] at h1
    have h2 : (mkJ (X 0) + α * mkJ θ) * (mkJ (X 1) + β * mkJ θ) =
        mkJ (X 0) * mkJ (X 1) + mkJ θ * (β * mkJ (X 0) + α * mkJ (X 1) + α * β * mkJ θ) := by ring
    rw [h2, hθT] at h1
    have h3 : mkJ θ + mkJ θ * (β * mkJ (X 0) + α * mkJ (X 1) + α * β * mkJ θ) = 0 := by
      have h4 := congrArg (fun t => t - mkJ (C c)) h1
      simp only [sub_self] at h4
      rw [← h4]; ring
    rw [mul_add, mul_one]
    exact h3

  have hXN : ∀ i : Fin 2, mkJ (X i) ∈ N := by
    intro i
    have hXi : (X i : P2 S) ∈ maximalIdeal (P2 S) := by
      refine (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr ?_)
      rw [isUnit_iff_constantCoeff, constantCoeff_X]
      exact not_isUnit_zero
    exact Ideal.mem_map_of_mem _ hXi
  have hθN : mkJ θ ∈ N := Ideal.mem_map_of_mem _ hθmax
  have hunit : IsUnit (1 + (β * mkJ (X 0) + α * mkJ (X 1) + α * β * mkJ θ)) := by
    refine hNunit _ ?_
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hXN 0))
      (Ideal.mul_mem_left _ _ (hXN 1))) (Ideal.mul_mem_left _ _ hθN)

  have hθzero : mkJ θ = 0 := by
    obtain ⟨uu, huu⟩ := hunit
    have h1 : mkJ θ * (uu : T) = 0 := by rw [huu]; exact hkey
    have h2 := congrArg (fun t => t * ((uu⁻¹ : Tˣ) : T)) h1
    simp only [zero_mul] at h2
    rwa [mul_assoc, Units.mul_inv, mul_one] at h2
  rw [hmkJ, Ideal.Quotient.eq_zero_iff_mem] at hθzero
  exact hθnotJ hθzero

open RingHom.NodeNotSmoothAux MvPowerSeries in
theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (j : A₀ →+* R)
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal R) R ≃+*
      (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
          MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}))
    (he : ∀ a : A₀,
      e (algebraMap R (AdicCompletion (maximalIdeal R) R) (j a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))) :
    ¬ j.FormallySmooth := by

  obtain ⟨instA, -, -, hmapA, -⟩ :=
    IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq A₀
  haveI : IsLocalRing (AdicCompletion (maximalIdeal A₀) A₀) := instA
  have hϖmem : algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀ ∈
      maximalIdeal (AdicCompletion (maximalIdeal A₀) A₀) := by
    rw [← hmapA]
    exact Ideal.mem_map_of_mem _ (by rw [hϖ₀]; exact Ideal.mem_span_singleton_self _)
  have hcmem : algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀ ^ w ∈
      maximalIdeal (AdicCompletion (maximalIdeal A₀) A₀) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hw
    rw [hk, pow_add, pow_one]
    exact Ideal.mul_mem_right _ _ hϖmem
  exact core A₀ (AdicCompletion (maximalIdeal A₀) A₀) _ hcmem (ϖ₀ ^ w) (by rw [map_pow]) R j
    _ rfl _ rfl e he

end S_RingHom_not_formallySmooth_of_ringEquiv_adicCompletion_crossingModel
end P2MW
export P2MW.S_RingHom_not_formallySmooth_of_ringEquiv_adicCompletion_crossingModel (solution)
