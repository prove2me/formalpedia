-- Prove2me | solution 1 for TateModule.charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/08f738a9-d9c9-5207-a63c-b053d908dd38

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval

set_option autoImplicit false

open Polynomial

namespace P2mResNorm

variable {p : ℕ} [Fact p.Prime]

theorem resultant_sub_mem_span (G₁ G₂ F : ℤ_[p][X]) (m k L : ℕ)
    (h : ∀ i, G₁.coeff i - G₂.coeff i ∈ Ideal.span {(p : ℤ_[p]) ^ L}) :
    resultant G₁ F m k - resultant G₂ F m k ∈ Ideal.span {(p : ℤ_[p]) ^ L} := by
  rw [← PadicInt.ker_toZModPow, RingHom.sub_mem_ker_iff, ← resultant_map_map,
    ← resultant_map_map]
  congr 1
  ext i
  rw [coeff_map, coeff_map, ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZModPow]
  exact h i

theorem resultant_sub_mem_span_right (G F₁ F₂ : ℤ_[p][X]) (m k L : ℕ)
    (h : ∀ i, F₁.coeff i - F₂.coeff i ∈ Ideal.span {(p : ℤ_[p]) ^ L}) :
    resultant G F₁ m k - resultant G F₂ m k ∈ Ideal.span {(p : ℤ_[p]) ^ L} := by
  rw [← PadicInt.ker_toZModPow, RingHom.sub_mem_ker_iff, ← resultant_map_map,
    ← resultant_map_map]
  congr 1
  ext i
  rw [coeff_map, coeff_map, ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZModPow]
  exact h i

theorem norm_eq_of_sub_mem_span {x y : ℤ_[p]} {L : ℕ}
    (h : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ L}) (hy : (p : ℝ) ^ (-(L : ℤ)) < ‖y‖) :
    ‖x‖ = ‖y‖ := by
  have hle : ‖x - y‖ ≤ (p : ℝ) ^ (-(L : ℤ)) := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 h
  have hlt : ‖x - y‖ < ‖y‖ := lt_of_le_of_lt hle hy
  have hne : ‖y‖ ≠ ‖x - y‖ := (ne_of_lt hlt).symm
  have := PadicInt.norm_add_eq_max_of_ne hne
  rw [add_sub_cancel] at this
  rw [this, max_eq_left hlt.le]

theorem mem_span_pow_of_le {x : ℤ_[p]} {L M : ℕ} (hML : M ≤ L)
    (h : x ∈ Ideal.span {(p : ℤ_[p]) ^ L}) : x ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  exact (pow_dvd_pow _ hML).trans h

theorem exists_int_lift (H : ℤ_[p][X]) (hH : H.Monic) (L : ℕ) :
    ∃ G : ℤ[X], G.Monic ∧ G.natDegree = H.natDegree ∧
      ∀ i, (G.map (Int.castRingHom ℤ_[p])).coeff i - H.coeff i ∈
        Ideal.span {(p : ℤ_[p]) ^ L} := by

  haveI : Fact (1 < p ^ (L + 1)) := ⟨Nat.one_lt_pow (Nat.succ_ne_zero L) (Fact.out : p.Prime).one_lt⟩
  set φ : ℤ_[p] →+* ZMod (p ^ (L + 1)) := PadicInt.toZModPow (L + 1) with hφ
  have hsurj : Function.Surjective (Int.castRingHom (ZMod (p ^ (L + 1)))) :=
    ZMod.ringHom_surjective _
  have hlifts : H.map φ ∈ lifts (Int.castRingHom (ZMod (p ^ (L + 1)))) := by
    rw [mem_lifts]
    exact map_surjective _ hsurj _
  obtain ⟨G, hGmap, hGdeg, hGmon⟩ := lifts_and_natDegree_eq_and_monic hlifts (hH.map φ)
  refine ⟨G, hGmon, ?_, ?_⟩
  · rw [hGdeg, hH.natDegree_map]
  · intro i
    apply mem_span_pow_of_le (Nat.le_succ L)
    rw [← PadicInt.ker_toZModPow, RingHom.sub_mem_ker_iff, coeff_map, ← hφ]
    have hcomp : φ.comp (Int.castRingHom ℤ_[p]) = Int.castRingHom (ZMod (p ^ (L + 1))) :=
      RingHom.ext_int _ _
    have := congrArg (fun q => coeff q i) hGmap
    simp only [coeff_map] at this
    rw [← this, ← RingHom.comp_apply, hcomp]

section Key

variable (π : ℤ_[p][X])

theorem resultant_ne_zero_of_not_dvd (hπ : π.Monic) (hπp : Prime π) (F : ℤ_[p][X])
    (hF : ¬ π ∣ F) : resultant π F ≠ 0 := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  have hirr : Irreducible (π.map (algebraMap ℤ_[p] ℚ_[p])) :=
    (hπ.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hπp.irreducible
  have hndvd : ¬ π.map (algebraMap ℤ_[p] ℚ_[p]) ∣ F.map (algebraMap ℤ_[p] ℚ_[p]) := by
    rwa [Polynomial.map_dvd_map _ hinj hπ]
  have hcop : IsCoprime (π.map (algebraMap ℤ_[p] ℚ_[p])) (F.map (algebraMap ℤ_[p] ℚ_[p])) :=
    hirr.coprime_iff_not_dvd.mpr hndvd
  have hne := resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hne
  exact fun h0 => hne (by rw [h0, map_zero])

theorem resultant_add_C_self (hπ : π.Monic) (c : ℤ_[p]) :
    resultant (π + C c) π π.natDegree π.natDegree =
      (-1) ^ (π.natDegree * π.natDegree) * c ^ π.natDegree := by
  have h1 : π + C c = C c + π * 1 := by ring
  rw [h1, resultant_add_mul_left (C c) π 1 π.natDegree π.natDegree (by simp) le_rfl,
    resultant_C_left]
  rw [coeff_natDegree, hπ.leadingCoeff, one_pow, mul_one]

theorem norm_resultant_perturb (hπ : π.Monic) (hm : 0 < π.natDegree) (F₁ : ℤ_[p][X])
    (a : ℕ) (hr : resultant π F₁ ≠ 0) (M : ℕ) (hM : (resultant π F₁).valuation < M)
    (G : ℤ_[p][X]) (hGdeg : G.natDegree = π.natDegree)
    (hcong : ∀ i, G.coeff i - (π + C ((p : ℤ_[p]) ^ M)).coeff i ∈
      Ideal.span {(p : ℤ_[p]) ^ (M * π.natDegree + 1)}) :
    ‖resultant G (π ^ a * F₁)‖ =
      (((p : ℝ) ^ (-(π.natDegree : ℤ))) ^ M) ^ a * ‖resultant π F₁‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  set m := π.natDegree with hmdef

  have hπa : (π ^ a).Monic := hπ.pow a
  have hdegP : (π ^ a * F₁).natDegree = (π ^ a).natDegree + F₁.natDegree := by
    by_cases hF : F₁ = 0
    · exfalso; apply hr; rw [hF]
      rw [resultant_zero_right]
      simp [hm.ne']
    exact hπa.natDegree_mul' hF

  have hfac : resultant G (π ^ a * F₁) = (resultant G π m m) ^ a * resultant G F₁ m F₁.natDegree := by
    show resultant G (π ^ a * F₁) G.natDegree (π ^ a * F₁).natDegree = _
    rw [hdegP, hGdeg, resultant_mul_right G (π ^ a) F₁ m (le_of_eq hGdeg),
      resultant_pow_right G π m a (le_of_eq hGdeg)
        (by rw [hπ.leadingCoeff, one_pow]; exact one_ne_zero)]

  set L := M * m + 1 with hL
  have hML : M ≤ L := by
    rw [hL]
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * m := Nat.mul_le_mul_left M hm
      _ ≤ M * m + 1 := Nat.le_succ _
  have hcong' : ∀ i, G.coeff i - π.coeff i ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
    intro i
    have h1 := mem_span_pow_of_le hML (hcong i)
    have h2 : (π + C ((p : ℤ_[p]) ^ M)).coeff i - π.coeff i ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
      rw [coeff_add, coeff_C, add_sub_cancel_left]
      split_ifs
      · exact Ideal.mem_span_singleton_self _
      · exact zero_mem _
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

  have hres1 : ‖resultant G π m m‖ = ((p : ℝ) ^ (-(m : ℤ))) ^ M := by
    have hc := resultant_sub_mem_span G (π + C ((p : ℤ_[p]) ^ M)) π m m L hcong
    rw [resultant_add_C_self π hπ] at hc
    have hval : ‖((-1 : ℤ_[p]) ^ (m * m) * ((p : ℤ_[p]) ^ M) ^ m)‖ = ((p : ℝ) ^ (-(m : ℤ))) ^ M := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
        PadicInt.norm_p_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    rw [← hval]
    apply norm_eq_of_sub_mem_span hc
    rw [hval, ← zpow_natCast, ← zpow_mul]
    apply zpow_lt_zpow_right₀ hp1
    rw [hL]
    lia

  have hres2 : ‖resultant G F₁ m F₁.natDegree‖ = ‖resultant π F₁‖ := by
    have hc := resultant_sub_mem_span G π F₁ m F₁.natDegree M hcong'
    apply norm_eq_of_sub_mem_span hc
    rw [PadicInt.norm_eq_zpow_neg_valuation hr]
    apply zpow_lt_zpow_right₀ hp1
    simpa using hM
  rw [hfac, norm_mul, norm_pow, hres1, hres2]

theorem nat_eq_of_pow_eq {u cP cQ : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hcQ : 0 < cQ) {a b M : ℕ}
    (h0 : (u ^ M) ^ a * cP = (u ^ M) ^ b * cQ)
    (h1 : (u ^ (M + 1)) ^ a * cP = (u ^ (M + 1)) ^ b * cQ) : a = b := by
  have e1 : (u ^ (M + 1)) ^ a * cP = u ^ a * ((u ^ M) ^ a * cP) := by ring
  have e2 : (u ^ (M + 1)) ^ b * cQ = u ^ b * ((u ^ M) ^ b * cQ) := by ring
  rw [e1, e2, h0] at h1
  have ht : 0 < (u ^ M) ^ b * cQ := by positivity
  have hab : u ^ a = u ^ b := mul_right_cancel₀ ht.ne' h1
  exact pow_right_injective₀ hu0 hu1.ne hab

theorem pow_eq_of_norm_resultant (hπ : π.Monic) (hm : 0 < π.natDegree)
    (P₁ Q₁ : ℤ_[p][X]) (a b : ℕ)
    (hrP : resultant π P₁ ≠ 0) (hrQ : resultant π Q₁ ≠ 0)
    (h : ∀ G : ℤ[X], G.Monic →
      ‖resultant (G.map (Int.castRingHom ℤ_[p])) (π ^ a * P₁)‖ =
        ‖resultant (G.map (Int.castRingHom ℤ_[p])) (π ^ b * Q₁)‖) : a = b := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  set m := π.natDegree with hmdef
  set u : ℝ := (p : ℝ) ^ (-(m : ℤ)) with hu
  have hu0 : 0 < u := zpow_pos hp0 _
  have hu1 : u < 1 := by
    rw [hu]
    apply zpow_lt_one_of_neg₀ hp1
    simpa using hm

  set M₀ := (resultant π P₁).valuation + (resultant π Q₁).valuation + 1 with hM₀
  have step : ∀ M : ℕ, (resultant π P₁).valuation < M → (resultant π Q₁).valuation < M →
      (u ^ M) ^ a * ‖resultant π P₁‖ = (u ^ M) ^ b * ‖resultant π Q₁‖ := by
    intro M hMP hMQ
    have hHmon : (π + C ((p : ℤ_[p]) ^ M)).Monic := hπ.add_of_left (by
      refine lt_of_le_of_lt degree_C_le ?_
      rw [degree_eq_natDegree hπ.ne_zero]
      exact_mod_cast hm)
    obtain ⟨G, hGmon, hGdeg, hGcong⟩ := exists_int_lift (π + C ((p : ℤ_[p]) ^ M)) hHmon (M * m + 1)
    rw [natDegree_add_C] at hGdeg
    have hGmdeg : (G.map (Int.castRingHom ℤ_[p])).natDegree = π.natDegree := by
      rw [hGmon.natDegree_map, hGdeg]
    have eP := norm_resultant_perturb π hπ hm P₁ a hrP M hMP _ hGmdeg hGcong
    have eQ := norm_resultant_perturb π hπ hm Q₁ b hrQ M hMQ _ hGmdeg hGcong
    rw [← eP, ← eQ]
    exact h G hGmon
  have h0 := step M₀ (by rw [hM₀]; omega) (by rw [hM₀]; omega)
  have h1 := step (M₀ + 1) (by rw [hM₀]; omega) (by rw [hM₀]; omega)
  exact nat_eq_of_pow_eq hu0 hu1 (norm_pos_iff.mpr hrQ) h0 h1

end Key

theorem multiplicity_eq (P Q : ℤ_[p][X]) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ G : ℤ[X], G.Monic →
      ‖resultant (G.map (Int.castRingHom ℤ_[p])) P‖ = ‖resultant (G.map (Int.castRingHom ℤ_[p])) Q‖)
    (π : ℤ_[p][X]) (hπ : π.Monic) (hπp : Prime π) (hm : 0 < π.natDegree) :
    multiplicity π P = multiplicity π Q := by
  have hdeg : (0 : WithBot ℕ) < degree π := by
    rw [degree_eq_natDegree hπ.ne_zero]; exact_mod_cast hm
  have hfP : FiniteMultiplicity π P := finiteMultiplicity_of_degree_pos_of_monic hdeg hπ hP.ne_zero
  have hfQ : FiniteMultiplicity π Q := finiteMultiplicity_of_degree_pos_of_monic hdeg hπ hQ.ne_zero
  obtain ⟨P₁, hP₁, hnP⟩ := hfP.exists_eq_pow_mul_and_not_dvd
  obtain ⟨Q₁, hQ₁, hnQ⟩ := hfQ.exists_eq_pow_mul_and_not_dvd
  have hrP := resultant_ne_zero_of_not_dvd π hπ hπp P₁ hnP
  have hrQ := resultant_ne_zero_of_not_dvd π hπ hπp Q₁ hnQ
  refine pow_eq_of_norm_resultant π hπ hm P₁ Q₁ _ _ hrP hrQ ?_
  intro G hG
  rw [← hP₁, ← hQ₁]
  exact h G hG

theorem exists_monic_prime_dvd (Q : ℤ_[p][X]) (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) :
    ∃ π : ℤ_[p][X], π.Monic ∧ Prime π ∧ 0 < π.natDegree ∧ π ∣ Q := by
  have hQ1 : Q ≠ 1 := by
    intro h1; rw [h1, natDegree_one] at hdeg; exact lt_irrefl 0 hdeg
  have hnu : ¬ IsUnit Q := fun hu => hQ1 (hQ.isUnit_iff.mp hu)
  obtain ⟨q, hq, hqQ⟩ := WfDvdMonoid.exists_irreducible_factor hnu hQ.ne_zero
  obtain ⟨r, hr⟩ := hqQ
  have hlc : q.leadingCoeff * r.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hr, hQ.leadingCoeff]
  have hu : IsUnit q.leadingCoeff := IsUnit.of_mul_eq_one _ hlc
  set c := r.leadingCoeff with hc
  have hcq : c * q.leadingCoeff = 1 := by rw [mul_comm]; exact hlc
  refine ⟨C c * q, monic_C_mul_of_mul_leadingCoeff_eq_one hcq, ?_, ?_, ?_⟩
  · have hcunit : IsUnit (C c) := isUnit_C.mpr (IsUnit.of_mul_eq_one _ hcq)
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ((irreducible_isUnit_mul hcunit).mpr hq)
  · rw [natDegree_C_mul (left_ne_zero_of_mul_eq_one hcq)]
    by_contra h0
    have h0' : q.natDegree = 0 := Nat.le_zero.mp (not_lt.mp h0)
    apply hq.not_isUnit
    rw [eq_C_of_natDegree_eq_zero h0']
    rw [isUnit_C]
    have : q.coeff 0 = q.leadingCoeff := by rw [leadingCoeff, h0']
    rw [this]; exact hu
  · refine ⟨C q.leadingCoeff * r, ?_⟩
    calc Q = q * r := hr
      _ = (C c * C q.leadingCoeff) * (q * r) := by rw [← C_mul, hcq, C_1, one_mul]
      _ = C c * q * (C q.leadingCoeff * r) := by ring

theorem eq_of_forall_multiplicity_eq :
    ∀ (n : ℕ) (P Q : ℤ_[p][X]), P.natDegree = n → P.Monic → Q.Monic →
      (∀ π : ℤ_[p][X], π.Monic → Prime π → 0 < π.natDegree →
        multiplicity π P = multiplicity π Q) → P = Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro P Q hn hP hQ hmult
  by_cases h0 : P.natDegree = 0
  ·
    have hP1 : P = 1 := hP.natDegree_eq_zero.mp h0
    by_cases hQ0 : Q.natDegree = 0
    · rw [hP1, hQ.natDegree_eq_zero.mp hQ0]
    exfalso
    obtain ⟨π, hπ, hπp, hπd, hπQ⟩ := exists_monic_prime_dvd Q hQ (Nat.pos_of_ne_zero hQ0)
    have h1 := hmult π hπ hπp hπd
    rw [hP1, multiplicity_of_one_right hπp.not_unit] at h1
    exact (Nat.pos_iff_ne_zero.mp (multiplicity_pos_of_dvd hπQ)) h1.symm
  · obtain ⟨π, hπ, hπp, hπd, hπP⟩ := exists_monic_prime_dvd P hP (Nat.pos_of_ne_zero h0)
    have hposP : 0 < multiplicity π P := multiplicity_pos_of_dvd hπP
    have hposQ : 0 < multiplicity π Q := by rw [← hmult π hπ hπp hπd]; exact hposP
    have hπQ : π ∣ Q := dvd_of_multiplicity_pos hposQ
    obtain ⟨P', hP'⟩ := hπP
    obtain ⟨Q', hQ'⟩ := hπQ
    have hP'm : P'.Monic := hπ.of_mul_monic_left (hP' ▸ hP)
    have hQ'm : Q'.Monic := hπ.of_mul_monic_left (hQ' ▸ hQ)
    have hdegP' : P'.natDegree < n := by
      have := hπ.natDegree_mul hP'm
      rw [← hP', hn] at this
      omega
    have hdeg : (0 : WithBot ℕ) < degree π := by
      rw [degree_eq_natDegree hπ.ne_zero]; exact_mod_cast hπd
    have key : P' = Q' := by
      refine IH _ hdegP' P' Q' rfl hP'm hQ'm ?_
      intro ρ hρ hρp hρd
      have hdegρ : (0 : WithBot ℕ) < degree ρ := by
        rw [degree_eq_natDegree hρ.ne_zero]; exact_mod_cast hρd
      have hfP : FiniteMultiplicity ρ (π * P') :=
        finiteMultiplicity_of_degree_pos_of_monic hdegρ hρ (hP' ▸ hP.ne_zero)
      have hfQ : FiniteMultiplicity ρ (π * Q') :=
        finiteMultiplicity_of_degree_pos_of_monic hdegρ hρ (hQ' ▸ hQ.ne_zero)
      have e := hmult ρ hρ hρp hρd
      rw [hP', hQ', multiplicity_mul hρp hfP, multiplicity_mul hρp hfQ] at e
      omega
    rw [hP', hQ', key]

theorem eq_of_forall_norm_resultant_eq (P Q : ℤ_[p][X]) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ G : ℤ[X], G.Monic →
      ‖resultant (G.map (Int.castRingHom ℤ_[p])) P‖ =
        ‖resultant (G.map (Int.castRingHom ℤ_[p])) Q‖) : P = Q :=
  eq_of_forall_multiplicity_eq P.natDegree P Q rfl hP hQ
    (fun π hπ hπp hm => multiplicity_eq P Q hP hQ h π hπ hπp hm)

theorem eq_of_forall_norm_resultant_eq' (P Q : ℤ_[p][X]) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ G : ℤ[X], G.Monic →
      ‖resultant P (G.map (Int.castRingHom ℤ_[p]))‖ =
        ‖resultant Q (G.map (Int.castRingHom ℤ_[p]))‖) : P = Q := by
  refine eq_of_forall_norm_resultant_eq P Q hP hQ fun G hG => ?_
  have e := h G hG
  have h1 : ‖resultant (G.map (Int.castRingHom ℤ_[p])) P‖ =
      ‖resultant P (G.map (Int.castRingHom ℤ_[p]))‖ := by
    rw [resultant_comm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h2 : ‖resultant (G.map (Int.castRingHom ℤ_[p])) Q‖ =
      ‖resultant Q (G.map (Int.castRingHom ℤ_[p]))‖ := by
    rw [resultant_comm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [h1, h2, e]

theorem eq_of_forall_norm_resultant_eq_all (P Q : ℤ_[p][X]) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ G : ℤ[X],
      ‖resultant (G.map (Int.castRingHom ℤ_[p])) P‖ =
        ‖resultant (G.map (Int.castRingHom ℤ_[p])) Q‖) : P = Q :=
  eq_of_forall_norm_resultant_eq P Q hP hQ fun G _ => h G

end P2mResNorm

namespace P2mKerCharpoly

variable {p : ℕ} [Fact p.Prime]

section Rep

variable (p) (M : Type) [AddCommGroup M]

noncomputable def repRingHom : Module.End ℤ M →+* Module.End ℤ_[p] (TateModule p M) where
  toFun := TateModule.rep p M (Module.End ℤ M)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [TateModule.rep_apply]
  map_add' f g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp only [TateModule.rep_apply, LinearMap.add_apply, Module.End.smul_def]
    rfl

variable {p M}

@[scoped simp] theorem repRingHom_apply (f : Module.End ℤ M) :
    repRingHom p M f = TateModule.rep p M (Module.End ℤ M) f := rfl

theorem rep_aeval (f : Module.End ℤ M) (G : ℤ[X]) :
    TateModule.rep p M (Module.End ℤ M) (aeval f G) =
      aeval (TateModule.rep p M (Module.End ℤ M) f) (G.map (Int.castRingHom ℤ_[p])) := by
  rw [← repRingHom_apply, ← repRingHom_apply]
  have h1 : (repRingHom p M) (aeval f G) = aeval ((repRingHom p M) f) G :=
    (Polynomial.aeval_algHom_apply ((repRingHom p M).toIntAlgHom) f G).symm
  rw [h1]
  have : (Int.castRingHom ℤ_[p]) = algebraMap ℤ ℤ_[p] := RingHom.ext_int _ _
  rw [this, aeval_map_algebraMap]

end Rep

section DetAeval

variable {r : ℕ}

theorem det_aeval_prod_X_sub_C {L : Type*} [Field L] (B : Matrix (Fin r) (Fin r) L)
    (s : Multiset L) :
    (aeval B (s.map (fun γ => X - C γ)).prod).det =
      (s.map fun γ => (-1 : L) ^ r * B.charpoly.eval γ).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Matrix.det_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]
    congr 1
    have h1 : aeval B (X - C a) = -(Matrix.scalar (Fin r) a - B) := by
      rw [map_sub, aeval_X, aeval_C, neg_sub]; rfl
    rw [h1, Matrix.det_neg, Fintype.card_fin, Matrix.eval_charpoly]

theorem det_aeval_eq_of_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (B : Matrix (Fin r) (Fin r) L) (G : L[X]) (hG : G.Monic) :
    (aeval B G).det = (-1) ^ (r * G.natDegree) * resultant G B.charpoly := by
  have hsplit : G.Splits := IsAlgClosed.splits G
  have hχdeg : B.charpoly.natDegree = r := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

  have hres : resultant G B.charpoly = (G.roots.map B.charpoly.eval).prod := by
    have := resultant_eq_prod_eval G B.charpoly r (le_of_eq hχdeg) hsplit
    rw [hG.leadingCoeff, one_pow, one_mul] at this
    rw [← this, hχdeg]

  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hG]
  rw [det_aeval_prod_X_sub_C, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    hres, hsplit.natDegree_eq_card_roots, pow_mul]

theorem det_aeval_eq (B : Matrix (Fin r) (Fin r) ℤ_[p]) (G : ℤ_[p][X]) (hG : G.Monic) :
    (aeval B G).det = (-1) ^ (r * G.natDegree) * resultant G B.charpoly := by
  set L := AlgebraicClosure ℚ_[p]
  set ι : ℤ_[p] →+* L := (algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p]) with hι
  have hinj : Function.Injective ι :=
    (algebraMap ℚ_[p] L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  apply hinj

  have hL : ι (aeval B G).det = (aeval (B.map ι) (G.map ι)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    letI : Algebra ℤ_[p] L := ι.toAlgebra
    have hcomp : (algebraMap L (Matrix (Fin r) (Fin r) L)).comp ι =
        (ι.mapMatrix).comp (algebraMap ℤ_[p] (Matrix (Fin r) (Fin r) ℤ_[p])) := by
      ext c i j
      simp [Matrix.algebraMap_matrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      split_ifs <;> simp
    have := Polynomial.map_aeval_eq_aeval_map hcomp G B
    rw [RingHom.mapMatrix_apply] at this
    exact this
  rw [hL, det_aeval_eq_of_isAlgClosed (B.map ι) (G.map ι) (hG.map ι), map_mul, map_pow, map_neg,
    map_one, hG.natDegree_map, Matrix.charpoly_map]
  congr 1
  rw [← resultant_map_map G B.charpoly G.natDegree B.charpoly.natDegree ι]
  rw [(Matrix.charpoly_monic B).natDegree_map]

end DetAeval

theorem eq_zero_of_smul_coprime {M : Type*} [AddCommGroup M] {m n : ℕ} (h : Nat.Coprime m n)
    {x : M} (hm : (m : ℤ) • x = 0) (hn : (n : ℤ) • x = 0) : x = 0 := by
  have hg : Int.gcd (m : ℤ) (n : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact h
  have hb := Int.gcd_eq_gcd_ab (m : ℤ) (n : ℤ)
  rw [hg] at hb
  have hb' : (1 : ℤ) = (m : ℤ) * Int.gcdA m n + (n : ℤ) * Int.gcdB m n := by exact_mod_cast hb
  have : (1 : ℤ) • x = 0 := by
    rw [hb', add_smul, mul_comm, mul_smul, hm, smul_zero, mul_comm, mul_smul, hn, smul_zero,
      add_zero]
  rwa [one_smul] at this

theorem norm_intCast_eq (k : ℤ) (hk : k ≠ 0) :
    ‖(k : ℤ_[p])‖ = (p : ℝ) ^ (-(k.natAbs.factorization p : ℤ)) := by

  have hnorm : ‖(k : ℤ_[p])‖ = ‖((k.natAbs : ℕ) : ℤ_[p])‖ := by
    rcases Int.natAbs_eq k with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      rw [Int.cast_neg, norm_neg]
      simp
  rw [hnorm]
  set n := k.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hk

  have hdecomp : p ^ (n.factorization p) * (n / p ^ (n.factorization p)) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hndvd : ¬ p ∣ n / p ^ (n.factorization p) := Nat.not_dvd_ordCompl (Fact.out) hn0
  set v := n.factorization p
  set m := n / p ^ v
  have hm : ‖((m : ℕ) : ℤ_[p])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra hlt
    push Not at hlt
    have : ((m : ℤ) : ℤ_[p]) = ((m : ℕ) : ℤ_[p]) := by simp
    rw [← this, PadicInt.norm_int_lt_one_iff_dvd] at hlt
    exact hndvd (by exact_mod_cast hlt)
  rw [← hdecomp, Nat.cast_mul, norm_mul, hm, mul_one, Nat.cast_pow, norm_pow, PadicInt.norm_p,
    ← zpow_natCast, ← zpow_neg_one, ← zpow_mul]
  congr 1
  ring

section Kernel

variable {M : Type} [AddCommGroup M]

theorem not_finite_primaryComponent_of_rep_apply_eq_zero (β : M →+ M)
    (x : TateModule p M) (hx : x ≠ 0)
    (hβx : TateModule.rep p M (Module.End ℤ M) β.toIntLinearMap x = 0) :
    ¬ Finite (AddCommGroup.primaryComponent β.ker p) := by
  intro hfin

  have hx' : ∃ n₀, (x : ℕ → M) n₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (Subtype.ext (funext fun n => by rw [h n]; rfl))
  obtain ⟨n₀, hn₀⟩ := hx'

  have hlev : ∀ n, β ((x : ℕ → M) n) = 0 := by
    intro n
    have := congrArg (fun y : TateModule p M => (y : ℕ → M) n) hβx
    simpa [TateModule.rep_apply, Module.End.smul_def] using this
  have hmem : ∀ n, (⟨(x : ℕ → M) n, (AddMonoidHom.mem_ker).mpr (hlev n)⟩ : β.ker) ∈
      AddCommGroup.primaryComponent β.ker p := by
    intro n
    rw [AddCommGroup.mem_primaryComponent]
    refine ⟨n, Subtype.ext ?_⟩
    show p ^ n • (x : ℕ → M) n = 0
    have := TateModule.torsion x n
    rw [← natCast_zsmul]
    exact_mod_cast this

  let f : ℕ → AddCommGroup.primaryComponent β.ker p := fun k =>
    ⟨⟨(x : ℕ → M) (n₀ + k), (AddMonoidHom.mem_ker).mpr (hlev (n₀ + k))⟩, hmem (n₀ + k)⟩
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm hfab.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
  have heq : (x : ℕ → M) (n₀ + a) = (x : ℕ → M) (n₀ + b) := by
    have := congrArg (fun y : AddCommGroup.primaryComponent β.ker p => ((y : β.ker) : M)) hfab
    exact this

  have hc : ((p ^ (b - a) : ℕ) : ℤ) • (x : ℕ → M) (n₀ + b) = (x : ℕ → M) (n₀ + a) := by
    have := TateModule.compat_pow x (n₀ + a) (b - a)
    rw [show n₀ + a + (b - a) = n₀ + b by omega] at this
    exact this
  rw [← heq] at hc
  have h1 : (((p ^ (b - a) - 1 : ℕ)) : ℤ) • (x : ℕ → M) (n₀ + a) = 0 := by
    have hp1 : 1 ≤ p ^ (b - a) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    rw [Nat.cast_sub hp1, sub_smul, hc, Nat.cast_one, one_smul, sub_self]
  have h2 : ((p ^ (n₀ + a) : ℕ) : ℤ) • (x : ℕ → M) (n₀ + a) = 0 := TateModule.torsion x (n₀ + a)
  have hcop : Nat.Coprime (p ^ (b - a) - 1) (p ^ (n₀ + a)) := by
    apply Nat.Coprime.pow_right
    have hba : 0 < b - a := Nat.sub_pos_of_lt hlt

    have hdvd : p ∣ p ^ (b - a) := dvd_pow_self p hba.ne'
    have hp1 : 1 ≤ p ^ (b - a) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    rw [Nat.Coprime, Nat.gcd_comm]
    have : Nat.gcd p (p ^ (b - a) - 1) ∣ 1 := by
      have h3 : Nat.gcd p (p ^ (b - a) - 1) ∣ p ^ (b - a) :=
        (Nat.gcd_dvd_left _ _).trans hdvd
      have h4 : Nat.gcd p (p ^ (b - a) - 1) ∣ p ^ (b - a) - 1 := Nat.gcd_dvd_right _ _
      have := Nat.dvd_sub h3 h4
      rwa [Nat.sub_sub_self hp1] at this
    exact Nat.dvd_one.mp this
  have hzero := eq_zero_of_smul_coprime hcop h1 h2

  have := TateModule.compat_pow x n₀ a
  rw [hzero, smul_zero] at this
  exact hn₀ this.symm

theorem not_finite_primaryComponent_of_det_eq_zero {r : ℕ}
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) (β : M →+ M)
    (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) β.toIntLinearMap) = 0) :
    ¬ Finite (AddCommGroup.primaryComponent β.ker p) := by
  classical
  set A := TateModule.rep p M (Module.End ℤ M) β.toIntLinearMap with hA
  have hdetM : (LinearMap.toMatrix b b A).det = 0 := by rw [LinearMap.det_toMatrix]; exact hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetM
  set x : TateModule p M := b.equivFun.symm v with hxdef
  have hrepr : b.repr x = Finsupp.equivFunOnFinite.symm v := by
    rw [hxdef, Module.Basis.equivFun_symm_apply, map_sum]
    ext i
    simp [Finsupp.single_apply, Finset.sum_ite_eq']
  have hx : x ≠ 0 := by
    intro h0
    apply hv
    have : b.equivFun x = v := by rw [hxdef]; exact b.equivFun.apply_symm_apply v
    rw [← this, h0, map_zero]
  have hAx : A x = 0 := by
    have h := LinearMap.toMatrix_mulVec_repr b b A x
    have hv' : ⇑(b.repr x) = v := by rw [hrepr]; rfl
    rw [hv', hMv] at h
    have : b.repr (A x) = 0 := by
      ext i
      have := congrFun h i
      simpa using this.symm
    exact b.repr.map_eq_zero_iff.mp this
  exact not_finite_primaryComponent_of_rep_apply_eq_zero β x hx hAx

end Kernel

section Main

variable {M : Type} [AddCommGroup M]

theorem norm_resultant_charpoly_eq (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (P : ℤ[X]) (hP : P.Monic)
    (hker : ∀ G : ℤ[X], G.Monic → G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p) =
        p ^ ((G.resultant P).natAbs.factorization p))
    (hker0 : ∀ G : ℤ[X], G.Monic → G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p))
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) (G : ℤ[X]) (hG : G.Monic) :
    ‖resultant (G.map (Int.castRingHom ℤ_[p]))
        (LinearMap.toMatrix b b (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).charpoly‖ =
      ‖resultant (G.map (Int.castRingHom ℤ_[p])) (P.map (Int.castRingHom ℤ_[p]))‖ := by
  classical
  set A := TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap with hA
  set B := LinearMap.toMatrix b b A with hB
  set Ĝ := G.map (Int.castRingHom ℤ_[p]) with hĜ
  set β : M →+ M := (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom with hβ
  have hβlin : β.toIntLinearMap = Polynomial.aeval (R := ℤ) α.toIntLinearMap G :=
    LinearMap.ext fun _ => rfl

  set d := LinearMap.det (TateModule.rep p M (Module.End ℤ M) β.toIntLinearMap) with hd
  have hrepβ : TateModule.rep p M (Module.End ℤ M) β.toIntLinearMap = aeval A Ĝ := by
    rw [hβlin, rep_aeval]
  have hmat : LinearMap.toMatrix b b (aeval A Ĝ) = aeval B Ĝ := by
    have := Polynomial.aeval_algHom_apply
      ((LinearMap.toMatrixAlgEquiv b).toAlgHom :
        Module.End ℤ_[p] (TateModule p M) →ₐ[ℤ_[p]] Matrix (Fin r) (Fin r) ℤ_[p]) A Ĝ
    exact this.symm
  have hdres : d = (-1) ^ (r * Ĝ.natDegree) * resultant Ĝ B.charpoly := by
    rw [hd, hrepβ, ← LinearMap.det_toMatrix b, hmat, det_aeval_eq B Ĝ (hG.map _)]
  have hnormd : ‖d‖ = ‖resultant Ĝ B.charpoly‖ := by
    rw [hdres, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

  have hresP : resultant Ĝ (P.map (Int.castRingHom ℤ_[p])) = ((G.resultant P : ℤ) : ℤ_[p]) := by
    show resultant Ĝ (P.map (Int.castRingHom ℤ_[p])) Ĝ.natDegree (P.map (Int.castRingHom ℤ_[p])).natDegree = _
    rw [hĜ, hG.natDegree_map, hP.natDegree_map, resultant_map_map, eq_intCast]
  rw [← hnormd, hresP]
  by_cases hres : G.resultant P = 0
  ·
    have hinf := hker0 G hG hres
    have hd0 : d = 0 := by
      by_contra hd0
      apply hinf
      have hcardk := TateModule.natCard_primaryComponent_ker_eq_pow_valuation_det p r hcard β hd0
      apply Nat.finite_of_card_ne_zero
      rw [hcardk]
      exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    rw [hd0, hres, Int.cast_zero]
  ·
    have hcardG := hker G hG hres
    have hfin : Finite (AddCommGroup.primaryComponent β.ker p) := by
      apply Nat.finite_of_card_ne_zero
      rw [hcardG]
      exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    have hd0 : d ≠ 0 := by
      intro hd0
      exact not_finite_primaryComponent_of_det_eq_zero b β hd0 hfin
    have hcardk := TateModule.natCard_primaryComponent_ker_eq_pow_valuation_det p r hcard β hd0
    rw [hcardG] at hcardk
    have hval : (G.resultant P).natAbs.factorization p = d.valuation :=
      Nat.pow_right_injective (Fact.out : p.Prime).two_le hcardk
    rw [PadicInt.norm_eq_zpow_neg_valuation hd0, norm_intCast_eq _ hres, hval]

theorem charpoly_toMatrix_rep_eq (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (P : ℤ[X]) (hP : P.Monic)
    (hker : ∀ G : ℤ[X], G.Monic → G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p) =
        p ^ ((G.resultant P).natAbs.factorization p))
    (hker0 : ∀ G : ℤ[X], G.Monic → G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p))
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) :
    (LinearMap.toMatrix b b (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).charpoly =
      P.map (Int.castRingHom ℤ_[p]) :=
  P2mResNorm.eq_of_forall_norm_resultant_eq _ _ (Matrix.charpoly_monic _) (hP.map _)
    (fun G hG => norm_resultant_charpoly_eq r hcard α P hP hker hker0 b G hG)

end Main

end P2mKerCharpoly
p2m_reactivate "P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval.P2mKerCharpoly"

theorem solution
    (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (P : Polynomial ℤ) (hP : P.Monic)
    (hker : ∀ G : Polynomial ℤ, G.Monic → G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p) =
        p ^ ((G.resultant P).natAbs.factorization p))
    (hker0 : ∀ G : Polynomial ℤ, G.Monic → G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p))
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) :
    (LinearMap.toMatrix b b (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).charpoly =
      P.map (Int.castRingHom ℤ_[p]) :=
  P2mKerCharpoly.charpoly_toMatrix_rep_eq r hcard α P hP hker hker0 b

end S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval
end P2MW
export P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval (solution)
