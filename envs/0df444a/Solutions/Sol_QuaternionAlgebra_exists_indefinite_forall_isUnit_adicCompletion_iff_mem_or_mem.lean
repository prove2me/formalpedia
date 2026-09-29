-- Prove2me | solution 1 for QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c2b203d2-ca8e-51c6-88b6-57578ff665be

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
import Theorems.Thm_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem
import Theorems.Thm_Rat_exists_sq_eq_adicCompletion_of_eight_dvd_sub_one
import Theorems.Thm_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
import Theorems.Thm_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
import Theorems.Thm_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace IModelCd1

def Iso {F : Type*} [Field F] (A B : F) : Prop :=
  ∃ z x y : F, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - A * x ^ 2 - B * y ^ 2 = 0

theorem iso_symm {F : Type*} [Field F] {A B : F} (h : Iso A B) : Iso B A := by
  obtain ⟨z, x, y, hne, h0⟩ := h
  exact ⟨z, y, x, fun hh => hne ⟨hh.1, hh.2.2, hh.2.1⟩, by linear_combination h0⟩

theorem iso_map_of_injective {F L φ : Type*} [Field F] [Field L] [FunLike φ F L]
    [RingHomClass φ F L] (f : φ) (hf : Function.Injective f) {A B : F} (h : Iso A B) :
    Iso (f A) (f B) := by
  obtain ⟨z, x, y, hnt, heq⟩ := h
  refine ⟨f z, f x, f y, ?_, by simpa [map_sub, map_mul, map_pow] using congrArg f heq⟩
  rintro ⟨hz, hx, hy⟩
  exact hnt ⟨(map_eq_zero_iff f hf).mp hz, (map_eq_zero_iff f hf).mp hx,
    (map_eq_zero_iff f hf).mp hy⟩

private local instance instFactPrimesIM (P : Nat.Primes) : Fact P.1.Prime := ⟨P.2⟩

theorem iso_adicCompletion_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℚ) :
    Iso (algebraMap ℚ (v.adicCompletion ℚ) a) (algebraMap ℚ (v.adicCompletion ℚ) b) ↔
      Iso (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])
        (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) := by
  set e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v with he
  have ha : (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) = algebraMap ℚ _ a :=
    (eq_ratCast _ a).symm
  have hb : (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) = algebraMap ℚ _ b :=
    (eq_ratCast _ b).symm
  rw [ha, hb]
  constructor
  · intro h
    have := iso_map_of_injective e e.injective h
    rwa [AlgEquivClass.commutes, AlgEquivClass.commutes] at this
  · intro h
    have := iso_map_of_injective e.symm e.symm.injective h
    rwa [AlgEquivClass.commutes, AlgEquivClass.commutes] at this

theorem primesEquiv_eq (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p := by
  show Rat.HeightOneSpectrum.natGenerator v = p
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rwa [map_natCast] at this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hdvd

theorem aniso_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℚ) :
    (∀ z x y : v.adicCompletion ℚ, z ^ 2 - (a : v.adicCompletion ℚ) * x ^ 2 - (b : v.adicCompletion ℚ) * y ^ 2 = 0 →
        z = 0 ∧ x = 0 ∧ y = 0) ↔
      ¬ Iso (algebraMap ℚ (v.adicCompletion ℚ) a) (algebraMap ℚ (v.adicCompletion ℚ) b) := by
  rw [eq_ratCast, eq_ratCast]
  constructor
  · rintro h ⟨z, x, y, hne, h0⟩
    exact hne (h z x y h0)
  · intro h z x y h0
    by_contra hne
    exact h ⟨z, x, y, hne, h0⟩

theorem exists_prime_aux (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hq2 : q ≠ 2) (hq'2 : q' ≠ 2)
    (hqq' : q ≠ q') :
    ∃ ℓ : ℕ, ℓ.Prime ∧ q < ℓ ∧ q' < ℓ ∧ ℓ % 8 = 1 ∧
      ¬ IsSquare ((ℓ : ℤ) : ZMod q) ∧ ¬ IsSquare ((ℓ : ℤ) : ZMod q') := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  have hch : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  have hch' : ringChar (ZMod q') ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq'2
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hch
  obtain ⟨c', hc'⟩ := FiniteField.exists_nonsquare hch'
  have hc0 : c ≠ 0 := fun h => hc (h ▸ IsSquare.zero)
  have hc'0 : c' ≠ 0 := fun h => hc' (h ▸ IsSquare.zero)
  have hqq'cop : Nat.Coprime q q' := (Nat.coprime_primes hq hq').mpr hqq'
  have h8cop : Nat.Coprime 8 (q * q') := by
    have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
    have h2q' : Nat.Coprime 2 q' := (Nat.coprime_primes Nat.prime_two hq').mpr (Ne.symm hq'2)
    simpa using (Nat.Coprime.mul_right h2q h2q').pow_left 3
  let e₁ := ZMod.chineseRemainder h8cop
  let e₂ := ZMod.chineseRemainder hqq'cop
  let a₀ : ZMod (8 * (q * q')) := e₁.symm (1, e₂.symm (c, c'))
  have ha₀ : IsUnit a₀ := by
    have h2 : IsUnit (e₂.symm (c, c')) :=
      (Prod.isUnit_iff.mpr ⟨isUnit_iff_ne_zero.mpr hc0, isUnit_iff_ne_zero.mpr hc'0⟩).map e₂.symm
    exact (Prod.isUnit_iff.mpr ⟨isUnit_one, h2⟩).map e₁.symm
  haveI : NeZero (8 * (q * q')) :=
    ⟨Nat.mul_ne_zero (by norm_num) (Nat.mul_ne_zero hq.ne_zero hq'.ne_zero)⟩
  obtain ⟨ℓ, hltℓ, hℓ, hℓa⟩ := Nat.forall_exists_prime_gt_and_eq_mod ha₀ (q + q')
  have h₁ : e₁ (ℓ : ZMod (8 * (q * q'))) = ((1 : ZMod 8), e₂.symm (c, c')) := by
    rw [hℓa]; exact e₁.apply_symm_apply _
  rw [map_natCast] at h₁
  have h8 : (ℓ : ZMod 8) = 1 := by simpa using congrArg Prod.fst h₁
  have hℓqq : (ℓ : ZMod (q * q')) = e₂.symm (c, c') := by simpa using congrArg Prod.snd h₁
  have h₂ : e₂ (ℓ : ZMod (q * q')) = (c, c') := by rw [hℓqq]; exact e₂.apply_symm_apply _
  rw [map_natCast] at h₂
  have hcq : (ℓ : ZMod q) = c := by simpa using congrArg Prod.fst h₂
  have hcq' : (ℓ : ZMod q') = c' := by simpa using congrArg Prod.snd h₂
  refine ⟨ℓ, hℓ, by omega, by omega, ?_, ?_, ?_⟩
  · have := (ZMod.natCast_eq_natCast_iff' ℓ 1 8).mp (by simpa using h8)
    simpa using this
  · rw [Int.cast_natCast, hcq]; exact hc
  · rw [Int.cast_natCast, hcq']; exact hc'

theorem iso_at_two (ℓ : ℕ) (n : ℤ) (hℓ8 : ℓ % 8 = 1) (w : HeightOneSpectrum (𝓞 ℚ))
    (hw : (2 : 𝓞 ℚ) ∈ w.asIdeal) :
    Iso (algebraMap ℚ (w.adicCompletion ℚ) (ℓ : ℚ)) (algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ)) := by
  obtain ⟨s, hs⟩ := Rat.exists_sq_eq_adicCompletion_of_eight_dvd_sub_one w hw (ℓ : ℤ) (by omega)
  refine ⟨s, 1, 0, fun hh => one_ne_zero hh.2.1, ?_⟩
  rw [hs, Int.cast_natCast]
  ring

theorem iso_at_ell (ℓ q q' : ℕ) (hℓ : ℓ.Prime) (hq : q.Prime) (hq' : q'.Prime) (hq2 : q ≠ 2) (hq'2 : q' ≠ 2)
    (hqℓ : q < ℓ) (hq'ℓ : q' < ℓ) (hℓ8 : ℓ % 8 = 1)
    (hnq : ¬ IsSquare ((ℓ : ℤ) : ZMod q)) (hnq' : ¬ IsSquare ((ℓ : ℤ) : ZMod q'))
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (ℓ : 𝓞 ℚ) ∈ w.asIdeal) :
    Iso (algebraMap ℚ (w.adicCompletion ℚ) (ℓ : ℚ)) (algebraMap ℚ (w.adicCompletion ℚ) ((q * q' : ℤ) : ℚ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓ4 : ℓ % 4 = 1 := by omega
  have hndvd : ¬ (ℓ : ℤ) ∣ (q * q' : ℤ) := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd h with h | h
    · have h' : ℓ ∣ q := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hℓ hq).mp h'
      omega
    · have h' : ℓ ∣ q' := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hℓ hq').mp h'
      omega

  have hleg : legendreSym ℓ (q * q' : ℤ) = 1 := by
    rw [legendreSym.mul, ← legendreSym.quadratic_reciprocity_one_mod_four hℓ4 hq2,
      ← legendreSym.quadratic_reciprocity_one_mod_four hℓ4 hq'2,
      (legendreSym.eq_neg_one_iff q).mpr hnq, (legendreSym.eq_neg_one_iff q').mpr hnq']
    norm_num
  have h0 : ((q * q' : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hndvd
  have hsq : IsSquare ((q * q' : ℤ) : ZMod ℓ) := (legendreSym.eq_one_iff ℓ h0).mp hleg
  obtain ⟨s, hs⟩ :=
    Rat.exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd ℓ hℓ hℓ2 w hw (q * q' : ℤ) hndvd hsq
  refine ⟨s, 0, 1, fun hh => one_ne_zero hh.2.2, ?_⟩
  rw [hs]
  ring

theorem iso_generic (ℓ : ℕ) (n : ℤ) (w : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ w.asIdeal)
    (hℓw : (ℓ : 𝓞 ℚ) ∉ w.asIdeal) (hnw : ((n : ℤ) : 𝓞 ℚ) ∉ w.asIdeal) :
    Iso (algebraMap ℚ (w.adicCompletion ℚ) (ℓ : ℚ)) (algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ)) := by
  have hℓw' : (((ℓ : ℤ)) : 𝓞 ℚ) ∉ w.asIdeal := by rwa [Int.cast_natCast]
  have h := Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem (ℓ : ℤ) n w h2 hℓw' hnw
  rw [Int.cast_natCast] at h
  exact h

theorem isSquare_zmod_of_isSquare_padic {p : ℕ} [Fact p.Prime] {u : ℤ} (hu : ¬ (p : ℤ) ∣ u)
    (h : IsSquare ((u : ℤ) : ℚ_[p])) : IsSquare ((u : ℤ) : ZMod p) := by
  obtain ⟨w, hw⟩ := h
  have hvn : ‖(u : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one u) (not_lt.mp fun h ↦ hu (Padic.norm_intCast_lt_one_iff.mp h))
  have hwn : ‖w‖ ≤ 1 := by
    have : ‖w‖ * ‖w‖ = 1 := by rw [← norm_mul, ← hw, hvn]
    nlinarith [norm_nonneg w]
  set W : ℤ_[p] := ⟨w, hwn⟩
  have hVW : (u : ℤ_[p]) = W * W := by
    apply Subtype.val_injective
    simp only [PadicInt.coe_mul, PadicInt.coe_intCast, W]
    exact hw
  have hres : PadicInt.toZMod ((u : ℤ_[p])) = (u : ZMod p) := map_intCast _ u
  refine ⟨PadicInt.toZMod W, ?_⟩
  rw [← hres, hVW, map_mul]

theorem aniso_at (p m ℓ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hm : m.Prime) (hpm : p ≠ m) (hℓ : ℓ.Prime)
    (hpℓ : p < ℓ) (hnr : ¬ IsSquare ((ℓ : ℤ) : ZMod p))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    ¬ Iso (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) (algebraMap ℚ (v.adicCompletion ℚ) ((p * m : ℤ) : ℚ)) := by
  have hP := primesEquiv_eq p hp v hv
  subst hP
  set P : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v with hPdef
  rw [iso_adicCompletion_iff]
  intro hiso
  have hcastA : (((ℓ : ℚ)) : ℚ_[P]) = ((ℓ : ℤ) : ℚ_[P]) := by push_cast; rfl
  have hcastB : ((((P : ℕ) * m : ℤ) : ℚ) : ℚ_[P]) = ((P : ℕ) : ℚ_[P]) * (m : ℚ_[P]) := by push_cast; rfl
  rw [hcastA, hcastB] at hiso
  have hPm : ¬ ((P : ℕ) : ℤ) ∣ (m : ℤ) := by
    intro h
    have h' : (P : ℕ) ∣ m := by exact_mod_cast h
    exact hpm ((Nat.prime_dvd_prime_iff_eq hp hm).mp h')
  have hPℓ : ¬ ((P : ℕ) : ℤ) ∣ (ℓ : ℤ) := by
    intro h
    have h' : (P : ℕ) ∣ ℓ := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hp hℓ).mp h'
    omega
  have hmU : ‖(m : ℚ_[P])‖ = 1 := by
    have := le_antisymm (Padic.norm_int_le_one (p := P) (m : ℤ))
      (not_lt.mp fun h ↦ hPm (Padic.norm_intCast_lt_one_iff.mp h))
    rwa [Int.cast_natCast] at this
  have hℓU : ‖((ℓ : ℤ) : ℚ_[P])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun h ↦ hPℓ (Padic.norm_intCast_lt_one_iff.mp h))
  have hiso' : ∃ z x y : ℚ_[P], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (((P : ℕ) : ℚ_[P]) * (m : ℚ_[P])) * x ^ 2 - ((ℓ : ℤ) : ℚ_[P]) * y ^ 2 = 0 :=
    iso_symm hiso
  have hsqP : IsSquare ((ℓ : ℤ) : ℚ_[P]) :=
    (Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two P hp2 (m : ℚ_[P]) ((ℓ : ℤ) : ℚ_[P])
      hmU hℓU).mp hiso'
  exact hnr (isSquare_zmod_of_isSquare_padic hPℓ hsqP)

theorem main (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hqq' : q ≠ q') (hq2 : q ≠ 2) (hq'2 : q' ≠ 2) :
    ∃ a b : ℚ, (0 < a ∨ 0 < b) ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
        ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) := by
  haveI hcz : ∀ w : HeightOneSpectrum (𝓞 ℚ), CharZero (w.adicCompletion ℚ) := fun w =>
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  obtain ⟨ℓ, hℓ, hqℓ, hq'ℓ, hℓ8, hnq, hnq'⟩ := exists_prime_aux q q' hq hq' hq2 hq'2 hqq'
  refine ⟨(ℓ : ℚ), ((q * q' : ℤ) : ℚ), Or.inl (by exact_mod_cast hℓ.pos), fun v => ?_⟩
  have hqq'0 : (q * q' : ℤ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hq.ne_zero hq'.ne_zero
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero,
    QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero _ _ _
      (by haveI := hcz v; rw [Rat.cast_natCast]; exact_mod_cast hℓ.ne_zero)
      (by haveI := hcz v; rw [Rat.cast_intCast]; exact_mod_cast hqq'0),
    aniso_iff]
  constructor
  · intro hnot
    by_contra hneither
    apply hnot
    have hvq : (q : 𝓞 ℚ) ∉ v.asIdeal := fun h => hneither (Or.inl h)
    have hvq' : (q' : 𝓞 ℚ) ∉ v.asIdeal := fun h => hneither (Or.inr h)
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · exact iso_at_two ℓ (q * q' : ℤ) hℓ8 v h2
    · by_cases hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal
      · exact iso_at_ell ℓ q q' hℓ hq hq' hq2 hq'2 hqℓ hq'ℓ hℓ8 hnq hnq' v hℓv
      · refine iso_generic ℓ (q * q' : ℤ) v h2 hℓv ?_
        intro h
        push_cast at h
        rcases v.isPrime.mem_or_mem h with h | h
        · exact hvq h
        · exact hvq' h
  · rintro (hvq | hvq')
    · exact aniso_at q q' ℓ hq hq2 hq' hqq' hℓ hqℓ hnq v hvq
    · have e : ((q * q' : ℤ) : ℚ) = ((q' * q : ℤ) : ℚ) := by push_cast; ring
      rw [e]
      exact aniso_at q' q ℓ hq' hq'2 hq (Ne.symm hqq') hℓ hq'ℓ hnq' v hvq'

end IModelCd1

namespace IModelTwo

open IModelCd1

theorem exists_prime_aux₂ (q' : ℕ) (hq' : q'.Prime) (hq'2 : q' ≠ 2) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ q' < ℓ ∧ ℓ % 8 = 5 ∧ ¬ IsSquare ((ℓ : ℤ) : ZMod q') := by
  haveI : Fact q'.Prime := ⟨hq'⟩
  have hchar : ringChar (ZMod q') ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq'2
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hchar
  have hc0 : c ≠ 0 := fun h => hc (h ▸ IsSquare.zero)
  have hcop : Nat.Coprime 8 q' := by
    have h2q : Nat.Coprime 2 q' := (Nat.coprime_primes Nat.prime_two hq').mpr (Ne.symm hq'2)
    simpa using h2q.pow_left 3
  let e := ZMod.chineseRemainder hcop
  let a₀ : ZMod (8 * q') := e.symm (5, c)
  have ha₀ : IsUnit a₀ := by
    have h5 : IsUnit (5 : ZMod 8) := by decide
    have : IsUnit ((5 : ZMod 8), c) := Prod.isUnit_iff.mpr ⟨h5, isUnit_iff_ne_zero.mpr hc0⟩
    exact this.map e.symm
  haveI : NeZero (8 * q') := ⟨Nat.mul_ne_zero (by norm_num) hq'.ne_zero⟩
  obtain ⟨ℓ, hq'ℓ, hℓ, hℓa⟩ := Nat.forall_exists_prime_gt_and_eq_mod ha₀ q'
  have her : e (ℓ : ZMod (8 * q')) = ((5 : ZMod 8), c) := by
    rw [hℓa]; exact e.apply_symm_apply _
  rw [map_natCast] at her
  have h8 : (ℓ : ZMod 8) = 5 := by simpa using congrArg Prod.fst her
  have hqc : (ℓ : ZMod q') = c := by simpa using congrArg Prod.snd her
  refine ⟨ℓ, hℓ, hq'ℓ, ?_, ?_⟩
  · have := (ZMod.natCast_eq_natCast_iff' ℓ 5 8).mp (by simpa using h8)
    simpa using this
  · rw [Int.cast_natCast, hqc]; exact hc

theorem iso_at_ell₂ (ℓ q' : ℕ) (hℓ : ℓ.Prime) (hq' : q'.Prime) (hq'2 : q' ≠ 2) (hq'ℓ : q' < ℓ) (hℓ8 : ℓ % 8 = 5)
    (hnq' : ¬ IsSquare ((ℓ : ℤ) : ZMod q'))
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (ℓ : 𝓞 ℚ) ∈ w.asIdeal) :
    Iso (algebraMap ℚ (w.adicCompletion ℚ) (ℓ : ℚ)) (algebraMap ℚ (w.adicCompletion ℚ) ((2 * q' : ℤ) : ℚ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓ4 : ℓ % 4 = 1 := by omega
  have hndvd : ¬ (ℓ : ℤ) ∣ (2 * q' : ℤ) := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd h with h | h
    · have h' : ℓ ∣ 2 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h'
      omega
    · have h' : ℓ ∣ q' := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hℓ hq').mp h'
      omega

  have h2 : legendreSym ℓ 2 = -1 := by
    rw [legendreSym.at_two hℓ2, ZMod.χ₈_nat_eq_if_mod_eight]
    have h1 : ℓ % 2 ≠ 0 := by omega
    have h3 : ¬ (ℓ % 8 = 1 ∨ ℓ % 8 = 7) := by omega
    rw [if_neg h1, if_neg h3]
  have hleg : legendreSym ℓ (2 * q' : ℤ) = 1 := by
    rw [legendreSym.mul, ← legendreSym.quadratic_reciprocity_one_mod_four hℓ4 hq'2,
      (legendreSym.eq_neg_one_iff q').mpr hnq']
    rw [h2]; norm_num
  have h0 : ((2 * q' : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hndvd
  have hsq : IsSquare ((2 * q' : ℤ) : ZMod ℓ) := (legendreSym.eq_one_iff ℓ h0).mp hleg
  obtain ⟨s, hs⟩ :=
    Rat.exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd ℓ hℓ hℓ2 w hw (2 * q' : ℤ) hndvd hsq
  refine ⟨s, 0, 1, fun hh => one_ne_zero hh.2.2, ?_⟩
  rw [hs]
  ring

theorem aniso_at_two₂ (ℓ q' : ℕ) (hℓ : ℓ.Prime) (hq' : q'.Prime) (hq'2 : q' ≠ 2) (hℓ8 : ℓ % 8 = 5)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    ¬ Iso (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) (algebraMap ℚ (v.adicCompletion ℚ) ((2 * q' : ℤ) : ℚ)) := by
  rw [iso_adicCompletion_iff]
  have hP2 : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = 2 :=
    primesEquiv_eq 2 Nat.prime_two v (by exact_mod_cast hv)
  generalize Rat.HeightOneSpectrum.primesEquiv v = P at hP2 ⊢
  obtain ⟨pv, pp⟩ := P
  simp only at hP2
  subst hP2

  change ¬ Iso (((ℓ : ℚ)) : ℚ_[2]) ((((2 * q' : ℤ) : ℚ)) : ℚ_[2])
  intro hiso
  have hcastA : (((ℓ : ℚ)) : ℚ_[2]) = ((ℓ : ℤ) : ℚ_[2]) := by push_cast; rfl
  have hcastB : ((((2 * q' : ℤ) : ℚ)) : ℚ_[2]) = 2 * ((q' : ℤ) : ℚ_[2]) := by push_cast; rfl
  rw [hcastA, hcastB] at hiso
  have hq'U : ‖((q' : ℤ) : ℚ_[2])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun h ↦ ?_)
    have hd : ((2 : ℕ) : ℤ) ∣ (q' : ℤ) := Padic.norm_intCast_lt_one_iff.mp h
    have : 2 ∣ q' := by exact_mod_cast hd
    exact hq'2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq').mp this).symm
  have hℓU : ‖((ℓ : ℤ) : ℚ_[2])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun h ↦ ?_)
    have hd : ((2 : ℕ) : ℤ) ∣ (ℓ : ℤ) := Padic.norm_intCast_lt_one_iff.mp h
    omega
  have hiso' : ∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (2 * ((q' : ℤ) : ℚ_[2])) * x ^ 2 - ((ℓ : ℤ) : ℚ_[2]) * y ^ 2 = 0 :=
    iso_symm hiso
  have hcrit := (Padic.exists_ternary_isotropic_two_mul_iff_of_norm_eq_one ((q' : ℤ) : ℚ_[2]) ((ℓ : ℤ) : ℚ_[2])
    hq'U hℓU).mp hiso'

  rcases hcrit with h | h
  · have h' : ‖(((ℓ - 1 : ℤ)) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by push_cast at h ⊢; exact h
    have hd := (Padic.norm_int_le_pow_iff_dvd (ℓ - 1 : ℤ) 3).mp (by exact_mod_cast h')
    omega
  · have h' : ‖(((2 * q' + ℓ - 1 : ℤ)) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by push_cast at h ⊢; exact h
    have hd := (Padic.norm_int_le_pow_iff_dvd (2 * q' + ℓ - 1 : ℤ) 3).mp (by exact_mod_cast h')
    have hodd : q' % 2 = 1 := (Nat.Prime.eq_two_or_odd hq').resolve_left hq'2
    omega

theorem main₂ (q' : ℕ) (hq' : q'.Prime) (hq'2 : q' ≠ 2) :
    ∃ a b : ℚ, (0 < a ∨ 0 < b) ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
        ((2 : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) := by
  haveI hcz : ∀ w : HeightOneSpectrum (𝓞 ℚ), CharZero (w.adicCompletion ℚ) := fun w =>
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  obtain ⟨ℓ, hℓ, hq'ℓ, hℓ8, hnq'⟩ := exists_prime_aux₂ q' hq' hq'2
  refine ⟨(ℓ : ℚ), ((2 * q' : ℤ) : ℚ), Or.inl (by exact_mod_cast hℓ.pos), fun v => ?_⟩
  have h2q'0 : (2 * q' : ℤ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero two_ne_zero hq'.ne_zero
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero,
    QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero _ _ _
      (by haveI := hcz v; rw [Rat.cast_natCast]; exact_mod_cast hℓ.ne_zero)
      (by haveI := hcz v; rw [Rat.cast_intCast]; exact_mod_cast h2q'0),
    aniso_iff]
  constructor
  · intro hnot
    by_contra hneither
    apply hnot
    have hv2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => hneither (Or.inl h)
    have hvq' : (q' : 𝓞 ℚ) ∉ v.asIdeal := fun h => hneither (Or.inr h)
    by_cases hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal
    · exact iso_at_ell₂ ℓ q' hℓ hq' hq'2 hq'ℓ hℓ8 hnq' v hℓv
    · refine iso_generic ℓ (2 * q' : ℤ) v hv2 hℓv ?_
      intro h
      push_cast at h
      rcases v.isPrime.mem_or_mem h with h | h
      · exact hv2 h
      · exact hvq' h
  · rintro (hv2 | hvq')
    · exact aniso_at_two₂ ℓ q' hℓ hq' hq'2 hℓ8 v hv2
    · have e : ((2 * q' : ℤ) : ℚ) = ((q' * 2 : ℤ) : ℚ) := by push_cast; ring
      rw [e]
      exact aniso_at q' 2 ℓ hq' hq'2 Nat.prime_two hq'2 hℓ hq'ℓ hnq' v hvq'

end IModelTwo

theorem solution
    (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hqq' : q' ≠ q) :
    ∃ a b : ℚ, (0 < a ∨ 0 < b) ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
          ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) := by
  rcases eq_or_ne q 2 with rfl | hq2
  · have hq'2 : q' ≠ 2 := hqq'
    simpa using IModelTwo.main₂ q' hq' hq'2
  · rcases eq_or_ne q' 2 with rfl | hq'2
    · obtain ⟨a, b, hab, h⟩ := IModelTwo.main₂ q hq hq2
      refine ⟨a, b, hab, fun v => ?_⟩
      rw [h v, or_comm]
      push_cast
      rfl
    · exact IModelCd1.main q q' hq hq' (Ne.symm hqq') hq2 hq'2

end S_QuaternionAlgebra_exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem
end P2MW
export P2MW.S_QuaternionAlgebra_exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem (solution)
