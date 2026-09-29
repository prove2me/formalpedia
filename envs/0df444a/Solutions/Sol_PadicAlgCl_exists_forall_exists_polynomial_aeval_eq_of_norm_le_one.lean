-- Prove2me | solution 1 for PadicAlgCl.exists_forall_exists_polynomial_aeval_eq_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d7382ea8-43ac-5a1d-a45c-cdfaff47cbf4

import Mathlib
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace TM0

open Polynomial IsLocalRing

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma norm_natCast_p : ‖(p : Ω)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap', Padic.norm_p]

lemma norm_algHom_eq {L : Type*} [Field L] [Algebra ℚ_[p] L] (σ τ : L →ₐ[ℚ_[p]] Ω) (y : L) :
    ‖σ y‖ = ‖τ y‖ := by
  have h1 : minpoly ℚ_[p] (σ y) = minpoly ℚ_[p] y := minpoly.algHom_eq σ σ.injective y
  have h2 : minpoly ℚ_[p] (τ y) = minpoly ℚ_[p] y := minpoly.algHom_eq τ τ.injective y
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, h1,
    h2]

section Abstract

variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

variable (L) in

def emb : L →ₐ[ℚ_[p]] Ω := IsAlgClosed.lift

def ν (y : L) : ℝ := ‖emb p L y‖

lemma ν_def (y : L) : ν p y = ‖emb p L y‖ := rfl

lemma norm_algHom_apply (σ : L →ₐ[ℚ_[p]] Ω) (y : L) : ‖σ y‖ = ν p y :=
  norm_algHom_eq p σ (emb p L) y

lemma emb_injective : Function.Injective (emb p L) := (emb p L).toRingHom.injective

lemma ν_nonneg (y : L) : 0 ≤ ν p y := norm_nonneg _

lemma ν_mul (y z : L) : ν p (y * z) = ν p y * ν p z := by
  simp [ν_def]

lemma ν_pow (y : L) (m : ℕ) : ν p (y ^ m) = ν p y ^ m := by
  simp [ν_def]

lemma ν_one : ν p (1 : L) = 1 := by simp [ν_def]

lemma ν_zero : ν p (0 : L) = 0 := by simp [ν_def]

lemma ν_neg (y : L) : ν p (-y) = ν p y := by simp [ν_def]

lemma ν_eq_zero_iff (y : L) : ν p y = 0 ↔ y = 0 := by
  rw [ν_def, norm_eq_zero, map_eq_zero_iff (emb p L) (emb_injective p)]

lemma ν_pos_iff (y : L) : 0 < ν p y ↔ y ≠ 0 := by
  rw [ν_def, norm_pos_iff, ne_eq, map_eq_zero_iff (emb p L) (emb_injective p)]

lemma ν_inv (y : L) : ν p y⁻¹ = (ν p y)⁻¹ := by
  simp [ν_def, map_inv₀, norm_inv]

lemma ν_div (y z : L) : ν p (y / z) = ν p y / ν p z := by
  rw [div_eq_mul_inv, ν_mul, ν_inv, div_eq_mul_inv]

lemma ν_add_le (y z : L) : ν p (y + z) ≤ max (ν p y) (ν p z) := by
  simp only [ν_def, map_add]
  exact IsUltrametricDist.norm_add_le_max _ _

lemma ν_sub_le (y z : L) : ν p (y - z) ≤ max (ν p y) (ν p z) := by
  rw [sub_eq_add_neg]
  refine (ν_add_le p y (-z)).trans ?_
  rw [ν_neg]

lemma ν_add_eq_max_of_ne {y z : L} (h : ν p y ≠ ν p z) :
    ν p (y + z) = max (ν p y) (ν p z) := by
  simp only [ν_def, map_add] at h ⊢
  exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h

lemma ν_algebraMap (c : ℚ_[p]) : ν p (algebraMap ℚ_[p] L c) = ‖c‖ := by
  rw [ν_def, AlgHom.commutes, norm_algebraMap']

lemma ν_natCast_p : ν p (p : L) = (p : ℝ)⁻¹ := by
  rw [ν_def, map_natCast, norm_natCast_p]

lemma ν_p_lt_one : ν p (p : L) < 1 := by
  rw [ν_natCast_p]
  exact inv_lt_one_of_one_lt₀ (one_lt_p p)

variable [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

abbrev OL : Subalgebra ℤ_[p] L := integralClosure ℤ_[p] L

scoped instance towZQΩ : IsScalarTower ℤ_[p] ℚ_[p] Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma mem_OL_iff (y : L) : y ∈ OL p (L := L) ↔ ν p y ≤ 1 := by
  rw [mem_integralClosure_iff, ν_def,
    ← PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p (emb p L y)]
  have : (emb p L y) = ((emb p L).restrictScalars ℤ_[p]) y := rfl
  rw [this, isIntegral_algHom_iff _ ((emb p L).restrictScalars ℤ_[p]).injective]

lemma ν_coe_le_one (b : OL p (L := L)) : ν p (b : L) ≤ 1 := (mem_OL_iff p (b : L)).mp b.2

lemma isUnit_iff_ν_eq_one (b : OL p (L := L)) : IsUnit b ↔ ν p (b : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    set a : OL p (L := L) := (u : OL p (L := L)) with ha_def
    set c : OL p (L := L) := ((u⁻¹ : (OL p (L := L))ˣ) : OL p (L := L)) with hc_def
    have hac : a * c = 1 := u.mul_inv
    have h1 : ν p (a : L) * ν p (c : L) = 1 := by
      rw [← ν_mul, ← Subalgebra.coe_mul, hac, Subalgebra.coe_one, ν_one]
    have ha := ν_coe_le_one p a
    have hb := ν_coe_le_one p c
    have ha0 := ν_nonneg p (a : L)
    have hb0 := ν_nonneg p (c : L)
    nlinarith
  · intro h
    have hb0 : (b : L) ≠ 0 := by
      rw [← ν_pos_iff p, h]
      exact one_pos
    have hinv : (b : L)⁻¹ ∈ OL p (L := L) := by
      rw [mem_OL_iff p, ν_inv, h, inv_one]
    refine IsUnit.of_mul_eq_one ⟨(b : L)⁻¹, hinv⟩ ?_
    ext
    simp [hb0]

lemma ν_lt_one_of_not_isUnit {b : OL p (L := L)} (hb : ¬IsUnit b) : ν p (b : L) < 1 :=
  lt_of_le_of_ne (ν_coe_le_one p b) (fun h => hb ((isUnit_iff_ν_eq_one p b).mpr h))

scoped instance isLocalRing_OL : IsLocalRing (OL p (L := L)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  by_cases hb : IsUnit b
  · exact Or.inl hb
  · right
    rw [isUnit_iff_ν_eq_one p]
    have hlt := ν_lt_one_of_not_isUnit p hb
    rw [Subalgebra.coe_sub, Subalgebra.coe_one, sub_eq_add_neg,
      ν_add_eq_max_of_ne p (by rw [ν_one, ν_neg]; exact hlt.ne'), ν_one, ν_neg]
    exact max_eq_left hlt.le

lemma mem_maximalIdeal_iff (b : OL p (L := L)) :
    b ∈ maximalIdeal (OL p (L := L)) ↔ ν p (b : L) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · exact ν_lt_one_of_not_isUnit p
  · intro h hu
    rw [isUnit_iff_ν_eq_one p] at hu
    exact h.ne hu

lemma residue_eq_zero_iff_ν (b : OL p (L := L)) :
    residue (OL p (L := L)) b = 0 ↔ ν p (b : L) < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal_iff p]

lemma ν_eq_one_of_residue_ne_zero {b : OL p (L := L)} (h : residue (OL p (L := L)) b ≠ 0) :
    ν p (b : L) = 1 := by
  rw [residue_ne_zero_iff_isUnit] at h
  exact (isUnit_iff_ν_eq_one p b).mp h

lemma ν_sub_lt_one_of_residue_eq {b c : OL p (L := L)}
    (h : residue (OL p (L := L)) b = residue (OL p (L := L)) c) : ν p ((b : L) - c) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_ν p] at h
  simpa using h

scoped instance isLocalHom_OL : IsLocalHom (algebraMap ℤ_[p] (OL p (L := L))) := by
  constructor
  intro a ha
  rw [isUnit_iff_ν_eq_one p] at ha
  rw [PadicInt.isUnit_iff]
  have : ((algebraMap ℤ_[p] (OL p (L := L)) a : OL p) : L) = algebraMap ℚ_[p] L (a : ℚ_[p]) := by
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L]
    rfl
  rw [this, ν_algebraMap] at ha
  simpa using ha

scoped instance isSeparable_L : Algebra.IsSeparable ℚ_[p] L := Algebra.IsSeparable.of_integral ℚ_[p] L

scoped instance module_finite_OL : Module.Finite ℤ_[p] (OL p (L := L)) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] L (OL p (L := L))

scoped instance finite_residueField : Finite (ResidueField (OL p (L := L))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  exact ResidueField.finite_of_finite (R := ℤ_[p]) (S := OL p (L := L)) inferInstance

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in

lemma exists_ν_eq_rpow {y : L} (hy : y ≠ 0) :
    ∃ k : ℤ, ν p y = (p : ℝ) ^ ((k : ℝ) / ((Module.finrank ℚ_[p] L).factorial : ℝ)) := by
  set x : Ω := emb p L y with hxdef
  have hx : x ≠ 0 := (map_ne_zero_iff (emb p L) (emb_injective p)).mpr hy
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  set d := Module.finrank ℚ_[p] L with hd
  set m := (minpoly ℚ_[p] x).natDegree with hm
  have hmpos : 0 < m := minpoly.natDegree_pos hint
  have hmd : m ≤ d := by
    have h1 : minpoly ℚ_[p] x = minpoly ℚ_[p] y := minpoly.algHom_eq (emb p L) (emb_injective p) y
    rw [hm, h1]
    exact minpoly.natDegree_le y
  have hc0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hnorm : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (m : ℝ)) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := Ω) x
  rw [Padic.norm_eq_zpow_neg_valuation hc0] at hnorm
  set v : ℤ := ((minpoly ℚ_[p] x).coeff 0).valuation with hv
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hmpos hmd
  refine ⟨-v * q, ?_⟩
  rw [ν_def, ← hxdef, hnorm, ← Real.rpow_intCast, ← Real.rpow_mul (p_pos p).le]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hq0 : (q : ℝ) ≠ 0 := by
    rintro hq0
    have : (q : ℕ) = 0 := by exact_mod_cast hq0
    rw [this, mul_zero] at hq
    exact (Nat.factorial_pos d).ne' hq
  have hdf : (d.factorial : ℝ) = (m : ℝ) * (q : ℝ) := by exact_mod_cast hq
  rw [hdf]
  field_simp
  push_cast
  ring

def IsUnif (ϖ : L) : Prop := ϖ ≠ 0 ∧ ν p ϖ < 1 ∧ ∀ y : L, ν p y < 1 → ν p y ≤ ν p ϖ

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
lemma exists_isUnif : ∃ π : L, IsUnif p π := by
  set D : ℝ := ((Module.finrank ℚ_[p] L).factorial : ℝ) with hDdef
  have hD : 0 < D := by rw [hDdef]; exact_mod_cast Nat.factorial_pos _
  let P : ℤ → Prop := fun k => ∃ y : L, y ≠ 0 ∧ ν p y < 1 ∧ ν p y = (p : ℝ) ^ ((k : ℝ) / D)
  have hbdd : ∀ k, P k → k ≤ 0 := by
    rintro k ⟨y, -, hy1, hyk⟩
    by_contra hk
    push Not at hk
    have h1 : (1 : ℝ) < (p : ℝ) ^ ((k : ℝ) / D) :=
      Real.one_lt_rpow (one_lt_p p) (div_pos (by exact_mod_cast hk) hD)
    linarith
  have hp0 : (p : L) ≠ 0 := by
    rw [← ν_pos_iff p, ν_natCast_p]
    exact inv_pos.mpr (p_pos p)
  have hinh : ∃ k, P k := by
    obtain ⟨k, hk⟩ := exists_ν_eq_rpow p hp0
    exact ⟨k, (p : L), hp0, ν_p_lt_one p, hk⟩
  obtain ⟨k₀, ⟨π, hπ0, hπ1, hπk⟩, hmax⟩ := Int.exists_greatest_of_bdd ⟨0, hbdd⟩ hinh
  refine ⟨π, hπ0, hπ1, fun y hy => ?_⟩
  by_cases hy0 : y = 0
  · rw [hy0, ν_zero]
    exact ν_nonneg p π
  obtain ⟨k, hk⟩ := exists_ν_eq_rpow p hy0
  have hkk : k ≤ k₀ := hmax k ⟨y, hy0, hy, hk⟩
  rw [hk, hπk]
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_p p).le
    (div_le_div_of_nonneg_right (by exact_mod_cast hkk) hD.le)

namespace IsUnif

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

variable {p}
variable {ϖ : L}

lemma ν_pos (h : IsUnif p ϖ) : 0 < ν p ϖ := (ν_pos_iff p ϖ).mpr h.1

lemma ν_div_le_one (h : IsUnif p ϖ) {y : L} (hy : ν p y < 1) : ν p (y / ϖ) ≤ 1 := by
  rw [ν_div, div_le_one h.ν_pos]
  exact h.2.2 y hy

lemma ν_le_sq (h : IsUnif p ϖ) {y : L} (hy : ν p y < ν p ϖ) : ν p y ≤ ν p ϖ ^ 2 := by
  have h1 : ν p (y / ϖ) < 1 := by
    rw [ν_div, div_lt_one h.ν_pos]
    exact hy
  have h2 := h.2.2 _ h1
  rw [ν_div, div_le_iff₀ h.ν_pos] at h2
  nlinarith [h2]

lemma of_ν_eq (h : IsUnif p ϖ) {ϖ' : L} (he : ν p ϖ' = ν p ϖ) : IsUnif p ϖ' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← ν_pos_iff p, he]
    exact h.ν_pos
  · rw [he]
    exact h.2.1
  · intro y hy
    rw [he]
    exact h.2.2 y hy

end IsUnif

local notation "𝓞" => OL p (L := L)

lemma exists_residue_eq_pow {gu : (ResidueField 𝓞)ˣ} (hgu : ∀ u : (ResidueField 𝓞)ˣ, u ∈ Subgroup.zpowers gu)
    {x : 𝓞} (hx : residue 𝓞 x = (gu : ResidueField 𝓞)) {b : 𝓞} (hb : residue 𝓞 b ≠ 0) :
    ∃ i : ℕ, residue 𝓞 b = residue 𝓞 (x ^ i) := by
  set u : (ResidueField 𝓞)ˣ := Units.mk0 _ hb with hu
  have hmem : u ∈ Submonoid.powers gu := (mem_powers_iff_mem_zpowers).mpr (hgu u)
  obtain ⟨i, hi⟩ := hmem
  refine ⟨i, ?_⟩
  have hi' : gu ^ i = u := hi
  have h1 : (residue 𝓞 b) = ((gu ^ i : (ResidueField 𝓞)ˣ) : ResidueField 𝓞) := by
    rw [hi', hu, Units.val_mk0]
  rw [h1, Units.val_pow_eq_pow_val, ← hx, map_pow]

private lemma _root_.TM0.exists_generator :
    ∃ x : 𝓞, ∃ n : ℕ, IsUnif p ((x : L) ^ n - 1) ∧
      ∀ b : 𝓞, residue 𝓞 b ≠ 0 → ∃ i : ℕ, residue 𝓞 b = residue 𝓞 (x ^ i) := by
  classical
  letI : Fintype (ResidueField 𝓞) := Fintype.ofFinite _
  obtain ⟨gu, hgu⟩ := IsCyclic.exists_generator (α := (ResidueField 𝓞)ˣ)
  obtain ⟨g, hg⟩ := IsLocalRing.residue_surjective (gu : ResidueField 𝓞)
  set n : ℕ := Fintype.card (ResidueField 𝓞) - 1 with hn

  have hRg : ν p ((g : L) ^ n - 1) < 1 := by
    have h1 : residue 𝓞 (g ^ n - 1) = 0 := by
      rw [map_sub, map_pow, hg, map_one, hn,
        FiniteField.pow_card_sub_one_eq_one (gu : ResidueField 𝓞) (Units.ne_zero gu), sub_self]
    have h2 := (residue_eq_zero_iff_ν p _).mp h1
    simpa using h2

  have hR'g : ν p ((n : L) * (g : L) ^ (n - 1)) = 1 := by
    have hne : residue 𝓞 ((n : 𝓞) * g ^ (n - 1)) ≠ 0 := by
      rw [map_mul, map_pow, map_natCast, hg]
      refine mul_ne_zero ?_ (pow_ne_zero _ (Units.ne_zero gu))
      have hq : (Fintype.card (ResidueField 𝓞) : ResidueField 𝓞) = 0 :=
        FiniteField.cast_card_eq_zero (ResidueField 𝓞)
      have hcast : ((n : ℕ) : ResidueField 𝓞) = (Fintype.card (ResidueField 𝓞) : ResidueField 𝓞) - 1 := by
        rw [hn, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
      rw [hcast, hq, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    have h2 := ν_eq_one_of_residue_ne_zero p hne
    simpa using h2
  obtain ⟨π, hπ⟩ := exists_isUnif p (L := L)
  have hπmem : π ∈ 𝓞 := (mem_OL_iff p π).mpr hπ.2.1.le
  set πO : 𝓞 := ⟨π, hπmem⟩ with hπO
  have hπres : residue 𝓞 πO = 0 := (residue_eq_zero_iff_ν p πO).mpr hπ.2.1

  obtain ⟨c, hc⟩ := Polynomial.binomExpansion ((X : 𝓞[X]) ^ n - 1) g πO
  have hO : (g + πO) ^ n - 1 = (g ^ n - 1) + ((n : 𝓞) * g ^ (n - 1)) * πO + c * πO ^ 2 := by
    have h := hc
    simp only [eval_sub, eval_pow, eval_X, eval_one, derivative_sub, derivative_X_pow,
      derivative_one, sub_zero, eval_mul, map_natCast, eval_natCast] at h
    rw [h]
  have hTaylor : ((g : L) + π) ^ n - 1 =
      ((g : L) ^ n - 1) + ((n : L) * (g : L) ^ (n - 1)) * π + (c : L) * π ^ 2 := by
    have h := congrArg (fun t : 𝓞 => (t : L)) hO
    push_cast at h
    exact h

  obtain ⟨x, hxres, hxunif⟩ : ∃ x : 𝓞, residue 𝓞 x = (gu : ResidueField 𝓞) ∧
      IsUnif p ((x : L) ^ n - 1) := by
    by_cases hcase : ν p ((g : L) ^ n - 1) = ν p π
    · exact ⟨g, hg, hπ.of_ν_eq hcase⟩
    · have hlt : ν p ((g : L) ^ n - 1) < ν p π := lt_of_le_of_ne (hπ.2.2 _ hRg) hcase
      have hsq : ν p ((g : L) ^ n - 1) ≤ ν p π ^ 2 := hπ.ν_le_sq hlt
      refine ⟨g + πO, by rw [map_add, hg, hπres, add_zero], hπ.of_ν_eq ?_⟩
      have hxL : ((g + πO : 𝓞) : L) = (g : L) + π := by rw [Subalgebra.coe_add]
      rw [hxL, hTaylor]
      have hmain : ν p ((n : L) * (g : L) ^ (n - 1) * π) = ν p π := by
        rw [ν_mul, hR'g, one_mul]
      have hππ : ν p π ^ 2 < ν p π := by
        have := hπ.ν_pos
        have := hπ.2.1
        nlinarith
      have hrest : ν p (((g : L) ^ n - 1) + (c : L) * π ^ 2) < ν p π := by
        refine lt_of_le_of_lt (ν_add_le p _ _) (max_lt (by exact hlt) ?_)
        rw [ν_mul, ν_pow]
        calc ν p (c : L) * ν p π ^ 2 ≤ 1 * ν p π ^ 2 := by
              gcongr
              exact ν_coe_le_one p c
          _ < ν p π := by rw [one_mul]; exact hππ
      have hre : (g : L) ^ n - 1 + (n : L) * (g : L) ^ (n - 1) * π + (c : L) * π ^ 2 =
          (n : L) * (g : L) ^ (n - 1) * π + (((g : L) ^ n - 1) + (c : L) * π ^ 2) := by ring
      rw [hre, ν_add_eq_max_of_ne p (by rw [hmain]; exact hrest.ne'), hmain]
      exact max_eq_left hrest.le
  exact ⟨x, n, hxunif, fun b hb => exists_residue_eq_pow p hgu hxres hb⟩

p2m_export "TM0" "exists_generator"

omit [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
lemma self_pow_sub_one_mem_adjoin (x : 𝓞) (n : ℕ) : x ^ n - 1 ∈ Algebra.adjoin ℤ_[p] {x} :=
  Subalgebra.sub_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ_[p] x) n)
    (Subalgebra.one_mem _)

lemma exists_mem_adjoin_add_mul (x : 𝓞) (n : ℕ) (hϖ : IsUnif p ((x : L) ^ n - 1))
    (hgen : ∀ b : 𝓞, residue 𝓞 b ≠ 0 → ∃ i : ℕ, residue 𝓞 b = residue 𝓞 (x ^ i)) (b : 𝓞) :
    ∃ a ∈ Algebra.adjoin ℤ_[p] {x}, ∃ b' : 𝓞, b = a + (x ^ n - 1) * b' := by
  have hϖ0 : (x : L) ^ n - 1 ≠ 0 := hϖ.1
  by_cases hb : residue 𝓞 b = 0
  · have hb1 : ν p (b : L) < 1 := (residue_eq_zero_iff_ν p b).mp hb
    have hmem : (b : L) / ((x : L) ^ n - 1) ∈ 𝓞 := (mem_OL_iff p _).mpr (hϖ.ν_div_le_one hb1)
    refine ⟨0, Subalgebra.zero_mem _, ⟨_, hmem⟩, ?_⟩
    ext
    push_cast
    rw [zero_add, mul_div_cancel₀ _ hϖ0]
  · obtain ⟨i, hi⟩ := hgen b hb
    have hb1 : ν p ((b : L) - (x : L) ^ i) < 1 := by
      simpa using ν_sub_lt_one_of_residue_eq p hi
    have hmem : ((b : L) - (x : L) ^ i) / ((x : L) ^ n - 1) ∈ 𝓞 :=
      (mem_OL_iff p _).mpr (hϖ.ν_div_le_one hb1)
    refine ⟨x ^ i, Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ_[p] x) i,
      ⟨_, hmem⟩, ?_⟩
    ext
    push_cast
    rw [mul_div_cancel₀ _ hϖ0]
    ring

lemma exists_mem_adjoin_add_pow_mul (x : 𝓞) (n : ℕ) (hϖ : IsUnif p ((x : L) ^ n - 1))
    (hgen : ∀ b : 𝓞, residue 𝓞 b ≠ 0 → ∃ i : ℕ, residue 𝓞 b = residue 𝓞 (x ^ i))
    (m : ℕ) (b : 𝓞) :
    ∃ a ∈ Algebra.adjoin ℤ_[p] {x}, ∃ b' : 𝓞, b = a + (x ^ n - 1) ^ m * b' := by
  induction m generalizing b with
  | zero => exact ⟨0, Subalgebra.zero_mem _, b, by simp⟩
  | succ m ih =>
    obtain ⟨a, ha, b₁, hb₁⟩ := ih b
    obtain ⟨a', ha', b₂, hb₂⟩ := exists_mem_adjoin_add_mul p x n hϖ hgen b₁
    refine ⟨a + (x ^ n - 1) ^ m * a', ?_, b₂, ?_⟩
    · exact Subalgebra.add_mem _ ha
        (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (self_pow_sub_one_mem_adjoin p x n) m) ha')
    · rw [hb₁, hb₂]
      ring

lemma adjoin_eq_top (x : 𝓞) (n : ℕ) (hϖ : IsUnif p ((x : L) ^ n - 1))
    (hgen : ∀ b : 𝓞, residue 𝓞 b ≠ 0 → ∃ i : ℕ, residue 𝓞 b = residue 𝓞 (x ^ i)) :
    Algebra.adjoin ℤ_[p] {x} = ⊤ := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ν p ((x : L) ^ n - 1) ^ m < (p : ℝ)⁻¹ :=
    exists_pow_lt_of_lt_one (inv_pos.mpr (p_pos p)) hϖ.2.1
  set N : Submodule ℤ_[p] 𝓞 := Subalgebra.toSubmodule (Algebra.adjoin ℤ_[p] {x}) with hN
  set I : Ideal ℤ_[p] := maximalIdeal ℤ_[p] with hI
  have hIJ : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hpI : (p : ℤ_[p]) ∈ I := by
    rw [hI, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hp0 : (p : L) ≠ 0 := by
    rw [← ν_pos_iff p, ν_natCast_p]
    exact inv_pos.mpr (p_pos p)
  have htop : (⊤ : Submodule ℤ_[p] 𝓞) ≤ N ⊔ I • ⊤ := by
    intro b _
    obtain ⟨a, ha, b', hb'⟩ := exists_mem_adjoin_add_pow_mul p x n hϖ hgen m b
    have hmem : ((x : L) ^ n - 1) ^ m * (b' : L) / (p : L) ∈ 𝓞 := by
      rw [mem_OL_iff p, ν_div, ν_natCast_p, ν_mul, ν_pow, div_le_iff₀ (inv_pos.mpr (p_pos p)),
        one_mul]
      calc ν p ((x : L) ^ n - 1) ^ m * ν p (b' : L) ≤ ν p ((x : L) ^ n - 1) ^ m * 1 := by
            gcongr
            · exact pow_nonneg (ν_nonneg p _) m
            · exact ν_coe_le_one p b'
        _ ≤ (p : ℝ)⁻¹ := by rw [mul_one]; exact hm.le
    set b'' : 𝓞 := ⟨_, hmem⟩ with hb''
    have hb : b = a + (p : ℤ_[p]) • b'' := by
      ext
      rw [hb', Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_smul, Algebra.smul_def,
        map_natCast]
      push_cast
      rw [mul_div_cancel₀ _ hp0]
    rw [hb]
    exact Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).mpr ha)
      (Submodule.smul_mem_smul hpI Submodule.mem_top)
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIJ htop
  exact eq_top_iff.mpr fun b _ => (Subalgebra.mem_toSubmodule _).mp (hle Submodule.mem_top)

theorem exists_monogenic :
    ∃ x : L, ν p x ≤ 1 ∧ ∀ y : L, ν p y ≤ 1 →
      ∃ Q : ℚ_[p][X], (∀ i, ‖Q.coeff i‖ ≤ 1) ∧ aeval x Q = y := by
  obtain ⟨x, n, hϖ, hgen⟩ := exists_generator p (L := L)
  have htop := adjoin_eq_top p x n hϖ hgen
  refine ⟨x, ν_coe_le_one p x, fun y hy => ?_⟩
  have hy' : (⟨y, (mem_OL_iff p y).mpr hy⟩ : 𝓞) ∈ Algebra.adjoin ℤ_[p] {x} := by
    rw [htop]
    exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨P, hP⟩ := hy'
  refine ⟨P.map (algebraMap ℤ_[p] ℚ_[p]), fun i => ?_, ?_⟩
  · rw [coeff_map]
    exact PadicInt.norm_le_one _
  · rw [aeval_map_algebraMap]
    have h := congrArg (fun t : 𝓞 => (t : L)) hP
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    rw [Polynomial.aeval_subalgebra_coe] at h
    exact h

end Abstract

section Concrete

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (E : IntermediateField F (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] F] [FiniteDimensional F E]

theorem main :
    ∃ x : E, ‖(x : Ω)‖ ≤ 1 ∧ IntermediateField.adjoin F {x} = ⊤ ∧
      ∀ y : E, ‖(y : Ω)‖ ≤ 1 →
        ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval x P = y := by
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans F E
  letI : Algebra ℤ_[p] E := ((algebraMap ℚ_[p] E).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  haveI : IsScalarTower ℤ_[p] ℚ_[p] E := IsScalarTower.of_algebraMap_eq fun _ => rfl

  have hν : ∀ y : E, ‖(y : Ω)‖ = ν p y := fun y =>
    norm_algHom_apply p (E.val.restrictScalars ℚ_[p]) y
  obtain ⟨x, hx, hmono⟩ := exists_monogenic p (L := E)
  have hx' : ‖(x : Ω)‖ ≤ 1 := by rw [hν]; exact hx
  have hpoly : ∀ y : E, ‖(y : Ω)‖ ≤ 1 →
      ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval x P = y := by
    intro y hy
    rw [hν] at hy
    exact hmono y hy
  refine ⟨x, hx', ?_, hpoly⟩

  rw [eq_top_iff]
  intro y _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(y : Ω)‖ ≤ (p : ℝ) ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖(y : Ω)‖ (one_lt_p p)
    exact ⟨N, hN.le⟩
  have hpN : ((p : E) ^ N : E) ≠ 0 := pow_ne_zero N (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hint : ‖(((p : E) ^ N * y : E) : Ω)‖ ≤ 1 := by
    push_cast
    rw [norm_mul, norm_pow, norm_natCast_p, inv_pow]
    have hpN' : (0 : ℝ) < (p : ℝ) ^ N := pow_pos (p_pos p) N
    calc ((p : ℝ) ^ N)⁻¹ * ‖(y : Ω)‖ ≤ ((p : ℝ) ^ N)⁻¹ * (p : ℝ) ^ N := by gcongr
      _ = 1 := inv_mul_cancel₀ hpN'.ne'
  obtain ⟨P, -, hP⟩ := hpoly _ hint

  have hle : Algebra.adjoin ℚ_[p] {x} ≤
      (IntermediateField.adjoin F {x}).toSubalgebra.restrictScalars ℚ_[p] :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self F x))
  have hmem : ((p : E) ^ N * y : E) ∈ IntermediateField.adjoin F {x} := by
    rw [← hP]
    exact hle (Polynomial.aeval_mem_adjoin_singleton ℚ_[p] x)
  have hy : y = ((p : E) ^ N)⁻¹ * ((p : E) ^ N * y) := by
    rw [← mul_assoc, inv_mul_cancel₀ hpN, one_mul]
  rw [hy]
  refine IntermediateField.mul_mem _ (IntermediateField.inv_mem _ ?_) hmem
  exact pow_mem (natCast_mem (IntermediateField.adjoin F {x}) p) N

end Concrete

end TM0
p2m_reactivate "P2MW.S_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one.TM0"

end
p2m_reactivate "P2MW.S_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one.TM0"

theorem solution
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] :
    ∃ x : E, ‖(x : PadicAlgCl p)‖ ≤ 1 ∧ IntermediateField.adjoin F {x} = ⊤ ∧
      ∀ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 →
        ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval x P = y :=
  TM0.main p F E

end S_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one
end P2MW
export P2MW.S_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one (solution)
