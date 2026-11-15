-- Prove2me | solution 1 for PrimeLocal.no_additive_integral_j_at_p
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:54:17.820083+00:00
-- url     : https://prove2.me/submissions/700edf5b-5d78-41ab-993b-a082a134b38c

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Theorems.Thm_PrimeLocal_norm_prime_le_norm_param_pow_of_prime_torsion
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
/-- If six is a unit, translations put a Weierstrass equation into short form. -/
private theorem short_change_of_unit_six {R : Type*} [CommRing R] (h6 : IsUnit (6 : R)) (W : WeierstrassCurve R) : ∃ C : WeierstrassCurve.VariableChange R, (C.u : R) = 1 ∧ (C • W).a₁ = 0 ∧ (C • W).a₂ = 0 ∧ (C • W).a₃ = 0 := by
  rcases h6 with ⟨e, he⟩
  let i : R := ↑e⁻¹
  have hi : (6 : R) * i = 1 := by
    rw [← he]
    exact e.mul_inv
  let d : R := 3 * i
  let q : R := 2 * i
  have hd : (2 : R) * d = 1 := by
    dsimp [d]
    linear_combination hi
  have hq : (3 : R) * q = 1 := by
    dsimp [q]
    linear_combination hi
  let s : R := -W.a₁ * d
  let r : R := (s * W.a₁ + s ^ 2 - W.a₂) * q
  let t : R := -(W.a₃ + r * W.a₁) * d
  have hs : W.a₁ + 2 * s = 0 := by
    dsimp [s]
    linear_combination -W.a₁ * hd
  have hr : W.a₂ - s * W.a₁ + 3 * r - s ^ 2 = 0 := by
    dsimp only [r]
    linear_combination (s * W.a₁ + s ^ 2 - W.a₂) * hq
  have ht : W.a₃ + r * W.a₁ + 2 * t = 0 := by
    dsimp only [t]
    linear_combination -(W.a₃ + r * W.a₁) * hd
  refine ⟨⟨1, r, s, t⟩, rfl, ?_, ?_, ?_⟩
  · simpa only [variableChange_a₁, inv_one, Units.val_one, one_mul] using hs
  · simpa only [variableChange_a₂, inv_one, Units.val_one, one_pow, one_mul] using hr
  · simpa only [variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul] using ht

/-- Prime-to-`p` constants retain norm one. -/
private theorem norm_nat_primeTo {p : ℕ} [Fact p.Prime] {n : ℕ}
    (h : Nat.Coprime n p) : ‖(n : ℚ_[p])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr h.symm

/-- The integral short change can be chosen over the rationals. -/
private theorem rational_short_change (W : WeierstrassCurve ℤ) {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) : ∃ C : VariableChange ℚ, (C.u : ℚ) = 1 ∧
      ‖(C.r : ℚ_[p])‖ ≤ 1 ∧ ‖(C.s : ℚ_[p])‖ ≤ 1 ∧ ‖(C.t : ℚ_[p])‖ ≤ 1 ∧
      (C • W.map (Int.castRingHom ℚ)).a₁ = 0 ∧
      (C • W.map (Int.castRingHom ℚ)).a₂ = 0 ∧
      (C • W.map (Int.castRingHom ℚ)).a₃ = 0 := by
  let V : Subring ℚ := (PadicInt.subring p).comap (algebraMap ℚ ℚ_[p])
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hn6 : ‖(6 : ℚ_[p])‖ = 1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    change Nat.Coprime p (2 * 3)
    apply Nat.Coprime.mul_right
    · exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
    · exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
  have hi : (6 : ℚ)⁻¹ ∈ V := by
    change ‖algebraMap ℚ ℚ_[p] (6 : ℚ)⁻¹‖ ≤ 1
    simpa only [map_inv₀, map_ofNat, norm_inv, hn6, inv_one] using (le_rfl : (1 : ℝ) ≤ 1)
  have h6 : IsUnit (6 : V) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(6 : ℚ)⁻¹, hi⟩, ?_⟩
    apply Subtype.ext
    change (6 : ℚ) * 6⁻¹ = 1
    norm_num
  obtain ⟨C, hu, h1, h2, h3⟩ := short_change_of_unit_six h6 (W.map (Int.castRingHom V))
  refine ⟨C.map V.subtype, ?_, C.r.property, C.s.property, C.t.property, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hu
  all_goals
    have he : C.map V.subtype • W.map (Int.castRingHom ℚ) =
        (C • W.map (Int.castRingHom V)).map V.subtype := by
      rw [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map]
      congr 1
    rw [he]
    simp only [map_a₁, map_a₂, map_a₃, h1, h2, h3, _root_.map_zero]

/-- Scaling a minimal equation by a nonunit cannot preserve integrality. -/
private theorem not_integral_of_scale_prime (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} [Fact p.Prime]
    (hm : IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p])))
    (C : VariableChange ℚ_[p]) (hu : (C.u : ℚ_[p]) = p) :
    ¬ IsIntegral ℤ_[p] (C • W.map (Int.castRingHom ℚ_[p])) := by
  intro hi
  let := hm
  let := hi
  let V := IsDedekindDomain.HeightOneSpectrum.valuation ℚ_[p]
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p])
  have hpv : V (p : ℚ_[p]) < 1 := by
    have hmem : (p : ℤ_[p]) ∈ (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).asIdeal := by
      change (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p]
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (K := ℚ_[p]) (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) (p : ℤ_[p])).mpr hmem
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hscale : 1 < V (↑C.u⁻¹ : ℚ_[p]) := by
    rw [Units.val_inv_eq_inv_val, hu, map_inv₀]
    exact one_lt_inv₀ (pos_iff_ne_zero.mpr ((map_ne_zero V).mpr hp0)) |>.mpr hpv
  have hpow : 1 < V (↑C.u⁻¹ : ℚ_[p]) ^ 12 := one_lt_pow₀ hscale (by norm_num)
  have hd0 : (W.map (Int.castRingHom ℚ_[p])).Δ ≠ 0 := by
    rw [map_Δ]
    change (W.Δ : ℚ_[p]) ≠ 0
    exact_mod_cast hΔ
  have hpos : 0 < V (W.map (Int.castRingHom ℚ_[p])).Δ :=
    lt_of_le_of_ne zero_le ((map_ne_zero V).mpr hd0).symm
  have hstrict : V (W.map (Int.castRingHom ℚ_[p])).Δ <
      V (C • W.map (Int.castRingHom ℚ_[p])).Δ := by
    rw [variableChange_Δ, map_mul, map_pow]
    exact lt_mul_of_one_lt_left hpos hpow
  have haux : valuation_Δ_aux ℤ_[p] (W.map (Int.castRingHom ℚ_[p])) <
      valuation_Δ_aux ℤ_[p] (C • W.map (Int.castRingHom ℚ_[p])) := by
    change (valuation_Δ_aux ℤ_[p] (W.map (Int.castRingHom ℚ_[p])) : WithZero (Multiplicative ℤ)) < _
    simpa only [valuation_Δ_aux_eq_of_isIntegral] using hstrict
  have hh := hm.val_Δ_maximal.2 hi
  simp only [one_smul] at hh
  exact (not_le_of_gt haux) (hh (le_of_lt haux))

/-- The two short coefficients obey the inequalities imposed by integral j. -/
private theorem short_norm_bounds (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hj : (p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3)
    (E : WeierstrassCurve ℚ_[p]) (h1 : E.a₁ = 0) (h2 : E.a₂ = 0) (h3 : E.a₃ = 0)
    (hd : E.Δ = (W.Δ : ℚ_[p])) (hc : E.c₄ = (W.c₄ : ℚ_[p])) :
    ‖E.a₄‖ ^ 3 ≤ ‖(W.Δ : ℚ_[p])‖ ∧ ‖E.a₆‖ ^ 2 ≤ ‖(W.Δ : ℚ_[p])‖ := by
  have hn2 : ‖(2 : ℚ_[p])‖ = 1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hd; have := Nat.le_of_dvd (by norm_num : 0 < 2) hd; omega
  have hn3 : ‖(3 : ℚ_[p])‖ = 1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hd; have := Nat.le_of_dvd (by norm_num : 0 < 3) hd; omega
  have hn48 : ‖(48 : ℚ_[p])‖ = 1 := by
    rw [show (48 : ℚ_[p]) = 2 ^ 4 * 3 by norm_num, norm_mul, norm_pow, hn2, hn3]
    norm_num
  have hn864 : ‖(864 : ℚ_[p])‖ = 1 := by
    rw [show (864 : ℚ_[p]) = 2 ^ 5 * 3 ^ 3 by norm_num, norm_mul, norm_pow, norm_pow, hn2, hn3]
    norm_num
  have hn1728 : ‖(1728 : ℚ_[p])‖ = 1 := by
    rw [show (1728 : ℚ_[p]) = 2 ^ 6 * 3 ^ 3 by norm_num, norm_mul, norm_pow, norm_pow, hn2, hn3]
    norm_num
  have h4 : E.c₄ = -48 * E.a₄ := by simp only [c₄, b₂, b₄, h1, h2, h3]; ring
  have h6 : E.c₆ = -864 * E.a₆ := by simp only [c₆, b₂, b₄, b₆, h1, h2, h3]; ring
  have h4n : ‖E.c₄‖ = ‖E.a₄‖ := by rw [h4, norm_mul, norm_neg, hn48, one_mul]
  have h6n : ‖E.c₆‖ = ‖E.a₆‖ := by rw [h6, norm_mul, norm_neg, hn864, one_mul]
  have hdn : ‖(W.Δ : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValInt p W.Δ : ℤ)) := by
    rw [show (W.Δ : ℚ_[p]) = ((W.Δ : ℚ) : ℚ_[p]) by norm_cast,
      Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hΔ), padicValRat.of_int]
    push_cast
    rfl
  have hcn : ‖E.c₄‖ ^ 3 ≤ ‖(W.Δ : ℚ_[p])‖ := by
    rw [hc, ← norm_pow, ← Int.cast_pow, hdn]
    exact (Padic.norm_int_le_pow_iff_dvd _ _).mpr hj
  refine ⟨by rwa [← h4n], ?_⟩
  have heq : E.c₆ ^ 2 = E.c₄ ^ 3 - 1728 * E.Δ := by linear_combination E.c_relation
  calc
    ‖E.a₆‖ ^ 2 = ‖E.c₆ ^ 2‖ := by rw [norm_pow, h6n]
    _ = ‖E.c₄ ^ 3 - 1728 * E.Δ‖ := congrArg norm heq
    _ ≤ max ‖E.c₄ ^ 3‖ ‖1728 * E.Δ‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using Padic.nonarchimedean (E.c₄ ^ 3) (-(1728 * E.Δ))
    _ ≤ ‖(W.Δ : ℚ_[p])‖ := by
      rw [max_le_iff, norm_pow, norm_mul, hn1728, one_mul, hd]
      exact ⟨hcn, le_rfl⟩

/-- A short equation remains integral after scaling when its coefficients have the required norms. -/
private theorem integral_short_scale {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ_[p]) (h1 : E.a₁ = 0) (h2 : E.a₂ = 0) (h3 : E.a₃ = 0)
    (u : ℚ_[p]) (hu : u ≠ 0)
    (h4 : ‖E.a₄‖ ≤ ‖u‖ ^ 4) (h6 : ‖E.a₆‖ ≤ ‖u‖ ^ 6) :
    IsIntegral ℤ_[p] ((⟨Units.mk0 u hu, 0, 0, 0⟩ : VariableChange ℚ_[p]) • E) := by
  have hA : ‖u⁻¹ ^ 4 * E.a₄‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_inv, inv_pow, ← div_eq_inv_mul]
    exact (div_le_one (pow_pos (norm_pos_iff.mpr hu) _)).mpr h4
  have hB : ‖u⁻¹ ^ 6 * E.a₆‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_inv, inv_pow, ← div_eq_inv_mul]
    exact (div_le_one (pow_pos (norm_pos_iff.mpr hu) _)).mpr h6
  refine ⟨⟨0, 0, 0, ⟨u⁻¹ ^ 4 * E.a₄, hA⟩, ⟨u⁻¹ ^ 6 * E.a₆, hB⟩⟩, ?_⟩
  ext <;> simp [WeierstrassCurve.baseChange, variableChange_def, h1, h2, h3]

/-- Integral j bounds the discriminant exponent of a minimal short equation. -/
private theorem discriminant_exponent_lt_twelve (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} [Fact p.Prime]
    (hm : IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p])))
    (C : VariableChange ℚ_[p]) (hu : (C.u : ℚ_[p]) = 1)
    (h1 : (C • W.map (Int.castRingHom ℚ_[p])).a₁ = 0)
    (h2 : (C • W.map (Int.castRingHom ℚ_[p])).a₂ = 0)
    (h3 : (C • W.map (Int.castRingHom ℚ_[p])).a₃ = 0)
    (h4 : ‖(C • W.map (Int.castRingHom ℚ_[p])).a₄‖ ^ 3 ≤ ‖(W.Δ : ℚ_[p])‖)
    (h6 : ‖(C • W.map (Int.castRingHom ℚ_[p])).a₆‖ ^ 2 ≤ ‖(W.Δ : ℚ_[p])‖) :
    padicValInt p W.Δ < 12 := by
  have hdn : ‖(W.Δ : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ ^ padicValInt p W.Δ := by
    rw [← norm_pow, Padic.norm_p_pow]
    rw [show (W.Δ : ℚ_[p]) = ((W.Δ : ℚ) : ℚ_[p]) by norm_cast,
      Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hΔ), padicValRat.of_int]
    push_cast
    rfl
  by_contra h
  have hd : 12 ≤ padicValInt p W.Δ := by omega
  have hn : ‖(W.Δ : ℚ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ 12 := by
    rw [hdn]
    exact pow_le_pow_of_le_one (norm_nonneg _) (Padic.norm_p_lt_one.le) hd
  have hA : ‖(C • W.map (Int.castRingHom ℚ_[p])).a₄‖ ≤ ‖(p : ℚ_[p])‖ ^ 4 := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity : 0 ≤ ‖(p : ℚ_[p])‖ ^ 4) (by norm_num : 3 ≠ 0)).mp
    rw [← pow_mul]
    exact h4.trans hn
  have hB : ‖(C • W.map (Int.castRingHom ℚ_[p])).a₆‖ ≤ ‖(p : ℚ_[p])‖ ^ 6 := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity : 0 ≤ ‖(p : ℚ_[p])‖ ^ 6) (by norm_num : 2 ≠ 0)).mp
    rw [← pow_mul]
    exact h6.trans hn
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let S : VariableChange ℚ_[p] := ⟨Units.mk0 p hp0, 0, 0, 0⟩
  have hi : IsIntegral ℤ_[p] ((S * C) • W.map (Int.castRingHom ℚ_[p])) := by
    rw [mul_smul]
    exact integral_short_scale _ h1 h2 h3 p hp0 hA hB
  apply not_integral_of_scale_prime W hΔ hm (S * C) ?_ hi
  change ↑(Units.mk0 (p : ℚ_[p]) hp0) * (C.u : ℚ_[p]) = p
  simp only [Units.val_mk0, hu, mul_one]

private lemma norm_prime (p : ℕ) [Fact p.Prime] :
    ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  simpa using PadicComplex.norm_extends' p (p : ℚ_[p]) |>.trans (Padic.norm_p)


/-- Unit norm of a scaled rational coordinate forces divisibility of its exponent. -/
private lemma twelve_dvd_of_norm_div_eq_one (p : ℕ) [Fact p.Prime]
    (π : ℂ_[p]) (hπ : π ^ 12 = (p : ℂ_[p]))
    (z : ℚ_[p]) (k : ℕ) (hn : ‖algebraMap ℚ_[p] ℂ_[p] z / π ^ k‖ = 1) : 12 ∣ k := by
  have hp0 : (p : ℝ) > 0 := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).ne_one
  have hπ0 : π ≠ 0 := by
    intro hh
    have : (p : ℂ_[p]) = 0 := by simpa [hh] using hπ.symm
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  have hz : z ≠ 0 := by
    intro hh
    simp [hh] at hn
  have hn' : ‖z‖ = ‖π‖ ^ k := by
    simpa only [norm_div, norm_pow, norm_algebraMap', div_eq_one_iff_eq
      (pow_ne_zero k (norm_ne_zero_iff.mpr hπ0))] using hn
  have heq : ‖z‖ ^ 12 = ‖(p : ℂ_[p])‖ ^ k := by
    rw [hn', ← pow_mul, Nat.mul_comm k 12, pow_mul, ← norm_pow, hπ]
  rw [Padic.norm_eq_zpow_neg_valuation hz, norm_prime] at heq
  have heq' : (p : ℝ) ^ (-z.valuation * 12 : ℤ) = (p : ℝ) ^ (-(k : ℤ)) := by
    norm_num [zpow_mul, zpow_neg, inv_pow] at heq ⊢
    exact heq
  have hexp := (zpow_right_inj₀ hp0 hp1).mp heq'
  have hd : (12 : ℤ) ∣ (k : ℤ) := ⟨z.valuation, by omega⟩
  exact_mod_cast hd

/-- Twelfth-root scaling turns an integral-j short equation into a good integral equation. -/
private theorem complex_good_short_scaling {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ_[p]) (h1 : E.a₁ = 0) (h2 : E.a₂ = 0) (h3 : E.a₃ = 0)
    (d : ℕ) (hd1 : 1 ≤ d) (hd11 : d ≤ 11)
    (hd : ‖E.Δ‖ = ‖(p : ℚ_[p])‖ ^ d)
    (h4 : ‖E.a₄‖ ^ 3 ≤ ‖E.Δ‖) (h6 : ‖E.a₆‖ ^ 2 ≤ ‖E.Δ‖) :
    ∃ (π : ℂ_[p]) (hπ : π ≠ 0) (D : WeierstrassCurve 𝓞_ℂ_[p]),
      π ^ 12 = (p : ℂ_[p]) ∧ D.a₁ = 0 ∧ D.a₂ = 0 ∧ D.a₃ = 0 ∧ IsUnit D.Δ ∧
      (⟨Units.mk0 (π ^ d) (pow_ne_zero d hπ), 0, 0, 0⟩ : VariableChange ℂ_[p]) •
        E.map (algebraMap ℚ_[p] ℂ_[p]) = D.map (PadicComplexInt p).subtype ∧
      (‖D.a₄.1‖ < 1 ∨ ¬ (4 ∣ d)) := by
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) (by norm_num : 0 < 12)
  have hπ0 : π ≠ 0 := by
    intro hh
    have : (p : ℂ_[p]) = 0 := by simpa [hh] using hπ.symm
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  have hnπ : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have hpn : ‖π‖ ^ 12 = ‖(p : ℚ_[p])‖ := by
    rw [← norm_pow, hπ]
    simpa using PadicComplex.norm_extends' p (p : ℚ_[p])
  have hdn : ‖E.Δ‖ = ‖π‖ ^ (12 * d) := by rw [hd, ← hpn, ← pow_mul]
  have hA : ‖E.a₄‖ ≤ ‖π‖ ^ (4 * d) := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity : 0 ≤ ‖π‖ ^ (4 * d)) (by norm_num : 3 ≠ 0)).mp
    rw [← pow_mul, show 4 * d * 3 = 12 * d by omega, ← hdn]
    exact h4
  have hB : ‖E.a₆‖ ≤ ‖π‖ ^ (6 * d) := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity : 0 ≤ ‖π‖ ^ (6 * d)) (by norm_num : 2 ≠ 0)).mp
    rw [← pow_mul, show 6 * d * 2 = 12 * d by omega, ← hdn]
    exact h6
  let S : VariableChange ℂ_[p] := ⟨Units.mk0 (π ^ d) (pow_ne_zero d hπ0), 0, 0, 0⟩
  let T := S • E.map (algebraMap ℚ_[p] ℂ_[p])
  have ht1 : T.a₁ = 0 := by simp [T, S, variableChange_a₁, h1]
  have ht2 : T.a₂ = 0 := by simp [T, S, variableChange_a₂, h1, h2]
  have ht3 : T.a₃ = 0 := by simp [T, S, variableChange_a₃, h1, h3]
  have ht4 : T.a₄ = algebraMap ℚ_[p] ℂ_[p] E.a₄ / π ^ (4 * d) := by
    simp only [T, S, variableChange_a₄, map_a₁, map_a₂, map_a₃, map_a₄,
      zero_mul, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), Units.val_mk0,
      Units.val_inv_eq_inv_val]
    simp only [inv_pow, ← pow_mul, Nat.mul_comm d 4, div_eq_inv_mul]
  have ht6 : T.a₆ = algebraMap ℚ_[p] ℂ_[p] E.a₆ / π ^ (6 * d) := by
    simp only [T, S, variableChange_a₆, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      zero_mul, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0), Units.val_mk0, Units.val_inv_eq_inv_val]
    simp only [inv_pow, ← pow_mul, Nat.mul_comm d 6, div_eq_inv_mul]
  have hn4 : ‖T.a₄‖ ≤ 1 := by
    rw [ht4, norm_div, norm_algebraMap', norm_pow]
    exact (div_le_one (pow_pos hnπ _)).mpr hA
  have hn6 : ‖T.a₆‖ ≤ 1 := by
    rw [ht6, norm_div, norm_algebraMap', norm_pow]
    exact (div_le_one (pow_pos hnπ _)).mpr hB
  have hmem (z : ℂ_[p]) : z ∈ PadicComplexInt p ↔ ‖z‖ ≤ 1 := by
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff (L := ℂ_[p]) (Γ₀ := NNReal) (x := z)).symm
  let D : WeierstrassCurve 𝓞_ℂ_[p] := ⟨0, 0, 0, ⟨T.a₄, (hmem _).mpr hn4⟩, ⟨T.a₆, (hmem _).mpr hn6⟩⟩
  have hTD : T = D.map (PadicComplexInt p).subtype := by
    ext <;> simp [D, ht1, ht2, ht3]
  have hΔn : ‖(D.Δ : ℂ_[p])‖ = 1 := by
    change ‖(PadicComplexInt p).subtype D.Δ‖ = 1
    rw [← WeierstrassCurve.map_Δ, ← hTD]
    simp only [T, variableChange_Δ, S, Units.val_inv_eq_inv_val, Units.val_mk0,
      norm_mul, norm_pow, norm_inv, map_Δ, norm_algebraMap']
    rw [hdn, ← inv_pow, ← pow_mul, show d * 12 = 12 * d by omega]
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ hnπ.ne')
  have hunit : IsUnit D.Δ := by
    apply isUnit_iff_exists_inv.mpr
    have hinv : (D.Δ : ℂ_[p])⁻¹ ∈ PadicComplexInt p := by
      apply (hmem _).mpr
      rw [norm_inv, hΔn, inv_one]
    refine ⟨⟨(D.Δ : ℂ_[p])⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hΔn]; norm_num))
  refine ⟨π, hπ0, D, hπ, rfl, rfl, rfl, hunit, hTD, ?_⟩
  by_cases hfour : 4 ∣ d
  · left
    change ‖T.a₄‖ < 1
    apply lt_of_le_of_ne hn4
    intro heq
    have hn : ‖algebraMap ℚ_[p] ℂ_[p] E.a₄ / π ^ (4 * d)‖ = 1 := by
      rw [← ht4]
      exact heq
    have hdiv := twelve_dvd_of_norm_div_eq_one p π hπ E.a₄ (4 * d) hn
    omega
  · exact Or.inr hfour

/-- An additive minimal equation with integral j acquires good reduction after twelfth-root scaling. -/
private theorem exists_good_scaling (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hmin : WeierstrassCurve.IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p]))) (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : (p : ℤ) ∣ W.c₄) (hj : ((p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3)) : ∃ (π : ℂ_[p]) (hπ : π ≠ 0) (d : ℕ) (C₀ : WeierstrassCurve.VariableChange ℚ) (D : WeierstrassCurve 𝓞_ℂ_[p]), π ^ 12 = (p : ℂ_[p]) ∧ 1 ≤ d ∧ d ≤ 11 ∧ (C₀.u : ℚ) = 1 ∧ ‖(C₀.r : ℚ_[p])‖ ≤ 1 ∧ ‖(C₀.s : ℚ_[p])‖ ≤ 1 ∧ ‖(C₀.t : ℚ_[p])‖ ≤ 1 ∧ D.a₁ = 0 ∧ D.a₂ = 0 ∧ D.a₃ = 0 ∧ IsUnit D.Δ ∧ ((⟨Units.mk0 (π ^ d) (pow_ne_zero d hπ), 0, 0, 0⟩ : WeierstrassCurve.VariableChange ℂ_[p]) * C₀.map (algebraMap ℚ ℂ_[p])) • (W.map (Int.castRingHom ℂ_[p])) = D.map (PadicComplexInt p).subtype ∧ (‖D.a₄.1‖ < 1 ∨ ¬ (4 ∣ d))  := by
  obtain ⟨C₀, hu0, hr, hs, ht, h1, h2, h3⟩ := rational_short_change W hp5
  let C : VariableChange ℚ_[p] := C₀.map (algebraMap ℚ ℚ_[p])
  let E := C • W.map (Int.castRingHom ℚ_[p])
  have hu : (C.u : ℚ_[p]) = 1 := by
    change algebraMap ℚ ℚ_[p] (C₀.u : ℚ) = 1
    rw [hu0, _root_.map_one]
  have he : E = (C₀ • W.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
    rw [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map]
    rfl
  have he1 : E.a₁ = 0 := by rw [he, map_a₁, h1, _root_.map_zero]
  have he2 : E.a₂ = 0 := by rw [he, map_a₂, h2, _root_.map_zero]
  have he3 : E.a₃ = 0 := by rw [he, map_a₃, h3, _root_.map_zero]
  have heΔ : E.Δ = (W.Δ : ℚ_[p]) := by
    simp only [E, variableChange_Δ, Units.val_inv_eq_inv_val, hu, inv_one, one_pow, one_mul, map_Δ]
    rfl
  have he4 : E.c₄ = (W.c₄ : ℚ_[p]) := by
    simp only [E, variableChange_c₄, Units.val_inv_eq_inv_val, hu, inv_one, one_pow, one_mul, map_c₄]
    rfl
  obtain ⟨hA, hB⟩ := short_norm_bounds W hΔ hp5 hj E he1 he2 he3 heΔ he4
  let d := padicValInt p W.Δ
  have hd1 : 1 ≤ d := by
    have h := (padicValInt_dvd_iff 1 W.Δ).mp (by simpa using hpΔ)
    rcases h with h | h
    · exact (hΔ h).elim
    · exact h
  have hd11 : d ≤ 11 := by
    have h := discriminant_exponent_lt_twelve W hΔ hmin C hu he1 he2 he3 hA hB
    omega
  have hdn : ‖E.Δ‖ = ‖(p : ℚ_[p])‖ ^ d := by
    rw [heΔ, ← norm_pow, Padic.norm_p_pow]
    rw [show (W.Δ : ℚ_[p]) = ((W.Δ : ℚ) : ℚ_[p]) by norm_cast,
      Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hΔ), padicValRat.of_int]
    push_cast
    rfl
  obtain ⟨π, hπ0, D, hπ, hd1', hd2', hd3', hunit, hmodel, hlast⟩ :=
    complex_good_short_scaling E he1 he2 he3 d hd1 hd11 hdn (heΔ ▸ hA) (heΔ ▸ hB)
  refine ⟨π, hπ0, d, C₀, D, hπ, hd1, hd11, hu0, hr, hs, ht, hd1', hd2', hd3', hunit, ?_, hlast⟩
  have hE : E.map (algebraMap ℚ_[p] ℂ_[p]) =
      C₀.map (algebraMap ℚ ℂ_[p]) • W.map (Int.castRingHom ℂ_[p]) := by
    simp only [E, C, ← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map,
      VariableChange.map_map, IsScalarTower.algebraMap_eq ℚ ℚ_[p] ℂ_[p]]
    have hf : (algebraMap ℚ_[p] ℂ_[p]).comp (Int.castRingHom ℚ_[p]) = Int.castRingHom ℂ_[p] := by
      ext; simp
    rw [hf]
  rw [mul_smul, ← hE]
  exact hmodel

/-- A parameter whose twelfth power is p-adic rational has a discrete norm bound. -/
private lemma norm_param_pow_lt_prime (p : ℕ) [Fact p.Prime] (hp : 14 ≤ p)
    (t : ℂ_[p]) (a : ℚ_[p]) (ha : t ^ 12 = algebraMap ℚ_[p] ℂ_[p] a)
    (ht : ‖t‖ < 1) : ‖t‖ ^ (p - 1) < ‖(p : ℂ_[p])‖ := by
  have hn : ‖t‖ ^ 12 = ‖a‖ := by
    rw [← norm_pow, ha]
    simp
  have ha1 : ‖a‖ < 1 := hn ▸ pow_lt_one₀ (norm_nonneg t) ht (by omega)
  have haP : ‖a‖ ≤ (p : ℝ)⁻¹ := by
    have hh := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one a 0).mp (by simpa using ha1)
    simpa using hh
  by_cases ht0 : t = 0
  · subst t
    simp only [norm_zero, zero_pow (show p - 1 ≠ 0 by omega)]
    exact norm_pos_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hpos : 0 < ‖t‖ ^ 12 := pow_pos (norm_pos_iff.mpr ht0) _
  have hsplit : p - 1 = 12 + (p - 13) := by omega
  calc
    ‖t‖ ^ (p - 1) = ‖t‖ ^ 12 * ‖t‖ ^ (p - 13) := by rw [hsplit, pow_add]
    _ < ‖t‖ ^ 12 * 1 := mul_lt_mul_of_pos_left
      (pow_lt_one₀ (norm_nonneg t) ht (by omega)) hpos
    _ = ‖a‖ := by rw [mul_one, hn]
    _ ≤ (p : ℝ)⁻¹ := haP
    _ = ‖(p : ℂ_[p])‖ := (norm_prime p).symm

/-- A point with zero ordinate on a short Weierstrass curve is killed by two. -/
private theorem two_nsmul_eq_zero_of_short_y_eq_zero {k : Type*} [Field k] [DecidableEq k]
    (E : WeierstrassCurve.Affine k) (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0)
    {x y : k} (h : E.Nonsingular x y) (hy : y = 0) :
    2 • (some x y h : E.Point) = 0 := by
  classical
  rw [two_nsmul]
  apply add_self_of_Y_eq
  simp [negY, ha₁, ha₃, hy]

/-- A point with zero abscissa on a short curve with zero linear coefficient is killed by three. -/
private theorem three_nsmul_eq_zero_of_short_x_eq_zero {k : Type*} [Field k] [DecidableEq k]
    (E : WeierstrassCurve.Affine k) (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0)
    (ha₃ : E.a₃ = 0) (ha₄ : E.a₄ = 0)
    {x y : k} (h : E.Nonsingular x y) (hx : x = 0) :
    3 • (some x y h : E.Point) = 0 := by
  classical
  subst x
  have hy : y ≠ E.negY 0 y := by
    have hn := (E.nonsingular_iff 0 y).mp h
    simpa [negY, ha₁, ha₂, ha₃, ha₄] using hn.2
  have hs : E.slope 0 0 y y = 0 := by
    rw [slope_of_Y_ne rfl hy]
    simp [ha₁, ha₂, ha₄]
  have hd : (some 0 y h : E.Point) + some 0 y h = -some 0 y h := by
    rw [add_self_of_Y_ne hy, neg_some]
    rw [some.injEq]
    simp [addX, addY, negAddY, hs, ha₁, ha₂, ha₃, negY]
  rw [show (3 : ℕ) = 2 + 1 by rfl, add_nsmul, two_nsmul, one_nsmul, hd, neg_add_cancel]

end PrimeLocal


namespace PrimeLocal

private lemma integral_norm_le_one (p : ℕ) [Fact p.Prime] (z : 𝓞_ℂ_[p]) :
    ‖(z : ℂ_[p])‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff (L := ℂ_[p]) (Γ₀ := NNReal)).mpr z.property

private lemma integral_unit_norm (p : ℕ) [Fact p.Prime] (z : 𝓞_ℂ_[p])
    (hz : IsUnit z) : ‖(z : ℂ_[p])‖ = 1 := by
  obtain ⟨u, rfl⟩ := hz
  have hu := integral_norm_le_one p (↑u : 𝓞_ℂ_[p])
  have hv := integral_norm_le_one p (↑u⁻¹ : 𝓞_ℂ_[p])
  have hm : ‖((u : 𝓞_ℂ_[p]) : ℂ_[p])‖ * ‖((↑u⁻¹ : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul]
    norm_cast
    simp
  nlinarith [norm_nonneg (((u : 𝓞_ℂ_[p]) : ℂ_[p]))]

private lemma residue_zero_of_norm_lt_one (p : ℕ) [Fact p.Prime] (z : 𝓞_ℂ_[p])
    (hz : ‖(z : ℂ_[p])‖ < 1) : IsLocalRing.residue 𝓞_ℂ_[p] z = 0 := by
  by_contra hn
  have hu := (IsLocalRing.residue_ne_zero_iff_isUnit z).mp hn
  have he := integral_unit_norm p z hu
  linarith


private lemma affine_point_eq_zero_of_two_or_three_torsion {k : Type*} [Field k] [DecidableEq k]
    (E : WeierstrassCurve.Affine k) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (P : E.Point) (hP : p • P = 0) (hn : 2 • P = 0 ∨ 3 • P = 0) : P = 0 := by
  have hd : addOrderOf P ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hP
  have ho : addOrderOf P = 1 := by
    rcases (Nat.dvd_prime hp).mp hd with hh | hh
    · exact hh
    · rcases hn with hn | hn
      · have hh2 : p ∣ 2 := hh ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn
        have := Nat.le_of_dvd (by decide : 0 < 2) hh2
        omega
      · have hh3 : p ∣ 3 := hh ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn
        have := Nat.le_of_dvd (by decide : 0 < 3) hh3
        omega
  have hone : (1 : ℕ) • P = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [ho])
  simpa using hone

/-- An integral affine prime-torsion point cannot occur in the degree-twelve scaling configuration. -/
private theorem no_integral_scaled_prime_torsion (p : ℕ) [Fact p.Prime] [DecidableEq ℂ_[p]]
    (hp5 : 5 ≤ p) (π : ℂ_[p]) (d : ℕ) (hd1 : 1 ≤ d) (hd11 : d ≤ 11)
    (D : WeierstrassCurve 𝓞_ℂ_[p])
    (ha₁ : D.a₁ = 0) (ha₂ : D.a₂ = 0) (ha₃ : D.a₃ = 0) (hΔ : IsUnit D.Δ)
    (ha₄ : ‖D.a₄.1‖ < 1 ∨ ¬4 ∣ d)
    (hdiv : ∀ (z : ℚ_[p]) (k : ℕ), ‖algebraMap ℚ_[p] ℂ_[p] z / π ^ k‖ = 1 → 12 ∣ k)
    (x₀ y₀ : ℚ_[p]) (X Y : ℂ_[p])
    (hX : X = algebraMap ℚ_[p] ℂ_[p] x₀ / π ^ (2*d))
    (hY : Y = algebraMap ℚ_[p] ℂ_[p] y₀ / π ^ (3*d))
    (h : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular X Y)
    (hP : p • (some X Y h) = 0) (hXm : X ∈ PadicComplexInt p) : False := by
  classical
  let A := PadicComplexInt p
  let xr : A := ⟨X, hXm⟩
  let yr : A := ⟨Y, Affine.Y_mem_of_X_mem D h.1 hXm⟩
  let E := (D.map (IsLocalRing.residue A)).toAffine
  have hΔr : (D.map (IsLocalRing.residue A)).Δ ≠ 0 :=
    (WeierstrassCurve.map_residue_Δ_ne_zero_iff D).mpr hΔ
  have hr : E.Nonsingular (IsLocalRing.residue A xr) (IsLocalRing.residue A yr) :=
    Affine.nonsingular_residue D hΔr h.1
  let P : E.Point := some _ _ hr
  have hred : WeierstrassCurve.reduceHom hΔr (some X Y h) = P :=
    WeierstrassCurve.reducePoint_some_of_mem hΔr h hXm
  have hpP : p • P = 0 := by
    rw [← hred, ← map_nsmul, hP, _root_.map_zero]
  have he₁ : E.a₁ = 0 := by simp [E, ha₁]
  have he₂ : E.a₂ = 0 := by simp [E, ha₂]
  have he₃ : E.a₃ = 0 := by simp [E, ha₃]
  have hn : 2 • P = 0 ∨ 3 • P = 0 := by
    by_cases hy : IsLocalRing.residue A yr = 0
    · exact Or.inl (two_nsmul_eq_zero_of_short_y_eq_zero E he₁ he₃ hr hy)
    · have hyn : ‖Y‖ = 1 := integral_unit_norm p yr
        ((IsLocalRing.residue_ne_zero_iff_isUnit yr).mp hy)
      have hdy : 12 ∣ 3 * d := hdiv y₀ (3*d) (hY ▸ hyn)
      have hd4 : 4 ∣ d := by omega
      have hx : IsLocalRing.residue A xr = 0 := by
        by_contra hx
        have hxn : ‖X‖ = 1 := integral_unit_norm p xr
          ((IsLocalRing.residue_ne_zero_iff_isUnit xr).mp hx)
        have hdx : 12 ∣ 2 * d := hdiv x₀ (2*d) (hX ▸ hxn)
        omega
      have hA4 : ‖D.a₄.1‖ < 1 := ha₄.resolve_right (not_not.mpr hd4)
      have he₄ : E.a₄ = 0 := residue_zero_of_norm_lt_one p D.a₄ hA4
      exact Or.inr (three_nsmul_eq_zero_of_short_x_eq_zero E he₁ he₂ he₃ he₄ hr hx)
  have hz := affine_point_eq_zero_of_two_or_three_torsion E p Fact.out hp5 P hpP hn
  exact Point.some_ne_zero _ hz


/-- Degree-twelve scaled rational coordinates cannot support nonzero prime torsion. -/
private theorem no_scaled_prime_torsion (p : ℕ) [Fact p.Prime] [DecidableEq ℂ_[p]]
    (hp14 : 14 ≤ p) (π : ℂ_[p]) (hπ : π ^ 12 = (p : ℂ_[p]))
    (d : ℕ) (hd1 : 1 ≤ d) (hd11 : d ≤ 11)
    (D : WeierstrassCurve 𝓞_ℂ_[p])
    (ha₁ : D.a₁ = 0) (ha₂ : D.a₂ = 0) (ha₃ : D.a₃ = 0) (hΔ : IsUnit D.Δ)
    (ha₄ : ‖D.a₄.1‖ < 1 ∨ ¬4 ∣ d)
    (x₀ y₀ : ℚ_[p]) (X Y : ℂ_[p])
    (hX : X = algebraMap ℚ_[p] ℂ_[p] x₀ / π ^ (2*d))
    (hY : Y = algebraMap ℚ_[p] ℂ_[p] y₀ / π ^ (3*d))
    (h : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular X Y)
    (hP : p • (some X Y h) = 0) : False := by
  classical
  by_cases hXm : X ∈ PadicComplexInt p
  · exact no_integral_scaled_prime_torsion p (by omega) π d hd1 hd11 D ha₁ ha₂ ha₃ hΔ ha₄
      (twelve_dvd_of_norm_div_eq_one p π hπ) x₀ y₀ X Y hX hY h hP hXm
  have hmem : ∀ z : ℂ_[p], z ∈ PadicComplexInt p ↔ ‖z‖ ≤ 1 := by
    intro z
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff (L := ℂ_[p]) (Γ₀ := NNReal) (x := z)).symm
  have hXnorm : 1 < ‖X‖ := lt_of_not_ge (fun hh => hXm ((hmem X).mpr hh))
  have hX0 : X ≠ 0 := fun hh => hXm (hh ▸ (PadicComplexInt p).zero_mem)
  have hY0 : Y ≠ 0 := Affine.Y_ne_zero_of_X_notMem D h.1 hXm
  have ht0 : X / Y ≠ 0 := div_ne_zero hX0 hY0
  have htn : X / Y ∈ (PadicComplexInt p).nonunits := Affine.X_div_Y_mem_nonunits D h.1 hXm
  have ht : ‖X / Y‖ < 1 := by
    have hinv : (X / Y)⁻¹ ∉ PadicComplexInt p :=
      ((PadicComplexInt p).mem_nonunits_iff_or.mp htn).resolve_left ht0
    by_contra hh
    apply hinv
    rw [hmem, norm_inv]
    exact inv_le_one_of_one_le₀ (le_of_not_gt hh)
  have hπ0 : π ≠ 0 := by
    intro hh
    have hp0 := (Fact.out : p.Prime).ne_zero
    have hh' : (p : ℂ_[p]) = 0 := by simpa [hh] using hπ.symm
    exact (Nat.cast_ne_zero.mpr hp0) hh'
  have hy₀ : y₀ ≠ 0 := by
    intro hh
    apply hY0
    simp [hY, hh]
  have hym : algebraMap ℚ_[p] ℂ_[p] y₀ ≠ 0 := (map_ne_zero (algebraMap ℚ_[p] ℂ_[p])).mpr hy₀
  have hpow : π ^ (3*d) = π ^ (2*d) * π ^ d := by
    rw [← pow_add]
    congr 1
    omega
  have hr : X / Y = algebraMap ℚ_[p] ℂ_[p] (x₀ / y₀) * π ^ d := by
    rw [hX, hY, hpow]
    rw [_root_.map_div₀ (algebraMap ℚ_[p] ℂ_[p]) x₀ y₀]
    field_simp
  have hrat : (X / Y) ^ 12 =
      algebraMap ℚ_[p] ℂ_[p] ((x₀ / y₀) ^ 12 * (p : ℚ_[p]) ^ d) := by
    rw [hr, mul_pow, ← pow_mul, Nat.mul_comm d 12, pow_mul, hπ]
    simp
  have hlt := norm_param_pow_lt_prime p hp14 (X/Y)
    ((x₀/y₀)^12 * (p : ℚ_[p])^d) hrat ht
  have hle := norm_prime_le_norm_param_pow_of_prime_torsion p D hΔ.ne_zero X Y h hXnorm hP
  exact (not_lt_of_ge hle) hlt

private lemma complex_rat_algebraMap (p : ℕ) [Fact p.Prime] (q : ℚ) :
    algebraMap ℚ ℂ_[p] q = (q : ℂ_[p]) := by
  exact congrArg (fun f : ℚ →+* ℂ_[p] => f q)
    (Subsingleton.elim (algebraMap ℚ ℂ_[p]) (Rat.castHom ℂ_[p]))

/-- Transport a rational torsion point through a rational translation and a pure scale. -/
private lemma scaled_point_of_rational_point (p : ℕ) [Fact p.Prime] [DecidableEq ℂ_[p]]
    (W : WeierstrassCurve ℤ) (C : VariableChange ℚ) (hu : (C.u : ℚ) = 1)
    (u : ℂ_[p]ˣ) (D : WeierstrassCurve 𝓞_ℂ_[p])
    (hC : ((⟨u, 0, 0, 0⟩ : VariableChange ℂ_[p]) * C.map (algebraMap ℚ ℂ_[p])) •
      W.map (Int.castRingHom ℂ_[p]) = D.map (PadicComplexInt p).subtype)
    (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y)
    (hP : p • Point.some x y h = 0) :
    ∃ x₀ y₀ : ℚ, ∃ hD : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular
      ((x₀ : ℂ_[p]) / (u : ℂ_[p]) ^ 2) ((y₀ : ℂ_[p]) / (u : ℂ_[p]) ^ 3),
      p • Point.some _ _ hD = 0 := by
  classical
  let x₀ := x - C.r
  let y₀ := y - C.t - C.s * (x - C.r)
  let E := W.map (Int.castRingHom ℂ_[p])
  have hc : E.toAffine.Nonsingular (x : ℂ_[p]) (y : ℂ_[p]) := by
    have hh := ((W.map (Int.castRingHom ℚ)).toAffine.map_nonsingular
      (f := algebraMap ℚ ℂ_[p]) (algebraMap ℚ ℂ_[p]).injective x y).mpr h
    have hw : (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ_[p]) = E := by
      rw [WeierstrassCurve.map_map]
      simp only [E, RingHom.eq_intCast']
    change ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ_[p])).toAffine.Nonsingular
      (x : ℂ_[p]) (y : ℂ_[p]) at hh
    rw [hw] at hh
    exact hh
  have hwQ : W.toAffine⁄ℚ = (W.map (Int.castRingHom ℚ)).toAffine := by
    simp only [WeierstrassCurve.baseChange, RingHom.eq_intCast']
  have hwC : W.toAffine⁄ℂ_[p] = E.toAffine := by
    simp only [E, WeierstrassCurve.baseChange, RingHom.eq_intCast']
  have hPc : p • Point.some (x : ℂ_[p]) (y : ℂ_[p]) hc = 0 := by
    have hq : (W.toAffine⁄ℚ).Nonsingular x y := by
      rw [hwQ]
      exact h
    have hpq : p • Point.some x y hq = 0 := by
      revert hq
      rw [hwQ]
      intro hq
      exact hP
    have hh := congrArg (Point.baseChange (W' := W.toAffine) ℚ ℂ_[p]) hpq
    rw [map_nsmul, _root_.map_zero] at hh
    change p • Point.some (algebraMap ℚ ℂ_[p] x) (algebraMap ℚ ℂ_[p] y) _ = 0 at hh
    revert hc
    rw [← hwC]
    intro hc
    simpa only [complex_rat_algebraMap] using hh
  let S : VariableChange ℂ_[p] := ⟨u, 0, 0, 0⟩ * C.map (algebraMap ℚ ℂ_[p])
  let g : E.toAffine.Point →+ (S • E).toAffine.Point :=
    { toFun := Point.vcInvFun S E.toAffine
      map_zero' := rfl
      map_add' := Point.vcInvFun_add S E.toAffine }
  have hPs : p • g (Point.some _ _ hc) = 0 := by
    rw [← map_nsmul, hPc, _root_.map_zero]
  have hx : vcXInv S (x : ℂ_[p]) = (x₀ : ℂ_[p]) / (u : ℂ_[p]) ^ 2 := by
    simp only [vcXInv, S, VariableChange.mul_def, VariableChange.map, Units.val_inv_eq_inv_val,
      Units.val_mul, Units.coe_map, hu, map_one, one_pow, zero_mul, add_zero,
      mul_zero, zero_add, x₀, Rat.cast_sub, complex_rat_algebraMap]
    ring
  have hy : vcYInv S (x : ℂ_[p]) (y : ℂ_[p]) =
      (y₀ : ℂ_[p]) / (u : ℂ_[p]) ^ 3 := by
    simp only [vcYInv, S, VariableChange.mul_def, VariableChange.map, Units.val_inv_eq_inv_val,
      Units.val_mul, Units.coe_map, hu, map_one, one_pow, zero_mul, add_zero,
      mul_zero, zero_add, y₀, Rat.cast_sub, Rat.cast_mul, complex_rat_algebraMap]
    ring
  have hDs : (S • E).toAffine.Nonsingular
      ((x₀ : ℂ_[p]) / (u : ℂ_[p]) ^ 2) ((y₀ : ℂ_[p]) / (u : ℂ_[p]) ^ 3) := by
    rw [← hx, ← hy]
    exact (nonsingular_variableChange_iff _ _).mpr (by simpa using hc)
  refine ⟨x₀, y₀, ?_⟩
  change S • E = _ at hC
  rw [← hC]
  refine ⟨hDs, ?_⟩
  change p • Point.some (vcXInv S (x : ℂ_[p])) (vcYInv S (x : ℂ_[p]) (y : ℂ_[p])) _ = 0 at hPs
  simpa only [hx, hy] using hPs

/-- A rational point of prime order excludes additive reduction with integral j at that prime. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime] (hmin : WeierstrassCurve.IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p]))) (hp17 : 17 ≤ p) (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : (p : ℤ) ∣ W.c₄) (hj : ((p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3)) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) : False := by
  classical
  obtain ⟨π, hπ0, d, C₀, D, hπ, hd1, hd11, hu, _, _, _, ha₁, ha₂, ha₃, hDΔ, hmodel, ha₄⟩ :=
    exists_good_scaling W hΔ (by omega) hmin hpΔ hpc₄ hj
  have hpP : p • (some x y h) = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero _
  obtain ⟨x₀, y₀, hD, hpD⟩ := scaled_point_of_rational_point p W C₀ hu
    (Units.mk0 (π ^ d) (pow_ne_zero d hπ0)) D hmodel x y h hpP
  apply no_scaled_prime_torsion p (by omega) π hπ d hd1 hd11 D ha₁ ha₂ ha₃ hDΔ ha₄
    (x₀ : ℚ_[p]) (y₀ : ℚ_[p]) _ _ ?_ ?_ hD hpD
  · simp only [Units.val_mk0, map_ratCast, ← pow_mul, Nat.mul_comm d 2]
  · simp only [Units.val_mk0, map_ratCast, ← pow_mul, Nat.mul_comm d 3]
end PrimeLocal
