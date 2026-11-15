-- Prove2me | solution 1 for PrimeLocal.exists_inertia_negating_tate_sign_of_additive_nonintegral_j
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:15:50.142503+00:00
-- url     : https://prove2.me/submissions/9c1a2a13-03c1-42fe-a034-d47f982929c6

import Theorems.Thm_PadicAlgCl_exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
import Theorems.Thm_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_TateCurve_TateParameter

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v


namespace PrimeLocal

/-- A variable change fixed by the Galois group descends to the base field. -/
private theorem exists_variableChange_map_of_galois_fixed
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (C : WeierstrassCurve.VariableChange L)
    (hfixed : ∀ σ : L ≃ₐ[K] L, C.map σ.toAlgHom.toRingHom = C) :
    ∃ C₀ : WeierstrassCurve.VariableChange K, C₀.map (algebraMap K L) = C := by
  have hu : ∀ σ : L ≃ₐ[K] L, σ (C.u : L) = (C.u : L) := by
    intro σ
    exact congrArg (fun D : WeierstrassCurve.VariableChange L => (D.u : L)) (hfixed σ)
  have hr : ∀ σ : L ≃ₐ[K] L, σ C.r = C.r := by
    intro σ
    exact congrArg WeierstrassCurve.VariableChange.r (hfixed σ)
  have hs : ∀ σ : L ≃ₐ[K] L, σ C.s = C.s := by
    intro σ
    exact congrArg WeierstrassCurve.VariableChange.s (hfixed σ)
  have ht : ∀ σ : L ≃ₐ[K] L, σ C.t = C.t := by
    intro σ
    exact congrArg WeierstrassCurve.VariableChange.t (hfixed σ)
  obtain ⟨u, hu⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (K := L)
    (k := K) (C.u : L)).mpr hu
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (K := L)
    (k := K) C.r).mpr hr
  obtain ⟨s, hs⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (K := L)
    (k := K) C.s).mpr hs
  obtain ⟨t, ht⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (K := L)
    (k := K) C.t).mpr ht
  have hu0 : u ≠ 0 := by
    intro h
    have hzero : (C.u : L) = 0 := by simpa [h] using hu.symm
    exact C.u.ne_zero hzero
  refine ⟨⟨Units.mk0 u hu0, r, s, t⟩, ?_⟩
  apply WeierstrassCurve.VariableChange.ext
  · apply Units.ext
    exact hu
  · exact hr
  · exact hs
  · exact ht

/-- An integral equation isomorphic to a minimal additive equation cannot have unit c₄. -/
private theorem not_integral_unit_c₄_of_minimal_additive
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (hmin : WeierstrassCurve.IsMinimal R W)
    (D : WeierstrassCurve.VariableChange K)
    (hU : WeierstrassCurve.IsIntegral R (D • W))
    (hc₄ : IsDedekindDomain.HeightOneSpectrum.valuation K
      (IsDiscreteValuationRing.maximalIdeal R) W.c₄ < 1)
    (hUc₄ : IsDedekindDomain.HeightOneSpectrum.valuation K
      (IsDiscreteValuationRing.maximalIdeal R) (D • W).c₄ = 1) : False := by
  letI := hmin
  letI := hU
  let v := IsDedekindDomain.HeightOneSpectrum.valuation K
    (IsDiscreteValuationRing.maximalIdeal R)
  have hscale : 1 < v (↑D.u⁻¹ : K) := by
    by_contra h
    have hle : v (↑D.u⁻¹ : K) ≤ 1 := le_of_not_gt h
    have hp : v (↑D.u⁻¹ : K) ^ 4 ≤ 1 := pow_le_one₀ zero_le hle
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ v W.c₄ from zero_le)
    have hid : v (D • W).c₄ = v (↑D.u⁻¹ : K) ^ 4 * v W.c₄ := by
      simp only [WeierstrassCurve.variableChange_c₄, map_mul, map_pow]
    rw [← hid, hUc₄, one_mul] at hm
    exact (not_le_of_gt hc₄) hm
  have hpow : 1 < v (↑D.u⁻¹ : K) ^ 12 := by
    exact one_lt_pow₀ hscale (by norm_num)
  have hΔpos : 0 < v W.Δ := by
    exact lt_of_le_of_ne zero_le ((map_ne_zero v).mpr hΔ).symm
  have hstrict : v W.Δ < v (D • W).Δ := by
    calc
      v W.Δ = 1 * v W.Δ := (one_mul _).symm
      _ < v (↑D.u⁻¹ : K) ^ 12 * v W.Δ := mul_lt_mul_of_pos_right hpow hΔpos
      _ = v (D • W).Δ := by
        simp only [WeierstrassCurve.variableChange_Δ, map_mul, map_pow]
  have haux : WeierstrassCurve.valuation_Δ_aux R W <
      WeierstrassCurve.valuation_Δ_aux R (D • W) := by
    change (WeierstrassCurve.valuation_Δ_aux R W : WithZero (Multiplicative ℤ)) <
      (WeierstrassCurve.valuation_Δ_aux R (D • W) : WithZero (Multiplicative ℤ))
    simpa only [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral] using hstrict
  have hmax := hmin.val_Δ_maximal.2 hU
  simp only [one_smul] at hmax
  exact (not_le_of_gt haux) (hmax (le_of_lt haux))

/-- No integral variable change of an additive minimal integer model has c₄ of norm one. -/
private theorem not_integral_norm_c₄_one_of_minimal_additive
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (q : ℕ) [Fact q.Prime]
    (hmin : WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q])))
    (hqc₄ : (q : ℤ) ∣ W.c₄)
    (D : WeierstrassCurve.VariableChange ℚ_[q])
    (hU : WeierstrassCurve.IsIntegral ℤ_[q] (D • W.map (Int.castRingHom ℚ_[q])))
    (hUnorm : ‖(D • W.map (Int.castRingHom ℚ_[q])).c₄‖ = 1) : False := by
  letI := hU
  let U := D • W.map (Int.castRingHom ℚ_[q])
  let z : ℤ_[q] := (WeierstrassCurve.integralModel ℤ_[q] U).c₄
  have hz : (z : ℚ_[q]) = U.c₄ := WeierstrassCurve.integralModel_c₄_eq ℤ_[q] U
  have hznorm : ‖z‖ = 1 := by
    rw [PadicInt.norm_def, hz]
    exact hUnorm
  have hznot : z ∉ (IsDiscreteValuationRing.maximalIdeal ℤ_[q]).asIdeal := by
    change z ∉ IsLocalRing.maximalIdeal ℤ_[q]
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    intro hdvd
    have hlt := (PadicInt.norm_lt_one_iff_dvd z).mpr hdvd
    rw [hznorm] at hlt
    exact (lt_irrefl _) hlt
  have hUc₄ : IsDedekindDomain.HeightOneSpectrum.valuation ℚ_[q]
      (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) U.c₄ = 1 := by
    rw [← hz]
    apply le_antisymm
    · exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
        (K := ℚ_[q]) (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) z
    · apply le_of_not_gt
      intro hlt
      exact hznot ((IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (K := ℚ_[q]) (IsDiscreteValuationRing.maximalIdeal ℤ_[q]) z).mp hlt)
  have hc₄ : IsDedekindDomain.HeightOneSpectrum.valuation ℚ_[q]
      (IsDiscreteValuationRing.maximalIdeal ℤ_[q])
      (W.map (Int.castRingHom ℚ_[q])).c₄ < 1 := by
    rw [WeierstrassCurve.map_c₄]
    have hzmem : (W.c₄ : ℤ_[q]) ∈ IsLocalRing.maximalIdeal ℤ_[q] := by
      simpa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
        ← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_int_lt_one_iff_dvd] using hqc₄
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (K := ℚ_[q]) (IsDiscreteValuationRing.maximalIdeal ℤ_[q])
      (W.c₄ : ℤ_[q])).mpr hzmem
  apply not_integral_unit_c₄_of_minimal_additive
    (W.map (Int.castRingHom ℚ_[q])) _ hmin D hU hc₄ hUc₄
  rw [WeierstrassCurve.map_Δ]
  change (W.Δ : ℚ_[q]) ≠ 0
  exact_mod_cast hΔ

/-- Away from two, dividing a difference of units by four preserves integrality. -/
private theorem norm_unit_sub_one_div_four_le_one (q : ℕ) [Fact q.Prime]
    (v : ℚ_[q]) (hv : ‖v‖ = 1)
    (h₂ : q = 2 → ‖(v - 1) / 4‖ ≤ 1) : ‖(v - 1) / 4‖ ≤ 1 := by
  by_cases hq₂ : q = 2
  · exact h₂ hq₂
  have hprime : q.Prime := Fact.out
  have hnot : ¬ q ∣ 2 := by
    intro hdvd
    have heq : q = 1 ∨ q = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd
    exact hq₂ (heq.resolve_left hprime.ne_one)
  have hnorm₂ : ‖(2 : ℚ_[q])‖ = 1 := by
    exact Padic.norm_natCast_eq_one_iff.mpr (hprime.coprime_iff_not_dvd.mpr hnot)
  have hnorm₄ : ‖(4 : ℚ_[q])‖ = 1 := by
    rw [show (4 : ℚ_[q]) = 2 ^ 2 by norm_num, norm_pow, hnorm₂, one_pow]
  rw [norm_div, hnorm₄, div_one]
  calc
    ‖v - 1‖ ≤ max ‖v‖ ‖(1 : ℚ_[q])‖ := by simpa only [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max v (-1 : ℚ_[q])
    _ = 1 := by rw [hv, norm_one, max_self]

/-- The c₄ invariant of the integral unit twist is the original invariant times the square unit. -/
private theorem unit_tate_twist_c₄ (q : ℕ) [Fact q.Prime] (v qT : ℚ_[q]) :
    (⟨1, (v - 1) / 4, 0, v ^ 2 * TateCurve.a₄ qT,
      v ^ 3 * TateCurve.a₆ qT⟩ : WeierstrassCurve ℚ_[q]).c₄ =
      v ^ 2 * (TateCurve.curve qT).c₄ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    TateCurve.curve_a₁, TateCurve.curve_a₂, TateCurve.curve_a₃, TateCurve.curve_a₄]
  ring

/-- The Tate unit twist is integral and its c₄ is a unit. -/
private theorem unit_tate_twist_integral_and_norm_c₄
    (q : ℕ) [Fact q.Prime] (v qT : ℚ_[q])
    (hv : ‖v‖ = 1) (hqT : ‖qT‖₊ < 1)
    (h₂ : q = 2 → ‖(v - 1) / 4‖ ≤ 1) :
    WeierstrassCurve.IsIntegral ℤ_[q]
      (⟨1, (v - 1) / 4, 0, v ^ 2 * TateCurve.a₄ qT,
        v ^ 3 * TateCurve.a₆ qT⟩ : WeierstrassCurve ℚ_[q]) ∧
    ‖(⟨1, (v - 1) / 4, 0, v ^ 2 * TateCurve.a₄ qT,
      v ^ 3 * TateCurve.a₆ qT⟩ : WeierstrassCurve ℚ_[q]).c₄‖ = 1 := by
  constructor
  · apply WeierstrassCurve.isIntegral_of_exists_lift ℤ_[q]
    · exact ⟨1, by simp⟩
    · exact ⟨⟨(v - 1) / 4, norm_unit_sub_one_div_four_le_one q v hv h₂⟩, rfl⟩
    · exact ⟨0, by simp⟩
    · refine ⟨⟨v ^ 2 * TateCurve.a₄ qT, ?_⟩, rfl⟩
      rw [norm_mul, norm_pow, hv, one_pow, one_mul]
      exact_mod_cast (TateCurve.nnnorm_a₄_le hqT).trans hqT.le
    · refine ⟨⟨v ^ 3 * TateCurve.a₆ qT, ?_⟩, rfl⟩
      rw [norm_mul, norm_pow, hv, one_pow, one_mul]
      exact_mod_cast (TateCurve.nnnorm_a₆_le hqT).trans hqT.le
  · rw [unit_tate_twist_c₄, norm_mul, norm_pow, hv, one_pow, one_mul]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ)) (TateCurve.nnnorm_c₄ hqT)

/-- The value group of the inertia-fixed field is discrete. -/
private theorem norm_le_prime_of_inertia_fixed_of_norm_lt_one
    (q : ℕ) [Fact q.Prime] {x : PadicAlgCl q}
    (hfix : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (∀ y : PadicAlgCl q, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → σ x = x)
    (hx : ‖x‖ < 1) : ‖x‖ ≤ ‖(q : PadicAlgCl q)‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨n, hn⟩ := PadicAlgCl.exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
    q hx0 (fun σ hσ => hfix σ
      ((PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one q σ).mp hσ))
  have hp0 : 0 < ‖(q : PadicAlgCl q)‖ := norm_pos_iff.mpr
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hp1 : ‖(q : PadicAlgCl q)‖ < 1 := by
    have h := Padic.norm_p_lt_one (p := q)
    have heq : ‖(q : PadicAlgCl q)‖ = ‖(q : ℚ_[q])‖ := by
      simpa using norm_algebraMap' (PadicAlgCl q) (q : ℚ_[q])
    rwa [heq]
  have hnpos : 0 < n :=
    (zpow_lt_one_iff_right_of_lt_one₀ hp0 hp1).mp (hn ▸ hx)
  rw [hn]
  simpa using zpow_le_zpow_right_of_le_one₀ hp0 hp1.le (show (1 : ℤ) ≤ n by omega)

/-- A quadratic root fixed by inertia has an unramified square class, including at two. -/
private theorem exists_square_mul_unit_of_inertia_fixed_root
    (q : ℕ) [Fact q.Prime] (d : ℚ_[q]) (hd : d ≠ 0)
    (s : PadicAlgCl q)
    (hs : s ^ 2 = algebraMap ℚ_[q] (PadicAlgCl q) d)
    (hfix : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (∀ y : PadicAlgCl q, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → σ s = s) :
    ∃ m v : ℚ_[q], m ≠ 0 ∧ d = m ^ 2 * v ∧ ‖v‖ = 1 ∧
      (q = 2 → ‖(v - 1) / 4‖ ≤ 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    have hz : algebraMap ℚ_[q] (PadicAlgCl q) d = 0 := by simpa [h] using hs.symm
    exact hd ((algebraMap ℚ_[q] (PadicAlgCl q)).injective (by simpa using hz))
  obtain ⟨n, hn⟩ := PadicAlgCl.exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
    q hs0 (fun σ hσ => hfix σ
      ((PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one q σ).mp hσ))
  let m : ℚ_[q] := (q : ℚ_[q]) ^ n
  have hm0 : m ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hmn : ‖m‖ = ‖s‖ := by
    dsimp [m]
    rw [norm_zpow, hn]
    congr 1
    simpa using (norm_algebraMap' (PadicAlgCl q) (q : ℚ_[q])).symm
  let v : ℚ_[q] := d / m ^ 2
  let t : PadicAlgCl q := s / algebraMap ℚ_[q] (PadicAlgCl q) m
  have htsq : t ^ 2 = algebraMap ℚ_[q] (PadicAlgCl q) v := by
    dsimp [t, v]
    rw [div_pow, hs, map_div₀, map_pow]
  have htnorm : ‖t‖ = 1 := by
    dsimp [t]
    rw [norm_div, norm_algebraMap', hmn, div_self (norm_ne_zero_iff.mpr hs0)]
  have hv : ‖v‖ = 1 := by
    have h := congrArg norm htsq
    simpa [norm_pow, norm_algebraMap', htnorm] using h.symm
  refine ⟨m, v, hm0, ?_, hv, ?_⟩
  · dsimp [v]
    field_simp [hm0]
  intro hq
  subst q
  have htwo : ‖(2 : PadicAlgCl 2)‖ = (1 / 2 : ℝ) := by
    have heq : ‖(2 : PadicAlgCl 2)‖ = ‖(2 : ℚ_[2])‖ := by
      simpa only [map_ofNat] using norm_algebraMap' (PadicAlgCl 2) (2 : ℚ_[2])
    have hp : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
      simpa only [Nat.cast_ofNat] using Padic.norm_p (p := 2)
    exact heq.trans (hp.trans (by norm_num))
  let z : ℤ_[2] := ⟨v, hv.le⟩
  have hznorm : ‖z‖ = 1 := by
    simpa [z, PadicInt.norm_def] using hv
  have hzrep0 : z.zmodRepr ≠ 0 :=
    (PadicInt.norm_natCast_zmodRepr_eq_one_iff_ne z).mp
      (PadicInt.norm_natCast_zmodRepr_eq_one_iff.mpr hznorm)
  have hzrep : z.zmodRepr = 1 := by
    have := PadicInt.zmodRepr_lt_p z
    omega
  have hvsmall : ‖v - 1‖ < 1 := by
    have h := PadicInt.norm_sub_zmodRepr_lt_one z
    rw [hzrep] at h
    change ‖((z - 1 : ℤ_[2]) : ℚ_[2])‖ < 1 at h
    change ‖v - 1‖ < 1 at h
    exact h
  have htprod : ‖(t - 1) * (t + 1)‖ < 1 := by
    have heq : (t - 1) * (t + 1) = algebraMap ℚ_[2] (PadicAlgCl 2) (v - 1) := by
      rw [map_sub, map_one, ← htsq]
      ring
    rw [heq, norm_algebraMap']
    exact hvsmall
  have htminusle : ‖t - 1‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (t) (-1 : PadicAlgCl 2)
    simpa [sub_eq_add_neg, htnorm] using h
  have htminus : ‖t - 1‖ < 1 := by
    by_contra h
    have heq : ‖t - 1‖ = 1 := le_antisymm htminusle (le_of_not_gt h)
    have htplus : ‖t + 1‖ < 1 := by
      simpa [norm_mul, heq] using htprod
    have htri := IsUltrametricDist.norm_add_le_max (t + 1) (-2 : PadicAlgCl 2)
    have hlt : ‖(t + 1) + -2‖ < 1 := htri.trans_lt
      (max_lt htplus (by rw [norm_neg, htwo]; norm_num))
    have heq' : (t + 1) + -2 = t - 1 := by ring
    rw [heq', heq] at hlt
    exact (lt_irrefl 1) hlt
  have htfix : ∀ σ : PadicAlgCl 2 ≃ₐ[ℚ_[2]] PadicAlgCl 2,
      (∀ y : PadicAlgCl 2, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → σ (t - 1) = t - 1 := by
    intro σ hσ
    dsimp [t]
    rw [map_sub, map_one, map_div₀, hfix σ hσ, σ.commutes m]
  have htminusbound : ‖t - 1‖ ≤ (1 / 2 : ℝ) := by
    simpa [htwo] using norm_le_prime_of_inertia_fixed_of_norm_lt_one 2 htfix htminus
  have htplusbound : ‖t + 1‖ ≤ (1 / 2 : ℝ) := by
    have h := IsUltrametricDist.norm_add_le_max (t - 1) (2 : PadicAlgCl 2)
    have heq : (t - 1) + 2 = t + 1 := by ring
    rw [heq] at h
    exact h.trans (max_le htminusbound (le_of_eq htwo))
  have hvbound : ‖v - 1‖ ≤ (1 / 4 : ℝ) := by
    have heq : (t - 1) * (t + 1) = algebraMap ℚ_[2] (PadicAlgCl 2) (v - 1) := by
      rw [map_sub, map_one, ← htsq]
      ring
    have hmul := mul_le_mul htminusbound htplusbound (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← norm_mul, heq, norm_algebraMap'] at hmul
    norm_num at hmul ⊢
    exact hmul
  have hfour : ‖(4 : ℚ_[2])‖ = (1 / 4 : ℝ) := by
    have htwoQ : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
      have hp : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
        simpa only [Nat.cast_ofNat] using Padic.norm_p (p := 2)
      exact hp.trans (by norm_num)
    calc ‖(4 : ℚ_[2])‖ = ‖(2 : ℚ_[2]) ^ 2‖ := by norm_num
      _ = (1 / 4 : ℝ) := by rw [norm_pow, htwoQ]; norm_num
  rw [norm_div, hfour]
  exact (div_le_one (by norm_num : (0 : ℝ) < 1 / 4)).mpr hvbound

/-- The normalized quadratic twist of the Tate equation. -/
private theorem tate_twist_variableChange
    {K : Type*} [Field K] [CharZero K] (a b t : K) (ht : t ≠ 0) :
    (⟨(Units.mk0 t ht)⁻¹, 0, (t⁻¹ - 1) / 2, 0⟩ : VariableChange K) •
      (⟨1, 0, 0, a, b⟩ : WeierstrassCurve K) =
      ⟨1, (t ^ 2 - 1) / 4, 0, t ^ 4 * a, t ^ 6 * b⟩ := by
  ext <;> simp only [variableChange_def, inv_inv, Units.val_mk0]
  all_goals field_simp
  all_goals ring

/-- The auxiliary twist change cancels the negative Tate automorphism. -/
private theorem tate_twist_change_neg
    {K : Type*} [Field K] [CharZero K] (t : K) (ht : t ≠ 0) :
    (⟨(Units.mk0 (-t) (neg_ne_zero.mpr ht))⁻¹, 0, ((-t)⁻¹ - 1) / 2, 0⟩ :
      VariableChange K) * ⟨-1, 0, -1, 0⟩ =
      ⟨(Units.mk0 t ht)⁻¹, 0, (t⁻¹ - 1) / 2, 0⟩ := by
  apply VariableChange.ext
  · apply Units.ext
    simp [VariableChange.mul_def]
  all_goals simp only [VariableChange.mul_def, Units.val_neg, Units.val_one,
    zero_mul, zero_add, add_zero, mul_zero, neg_inv]
  all_goals ring

/-- A sign-compatible variable change becomes Galois-fixed after twisting its scale. -/
private theorem normalized_tate_change_fixed
    {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    (C : VariableChange L) (m : K) (hm : m ≠ 0) (s : L)
    (hCσ : ∀ σ : L ≃ₐ[K] L,
      (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
      (σ s ≠ s → C.map σ.toAlgHom.toRingHom = ⟨-1, 0, -1, 0⟩ * C)) :
    let t := (C.u : L) / algebraMap K L m
    let ht : t ≠ 0 := div_ne_zero C.u.ne_zero ((map_ne_zero (algebraMap K L)).mpr hm)
    let D : VariableChange L := ⟨(Units.mk0 t ht)⁻¹, 0, (t⁻¹ - 1) / 2, 0⟩
    ∀ σ : L ≃ₐ[K] L, (D * C).map σ.toAlgHom.toRingHom = D * C := by
  dsimp only
  intro σ
  let t := (C.u : L) / algebraMap K L m
  have ht : t ≠ 0 := div_ne_zero C.u.ne_zero ((map_ne_zero (algebraMap K L)).mpr hm)
  let D : VariableChange L := ⟨(Units.mk0 t ht)⁻¹, 0, (t⁻¹ - 1) / 2, 0⟩
  change (D * C).map σ.toAlgHom.toRingHom = D * C
  change (VariableChange.mapHom σ.toAlgHom.toRingHom) (D * C) = D * C
  rw [map_mul]
  change D.map σ.toAlgHom.toRingHom * C.map σ.toAlgHom.toRingHom = D * C
  by_cases hs : σ s = s
  · have hC := (hCσ σ).1 hs
    have hu : σ (C.u : L) = (C.u : L) :=
      congrArg (fun B : VariableChange L => (B.u : L)) hC
    have htf : σ t = t := by simp only [t, map_div₀, hu, σ.commutes]
    have hD : D.map σ.toAlgHom.toRingHom = D := by
      apply VariableChange.ext
      · apply Units.ext
        change σ t⁻¹ = t⁻¹
        rw [map_inv₀, htf]
      · exact map_zero σ
      · change σ ((t⁻¹ - 1) / 2) = (t⁻¹ - 1) / 2
        simp only [map_div₀, map_sub, map_inv₀, map_one, map_ofNat, htf]
      · exact map_zero σ
    rw [hD, hC]
  · have hC := (hCσ σ).2 hs
    have hu : σ (C.u : L) = -(C.u : L) := by
      simpa [VariableChange.mul_def] using
        congrArg (fun B : VariableChange L => (B.u : L)) hC
    have htf : σ t = -t := by simp only [t, map_div₀, hu, σ.commutes, neg_div]
    have hD : D.map σ.toAlgHom.toRingHom =
        ⟨(Units.mk0 (-t) (neg_ne_zero.mpr ht))⁻¹, 0, ((-t)⁻¹ - 1) / 2, 0⟩ := by
      apply VariableChange.ext
      · apply Units.ext
        change σ t⁻¹ = (-t)⁻¹
        rw [map_inv₀, htf]
      · exact map_zero σ
      · change σ ((t⁻¹ - 1) / 2) = ((-t)⁻¹ - 1) / 2
        simp only [map_div₀, map_sub, map_inv₀, map_one, map_ofNat, htf]
      · exact map_zero σ
    rw [hD, hC, ← mul_assoc, tate_twist_change_neg]

theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (q : ℕ) [Fact q.Prime] (hj : ¬ ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (qT : ℚ_[q]) (_ : qT ≠ 0) (_ : ‖qT‖₊ < 1) (d : ℚ_[q]) (s : AlgebraicClosure ℚ_[q]) (C : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ_[q])) (hs : s ^ 2 = algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) d) (hC : C • ((W.map (Int.castRingHom ℚ_[q])).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]))) = (TateCurve.curve qT).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]))) (hCσ : ∀ σ : AlgebraicClosure ℚ_[q] ≃ₐ[ℚ_[q]] AlgebraicClosure ℚ_[q], (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧ (σ s ≠ s → C.map σ.toAlgHom.toRingHom = ⟨-1, 0, -1, 0⟩ * C)) (hmin : WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : (q : ℤ) ∣ W.c₄) : ∃ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, (∀ x : PadicAlgCl q, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) ∧ σ s ≠ s := by
  rename_i hqT0 hqT
  classical
  by_contra hnone
  have hsignfix : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (∀ x : PadicAlgCl q, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ s = s := by
    intro σ hσ
    by_contra hne
    exact hnone ⟨σ, hσ, hne⟩
  have hufix : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (∀ x : PadicAlgCl q, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) →
        σ (C.u : PadicAlgCl q) = (C.u : PadicAlgCl q) := by
    intro σ hσ
    exact congrArg (fun B : WeierstrassCurve.VariableChange (PadicAlgCl q) =>
      (B.u : PadicAlgCl q)) ((hCσ σ).1 (hsignfix σ hσ))
  have husqfix : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      σ ((C.u : PadicAlgCl q) ^ 2) = (C.u : PadicAlgCl q) ^ 2 := by
    intro σ
    by_cases hσs : σ s = s
    · have hu : σ (C.u : PadicAlgCl q) = (C.u : PadicAlgCl q) :=
        congrArg (fun B : WeierstrassCurve.VariableChange (PadicAlgCl q) =>
          (B.u : PadicAlgCl q)) ((hCσ σ).1 hσs)
      rw [map_pow, hu]
    · have hu : σ (C.u : PadicAlgCl q) = -(C.u : PadicAlgCl q) := by
        simpa [WeierstrassCurve.VariableChange.mul_def] using
          congrArg (fun B : WeierstrassCurve.VariableChange (PadicAlgCl q) =>
            (B.u : PadicAlgCl q)) ((hCσ σ).2 hσs)
      rw [map_pow, hu, neg_sq]
  obtain ⟨d₀, hd₀⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (K := PadicAlgCl q) (k := ℚ_[q]) ((C.u : PadicAlgCl q) ^ 2)).mpr husqfix
  have hd₀ne : d₀ ≠ 0 := by
    intro hz
    have hu0 : (C.u : PadicAlgCl q) ^ 2 = 0 := by simpa only [hz, _root_.map_zero] using hd₀.symm
    exact (pow_ne_zero 2 C.u.ne_zero) hu0
  obtain ⟨m, v, hm, hdmv, hv, hv₂⟩ :=
    exists_square_mul_unit_of_inertia_fixed_root q d₀ hd₀ne
      (C.u : PadicAlgCl q) hd₀.symm hufix
  let f := algebraMap ℚ_[q] (PadicAlgCl q)
  have hfm : f m ≠ 0 := (map_ne_zero f).mpr hm
  let t : PadicAlgCl q := (C.u : PadicAlgCl q) / f m
  have ht : t ≠ 0 := div_ne_zero C.u.ne_zero hfm
  have ht₂ : t ^ 2 = f v := by
    dsimp only [t]
    rw [div_pow, ← hd₀, hdmv, map_mul, map_pow]
    field_simp [hfm]
    rfl
  let D : WeierstrassCurve.VariableChange (PadicAlgCl q) :=
    ⟨(Units.mk0 t ht)⁻¹, 0, (t⁻¹ - 1) / 2, 0⟩
  have hDCfix : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (D * C).map σ.toAlgHom.toRingHom = D * C := by
    exact normalized_tate_change_fixed C m hm s hCσ
  obtain ⟨D₀, hD₀⟩ := exists_variableChange_map_of_galois_fixed (D * C) hDCfix
  let U : WeierstrassCurve ℚ_[q] :=
    ⟨1, (v - 1) / 4, 0, v ^ 2 * TateCurve.a₄ qT, v ^ 3 * TateCurve.a₆ qT⟩
  have hD₀U : D₀ • W.map (Int.castRingHom ℚ_[q]) = U := by
    apply WeierstrassCurve.map_injective f.injective
    change (D₀ • W.map (Int.castRingHom ℚ_[q])).map f = U.map f
    rw [← WeierstrassCurve.map_variableChange, hD₀, mul_smul, hC]
    have ht₄ : t ^ 4 = (f v) ^ 2 := by rw [← ht₂]; ring
    have ht₆ : t ^ 6 = (f v) ^ 3 := by rw [← ht₂]; ring
    calc
      D • (TateCurve.curve qT).map f =
          (⟨1, (t ^ 2 - 1) / 4, 0,
            t ^ 4 * f (TateCurve.a₄ qT), t ^ 6 * f (TateCurve.a₆ qT)⟩ :
              WeierstrassCurve (PadicAlgCl q)) := by
        simpa only [TateCurve.curve, WeierstrassCurve.map, map_one, _root_.map_zero] using
          tate_twist_variableChange (f (TateCurve.a₄ qT)) (f (TateCurve.a₆ qT)) t ht
      _ = U.map f := by
        ext <;> simp only [U, WeierstrassCurve.map, map_one, _root_.map_zero,
          map_div₀, map_sub, map_mul, map_pow, map_ofNat, ht₂, ht₄, ht₆]
  obtain ⟨hUint, hUc₄⟩ := unit_tate_twist_integral_and_norm_c₄ q v qT hv hqT hv₂
  have hD₀int : WeierstrassCurve.IsIntegral ℤ_[q]
      (D₀ • W.map (Int.castRingHom ℚ_[q])) := by
    rw [hD₀U]
    exact hUint
  have hD₀c₄ : ‖(D₀ • W.map (Int.castRingHom ℚ_[q])).c₄‖ = 1 := by
    rw [hD₀U]
    exact hUc₄
  exact not_integral_norm_c₄_one_of_minimal_additive W hΔ q hmin hqc₄ D₀ hD₀int hD₀c₄

end PrimeLocal
