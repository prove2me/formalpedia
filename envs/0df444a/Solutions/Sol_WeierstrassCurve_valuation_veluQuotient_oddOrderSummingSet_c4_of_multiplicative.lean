-- Prove2me | solution 1 for WeierstrassCurve.valuation_veluQuotient_oddOrderSummingSet_c4_of_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/73ad3e7d-1931-5eb5-b051-33481d7d6d70

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_torsion_integral_of_not_dvd
import Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_valuation_veluQuotient_oddOrderSummingSet_c4_of_multiplicative
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
open WeierstrassCurve WeierstrassCurve.Affine ValuationSubring

set_option autoImplicit false

namespace N5c4aux

section SubgroupGlue

open WeierstrassCurve.Affine.Point

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma zeroMem : W.InZeroComponentAt A 0 := Or.inl rfl

private lemma negMem {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (-P) := by
  rw [← zero_sub]; exact W.inZeroComponentAt_sub A (zeroMem W A) hP

private lemma addMem {P Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) (hQ : W.InZeroComponentAt A Q) :
    W.InZeroComponentAt A (P + Q) := by
  simpa [sub_neg_eq_add] using W.inZeroComponentAt_sub A hP (negMem W A hQ)

private lemma nsmulMem (n : ℕ) {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (n • P) := by
  induction n with
  | zero => rw [zero_nsmul]; exact zeroMem W A
  | succ n ih => rw [succ_nsmul]; exact addMem W A ih hP

private lemma zsmulMem (a : ℤ) {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (a • P) := by
  cases a with
  | ofNat n => simpa using nsmulMem W A n hP
  | negSucc n => rw [negSucc_zsmul]; exact negMem W A (nsmulMem W A (n + 1) hP)

private lemma mem_of_nsmul_mem {p : ℕ} (hp : p.Prime)
    {Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point} (hQ : p • Q = 0)
    {m : ℕ} (hm : ¬ p ∣ m) (h : W.InZeroComponentAt A (m • Q)) :
    W.InZeroComponentAt A Q := by
  have hcop : IsCoprime (m : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hm)
  obtain ⟨a, b, hab⟩ := hcop
  have hQeq : Q = a • (m • Q) := by
    calc Q = ((a * m + b * p : ℤ)) • Q := by rw [hab, one_zsmul]
    _ = a • (m • Q) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, hQ]
        rw [zsmul_zero, add_zero]
  rw [hQeq]; exact zsmulMem W A a h

private lemma mem_of_nsmul_mem' {p : ℕ} (hp : p.Prime)
    {Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point} (hQ : p • Q = 0) :
    ∀ m : ℕ, 0 < m → m < p → W.InZeroComponentAt A (m • Q) → W.InZeroComponentAt A Q :=
  fun _ hm1 hmp h => mem_of_nsmul_mem W A hp hQ (Nat.not_dvd_of_pos_of_lt hm1 hmp) h

end SubgroupGlue

section VeluGlue

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))

private lemma veluQuotient_c₄ : (W.veluQuotient S).c₄ = W.c₄ + 240 * W.veluTSum S := by
  simp only [c₄, veluQuotient_b₂, veluQuotient_b₄]; ring

end VeluGlue

section SummingSetGlue

variable {F : Type*} [Field F] [DecidableEq F] (W' : WeierstrassCurve F)

private lemma coords_inj_on_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) :
    Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 n : Set ℕ) := by
  intro k hk k' hk' hcoords
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  have hkne : k • Q ≠ 0 := fun h0 => by
    have hd : p ∣ k := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd (Nat.le_of_dvd hk.1 hd) (by omega)
  have hk'ne : k' • Q ≠ 0 := fun h0 => by
    have hd : p ∣ k' := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd (Nat.le_of_dvd hk'.1 hd) (by omega)
  have hpt : k • Q = k' • Q := by
    cases hkQ : k • Q with
    | zero => exact absurd hkQ hkne
    | some xk yk hknon =>
      cases hk'Q : k' • Q with
      | zero => exact absurd hk'Q hk'ne
      | some xk' yk' hk'non =>
        simp only [hkQ, hk'Q, Affine.Point.coordsOrZero_some, Prod.mk.injEq] at hcoords
        obtain ⟨rfl, rfl⟩ := hcoords
        rfl
  have hz : (p : ℤ) ∣ ((k : ℤ) - k') := by
    have h0 : ((k : ℤ) - k') • Q = 0 := by
      rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hpt]; exact sub_self _
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
    rw [hord] at this
    exact_mod_cast this
  have habs : |(k : ℤ) - (k' : ℤ)| < p := by
    have h1 : (k : ℤ) - k' < p := by omega
    have h2 : (k' : ℤ) - k < p := by omega
    rw [abs_sub_lt_iff]; omega
  have hsub0 : (k : ℤ) - k' = 0 := Int.eq_zero_of_abs_lt_dvd hz habs
  omega

private lemma veluTSum_eq_sum_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) :
    W'.veluTSum (W'.oddOrderSummingSet Q n)
      = ∑ k ∈ Finset.Icc 1 n, W'.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 := by
  rw [veluTSum, oddOrderSummingSet, Finset.sum_image]
  intro k hk k' hk' h
  exact coords_inj_on_Icc W' hord hn (Finset.mem_coe.mpr hk) (Finset.mem_coe.mpr hk') h

end SummingSetGlue

section ValGlue

local notation "Kb" => AlgebraicClosure ℚ

private lemma valuation_intCast_eq_one (A : ValuationSubring Kb) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : A.LiesOverPrime ℓ) {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) :
    A.valuation (m : Kb) = 1 := by
  have hℓK : ((ℓ : ℕ) : Kb) ∈ A.nonunits := hA
  have hℓmem : ((ℓ : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    A.coe_mem_nonunits_iff.mp (by simpa using hℓK)
  have hunit : IsUnit ((m : ℤ) : A) := by
    by_contra hunit
    have hmem : ((m : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact hunit
    obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.mp hℓ).coprime_iff_not_dvd.mpr hm
    have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have h := congrArg (fun z : ℤ => ((z : ℤ) : A)) huv
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
      rw [← h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓmem) (Ideal.mul_mem_left _ _ hmem)
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have h := (A.valuation_eq_one_iff _).mp hunit
  simpa using h

private lemma baseChange_c₄ (W : WeierstrassCurve ℤ) :
    ((W.map (Int.castRingHom ℚ))⁄Kb).c₄ = (W.c₄ : Kb) := by
  simp [Affine.baseChange, WeierstrassCurve.baseChange, map_c₄, eq_intCast, map_intCast]

end ValGlue

section Nontoric

local notation "Kb" => AlgebraicClosure ℚ

private theorem veluT_factor (W : WeierstrassCurve ℤ) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) (x y : Kb) :
    ((W.map (Int.castRingHom ℚ))⁄Kb).veluT x y
      = (x - x₀) * (6 * (x - x₀) + ((W.b₂ : Kb) + 12 * x₀)) := by
  simp only [veluT, veluGx, veluGy, Affine.baseChange_a₁, Affine.baseChange_a₂,
    Affine.baseChange_a₃, Affine.baseChange_a₄, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    eq_intCast, map_intCast]
  have hb₂ : ((W.b₂ : ℤ) : Kb) = (W.a₁ : Kb) ^ 2 + 4 * W.a₂ := by simp [WeierstrassCurve.b₂]
  rw [hb₂]
  linear_combination (-2) * hFx + (W.a₁ : Kb) * hFy

private theorem nontoric_c₄ (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (A : ValuationSubring Kb) (hA : A.LiesOverPrime ℓ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point) (hQord : addOrderOf Q = p)
    (hout : ¬ W.InZeroComponentAt A Q) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient
      (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q (p / 2))).c₄ = 1 := by

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction W hℓ hΔ hℓΔ hℓc₄ A hA
  set n := p / 2 with hn
  have hpn : p = 2 * n + 1 := (Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2)).symm
  have h2n : 2 * n < p := by omega
  have hpQ : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  have hcl := mem_of_nsmul_mem' W A hp hpQ

  have hpt : ∀ k ∈ Finset.Icc 1 n, ∃ (x y : Kb)
      (hxy : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y), k • Q = .some x y hxy := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hne : k • Q ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQord]; omega)
    cases hkQ : k • Q with
    | zero => exact absurd hkQ hne
    | @some x y hxy => exact ⟨x, y, hxy, rfl⟩
  choose! xk yk hk hkQ using hpt

  have hlev : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) < 1 := by
    intro k hk'
    have hk2 := hk'
    rw [Finset.mem_Icc] at hk2
    refine (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre W A hx₀ hy₀ hFy hFx
      hnode hbad (hk k hk')).mp ?_
    have hout' : ¬ W.InZeroComponentAt A (k • Q) :=
      fun hin => hout (hcl k (by omega) (by omega) hin)
    rw [hkQ k hk'] at hout'
    exact hout'

  have h6 : A.valuation (6 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 6)
  have hT : A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluTSum
      (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q n)) < 1 := by
    rw [veluTSum_eq_sum_Icc _ hQord h2n]
    refine Valuation.map_sum_lt _ one_ne_zero fun k hk' => ?_
    rw [hkQ k hk']
    simp only [Affine.Point.coordsOrZero_some]
    rw [veluT_factor W hFy hFx, map_mul]
    have hb : A.valuation (6 * (xk k - x₀) + ((W.b₂ : Kb) + 12 * x₀)) ≤ 1 := by
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hnode.le)
      rw [map_mul]
      exact mul_le_one' h6 (hlev k hk').le
    calc A.valuation (xk k - x₀) * A.valuation (6 * (xk k - x₀) + ((W.b₂ : Kb) + 12 * x₀))
        ≤ A.valuation (xk k - x₀) := mul_le_of_le_one_right' hb
      _ < 1 := hlev k hk'

  have hc₄ : A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).c₄) = 1 := by
    rw [baseChange_c₄]
    exact valuation_intCast_eq_one A hℓ hA hℓc₄
  have h240 : A.valuation (240 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 240)
  have h240T : A.valuation (240 * ((W.map (Int.castRingHom ℚ))⁄Kb).veluTSum
      (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q n))
        < A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).c₄) := by
    rw [hc₄, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h240) hT
  rw [veluQuotient_c₄, Valuation.map_add_eq_of_lt_left _ h240T, hc₄]

end Nontoric

end N5c4aux

namespace N5c4M

local notation "Kb" => AlgebraicClosure ℚ

section IntegerUnits

variable {ℓ : ℕ} (A : ValuationSubring Kb)

private lemma natCast_mem_maximalIdeal (hA : A.LiesOverPrime ℓ) :
    ((ℓ : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
  have hℓK : ((ℓ : ℕ) : Kb) ∈ A.nonunits := hA
  exact A.coe_mem_nonunits_iff.mp (by simpa using hℓK)

private lemma isUnit_intCast_of_not_dvd (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ)
    {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) : IsUnit ((m : ℤ) : A) := by
  by_contra hunit
  have hmem : ((m : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]; exact hunit
  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.mp hℓ).coprime_iff_not_dvd.mpr hm
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    have h := congrArg (fun z : ℤ => ((z : ℤ) : A)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
    rw [← h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (natCast_mem_maximalIdeal A hA))
      (Ideal.mul_mem_left _ _ hmem)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private lemma intCast_residueField_ne_zero (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ)
    {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) : ((m : ℤ) : IsLocalRing.ResidueField A) ≠ 0 := by
  have hunit := isUnit_intCast_of_not_dvd A hℓ hA hm
  have hres : IsLocalRing.residue A ((m : ℤ) : A) ≠ 0 := by
    intro h0
    have hm' : ((m : ℤ) : A) ∈ _root_.nonunits A :=
      (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)
    exact hm' hunit
  simpa [map_intCast] using hres

private lemma intCast_residueField_eq_zero_of_dvd (hA : A.LiesOverPrime ℓ)
    {m : ℤ} (hm : (ℓ : ℤ) ∣ m) : ((m : ℤ) : IsLocalRing.ResidueField A) = 0 := by
  obtain ⟨c, hc⟩ := hm
  have hmem : ((m : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [hc, Int.cast_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ (natCast_mem_maximalIdeal A hA)
  have := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  simpa [map_intCast] using this

end IntegerUnits

section Casts

variable (W : WeierstrassCurve ℤ)

private lemma Wb_b₂ : ((W.map (Int.castRingHom ℚ))⁄Kb).b₂ = (W.b₂ : Kb) := by
  simp [WeierstrassCurve.baseChange, map_b₂, eq_intCast, map_intCast]

private lemma Wb_b₄ : ((W.map (Int.castRingHom ℚ))⁄Kb).b₄ = (W.b₄ : Kb) := by
  simp [WeierstrassCurve.baseChange, map_b₄, eq_intCast, map_intCast]

private lemma Wb_c₄ : ((W.map (Int.castRingHom ℚ))⁄Kb).c₄ = (W.c₄ : Kb) := by
  simp [WeierstrassCurve.baseChange, map_c₄, eq_intCast, map_intCast]

variable {K : Type*} [CommRing K]

private lemma Wmap_b₂ : (W.map (Int.castRingHom K)).b₂ = (W.b₂ : K) := by
  simp [map_b₂, eq_intCast]

private lemma Wmap_b₄ : (W.map (Int.castRingHom K)).b₄ = (W.b₄ : K) := by
  simp [map_b₄, eq_intCast]

private lemma Wmap_c₄ : (W.map (Int.castRingHom K)).c₄ = (W.c₄ : K) := by
  simp [map_c₄, eq_intCast]

private lemma Wmap_Δ : (W.map (Int.castRingHom K)).Δ = (W.Δ : K) := by
  simp [map_Δ, eq_intCast]

end Casts

section SubgroupGlue

open WeierstrassCurve.Affine.Point

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)

private lemma zeroMem : W.InZeroComponentAt A 0 := Or.inl rfl

private lemma negMem {P : ((W.map (Int.castRingHom ℚ))⁄Kb).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (-P) := by
  rw [← zero_sub]; exact W.inZeroComponentAt_sub A (zeroMem W A) hP

private lemma addMem {P Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point}
    (hP : W.InZeroComponentAt A P) (hQ : W.InZeroComponentAt A Q) :
    W.InZeroComponentAt A (P + Q) := by
  simpa [sub_neg_eq_add] using W.inZeroComponentAt_sub A hP (negMem W A hQ)

private lemma nsmulMem (n : ℕ) {P : ((W.map (Int.castRingHom ℚ))⁄Kb).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (n • P) := by
  induction n with
  | zero => rw [zero_nsmul]; exact zeroMem W A
  | succ n ih => rw [succ_nsmul]; exact addMem W A ih hP

private lemma unpack_torsion {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ)
    {p : ℕ} (hp : p.Prime) (hℓp : ℓ ≠ p)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    ∃ (x y : Kb)
      (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y),
      k • Q = .some x y h ∧ x ∈ A ∧ y ∈ A := by
  have hk0 : k • Q ≠ 0 := by
    intro h0
    have hdvd : p ∣ k := by
      rw [← hQord]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd hdvd (Nat.not_dvd_of_pos_of_lt hk1 hkp)
  have htor : p • (k • Q) = 0 := by
    rw [smul_comm, ← hQord, addOrderOf_nsmul_eq_zero, smul_zero]
  have hnd : ¬ ℓ ∣ p := fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd)
  rcases W.torsion_integral_of_not_dvd hℓ A hA hnd (k • Q) htor with h0 | ⟨x, y, h, heq, hx, hy⟩
  · exact absurd h0 hk0
  · exact ⟨x, y, h, heq, hx, hy⟩

private lemma residue_nonsingular_of_mem {x y : Kb}
    {h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y}
    (hx : x ∈ A) (hy : y ∈ A) (hmem : W.InZeroComponentAt A (.some x y h)) :
    (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
      (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) := by
  rcases hmem with h0 | ⟨x', y', h', heq, hcase⟩
  · exact absurd h0 (some_ne_zero h)
  · obtain ⟨hx', hy'⟩ : x = x' ∧ y = y' := by
      have := heq
      rw [Point.some.injEq] at this
      exact ⟨this.1, this.2⟩
    subst hx'; subst hy'
    rcases hcase with hnx | ⟨hx'', hy'', hns⟩
    · exact absurd hx hnx
    · exact hns

end SubgroupGlue

section SummingSetPlumbing
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
private lemma nonsingular_coordsOrZero {P : W.toAffine.Point} (hP : P ≠ 0) :
    W.toAffine.Nonsingular P.coordsOrZero.1 P.coordsOrZero.2 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact h

omit [DecidableEq F] in
private lemma eq_of_coordsOrZero_eq {P P' : W.toAffine.Point}
    (hP : P ≠ 0) (hP' : P' ≠ 0) (h : P.coordsOrZero = P'.coordsOrZero) : P = P' := by
  rcases P with _ | ⟨x, y, hh⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨x', y', hh'⟩
  · exact absurd rfl hP'
  obtain ⟨hx, hy⟩ := Prod.mk.injEq .. |>.mp h
  subst hx hy; rfl

variable {W} {Q : W.toAffine.Point} {n : ℕ} (hQord : addOrderOf Q = n)

include hQord in
private lemma nsmul_ne_zero_of_lt' {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) : k • Q ≠ 0 := by
  intro h0
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
  rw [hQord] at hdvd
  exact absurd (Nat.le_of_dvd hk1 hdvd) (not_le.mpr hkn)

include hQord in
private lemma nsmul_inj_of_lt {m : ℕ} (hm : m < n)
    {j k : ℕ} (hj : j ∈ Finset.Icc 1 m) (hk : k ∈ Finset.Icc 1 m)
    (hjk : j • Q = k • Q) : j = k := by
  rw [Finset.mem_Icc] at hj hk
  rcases le_total j k with hle | hle
  · have hsub : (k - j) • Q = 0 := add_right_cancel (b := j • Q)
      (by rw [← add_nsmul, Nat.sub_add_cancel hle, zero_add, hjk])
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hsub; rw [hQord] at hdvd
    have : k - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd
      (lt_of_le_of_lt (Nat.sub_le k j) (lt_of_le_of_lt hk.2 hm))
    omega
  · have hsub : (j - k) • Q = 0 := add_right_cancel (b := k • Q)
      (by rw [← add_nsmul, Nat.sub_add_cancel hle, zero_add, ← hjk])
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hsub; rw [hQord] at hdvd
    have : j - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd
      (lt_of_le_of_lt (Nat.sub_le j k) (lt_of_le_of_lt hj.2 hm))
    omega

include hQord in
private lemma coordsOrZero_nsmul_injOn {m : ℕ} (hm : m < n) :
    Set.InjOn (fun k => (k • Q).coordsOrZero) (Finset.Icc 1 m : Set ℕ) := by
  intro j hj k hk hjk
  simp only at hjk
  have hj' := Finset.mem_coe.mp hj; have hk' := Finset.mem_coe.mp hk
  rw [Finset.mem_Icc] at hj' hk'
  have hjQ : j • Q ≠ 0 := nsmul_ne_zero_of_lt' hQord hj'.1 (lt_of_le_of_lt hj'.2 hm)
  have hkQ : k • Q ≠ 0 := nsmul_ne_zero_of_lt' hQord hk'.1 (lt_of_le_of_lt hk'.2 hm)
  exact nsmul_inj_of_lt hQord hm (Finset.mem_coe.mp hj) (Finset.mem_coe.mp hk)
    (eq_of_coordsOrZero_eq W hjQ hkQ hjk)

include hQord in
private lemma veluTSum_oddOrderSummingSet {m : ℕ} (hm : m < n) :
    W.veluTSum (W.oddOrderSummingSet Q m)
      = ∑ k ∈ Finset.Icc 1 m,
          (((6 : ℤ) : F) * ((k • Q).coordsOrZero.1) ^ 2 + W.b₂ * ((k • Q).coordsOrZero.1)
            + W.b₄) := by
  rw [veluTSum, oddOrderSummingSet, Finset.sum_image (coordsOrZero_nsmul_injOn hQord hm)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [veluT_eq]
  push_cast
  ring

end SummingSetPlumbing

private lemma veluQuotient_c₄' {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (S : Finset (R × R)) :
    (W.veluQuotient S).c₄ = W.c₄ + ((240 : ℤ) : R) * W.veluTSum S := by
  simp only [c₄, veluQuotient_b₂, veluQuotient_b₄]
  push_cast
  ring

section Toric

open WeierstrassCurve.Affine.Point

private theorem toric_c₄ (W : WeierstrassCurve ℤ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (A : ValuationSubring Kb) (hA : A.LiesOverPrime ℓ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓp : ℓ ≠ p)
    (Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point) (hQord : addOrderOf Q = p)
    (hmem : W.InZeroComponentAt A Q) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient
      (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q (p / 2))).c₄ = 1 := by
  classical
  have hnp : p / 2 < p := Nat.div_lt_self hp.pos one_lt_two
  have hp1 : 1 < p := hp.one_lt

  obtain ⟨red, hred0, hredadd, hredint, hredinf, hredker, hredgal⟩ :=
    W.exists_reduction_inZeroComponentAt A
  have hrednsmul : ∀ m : ℕ, red (m • Q) = m • red Q := by
    intro m
    induction m with
    | zero => simpa using hred0
    | succ m ih =>
      calc red ((m + 1) • Q) = red (m • Q + Q) := by rw [succ_nsmul]
        _ = red (m • Q) + red Q := hredadd _ _ (nsmulMem W A m hmem) hmem
        _ = m • red Q + red Q := by rw [ih]
        _ = (m + 1) • red Q := (succ_nsmul _ m).symm

  obtain ⟨x0, y0, h0, hQeq, hx0, hy0⟩ : ∃ (x y : Kb)
      (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y),
      Q = .some x y h ∧ x ∈ A ∧ y ∈ A := by
    have h1 := unpack_torsion W A hℓ hA hp hℓp hQord (k := 1) le_rfl hp1
    rwa [one_smul] at h1
  have hmemQ : W.InZeroComponentAt A (.some x0 y0 h0) := hQeq ▸ hmem
  have hns0 := residue_nonsingular_of_mem W A hx0 hy0 hmemQ
  have hredQ : red Q
      = .some (IsLocalRing.residue A ⟨x0, hx0⟩) (IsLocalRing.residue A ⟨y0, hy0⟩) hns0 := by
    rw [hQeq]; exact hredint x0 y0 h0 hx0 hy0 hns0

  have hpQbar : p • red Q = 0 := by
    have h1 : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
    rw [← hrednsmul, h1, hred0]
  have hQbar_ne : red Q ≠ 0 := by rw [hredQ]; exact some_ne_zero hns0
  have hQbar_ord : addOrderOf (red Q) = p := by
    have hdvd : addOrderOf (red Q) ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpQbar
    rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd with h1 | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hQbar_ne
    · exact h

  have hkdata : ∀ k ∈ Finset.Icc 1 (p / 2), ∃ (x y : Kb)
      (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y),
      k • Q = .some x y h ∧ x ∈ A ∧ y ∈ A := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact unpack_torsion W A hℓ hA hp hℓp hQord hk.1 (lt_of_le_of_lt hk.2 hnp)
  choose! xk yk hknons hkQ hxkA hykA using hkdata
  have hkns : ∀ k (hk' : k ∈ Finset.Icc 1 (p / 2)),
      (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
        (IsLocalRing.residue A ⟨xk k, hxkA k hk'⟩)
        (IsLocalRing.residue A ⟨yk k, hykA k hk'⟩) := by
    intro k hk'
    exact residue_nonsingular_of_mem W A (hxkA k hk') (hykA k hk')
      ((hkQ k hk') ▸ nsmulMem W A k hmem)
  have hkred : ∀ k (hk' : k ∈ Finset.Icc 1 (p / 2)),
      k • red Q = .some (IsLocalRing.residue A ⟨xk k, hxkA k hk'⟩)
        (IsLocalRing.residue A ⟨yk k, hykA k hk'⟩) (hkns k hk') := by
    intro k hk'
    rw [← hrednsmul, hkQ k hk']
    exact hredint _ _ _ _ _ (hkns k hk')

  set xA : ℕ → A := fun k =>
    if h : k ∈ Finset.Icc 1 (p / 2) then ⟨xk k, hxkA k h⟩ else 0 with hxA
  have hxAres : ∀ k ∈ Finset.Icc 1 (p / 2),
      IsLocalRing.residue A (xA k) = (k • red Q).coordsOrZero.1 := by
    intro k hk'
    rw [hkred k hk', Point.coordsOrZero_some, hxA]
    simp only [dif_pos hk']

  set cA : A := ((W.c₄ : ℤ) : A) + ((240 : ℤ) : A) * ∑ k ∈ Finset.Icc 1 (p / 2),
    (((6 : ℤ) : A) * xA k ^ 2 + ((W.b₂ : ℤ) : A) * xA k + ((W.b₄ : ℤ) : A)) with hcA

  have hcoe : (cA : Kb) = (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient
      (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q (p / 2))).c₄ := by
    rw [veluQuotient_c₄', veluTSum_oddOrderSummingSet hQord hnp, Wb_c₄ W, Wb_b₂ W, Wb_b₄ W]
    calc (cA : Kb)
        = ((W.c₄ : ℤ) : Kb) + ((240 : ℤ) : Kb)
            * ((∑ k ∈ Finset.Icc 1 (p / 2),
                (((6 : ℤ) : A) * xA k ^ 2 + ((W.b₂ : ℤ) : A) * xA k
                  + ((W.b₄ : ℤ) : A)) : A) : Kb) := rfl
      _ = ((W.c₄ : ℤ) : Kb) + ((240 : ℤ) : Kb)
            * ∑ k ∈ Finset.Icc 1 (p / 2),
                ((((6 : ℤ) : A) * xA k ^ 2 + ((W.b₂ : ℤ) : A) * xA k
                  + ((W.b₄ : ℤ) : A) : A) : Kb) := by
          rw [AddSubmonoidClass.coe_finsetSum]
      _ = ((W.c₄ : ℤ) : Kb) + ((240 : ℤ) : Kb)
            * ∑ k ∈ Finset.Icc 1 (p / 2),
                (((6 : ℤ) : Kb) * (k • Q).coordsOrZero.1 ^ 2
                  + ((W.b₂ : ℤ) : Kb) * (k • Q).coordsOrZero.1 + ((W.b₄ : ℤ) : Kb)) := by
          refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun k hk' => ?_))
          rw [hkQ k hk', Point.coordsOrZero_some]
          simp only [hxA, dif_pos hk']
          rfl

  have hres : IsLocalRing.residue A cA
      = ((W.map (Int.castRingHom (IsLocalRing.ResidueField A))).veluQuotient
          ((W.map (Int.castRingHom (IsLocalRing.ResidueField A))).oddOrderSummingSet
            (red Q) (p / 2))).c₄ := by
    rw [veluQuotient_c₄', veluTSum_oddOrderSummingSet hQbar_ord hnp, Wmap_c₄ W, Wmap_b₂ W,
      Wmap_b₄ W, hcA]
    rw [map_add, map_mul, map_sum]
    simp only [map_intCast, map_add, map_mul, map_pow]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [hxAres k hk']

  have hΔbar : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ = 0 := by
    rw [Wmap_Δ W]; exact intCast_residueField_eq_zero_of_dvd A hA hℓΔ
  have hc₄bar : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).c₄ ≠ 0 := by
    rw [Wmap_c₄ W]; exact intCast_residueField_ne_zero A hℓ hA hℓc₄
  have hpbar : ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
    have hnd : ¬ (ℓ : ℤ) ∣ (p : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      exact fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd)
    have := intCast_residueField_ne_zero A hℓ hA hnd
    simpa using this
  have hRb := ((W.map (Int.castRingHom
      (IsLocalRing.ResidueField A))).veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal
    hΔbar hc₄bar (hp.odd_of_ne_two hp2) (red Q) hQbar_ord).1
  have hval : IsLocalRing.residue A cA
      = ((p : ℕ) : IsLocalRing.ResidueField A) ^ 4
        * ((W.c₄ : ℤ) : IsLocalRing.ResidueField A) := by
    rw [hres, hRb, Wmap_c₄ W]

  have hne : IsLocalRing.residue A cA ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (pow_ne_zero _ hpbar)
      (intCast_residueField_ne_zero A hℓ hA hℓc₄)
  have hunit : IsUnit cA := by
    by_contra hnu
    exact hne ((IsLocalRing.residue_eq_zero_iff _).mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have hv1 := (A.valuation_eq_one_iff cA).mp hunit
  rw [← hcoe]
  simpa using hv1

end Toric

end N5c4M

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓp : ℓ ≠ p)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p) :
    let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
    A.valuation (Wb.veluQuotient (Wb.oddOrderSummingSet Q (p / 2))).c₄ = 1 := by
  intro Wb
  by_cases hQ0 : W.InZeroComponentAt A Q
  · exact N5c4M.toric_c₄ W hℓ hℓΔ hℓc₄ A hA hp hp2 hℓp Q hQord hQ0
  · exact N5c4aux.nontoric_c₄ W hΔ hℓ hℓΔ hℓc₄ A hA hp hp2 Q hQord hQ0

end S_WeierstrassCurve_valuation_veluQuotient_oddOrderSummingSet_c4_of_multiplicative
end P2MW
export P2MW.S_WeierstrassCurve_valuation_veluQuotient_oddOrderSummingSet_c4_of_multiplicative (solution)
