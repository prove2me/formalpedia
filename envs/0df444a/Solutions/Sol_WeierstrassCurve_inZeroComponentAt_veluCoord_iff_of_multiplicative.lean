-- Prove2me | solution 1 for WeierstrassCurve.inZeroComponentAt_veluCoord_iff_of_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3fcb11db-fa37-5be7-8414-dd4533a0af94

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_level_add_of_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
import Theorems.Thm_cyclotomic_velu_xLaw
import Theorems.Thm_cyclotomic_velu_powerSums
import Theorems.Thm_WeierstrassCurve_valuation_c4_add_veluTSum_lt_one_of_formal_kernel
import Theorems.Thm_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_addX_sub_mul_addX_neg_sub_mul_sq_of_criticalCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

namespace QD1dpAux

section SubgroupGlue

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

end SubgroupGlue

section Bookkeep

variable {G : Type*} [AddCommGroup G]

private lemma exists_nat_lt_of_mem_zmultiples {Q : G} {p : ℕ} (hp : 0 < p)
    (hQord : addOrderOf Q = p) {k : G} (hk : k ∈ AddSubgroup.zmultiples Q) :
    ∃ m : ℕ, m < p ∧ k = m • Q := by
  obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hk
  refine ⟨(a % p).toNat, ?_, ?_⟩
  · have hmod : 0 ≤ a % p ∧ a % p < p := ⟨Int.emod_nonneg a (by omega), Int.emod_lt_of_pos a (by omega)⟩
    omega
  · have hmod : 0 ≤ a % p := Int.emod_nonneg a (by omega)
    rw [← natCast_zsmul, Int.toNat_of_nonneg hmod]
    have hmodeq : (a % (p : ℤ)) • Q = a • Q := by
      have := mod_addOrderOf_zsmul Q a
      rw [hQord] at this
      exact this
    rw [← hmodeq]

private lemma nsmul_mem_zmultiples (Q : G) (m : ℕ) : m • Q ∈ AddSubgroup.zmultiples Q := by
  rw [← natCast_zsmul]; exact AddSubgroup.zsmul_mem_zmultiples Q m

end Bookkeep

section RHSToric

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma rhs_iff_of_toric
    {Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hQ : W.InZeroComponentAt A Q)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :
    (∃ k ∈ AddSubgroup.zmultiples Q, W.InZeroComponentAt A (P - k))
      ↔ W.InZeroComponentAt A P := by
  constructor
  · rintro ⟨k, hk, hPk⟩
    obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hk
    have hkMem : W.InZeroComponentAt A (a • Q) := zsmulMem W A a hQ
    simpa using addMem W A hPk hkMem
  · intro hP
    exact ⟨0, AddSubgroup.zero_mem _, by simpa using hP⟩

end RHSToric

section QUnit

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma valuation_intCast_eq_one_of_not_dvd {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {n : ℤ} (hn : ¬ (q : ℤ) ∣ n) :
    A.valuation ((n : ℤ) : AlgebraicClosure ℚ) = 1 := by
  have hqK : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
  have hqmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    A.coe_mem_nonunits_iff.mp (by simpa using hqK)
  have hunit : IsUnit ((n : ℤ) : A) := by
    by_contra hunit
    have hmem : ((n : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal]; exact hunit
    obtain ⟨a, b, hab⟩ := (Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hn
    have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have hh := congrArg (fun z : ℤ => ((z : ℤ) : A)) hab
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at hh
      rw [← hh]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqmem) (Ideal.mul_mem_left _ _ hmem)
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  simpa using (A.valuation_eq_one_iff _).mp hunit

private lemma valuation_intCast_lt_one_of_dvd {q : ℕ}
    (hA : A.LiesOverPrime q) {n : ℤ} (hn : (q : ℤ) ∣ n) :
    A.valuation ((n : ℤ) : AlgebraicClosure ℚ) < 1 := by
  have hqK : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
  have hqmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    A.coe_mem_nonunits_iff.mp (by simpa using hqK)
  obtain ⟨m, hm⟩ := hn
  have hmem : ((n : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [hm, Int.cast_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ hqmem
  simpa using (A.valuation_lt_one_iff _).mp hmem

end QUnit

section WprimeCoeff

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ)

private lemma _root_.QD1dpAux.baseChange_a₁ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).a₁ = (W.a₁ : Kb) := by
  simp only [Affine.baseChange_a₁, WeierstrassCurve.map_a₁, eq_intCast, map_intCast]
p2m_export "QD1dpAux" "baseChange_a₁"
private lemma _root_.QD1dpAux.baseChange_a₂ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).a₂ = (W.a₂ : Kb) := by
  simp only [Affine.baseChange_a₂, WeierstrassCurve.map_a₂, eq_intCast, map_intCast]
p2m_export "QD1dpAux" "baseChange_a₂"
private lemma _root_.QD1dpAux.baseChange_a₃ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).a₃ = (W.a₃ : Kb) := by
  simp only [Affine.baseChange_a₃, WeierstrassCurve.map_a₃, eq_intCast, map_intCast]
p2m_export "QD1dpAux" "baseChange_a₃"
private lemma _root_.QD1dpAux.baseChange_a₄ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).a₄ = (W.a₄ : Kb) := by
  simp only [Affine.baseChange_a₄, WeierstrassCurve.map_a₄, eq_intCast, map_intCast]
p2m_export "QD1dpAux" "baseChange_a₄"
private lemma _root_.QD1dpAux.baseChange_a₆ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).a₆ = (W.a₆ : Kb) := by
  simp only [Affine.baseChange_a₆, WeierstrassCurve.map_a₆, eq_intCast, map_intCast]
p2m_export "QD1dpAux" "baseChange_a₆"
private lemma baseChange_b₂ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).b₂ = (W.b₂ : Kb) := by
  simp only [WeierstrassCurve.b₂, baseChange_a₁, baseChange_a₂]; push_cast; ring
private lemma baseChange_c₄ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).c₄ = (W.c₄ : Kb) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄]
  push_cast; ring
private lemma baseChange_Δ :
    ((W.map (Int.castRingHom ℚ))⁄Kb).Δ = (W.Δ : Kb) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄, baseChange_a₆]
  push_cast; ring

end WprimeCoeff

section CentreTransfer

local notation "Kb" => AlgebraicClosure ℚ

private lemma valuation_uscale_sub (A : ValuationSubring Kb) (u : Kbˣ)
    (hu : A.valuation (u : Kb) = 1) (α β : Kb) :
    A.valuation (((u⁻¹ : Kbˣ) : Kb) ^ 2 * α - β) = A.valuation (α - (u : Kb) ^ 2 * β) := by
  have huK : (u : Kb) ≠ 0 := Units.ne_zero u
  have h : ((u⁻¹ : Kbˣ) : Kb) ^ 2 * α - β
      = ((u⁻¹ : Kbˣ) : Kb) ^ 2 * (α - (u : Kb) ^ 2 * β) := by
    rw [Units.val_inv_eq_inv_val]; field_simp
  rw [h, map_mul, map_pow]
  have hvinv : A.valuation ((u⁻¹ : Kbˣ) : Kb) = 1 := by
    rw [show ((u⁻¹ : Kbˣ) : Kb) = (u : Kb)⁻¹ from Units.val_inv_eq_inv_val u, map_inv₀, hu, inv_one]
  rw [hvinv, one_pow, one_mul]

private lemma centre_hFy_transfer (W W' : WeierstrassCurve ℤ) (u : Kbˣ) {S : Finset (Kb × Kb)}
    (hW' : (W'.map (Int.castRingHom ℚ))⁄Kb = (⟨u, 0, 0, 0⟩ : VariableChange Kb) •
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient S))
    (x₀' y₀' : Kb) (hFy' : 2 * y₀' + (W'.a₁ : Kb) * x₀' + W'.a₃ = 0) :
    2 * ((u : Kb) ^ 3 * y₀') + (W.a₁ : Kb) * ((u : Kb) ^ 2 * x₀') + W.a₃ = 0 := by
  have huK : (u : Kb) ≠ 0 := Units.ne_zero u

  have ha₁ : (W'.a₁ : Kb) = (u : Kb)⁻¹ * (W.a₁ : Kb) := by
    have h := congrArg WeierstrassCurve.a₁ hW'
    rw [baseChange_a₁ W', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.veluQuotient_a₁,
      baseChange_a₁ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have ha₃ : (W'.a₃ : Kb) = (u : Kb)⁻¹ ^ 3 * (W.a₃ : Kb) := by
    have h := congrArg WeierstrassCurve.a₃ hW'
    rw [baseChange_a₃ W', WeierstrassCurve.variableChange_a₃, WeierstrassCurve.veluQuotient_a₃,
      baseChange_a₃ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  rw [ha₁, ha₃] at hFy'
  have h := mul_eq_zero_of_right ((u : Kb) ^ 3) hFy'
  field_simp at h
  linear_combination h

private lemma centre_hFx_transfer (W W' : WeierstrassCurve ℤ) (u : Kbˣ) {S : Finset (Kb × Kb)}
    (hW' : (W'.map (Int.castRingHom ℚ))⁄Kb = (⟨u, 0, 0, 0⟩ : VariableChange Kb) •
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient S))
    (x₀' y₀' : Kb)
    (hFx' : (W'.a₁ : Kb) * y₀' = 3 * x₀' ^ 2 + 2 * W'.a₂ * x₀' + W'.a₄) :
    (W.a₁ : Kb) * ((u : Kb) ^ 3 * y₀')
      = 3 * ((u : Kb) ^ 2 * x₀') ^ 2 + 2 * W.a₂ * ((u : Kb) ^ 2 * x₀')
        + ((W.a₄ : Kb) - 5 * ((W.map (Int.castRingHom ℚ))⁄Kb).veluTSum S) := by
  have huK : (u : Kb) ≠ 0 := Units.ne_zero u
  have ha₁ : (W'.a₁ : Kb) = (u : Kb)⁻¹ * (W.a₁ : Kb) := by
    have h := congrArg WeierstrassCurve.a₁ hW'
    rw [baseChange_a₁ W', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.veluQuotient_a₁,
      baseChange_a₁ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have ha₂ : (W'.a₂ : Kb) = (u : Kb)⁻¹ ^ 2 * (W.a₂ : Kb) := by
    have h := congrArg WeierstrassCurve.a₂ hW'
    rw [baseChange_a₂ W', WeierstrassCurve.variableChange_a₂, WeierstrassCurve.veluQuotient_a₂,
      baseChange_a₂ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have ha₄ : (W'.a₄ : Kb)
      = (u : Kb)⁻¹ ^ 4 * ((W.a₄ : Kb) - 5 * ((W.map (Int.castRingHom ℚ))⁄Kb).veluTSum S) := by
    have h := congrArg WeierstrassCurve.a₄ hW'
    rw [baseChange_a₄ W', WeierstrassCurve.variableChange_a₄, WeierstrassCurve.veluQuotient_a₄,
      baseChange_a₄ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  rw [ha₁, ha₂, ha₄] at hFx'
  have hmul := congrArg (· * (u : Kb) ^ 4) hFx'
  field_simp at hmul
  linear_combination hmul

private lemma centre_hnode_transfer (W W' : WeierstrassCurve ℤ) (u : Kbˣ) {S : Finset (Kb × Kb)}
    (hW' : (W'.map (Int.castRingHom ℚ))⁄Kb = (⟨u, 0, 0, 0⟩ : VariableChange Kb) •
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient S))
    (A : ValuationSubring Kb) (hu : A.valuation (u : Kb) = 1)
    (x₀' : Kb) (hnode' : A.valuation ((W'.b₂ : Kb) + 12 * x₀') = 1) :
    A.valuation ((W.b₂ : Kb) + 12 * ((u : Kb) ^ 2 * x₀')) = 1 := by
  have huK : (u : Kb) ≠ 0 := Units.ne_zero u
  have hb₂ : (W'.b₂ : Kb) = (u : Kb)⁻¹ ^ 2 * (W.b₂ : Kb) := by
    have h := congrArg WeierstrassCurve.b₂ hW'
    rw [baseChange_b₂ W', WeierstrassCurve.variableChange_b₂, WeierstrassCurve.veluQuotient_b₂,
      baseChange_b₂ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have hrw : (W.b₂ : Kb) + 12 * ((u : Kb) ^ 2 * x₀')
      = (u : Kb) ^ 2 * ((W'.b₂ : Kb) + 12 * x₀') := by
    rw [hb₂]; field_simp
  rw [hrw, map_mul, map_pow, hu, one_pow, one_mul, hnode']

private lemma centre_hbad_transfer (W W' : WeierstrassCurve ℤ) (u : Kbˣ) {S : Finset (Kb × Kb)}
    (hW' : (W'.map (Int.castRingHom ℚ))⁄Kb = (⟨u, 0, 0, 0⟩ : VariableChange Kb) •
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient S))
    (A : ValuationSubring Kb) (hu : A.valuation (u : Kb) = 1)
    (x₀' y₀' : Kb)
    (hbad' : A.valuation (y₀' ^ 2 + W'.a₁ * x₀' * y₀' + W'.a₃ * y₀'
      - (x₀' ^ 3 + W'.a₂ * x₀' ^ 2 + W'.a₄ * x₀' + W'.a₆)) < 1) :
    let t := ((W.map (Int.castRingHom ℚ))⁄Kb).veluTSum S
    let w := ((W.map (Int.castRingHom ℚ))⁄Kb).veluWSum S
    let z₀ := (u : Kb) ^ 2 * x₀'
    let Z₀ := (u : Kb) ^ 3 * y₀'
    A.valuation (Z₀ ^ 2 + (W.a₁ : Kb) * z₀ * Z₀ + W.a₃ * Z₀
      - (z₀ ^ 3 + W.a₂ * z₀ ^ 2 + ((W.a₄ : Kb) - 5 * t) * z₀
        + ((W.a₆ : Kb) - W.b₂ * t - 7 * w))) < 1 := by
  intro t w z₀ Z₀
  have huK : (u : Kb) ≠ 0 := Units.ne_zero u
  have ha₁ : (W'.a₁ : Kb) = (u : Kb)⁻¹ * (W.a₁ : Kb) := by
    have h := congrArg WeierstrassCurve.a₁ hW'
    rw [baseChange_a₁ W', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.veluQuotient_a₁,
      baseChange_a₁ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have ha₂ : (W'.a₂ : Kb) = (u : Kb)⁻¹ ^ 2 * (W.a₂ : Kb) := by
    have h := congrArg WeierstrassCurve.a₂ hW'
    rw [baseChange_a₂ W', WeierstrassCurve.variableChange_a₂, WeierstrassCurve.veluQuotient_a₂,
      baseChange_a₂ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have ha₃ : (W'.a₃ : Kb) = (u : Kb)⁻¹ ^ 3 * (W.a₃ : Kb) := by
    have h := congrArg WeierstrassCurve.a₃ hW'
    rw [baseChange_a₃ W', WeierstrassCurve.variableChange_a₃, WeierstrassCurve.veluQuotient_a₃,
      baseChange_a₃ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have ha₄ : (W'.a₄ : Kb)
      = (u : Kb)⁻¹ ^ 4 * ((W.a₄ : Kb) - 5 * t) := by
    have h := congrArg WeierstrassCurve.a₄ hW'
    rw [baseChange_a₄ W', WeierstrassCurve.variableChange_a₄, WeierstrassCurve.veluQuotient_a₄,
      baseChange_a₄ W] at h
    simpa [Units.val_inv_eq_inv_val] using h
  have ha₆ : (W'.a₆ : Kb)
      = (u : Kb)⁻¹ ^ 6 * ((W.a₆ : Kb) - W.b₂ * t - 7 * w) := by
    have h := congrArg WeierstrassCurve.a₆ hW'
    rw [baseChange_a₆ W', WeierstrassCurve.variableChange_a₆, WeierstrassCurve.veluQuotient_a₆,
      baseChange_a₆ W, baseChange_b₂ W] at h
    simpa [Units.val_inv_eq_inv_val] using h

  have hrw : Z₀ ^ 2 + (W.a₁ : Kb) * z₀ * Z₀ + W.a₃ * Z₀
      - (z₀ ^ 3 + W.a₂ * z₀ ^ 2 + ((W.a₄ : Kb) - 5 * t) * z₀
        + ((W.a₆ : Kb) - W.b₂ * t - 7 * w))
    = (u : Kb) ^ 6 * (y₀' ^ 2 + W'.a₁ * x₀' * y₀' + W'.a₃ * y₀'
      - (x₀' ^ 3 + W'.a₂ * x₀' ^ 2 + W'.a₄ * x₀' + W'.a₆)) := by
    rw [ha₁, ha₂, ha₃, ha₄, ha₆]
    simp only [z₀, Z₀]
    field_simp
  rw [hrw, map_mul, map_pow, hu, one_pow, one_mul]
  exact hbad'

private lemma valuation_c₄_veluQuotient_eq_one (W W' : WeierstrassCurve ℤ) (u : Kbˣ)
    {S : Finset (Kb × Kb)}
    (hW' : (W'.map (Int.castRingHom ℚ))⁄Kb = (⟨u, 0, 0, 0⟩ : VariableChange Kb) •
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient S))
    (A : ValuationSubring Kb) (hu : A.valuation (u : Kb) = 1)
    {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) (hqc₄' : ¬ (q : ℤ) ∣ W'.c₄) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient S).c₄ = 1 := by
  have hvc₄' : A.valuation (W'.c₄ : Kb) = 1 := valuation_intCast_eq_one_of_not_dvd A hq hA hqc₄'
  have hc₄ : (W'.c₄ : Kb)
      = ((u⁻¹ : Kbˣ) : Kb) ^ 4 * (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient S).c₄ := by
    have h := congrArg WeierstrassCurve.c₄ hW'
    rw [baseChange_c₄ W', WeierstrassCurve.variableChange_c₄] at h
    exact h
  rw [hc₄, map_mul, map_pow,
    show ((u⁻¹ : Kbˣ) : Kb) = (u : Kb)⁻¹ from Units.val_inv_eq_inv_val u,
    map_inv₀, hu, inv_one, one_pow, one_mul] at hvc₄'
  exact hvc₄'

end CentreTransfer

section CriterionWprime

local notation "Kb" => AlgebraicClosure ℚ

private lemma not_lhs_iff (W W' : WeierstrassCurve ℤ)
    (A : ValuationSubring Kb) (u : Kbˣ) (hu : A.valuation (u : Kb) = 1)
    {x₀' y₀' : Kb} (hx₀' : x₀' ∈ A) (hy₀' : y₀' ∈ A)
    (hFy' : 2 * y₀' + (W'.a₁ : Kb) * x₀' + W'.a₃ = 0)
    (hFx' : (W'.a₁ : Kb) * y₀' = 3 * x₀' ^ 2 + 2 * W'.a₂ * x₀' + W'.a₄)
    (hnode' : A.valuation ((W'.b₂ : Kb) + 12 * x₀') = 1)
    (hbad' : A.valuation (y₀' ^ 2 + W'.a₁ * x₀' * y₀' + W'.a₃ * y₀'
      - (x₀' ^ 3 + W'.a₂ * x₀' ^ 2 + W'.a₄ * x₀' + W'.a₆)) < 1)
    {S : Finset (Kb × Kb)} (x y : Kb)
    (h' : ((W'.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular
      (((u⁻¹ : Kbˣ) : Kb) ^ 2 * ((W.map (Int.castRingHom ℚ))⁄Kb).veluX S x)
      (((u⁻¹ : Kbˣ) : Kb) ^ 3 * ((W.map (Int.castRingHom ℚ))⁄Kb).veluY S x y)) :
    ¬ W'.InZeroComponentAt A (.some _ _ h')
      ↔ A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluX S x - (u : Kb) ^ 2 * x₀') < 1 := by
  rw [W'.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀' hy₀' hFy' hFx' hnode' hbad' h']
  rw [valuation_uscale_sub A u hu]

private lemma unit_mem_of_valuation_one (A : ValuationSubring Kb) (u : Kbˣ)
    (hu : A.valuation (u : Kb) = 1) :
    (u : Kb) ∈ A ∧ (u : Kb)⁻¹ ∈ A := by
  constructor
  · exact (A.valuation_le_one_iff _).mp hu.le
  · exact (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hu, inv_one])

private lemma zcentre_mem (A : ValuationSubring Kb) (u : Kbˣ)
    (hu : A.valuation (u : Kb) = 1) {x₀' y₀' : Kb} (hx₀' : x₀' ∈ A) (hy₀' : y₀' ∈ A) :
    (u : Kb) ^ 2 * x₀' ∈ A ∧ (u : Kb) ^ 3 * y₀' ∈ A := by
  have huA := (unit_mem_of_valuation_one A u hu).1
  exact ⟨mul_mem (pow_mem huA 2) hx₀', mul_mem (pow_mem huA 3) hy₀'⟩

end CriterionWprime

section TSetup

variable {R : Type*} [CommRing R]

private lemma veluQuotient_c₄ (W : WeierstrassCurve R) (S : Finset (R × R)) :
    (W.veluQuotient S).c₄ = W.c₄ + 240 * W.veluTSum S := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.veluQuotient_b₂,
    WeierstrassCurve.veluQuotient_b₄]
  ring

local notation "Kb" => AlgebraicClosure ℚ

private lemma ne_zero_exists_some {W : WeierstrassCurve ℤ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQ : Q ≠ 0) :
    ∃ (xQ yQ : Kb) (hQns : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xQ yQ),
      Q = .some xQ yQ hQns := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some xQ yQ hQns => exact ⟨xQ, yQ, hQns, rfl⟩

private lemma ne_zero_of_addOrderOf {G : Type*} [AddGroup G] {Q : G} {p : ℕ}
    (hQord : addOrderOf Q = p) (hp1 : 1 < p) : Q ≠ 0 := by
  intro h0
  rw [h0, addOrderOf_zero] at hQord
  omega

private lemma toric_caseA_absurd (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring Kb) (hA : A.LiesOverPrime q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {xQ yQ : Kb} (hQns : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xQ yQ)
    (hQord : addOrderOf (Point.some xQ yQ hQns) = p) (hxQA : xQ ∉ A)
    (hc₄V : A.valuation
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet (Point.some xQ yQ hQns) (p / 2))).c₄
      = 1) :
    False := by
  have hfk := W.valuation_c4_add_veluTSum_lt_one_of_formal_kernel hΔ hq hqΔ hqc₄ A hA hp hp2
    hQns hQord hxQA
  rw [veluQuotient_c₄, baseChange_c₄ W] at hc₄V
  exact absurd (hc₄V ▸ hfk) (lt_irrefl 1)

end TSetup

section DeltaPrime

local notation "Kb" => AlgebraicClosure ℚ

set_option maxHeartbeats 3200000 in
set_option maxSynthPendingDepth 3 in

private lemma deltaPrime_ne_zero (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point) (hQord : addOrderOf Q = p)
    (W' : WeierstrassCurve ℤ) (u : Kbˣ)
    (hW' : (W'.map (Int.castRingHom ℚ))⁄Kb = (⟨u, 0, 0, 0⟩ : VariableChange Kb) •
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q (p / 2)))) :
    W'.Δ ≠ 0 := by
  intro h0
  have hΔcast : ((W'.map (Int.castRingHom ℚ))⁄Kb).Δ = 0 := by
    rw [baseChange_Δ W', h0, Int.cast_zero]
  rw [hW', WeierstrassCurve.variableChange_Δ] at hΔcast
  rcases mul_eq_zero.mp hΔcast with hu0 | hV0
  · exact absurd hu0 (pow_ne_zero 12 (Units.ne_zero _))
  · have hWbΔ : ((W.map (Int.castRingHom ℚ))⁄Kb).Δ ≠ 0 := by
      rw [baseChange_Δ W]; exact_mod_cast hΔ
    have hQord' : addOrderOf Q = 2 * (p / 2) + 1 := by
      rw [hQord, Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2)]
    exact @WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero
      Kb _ _ _ two_ne_zero _ ⟨isUnit_iff_ne_zero.mpr hWbΔ⟩ (p / 2) Q hQord' hV0

end DeltaPrime

section Centre

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x₀ y₀ : R}

private theorem centre_veluT_eq_zero
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) :
    6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄ = 0 := by
  simp only [b₂, b₄]
  linear_combination W.a₁ * hFy - 2 * hFx

private theorem centre_c₄_mul_eq
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) :
    W.c₄ * x₀ = 18 * W.b₆ - W.b₂ * W.b₄
      + 72 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  simp only [c₄, b₂, b₄, b₆]
  linear_combination
    (W.a₁ * (W.a₁ ^ 2 + 4 * W.a₂) + 12 * x₀ * W.a₁
      - 18 * (2 * y₀ + W.a₁ * x₀ + W.a₃)) * hFy
    - (24 * x₀ + 2 * (W.a₁ ^ 2 + 4 * W.a₂)) * hFx

private theorem veluT_factor
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) (xk yk : R) :
    W.veluT xk yk = (xk - x₀) * ((W.b₂ + 12 * x₀) + 6 * (xk - x₀)) := by
  rw [veluT_eq]
  simp only [b₂, b₄]
  linear_combination W.a₁ * hFy - 2 * hFx

private theorem veluT_mul_add_veluU
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {xk yk : R} (hk : W.toAffine.Equation xk yk) (x : R) :
    W.veluT xk yk * (x - xk) + W.veluU xk yk
      = (W.b₂ + 12 * x₀) * (xk - x₀) * (x - x₀) + 6 * (xk - x₀) ^ 2 * (x - x₀)
        - 2 * (xk - x₀) ^ 3
        - 4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
            - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  rw [Affine.equation_iff] at hk
  simp only [veluT, veluU, veluGx, veluGy, b₂]
  linear_combination 4 * hk
    + ((2 * y₀ + W.a₁ * x₀ + W.a₃) + 2 * W.a₁ * (xk - x₀)) * hFy
    - 4 * (xk - x₀) * hFx
    + (x - xk) * (W.a₁ * hFy - 2 * hFx)

private theorem veluU_expand
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : R} (h : W.toAffine.Equation x y) :
    W.veluU x y
      = -4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
            - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        + (W.b₂ + 12 * x₀) * (x - x₀) ^ 2 + 4 * (x - x₀) ^ 3 := by
  have h0 := veluT_mul_add_veluU W hFy hFx h x
  rw [sub_self, mul_zero, zero_add] at h0
  rw [h0]; ring

end Centre

section Estimates

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

private theorem val_summand_lt_one (v : Valuation F Γ₀) {β X Xk ε4 : F}
    (hβ : v β = 1) (h6 : v 6 ≤ 1) (h2 : v 2 ≤ 1)
    (hX : v X ≤ 1) (hXk : v Xk < 1) (hne : v X ≠ v Xk)
    (hsh : v ε4 < v Xk ^ 2) :
    v ((β * Xk * X + 6 * Xk ^ 2 * X - 2 * Xk ^ 3 - ε4) / (X - Xk) ^ 2) < 1 := by
  have hXk0 : v Xk ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact not_lt_zero hsh
  have hXkpos : (0 : Γ₀) < v Xk := zero_lt_iff.mpr hXk0
  have hXksq : (0 : Γ₀) < v Xk ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 hXk0)
  have hM : v (X - Xk) = max (v X) (v Xk) := by
    rw [sub_eq_add_neg, Valuation.map_add_of_distinct_val, Valuation.map_neg]
    rw [Valuation.map_neg]
    exact hne
  rw [map_div₀, map_pow, hM]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have hXlt : v X < 1 := hlt.trans hXk
    rw [max_eq_right hlt.le, div_lt_one₀ hXksq]
    have m1 : v (β * Xk * X) < v Xk ^ 2 := by
      rw [map_mul, map_mul, hβ, one_mul, sq]
      exact (mul_lt_mul_iff_right₀ hXkpos).mpr hlt
    have m2 : v (6 * Xk ^ 2 * X) < v Xk ^ 2 := by
      rw [map_mul, map_mul, map_pow, mul_assoc]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h6) ?_
      calc v Xk ^ 2 * v X < v Xk ^ 2 * 1 := (mul_lt_mul_iff_right₀ hXksq).mpr hXlt
        _ = v Xk ^ 2 := mul_one _
    have m3 : v (2 * Xk ^ 3) < v Xk ^ 2 := by
      rw [map_mul, map_pow]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h2) ?_
      exact pow_lt_pow_right_of_lt_one₀ hXkpos hXk (by norm_num)
    exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ (Valuation.map_add_lt _ m1 m2) m3) hsh
  ·
    have hXpos : (0 : Γ₀) < v X := lt_trans hXkpos hgt
    have hXsq : (0 : Γ₀) < v X ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 (zero_lt_iff.mp hXpos))
    rw [max_eq_left hgt.le, div_lt_one₀ hXsq]
    have hsq : v Xk ^ 2 < v X ^ 2 := pow_lt_pow_left₀ hgt zero_le' two_ne_zero
    have m1 : v (β * Xk * X) < v X ^ 2 := by
      rw [map_mul, map_mul, hβ, one_mul, sq]
      exact (mul_lt_mul_iff_left₀ hXpos).mpr hgt
    have m2 : v (6 * Xk ^ 2 * X) < v X ^ 2 := by
      rw [map_mul, map_mul, map_pow, mul_assoc]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h6) ?_
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hX) hsq
    have m3 : v (2 * Xk ^ 3) < v X ^ 2 := by
      rw [map_mul, map_pow]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' h2) ?_
      calc v Xk ^ 3 < v X ^ 3 := pow_lt_pow_left₀ hgt zero_le' three_ne_zero
        _ = v X ^ 2 * v X := by rw [pow_succ]
        _ ≤ v X ^ 2 := mul_le_of_le_one_right' hX
    have m4 : v ε4 < v X ^ 2 := lt_trans hsh hsq
    exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ (Valuation.map_add_lt _ m1 m2) m3) m4

private theorem val_numer_collision (v : Valuation F Γ₀) {β X Xk ε4 : F}
    (hβ : v β = 1) (h6 : v 6 ≤ 1) (h2 : v 2 ≤ 1)
    (hX : v X < 1) (hX0 : v X ≠ 0) (heq : v Xk = v X)
    (hsh : v ε4 < v X ^ 2) :
    v (β * Xk * X + 6 * Xk ^ 2 * X - 2 * Xk ^ 3 - ε4) = v X ^ 2 := by
  have hXpos : (0 : Γ₀) < v X := zero_lt_iff.mpr hX0
  have hXsq : (0 : Γ₀) < v X ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 hX0)
  have hrw : β * Xk * X + 6 * Xk ^ 2 * X - 2 * Xk ^ 3 - ε4
      = β * Xk * X + (6 * Xk ^ 2 * X - (2 * Xk ^ 3) - ε4) := by ring
  have m1 : v (β * Xk * X) = v X ^ 2 := by
    rw [map_mul, map_mul, hβ, one_mul, heq, sq]
  have m2 : v (6 * Xk ^ 2 * X) < v X ^ 2 := by
    rw [map_mul, map_mul, map_pow, heq, mul_assoc]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' h6) ?_
    calc v X ^ 2 * v X < v X ^ 2 * 1 := (mul_lt_mul_iff_right₀ hXsq).mpr hX
      _ = v X ^ 2 := mul_one _
  have m3 : v (2 * Xk ^ 3) < v X ^ 2 := by
    rw [map_mul, map_pow, heq]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' h2) ?_
    exact pow_lt_pow_right_of_lt_one₀ hXpos hX (by norm_num)
  have hR : v (6 * Xk ^ 2 * X - (2 * Xk ^ 3) - ε4) < v (β * Xk * X) := by
    rw [m1]
    exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ m2 m3) hsh
  rw [hrw, Valuation.map_add_eq_of_lt_left _ hR, m1]

end Estimates

section Integrality

local notation "Kb" => AlgebraicClosure ℚ

private theorem val_y_le_one (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb) {x y : Kb}
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y)
    (hx : A.valuation x ≤ 1) : A.valuation y ≤ 1 := by
  by_contra hgt
  push Not at hgt
  rw [Affine.equation_iff] at h
  simp only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
    Affine.baseChange_a₄, Affine.baseChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    eq_intCast, map_intCast] at h
  have hcast : ∀ m : ℤ, A.valuation ((m : Kb)) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hypos : (0 : _) < A.valuation y := lt_trans zero_lt_one hgt
  have hx3 : A.valuation (x ^ 3) ≤ 1 := by rw [map_pow]; exact pow_le_one' hx 3
  have hx2 : A.valuation ((W.a₂ : Kb) * x ^ 2) ≤ 1 := by
    rw [map_mul, map_pow]; exact mul_le_one' (hcast _) (pow_le_one' hx 2)
  have hx1 : A.valuation ((W.a₄ : Kb) * x) ≤ 1 := by
    rw [map_mul]; exact mul_le_one' (hcast _) hx
  have hrhs : A.valuation (x ^ 3 + (W.a₂ : Kb) * x ^ 2 + (W.a₄ : Kb) * x + (W.a₆ : Kb)) ≤ 1 :=
    A.valuation.map_add_le (A.valuation.map_add_le (A.valuation.map_add_le hx3 hx2) hx1)
      (hcast _)
  have ha1y : A.valuation ((W.a₁ : Kb) * x * y) ≤ A.valuation y := by
    rw [map_mul, map_mul]
    exact mul_le_of_le_one_left' (mul_le_one' (hcast _) hx)
  have ha3y : A.valuation ((W.a₃ : Kb) * y) ≤ A.valuation y := by
    rw [map_mul]
    exact mul_le_of_le_one_left' (hcast _)
  have hylt : A.valuation y < A.valuation (y ^ 2) := by
    rw [map_pow, sq]
    nth_rewrite 1 [← one_mul (A.valuation y)]
    exact (mul_lt_mul_iff_left₀ hypos).mpr hgt
  have h1 : A.valuation ((W.a₁ : Kb) * x * y + (W.a₃ : Kb) * y) < A.valuation (y ^ 2) :=
    lt_of_le_of_lt (A.valuation.map_add_le ha1y ha3y) hylt
  have hlhs : 1 < A.valuation (y ^ 2 + ((W.a₁ : Kb) * x * y + (W.a₃ : Kb) * y)) := by
    rw [Valuation.map_add_eq_of_lt_left _ h1, map_pow, sq]
    calc (1 : _) < A.valuation y := hgt
      _ < A.valuation y * A.valuation y := by
          nth_rewrite 1 [← one_mul (A.valuation y)]
          exact (mul_lt_mul_iff_left₀ hypos).mpr hgt
  have heq : y ^ 2 + ((W.a₁ : Kb) * x * y + (W.a₃ : Kb) * y)
      = x ^ 3 + (W.a₂ : Kb) * x ^ 2 + (W.a₄ : Kb) * x + W.a₆ := by
    linear_combination h
  rw [heq] at hlhs
  exact absurd hrhs (not_le.mpr hlhs)

end Integrality

section NTTranslate

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)

private lemma mem_of_nsmul_mem {p : ℕ} (hp : p.Prime)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQ : p • Q = 0)
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

private lemma kernel_affine {p : ℕ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    {m : ℕ} (hm1 : 1 ≤ m) (hmp : m < p) :
    ∃ (xm ym : Kb) (hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym),
      m • Q = .some xm ym hm := by
  have hne : m • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQord]; omega)
  cases hmQ : m • Q with
  | zero => exact absurd hmQ hne
  | some xm ym hm => exact ⟨xm, ym, hm, rfl⟩

private lemma kernel_neg {p : ℕ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    {m : ℕ} (hmp : m ≤ p) : (p - m) • Q = -(m • Q) := by
  have hpQ : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hmp, hpQ]

private lemma exists_nsmul_eq_of_mem_zmultiples {p : ℕ} (hp : 0 < p)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    {k : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hk : k ∈ AddSubgroup.zmultiples Q) :
    ∃ m : ℕ, m < p ∧ k = m • Q := by
  obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hk
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  refine ⟨(a % p).toNat, ?_, ?_⟩
  · have h1 : a % p < p := Int.emod_lt_of_pos a (by exact_mod_cast hp)
    have h2 : 0 ≤ a % p := Int.emod_nonneg a hp0
    omega
  · have h2 : 0 ≤ a % p := Int.emod_nonneg a hp0
    have hmodeq : (a % (p : ℤ)) • Q = a • Q := by
      have := mod_addOrderOf_zsmul Q a
      rwa [hQord] at this
    change a • Q = ((a % ↑p).toNat : ℕ) • Q
    rw [← natCast_zsmul, Int.toNat_of_nonneg h2, hmodeq]

private lemma mem_zmultiples_of_x_eq
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} {m : ℕ}
    {xm ym : Kb} {hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym}
    (hmQ : m • Q = .some xm ym hm)
    {x y : Kb} {h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y}
    (hx : x = xm) :
    (Point.some x y h) ∈ AddSubgroup.zmultiples Q := by
  have hmem : m • Q ∈ AddSubgroup.zmultiples Q := by
    rw [← natCast_zsmul]; exact AddSubgroup.zsmul_mem_zmultiples Q m
  rcases (X_eq_iff (h₁ := h) (h₂ := hm)).mp hx with heq | heq
  · rw [heq, ← hmQ]; exact hmem
  · rw [heq, ← hmQ]; exact AddSubgroup.neg_mem _ hmem

private lemma kernel_level {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hA : A.LiesOverPrime q)
    {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    (hout : ¬ W.InZeroComponentAt A Q)
    {m : ℕ} (hm1 : 1 ≤ m) (hmp : m < p)
    {xm ym : Kb} {hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym}
    (hmQ : m • Q = .some xm ym hm) :
    A.valuation (xm - x₀) < 1 ∧
      A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xm - x₀) ^ 2 := by
  have hpQ : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  have houtm : ¬ W.InZeroComponentAt A (.some xm ym hm) := by
    have h' : ¬ W.InZeroComponentAt A (m • Q) :=
      fun hin => hout (mem_of_nsmul_mem W A hp hpQ (Nat.not_dvd_of_pos_of_lt hm1 hmp) hin)
    rw [hmQ] at h'
    exact h'
  have hlev : A.valuation (xm - x₀) < 1 :=
    (W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad hm).mp houtm
  refine ⟨hlev, ?_⟩
  have htor : p • (Point.some xm ym hm) = 0 := by
    have h' : p • (m • Q) = 0 := by rw [smul_comm, hpQ, nsmul_zero]
    rw [hmQ] at h'
    exact h'
  have hrow := W.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt hq hΔ hqΔ hqc₄ A hA
    hx₀ hy₀ hFy hFx hnode hbad hp hp2 hm htor hlev
  rw [← W.valuation_discriminant_eq_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad]
  exact hrow.1

private theorem valuation_slope_le_one {x₀ y₀ x y : Kb} (hx₀ : x₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2) :
    A.valuation ((y - y₀) / (x - x₀)) ≤ 1 := by
  have key : (y - y₀) ^ 2 + (W.a₁ : Kb) * (x - x₀) * (y - y₀)
      = (3 * x₀ + W.a₂) * (x - x₀) ^ 2 + (x - x₀) ^ 3
        - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
    rw [Affine.equation_iff] at h
    simp only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
      Affine.baseChange_a₄, Affine.baseChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      eq_intCast, map_intCast] at h
    linear_combination h - (y - y₀) * hFy - (x - x₀) * hFx
  have hX0 : A.valuation (x - x₀) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact not_lt_zero hsh
  suffices hYX : A.valuation (y - y₀) ≤ A.valuation (x - x₀) by
    rw [map_div₀]
    exact div_le_one_of_le₀ hYX zero_le'
  by_contra hlt
  rw [not_le] at hlt
  have hY0 : 0 < A.valuation (y - y₀) := lt_of_le_of_lt zero_le' hlt
  have key' := congrArg A.valuation key
  have ha₁ : A.valuation (W.a₁ : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hcross : A.valuation ((W.a₁ : Kb) * (x - x₀) * (y - y₀)) < A.valuation ((y - y₀) ^ 2) := by
    rw [map_mul, map_mul, map_pow, pow_two]
    calc A.valuation (W.a₁ : Kb) * A.valuation (x - x₀) * A.valuation (y - y₀)
        ≤ A.valuation (x - x₀) * A.valuation (y - y₀) := by
          rw [mul_assoc]; exact mul_le_of_le_one_left' ha₁
      _ < A.valuation (y - y₀) * A.valuation (y - y₀) := (mul_lt_mul_iff_left₀ hY0).mpr hlt
  have hlhs : A.valuation ((y - y₀) ^ 2 + (W.a₁ : Kb) * (x - x₀) * (y - y₀))
      = A.valuation (y - y₀) ^ 2 := by
    rw [Valuation.map_add_eq_of_lt_left _ hcross, map_pow]
  have hXY2 : A.valuation (x - x₀) ^ 2 < A.valuation (y - y₀) ^ 2 :=
    pow_lt_pow_left₀ hlt zero_le' two_ne_zero
  have h3x₀ : A.valuation (3 * x₀ + (W.a₂ : Kb)) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (add_mem (mul_mem (ofNat_mem A 3) hx₀) (intCast_mem A _))
  have hr1 : A.valuation ((3 * x₀ + (W.a₂ : Kb)) * (x - x₀) ^ 2) < A.valuation (y - y₀) ^ 2 := by
    rw [map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h3x₀) hXY2
  have hr2 : A.valuation ((x - x₀) ^ 3) < A.valuation (y - y₀) ^ 2 := by
    rw [map_pow]
    exact lt_trans (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hX0) hX (by norm_num)) hXY2
  have hr3 : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (y - y₀) ^ 2 :=
    lt_trans hsh hXY2
  have hrhs := Valuation.map_sub_lt A.valuation (Valuation.map_add_lt A.valuation hr1 hr2) hr3
  rw [← key', hlhs] at hrhs
  exact lt_irrefl _ hrhs

private theorem branch_dichotomy {s₁ s₂ : Kb}
    (h₁ : A.valuation s₁ ≤ 1) (h₂ : A.valuation s₂ ≤ 1) :
    A.valuation (s₁ - s₂) < 1 ∨ A.valuation (s₁ - s₂) = 1 :=
  (Valuation.map_sub_le A.valuation h₁ h₂).lt_or_eq

private lemma sub_mem_or_add_mem_of_level_eq
    {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ : Kb}
    (h₁ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₁ y₁)
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₂ y₂)
    (hX₁ : A.valuation (x₁ - x₀) < 1) (hX₂ : A.valuation (x₂ - x₀) < 1)
    (hlev : A.valuation (x₁ - x₀) = A.valuation (x₂ - x₀))
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₁ - x₀) ^ 2) :
    W.InZeroComponentAt A (.some x₁ y₁ h₁ - .some x₂ y₂ h₂) ∨
      W.InZeroComponentAt A (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) := by
  have hsh₂ : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₂ - x₀) ^ 2 := by
    rw [← hlev]; exact hsh
  have hs₁ := valuation_slope_le_one W A hx₀ hFy hFx h₁.left hX₁ hsh
  have hs₂ := valuation_slope_le_one W A hx₀ hFy hFx h₂.left hX₂ hsh₂
  rcases branch_dichotomy A hs₁ hs₂ with hbr | hbr
  · exact Or.inl (W.inZeroComponentAt_sub_of_level_eq_of_branch_eq A hx₀ hy₀ hFy hFx hnode hbad
      h₁ h₂ hX₁ hX₂ hlev hsh hbr).1
  · exact Or.inr (W.inZeroComponentAt_add_of_level_eq_of_branch_ne A hx₀ hy₀ hFy hFx hnode hbad
      h₁ h₂ hX₁ hX₂ hlev hsh hbr).1

private lemma kernel_level_injOn {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hA : A.LiesOverPrime q)
    {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    (hout : ¬ W.InZeroComponentAt A Q)
    {m m' : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ p / 2) (hm1' : 1 ≤ m') (hmn' : m' ≤ p / 2)
    {xm ym : Kb} {hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym}
    (hmQ : m • Q = .some xm ym hm)
    {xm' ym' : Kb} {hm' : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm' ym'}
    (hmQ' : m' • Q = .some xm' ym' hm')
    (hlev : A.valuation (xm - x₀) = A.valuation (xm' - x₀)) : m = m' := by
  have hpQ : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  have hmp : m < p := lt_of_le_of_lt hmn (Nat.div_lt_self hp.pos one_lt_two)
  have hmp' : m' < p := lt_of_le_of_lt hmn' (Nat.div_lt_self hp.pos one_lt_two)
  have h2n : 2 * (p / 2) < p := by
    have := Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2); omega
  obtain ⟨hX, hsh⟩ := kernel_level W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 hQord
    hout hm1 hmp hmQ
  obtain ⟨hX', -⟩ := kernel_level W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 hQord
    hout hm1' hmp' hmQ'
  by_contra hne

  have hcl : ∀ d : ℕ, 0 < d → d < p → ¬ W.InZeroComponentAt A (d • Q) := fun d hd1 hdp hin =>
    hout (mem_of_nsmul_mem W A hp hpQ (Nat.not_dvd_of_pos_of_lt hd1 hdp) hin)
  have hdich : W.InZeroComponentAt A (m • Q - m' • Q) ∨ W.InZeroComponentAt A (m • Q + m' • Q) := by
    rw [hmQ, hmQ']
    exact sub_mem_or_add_mem_of_level_eq W A hx₀ hy₀ hFy hFx hnode hbad hm hm' hX hX' hlev hsh
  rcases hdich with hz | hz
  · rcases lt_or_gt_of_ne hne with hlt | hlt
    ·
      have hz' := negMem W A hz
      rw [neg_sub, sub_eq_add_neg, ← sub_nsmul Q hlt.le] at hz'
      exact hcl (m' - m) (by omega) (by omega) hz'
    · have hz' : W.InZeroComponentAt A ((m - m') • Q) := by
        rw [sub_nsmul Q hlt.le, ← sub_eq_add_neg]; exact hz
      exact hcl (m - m') (by omega) (by omega) hz'
  · rw [← add_nsmul] at hz
    exact hcl (m + m') (by omega) (by omega) hz

private lemma rhs_of_level_eq {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hA : A.LiesOverPrime q)
    {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    (hout : ¬ W.InZeroComponentAt A Q)
    {m : ℕ} (hm1 : 1 ≤ m) (hmp : m < p)
    {xm ym : Kb} {hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym}
    (hmQ : m • Q = .some xm ym hm)
    {x y : Kb} (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y)
    (hlev : A.valuation (x - x₀) = A.valuation (xm - x₀)) :
    ∃ k ∈ AddSubgroup.zmultiples Q, W.InZeroComponentAt A (Point.some x y h - k) := by
  obtain ⟨hXm, hshm⟩ := kernel_level W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 hQord
    hout hm1 hmp hmQ
  have hX : A.valuation (x - x₀) < 1 := by rw [hlev]; exact hXm
  have hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2 := by
    rw [hlev]; exact hshm
  have hmem : m • Q ∈ AddSubgroup.zmultiples Q := by
    rw [← natCast_zsmul]; exact AddSubgroup.zsmul_mem_zmultiples Q m
  rcases sub_mem_or_add_mem_of_level_eq W A hx₀ hy₀ hFy hFx hnode hbad h hm hX hXm hlev hsh
    with hz | hz
  · exact ⟨m • Q, hmem, by rw [hmQ]; exact hz⟩
  · exact ⟨-(m • Q), AddSubgroup.neg_mem _ hmem, by rw [sub_neg_eq_add, hmQ]; exact hz⟩

private lemma level_eq_of_rhs {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hA : A.LiesOverPrime q)
    {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    (hout : ¬ W.InZeroComponentAt A Q)
    {x y : Kb} (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y)
    (hX : A.valuation (x - x₀) < 1)
    (hrhs : ∃ k ∈ AddSubgroup.zmultiples Q, W.InZeroComponentAt A (Point.some x y h - k)) :
    ∃ (m : ℕ) (xm ym : Kb) (hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym),
      1 ≤ m ∧ m ≤ p / 2 ∧ m • Q = .some xm ym hm ∧
        A.valuation (x - x₀) = A.valuation (xm - x₀) := by
  obtain ⟨k, hk, hz⟩ := hrhs
  obtain ⟨m', hm'p, rfl⟩ := exists_nsmul_eq_of_mem_zmultiples W hp.pos hQord hk
  have hpodd := Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2)

  have key : ∀ {x₂ y₂ : Kb} (h₂ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₂ y₂)
      (R : ((W.map (Int.castRingHom ℚ))⁄Kb).Point), W.InZeroComponentAt A R →
      R + .some x₂ y₂ h₂ = .some x y h → A.valuation (x₂ - x₀) < 1 →
      A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₂ - x₀) ^ 2 →
      A.valuation (x - x₀) = A.valuation (x₂ - x₀) := by
    intro x₂ y₂ h₂ R hR hsum hX₂ hsh₂
    obtain ⟨x₃, y₃, h₃, h3eq, -, hlev3, -⟩ :=
      W.level_add_of_inZeroComponentAt A hx₀ hy₀ hFy hFx hnode hbad R hR h₂ hX₂
    have hx3 : x₃ = x := by
      have := h3eq.symm.trans hsum
      rw [some.injEq] at this
      exact this.1
    rw [← hx3]
    exact (hlev3 hsh₂).1
  rcases Nat.eq_zero_or_pos m' with rfl | hm'1
  ·
    exfalso
    rw [zero_nsmul, sub_zero] at hz
    exact (W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad h).mpr
      hX hz
  rcases le_or_gt m' (p / 2) with hle | hgt
  ·
    obtain ⟨xm, ym, hm, hmQ⟩ := kernel_affine W hQord hm'1 hm'p
    obtain ⟨hXm, hshm⟩ := kernel_level W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2
      hQord hout hm'1 hm'p hmQ
    refine ⟨m', xm, ym, hm, hm'1, hle, hmQ, ?_⟩
    refine key hm (.some x y h - m' • Q) hz ?_ hXm hshm
    rw [← hmQ, sub_add_cancel]
  ·
    have hm1 : 1 ≤ p - m' := by omega
    have hmn : p - m' ≤ p / 2 := by omega
    have hmp : p - m' < p := by omega
    obtain ⟨xm, ym, hm, hmQ⟩ := kernel_affine W hQord hm1 hmp
    obtain ⟨hXm, hshm⟩ := kernel_level W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2
      hQord hout hm1 hmp hmQ
    refine ⟨p - m', xm, ym, hm, hm1, hmn, hmQ, ?_⟩
    have hneg : m' • Q = -((p - m') • Q) := by
      rw [kernel_neg W hQord hm'p.le, neg_neg]
    have hnegpt : -((p - m') • Q) = .some xm (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY xm ym)
        ((nonsingular_neg ..).mpr hm) := by
      rw [hmQ, neg_some]
    have hsum : (.some x y h - m' • Q) + .some xm (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY
        xm ym) ((nonsingular_neg ..).mpr hm) = .some x y h := by
      rw [← hnegpt, ← hneg, sub_add_cancel]
    exact key _ (.some x y h - m' • Q) hz hsum hXm hshm

end NTTranslate

section Reindex

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

private lemma sum_oddOrderSummingSet_eq {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) {M : Type*} [AddCommMonoid M] (g : F × F → M) :
    ∑ P ∈ W'.oddOrderSummingSet Q n, g P = ∑ k ∈ Finset.Icc 1 n, g (k • Q).coordsOrZero := by
  rw [oddOrderSummingSet, Finset.sum_image]
  intro k hk k' hk' h
  exact coords_inj_on_Icc W' hord hn (by simpa only [Finset.coe_Icc, Set.mem_Icc] using Finset.mem_Icc.mp hk)
    (by simpa only [Finset.coe_Icc, Set.mem_Icc] using Finset.mem_Icc.mp hk') h

private lemma veluX_eq_sum_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p)
    {xk yk : ℕ → F} {hk : ∀ k ∈ Finset.Icc 1 n, W'.toAffine.Nonsingular (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 n), k • Q = .some (xk k) (yk k) (hk k hk')) (x : F) :
    W'.veluX (W'.oddOrderSummingSet Q n) x
      = x + ∑ k ∈ Finset.Icc 1 n,
          (W'.veluT (xk k) (yk k) / (x - xk k) + W'.veluU (xk k) (yk k) / (x - xk k) ^ 2) := by
  unfold veluX
  rw [sum_oddOrderSummingSet_eq W' hord hn]
  congr 1
  refine Finset.sum_congr rfl fun k hk' => ?_
  rw [hkQ k hk', Affine.Point.coordsOrZero_some]

private lemma veluTSum_eq_sum_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p)
    {xk yk : ℕ → F} {hk : ∀ k ∈ Finset.Icc 1 n, W'.toAffine.Nonsingular (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 n), k • Q = .some (xk k) (yk k) (hk k hk')) :
    W'.veluTSum (W'.oddOrderSummingSet Q n) = ∑ k ∈ Finset.Icc 1 n, W'.veluT (xk k) (yk k) := by
  unfold veluTSum
  rw [sum_oddOrderSummingSet_eq W' hord hn]
  refine Finset.sum_congr rfl fun k hk' => ?_
  rw [hkQ k hk', Affine.Point.coordsOrZero_some]

private lemma veluWSum_eq_sum_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p)
    {xk yk : ℕ → F} {hk : ∀ k ∈ Finset.Icc 1 n, W'.toAffine.Nonsingular (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 n), k • Q = .some (xk k) (yk k) (hk k hk')) :
    W'.veluWSum (W'.oddOrderSummingSet Q n) = ∑ k ∈ Finset.Icc 1 n, W'.veluW (xk k) (yk k) := by
  unfold veluWSum
  rw [sum_oddOrderSummingSet_eq W' hord hn]
  refine Finset.sum_congr rfl fun k hk' => ?_
  rw [hkQ k hk', Affine.Point.coordsOrZero_some]

end Reindex

section KernelChoice

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ)

private lemma exists_kernel_coords {p : ℕ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p) :
    ∃ (xk yk : ℕ → Kb)
      (hk : ∀ k ∈ Finset.Icc 1 (p - 1), ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular
        (xk k) (yk k)),
      ∀ k (hk' : k ∈ Finset.Icc 1 (p - 1)), k • Q = .some (xk k) (yk k) (hk k hk') := by
  have hpt : ∀ k ∈ Finset.Icc 1 (p - 1), ∃ (x y : Kb)
      (hxy : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y), k • Q = .some x y hxy := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact kernel_affine W hQord hk.1 (by omega)
  choose! xk yk hk hkQ using hpt
  exact ⟨xk, yk, hk, hkQ⟩

end KernelChoice

section Chebyshev

variable {k : Type*} [Field k]

private lemma cheb_identity (w : k) (m : ℕ) (hm : 1 ≤ m) :
    (w ^ m - 1) ^ 2 - w ^ (m - 1) * (w - 1) ^ 2 = (w ^ (m + 1) - 1) * (w ^ (m - 1) - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

private theorem chebyshev_orbit {p : ℕ} (hp3 : 3 ≤ p) (Y : ℕ → k)
    (hY0 : ∀ m, 1 ≤ m → m ≤ p - 1 → Y m ≠ 0)
    (h2 : Y 2 = Y 1 ^ 2 + 4 * Y 1)
    (hrec : ∀ m, 2 ≤ m → m ≤ p - 2 → (Y m - Y 1) ^ 2 = Y (m + 1) * Y (m - 1))
    (hsym1 : Y (p - 1) = Y 1) (hsym2 : Y (p - 2) = Y 2)
    {w : k} (hw : w ^ 2 - (2 + Y 1) * w + 1 = 0) :
    (∀ m, 1 ≤ m → m ≤ p - 1 → Y m * w ^ m = (w ^ m - 1) ^ 2) ∧ w ^ p = 1 ∧ w ≠ 1 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hY1 : Y 1 * w ^ 1 = (w ^ 1 - 1) ^ 2 := by linear_combination -hw
  have hY2 : Y 2 * w ^ 2 = (w ^ 2 - 1) ^ 2 := by
    rw [h2]; linear_combination (Y 1 * w + w ^ 2 + 2 * w + 1) * hY1

  have key : ∀ m, 1 ≤ m → m + 1 ≤ p - 1 →
      Y m * w ^ m = (w ^ m - 1) ^ 2 ∧ Y (m + 1) * w ^ (m + 1) = (w ^ (m + 1) - 1) ^ 2 := by
    intro m hm1 hmp
    induction m with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact ⟨hY1, hY2⟩
      · obtain ⟨ihj, ihj1⟩ := ih hj (by omega)
        refine ⟨ihj1, ?_⟩

        have hr := hrec (j + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hr
        have hne : (w ^ j - 1) ^ 2 ≠ 0 := by
          rw [← ihj]; exact mul_ne_zero (hY0 j hj (by omega)) (pow_ne_zero _ hw0)
        have hid := cheb_identity w (j + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hid

        have hcalc : Y (j + 1 + 1) * w ^ (j + 1 + 1) * (w ^ j - 1) ^ 2
            = (w ^ (j + 1 + 1) - 1) ^ 2 * (w ^ j - 1) ^ 2 := by
          have e1 : Y (j + 1 + 1) * w ^ (j + 1 + 1) * (w ^ j - 1) ^ 2
              = (Y (j + 1 + 1) * Y j) * (w ^ (j + 1 + 1) * w ^ j) := by rw [← ihj]; ring
          have e2 : (Y (j + 1 + 1) * Y j) * (w ^ (j + 1 + 1) * w ^ j)
              = ((Y (j + 1) - Y 1) * w ^ (j + 1)) ^ 2 := by rw [← hr]; ring
          have e3 : (Y (j + 1) - Y 1) * w ^ (j + 1)
              = (w ^ (j + 1) - 1) ^ 2 - w ^ j * (w - 1) ^ 2 := by
            have := ihj1
            have h1' := hY1
            simp only [pow_one] at h1'
            linear_combination this - w ^ j * h1'
          rw [e1, e2, e3, hid]; ring
        exact mul_right_cancel₀ hne hcalc
  have hall : ∀ m, 1 ≤ m → m ≤ p - 1 → Y m * w ^ m = (w ^ m - 1) ^ 2 := by
    intro m hm1 hmp
    rcases lt_or_eq_of_le hmp with hlt | heq
    · exact (key m hm1 (by omega)).1
    · have := (key (m - 1) (by omega) (by omega)).2
      rwa [show m - 1 + 1 = m by omega] at this
  have hw1 : w ≠ 1 := by
    rintro rfl
    have := hY1
    simp at this
    exact hY0 1 le_rfl (by omega) this
  refine ⟨hall, ?_, hw1⟩
  have h1' : Y 1 * w = (w - 1) ^ 2 := by simpa using hY1

  have hwneg : w ≠ -1 := by
    rintro rfl
    have : Y 1 = -4 := by linear_combination -h1'
    exact hY0 2 (by norm_num) (by omega) (by rw [h2, this]; norm_num)
  have hsq : w ^ 2 ≠ 1 := fun h => by
    rcases sq_eq_one_iff.mp h with h | h
    · exact hw1 h
    · exact hwneg h

  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  ·
    interval_cases p
    ·
      have e : Y 1 * w ^ 2 = (w ^ 2 - 1) ^ 2 := by rw [← hsym1]; exact hY2
      have h3 : (w ^ 3 - 1) * (w - 1) = 0 := by linear_combination w * h1' - e
      rcases mul_eq_zero.mp h3 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h) hw1
    ·
      have e : Y 1 * w ^ 3 = (w ^ 3 - 1) ^ 2 := by rw [← hsym1]; exact hall 3 (by omega) le_rfl
      have h4 : (w ^ 4 - 1) * (w ^ 2 - 1) = 0 := by linear_combination w ^ 2 * h1' - e
      rcases mul_eq_zero.mp h4 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h) hsq
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + 5 := ⟨p - 5, by omega⟩
    have eA : Y 1 * w ^ (i + 4) = (w ^ (i + 4) - 1) ^ 2 := by
      rw [← hsym1]; exact hall (i + 4) (by omega) (by omega)
    have eB : Y 2 * w ^ (i + 3) = (w ^ (i + 3) - 1) ^ 2 := by
      have hs : Y (i + 3) = Y 2 := hsym2
      rw [← hs]; exact hall (i + 3) (by omega) (by omega)
    have hA : (w ^ (i + 5) - 1) * (w ^ (i + 3) - 1) = 0 := by
      linear_combination w ^ (i + 3) * h1' - eA
    have hB : (w ^ (i + 5) - 1) * (w ^ (i + 1) - 1) = 0 := by
      linear_combination w ^ (i + 1) * hY2 - eB
    rcases mul_eq_zero.mp hA with hA | hA
    · exact sub_eq_zero.mp hA
    rcases mul_eq_zero.mp hB with hB | hB
    · exact sub_eq_zero.mp hB

    exfalso
    have h3 : w ^ (i + 3) = 1 := sub_eq_zero.mp hA
    have h1 : w ^ (i + 1) = 1 := sub_eq_zero.mp hB
    apply hsq
    have : w ^ (i + 3) = w ^ (i + 1) * w ^ 2 := by ring
    rw [h3, h1, one_mul] at this
    exact this.symm

end Chebyshev

section NTEndgame

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)

private lemma exists_kernel_coords_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p) :
    ∃ (xk yk : ℕ → Kb)
      (hk : ∀ k ∈ Finset.Icc 1 (p / 2), ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular
        (xk k) (yk k)),
      ∀ k (hk' : k ∈ Finset.Icc 1 (p / 2)), k • Q = .some (xk k) (yk k) (hk k hk') := by
  have h2n : 2 * (p / 2) < p := by
    have := Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2); omega
  have hpt : ∀ k ∈ Finset.Icc 1 (p / 2), ∃ (x y : Kb)
      (hxy : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y), k • Q = .some x y hxy := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact kernel_affine W hQord hk.1 (by omega)
  choose! xk yk hk hkQ using hpt
  exact ⟨xk, yk, hk, hkQ⟩

private theorem nt_endgame {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hA : A.LiesOverPrime q)
    {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    (hout : ¬ W.InZeroComponentAt A Q)
    {xk yk : ℕ → Kb}
    {hk : ∀ m ∈ Finset.Icc 1 (p / 2),
      ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xk m) (yk m)}
    (hkQ : ∀ m (hm : m ∈ Finset.Icc 1 (p / 2)), m • Q = .some (xk m) (yk m) (hk m hm))
    {x y : Kb} (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y)
    (hL : (Point.some x y h) ∉ AddSubgroup.zmultiples Q)
    (vX : Kb)
    {L : Prop} (hcrit : ¬ L ↔ A.valuation (vX - x₀) < 1)
    (master_off : (∀ m ∈ Finset.Icc 1 (p / 2), x ≠ xk m) →
      (∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x - x₀) ≠ A.valuation (xk m - x₀)) →
      A.valuation (x - x₀) < 1 → A.valuation (vX - x₀) < 1)
    (master_on : (∀ m ∈ Finset.Icc 1 (p / 2), x ≠ xk m) →
      ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x - x₀) = A.valuation (xk m - x₀) →
      (∀ m' ∈ Finset.Icc 1 (p / 2), m' ≠ m → A.valuation (x - x₀) ≠ A.valuation (xk m' - x₀)) →
      ¬ A.valuation (vX - x₀) < 1)
    (master_unit : A.valuation (x - x₀) = 1 → ¬ A.valuation (vX - x₀) < 1)
    (master_formal : x ∉ A → ¬ A.valuation (vX - x₀) < 1) :
    L ↔ ∃ k ∈ AddSubgroup.zmultiples Q, W.InZeroComponentAt A (Point.some x y h - k) := by

  have hne : ∀ m ∈ Finset.Icc 1 (p / 2), x ≠ xk m := fun m hm hx =>
    hL (mem_zmultiples_of_x_eq W (hkQ m hm) hx)
  have hcritW := W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad h
  by_cases hX : A.valuation (x - x₀) < 1
  ·
    constructor
    · intro hLt
      have hcoll : ∃ m ∈ Finset.Icc 1 (p / 2), A.valuation (x - x₀) = A.valuation (xk m - x₀) := by
        by_contra hno
        push Not at hno
        exact absurd hLt (hcrit.mpr (master_off hne hno hX))
      obtain ⟨m, hm, hlev⟩ := hcoll
      have hm' := Finset.mem_Icc.mp hm
      exact rhs_of_level_eq W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 hQord hout
        hm'.1 (lt_of_le_of_lt hm'.2 (Nat.div_lt_self hp.pos one_lt_two)) (hkQ m hm) h hlev
    · intro hrhs
      obtain ⟨m, xm, ym, hm, hm1, hmn, hmQ, hlev⟩ := level_eq_of_rhs W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀
        hFy hFx hnode hbad hp hp2 hQord hout h hX hrhs
      have hmI : m ∈ Finset.Icc 1 (p / 2) := Finset.mem_Icc.mpr ⟨hm1, hmn⟩

      have hxm : xm = xk m := by
        have := hmQ.symm.trans (hkQ m hmI)
        rw [some.injEq] at this
        exact this.1
      by_contra hLf
      rw [hxm] at hlev

      have hne' : ∀ m' ∈ Finset.Icc 1 (p / 2), m' ≠ m →
          A.valuation (x - x₀) ≠ A.valuation (xk m' - x₀) := by
        intro m' hm'I hm'ne hlev'
        have hmm := Finset.mem_Icc.mp hmI
        have hmm' := Finset.mem_Icc.mp hm'I
        exact hm'ne (kernel_level_injOn W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2
          hQord hout hmm'.1 hmm'.2 hmm.1 hmm.2 (hkQ m' hm'I) (hkQ m hmI) (hlev'.symm.trans hlev))
      exact master_on hne m hmI hlev hne' (hcrit.mp hLf)
  ·
    have hP : W.InZeroComponentAt A (Point.some x y h) := by
      by_contra hP; exact hX (hcritW.mp hP)
    have hLt : L := by
      by_contra hLf
      have hlt := hcrit.mp hLf
      by_cases hxA : x ∈ A
      · have hle : A.valuation (x - x₀) ≤ 1 := (A.valuation_le_one_iff _).mpr (sub_mem hxA hx₀)
        exact master_unit (le_antisymm hle (not_lt.mp hX)) hlt
      · exact master_formal hxA hlt
    exact ⟨fun _ => ⟨0, AddSubgroup.zero_mem _, by rw [sub_zero]; exact hP⟩, fun _ => hLt⟩

end NTEndgame

section AnchorSwap

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

private lemma val_sub_lt_one_congr (v : Valuation F Γ₀) {a x₀ z₀ : F}
    (hz : v (z₀ - x₀) < 1) : v (a - z₀) < 1 ↔ v (a - x₀) < 1 := by
  constructor
  · intro h
    have : a - x₀ = (a - z₀) + (z₀ - x₀) := by ring
    rw [this]; exact Valuation.map_add_lt v h hz
  · intro h
    have : a - z₀ = (a - x₀) - (z₀ - x₀) := by ring
    rw [this]; exact Valuation.map_sub_lt v h hz

end AnchorSwap

section NTSums

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb) (W' : WeierstrassCurve Kb)

private lemma val_veluT_le_level {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hb₂ : A.valuation W'.b₂ ≤ 1) (hx₀ : A.valuation x₀ ≤ 1)
    (xk yk : Kb) (hxk : A.valuation (xk - x₀) ≤ 1) :
    A.valuation (W'.veluT xk yk) ≤ A.valuation (xk - x₀) := by
  have hfac : W'.veluT xk yk = (xk - x₀) * ((W'.b₂ + 12 * x₀) + 6 * (xk - x₀)) := by
    rw [veluT_eq]
    simp only [b₂, b₄]
    linear_combination W'.a₁ * hFy - 2 * hFx
  have hn : ∀ n : ℕ, A.valuation ((n : Kb)) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have hβ : A.valuation ((W'.b₂ + 12 * x₀) + 6 * (xk - x₀)) ≤ 1 := by
    refine A.valuation.map_add_le (A.valuation.map_add_le hb₂ ?_) ?_
    · rw [map_mul]; exact mul_le_one' (by exact_mod_cast hn 12) hx₀
    · rw [map_mul]; exact mul_le_one' (by exact_mod_cast hn 6) hxk
  rw [hfac, map_mul]
  exact mul_le_of_le_one_right' hβ

private theorem val_sum_veluT_lt_one {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hb₂ : A.valuation W'.b₂ ≤ 1) (hx₀ : A.valuation x₀ ≤ 1)
    (s : Finset ℕ) (xk yk : ℕ → Kb) (hlam : ∀ k ∈ s, A.valuation (xk k - x₀) < 1) :
    A.valuation (∑ k ∈ s, W'.veluT (xk k) (yk k)) < 1 := by
  refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
  exact lt_of_le_of_lt (val_veluT_le_level A W' hFy hFx hb₂ hx₀ (xk k) (yk k) (hlam k hk).le)
    (hlam k hk)

private lemma veluU_node_expand {x₀ y₀ x y : Kb}
    (heq : W'.toAffine.Equation x y)
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄) :
    W'.veluU x y =
      -4 * (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆))
      + (W'.b₂ + 12 * x₀) * (x - x₀) ^ 2 + 4 * (x - x₀) ^ 3 := by
  rw [W'.veluU_eq_Ψ₂Sq_eval heq]
  simp only [Ψ₂Sq, b₂, b₄, b₆, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  linear_combination (-4 * x + 4 * x₀) * hFx + (2 * W'.a₁ * x - W'.a₁ * x₀ + 2 * y₀ + W'.a₃) * hFy

private theorem val_sum_veluW_lt_one {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hb₂ : A.valuation W'.b₂ ≤ 1) (hx₀ : A.valuation x₀ ≤ 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1)
    (s : Finset ℕ) (xk yk : ℕ → Kb) (heq : ∀ k ∈ s, W'.toAffine.Equation (xk k) (yk k))
    (hlam : ∀ k ∈ s, A.valuation (xk k - x₀) < 1) :
    A.valuation (∑ k ∈ s, W'.veluW (xk k) (yk k)) < 1 := by
  have hn : ∀ n : ℕ, A.valuation ((n : Kb)) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have hβ : A.valuation (W'.b₂ + 12 * x₀) ≤ 1 := by
    refine A.valuation.map_add_le hb₂ ?_
    rw [map_mul]; exact mul_le_one' (by exact_mod_cast hn 12) hx₀
  refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
  have hl := hlam k hk
  have hxk : A.valuation (xk k) ≤ 1 := by
    have : xk k = (xk k - x₀) + x₀ := by ring
    rw [this]; exact A.valuation.map_add_le hl.le hx₀
  have hU : A.valuation (W'.veluU (xk k) (yk k)) < 1 := by
    rw [veluU_node_expand W' (heq k hk) hFy hFx]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) ?_
    · rw [map_mul, Valuation.map_neg]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (by exact_mod_cast hn 4)) hε
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hβ) (pow_lt_one₀ zero_le' hl two_ne_zero)
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (by exact_mod_cast hn 4))
        (pow_lt_one₀ zero_le' hl three_ne_zero)
  have hT : A.valuation (xk k * W'.veluT (xk k) (yk k)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hxk)
      (lt_of_le_of_lt (val_veluT_le_level A W' hFy hFx hb₂ hx₀ (xk k) (yk k) hl.le) hl)
  unfold veluW
  exact Valuation.map_add_lt _ hU hT

end NTSums

section Masters

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)

private lemma b₂_dock :
    ((W.map (Int.castRingHom ℚ))⁄Kb).b₂ = ((W.b₂ : ℤ) : Kb) := by
  simp only [WeierstrassCurve.b₂, Affine.baseChange_a₁, Affine.baseChange_a₂,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, eq_intCast, map_intCast]
  push_cast
  ring

private lemma ε_dock (x₀ y₀ : Kb) :
    y₀ ^ 2 + ((W.map (Int.castRingHom ℚ))⁄Kb).a₁ * x₀ * y₀
        + ((W.map (Int.castRingHom ℚ))⁄Kb).a₃ * y₀
        - (x₀ ^ 3 + ((W.map (Int.castRingHom ℚ))⁄Kb).a₂ * x₀ ^ 2
            + ((W.map (Int.castRingHom ℚ))⁄Kb).a₄ * x₀ + ((W.map (Int.castRingHom ℚ))⁄Kb).a₆)
      = y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + (W.a₃ : Kb) * y₀
        - (x₀ ^ 3 + (W.a₂ : Kb) * x₀ ^ 2 + (W.a₄ : Kb) * x₀ + (W.a₆ : Kb)) := by
  simp only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
    Affine.baseChange_a₄, Affine.baseChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    eq_intCast, map_intCast]

private lemma hFy_dock {x₀ y₀ : Kb} (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0) :
    2 * y₀ + ((W.map (Int.castRingHom ℚ))⁄Kb).a₁ * x₀
      + ((W.map (Int.castRingHom ℚ))⁄Kb).a₃ = 0 := by
  simp only [Affine.baseChange_a₁, Affine.baseChange_a₃, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, eq_intCast, map_intCast]
  exact hFy

private lemma hFx_dock {x₀ y₀ : Kb}
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) :
    ((W.map (Int.castRingHom ℚ))⁄Kb).a₁ * y₀
      = 3 * x₀ ^ 2 + 2 * ((W.map (Int.castRingHom ℚ))⁄Kb).a₂ * x₀
        + ((W.map (Int.castRingHom ℚ))⁄Kb).a₄ := by
  simp only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₄,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
    eq_intCast, map_intCast]
  exact hFx

private theorem val_velusum_lt_one (s : Finset ℕ)
    {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    (hk : ∀ k ∈ s,
      ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xk k) (yk k))
    (hlam : ∀ k ∈ s, A.valuation (xk k - x₀) < 1)
    (hshk : ∀ k ∈ s,
      A.valuation (y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xk k - x₀) ^ 2)
    {x : Kb} (hX1 : A.valuation (x - x₀) ≤ 1)
    (hne : ∀ k ∈ s, A.valuation (x - x₀) ≠ A.valuation (xk k - x₀))
    (hxne : ∀ k ∈ s, x ≠ xk k) :
    A.valuation (∑ k ∈ s,
        (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
          + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2)) < 1 := by
  refine A.valuation.map_sum_lt one_ne_zero fun k hkm => ?_
  have hd : x - xk k ≠ 0 := sub_ne_zero.mpr (hxne k hkm)
  have hEq : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation (xk k) (yk k) := (hk k hkm).1
  have hN := veluT_mul_add_veluU ((W.map (Int.castRingHom ℚ))⁄Kb)
    (hFy_dock W hFy) (hFx_dock W hFx) hEq x
  have hsplit : ((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
      + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2
      = (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) * (x - xk k)
          + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k)) / (x - xk k) ^ 2 := by
    field_simp
  have hdd : x - xk k = (x - x₀) - (xk k - x₀) := by ring
  rw [hsplit, hN, b₂_dock, ε_dock, hdd]
  have h6 : A.valuation (6 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 6)
  have h2 : A.valuation (2 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 2)
  have h4 : A.valuation (4 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 4)
  have hsh4 : A.valuation (4 * (y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) < A.valuation (xk k - x₀) ^ 2 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h4) (hshk k hkm)
  exact val_summand_lt_one A.valuation hnode h6 h2 hX1 (hlam k hkm) (hne k hkm) hsh4

private lemma b₄_dock :
    ((W.map (Int.castRingHom ℚ))⁄Kb).b₄ = ((W.b₄ : ℤ) : Kb) := by
  simp only [WeierstrassCurve.b₄, Affine.baseChange_a₁, Affine.baseChange_a₃,
    Affine.baseChange_a₄, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, eq_intCast, map_intCast]
  push_cast
  ring

private lemma val_veluT_le_one {xc : Kb} (hxc : A.valuation xc ≤ 1) (yc : Kb) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluT xc yc) ≤ 1 := by
  have hcast : ∀ m : ℤ, A.valuation ((m : Kb)) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  rw [veluT_eq, b₂_dock, b₄_dock]
  refine A.valuation.map_add_le (A.valuation.map_add_le ?_ ?_) (hcast _)
  · rw [map_mul, map_pow]
    exact mul_le_one' (by exact_mod_cast hcast 6) (pow_le_one' hxc 2)
  · rw [map_mul]
    exact mul_le_one' (hcast _) hxc

private lemma val_veluU_le_one {xc yc : Kb} (hxc : A.valuation xc ≤ 1)
    (hyc : A.valuation yc ≤ 1) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluU xc yc) ≤ 1 := by
  have hcast : ∀ m : ℤ, A.valuation ((m : Kb)) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  simp only [veluU, veluGy, Affine.baseChange_a₁, Affine.baseChange_a₃,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, eq_intCast, map_intCast]
  rw [map_pow]
  refine pow_le_one' ?_ 2
  rw [Valuation.map_neg]
  refine A.valuation.map_add_le (A.valuation.map_add_le ?_ ?_) (hcast _)
  · rw [map_mul]
    exact mul_le_one' (by exact_mod_cast hcast 2) hyc
  · rw [map_mul]
    exact mul_le_one' (hcast _) hxc

private theorem val_velusum_collision {n : ℕ} {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    (hk : ∀ k ∈ Finset.Icc 1 n,
      ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xk k) (yk k))
    (hlam : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) < 1)
    (hshk : ∀ k ∈ Finset.Icc 1 n,
      A.valuation (y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xk k - x₀) ^ 2)
    {x : Kb} {K : ℕ} (hKmem : K ∈ Finset.Icc 1 n)
    (heqK : A.valuation (x - x₀) = A.valuation (xk K - x₀))
    (hne' : ∀ k ∈ Finset.Icc 1 n, k ≠ K →
      A.valuation (x - x₀) ≠ A.valuation (xk k - x₀))
    (hxne : ∀ k ∈ Finset.Icc 1 n, x ≠ xk k) :
    1 ≤ A.valuation ((x + ∑ k ∈ Finset.Icc 1 n,
        (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
          + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2)) - x₀) := by
  have h6 : A.valuation (6 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 6)
  have h2 : A.valuation (2 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 2)
  have h4 : A.valuation (4 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 4)
  have hX : A.valuation (x - x₀) < 1 := by rw [heqK]; exact hlam K hKmem
  have hlam0 : A.valuation (xk K - x₀) ≠ 0 := by
    intro h0
    have h' := hshk K hKmem
    rw [h0, zero_pow two_ne_zero] at h'
    exact not_lt_zero h'
  have hX0 : A.valuation (x - x₀) ≠ 0 := by rw [heqK]; exact hlam0
  rw [← Finset.add_sum_erase _ _ hKmem]
  have hgroup : x + ((((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk K) (yk K) / (x - xk K)
        + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk K) (yk K) / (x - xk K) ^ 2)
      + ∑ k ∈ (Finset.Icc 1 n).erase K,
          (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
            + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2)) - x₀
      = (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk K) (yk K) / (x - xk K)
          + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk K) (yk K) / (x - xk K) ^ 2)
        + ((x - x₀) + ∑ k ∈ (Finset.Icc 1 n).erase K,
            (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
              + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2)) := by
    ring
  rw [hgroup]
  have hrest : A.valuation ((x - x₀) + ∑ k ∈ (Finset.Icc 1 n).erase K,
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
        + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2)) < 1 := by
    refine Valuation.map_add_lt _ hX ?_
    exact val_velusum_lt_one W A ((Finset.Icc 1 n).erase K) hFy hFx hnode
      (fun k hk' => hk k (Finset.mem_of_mem_erase hk'))
      (fun k hk' => hlam k (Finset.mem_of_mem_erase hk'))
      (fun k hk' => hshk k (Finset.mem_of_mem_erase hk'))
      hX.le
      (fun k hk' => hne' k (Finset.mem_of_mem_erase hk') (Finset.ne_of_mem_erase hk'))
      (fun k hk' => hxne k (Finset.mem_of_mem_erase hk'))
  have hdK : x - xk K ≠ 0 := sub_ne_zero.mpr (hxne K hKmem)
  have hEqK : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation (xk K) (yk K) :=
    (hk K hKmem).1
  have hNK := veluT_mul_add_veluU ((W.map (Int.castRingHom ℚ))⁄Kb)
    (hFy_dock W hFy) (hFx_dock W hFx) hEqK x
  have hsplitK : ((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk K) (yk K) / (x - xk K)
      + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk K) (yk K) / (x - xk K) ^ 2
      = (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk K) (yk K) * (x - xk K)
          + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk K) (yk K)) / (x - xk K) ^ 2 := by
    field_simp
  have hsh4K : A.valuation (4 * (y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) < A.valuation (x - x₀) ^ 2 := by
    rw [map_mul, heqK]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h4) (hshk K hKmem)
  have h1K : 1 ≤ A.valuation
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk K) (yk K) / (x - xk K)
        + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk K) (yk K) / (x - xk K) ^ 2) := by
    rw [hsplitK, hNK, b₂_dock, ε_dock,
      (show x - xk K = (x - x₀) - (xk K - x₀) by ring)]
    have hvN := val_numer_collision A.valuation hnode h6 h2 hX hX0 heqK.symm hsh4K
    have hD0 : A.valuation ((x - x₀) - (xk K - x₀)) ≠ 0 := by
      rw [show (x - x₀) - (xk K - x₀) = x - xk K by ring]
      intro h0
      exact hdK (A.valuation.zero_iff.mp h0)
    have hDle : A.valuation ((x - x₀) - (xk K - x₀)) ≤ A.valuation (x - x₀) :=
      A.valuation.map_sub_le le_rfl heqK.ge
    rw [map_div₀, map_pow, hvN]
    rw [one_le_div₀ (zero_lt_iff.mpr (pow_ne_zero 2 hD0))]
    exact pow_le_pow_left₀ zero_le' hDle 2
  rw [Valuation.map_add_eq_of_lt_left _ (lt_of_lt_of_le hrest h1K)]
  exact h1K

private theorem val_veluX_formal (s : Finset ℕ) {xk yk : ℕ → Kb}
    (hxk : ∀ k ∈ s, A.valuation (xk k) ≤ 1) (hyk : ∀ k ∈ s, A.valuation (yk k) ≤ 1)
    {x : Kb} (hX : 1 < A.valuation x) :
    A.valuation (x + ∑ k ∈ s,
        (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
          + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2))
      = A.valuation x := by
  have hxpos : (0 : _) < A.valuation x := lt_trans zero_lt_one hX
  have hsum : A.valuation (∑ k ∈ s,
      (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)
        + ((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2)) < 1 := by
    refine A.valuation.map_sum_lt one_ne_zero fun k hkm => ?_
    have hden : A.valuation (x - xk k) = A.valuation x :=
      Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt (hxk k hkm) hX)
    have ht : A.valuation
        (((W.map (Int.castRingHom ℚ))⁄Kb).veluT (xk k) (yk k) / (x - xk k)) < 1 := by
      rw [map_div₀, hden, div_lt_one₀ hxpos]
      exact lt_of_le_of_lt (val_veluT_le_one W A (hxk k hkm) (yk k)) hX
    have hu : A.valuation
        (((W.map (Int.castRingHom ℚ))⁄Kb).veluU (xk k) (yk k) / (x - xk k) ^ 2) < 1 := by
      rw [map_div₀, map_pow, hden,
        div_lt_one₀ (zero_lt_iff.mpr (pow_ne_zero 2 (zero_lt_iff.mp hxpos)))]
      exact lt_of_le_of_lt (val_veluU_le_one W A (hxk k hkm) (hyk k hkm))
        (one_lt_pow' hX two_ne_zero)
    exact Valuation.map_add_lt _ ht hu
  exact Valuation.map_add_eq_of_lt_left _ (lt_trans hsum hX)

end Masters

section MasterWraps

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)

private theorem master_off_wrap {p n : ℕ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Point}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    {hk : ∀ k ∈ Finset.Icc 1 n,
      ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 n), k • Q = .some (xk k) (yk k) (hk k hk'))
    (hlam : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) < 1)
    (hshk : ∀ k ∈ Finset.Icc 1 n,
      A.valuation (y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xk k - x₀) ^ 2)
    {x : Kb} (hxne : ∀ m ∈ Finset.Icc 1 n, x ≠ xk m)
    (hne : ∀ m ∈ Finset.Icc 1 n, A.valuation (x - x₀) ≠ A.valuation (xk m - x₀))
    (hX : A.valuation (x - x₀) < 1) :
    A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluX
        (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q n) x - x₀) < 1 := by
  have hre : ∀ a b c : Kb, a + b - c = a - c + b := fun a b c => by ring
  rw [veluX_eq_sum_Icc _ hord hn hkQ, hre]
  exact Valuation.map_add_lt _ hX
    (val_velusum_lt_one W A (Finset.Icc 1 n) hFy hFx hnode hk hlam hshk hX.le hne hxne)

private theorem master_on_wrap {p n : ℕ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Point}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    {hk : ∀ k ∈ Finset.Icc 1 n,
      ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 n), k • Q = .some (xk k) (yk k) (hk k hk'))
    (hlam : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) < 1)
    (hshk : ∀ k ∈ Finset.Icc 1 n,
      A.valuation (y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xk k - x₀) ^ 2)
    {x : Kb} (hxne : ∀ m ∈ Finset.Icc 1 n, x ≠ xk m)
    {K : ℕ} (hKmem : K ∈ Finset.Icc 1 n)
    (heqK : A.valuation (x - x₀) = A.valuation (xk K - x₀))
    (hne' : ∀ m ∈ Finset.Icc 1 n, m ≠ K →
      A.valuation (x - x₀) ≠ A.valuation (xk m - x₀)) :
    ¬ A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluX
        (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q n) x - x₀) < 1 := by
  rw [veluX_eq_sum_Icc _ hord hn hkQ]
  exact not_lt.mpr
    (val_velusum_collision W A hFy hFx hnode hk hlam hshk hKmem heqK hne' hxne)

private theorem master_unit_wrap {p n : ℕ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Point}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    {hk : ∀ k ∈ Finset.Icc 1 n,
      ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 n), k • Q = .some (xk k) (yk k) (hk k hk'))
    (hlam : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) < 1)
    (hshk : ∀ k ∈ Finset.Icc 1 n,
      A.valuation (y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xk k - x₀) ^ 2)
    {x : Kb} (hunit : A.valuation (x - x₀) = 1) :
    ¬ A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluX
        (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q n) x - x₀) < 1 := by
  have hxne : ∀ m ∈ Finset.Icc 1 n, x ≠ xk m := by
    intro m hm hxeq
    rw [hxeq] at hunit
    exact absurd (hunit ▸ hlam m hm) (lt_irrefl 1)
  have hne : ∀ m ∈ Finset.Icc 1 n, A.valuation (x - x₀) ≠ A.valuation (xk m - x₀) := by
    intro m hm
    rw [hunit]
    exact (hlam m hm).ne'
  have hre : ∀ a b c : Kb, a + b - c = a - c + b := fun a b c => by ring
  rw [veluX_eq_sum_Icc _ hord hn hkQ, hre]
  have hsum := val_velusum_lt_one W A (Finset.Icc 1 n) hFy hFx hnode hk hlam hshk
    hunit.le hne hxne
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hunit]; exact hsum), hunit]
  exact lt_irrefl 1

private theorem master_formal_wrap {p n : ℕ}
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Point}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) {x₀ : Kb} (hx₀ : x₀ ∈ A)
    {xk yk : ℕ → Kb}
    {hk : ∀ k ∈ Finset.Icc 1 n,
      ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 n), k • Q = .some (xk k) (yk k) (hk k hk'))
    (hlam : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k - x₀) < 1)
    {x : Kb} (hxA : x ∉ A) :
    ¬ A.valuation (((W.map (Int.castRingHom ℚ))⁄Kb).veluX
        (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q n) x - x₀) < 1 := by
  have hx₀v : A.valuation x₀ ≤ 1 := (A.valuation_le_one_iff _).mpr hx₀
  have hX : 1 < A.valuation x := not_le.mp (fun h => hxA ((A.valuation_le_one_iff _).mp h))
  have hxkI : ∀ k ∈ Finset.Icc 1 n, A.valuation (xk k) ≤ 1 := by
    intro k hm
    have : xk k = (xk k - x₀) + x₀ := by ring
    rw [this]
    exact A.valuation.map_add_le (hlam k hm).le hx₀v
  have hykI : ∀ k ∈ Finset.Icc 1 n, A.valuation (yk k) ≤ 1 := fun k hm =>
    val_y_le_one W A (hk k hm).1 (hxkI k hm)
  rw [veluX_eq_sum_Icc _ hord hn hkQ]
  have hval := val_veluX_formal W A (Finset.Icc 1 n) hxkI hykI hX
  have h1 := lt_of_lt_of_eq hX hval.symm
  rw [Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt hx₀v h1), hval]
  exact not_lt.mpr hX.le

end MasterWraps

section Anchor

local notation "Kb" => AlgebraicClosure ℚ

private theorem anchor_identity {F : Type*} [Field F] (W : WeierstrassCurve F)
    (S : Finset (F × F)) {x₀ y₀ z₀ Z₀ : F}
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hFyV : 2 * Z₀ + (W.veluQuotient S).a₁ * z₀ + (W.veluQuotient S).a₃ = 0)
    (hFxV : (W.veluQuotient S).a₁ * Z₀
      = 3 * z₀ ^ 2 + 2 * (W.veluQuotient S).a₂ * z₀ + (W.veluQuotient S).a₄) :
    (W.veluQuotient S).c₄ * (z₀ - x₀)
      = -((240 * x₀ + 62 * W.b₂) * W.veluTSum S) - 504 * W.veluWSum S
        + 72 * ((Z₀ ^ 2 + (W.veluQuotient S).a₁ * z₀ * Z₀ + (W.veluQuotient S).a₃ * Z₀
              - (z₀ ^ 3 + (W.veluQuotient S).a₂ * z₀ ^ 2 + (W.veluQuotient S).a₄ * z₀
                  + (W.veluQuotient S).a₆))
            - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
              - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) := by
  have h1 := centre_c₄_mul_eq W hFy hFx
  have h2 := centre_c₄_mul_eq (W.veluQuotient S) hFyV hFxV
  simp only [c₄, b₂, b₄, b₆, veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃,
    veluQuotient_a₄, veluQuotient_a₆] at h1 h2 ⊢
  linear_combination h2 - h1

private theorem anchor_val_lt_one (A : ValuationSubring Kb) (W' : WeierstrassCurve Kb)
    (S : Finset (Kb × Kb)) {x₀ y₀ z₀ Z₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hFyV : 2 * Z₀ + (W'.veluQuotient S).a₁ * z₀ + (W'.veluQuotient S).a₃ = 0)
    (hFxV : (W'.veluQuotient S).a₁ * Z₀
      = 3 * z₀ ^ 2 + 2 * (W'.veluQuotient S).a₂ * z₀ + (W'.veluQuotient S).a₄)
    (hc₄V : A.valuation (W'.veluQuotient S).c₄ = 1)
    (hx₀ : A.valuation x₀ ≤ 1) (hb₂ : A.valuation W'.b₂ ≤ 1)
    (ht : A.valuation (W'.veluTSum S) < 1) (hw : A.valuation (W'.veluWSum S) < 1)
    (hεV : A.valuation (Z₀ ^ 2 + (W'.veluQuotient S).a₁ * z₀ * Z₀
        + (W'.veluQuotient S).a₃ * Z₀
        - (z₀ ^ 3 + (W'.veluQuotient S).a₂ * z₀ ^ 2 + (W'.veluQuotient S).a₄ * z₀
            + (W'.veluQuotient S).a₆)) < 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1) :
    A.valuation (z₀ - x₀) < 1 := by
  have hid := anchor_identity W' S hFy hFx hFyV hFxV
  have hcast : ∀ m : ℤ, A.valuation ((m : Kb)) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have h240 : A.valuation (240 * x₀ + 62 * W'.b₂) ≤ 1 := by
    refine A.valuation.map_add_le ?_ ?_
    · rw [map_mul]
      exact mul_le_one' (by exact_mod_cast hcast 240) hx₀
    · rw [map_mul]
      exact mul_le_one' (by exact_mod_cast hcast 62) hb₂
  have hterm1 : A.valuation (-((240 * x₀ + 62 * W'.b₂) * W'.veluTSum S)) < 1 := by
    rw [Valuation.map_neg, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h240) ht
  have hterm2 : A.valuation (504 * W'.veluWSum S) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (by exact_mod_cast hcast 504)) hw
  have hterm3 : A.valuation (72 * ((Z₀ ^ 2 + (W'.veluQuotient S).a₁ * z₀ * Z₀
      + (W'.veluQuotient S).a₃ * Z₀
      - (z₀ ^ 3 + (W'.veluQuotient S).a₂ * z₀ ^ 2 + (W'.veluQuotient S).a₄ * z₀
          + (W'.veluQuotient S).a₆))
      - (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
          - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)))) < 1 := by
    rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (by exact_mod_cast hcast 72)) ?_
    exact Valuation.map_sub_lt _ hεV hε
  calc A.valuation (z₀ - x₀)
      = A.valuation ((W'.veluQuotient S).c₄ * (z₀ - x₀)) := by
        rw [map_mul, hc₄V, one_mul]
    _ < 1 := by
        rw [hid]
        exact Valuation.map_add_lt _ (Valuation.map_sub_lt _ hterm1 hterm2) hterm3

end Anchor

section TRed

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private noncomputable def red (a : Kb) : IsLocalRing.ResidueField A := by
  classical
  exact if ha : a ∈ A then IsLocalRing.residue A ⟨a, ha⟩ else 0

private lemma red_of_mem {a : Kb} (ha : a ∈ A) : red A a = IsLocalRing.residue A ⟨a, ha⟩ := by
  unfold red
  rw [dif_pos ha]

private lemma red_zero : red A 0 = 0 := by
  rw [red_of_mem A A.zero_mem]; exact map_zero (IsLocalRing.residue A)

private lemma red_one : red A 1 = 1 := by
  rw [red_of_mem A A.one_mem]; exact map_one (IsLocalRing.residue A)

private lemma red_add {a b : Kb} (ha : a ∈ A) (hb : b ∈ A) :
    red A (a + b) = red A a + red A b := by
  rw [red_of_mem A (add_mem ha hb), red_of_mem A ha, red_of_mem A hb]
  exact map_add (IsLocalRing.residue A) ⟨a, ha⟩ ⟨b, hb⟩

private lemma red_sub {a b : Kb} (ha : a ∈ A) (hb : b ∈ A) :
    red A (a - b) = red A a - red A b := by
  rw [red_of_mem A (sub_mem ha hb), red_of_mem A ha, red_of_mem A hb]
  exact map_sub (IsLocalRing.residue A) ⟨a, ha⟩ ⟨b, hb⟩

private lemma red_neg {a : Kb} (ha : a ∈ A) : red A (-a) = -red A a := by
  rw [red_of_mem A (neg_mem ha), red_of_mem A ha]
  exact map_neg (IsLocalRing.residue A) ⟨a, ha⟩

private lemma red_mul {a b : Kb} (ha : a ∈ A) (hb : b ∈ A) :
    red A (a * b) = red A a * red A b := by
  rw [red_of_mem A (mul_mem ha hb), red_of_mem A ha, red_of_mem A hb]
  exact map_mul (IsLocalRing.residue A) ⟨a, ha⟩ ⟨b, hb⟩

private lemma red_pow {a : Kb} (ha : a ∈ A) (n : ℕ) : red A (a ^ n) = red A a ^ n := by
  rw [red_of_mem A (pow_mem ha n), red_of_mem A ha]
  exact map_pow (IsLocalRing.residue A) ⟨a, ha⟩ n

private lemma red_natCast (n : ℕ) : red A (n : Kb) = n := by
  rw [red_of_mem A (natCast_mem A n)]
  exact map_natCast (IsLocalRing.residue A) n

private lemma red_ofNat (n : ℕ) [n.AtLeastTwo] :
    red A (OfNat.ofNat n : Kb) = (OfNat.ofNat n : IsLocalRing.ResidueField A) :=
  red_natCast A n

private lemma mem_of_val_eq_one {b : Kb} (hb : A.valuation b = 1) : b ∈ A :=
  (A.valuation_le_one_iff b).mp hb.le

private lemma inv_mem_of_val_eq_one {b : Kb} (hb : A.valuation b = 1) : b⁻¹ ∈ A :=
  (A.valuation_le_one_iff b⁻¹).mp (by rw [map_inv₀, hb, inv_one])

private lemma div_mem_of_val_eq_one {a b : Kb} (ha : a ∈ A) (hb : A.valuation b = 1) :
    a / b ∈ A := by
  rw [div_eq_mul_inv]; exact mul_mem ha (inv_mem_of_val_eq_one A hb)

private lemma red_eq_zero_iff {a : Kb} (ha : a ∈ A) : red A a = 0 ↔ A.valuation a < 1 := by
  rw [red_of_mem A ha, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff ⟨a, ha⟩

private lemma red_ne_zero_iff {a : Kb} (ha : a ∈ A) : red A a ≠ 0 ↔ A.valuation a = 1 := by
  rw [Ne, red_eq_zero_iff A ha, not_lt]
  have hle : A.valuation a ≤ 1 := (A.valuation_le_one_iff a).mpr ha
  exact ⟨fun h => le_antisymm hle h, fun h => h.ge⟩

private lemma red_eq_red_iff {a b : Kb} (ha : a ∈ A) (hb : b ∈ A) :
    red A a = red A b ↔ A.valuation (a - b) < 1 := by
  rw [← sub_eq_zero, ← red_sub A ha hb, red_eq_zero_iff A (sub_mem ha hb)]

private lemma red_inv {b : Kb} (hb : A.valuation b = 1) : red A b⁻¹ = (red A b)⁻¹ := by
  have hbA := mem_of_val_eq_one A hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hb
    exact zero_ne_one hb
  have hmul : red A b⁻¹ * red A b = 1 := by
    rw [← red_mul A (inv_mem_of_val_eq_one A hb) hbA, inv_mul_cancel₀ hb0, red_one]
  exact eq_inv_of_mul_eq_one_left hmul

private lemma red_div {a b : Kb} (ha : a ∈ A) (hb : A.valuation b = 1) :
    red A (a / b) = red A a / red A b := by
  rw [div_eq_mul_inv, red_mul A ha (inv_mem_of_val_eq_one A hb), red_inv A hb, div_eq_mul_inv]

private lemma red_sum {ι : Type*} (s : Finset ι) (f : ι → Kb) (hf : ∀ i ∈ s, f i ∈ A) :
    red A (∑ i ∈ s, f i) = ∑ i ∈ s, red A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [red_zero]
  | insert i s hi ih =>
    have hfi : f i ∈ A := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ∈ A := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      red_add A hfi (sum_mem fun j hj => hfs j hj), ih hfs]

private lemma red_prod {ι : Type*} (s : Finset ι) (f : ι → Kb) (hf : ∀ i ∈ s, f i ∈ A) :
    red A (∏ i ∈ s, f i) = ∏ i ∈ s, red A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [red_one]
  | insert i s hi ih =>
    have hfi : f i ∈ A := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ∈ A := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      red_mul A hfi (prod_mem fun j hj => hfs j hj), ih hfs]

end TRed

section TKernel

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)

private lemma residue_nonsingular_of_mem {x y : Kb}
    {h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y} (hx : x ∈ A) (hy : y ∈ A)
    (hmem : W.InZeroComponentAt A (.some x y h)) :
    (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
      (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) := by
  rcases hmem with h0 | ⟨x', y', h', heq, hcase⟩
  · exact absurd h0 (some_ne_zero h)
  · obtain ⟨hx', hy'⟩ : x = x' ∧ y = y' := by
      rw [Point.some.injEq] at heq
      exact ⟨heq.1, heq.2⟩
    subst hx'; subst hy'
    rcases hcase with hnx | ⟨hx'', hy'', hns⟩
    · exact absurd hx hnx
    · exact hns

private theorem toric_kernel_integral {p : ℕ} (hp : p.Prime)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    (hQc : W.InZeroComponentAt A Q)
    {xQ yQ : Kb} {hQ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xQ yQ}
    (hQeq : Q = .some xQ yQ hQ) (hxQ : xQ ∈ A)
    {m : ℕ} (hm1 : 1 ≤ m) (hmp : m < p)
    {xm ym : Kb} {hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym}
    (hmQ : m • Q = .some xm ym hm) : xm ∈ A := by
  classical
  obtain ⟨red', hred0, hredadd, hredint, hredinf, -, -⟩ := W.exists_reduction_inZeroComponentAt A
  by_contra hxm
  have hrednsmul : ∀ n : ℕ, red' (n • Q) = n • red' Q := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, zero_nsmul, hred0]
    | succ n ih => rw [succ_nsmul, hredadd _ _ (nsmulMem W A n hQc) hQc, ih, succ_nsmul]
  have hyQ : yQ ∈ A :=
    (A.valuation_le_one_iff _).mp (val_y_le_one W A hQ.left ((A.valuation_le_one_iff _).mpr hxQ))
  have hQc' : W.InZeroComponentAt A (.some xQ yQ hQ) := by rw [hQeq] at hQc; exact hQc
  have hns := residue_nonsingular_of_mem W A hxQ hyQ hQc'
  have hredQ : red' Q = .some _ _ hns := by rw [hQeq]; exact hredint xQ yQ hQ hxQ hyQ hns
  have hredm : red' (m • Q) = 0 := by rw [hmQ]; exact hredinf xm ym hm hxm
  have hpQ : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  have hpred : p • red' Q = 0 := by rw [← hrednsmul, hpQ, hred0]
  have hmred : m • red' Q = 0 := by rw [← hrednsmul]; exact hredm
  have hne : red' Q ≠ 0 := by rw [hredQ]; exact some_ne_zero hns
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : addOrderOf (red' Q) = p := addOrderOf_eq_prime hpred hne
  have hdvd : p ∣ m := hord ▸ addOrderOf_dvd_of_nsmul_eq_zero hmred
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

private theorem toric_kernel_unit {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQc : W.InZeroComponentAt A Q)
    (m : ℕ) {xm ym : Kb} {hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym}
    (hmQ : m • Q = .some xm ym hm) (hxm : xm ∈ A) :
    A.valuation (xm - x₀) = 1 ∧ ym ∈ A := by
  have hmem : W.InZeroComponentAt A (.some xm ym hm) := by
    have h' := nsmulMem W A m hQc
    rw [hmQ] at h'
    exact h'
  have hnot : ¬ A.valuation (xm - x₀) < 1 := fun hlt =>
    ((W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad hm).mpr
      hlt) hmem
  have hle : A.valuation (xm - x₀) ≤ 1 := (A.valuation_le_one_iff _).mpr (sub_mem hxm hx₀)
  exact ⟨le_antisymm hle (not_lt.mp hnot),
    (A.valuation_le_one_iff _).mp (val_y_le_one W A hm.left ((A.valuation_le_one_iff _).mpr hxm))⟩

private lemma hkQ_half_of_full {p : ℕ} (hp : p.Prime)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point}
    {xk yk : ℕ → Kb}
    {hk : ∀ k ∈ Finset.Icc 1 (p - 1), ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular
      (xk k) (yk k)}
    (hkQ : ∀ k (hk' : k ∈ Finset.Icc 1 (p - 1)), k • Q = .some (xk k) (yk k) (hk k hk')) :
    ∃ hk' : ∀ k ∈ Finset.Icc 1 (p / 2), ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular
        (xk k) (yk k),
      ∀ k (hm : k ∈ Finset.Icc 1 (p / 2)), k • Q = .some (xk k) (yk k) (hk' k hm) := by
  have hsub : ∀ k ∈ Finset.Icc 1 (p / 2), k ∈ Finset.Icc 1 (p - 1) := by
    intro k hk'
    rw [Finset.mem_Icc] at hk' ⊢
    have := Nat.div_lt_self hp.pos one_lt_two
    omega
  exact ⟨fun k hm => hk k (hsub k hm), fun k hm => hkQ k (hsub k hm)⟩

end TKernel

section TTorus

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring Kb)

private lemma equation_cast {x y : Kb}
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y) :
    y ^ 2 + (W.a₁ : Kb) * x * y + (W.a₃ : Kb) * y
      = x ^ 3 + (W.a₂ : Kb) * x ^ 2 + (W.a₄ : Kb) * x + (W.a₆ : Kb) := by
  rw [Affine.equation_iff] at h
  simpa only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
    Affine.baseChange_a₄, Affine.baseChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    eq_intCast, map_intCast] using h

private lemma eq_negY_of_psi_eq_zero {x y : Kb} (hΨ : 2 * y + (W.a₁ : Kb) * x + W.a₃ = 0) :
    y = ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x y := by
  simp only [Affine.negY, Affine.baseChange_a₁, Affine.baseChange_a₃, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, eq_intCast, map_intCast]
  linear_combination hΨ

private lemma psi_sq_expand {x₀ y₀ x y : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Equation x y) :
    (2 * y + (W.a₁ : Kb) * x + W.a₃) ^ 2 =
      -4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        + ((W.b₂ : Kb) + 12 * x₀) * (x - x₀) ^ 2 + 4 * (x - x₀) ^ 3 := by
  have heq := equation_cast W h
  have hb₂ : ((W.b₂ : ℤ) : Kb) = (W.a₁ : Kb) ^ 2 + 4 * W.a₂ := by
    push_cast [WeierstrassCurve.b₂]; ring
  rw [hb₂]
  linear_combination 4 * heq + (-4 * x + 4 * x₀) * hFx
    + (2 * (W.a₁ : Kb) * x - W.a₁ * x₀ + 2 * y₀ + W.a₃) * hFy

private lemma eps_mem {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A) :
    y₀ ^ 2 + (W.a₁ : Kb) * x₀ * y₀ + (W.a₃ : Kb) * y₀
      - (x₀ ^ 3 + (W.a₂ : Kb) * x₀ ^ 2 + (W.a₄ : Kb) * x₀ + (W.a₆ : Kb)) ∈ A :=
  sub_mem (add_mem (add_mem (pow_mem hy₀ 2) (mul_mem (mul_mem (intCast_mem A _) hx₀) hy₀))
      (mul_mem (intCast_mem A _) hy₀))
    (add_mem (add_mem (add_mem (pow_mem hx₀ 3) (mul_mem (intCast_mem A _) (pow_mem hx₀ 2)))
      (mul_mem (intCast_mem A _) hx₀)) (intCast_mem A _))

private lemma beta_mem {x₀ : Kb} (hx₀ : x₀ ∈ A) : (W.b₂ : Kb) + 12 * x₀ ∈ A :=
  add_mem (intCast_mem A _) (mul_mem (ofNat_mem A 12) hx₀)

private theorem red_doubling {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ : Kb}
    {h₁ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₁ y₁}
    {h₂ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₂ y₂}
    (hsum : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂)
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hX₁ : A.valuation (x₁ - x₀) = 1) :
    red A (x₂ - x₀) * (red A ((W.b₂ : Kb) + 12 * x₀) + 4 * red A (x₁ - x₀))
      = red A (x₁ - x₀) ^ 2 := by
  have hΨ : 2 * y₁ + (W.a₁ : Kb) * x₁ + W.a₃ ≠ 0 := by
    intro hΨ0
    have h0 : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ = 0 :=
      add_of_Y_eq rfl (eq_negY_of_psi_eq_zero W hΨ0)
    rw [h0] at hsum
    exact some_ne_zero h₂ hsum.symm
  have hy : y₁ ≠ ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x₁ y₁ := by
    intro hy
    apply hΨ
    simp only [Affine.negY, Affine.baseChange_a₁, Affine.baseChange_a₃, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃, eq_intCast, map_intCast] at hy
    linear_combination hy
  have hx₂eq : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.addX x₁ x₁
      (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.slope x₁ x₁ y₁ y₁) = x₂ := by
    have e := (add_self_of_Y_ne (h₁ := h₁) hy).symm.trans hsum
    rw [Point.some.injEq] at e
    exact e.1
  have hrow := W.addX_self_sub_mul_sq_of_criticalCentre hFy hFx h₁ hΨ
  rw [hx₂eq] at hrow
  have hΨsq := psi_sq_expand W hFy hFx h₁.left

  have herr : (x₂ - x₀) * (((W.b₂ : Kb) + 12 * x₀) + 4 * (x₁ - x₀)) * (x₁ - x₀) ^ 2
      - (x₁ - x₀) ^ 4
      = (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        * (8 * (x₁ - x₀) + ((W.b₂ : Kb) + 12 * x₀) + 4 * (x₂ - x₀)) := by
    linear_combination hrow - (x₂ - x₀) * hΨsq

  have hβA : (W.b₂ : Kb) + 12 * x₀ ∈ A := beta_mem W A hx₀
  have hX₁A : x₁ - x₀ ∈ A := sub_mem hx₁ hx₀
  have hX₂A : x₂ - x₀ ∈ A := sub_mem hx₂ hx₀
  have h4X₁A : 4 * (x₁ - x₀) ∈ A := mul_mem (ofNat_mem A 4) hX₁A
  have hβ4A : ((W.b₂ : Kb) + 12 * x₀) + 4 * (x₁ - x₀) ∈ A := add_mem hβA h4X₁A
  have h12A : (x₂ - x₀) * (((W.b₂ : Kb) + 12 * x₀) + 4 * (x₁ - x₀)) ∈ A := mul_mem hX₂A hβ4A
  have hlhsA : (x₂ - x₀) * (((W.b₂ : Kb) + 12 * x₀) + 4 * (x₁ - x₀)) * (x₁ - x₀) ^ 2 ∈ A :=
    mul_mem h12A (pow_mem hX₁A 2)
  have hrhsA : (x₁ - x₀) ^ 4 ∈ A := pow_mem hX₁A 4
  have hval : A.valuation ((x₂ - x₀) * (((W.b₂ : Kb) + 12 * x₀) + 4 * (x₁ - x₀)) * (x₁ - x₀) ^ 2
      - (x₁ - x₀) ^ 4) < 1 := by
    rw [herr, map_mul]
    have hle : A.valuation (8 * (x₁ - x₀) + ((W.b₂ : Kb) + 12 * x₀) + 4 * (x₂ - x₀)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr
        (add_mem (add_mem (mul_mem (ofNat_mem A 8) hX₁A) hβA) (mul_mem (ofNat_mem A 4) hX₂A))
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hle) hbad
  have hred := (red_eq_red_iff A hlhsA hrhsA).mpr hval
  rw [red_mul A h12A (pow_mem hX₁A 2), red_mul A hX₂A hβ4A, red_add A hβA h4X₁A,
    red_mul A (ofNat_mem A 4) hX₁A, red_ofNat, red_pow A hX₁A, red_pow A hX₁A] at hred
  have hX₁0 : red A (x₁ - x₀) ≠ 0 := (red_ne_zero_iff A hX₁A).mpr hX₁
  exact mul_right_cancel₀ (pow_ne_zero 2 hX₁0) (hred.trans (by ring))

private theorem red_two_point {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : Kb}
    {h₁ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₁ y₁}
    {h₂ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₂ y₂}
    {h₃ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₃ y₃}
    {h₄ : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x₄ y₄}
    (hadd : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃)
    (hsub : Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ = Point.some x₄ y₄ h₄)
    (hx : x₁ ≠ x₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hx₃ : x₃ ∈ A) (hx₄ : x₄ ∈ A) :
    red A (x₃ - x₀) * red A (x₄ - x₀) * (red A (x₁ - x₀) - red A (x₂ - x₀)) ^ 2
      = red A (x₁ - x₀) ^ 2 * red A (x₂ - x₀) ^ 2 := by
  have hx₃eq : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.addX x₁ x₂
      (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.slope x₁ x₂ y₁ y₂) = x₃ := by
    have e := (add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx).symm.trans hadd
    rw [Point.some.injEq] at e
    exact e.1
  have hx₄eq : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.addX x₁ x₂
      (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.slope x₁ x₂ y₁
        (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x₂ y₂)) = x₄ := by
    have hsub' : Point.some x₁ y₁ h₁ + Point.some x₂
        (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x₂ y₂) ((nonsingular_neg ..).mpr h₂)
        = Point.some x₄ y₄ h₄ := by
      rw [← hsub, sub_eq_add_neg, neg_some]
    have e := (add_of_X_ne (h₁ := h₁) (h₂ := (nonsingular_neg ..).mpr h₂) hx).symm.trans hsub'
    rw [Point.some.injEq] at e
    exact e.1
  have hrow := W.addX_sub_mul_addX_neg_sub_mul_sq_of_criticalCentre hFy hFx h₁ h₂ hx
  rw [hx₃eq, hx₄eq] at hrow
  have herr : (x₃ - x₀) * (x₄ - x₀) * ((x₁ - x₀) - (x₂ - x₀)) ^ 2
      - (x₁ - x₀) ^ 2 * (x₂ - x₀) ^ 2
      = (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        * (4 * (x₁ - x₀) + 4 * (x₂ - x₀) + ((W.b₂ : Kb) + 12 * x₀)) := by
    linear_combination hrow
  have hβA : (W.b₂ : Kb) + 12 * x₀ ∈ A := beta_mem W A hx₀
  have hX₁A : x₁ - x₀ ∈ A := sub_mem hx₁ hx₀
  have hX₂A : x₂ - x₀ ∈ A := sub_mem hx₂ hx₀
  have hX₃A : x₃ - x₀ ∈ A := sub_mem hx₃ hx₀
  have hX₄A : x₄ - x₀ ∈ A := sub_mem hx₄ hx₀
  have hdA : (x₁ - x₀) - (x₂ - x₀) ∈ A := sub_mem hX₁A hX₂A
  have hlhsA : (x₃ - x₀) * (x₄ - x₀) * ((x₁ - x₀) - (x₂ - x₀)) ^ 2 ∈ A :=
    mul_mem (mul_mem hX₃A hX₄A) (pow_mem hdA 2)
  have hrhsA : (x₁ - x₀) ^ 2 * (x₂ - x₀) ^ 2 ∈ A := mul_mem (pow_mem hX₁A 2) (pow_mem hX₂A 2)
  have hval : A.valuation ((x₃ - x₀) * (x₄ - x₀) * ((x₁ - x₀) - (x₂ - x₀)) ^ 2
      - (x₁ - x₀) ^ 2 * (x₂ - x₀) ^ 2) < 1 := by
    rw [herr, map_mul]
    have hle : A.valuation (4 * (x₁ - x₀) + 4 * (x₂ - x₀) + ((W.b₂ : Kb) + 12 * x₀)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr
        (add_mem (add_mem (mul_mem (ofNat_mem A 4) hX₁A) (mul_mem (ofNat_mem A 4) hX₂A)) hβA)
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hle) hbad
  have hred := (red_eq_red_iff A hlhsA hrhsA).mpr hval
  rw [red_mul A (mul_mem hX₃A hX₄A) (pow_mem hdA 2), red_mul A hX₃A hX₄A, red_pow A hdA,
    red_sub A hX₁A hX₂A, red_mul A (pow_mem hX₁A 2) (pow_mem hX₂A 2), red_pow A hX₁A,
    red_pow A hX₂A] at hred
  exact hred

private theorem toric_torus_param {x₀ y₀ : Kb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Kb) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).Point} (hQord : addOrderOf Q = p)
    (hQc : W.InZeroComponentAt A Q)
    {xk yk : ℕ → Kb}
    {hk : ∀ m ∈ Finset.Icc 1 (p - 1), ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular
      (xk m) (yk m)}
    (hkQ : ∀ m (hm : m ∈ Finset.Icc 1 (p - 1)), m • Q = .some (xk m) (yk m) (hk m hm))
    (hint : ∀ m ∈ Finset.Icc 1 (p - 1), xk m ∈ A) :
    ∃ ζ : Kb, IsPrimitiveRoot ζ p ∧ A.valuation (p : Kb) = 1 ∧ A.valuation ζ = 1 ∧
      (∀ i ∈ Finset.Icc 1 (p - 1), A.valuation (1 - ζ ^ i) = 1) ∧
      ∀ m ∈ Finset.Icc 1 (p - 1),
        A.valuation (xk m - x₀ - ((W.b₂ : Kb) + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) < 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega

  have hunit : ∀ m (hm : m ∈ Finset.Icc 1 (p - 1)), A.valuation (xk m - x₀) = 1 := fun m hm =>
    (toric_kernel_unit W A hx₀ hy₀ hFy hFx hnode hbad hQc m (hkQ m hm) (hint m hm)).1
  have hXA : ∀ m (hm : m ∈ Finset.Icc 1 (p - 1)), xk m - x₀ ∈ A := fun m hm =>
    sub_mem (hint m hm) hx₀
  have hβA : (W.b₂ : Kb) + 12 * x₀ ∈ A := beta_mem W A hx₀
  have hrβ0 : red A ((W.b₂ : Kb) + 12 * x₀) ≠ 0 := (red_ne_zero_iff A hβA).mpr hnode
  have hrX0 : ∀ m (hm : m ∈ Finset.Icc 1 (p - 1)), red A (xk m - x₀) ≠ 0 := fun m hm =>
    (red_ne_zero_iff A (hXA m hm)).mpr (hunit m hm)
  have hmemI : ∀ m, 1 ≤ m → m ≤ p - 1 → m ∈ Finset.Icc 1 (p - 1) := fun m h1 h2 =>
    Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hY0 : ∀ m, 1 ≤ m → m ≤ p - 1 →
      red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk m - x₀) ≠ 0 := fun m h1 h2 =>
    div_ne_zero hrβ0 (hrX0 m (hmemI m h1 h2))
  have h1I := hmemI 1 le_rfl (by omega)
  have h2I := hmemI 2 (by norm_num) (by omega)

  have hdbl : red A (xk 2 - x₀) * (red A ((W.b₂ : Kb) + 12 * x₀) + 4 * red A (xk 1 - x₀))
      = red A (xk 1 - x₀) ^ 2 := by
    have hsum : Point.some (xk 1) (yk 1) (hk 1 h1I) + Point.some (xk 1) (yk 1) (hk 1 h1I)
        = Point.some (xk 2) (yk 2) (hk 2 h2I) := by
      have e : 1 • Q + 1 • Q = 2 • Q := by rw [one_nsmul, two_nsmul]
      rw [hkQ 1 h1I, hkQ 2 h2I] at e
      exact e
    exact red_doubling W A hx₀ hFy hFx hbad hsum (hint 1 h1I) (hint 2 h2I) (hunit 1 h1I)
  have h2 : red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk 2 - x₀)
      = (red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk 1 - x₀)) ^ 2
        + 4 * (red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk 1 - x₀)) := by
    rw [div_pow, mul_div_assoc', div_add_div _ _ (pow_ne_zero 2 (hrX0 1 h1I)) (hrX0 1 h1I),
      div_eq_div_iff (hrX0 2 h2I) (mul_ne_zero (pow_ne_zero 2 (hrX0 1 h1I)) (hrX0 1 h1I))]
    linear_combination (-(red A ((W.b₂ : Kb) + 12 * x₀) * red A (xk 1 - x₀))) * hdbl

  have hrec : ∀ m, 2 ≤ m → m ≤ p - 2 →
      (red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk m - x₀)
        - red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk 1 - x₀)) ^ 2
      = red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk (m + 1) - x₀)
        * (red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk (m - 1) - x₀)) := by
    intro m hm2 hmp2
    have hmI := hmemI m (by omega) (by omega)
    have hm1I := hmemI (m + 1) (by omega) (by omega)
    have hm_1I := hmemI (m - 1) (by omega) (by omega)
    have hadd : Point.some (xk m) (yk m) (hk m hmI) + Point.some (xk 1) (yk 1) (hk 1 h1I)
        = Point.some (xk (m + 1)) (yk (m + 1)) (hk (m + 1) hm1I) := by
      have e : m • Q + 1 • Q = (m + 1) • Q := (add_nsmul Q m 1).symm
      rw [hkQ m hmI, hkQ 1 h1I, hkQ (m + 1) hm1I] at e
      exact e
    have hsub : Point.some (xk m) (yk m) (hk m hmI) - Point.some (xk 1) (yk 1) (hk 1 h1I)
        = Point.some (xk (m - 1)) (yk (m - 1)) (hk (m - 1) hm_1I) := by
      have e0 : (m - 1) • Q + 1 • Q = m • Q := by
        rw [← add_nsmul, Nat.sub_add_cancel (by omega : 1 ≤ m)]
      have e : m • Q - 1 • Q = (m - 1) • Q := by rw [← e0, add_sub_cancel_right]
      rw [hkQ m hmI, hkQ 1 h1I, hkQ (m - 1) hm_1I] at e
      exact e
    have hx : xk m ≠ xk 1 := by
      intro hxe
      rcases (X_eq_iff (h₁ := hk m hmI) (h₂ := hk 1 h1I)).mp hxe with he | he
      · rw [he, sub_self] at hsub
        exact some_ne_zero _ hsub.symm
      · rw [he, neg_add_cancel] at hadd
        exact some_ne_zero _ hadd.symm
    have htp := red_two_point W A hx₀ hFy hFx hbad hadd hsub hx (hint m hmI) (hint 1 h1I)
      (hint (m + 1) hm1I) (hint (m - 1) hm_1I)
    rw [div_sub_div _ _ (hrX0 m hmI) (hrX0 1 h1I), div_pow, div_mul_div_comm,
      div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (hrX0 m hmI) (hrX0 1 h1I)))
        (mul_ne_zero (hrX0 (m + 1) hm1I) (hrX0 (m - 1) hm_1I))]
    linear_combination (red A ((W.b₂ : Kb) + 12 * x₀)) ^ 2 * htp

  have hp1I := hmemI (p - 1) (by omega) le_rfl
  have hp2I := hmemI (p - 2) (by omega) (by omega)
  have hxp1 : xk (p - 1) = xk 1 := by
    have e : (p - 1) • Q = -(1 • Q) := kernel_neg W hQord (m := 1) hp.one_lt.le
    rw [hkQ (p - 1) hp1I, hkQ 1 h1I, neg_some, Point.some.injEq] at e
    exact e.1
  have hxp2 : xk (p - 2) = xk 2 := by
    have e : (p - 2) • Q = -(2 • Q) := kernel_neg W hQord (m := 2) (by omega)
    rw [hkQ (p - 2) hp2I, hkQ 2 h2I, neg_some, Point.some.injEq] at e
    exact e.1
  have hsym1 : red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk (p - 1) - x₀)
      = red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk 1 - x₀) := by rw [hxp1]
  have hsym2 : red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk (p - 2) - x₀)
      = red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk 2 - x₀) := by rw [hxp2]

  obtain ⟨c, hcdef⟩ : ∃ c : Kb, c = 2 + ((W.b₂ : Kb) + 12 * x₀) / (xk 1 - x₀) := ⟨_, rfl⟩
  have hcA : c ∈ A := by
    rw [hcdef]; exact add_mem (ofNat_mem A 2) (div_mem_of_val_eq_one A hβA (hunit 1 h1I))
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (c ^ 2 - 4) two_pos
  obtain ⟨w, hwdef⟩ : ∃ w : Kb, w = (c + s) / 2 := ⟨_, rfl⟩
  have hquad : w ^ 2 - c * w + 1 = 0 := by
    rw [hwdef]; linear_combination (1 / 4 : Kb) * hs
  have hww' : w * (c - w) = 1 := by linear_combination -hquad
  have hwA : w ∈ A := by
    by_contra hwA
    have hgt : 1 < A.valuation w := lt_of_not_ge fun h => hwA ((A.valuation_le_one_iff w).mp h)
    have hprod : A.valuation w * A.valuation (c - w) = 1 := by
      rw [← map_mul, hww', map_one]
    have hlt : A.valuation (c - w) < 1 := by
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact inv_lt_one_of_one_lt₀ hgt
    have hvc : A.valuation c = A.valuation w := by
      have e : c = w + (c - w) := by ring
      rw [e]
      exact Valuation.map_add_eq_of_lt_left _ (lt_trans hlt hgt)
    have hcle : A.valuation c ≤ 1 := (A.valuation_le_one_iff c).mpr hcA
    rw [hvc] at hcle
    exact absurd hgt (not_lt.mpr hcle)
  have hwbar : red A w ^ 2
      - (2 + red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk 1 - x₀)) * red A w + 1 = 0 := by
    have e := congrArg (red A) hquad
    rw [red_zero, red_add A (sub_mem (pow_mem hwA 2) (mul_mem hcA hwA)) A.one_mem,
      red_sub A (pow_mem hwA 2) (mul_mem hcA hwA), red_pow A hwA, red_mul A hcA hwA, red_one,
      hcdef, red_add A (ofNat_mem A 2) (div_mem_of_val_eq_one A hβA (hunit 1 h1I)), red_ofNat,
      red_div A hβA (hunit 1 h1I)] at e
    exact e

  obtain ⟨hall, hwp, hw1⟩ := chebyshev_orbit hp3
    (fun m => red A ((W.b₂ : Kb) + 12 * x₀) / red A (xk m - x₀)) hY0 h2 hrec hsym1 hsym2 hwbar

  have hpk : (p : IsLocalRing.ResidueField A) ≠ 0 := by
    intro hp0
    haveI : CharP (IsLocalRing.ResidueField A) p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
    have e : (red A w - 1) ^ p = 0 := by
      rw [sub_pow_char, hwp, one_pow, sub_self]
    exact hw1 (sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp e))
  have hvp : A.valuation (p : Kb) = 1 :=
    (red_ne_zero_iff A (natCast_mem A p)).mp (by rw [red_natCast]; exact hpk)

  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Kb p
  have hvζ₀ : A.valuation ζ₀ = 1 := by
    have hpow : A.valuation ζ₀ ^ p = 1 := by rw [← map_pow, hζ₀.pow_eq_one, map_one]
    rcases lt_trichotomy (A.valuation ζ₀) 1 with hlt | heq | hgt
    · exact absurd hpow (ne_of_lt (pow_lt_one₀ zero_le' hlt hp.ne_zero))
    · exact heq
    · exact absurd hpow (ne_of_gt (one_lt_pow₀ hgt hp.ne_zero))
  have hζ₀A : ζ₀ ∈ A := mem_of_val_eq_one A hvζ₀
  have hrζ₀1 : red A ζ₀ ≠ 1 := by
    intro h1
    have e := congrArg (red A) (hζ₀.geom_sum_eq_zero hp.one_lt)
    rw [red_sum A _ _ (fun i _ => pow_mem hζ₀A i), red_zero] at e
    simp only [red_pow A hζ₀A, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at e
    exact hpk e
  have hrζ₀p : red A ζ₀ ^ p = 1 := by rw [← red_pow A hζ₀A, hζ₀.pow_eq_one, red_one]
  have hprim : IsPrimitiveRoot (red A ζ₀) p := by
    have h := IsPrimitiveRoot.orderOf (red A ζ₀)
    rwa [orderOf_eq_prime hrζ₀p hrζ₀1] at h
  obtain ⟨a, hap, haw⟩ := hprim.eq_pow_of_pow_eq_one hwp
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at haw
    exact hw1 haw.symm
  have hζA : ζ₀ ^ a ∈ A := pow_mem hζ₀A a

  have hone_sub : ∀ i ∈ Finset.Icc 1 (p - 1), A.valuation (1 - (ζ₀ ^ a) ^ i) = 1 := by
    intro i hi
    have hiI := Finset.mem_Icc.mp hi
    have hζiA : (ζ₀ ^ a) ^ i ∈ A := pow_mem hζA i
    refine (red_ne_zero_iff A (sub_mem A.one_mem hζiA)).mp ?_
    rw [red_sub A A.one_mem hζiA, red_one, red_pow A hζA, red_pow A hζ₀A, haw]
    intro h0
    rw [sub_eq_zero] at h0
    have e := hall i hiI.1 hiI.2
    rw [← h0, mul_one, sub_self, zero_pow two_ne_zero] at e
    exact hY0 i hiI.1 hiI.2 e
  refine ⟨ζ₀ ^ a, hζ₀.pow_of_coprime a (Nat.coprime_of_lt_prime ha0 hap hp).symm, hvp,
    by rw [map_pow, hvζ₀, one_pow], hone_sub, ?_⟩

  intro m hm
  have hmI' := Finset.mem_Icc.mp hm
  have hζmA : (ζ₀ ^ a) ^ m ∈ A := pow_mem hζA m
  have hD : A.valuation ((1 - (ζ₀ ^ a) ^ m) ^ 2) = 1 := by rw [map_pow, hone_sub m hm, one_pow]
  have hfracA : ((W.b₂ : Kb) + 12 * x₀) * ((ζ₀ ^ a) ^ m / (1 - (ζ₀ ^ a) ^ m) ^ 2) ∈ A :=
    mul_mem hβA (div_mem_of_val_eq_one A hζmA hD)
  refine (red_eq_red_iff A (hXA m hm) hfracA).mp ?_
  have hDm : (1 - red A w ^ m) ≠ 0 := by
    have h := (red_ne_zero_iff A (sub_mem A.one_mem hζmA)).mpr (hone_sub m hm)
    rwa [red_sub A A.one_mem hζmA, red_one, red_pow A hζA, red_pow A hζ₀A, haw] at h
  rw [red_mul A hβA (div_mem_of_val_eq_one A hζmA hD), red_div A hζmA hD,
    red_pow A (sub_mem A.one_mem hζmA), red_sub A A.one_mem hζmA, red_one, red_pow A hζA,
    red_pow A hζ₀A, haw]
  have e := hall m hmI'.1 hmI'.2
  rw [div_mul_eq_mul_div, div_eq_iff (hrX0 m hm)] at e
  rw [eq_comm, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hDm)]
  linear_combination e

end TTorus

section TGuards

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private lemma val_sigma_eq_one {ζ : Kb} (hζ : A.valuation ζ = 1) {m : ℕ}
    (h1 : A.valuation (1 - ζ ^ m) = 1) :
    A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2) = 1 := by
  rw [map_div₀, map_pow, hζ, one_pow, map_pow, h1, one_pow, div_one]

private lemma val_one_add_four_sigma_eq_one {ζ : Kb} {m : ℕ}
    (h1 : A.valuation (1 - ζ ^ m) = 1) (h2 : A.valuation (1 - ζ ^ (2 * m)) = 1) :
    A.valuation (1 + 4 * (ζ ^ m / (1 - ζ ^ m) ^ 2)) = 1 := by
  have hne : 1 - ζ ^ m ≠ 0 := fun h => by
    rw [h, _root_.map_zero] at h1; exact zero_ne_one h1
  have hid : 1 + 4 * (ζ ^ m / (1 - ζ ^ m) ^ 2) = (1 + ζ ^ m) ^ 2 / (1 - ζ ^ m) ^ 2 := by
    field_simp
    ring
  have hplus : A.valuation (1 + ζ ^ m) = 1 := by
    have hfac : (1 - ζ ^ m) * (1 + ζ ^ m) = 1 - ζ ^ (2 * m) := by ring
    have h := congrArg A.valuation hfac
    rw [map_mul, h1, one_mul, h2] at h
    exact h
  rw [hid, map_div₀, map_pow, map_pow, hplus, h1, one_pow, div_one]

private lemma val_sigma_sub_sigma_eq_one_of_lt {ζ : Kb} (hζ : A.valuation ζ = 1) {m j : ℕ}
    (hjm : j < m) (hm : A.valuation (1 - ζ ^ m) = 1) (hj : A.valuation (1 - ζ ^ j) = 1)
    (hd : A.valuation (1 - ζ ^ (m - j)) = 1) (hs : A.valuation (1 - ζ ^ (m + j)) = 1) :
    A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2 - ζ ^ j / (1 - ζ ^ j) ^ 2) = 1 := by
  have hne_m : 1 - ζ ^ m ≠ 0 := fun h => by
    rw [h, _root_.map_zero] at hm; exact zero_ne_one hm
  have hne_j : 1 - ζ ^ j ≠ 0 := fun h => by
    rw [h, _root_.map_zero] at hj; exact zero_ne_one hj
  obtain ⟨d, rfl⟩ : ∃ d, m = j + d := ⟨m - j, by omega⟩
  have hdpos : (j + d) - j = d := by omega
  rw [hdpos] at hd
  have hid : ζ ^ (j + d) / (1 - ζ ^ (j + d)) ^ 2 - ζ ^ j / (1 - ζ ^ j) ^ 2
      = -(ζ ^ j * (1 - ζ ^ d) * (1 - ζ ^ (j + d + j)))
        / ((1 - ζ ^ (j + d)) ^ 2 * (1 - ζ ^ j) ^ 2) := by
    rw [div_sub_div _ _ (pow_ne_zero 2 hne_m) (pow_ne_zero 2 hne_j)]
    congr 1
    ring
  rw [hid, map_div₀, Valuation.map_neg, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hζ,
    one_pow, one_mul, hd, one_mul, hs, hm, hj, one_pow, one_mul, div_one]

private lemma val_sigma_sub_sigma_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kb} (hζ : A.valuation ζ = 1)
    (hU : ∀ i ∈ Finset.Icc 1 (p - 1), A.valuation (1 - ζ ^ i) = 1)
    {m j : ℕ} (hm : m ∈ Finset.Icc 1 (p / 2)) (hj : j ∈ Finset.Icc 1 (p / 2)) (hne : m ≠ j) :
    A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2 - ζ ^ j / (1 - ζ ^ j) ^ 2) = 1 := by
  have h2n : 2 * (p / 2) < p := by
    have := Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2); omega
  have hmm := Finset.mem_Icc.mp hm
  have hjj := Finset.mem_Icc.mp hj
  have hI : ∀ i, 1 ≤ i → i ≤ p - 1 → A.valuation (1 - ζ ^ i) = 1 := fun i h1 h2 =>
    hU i (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  ·
    have h := val_sigma_sub_sigma_eq_one_of_lt A hζ hlt (hI j hjj.1 (by omega))
      (hI m hmm.1 (by omega)) (hI (j - m) (by omega) (by omega)) (hI (j + m) (by omega) (by omega))
    rw [← Valuation.map_neg, neg_sub]
    exact h
  · exact val_sigma_sub_sigma_eq_one_of_lt A hζ hlt (hI m hmm.1 (by omega))
      (hI j hjj.1 (by omega)) (hI (m - j) (by omega) (by omega)) (hI (m + j) (by omega) (by omega))

private lemma val_sigma_eq_one' {p : ℕ} {ζ : Kb} (hζ : A.valuation ζ = 1)
    (hU : ∀ i ∈ Finset.Icc 1 (p - 1), A.valuation (1 - ζ ^ i) = 1)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (p - 1)) :
    A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2) = 1 :=
  val_sigma_eq_one A hζ (hU m hm)

private lemma val_one_add_four_sigma_eq_one' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kb}
    (hU : ∀ i ∈ Finset.Icc 1 (p - 1), A.valuation (1 - ζ ^ i) = 1)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (p / 2)) :
    A.valuation (1 + 4 * (ζ ^ m / (1 - ζ ^ m) ^ 2)) = 1 := by
  have h2n : 2 * (p / 2) < p := by
    have := Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2); omega
  have hmm := Finset.mem_Icc.mp hm
  exact val_one_add_four_sigma_eq_one A (hU m (Finset.mem_Icc.mpr ⟨hmm.1, by omega⟩))
    (hU (2 * m) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

end TGuards

section C4Sq

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x₀ y₀ : R}

private theorem centre_c₄_eq_sq
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) :
    W.c₄ = (W.b₂ + 12 * x₀) ^ 2 := by
  have h := centre_veluT_eq_zero W hFy hFx
  simp only [c₄]
  linear_combination (-24 : R) * h

end C4Sq

section SigmaCongr

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private theorem val_sum_sub_lt_one {ι : Type*} {s : Finset ι} {f g : ι → Kb}
    (h : ∀ m ∈ s, A.valuation (f m - g m) < 1) :
    A.valuation (∑ m ∈ s, f m - ∑ m ∈ s, g m) < 1 := by
  rw [← Finset.sum_sub_distrib]
  exact A.valuation.map_sum_lt one_ne_zero h

private theorem val_veluT_sub_ideal_lt_one (W : WeierstrassCurve Kb) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0)
    (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {xc Xc : Kb} (hpos : A.valuation (xc - Xc) < 1)
    (hxc : A.valuation (xc - x₀) ≤ 1) (hXc : A.valuation (Xc - x₀) ≤ 1)
    (hβ : A.valuation (W.b₂ + 12 * x₀) ≤ 1) (yc : Kb) :
    A.valuation (W.veluT xc yc - (Xc - x₀) * ((W.b₂ + 12 * x₀) + 6 * (Xc - x₀))) < 1 := by
  rw [veluT_factor W hFy hFx]
  have hkey : (xc - x₀) * ((W.b₂ + 12 * x₀) + 6 * (xc - x₀))
      - (Xc - x₀) * ((W.b₂ + 12 * x₀) + 6 * (Xc - x₀))
      = (xc - Xc) * ((W.b₂ + 12 * x₀) + 6 * ((xc - x₀) + (Xc - x₀))) := by ring
  rw [hkey, map_mul]
  have h6 : A.valuation (6 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 6)
  refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) hpos
  refine A.valuation.map_add_le hβ ?_
  rw [map_mul]
  exact mul_le_one' h6 (A.valuation.map_add_le hxc hXc)

end SigmaCongr

section Pin

local notation "Kb" => AlgebraicClosure ℚ

private theorem pin_ID {F : Type*} [Field F] [CharZero F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (x₀ b₂ : F) :
    ((b₂ + 12 * x₀) ^ 2
        + 240 * ((b₂ + 12 * x₀) ^ 2
            * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
              + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)))
      * ((b₂ + 12 * x₀) * ((p : F) ^ 2 - 1) / 12)
    = -((240 * x₀ + 62 * b₂) * ((b₂ + 12 * x₀) ^ 2
          * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
            + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)))
      - 504 * (x₀ * ((b₂ + 12 * x₀) ^ 2
            * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
              + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
          + (b₂ + 12 * x₀) ^ 3
            * (2 * (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
              + 10 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3)) := by
  obtain ⟨h1, h2, h3⟩ := cyclotomic_velu_powerSums hp hp2 hζ
  rw [h1, h2, h3]
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h24 : (24 : F) ≠ 0 := by norm_num
  have h1440 : (1440 : F) ≠ 0 := by norm_num
  have h120960 : (120960 : F) ≠ 0 := by norm_num
  field_simp
  ring

end Pin

section ZPin

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private theorem toric_z_pin (W' : WeierstrassCurve Kb) (S : Finset (Kb × Kb))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kb} (hζ : IsPrimitiveRoot ζ p)
    {x₀ y₀ z₀ Z₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hFyV : 2 * Z₀ + (W'.veluQuotient S).a₁ * z₀ + (W'.veluQuotient S).a₃ = 0)
    (hFxV : (W'.veluQuotient S).a₁ * Z₀
      = 3 * z₀ ^ 2 + 2 * (W'.veluQuotient S).a₂ * z₀ + (W'.veluQuotient S).a₄)
    (hc₄V : A.valuation (W'.veluQuotient S).c₄ = 1)
    (hx₀ : A.valuation x₀ ≤ 1) (hb₂ : A.valuation W'.b₂ ≤ 1)
    (hμI : A.valuation (((p : Kb) ^ 2 - 1) / 12) ≤ 1)
    (ht : A.valuation (W'.veluTSum S
        - (W'.b₂ + 12 * x₀) ^ 2
            * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
              + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)) < 1)
    (hw : A.valuation (W'.veluWSum S
        - (x₀ * ((W'.b₂ + 12 * x₀) ^ 2
              * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
                + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
            + (W'.b₂ + 12 * x₀) ^ 3
              * (2 * (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
                + 10 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3))) < 1)
    (hεV : A.valuation (Z₀ ^ 2 + (W'.veluQuotient S).a₁ * z₀ * Z₀
        + (W'.veluQuotient S).a₃ * Z₀
        - (z₀ ^ 3 + (W'.veluQuotient S).a₂ * z₀ ^ 2 + (W'.veluQuotient S).a₄ * z₀
            + (W'.veluQuotient S).a₆)) < 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1) :
    A.valuation (z₀ - x₀ - (W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) < 1 := by
  have hcast : ∀ m : ℤ, A.valuation ((m : Kb)) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hβ : A.valuation (W'.b₂ + 12 * x₀) ≤ 1 := by
    refine A.valuation.map_add_le hb₂ ?_
    rw [map_mul]
    exact mul_le_one' (by exact_mod_cast hcast 12) hx₀
  have hanch := anchor_identity W' S hFy hFx hFyV hFxV
  have hc4sq := centre_c₄_eq_sq W' hFy hFx
  have hc₄Vsq : (W'.veluQuotient S).c₄
      = (W'.b₂ + 12 * x₀) ^ 2 + 240 * W'.veluTSum S := by
    rw [veluQuotient_c₄, hc4sq]
  have hID := pin_ID hp hp2 hζ x₀ W'.b₂

  have hkey : (W'.veluQuotient S).c₄
        * (z₀ - x₀ - (W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12)
      = -((240 * x₀ + 62 * W'.b₂) * (W'.veluTSum S
            - (W'.b₂ + 12 * x₀) ^ 2
              * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
                + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)))
        - 504 * (W'.veluWSum S
            - (x₀ * ((W'.b₂ + 12 * x₀) ^ 2
                  * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
                    + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
                + (W'.b₂ + 12 * x₀) ^ 3
                  * (2 * (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
                    + 10 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3)))
        + 72 * ((Z₀ ^ 2 + (W'.veluQuotient S).a₁ * z₀ * Z₀
              + (W'.veluQuotient S).a₃ * Z₀
              - (z₀ ^ 3 + (W'.veluQuotient S).a₂ * z₀ ^ 2 + (W'.veluQuotient S).a₄ * z₀
                  + (W'.veluQuotient S).a₆))
            - (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
              - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)))
        - 240 * (W'.veluTSum S
            - (W'.b₂ + 12 * x₀) ^ 2
              * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
                + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
            * ((W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) := by
    linear_combination hanch - hID
      - ((W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) * hc₄Vsq

  have hco : A.valuation (240 * x₀ + 62 * W'.b₂) ≤ 1 := by
    refine A.valuation.map_add_le ?_ ?_ <;> rw [map_mul]
    · exact mul_le_one' (by exact_mod_cast hcast 240) hx₀
    · exact mul_le_one' (by exact_mod_cast hcast 62) hb₂
  have hT1 : A.valuation (-((240 * x₀ + 62 * W'.b₂) * (W'.veluTSum S
      - (W'.b₂ + 12 * x₀) ^ 2
        * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
          + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)))) < 1 := by
    rw [Valuation.map_neg, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hco) ht
  have hT2 : A.valuation (504 * (W'.veluWSum S
      - (x₀ * ((W'.b₂ + 12 * x₀) ^ 2
            * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
              + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
          + (W'.b₂ + 12 * x₀) ^ 3
            * (2 * (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
              + 10 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3)))) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (by exact_mod_cast hcast 504)) hw
  have hT3 : A.valuation (72 * ((Z₀ ^ 2 + (W'.veluQuotient S).a₁ * z₀ * Z₀
      + (W'.veluQuotient S).a₃ * Z₀
      - (z₀ ^ 3 + (W'.veluQuotient S).a₂ * z₀ ^ 2 + (W'.veluQuotient S).a₄ * z₀
          + (W'.veluQuotient S).a₆))
      - (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)))) < 1 := by
    rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (by exact_mod_cast hcast 72)) ?_
    exact Valuation.map_sub_lt _ hεV hε
  have hT4 : A.valuation (240 * (W'.veluTSum S
      - (W'.b₂ + 12 * x₀) ^ 2
        * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
          + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
      * ((W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12)) < 1 := by
    rw [map_mul, map_mul]
    have hβμ : A.valuation ((W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) ≤ 1 := by
      rw [mul_div_assoc, map_mul]
      exact mul_le_one' hβ hμI
    refine lt_of_le_of_lt (mul_le_of_le_one_right' hβμ) ?_
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (by exact_mod_cast hcast 240)) ht
  have hfin : A.valuation ((W'.veluQuotient S).c₄
      * (z₀ - x₀ - (W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12)) < 1 := by
    rw [hkey]
    exact Valuation.map_sub_lt _
      (Valuation.map_add_lt _ (Valuation.map_sub_lt _ hT1 hT2) hT3) hT4
  rw [map_mul, hc₄V, one_mul] at hfin
  exact hfin

end ZPin

section PinCoeff

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private theorem val_pin_coeff_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hvp : A.valuation ((p : Kb)) = 1) :
    A.valuation (((p : Kb) ^ 2 - 1) / 12) ≤ 1 := by
  by_cases hp3 : p = 3
  · subst hp3
    push_cast at hvp ⊢
    have h1 : ((3 : Kb) ^ 2 - 1) / 12 = 2 / 3 := by norm_num
    rw [h1, map_div₀, hvp, div_one]
    exact (A.valuation_le_one_iff _).mpr (ofNat_mem A 2)
  ·
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have h3 : ¬ (3 ∣ p) := fun hdvd => by
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd) with h | h
      · norm_num at h
      · exact hp3 h.symm
    have h3m : p % 3 ≠ 0 := fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
    have hm : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
    have hsq : p ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]
      rcases hm with h | h | h | h <;> rw [h]
    have hsqz : ((p : ℤ) ^ 2 - 1) % 12 = 0 := by
      have hN : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 := by push_cast; ring
      rw [← hN]
      omega
    obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hsqz
    have hcast : ((p : Kb) ^ 2 - 1) / 12 = ((c : ℤ) : Kb) := by
      have h12 : (12 : Kb) ≠ 0 := by norm_num
      field_simp
      exact_mod_cast hc
    rw [hcast]
    exact (A.valuation_le_one_iff _).mpr (intCast_mem A c)

end PinCoeff

section TermApprox

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private theorem val_term_sub_ideal_lt_one (W' : WeierstrassCurve Kb) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    {xc yc Xc x : Kb} (hcurve : W'.toAffine.Equation xc yc)
    (hpos : A.valuation (xc - Xc) < 1)
    (hβ : A.valuation (W'.b₂ + 12 * x₀) ≤ 1)
    (hxc : A.valuation (xc - x₀) ≤ 1) (hXc : A.valuation (Xc - x₀) ≤ 1)
    (hx : A.valuation (x - x₀) ≤ 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1)
    (hdc : A.valuation (x - xc) = 1) (hdC : A.valuation (x - Xc) = 1) :
    A.valuation ((W'.veluT xc yc / (x - xc) + W'.veluU xc yc / (x - xc) ^ 2)
      - ((Xc - x₀) * ((W'.b₂ + 12 * x₀) + 6 * (Xc - x₀)) / (x - Xc)
         + ((W'.b₂ + 12 * x₀) * (Xc - x₀) ^ 2 + 4 * (Xc - x₀) ^ 3) / (x - Xc) ^ 2)) < 1 := by
  have hdc0 : x - xc ≠ 0 := fun h0 => by
    rw [h0, _root_.map_zero] at hdc; exact zero_ne_one hdc
  have hdC0 : x - Xc ≠ 0 := fun h0 => by
    rw [h0, _root_.map_zero] at hdC; exact zero_ne_one hdC
  have h6 : A.valuation (6 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 6)
  have h4 : A.valuation (4 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 4)
  have h2 : A.valuation (2 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 2)

  have hsplit : (W'.veluT xc yc / (x - xc) + W'.veluU xc yc / (x - xc) ^ 2)
      - ((Xc - x₀) * ((W'.b₂ + 12 * x₀) + 6 * (Xc - x₀)) / (x - Xc)
         + ((W'.b₂ + 12 * x₀) * (Xc - x₀) ^ 2 + 4 * (Xc - x₀) ^ 3) / (x - Xc) ^ 2)
      = (xc - Xc) * (((W'.b₂ + 12 * x₀) + 6 * ((xc - x₀) + (Xc - x₀))) * (x - x₀)
            - 6 * (xc - x₀) * (Xc - x₀)) / ((x - xc) * (x - Xc))
        + (-4 * (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
            - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆))) / (x - xc) ^ 2
        + (xc - Xc) * (((W'.b₂ + 12 * x₀) * ((xc - x₀) + (Xc - x₀))
              + 4 * ((xc - x₀) ^ 2 + (xc - x₀) * (Xc - x₀) + (Xc - x₀) ^ 2)) * (x - x₀) ^ 2
            - 2 * (xc - x₀) * (Xc - x₀) * ((W'.b₂ + 12 * x₀) + 4 * ((xc - x₀) + (Xc - x₀)))
              * (x - x₀)
            + 4 * (xc - x₀) ^ 2 * (Xc - x₀) ^ 2) / ((x - xc) ^ 2 * (x - Xc) ^ 2) := by
    rw [veluT_factor W' hFy hFx, veluU_expand W' hFy hFx hcurve]
    field_simp
    ring
  rw [hsplit]
  have hsum : A.valuation ((xc - x₀) + (Xc - x₀)) ≤ 1 := A.valuation.map_add_le hxc hXc
  have hA1 : A.valuation ((xc - Xc) * (((W'.b₂ + 12 * x₀) + 6 * ((xc - x₀) + (Xc - x₀)))
      * (x - x₀) - 6 * (xc - x₀) * (Xc - x₀)) / ((x - xc) * (x - Xc))) < 1 := by
    rw [map_div₀, map_mul, map_mul, hdc, hdC, one_mul, div_one]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) hpos
    refine A.valuation.map_sub_le ?_ ?_
    · rw [map_mul]
      refine mul_le_one' (A.valuation.map_add_le hβ ?_) hx
      rw [map_mul]
      exact mul_le_one' h6 hsum
    · rw [map_mul, map_mul]
      exact mul_le_one' (mul_le_one' h6 hxc) hXc
  have hA2 : A.valuation ((-4 * (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
      - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆))) / (x - xc) ^ 2) < 1 := by
    rw [map_div₀, map_pow, hdc, one_pow, div_one, map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) hε
    rw [Valuation.map_neg]
    exact h4
  have hA3 : A.valuation ((xc - Xc) * (((W'.b₂ + 12 * x₀) * ((xc - x₀) + (Xc - x₀))
        + 4 * ((xc - x₀) ^ 2 + (xc - x₀) * (Xc - x₀) + (Xc - x₀) ^ 2)) * (x - x₀) ^ 2
      - 2 * (xc - x₀) * (Xc - x₀) * ((W'.b₂ + 12 * x₀) + 4 * ((xc - x₀) + (Xc - x₀)))
        * (x - x₀)
      + 4 * (xc - x₀) ^ 2 * (Xc - x₀) ^ 2) / ((x - xc) ^ 2 * (x - Xc) ^ 2)) < 1 := by
    rw [map_div₀, map_mul, map_mul, map_pow, map_pow, hdc, hdC, one_pow, one_mul, div_one]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) hpos
    refine A.valuation.map_add_le (A.valuation.map_sub_le ?_ ?_) ?_
    · rw [map_mul]
      refine mul_le_one' (A.valuation.map_add_le ?_ ?_) ?_
      · rw [map_mul]; exact mul_le_one' hβ hsum
      · rw [map_mul]
        refine mul_le_one' h4 ?_
        refine A.valuation.map_add_le (A.valuation.map_add_le ?_ ?_) ?_
        · rw [map_pow]; exact pow_le_one' hxc 2
        · rw [map_mul]; exact mul_le_one' hxc hXc
        · rw [map_pow]; exact pow_le_one' hXc 2
      · rw [map_pow]; exact pow_le_one' hx 2
    · rw [map_mul, map_mul, map_mul, map_mul]
      refine mul_le_one' (mul_le_one' (mul_le_one' (mul_le_one' h2 hxc) hXc)
        (A.valuation.map_add_le hβ ?_)) hx
      rw [map_mul]
      exact mul_le_one' h4 hsum
    · rw [map_mul, map_mul, map_pow, map_pow]
      exact mul_le_one' (mul_le_one' h4 (pow_le_one' hxc 2)) (pow_le_one' hXc 2)
  exact Valuation.map_add_lt _ (Valuation.map_add_lt _ hA1 hA2) hA3

end TermApprox

section WTerm

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private theorem val_veluW_sub_ideal_lt_one (W' : WeierstrassCurve Kb) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    {xc yc Xc : Kb} (hcurve : W'.toAffine.Equation xc yc)
    (hpos : A.valuation (xc - Xc) < 1)
    (hx₀ : A.valuation x₀ ≤ 1) (hβ : A.valuation (W'.b₂ + 12 * x₀) ≤ 1)
    (hxc : A.valuation (xc - x₀) ≤ 1) (hXc : A.valuation (Xc - x₀) ≤ 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1) :
    A.valuation (W'.veluW xc yc
      - (((W'.b₂ + 12 * x₀) * (Xc - x₀) ^ 2 + 4 * (Xc - x₀) ^ 3)
         + Xc * ((Xc - x₀) * ((W'.b₂ + 12 * x₀) + 6 * (Xc - x₀))))) < 1 := by
  have h4 : A.valuation (4 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 4)
  have h6 : A.valuation (6 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 6)
  have hxcI : A.valuation xc ≤ 1 := by
    have h : xc = (xc - x₀) + x₀ := by ring
    rw [h]
    exact A.valuation.map_add_le hxc hx₀
  have hsum : A.valuation ((xc - x₀) + (Xc - x₀)) ≤ 1 := A.valuation.map_add_le hxc hXc
  have hkey : W'.veluW xc yc
      - (((W'.b₂ + 12 * x₀) * (Xc - x₀) ^ 2 + 4 * (Xc - x₀) ^ 3)
         + Xc * ((Xc - x₀) * ((W'.b₂ + 12 * x₀) + 6 * (Xc - x₀))))
      = -4 * (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
            - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆))
        + (xc - Xc) * ((W'.b₂ + 12 * x₀) * ((xc - x₀) + (Xc - x₀))
            + 4 * ((xc - x₀) ^ 2 + (xc - x₀) * (Xc - x₀) + (Xc - x₀) ^ 2)
            + xc * ((W'.b₂ + 12 * x₀) + 6 * ((xc - x₀) + (Xc - x₀)))
            + (Xc - x₀) * ((W'.b₂ + 12 * x₀) + 6 * (Xc - x₀))) := by
    simp only [veluW]
    rw [veluT_factor W' hFy hFx, veluU_expand W' hFy hFx hcurve]
    ring
  rw [hkey]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) hε
    rw [Valuation.map_neg]
    exact h4
  · rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) hpos
    refine A.valuation.map_add_le (A.valuation.map_add_le (A.valuation.map_add_le ?_ ?_) ?_) ?_
    · rw [map_mul]; exact mul_le_one' hβ hsum
    · rw [map_mul]
      refine mul_le_one' h4 ?_
      refine A.valuation.map_add_le (A.valuation.map_add_le ?_ ?_) ?_
      · rw [map_pow]; exact pow_le_one' hxc 2
      · rw [map_mul]; exact mul_le_one' hxc hXc
      · rw [map_pow]; exact pow_le_one' hXc 2
    · rw [map_mul]
      refine mul_le_one' hxcI (A.valuation.map_add_le hβ ?_)
      rw [map_mul]; exact mul_le_one' h6 hsum
    · rw [map_mul]
      refine mul_le_one' hXc (A.valuation.map_add_le hβ ?_)
      rw [map_mul]; exact mul_le_one' h6 hXc

end WTerm

section Bridge

local notation "Kb" => AlgebraicClosure ℚ

private theorem toric_ideal_sum_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kb} (hζ : IsPrimitiveRoot ζ p) {x₀ β x : Kb} (hβ0 : β ≠ 0)
    (hd : ∀ k ∈ Finset.Icc 1 (p / 2), x - (x₀ + β * (ζ ^ k / (1 - ζ ^ k) ^ 2)) ≠ 0) :
    x + ∑ m ∈ Finset.Icc 1 (p / 2),
        (((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀)
            * (β + 6 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀))
            / (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)))
          + (β * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 2
              + 4 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 3)
            / (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2)
      = x₀ + β * ((p : Kb) ^ 2 - 1) / 12
        + (x - x₀) ^ p
          / ∏ m ∈ Finset.Icc 1 (p / 2), (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2 := by
  obtain ⟨n', hn'⟩ := hp.odd_of_ne_two hp2
  have hhalf : p / 2 = n' := by omega
  have h1ζ : ∀ k ∈ Finset.Icc 1 (p / 2), (1 : Kb) - ζ ^ k ≠ 0 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hkp : k < p := lt_of_le_of_lt hk2 (Nat.div_lt_self hp.pos one_lt_two)
    refine sub_ne_zero.mpr fun h1 => ?_
    have hdvd : p ∣ k := hζ.dvd_of_pow_eq_one k h1.symm
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hξd : ∀ k ∈ Finset.Icc 1 (p / 2), (x - x₀) / β ≠ ζ ^ k / (1 - ζ ^ k) ^ 2 := by
    intro k hk heq
    refine hd k hk ?_
    have h1 := h1ζ k hk
    field_simp at heq
    field_simp
    linear_combination heq
  have hL := cyclotomic_velu_xLaw hp hp2 hζ ((x - x₀) / β) hξd

  have hterm : ∀ m ∈ Finset.Icc 1 (p / 2),
      (((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀)
          * (β + 6 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀))
          / (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)))
        + (β * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 2
            + 4 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 3)
          / (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2)
      = β * (ζ ^ m / (1 - ζ ^ m) ^ 2 * (1 + 6 * (ζ ^ m / (1 - ζ ^ m) ^ 2))
              / ((x - x₀) / β - ζ ^ m / (1 - ζ ^ m) ^ 2)
            + (ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2 * (1 + 4 * (ζ ^ m / (1 - ζ ^ m) ^ 2))
              / ((x - x₀) / β - ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2) := by
    intro m hm
    have hdm := hd m hm
    have hdm' : x - x₀ - β * (ζ ^ m / (1 - ζ ^ m) ^ 2) ≠ 0 := by
      intro h0; exact hdm (by linear_combination h0)
    have h1 := h1ζ m hm
    have hξm : (x - x₀) / β - ζ ^ m / (1 - ζ ^ m) ^ 2 ≠ 0 := sub_ne_zero.mpr (hξd m hm)
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

  have hprod : ∏ m ∈ Finset.Icc 1 (p / 2), (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2
      = β ^ (2 * n') * ∏ m ∈ Finset.Icc 1 (p / 2),
          ((x - x₀) / β - ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2 := by
    have hfac : ∀ m ∈ Finset.Icc 1 (p / 2),
        (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2
        = β ^ 2 * ((x - x₀) / β - ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2 := by
      intro m _
      field_simp
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Nat.card_Icc, hhalf]
    rw [show n' + 1 - 1 = n' from rfl, ← pow_mul, mul_comm 2 n']
  have hPterm : (x - x₀) ^ p
        / ∏ m ∈ Finset.Icc 1 (p / 2), (x - (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2
      = β * (((x - x₀) / β) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
          ((x - x₀) / β - ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2) := by
    rw [hprod, div_pow]
    rw [show p = 2 * n' + 1 from hn'.symm ▸ by omega]
    have hprod0 : ∏ m ∈ Finset.Icc 1 (p / 2),
        ((x - x₀) / β - ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2 ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun m hm => ?_
      exact pow_ne_zero 2 (sub_ne_zero.mpr (hξd m hm))
    field_simp
    ring
  rw [hPterm]
  have hx' : β * ((x - x₀) / β) = x - x₀ := by field_simp
  linear_combination β * hL - hx'

end Bridge

section ToricMasters

local notation "Kb" => AlgebraicClosure ℚ

variable (A : ValuationSubring Kb)

private theorem toric_principal (W' : WeierstrassCurve Kb) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Kb} (hζ : IsPrimitiveRoot ζ p) {x₀ y₀ z₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hnode : A.valuation (W'.b₂ + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    (hcur : ∀ m ∈ Finset.Icc 1 (p / 2), W'.toAffine.Equation (xk m) (yk m))
    (hpos : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xk m
      - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) < 1)
    (hσI : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2) ≤ 1)
    {x : Kb} (hx : A.valuation (x - x₀) ≤ 1)
    (hdk : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x - xk m) = 1)
    (hdK : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x
      - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) = 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1)
    (hzpin : A.valuation (z₀ - x₀ - (W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) < 1) :
    A.valuation ((x + ∑ m ∈ Finset.Icc 1 (p / 2),
        (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
      - z₀ - (x - x₀) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
          (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2) < 1 := by
  have hβ0 : W'.b₂ + 12 * x₀ ≠ 0 := fun h0 => by
    rw [h0, _root_.map_zero] at hnode; exact zero_ne_one hnode
  have hd : ∀ k ∈ Finset.Icc 1 (p / 2),
      x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ k / (1 - ζ ^ k) ^ 2)) ≠ 0 := fun k hk h0 => by
    have h1 := hdK k hk
    rw [h0, _root_.map_zero] at h1
    exact zero_ne_one h1
  have hbridge := toric_ideal_sum_eq hp hp2 hζ (x₀ := x₀) (x := x) hβ0 hd
  have hsplit : (x + ∑ m ∈ Finset.Icc 1 (p / 2),
        (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
      - z₀ - (x - x₀) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
          (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2
      = ((∑ m ∈ Finset.Icc 1 (p / 2),
            (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
          - ∑ m ∈ Finset.Icc 1 (p / 2),
            (((x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀)
                * ((W'.b₂ + 12 * x₀)
                    + 6 * ((x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀))
                / (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)))
              + ((W'.b₂ + 12 * x₀)
                    * ((x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 2
                  + 4 * ((x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 3)
                / (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2))
        + -(z₀ - x₀ - (W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) := by
    linear_combination hbridge
  rw [hsplit]
  refine Valuation.map_add_lt _ ?_ ?_
  · refine val_sum_sub_lt_one A fun m hm => ?_
    have hXcm : A.valuation ((x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ≤ 1 := by
      rw [show (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀
        = (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2) from by ring, map_mul]
      exact mul_le_one' (le_of_eq hnode) (hσI m hm)
    have hxcm : A.valuation (xk m - x₀) ≤ 1 := by
      rw [show xk m - x₀ = (xk m - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)))
        + ((x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) from by ring]
      exact A.valuation.map_add_le (le_of_lt (hpos m hm)) hXcm
    exact val_term_sub_ideal_lt_one A W' hFy hFx (hcur m hm) (hpos m hm)
      (le_of_eq hnode) hxcm hXcm hx hε (hdk m hm) (hdK m hm)
  · rw [Valuation.map_neg]
    exact hzpin

private theorem toric_master_low (W' : WeierstrassCurve Kb) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Kb} (hζ : IsPrimitiveRoot ζ p) {x₀ y₀ z₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hnode : A.valuation (W'.b₂ + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    (hcur : ∀ m ∈ Finset.Icc 1 (p / 2), W'.toAffine.Equation (xk m) (yk m))
    (hpos : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xk m
      - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) < 1)
    (hσu : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2) = 1)
    (hlamu : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xk m - x₀) = 1)
    {x : Kb} (hxlow : A.valuation (x - x₀) < 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1)
    (hzpin : A.valuation (z₀ - x₀ - (W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) < 1) :
    A.valuation ((x + ∑ m ∈ Finset.Icc 1 (p / 2),
        (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
      - z₀) < 1 := by
  have hdk : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x - xk m) = 1 := by
    intro m hm
    rw [Valuation.map_sub_swap]
    rw [show xk m - x = (xk m - x₀) - (x - x₀) from by ring]
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hlamu m hm]; exact hxlow)]
    exact hlamu m hm
  have hdK : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x
      - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) = 1 := by
    intro m hm
    have hβσ : A.valuation ((W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) = 1 := by
      rw [map_mul, hnode, hσu m hm, one_mul]
    rw [Valuation.map_sub_swap]
    rw [show (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x
      = (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2) - (x - x₀) from by ring]
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hβσ]; exact hxlow)]
    exact hβσ
  have hprin := toric_principal A W' hp hp2 hζ hFy hFx hnode hcur hpos
    (fun m hm => le_of_eq (hσu m hm)) (le_of_lt hxlow) hdk hdK hε hzpin
  have hP : A.valuation ((x - x₀) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
      (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2) < 1 := by
    rw [map_div₀, map_pow, map_prod]
    rw [Finset.prod_congr rfl (fun m hm => by rw [map_pow, hdK m hm, one_pow])]
    rw [Finset.prod_const_one, div_one]
    exact pow_lt_one₀ zero_le' hxlow hp.pos.ne'
  have hfin := Valuation.map_add_lt _ hprin hP
  rw [sub_add_cancel] at hfin
  exact hfin

private theorem toric_master_unit (W' : WeierstrassCurve Kb) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Kb} (hζ : IsPrimitiveRoot ζ p) {x₀ y₀ z₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hnode : A.valuation (W'.b₂ + 12 * x₀) = 1)
    {xk yk : ℕ → Kb}
    (hcur : ∀ m ∈ Finset.Icc 1 (p / 2), W'.toAffine.Equation (xk m) (yk m))
    (hpos : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xk m
      - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) < 1)
    (hσI : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2) ≤ 1)
    {x : Kb} (hxu : A.valuation (x - x₀) = 1)
    (hdk : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x - xk m) = 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1)
    (hzpin : A.valuation (z₀ - x₀ - (W'.b₂ + 12 * x₀) * ((p : Kb) ^ 2 - 1) / 12) < 1) :
    ¬ A.valuation ((x + ∑ m ∈ Finset.Icc 1 (p / 2),
        (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
      - z₀) < 1 := by
  have hdK : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x
      - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) = 1 := by
    intro m hm
    rw [show x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))
      = (x - xk m) + (xk m - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)))
      from by ring]
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hdk m hm]; exact hpos m hm)]
    exact hdk m hm
  have hprin := toric_principal A W' hp hp2 hζ hFy hFx hnode hcur hpos hσI
    (le_of_eq hxu) hdk hdK hε hzpin
  have hP : A.valuation ((x - x₀) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
      (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2) = 1 := by
    rw [map_div₀, map_pow, map_prod]
    rw [Finset.prod_congr rfl (fun m hm => by rw [map_pow, hdK m hm, one_pow])]
    rw [Finset.prod_const_one, div_one, hxu, one_pow]
  intro hlt
  have hcontra : A.valuation ((x - x₀) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
      (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2) < 1 := by
    rw [show (x - x₀) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
          (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2
      = ((x + ∑ m ∈ Finset.Icc 1 (p / 2),
            (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
          - z₀)
        - ((x + ∑ m ∈ Finset.Icc 1 (p / 2),
            (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
          - z₀ - (x - x₀) ^ p / ∏ m ∈ Finset.Icc 1 (p / 2),
              (x - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) ^ 2) from by ring]
    exact Valuation.map_sub_lt _ hlt hprin
  rw [hP] at hcontra
  exact lt_irrefl 1 hcontra

private theorem toric_master_pole (W' : WeierstrassCurve Kb) {p : ℕ} {ζ : Kb}
    {x₀ y₀ z₀ : Kb}
    (hFy : 2 * y₀ + W'.a₁ * x₀ + W'.a₃ = 0)
    (hFx : W'.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W'.a₂ * x₀ + W'.a₄)
    (hnode : A.valuation (W'.b₂ + 12 * x₀) = 1) (hx₀I : A.valuation x₀ ≤ 1)
    {xk yk : ℕ → Kb}
    (hcur : ∀ m ∈ Finset.Icc 1 (p / 2), W'.toAffine.Equation (xk m) (yk m))
    (hpos : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xk m
      - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2))) < 1)
    (hlamu : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xk m - x₀) = 1)
    {K : ℕ} (hKmem : K ∈ Finset.Icc 1 (p / 2))
    (hσd : ∀ m ∈ Finset.Icc 1 (p / 2), m ≠ K →
      A.valuation (ζ ^ K / (1 - ζ ^ K) ^ 2 - ζ ^ m / (1 - ζ ^ m) ^ 2) = 1)
    (h4σ : A.valuation (1 + 4 * (ζ ^ K / (1 - ζ ^ K) ^ 2)) = 1)
    {x : Kb} (hcolK : A.valuation (x - xk K) < 1) (hxneK : x ≠ xk K)
    (hzI : A.valuation z₀ ≤ 1)
    (hε : A.valuation (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
        - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) < 1) :
    ¬ A.valuation ((x + ∑ m ∈ Finset.Icc 1 (p / 2),
        (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
      - z₀) < 1 := by
  have h4 : A.valuation (4 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 4)
  have h6 : A.valuation (6 : Kb) ≤ 1 := (A.valuation_le_one_iff _).mpr (ofNat_mem A 6)
  have hβ : A.valuation (W'.b₂ + 12 * x₀) ≤ 1 := le_of_eq hnode
  have hdcK0 : x - xk K ≠ 0 := sub_ne_zero.mpr hxneK

  have hxu : A.valuation (x - x₀) = 1 := by
    rw [show x - x₀ = (xk K - x₀) + (x - xk K) from by ring,
      Valuation.map_add_eq_of_lt_left _ (by rw [hlamu K hKmem]; exact hcolK)]
    exact hlamu K hKmem
  have hxI : A.valuation x ≤ 1 := by
    rw [show x = (x - x₀) + x₀ from by ring]
    exact A.valuation.map_add_le (le_of_eq hxu) hx₀I

  have hβ4c : A.valuation ((W'.b₂ + 12 * x₀) + 4 * (xk K - x₀)) = 1 := by
    have hid : (W'.b₂ + 12 * x₀) + 4 * (xk K - x₀)
        = (W'.b₂ + 12 * x₀) * (1 + 4 * (ζ ^ K / (1 - ζ ^ K) ^ 2))
          + 4 * (xk K - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ K / (1 - ζ ^ K) ^ 2))) := by ring
    have hunit : A.valuation ((W'.b₂ + 12 * x₀)
        * (1 + 4 * (ζ ^ K / (1 - ζ ^ K) ^ 2))) = 1 := by
      rw [map_mul, hnode, h4σ, one_mul]
    rw [hid, Valuation.map_add_eq_of_lt_left _ (by
      rw [hunit, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h4) (hpos K hKmem))]
    exact hunit
  have hukK : A.valuation (W'.veluU (xk K) (yk K)) = 1 := by
    rw [veluU_expand W' hFy hFx (hcur K hKmem)]
    have hid : -4 * (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
          - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆))
        + (W'.b₂ + 12 * x₀) * (xk K - x₀) ^ 2 + 4 * (xk K - x₀) ^ 3
        = (xk K - x₀) ^ 2 * ((W'.b₂ + 12 * x₀) + 4 * (xk K - x₀))
          + (-4) * (y₀ ^ 2 + W'.a₁ * x₀ * y₀ + W'.a₃ * y₀
            - (x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) := by ring
    have hmain : A.valuation ((xk K - x₀) ^ 2
        * ((W'.b₂ + 12 * x₀) + 4 * (xk K - x₀))) = 1 := by
      rw [map_mul, map_pow, hlamu K hKmem, one_pow, one_mul, hβ4c]
    rw [hid, Valuation.map_add_eq_of_lt_left _ (by
      rw [hmain, map_mul, Valuation.map_neg]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h4) hε)]
    exact hmain

  have htK : A.valuation (W'.veluT (xk K) (yk K)) ≤ 1 := by
    rw [veluT_factor W' hFy hFx, map_mul]
    refine mul_le_one' (le_of_eq (hlamu K hKmem)) (A.valuation.map_add_le hβ ?_)
    rw [map_mul]
    exact mul_le_one' h6 (le_of_eq (hlamu K hKmem))
  have hnumK : A.valuation (W'.veluU (xk K) (yk K)
      + W'.veluT (xk K) (yk K) * (x - xk K)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by
      rw [hukK, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' htK) hcolK)]
    exact hukK
  have hsplitK : W'.veluT (xk K) (yk K) / (x - xk K) + W'.veluU (xk K) (yk K) / (x - xk K) ^ 2
      = (W'.veluU (xk K) (yk K) + W'.veluT (xk K) (yk K) * (x - xk K)) / (x - xk K) ^ 2 := by
    field_simp
    ring
  have hden2 : A.valuation (x - xk K) ^ 2 < 1 :=
    pow_lt_one₀ zero_le' hcolK two_ne_zero
  have hden0 : (0 : _) < A.valuation (x - xk K) ^ 2 :=
    zero_lt_iff.mpr (pow_ne_zero 2 fun h0 => hdcK0 (A.valuation.zero_iff.mp h0))
  have h1K : 1 < A.valuation (W'.veluT (xk K) (yk K) / (x - xk K)
      + W'.veluU (xk K) (yk K) / (x - xk K) ^ 2) := by
    rw [hsplitK, map_div₀, map_pow, hnumK, one_lt_div₀ hden0]
    exact hden2

  have hrest : A.valuation ((x - z₀) + ∑ m ∈ (Finset.Icc 1 (p / 2)).erase K,
      (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2)) ≤ 1 := by
    refine A.valuation.map_add_le (A.valuation.map_sub_le hxI hzI) ?_
    refine A.valuation.map_sum_le fun m hm' => ?_
    have hm := Finset.mem_of_mem_erase hm'
    have hmK := Finset.ne_of_mem_erase hm'
    have hdkm : A.valuation (x - xk m) = 1 := by
      have happ : A.valuation (xk K - xk m) = 1 := by
        have hid : xk K - xk m
            = (W'.b₂ + 12 * x₀) * (ζ ^ K / (1 - ζ ^ K) ^ 2 - ζ ^ m / (1 - ζ ^ m) ^ 2)
              + ((xk K - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ K / (1 - ζ ^ K) ^ 2)))
                - (xk m - (x₀ + (W'.b₂ + 12 * x₀) * (ζ ^ m / (1 - ζ ^ m) ^ 2)))) := by ring
        have hunit : A.valuation ((W'.b₂ + 12 * x₀)
            * (ζ ^ K / (1 - ζ ^ K) ^ 2 - ζ ^ m / (1 - ζ ^ m) ^ 2)) = 1 := by
          rw [map_mul, hnode, hσd m hm hmK, one_mul]
        rw [hid, Valuation.map_add_eq_of_lt_left _ (by
          rw [hunit]
          exact Valuation.map_sub_lt _ (hpos K hKmem) (hpos m hm))]
        exact hunit
      rw [show x - xk m = (xk K - xk m) + (x - xk K) from by ring,
        Valuation.map_add_eq_of_lt_left _ (by rw [happ]; exact hcolK)]
      exact happ
    have hukm : A.valuation (W'.veluU (xk m) (yk m)) ≤ 1 := by
      rw [veluU_expand W' hFy hFx (hcur m hm)]
      refine A.valuation.map_add_le (A.valuation.map_add_le ?_ ?_) ?_
      · rw [map_mul, Valuation.map_neg]
        exact mul_le_one' h4 (le_of_lt hε)
      · rw [map_mul, map_pow]
        exact mul_le_one' hβ (pow_le_one' (le_of_eq (hlamu m hm)) 2)
      · rw [map_mul, map_pow]
        exact mul_le_one' h4 (pow_le_one' (le_of_eq (hlamu m hm)) 3)
    have htkm : A.valuation (W'.veluT (xk m) (yk m)) ≤ 1 := by
      rw [veluT_factor W' hFy hFx, map_mul]
      refine mul_le_one' (le_of_eq (hlamu m hm)) (A.valuation.map_add_le hβ ?_)
      rw [map_mul]
      exact mul_le_one' h6 (le_of_eq (hlamu m hm))
    refine A.valuation.map_add_le ?_ ?_
    · rw [map_div₀, hdkm, div_one]
      exact htkm
    · rw [map_div₀, map_pow, hdkm, one_pow, div_one]
      exact hukm

  intro hlt
  have hsplit : (x + ∑ m ∈ Finset.Icc 1 (p / 2),
        (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2))
      - z₀
      = (W'.veluT (xk K) (yk K) / (x - xk K) + W'.veluU (xk K) (yk K) / (x - xk K) ^ 2)
        + ((x - z₀) + ∑ m ∈ (Finset.Icc 1 (p / 2)).erase K,
          (W'.veluT (xk m) (yk m) / (x - xk m) + W'.veluU (xk m) (yk m) / (x - xk m) ^ 2)) := by
    rw [← Finset.add_sum_erase _ _ hKmem]
    ring
  rw [hsplit, Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hrest h1K)] at hlt
  exact absurd hlt (not_lt.mpr (le_of_lt h1K))

end ToricMasters

section IdealSums

local notation "Kb" => AlgebraicClosure ℚ

private theorem ideal_tsum_eq {p : ℕ} (ζ x₀ β : Kb) :
    ∑ m ∈ Finset.Icc 1 (p / 2),
        ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀)
          * (β + 6 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀))
      = β ^ 2 * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
          + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2) := by
    rw [Finset.sum_congr rfl (fun m _ => show
        ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀)
          * (β + 6 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀))
        = β ^ 2 * (ζ ^ m / (1 - ζ ^ m) ^ 2)
          + 6 * β ^ 2 * (ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2 from by ring)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring

private theorem ideal_wsum_eq {p : ℕ} (ζ x₀ β : Kb) :
    ∑ m ∈ Finset.Icc 1 (p / 2),
        ((β * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 2
            + 4 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 3)
          + (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))
            * (((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀)
                * (β + 6 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀))))
      = x₀ * (β ^ 2 * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
            + 6 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
        + β ^ 3 * (2 * (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
            + 10 * ∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3) := by
    rw [Finset.sum_congr rfl (fun m _ => show
        ((β * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 2
            + 4 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀) ^ 3)
          + (x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2))
            * (((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀)
                * (β + 6 * ((x₀ + β * (ζ ^ m / (1 - ζ ^ m) ^ 2)) - x₀))))
        = x₀ * β ^ 2 * (ζ ^ m / (1 - ζ ^ m) ^ 2)
          + (6 * x₀ * β ^ 2 + 2 * β ^ 3) * (ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 2
          + 10 * β ^ 3 * (ζ ^ m / (1 - ζ ^ m) ^ 2) ^ 3 from by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring

end IdealSums

end QD1dpAux

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p)
    (W' : WeierstrassCurve ℤ) (u : (AlgebraicClosure ℚ)ˣ)
    (hW' : (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) =
      (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) •
        (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
         Wb.veluQuotient (Wb.oddOrderSummingSet Q (p / 2))))
    {q : ℕ} (hq : q.Prime) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (hqΔ' : (q : ℤ) ∣ W'.Δ) (hqc₄' : ¬ (q : ℤ) ∣ W'.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hu : A.valuation (u : AlgebraicClosure ℚ) = 1)
    (x y : AlgebraicClosure ℚ)
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hL : (.some x y h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
      ∉ AddSubgroup.zmultiples Q)
    (h' : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular
      (((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 2 *
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) x)
      (((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 *
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluY
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) x y)) :
    W'.InZeroComponentAt A (.some _ _ h') ↔
      ∃ k ∈ AddSubgroup.zmultiples Q,
        W.InZeroComponentAt A
          ((.some x y h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) - k) := by
  have hW'' : (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
      = (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) •
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))) := hW'
  have hΔ' : W'.Δ ≠ 0 := QD1dpAux.deltaPrime_ne_zero W hΔ hp hp2 Q hQord W' u hW''

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    W.exists_criticalCentre_of_multiplicativeReduction hq hΔ hqΔ hqc₄ A hA

  obtain ⟨x₀', y₀', hx₀', hy₀', hFy', hFx', hnode', hbad', -⟩ :=
    W'.exists_criticalCentre_of_multiplicativeReduction hq hΔ' hqΔ' hqc₄' A hA

  obtain ⟨xk, yk, hk, hkQ⟩ := QD1dpAux.exists_kernel_coords_half W hp hp2 hQord
  have h2n : 2 * (p / 2) < p := by
    have := Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2); omega

  have hFyb := QD1dpAux.hFy_dock W hFy
  have hFxb := QD1dpAux.hFx_dock W hFx
  have hb₂b : A.valuation ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ ≤ 1 := by
    rw [QD1dpAux.b₂_dock W]; exact (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hx₀v : A.valuation x₀ ≤ 1 := (A.valuation_le_one_iff _).mpr hx₀
  have hεb : A.valuation (y₀ ^ 2
      + ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₁ * x₀ * y₀
      + ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₃ * y₀
      - (x₀ ^ 3 + ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₂ * x₀ ^ 2
          + ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₄ * x₀
          + ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₆)) < 1 := by
    rw [QD1dpAux.ε_dock W x₀ y₀]; exact hbad
  have hc₄V := QD1dpAux.valuation_c₄_veluQuotient_eq_one W W' u hW'' A hu hq hA hqc₄'

  have hFyV := QD1dpAux.centre_hFy_transfer W W' u hW'' x₀' y₀' hFy'
  have hFxV := QD1dpAux.centre_hFx_transfer W W' u hW'' x₀' y₀' hFx'
  have hbadV := QD1dpAux.centre_hbad_transfer W W' u hW'' A hu x₀' y₀' hbad'
  simp only at hbadV
  have hFyV' : 2 * ((u : AlgebraicClosure ℚ) ^ 3 * y₀')
      + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₁
        * ((u : AlgebraicClosure ℚ) ^ 2 * x₀')
      + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₃
      = 0 := by
    simp only [WeierstrassCurve.veluQuotient_a₁, WeierstrassCurve.veluQuotient_a₃,
      QD1dpAux.baseChange_a₁, QD1dpAux.baseChange_a₃]
    exact hFyV
  have hFxV' : (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₁
        * ((u : AlgebraicClosure ℚ) ^ 3 * y₀')
      = 3 * ((u : AlgebraicClosure ℚ) ^ 2 * x₀') ^ 2
        + 2 * (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₂
          * ((u : AlgebraicClosure ℚ) ^ 2 * x₀')
        + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q
              (p / 2))).a₄ := by
    simp only [WeierstrassCurve.veluQuotient_a₁, WeierstrassCurve.veluQuotient_a₂,
      WeierstrassCurve.veluQuotient_a₄, QD1dpAux.baseChange_a₁, QD1dpAux.baseChange_a₂,
      QD1dpAux.baseChange_a₄]
    exact hFxV
  have hεV : A.valuation (((u : AlgebraicClosure ℚ) ^ 3 * y₀') ^ 2
      + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₁
        * ((u : AlgebraicClosure ℚ) ^ 2 * x₀') * ((u : AlgebraicClosure ℚ) ^ 3 * y₀')
      + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₃
        * ((u : AlgebraicClosure ℚ) ^ 3 * y₀')
      - (((u : AlgebraicClosure ℚ) ^ 2 * x₀') ^ 3
        + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₂
          * ((u : AlgebraicClosure ℚ) ^ 2 * x₀') ^ 2
        + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))).a₄
          * ((u : AlgebraicClosure ℚ) ^ 2 * x₀')
        + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q
              (p / 2))).a₆)) < 1 := by
    simp only [WeierstrassCurve.veluQuotient_a₁, WeierstrassCurve.veluQuotient_a₂,
      WeierstrassCurve.veluQuotient_a₃, WeierstrassCurve.veluQuotient_a₄,
      WeierstrassCurve.veluQuotient_a₆, QD1dpAux.baseChange_a₁, QD1dpAux.baseChange_a₂,
      QD1dpAux.baseChange_a₃, QD1dpAux.baseChange_a₄, QD1dpAux.baseChange_a₆,
      QD1dpAux.baseChange_b₂]
    exact hbadV
  by_cases hQc : W.InZeroComponentAt A Q
  ·

    rw [QD1dpAux.rhs_iff_of_toric W A hQc (.some x y h)]
    have hcritW : ¬ W.InZeroComponentAt A (Point.some x y h) ↔ A.valuation (x - x₀) < 1 :=
      W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad h
    have hcritW' : ¬ W'.InZeroComponentAt A (Point.some _ _ h')
        ↔ A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) x
            - (u : AlgebraicClosure ℚ) ^ 2 * x₀') < 1 :=
      QD1dpAux.not_lhs_iff W W' A u hu hx₀' hy₀' hFy' hFx' hnode' hbad' x y h'

    suffices hsuff :
        A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) x
            - (u : AlgebraicClosure ℚ) ^ 2 * x₀') < 1
          ↔ A.valuation (x - x₀) < 1 by
      exact not_iff_not.mp (hcritW'.trans (hsuff.trans hcritW.symm))

    obtain ⟨xQ, yQ, hQns, rfl⟩ :=
      QD1dpAux.ne_zero_exists_some (QD1dpAux.ne_zero_of_addOrderOf hQord hp.one_lt)
    by_cases hxQA : xQ ∈ A
    ·

      obtain ⟨xkf, ykf, hkf, hkQf⟩ := QD1dpAux.exists_kernel_coords W hQord

      have hvxQ : A.valuation (xQ - x₀) = 1 := by
        have hge : ¬ A.valuation (xQ - x₀) < 1 := fun hlt =>
          (W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad
            hQns).mpr hlt hQc
        have hle : A.valuation (xQ - x₀) ≤ 1 :=
          (A.valuation_le_one_iff _).mpr (sub_mem hxQA hx₀)
        exact le_antisymm hle (not_lt.mp hge)

      have h1mem : 1 ∈ Finset.Icc 1 (p - 1) :=
        Finset.mem_Icc.mpr ⟨le_refl 1, Nat.le_sub_one_of_lt hp.one_lt⟩
      have hQ1 : Point.some xQ yQ hQns = Point.some (xkf 1) (ykf 1) (hkf 1 h1mem) := by
        have := hkQf 1 h1mem
        rw [one_nsmul] at this; exact this

      have hint : ∀ m ∈ Finset.Icc 1 (p - 1), xkf m ∈ A := fun m hm =>
        QD1dpAux.toric_kernel_integral W A hp hQord hQc rfl hxQA
          (Finset.mem_Icc.mp hm).1 (Nat.lt_of_le_pred hp.pos (Finset.mem_Icc.mp hm).2) (hkQf m hm)

      obtain ⟨ζ, hζ, hvp, hvζ, hU, hposf⟩ :=
        QD1dpAux.toric_torus_param W A hx₀ hy₀ hFy hFx hnode hbad hp hp2 hQord hQc hkQf hint

      obtain ⟨hkf', hkQf'⟩ := QD1dpAux.hkQ_half_of_full W hp hkQf
      have hsub : ∀ m ∈ Finset.Icc 1 (p / 2), m ∈ Finset.Icc 1 (p - 1) := fun m hm => by
        have := Finset.mem_Icc.mp hm
        have hd := Nat.div_lt_self hp.pos one_lt_two
        exact Finset.mem_Icc.mpr ⟨this.1, Nat.le_sub_one_of_lt (Nat.lt_of_le_of_lt this.2 hd)⟩

      have hnodeb : A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂
          + 12 * x₀) = 1 := by rw [QD1dpAux.b₂_dock W]; exact hnode
      have hcur : ∀ m ∈ Finset.Icc 1 (p / 2),
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Equation
            (xkf m) (ykf m) := fun m hm => (hkf' m hm).1
      have hlamu : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xkf m - x₀) = 1 := fun m hm =>
        (QD1dpAux.toric_kernel_unit W A hx₀ hy₀ hFy hFx hnode hbad hQc m (hkQf' m hm)
          (hint m (hsub m hm))).1
      have hpos : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xkf m
          - (x₀ + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ + 12 * x₀)
              * (ζ ^ m / (1 - ζ ^ m) ^ 2))) < 1 := by
        intro m hm
        have h := hposf m (hsub m hm)
        rw [QD1dpAux.b₂_dock W]
        rw [show xkf m - (x₀ + ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀)
              * (ζ ^ m / (1 - ζ ^ m) ^ 2))
          = xkf m - x₀ - ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀)
              * (ζ ^ m / (1 - ζ ^ m) ^ 2) from by ring]
        exact h
      have hσu : ∀ m ∈ Finset.Icc 1 (p / 2),
          A.valuation (ζ ^ m / (1 - ζ ^ m) ^ 2) = 1 := fun m hm =>
        QD1dpAux.val_sigma_eq_one' A hvζ hU (hsub m hm)
      have hμI : A.valuation (((p : AlgebraicClosure ℚ) ^ 2 - 1) / 12) ≤ 1 :=
        QD1dpAux.val_pin_coeff_le_one A hp hp2 hvp

      have ht : A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluTSum
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet
              (Point.some xQ yQ hQns) (p / 2))
          - (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ + 12 * x₀) ^ 2
              * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
                + 6 * ∑ k ∈ Finset.Icc 1 (p / 2),
                    (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)) < 1 := by
        rw [QD1dpAux.veluTSum_eq_sum_Icc _ hQord h2n hkQf',
          ← QD1dpAux.ideal_tsum_eq (p := p) ζ x₀
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ + 12 * x₀)]
        refine QD1dpAux.val_sum_sub_lt_one A (fun m hm => ?_)
        exact QD1dpAux.val_veluT_sub_ideal_lt_one A _ hFyb hFxb (hpos m hm)
          (le_of_eq (hlamu m hm))
          (by rw [add_sub_cancel_left, map_mul, hnodeb, hσu m hm, one_mul])
          (le_of_eq hnodeb) (ykf m)
      have hw : A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluWSum
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet
              (Point.some xQ yQ hQns) (p / 2))
          - (x₀ * ((((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ + 12 * x₀) ^ 2
                * ((∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2)
                  + 6 * ∑ k ∈ Finset.Icc 1 (p / 2),
                      (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2))
              + (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ + 12 * x₀) ^ 3
                * (2 * (∑ k ∈ Finset.Icc 1 (p / 2),
                    (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
                  + 10 * ∑ k ∈ Finset.Icc 1 (p / 2),
                      (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3))) < 1 := by
        rw [QD1dpAux.veluWSum_eq_sum_Icc _ hQord h2n hkQf',
          ← QD1dpAux.ideal_wsum_eq (p := p) ζ x₀
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ + 12 * x₀)]
        refine QD1dpAux.val_sum_sub_lt_one A (fun m hm => ?_)
        exact QD1dpAux.val_veluW_sub_ideal_lt_one A _ hFyb hFxb (hcur m hm) (hpos m hm) hx₀v
          (le_of_eq hnodeb) (le_of_eq (hlamu m hm))
          (by rw [add_sub_cancel_left, map_mul, hnodeb, hσu m hm, one_mul]) hεb

      have hzpin : A.valuation ((u : AlgebraicClosure ℚ) ^ 2 * x₀' - x₀
          - (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂ + 12 * x₀)
              * ((p : AlgebraicClosure ℚ) ^ 2 - 1) / 12) < 1 :=
        QD1dpAux.toric_z_pin A _ _ hp hp2 hζ hFyb hFxb hFyV' hFxV' hc₄V hx₀v hb₂b hμI
          ht hw hεV hεb

      have hzI : A.valuation ((u : AlgebraicClosure ℚ) ^ 2 * x₀') ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (QD1dpAux.zcentre_mem A u hu hx₀' hy₀').1

      rw [QD1dpAux.veluX_eq_sum_Icc _ hQord h2n hkQf']

      by_cases hxA : x ∈ A
      · have hxle : A.valuation (x - x₀) ≤ 1 := (A.valuation_le_one_iff _).mpr (sub_mem hxA hx₀)
        rcases lt_or_eq_of_le hxle with hxlow | hxu
        ·
          exact iff_of_true (QD1dpAux.toric_master_low A _ hp hp2 hζ hFyb hFxb hnodeb hcur hpos
            hσu hlamu hxlow hεb hzpin) hxlow
        ·
          refine iff_of_false ?_ (by rw [hxu]; exact lt_irrefl 1)
          by_cases hcol : ∃ K ∈ Finset.Icc 1 (p / 2), A.valuation (x - xkf K) < 1
          ·
            obtain ⟨K, hKmem, hcolK⟩ := hcol
            have hxneK : x ≠ xkf K := by
              intro heq
              exact hL (QD1dpAux.mem_zmultiples_of_x_eq W (hkQf' K hKmem) heq)
            exact QD1dpAux.toric_master_pole A _ hFyb hFxb hnodeb hx₀v hcur hpos hlamu hKmem
              (fun m hm hne =>
                QD1dpAux.val_sigma_sub_sigma_eq_one A hp hp2 hvζ hU hKmem hm (Ne.symm hne))
              (QD1dpAux.val_one_add_four_sigma_eq_one' A hp hp2 hU hKmem)
              hcolK hxneK hzI hεb
          ·
            simp only [not_exists, not_and, not_lt] at hcol
            have hdk : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (x - xkf m) = 1 := fun m hm => by
              have hle' : A.valuation (x - xkf m) ≤ 1 :=
                (A.valuation_le_one_iff _).mpr (sub_mem hxA (hint m (hsub m hm)))
              exact le_antisymm hle' (hcol m hm)
            exact QD1dpAux.toric_master_unit A _ hp hp2 hζ hFyb hFxb hnodeb hcur hpos
              (fun m hm => le_of_eq (hσu m hm)) hxu hdk hεb hzpin
      ·
        have hxv : 1 < A.valuation x := by
          have h := (A.valuation_le_one_iff x).not.mpr hxA
          exact lt_of_not_ge h
        have hvXsub : 1 < A.valuation (x - x₀) := by
          rw [Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt hx₀v hxv)]; exact hxv
        refine iff_of_false (not_lt_of_ge ?_) (not_lt_of_gt hvXsub)
        have hintk : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xkf m) ≤ 1 := fun m hm =>
          (A.valuation_le_one_iff _).mpr (hint m (hsub m hm))
        have hyk : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (ykf m) ≤ 1 := fun m hm =>
          (A.valuation_le_one_iff _).mpr (QD1dpAux.toric_kernel_unit W A hx₀ hy₀ hFy hFx hnode
            hbad hQc m (hkQf' m hm) (hint m (hsub m hm))).2
        have hvf := QD1dpAux.val_veluX_formal W A (Finset.Icc 1 (p / 2)) hintk hyk hxv
        rw [Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt hzI (hvf ▸ hxv))]
        exact le_of_lt (hvf ▸ hxv)
    ·
      exact absurd hc₄V
        (fun h1 => QD1dpAux.toric_caseA_absurd W hΔ hq hqΔ hqc₄ A hA hp hp2 hQns hQord hxQA h1)
  ·

    have hlam : ∀ m ∈ Finset.Icc 1 (p / 2), A.valuation (xk m - x₀) < 1 := by
      intro m hm
      have hm' := Finset.mem_Icc.mp hm
      exact (QD1dpAux.kernel_level W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2
        hQord hQc hm'.1 (by omega) (hkQ m hm)).1
    have hshk : ∀ m ∈ Finset.Icc 1 (p / 2),
        A.valuation (y₀ ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (xk m - x₀) ^ 2 := by
      intro m hm
      have hm' := Finset.mem_Icc.mp hm
      exact (QD1dpAux.kernel_level W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2
        hQord hQc hm'.1 (by omega) (hkQ m hm)).2

    have hanchor : A.valuation ((u : AlgebraicClosure ℚ) ^ 2 * x₀' - x₀) < 1 := by

      have ht : A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluTSum
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))) < 1 := by
        rw [QD1dpAux.veluTSum_eq_sum_Icc _ hQord h2n hkQ]
        exact QD1dpAux.val_sum_veluT_lt_one A _ hFyb hFxb hb₂b hx₀v _ xk yk hlam
      have heqk : ∀ m ∈ Finset.Icc 1 (p / 2),
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Equation (xk m) (yk m) :=
        fun m hm => (hk m hm).1
      have hw : A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluWSum
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))) < 1 := by
        rw [QD1dpAux.veluWSum_eq_sum_Icc _ hQord h2n hkQ]
        exact QD1dpAux.val_sum_veluW_lt_one A _ hFyb hFxb hb₂b hx₀v hεb _ xk yk heqk hlam

      exact QD1dpAux.anchor_val_lt_one A _ _ hFyb hFxb hFyV' hFxV' hc₄V hx₀v hb₂b ht hw hεV hεb

    have hcrit : ¬ W'.InZeroComponentAt A (.some _ _ h')
        ↔ A.valuation (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) x
              - x₀) < 1 :=
      (QD1dpAux.not_lhs_iff W W' A u hu hx₀' hy₀' hFy' hFx' hnode' hbad' x y h').trans
        (QD1dpAux.val_sub_lt_one_congr A.valuation hanchor)

    exact QD1dpAux.nt_endgame W A hq hΔ hqΔ hqc₄ hA hx₀ hy₀ hFy hFx hnode hbad hp hp2 hQord hQc
      hkQ h hL _ hcrit
      (fun hxne hne hX => QD1dpAux.master_off_wrap W A hQord h2n hFy hFx hnode
        hkQ hlam hshk hxne hne hX)
      (fun hxne m hm heq hne' => QD1dpAux.master_on_wrap W A hQord h2n hFy hFx hnode
        hkQ hlam hshk hxne hm heq hne')
      (fun hunit => QD1dpAux.master_unit_wrap W A hQord h2n hFy hFx hnode
        hkQ hlam hshk hunit)
      (fun hxA => QD1dpAux.master_formal_wrap W A hQord h2n hx₀ hkQ hlam hxA)

end S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative
end P2MW
export P2MW.S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative (solution)
