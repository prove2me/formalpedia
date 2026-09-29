-- Prove2me | solution 1 for WeierstrassCurve.comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/39c653a5-efa5-51ad-af80-228f7075171c

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_forall_mem_zmultiples_of_char_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ toAffine Affine.Point Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed exists_isDualPair_of_mem_rationalHomSet exists_forall_mem_zmultiples_of_char_nsmul_eq_zero"
namespace OrdinaryEndComm
p2m_open "WeierstrassCurve"

section HomSet

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented k W W (-(AddMonoidHom.id _)) := by
  refine ⟨C X, 1, -X - C (C W.a₁ * X + C W.a₃), 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C X : F[X][Y]) x y = x := by simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC k (-X - C (C W.a₁ * X + C W.a₃) : F[X][Y]) x y =
      (W.baseChange k).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

theorem neg_id_mem_rationalHomSet (W : WeierstrassCurve F) :
    (-(AddMonoidHom.id _) : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  Or.inr (isRationallyRepresented_neg_id k W)

variable {k}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) : -α ∈ rationalHomSet k W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet k W₁ W₂ W₂ hα (neg_id_mem_rationalHomSet k W₂)
  have e : (-(AddMonoidHom.id _)).comp α = -α := by ext P; simp
  rwa [e] at h

variable [IsAlgClosed k]

theorem sub_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hβ : β ∈ rationalHomSet k W₁ W₂) :
    α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet hβ)

theorem zsmul_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (n : ℤ) : n • α ∈ rationalHomSet k W₁ W₂ := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih =>
    rw [add_zsmul, one_zsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact sub_mem_rationalHomSet ih hα

theorem zsmul_id_mem_rationalHomSet (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ) :
    (n • AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  zsmul_mem_rationalHomSet (id_mem_rationalHomSet k W) n

end HomSet

section Torsion

variable (k : Type*) [Field k]

theorem exists_prime_gt_natCast_ne_zero (M : ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ M < ℓ ∧ (ℓ : k) ≠ 0 := by
  obtain ⟨ℓ₁, h₁, hp₁⟩ := Nat.exists_infinite_primes (M + 1)
  obtain ⟨ℓ₂, h₂, hp₂⟩ := Nat.exists_infinite_primes (ℓ₁ + 1)
  by_cases hz₁ : (ℓ₁ : k) = 0
  · refine ⟨ℓ₂, hp₂, by omega, fun hz₂ => ?_⟩
    have d₁ : ringChar k ∣ ℓ₁ := (ringChar.spec k ℓ₁).mp hz₁
    have d₂ : ringChar k ∣ ℓ₂ := (ringChar.spec k ℓ₂).mp hz₂
    have hne : ℓ₁ ≠ ℓ₂ := by omega
    have hcop : Nat.Coprime ℓ₁ ℓ₂ := (Nat.coprime_primes hp₁ hp₂).mpr hne
    have h1 : ringChar k ∣ 1 := by
      have := Nat.dvd_gcd d₁ d₂
      rwa [hcop] at this
    exact absurd (Nat.dvd_one.mp h1) (CharP.ringChar_ne_one)
  · exact ⟨ℓ₁, hp₁, by omega, hz₁⟩

variable {k} [DecidableEq k] [IsAlgClosed k]

theorem exists_ne_zero_zsmul_eq_zero (W : WeierstrassCurve k) [W.IsElliptic] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) : ∃ Q : W.toAffine.Point, Q ≠ 0 ∧ (ℓ : ℤ) • Q = 0 := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ : ℤ)) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hℓk
  set Tor := Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ : ℤ)
  haveI : Finite Tor := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hnt : Nontrivial Tor := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hℓ.one_lt
  obtain ⟨⟨R, hR⟩, hR1⟩ := exists_ne (0 : Tor)
  exact ⟨R, fun h => hR1 (Subtype.ext h), (Submodule.mem_torsionBy_iff _ _).mp hR⟩

theorem eq_zero_of_prime_zsmul_of_zsmul {G : Type*} [AddCommGroup G] {Q : G} {ℓ : ℕ}
    (hℓ : ℓ.Prime) {N : ℤ} (hN : N ≠ 0) (hlt : N.natAbs < ℓ) (h1 : (ℓ : ℤ) • Q = 0)
    (h2 : N • Q = 0) : Q = 0 := by
  have hcop : IsCoprime (ℓ : ℤ) N := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd (ℓ : ℤ) N ∣ ℓ := by
      have := Int.gcd_dvd_left (ℓ : ℤ) N
      exact_mod_cast this
    rcases (Nat.dvd_prime hℓ).mp h1 with h | h
    · exact h
    · exfalso
      have h2 : ((Int.gcd (ℓ : ℤ) N : ℕ) : ℤ) ∣ N := Int.gcd_dvd_right _ _
      rw [h] at h2
      have h3 : ℓ ∣ N.natAbs := Int.natCast_dvd.mp h2
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h3
      omega
  obtain ⟨a, b, hab⟩ := hcop
  calc Q = (1 : ℤ) • Q := (one_zsmul Q).symm
    _ = (a * ℓ + b * N) • Q := by rw [hab]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, h1, h2, zsmul_zero, zsmul_zero, add_zero]

theorem zsmul_id_ne_zero (W : WeierstrassCurve k) [W.IsElliptic] {N : ℤ} (hN : N ≠ 0) :
    (N • AddMonoidHom.id _ : W.toAffine.Point →+ W.toAffine.Point) ≠ 0 := by
  intro h
  obtain ⟨ℓ, hℓ, hNℓ, hℓk⟩ := exists_prime_gt_natCast_ne_zero k N.natAbs
  obtain ⟨Q, hQ0, hQℓ⟩ := exists_ne_zero_zsmul_eq_zero W hℓ hℓk
  have hNQ : N • Q = 0 := by
    have := DFunLike.congr_fun h Q
    simpa using this
  exact hQ0 (eq_zero_of_prime_zsmul_of_zsmul hℓ hN hNℓ hQℓ hNQ)

theorem exists_zsmul_eq (W : WeierstrassCurve k) [W.IsElliptic] {N : ℤ} (hN : N ≠ 0)
    (Q : W.toAffine.Point) : ∃ P : W.toAffine.Point, N • P = Q := by
  obtain ⟨P, hP⟩ : ∃ P : W.toAffine.Point, (N • AddMonoidHom.id _ : W.toAffine.Point →+ _) P = Q :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k
      (zsmul_id_mem_rationalHomSet (k := k) W N) (zsmul_id_ne_zero W hN) Q
  exact ⟨P, by exact hP⟩

end Torsion

section Tower

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
  (W : WeierstrassCurve k) [W.IsElliptic] (T : W.toAffine.Point)

def tower : ℕ → W.toAffine.Point
  | 0 => T
  | n + 1 => Classical.choose
      (exists_zsmul_eq (k := k) W (N := (p : ℤ)) (by exact_mod_cast hp.out.ne_zero) (tower n))

theorem tower_zero : tower p W T 0 = T := rfl

theorem p_zsmul_tower_succ (n : ℕ) : (p : ℤ) • tower p W T (n + 1) = tower p W T n :=
  Classical.choose_spec
    (exists_zsmul_eq (k := k) W (N := (p : ℤ)) (by exact_mod_cast hp.out.ne_zero) (tower p W T n))

theorem p_nsmul_tower_succ (n : ℕ) : p • tower p W T (n + 1) = tower p W T n := by
  rw [← natCast_zsmul]; exact p_zsmul_tower_succ p W T n

theorem pow_nsmul_tower (n : ℕ) : p ^ n • tower p W T n = T := by
  induction n with
  | zero => simp [tower_zero]
  | succ n ih => rw [pow_succ, mul_comm, mul_nsmul, p_nsmul_tower_succ, ih]

variable {T} (hT : T ≠ 0) (hpT : p • T = 0)
include hpT

theorem pow_succ_nsmul_tower (n : ℕ) : p ^ (n + 1) • tower p W T n = 0 := by
  rw [pow_succ', mul_comm, mul_nsmul, pow_nsmul_tower, hpT]

include hT

theorem addOrderOf_tower (n : ℕ) : addOrderOf (tower p W T n) = p ^ (n + 1) := by
  refine addOrderOf_eq_prime_pow (fun h => hT ?_) (pow_succ_nsmul_tower p W hpT n)
  rw [← pow_nsmul_tower p W T n]; exact h

theorem mem_zmultiples_of_p_nsmul_eq_zero {P : W.toAffine.Point} (hP : p • P = 0) :
    P ∈ AddSubgroup.zmultiples T := by
  obtain ⟨T₀, hT₀, hgen⟩ :=
    WeierstrassCurve.exists_forall_mem_zmultiples_of_char_nsmul_eq_zero p W

  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen T hpT)
  have hpa : ¬ (p : ℤ) ∣ a := by
    rintro ⟨c, rfl⟩
    apply hT
    rw [← ha, mul_comm, mul_zsmul, natCast_zsmul, hT₀, zsmul_zero]

  have hcop : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd a p ∣ p := by
      have := Int.gcd_dvd_right a (p : ℤ)
      exact_mod_cast this
    rcases (Nat.dvd_prime hp.out).mp h1 with h | h
    · exact h
    · exfalso; apply hpa
      have h2 : ((Int.gcd a p : ℕ) : ℤ) ∣ a := Int.gcd_dvd_left _ _
      rwa [h] at h2
  obtain ⟨b, c, hbc⟩ := hcop
  have hT₀T : T₀ = b • T := by
    calc T₀ = (1 : ℤ) • T₀ := (one_zsmul _).symm
      _ = (b * a + c * p) • T₀ := by rw [hbc]
      _ = b • T := by
        rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, hT₀, zsmul_zero, add_zero, ha]
  obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen P hP)
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨d * b, ?_⟩
  rw [mul_zsmul, ← hT₀T, hd]

theorem mem_zmultiples_tower {n : ℕ} {P : W.toAffine.Point} (hP : p ^ (n + 1) • P = 0) :
    P ∈ AddSubgroup.zmultiples (tower p W T n) := by
  induction n generalizing P with
  | zero =>
    rw [zero_add, pow_one] at hP
    exact mem_zmultiples_of_p_nsmul_eq_zero p W hT hpT hP
  | succ n ih =>

    have h1 : p ^ (n + 1) • (p • P) = 0 := by
      rw [← mul_nsmul', ← pow_succ, hP]
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (ih h1)

    have h2 : p • (P - a • tower p W T (n + 1)) = 0 := by
      rw [nsmul_sub, ← ha, ← p_nsmul_tower_succ p W T n, smul_comm, sub_self]
    have h3 := mem_zmultiples_of_p_nsmul_eq_zero p W hT hpT h2

    have hTmem : T ∈ AddSubgroup.zmultiples (tower p W T (n + 1)) := by
      have e := pow_nsmul_tower p W T (n + 1)
      have hmem : p ^ (n + 1) • tower p W T (n + 1) ∈ AddSubgroup.zmultiples (tower p W T (n + 1)) :=
        AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _
      rwa [e] at hmem
    have h4 : P - a • tower p W T (n + 1) ∈ AddSubgroup.zmultiples (tower p W T (n + 1)) :=
      (AddSubgroup.zmultiples_le_of_mem hTmem) h3
    have h5 : a • tower p W T (n + 1) ∈ AddSubgroup.zmultiples (tower p W T (n + 1)) :=
      AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
    have := AddSubgroup.add_mem _ h4 h5
    rwa [sub_add_cancel] at this

theorem exists_apply_tower_eq_zsmul (φ : W.toAffine.Point →+ W.toAffine.Point) (n : ℕ) :
    ∃ a : ℤ, φ (tower p W T n) = a • tower p W T n := by
  have h : p ^ (n + 1) • φ (tower p W T n) = 0 := by
    rw [← map_nsmul, pow_succ_nsmul_tower p W hpT n, map_zero]
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (mem_zmultiples_tower p W hT hpT h)
  exact ⟨a, ha.symm⟩

theorem comm_apply_tower (α β : W.toAffine.Point →+ W.toAffine.Point) (n : ℕ) :
    α (β (tower p W T n)) = β (α (tower p W T n)) := by
  obtain ⟨a, ha⟩ := exists_apply_tower_eq_zsmul p W hT hpT α n
  obtain ⟨b, hb⟩ := exists_apply_tower_eq_zsmul p W hT hpT β n
  rw [hb, map_zsmul, ha, map_zsmul, hb, smul_comm]

end Tower

section Main

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
  (W : WeierstrassCurve k) [W.IsElliptic]

theorem main {T : W.toAffine.Point} (hT : T ≠ 0) (hpT : p • T = 0)
    {α β : W.toAffine.Point →+ W.toAffine.Point}
    (hα : α ∈ rationalHomSet k W W) (hβ : β ∈ rationalHomSet k W W) : α.comp β = β.comp α := by

  set δ : W.toAffine.Point →+ W.toAffine.Point := α.comp β - β.comp α with hδ
  have hδmem : δ ∈ rationalHomSet k W W :=
    sub_mem_rationalHomSet (WeierstrassCurve.comp_mem_rationalHomSet k W W W hβ hα)
      (WeierstrassCurve.comp_mem_rationalHomSet k W W W hα hβ)
  have hδT : ∀ n, δ (tower p W T n) = 0 := fun n => by
    simp only [hδ, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, comm_apply_tower p W hT hpT α β n,
      sub_self]
  suffices h0 : δ = 0 by
    have := h0; rw [hδ] at this; exact eq_of_sub_eq_zero this
  by_contra hδ0
  obtain ⟨σ, -, N, hN, hdual⟩ :
      ∃ σ ∈ rationalHomSet k W W, ∃ N : ℤ, 0 < N ∧ AddMonoidHom.IsDualPair δ σ N :=
    WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet k W W hδmem hδ0

  have hNT : ∀ n, N • tower p W T n = 0 := fun n => by
    rw [← hdual.comp_left (tower p W T n), hδT n, map_zero]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N.natAbs < p ^ (n + 1) := ⟨N.natAbs, by
    calc N.natAbs < p ^ N.natAbs := Nat.lt_pow_self hp.out.one_lt
      _ ≤ p ^ (N.natAbs + 1) := Nat.pow_le_pow_right hp.out.pos (Nat.le_succ _)⟩
  have hdvd : (addOrderOf (tower p W T n) : ℤ) ∣ N :=
    (addOrderOf_dvd_iff_zsmul_eq_zero).mpr (hNT n)
  rw [addOrderOf_tower p W hT hpT n] at hdvd
  have h1 : p ^ (n + 1) ∣ N.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hN.ne') h1
  omega

end Main

end WeierstrassCurve.OrdinaryEndComm

end

theorem solution {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic] {T : W.toAffine.Point} (hT : T ≠ 0) (hpT : p • T = 0) {α β : W.toAffine.Point →+ W.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W W) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) : α.comp β = β.comp α :=
  WeierstrassCurve.OrdinaryEndComm.main p W hT hpT hα hβ

end S_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero (solution)
