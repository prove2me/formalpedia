-- Prove2me | solution 1 for WeierstrassCurve.eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a2f1648c-4f5b-58ce-8de2-865c82162c38

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id
import Theorems.Thm_WeierstrassCurve_finite_rationalHomSet_units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ toAffine Affine.Point Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id finite_rationalHomSet_units"
namespace LevelRigidity
p2m_open "WeierstrassCurve"

variable {A : Type*} [AddCommGroup A]

theorem sub_apply' (f g : AddMonoid.End A) (a : A) : (f - g) a = f a - g a := rfl
theorem mul_apply' (f g : AddMonoid.End A) (a : A) : (f * g) a = f (g a) := rfl
theorem one_apply' (a : A) : (1 : AddMonoid.End A) a = a := rfl

theorem finsetSum_apply' {ι : Type*} (s : Finset ι) (f : ι → AddMonoid.End A) (a : A) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih]; rfl

theorem pow_apply_of_apply_eq {ε : AddMonoid.End A} {a : A} (h : ε a = a) :
    ∀ m : ℕ, (ε ^ m) a = a
  | 0 => by simp
  | m + 1 => by rw [pow_succ, mul_apply', h, pow_apply_of_apply_eq h m]

abbrev T (A : Type*) [AddCommGroup A] (N : ℕ) : Submodule ℤ A := Submodule.torsionBy ℤ A (N : ℤ)

theorem mem_T {N : ℕ} {a : A} : a ∈ T A N ↔ (N : ℤ) • a = 0 := Submodule.mem_torsionBy_iff _ _

structure Setup (A : Type*) [AddCommGroup A] where
  S : Subring (AddMonoid.End A)
  good : ℕ → Prop
  good_pos : ∀ {N}, good N → 0 < N
  good_mul : ∀ {M N}, good M → good N → good (M * N)
  good_dvd : ∀ {M N}, M ∣ N → good N → good M
  surj : ∀ {s}, s ∈ S → s ≠ 0 → Function.Surjective s
  dvd : ∀ {N}, good N → ∀ {s}, s ∈ S → (∀ a, (N : ℤ) • a = 0 → s a = 0) →
    ∃ s' ∈ S, ∀ a, s a = (N : ℤ) • s' a
  kerBound : ∀ {s}, s ∈ S → s ≠ 0 → ∃ n : ℤ, 0 < n ∧ ∀ a, s a = 0 → n • a = 0
  card : ∀ {N}, good N → Nat.card (T A N) = N ^ 2
  finU : {u : AddMonoid.End A | u ∈ S ∧ ∃ v ∈ S, u * v = 1 ∧ v * u = 1}.Finite

namespace Setup

variable (X : Setup A)

theorem good_pow {N : ℕ} (hN : X.good N) : ∀ j : ℕ, X.good (N ^ j)
  | 0 => by simpa using X.good_dvd (one_dvd N) hN
  | j + 1 => by rw [pow_succ]; exact X.good_mul (good_pow hN j) hN

theorem finite_T {N : ℕ} (hN : X.good N) : Finite (T A N) := by
  have h := X.card hN
  exact Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero 2 (X.good_pos hN).ne')

theorem eq_zero_of_mul_eq_zero {s t : AddMonoid.End A} (ht : t ∈ X.S) (h : s * t = 0)
    (ht0 : t ≠ 0) : s = 0 := by
  ext b
  obtain ⟨a, rfl⟩ := X.surj ht ht0 b
  have := DFunLike.congr_fun h a
  simpa using this

theorem dvd_of_torsion_le {P : ℕ} (hP : X.good P) {m : ℤ}
    (h : ∀ a : A, (P : ℤ) • a = 0 → m • a = 0) : (P : ℤ) ∣ m := by

  set g : ℕ := Int.gcd m P with hg
  have hgP : g ∣ P := by
    have := Int.gcd_dvd_right m P
    exact_mod_cast this
  have hgood : X.good g := X.good_dvd hgP hP
  have hle : T A P ≤ T A g := by
    intro a ha
    rw [mem_T] at ha ⊢
    have hb := Int.gcd_eq_gcd_ab m P
    rw [show ((g : ℕ) : ℤ) = (Int.gcd m P : ℤ) from rfl, hb, add_zsmul, mul_comm m, mul_zsmul, h a ha,
      mul_comm (P : ℤ), mul_zsmul, ha, zsmul_zero, zsmul_zero, add_zero]
  haveI := X.finite_T hgood
  have hcard : Nat.card (T A P) ≤ Nat.card (T A g) :=
    Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hle)
  rw [X.card hP, X.card hgood] at hcard
  have hPg : P ≤ g := by
    by_contra hlt
    push Not at hlt
    have := Nat.pow_lt_pow_left hlt (two_ne_zero)
    omega
  have hgP' : g ≤ P := Nat.le_of_dvd (X.good_pos hP) hgP
  have hgeq : g = P := le_antisymm hgP' hPg
  have : (g : ℤ) ∣ m := by
    have := Int.gcd_dvd_left m P
    exact_mod_cast this
  rwa [hgeq] at this

theorem eq_zero_of_forall_torsion_pow {N : ℕ} (hN : X.good N) (hN2 : 2 ≤ N) {s : AddMonoid.End A}
    (hs : s ∈ X.S) (h : ∀ M : ℕ, ∀ a : A, ((N ^ M : ℕ) : ℤ) • a = 0 → s a = 0) : s = 0 := by
  by_contra hs0
  obtain ⟨n, hn, hker⟩ := X.kerBound hs hs0
  have hdvd : ((N ^ n.toNat : ℕ) : ℤ) ∣ n :=
    X.dvd_of_torsion_le (X.good_pow hN _) fun a ha => hker a (h _ a ha)
  have hle : ((N ^ n.toNat : ℕ) : ℤ) ≤ n := Int.le_of_dvd hn hdvd
  have hlt : n.toNat < N ^ n.toNat := Nat.lt_pow_self (by omega)
  omega

theorem exists_pow_apply_eq_add {Q N : ℕ} (hQ : X.good Q) (hNQ : N ∣ Q) {ε : AddMonoid.End A}
    (hε : ε ∈ X.S) (hfix : ∀ a : A, (Q : ℤ) • a = 0 → ε a = a)
    (a : A) (ha : ((Q * N : ℕ) : ℤ) • a = 0) :
    ∃ R : A, (N : ℤ) • R = 0 ∧ ∀ i : ℕ, (ε ^ i) a = a + (i : ℤ) • R := by

  have hkill : ∀ a : A, (Q : ℤ) • a = 0 → (ε - 1) a = 0 := fun a ha => by
    rw [sub_apply', one_apply', hfix a ha, sub_self]
  obtain ⟨γ, -, hγ⟩ := X.dvd hQ (X.S.sub_mem hε X.S.one_mem) hkill
  set R : A := γ ((Q : ℤ) • a) with hR

  have hεa : ε a = a + R := by
    have h1 : (ε - 1) a = (Q : ℤ) • γ a := hγ a
    rw [hR, map_zsmul, ← h1, sub_apply', one_apply']; abel

  have hRN : (N : ℤ) • R = 0 := by
    have h : (N : ℤ) • (Q : ℤ) • a = 0 := by rw [smul_smul, ← Nat.cast_mul, Nat.mul_comm]; exact ha
    rw [hR, ← map_zsmul, h, map_zero]
  have hRQ : (Q : ℤ) • R = 0 := by
    obtain ⟨c, rfl⟩ := hNQ
    rw [Nat.cast_mul, mul_comm, mul_zsmul, hRN, zsmul_zero]
  have hεR : ε R = R := hfix R hRQ
  refine ⟨R, hRN, fun i => ?_⟩
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, mul_apply', hεa, map_add, ih, pow_apply_of_apply_eq hεR i]
    push_cast
    rw [add_zsmul, one_zsmul]
    abel

theorem pow_apply_eq_of_apply_eq {Q N : ℕ} (hQ : X.good Q) (hNQ : N ∣ Q) {ε : AddMonoid.End A}
    (hε : ε ∈ X.S) (hfix : ∀ a : A, (Q : ℤ) • a = 0 → ε a = a) :
    ∀ a : A, ((Q * N : ℕ) : ℤ) • a = 0 → (ε ^ N) a = a := by
  intro a ha
  obtain ⟨R, hRN, hiter⟩ := X.exists_pow_apply_eq_add hQ hNQ hε hfix a ha
  rw [hiter N, hRN, add_zero]

theorem pow_pow_apply_eq {N : ℕ} (hN : X.good N) {ε : AddMonoid.End A} (hε : ε ∈ X.S)
    (hfix : ∀ a : A, (N : ℤ) • a = 0 → ε a = a) :
    ∀ j : ℕ, ∀ a : A, ((N ^ (j + 1) : ℕ) : ℤ) • a = 0 → (ε ^ (N ^ j)) a = a
  | 0 => by simpa using hfix
  | j + 1 => by
    intro a ha
    have ih := pow_pow_apply_eq hN hε hfix j
    have h := X.pow_apply_eq_of_apply_eq (X.good_pow hN (j + 1))
      (dvd_pow_self N (Nat.succ_ne_zero j)) (X.S.pow_mem hε _) ih a (by simpa [pow_succ] using ha)
    rwa [← pow_mul, ← pow_succ] at h

theorem eq_one_of_pow_eq_one {N : ℕ} (hN : X.good N) (hN3 : 3 ≤ N) {η : AddMonoid.End A}
    (hη : η ∈ X.S) (hpow : η ^ N = 1) (hfix : ∀ a : A, (N : ℤ) • a = 0 → η a = a) : η = 1 := by
  by_contra hne

  set Φ : AddMonoid.End A := ∑ i ∈ Finset.range N, η ^ i with hΦ
  have hΦmul : Φ * (η - 1) = 0 := by rw [hΦ, geom_sum_mul, hpow, sub_self]
  have hΦ0 : Φ = 0 :=
    X.eq_zero_of_mul_eq_zero (X.S.sub_mem hη X.S.one_mem) hΦmul (sub_ne_zero.mpr hne)

  set s : ℤ := ∑ i ∈ Finset.range N, (i : ℤ) with hs
  have h2s : 2 * s = (N : ℤ) * ((N : ℤ) - 1) := by
    have h := Finset.sum_range_id_mul_two N
    have h1 : (1 : ℕ) ≤ N := by omega
    have h' : ((∑ i ∈ Finset.range N, i : ℕ) : ℤ) * 2 = (N : ℤ) * ((N - 1 : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [Nat.cast_sum, Nat.cast_sub h1] at h'
    push_cast at h'
    rw [hs]; linarith

  have hkey : ∀ a : A, ((N ^ 2 : ℕ) : ℤ) • a = 0 → ((2 * N : ℕ) : ℤ) • a = 0 := by
    intro a ha
    obtain ⟨R, hRN, hiter⟩ :=
      X.exists_pow_apply_eq_add hN (dvd_refl N) hη hfix a (by simpa [sq] using ha)
    have hΦa : Φ a = (N : ℤ) • a + s • R := by
      rw [hΦ, finsetSum_apply', Finset.sum_congr rfl fun i _ => hiter i, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, ← Finset.sum_smul, ← hs, natCast_zsmul]
    have hzero : (N : ℤ) • a + s • R = 0 := by rw [← hΦa, hΦ0]; rfl
    have h2sR : (2 * s) • R = 0 := by
      rw [h2s, mul_comm, mul_smul, hRN, smul_zero]
    have hNa : (N : ℤ) • a = -(s • R) := eq_neg_of_add_eq_zero_left hzero
    calc ((2 * N : ℕ) : ℤ) • a = (2 : ℤ) • (N : ℤ) • a := by push_cast; rw [mul_smul]
      _ = -((2 * s) • R) := by rw [hNa, smul_neg, smul_smul]
      _ = 0 := by rw [h2sR, neg_zero]
  have hdvd := X.dvd_of_torsion_le (X.good_pow hN 2) hkey

  have hdvd' : N * N ∣ 2 * N := by rw [← sq]; exact_mod_cast hdvd
  have hN2 : N ∣ 2 := (Nat.mul_dvd_mul_iff_right (by omega : 0 < N)).mp hdvd'
  have := Nat.le_of_dvd two_pos hN2
  omega

theorem exists_pow_pow_eq_one {N : ℕ} (hN : X.good N) (hN2 : 2 ≤ N) {ε ε' : AddMonoid.End A}
    (hε : ε ∈ X.S) (hε' : ε' ∈ X.S) (h₁ : ε' * ε = 1) (h₂ : ε * ε' = 1)
    (hfix : ∀ a : A, (N : ℤ) • a = 0 → ε a = a) : ∃ j : ℕ, ε ^ (N ^ j) = 1 := by
  set U : Set (AddMonoid.End A) := {u | u ∈ X.S ∧ ∃ v ∈ X.S, u * v = 1 ∧ v * u = 1} with hU
  haveI : Finite U := X.finU.to_subtype
  have hmem : ∀ m : ℕ, ε ^ m ∈ U := fun m =>
    ⟨X.S.pow_mem hε m, ε' ^ m, X.S.pow_mem hε' m, pow_mul_pow_eq_one m h₂, pow_mul_pow_eq_one m h₁⟩
  let f : ℕ → U := fun j => ⟨ε ^ (N ^ j), hmem _⟩
  obtain ⟨j, j', hne, hjj⟩ := Finite.exists_ne_map_eq_of_infinite f
  have heq : ε ^ (N ^ j) = ε ^ (N ^ j') := congrArg Subtype.val hjj
  wlog hlt : j < j' generalizing j j'
  · exact this j' j hne.symm hjj.symm heq.symm (by omega)
  refine ⟨j, ?_⟩
  set θ : AddMonoid.End A := ε ^ (N ^ j) with hθ
  obtain ⟨d, rfl⟩ : ∃ d, j' = j + d := ⟨j' - j, by omega⟩
  have hd : 0 < d := by omega

  have hperiod : ∀ k : ℕ, ε ^ (N ^ (j + k * d)) = θ := by
    intro k
    induction k with
    | zero => simp [hθ]
    | succ k ih =>
      have e1 : ε ^ (N ^ (j + (k + 1) * d)) = (ε ^ (N ^ (j + k * d))) ^ (N ^ d) := by
        rw [← pow_mul, ← pow_add]; congr 2; ring
      have e2 : θ ^ (N ^ d) = ε ^ (N ^ (j + d)) := by rw [hθ, ← pow_mul, ← pow_add]
      rw [e1, ih, e2, ← heq]

  have hfixall : ∀ M : ℕ, ∀ a : A, ((N ^ M : ℕ) : ℤ) • a = 0 → (θ - 1) a = 0 := by
    intro M a ha
    have hle : M ≤ j + M * d + 1 := by nlinarith
    obtain ⟨c, hc⟩ := pow_dvd_pow N hle
    have ha' : ((N ^ (j + M * d + 1) : ℕ) : ℤ) • a = 0 := by
      rw [hc, Nat.cast_mul, mul_comm, mul_smul, ha, smul_zero]
    have h := X.pow_pow_apply_eq hN hε hfix (j + M * d) a ha'
    rw [hperiod] at h
    rw [sub_apply', one_apply', h, sub_self]
  have h0 := X.eq_zero_of_forall_torsion_pow hN hN2 (X.S.sub_mem (X.S.pow_mem hε _) X.S.one_mem) hfixall
  exact sub_eq_zero.mp h0

theorem eq_one_of_forall_apply_eq {N : ℕ} (hN : X.good N) (hN3 : 3 ≤ N) {ε ε' : AddMonoid.End A}
    (hε : ε ∈ X.S) (hε' : ε' ∈ X.S) (h₁ : ε' * ε = 1) (h₂ : ε * ε' = 1)
    (hfix : ∀ a : A, (N : ℤ) • a = 0 → ε a = a) : ε = 1 := by
  obtain ⟨j, hj⟩ := X.exists_pow_pow_eq_one hN (by omega) hε hε' h₁ h₂ hfix

  suffices H : ∀ i : ℕ, ε ^ (N ^ (j - i)) = 1 by simpa using H j
  intro i
  induction i with
  | zero => simpa using hj
  | succ i ih =>
    rcases Nat.lt_or_ge i j with hi | hi
    · have e : j - i = (j - (i + 1)) + 1 := by omega
      rw [e, pow_succ, pow_mul] at ih
      exact X.eq_one_of_pow_eq_one hN hN3 (X.S.pow_mem hε _) ih
        fun a ha => pow_apply_of_apply_eq (hfix a ha) _
    · have e : j - (i + 1) = j - i := by omega
      rw [e]; exact ih

end Setup

section Instantiate

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

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

variable {k} in
theorem neg_mem_rationalHomSet {W : WeierstrassCurve F}
    {α : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W W) : -α ∈ rationalHomSet k W W := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet k W W W hα
    (Or.inr (isRationallyRepresented_neg_id k W))
  have e : (-(AddMonoidHom.id _)).comp α = -α := by ext P; simp
  rwa [e] at h

variable [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic]

def homSubring : Subring (AddMonoid.End (W.baseChange k).toAffine.Point) where
  carrier := rationalHomSet k W W
  mul_mem' ha hb := WeierstrassCurve.comp_mem_rationalHomSet k W W W hb ha
  one_mem' := id_mem_rationalHomSet k W
  add_mem' ha hb := WeierstrassCurve.add_mem_rationalHomSet k W W ha hb
  zero_mem' := zero_mem_rationalHomSet k W W
  neg_mem' ha := neg_mem_rationalHomSet ha

theorem mem_homSubring {α : AddMonoid.End (W.baseChange k).toAffine.Point} :
    α ∈ homSubring k W ↔ (α : (W.baseChange k).toAffine.Point →+ _) ∈ rationalHomSet k W W := Iff.rfl

omit [DecidableEq k] [IsAlgClosed k] in
theorem natCast_ne_zero_of_ne_zero {N : ℕ} (hN : (N : F) ≠ 0) : (N : k) ≠ 0 := by
  intro h
  apply hN
  have : algebraMap F k (N : F) = 0 := by rw [map_natCast, h]
  exact (map_eq_zero_iff _ (algebraMap F k).injective).mp this

noncomputable def setup : Setup (W.baseChange k).toAffine.Point where
  S := homSubring k W
  good N := (N : F) ≠ 0
  good_pos h := Nat.pos_of_ne_zero (by rintro rfl; exact h (by simp))
  good_mul hM hN := by push_cast; exact mul_ne_zero hM hN
  good_dvd := by
    rintro M N ⟨c, rfl⟩ hN hM
    exact hN (by push_cast; rw [hM, zero_mul])
  surj hs hs0 := WeierstrassCurve.surjective_of_mem_rationalHomSet k hs hs0
  dvd hN _ hs hker :=
    WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero k W W hN hs hker
  kerBound hs hs0 := by
    obtain ⟨σ, -, t, n, hn, hdual, -⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id k W hs hs0
    exact ⟨n, hn, fun a ha => hdual.ker_le_torsion_right ha⟩
  card hN := WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W (natCast_ne_zero_of_ne_zero k hN)
  finU := WeierstrassCurve.finite_rationalHomSet_units k W

end Instantiate

end WeierstrassCurve.LevelRigidity

open WeierstrassCurve.LevelRigidity in
theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve F) [W.IsElliptic] {N : ℕ} (hN3 : 3 ≤ N) (hN : (N : F) ≠ 0) {ε ε' : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point} (hε : ε ∈ WeierstrassCurve.rationalHomSet k W W) (hε' : ε' ∈ WeierstrassCurve.rationalHomSet k W W) (h₁ : ε'.comp ε = AddMonoidHom.id _) (h₂ : ε.comp ε' = AddMonoidHom.id _) (hfix : ∀ P : (W.baseChange k).toAffine.Point, (N : ℤ) • P = 0 → ε P = P) : ε = AddMonoidHom.id _ :=
  (setup k W).eq_one_of_forall_apply_eq (N := N) hN hN3 (ε := ε) (ε' := ε') hε hε' h₁ h₂ hfix

end S_WeierstrassCurve_eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self
end P2MW
export P2MW.S_WeierstrassCurve_eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self (solution)
