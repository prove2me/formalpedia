-- Prove2me | solution 1 for WeierstrassCurve.comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/00669825-4ab7-50c3-b917-50c8c555aa9e

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map toAffine Affine.Point Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet Affine.Point.some_congr ratPointMap_injective ratPointHom comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed exists_isDualPair_of_mem_rationalHomSet"
namespace FrobeniusTransport
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

section Frobenius

variable {k : Type} [Field k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)

theorem ratPointHom_iterateFrobenius_mem (W : WeierstrassCurve k) :
    (ratPointHom (iterateFrobenius k p n) (W₀ := W) :
        (W.baseChange k).toAffine.Point →+
          ((W.map (iterateFrobenius k p n)).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (W.map (iterateFrobenius k p n)) := by
  right
  refine ⟨C (X ^ p ^ n), 1, X ^ p ^ n, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC (F := k) k (1 : k[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := k) k (C (X ^ p ^ n) : k[X][Y]) x y = x ^ p ^ n := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := k) k (X ^ p ^ n : k[X][Y]) x y = y ^ p ^ n := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  have key : ratPointHom (iterateFrobenius k p n) (W₀ := W) (.some x y h) =
      .some (iterateFrobenius k p n x) (iterateFrobenius k p n y)
        ((W.toAffine.map_nonsingular (iterateFrobenius k p n).injective x y).mpr h) := rfl
  have hx : iterateFrobenius k p n x = evalEvalBC (F := k) k (C (X ^ p ^ n) : k[X][Y]) x y /
      evalEvalBC (F := k) k (1 : k[X][Y]) x y := by rw [e0, e1, div_one, iterateFrobenius_def]
  have hy : iterateFrobenius k p n y = evalEvalBC (F := k) k (X ^ p ^ n : k[X][Y]) x y /
      evalEvalBC (F := k) k (1 : k[X][Y]) x y := by rw [e0, e2, div_one, iterateFrobenius_def]
  refine ⟨?_, key.trans ?_⟩
  · have h' := (W.toAffine.map_nonsingular (iterateFrobenius k p n).injective x y).mpr h
    rw [hx, hy] at h'
    exact h'
  · exact Affine.Point.some_congr hx hy _ _

end Frobenius

section Main

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
  (n : ℕ) (W : WeierstrassCurve k) [W.IsElliptic]

theorem main {T : W.toAffine.Point} (hT : T ≠ 0) (hpT : p • T = 0)
    {ρ : W.toAffine.Point →+ (W.map (iterateFrobenius k p n)).toAffine.Point}
    (hρ : ρ ∈ rationalHomSet k W (W.map (iterateFrobenius k p n))) (hρ0 : ρ ≠ 0)
    {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ rationalHomSet k W W)
    {β' : (W.map (iterateFrobenius k p n)).toAffine.Point →+
      (W.map (iterateFrobenius k p n)).toAffine.Point}
    (hβ' : β' ∈ rationalHomSet k (W.map (iterateFrobenius k p n)) (W.map (iterateFrobenius k p n)))
    (h : β'.comp ρ = ρ.comp β) :
    β'.comp (ratPointHom (iterateFrobenius k p n)) = (ratPointHom (iterateFrobenius k p n)).comp β := by
  have hFr : (ratPointHom (iterateFrobenius k p n) (W₀ := W) :
      (W.baseChange k).toAffine.Point →+
        ((W.map (iterateFrobenius k p n)).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (W.map (iterateFrobenius k p n)) := ratPointHom_iterateFrobenius_mem p n W

  obtain ⟨ρ', hρ', N, hN, hdual⟩ :
      ∃ ρ' : (W.map (iterateFrobenius k p n)).toAffine.Point →+ W.toAffine.Point,
        ρ' ∈ rationalHomSet k (W.map (iterateFrobenius k p n)) W ∧ ∃ N : ℤ, 0 < N ∧
        AddMonoidHom.IsDualPair ρ ρ' N := by
    obtain ⟨ρ', h₁, N, h₂, h₃⟩ :=
      WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet k W (W.map (iterateFrobenius k p n)) hρ hρ0
    exact ⟨ρ', h₁, N, h₂, h₃⟩
  have hβρ : ∀ P, β' (ρ P) = ρ (β P) := fun P => DFunLike.congr_fun h P

  have h1 : ∀ Q : (W.map (iterateFrobenius k p n)).toAffine.Point, ρ' (β' Q) = β (ρ' Q) := by
    intro Q
    obtain ⟨Q', rfl⟩ := exists_zsmul_eq (k := k) (W.map (iterateFrobenius k p n)) hN.ne' Q
    have e1 : ρ (ρ' Q') = N • Q' := hdual.comp_right Q'
    have e2 : ρ' (ρ (β (ρ' Q'))) = N • β (ρ' Q') := hdual.comp_left _
    rw [← e1, hβρ (ρ' Q'), e2, e1, map_zsmul ρ', map_zsmul β]

  have hT' : ratPointHom (iterateFrobenius k p n) (W₀ := W) T ≠ 0 := by
    intro h0
    apply hT
    have : ratPointHom (iterateFrobenius k p n) (W₀ := W) T =
        ratPointHom (iterateFrobenius k p n) (W₀ := W) 0 := by rw [h0, map_zero]
    exact ratPointMap_injective (iterateFrobenius k p n) this
  have hpT' : p • ratPointHom (iterateFrobenius k p n) (W₀ := W) T = 0 := by
    rw [← map_nsmul, hpT, map_zero]

  have hθ : ((ratPointHom (iterateFrobenius k p n) (W₀ := W)).comp ρ' :
      (W.map (iterateFrobenius k p n)).toAffine.Point →+ (W.map (iterateFrobenius k p n)).toAffine.Point) ∈
        rationalHomSet k (W.map (iterateFrobenius k p n)) (W.map (iterateFrobenius k p n)) :=
    WeierstrassCurve.comp_mem_rationalHomSet k (W.map (iterateFrobenius k p n)) W
      (W.map (iterateFrobenius k p n)) hρ' hFr
  have hcomm :=
    WeierstrassCurve.comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero p
      (W.map (iterateFrobenius k p n)) hT' hpT' hθ hβ'

  have hρ'0 : ρ' ≠ 0 := by
    intro h0
    apply zsmul_id_ne_zero (k := k) (W.map (iterateFrobenius k p n)) hN.ne'
    ext Q
    have e1 : ρ (ρ' Q) = N • Q := hdual.comp_right Q
    have e2 : ρ' Q = 0 := by rw [h0]; rfl
    rw [e2, map_zero ρ] at e1
    rw [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, ← e1, AddMonoidHom.zero_apply]
  have hsurj : Function.Surjective ρ' :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k hρ' hρ'0
  ext P
  obtain ⟨Q, rfl⟩ := hsurj P
  have e1 : ratPointHom (iterateFrobenius k p n) (W₀ := W) (ρ' (β' Q)) =
      β' (ratPointHom (iterateFrobenius k p n) (W₀ := W) (ρ' Q)) := DFunLike.congr_fun hcomm Q
  show β' (ratPointHom (iterateFrobenius k p n) (W₀ := W) (ρ' Q)) =
    ratPointHom (iterateFrobenius k p n) (W₀ := W) (β (ρ' Q))
  rw [← e1, h1]

end Main

end WeierstrassCurve.FrobeniusTransport

end

theorem solution {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) (W : WeierstrassCurve k) [W.IsElliptic] {T : W.toAffine.Point} (hT : T ≠ 0) (hpT : p • T = 0) {ρ : W.toAffine.Point →+ (W.map (iterateFrobenius k p n)).toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W (W.map (iterateFrobenius k p n))) (hρ0 : ρ ≠ 0) {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) {β' : (W.map (iterateFrobenius k p n)).toAffine.Point →+ (W.map (iterateFrobenius k p n)).toAffine.Point} (hβ' : β' ∈ WeierstrassCurve.rationalHomSet k (W.map (iterateFrobenius k p n)) (W.map (iterateFrobenius k p n))) (h : β'.comp ρ = ρ.comp β) : β'.comp (WeierstrassCurve.ratPointHom (iterateFrobenius k p n)) = (WeierstrassCurve.ratPointHom (iterateFrobenius k p n)).comp β :=
  WeierstrassCurve.FrobeniusTransport.main p n W hT hpT hρ hρ0 hβ hβ' h

end S_WeierstrassCurve_comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp
end P2MW
export P2MW.S_WeierstrassCurve_comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp (solution)
