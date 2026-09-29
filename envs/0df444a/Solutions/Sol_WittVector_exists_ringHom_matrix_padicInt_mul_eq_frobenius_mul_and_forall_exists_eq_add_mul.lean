-- Prove2me | solution 1 for WittVector.exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/1707472c-9ac7-584e-8680-210ca99d4d13

import Mathlib
import Theorems.Thm_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

namespace P2mKcZp2Matrix

variable (p : ℕ) [Fact p.Prime]

abbrev F : Type := GaloisField p 2

abbrev O : Type := WittVector p (GaloisField p 2)

abbrev W0 : Type := WittVector p (ZMod p)

scoped instance instFintypeF : Fintype (F p) := Fintype.ofFinite _

theorem card_F : Fintype.card (F p) = p ^ 2 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p 2 two_ne_zero]

abbrev ι : ZMod p →+* F p := algebraMap (ZMod p) (F p)

theorem pow_p_algebraMap (c : ZMod p) : (ι p c) ^ p = ι p c := by
  rw [← map_pow, ZMod.pow_card]

theorem exists_pow_ne : ∃ ω : F p, ω ^ p ≠ ω := by
  classical
  by_contra h
  push Not at h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set P : Polynomial (F p) := Polynomial.X ^ p - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1
  have hroots : ∀ ω : F p, ω ∈ P.roots := by
    intro ω
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, h ω, sub_self]
  have hcard : Fintype.card (F p) ≤ p := by
    calc Fintype.card (F p) = (Finset.univ : Finset (F p)).card := Finset.card_univ.symm
      _ ≤ P.roots.toFinset.card :=
          Finset.card_le_card fun ω _ => Multiset.mem_toFinset.mpr (hroots ω)
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p := hdeg
  rw [card_F, sq] at hcard
  have : p * p ≤ p * 1 := by simpa using hcard
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

def ω : F p := (exists_pow_ne p).choose

theorem ω_spec : (ω p) ^ p ≠ ω p := (exists_pow_ne p).choose_spec

theorem linearIndependent_one_ω : LinearIndependent (ZMod p) ![(1 : F p), ω p] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply ω_spec p
    have hω : ω p = ι p (-(s / t)) := by
      have h1 : t • ω p = -(s • (1 : F p)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h1
      have ht' : ι p t ≠ 0 := by
        intro h0; exact ht ((map_eq_zero_iff _ (algebraMap (ZMod p) (F p)).injective).mp h0)
      field_simp
      rw [map_neg, map_div₀]
      field_simp
      linear_combination h1
    rw [hω, pow_p_algebraMap]

def bF : Module.Basis (Fin 2) (ZMod p) (F p) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_ω p)
    (by rw [Fintype.card_fin, GaloisField.finrank p two_ne_zero])

@[scoped simp] theorem bF_zero : bF p 0 = 1 := by
  rw [bF, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

@[scoped simp] theorem bF_one : bF p 1 = ω p := by
  rw [bF, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

abbrev ιW : W0 p →+* O p := WittVector.map (ι p)

scoped instance instAlgebra : Algebra (W0 p) (O p) := (ιW p).toAlgebra

theorem algebraMap_eq : algebraMap (W0 p) (O p) = ιW p := rfl

theorem smul_def' (a : W0 p) (x : O p) : a • x = ιW p a * x := Algebra.smul_def a x

def B : Fin 2 → O p := fun i => WittVector.teichmuller p (bF p i)

theorem B_zero : B p 0 = 1 := by
  rw [B, bF_zero]; exact (WittVector.teichmuller p).map_one

theorem B_one : B p 1 = WittVector.teichmuller p (ω p) := by rw [B, bF_one]

theorem bijective_sum :
    Function.Bijective fun a : Fin 2 → W0 p => ∑ i, ιW p (a i) * B p i :=
  WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing p (bF p)

theorem linearIndependent_B : LinearIndependent (W0 p) (B p) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : (fun a : Fin 2 → W0 p => ∑ i, ιW p (a i) * B p i) g =
      (fun a : Fin 2 → W0 p => ∑ i, ιW p (a i) * B p i) 0 := by
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
    simpa only [smul_def'] using hg
  have := (bijective_sum p).1 h0
  exact fun i => congrFun this i

theorem span_B : ⊤ ≤ Submodule.span (W0 p) (Set.range (B p)) := by
  intro x _
  obtain ⟨a, ha⟩ := (bijective_sum p).2 x
  rw [← ha]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_def']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def bO : Module.Basis (Fin 2) (W0 p) (O p) := Module.Basis.mk (linearIndependent_B p) (span_B p)

theorem bO_apply (i : Fin 2) : bO p i = B p i := by rw [bO, Module.Basis.mk_apply]

local notation "σ" => (WittVector.frobenius : O p →+* O p)

theorem frobenius_frobenius (a : O p) : σ (σ a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← sq,
    ← card_F, FiniteField.pow_card]

theorem frobenius_ιW (a : W0 p) : σ (ιW p a) = ιW p a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff, pow_p_algebraMap]

theorem frobenius_teichmuller (x : F p) :
    σ (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ p) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

def σl : O p →ₗ[W0 p] O p where
  toFun := σ
  map_add' := map_add _
  map_smul' a x := by
    rw [smul_def', smul_def', RingHom.id_apply, map_mul, frobenius_ιW]

@[scoped simp] theorem σl_apply (x : O p) : σl p x = σ x := rfl

theorem σl_comp_σl : (σl p).comp (σl p) = LinearMap.id :=
  LinearMap.ext fun x => frobenius_frobenius p x

theorem isUnit_u : IsUnit (WittVector.teichmuller p (ω p ^ p) - WittVector.teichmuller p (ω p)) := by
  refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero]
  exact sub_ne_zero.mpr (ω_spec p)

def r₀ : O p →+* Matrix (Fin 2) (Fin 2) (W0 p) := (Algebra.leftMulMatrix (bO p)).toRingHom

theorem r₀_apply (a : O p) : r₀ p a = LinearMap.toMatrix (bO p) (bO p) (Algebra.lmul (W0 p) (O p) a) :=
  Algebra.leftMulMatrix_apply _ a

def S₀ : Matrix (Fin 2) (Fin 2) (W0 p) := LinearMap.toMatrix (bO p) (bO p) (σl p)

theorem S₀_mul_S₀ : S₀ p * S₀ p = 1 := by
  rw [S₀, ← LinearMap.toMatrix_comp, σl_comp_σl, LinearMap.toMatrix_id]

theorem S₀_mul_r₀ (a : O p) : S₀ p * r₀ p a = r₀ p (σ a) * S₀ p := by
  rw [S₀, r₀_apply, r₀_apply, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  congr 1
  apply LinearMap.ext
  intro x
  show σ (a * x) = σ a * σ x
  exact map_mul _ _ _

def lin (a c : O p) : O p →ₗ[W0 p] O p := Algebra.lmul (W0 p) (O p) a + (Algebra.lmul (W0 p) (O p) c).comp (σl p)

theorem lin_apply (a c x : O p) : lin p a c x = a * x + c * σ x := rfl

theorem toMatrix_lin (a c : O p) : LinearMap.toMatrix (bO p) (bO p) (lin p a c) = r₀ p a + r₀ p c * S₀ p := by
  rw [lin, map_add, LinearMap.toMatrix_comp (bO p) (bO p) (bO p), ← r₀_apply, ← r₀_apply, S₀]

theorem indep₀ (a c : O p) (h : r₀ p a + r₀ p c * S₀ p = 0) : a = 0 ∧ c = 0 := by
  have hlin : lin p a c = 0 := by
    apply (LinearMap.toMatrix (bO p) (bO p)).injective
    rw [toMatrix_lin, h, map_zero]
  have h1 : a + c = 0 := by
    have := LinearMap.congr_fun hlin 1
    rwa [lin_apply, mul_one, map_one, mul_one, LinearMap.zero_apply] at this
  have h2 : a * WittVector.teichmuller p (ω p) + c * WittVector.teichmuller p (ω p ^ p) = 0 := by
    have := LinearMap.congr_fun hlin (WittVector.teichmuller p (ω p))
    rwa [lin_apply, frobenius_teichmuller, LinearMap.zero_apply] at this
  have ha : a = -c := eq_neg_of_add_eq_zero_left h1
  rw [ha, neg_mul, neg_add_eq_sub, ← mul_sub] at h2
  have hc : c = 0 := (isUnit_u p).mul_left_eq_zero.mp h2
  exact ⟨by rw [ha, hc, neg_zero], hc⟩

theorem span₀ (M : Matrix (Fin 2) (Fin 2) (W0 p)) : ∃ a c : O p, M = r₀ p a + r₀ p c * S₀ p := by
  set g : O p →ₗ[W0 p] O p := Matrix.toLin (bO p) (bO p) M with hg
  set t : O p := WittVector.teichmuller p (ω p) with ht
  set u : O p := WittVector.teichmuller p (ω p ^ p) - WittVector.teichmuller p (ω p) with hu
  obtain ⟨v, hv⟩ := isUnit_u p
  set c : O p := (g t - g 1 * t) * ↑v⁻¹ with hc
  set a : O p := g 1 - c with ha
  have hcu : c * u = g t - g 1 * t := by
    rw [hc, hu, ← hv, mul_assoc, Units.inv_mul, mul_one]
  have hlin : lin p a c = g := by
    apply (bO p).ext
    intro i
    fin_cases i
    · show lin p a c (bO p 0) = g (bO p 0)
      rw [bO_apply, B_zero, lin_apply, mul_one, map_one, mul_one, ha, sub_add_cancel]
    · show lin p a c (bO p 1) = g (bO p 1)
      rw [bO_apply, B_one, lin_apply, frobenius_teichmuller, ← ht, ha, sub_mul, sub_add,
        ← mul_sub, ← neg_sub (WittVector.teichmuller p (ω p ^ p)) t, mul_neg, ← hu, sub_neg_eq_add,
        hcu]
      abel
  refine ⟨a, c, ?_⟩
  rw [← toMatrix_lin, hlin, hg, LinearMap.toMatrix_toLin]

def εM : Matrix (Fin 2) (Fin 2) (W0 p) ≃+* Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  (WittVector.equiv p).mapMatrix

def r : O p →+* Matrix (Fin 2) (Fin 2) ℤ_[p] := (εM p).toRingHom.comp (r₀ p)

def S : Matrix (Fin 2) (Fin 2) ℤ_[p] := εM p (S₀ p)

theorem r_apply (a : O p) : r p a = εM p (r₀ p a) := rfl

theorem S_mul_S : S p * S p = 1 := by
  rw [S, ← map_mul, S₀_mul_S₀, map_one]

theorem S_mul_r (a : O p) : S p * r p a = r p (σ a) * S p := by
  rw [S, r_apply, r_apply, ← map_mul, S₀_mul_r₀, map_mul]

theorem indep (a c : O p) (h : r p a + r p c * S p = 0) : a = 0 ∧ c = 0 := by
  apply indep₀ p
  apply (εM p).injective
  rw [map_add, map_mul, map_zero]
  exact h

private theorem _root_.P2mKcZp2Matrix.span (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) : ∃ a c : O p, M = r p a + r p c * S p := by
  obtain ⟨a, c, h⟩ := span₀ p ((εM p).symm M)
  refine ⟨a, c, ?_⟩
  rw [r_apply, r_apply, S, ← map_mul, ← map_add, ← h, RingEquiv.apply_symm_apply]

p2m_export "P2mKcZp2Matrix" "span"
end P2mKcZp2Matrix
p2m_reactivate "P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul.P2mKcZp2Matrix"

end
p2m_reactivate "P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul.P2mKcZp2Matrix"

open P2mKcZp2Matrix in

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ (r : WittVector p (GaloisField p 2) →+* Matrix (Fin 2) (Fin 2) ℤ_[p])
      (S : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      S * S = 1 ∧
      (∀ a, S * r a = r (WittVector.frobenius a) * S) ∧
      (∀ a c, r a + r c * S = 0 → a = 0 ∧ c = 0) ∧
      (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ a c, M = r a + r c * S) :=
  ⟨r p, S p, S_mul_S p, S_mul_r p, indep p, span p⟩

end S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul
end P2MW
export P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul (solution)
