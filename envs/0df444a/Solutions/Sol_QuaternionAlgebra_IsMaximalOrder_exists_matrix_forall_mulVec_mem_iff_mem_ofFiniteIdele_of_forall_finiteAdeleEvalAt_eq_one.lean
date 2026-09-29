-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a16806e4-09c4-58d4-9ac3-34785c618ea7

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one
import Theorems.Thm_Submodule_exists_list_prod_elementary_tmul_one_mul_eq_of_mem_asIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

namespace P2mSFv

section Words

variable {A : Type*} [Ring A]

def E (e : Bool × A) : Matrix (Fin 2) (Fin 2) A :=
  if e.1 then !![(1 : A), e.2; 0, 1] else !![(1 : A), 0; e.2, 1]

def W (l : List (Bool × A)) : Matrix (Fin 2) (Fin 2) A := (l.map E).prod

theorem W_def (l : List (Bool × A)) :
    W l = (l.map fun e : Bool × A => if e.1 then !![(1 : A), e.2; 0, 1] else !![(1 : A), 0; e.2, 1]).prod :=
  rfl

@[scoped simp] theorem W_nil : W ([] : List (Bool × A)) = 1 := by simp [W]

@[scoped simp] theorem W_cons (e : Bool × A) (l : List (Bool × A)) : W (e :: l) = E e * W l := by
  simp [W]

theorem W_append (l l' : List (Bool × A)) : W (l ++ l') = W l * W l' := by
  simp [W, List.map_append, List.prod_append]

theorem W_singleton (e : Bool × A) : W [e] = E e := by simp [W]

theorem fin_two_eq {a b c d a' b' c' d' : A} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c') (h₄ : d = d') :
    !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h₁ h₂ h₃ h₄; rfl

theorem one_eq : (1 : Matrix (Fin 2) (Fin 2) A) = !![(1 : A), 0; 0, 1] := Matrix.one_fin_two

theorem E_add (b : Bool) (s t : A) : E (b, s) * E (b, t) = E (b, s + t) := by
  cases b
  · simp only [E, Bool.false_eq_true, ↓reduceIte, Matrix.mul_fin_two]
    exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)
  · simp only [E, ↓reduceIte, Matrix.mul_fin_two]
    exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem E_zero (b : Bool) : E (b, (0 : A)) = 1 := by
  cases b <;> simp [E, one_eq]

def inv (l : List (Bool × A)) : List (Bool × A) := (l.map fun e => (e.1, -e.2)).reverse

theorem inv_cons (e : Bool × A) (l : List (Bool × A)) : inv (e :: l) = inv l ++ [(e.1, -e.2)] := by
  simp [inv]

theorem W_mul_W_inv (l : List (Bool × A)) : W l * W (inv l) = 1 := by
  induction l with
  | nil => simp [inv]
  | cons e l ih =>
    rw [inv_cons, W_cons, W_append, W_singleton, mul_assoc, ← mul_assoc (W l), ih, one_mul, E_add,
      add_neg_cancel, E_zero]

theorem W_inv_mul_W (l : List (Bool × A)) : W (inv l) * W l = 1 := by
  induction l with
  | nil => simp [inv]
  | cons e l ih =>
    rw [inv_cons, W_cons, W_append, W_singleton, mul_assoc, ← mul_assoc (E _), E_add, neg_add_cancel,
      E_zero, one_mul, ih]

theorem map_W {B : Type*} [Ring B] (f : A →+* B) (l : List (Bool × A)) :
    f.mapMatrix (W l) = W (l.map fun e => (e.1, f e.2)) := by
  induction l with
  | nil => simp [W]
  | cons e l ih =>
    rw [W_cons, map_mul, ih, List.map_cons, W_cons]
    congr 1
    rcases e with ⟨b, t⟩
    cases b
    · simp only [E, Bool.false_eq_true, ↓reduceIte]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp only [E, ↓reduceIte]
      ext i j; fin_cases i <;> fin_cases j <;> simp

theorem inv_map {B : Type*} [Ring B] (f : A →+* B) (l : List (Bool × A)) :
    inv (l.map fun e => (e.1, f e.2)) = (inv l).map fun e => (e.1, f e.2) := by
  simp [inv, List.map_reverse, Function.comp_def]

theorem inv_unique {M : Type*} [Monoid M] {x y z : M} (hxy : x * y = 1) (hzx : z * x = 1) : y = z :=
  (left_inv_eq_right_inv hzx hxy).symm

end Words

section IntVec

variable {A : Type*} [Ring A] (S : AddSubgroup A)
variable (hone : (1 : A) ∈ S) (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
include hone hmul

theorem mulVec_mem {P : Matrix (Fin 2) (Fin 2) A} (hP : ∀ i j, P i j ∈ S) {y : Fin 2 → A}
    (hy : ∀ i, y i ∈ S) : ∀ i, (P.mulVec y) i ∈ S := by
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact S.add_mem (hmul _ (hP i 0) _ (hy 0)) (hmul _ (hP i 1) _ (hy 1))

theorem forall_mulVec_mem_iff {P P' : Matrix (Fin 2) (Fin 2) A} (hP : ∀ i j, P i j ∈ S)
    (hP' : ∀ i j, P' i j ∈ S) (h : P' * P = 1) (y : Fin 2 → A) :
    (∀ i, (P.mulVec y) i ∈ S) ↔ ∀ i, y i ∈ S := by
  refine ⟨fun hy => ?_, mulVec_mem S hone hmul hP⟩
  have : y = P'.mulVec (P.mulVec y) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  rw [this]
  exact mulVec_mem S hone hmul hP' hy

theorem int_mul {P Q : Matrix (Fin 2) (Fin 2) A} (hP : ∀ i j, P i j ∈ S) (hQ : ∀ i j, Q i j ∈ S) :
    ∀ i j, (P * Q) i j ∈ S := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact S.add_mem (hmul _ (hP i 0) _ (hQ 0 j)) (hmul _ (hP i 1) _ (hQ 1 j))

theorem int_E {t : A} (ht : t ∈ S) (b : Bool) : ∀ i j, E (b, t) i j ∈ S := by
  intro i j
  cases b
  · simp only [E, Bool.false_eq_true, ↓reduceIte]
    fin_cases i <;> fin_cases j <;> simp [hone, ht, S.zero_mem]
  · simp only [E, ↓reduceIte]
    fin_cases i <;> fin_cases j <;> simp [hone, ht, S.zero_mem]

theorem int_W {L : List (Bool × A)} (hL : ∀ e ∈ L, e.2 ∈ S) : ∀ i j, W L i j ∈ S := by
  induction L with
  | nil =>
    intro i j
    rw [W_nil, one_eq]
    fin_cases i <;> fin_cases j <;> simp [hone, S.zero_mem]
  | cons e L ih =>
    rw [W_cons]
    exact int_mul S hone hmul (int_E S hone hmul (hL e List.mem_cons_self) e.1)
      (ih fun e' he' => hL e' (List.mem_cons_of_mem _ he'))

omit hone hmul in
theorem inv_mem_of_forall {L : List (Bool × A)} (hL : ∀ e ∈ L, e.2 ∈ S) : ∀ e ∈ inv L, e.2 ∈ S := by
  intro e he
  simp only [inv, List.mem_reverse, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  exact S.neg_mem (hL e' he')

omit hone hmul in
theorem diag_mulVec (a b : A) (y : Fin 2 → A) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) A).mulVec y = ![a * y 0, b * y 1] := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp

end IntVec

section LocalGlobal

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)
  (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)

local notation "𝔸" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem finiteAdeleEvalAt_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : D) :
    Submodule.finiteAdeleEvalAt D w (z ⊗ₜ[ℚ] (1 : 𝔸)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]
  rfl

include hfg hspan in

theorem mem_ofFiniteIdele_iff_forall (g : (D ⊗[ℚ] 𝔸)ˣ) (z : D) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸)ˣ) : D ⊗[ℚ] 𝔸) *
          (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  have key : (∃ y ∈ Submodule.finiteAdeleBox Λ, AddMonoidHom.mulLeft (g : D ⊗[ℚ] 𝔸) y = z ⊗ₜ[ℚ] (1 : 𝔸)) ↔
      ((g⁻¹ : (D ⊗[ℚ] 𝔸)ˣ) : D ⊗[ℚ] 𝔸) * (z ⊗ₜ[ℚ] (1 : 𝔸)) ∈ Submodule.finiteAdeleBox Λ := by
    constructor
    · rintro ⟨y, hy, hgy⟩
      rw [AddMonoidHom.coe_mulLeft] at hgy
      rw [← hgy, ← mul_assoc, Units.inv_mul, one_mul]
      exact hy
    · intro h
      exact ⟨_, h, by rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]⟩
  rw [key, Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan]
  refine forall_congr' fun w => ?_
  rw [map_mul, finiteAdeleEvalAt_tmul_one]

include hfg hspan in

theorem mem_iff_forall (z : D) :
    z ∈ Λ ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ), z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  conv_lhs => rw [← Submodule.ofFiniteIdele_one Λ hfg hspan]
  rw [mem_ofFiniteIdele_iff_forall Λ hfg hspan]
  refine forall_congr' fun w => ?_
  rw [inv_one, Units.val_one, map_one, one_mul]

end LocalGlobal

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (w : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : w.adicCompletion ℚ}
    (hc : c ∈ w.adicCompletionIntegers ℚ) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem mul_mem_localBox (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) {x y : D ⊗[ℚ] w.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ w) (hy : y ∈ Submodule.localBox Λ w) :
    x * y ∈ Submodule.localBox Λ w := by
  have hgen : ∀ y : D ⊗[ℚ] w.adicCompletion ℚ, (∃ z' ∈ Λ, ∃ c' : w.adicCompletion ℚ,
      c' ∈ w.adicCompletionIntegers ℚ ∧ y = z' ⊗ₜ[ℚ] c') → ∀ x ∈ Submodule.localBox Λ w,
        x * y ∈ Submodule.localBox Λ w := by
    rintro y ⟨z', hz', c', hc', rfl⟩ x hx
    have hle : Submodule.localBox Λ w ≤
        (Submodule.localBox Λ w).comap (AddMonoidHom.mulRight (z' ⊗ₜ[ℚ] c')) := by
      rw [Submodule.localBox, AddSubgroup.closure_le]
      rintro _ ⟨z, hz, c, hc, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, AddMonoidHom.coe_mulRight, SetLike.mem_coe,
        Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ w (hmul z hz z' hz') ((w.adicCompletionIntegers ℚ).toSubring.mul_mem hc hc')
    exact hle hx
  have hle : Submodule.localBox Λ w ≤ (Submodule.localBox Λ w).comap (AddMonoidHom.mulLeft x) := by
    rw [Submodule.localBox, AddSubgroup.closure_le]
    intro y hy
    exact hgen y hy x hx
  exact hle hy

theorem one_mem_localBox (hone : (1 : D) ∈ Λ) : (1 : D ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_localBox Λ w hone (Subring.one_mem _)

theorem notMem_of_ne {r : ℕ} (hr : r.Prime) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : w ≠ v) : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hrw
  apply hw
  have key : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
      Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) u = ⟨r, hr⟩ := by
    intro u hu
    have h1 : Rat.HeightOneSpectrum.natGenerator u ∣ r := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hu
      rwa [map_natCast] at this
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator u) hr).mp h1)
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective ((key w hrw).trans (key v hv).symm)

theorem notMem_of_mem_of_ne {r q : ℕ} (hr : r.Prime) (hq : q.Prime) (hrq : r ≠ q)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hqv
  have key : ∀ {s : ℕ} (hs : s.Prime), ((s : ℕ) : 𝓞 ℚ) ∈ v.asIdeal →
      Rat.HeightOneSpectrum.natGenerator v = s := by
    intro s hs hsv
    have h1 : Rat.HeightOneSpectrum.natGenerator v ∣ s := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hsv
      rwa [map_natCast] at this
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hs).mp h1
  exact hrq ((key hr hv).symm.trans (key hq hqv))

theorem inv_natCast_pow_mem {r : ℕ} (hr : r.Prime) (hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) (n : ℕ) :
    ((r : w.adicCompletion ℚ) ^ n)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_pow]
  have : Valued.v (r : w.adicCompletion ℚ) = 1 := by
    have h1 : (r : w.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) (r : 𝓞 ℚ) :=
      (map_natCast _ r).symm
    have h2 : Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) (r : 𝓞 ℚ)) =
        w.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation w (r : 𝓞 ℚ)
    rw [h1, h2, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact hrw
  rw [this, one_pow, inv_one]

theorem tmul_one_mem_localBox_of_smul_mem {r : ℕ} (hr : r.Prime) (hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal)
    {α : D} {n : ℕ} (hα : ((r ^ n : ℕ) : ℤ) • α ∈ Λ) :
    α ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  haveI : CharZero (w.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (w.adicCompletion ℚ)).injective
  have hr0 : ((r : w.adicCompletion ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.ne_zero)
  have hcast : (((r ^ n : ℕ) : ℤ) • α) = ((r ^ n : ℕ) : D) * α := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have e1 : ((r ^ n : ℕ) : D ⊗[ℚ] w.adicCompletion ℚ) *
      ((1 : D) ⊗ₜ[ℚ] ((r : w.adicCompletion ℚ) ^ n)⁻¹) = 1 := by
    rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul, Nat.cast_pow,
      mul_inv_cancel₀ hr0, ← Algebra.TensorProduct.one_def]
  have e2 : ((r ^ n : ℕ) : D ⊗[ℚ] w.adicCompletion ℚ) *
      ((1 : D) ⊗ₜ[ℚ] ((r : w.adicCompletion ℚ) ^ n)⁻¹) * (α ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) =
        ((((r ^ n : ℕ) : ℤ) • α) ⊗ₜ[ℚ] ((r : w.adicCompletion ℚ) ^ n)⁻¹) := by
    rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one, hcast]
  rw [← one_mul (α ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)), ← e1, e2]
  exact tmul_mem_localBox Λ w hα (inv_natCast_pow_mem w hr hrw n)

end Box

section Main

variable {c d : ℚ}

local notation "H" => ℍ[ℚ, c, d]
local notation "𝔸" => FiniteAdeleRing (𝓞 ℚ) ℚ

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6400000 in
theorem main (q : ℕ) [hq : Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ H) (hO : IsMaximalOrder O)
    (r : ℕ) [hr : Fact r.Prime] (hrq : r ≠ q) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (g₁ g₂ : (H ⊗[ℚ] 𝔸)ˣ)
    (hg₁ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt H w (g₁ : H ⊗[ℚ] 𝔸) = 1)
    (hg₂ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt H w (g₂ : H ⊗[ℚ] 𝔸) = 1)
    (hdet : ∀ φ : H ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ t : v.adicCompletion ℚ,
        φ ((1 : H) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) →
      (∀ x : H ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox O v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) →
      (φ (Submodule.finiteAdeleEvalAt H v ((g₁ * g₂ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸))).det ∈
          v.adicCompletionIntegers ℚ ∧
      (φ (Submodule.finiteAdeleEvalAt H v (((g₁ * g₂)⁻¹ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸))).det ∈
          v.adicCompletionIntegers ℚ) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) H, γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → H,
        (∀ i, (γ'.mulVec x) i ∈ O) ↔
          (x 0 ∈ Submodule.ofFiniteIdele O g₁ ∧ x 1 ∈ Submodule.ofFiniteIdele O g₂) := by
  classical
  have hOo : IsOrder O := hO.isOrder
  have hmulO : ∀ x ∈ O, ∀ y ∈ O, x * y ∈ O := fun x hx y hy => hOo.mul_mem hx hy

  have hE : IsEichlerOrder O 1 :=
    ⟨O, O, hO, hO, (inf_idem O).symm, by rw [AddSubgroup.relIndex_self]⟩
  have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := notMem_of_mem_of_ne hr.out hq.out hrq hv
  have h1v : ((1 : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).mp v.isPrime.ne_top
  obtain ⟨φ, hφ1, hφO⟩ := IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hH hE v hqv h1v
  obtain ⟨hδ, hδ'⟩ := hdet φ hφ1 hφO

  set ev := Submodule.finiteAdeleEvalAt H v with hev
  set G : (H ⊗[ℚ] 𝔸)ˣ := g₁ * g₂ with hG
  set δ := (φ (ev (G : H ⊗[ℚ] 𝔸))).det with hδdef
  set δ' := (φ (ev ((G⁻¹ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸))).det with hδ'def
  have hδδ' : δ * δ' = 1 := by
    rw [hδdef, hδ'def, ← Matrix.det_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one,
      Matrix.det_one]
  have hδ'δ : δ' * δ = 1 := by rw [mul_comm]; exact hδδ'

  set Um : H ⊗[ℚ] v.adicCompletion ℚ := φ.symm !![1, 0; 0, δ] with hUm
  set Um' : H ⊗[ℚ] v.adicCompletion ℚ := φ.symm !![1, 0; 0, δ'] with hUm'
  have hdiag : ∀ s t : v.adicCompletion ℚ, (!![(1 : v.adicCompletion ℚ), 0; 0, s] * !![1, 0; 0, t] :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, 0; 0, s * t] := by
    intro s t
    rw [Matrix.mul_fin_two]
    exact fin_two_eq (by ring) (by ring) (by ring) (by ring)
  have hUU' : Um * Um' = 1 := by
    rw [hUm, hUm', ← φ.symm.map_mul, hdiag, hδδ', ← one_eq, φ.symm.map_one]
  have hU'U : Um' * Um = 1 := by
    rw [hUm, hUm', ← φ.symm.map_mul, hdiag, hδ'δ, ← one_eq, φ.symm.map_one]
  have h1i : (1 : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := Subring.one_mem _
  have h0i : (0 : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := Subring.zero_mem _
  have hUint : Um ∈ Submodule.localBox O v := by
    rw [hφO, hUm, RingEquiv.apply_symm_apply]
    intro i j; fin_cases i <;> fin_cases j <;> simp [h1i, h0i, hδ]
  have hU'int : Um' ∈ Submodule.localBox O v := by
    rw [hφO, hUm', RingEquiv.apply_symm_apply]
    intro i j; fin_cases i <;> fin_cases j <;> simp [h1i, h0i, hδ']
  let U : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ := ⟨Um, Um', hUU', hU'U⟩

  let cu : (H ⊗[ℚ] 𝔸)ˣ →* (H ⊗[ℚ] v.adicCompletion ℚ)ˣ := Units.map (ev : H ⊗[ℚ] 𝔸 →ₐ[ℚ] H ⊗[ℚ] v.adicCompletion ℚ).toRingHom.toMonoidHom
  have cu_val : ∀ g : (H ⊗[ℚ] 𝔸)ˣ, ((cu g : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) = ev (g : H ⊗[ℚ] 𝔸) := fun g => rfl
  have cu_inv : ∀ g : (H ⊗[ℚ] 𝔸)ˣ, (((cu g)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) = ev ((g⁻¹ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸) :=
    fun g => by rw [← map_inv]; rfl

  have hdet1 : (φ (((cu g₁ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) * ((cu g₂ * U⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ))).det = 1 := by
    have e1 : ((cu g₁ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) * ((cu g₂ * U⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) =
        ev (G : H ⊗[ℚ] 𝔸) * Um' := by
      rw [Units.val_mul, cu_val, cu_val, ← mul_assoc, ← map_mul, hG, Units.val_mul]
      rfl
    rw [e1, map_mul, Matrix.det_mul, ← hδdef, hUm', RingEquiv.apply_symm_apply, Matrix.det_fin_two_of,
      mul_zero, sub_zero, one_mul, hδδ']
  obtain ⟨l, hl⟩ :=
    Matrix.exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one φ (cu g₁) (cu g₂ * U⁻¹) hdet1
  change W l = _ at hl

  obtain ⟨l', hglob, X, Y, hX, hY, hXY, hYX, hEq⟩ :=
    Submodule.exists_list_prod_elementary_tmul_one_mul_eq_of_mem_asIdeal O hOo.one_mem hmulO hOo.spanTop
      r v hv l
  change W l = W (l'.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) * X at hEq

  refine ⟨W l', W (inv l'), W_mul_W_inv l', W_inv_mul_W l', fun x => ?_⟩

  have hloc : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (L : List (Bool × H)) (i : Fin 2),
      ((W L).mulVec x i) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
        ((W (L.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)))).mulVec
          (fun j => x j ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) i := by
    intro w L i
    let ι : H →+* H ⊗[ℚ] w.adicCompletion ℚ :=
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (A := H) (B := w.adicCompletion ℚ)).toRingHom
    have hι : ∀ z : H, ι z = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := fun z => rfl
    have h1 := RingHom.map_mulVec ι (W L) x i
    rw [hι] at h1
    rw [h1, ← RingHom.mapMatrix_apply, map_W]
    rfl

  have hL : (∀ i, ((W (inv l')).mulVec x) i ∈ O) ↔ ∀ i, ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ((W ((inv l').map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)))).mulVec
        (fun j => x j ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) i ∈ Submodule.localBox O w := by
    refine forall_congr' fun i => ?_
    rw [mem_iff_forall O hOo.fg hOo.spanTop]
    refine forall_congr' fun w => ?_
    rw [hloc]
  have hR : (x 0 ∈ Submodule.ofFiniteIdele O g₁ ∧ x 1 ∈ Submodule.ofFiniteIdele O g₂) ↔
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt H w ((g₁⁻¹ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸) *
            (x 0 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox O w ∧
        Submodule.finiteAdeleEvalAt H w ((g₂⁻¹ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸) *
            (x 1 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox O w := by
    rw [mem_ofFiniteIdele_iff_forall O hOo.fg hOo.spanTop, mem_ofFiniteIdele_iff_forall O hOo.fg hOo.spanTop,
      ← forall_and]
  rw [hL, forall_comm, hR]
  refine forall_congr' fun w => ?_

  have honew : (1 : H ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox O w := one_mem_localBox O w hOo.one_mem
  have hmulw : ∀ a ∈ Submodule.localBox O w, ∀ b ∈ Submodule.localBox O w,
      a * b ∈ Submodule.localBox O w := fun a ha b hb => mul_mem_localBox O w hmulO ha hb
  by_cases hw : w = v
  ·
    subst w

    set Γ := W (l'.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) with hΓ
    have hΓ' : W ((inv l').map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) = X * W (inv l) := by
      have hmap : (inv l').map (fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) =
          inv (l'.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) := by
        simp only [inv, List.map_reverse, List.map_map, Function.comp_def, TensorProduct.neg_tmul]
      rw [hmap]
      have hΓeq : Γ = W l * Y := by rw [hEq, mul_assoc, hXY, mul_one]
      refine inv_unique (W_mul_W_inv _) ?_
      rw [← hΓ, hΓeq]
      calc X * W (inv l) * (W l * Y) = X * (W (inv l) * W l) * Y := by noncomm_ring
        _ = 1 := by rw [W_inv_mul_W, mul_one, hXY]
    rw [hΓ']

    have hΔ' : W (inv l) = !![(((cu g₁)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ), 0;
        0, Um * (((cu g₂)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ)] := by
      refine inv_unique (W_mul_W_inv l) ?_
      rw [hl, Matrix.mul_fin_two, one_eq]
      refine fin_two_eq ?_ (by simp) (by simp) ?_
      · rw [Units.inv_mul, mul_zero, add_zero]
      · rw [zero_mul, zero_add, Units.val_mul]
        calc Um * (((cu g₂)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) * ((cu g₂ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) * ((U⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ))
            = Um * ((((cu g₂)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) * (cu g₂ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ)) *
                ((U⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ) := by noncomm_ring
          _ = 1 := by rw [Units.inv_mul, mul_one]; exact hUU'
    rw [hΔ']

    have hXint : ∀ i j, X i j ∈ (Submodule.localBox O v) := hX
    rw [show ∀ y : Fin 2 → H ⊗[ℚ] v.adicCompletion ℚ, (X * !![(((cu g₁)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ), 0;
        0, Um * (((cu g₂)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ)]).mulVec y =
        X.mulVec ((!![(((cu g₁)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ), 0;
          0, Um * (((cu g₂)⁻¹ : (H ⊗[ℚ] v.adicCompletion ℚ)ˣ) : H ⊗[ℚ] v.adicCompletion ℚ)]).mulVec y) from
        fun y => (Matrix.mulVec_mulVec _ _ _).symm]
    rw [forall_mulVec_mem_iff (Submodule.localBox O v) honew hmulw hX hY hYX, diag_mulVec, cu_inv, cu_inv,
      Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · have := hmulw _ hU'int _ h
      rwa [← mul_assoc, ← mul_assoc, hU'U, one_mul] at this
    · rw [mul_assoc]
      exact hmulw _ hUint _ h
  ·
    have hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := notMem_of_ne w hr.out hv hw
    have hint : ∀ L : List (Bool × H), (∀ e ∈ L, ∃ n : ℕ, ((r ^ n : ℕ) : ℤ) • e.2 ∈ O) →
        ∀ i j, W (L.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) i j ∈ Submodule.localBox O w := by
      intro L hL'
      refine int_W (Submodule.localBox O w) honew hmulw ?_
      intro e he
      rw [List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      obtain ⟨n, hn⟩ := hL' e' he'
      exact tmul_one_mem_localBox_of_smul_mem O w hr.out hrw hn
    have hglob' : ∀ e ∈ inv l', ∃ n : ℕ, ((r ^ n : ℕ) : ℤ) • e.2 ∈ O := by
      intro e he
      simp only [inv, List.mem_reverse, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      obtain ⟨n, hn⟩ := hglob e' he'
      exact ⟨n, by rw [smul_neg]; exact O.neg_mem hn⟩
    have hprod : W (l'.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) *
        W ((inv l').map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) = 1 := by
      have hmap : (inv l').map (fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) =
          inv (l'.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) := by
        simp only [inv, List.map_reverse, List.map_map, Function.comp_def, TensorProduct.neg_tmul]
      rw [hmap, W_mul_W_inv]
    rw [forall_mulVec_mem_iff (Submodule.localBox O w) honew hmulw (hint _ hglob') (hint _ hglob) hprod,
      Fin.forall_fin_two]
    have hg₁' : Submodule.finiteAdeleEvalAt H w ((g₁⁻¹ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸) = 1 := by
      have := congrArg (Submodule.finiteAdeleEvalAt H w) g₁.mul_inv
      rwa [map_mul, map_one, hg₁ w hw, one_mul] at this
    have hg₂' : Submodule.finiteAdeleEvalAt H w ((g₂⁻¹ : (H ⊗[ℚ] 𝔸)ˣ) : H ⊗[ℚ] 𝔸) = 1 := by
      have := congrArg (Submodule.finiteAdeleEvalAt H w) g₂.mul_inv
      rwa [map_mul, map_one, hg₂ w hw, one_mul] at this
    rw [hg₁', hg₂', one_mul, one_mul]

end Main

end P2mSFv
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one.P2mSFv"

open P2mSFv in
theorem solution
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (r : ℕ) [Fact r.Prime] (hrq : r ≠ q) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (g₁ g₂ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg₁ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] w (g₁ : ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hg₂ : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] w (g₂ : ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hdet : ∀ φ : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ t : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, c, d]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) →
      (∀ x : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox O v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) →
      (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
          ((g₁ * g₂ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ ∧
      (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
          (((g₁ * g₂)⁻¹ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → ℍ[ℚ, c, d],
        (∀ i, (γ'.mulVec x) i ∈ O) ↔
          (x 0 ∈ Submodule.ofFiniteIdele O g₁ ∧ x 1 ∈ Submodule.ofFiniteIdele O g₂) :=
  main q hH O hO r hrq v hv g₁ g₂ hg₁ hg₂ hdet

end S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one (solution)
