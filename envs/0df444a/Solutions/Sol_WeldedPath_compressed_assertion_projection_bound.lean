-- Prove2me | solution 1 for WeldedPath.compressed_assertion_projection_bound
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-18T17:48:14.874229+00:00
-- url     : https://prove2.me/submissions/7df9039f-b5f3-4cdd-94b8-9429da83a6e1

import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Definitions.Def_WeldedPath_InjDb
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Definitions.Def_WeldedPath_exactCpO
import Definitions.Def_WeldedPath_Supplement_exactCpWT
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Theorems.Thm_WeldedPath_incidence_gap
import Mathlib

set_option autoImplicit false

-- Solutions.CompressedPermutationPrimitive
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate

theorem ketBra_eq_rankOne {X Y : Type*} [Fintype X] [Fintype Y]
    (u : Hil Y) (v : Hil X) : ketBra u v = InnerProductSpace.rankOne ℂ u v := rfl

theorem ket_inner {X : Type*} [Fintype X] [DecidableEq X] (x y : X) :
    inner ℂ (ket x) (ket y) = if x = y then 1 else 0 := by
  simp [ket, EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem pCF_apply {X : Type*} [Fintype X] (u v w : Hil X) :
    pCF u v w = w - inner ℂ u w • u - inner ℂ v w • v +
      inner ℂ v w • u + inner ℂ u w • v := by
  rfl

theorem pCF_adjoint {X : Type*} [Fintype X] (u v : Hil X) :
    ContinuousLinearMap.adjoint (pCF u v) = pCF u v := by
  simp only [pCF, ketBra_eq_rankOne, map_add, map_sub,
    ContinuousLinearMap.adjoint_one, InnerProductSpace.adjoint_rankOne]
  abel

theorem pCF_involutive {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0) :
    (pCF u v).comp (pCF u v) = 1 := by
  have hvu : inner ℂ v u = 0 := by rw [← inner_conj_symm, huv]; simp
  have hleft (w : Hil X) : inner ℂ u (pCF u v w) = inner ℂ v w := by
    rw [pCF_apply]
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hu, huv]
    ring
  have hright (w : Hil X) : inner ℂ v (pCF u v w) = inner ℂ u w := by
    rw [pCF_apply]
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hv, hvu]
    ring
  apply ContinuousLinearMap.ext
  intro w
  change pCF u v (pCF u v w) = w
  rw [pCF_apply, hleft, hright, pCF_apply]
  module

theorem pCF_norm_map {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0)
    (w : Hil X) : ‖pCF u v w‖ = ‖w‖ := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (pCF u v)).mpr
  rw [pCF_adjoint, pCF_involutive u v hu hv huv]

theorem addPair_apply_self {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) : I.addPair x y x = some y := by
  simp [InjDb.addPair, hx, hy]

theorem addPair_injective {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    Set.InjOn (I.addPair x) {y | I.symm y = none} := by
  intro y hy z hz h
  have hh := congrArg (fun J : InjDb s => J x) h
  rw [addPair_apply_self I x y hx hy, addPair_apply_self I x z hx hz] at hh
  exact Option.some.inj hh

theorem addPair_ne {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) : I.addPair x y ≠ I := by
  intro h
  have hh := congrArg (fun J : InjDb s => J x) h
  rw [addPair_apply_self I x y hx hy, hx] at hh
  cases hh

theorem size_symm {s : ℕ} (I : InjDb s) : InjDb.size I.symm = I.size := by
  have hex (x : Fin s) (hx : x ∈ Finset.univ.filter fun x => (I x).isSome) :
      ∃ y, I x = some y := by
    cases h : I x with
    | none => simp [h] at hx
    | some y => exact ⟨y, rfl⟩
  let f (x : Fin s) (hx : x ∈ Finset.univ.filter fun x => (I x).isSome) :=
    (hex x hx).choose
  have hf x hx : I x = some (f x hx) := (hex x hx).choose_spec
  symm
  apply Finset.card_bij f
  · intro x hx
    have h := (I.inv x (f x hx)).mpr (hf x hx)
    change I.symm (f x hx) = some x at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h]
    rfl
  · intro x hx y hy hxy
    have h := (I.inv x (f x hx)).mpr (hf x hx)
    have h' := (I.inv y (f y hy)).mpr (hf y hy)
    rw [hxy, h'] at h
    exact (Option.some.inj h).symm
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    cases h : I.symm y with
    | none => simp [h] at hy'
    | some x =>
      have hx : I x = some y := (I.inv x y).mp h
      have hxmem : x ∈ Finset.univ.filter fun x => (I x).isSome := by simp [hx]
      refine ⟨x, hxmem, ?_⟩
      exact Option.some.inj ((hf x hxmem).symm.trans hx)

theorem unused_card {s : ℕ} (I : InjDb s) :
    (Finset.univ.filter fun y => I.symm y = none).card = s - I.size := by
  have hh := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun y : Fin s => (I.symm y).isSome)
  have hf : (Finset.univ.filter fun y : Fin s => ¬ (I.symm y).isSome) =
      (Finset.univ.filter fun y => I.symm y = none) := by
    ext y
    cases h : I.symm y <;> simp [h]
  rw [hf, Finset.card_univ, Fintype.card_fin] at hh
  change InjDb.size I.symm + _ = s at hh
  rw [size_symm] at hh
  omega

theorem size_lt_of_unset {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    I.size < s := by
  have hh := Finset.card_lt_card (Finset.filter_ssubset.mpr
    (show ∃ y ∈ (Finset.univ : Finset (Fin s)), ¬ (I y).isSome from
      ⟨x, Finset.mem_univ _, by simp [hx]⟩))
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using hh

theorem plus_sum_inner_self {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y))
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y)) =
        ((s - I.size : ℕ) : ℂ) := by
  let D := Finset.univ.filter fun y => I.symm y = none
  have hsum : inner ℂ (∑ y ∈ D, ket (I.addPair x y))
      (∑ y ∈ D, ket (I.addPair x y)) = (D.card : ℂ) := by
    rw [sum_inner]
    calc
      _ = ∑ y ∈ D, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [inner_sum]
        simp only [ket_inner]
        rw [Finset.sum_eq_single y]
        · simp
        · intro z hz hzy
          apply if_neg
          intro heq
          exact hzy ((addPair_injective I x hx
            (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 heq).symm)
        · intro hnot
          exact (hnot hy).elim
      _ = _ := by simp
  simpa only [D, unused_card] using hsum

theorem plusState_inner_self {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ (plusState I x) (plusState I x) = 1 := by
  have hm : 0 < ((s - I.size : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (size_lt_of_unset I x hx)
  have hs : Real.sqrt ((s - I.size : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  have hscalar : (Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ ^ 2 *
      ((s - I.size : ℕ) : ℝ) = 1 := by
    field_simp
    exact (Real.sq_sqrt hm.le).symm
  unfold plusState
  rw [inner_smul_left, inner_smul_right, plus_sum_inner_self I x hx]
  push_cast
  have hh : ((Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ)⁻¹) ^ 2 *
      ((s - I.size : ℕ) : ℂ) = 1 := by exact_mod_cast hscalar
  convert hh using 1
  simp only [map_inv₀, Complex.conj_ofReal]
  ring

theorem ket_inner_plusState {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ (ket I) (plusState I x) = 0 := by
  unfold plusState
  rw [inner_smul_right, inner_sum]
  have hh : (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      inner ℂ (ket I) (ket (I.addPair x y))) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [ket_inner, if_neg]
    exact (addPair_ne I x y hx (Finset.mem_filter.mp hy).2).symm
  rw [hh, mul_zero]

theorem compressionPrimitive_norm {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none)
    (ψ : Hil (InjDb s)) : ‖pCF (plusState I x) (ket I) ψ‖ = ‖ψ‖ := by
  apply pCF_norm_map
  · exact plusState_inner_self I x hx
  · simp only [ket_inner, if_true]
  · rw [← inner_conj_symm, ket_inner_plusState I x hx]
    simp

end WeldedPath.CompressedPrimitive

end

-- Solutions.CompressedPermutationUnitary
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate

theorem addPair_apply_other {s : ℕ} (I : InjDb s) (x y u : Fin s)
    (hx : I x = none) (hy : I.symm y = none) (hu : u ≠ x) :
    I.addPair x y u = I u := by
  simp [InjDb.addPair, hx, hy, hu]

theorem addPair_eq_original {s : ℕ} (I J : InjDb s) (x y z : Fin s)
    (hIx : I x = none) (hIy : I.symm y = none)
    (hJx : J x = none) (hJz : J.symm z = none)
    (h : I.addPair x y = J.addPair x z) : I = J := by
  apply PEquiv.ext
  intro u
  by_cases hu : u = x
  · simp only [hu, hIx, hJx]
  · have hh := congrArg (fun K : InjDb s => K u) h
    simpa only [addPair_apply_other I x y u hIx hIy hu,
      addPair_apply_other J x z u hJx hJz hu] using hh

theorem ket_inner_plus_other {s : ℕ} (I J : InjDb s) (x : Fin s)
    (hIx : I x = none) (hJx : J x = none) :
    inner ℂ (ket I) (plusState J x) = 0 := by
  unfold plusState
  rw [inner_smul_right, inner_sum]
  have hh : (∑ y ∈ Finset.univ.filter (fun y => J.symm y = none),
      inner ℂ (ket I) (ket (J.addPair x y))) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [ket_inner, if_neg]
    intro heq
    have hh := congrArg (fun K : InjDb s => K x) heq
    rw [hIx, addPair_apply_self J x y hJx (Finset.mem_filter.mp hy).2] at hh
    cases hh
  rw [hh, mul_zero]

theorem plus_inner_plus_other {s : ℕ} (I J : InjDb s) (x : Fin s)
    (hIx : I x = none) (hJx : J x = none) (hIJ : I ≠ J) :
    inner ℂ (plusState I x) (plusState J x) = 0 := by
  have hsum : inner ℂ
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y))
      (∑ z ∈ Finset.univ.filter (fun z => J.symm z = none), ket (J.addPair x z)) = 0 := by
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro y hy
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro z hz
    rw [ket_inner, if_neg]
    exact fun h => hIJ (addPair_eq_original I J x y z hIx
      (Finset.mem_filter.mp hy).2 hJx (Finset.mem_filter.mp hz).2 h)
  simp only [plusState, inner_smul_left, inner_smul_right, hsum, mul_zero]

theorem pCF_delta (X : Type*) [Fintype X] (u v : Hil X) :
    pCF u v - 1 = -ketBra u u - ketBra v v + ketBra u v + ketBra v u := by
  unfold pCF
  abel

theorem pCF_delta_mul_zero {X : Type*} [Fintype X] (u v a b : Hil X)
    (hua : inner ℂ u a = 0) (hub : inner ℂ u b = 0)
    (hva : inner ℂ v a = 0) (hvb : inner ℂ v b = 0) :
    (pCF u v - 1) * (pCF a b - 1) = 0 := by
  rw [pCF_delta, pCF_delta]
  simp only [add_mul, sub_mul, neg_mul, mul_add, mul_sub, mul_neg,
    ketBra_eq_rankOne, ContinuousLinearMap.mul_def, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
    InnerProductSpace.rankOne_comp_rankOne,
    hua, hub, hva, hvb, zero_smul, neg_zero, sub_zero, add_zero]

theorem pCF_delta_square {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0) :
    (pCF u v - 1) * (pCF u v - 1) = -((pCF u v - 1) + (pCF u v - 1)) := by
  have hh : pCF u v * pCF u v = 1 := pCF_involutive u v hu hv huv
  simp only [sub_mul, mul_sub, one_mul, mul_one, hh]
  abel

theorem compression_family_norm {X ι : Type*} [Fintype X] (S : Finset ι)
    (u v : ι → Hil X)
    (hu : ∀ i ∈ S, inner ℂ (u i) (u i) = 1)
    (hv : ∀ i ∈ S, inner ℂ (v i) (v i) = 1)
    (huv : ∀ i ∈ S, inner ℂ (u i) (v i) = 0)
    (hoff : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      inner ℂ (u i) (u j) = 0 ∧ inner ℂ (u i) (v j) = 0 ∧
      inner ℂ (v i) (u j) = 0 ∧ inner ℂ (v i) (v j) = 0)
    (ψ : Hil X) :
    ‖(1 + ∑ i ∈ S, (pCF (u i) (v i) - 1)) ψ‖ = ‖ψ‖ := by
  let Δ := fun i => pCF (u i) (v i) - 1
  have hdiag i (hi : i ∈ S) : Δ i * Δ i = -(Δ i + Δ i) :=
    pCF_delta_square (u i) (v i) (hu i hi) (hv i hi) (huv i hi)
  have hneq i (hi : i ∈ S) j (hj : j ∈ S) (hij : i ≠ j) : Δ i * Δ j = 0 := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hoff i hi j hj hij
    exact pCF_delta_mul_zero _ _ _ _ h₁ h₂ h₃ h₄
  have hsquare : (∑ i ∈ S, Δ i) * (∑ i ∈ S, Δ i) =
      -((∑ i ∈ S, Δ i) + (∑ i ∈ S, Δ i)) := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ i ∈ S, Δ i * Δ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_eq_single i
        · intro j hj hji
          exact hneq i hi j hj hji.symm
        · intro hnot
          exact (hnot hi).elim
      _ = ∑ i ∈ S, -(Δ i + Δ i) := Finset.sum_congr rfl hdiag
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hinv : (1 + ∑ i ∈ S, Δ i) * (1 + ∑ i ∈ S, Δ i) = 1 := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hsquare]
    abel
  have hadj : ContinuousLinearMap.adjoint (1 + ∑ i ∈ S, Δ i) =
      1 + ∑ i ∈ S, Δ i := by
    simp only [Δ, map_add, map_sum, map_sub, pCF_adjoint, ContinuousLinearMap.adjoint_one]
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    (1 + ∑ i ∈ S, Δ i)).mpr
  rw [hadj]
  exact hinv

theorem pC_norm_map (s : ℕ) (x : Fin s) (ψ : Hil (InjDb s)) : ‖pC s x ψ‖ = ‖ψ‖ := by
  unfold pC
  apply compression_family_norm
  · intro I hI
    exact plusState_inner_self I x (Finset.mem_filter.mp hI).2
  · intro I _
    simp only [ket_inner, if_true]
  · intro I hI
    rw [← inner_conj_symm, ket_inner_plusState I x (Finset.mem_filter.mp hI).2]
    simp
  · intro I hI J hJ hIJ
    have hIx := (Finset.mem_filter.mp hI).2
    have hJx := (Finset.mem_filter.mp hJ).2
    refine ⟨plus_inner_plus_other I J x hIx hJx hIJ, ?_,
      ket_inner_plus_other I J x hIx hJx, ?_⟩
    · rw [← inner_conj_symm, ket_inner_plus_other J I x hJx hIx]
      simp
    · simp only [ket_inner, hIJ, if_false]

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathHilbertSupport
section

namespace WeldedPath.HilbertSupport

open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

theorem ketBra_apply (u : Hil Y) (v ψ : Hil X) :
    ketBra u v ψ = inner ℂ v ψ • u := rfl

theorem inner_ket [DecidableEq X] (x : X) (ψ : Hil X) :
    inner ℂ (ket x) ψ = ψ x := by
  simp [ket, EuclideanSpace.inner_single_left]

theorem ket_apply [DecidableEq X] (x y : X) :
    ket x y = if y = x then 1 else 0 := by
  simp [ket, PiLp.single_apply]

theorem ketTensor_apply (u : Hil A) (v : Hil X) (a : A) (x : X) :
    ketTensor u v (a, x) = u a * v x := rfl

theorem sum_basis [DecidableEq X] (ψ : Hil X) :
    (∑ x, ψ x • ket x) = ψ := by
  ext y
  simp [ket_apply]

theorem diagProj_apply [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) (x : X) :
    diagProj P ψ x = if P x then ψ x else 0 := by
  simp [diagProj, ketBra_apply, inner_ket, ket_apply]

theorem diagProj_zero_iff [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : diagProj P ψ = 0 ↔ ∀ x, P x → ψ x = 0 := by
  constructor
  · intro h x hx
    have he := congrArg (fun v : Hil X => v x) h
    simpa [diagProj_apply, hx] using he
  · intro h
    ext x
    by_cases hx : P x <;> simp [diagProj_apply, hx, h]

theorem diagProj_norm_le [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : ‖diagProj P ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x
  · simp [diagProj_apply, hx]
  · simp [diagProj_apply, hx]

theorem diagProj_ket [DecidableEq X] (P : X → Prop) [DecidablePred P] (x : X) :
    diagProj P (ket x) = if P x then ket x else 0 := by
  ext y
  by_cases hx : P x <;> by_cases hy : y = x <;>
    simp_all [diagProj_apply, ket_apply]

theorem opTensor_ket [DecidableEq A] [DecidableEq X]
    {B : Type*} [Fintype B] (S : Hil A →L[ℂ] Hil B) (T : Hil X →L[ℂ] Hil Y)
    (a : A) (x : X) :
    opTensor S T (ket (a, x)) = ketTensor (S (ket a)) (T (ket x)) := by
  simp [opTensor, ketBra_apply, inner_ket, ket_apply]

theorem tensor_ket_eq [DecidableEq A] [DecidableEq X] (a : A) (x : X) :
    ketTensor (ket a) (ket x) = ket (a, x) := by
  ext p
  obtain ⟨b, y⟩ := p
  by_cases ha : b = a <;> by_cases hx : y = x <;>
    simp [ketTensor_apply, ket_apply, ha, hx, Prod.mk.injEq]

theorem diagProj_tensor_zero [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (u : Hil A) (v : Hil X)
    (hv : ∀ x, P x → v x = 0) :
    diagProj (fun p : A × X => P p.2) (ketTensor u v) = 0 := by
  apply (diagProj_zero_iff _ _).mpr
  rintro ⟨a, x⟩ hx
  simp [ketTensor_apply, hv x hx]

theorem tensor_projector_annihilates [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (K : Submodule ℂ (Hil X))
    (hK : ∀ v ∈ K, ∀ x, P x → v x = 0) :
    (diagProj (fun p : A × X => P p.2)).comp
      (opTensor (1 : Hil A →L[ℂ] Hil A) K.starProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, smul_zero, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro p _
  rw [opTensor_ket]
  have hz := diagProj_tensor_zero P (ket p.1) (K.starProjection (ket p.2))
    (hK _ (K.starProjection_apply_mem _) )
  simpa using congrArg (fun v => ψ p • v) hz

end WeldedPath.HilbertSupport

end

-- Solutions.CompressedPermutationAction
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb HilbertSupport
open scoped BigOperators ComplexConjugate

variable {s : ℕ}

theorem plus_inner_ket_added (I J : InjDb s) (x y : Fin s)
    (hI : I x = none) (hJ : J x = none) (hy : J.symm y = none) :
    inner ℂ (plusState I x) (ket (J.addPair x y)) =
      if I = J then ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) else 0 := by
  unfold plusState
  rw [inner_smul_left, sum_inner]
  by_cases hij : I = J
  · subst J
    rw [if_pos rfl]
    have hs : (∑ z ∈ Finset.univ.filter (fun z => I.symm z = none),
        inner ℂ (ket (I.addPair x z)) (ket (I.addPair x y))) = 1 := by
      rw [Finset.sum_eq_single y]
      · rw [ket_inner, if_pos rfl]
      · intro z hz hzy
        rw [ket_inner, if_neg]
        exact fun he => hzy (addPair_injective I x hI
          (Finset.mem_filter.mp hz).2 hy he)
      · intro hn
        exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)).elim
    rw [hs]
    simp
  · rw [if_neg hij]
    have hs : (∑ z ∈ Finset.univ.filter (fun z => I.symm z = none),
        inner ℂ (ket (I.addPair x z)) (ket (J.addPair x y))) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      rw [ket_inner, if_neg]
      exact fun he => hij (addPair_eq_original I J x z y hI
        (Finset.mem_filter.mp hz).2 hJ hy he)
    rw [hs, mul_zero]

theorem ket_inner_added (I J : InjDb s) (x y : Fin s)
    (hI : I x = none) (hJ : J x = none) (hy : J.symm y = none) :
    inner ℂ (ket I) (ket (J.addPair x y)) = 0 := by
  rw [ket_inner, if_neg]
  intro he
  have hh := congrArg (fun K : InjDb s => K x) he
  rw [hI, addPair_apply_self J x y hJ hy] at hh
  cases hh

theorem pC_ket_unset (I : InjDb s) (x : Fin s) (hx : I x = none) :
    pC s x (ket I) = plusState I x := by
  have hterm (J : InjDb s) (hJ : J x = none) :
      (pCF (plusState J x) (ket J) - 1) (ket I) =
        if J = I then plusState I x - ket I else 0 := by
    have hp : inner ℂ (plusState J x) (ket I) = 0 := by
      rw [← inner_conj_symm, ket_inner_plus_other I J x hx hJ]
      simp
    change pCF _ _ _ - ket I = _
    rw [pCF_apply, hp, ket_inner]
    by_cases hji : J = I
    · subst J
      simp
    · simp [hji]
  unfold pC
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.sum_apply]
  have hs : (∑ J ∈ Finset.univ.filter (fun J : InjDb s => J x = none),
      (pCF (plusState J x) (ket J) - 1) (ket I)) = plusState I x - ket I := by
    rw [Finset.sum_eq_single I]
    · simpa only [ite_true] using hterm I hx
    · intro J hJ hji
      rw [hterm J (Finset.mem_filter.mp hJ).2, if_neg hji]
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).elim
  rw [hs]
  abel

theorem pC_ket_added (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) :
    pC s x (ket (I.addPair x y)) = ket (I.addPair x y) +
      ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) • (ket I - plusState I x) := by
  have hterm (J : InjDb s) (hJ : J x = none) :
      (pCF (plusState J x) (ket J) - 1) (ket (I.addPair x y)) =
        if J = I then ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) •
          (ket I - plusState I x) else 0 := by
    change pCF _ _ _ - ket (I.addPair x y) = _
    rw [pCF_apply, ket_inner_added J I x y hJ hx hy,
      plus_inner_ket_added J I x y hJ hx hy]
    by_cases hji : J = I
    · subst J
      simp only [ite_true, zero_smul, sub_zero, add_zero]
      module
    · simp [hji]
  unfold pC
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.sum_apply]
  congr 1
  rw [Finset.sum_eq_single I]
  · simpa only [ite_true] using hterm I hx
  · intro J hJ hji
    rw [hterm J (Finset.mem_filter.mp hJ).2, if_neg hji]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).elim

theorem pC_added_error_sq (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) :
    ‖(pC s x - 1) (ket (I.addPair x y))‖ ^ 2 =
      2 / ((s - I.size : ℕ) : ℝ) := by
  have hket : ‖ket I‖ ^ 2 = 1 := by
    calc
      _ = (inner ℂ (ket I) (ket I)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = 1 := by rw [ket_inner, if_pos rfl]; rfl
  have hplus : ‖plusState I x‖ ^ 2 = 1 := by
    calc
      _ = (inner ℂ (plusState I x) (plusState I x)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = 1 := by rw [plusState_inner_self I x hx]; rfl
  have hdiff : ‖ket I - plusState I x‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), ket_inner_plusState I x hx, hket, hplus]
    norm_num
  have he : (pC s x - 1) (ket (I.addPair x y)) =
      ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) • (ket I - plusState I x) := by
    change pC s x _ - ket (I.addPair x y) = _
    rw [pC_ket_added I x y hx hy]
    abel
  rw [he, norm_smul, mul_pow, hdiff, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

end WeldedPath.CompressedPrimitive

end

-- Solutions.CompressedPermutationInsertionBlock
section

namespace WeldedPath.CompressedPrimitive

open Classical HilbertSupport
open scoped BigOperators

noncomputable def insertionBlock (s : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none), ketBra (plusState I x) (ket I)

noncomputable def unsetBlock (s : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  diagProj (fun I : InjDb s => I x = none)

noncomputable def plusBlock (s : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none),
    ketBra (plusState I x) (plusState I x)

theorem insertionBlock_ket {s : ℕ} (x : Fin s) (I : InjDb s) :
    insertionBlock s x (ket I) = if I x = none then plusState I x else 0 := by
  simp [insertionBlock, ContinuousLinearMap.sum_apply, ketBra_apply, ket_inner]

theorem insertionBlock_adjoint (s : ℕ) (x : Fin s) :
    ContinuousLinearMap.adjoint (insertionBlock s x) =
      ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none), ketBra (ket I) (plusState I x) := by
  simp only [insertionBlock, map_sum, ketBra_eq_rankOne, InnerProductSpace.adjoint_rankOne]

theorem insertionBlock_adjoint_plus {s : ℕ} (x : Fin s) (I : InjDb s) (hx : I x = none) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (plusState I x) = ket I := by
  rw [insertionBlock_adjoint]
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  rw [Finset.sum_eq_single I]
  · rw [plusState_inner_self I x hx, one_smul]
  · intro J hJ hJI
    rw [plus_inner_plus_other J I x (Finset.mem_filter.mp hJ).2 hx hJI, zero_smul]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)).elim

theorem insertionBlock_adjoint_ket_added {s : ℕ} (x y : Fin s) (I : InjDb s)
    (hx : I x = none) (hy : I.symm y = none) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (ket (I.addPair x y)) =
      ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) • ket I := by
  rw [insertionBlock_adjoint]
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  rw [Finset.sum_eq_single I]
  · rw [plus_inner_ket_added I I x y hx hx hy, if_pos rfl]
  · intro J hJ hJI
    rw [plus_inner_ket_added J I x y (Finset.mem_filter.mp hJ).2 hx hy,
      if_neg hJI, zero_smul]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)).elim

theorem insertionBlock_adjoint_comp (s : ℕ) (x : Fin s) :
    (ContinuousLinearMap.adjoint (insertionBlock s x)).comp (insertionBlock s x) = unsetBlock s x := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  change ContinuousLinearMap.adjoint (insertionBlock s x) (insertionBlock s x (ket I)) = _
  rw [insertionBlock_ket, unsetBlock, diagProj_ket]
  by_cases hx : I x = none
  · simp only [if_pos hx, insertionBlock_adjoint_plus x I hx]
  · simp only [if_neg hx, map_zero]

theorem insertionBlock_comp_adjoint (s : ℕ) (x : Fin s) :
    (insertionBlock s x).comp (ContinuousLinearMap.adjoint (insertionBlock s x)) = plusBlock s x := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [ContinuousLinearMap.comp_apply, insertionBlock_adjoint]
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply, map_sum, map_smul]
  change (∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x = none),
    inner ℂ (plusState I x) ψ • insertionBlock s x (ket I)) = _
  unfold plusBlock
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  apply Finset.sum_congr rfl
  intro I hI
  rw [insertionBlock_ket, if_pos (Finset.mem_filter.mp hI).2]

theorem insertionBlock_eq_pC_unset (s : ℕ) (x : Fin s) :
    insertionBlock s x = (pC s x).comp (unsetBlock s x) := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  rw [ContinuousLinearMap.comp_apply, insertionBlock_ket, unsetBlock, diagProj_ket]
  by_cases hx : I x = none
  · simp only [if_pos hx, pC_ket_unset I x hx]
  · simp only [if_neg hx, map_zero]

theorem insertionBlock_norm_le (s : ℕ) (x : Fin s) (ψ : Hil (InjDb s)) :
    ‖insertionBlock s x ψ‖ ≤ ‖ψ‖ := by
  rw [insertionBlock_eq_pC_unset, ContinuousLinearMap.comp_apply, pC_norm_map]
  exact diagProj_norm_le _ ψ

theorem insertionBlock_opNorm_le (s : ℕ) (x : Fin s) : ‖insertionBlock s x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using insertionBlock_norm_le s x ψ

theorem insertionBlock_adjoint_norm_le (s : ℕ) (x : Fin s) (ψ : Hil (InjDb s)) :
    ‖ContinuousLinearMap.adjoint (insertionBlock s x) ψ‖ ≤ ‖ψ‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint (insertionBlock s x)‖ * ‖ψ‖ :=
      (ContinuousLinearMap.adjoint (insertionBlock s x)).le_opNorm ψ
    _ = ‖insertionBlock s x‖ * ‖ψ‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right (insertionBlock_opNorm_le s x) (norm_nonneg _)
    _ = _ := one_mul _

theorem pC_insertion_block (s : ℕ) (x : Fin s) :
    pC s x = insertionBlock s x + ContinuousLinearMap.adjoint (insertionBlock s x) + 1 -
      unsetBlock s x - (insertionBlock s x).comp (ContinuousLinearMap.adjoint (insertionBlock s x)) := by
  rw [insertionBlock_comp_adjoint, insertionBlock_adjoint]
  simp only [pC, pCF_delta]
  simp only [sub_eq_add_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib,
    insertionBlock,unsetBlock,diagProj,plusBlock]
  abel

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathCompletionLevels
section

namespace WeldedPath.CompletionLevels

open Classical InjDb
open scoped BigOperators

variable {s : ℕ}

theorem size_le (I : InjDb s) : I.size ≤ s := by
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card (Finset.filter_subset (fun x => (I x).isSome) Finset.univ))

theorem exists_unset (I : InjDb s) (hI : I.size < s) : ∃ x, I x = none := by
  by_contra! hn
  have hall : ∀ x, (I x).isSome := by
    intro x
    cases h : I x with
    | none => exact (hn x h).elim
    | some y => rfl
  have heq : I.size = s := by simp [InjDb.size, hall]
  omega

theorem size_addPair (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) :
    (I.addPair x y).size = I.size + 1 := by
  have hset : (Finset.univ.filter fun u => ((I.addPair x y) u).isSome) =
      insert x (Finset.univ.filter fun u => (I u).isSome) := by
    ext u
    by_cases hu : u = x
    · subst u
      simp [InjDb.addPair, hx, hy]
    · simp [InjDb.addPair, hx, hy, hu]
  have hnot : x ∉ Finset.univ.filter (fun u => (I u).isSome) := by simp [hx]
  exact (congrArg Finset.card hset).trans (Finset.card_insert_of_notMem hnot)

theorem unused_of_extends (I : InjDb s) (x : Fin s) (hx : I x = none)
    (φ : Equiv.Perm (Fin s)) (hφ : Extends φ I) : I.symm (φ x) = none := by
  cases h : I.symm (φ x) with
  | none => rfl
  | some z =>
    have hz : I z = some (φ x) := (I.inv z (φ x)).mp h
    have heq : z = x := φ.injective (hφ z (φ x) hz)
    subst z
    rw [hx] at hz
    cases hz

theorem extends_addPair_iff (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) (φ : Equiv.Perm (Fin s)) :
    Extends φ (I.addPair x y) ↔ Extends φ I ∧ φ x = y := by
  constructor
  · intro h
    refine ⟨?_, h x y (CompressedPrimitive.addPair_apply_self I x y hx hy)⟩
    intro u v huv
    have hux : u ≠ x := by
      intro heq
      subst u
      rw [hx] at huv
      cases huv
    exact h u v (by simp [InjDb.addPair, hx, hy, hux, huv])
  · rintro ⟨h, heq⟩ u v huv
    by_cases hux : u = x
    · subst u
      have hv : y = v := by simpa [InjDb.addPair, hx, hy] using huv
      exact heq.trans hv
    · exact h u v (by simpa [InjDb.addPair, hx, hy, hux] using huv)

noncomputable def rawCompletion (I : InjDb s) : Hil (Equiv.Perm (Fin s)) :=
  ∑ φ ∈ Finset.univ.filter (fun φ : Equiv.Perm (Fin s) => Extends φ I), ket φ

theorem rawCompletion_apply (I : InjDb s) (φ : Equiv.Perm (Fin s)) :
    rawCompletion I φ = if Extends φ I then 1 else 0 := by
  simp [rawCompletion, HilbertSupport.ket_apply]

theorem completion_mem_iff (M : Submodule ℂ (Hil (Equiv.Perm (Fin s))))
    (I : InjDb s) : completion I ∈ M ↔ rawCompletion I ∈ M := by
  have hpos : 0 < Real.sqrt (((s - I.size).factorial : ℕ) : ℝ) := by positivity
  have hnz : (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (ne_of_gt hpos)
  apply M.smul_mem_iff
  simpa only [Complex.ofReal_inv] using hnz

theorem rawCompletion_extension (I : InjDb s) (x : Fin s) (hx : I x = none) :
    rawCompletion I = ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      rawCompletion (I.addPair x y) := by
  ext φ
  simp only [WithLp.ofLp_sum, Finset.sum_apply, rawCompletion_apply]
  by_cases hφ : Extends φ I
  · rw [if_pos hφ]
    symm
    rw [Finset.sum_eq_single (φ x)]
    · rw [if_pos ((extends_addPair_iff I x (φ x) hx
        (unused_of_extends I x hx φ hφ) φ).mpr ⟨hφ, rfl⟩)]
    · intro y hy hne
      apply if_neg
      intro he
      exact hne (((extends_addPair_iff I x y hx (Finset.mem_filter.mp hy).2 φ).mp he).2.symm)
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        unused_of_extends I x hx φ hφ⟩)).elim
  · rw [if_neg hφ]
    symm
    apply Finset.sum_eq_zero
    intro y hy
    apply if_neg
    intro he
    exact hφ (((extends_addPair_iff I x y hx (Finset.mem_filter.mp hy).2 φ).mp he).1)

theorem Hle_succ (r : ℕ) (hr : r < s) : Hle s r ≤ Hle s (r + 1) := by
  apply Submodule.span_le.mpr
  rintro v ⟨I, hI, rfl⟩
  obtain ⟨x, hx⟩ := exists_unset I (by omega)
  apply (completion_mem_iff _ I).mpr
  rw [rawCompletion_extension I x hx]
  apply Submodule.sum_mem
  intro y hy
  apply (completion_mem_iff _ _).mp
  apply Submodule.subset_span
  refine ⟨I.addPair x y, ?_, rfl⟩
  rw [size_addPair I x y hx (Finset.mem_filter.mp hy).2, hI]

theorem Hle_mono {r t : ℕ} (hrt : r ≤ t) (ht : t ≤ s) : Hle s r ≤ Hle s t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrt
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega) (by omega)).trans (by simpa [Nat.add_assoc] using
      (Hle_succ (s := s) (r + d) (by omega)))

theorem Hle_eq_bot {r : ℕ} (hr : s < r) : Hle s r = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro v ⟨I, hI, _⟩
  have := size_le I
  omega

theorem Hlevel_le (r : ℕ) : Hlevel s r ≤ Hle s r := by
  cases r with
  | zero => exact le_rfl
  | succ r => exact inf_le_left

theorem Hlevel_pairwise_orthogonal (r t : ℕ) (hrt : r ≠ t)
    (u v : Hil (Equiv.Perm (Fin s))) (hu : u ∈ Hlevel s r) (hv : v ∈ Hlevel s t) :
    inner ℂ u v = 0 := by
  have hlt : ∀ {a b : ℕ}, a < b → ∀ x ∈ Hlevel s a, ∀ y ∈ Hlevel s b,
      inner ℂ x y = 0 := by
    intro a b hab x hx y hy
    by_cases hb : b ≤ s
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      have hx' : x ∈ Hle s b := Hle_mono (by omega) (by omega) (Hlevel_le a hx)
      exact ((Hle s b).mem_orthogonal y).mp hy.2 x hx'
    · have hy' : y ∈ (⊥ : Submodule ℂ (Hil (Equiv.Perm (Fin s)))) := by
        simpa only [Hle_eq_bot (by omega : s < b)] using Hlevel_le b hy
      have : y = 0 := hy'
      simp [this]
  rcases lt_or_gt_of_ne hrt with h | h
  · exact hlt h u hu v hv
  · rw [← inner_conj_symm, hlt h v hv u hu]
    simp

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathCompletionExtension
section

namespace WeldedPath.CompletionLevels

open Classical InjDb
open scoped BigOperators

variable {s : ℕ}

theorem size_lt_of_unset (I : InjDb s) (x : Fin s) (hx : I x = none) : I.size < s := by
  have hproper : (Finset.univ.filter fun u => (I u).isSome) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ Finset.univ.filter (fun u => (I u).isSome) := by
      rw [he]
      exact Finset.mem_univ x
    simpa [hx] using hm
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hproper

theorem inv_sqrt_factorial_succ (m : ℕ) :
    (Real.sqrt (m.factorial : ℝ))⁻¹ =
      Real.sqrt ((m + 1 : ℕ) : ℝ) * (Real.sqrt ((m + 1).factorial : ℝ))⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  have hn : Real.sqrt ((m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hf : Real.sqrt (m.factorial : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp

theorem completion_extension (I : InjDb s) (x : Fin s) (hx : I x = none) :
    ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), completion (I.addPair x y) =
      (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) • completion I := by
  let m := s - I.size - 1
  have hm : s - I.size = m + 1 := by
    have := size_lt_of_unset I x hx
    dsimp [m]
    omega
  have hsum : ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      completion (I.addPair x y) =
      ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) •
        ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), rawCompletion (I.addPair x y) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    change ((Real.sqrt ((s - (I.addPair x y).size).factorial : ℝ))⁻¹ : ℂ) • _ = _
    rw [size_addPair I x y hx (Finset.mem_filter.mp hy).2]
    have he : s - (I.size + 1) = m := by dsimp [m]; omega
    rw [he]
    rfl
  rw [hsum, ← rawCompletion_extension I x hx]
  change ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) • rawCompletion I =
    (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) •
      (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) • rawCompletion I)
  rw [smul_smul, hm]
  congr 1
  exact_mod_cast inv_sqrt_factorial_succ m

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathEncodedOracleUnitary
section

namespace WeldedPath.EncodedOracleUnitary

open Classical QAlgorithms HilbertSupport CompressedPrimitive Supplement
open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

theorem basisMap_apply_equiv [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (ψ : Hil X) (x : X) : basisMap e ψ (e x) = ψ x := by
  simp [basisMap, ketBra_apply, inner_ket, ket_apply, e.injective.eq_iff]

theorem basisMap_equiv_norm [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (ψ : Hil X) : ‖basisMap e ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  rw [← Equiv.sum_comp e (fun y => ‖basisMap e ψ y‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro x _
  rw [basisMap_apply_equiv]

theorem basisMap_involutive_norm [DecidableEq X]
    (f : X → X) (hf : Function.Involutive f) (ψ : Hil X) :
    ‖basisMap f ψ‖ = ‖ψ‖ :=
  basisMap_equiv_norm (hf.toPerm f) ψ

noncomputable def slice (ψ : Hil (A × X)) (a : A) : Hil X :=
  WithLp.toLp 2 (fun x => ψ (a, x))

theorem opTensor_one_apply [DecidableEq A] [DecidableEq X]
    (T : Hil X →L[ℂ] Hil Y) (ψ : Hil (A × X)) (a : A) (y : Y) :
    opTensor (1 : Hil A →L[ℂ] Hil A) T ψ (a, y) = T (slice ψ a) y := by
  conv_rhs => rw [← sum_basis (slice ψ a)]
  simp [opTensor, ketBra_apply, inner_ket, ketTensor_apply,
    Fintype.sum_prod_type, ket_apply, slice]

theorem sum_slice_norm_sq (ψ : Hil (A × X)) :
    (∑ a, ‖slice ψ a‖ ^ 2) = ‖ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, slice,
    PiLp.toLp_apply]

theorem opTensor_one_norm [DecidableEq A] [DecidableEq X]
    (T : Hil X →L[ℂ] Hil Y) (hT : ∀ ψ, ‖T ψ‖ = ‖ψ‖) (ψ : Hil (A × X)) :
    ‖opTensor (1 : Hil A →L[ℂ] Hil A) T ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← sum_slice_norm_sq, ← sum_slice_norm_sq]
  apply Finset.sum_congr rfl
  intro a _
  have hs : slice (opTensor (1 : Hil A →L[ℂ] Hil A) T ψ) a = T (slice ψ a) := by
    ext y
    exact opTensor_one_apply T ψ a y
  rw [hs, hT]

theorem adjoint_norm_of_norm (U : Hil X →L[ℂ] Hil X)
    (hU : ∀ ψ, ‖U ψ‖ = ‖ψ‖) (ψ : Hil X) :
    ‖ContinuousLinearMap.adjoint U ψ‖ = ‖ψ‖ := by
  have he : (ContinuousLinearMap.adjoint U).comp U = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mp hU
  have hi : Function.LeftInverse (ContinuousLinearMap.adjoint U) U := by
    intro v
    exact congrArg (fun T : Hil X →L[ℂ] Hil X => T v) he
  have hsurj : Function.Surjective U :=
    LinearMap.surjective_of_injective (f := U.toLinearMap) hi.injective
  obtain ⟨v, rfl⟩ := hsurj ψ
  rw [hi v, hU v]

theorem qubits_add_cancel {d : ℕ} (a b : Qubits d) : a + b + b = a := by
  funext i
  change a i + b i + b i = a i
  cases a i <;> cases b i <;> rfl

theorem stdQueryE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × Equiv.Perm (Fin s))) :
    ‖stdQueryE enc x inv ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  rintro ⟨a, π⟩
  exact Prod.ext (qubits_add_cancel a _) rfl

theorem purifiedXorE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (ψ : Hil (Qubits d × InjDb s)) :
    ‖purifiedXorE enc x ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  rintro ⟨a, I⟩
  cases h : I x with
  | none => simp only [h]
  | some y => simp only [h, qubits_add_cancel]

theorem flipDb_norm (s : ℕ) (ψ : Hil (InjDb s)) : ‖flipDb s ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  exact PEquiv.symm_symm

theorem cpOE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖cpOE enc x inv ψ‖ = ‖ψ‖ := by
  let pc := opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (pC s x)
  let fl := opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (flipDb s)
  have hpc : ∀ v, ‖pc v‖ = ‖v‖ := opTensor_one_norm (pC s x) (pC_norm_map s x)
  have hfl : ∀ v, ‖fl v‖ = ‖v‖ := opTensor_one_norm (flipDb s) (flipDb_norm s)
  have hpc' : ∀ v, ‖ContinuousLinearMap.adjoint pc v‖ = ‖v‖ :=
    adjoint_norm_of_norm pc hpc
  have hfl' : ∀ v, ‖ContinuousLinearMap.adjoint fl v‖ = ‖v‖ :=
    adjoint_norm_of_norm fl hfl
  change ‖(if inv then fl.comp
    ((pc.comp ((purifiedXorE enc x).comp (ContinuousLinearMap.adjoint pc))).comp
      (ContinuousLinearMap.adjoint fl))
    else pc.comp ((purifiedXorE enc x).comp (ContinuousLinearMap.adjoint pc))) ψ‖ = _
  cases inv <;> simp only [Bool.false_eq_true, if_false, if_true,
    ContinuousLinearMap.comp_apply, hpc, hfl, purifiedXorE_norm, hpc', hfl']

theorem cpOE_adjoint_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖ContinuousLinearMap.adjoint (cpOE enc x inv) ψ‖ = ‖ψ‖ :=
  adjoint_norm_of_norm _ (cpOE_norm enc x inv) ψ

theorem cpOE_norm_le {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖cpOE enc x inv ψ‖ ≤ ‖ψ‖ := (cpOE_norm enc x inv ψ).le

end WeldedPath.EncodedOracleUnitary

end

-- Solutions.WeldedPathOperatorPolar
section

namespace WeldedPath.OperatorPolar

open scoped BigOperators
open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma inv_sqrt_scalar (x : ℝ) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = (Real.sqrt x)⁻¹ := by
  by_cases hx : x ≤ 0
  · simp [Real.sqrt_eq_zero_of_nonpos hx]
  · have hx' : 0 < x := lt_of_not_ge hx
    have hh : (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ * x = 1 := by
      rw [← mul_inv, ← pow_two, Real.sq_sqrt hx'.le, inv_mul_cancel₀ (ne_of_gt hx')]
    rw [hh, one_mul]

noncomputable def invSqrt (A : Hil X →L[ℂ] Hil X) : Hil X →L[ℂ] Hil X :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A

lemma invSqrt_adjoint (A : Hil X →L[ℂ] Hil X) :
    ContinuousLinearMap.adjoint (invSqrt A) = invSqrt A := by
  change star (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A) = _
  rw [← cfc_star]
  simp only [star_trivial]
  rfl

lemma invSqrt_sandwich (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    invSqrt A * invSqrt A * A * invSqrt A = invSqrt A := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  by_cases hf : ContinuousOn f (spectrum ℝ A)
  · have hff := cfc_mul f f A hf hf
    have hffi := cfc_mul (fun x => f x * f x) (fun x : ℝ => x) A
      (hf.mul hf) continuousOn_id
    have hffif := cfc_mul (fun x => f x * f x * x) f A
      ((hf.mul hf).mul continuousOn_id) hf
    calc
      _ = cfc (fun x => f x * f x * x * f x) A := by
        rw [hffif, hffi, hff, cfc_id' ℝ A hA]
        rfl
      _ = _ := cfc_congr (fun x _ => inv_sqrt_scalar x)
  · have hz : invSqrt A = 0 := cfc_apply_of_not_continuousOn A hf
    simp only [hz, zero_mul, mul_zero]

lemma invSqrt_commute (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    Commute (invSqrt A) A := by
  have h := cfc_commute_cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) A
  rwa [cfc_id' ℝ A hA] at h

lemma invSqrt_range_factor (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    invSqrt A = A * invSqrt A * invSqrt A * invSqrt A := by
  have hc := (invSqrt_commute A hA).eq
  calc
    _ = invSqrt A * invSqrt A * A * invSqrt A := (invSqrt_sandwich A hA).symm
    _ = invSqrt A * (invSqrt A * A) * invSqrt A := by simp only [mul_assoc]
    _ = invSqrt A * (A * invSqrt A) * invSqrt A := by rw [hc]
    _ = (invSqrt A * A) * invSqrt A * invSqrt A := by simp only [mul_assoc]
    _ = _ := by rw [hc]

lemma invSqrt_mapsTo (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A)
    (K : Submodule ℂ (Hil X)) (hK : ∀ ψ, A ψ ∈ K) (ψ : Hil X) :
    invSqrt A ψ ∈ K := by
  rw [invSqrt_range_factor A hA]
  exact hK _

noncomputable def polarMap (T : Hil X →L[ℂ] Hil Y) : Hil Y →L[ℂ] Hil X :=
  (ContinuousLinearMap.adjoint T).comp (invSqrt (T.comp (ContinuousLinearMap.adjoint T)))

lemma gram_selfadjoint (T : Hil X →L[ℂ] Hil Y) :
    IsSelfAdjoint (T.comp (ContinuousLinearMap.adjoint T)) := by
  change ContinuousLinearMap.adjoint (T.comp (ContinuousLinearMap.adjoint T)) = _
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem polarMap_partial (T : Hil X →L[ℂ] Hil Y) :
    ((polarMap T).comp (ContinuousLinearMap.adjoint (polarMap T))).comp (polarMap T) =
      polarMap T := by
  let B := invSqrt (T.comp (ContinuousLinearMap.adjoint T))
  have hB : ((B.comp B).comp (T.comp (ContinuousLinearMap.adjoint T))).comp B = B := by
    exact invSqrt_sandwich _ (gram_selfadjoint T)
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change (((ContinuousLinearMap.adjoint T).comp B).comp
    (B.comp T)).comp ((ContinuousLinearMap.adjoint T).comp B) =
      (ContinuousLinearMap.adjoint T).comp B
  calc
    _ = (ContinuousLinearMap.adjoint T).comp
        (((B.comp B).comp (T.comp (ContinuousLinearMap.adjoint T))).comp B) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [hB]

end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathIntertwinerPartial
section

namespace WeldedPath.IntertwinerPartial

open Classical OperatorPolar HilbertSupport
open scoped BigOperators

lemma Gam_range (s r : ℕ) (ψ : Hil (InjDb s)) : Gam s r ψ ∈ Hlevel s r := by
  unfold Gam
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  apply Submodule.sum_mem
  intro I hI
  exact Submodule.smul_mem _ _ ((Hlevel s r).starProjection_apply_mem (completion I))

lemma Gam_ket (s r : ℕ) (I : InjDb s) :
    Gam s r (ket I) = if I.size = r then projLevel s r (completion I) else 0 := by
  simp [Gam, ketBra_apply, inner_ket, ket_apply]

lemma Gam_adjoint_support (s r : ℕ) (ψ : Hil (Equiv.Perm (Fin s)))
    (I : InjDb s) (hI : I.size ≠ r) : ContinuousLinearMap.adjoint (Gam s r) ψ I = 0 := by
  rw [← inner_ket I, ContinuousLinearMap.adjoint_inner_right, Gam_ket,
    if_neg hI, inner_zero_left]

lemma Gam_comp_adjoint_zero (s r t : ℕ) (hrt : r ≠ t) :
    (Gam s r).comp (ContinuousLinearMap.adjoint (Gam s t)) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  change Gam s r (ContinuousLinearMap.adjoint (Gam s t) ψ) = 0
  rw [← sum_basis (ContinuousLinearMap.adjoint (Gam s t) ψ)]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro I _
  by_cases hI : I.size = r
  · rw [Gam_adjoint_support s t ψ I (by omega), zero_smul]
  · rw [Gam_ket, if_neg hI, smul_zero]

lemma GramInvSqrt_eq (s r : ℕ) : GramInvSqrt s r = invSqrt (Gram s r) := rfl

lemma Gram_selfadjoint (s r : ℕ) : IsSelfAdjoint (Gram s r) := gram_selfadjoint (Gam s r)

lemma GramInvSqrt_range (s r : ℕ) (ψ : Hil (Equiv.Perm (Fin s))) :
    GramInvSqrt s r ψ ∈ Hlevel s r :=
  invSqrt_mapsTo _ (Gram_selfadjoint s r) (Hlevel s r)
    (fun v => Gam_range s r (ContinuousLinearMap.adjoint (Gam s r) v)) ψ

lemma GramInvSqrt_adjoint (s r : ℕ) :
    ContinuousLinearMap.adjoint (GramInvSqrt s r) = GramInvSqrt s r :=
  invSqrt_adjoint _

lemma GramInvSqrt_comp_zero (s r t : ℕ) (hrt : r ≠ t) :
    (GramInvSqrt s r).comp (GramInvSqrt s t) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_left ℂ
  intro η
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, inner_zero_right]
  have he := ContinuousLinearMap.adjoint_inner_right (GramInvSqrt s r) η
    (GramInvSqrt s t ψ)
  rw [GramInvSqrt_adjoint] at he
  rw [he]
  exact CompletionLevels.Hlevel_pairwise_orthogonal r t hrt _ _
    (GramInvSqrt_range s r η) (GramInvSqrt_range s t ψ)

lemma polar_Gam_cross_final (s r t : ℕ) (hrt : r ≠ t) :
    (polarMap (Gam s r)).comp (ContinuousLinearMap.adjoint (polarMap (Gam s t))) = 0 := by
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change ((ContinuousLinearMap.adjoint (Gam s r)).comp (GramInvSqrt s r)).comp
    ((GramInvSqrt s t).comp (Gam s t)) = 0
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (GramInvSqrt s r) (GramInvSqrt s t) (Gam s t), GramInvSqrt_comp_zero s r t hrt]
  simp

lemma polar_Gam_cross_initial (s r t : ℕ) (hrt : r ≠ t) :
    (ContinuousLinearMap.adjoint (polarMap (Gam s r))).comp (polarMap (Gam s t)) = 0 := by
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change ((GramInvSqrt s r).comp (Gam s r)).comp
    ((ContinuousLinearMap.adjoint (Gam s t)).comp (GramInvSqrt s t)) = 0
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (Gam s r) (ContinuousLinearMap.adjoint (Gam s t)) (GramInvSqrt s t),
    Gam_comp_adjoint_zero s r t hrt]
  simp

theorem sum_partial {X Y ι : Type*} [Fintype X] [Fintype Y]
    (S : Finset ι) (V : ι → Hil X →L[ℂ] Hil Y)
    (hp : ∀ i ∈ S, ((V i).comp (ContinuousLinearMap.adjoint (V i))).comp (V i) = V i)
    (hf : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (V i).comp (ContinuousLinearMap.adjoint (V j)) = 0)
    (hi : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (ContinuousLinearMap.adjoint (V i)).comp (V j) = 0) :
    (((∑ i ∈ S, V i).comp (ContinuousLinearMap.adjoint (∑ i ∈ S, V i))).comp
      (∑ i ∈ S, V i)) = ∑ i ∈ S, V i := by
  classical
  simp only [map_sum, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  apply Finset.sum_congr rfl
  intro i hiS
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · exact hp i hiS
    · intro j hj hji
      rw [hf j hj i hiS hji]
      simp
    · exact fun h => (h hiS).elim
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro k hk
    rw [ContinuousLinearMap.comp_assoc, hi j hj i hiS hji]
    simp
  · exact fun h => (h hiS).elim

theorem intertwiner_partial (s : ℕ) :
    ((intertwiner s).comp (ContinuousLinearMap.adjoint (intertwiner s))).comp
      (intertwiner s) = intertwiner s := by
  change (((∑ r ∈ Finset.range s, polarMap (Gam s r)).comp
    (ContinuousLinearMap.adjoint (∑ r ∈ Finset.range s, polarMap (Gam s r)))).comp
      (∑ r ∈ Finset.range s, polarMap (Gam s r))) =
        ∑ r ∈ Finset.range s, polarMap (Gam s r)
  exact sum_partial _ _ (fun r _ => polarMap_partial (Gam s r))
    (fun r _ t _ hrt => polar_Gam_cross_final s r t hrt)
    (fun r _ t _ hrt => polar_Gam_cross_initial s r t hrt)

end WeldedPath.IntertwinerPartial

end

-- Solutions.WeldedPathCoefficientStability
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem norm_sum_sq_le_card_sum {ι : Type*} [Fintype ι] (v : ι → E) :
    ‖∑ i, v i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  have hs := norm_sum_le (Finset.univ : Finset ι) v
  have hsq : ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr hs
  exact hsq.trans (by simpa using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖)))

/-- Components lying in the discarded kernel have zero inner product with a minimal
representative. Removing those components cannot decrease the norm of its collision projection. -/
theorem collision_remove_kernel (K C : Submodule ℂ E) (f k r : E)
    (hf : f ∈ Kᗮ) (hk : k ∈ K) (hkC : k ∈ C)
    (hdec : C.starProjection f = k + r) :
    ‖C.starProjection f‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  have horth : inner ℂ (C.starProjection f) k = 0 := by
    rw [C.inner_starProjection_left_eq_right,
      C.starProjection_eq_self_iff.mpr hkC]
    exact (K.mem_orthogonal' f).mp hf k hk
  have hneg : inner ℂ (C.starProjection f) (-k) = 0 := by
    simp only [inner_neg_right, horth, neg_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (C.starProjection f) (-k) hneg
  have he : C.starProjection f + -k = r := by rw [hdec]; abel
  rw [he, norm_neg] at hpy
  nlinarith [sq_nonneg ‖k‖]

/-- The collision estimate on arbitrary coefficient combinations. Fixed collision
parts lie in the discarded kernel; free parts are bounded separately, and their
energy is controlled by the orthogonal coefficient decomposition. -/
theorem collision_from_decomposition {ι : Type*} [Fintype ι]
    (K C : Submodule ℂ E) (f : E) (hf : f ∈ Kᗮ)
    (v k r : ι → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hdec : C.starProjection f = (∑ i, k i) + ∑ i, r i)
    (hk : ∀ i, k i ∈ K) (hkC : ∀ i, k i ∈ C)
    (hr : ∀ i, ‖r i‖ ^ 2 ≤ ε * ‖v i‖ ^ 2)
    (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖C.starProjection f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖∑ i, r i‖ ^ 2 := collision_remove_kernel K C f _ _ hf
      (K.sum_mem fun i _ => hk i) (C.sum_mem fun i _ => hkC i) hdec
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, ‖r i‖ ^ 2 := norm_sum_sq_le_card_sum r
    _ ≤ (Fintype.card ι : ℝ) * (ε * ∑ i, ‖v i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hr i
    _ ≤ (Fintype.card ι : ℝ) * (ε * ‖f‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy hε) (by positivity)
    _ = _ := by ring

theorem projection_injective_on_minimal (S R : Submodule ℂ E) {f g : E}
    (hfS : f ∈ S) (hgS : g ∈ S)
    (hf : f ∈ (S ⊓ Rᗮ)ᗮ) (hg : g ∈ (S ⊓ Rᗮ)ᗮ)
    (he : R.starProjection f = R.starProjection g) : f = g := by
  have hzero : R.starProjection (f - g) = 0 := by rw [map_sub, he, sub_self]
  have hker : f - g ∈ S ⊓ Rᗮ :=
    ⟨S.sub_mem hfS hgS, R.starProjection_apply_eq_zero_iff.mp hzero⟩
  have horth : f - g ∈ (S ⊓ Rᗮ)ᗮ := (S ⊓ Rᗮ)ᗮ.sub_mem hf hg
  have heq : f - g = 0 := inner_self_eq_zero.mp
    (((S ⊓ Rᗮ).mem_orthogonal (f - g)).mp horth (f - g) hker)
  exact sub_eq_zero.mp heq

/-- The stable coefficient representative: remove the kernel of the injectivity
projection, then use the collision estimate to bound the representative's energy. -/
theorem stable_representative (S R : Submodule ℂ E)
    (hsmall : ∀ f ∈ S, f ∈ (S ⊓ Rᗮ)ᗮ →
      ‖Rᗮ.starProjection f‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2)
    (f₀ : E) (hf₀ : f₀ ∈ S) :
    ∃! f : E, f ∈ S ∧ f ∈ (S ⊓ Rᗮ)ᗮ ∧
      R.starProjection f = R.starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2 := by
  let K : Submodule ℂ E := S ⊓ Rᗮ
  let f := f₀ - K.starProjection f₀
  have hk : K.starProjection f₀ ∈ K := K.starProjection_apply_mem _
  have hfS : f ∈ S := S.sub_mem hf₀ hk.1
  have hfK : f ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f₀
  have hRf : R.starProjection f = R.starProjection f₀ := by
    dsimp [f]
    rw [map_sub, R.starProjection_apply_eq_zero_iff.mpr hk.2, sub_zero]
  have hbound : ‖f‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2 := by
    have hp := R.norm_sq_eq_add_norm_sq_starProjection f
    have hs := hsmall f hfS hfK
    rw [hRf] at hp
    linarith
  refine ⟨f, ⟨hfS, hfK, hRf, hbound⟩, ?_⟩
  intro g hg
  exact projection_injective_on_minimal S R hg.1 hfS hg.2.1 hfK (hg.2.2.1.trans hRf.symm)

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathOrthogonalCollision
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι]

theorem norm_sum_sq_orthogonal (v : ι → E)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  have aux (s : Finset ι) : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hz : inner ℂ (v i) (∑ j ∈ s, v j) = 0 := by
        rw [inner_sum]
        exact Finset.sum_eq_zero (fun j hj => horth i j (fun he => hi (he ▸ hj)))
      have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v i) (∑j∈s,v j) hz
      simpa only [← pow_two, ih] using hp
  exact aux Finset.univ

/-- In a collision-orthogonal decomposition, fixed collision pieces vanish
individually by minimality. The remaining estimates add without a term-count
loss, which is essential for collisions between distinct graph components. -/
theorem orthogonal_collision_bound (K C : Submodule ℂ E)
    (f : E) (hf : f ∈ Kᗮ) (v : ι → E) (hdec : (∑ i, v i) = f)
    (horth : ∀ i j, i ≠ j →
      inner ℂ (C.starProjection (v i)) (C.starProjection (v j)) = 0)
    (fixed : ι → Prop)
    (hfixed : ∀ i, fixed i → C.starProjection (v i) ∈ K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hfree : ∀ i, ¬fixed i → ‖C.starProjection (v i)‖ ^ 2 ≤ ε * ‖v i‖ ^ 2)
    (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖C.starProjection f‖ ^ 2 ≤ ε * ‖f‖ ^ 2 := by
  classical
  have hzero (i : ι) (hi : fixed i) : C.starProjection (v i) = 0 := by
    have hz : inner ℂ (C.starProjection f) (C.starProjection (v i)) = 0 := by
      rw [C.inner_starProjection_left_eq_right,
        C.starProjection_eq_self_iff.mpr (C.starProjection_apply_mem _)]
      exact (K.mem_orthogonal' f).mp hf _ (hfixed i hi)
    rw [← hdec, map_sum, sum_inner] at hz
    have he : (∑ j, inner ℂ (C.starProjection (v j)) (C.starProjection (v i))) =
        inner ℂ (C.starProjection (v i)) (C.starProjection (v i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact horth j i hji
      · simp
    rw [he] at hz
    exact inner_self_eq_zero.mp hz
  calc
    ‖C.starProjection f‖ ^ 2 = ∑ i, ‖C.starProjection (v i)‖ ^ 2 := by
      rw [← hdec, map_sum]
      exact norm_sum_sq_orthogonal _ horth
    _ ≤ ∑ i, ε * ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : fixed i
      · rw [hzero i hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        exact mul_nonneg hε (sq_nonneg _)
      · exact hfree i hi
    _ = ε * ∑ i, ‖v i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ε * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left henergy hε

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathControlledOperators
section

namespace WeldedPath.ControlledOperators

open Classical HilbertSupport EncodedOracleUnitary
open scoped BigOperators

variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq X]

theorem controlled_apply (T : C → Hil X →L[ℂ] Hil Y)
    (ψ : Hil (C × X)) (c : C) (y : Y) :
    controlled T ψ (c, y) = T c (slice ψ c) y := by
  conv_rhs => rw [← sum_basis (slice ψ c)]
  simp [controlled, opTensor, ketBra_apply, inner_ket, ketTensor_apply,
    Fintype.sum_prod_type, ket_apply, slice, apply_ite, ite_apply]

theorem controlled_norm_le (T : C → Hil X →L[ℂ] Hil Y)
    (hT : ∀ c ψ, ‖T c ψ‖ ≤ ‖ψ‖) (ψ : Hil (C × X)) :
    ‖controlled T ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← sum_slice_norm_sq, ← sum_slice_norm_sq]
  apply Finset.sum_le_sum
  intro c _
  have hs : slice (controlled T ψ) c = T c (slice ψ c) := by
    ext y
    exact controlled_apply T ψ c y
  rw [hs]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT c _)

theorem controlled_opNorm_le (T : C → Hil X →L[ℂ] Hil Y)
    (hT : ∀ c ψ, ‖T c ψ‖ ≤ ‖ψ‖) : ‖controlled T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using controlled_norm_le T hT ψ

end WeldedPath.ControlledOperators

end

-- Solutions.CompressedPermutationRetained
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb HilbertSupport CoefficientStability
open scoped BigOperators ComplexConjugate

variable {s : ℕ}

noncomputable def eraseAt (I : InjDb s) (x : Fin s) : InjDb s :=
  (PEquiv.ofSet {u : Fin s | u ≠ x}).trans I

theorem eraseAt_apply (I : InjDb s) (x u : Fin s) :
    eraseAt I x u = if u = x then none else I u := by
  by_cases h : u = x <;> simp [eraseAt, PEquiv.trans, PEquiv.ofSet, h]

theorem eraseAt_self (I : InjDb s) (x : Fin s) : eraseAt I x x = none := by
  rw [eraseAt_apply, if_pos rfl]

theorem eraseAt_unused (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (eraseAt I x).symm y = none := by
  cases hh : (eraseAt I x).symm y with
  | none => rfl
  | some u =>
    have hu := ((eraseAt I x).inv u y).mp hh
    change eraseAt I x u = some y at hu
    rw [eraseAt_apply] at hu
    by_cases hux : u = x
    · rw [if_pos hux] at hu
      cases hu
    · rw [if_neg hux] at hu
      have he := (I.inv u y).mpr hu
      rw [(I.inv x y).mpr hxy] at he
      exact (hux (Option.some.inj he).symm).elim

theorem eraseAt_add (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (eraseAt I x).addPair x y = I := by
  apply PEquiv.ext
  intro u
  by_cases hu : u = x
  · subst u
    rw [addPair_apply_self _ _ _ (eraseAt_self I x) (eraseAt_unused I x y hxy), hxy]
  · rw [addPair_apply_other _ _ _ _ (eraseAt_self I x) (eraseAt_unused I x y hxy) hu,
      eraseAt_apply, if_neg hu]

theorem eraseAt_size (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (eraseAt I x).size + 1 = I.size := by
  rw [← CompletionLevels.size_addPair (eraseAt I x) x y (eraseAt_self I x)
    (eraseAt_unused I x y hxy), eraseAt_add I x y hxy]

theorem pC_known_error (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    (pC s x - 1) (ket I) =
      ((Real.sqrt ((s - (eraseAt I x).size : ℕ) : ℝ))⁻¹ : ℂ) •
        (ket (eraseAt I x) - plusState (eraseAt I x) x) := by
  have he := pC_ket_added (eraseAt I x) x y (eraseAt_self I x) (eraseAt_unused I x y hxy)
  rw [eraseAt_add I x y hxy] at he
  change pC s x (ket I) - ket I = _
  rw [he]
  abel

theorem pC_known_error_sq (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    ‖(pC s x - 1) (ket I)‖ ^ 2 = 2 / ((s - I.size + 1 : ℕ) : ℝ) := by
  have he := pC_added_error_sq (eraseAt I x) x y (eraseAt_self I x)
    (eraseAt_unused I x y hxy)
  rw [eraseAt_add I x y hxy] at he
  have hsize := eraseAt_size I x y hxy
  have hle := CompletionLevels.size_le I
  have harith : s - (eraseAt I x).size = s - I.size + 1 := by omega
  simpa only [harith] using he

theorem pC_known_error_orthogonal (I J : InjDb s) (x y : Fin s)
    (hI : I x = some y) (hJ : J x = some y) (hIJ : I ≠ J) :
    inner ℂ ((pC s x - 1) (ket I)) ((pC s x - 1) (ket J)) = 0 := by
  have hb : eraseAt I x ≠ eraseAt J x := by
    intro he
    have hh := congrArg (fun K : InjDb s => K.addPair x y) he
    rw [eraseAt_add I x y hI, eraseAt_add J x y hJ] at hh
    exact hIJ hh
  have hp : inner ℂ (plusState (eraseAt I x) x) (ket (eraseAt J x)) = 0 := by
    rw [← inner_conj_symm,
      ket_inner_plus_other _ _ x (eraseAt_self J x) (eraseAt_self I x)]
    simp
  rw [pC_known_error I x y hI, pC_known_error J x y hJ,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    inner_sub_right, ket_inner, if_neg hb,
    ket_inner_plus_other _ _ x (eraseAt_self I x) (eraseAt_self J x), hp,
    plus_inner_plus_other _ _ x (eraseAt_self I x) (eraseAt_self J x) hb]
  simp

/-- Keeping the answer y distinguishes the otherwise overlapping compression
errors, giving a bound uniform over coherent superpositions of databases. -/
theorem pC_retained_slice_bound (x y : Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (InjDb s))
    (hψ : ∀ I, ψ I ≠ 0 → I x = some y ∧ I.size ≤ r) :
    ‖(pC s x - 1) ψ‖ ^ 2 ≤
      (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ ^ 2 := by
  let T := pC s x - 1
  have ho : ∀ I J : InjDb s, I ≠ J →
      inner ℂ (ψ I • T (ket I)) (ψ J • T (ket J)) = 0 := by
    intro I J hIJ
    by_cases hi : ψ I = 0
    · simp [hi]
    by_cases hj : ψ J = 0
    · simp [hj]
    rw [inner_smul_left, inner_smul_right,
      pC_known_error_orthogonal I J x y (hψ I hi).1 (hψ J hj).1 hIJ]
    simp
  have he : T ψ = ∑ I, ψ I • T (ket I) := by
    conv_lhs => rw [← sum_basis ψ]
    simp only [map_sum, map_smul]
  change ‖T ψ‖ ^ 2 ≤ _
  rw [he, norm_sum_sq_orthogonal _ ho, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  by_cases hi : ψ I = 0
  · simp [hi]
  obtain ⟨hxy, hsize⟩ := hψ I hi
  rw [norm_smul, mul_pow, pC_known_error_sq I x y hxy]
  have hd : (s - r + 1 : ℕ) ≤ s - I.size + 1 := by omega
  have hb : (2 : ℝ) / ((s - I.size + 1 : ℕ) : ℝ) ≤
      2 / ((s - r + 1 : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast hd
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (sq_nonneg ‖ψ I‖)

theorem pC_retained_bound (x : Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (Fin s × InjDb s))
    (hψ : ∀ y I, ψ (y, I) ≠ 0 → I x = some y ∧ I.size ≤ r) :
    ‖opTensor (1 : Hil (Fin s) →L[ℂ] Hil (Fin s)) (pC s x - 1) ψ‖ ^ 2 ≤
      (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ ^ 2 := by
  have hs (y : Fin s) :
      EncodedOracleUnitary.slice (opTensor 1 (pC s x - 1) ψ) y =
        (pC s x - 1) (EncodedOracleUnitary.slice ψ y) := by
    ext I
    exact EncodedOracleUnitary.opTensor_one_apply _ ψ y I
  calc
    _ = ∑ y, ‖(pC s x - 1) (EncodedOracleUnitary.slice ψ y)‖ ^ 2 := by
      rw [← EncodedOracleUnitary.sum_slice_norm_sq]
      exact Finset.sum_congr rfl (fun y _ => congrArg (fun v => ‖v‖ ^ 2) (hs y))
    _ ≤ ∑ y, (2 / ((s - r + 1 : ℕ) : ℝ)) *
        ‖EncodedOracleUnitary.slice ψ y‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      exact pC_retained_slice_bound x y r hr _ (hψ y)
    _ = _ := by rw [← Finset.mul_sum, EncodedOracleUnitary.sum_slice_norm_sq]

theorem pC_retained_norm_bound (x : Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (Fin s × InjDb s))
    (hψ : ∀ y I, ψ (y, I) ≠ 0 → I x = some y ∧ I.size ≤ r) :
    ‖opTensor (1 : Hil (Fin s) →L[ℂ] Hil (Fin s)) (pC s x - 1) ψ‖ ≤
      Real.sqrt (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact pC_retained_bound x r hr ψ hψ

theorem pC_retained_control_bound {C : Type*} [Fintype C] [DecidableEq C]
    (x y : C → Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (C × InjDb s))
    (hψ : ∀ c I, ψ (c, I) ≠ 0 → I (x c) = some (y c) ∧ I.size ≤ r) :
    ‖controlled (fun c => pC s (x c) - 1) ψ‖ ^ 2 ≤
      (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ ^ 2 := by
  have hs (c : C) :
      EncodedOracleUnitary.slice (controlled (fun c => pC s (x c) - 1) ψ) c =
        (pC s (x c) - 1) (EncodedOracleUnitary.slice ψ c) := by
    ext I
    exact ControlledOperators.controlled_apply _ ψ c I
  calc
    _ = ∑ c, ‖(pC s (x c) - 1) (EncodedOracleUnitary.slice ψ c)‖ ^ 2 := by
      rw [← EncodedOracleUnitary.sum_slice_norm_sq]
      exact Finset.sum_congr rfl (fun c _ => congrArg (fun v => ‖v‖ ^ 2) (hs c))
    _ ≤ ∑ c, (2 / ((s - r + 1 : ℕ) : ℝ)) *
        ‖EncodedOracleUnitary.slice ψ c‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      exact pC_retained_slice_bound (x c) (y c) r hr _ (hψ c)
    _ = _ := by rw [← Finset.mul_sum, EncodedOracleUnitary.sum_slice_norm_sq]

theorem pC_retained_control_norm_bound {C : Type*} [Fintype C] [DecidableEq C]
    (x y : C → Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (C × InjDb s))
    (hψ : ∀ c I, ψ (c, I) ≠ 0 → I (x c) = some (y c) ∧ I.size ≤ r) :
    ‖controlled (fun c => pC s (x c) - 1) ψ‖ ≤
      Real.sqrt (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact pC_retained_control_bound x y r hr ψ hψ

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathCompletionRange
section

namespace WeldedPath.CompletionLevels

open Classical InjDb HilbertSupport IntertwinerPartial CompressedPrimitive
open scoped BigOperators

variable {s : ℕ}

theorem Gam_range_eq (s r : ℕ) : (Gam s r).range = Hlevel s r := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    exact Gam_range s r u
  · intro v hv
    have hp (w : Hil (Equiv.Perm (Fin s))) (hw : w ∈ Hle s r) :
        projLevel s r w ∈ (Gam s r).range := by
      change w ∈ Submodule.span ℂ {v | ∃ I : InjDb s, I.size = r ∧ v = completion I} at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨I, hI, rfl⟩ := hw
        refine ⟨ket I, ?_⟩
        change Gam s r (ket I) = projLevel s r (completion I)
        rw [Gam_ket, if_pos hI]
      | zero => simp
      | add u w hu hw ihu ihw =>
        rw [map_add]
        exact (Gam s r).range.add_mem ihu ihw
      | smul c w hw ihw =>
        rw [map_smul]
        exact (Gam s r).range.smul_mem c ihw
    have he : projLevel s r v = v := (Hlevel s r).starProjection_eq_self_iff.mpr hv
    simpa only [he] using hp v (Hlevel_le r hv)

theorem Gram_range_eq (s r : ℕ) : (Gram s r).range = Hlevel s r := by
  have he := (Gam s r).toLinearMap.range_self_comp_adjoint
  rw [ContinuousLinearMap.adjoint_toLinearMap] at he
  change (Gram s r).range = (Gam s r).range at he
  exact he.trans (Gam_range_eq s r)

theorem permutation_eq_of_except (φ ψ : Equiv.Perm (Fin s)) (x : Fin s)
    (h : ∀ u, u ≠ x → ψ u = φ u) : ψ = φ := by
  apply Equiv.ext
  intro u
  by_cases hu : u = x
  · subst u
    by_cases hv : φ.symm (ψ x) = x
    · have he := congrArg φ hv
      simpa only [Equiv.apply_symm_apply] using he
    · have he := h (φ.symm (ψ x)) hv
      rw [Equiv.apply_symm_apply] at he
      exact (hv (ψ.injective he)).elim
  · exact h u hu

theorem erased_permutation_extends_iff (φ ψ : Equiv.Perm (Fin s)) (x : Fin s) :
    Extends ψ (eraseAt φ.toPEquiv x) ↔ ψ = φ := by
  constructor
  · intro h
    apply permutation_eq_of_except φ ψ x
    intro u hu
    apply h u (φ u)
    rw [eraseAt_apply, if_neg hu]
    rfl
  · rintro rfl u y h
    rw [eraseAt_apply] at h
    by_cases hu : u = x
    · rw [if_pos hu] at h
      cases h
    · rw [if_neg hu] at h
      exact Option.some.inj h

theorem erased_permutation_rawCompletion (φ : Equiv.Perm (Fin s)) (x : Fin s) :
    rawCompletion (eraseAt φ.toPEquiv x) = ket φ := by
  ext ψ
  simp only [rawCompletion_apply, erased_permutation_extends_iff, ket_apply]

theorem Hle_pred_eq_top (hs : 0 < s) : Hle s (s - 1) = ⊤ := by
  apply eq_top_iff.mpr
  intro v _
  rw [← sum_basis v]
  apply Submodule.sum_mem
  intro φ _
  apply Submodule.smul_mem
  let x : Fin s := ⟨0, hs⟩
  rw [← erased_permutation_rawCompletion φ x]
  apply (completion_mem_iff _ _).mp
  apply Submodule.subset_span
  refine ⟨eraseAt φ.toPEquiv x, ?_, rfl⟩
  have he := eraseAt_size φ.toPEquiv x (φ x) rfl
  have hsize : InjDb.size φ.toPEquiv = s := by simp [InjDb.size]
  omega

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathPolarSupport
section

namespace WeldedPath.OperatorPolar

open Classical

set_option maxHeartbeats 1000000

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def endAlgEquiv :
    (Hil X →L[ℂ] Hil X) ≃ₐ[ℂ] Module.End ℂ (Hil X) :=
  (AlgEquiv.ofLinearEquiv
    (LinearMap.toContinuousLinearMap : Module.End ℂ (Hil X) ≃ₗ[ℂ] (Hil X →L[ℂ] Hil X))
    rfl (fun _ _ => rfl)).symm

theorem finite_complex_spectrum (A : Hil X →L[ℂ] Hil X) : (spectrum ℂ A).Finite := by
  rw [← AlgEquiv.spectrum_eq endAlgEquiv A]
  exact Module.End.finite_spectrum _

theorem finite_real_spectrum (A : Hil X →L[ℂ] Hil X) : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (finite_complex_spectrum A).preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

theorem gram_invSqrt_sandwich (A : Hil X →L[ℂ] Hil X) (hA : A.IsPositive) :
    A * invSqrt A * invSqrt A * A = A := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  have hf : ContinuousOn f (spectrum ℝ A) := (finite_real_spectrum A).continuousOn f
  have hnonneg : 0 ≤ A := by simpa only [ContinuousLinearMap.le_def, sub_zero] using hA
  have hi : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA.isSelfAdjoint
  have he₁ := cfc_mul (fun x : ℝ => x) f A continuousOn_id hf
  have he₂ := cfc_mul (fun x => x * f x) f A (continuousOn_id.mul hf) hf
  have he₃ := cfc_mul (fun x => x * f x * f x) (fun x : ℝ => x) A
    ((continuousOn_id.mul hf).mul hf) continuousOn_id
  calc
    _ = cfc (fun x => x * f x * f x * x) A := by
      rw [he₃, he₂, he₁, hi]
      rfl
    _ = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hnonneg hx
      by_cases hz : x = 0
      · simp [hz, f]
      · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hx₀ (Ne.symm hz)))
        dsimp [f]
        field_simp [hs]
        nlinarith [Real.sq_sqrt hx₀]
    _ = A := hi

theorem rectangular_gram_identity (T : Hil X →L[ℂ] Hil Y) (B : Hil Y →L[ℂ] Hil Y)
    (hB : ContinuousLinearMap.adjoint B = B)
    (hc : B.comp (T.comp (ContinuousLinearMap.adjoint T)) =
      (T.comp (ContinuousLinearMap.adjoint T)).comp B)
    (hs : ((((T.comp (ContinuousLinearMap.adjoint T)).comp B).comp B).comp
      (T.comp (ContinuousLinearMap.adjoint T))) = T.comp (ContinuousLinearMap.adjoint T)) :
    ((ContinuousLinearMap.adjoint ((ContinuousLinearMap.adjoint T).comp B)).comp
      ((ContinuousLinearMap.adjoint T).comp B)).comp
      (T.comp (ContinuousLinearMap.adjoint T)) = T.comp (ContinuousLinearMap.adjoint T) := by
  rw [ContinuousLinearMap.adjoint_comp, hB, ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun Q : Hil Y →L[ℂ] Hil Y => Q v) hs
  have hcv := congrArg (fun Q : Hil Y →L[ℂ] Hil Y =>
    Q (B (T (ContinuousLinearMap.adjoint T v)))) hc
  exact hcv.trans hv

theorem polar_gram_fixed (T : Hil X →L[ℂ] Hil Y) :
    ((ContinuousLinearMap.adjoint (polarMap T)).comp (polarMap T)).comp
      (T.comp (ContinuousLinearMap.adjoint T)) = T.comp (ContinuousLinearMap.adjoint T) :=
  rectangular_gram_identity T _ (invSqrt_adjoint _)
    (invSqrt_commute _ (gram_selfadjoint T)).eq
    (gram_invSqrt_sandwich _ T.isPositive_self_comp_adjoint)

end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathPolarProjection
section

namespace WeldedPath.OperatorPolar

open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem polar_initial_projection (T : Hil X →L[ℂ] Hil Y) :
    (ContinuousLinearMap.adjoint (polarMap T)).comp (polarMap T) = T.range.starProjection := by
  let A := T.comp (ContinuousLinearMap.adjoint T)
  let P := (ContinuousLinearMap.adjoint (polarMap T)).comp (polarMap T)
  have hR : A.range = T.range := by
    have he := T.toLinearMap.range_self_comp_adjoint
    rw [ContinuousLinearMap.adjoint_toLinearMap] at he
    exact he
  have hpadj : ContinuousLinearMap.adjoint P = P := by
    simp only [P, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hfix (v : Hil Y) (hv : v ∈ T.range) : P v = v := by
    rw [← hR] at hv
    obtain ⟨u, rfl⟩ := hv
    exact congrArg (fun Q : Hil Y →L[ℂ] Hil Y => Q u) (polar_gram_fixed T)
  have hmem (v : Hil Y) : P v ∈ T.range := by
    simp only [P, polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]
    apply invSqrt_mapsTo A (gram_selfadjoint T) T.range
    intro w
    exact ⟨ContinuousLinearMap.adjoint T w, rfl⟩
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply T.range.eq_starProjection_of_mem_of_inner_eq_zero (hmem v)
  intro w hw
  rw [inner_sub_left]
  have he := ContinuousLinearMap.adjoint_inner_left P w v
  rw [hpadj, hfix w hw] at he
  exact sub_eq_zero.mpr he.symm

end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathIntertwinerIsometry
section

namespace WeldedPath.IntertwinerIsometry

open Classical OperatorPolar CompletionLevels IntertwinerPartial HilbertSupport
open scoped BigOperators

theorem sum_initial {X Y ι : Type*} [Fintype X] [Fintype Y]
    (S : Finset ι) (V : ι → Hil X →L[ℂ] Hil Y) (P : ι → Hil X →L[ℂ] Hil X)
    (hdiag : ∀ i ∈ S, (ContinuousLinearMap.adjoint (V i)).comp (V i) = P i)
    (hcross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (ContinuousLinearMap.adjoint (V i)).comp (V j) = 0) :
    (ContinuousLinearMap.adjoint (∑ i ∈ S, V i)).comp (∑ i ∈ S, V i) =
      ∑ i ∈ S, P i := by
  simp only [map_sum, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact hdiag i hi
  · intro j hj hji
    exact hcross j hj i hi hji
  · exact fun hn => (hn hi).elim

theorem intertwiner_initial_sum (s : ℕ) :
    (ContinuousLinearMap.adjoint (intertwiner s)).comp (intertwiner s) =
      ∑ r ∈ Finset.range s, projLevel s r := by
  change (ContinuousLinearMap.adjoint (∑ r ∈ Finset.range s, polarMap (Gam s r))).comp
    (∑ r ∈ Finset.range s, polarMap (Gam s r)) = _
  apply sum_initial
  · intro r hr
    rw [polar_initial_projection]
    exact congrArg (fun K : Submodule ℂ (Hil (Equiv.Perm (Fin s))) => K.starProjection)
      (Gam_range_eq s r)
  · intro r hr t ht hrt
    exact polar_Gam_cross_initial s r t hrt

theorem projLevel_other (s r t : ℕ) (hrt : r ≠ t)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hlevel s r) : projLevel s t v = 0 := by
  apply (Hlevel s t).eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  simpa only [sub_zero] using Hlevel_pairwise_orthogonal r t hrt v w hv hw

theorem level_sum_fixes (s r : ℕ) (hr : r < s)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hlevel s r) :
    (∑ t ∈ Finset.range s, projLevel s t) v = v := by
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_eq_single r]
  · exact (Hlevel s r).starProjection_eq_self_iff.mpr hv
  · intro t ht htr
    exact projLevel_other s r t (Ne.symm htr) v hv
  · intro hn
    exact (hn (Finset.mem_range.mpr hr)).elim

theorem level_sum_fixes_Hle (s r : ℕ) (hr : r < s)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hle s r) :
    (∑ t ∈ Finset.range s, projLevel s t) v = v := by
  induction r generalizing v with
  | zero => exact level_sum_fixes s 0 hr v hv
  | succ r ih =>
    let Q := (Hle s r).starProjection
    have hQ : Q v ∈ Hle s r := (Hle s r).starProjection_apply_mem v
    have hrest : v - Q v ∈ Hlevel s (r + 1) :=
      ⟨(Hle s (r + 1)).sub_mem hv ((Hle_succ r (by omega)) hQ),
        (Hle s r).sub_starProjection_mem_orthogonal v⟩
    calc
      _ = (∑ t ∈ Finset.range s, projLevel s t) (Q v + (v - Q v)) := by
        congr 1
        abel
      _ = (∑ t ∈ Finset.range s, projLevel s t) (Q v) +
          (∑ t ∈ Finset.range s, projLevel s t) (v - Q v) := map_add _ _ _
      _ = Q v + (v - Q v) := by
        rw [ih (by omega) (Q v) hQ, level_sum_fixes s (r + 1) hr _ hrest]
      _ = v := by abel

theorem intertwiner_adjoint_comp (s : ℕ) (hs : 0 < s) :
    (ContinuousLinearMap.adjoint (intertwiner s)).comp (intertwiner s) = 1 := by
  rw [intertwiner_initial_sum]
  apply ContinuousLinearMap.ext
  intro v
  apply level_sum_fixes_Hle s (s - 1) (by omega) v
  rw [Hle_pred_eq_top hs]
  trivial

theorem intertwiner_norm (s : ℕ) (hs : 0 < s) (v : Hil (Equiv.Perm (Fin s))) :
    ‖intertwiner s v‖ = ‖v‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (intertwiner s)).mpr
    (intertwiner_adjoint_comp s hs) v

end WeldedPath.IntertwinerIsometry

end

-- Solutions.WeldedPathIntertwinerLevels
section

namespace WeldedPath.IntertwinerIsometry

open Classical OperatorPolar CompletionLevels IntertwinerPartial HilbertSupport
open scoped BigOperators

theorem GramInvSqrt_other (s r t : ℕ) (hrt : r ≠ t)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hlevel s r) :
    GramInvSqrt s t v = 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [inner_zero_right]
  have he := ContinuousLinearMap.adjoint_inner_right (GramInvSqrt s t) w v
  rw [GramInvSqrt_adjoint] at he
  rw [he]
  exact Hlevel_pairwise_orthogonal t r (Ne.symm hrt) _ _
    (GramInvSqrt_range s t w) hv

theorem intertwiner_level_support (s r : ℕ)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hlevel s r)
    (I : InjDb s) (hI : I.size ≠ r) : intertwiner s v I = 0 := by
  simp only [intertwiner, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases htr : t = r
  · subst t
    exact Gam_adjoint_support s r _ I hI
  · rw [GramInvSqrt_other s r t (Ne.symm htr) v hv, map_zero]
    rfl

theorem intertwiner_Hle_support (s r : ℕ) (hr : r < s)
    (v : Hil (Equiv.Perm (Fin s))) (hv : v ∈ Hle s r)
    (I : InjDb s) (hI : r < I.size) : intertwiner s v I = 0 := by
  induction r generalizing v with
  | zero => exact intertwiner_level_support s 0 v hv I (by omega)
  | succ r ih =>
    let Q := (Hle s r).starProjection
    have hQ : Q v ∈ Hle s r := (Hle s r).starProjection_apply_mem v
    have hrest : v - Q v ∈ Hlevel s (r + 1) :=
      ⟨(Hle s (r + 1)).sub_mem hv ((Hle_succ r (by omega)) hQ),
        (Hle s r).sub_starProjection_mem_orthogonal v⟩
    have he : v = Q v + (v - Q v) := by abel
    rw [he, map_add]
    change intertwiner s (Q v) I + intertwiner s (v - Q v) I = 0
    rw [ih (by omega) (Q v) hQ (by omega),
      intertwiner_level_support s (r + 1) _ hrest I (by omega), add_zero]

end WeldedPath.IntertwinerIsometry

end

-- Solutions.WeldedPathCompletionZeroSum
section

namespace WeldedPath.CompletionLevels

open Classical InjDb IntertwinerPartial HilbertSupport
open scoped BigOperators

variable {s : ℕ}

theorem projLevel_completion_lower (r : ℕ) (I : InjDb s) (hI : I.size = r) :
    projLevel s (r + 1) (completion I) = 0 := by
  have hmem : completion I ∈ Hle s r := Submodule.subset_span ⟨I, hI, rfl⟩
  apply (Hlevel s (r + 1)).eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  rw [sub_zero]
  exact ((Hle s r).mem_orthogonal w).mp hw.2 (completion I) hmem

theorem Gam_adjoint_zero_sum (r : ℕ) (I : InjDb s) (hI : I.size = r)
    (x : Fin s) (hx : I x = none) (ψ : Hil (Equiv.Perm (Fin s))) :
    ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      ContinuousLinearMap.adjoint (Gam s (r + 1)) ψ (I.addPair x y) = 0 := by
  have hproj : ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      projLevel s (r + 1) (completion (I.addPair x y)) = 0 := by
    rw [← map_sum, completion_extension I x hx, map_smul,
      projLevel_completion_lower r I hI, smul_zero]
  calc
    _ = ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
        inner ℂ (projLevel s (r + 1) (completion (I.addPair x y))) ψ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← inner_ket (I.addPair x y), ContinuousLinearMap.adjoint_inner_right,
        Gam_ket, if_pos]
      rw [size_addPair I x y hx (Finset.mem_filter.mp hy).2, hI]
    _ = inner ℂ (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
        projLevel s (r + 1) (completion (I.addPair x y))) ψ := (sum_inner _ _ _).symm
    _ = 0 := by rw [hproj, inner_zero_left]

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathRegisterTransport
section

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open scoped BigOperators

variable {Ω C X : Type*} [Fintype Ω] [Fintype C] [Fintype X]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X]

theorem ofBasis_ket {Y : Type*} [Fintype Y] (f : Ω → Hil Y) (p : Ω) :
    ofBasis f (ket p) = f p := by
  simp [ofBasis, ketBra_apply, inner_ket, ket_apply]

theorem basisMap_ket {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : Ω → Y) (p : Ω) : basisMap f (ket p) = ket (f p) := by
  simp [basisMap, ketBra_apply, inner_ket, ket_apply]

theorem partImg_one (x : X) (f : X → Ω) :
    partImg (1 : Hil X →L[ℂ] Hil X) x f = ket (f x) := by
  simp [partImg, inner_ket, ket_apply]

theorem partImg_basisMap (x : X) (f : X → X) (put : X → Ω) :
    partImg (basisMap f) x put = ket (put (f x)) := by
  simp [partImg, basisMap_ket, inner_ket, ket_apply]

theorem controlled_ket (T : C → Hil X →L[ℂ] Hil X) (c : C) (x : X) :
    controlled T (ket (c, x)) = ketTensor (ket c) (T c (ket x)) := by
  have hs (a : C) : slice (ket (c, x)) a = if a = c then ket x else 0 := by
    ext y
    by_cases ha : a = c <;> simp [slice, ket_apply, ha, Prod.mk.injEq]
  ext ⟨a, y⟩
  rw [controlled_apply, hs]
  by_cases ha : a = c
  · subst a
    simp [ketTensor_apply, ket_apply]
  · simp [ha, ketTensor_apply, ket_apply]

theorem partImg_reindex (e : Ω ≃ C × X) (T : Hil X →L[ℂ] Hil X)
    (c : C) (x : X) :
    basisMap e (partImg T x (fun y => e.symm (c, y))) =
      ketTensor (ket c) (T (ket x)) := by
  simp only [partImg, map_sum, map_smul, basisMap_ket, Equiv.apply_symm_apply, inner_ket]
  ext ⟨a, y⟩
  by_cases ha : a = c <;> simp [ketTensor_apply, ket_apply, Prod.mk.injEq, ha]

/-- Relabeling the coordinates of a controlled contraction preserves its
norm bound. The conclusion is expressed in the canonical `ofBasis` and
`partImg` syntax used by the welded-tree oracle registers. -/
theorem ofBasis_partImg_norm_le (e : Ω ≃ C × X)
    (T : C → Hil X →L[ℂ] Hil X) (hT : ∀ c x, ‖T c x‖ ≤ ‖x‖)
    (ψ : Hil Ω) :
    ‖ofBasis (fun p => partImg (T (e p).1) (e p).2
      (fun x => e.symm ((e p).1, x))) ψ‖ ≤ ‖ψ‖ := by
  let U := ofBasis (fun p => partImg (T (e p).1) (e p).2
    (fun x => e.symm ((e p).1, x)))
  have heq : basisMap e (U ψ) = controlled T (basisMap e ψ) := by
    rw [← sum_basis ψ]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    change basisMap e (ofBasis _ (ket p)) = controlled T (basisMap e (ket p))
    rw [ofBasis_ket, basisMap_ket, partImg_reindex]
    exact (controlled_ket T (e p).1 (e p).2).symm
  change ‖U ψ‖ ≤ ‖ψ‖
  rw [← basisMap_equiv_norm e (U ψ), heq, ← basisMap_equiv_norm e ψ]
  exact controlled_norm_le T hT _

end WeldedPath.RegisterTransport

end

-- Solutions.CompressedPermutationInverse
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb Supplement HilbertSupport RegisterTransport EncodedOracleUnitary
open scoped BigOperators

theorem addPair_symm {s : ℕ} (I : InjDb s) (x y : Fin s) :
    (I.addPair x y).symm = InjDb.addPair I.symm y x := by
  unfold InjDb.addPair
  by_cases h : I x = none ∧ I.symm y = none
  · have h' : I.symm y = none ∧ I.symm.symm x = none := ⟨h.2, h.1⟩
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : ¬(I.symm y = none ∧ I.symm.symm x = none) := fun hh => h ⟨hh.2, hh.1⟩
    rw [dif_neg h, dif_neg h']

theorem flipDb_ket {s : ℕ} (I : InjDb s) : flipDb s (ket I) = ket I.symm :=
  basisMap_ket _ _

theorem flipDb_flip {s : ℕ} (ψ : Hil (InjDb s)) : flipDb s (flipDb s ψ) = ψ := by
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul, flipDb_ket, PEquiv.symm_symm]

theorem flipDb_inner {s : ℕ} (u v : Hil (InjDb s)) :
    inner ℂ (flipDb s u) (flipDb s v) = inner ℂ u v :=
  ((flipDb s).inner_map_map_iff_adjoint_comp_self.mpr
    ((flipDb s).norm_map_iff_adjoint_comp_self.mp (flipDb_norm s))) u v

theorem flipDb_plus {s : ℕ} (I : InjDb s) (x : Fin s) :
    flipDb s (plusState I x) = plusInv I.symm x := by
  simp only [plusState, plusInv, map_smul, map_sum, flipDb_ket,
    size_symm, addPair_symm]

theorem flipDb_pCF {s : ℕ} (u v ψ : Hil (InjDb s)) :
    flipDb s (pCF u v ψ) = pCF (flipDb s u) (flipDb s v) (flipDb s ψ) := by
  simp only [pCF_apply, map_add, map_sub, map_smul, flipDb_inner]

theorem flipDb_pC {s : ℕ} (x : Fin s) (ψ : Hil (InjDb s)) :
    flipDb s (pC s x ψ) = pCinv s x (flipDb s ψ) := by
  simp only [pC, pCinv, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    map_add, map_sum, map_sub, flipDb_pCF, flipDb_plus, flipDb_ket]
  congr 1
  apply Finset.sum_bij (fun I _ => I.symm)
  · intro I hI
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, PEquiv.symm_symm] using hI
  · intro I hI J hJ he
    exact congrArg PEquiv.symm he
  · intro J hJ
    refine ⟨J.symm, ?_, PEquiv.symm_symm J⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hJ
  · intro I hI
    rfl

theorem pCinv_eq_flip (s : ℕ) (x : Fin s) :
    pCinv s x = (flipDb s).comp ((pC s x).comp (flipDb s)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  change pCinv s x ψ = flipDb s (pC s x (flipDb s ψ))
  rw [flipDb_pC, flipDb_flip]

theorem pCinv_ket_unset {s : ℕ} (I : InjDb s) (x : Fin s)
    (hx : I.symm x = none) : pCinv s x (ket I) = plusInv I x := by
  rw [pCinv_eq_flip]
  simp only [ContinuousLinearMap.comp_apply, flipDb_ket,
    pC_ket_unset I.symm x hx, flipDb_plus, PEquiv.symm_symm]

theorem pCinv_norm_map (s : ℕ) (x : Fin s) (ψ : Hil (InjDb s)) :
    ‖pCinv s x ψ‖ = ‖ψ‖ := by
  rw [pCinv_eq_flip]
  simp only [ContinuousLinearMap.comp_apply, flipDb_norm, pC_norm_map]

theorem pCinv_ket_added {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I.symm x = none) (hy : I y = none) :
    pCinv s x (ket (I.addPair y x)) = ket (I.addPair y x) +
      ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) • (ket I - plusInv I x) := by
  rw [pCinv_eq_flip]
  simp only [ContinuousLinearMap.comp_apply, flipDb_ket, addPair_symm]
  rw [pC_ket_added I.symm x y hx hy]
  simp only [map_add, map_smul, map_sub, flipDb_ket, flipDb_plus,
    size_symm, addPair_symm, PEquiv.symm_symm]

theorem flipDb_apply {s : ℕ} (ψ : Hil (InjDb s)) (I : InjDb s) :
    flipDb s ψ I = ψ I.symm := by
  have hf : Function.Involutive (fun I : InjDb s => I.symm) := PEquiv.symm_symm
  let e : InjDb s ≃ InjDb s := hf.toPerm (fun I : InjDb s => I.symm)
  exact basisMap_apply_equiv e ψ I.symm

theorem pCinv_error_flip {s : ℕ} (x : Fin s) (ψ : Hil (InjDb s)) :
    (pCinv s x - 1) ψ = flipDb s ((pC s x - 1) (flipDb s ψ)) := by
  change pCinv s x ψ - ψ = flipDb s (pC s x (flipDb s ψ) - flipDb s ψ)
  rw [map_sub, flipDb_pC, flipDb_flip]

theorem pCinv_known_error_sq {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hxy : I.symm x = some y) :
    ‖(pCinv s x - 1) (ket I)‖ ^ 2 = 2 / ((s - I.size + 1 : ℕ) : ℝ) := by
  rw [pCinv_error_flip, flipDb_norm, flipDb_ket, pC_known_error_sq I.symm x y hxy,
    size_symm]

theorem pCinv_retained_slice_bound {s : ℕ} (x y : Fin s) (r : ℕ) (hr : r ≤ s)
    (ψ : Hil (InjDb s))
    (hψ : ∀ I, ψ I ≠ 0 → I.symm x = some y ∧ I.size ≤ r) :
    ‖(pCinv s x - 1) ψ‖ ^ 2 ≤
      (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖ ^ 2 := by
  rw [pCinv_error_flip, flipDb_norm]
  have hsupport : ∀ I, flipDb s ψ I ≠ 0 → I x = some y ∧ I.size ≤ r := by
    intro I hI
    rw [flipDb_apply] at hI
    simpa only [PEquiv.symm_symm, size_symm] using hψ I.symm hI
  simpa only [flipDb_norm] using pC_retained_slice_bound x y r hr (flipDb s ψ) hsupport

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathCompressionSelfAdjoint
section

namespace WeldedPath.CompletionLevels

open Classical InjDb IntertwinerPartial HilbertSupport
open scoped BigOperators

variable {s : ℕ}

theorem unused_preimage_of_extends (I : InjDb s) (y : Fin s) (hy : I.symm y = none)
    (φ : Equiv.Perm (Fin s)) (hφ : Extends φ I) : I (φ.symm y) = none := by
  cases hx : I (φ.symm y) with
  | none => rfl
  | some z =>
    have hz : y = z := by simpa only [Equiv.apply_symm_apply] using hφ _ z hx
    subst z
    have hi := (I.inv (φ.symm y) y).mpr hx
    change I.symm y = some (φ.symm y) at hi
    rw [hy] at hi
    cases hi

theorem rawCompletion_inverse_extension (I : InjDb s) (y : Fin s) (hy : I.symm y = none) :
    rawCompletion I = ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      rawCompletion (I.addPair x y) := by
  ext φ
  simp only [WithLp.ofLp_sum, Finset.sum_apply, rawCompletion_apply]
  by_cases hφ : Extends φ I
  · rw [if_pos hφ]
    symm
    rw [Finset.sum_eq_single (φ.symm y)]
    · rw [if_pos ((extends_addPair_iff I (φ.symm y) y
        (unused_preimage_of_extends I y hy φ hφ) hy φ).mpr
        ⟨hφ,φ.apply_symm_apply y⟩)]
    · intro x hx hne
      apply if_neg
      intro he
      have heq := ((extends_addPair_iff I x y (Finset.mem_filter.mp hx).2 hy φ).mp he).2
      exact hne ((Equiv.eq_symm_apply φ).mpr heq)
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        unused_preimage_of_extends I y hy φ hφ⟩)).elim
  · rw [if_neg hφ]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    apply if_neg
    intro he
    exact hφ (((extends_addPair_iff I x y (Finset.mem_filter.mp hx).2 hy φ).mp he).1)

theorem completion_inverse_extension (I : InjDb s) (y : Fin s) (hy : I.symm y = none) :
    ∑ x ∈ Finset.univ.filter (fun x => I x = none), completion (I.addPair x y) =
      (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) • completion I := by
  let m := s - I.size - 1
  have hm : s - I.size = m + 1 := by
    have hi := size_lt_of_unset I.symm y hy
    rw [CompressedPrimitive.size_symm] at hi
    dsimp [m]
    omega
  have hsum : ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      completion (I.addPair x y) =
      ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) •
        ∑ x ∈ Finset.univ.filter (fun x => I x = none), rawCompletion (I.addPair x y) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    change ((Real.sqrt ((s - (I.addPair x y).size).factorial : ℝ))⁻¹ : ℂ) • _ = _
    rw [size_addPair I x y (Finset.mem_filter.mp hx).2 hy]
    have he : s - (I.size + 1) = m := by dsimp [m]; omega
    rw [he]
    rfl
  rw [hsum, ← rawCompletion_inverse_extension I y hy]
  change ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) • rawCompletion I =
    (Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ) •
      (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℂ) • rawCompletion I)
  rw [smul_smul, hm]
  congr 1
  exact_mod_cast inv_sqrt_factorial_succ m

theorem Gam_adjoint_inverse_zero_sum (r : ℕ) (I : InjDb s) (hI : I.size = r)
    (y : Fin s) (hy : I.symm y = none) (ψ : Hil (Equiv.Perm (Fin s))) :
    ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      ContinuousLinearMap.adjoint (Gam s (r + 1)) ψ (I.addPair x y) = 0 := by
  have hproj : ∑ x ∈ Finset.univ.filter (fun x => I x = none),
      projLevel s (r + 1) (completion (I.addPair x y)) = 0 := by
    rw [← map_sum, completion_inverse_extension I y hy, map_smul,
      projLevel_completion_lower r I hI, smul_zero]
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x => I x = none),
        inner ℂ (projLevel s (r + 1) (completion (I.addPair x y))) ψ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← inner_ket (I.addPair x y), ContinuousLinearMap.adjoint_inner_right,
        Gam_ket, if_pos]
      rw [size_addPair I x y (Finset.mem_filter.mp hx).2 hy, hI]
    _ = inner ℂ (∑ x ∈ Finset.univ.filter (fun x => I x = none),
        projLevel s (r + 1) (completion (I.addPair x y))) ψ := (sum_inner _ _ _).symm
    _ = 0 := by rw [hproj, inner_zero_left]

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathIncidenceOperators
section

namespace WeldedPath.Incidence

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels
open scoped BigOperators

variable {s : ℕ}

def recordLevel (s j : ℕ) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  diagProj (fun I : InjDb s => I.size = j)

def domainMap (s j : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  (ContinuousLinearMap.adjoint (insertionBlock s x)).comp (recordLevel s j)

def imageMap (s j : ℕ) (y : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  (flipDb s).comp ((domainMap s j y).comp (flipDb s))

def laplacian (s j : ℕ) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  ∑ x : Fin s, ((ContinuousLinearMap.adjoint (domainMap s j x)).comp (domainMap s j x) +
    (ContinuousLinearMap.adjoint (imageMap s j x)).comp (imageMap s j x))

lemma insertionBlock_adjoint_apply (x : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    ContinuousLinearMap.adjoint (insertionBlock s x) a I =
      if I x = none then inner ℂ (plusState I x) a else 0 := by
  rw [insertionBlock_adjoint]
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, ket_apply]
  simp

lemma inner_plusState (x : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    inner ℂ (plusState I x) a = ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) *
      ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), a (I.addPair x y) := by
  simp [plusState, inner_smul_left, sum_inner, inner_ket, mul_comm]

theorem insertionBlock_adjoint_ket_known (I : InjDb s) (x y : Fin s)
    (hxy : I x = some y) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (ket I) =
      ((Real.sqrt ((s-(eraseAt I x).size : ℕ) : ℝ))⁻¹ : ℂ) • ket (eraseAt I x) := by
  have he := insertionBlock_adjoint_ket_added x y (eraseAt I x)
    (eraseAt_self I x) (eraseAt_unused I x y hxy)
  rwa [eraseAt_add I x y hxy] at he

theorem insertionBlock_adjoint_ket_unset (I : InjDb s) (x : Fin s)
    (hx : I x = none) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (ket I) = 0 := by
  ext J
  rw [insertionBlock_adjoint_apply]
  by_cases hJ : J x = none
  · rw [if_pos hJ,← inner_conj_symm,ket_inner_plus_other I J x hx hJ]
    simp
  · rw [if_neg hJ]
    rfl

theorem plusBlock_ket_known (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    plusBlock s x (ket I) =
      ((Real.sqrt ((s-(eraseAt I x).size : ℕ) : ℝ))⁻¹ : ℂ) • plusState (eraseAt I x) x := by
  rw [← insertionBlock_comp_adjoint]
  change insertionBlock s x (ContinuousLinearMap.adjoint (insertionBlock s x) (ket I)) = _
  rw [insertionBlock_adjoint_ket_known I x y hxy,map_smul,insertionBlock_ket,
    if_pos (eraseAt_self I x)]

theorem plusBlock_ket_unset (I : InjDb s) (x : Fin s) (hx : I x=none) :
    plusBlock s x (ket I) = 0 := by
  rw [← insertionBlock_comp_adjoint]
  change insertionBlock s x (ContinuousLinearMap.adjoint (insertionBlock s x) (ket I)) = 0
  rw [insertionBlock_adjoint_ket_unset I x hx,map_zero]

lemma square_normalization (m : ℕ) :
    (((Real.sqrt (m : ℝ))⁻¹ : ℂ) * ((Real.sqrt (m : ℝ))⁻¹ : ℂ)) = (1/(m : ℂ)) := by
  have h : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = 1/(m : ℝ) := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg m),one_div]
  simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_one] using congrArg Complex.ofReal h

theorem plusBlock_ket_average (I : InjDb s) (x y : Fin s) (hxy : I x = some y) :
    plusBlock s x (ket I) = (1/((s-I.size+1 : ℕ) : ℂ)) •
      ∑ z ∈ Finset.univ.filter (fun z => (eraseAt I x).symm z = none),
        ket ((eraseAt I x).addPair x z) := by
  rw [plusBlock_ket_known I x y hxy,plusState,smul_smul,square_normalization]
  have hs := eraseAt_size I x y hxy
  have hi := size_le I
  have he : s-(eraseAt I x).size=s-I.size+1 := by omega
  rw [he]

theorem domainMap_apply (j : ℕ) (x : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    domainMap s j x a I = if I.size+1=j ∧ I x=none then
      ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) *
        ∑ y ∈ Finset.univ.filter (fun y => I.symm y=none), a (I.addPair x y)
      else 0 := by
  change ContinuousLinearMap.adjoint (insertionBlock s x) (recordLevel s j a) I = _
  rw [insertionBlock_adjoint_apply]
  by_cases hx : I x=none
  · rw [if_pos hx,inner_plusState]
    have he : (∑ y ∈ Finset.univ.filter (fun y => I.symm y=none),
        recordLevel s j a (I.addPair x y)) =
        if I.size+1=j then ∑ y ∈ Finset.univ.filter (fun y => I.symm y=none),
          a (I.addPair x y) else 0 := by
      by_cases hj : I.size+1=j
      · rw [if_pos hj]
        apply Finset.sum_congr rfl
        intro y hy
        rw [recordLevel,diagProj_apply,size_addPair I x y hx (Finset.mem_filter.mp hy).2,
          if_pos hj]
      · rw [if_neg hj]
        apply Finset.sum_eq_zero
        intro y hy
        rw [recordLevel,diagProj_apply,size_addPair I x y hx (Finset.mem_filter.mp hy).2,
          if_neg hj]
    rw [he]
    by_cases hj : I.size+1=j <;> simp [hj,hx]
  · simp [hx]

theorem imageMap_apply (j : ℕ) (y : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    imageMap s j y a I = if I.size+1=j ∧ I.symm y=none then
      ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ) *
        ∑ x ∈ Finset.univ.filter (fun x => I x=none), a (I.addPair x y)
      else 0 := by
  change flipDb s (domainMap s j y (flipDb s a)) I = _
  rw [flipDb_apply,domainMap_apply]
  simp only [size_symm,PEquiv.symm_symm,flipDb_apply,addPair_symm]
  rfl

theorem domainMap_Gam_adjoint_zero (j : ℕ) (x : Fin s)
    (v : Hil (Equiv.Perm (Fin s))) :
    domainMap s j x (ContinuousLinearMap.adjoint (Gam s j) v) = 0 := by
  ext I
  rw [domainMap_apply]
  by_cases h : I.size+1=j ∧ I x=none
  · rw [if_pos h,← h.1,Gam_adjoint_zero_sum I.size I rfl x h.2 v,mul_zero]
    rfl
  · rw [if_neg h]
    rfl

theorem imageMap_Gam_adjoint_zero (j : ℕ) (y : Fin s)
    (v : Hil (Equiv.Perm (Fin s))) :
    imageMap s j y (ContinuousLinearMap.adjoint (Gam s j) v) = 0 := by
  ext I
  rw [imageMap_apply]
  by_cases h : I.size+1=j ∧ I.symm y=none
  · rw [if_pos h,← h.1,Gam_adjoint_inverse_zero_sum I.size I rfl y h.2 v,mul_zero]
    rfl
  · rw [if_neg h]
    rfl

theorem laplacian_Gam_adjoint_zero (j : ℕ) (v : Hil (Equiv.Perm (Fin s))) :
    laplacian s j (ContinuousLinearMap.adjoint (Gam s j) v) = 0 := by
  simp only [laplacian,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,domainMap_Gam_adjoint_zero,imageMap_Gam_adjoint_zero,
    map_zero,add_zero,Finset.sum_const_zero]

lemma recordLevel_adjoint (s j : ℕ) :
    ContinuousLinearMap.adjoint (recordLevel s j) = recordLevel s j := by
  simp only [recordLevel,diagProj,map_sum,ketBra_eq_rankOne,InnerProductSpace.adjoint_rankOne]

theorem domainMap_square (s j : ℕ) (x : Fin s) :
    (ContinuousLinearMap.adjoint (domainMap s j x)).comp (domainMap s j x) =
      (recordLevel s j).comp ((plusBlock s x).comp (recordLevel s j)) := by
  simp only [domainMap,ContinuousLinearMap.adjoint_comp,recordLevel_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  rw [← insertionBlock_comp_adjoint]
  simp only [ContinuousLinearMap.comp_assoc]

theorem laplacian_positive (s j : ℕ) : (laplacian s j).IsPositive := by
  unfold laplacian
  apply ContinuousLinearMap.isPositive_sum
  intro x _
  exact (domainMap s j x).isPositive_adjoint_comp_self.add
    (imageMap s j x).isPositive_adjoint_comp_self

theorem laplacian_energy (j : ℕ) (a : Hil (InjDb s)) :
    (inner ℂ a (laplacian s j a)).re =
      ∑ x : Fin s, (‖domainMap s j x a‖^2 + ‖imageMap s j x a‖^2) := by
  simp only [laplacian,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,inner_sum,inner_add_right,Complex.re_sum,Complex.add_re,
    ContinuousLinearMap.adjoint_inner_right]
  change (∑ x : Fin s, (RCLike.re (inner ℂ (domainMap s j x a) (domainMap s j x a)) +
    RCLike.re (inner ℂ (imageMap s j x a) (imageMap s j x a)))) = _
  simp only [inner_self_eq_norm_sq]

end
end WeldedPath.Incidence

end

-- Solutions.WeldedPathRootComparisonAdapters
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence IntertwinerPartial
open scoped BigOperators

variable {s : ℕ}

def selector (x y : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  diagProj (fun I : InjDb s => I x=some y)

def assertion (x y : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  (pC s x).comp ((selector x y).comp (pC s x))

lemma selector_apply (x y : Fin s) (v : Hil (InjDb s)) (I : InjDb s) :
    selector x y v I=if I x=some y then v I else 0 := diagProj_apply _ _ _

lemma unset_selector (x y : Fin s) (v : Hil (InjDb s)) :
    unsetBlock s x (selector x y v)=0 := by
  ext I
  simp only [unsetBlock,diagProj_apply,selector_apply]
  cases hx : I x <;> simp [hx]

lemma selector_unset (x y : Fin s) (v : Hil (InjDb s)) :
    selector x y (unsetBlock s x v)=0 := by
  ext I
  simp only [unsetBlock,diagProj_apply,selector_apply]
  cases hx : I x <;> simp [hx]

lemma insertionBlock_unset (x : Fin s) (v : Hil (InjDb s)) :
    insertionBlock s x (unsetBlock s x v)=insertionBlock s x v := by
  unfold insertionBlock
  simp only [ContinuousLinearMap.sum_apply,ketBra_apply,inner_ket]
  apply Finset.sum_congr rfl
  intro I hI
  rw [unsetBlock,diagProj_apply,if_pos (Finset.mem_filter.mp hI).2]

lemma insertionBlock_zero_of_unset_zero (x : Fin s) (v : Hil (InjDb s))
    (hv : unsetBlock s x v=0) : insertionBlock s x v=0 := by
  rw [← insertionBlock_unset x v,hv,map_zero]

theorem pC_on_known (x : Fin s) (v : Hil (InjDb s)) (hv : unsetBlock s x v=0) :
    pC s x v=v+ContinuousLinearMap.adjoint (insertionBlock s x) v-
      insertionBlock s x (ContinuousLinearMap.adjoint (insertionBlock s x) v) := by
  rw [pC_insertion_block]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.comp_apply,
    insertionBlock_zero_of_unset_zero x v hv,hv]
  abel

lemma recordLevel_Gam_adjoint (j : ℕ) (v : Hil (Equiv.Perm (Fin s))) :
    recordLevel s j (ContinuousLinearMap.adjoint (Gam s j) v)=
      ContinuousLinearMap.adjoint (Gam s j) v := by
  ext I
  simp only [recordLevel,diagProj_apply]
  by_cases hI : I.size=j
  · rw [if_pos hI]
  · rw [if_neg hI,Gam_adjoint_support s j v I hI]

theorem insertionBlock_adjoint_Gam_zero (j : ℕ) (x : Fin s)
    (v : Hil (Equiv.Perm (Fin s))) :
    ContinuousLinearMap.adjoint (insertionBlock s x)
      (ContinuousLinearMap.adjoint (Gam s j) v)=0 := by
  have he := domainMap_Gam_adjoint_zero j x v
  change ContinuousLinearMap.adjoint (insertionBlock s x)
    (recordLevel s j (ContinuousLinearMap.adjoint (Gam s j) v))=0 at he
  rwa [recordLevel_Gam_adjoint] at he

theorem pC_on_harmonic (j : ℕ) (x : Fin s) (a : Hil (InjDb s))
    (ha : a∈(ContinuousLinearMap.adjoint (Gam s j)).range) :
    pC s x a=insertionBlock s x a+a-unsetBlock s x a := by
  obtain ⟨v,rfl⟩ := ha
  change pC s x (ContinuousLinearMap.adjoint (Gam s j) v)=
    insertionBlock s x (ContinuousLinearMap.adjoint (Gam s j) v)+
      ContinuousLinearMap.adjoint (Gam s j) v-
      unsetBlock s x (ContinuousLinearMap.adjoint (Gam s j) v)
  rw [pC_insertion_block]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.comp_apply,
    insertionBlock_adjoint_Gam_zero,map_zero,add_zero,sub_zero]

def upward (x y : Fin s) (a : Hil (InjDb s)) : Hil (InjDb s) :=
  selector x y (insertionBlock s x a)-
    insertionBlock s x (ContinuousLinearMap.adjoint (insertionBlock s x)
      (selector x y (insertionBlock s x a)))

def middle (x y : Fin s) (a : Hil (InjDb s)) : Hil (InjDb s) :=
  selector x y a+ContinuousLinearMap.adjoint (insertionBlock s x)
    (selector x y (insertionBlock s x a))-
    insertionBlock s x (ContinuousLinearMap.adjoint (insertionBlock s x) (selector x y a))

def downward (x y : Fin s) (a : Hil (InjDb s)) : Hil (InjDb s) :=
  ContinuousLinearMap.adjoint (insertionBlock s x) (selector x y a)

theorem assertion_harmonic_split (j : ℕ) (x y : Fin s) (a : Hil (InjDb s))
    (ha : a∈(ContinuousLinearMap.adjoint (Gam s j)).range) :
    assertion x y a=upward x y a+middle x y a+downward x y a := by
  change pC s x (selector x y (pC s x a))=_
  rw [pC_on_harmonic j x a ha,map_sub,map_add,selector_unset,sub_zero,map_add,
    pC_on_known x _ (unset_selector x y _),pC_on_known x _ (unset_selector x y _)]
  unfold upward middle downward
  abel

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathCompressedAssertionCoordinates
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

def coefficient (I : InjDb s) : ℂ := ((Real.sqrt ((s-I.size : ℕ) : ℝ))⁻¹ : ℂ)

lemma coefficient_square (I : InjDb s) : coefficient I*coefficient I=1/((s-I.size : ℕ) : ℂ) :=
  square_normalization _

theorem insertion_apply_added (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) (hy : I.symm y=none) :
    insertionBlock s x a (I.addPair x y)=coefficient I*a I := by
  rw [← inner_ket,← ContinuousLinearMap.adjoint_inner_left,
    insertionBlock_adjoint_ket_added x y I hx hy,inner_smul_left,inner_ket]
  simp [coefficient]

theorem insertion_apply_unset (x : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) : insertionBlock s x a I=0 := by
  rw [← inner_ket,← ContinuousLinearMap.adjoint_inner_left,
    insertionBlock_adjoint_ket_unset I x hx,inner_zero_left]

theorem adjoint_selector_apply (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (selector x y a) I=
      if I x=none ∧ I.symm y=none then coefficient I*a (I.addPair x y) else 0 := by
  rw [insertionBlock_adjoint_apply]
  by_cases hx : I x=none
  · rw [if_pos hx,inner_plusState]
    change coefficient I*(∑ z ∈ Finset.univ.filter (fun z => I.symm z=none),
      selector x y a (I.addPair x z))=_
    by_cases hy : I.symm y=none
    · rw [if_pos ⟨hx,hy⟩]
      congr 1
      rw [Finset.sum_eq_single y]
      · rw [selector_apply,addPair_apply_self I x y hx hy,if_pos rfl]
      · intro z hz hzy
        rw [selector_apply,addPair_apply_self I x z hx (Finset.mem_filter.mp hz).2,if_neg]
        exact fun he => hzy (Option.some.inj he)
      · intro hn
        exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩)).elim
    · rw [if_neg (by simp [hy])]
      have hsum : (∑ z ∈ Finset.univ.filter (fun z => I.symm z=none),
          selector x y a (I.addPair x z))=0 := by
        apply Finset.sum_eq_zero
        intro z hz
        rw [selector_apply,addPair_apply_self I x z hx (Finset.mem_filter.mp hz).2,if_neg]
        intro he
        exact hy ((Option.some.inj he) ▸ (Finset.mem_filter.mp hz).2)
      rw [hsum,mul_zero]
  · rw [if_neg hx,if_neg (by simp [hx])]

theorem adjoint_selector_insertion_apply (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    ContinuousLinearMap.adjoint (insertionBlock s x) (selector x y (insertionBlock s x a)) I=
      if I x=none ∧ I.symm y=none then (1/((s-I.size : ℕ) : ℂ))*a I else 0 := by
  rw [adjoint_selector_apply]
  by_cases h : I x=none ∧ I.symm y=none
  · rw [if_pos h,if_pos h,insertion_apply_added x y a I h.1 h.2,← mul_assoc,coefficient_square]
  · rw [if_neg h,if_neg h]

theorem upward_apply_unset (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) : upward x y a I=0 := by
  simp only [upward,PiLp.sub_apply,selector_apply,insertion_apply_unset x _ I hx,hx]
  simp

theorem middle_apply_unset (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) :
    middle x y a I=if I.symm y=none then (1/((s-I.size : ℕ) : ℂ))*a I else 0 := by
  simp only [middle,PiLp.sub_apply,PiLp.add_apply,selector_apply,hx,
    adjoint_selector_insertion_apply,insertion_apply_unset x _ I hx]
  simp

theorem downward_apply_unset (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) :
    downward x y a I=if I.symm y=none then coefficient I*a (I.addPair x y) else 0 := by
  simp only [downward,adjoint_selector_apply,hx,true_and]

theorem downward_apply_added (x y z : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) (hz : I.symm z=none) : downward x y a (I.addPair x z)=0 := by
  simp only [downward,adjoint_selector_apply,addPair_apply_self I x z hx hz]
  simp

theorem upward_apply_added (x y z : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) (hz : I.symm z=none) :
    upward x y a (I.addPair x z)=if I.symm y=none then
      coefficient I*a I*((if z=y then 1 else 0)-(1/((s-I.size : ℕ) : ℂ))) else 0 := by
  simp only [upward,PiLp.sub_apply,selector_apply,addPair_apply_self I x z hx hz,
    Option.some.injEq,insertion_apply_added x z _ I hx hz,adjoint_selector_insertion_apply,hx,true_and]
  by_cases hy : I.symm y=none
  · rw [if_pos hy,if_pos hy]
    split_ifs <;> ring
  · have hzy : z≠y := fun he => hy (he ▸ hz)
    simp [hy,hzy]

theorem middle_apply_added (x y z : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) (hz : I.symm z=none) :
    middle x y a (I.addPair x z)=if I.symm y=none then
      a (I.addPair x y)*((if z=y then 1 else 0)-(1/((s-I.size : ℕ) : ℂ))) else 0 := by
  simp only [middle,PiLp.sub_apply,PiLp.add_apply,selector_apply,
    addPair_apply_self I x z hx hz,Option.some.injEq,adjoint_selector_insertion_apply,
    insertion_apply_added x z _ I hx hz,adjoint_selector_apply,hx,true_and]
  simp only [reduceCtorEq,false_and,if_false,add_zero]
  by_cases hy : I.symm y=none
  · rw [if_pos hy,if_pos hy,← mul_assoc,coefficient_square]
    by_cases hzy : z=y
    · subst z
      simp only [if_true]
      ring
    · simp only [if_neg hzy]
      ring
  · have hzy : z≠y := fun he => hy (he ▸ hz)
    simp [hy,hzy]

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathAssertionIncidenceCoordinates
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

def LevelSupported (r : ℕ) (a : Hil (InjDb s)) : Prop := ∀ I,I.size≠r → a I=0

lemma Gam_adjoint_levelSupported (r : ℕ) (ψ : Hil (Equiv.Perm (Fin s))) :
    LevelSupported r (ContinuousLinearMap.adjoint (Gam s r) ψ) := by
  intro I hI
  exact IntertwinerPartial.Gam_adjoint_support s r ψ I hI

lemma upward_levelSupported (r : ℕ) (x y : Fin s) (a : Hil (InjDb s))
    (ha : LevelSupported r a) : LevelSupported (r+1) (upward x y a) := by
  intro J hJ
  cases hx : J x with
  | none => exact upward_apply_unset x y a J hx
  | some z =>
    have hs := eraseAt_size J x z hx
    have hz := eraseAt_unused J x z hx
    have he := upward_apply_added x y z a (eraseAt J x) (eraseAt_self J x) hz
    rw [eraseAt_add J x z hx] at he
    rw [he]
    simp only [ha (eraseAt J x) (by omega),mul_zero,zero_mul,ite_self]

lemma middle_levelSupported (r : ℕ) (x y : Fin s) (a : Hil (InjDb s))
    (ha : LevelSupported r a) : LevelSupported r (middle x y a) := by
  intro J hJ
  cases hx : J x with
  | none => simp only [middle_apply_unset x y a J hx,ha J hJ,mul_zero,ite_self]
  | some z =>
    have hs := eraseAt_size J x z hx
    have hz := eraseAt_unused J x z hx
    have he := middle_apply_added x y z a (eraseAt J x) (eraseAt_self J x) hz
    rw [eraseAt_add J x z hx] at he
    rw [he]
    by_cases hy : (eraseAt J x).symm y=none
    · have hsize := size_addPair (eraseAt J x) x y (eraseAt_self J x) hy
      rw [if_pos hy,ha _ (by omega),zero_mul]
    · rw [if_neg hy]

lemma downward_support (r : ℕ) (x y : Fin s) (a : Hil (InjDb s))
    (ha : LevelSupported r a) (J : InjDb s) (hJ : J.size+1≠r) : downward x y a J=0 := by
  cases hx : J x with
  | none =>
    rw [downward_apply_unset x y a J hx]
    split_ifs with hy
    · rw [ha _ (by rw [size_addPair J x y hx hy]; exact hJ),mul_zero]
    · rfl
  | some z =>
    have he := downward_apply_added x y z a (eraseAt J x) (eraseAt_self J x) (eraseAt_unused J x z hx)
    rwa [eraseAt_add J x z hx] at he

def Harmonic (r : ℕ) (a : Hil (InjDb s)) : Prop :=
  (∀ (I : InjDb s),I.size+1=r → ∀ x,I x=none →
    ∑ y ∈ Finset.univ.filter (fun y => I.symm y=none),a (I.addPair x y)=0) ∧
  (∀ (I : InjDb s),I.size+1=r → ∀ y,I.symm y=none →
    ∑ x ∈ Finset.univ.filter (fun x => I x=none),a (I.addPair x y)=0)

lemma Gam_adjoint_harmonic (r : ℕ) (ψ : Hil (Equiv.Perm (Fin s))) :
    Harmonic r (ContinuousLinearMap.adjoint (Gam s r) ψ) := by
  constructor
  · intro I hI x hx
    rw [← hI]
    exact Gam_adjoint_zero_sum I.size I rfl x hx ψ
  · intro I hI y hy
    rw [← hI]
    exact Gam_adjoint_inverse_zero_sum I.size I rfl y hy ψ

lemma harmonic_image_except (r : ℕ) (a : Hil (InjDb s)) (ha : Harmonic r a)
    (I : InjDb s) (hI : I.size+1=r) (x b : Fin s) (hx : I x=none) (hb : I.symm b=none) :
    ∑ u ∈ Finset.univ.filter (fun u => I u=none ∧ u≠x),a (I.addPair u b)=
      -a (I.addPair x b) := by
  have he : Finset.univ.filter (fun u => I u=none ∧ u≠x)=
      (Finset.univ.filter (fun u => I u=none)).erase x := by
    ext u
    simp [and_comm]
  rw [he]
  have hh := Finset.sum_erase_add (Finset.univ.filter (fun u => I u=none))
    (fun u => a (I.addPair u b)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
  rw [ha.2 I hI b hb] at hh
  exact eq_neg_of_add_eq_zero_left hh

lemma added_symm_apply (I : InjDb s) (x y z : Fin s)
    (hx : I x=none) (hy : I.symm y=none) :
    (I.addPair x y).symm z=if z=y then some x else I.symm z := by
  rw [addPair_symm]
  by_cases hz : z=y
  · subst z
    rw [if_pos rfl,addPair_apply_self I.symm y x hy hx]
  · rw [if_neg hz,addPair_apply_other I.symm y x z hy hx hz]

lemma added_apply (I : InjDb s) (x y z : Fin s)
    (hx : I x=none) (hy : I.symm y=none) :
    I.addPair x y z=if z=x then some y else I z := by
  by_cases hz : z=x
  · subst z
    rw [if_pos rfl,addPair_apply_self I x y hx hy]
  · rw [if_neg hz,addPair_apply_other I x y z hx hy hz]

lemma addPair_commute (I : InjDb s) (x u y b : Fin s)
    (hx : I x=none) (hu : I u=none) (hy : I.symm y=none) (hb : I.symm b=none)
    (hux : u≠x) (hby : b≠y) :
    (I.addPair x y).addPair u b=(I.addPair u b).addPair x y := by
  have hu' : I.addPair x y u=none := by rw [added_apply I x y u hx hy,if_neg hux,hu]
  have hb' : (I.addPair x y).symm b=none := by rw [added_symm_apply I x y b hx hy,if_neg hby,hb]
  have hx' : I.addPair u b x=none := by rw [added_apply I u b x hu hb,if_neg hux.symm,hx]
  have hy' : (I.addPair u b).symm y=none := by rw [added_symm_apply I u b y hu hb,if_neg hby.symm,hy]
  apply PEquiv.ext
  intro z
  rw [added_apply _ u b z hu' hb',added_apply _ x y z hx' hy',
    added_apply I x y z hx hy,added_apply I u b z hu hb]
  by_cases hz : z=x
  · subst z
    simp [hux.symm]
  · by_cases hz' : z=u
    · subst z
      simp [hux]
    · simp [hz,hz']

theorem upward_image_unset (r : ℕ) (x y b : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hI : I.size=r) (hx : I x=none) (hb : I.symm b=none) :
    imageMap s (r+1) b (upward x y a) I=
      if I.symm y=none then (1/((s-r : ℕ) : ℂ))*a I*
        ((if b=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0 := by
  rw [imageMap_apply,if_pos ⟨by omega,hb⟩]
  have hs : (∑ u ∈ Finset.univ.filter (fun u => I u=none),upward x y a (I.addPair u b))=
      upward x y a (I.addPair x b) := by
    apply Finset.sum_eq_single x
    · intro u hu hux
      exact upward_apply_unset x y a _ (by
        rw [addPair_apply_other I u b x (Finset.mem_filter.mp hu).2 hb hux.symm,hx])
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)).elim
  rw [hs,upward_apply_added x y b a I hx hb]
  by_cases hy : I.symm y=none
  · rw [if_pos hy,if_pos hy]
    change coefficient I*(coefficient I*a I*((if b=y then 1 else 0)-1/((s-I.size : ℕ) : ℂ)))=_
    rw [← mul_assoc,← mul_assoc,coefficient_square,hI]
  · rw [if_neg hy,if_neg hy,mul_zero]

theorem upward_domain_unset_other (r : ℕ) (x y u : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) (hux : u≠x) : domainMap s r u (upward x y a) I=0 := by
  rw [domainMap_apply]
  split_ifs with h
  · have hs : (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none),upward x y a (I.addPair u b))=0 := by
      apply Finset.sum_eq_zero
      intro b hb
      exact upward_apply_unset x y a _ (by
        rw [addPair_apply_other I u b x h.2 (Finset.mem_filter.mp hb).2 hux.symm,hx])
    rw [hs,mul_zero]
  · rfl

theorem upward_image_added (r : ℕ) (x y z b : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (I : InjDb s) (hI : I.size+1=r)
    (hx : I x=none) (hz : I.symm z=none) (hb : I.symm b=none) (hbz : b≠z) :
    imageMap s (r+1) b (upward x y a) (I.addPair x z)=
      if I.symm y=none ∧ y≠b then
        -(1/((s-r : ℕ) : ℂ))*a (I.addPair x b)*
          ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0 := by
  have hJ : (I.addPair x z).size=r := (size_addPair I x z hx hz).trans hI
  have hb' : (I.addPair x z).symm b=none := by
    rw [added_symm_apply I x z b hx hz,if_neg hbz,hb]
  rw [imageMap_apply,if_pos ⟨by omega,hb'⟩]
  have hfilter : Finset.univ.filter (fun u => I.addPair x z u=none)=
      Finset.univ.filter (fun u => I u=none ∧ u≠x) := by
    ext u
    rw [Finset.mem_filter,Finset.mem_filter,added_apply I x z u hx hz]
    by_cases hu : u=x <;> simp [hu]
  rw [hfilter]
  have hterm (u : Fin s) (hu : u∈Finset.univ.filter (fun u => I u=none ∧ u≠x)) :
      upward x y a ((I.addPair x z).addPair u b)=
        if I.symm y=none ∧ y≠b then
          ((Real.sqrt ((s-r : ℕ) : ℝ))⁻¹ : ℂ)*a (I.addPair u b)*
            ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0 := by
    obtain ⟨hu,hux⟩ := (Finset.mem_filter.mp hu).2
    rw [addPair_commute I x u z b hx hu hz hb hux hbz]
    have hx' : I.addPair u b x=none := by rw [added_apply I u b x hu hb,if_neg hux.symm,hx]
    have hz' : (I.addPair u b).symm z=none := by rw [added_symm_apply I u b z hu hb,if_neg hbz.symm,hz]
    rw [upward_apply_added x y z a _ hx' hz']
    have hsize : (I.addPair u b).size=r := (size_addPair I u b hu hb).trans hI
    simp only [coefficient,hsize,added_symm_apply I u b y hu hb]
    by_cases hyb : y=b <;> simp [hyb]
  rw [Finset.sum_congr rfl hterm]
  by_cases hy : I.symm y=none ∧ y≠b
  · simp only [if_pos hy]
    rw [← Finset.sum_mul,← Finset.mul_sum,harmonic_image_except r a ha I hI x b hx hb,hJ]
    rw [← mul_assoc,← mul_assoc,square_normalization]
    ring
  · simp [hy]

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardDomainCoordinates
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma harmonic_domain_except_two (r : ℕ) (a : Hil (InjDb s)) (ha : Harmonic r a)
    (I : InjDb s) (hI : I.size+1=r) (u z y : Fin s)
    (hu : I u=none) (hz : I.symm z=none) (hy : I.symm y=none) :
    (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none ∧ b≠z ∧ b≠y),
      a (I.addPair u b)) = -(a (I.addPair u z)+(if y≠z then a (I.addPair u y) else 0)) := by
  let S := Finset.univ.filter (fun b => I.symm b=none)
  have hzm : z∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
  have hym : y∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩
  have he : Finset.univ.filter (fun b => I.symm b=none ∧ b≠z ∧ b≠y)=(S.erase z).erase y := by
    ext b
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
    tauto
  rw [he]
  by_cases hyz : y=z
  · subst y
    rw [Finset.erase_idem,Finset.sum_erase_eq_sub hzm,ha.1 I hI u hu]
    simp
  · rw [Finset.sum_erase_eq_sub (Finset.mem_erase.mpr ⟨hyz,hym⟩),
      Finset.sum_erase_eq_sub hzm,ha.1 I hI u hu,if_pos hyz]
    ring

theorem upward_domain_added (r : ℕ) (x y z u : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (I : InjDb s) (hI : I.size+1=r)
    (hx : I x=none) (hz : I.symm z=none) (hu : I u=none) (hux : u≠x) :
    domainMap s (r+1) u (upward x y a) (I.addPair x z)=
      if I.symm y=none then
        -(1/((s-r : ℕ) : ℂ))*((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ))*
          (a (I.addPair u z)+(if y≠z then a (I.addPair u y) else 0)) else 0 := by
  have hJ : (I.addPair x z).size=r := (size_addPair I x z hx hz).trans hI
  have hu' : I.addPair x z u=none := by
    rw [added_apply I x z u hx hz,if_neg hux,hu]
  rw [domainMap_apply,if_pos ⟨by omega,hu'⟩]
  have hf : Finset.univ.filter (fun b => (I.addPair x z).symm b=none)=
      Finset.univ.filter (fun b => I.symm b=none ∧ b≠z) := by
    ext b
    rw [Finset.mem_filter,Finset.mem_filter,added_symm_apply I x z b hx hz]
    by_cases hb : b=z <;> simp [hb]
  rw [hf]
  have ht (b : Fin s) (hb : b∈Finset.univ.filter (fun b => I.symm b=none ∧ b≠z)) :
      upward x y a ((I.addPair x z).addPair u b)=
        if I.symm y=none ∧ b≠y then
          ((Real.sqrt ((s-r : ℕ) : ℝ))⁻¹ : ℂ)*a (I.addPair u b)*
            ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0 := by
    obtain ⟨hb,hbz⟩ := (Finset.mem_filter.mp hb).2
    rw [addPair_commute I x u z b hx hu hz hb hux hbz]
    have hx' : I.addPair u b x=none := by
      rw [added_apply I u b x hu hb,if_neg hux.symm,hx]
    have hz' : (I.addPair u b).symm z=none := by
      rw [added_symm_apply I u b z hu hb,if_neg hbz.symm,hz]
    rw [upward_apply_added x y z a _ hx' hz']
    have hs : (I.addPair u b).size=r := (size_addPair I u b hu hb).trans hI
    simp only [coefficient,hs,added_symm_apply I u b y hu hb]
    by_cases hby : b=y
    · subst b
      simp
    · simp [Ne.symm hby,hby]
  rw [Finset.sum_congr rfl ht]
  by_cases hy : I.symm y=none
  · rw [if_pos hy]
    have he : (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none ∧ b≠z),
        if I.symm y=none ∧ b≠y then
          ((Real.sqrt ((s-r : ℕ) : ℝ))⁻¹ : ℂ)*a (I.addPair u b)*
            ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0)=
        ((Real.sqrt ((s-r : ℕ) : ℝ))⁻¹ : ℂ)*
          (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none ∧ b≠z ∧ b≠y),a (I.addPair u b))*
            ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) := by
      rw [Finset.mul_sum,Finset.sum_mul]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : I.symm b=none <;> by_cases hbz : b=z <;> by_cases hby : b=y <;>
        simp [hy,hb,hbz,hby]
    rw [he,harmonic_domain_except_two r a ha I hI u z y hu hz hy,hJ]
    rw [← mul_assoc,← mul_assoc,square_normalization]
    ring
  · simp [hy]

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathMiddleIncidenceCoordinates
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem middle_image_unset (r : ℕ) (x y b : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (I : InjDb s) (hI : I.size+1=r)
    (hx : I x=none) (hb : I.symm b=none) :
    imageMap s r b (middle x y a) I=
      if I.symm y=none then coefficient I*
        (a (I.addPair x y)*((if b=y then 1 else 0)-1/((s-I.size : ℕ) : ℂ))-
          (if b≠y then (1/((s-r : ℕ) : ℂ))*a (I.addPair x b) else 0)) else 0 := by
  rw [imageMap_apply,if_pos ⟨hI,hb⟩]
  let U := Finset.univ.filter (fun u => I u=none)
  have hxm : x∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
  have he : U.erase x=Finset.univ.filter (fun u => I u=none ∧ u≠x) := by
    ext u
    simp [U,and_comm]
  have ht (u : Fin s) (hu : u∈U.erase x) :
      middle x y a (I.addPair u b)=if I.symm y=none ∧ b≠y then
        (1/((s-r : ℕ) : ℂ))*a (I.addPair u b) else 0 := by
    obtain ⟨hux,hu⟩ := Finset.mem_erase.mp hu
    have hu := (Finset.mem_filter.mp hu).2
    have hx' : I.addPair u b x=none := by
      rw [added_apply I u b x hu hb,if_neg (Ne.symm hux),hx]
    rw [middle_apply_unset x y a _ hx',size_addPair I u b hu hb,hI,
      added_symm_apply I u b y hu hb]
    by_cases hby : b=y
    · subst b
      simp
    · simp [hby,Ne.symm hby]
  change coefficient I*(∑ u ∈ U,middle x y a (I.addPair u b))=_
  rw [← Finset.sum_erase_add U (fun u => middle x y a (I.addPair u b)) hxm,
    Finset.sum_congr rfl ht,middle_apply_added x y b a I hx hb]
  by_cases hy : I.symm y=none
  · rw [if_pos hy,if_pos hy]
    by_cases hby : b=y
    · subst b
      simp
    · simp only [if_pos (show I.symm y=none ∧ b≠y from ⟨hy,hby⟩),if_pos hby]
      rw [← Finset.mul_sum,he,harmonic_image_except r a ha I hI x b hx hb]
      ring
  · simp [hy]

lemma harmonic_domain_except (r : ℕ) (a : Hil (InjDb s)) (ha : Harmonic r a)
    (I : InjDb s) (hI : I.size+1=r) (u y : Fin s)
    (hu : I u=none) (hy : I.symm y=none) :
    (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none ∧ b≠y),a (I.addPair u b))=
      -a (I.addPair u y) := by
  simpa only [and_self,ne_eq,not_true_eq_false,if_false,add_zero] using
    harmonic_domain_except_two r a ha I hI u y y hu hy hy

theorem middle_domain_unset_other (r : ℕ) (x y u : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (I : InjDb s) (hI : I.size+1=r)
    (hx : I x=none) (hu : I u=none) (hux : u≠x) :
    domainMap s r u (middle x y a) I=
      if I.symm y=none then
        -(coefficient I*(1/((s-r : ℕ) : ℂ)))*a (I.addPair u y) else 0 := by
  rw [domainMap_apply,if_pos ⟨hI,hu⟩]
  have ht (b : Fin s) (hb : b∈Finset.univ.filter (fun b => I.symm b=none)) :
      middle x y a (I.addPair u b)=if I.symm y=none ∧ b≠y then
        (1/((s-r : ℕ) : ℂ))*a (I.addPair u b) else 0 := by
    have hb := (Finset.mem_filter.mp hb).2
    have hx' : I.addPair u b x=none := by
      rw [added_apply I u b x hu hb,if_neg hux.symm,hx]
    rw [middle_apply_unset x y a _ hx',size_addPair I u b hu hb,hI,
      added_symm_apply I u b y hu hb]
    by_cases hby : b=y
    · subst b
      simp
    · simp [hby,Ne.symm hby]
  rw [Finset.sum_congr rfl ht]
  by_cases hy : I.symm y=none
  · rw [if_pos hy]
    have he : (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none),
        if I.symm y=none ∧ b≠y then (1/((s-r : ℕ) : ℂ))*a (I.addPair u b) else 0)=
        (1/((s-r : ℕ) : ℂ))*
          ∑ b ∈ Finset.univ.filter (fun b => I.symm b=none ∧ b≠y),a (I.addPair u b) := by
      rw [Finset.mul_sum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : I.symm b=none <;> by_cases hby : b=y <;> simp [hy,hb,hby]
    rw [he,harmonic_domain_except r a ha I hI u y hu hy]
    change coefficient I*((1/((s-r : ℕ) : ℂ))*(-a (I.addPair u y)))=_
    ring
  · simp [hy]

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathMiddleKnownIncidence
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma middle_apply_double (x y z u b : Fin s) (a : Hil (InjDb s)) (I : InjDb s)
    (hx : I x=none) (hu : I u=none) (hz : I.symm z=none) (hb : I.symm b=none)
    (hux : u≠x) (hbz : b≠z) :
    middle x y a ((I.addPair x z).addPair u b)=
      if I.symm y=none ∧ b≠y then
        a ((I.addPair x y).addPair u b)*
          ((if z=y then 1 else 0)-1/((s-(I.size+1) : ℕ) : ℂ)) else 0 := by
  rw [addPair_commute I x u z b hx hu hz hb hux hbz]
  have hx' : I.addPair u b x=none := by
    rw [added_apply I u b x hu hb,if_neg hux.symm,hx]
  have hz' : (I.addPair u b).symm z=none := by
    rw [added_symm_apply I u b z hu hb,if_neg hbz.symm,hz]
  rw [middle_apply_added x y z a _ hx' hz',size_addPair I u b hu hb,
    added_symm_apply I u b y hu hb]
  by_cases hby : b=y
  · subst b
    simp
  · rw [if_neg (Ne.symm hby)]
    by_cases hy : I.symm y=none
    · rw [if_pos hy,if_pos (show I.symm y=none ∧ b≠y from ⟨hy,hby⟩),
        ← addPair_commute I x u y b hx hu hy hb hux hby]
    · rw [if_neg hy,if_neg (fun h => hy h.1)]

theorem middle_image_added (r : ℕ) (x y z b : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (I : InjDb s) (hI : I.size+2=r)
    (hx : I x=none) (hz : I.symm z=none) (hb : I.symm b=none) (hbz : b≠z) :
    imageMap s r b (middle x y a) (I.addPair x z)=0 := by
  have hsize := size_addPair I x z hx hz
  have hb' : (I.addPair x z).symm b=none := by
    rw [added_symm_apply I x z b hx hz,if_neg hbz,hb]
  rw [imageMap_apply,if_pos ⟨by omega,hb'⟩]
  have hf : Finset.univ.filter (fun u => I.addPair x z u=none)=
      Finset.univ.filter (fun u => I u=none ∧ u≠x) := by
    ext u
    rw [Finset.mem_filter,Finset.mem_filter,added_apply I x z u hx hz]
    by_cases hu : u=x <;> simp [hu]
  rw [hf]
  have ht (u : Fin s) (hu : u∈Finset.univ.filter (fun u => I u=none ∧ u≠x)) :
      middle x y a ((I.addPair x z).addPair u b)=
        if I.symm y=none ∧ b≠y then a ((I.addPair x y).addPair u b)*
          ((if z=y then 1 else 0)-1/((s-(I.size+1) : ℕ) : ℂ)) else 0 :=
    middle_apply_double x y z u b a I hx (Finset.mem_filter.mp hu).2.1 hz hb
      (Finset.mem_filter.mp hu).2.2 hbz
  rw [Finset.sum_congr rfl ht]
  by_cases hy : I.symm y=none ∧ b≠y
  · simp only [if_pos hy]
    rw [← Finset.sum_mul]
    have hf' : Finset.univ.filter (fun u => I u=none ∧ u≠x)=
        Finset.univ.filter (fun u => I.addPair x y u=none) := by
      ext u
      rw [Finset.mem_filter,Finset.mem_filter,added_apply I x y u hx hy.1]
      by_cases hu : u=x <;> simp [hu]
    have hb'' : (I.addPair x y).symm b=none := by
      rw [added_symm_apply I x y b hx hy.1,if_neg hy.2,hb]
    rw [hf',ha.2 (I.addPair x y) (by rw [size_addPair I x y hx hy.1]; omega) b hb'',
      zero_mul,mul_zero]
  · simp [hy]

theorem middle_domain_added (r : ℕ) (x y z u : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (I : InjDb s) (hI : I.size+2=r)
    (hx : I x=none) (hz : I.symm z=none) (hu : I u=none) (hux : u≠x) :
    domainMap s r u (middle x y a) (I.addPair x z)=
      if I.symm y=none ∧ y≠z then
        (coefficient (I.addPair x z)*(1/((s-(I.size+1) : ℕ) : ℂ)))*
          a ((I.addPair x y).addPair u z) else 0 := by
  have hsize := size_addPair I x z hx hz
  have hu' : I.addPair x z u=none := by
    rw [added_apply I x z u hx hz,if_neg hux,hu]
  rw [domainMap_apply,if_pos ⟨by omega,hu'⟩]
  have hf : Finset.univ.filter (fun b => (I.addPair x z).symm b=none)=
      Finset.univ.filter (fun b => I.symm b=none ∧ b≠z) := by
    ext b
    rw [Finset.mem_filter,Finset.mem_filter,added_symm_apply I x z b hx hz]
    by_cases hb : b=z <;> simp [hb]
  rw [hf]
  have ht (b : Fin s) (hb : b∈Finset.univ.filter (fun b => I.symm b=none ∧ b≠z)) :
      middle x y a ((I.addPair x z).addPair u b)=
        if I.symm y=none ∧ b≠y then a ((I.addPair x y).addPair u b)*
          ((if z=y then 1 else 0)-1/((s-(I.size+1) : ℕ) : ℂ)) else 0 :=
    middle_apply_double x y z u b a I hx hu hz (Finset.mem_filter.mp hb).2.1
      hux (Finset.mem_filter.mp hb).2.2
  rw [Finset.sum_congr rfl ht]
  by_cases hy : I.symm y=none
  · let J := I.addPair x y
    have hJ : J.size+1=r := by rw [size_addPair I x y hx hy]; omega
    have huJ : J u=none := by rw [added_apply I x y u hx hy,if_neg hux,hu]
    have he : (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none ∧ b≠z),
        if I.symm y=none ∧ b≠y then a (J.addPair u b)*
          ((if z=y then 1 else 0)-1/((s-(I.size+1) : ℕ) : ℂ)) else 0)=
        (∑ b ∈ Finset.univ.filter (fun b => J.symm b=none ∧ b≠z),a (J.addPair u b))*
          ((if z=y then 1 else 0)-1/((s-(I.size+1) : ℕ) : ℂ)) := by
      rw [Finset.sum_mul]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      change (if I.symm b=none ∧ b≠z then _ else 0)=_
      rw [added_symm_apply I x y b hx hy]
      by_cases hb : I.symm b=none <;> by_cases hbz : b=z <;> by_cases hby : b=y <;>
        simp [hy,hb,hbz,hby]
    rw [he]
    by_cases hyz : y=z
    · subst y
      rw [if_neg (show ¬(I.symm z=none ∧ z≠z) by simp)]
      have hf' : Finset.univ.filter (fun b => J.symm b=none ∧ b≠z)=
          Finset.univ.filter (fun b => J.symm b=none) := by
        ext b
        have hzJ : J.symm z=some x := by rw [added_symm_apply I x z z hx hy,if_pos rfl]
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · exact And.left
        · intro hb
          refine ⟨hb,?_⟩
          intro h
          subst b
          simp [hzJ] at hb
      rw [hf',ha.1 J hJ u huJ,zero_mul,mul_zero]
    · have hzJ : J.symm z=none := by
        rw [added_symm_apply I x y z hx hy,if_neg (Ne.symm hyz),hz]
      rw [if_pos (show I.symm y=none ∧ y≠z from ⟨hy,hyz⟩),harmonic_domain_except r a ha J hJ u z huJ hzJ,
        if_neg (Ne.symm hyz)]
      change coefficient (I.addPair x z)*(-a (J.addPair u z)*(0-1/((s-(I.size+1) : ℕ) : ℂ)))=_
      ring
  · simp [hy]

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathIncidenceZeroRows
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma centered_unused_sum (I : InjDb s) (y : Fin s) (hy : I.symm y=none) :
    (∑ b ∈ Finset.univ.filter (fun b => I.symm b=none),
      ((if b=y then (1 : ℂ) else 0)-1/((s-I.size : ℕ) : ℂ)))=0 := by
  have hm : s-I.size≠0 := by
    rw [← unused_card I]
    exact Finset.card_ne_zero.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩⟩
  have hc : ((s-I.size : ℕ) : ℂ)≠0 := Nat.cast_ne_zero.mpr hm
  rw [Finset.sum_sub_distrib]
  simp [hy,unused_card,hc]

theorem upward_domain_self (j : ℕ) (x y : Fin s) (a : Hil (InjDb s)) :
    domainMap s j x (upward x y a)=0 := by
  ext I
  rw [domainMap_apply]
  by_cases h : I.size+1=j ∧ I x=none
  · rw [if_pos h]
    have ht (b : Fin s) (hb : b∈Finset.univ.filter (fun b => I.symm b=none)) :
        upward x y a (I.addPair x b)=if I.symm y=none then
          coefficient I*a I*((if b=y then 1 else 0)-1/((s-I.size : ℕ) : ℂ)) else 0 :=
      upward_apply_added x y b a I h.2 (Finset.mem_filter.mp hb).2
    rw [Finset.sum_congr rfl ht]
    by_cases hy : I.symm y=none
    · simp only [if_pos hy]
      rw [← Finset.mul_sum,centered_unused_sum I y hy,mul_zero,mul_zero]
      rfl
    · simp [hy]
  · rw [if_neg h]
    rfl

theorem middle_domain_self (j : ℕ) (x y : Fin s) (a : Hil (InjDb s)) :
    domainMap s j x (middle x y a)=0 := by
  ext I
  rw [domainMap_apply]
  by_cases h : I.size+1=j ∧ I x=none
  · rw [if_pos h]
    have ht (b : Fin s) (hb : b∈Finset.univ.filter (fun b => I.symm b=none)) :
        middle x y a (I.addPair x b)=if I.symm y=none then
          a (I.addPair x y)*((if b=y then 1 else 0)-1/((s-I.size : ℕ) : ℂ)) else 0 :=
      middle_apply_added x y b a I h.2 (Finset.mem_filter.mp hb).2
    rw [Finset.sum_congr rfl ht]
    by_cases hy : I.symm y=none
    · simp only [if_pos hy]
      rw [← Finset.mul_sum,centered_unused_sum I y hy,mul_zero,mul_zero]
      rfl
    · simp [hy]
  · rw [if_neg h]
    rfl

theorem upward_domain_unset (j : ℕ) (x y u : Fin s) (a : Hil (InjDb s))
    (I : InjDb s) (hx : I x=none) : domainMap s j u (upward x y a) I=0 := by
  by_cases hux : u=x
  · subst u
    rw [upward_domain_self]
    rfl
  · exact upward_domain_unset_other j x y u a I hx hux

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathReplacementCounting
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma eraseAt_unused_of_unused (I : InjDb s) (x b : Fin s) (hb : I.symm b=none) :
    (eraseAt I x).symm b=none := by
  cases he : (eraseAt I x).symm b with
  | none => rfl
  | some u =>
    have hu := ((eraseAt I x).inv u b).mp he
    change eraseAt I x u=some b at hu
    rw [eraseAt_apply] at hu
    by_cases hux : u=x
    · rw [if_pos hux] at hu
      cases hu
    · rw [if_neg hux] at hu
      have hh := (I.inv u b).mpr hu
      change I.symm b=some u at hh
      rw [hb] at hh
      cases hh

lemma eraseAt_addPair_unset (I : InjDb s) (x b : Fin s)
    (hx : I x=none) (hb : I.symm b=none) : eraseAt (I.addPair x b) x=I := by
  apply PEquiv.ext
  intro u
  rw [eraseAt_apply,added_apply I x b u hx hb]
  by_cases hu : u=x
  · subst u
    simp [hx]
  · simp [hu]

def replacement (x b : Fin s) (I : InjDb s) : InjDb s :=
  (eraseAt I x).addPair x b

lemma replacement_self (x b : Fin s) (I : InjDb s) (hb : I.symm b=none) :
    replacement x b I x=some b :=
  addPair_apply_self _ x b (eraseAt_self I x) (eraseAt_unused_of_unused I x b hb)

lemma replacement_recover (x z b : Fin s) (I : InjDb s)
    (hz : I x=some z) (hb : I.symm b=none) :
    (eraseAt (replacement x b I) x).addPair x z=I := by
  rw [replacement,eraseAt_addPair_unset _ x b (eraseAt_self I x)
    (eraseAt_unused_of_unused I x b hb),eraseAt_add I x z hz]

theorem replacement_injective_on (x z : Fin s) :
    Set.InjOn (fun p : Fin s × InjDb s => replacement x p.1 p.2)
      {p | p.2 x=some z ∧ p.2.symm p.1=none} := by
  rintro ⟨b,I⟩ ⟨hI,hb⟩ ⟨c,J⟩ ⟨hJ,hc⟩ he
  have hbc : b=c := by
    have hh := congrArg (fun K : InjDb s => K x) he
    rw [replacement_self x b I hb,replacement_self x c J hc] at hh
    exact Option.some.inj hh
  have hIJ : I=J := by
    have hh := congrArg (fun K : InjDb s => (eraseAt K x).addPair x z) he
    rwa [replacement_recover x z b I hI hb,replacement_recover x z c J hJ hc] at hh
  exact Prod.ext hbc hIJ

/-- Replacing the queried image is injective when the old image is fixed.
Thus summing over all possible new images costs no factor of the database size. -/
theorem replacement_energy_le (x z : Fin s) (a : Hil (InjDb s)) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin s × InjDb s =>
        p.2 x=some z ∧ p.2.symm p.1=none),‖a (replacement x p.1 p.2)‖^2) ≤ ‖a‖^2 := by
  let S := Finset.univ.filter (fun p : Fin s × InjDb s =>
    p.2 x=some z ∧ p.2.symm p.1=none)
  let f := fun p : Fin s × InjDb s => replacement x p.1 p.2
  have hinj : Set.InjOn f S := by
    intro p hp q hq h
    exact replacement_injective_on x z (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2 h
  change (∑ p ∈ S,‖a (f p)‖^2) ≤ _
  rw [← Finset.sum_image (f := fun I : InjDb s => ‖a I‖^2) hinj,EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun I _ _ => sq_nonneg ‖a I‖)

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathRelocationCounting
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

def relocation (x u y : Fin s) (J : InjDb s) : InjDb s :=
  (eraseAt J x).addPair u y

lemma eraseAt_unset (J : InjDb s) (x u : Fin s) (hu : J u=none) :
    eraseAt J x u=none := by
  rw [eraseAt_apply]
  split_ifs
  · rfl
  · exact hu

lemma relocation_self (x u y : Fin s) (J : InjDb s)
    (hu : J u=none) (hy : (eraseAt J x).symm y=none) :
    relocation x u y J u=some y :=
  addPair_apply_self _ u y (eraseAt_unset J x u hu) hy

lemma relocation_recover (x u y z : Fin s) (J : InjDb s)
    (hz : J x=some z) (hu : J u=none) (hy : (eraseAt J x).symm y=none) :
    (eraseAt (relocation x u y J) u).addPair x z=J := by
  rw [relocation,eraseAt_addPair_unset _ u y (eraseAt_unset J x u hu) hy,
    eraseAt_add J x z hz]

theorem relocation_injective_on (x z y : Fin s) :
    Set.InjOn (fun p : Fin s × InjDb s => relocation x p.1 y p.2)
      {p | p.2 x=some z ∧ p.2 p.1=none ∧ (eraseAt p.2 x).symm y=none} := by
  rintro ⟨u,I⟩ ⟨hI,hu,hy⟩ ⟨v,J⟩ ⟨hJ,hv,hy'⟩ he
  change relocation x u y I=relocation x v y J at he
  have huv : u=v := by
    have hi := ((relocation x u y I).inv u y).mpr (relocation_self x u y I hu hy)
    have hj := ((relocation x v y J).inv v y).mpr (relocation_self x v y J hv hy')
    rw [he] at hi
    exact Option.some.inj (hi.symm.trans hj)
  have hIJ : I=J := by
    subst v
    have hh := congrArg (fun K : InjDb s => (eraseAt K u).addPair x z) he
    rwa [relocation_recover x u y z I hI hu hy,
      relocation_recover x u y z J hJ hv hy'] at hh
  exact Prod.ext huv hIJ

theorem relocation_energy_le (x z y : Fin s) (a : Hil (InjDb s)) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin s × InjDb s =>
        p.2 x=some z ∧ p.2 p.1=none ∧ (eraseAt p.2 x).symm y=none),
      ‖a (relocation x p.1 y p.2)‖^2) ≤ ‖a‖^2 := by
  let S := Finset.univ.filter (fun p : Fin s × InjDb s =>
    p.2 x=some z ∧ p.2 p.1=none ∧ (eraseAt p.2 x).symm y=none)
  let f := fun p : Fin s × InjDb s => relocation x p.1 y p.2
  have hinj : Set.InjOn f S := by
    intro p hp q hq h
    exact relocation_injective_on x z y (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2 h
  change (∑ p ∈ S,‖a (f p)‖^2) ≤ _
  rw [← Finset.sum_image (f := fun I : InjDb s => ‖a I‖^2) hinj,
    EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun I _ _ => sq_nonneg ‖a I‖)

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardImageEstimate
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma complex_sub_norm_sq_le (u v : ℂ) : ‖u-v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (u-v)) (norm_sub_le u v) 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

lemma centered_norm_sq_le (c : ℝ) (hc : 0 ≤ c) (w : ℂ) (p : Prop) [Decidable p] :
    ‖(c : ℂ)*w*((if p then 1 else 0)-(c : ℂ))‖^2 ≤
      2*c^2*(if p then ‖w‖^2 else 0)+2*c^4*‖w‖^2 := by
  have hn : ‖(c : ℂ)‖=c := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  by_cases hp : p
  · rw [if_pos hp,if_pos hp]
    have he : (c : ℂ)*w*(1-(c : ℂ))=(c : ℂ)*w-(c : ℂ)^2*w := by ring
    rw [he]
    calc
      _ ≤ 2*‖(c : ℂ)*w‖^2+2*‖(c : ℂ)^2*w‖^2 := complex_sub_norm_sq_le _ _
      _ = _ := by simp only [norm_mul,norm_pow,hn]; ring
  · rw [if_neg hp,if_neg hp]
    have he : (c : ℂ)*w*(0-(c : ℂ))=-((c : ℂ)^2*w) := by ring
    rw [he,norm_neg,norm_mul,norm_pow,hn]
    nlinarith [mul_nonneg (pow_nonneg hc 4) (sq_nonneg ‖w‖)]

/-- A pointwise bound separating the diagonal and uniform parts of the
upward image incidence. Its subsequent summation uses actual replacement
injectivity rather than a bound depending on the number of records. -/
theorem upward_image_point_bound (r : ℕ) (x y b : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (J : InjDb s) :
    ‖imageMap s (r+1) b (upward x y a) J‖^2 ≤
      if J.symm b=none then
        2*((s-r : ℕ) : ℝ)⁻¹^2*
          (if J x=none then (if b=y then ‖a J‖^2 else 0)
            else (if J x=some y then ‖a (replacement x b J)‖^2 else 0))+
        2*((s-r : ℕ) : ℝ)⁻¹^4*
          (if J x=none then ‖a J‖^2 else ‖a (replacement x b J)‖^2)
      else 0 := by
  by_cases hb : J.symm b=none
  · rw [if_pos hb]
    by_cases hJ : J.size+1=r+1
    · have hsize : J.size=r := by omega
      have hc : 0 ≤ ((s-r : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      cases hx : J x with
      | none =>
        simp only [hx,if_true]
        rw [upward_image_unset r x y b a J hsize hx hb]
        by_cases hy : J.symm y=none
        · rw [if_pos hy]
          simpa only [Complex.ofReal_inv,Complex.ofReal_natCast,one_div] using
            centered_norm_sq_le ((s-r : ℕ) : ℝ)⁻¹ hc (a J) (b=y)
        · rw [if_neg hy,norm_zero,zero_pow (by decide : 2≠0)]
          split_ifs <;> positivity
      | some z =>
        simp only [hx,reduceCtorEq,if_false,Option.some.injEq]
        have hz : (eraseAt J x).symm z=none := eraseAt_unused J x z hx
        have hb' : (eraseAt J x).symm b=none := eraseAt_unused_of_unused J x b hb
        have hbz : b≠z := by
          intro h
          subst b
          have hh := (J.inv x z).mpr hx
          change J.symm z=some x at hh
          rw [hb] at hh
          cases hh
        have hp := upward_image_added r x y z b a ha (eraseAt J x)
          ((eraseAt_size J x z hx).trans hsize) (eraseAt_self J x) hz hb' hbz
        rw [eraseAt_add J x z hx] at hp
        rw [hp]
        by_cases hy : (eraseAt J x).symm y=none ∧ y≠b
        · rw [if_pos hy]
          simp only [neg_mul,norm_neg]
          simpa only [Complex.ofReal_inv,Complex.ofReal_natCast,one_div,replacement] using centered_norm_sq_le
            ((s-r : ℕ) : ℝ)⁻¹ hc (a (replacement x b J)) (z=y)
        · rw [if_neg hy,norm_zero,zero_pow (by decide : 2≠0)]
          split_ifs <;> positivity
    · rw [imageMap_apply,if_neg (fun h => hJ h.1),norm_zero,zero_pow (by decide : 2≠0)]
      split_ifs <;> positivity
  · rw [if_neg hb,imageMap_apply,if_neg (fun h => hb h.2),norm_zero,zero_pow (by decide : 2≠0)]

end
end WeldedPath.CompressedAssertions


end

-- Solutions.FiniteCenteredRows
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem masked_sum_norm_sq_le (w : ι → ℂ) (p : ι → Prop) :
    ‖∑ i,if p i then w i else 0‖^2 ≤ (Fintype.card ι : ℝ)*(∑ i,‖w i‖^2) := by
  calc
    _ ≤ (∑ i,‖if p i then w i else 0‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Fintype.card ι : ℝ)*(∑ i,‖if p i then w i else 0‖^2) := by
      simpa only [Finset.card_univ] using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := fun i => ‖if p i then w i else 0‖))
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by
      by_cases hp : p i
      · rw [if_pos hp]
      · rw [if_neg hp,norm_zero,zero_pow (by decide : 2≠0)]
        exact sq_nonneg _) (Nat.cast_nonneg _)

theorem centered_row_norm_sq_le [DecidableEq ι] (c : ℝ) (hc : 0 ≤ c) (w : ι → ℂ)
    (p : ι → Prop) (z : ι) :
    ‖∑ i,if p i then (c : ℂ)*w i*((if z=i then 1 else 0)-(c : ℂ)) else 0‖^2 ≤
      2*c^2*‖w z‖^2+2*(Fintype.card ι : ℝ)*c^4*(∑ i,‖w i‖^2) := by
  have he : (∑ i,if p i then (c : ℂ)*w i*((if z=i then 1 else 0)-(c : ℂ)) else 0)=
      (c : ℂ)*(if p z then w z else 0)-(c : ℂ)^2*(∑ i,if p i then w i else 0) := by
    calc
      _ = ∑ i,((if z=i then (c : ℂ)*(if p i then w i else 0) else 0)-
          (c : ℂ)^2*(if p i then w i else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hp : p i <;> by_cases hi : z=i <;> simp [hp,hi] <;> ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.mul_sum]
  have hn : ‖(c : ℂ)‖=c := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  have hp : ‖if p z then w z else 0‖^2 ≤ ‖w z‖^2 := by
    by_cases hz : p z <;> simp [hz]
  rw [he]
  calc
    _ ≤ 2*c^2*‖if p z then w z else 0‖^2+2*c^4*‖∑ i,if p i then w i else 0‖^2 := by
      have h := complex_sub_norm_sq_le ((c : ℂ)*(if p z then w z else 0))
        ((c : ℂ)^2*(∑ i,if p i then w i else 0))
      simpa only [norm_mul,norm_pow,hn,mul_pow,← pow_mul,Nat.reduceMul,mul_assoc] using h
    _ ≤ 2*c^2*‖w z‖^2+2*c^4*((Fintype.card ι : ℝ)*(∑ i,‖w i‖^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left (masked_sum_norm_sq_le w p) (by positivity))
    _ = _ := by ring

theorem centered_masked_row_norm_sq_le [DecidableEq ι]
    (c : ℝ) (hc : 0 ≤ c) (w : ι → ℂ) (p : ι → Prop) (z : ι) :
    ‖∑ i,if p i then (c : ℂ)*w i*((if z=i then 1 else 0)-(c : ℂ)) else 0‖^2 ≤
      2*c^2*(if p z then ‖w z‖^2 else 0)+
        2*(Fintype.card ι : ℝ)*c^4*(∑ i,if p i then ‖w i‖^2 else 0) := by
  have h := centered_row_norm_sq_le c hc (fun i => if p i then w i else 0) p z
  have he (i : ι) :
      (if p i then (c : ℂ)*(if p i then w i else 0)*
        ((if z=i then 1 else 0)-(c : ℂ)) else 0)=
      (if p i then (c : ℂ)*w i*((if z=i then 1 else 0)-(c : ℂ)) else 0) := by
    by_cases hp : p i <;> simp [hp]
  have hn (i : ι) : ‖if p i then w i else 0‖^2=(if p i then ‖w i‖^2 else 0) := by
    by_cases hp : p i <;> simp [hp]
  simpa only [he,hn] using h

theorem image_column_constant_le (s m : ℕ) (hm : 0 < m) (hs : s ≤ 2*m) :
    4*(s : ℝ)*(m : ℝ)⁻¹^2+4*(s : ℝ)^2*(m : ℝ)⁻¹^4 ≤ 24*(m : ℝ)⁻¹ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs' : (s : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hs
  have hs2 := pow_le_pow_left₀ (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hs' 2
  have h : 4*(s : ℝ)*(m : ℝ)^2+4*(s : ℝ)^2 ≤ 24*(m : ℝ)^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sq_nonneg (m : ℝ)),
      mul_nonneg (sub_nonneg.mpr hs') (sq_nonneg (m : ℝ))]
  have hh := div_le_div_of_nonneg_right h (le_of_lt (pow_pos hm0 4))
  calc
    _ = (4*(s : ℝ)*(m : ℝ)^2+4*(s : ℝ)^2)/(m : ℝ)^4 := by
      field_simp [ne_of_gt hm0]
    _ ≤ (24*(m : ℝ)^3)/(m : ℝ)^4 := hh
    _ = _ := by
      field_simp [ne_of_gt hm0]

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardDomainEstimate
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma complex_add_norm_sq_le (v w : ℂ) : ‖v+w‖^2 ≤ 2*‖v‖^2+2*‖w‖^2 := by
  simpa only [sub_neg_eq_add,norm_neg] using complex_sub_norm_sq_le v (-w)

lemma centered_two_norm_sq_le (c : ℝ) (hc : 0 ≤ c) (v w : ℂ)
    (p : Prop) [Decidable p] :
    ‖(c : ℂ)*((if p then 1 else 0)-(c : ℂ))*(v+(if ¬p then w else 0))‖^2 ≤
      2*c^2*(if p then ‖v‖^2 else 0)+4*c^4*(‖v‖^2+‖w‖^2) := by
  have h := centered_norm_sq_le c hc (v+(if ¬p then w else 0)) p
  have he : (c : ℂ)*((if p then 1 else 0)-(c : ℂ))*(v+(if ¬p then w else 0))=
      (c : ℂ)*(v+(if ¬p then w else 0))*((if p then 1 else 0)-(c : ℂ)) := by ring
  have hd : (if p then ‖v+(if ¬p then w else 0)‖^2 else 0)=
      (if p then ‖v‖^2 else 0) := by by_cases hp : p <;> simp [hp]
  have hu : ‖v+(if ¬p then w else 0)‖^2 ≤ 2*(‖v‖^2+‖w‖^2) := by
    by_cases hp : p
    · simp only [hp,not_true_eq_false,if_false,add_zero]
      nlinarith [sq_nonneg ‖v‖,sq_nonneg ‖w‖]
    · simpa only [hp,not_false_eq_true,if_true,mul_add] using complex_add_norm_sq_le v w
  rw [he]
  exact h.trans (by rw [hd]; nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ c^4)])

def relocationMass (x z y u : Fin s) (a : Hil (InjDb s)) (J : InjDb s) : ℝ :=
  if J x=some z ∧ J u=none ∧ (eraseAt J x).symm y=none then
    ‖a (relocation x u y J)‖^2 else 0

lemma relocationMass_nonneg (x z y u : Fin s) (a : Hil (InjDb s)) (J : InjDb s) :
    0 ≤ relocationMass x z y u a J := by unfold relocationMass; positivity

theorem relocationMass_sum_le (x z y : Fin s) (a : Hil (InjDb s)) :
    (∑ p : Fin s × InjDb s,relocationMass x z y p.1 a p.2) ≤ ‖a‖^2 := by
  simpa only [relocationMass,Finset.sum_filter] using relocation_energy_le x z y a

theorem upward_domain_point_bound (r : ℕ) (x y u : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) (J : InjDb s) :
    ‖domainMap s (r+1) u (upward x y a) J‖^2 ≤
      2*((s-r : ℕ) : ℝ)⁻¹^2*relocationMass x y y u a J+
        4*((s-r : ℕ) : ℝ)⁻¹^4*
          (∑ z : Fin s,(relocationMass x z z u a J+relocationMass x z y u a J)) := by
  have hn : 0 ≤ 2*((s-r : ℕ) : ℝ)⁻¹^2*relocationMass x y y u a J+
      4*((s-r : ℕ) : ℝ)⁻¹^4*
        (∑ z : Fin s,(relocationMass x z z u a J+relocationMass x z y u a J)) := by
    unfold relocationMass
    positivity
  by_cases hJu : J u=none
  · by_cases hsize : J.size+1=r+1
    · cases hx : J x with
      | none =>
        rw [upward_domain_unset (r+1) x y u a J hx,norm_zero,zero_pow (by decide : 2≠0)]
        exact hn
      | some z =>
        have hux : u≠x := by intro h; subst u; rw [hx] at hJu; cases hJu
        have hz := eraseAt_unused J x z hx
        have hu := eraseAt_unset J x u hJu
        have hsz : (eraseAt J x).size+1=r := by
          have hh := eraseAt_size J x z hx
          omega
        have he := upward_domain_added r x y z u a ha (eraseAt J x) hsz
          (eraseAt_self J x) hz hu hux
        rw [eraseAt_add J x z hx] at he
        rw [he]
        by_cases hy : (eraseAt J x).symm y=none
        · rw [if_pos hy]
          have hc : 0 ≤ ((s-r : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
          have hh := centered_two_norm_sq_le ((s-r : ℕ) : ℝ)⁻¹ hc
            (a (relocation x u z J)) (a (relocation x u y J)) (z=y)
          have hneg : -(1/((s-r : ℕ) : ℂ))*((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ))*
              (a ((eraseAt J x).addPair u z)+(if y≠z then a ((eraseAt J x).addPair u y) else 0))=
              -((1/((s-r : ℕ) : ℂ))*((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ))*
                (a (relocation x u z J)+(if z≠y then a (relocation x u y J) else 0))) := by
            simp only [relocation,ne_comm,neg_mul]
          rw [hneg,norm_neg]
          by_cases hzy : z=y
          · subst z
            simpa [Complex.ofReal_inv,Complex.ofReal_natCast,one_div,
              relocationMass,hx,hJu,hz,hy,ite_and,Finset.sum_add_distrib] using hh
          · simpa [Complex.ofReal_inv,Complex.ofReal_natCast,one_div,
              relocationMass,hx,hJu,hz,hy,ite_and,hzy,Finset.sum_add_distrib] using hh
        · rw [if_neg hy,norm_zero,zero_pow (by decide : 2≠0)]
          exact hn
    · rw [domainMap_apply,if_neg (fun h => hsize h.1),norm_zero,
        zero_pow (by decide : 2≠0)]
      exact hn
  · rw [domainMap_apply,if_neg (fun h => hJu h.2),norm_zero,
      zero_pow (by decide : 2≠0)]
    exact hn

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardDomainColumn
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem upward_domain_energy_le (r : ℕ) (x : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) :
    (∑ y : Fin s,∑ u : Fin s,‖domainMap s (r+1) u (upward x y a)‖^2) ≤
      (2*(s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^2+
        8*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4)*‖a‖^2 := by
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  have hy (y : Fin s) :
      (∑ u : Fin s,‖domainMap s (r+1) u (upward x y a)‖^2) ≤
        (2*c^2+8*(s : ℝ)*c^4)*‖a‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    rw [← Fintype.sum_prod_type (fun p : Fin s × InjDb s =>
      ‖domainMap s (r+1) p.1 (upward x y a) p.2‖^2)]
    calc
      _ ≤ ∑ p : Fin s × InjDb s,(2*c^2*relocationMass x y y p.1 a p.2+
          4*c^4*(∑ z : Fin s,(relocationMass x z z p.1 a p.2+
            relocationMass x z y p.1 a p.2))) :=
        Finset.sum_le_sum fun p _ => upward_domain_point_bound r x y p.1 a ha p.2
      _ = 2*c^2*(∑ p : Fin s × InjDb s,relocationMass x y y p.1 a p.2)+
          4*c^4*(∑ z : Fin s,((∑ p : Fin s × InjDb s,relocationMass x z z p.1 a p.2)+
            (∑ p : Fin s × InjDb s,relocationMass x z y p.1 a p.2))) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,Finset.sum_comm]
        simp only [Finset.sum_add_distrib]
      _ ≤ 2*c^2*‖a‖^2+4*c^4*(∑ _z : Fin s,(‖a‖^2+‖a‖^2)) := add_le_add
        (mul_le_mul_of_nonneg_left (relocationMass_sum_le x y y a) (by positivity))
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => add_le_add
          (relocationMass_sum_le x z z a) (relocationMass_sum_le x z y a)) (by positivity))
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
          EuclideanSpace.norm_sq_eq]
        ring
  calc
    _ ≤ ∑ _y : Fin s,((2*c^2+8*(s : ℝ)*c^4)*‖a‖^2) := Finset.sum_le_sum fun y _ => hy y
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,c]; ring

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardDomainRow
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma centered_two_row_norm_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (hc : 0 ≤ c) (v w : ι → ℂ) (p : ι → Prop) (z : ι) :
    ‖∑ i,if p i then (c : ℂ)*((if z=i then 1 else 0)-(c : ℂ))*
      (v i+(if i≠z then w i else 0)) else 0‖^2 ≤
      2*c^2*‖v z‖^2+4*(Fintype.card ι : ℝ)*c^4*
        (∑ i,(‖v i‖^2+(if p i then ‖w i‖^2 else 0))) := by
  have h := centered_masked_row_norm_sq_le c hc
    (fun i => v i+(if i≠z then w i else 0)) p z
  have he (i : ι) :
      (if p i then (c : ℂ)*((if z=i then 1 else 0)-(c : ℂ))*
        (v i+(if i≠z then w i else 0)) else 0)=
      (if p i then (c : ℂ)*(v i+(if i≠z then w i else 0))*
        ((if z=i then 1 else 0)-(c : ℂ)) else 0) := by
    by_cases hp : p i <;> simp only [hp,if_true,if_false] <;> ring
  have hd : (if p z then ‖v z+(if z≠z then w z else 0)‖^2 else 0) ≤ ‖v z‖^2 := by
    by_cases hp : p z <;> simp [hp]
  have hu (i : ι) : (if p i then ‖v i+(if i≠z then w i else 0)‖^2 else 0) ≤
      2*(‖v i‖^2+(if p i then ‖w i‖^2 else 0)) := by
    by_cases hp : p i
    · simp only [if_pos hp]
      by_cases hi : i=z
      · simp only [hi,ne_self_iff_false,if_false,add_zero]
        nlinarith [sq_nonneg ‖v z‖,sq_nonneg ‖w z‖]
      · simpa only [if_pos hi,mul_add] using complex_add_norm_sq_le (v i) (w i)
    · simp only [if_neg hp,add_zero]
      positivity
  rw [Finset.sum_congr rfl (fun i _ => he i)]
  refine h.trans ((add_le_add (mul_le_mul_of_nonneg_left hd (by positivity))
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hu i) (by positivity))).trans_eq ?_)
  rw [← Finset.mul_sum]
  ring

theorem upward_domain_row_point (r : ℕ) (x u : Fin s) (a : Fin s → Hil (InjDb s))
    (ha : ∀ y,Harmonic r (a y)) (J : InjDb s) :
    ‖∑ y : Fin s,domainMap s (r+1) u (upward x y (a y)) J‖^2 ≤
      2*((s-r : ℕ) : ℝ)⁻¹^2*(∑ z : Fin s,relocationMass x z z u (a z) J)+
        4*(s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^4*(∑ y : Fin s,∑ z : Fin s,
          (relocationMass x z z u (a y) J+relocationMass x z y u (a y) J)) := by
  have hn : 0 ≤ 2*((s-r : ℕ) : ℝ)⁻¹^2*(∑ z : Fin s,relocationMass x z z u (a z) J)+
      4*(s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^4*(∑ y : Fin s,∑ z : Fin s,
        (relocationMass x z z u (a y) J+relocationMass x z y u (a y) J)) := by
    unfold relocationMass
    positivity
  by_cases hJu : J u=none
  · by_cases hsize : J.size+1=r+1
    · cases hx : J x with
      | none =>
        simp only [upward_domain_unset (r+1) x _ u _ J hx,
          Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]
        exact hn
      | some z =>
        have hux : u≠x := by intro h; subst u; rw [hx] at hJu; cases hJu
        have hz := eraseAt_unused J x z hx
        have hu := eraseAt_unset J x u hJu
        have hsz : (eraseAt J x).size+1=r := by
          have hh := eraseAt_size J x z hx
          omega
        have he (y : Fin s) := upward_domain_added r x y z u (a y) (ha y) (eraseAt J x) hsz
          (eraseAt_self J x) hz hu hux
        simp only [eraseAt_add J x z hx] at he
        rw [Finset.sum_congr rfl (fun y _ => he y)]
        have hneg : (∑ y : Fin s,if (eraseAt J x).symm y=none then
            -(1/((s-r : ℕ) : ℂ))*((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ))*
              (a y ((eraseAt J x).addPair u z)+
                (if y≠z then a y ((eraseAt J x).addPair u y) else 0)) else 0)=
            -(∑ y : Fin s,if (eraseAt J x).symm y=none then
              (1/((s-r : ℕ) : ℂ))*((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ))*
                (a y (relocation x u z J)+(if y≠z then a y (relocation x u y J) else 0)) else 0) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : (eraseAt J x).symm y=none <;> simp [hy,relocation,neg_mul]
        rw [hneg,norm_neg]
        have hc : 0 ≤ ((s-r : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
        have hh := centered_two_row_norm_sq_le ((s-r : ℕ) : ℝ)⁻¹ hc
          (fun y => a y (relocation x u z J)) (fun y => a y (relocation x u y J))
          (fun y => (eraseAt J x).symm y=none) z
        have hm (z' y' : Fin s) (v : Hil (InjDb s)) : relocationMass x z' y' u v J=
            if z=z' then (if (eraseAt J x).symm y'=none then
              ‖v (relocation x u y' J)‖^2 else 0) else 0 := by
          simp only [relocationMass,hx,hJu,Option.some.injEq,true_and,and_true,ite_and]
        simpa only [hm,Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,
          if_true,hz,Complex.ofReal_inv,Complex.ofReal_natCast,one_div,Fintype.card_fin] using hh
    · have hz (y : Fin s) : domainMap s (r+1) u (upward x y (a y)) J=0 := by
        rw [domainMap_apply,if_neg (fun h => hsize h.1)]
      simp only [hz,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]
      exact hn
  · have hz (y : Fin s) : domainMap s (r+1) u (upward x y (a y)) J=0 := by
      rw [domainMap_apply,if_neg (fun h => hJu h.2)]
    simp only [hz,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]
    exact hn

theorem upward_domain_row_energy_le (r : ℕ) (x : Fin s) (a : Fin s → Hil (InjDb s))
    (ha : ∀ y,Harmonic r (a y)) :
    (∑ u : Fin s,‖∑ y : Fin s,domainMap s (r+1) u (upward x y (a y))‖^2) ≤
      (2*((s-r : ℕ) : ℝ)⁻¹^2+8*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4)*
        (∑ y : Fin s,‖a y‖^2) := by
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  have hD : (∑ p : Fin s × InjDb s,∑ z : Fin s,relocationMass x z z p.1 (a z) p.2) ≤
      ∑ z : Fin s,‖a z‖^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun z _ => relocationMass_sum_le x z z (a z)
  have hUy (y : Fin s) : (∑ p : Fin s × InjDb s,∑ z : Fin s,
      (relocationMass x z z p.1 (a y) p.2+relocationMass x z y p.1 (a y) p.2)) ≤
      2*(s : ℝ)*‖a y‖^2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _z : Fin s,(‖a y‖^2+‖a y‖^2) := Finset.sum_le_sum fun z _ => by
        rw [Finset.sum_add_distrib]
        exact add_le_add (relocationMass_sum_le x z z (a y)) (relocationMass_sum_le x z y (a y))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  have hU : (∑ p : Fin s × InjDb s,∑ y : Fin s,∑ z : Fin s,
      (relocationMass x z z p.1 (a y) p.2+relocationMass x z y p.1 (a y) p.2)) ≤
      2*(s : ℝ)*(∑ y : Fin s,‖a y‖^2) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => hUy y
  conv_lhs =>
    arg 2
    ext u
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
  rw [← Fintype.sum_prod_type (fun p : Fin s × InjDb s =>
    ‖∑ y : Fin s,domainMap s (r+1) p.1 (upward x y (a y)) p.2‖^2)]
  change _ ≤ (2*c^2+8*(s : ℝ)^2*c^4)*(∑ y : Fin s,‖a y‖^2)
  calc
    _ ≤ ∑ p : Fin s × InjDb s,
        (2*c^2*(∑ z : Fin s,relocationMass x z z p.1 (a z) p.2)+
          4*(s : ℝ)*c^4*(∑ y : Fin s,∑ z : Fin s,
            (relocationMass x z z p.1 (a y) p.2+relocationMass x z y p.1 (a y) p.2))) :=
      Finset.sum_le_sum fun p _ => upward_domain_row_point r x p.1 a ha p.2
    _ = 2*c^2*(∑ p : Fin s × InjDb s,∑ z : Fin s,relocationMass x z z p.1 (a z) p.2)+
        4*(s : ℝ)*c^4*(∑ p : Fin s × InjDb s,∑ y : Fin s,∑ z : Fin s,
          (relocationMass x z z p.1 (a y) p.2+relocationMass x z y p.1 (a y) p.2)) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ 2*c^2*(∑ y : Fin s,‖a y‖^2)+4*(s : ℝ)*c^4*(2*(s : ℝ)*(∑ y : Fin s,‖a y‖^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hD (by positivity))
        (mul_le_mul_of_nonneg_left hU (by positivity))
    _ = _ := by ring

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardImageColumn
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

def imageDiagonalEnergy (x y : Fin s) (a : Hil (InjDb s)) : ℝ :=
  ∑ p : Fin s × InjDb s, if p.2.symm p.1=none then
    (if p.2 x=none then (if p.1=y then ‖a p.2‖^2 else 0)
      else (if p.2 x=some y then ‖a (replacement x p.1 p.2)‖^2 else 0)) else 0

def imageUniformEnergy (x : Fin s) (a : Hil (InjDb s)) : ℝ :=
  ∑ p : Fin s × InjDb s, if p.2.symm p.1=none then
    (if p.2 x=none then ‖a p.2‖^2 else ‖a (replacement x p.1 p.2)‖^2) else 0

theorem imageDiagonalEnergy_le (x y : Fin s) (a : Hil (InjDb s)) :
    imageDiagonalEnergy x y a ≤ 2*‖a‖^2 := by
  have hpoint (p : Fin s × InjDb s) :
      (if p.2.symm p.1=none then
        (if p.2 x=none then (if p.1=y then ‖a p.2‖^2 else 0)
          else (if p.2 x=some y then ‖a (replacement x p.1 p.2)‖^2 else 0)) else 0) ≤
      (if p.1=y then ‖a p.2‖^2 else 0)+
        (if p.2 x=some y ∧ p.2.symm p.1=none then ‖a (replacement x p.1 p.2)‖^2 else 0) := by
    split_ifs <;> (try tauto) <;>
      nlinarith [sq_nonneg ‖a p.2‖,sq_nonneg ‖a (replacement x p.1 p.2)‖]
  have hfirst : (∑ p : Fin s × InjDb s,if p.1=y then ‖a p.2‖^2 else 0)=‖a‖^2 := by
    rw [Fintype.sum_prod_type]
    simp [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ p : Fin s × InjDb s,((if p.1=y then ‖a p.2‖^2 else 0)+
        (if p.2 x=some y ∧ p.2.symm p.1=none then ‖a (replacement x p.1 p.2)‖^2 else 0)) :=
      Finset.sum_le_sum fun p _ => hpoint p
    _ = ‖a‖^2+(∑ p ∈ Finset.univ.filter (fun p : Fin s × InjDb s =>
        p.2 x=some y ∧ p.2.symm p.1=none),‖a (replacement x p.1 p.2)‖^2) := by
      rw [Finset.sum_add_distrib,hfirst,Finset.sum_filter]
    _ ≤ ‖a‖^2+‖a‖^2 := add_le_add_right (replacement_energy_le x y a) _
    _ = _ := by ring

theorem imageUniformEnergy_le (x : Fin s) (a : Hil (InjDb s)) :
    imageUniformEnergy x a ≤ 2*(s : ℝ)*‖a‖^2 := by
  have hpoint (p : Fin s × InjDb s) :
      (if p.2.symm p.1=none then
        (if p.2 x=none then ‖a p.2‖^2 else ‖a (replacement x p.1 p.2)‖^2) else 0) ≤
      ‖a p.2‖^2+∑ z : Fin s,
        (if p.2 x=some z ∧ p.2.symm p.1=none then ‖a (replacement x p.1 p.2)‖^2 else 0) := by
    by_cases hb : p.2.symm p.1=none
    · cases hx : p.2 x with
      | none => simp [hb,hx]
      | some z => simp [hb,hx,Option.some.injEq,sq_nonneg]
    · simp only [if_neg hb,hb,and_false,if_false,Finset.sum_const_zero,add_zero]
      exact sq_nonneg _
  have hfirst : (∑ p : Fin s × InjDb s,‖a p.2‖^2)=(s : ℝ)*‖a‖^2 := by
    simp [Fintype.sum_prod_type,EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ p : Fin s × InjDb s,(‖a p.2‖^2+∑ z : Fin s,
        (if p.2 x=some z ∧ p.2.symm p.1=none then ‖a (replacement x p.1 p.2)‖^2 else 0)) :=
      Finset.sum_le_sum fun p _ => hpoint p
    _ = (s : ℝ)*‖a‖^2+∑ z : Fin s,∑ p ∈ Finset.univ.filter (fun p : Fin s × InjDb s =>
        p.2 x=some z ∧ p.2.symm p.1=none),‖a (replacement x p.1 p.2)‖^2 := by
      rw [Finset.sum_add_distrib,hfirst,Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ (s : ℝ)*‖a‖^2+∑ _z : Fin s,‖a‖^2 := add_le_add le_rfl
      (Finset.sum_le_sum fun z _ => replacement_energy_le x z a)
    _ = _ := by simp; ring

theorem upward_image_energy_le (r : ℕ) (x : Fin s) (a : Hil (InjDb s))
    (ha : Harmonic r a) :
    (∑ y : Fin s,∑ b : Fin s,‖imageMap s (r+1) b (upward x y a)‖^2) ≤
      (4*(s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^2+
        4*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4)*‖a‖^2 := by
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  have hy (y : Fin s) :
      (∑ b : Fin s,‖imageMap s (r+1) b (upward x y a)‖^2) ≤
        2*c^2*imageDiagonalEnergy x y a+2*c^4*imageUniformEnergy x a := by
    simp only [EuclideanSpace.norm_sq_eq]
    rw [← Fintype.sum_prod_type (fun p : Fin s × InjDb s =>
      ‖imageMap s (r+1) p.1 (upward x y a) p.2‖^2)]
    calc
      _ ≤ ∑ p : Fin s × InjDb s,
          (if p.2.symm p.1=none then
            2*c^2*(if p.2 x=none then (if p.1=y then ‖a p.2‖^2 else 0)
              else (if p.2 x=some y then ‖a (replacement x p.1 p.2)‖^2 else 0))+
            2*c^4*(if p.2 x=none then ‖a p.2‖^2 else ‖a (replacement x p.1 p.2)‖^2)
          else 0) := Finset.sum_le_sum fun p _ => upward_image_point_bound r x y p.1 a ha p.2
      _ = _ := by
        unfold imageDiagonalEnergy imageUniformEnergy
        rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        by_cases hb : p.2.symm p.1=none <;> simp [hb]
  calc
    _ ≤ ∑ y : Fin s,(2*c^2*imageDiagonalEnergy x y a+2*c^4*imageUniformEnergy x a) :=
      Finset.sum_le_sum fun y _ => hy y
    _ ≤ ∑ _y : Fin s,(2*c^2*(2*‖a‖^2)+2*c^4*(2*(s : ℝ)*‖a‖^2)) :=
      Finset.sum_le_sum fun y _ => add_le_add
        (mul_le_mul_of_nonneg_left (imageDiagonalEnergy_le x y a) (by positivity))
        (mul_le_mul_of_nonneg_left (imageUniformEnergy_le x a) (by positivity))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,c]; ring

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardImageRow
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem upward_image_row_point (r : ℕ) (x b : Fin s) (a : Fin s → Hil (InjDb s))
    (ha : ∀ y,Harmonic r (a y)) (J : InjDb s) :
    ‖∑ y : Fin s,imageMap s (r+1) b (upward x y (a y)) J‖^2 ≤
      2*((s-r : ℕ) : ℝ)⁻¹^2*(∑ y : Fin s,if J.symm b=none then
        (if J x=none then (if b=y then ‖a y J‖^2 else 0)
          else (if J x=some y then ‖a y (replacement x b J)‖^2 else 0)) else 0)+
      2*(s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^4*(∑ y : Fin s,if J.symm b=none then
        (if J x=none then ‖a y J‖^2 else ‖a y (replacement x b J)‖^2) else 0) := by
  by_cases hb : J.symm b=none
  · simp only [if_pos hb]
    by_cases hJ : J.size+1=r+1
    · have hsize : J.size=r := by omega
      have hc : 0 ≤ ((s-r : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      cases hx : J x with
      | none =>
        simp only [if_true]
        have ht (y : Fin s) : imageMap s (r+1) b (upward x y (a y)) J=
            if J.symm y=none then (1/((s-r : ℕ) : ℂ))*a y J*
              ((if b=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0 :=
          upward_image_unset r x y b (a y) J hsize hx hb
        rw [Finset.sum_congr rfl (fun y _ => ht y)]
        simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
        simpa only [Complex.ofReal_inv,Complex.ofReal_natCast,one_div,Fintype.card_fin] using
          centered_row_norm_sq_le ((s-r : ℕ) : ℝ)⁻¹ hc (fun y => a y J)
            (fun y => J.symm y=none) b
      | some z =>
        simp only [reduceCtorEq,if_false,Option.some.injEq,Finset.sum_ite_eq,Finset.mem_univ,if_true]
        have hz : (eraseAt J x).symm z=none := eraseAt_unused J x z hx
        have hb' : (eraseAt J x).symm b=none := eraseAt_unused_of_unused J x b hb
        have hbz : b≠z := by
          intro h
          subst b
          have hh := (J.inv x z).mpr hx
          change J.symm z=some x at hh
          rw [hb] at hh
          cases hh
        have ht (y : Fin s) : imageMap s (r+1) b (upward x y (a y)) J=
            if (eraseAt J x).symm y=none ∧ y≠b then
              -(1/((s-r : ℕ) : ℂ))*a y (replacement x b J)*
                ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0 := by
          have h := upward_image_added r x y z b (a y) (ha y) (eraseAt J x)
            ((eraseAt_size J x z hx).trans hsize) (eraseAt_self J x) hz hb' hbz
          rwa [eraseAt_add J x z hx] at h
        rw [Finset.sum_congr rfl (fun y _ => ht y)]
        have he : (∑ y : Fin s,if (eraseAt J x).symm y=none ∧ y≠b then
            -(1/((s-r : ℕ) : ℂ))*a y (replacement x b J)*
              ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0)=
            -(∑ y : Fin s,if (eraseAt J x).symm y=none ∧ y≠b then
              (1/((s-r : ℕ) : ℂ))*a y (replacement x b J)*
                ((if z=y then 1 else 0)-1/((s-r : ℕ) : ℂ)) else 0) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : (eraseAt J x).symm y=none ∧ y≠b <;> simp [hy,neg_mul]
        rw [he,norm_neg]
        simpa only [Complex.ofReal_inv,Complex.ofReal_natCast,one_div,Fintype.card_fin] using
          centered_row_norm_sq_le ((s-r : ℕ) : ℝ)⁻¹ hc (fun y => a y (replacement x b J))
            (fun y => (eraseAt J x).symm y=none ∧ y≠b) z
    · have hz (y : Fin s) : imageMap s (r+1) b (upward x y (a y)) J=0 := by
        rw [imageMap_apply,if_neg (fun h => hJ h.1)]
      simp only [hz,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]
      positivity
  · have hz (y : Fin s) : imageMap s (r+1) b (upward x y (a y)) J=0 := by
      rw [imageMap_apply,if_neg (fun h => hb h.2)]
    simp [hb,hz]

theorem upward_image_row_energy_le (r : ℕ) (x : Fin s) (a : Fin s → Hil (InjDb s))
    (ha : ∀ y,Harmonic r (a y)) :
    (∑ b : Fin s,‖∑ y : Fin s,imageMap s (r+1) b (upward x y (a y))‖^2) ≤
      (4*((s-r : ℕ) : ℝ)⁻¹^2+4*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4)*
        (∑ y : Fin s,‖a y‖^2) := by
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  let d := fun (y : Fin s) (p : Fin s × InjDb s) => if p.2.symm p.1=none then
    (if p.2 x=none then (if p.1=y then ‖a y p.2‖^2 else 0)
      else (if p.2 x=some y then ‖a y (replacement x p.1 p.2)‖^2 else 0)) else 0
  let e := fun (y : Fin s) (p : Fin s × InjDb s) => if p.2.symm p.1=none then
    (if p.2 x=none then ‖a y p.2‖^2 else ‖a y (replacement x p.1 p.2)‖^2) else 0
  have hD : (∑ p : Fin s × InjDb s,∑ y : Fin s,d y p)=
      ∑ y : Fin s,imageDiagonalEnergy x y (a y) := by rw [Finset.sum_comm]; rfl
  have hE : (∑ p : Fin s × InjDb s,∑ y : Fin s,e y p)=
      ∑ y : Fin s,imageUniformEnergy x (a y) := by rw [Finset.sum_comm]; rfl
  conv_lhs =>
    arg 2
    ext b
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
  rw [← Fintype.sum_prod_type (fun p : Fin s × InjDb s =>
    ‖∑ y : Fin s,imageMap s (r+1) p.1 (upward x y (a y)) p.2‖^2)]
  change _ ≤ (4*c^2+4*(s : ℝ)^2*c^4)*(∑ y : Fin s,‖a y‖^2)
  calc
    _ ≤ ∑ p : Fin s × InjDb s,(2*c^2*(∑ y : Fin s,d y p)+
        2*(s : ℝ)*c^4*(∑ y : Fin s,e y p)) :=
      Finset.sum_le_sum fun p _ => upward_image_row_point r x p.1 a ha p.2
    _ = 2*c^2*(∑ y : Fin s,imageDiagonalEnergy x y (a y))+
        2*(s : ℝ)*c^4*(∑ y : Fin s,imageUniformEnergy x (a y)) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hD,hE]
    _ ≤ 2*c^2*(∑ y : Fin s,2*‖a y‖^2)+
        2*(s : ℝ)*c^4*(∑ y : Fin s,2*(s : ℝ)*‖a y‖^2) := add_le_add
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => imageDiagonalEnergy_le x y (a y)) (by positivity))
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => imageUniformEnergy_le x (a y)) (by positivity))
    _ = _ := by rw [← Finset.mul_sum,← Finset.mul_sum]; ring

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathUpwardImageBounds
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem upward_image_column_bound (r : ℕ) (hr : 2*r ≤ s)
    (x : Fin s) (a : Hil (InjDb s)) (ha : Harmonic r a) :
    (∑ y : Fin s,∑ b : Fin s,‖imageMap s (r+1) b (upward x y a)‖^2) ≤
      24*((s-r : ℕ) : ℝ)⁻¹*‖a‖^2 := by
  have hs := x.isLt
  exact (upward_image_energy_le r x a ha).trans (mul_le_mul_of_nonneg_right
    (image_column_constant_le s (s-r) (by omega) (by omega)) (sq_nonneg _))

theorem upward_image_row_bound (r : ℕ) (hr : 2*r ≤ s)
    (x : Fin s) (a : Fin s → Hil (InjDb s)) (ha : ∀ y,Harmonic r (a y)) :
    (∑ b : Fin s,‖∑ y : Fin s,imageMap s (r+1) b (upward x y (a y))‖^2) ≤
      24*((s-r : ℕ) : ℝ)⁻¹*(∑ y : Fin s,‖a y‖^2) := by
  have hs := x.isLt
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have h : 4*((s-r : ℕ) : ℝ)⁻¹^2+4*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4 ≤
      4*(s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^2+4*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (((s-r : ℕ) : ℝ)⁻¹))]
  exact (upward_image_row_energy_le r x a ha).trans (mul_le_mul_of_nonneg_right
    (h.trans (image_column_constant_le s (s-r) (by omega) (by omega))) (by positivity))

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathIncidenceGap
section

namespace WeldedPath.Incidence

noncomputable section
open Classical HilbertSupport CompressedPrimitive
open scoped BigOperators

theorem incidence_distance_bound {s j : ℕ} (hsmall : 3*j ≤ s+1)
    (ψ : Hil (InjDb s)) (hψ : ∀ I : InjDb s,I.size≠j → ψ I=0) :
    ‖ψ-((ContinuousLinearMap.adjoint (Gam s j)).range).starProjection ψ‖^2 ≤
      2*∑ x : Fin s,(‖domainMap s j x ψ‖^2+‖imageMap s j x ψ‖^2) := by
  let D : Fin s → Hil (InjDb s) →L[ℂ] Hil (InjDb s) := fun x =>
    ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x=none),ketBra (ket I) (plusState I x)
  have hD (x : Fin s) (v : Hil (InjDb s)) (hv : ∀ I : InjDb s,I.size≠j → v I=0) :
      D x v=domainMap s j x v := by
    have hlevel : recordLevel s j v=v := by
      ext I
      rw [recordLevel,diagProj_apply]
      by_cases hI : I.size=j
      · rw [if_pos hI]
      · rw [if_neg hI,hv I hI]
    change (∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x=none),
      ketBra (ket I) (plusState I x)) v=
      ContinuousLinearMap.adjoint (insertionBlock s x) (recordLevel s j v)
    rw [← insertionBlock_adjoint,hlevel]
  have hf : ∀ I : InjDb s,I.size≠j → flipDb s ψ I=0 := by
    intro I hI
    rw [flipDb_apply]
    exact hψ I.symm (by simpa only [size_symm] using hI)
  have hI (x : Fin s) : imageMap s j x ψ=flipDb s (D x (flipDb s ψ)) := by
    change flipDb s (domainMap s j x (flipDb s ψ))=_
    rw [← hD x (flipDb s ψ) hf]
  have h := (WeldedPath.incidence_gap s j hsmall ψ hψ).2
  change ‖ψ-((ContinuousLinearMap.adjoint (Gam s j)).range).starProjection ψ‖^2 ≤
    2*∑ x : Fin s,(‖D x ψ‖^2+‖D x (flipDb s ψ)‖^2) at h
  simpa only [hD _ ψ hψ,hI,EncodedOracleUnitary.flipDb_norm] using h

end
end WeldedPath.Incidence

end

-- Solutions.WeldedPathUpwardLeakage
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem upward_domain_column_bound (r : ℕ) (hr : 2*r ≤ s)
    (x : Fin s) (a : Hil (InjDb s)) (ha : Harmonic r a) :
    (∑ y : Fin s,∑ u : Fin s,‖domainMap s (r+1) u (upward x y a)‖^2) ≤
      48*((s-r : ℕ) : ℝ)⁻¹*‖a‖^2 := by
  have hs := x.isLt
  have hb := image_column_constant_le s (s-r) (by omega) (by omega)
  have hn : 0 ≤ (s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^2 := by positivity
  exact (upward_domain_energy_le r x a ha).trans (mul_le_mul_of_nonneg_right
    (by nlinarith : 2*(s : ℝ)*((s-r : ℕ) : ℝ)⁻¹^2+
      8*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4 ≤ 48*((s-r : ℕ) : ℝ)⁻¹) (sq_nonneg _))

theorem upward_domain_row_bound (r : ℕ) (hr : 2*r ≤ s)
    (x : Fin s) (a : Fin s → Hil (InjDb s)) (ha : ∀ y,Harmonic r (a y)) :
    (∑ u : Fin s,‖∑ y : Fin s,domainMap s (r+1) u (upward x y (a y))‖^2) ≤
      48*((s-r : ℕ) : ℝ)⁻¹*(∑ y : Fin s,‖a y‖^2) := by
  have hs := x.isLt
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hb := image_column_constant_le s (s-r) (by omega) (by omega)
  have hc := sq_nonneg (((s-r : ℕ) : ℝ)⁻¹)
  have hsc := mul_nonneg (sub_nonneg.mpr hs1) hc
  exact (upward_domain_row_energy_le r x a ha).trans (mul_le_mul_of_nonneg_right
    (by nlinarith : 2*((s-r : ℕ) : ℝ)⁻¹^2+
      8*(s : ℝ)^2*((s-r : ℕ) : ℝ)⁻¹^4 ≤ 48*((s-r : ℕ) : ℝ)⁻¹) (by positivity))

/-- Squared error of the actual upward assertion, summed over response values. -/
theorem upward_leakage_column_bound (r : ℕ) (hr : 3*r+2 ≤ s)
    (x : Fin s) (a : Hil (InjDb s)) (hsupport : LevelSupported r a) (ha : Harmonic r a) :
    (∑ y : Fin s,‖upward x y a-
      ((ContinuousLinearMap.adjoint (Gam s (r+1))).range).starProjection (upward x y a)‖^2) ≤
      144*((s-r : ℕ) : ℝ)⁻¹*‖a‖^2 := by
  have h (y : Fin s) := incidence_distance_bound (by omega : 3*(r+1) ≤ s+1)
    (upward x y a) (upward_levelSupported r x y a hsupport)
  have hd := upward_domain_column_bound r (by omega) x a ha
  have hi := upward_image_column_bound r (by omega) x a ha
  calc
    _ ≤ ∑ y : Fin s,2*∑ z : Fin s,
        (‖domainMap s (r+1) z (upward x y a)‖^2+
          ‖imageMap s (r+1) z (upward x y a)‖^2) := Finset.sum_le_sum fun y _ => h y
    _ = 2*((∑ y : Fin s,∑ z : Fin s,‖domainMap s (r+1) z (upward x y a)‖^2)+
        (∑ y : Fin s,∑ z : Fin s,‖imageMap s (r+1) z (upward x y a)‖^2)) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

/-- The corresponding bound for a coherent superposition of response values. -/
theorem upward_leakage_row_bound (r : ℕ) (hr : 3*r+2 ≤ s)
    (x : Fin s) (a : Fin s → Hil (InjDb s))
    (hsupport : ∀ y,LevelSupported r (a y)) (ha : ∀ y,Harmonic r (a y)) :
    ‖(∑ y : Fin s,upward x y (a y))-
      ((ContinuousLinearMap.adjoint (Gam s (r+1))).range).starProjection
        (∑ y : Fin s,upward x y (a y))‖^2 ≤
      144*((s-r : ℕ) : ℝ)⁻¹*(∑ y : Fin s,‖a y‖^2) := by
  have hlevel : LevelSupported (r+1) (∑ y : Fin s,upward x y (a y)) := by
    intro J hJ
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
    exact Finset.sum_eq_zero fun y _ => upward_levelSupported r x y (a y) (hsupport y) J hJ
  have h := incidence_distance_bound (by omega : 3*(r+1) ≤ s+1)
    (∑ y : Fin s,upward x y (a y)) hlevel
  have hd := upward_domain_row_bound r (by omega) x a ha
  have hi := upward_image_row_bound r (by omega) x a ha
  simp only [map_sum,Finset.sum_add_distrib] at h
  simp only [map_sum]
  linarith

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathMiddleConstants
section

namespace WeldedPath.CompressedAssertions

variable {s : Nat}

lemma middle_scalar_constants (t c d : ℝ) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hc1 : c ≤ 1) (hd : 0 ≤ d) (hdc : d ≤ c) (htc : t*c ≤ 2) :
    (4*d+4*t*d^3+2*t*d*c^2 ≤ 24*c) ∧
    (4*d+4*t^2*d^3+2*t*d*c^2 ≤ 24*c) ∧
    (t*d*c^2+t^2*d^3 ≤ 6*c) := by
  have hc2 : c^2 ≤ c := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]
  have ht2 : (t*c)^2 ≤ 4 := by nlinarith [sq_nonneg (t*c),mul_nonneg ht hc]
  have htc3 : t*c^3 ≤ 2*c := by
    nlinarith [mul_le_mul_of_nonneg_right htc (sq_nonneg c)]
  have ht2c3 : t^2*c^3 ≤ 4*c := by
    nlinarith [mul_le_mul_of_nonneg_right ht2 hc]
  have hd3 := pow_le_pow_left₀ hd hdc 3
  have htd3 : t*d^3 ≤ 2*c :=
    (mul_le_mul_of_nonneg_left hd3 ht).trans htc3
  have ht2d3 : t^2*d^3 ≤ 4*c :=
    (mul_le_mul_of_nonneg_left hd3 (sq_nonneg t)).trans ht2c3
  have htdc : t*d*c^2 ≤ 2*c := by
    have h := mul_le_mul_of_nonneg_left hdc (mul_nonneg ht (sq_nonneg c))
    nlinarith
  constructor
  · linarith
  · constructor <;> linarith

lemma middle_constants (r : ℕ) (hr : 2*r ≤ s) (hs : 0 < s) :
    (4*((s-r+1 : ℕ) : ℝ)⁻¹+4*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹^3+
      2*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2 ≤ 24*((s-r : ℕ) : ℝ)⁻¹) ∧
    (4*((s-r+1 : ℕ) : ℝ)⁻¹+4*(s : ℝ)^2*((s-r+1 : ℕ) : ℝ)⁻¹^3+
      2*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2 ≤ 24*((s-r : ℕ) : ℝ)⁻¹) ∧
    ((s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2+
      (s : ℝ)^2*((s-r+1 : ℕ) : ℝ)⁻¹^3 ≤ 6*((s-r : ℕ) : ℝ)⁻¹) := by
  have hm : (0 : ℝ) < (s-r : ℕ) := by exact_mod_cast (by omega : 0 < s-r)
  have hm1 : (1 : ℝ) ≤ (s-r : ℕ) := by exact_mod_cast (by omega : 1 ≤ s-r)
  apply middle_scalar_constants _ _ _ (Nat.cast_nonneg _) (by positivity)
    (inv_le_one_of_one_le₀ hm1) (by positivity)
  · exact inv_anti₀ hm (by exact_mod_cast (by omega : s-r ≤ s-r+1))
  · rw [← div_eq_mul_inv,div_le_iff₀ hm]
    exact_mod_cast (by omega : s ≤ 2*(s-r))


end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathExtensionCounting
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem extension_injective_on (x : Fin s) :
    Set.InjOn (fun p : Fin s × InjDb s => p.2.addPair x p.1)
      {p | p.2 x=none ∧ p.2.symm p.1=none} := by
  rintro ⟨y,I⟩ ⟨hx,hy⟩ ⟨z,J⟩ ⟨hx',hz⟩ he
  change I.addPair x y=J.addPair x z at he
  have hyz : y=z := by
    have h := congrArg (fun K : InjDb s => K x) he
    rw [addPair_apply_self I x y hx hy,addPair_apply_self J x z hx' hz] at h
    exact Option.some.inj h
  have hIJ : I=J := by
    have h := congrArg (fun K : InjDb s => eraseAt K x) he
    rwa [eraseAt_addPair_unset I x y hx hy,eraseAt_addPair_unset J x z hx' hz] at h
  exact Prod.ext hyz hIJ

def extensionMass (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s) : ℝ :=
  if I x=none ∧ I.symm y=none then ‖a (I.addPair x y)‖^2 else 0

lemma extensionMass_nonneg (x y : Fin s) (a : Hil (InjDb s)) (I : InjDb s) :
    0 ≤ extensionMass x y a I := by unfold extensionMass; positivity

theorem extensionMass_sum_le (x : Fin s) (a : Hil (InjDb s)) :
    (∑ p : Fin s × InjDb s,extensionMass x p.1 a p.2) ≤ ‖a‖^2 := by
  let S := Finset.univ.filter (fun p : Fin s × InjDb s => p.2 x=none ∧ p.2.symm p.1=none)
  let f := fun p : Fin s × InjDb s => p.2.addPair x p.1
  have hinj : Set.InjOn f S := by
    intro p hp q hq he
    exact extension_injective_on x (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he
  change (∑ p : Fin s × InjDb s,
    if p.2 x=none ∧ p.2.symm p.1=none then ‖a (f p)‖^2 else 0) ≤ _
  rw [← Finset.sum_filter]
  change (∑ p ∈ S,‖a (f p)‖^2) ≤ _
  rw [← Finset.sum_image (f := fun I : InjDb s => ‖a I‖^2) hinj,EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun I _ _ => sq_nonneg ‖a I‖)

theorem extensionMass_fixed_sum_le (x y : Fin s) (a : Hil (InjDb s)) :
    (∑ I : InjDb s,extensionMass x y a I) ≤ ‖a‖^2 := by
  apply le_trans _ (extensionMass_sum_le x a)
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (fun z _ => Finset.sum_nonneg fun I _ => extensionMass_nonneg x z a I)
    (Finset.mem_univ y)

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathMiddleImageEstimate
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma coefficient_norm_sq (I : InjDb s) :
    ‖coefficient I‖^2=((s-I.size : ℕ) : ℝ)⁻¹ := by
  simp only [coefficient,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

lemma scalar_centered_norm_sq_le (d : ℝ) (hd : 0 ≤ d) (v : ℂ)
    (p : Prop) [Decidable p] :
    ‖v*((if p then 1 else 0)-(d : ℂ))‖^2 ≤
      2*(if p then ‖v‖^2 else 0)+2*d^2*‖v‖^2 := by
  have hn : ‖(d : ℂ)‖=d := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd]
  have he : v*((if p then 1 else 0)-(d : ℂ))=
      (if p then v else 0)-(d : ℂ)*v := by by_cases hp : p <;> simp [hp] <;> ring
  have h := complex_sub_norm_sq_le (if p then v else 0) ((d : ℂ)*v)
  rw [he]
  by_cases hp : p <;> simpa [hp,norm_mul,norm_pow,hn,mul_pow,mul_assoc] using h

lemma middle_scalar_norm_sq_le (q : ℂ) (d c : ℝ) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hq : ‖q‖^2=d) (v w : ℂ) (p : Prop) [Decidable p] :
    ‖q*(v*((if p then 1 else 0)-(d : ℂ))-(if ¬p then (c : ℂ)*w else 0))‖^2 ≤
      4*d*(if p then ‖v‖^2 else 0)+4*d^3*‖v‖^2+2*d*c^2*‖w‖^2 := by
  have hn : ‖(c : ℂ)‖=c := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  have hw : ‖if ¬p then (c : ℂ)*w else 0‖^2 ≤ c^2*‖w‖^2 := by
    by_cases hp : p
    · simp only [hp,not_true_eq_false,if_false,norm_zero,zero_pow (by decide : 2≠0)]
      positivity
    · simp only [hp,not_false_eq_true,if_true,norm_mul,mul_pow,hn,le_refl]
  rw [norm_mul,mul_pow,hq]
  calc
    _ ≤ d*(2*‖v*((if p then 1 else 0)-(d : ℂ))‖^2+
        2*‖if ¬p then (c : ℂ)*w else 0‖^2) :=
      mul_le_mul_of_nonneg_left (complex_sub_norm_sq_le _ _) hd
    _ ≤ d*(2*(2*(if p then ‖v‖^2 else 0)+2*d^2*‖v‖^2)+2*(c^2*‖w‖^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (scalar_centered_norm_sq_le d hd v p) (by norm_num))
        (mul_le_mul_of_nonneg_left hw (by norm_num))) hd
    _ = _ := by ring

theorem middle_image_point_bound (r : ℕ) (hr : r ≤ s)
    (x y b : Fin s) (a : Hil (InjDb s)) (ha : Harmonic r a) (J : InjDb s) :
    ‖imageMap s r b (middle x y a) J‖^2 ≤
      4*((s-r+1 : ℕ) : ℝ)⁻¹*(if b=y then extensionMass x y a J else 0)+
        4*((s-r+1 : ℕ) : ℝ)⁻¹^3*extensionMass x y a J+
        2*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2*extensionMass x b a J := by
  have hn : 0 ≤
      4*((s-r+1 : ℕ) : ℝ)⁻¹*(if b=y then extensionMass x y a J else 0)+
        4*((s-r+1 : ℕ) : ℝ)⁻¹^3*extensionMass x y a J+
        2*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2*extensionMass x b a J := by
    unfold extensionMass
    positivity
  by_cases hb : J.symm b=none
  · by_cases hJ : J.size+1=r
    · cases hx : J x with
      | none =>
        rw [middle_image_unset r x y b a ha J hJ hx hb]
        by_cases hy : J.symm y=none
        · rw [if_pos hy]
          have hsize : s-J.size=s-r+1 := by omega
          have hq : ‖coefficient J‖^2=((s-r+1 : ℕ) : ℝ)⁻¹ := by
            rw [coefficient_norm_sq,hsize]
          have h := middle_scalar_norm_sq_le (coefficient J)
            ((s-r+1 : ℕ) : ℝ)⁻¹ ((s-r : ℕ) : ℝ)⁻¹ (by positivity) (by positivity) hq
            (a (J.addPair x y)) (a (J.addPair x b)) (b=y)
          simpa only [hsize,Complex.ofReal_inv,Complex.ofReal_natCast,one_div,
            extensionMass,hx,hy,hb,and_self,if_true] using h
        · rw [if_neg hy,norm_zero,zero_pow (by decide : 2≠0)]
          exact hn
      | some z =>
        have hbz : b≠z := by
          intro h
          subst b
          have hh := (J.inv x z).mpr hx
          change J.symm z=some x at hh
          rw [hb] at hh
          cases hh
        have hsize : (eraseAt J x).size+2=r := by
          have hh := eraseAt_size J x z hx
          omega
        have hz := middle_image_added r x y z b a ha (eraseAt J x) hsize
          (eraseAt_self J x) (eraseAt_unused J x z hx) (eraseAt_unused_of_unused J x b hb) hbz
        rw [eraseAt_add J x z hx] at hz
        rw [hz,norm_zero,zero_pow (by decide : 2≠0)]
        exact hn
    · rw [imageMap_apply,if_neg (fun h => hJ h.1),norm_zero,zero_pow (by decide : 2≠0)]
      exact hn
  · rw [imageMap_apply,if_neg (fun h => hb h.2),norm_zero,zero_pow (by decide : 2≠0)]
    exact hn

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathMiddleImageComplete
section

set_option autoImplicit false

-- FiniteAffineRows
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma masked_sum_energy_le (w : ι → ℂ) (p : ι → Prop) [DecidablePred p] :
    ‖∑ i,if p i then w i else 0‖^2 ≤
      (Fintype.card ι : ℝ)*(∑ i,if p i then ‖w i‖^2 else 0) := by
  have h := masked_sum_norm_sq_le (fun i => if p i then w i else 0) (fun _ => True)
  have hn (i : ι) : ‖if p i then w i else 0‖^2=(if p i then ‖w i‖^2 else 0) := by
    by_cases hp : p i <;> simp [hp]
  simpa only [if_true,hn] using h

lemma scalar_centered_row_norm_sq_le (d : ℝ) (hd : 0 ≤ d) (v : ι → ℂ)
    (p : ι → Prop) [DecidablePred p] (z : ι) :
    ‖∑ i,if p i then v i*((if z=i then 1 else 0)-(d : ℂ)) else 0‖^2 ≤
      2*‖v z‖^2+2*(Fintype.card ι : ℝ)*d^2*(∑ i,if p i then ‖v i‖^2 else 0) := by
  have he : (∑ i,if p i then v i*((if z=i then 1 else 0)-(d : ℂ)) else 0)=
      (if p z then v z else 0)-(d : ℂ)*(∑ i,if p i then v i else 0) := by
    calc
      _ = ∑ i,((if z=i then (if p i then v i else 0) else 0)-
          (d : ℂ)*(if p i then v i else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hp : p i <;> by_cases hz : z=i <;> simp [hp,hz] <;> ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.mul_sum]
  have hn : ‖(d : ℂ)‖=d := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd]
  have hz : ‖if p z then v z else 0‖^2 ≤ ‖v z‖^2 := by by_cases hp : p z <;> simp [hp]
  have h := complex_sub_norm_sq_le (if p z then v z else 0) ((d : ℂ)*(∑ i,if p i then v i else 0))
  rw [he]
  calc
    _ ≤ 2*‖if p z then v z else 0‖^2+2*d^2*‖∑ i,if p i then v i else 0‖^2 := by
      simpa only [norm_mul,mul_pow,hn,mul_assoc] using h
    _ ≤ 2*‖v z‖^2+2*d^2*((Fintype.card ι : ℝ)*(∑ i,if p i then ‖v i‖^2 else 0)) :=
      add_le_add (mul_le_mul_of_nonneg_left hz (by norm_num))
        (mul_le_mul_of_nonneg_left (masked_sum_energy_le v p) (by positivity))
    _ = _ := by ring

lemma middle_scalar_row_norm_sq_le (q : ℂ) (d c : ℝ) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hq : ‖q‖^2=d) (v w : ι → ℂ) (p : ι → Prop) [DecidablePred p] (z : ι) :
    ‖∑ i,if p i then q*(v i*((if z=i then 1 else 0)-(d : ℂ))-
      (if z≠i then (c : ℂ)*w i else 0)) else 0‖^2 ≤
      4*d*‖v z‖^2+4*(Fintype.card ι : ℝ)*d^3*(∑ i,if p i then ‖v i‖^2 else 0)+
        2*(Fintype.card ι : ℝ)*d*c^2*(∑ i,if p i then ‖w i‖^2 else 0) := by
  have he : (∑ i,if p i then q*(v i*((if z=i then 1 else 0)-(d : ℂ))-
      (if z≠i then (c : ℂ)*w i else 0)) else 0)=
      q*((∑ i,if p i then v i*((if z=i then 1 else 0)-(d : ℂ)) else 0)-
        (c : ℂ)*(∑ i,if p i ∧ z≠i then w i else 0)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p i <;> by_cases hz : z=i <;> simp [hp,hz] <;> ring
  have hw : ‖∑ i,if p i ∧ z≠i then w i else 0‖^2 ≤
      (Fintype.card ι : ℝ)*(∑ i,if p i then ‖w i‖^2 else 0) := by
    calc
      _ ≤ (Fintype.card ι : ℝ)*(∑ i,if p i ∧ z≠i then ‖w i‖^2 else 0) :=
        masked_sum_energy_le w (fun i => p i ∧ z≠i)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by
        by_cases hp : p i <;> by_cases hz : z=i <;> simp [hp,hz]) (Nat.cast_nonneg _)
  have hn : ‖(c : ℂ)‖=c := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  rw [he,norm_mul,mul_pow,hq]
  calc
    _ ≤ d*(2*‖∑ i,if p i then v i*((if z=i then 1 else 0)-(d : ℂ)) else 0‖^2+
        2*‖(c : ℂ)*(∑ i,if p i ∧ z≠i then w i else 0)‖^2) :=
      mul_le_mul_of_nonneg_left (complex_sub_norm_sq_le _ _) hd
    _ ≤ d*(2*(2*‖v z‖^2+2*(Fintype.card ι : ℝ)*d^2*(∑ i,if p i then ‖v i‖^2 else 0))+
        2*c^2*((Fintype.card ι : ℝ)*(∑ i,if p i then ‖w i‖^2 else 0))) := by
      simp only [norm_mul,mul_pow,hn]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (scalar_centered_row_norm_sq_le d hd v p z) (by norm_num))
        (by nlinarith [mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ c^2)])) hd
    _ = _ := by ring

end
end WeldedPath.CompressedAssertions


end

-- WeldedPathMiddleImageColumn
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem middle_image_energy_le (r : ℕ) (hr : r ≤ s) (x : Fin s)
    (a : Hil (InjDb s)) (ha : Harmonic r a) :
    (∑ y : Fin s,∑ b : Fin s,‖imageMap s r b (middle x y a)‖^2) ≤
      (4*((s-r+1 : ℕ) : ℝ)⁻¹+4*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹^3+
        2*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2)*‖a‖^2 := by
  let d : ℝ := ((s-r+1 : ℕ) : ℝ)⁻¹
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  let E : ℝ := ∑ p : Fin s × InjDb s,extensionMass x p.1 a p.2
  have hE : E ≤ ‖a‖^2 := extensionMass_sum_le x a
  have hy (y : Fin s) :
      (∑ b : Fin s,‖imageMap s r b (middle x y a)‖^2) ≤
        (4*d+4*(s : ℝ)*d^3)*(∑ J : InjDb s,extensionMass x y a J)+2*d*c^2*E := by
    simp only [EuclideanSpace.norm_sq_eq]
    have hpoint (b : Fin s) :
        (∑ J : InjDb s,‖imageMap s r b (middle x y a) J‖^2) ≤
          ∑ J : InjDb s,(4*d*(if b=y then extensionMass x y a J else 0)+
            4*d^3*extensionMass x y a J+2*d*c^2*extensionMass x b a J) :=
      Finset.sum_le_sum fun J _ => middle_image_point_bound r hr x y b a ha J
    calc
      _ ≤ ∑ b : Fin s,∑ J : InjDb s,
          (4*d*(if b=y then extensionMass x y a J else 0)+
            4*d^3*extensionMass x y a J+2*d*c^2*extensionMass x b a J) :=
        Finset.sum_le_sum fun b _ => hpoint b
      _ = _ := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        rw [Finset.sum_comm (f := fun b J => if b=y then extensionMass x y a J else 0)]
        simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const,
          Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,E,Fintype.sum_prod_type]
        ring
  calc
    _ ≤ ∑ y : Fin s,((4*d+4*(s : ℝ)*d^3)*(∑ J : InjDb s,extensionMass x y a J)+2*d*c^2*E) :=
      Finset.sum_le_sum fun y _ => hy y
    _ = (4*d+4*(s : ℝ)*d^3+2*(s : ℝ)*d*c^2)*E := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,E,Fintype.sum_prod_type]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by dsimp [d,c]; positivity)

end
end WeldedPath.CompressedAssertions


end

-- WeldedPathMiddleImageRow
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem middle_image_row_point (r : ℕ) (hr : r ≤ s)
    (x b : Fin s) (a : Fin s → Hil (InjDb s)) (ha : ∀ y,Harmonic r (a y)) (J : InjDb s) :
    ‖∑ y : Fin s,imageMap s r b (middle x y (a y)) J‖^2 ≤
      4*((s-r+1 : ℕ) : ℝ)⁻¹*extensionMass x b (a b) J+
        4*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹^3*(∑ y : Fin s,extensionMass x y (a y) J)+
        2*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2*
          (∑ y : Fin s,extensionMass x b (a y) J) := by
  have hn : 0 ≤
      4*((s-r+1 : ℕ) : ℝ)⁻¹*extensionMass x b (a b) J+
        4*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹^3*(∑ y : Fin s,extensionMass x y (a y) J)+
        2*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2*
          (∑ y : Fin s,extensionMass x b (a y) J) := by
    unfold extensionMass
    positivity
  by_cases hb : J.symm b=none
  · by_cases hJ : J.size+1=r
    · cases hx : J x with
      | none =>
        have he (y : Fin s) := middle_image_unset r x y b (a y) (ha y) J hJ hx hb
        rw [Finset.sum_congr rfl (fun y _ => he y)]
        have hsize : s-J.size=s-r+1 := by omega
        have hq : ‖coefficient J‖^2=((s-r+1 : ℕ) : ℝ)⁻¹ := by
          rw [coefficient_norm_sq,hsize]
        have h := middle_scalar_row_norm_sq_le (coefficient J)
          ((s-r+1 : ℕ) : ℝ)⁻¹ ((s-r : ℕ) : ℝ)⁻¹ (by positivity) (by positivity) hq
          (fun y => a y (J.addPair x y)) (fun y => a y (J.addPair x b))
          (fun y => J.symm y=none) b
        have hu : (∑ y : Fin s,if J.symm y=none then ‖a y (J.addPair x b)‖^2 else 0) ≤
            ∑ y : Fin s,‖a y (J.addPair x b)‖^2 := Finset.sum_le_sum fun y _ => by
          by_cases hy : J.symm y=none <;> simp [hy]
        have hpos : 0 ≤ 2*(Fintype.card (Fin s) : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*
            ((s-r : ℕ) : ℝ)⁻¹^2 := by positivity
        have hh := h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hu hpos))
        simpa only [hsize,Complex.ofReal_inv,Complex.ofReal_natCast,one_div,
          extensionMass,hx,hb,true_and,if_true,Fintype.card_fin] using hh
      | some z =>
        have hbz : b≠z := by
          intro h
          subst b
          have hh := (J.inv x z).mpr hx
          change J.symm z=some x at hh
          rw [hb] at hh
          cases hh
        have hsize : (eraseAt J x).size+2=r := by
          have hh := eraseAt_size J x z hx
          omega
        have hz (y : Fin s) := middle_image_added r x y z b (a y) (ha y) (eraseAt J x) hsize
          (eraseAt_self J x) (eraseAt_unused J x z hx) (eraseAt_unused_of_unused J x b hb) hbz
        simp only [eraseAt_add J x z hx] at hz
        simp only [hz,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]
        exact hn
    · have hz (y : Fin s) : imageMap s r b (middle x y (a y)) J=0 := by
        rw [imageMap_apply,if_neg (fun h => hJ h.1)]
      simp only [hz,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]
      exact hn
  · have hz (y : Fin s) : imageMap s r b (middle x y (a y)) J=0 := by
      rw [imageMap_apply,if_neg (fun h => hb h.2)]
    simp only [hz,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]
    exact hn

theorem middle_image_row_energy_le (r : ℕ) (hr : r ≤ s) (x : Fin s)
    (a : Fin s → Hil (InjDb s)) (ha : ∀ y,Harmonic r (a y)) :
    (∑ b : Fin s,‖∑ y : Fin s,imageMap s r b (middle x y (a y))‖^2) ≤
      (4*((s-r+1 : ℕ) : ℝ)⁻¹+4*(s : ℝ)^2*((s-r+1 : ℕ) : ℝ)⁻¹^3+
        2*(s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2)*(∑ y : Fin s,‖a y‖^2) := by
  let d : ℝ := ((s-r+1 : ℕ) : ℝ)⁻¹
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  have hD : (∑ p : Fin s × InjDb s,extensionMass x p.1 (a p.1) p.2) ≤
      ∑ y : Fin s,‖a y‖^2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun y _ => extensionMass_fixed_sum_le x y (a y)
  have hV : (∑ p : Fin s × InjDb s,∑ y : Fin s,extensionMass x y (a y) p.2) ≤
      (s : ℝ)*(∑ y : Fin s,‖a y‖^2) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun y _ => extensionMass_fixed_sum_le x y (a y)
  have hW : (∑ p : Fin s × InjDb s,∑ y : Fin s,extensionMass x p.1 (a y) p.2) ≤
      ∑ y : Fin s,‖a y‖^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun y _ => extensionMass_sum_le x (a y)
  conv_lhs =>
    arg 2
    ext b
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
  rw [← Fintype.sum_prod_type (fun p : Fin s × InjDb s =>
    ‖∑ y : Fin s,imageMap s r p.1 (middle x y (a y)) p.2‖^2)]
  change _ ≤ (4*d+4*(s : ℝ)^2*d^3+2*(s : ℝ)*d*c^2)*(∑ y : Fin s,‖a y‖^2)
  calc
    _ ≤ ∑ p : Fin s × InjDb s,(4*d*extensionMass x p.1 (a p.1) p.2+
        4*(s : ℝ)*d^3*(∑ y : Fin s,extensionMass x y (a y) p.2)+
        2*(s : ℝ)*d*c^2*(∑ y : Fin s,extensionMass x p.1 (a y) p.2)) :=
      Finset.sum_le_sum fun p _ => middle_image_row_point r hr x p.1 a ha p.2
    _ = 4*d*(∑ p : Fin s × InjDb s,extensionMass x p.1 (a p.1) p.2)+
        4*(s : ℝ)*d^3*(∑ p : Fin s × InjDb s,∑ y : Fin s,extensionMass x y (a y) p.2)+
        2*(s : ℝ)*d*c^2*(∑ p : Fin s × InjDb s,∑ y : Fin s,extensionMass x p.1 (a y) p.2) := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    _ ≤ 4*d*(∑ y : Fin s,‖a y‖^2)+
        4*(s : ℝ)*d^3*((s : ℝ)*(∑ y : Fin s,‖a y‖^2))+
        2*(s : ℝ)*d*c^2*(∑ y : Fin s,‖a y‖^2) := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hD (by dsimp [d]; positivity))
        (mul_le_mul_of_nonneg_left hV (by dsimp [d]; positivity)))
      (mul_le_mul_of_nonneg_left hW (by dsimp [d,c]; positivity))
    _ = _ := by ring

end
end WeldedPath.CompressedAssertions


end

end

-- Solutions.WeldedPathMiddleDomainComplete
section

set_option autoImplicit false

-- WeldedPathMiddleMoveCounting
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

def middleMove (x y u z : Fin s) (J : InjDb s) : InjDb s :=
  ((eraseAt J x).addPair x y).addPair u z

lemma middleMove_fresh (x y u z : Fin s) (J : InjDb s)
    (hx : J x=some z) (hu : J u=none) (hy : (eraseAt J x).symm y=none) (hyz : y≠z) :
    (eraseAt J x).addPair x y u=none ∧ ((eraseAt J x).addPair x y).symm z=none := by
  have hux : u≠x := by intro h; subst u; rw [hx] at hu; cases hu
  constructor
  · rw [added_apply _ x y u (eraseAt_self J x) hy,if_neg hux,eraseAt_unset J x u hu]
  · rw [added_symm_apply _ x y z (eraseAt_self J x) hy,if_neg (Ne.symm hyz),
      eraseAt_unused J x z hx]

lemma middleMove_self (x y u z : Fin s) (J : InjDb s)
    (hx : J x=some z) (hu : J u=none) (hy : (eraseAt J x).symm y=none) (hyz : y≠z) :
    middleMove x y u z J u=some z := by
  have hf := middleMove_fresh x y u z J hx hu hy hyz
  exact addPair_apply_self _ u z hf.1 hf.2

lemma middleMove_recover (x y u z : Fin s) (J : InjDb s)
    (hx : J x=some z) (hu : J u=none) (hy : (eraseAt J x).symm y=none) (hyz : y≠z) :
    (eraseAt (eraseAt (middleMove x y u z J) u) x).addPair x z=J := by
  have hf := middleMove_fresh x y u z J hx hu hy hyz
  rw [middleMove,eraseAt_addPair_unset _ u z hf.1 hf.2,
    eraseAt_addPair_unset _ x y (eraseAt_self J x) hy,eraseAt_add J x z hx]

theorem middleMove_injective_on (x y u : Fin s) :
    Set.InjOn (fun p : Fin s × InjDb s => middleMove x y u p.1 p.2)
      {p | p.2 x=some p.1 ∧ p.2 u=none ∧ (eraseAt p.2 x).symm y=none ∧ y≠p.1} := by
  rintro ⟨z,I⟩ ⟨hx,hu,hy,hyz⟩ ⟨w,J⟩ ⟨hx',hu',hy',hyw⟩ he
  change middleMove x y u z I=middleMove x y u w J at he
  have hzw : z=w := by
    have h := congrArg (fun K : InjDb s => K u) he
    rw [middleMove_self x y u z I hx hu hy hyz,middleMove_self x y u w J hx' hu' hy' hyw] at h
    exact Option.some.inj h
  have hIJ : I=J := by
    subst w
    have h := congrArg (fun K : InjDb s => (eraseAt (eraseAt K u) x).addPair x z) he
    rwa [middleMove_recover x y u z I hx hu hy hyz,middleMove_recover x y u z J hx' hu' hy' hyw] at h
  exact Prod.ext hzw hIJ

def middleMoveMass (x y u z : Fin s) (a : Hil (InjDb s)) (J : InjDb s) : ℝ :=
  if J x=some z ∧ J u=none ∧ (eraseAt J x).symm y=none ∧ y≠z then
    ‖a (middleMove x y u z J)‖^2 else 0

theorem middleMoveMass_fixed_sum_le (x y u : Fin s) (a : Hil (InjDb s)) :
    (∑ p : Fin s × InjDb s,middleMoveMass x y u p.1 a p.2) ≤ ‖a‖^2 := by
  let S := Finset.univ.filter (fun p : Fin s × InjDb s =>
    p.2 x=some p.1 ∧ p.2 u=none ∧ (eraseAt p.2 x).symm y=none ∧ y≠p.1)
  let f := fun p : Fin s × InjDb s => middleMove x y u p.1 p.2
  have hinj : Set.InjOn f S := by
    intro p hp q hq he
    exact middleMove_injective_on x y u (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he
  change (∑ p : Fin s × InjDb s,
    if p.2 x=some p.1 ∧ p.2 u=none ∧ (eraseAt p.2 x).symm y=none ∧ y≠p.1 then
      ‖a (f p)‖^2 else 0) ≤ _
  rw [← Finset.sum_filter]
  change (∑ p ∈ S,‖a (f p)‖^2) ≤ _
  rw [← Finset.sum_image (f := fun I : InjDb s => ‖a I‖^2) hinj,EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun I _ _ => sq_nonneg ‖a I‖)

theorem extension_image_injective_on (y : Fin s) :
    Set.InjOn (fun p : Fin s × InjDb s => p.2.addPair p.1 y)
      {p | p.2 p.1=none ∧ p.2.symm y=none} := by
  rintro ⟨u,I⟩ ⟨hu,hy⟩ ⟨v,J⟩ ⟨hv,hy'⟩ he
  change I.addPair u y=J.addPair v y at he
  have huv : u=v := by
    have h := congrArg (fun K : InjDb s => K.symm y) he
    rw [added_symm_apply I u y y hu hy,added_symm_apply J v y y hv hy',if_pos rfl,if_pos rfl] at h
    exact Option.some.inj h
  have hIJ : I=J := by
    subst v
    have h := congrArg (fun K : InjDb s => eraseAt K u) he
    rwa [eraseAt_addPair_unset I u y hu hy,eraseAt_addPair_unset J u y hv hy'] at h
  exact Prod.ext huv hIJ

theorem extensionMass_image_sum_le (y : Fin s) (a : Hil (InjDb s)) :
    (∑ p : Fin s × InjDb s,extensionMass p.1 y a p.2) ≤ ‖a‖^2 := by
  let S := Finset.univ.filter (fun p : Fin s × InjDb s => p.2 p.1=none ∧ p.2.symm y=none)
  let f := fun p : Fin s × InjDb s => p.2.addPair p.1 y
  have hinj : Set.InjOn f S := by
    intro p hp q hq he
    exact extension_image_injective_on y (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he
  change (∑ p : Fin s × InjDb s,
    if p.2 p.1=none ∧ p.2.symm y=none then ‖a (f p)‖^2 else 0) ≤ _
  rw [← Finset.sum_filter]
  change (∑ p ∈ S,‖a (f p)‖^2) ≤ _
  rw [← Finset.sum_image (f := fun I : InjDb s => ‖a I‖^2) hinj,EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun I _ _ => sq_nonneg ‖a I‖)

end
end WeldedPath.CompressedAssertions


end

-- WeldedPathMiddleDomainEstimate
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma inverse_nat_complex_norm_sq (m : ℕ) : ‖(1/(m : ℂ))‖^2=(m : ℝ)⁻¹^2 := by
  simp only [one_div,norm_inv,Complex.norm_natCast]

theorem middle_domain_unset_norm_sq (r : ℕ) (hr : r ≤ s) (x y u : Fin s)
    (a : Hil (InjDb s)) (ha : Harmonic r a) (J : InjDb s)
    (hJ : J.size+1=r) (hx : J x=none) (hu : J u=none) (hux : u≠x) :
    ‖domainMap s r u (middle x y a) J‖^2=
      ((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2*extensionMass u y a J := by
  have hs : s-J.size=s-r+1 := by omega
  rw [middle_domain_unset_other r x y u a ha J hJ hx hu hux]
  by_cases hy : J.symm y=none
  · simp only [if_pos hy,norm_mul,norm_neg,mul_pow,coefficient_norm_sq,
      inverse_nat_complex_norm_sq,hs,extensionMass,hu,hy,and_self,if_true]
  · simp [hy,extensionMass]

theorem middle_domain_known_norm_sq (r : ℕ) (hr : r ≤ s) (x y u z : Fin s)
    (a : Hil (InjDb s)) (ha : Harmonic r a) (J : InjDb s)
    (hJ : J.size+1=r) (hx : J x=some z) (hu : J u=none) :
    ‖domainMap s r u (middle x y a) J‖^2=
      ((s-r+1 : ℕ) : ℝ)⁻¹^3*middleMoveMass x y u z a J := by
  have hux : u≠x := by intro h; subst u; rw [hx] at hu; cases hu
  have he := eraseAt_size J x z hx
  have hs : s-J.size=s-r+1 := by omega
  have hh := middle_domain_added r x y z u a ha (eraseAt J x) (by omega)
    (eraseAt_self J x) (eraseAt_unused J x z hx) (eraseAt_unset J x u hu) hux
  rw [eraseAt_add J x z hx,he] at hh
  rw [hh]
  by_cases hy : (eraseAt J x).symm y=none ∧ y≠z
  · rw [if_pos hy,middleMoveMass,if_pos (show J x=some z ∧ J u=none ∧
        (eraseAt J x).symm y=none ∧ y≠z from ⟨hx,hu,hy.1,hy.2⟩)]
    simp only [norm_mul,mul_pow,coefficient_norm_sq,inverse_nat_complex_norm_sq,hs,middleMove]
    ring
  · rw [if_neg hy,middleMoveMass,if_neg (fun h => hy ⟨h.2.2.1,h.2.2.2⟩)]
    simp

theorem middle_domain_point_bound (r : ℕ) (hr : r ≤ s) (x y u : Fin s)
    (a : Hil (InjDb s)) (ha : Harmonic r a) (J : InjDb s) :
    ‖domainMap s r u (middle x y a) J‖^2 ≤
      ((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2*extensionMass u y a J+
        ((s-r+1 : ℕ) : ℝ)⁻¹^3*(∑ z : Fin s,middleMoveMass x y u z a J) := by
  have hn : 0 ≤ ((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2*extensionMass u y a J+
      ((s-r+1 : ℕ) : ℝ)⁻¹^3*(∑ z : Fin s,middleMoveMass x y u z a J) := by
    unfold extensionMass middleMoveMass
    positivity
  by_cases hu : J u=none
  · by_cases hJ : J.size+1=r
    · cases hx : J x with
      | none =>
        by_cases hux : u=x
        · subst u
          rw [middle_domain_self]
          simpa only [PiLp.zero_apply,norm_zero,zero_pow (by decide : 2≠0)] using hn
        · rw [middle_domain_unset_norm_sq r hr x y u a ha J hJ hx hu hux]
          have hz : 0 ≤ ((s-r+1 : ℕ) : ℝ)⁻¹^3*(∑ z : Fin s,middleMoveMass x y u z a J) := by
            unfold middleMoveMass
            positivity
          exact le_add_of_nonneg_right hz
      | some z =>
        rw [middle_domain_known_norm_sq r hr x y u z a ha J hJ hx hu]
        have hsum : (∑ z' : Fin s,middleMoveMass x y u z' a J)=middleMoveMass x y u z a J := by
          simp only [middleMoveMass,hx,Option.some.injEq,ite_and,Finset.sum_ite_eq,
            Finset.mem_univ,if_true]
        rw [hsum]
        exact le_add_of_nonneg_left (by unfold extensionMass; positivity)
    · rw [domainMap_apply,if_neg (fun h => hJ h.1),norm_zero,zero_pow (by decide : 2≠0)]
      exact hn
  · rw [domainMap_apply,if_neg (fun h => hu h.2),norm_zero,zero_pow (by decide : 2≠0)]
    exact hn

end
end WeldedPath.CompressedAssertions


end

-- WeldedPathMiddleDomainEnergy
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem middle_domain_fixed_energy_le (r : ℕ) (hr : r ≤ s) (x y : Fin s)
    (a : Hil (InjDb s)) (ha : Harmonic r a) :
    (∑ u : Fin s,‖domainMap s r u (middle x y a)‖^2) ≤
      (((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2+
        (s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹^3)*‖a‖^2 := by
  let d : ℝ := ((s-r+1 : ℕ) : ℝ)⁻¹
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  have hM : (∑ p : Fin s × InjDb s,∑ z : Fin s,middleMoveMass x y p.1 z a p.2) ≤
      (s : ℝ)*‖a‖^2 := by
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ _u : Fin s,‖a‖^2 := Finset.sum_le_sum fun u _ => by
        rw [Finset.sum_comm]
        simpa only [Fintype.sum_prod_type] using middleMoveMass_fixed_sum_le x y u a
      _ = _ := by simp
  conv_lhs =>
    arg 2
    ext u
    rw [EuclideanSpace.norm_sq_eq]
  rw [← Fintype.sum_prod_type (fun p : Fin s × InjDb s =>
    ‖domainMap s r p.1 (middle x y a) p.2‖^2)]
  change _ ≤ (d*c^2+(s : ℝ)*d^3)*‖a‖^2
  calc
    _ ≤ ∑ p : Fin s × InjDb s,(d*c^2*extensionMass p.1 y a p.2+
        d^3*(∑ z : Fin s,middleMoveMass x y p.1 z a p.2)) :=
      Finset.sum_le_sum fun p _ => middle_domain_point_bound r hr x y p.1 a ha p.2
    _ = d*c^2*(∑ p : Fin s × InjDb s,extensionMass p.1 y a p.2)+
        d^3*(∑ p : Fin s × InjDb s,∑ z : Fin s,middleMoveMass x y p.1 z a p.2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ d*c^2*‖a‖^2+d^3*((s : ℝ)*‖a‖^2) := add_le_add
      (mul_le_mul_of_nonneg_left (extensionMass_image_sum_le y a) (by dsimp [c,d]; positivity))
      (mul_le_mul_of_nonneg_left hM (by dsimp [d]; positivity))
    _ = _ := by ring

theorem middle_domain_energy_le (r : ℕ) (hr : r ≤ s) (x : Fin s)
    (a : Hil (InjDb s)) (ha : Harmonic r a) :
    (∑ y : Fin s,∑ u : Fin s,‖domainMap s r u (middle x y a)‖^2) ≤
      ((s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2+
        (s : ℝ)^2*((s-r+1 : ℕ) : ℝ)⁻¹^3)*‖a‖^2 := by
  calc
    _ ≤ ∑ _y : Fin s,((((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2+
        (s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹^3)*‖a‖^2) :=
      Finset.sum_le_sum fun y _ => middle_domain_fixed_energy_le r hr x y a ha
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem middle_domain_row_energy_le (r : ℕ) (hr : r ≤ s) (x : Fin s)
    (a : Fin s → Hil (InjDb s)) (ha : ∀ y,Harmonic r (a y)) :
    (∑ u : Fin s,‖∑ y : Fin s,domainMap s r u (middle x y (a y))‖^2) ≤
      ((s : ℝ)*((s-r+1 : ℕ) : ℝ)⁻¹*((s-r : ℕ) : ℝ)⁻¹^2+
        (s : ℝ)^2*((s-r+1 : ℕ) : ℝ)⁻¹^3)*(∑ y : Fin s,‖a y‖^2) := by
  let d : ℝ := ((s-r+1 : ℕ) : ℝ)⁻¹
  let c : ℝ := ((s-r : ℕ) : ℝ)⁻¹
  have h (u : Fin s) : ‖∑ y : Fin s,domainMap s r u (middle x y (a y))‖^2 ≤
      (s : ℝ)*(∑ y : Fin s,‖domainMap s r u (middle x y (a y))‖^2) := by
    calc
      _ ≤ (∑ y : Fin s,‖domainMap s r u (middle x y (a y))‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa only [Finset.card_univ,Fintype.card_fin] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun y : Fin s => ‖domainMap s r u (middle x y (a y))‖))
  calc
    _ ≤ ∑ u : Fin s,(s : ℝ)*(∑ y : Fin s,‖domainMap s r u (middle x y (a y))‖^2) :=
      Finset.sum_le_sum fun u _ => h u
    _ = (s : ℝ)*(∑ y : Fin s,∑ u : Fin s,‖domainMap s r u (middle x y (a y))‖^2) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (s : ℝ)*(∑ y : Fin s,(d*c^2+(s : ℝ)*d^3)*‖a y‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
        middle_domain_fixed_energy_le r hr x y (a y) (ha y)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; dsimp [d,c]; ring

end
end WeldedPath.CompressedAssertions


end

end

-- Solutions.WeldedPathMiddleLeakage
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

theorem middle_leakage_column_bound (r : ℕ) (hr : 3*r+2 ≤ s)
    (x : Fin s) (a : Hil (InjDb s)) (hsupport : LevelSupported r a) (ha : Harmonic r a) :
    (∑ y : Fin s,‖middle x y a-
      ((ContinuousLinearMap.adjoint (Gam s r)).range).starProjection (middle x y a)‖^2) ≤
      60*((s-r : ℕ) : ℝ)⁻¹*‖a‖^2 := by
  have hc := middle_constants r (by omega) (by omega : 0 < s)
  have hd := (middle_domain_energy_le r (by omega) x a ha).trans
    (mul_le_mul_of_nonneg_right hc.2.2 (sq_nonneg ‖a‖))
  have hi := (middle_image_energy_le r (by omega) x a ha).trans
    (mul_le_mul_of_nonneg_right hc.1 (sq_nonneg ‖a‖))
  have h (y : Fin s) := incidence_distance_bound (by omega : 3*r ≤ s+1)
    (middle x y a) (middle_levelSupported r x y a hsupport)
  calc
    _ ≤ ∑ y : Fin s,2*∑ z : Fin s,
        (‖domainMap s r z (middle x y a)‖^2+‖imageMap s r z (middle x y a)‖^2) :=
      Finset.sum_le_sum fun y _ => h y
    _ = 2*((∑ y : Fin s,∑ z : Fin s,‖domainMap s r z (middle x y a)‖^2)+
        (∑ y : Fin s,∑ z : Fin s,‖imageMap s r z (middle x y a)‖^2)) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

theorem middle_leakage_row_bound (r : ℕ) (hr : 3*r+2 ≤ s)
    (x : Fin s) (a : Fin s → Hil (InjDb s))
    (hsupport : ∀ y,LevelSupported r (a y)) (ha : ∀ y,Harmonic r (a y)) :
    ‖(∑ y : Fin s,middle x y (a y))-
      ((ContinuousLinearMap.adjoint (Gam s r)).range).starProjection
        (∑ y : Fin s,middle x y (a y))‖^2 ≤
      60*((s-r : ℕ) : ℝ)⁻¹*(∑ y : Fin s,‖a y‖^2) := by
  have hc := middle_constants r (by omega) (by omega : 0 < s)
  have hd := (middle_domain_row_energy_le r (by omega) x a ha).trans
    (mul_le_mul_of_nonneg_right hc.2.2 (by positivity))
  have hi := (middle_image_row_energy_le r (by omega) x a ha).trans
    (mul_le_mul_of_nonneg_right hc.2.1 (by positivity))
  have hlevel : LevelSupported r (∑ y : Fin s,middle x y (a y)) := by
    intro J hJ
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
    exact Finset.sum_eq_zero fun y _ => middle_levelSupported r x y (a y) (hsupport y) J hJ
  have h := incidence_distance_bound (by omega : 3*r ≤ s+1)
    (∑ y : Fin s,middle x y (a y)) hlevel
  simp only [map_sum,Finset.sum_add_distrib] at h
  simp only [map_sum]
  linarith

end
end WeldedPath.CompressedAssertions


end

-- Solutions.WeldedPathAssertionProjectionLeakage
section

namespace WeldedPath.CompressedAssertions

noncomputable section
open Classical InjDb HilbertSupport CompressedPrimitive CompletionLevels Incidence
open scoped BigOperators

variable {s : ℕ}

lemma recordLevel_of_levelSupported (r : ℕ) (a : Hil (InjDb s)) (ha : LevelSupported r a) :
    recordLevel s r a=a := by
  ext I
  rw [recordLevel,diagProj_apply]
  by_cases hI : I.size=r
  · rw [if_pos hI]
  · rw [if_neg hI,ha I hI]

lemma recordLevel_zero_of_levelSupported (j r : ℕ) (hjr : j≠r)
    (a : Hil (InjDb s)) (ha : LevelSupported r a) : recordLevel s j a=0 := by
  ext I
  rw [recordLevel,diagProj_apply]
  by_cases hI : I.size=j
  · rw [if_pos hI,ha I (by omega)]
    rfl
  · rw [if_neg hI]
    rfl

lemma recordLevel_downward_zero (j r : ℕ) (hrj : r ≤ j) (x y : Fin s)
    (a : Hil (InjDb s)) (ha : LevelSupported r a) :
    recordLevel s j (downward x y a)=0 := by
  ext I
  rw [recordLevel,diagProj_apply]
  by_cases hI : I.size=j
  · rw [if_pos hI,downward_support r x y a ha I (by omega)]
    rfl
  · rw [if_neg hI]
    rfl

theorem assertion_upward_level (r : ℕ) (x y : Fin s) (a : Hil (InjDb s))
    (ha : a∈(ContinuousLinearMap.adjoint (Gam s r)).range) :
    recordLevel s (r+1) (assertion x y a)=upward x y a := by
  have hsupport : LevelSupported r a := by
    obtain ⟨v,rfl⟩ := ha
    exact Gam_adjoint_levelSupported r v
  rw [assertion_harmonic_split r x y a ha,map_add,map_add,
    recordLevel_of_levelSupported (r+1) _ (upward_levelSupported r x y a hsupport),
    recordLevel_zero_of_levelSupported (r+1) r (by omega) _ (middle_levelSupported r x y a hsupport),
    recordLevel_downward_zero (r+1) r (by omega) x y a hsupport,add_zero,add_zero]

theorem assertion_middle_level (r : ℕ) (x y : Fin s) (a : Hil (InjDb s))
    (ha : a∈(ContinuousLinearMap.adjoint (Gam s r)).range) :
    recordLevel s r (assertion x y a)=middle x y a := by
  have hsupport : LevelSupported r a := by
    obtain ⟨v,rfl⟩ := ha
    exact Gam_adjoint_levelSupported r v
  rw [assertion_harmonic_split r x y a ha,map_add,map_add,
    recordLevel_zero_of_levelSupported r (r+1) (by omega) _ (upward_levelSupported r x y a hsupport),
    recordLevel_of_levelSupported r _ (middle_levelSupported r x y a hsupport),
    recordLevel_downward_zero r r le_rfl x y a hsupport,zero_add,add_zero]

theorem assertion_projection_column_bound (r : ℕ) (hr : 3*r+2 ≤ s)
    (x : Fin s) (a : Hil (InjDb s)) (ha : a∈(ContinuousLinearMap.adjoint (Gam s r)).range) :
    (∑ y : Fin s,
      (‖recordLevel s (r+1) (assertion x y a)-
        ((ContinuousLinearMap.adjoint (Gam s (r+1))).range).starProjection
          (recordLevel s (r+1) (assertion x y a))‖^2+
        ‖recordLevel s r (assertion x y a)-
          ((ContinuousLinearMap.adjoint (Gam s r)).range).starProjection
            (recordLevel s r (assertion x y a))‖^2)) ≤
      204*((s-r : ℕ) : ℝ)⁻¹*‖a‖^2 := by
  simp only [assertion_upward_level r x _ a ha,assertion_middle_level r x _ a ha,
    Finset.sum_add_distrib]
  have hsupport : LevelSupported r a := by
    obtain ⟨v,hv⟩ := ha
    rw [← hv]
    exact Gam_adjoint_levelSupported r v
  have hharmonic : Harmonic r a := by
    obtain ⟨v,hv⟩ := ha
    rw [← hv]
    exact Gam_adjoint_harmonic r v
  have hu := upward_leakage_column_bound r hr x a hsupport hharmonic
  have hm := middle_leakage_column_bound r hr x a hsupport hharmonic
  linarith

theorem assertion_projection_row_bound (r : ℕ) (hr : 3*r+2 ≤ s)
    (x : Fin s) (a : Fin s → Hil (InjDb s))
    (ha : ∀ y,a y∈(ContinuousLinearMap.adjoint (Gam s r)).range) :
    ‖(∑ y : Fin s,recordLevel s (r+1) (assertion x y (a y)))-
      ((ContinuousLinearMap.adjoint (Gam s (r+1))).range).starProjection
        (∑ y : Fin s,recordLevel s (r+1) (assertion x y (a y)))‖^2+
      ‖(∑ y : Fin s,recordLevel s r (assertion x y (a y)))-
        ((ContinuousLinearMap.adjoint (Gam s r)).range).starProjection
          (∑ y : Fin s,recordLevel s r (assertion x y (a y)))‖^2 ≤
      204*((s-r : ℕ) : ℝ)⁻¹*(∑ y : Fin s,‖a y‖^2) := by
  simp only [assertion_upward_level r x _ _ (ha _),assertion_middle_level r x _ _ (ha _)]
  have hsupport (y : Fin s) : LevelSupported r (a y) := by
    obtain ⟨v,hv⟩ := ha y
    rw [← hv]
    exact Gam_adjoint_levelSupported r v
  have hharmonic (y : Fin s) : Harmonic r (a y) := by
    obtain ⟨v,hv⟩ := ha y
    rw [← hv]
    exact Gam_adjoint_harmonic r v
  have hu := upward_leakage_row_bound r hr x a hsupport hharmonic
  have hm := middle_leakage_row_bound r hr x a hsupport hharmonic
  linarith

end
end WeldedPath.CompressedAssertions


end

open Classical WeldedPath
open scoped BigOperators

theorem solution (s r : ℕ) (hsmall : 3*r+2 ≤ s) (x : Fin s) :
    let K := fun j : ℕ => (ContinuousLinearMap.adjoint (Gam s j)).range
    let L := fun j : ℕ => diagProj (fun I : InjDb s => I.size=j)
    let A := fun y : Fin s => (pC s x).comp
      ((diagProj (fun I : InjDb s => I x=some y)).comp (pC s x))
    (∀ a : Hil (InjDb s), a∈K r →
      (∑ y : Fin s,
        (‖L (r+1) (A y a)-(K (r+1)).starProjection (L (r+1) (A y a))‖^2+
          ‖L r (A y a)-(K r).starProjection (L r (A y a))‖^2)) ≤
        204*((s-r : ℕ) : ℝ)⁻¹*‖a‖^2) ∧
    (∀ a : Fin s → Hil (InjDb s), (∀ y,a y∈K r) →
      ‖(∑ y : Fin s,L (r+1) (A y (a y)))-
        (K (r+1)).starProjection (∑ y : Fin s,L (r+1) (A y (a y)))‖^2+
        ‖(∑ y : Fin s,L r (A y (a y)))-
          (K r).starProjection (∑ y : Fin s,L r (A y (a y)))‖^2 ≤
        204*((s-r : ℕ) : ℝ)⁻¹*(∑ y : Fin s,‖a y‖^2)) := by
  dsimp only
  constructor
  · intro a ha
    simpa only [Incidence.recordLevel,CompressedAssertions.assertion,CompressedAssertions.selector]
      using CompressedAssertions.assertion_projection_column_bound r hsmall x a ha
  · intro a ha
    simpa only [Incidence.recordLevel,CompressedAssertions.assertion,CompressedAssertions.selector]
      using CompressedAssertions.assertion_projection_row_bound r hsmall x a ha
