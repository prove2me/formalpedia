-- Prove2me | solution 1 for WeldedPath.exact_query_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T22:07:17.718425+00:00
-- url     : https://prove2.me/submissions/059b8e76-33ff-4717-b1b7-eaf40ef026df

import Definitions.Def_WeldedPath_Supplement_exactCpWT
import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Definitions.Def_WeldedPath_InjDb
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Definitions.Def_WeldedPath_exactCpO
import Definitions.Def_WeldedPath_opTensor
import Mathlib.Analysis.CStarAlgebra.Basic

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

-- Solutions.WeldedPathTensorOperators
section

namespace WeldedPath.TensorOperators

open Classical EncodedOracleUnitary HilbertSupport
open scoped BigOperators

variable {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq A] [DecidableEq X] [DecidableEq Y]

lemma slice_opTensor_one (T : Hil X →L[ℂ] Hil Y) (ψ : Hil (A × X)) (a : A) :
    slice (opTensor (1 : Hil A →L[ℂ] Hil A) T ψ) a = T (slice ψ a) := by
  ext y
  exact opTensor_one_apply T ψ a y

lemma opTensor_one_comp (S : Hil Y →L[ℂ] Hil Z) (T : Hil X →L[ℂ] Hil Y) :
    (opTensor (1 : Hil A →L[ℂ] Hil A) S).comp
      (opTensor (1 : Hil A →L[ℂ] Hil A) T) =
      opTensor (1 : Hil A →L[ℂ] Hil A) (S.comp T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext p
  rcases p with ⟨a, y⟩
  simp only [ContinuousLinearMap.comp_apply, opTensor_one_apply, slice_opTensor_one]

lemma inner_ketTensor_slice (a : A) (v : Hil X) (ψ : Hil (A × X)) :
    inner ℂ (ketTensor (ket a) v) ψ = inner ℂ v (slice ψ a) := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, ketTensor_apply, ket_apply, slice,
    apply_ite, mul_ite]

lemma adjoint_opTensor_one_apply (T : Hil X →L[ℂ] Hil Y)
    (ψ : Hil (A × Y)) (a : A) (x : X) :
    ContinuousLinearMap.adjoint (opTensor (1 : Hil A →L[ℂ] Hil A) T) ψ (a, x) =
      ContinuousLinearMap.adjoint T (slice ψ a) x := by
  rw [← inner_ket (a, x), ContinuousLinearMap.adjoint_inner_right, opTensor_ket]
  simp only [ContinuousLinearMap.one_apply]
  rw [inner_ketTensor_slice, ← ContinuousLinearMap.adjoint_inner_right, inner_ket]

lemma adjoint_opTensor_one (T : Hil X →L[ℂ] Hil Y) :
    ContinuousLinearMap.adjoint (opTensor (1 : Hil A →L[ℂ] Hil A) T) =
      opTensor (1 : Hil A →L[ℂ] Hil A) (ContinuousLinearMap.adjoint T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext p
  rcases p with ⟨a, x⟩
  rw [adjoint_opTensor_one_apply, opTensor_one_apply]

theorem opTensor_one_partial (V : Hil X →L[ℂ] Hil Y)
    (hV : (V.comp (ContinuousLinearMap.adjoint V)).comp V = V) :
    (((opTensor (1 : Hil A →L[ℂ] Hil A) V).comp
      (ContinuousLinearMap.adjoint (opTensor (1 : Hil A →L[ℂ] Hil A) V))).comp
        (opTensor (1 : Hil A →L[ℂ] Hil A) V)) =
        opTensor (1 : Hil A →L[ℂ] Hil A) V := by
  rw [adjoint_opTensor_one, opTensor_one_comp, opTensor_one_comp, hV]

end WeldedPath.TensorOperators

end

-- Solutions.WeldedPathPartialIsometryContraction
section

namespace WeldedPath.PartialIsometryContraction

open ContinuousLinearMap

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The exact-oracle block construction is contractive for every partial
isometry and every two contractive constituent maps. -/
theorem block_norm_le (V : Hil X →L[ℂ] Hil Y)
    (hV : (V.comp (adjoint V)).comp V = V)
    (O : Hil X →L[ℂ] Hil X) (C : Hil Y →L[ℂ] Hil Y)
    (hO : ∀ x, ‖O x‖ ≤ ‖x‖) (hC : ∀ y, ‖C y‖ ≤ ‖y‖)
    (ψ : Hil Y) :
    ‖(V.comp (O.comp (adjoint V)) +
      ((1 : Hil Y →L[ℂ] Hil Y) - V.comp (adjoint V)).comp
        (C.comp ((1 : Hil Y →L[ℂ] Hil Y) - V.comp (adjoint V)))) ψ‖ ≤ ‖ψ‖ := by
  let P := V.comp (adjoint V)
  let R : Hil Y →L[ℂ] Hil Y := 1 - P
  have hPv : ∀ x, P (V x) = V x := fun x =>
    congrArg (fun T : Hil X →L[ℂ] Hil Y => T x) hV
  have hPP : ∀ y, P (P y) = P y := fun y => hPv (adjoint V y)
  have hPstar : adjoint P = P := by simp only [P, adjoint_comp, adjoint_adjoint]
  have hP : IsStarProjection P := by
    refine ⟨?_, ?_⟩
    · exact ContinuousLinearMap.ext hPP
    · exact hPstar
  have hR : IsStarProjection R := hP.one_sub
  have hVadj : (adjoint V).comp P = adjoint V := by
    have hh := congrArg adjoint hV
    simpa only [adjoint_comp, adjoint_adjoint, comp_assoc, P] using hh
  have hVR : ∀ y, adjoint V (R y) = 0 := by
    intro y
    have hh := congrArg (fun T : Hil Y →L[ℂ] Hil X => T y) hVadj
    change adjoint V (y - P y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hh.symm
  have horth : ∀ x y, inner ℂ (V x) (R y) = 0 := by
    intro x y
    rw [← adjoint_inner_right, hVR, inner_zero_right]
  have hnV : ‖V‖ ≤ 1 := by
    have hh := IsStarProjection.norm_le P hP
    have he := norm_adjoint_comp_self (adjoint V)
    simp only [adjoint_adjoint, LinearIsometryEquiv.norm_map] at he
    change ‖P‖ = ‖V‖ * ‖V‖ at he
    nlinarith [norm_nonneg V]
  have hVnorm : ∀ x, ‖V x‖ ≤ ‖x‖ := by
    intro x
    exact (le_opNorm V x).trans (by simpa using mul_le_mul_of_nonneg_right hnV (norm_nonneg x))
  have hRnorm : ∀ y, ‖R y‖ ≤ ‖y‖ := by
    intro y
    calc
      ‖R y‖ ≤ ‖R‖ * ‖y‖ := le_opNorm R y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (IsStarProjection.norm_le R hR) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  have henergy : ‖P ψ‖ ^ 2 = ‖adjoint V ψ‖ ^ 2 := by
    rw [apply_norm_sq_eq_inner_adjoint_right P,
      apply_norm_sq_eq_inner_adjoint_right (adjoint V), adjoint_adjoint]
    simp only [hPstar, comp_apply]
    change RCLike.re (inner ℂ ψ (P (P ψ))) = RCLike.re (inner ℂ ψ (P ψ))
    rw [hPP]
  have hinput : ‖ψ‖ ^ 2 = ‖adjoint V ψ‖ ^ 2 + ‖R ψ‖ ^ 2 := by
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (P ψ) (R ψ) (horth (adjoint V ψ) ψ)
    have he : P ψ + R ψ = ψ := by change P ψ + (ψ - P ψ) = ψ; abel
    simp only [← sq, he, henergy] at hh
    exact hh
  let a := V (O (adjoint V ψ))
  let b := R (C (R ψ))
  have ha : ‖a‖ ≤ ‖adjoint V ψ‖ := (hVnorm _).trans (hO _)
  have hb : ‖b‖ ≤ ‖R ψ‖ := (hRnorm _).trans (hC _)
  have hout : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b (horth _ _)
  have ha2 := (sq_le_sq₀ (norm_nonneg a) (norm_nonneg (adjoint V ψ))).mpr ha
  have hb2 := (sq_le_sq₀ (norm_nonneg b) (norm_nonneg (R ψ))).mpr hb
  change ‖a + b‖ ≤ ‖ψ‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

end WeldedPath.PartialIsometryContraction

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

-- Solutions.WeldedPathExactContraction
section

namespace WeldedPath.ExactContraction

open Classical QAlgorithms Supplement EncodedOracleUnitary CompressedPrimitive
open scoped BigOperators

theorem exactCpOE_norm_le {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖exactCpOE enc x inv ψ‖ ≤ ‖ψ‖ := by
  exact PartialIsometryContraction.block_norm_le
    (opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (intertwiner s))
    (TensorOperators.opTensor_one_partial (intertwiner s)
      (IntertwinerPartial.intertwiner_partial s))
    (stdQueryE enc x inv) (cpOE enc x inv)
    (fun v => (stdQueryE_norm enc x inv v).le) (cpOE_norm_le enc x inv) ψ

theorem exactCpO_norm_le {s : ℕ} (d : ℕ) (x : Fin s) (inv : Bool)
    (ψ : Hil (Qubits d × InjDb s)) : ‖exactCpO d x inv ψ‖ ≤ ‖ψ‖ :=
  exactCpOE_norm_le (encode d) x inv ψ

theorem basisMap_involutive_adjoint {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (hf : Function.Involutive f) :
    ContinuousLinearMap.adjoint (basisMap f) = basisMap f := by
  simp only [basisMap, ketBra_eq_rankOne, map_sum, InnerProductSpace.adjoint_rankOne]
  calc
    _ = ∑ i, InnerProductSpace.rankOne ℂ (ket (f i)) (ket (f (f i))) :=
      (Equiv.sum_comp (hf.toPerm f)
        (fun i => InnerProductSpace.rankOne ℂ (ket i) (ket (f i)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hf i]

theorem stdQueryE_adjoint {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (stdQueryE enc x inv) = stdQueryE enc x inv := by
  apply basisMap_involutive_adjoint
  rintro ⟨a, π⟩
  exact Prod.ext (qubits_add_cancel a _) rfl

theorem purifiedXorE_adjoint {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) :
    ContinuousLinearMap.adjoint (purifiedXorE enc x) = purifiedXorE enc x := by
  apply basisMap_involutive_adjoint
  rintro ⟨a, I⟩
  cases h : I x with
  | none => simp only [h]
  | some y => simp only [h, qubits_add_cancel]

theorem cpOE_adjoint {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (cpOE enc x inv) = cpOE enc x inv := by
  cases inv <;> simp only [cpOE, Bool.false_eq_true, if_false, if_true,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    purifiedXorE_adjoint, ContinuousLinearMap.comp_assoc]

theorem exactCpOE_adjoint {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (exactCpOE enc x inv) = exactCpOE enc x inv := by
  simp only [exactCpOE, map_add, map_sub, ContinuousLinearMap.adjoint_one,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    stdQueryE_adjoint, cpOE_adjoint, ContinuousLinearMap.comp_assoc]

theorem exactCpO_adjoint {s : ℕ} (d : ℕ) (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (exactCpO d x inv) = exactCpO d x inv :=
  exactCpOE_adjoint (encode d) x inv

theorem exactCpOE_opNorm_le {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) : ‖exactCpOE enc x inv‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using exactCpOE_norm_le enc x inv ψ

theorem controlled_ket {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
    [DecidableEq C] [DecidableEq X]
    (T : C → Hil X →L[ℂ] Hil Y) (c : C) (x : X) :
    controlled T (ket (c, x)) = ketTensor (ket c) (T c (ket x)) := by
  ext p
  rcases p with ⟨a, y⟩
  rw [ControlledOperators.controlled_apply]
  by_cases ha : a = c
  · subst a
    have hs : slice (ket (c, x)) c = ket x := by
      ext z
      simp [slice, HilbertSupport.ket_apply]
    rw [hs]
    simp [HilbertSupport.ketTensor_apply, HilbertSupport.ket_apply]
  · have hs : slice (ket (c, x)) a = 0 := by
      ext z
      simp [slice, HilbertSupport.ket_apply, ha]
    rw [hs, map_zero]
    simp [HilbertSupport.ketTensor_apply, HilbertSupport.ket_apply, ha]

theorem controlled_adjoint {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
    [DecidableEq C] [DecidableEq X] [DecidableEq Y]
    (T : C → Hil X →L[ℂ] Hil Y) :
    ContinuousLinearMap.adjoint (controlled T) =
      controlled (fun c => ContinuousLinearMap.adjoint (T c)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext p
  rcases p with ⟨c, x⟩
  rw [← HilbertSupport.inner_ket (c, x), ContinuousLinearMap.adjoint_inner_right,
    controlled_ket, TensorOperators.inner_ketTensor_slice,
    ← ContinuousLinearMap.adjoint_inner_right, HilbertSupport.inner_ket,
    ControlledOperators.controlled_apply]

theorem controlled_exactCpOE_adjoint {C : Type*} [Fintype C] [DecidableEq C]
    {s d : ℕ} (enc : C → Fin s → Qubits d) (x : C → Fin s) (inv : C → Bool) :
    ContinuousLinearMap.adjoint (controlled (fun c => exactCpOE (enc c) (x c) (inv c))) =
      controlled (fun c => exactCpOE (enc c) (x c) (inv c)) := by
  rw [controlled_adjoint]
  simp only [exactCpOE_adjoint]

theorem controlled_exactCpOE_opNorm_le {C : Type*} [Fintype C] [DecidableEq C]
    {s d : ℕ} (enc : C → Fin s → Qubits d) (x : C → Fin s) (inv : C → Bool) :
    ‖controlled (fun c => exactCpOE (enc c) (x c) (inv c))‖ ≤ 1 :=
  ControlledOperators.controlled_opNorm_le _
    (fun c ψ => exactCpOE_norm_le (enc c) (x c) (inv c) ψ)

end WeldedPath.ExactContraction

end

open Classical WeldedPath WeldedPath.Supplement QAlgorithms

universe u

theorem solution :
    ∀ s d : ℕ,
    (∀ (enc : Fin s → Qubits d) (x : Fin s) (inv : Bool),
      ContinuousLinearMap.adjoint (exactCpOE enc x inv) = exactCpOE enc x inv ∧
      ‖exactCpOE enc x inv‖ ≤ 1) ∧
    (∀ (C : Type u) [Fintype C] [DecidableEq C]
      (enc : C → Fin s → Qubits d) (x : C → Fin s) (inv : C → Bool),
      ContinuousLinearMap.adjoint (controlled (fun c => exactCpOE (enc c) (x c) (inv c))) =
        controlled (fun c => exactCpOE (enc c) (x c) (inv c)) ∧
      ‖controlled (fun c => exactCpOE (enc c) (x c) (inv c))‖ ≤ 1) := by
  intro s d
  constructor
  · intro enc x inv
    exact ⟨ExactContraction.exactCpOE_adjoint enc x inv,
      ExactContraction.exactCpOE_opNorm_le enc x inv⟩
  · intro C _ _ enc x inv
    exact ⟨ExactContraction.controlled_exactCpOE_adjoint enc x inv,
      ExactContraction.controlled_exactCpOE_opNorm_le enc x inv⟩
