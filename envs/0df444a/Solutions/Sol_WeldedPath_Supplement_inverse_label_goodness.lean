-- Prove2me | solution 1 for WeldedPath.Supplement.inverse_label_goodness
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-18T01:53:15.578931+00:00
-- url     : https://prove2.me/submissions/90e7be6f-4b43-4a10-96e9-85270060b0c7

import Definitions.Def_WeldedPath_Supplement_exactCpWT
import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Definitions.Def_WeldedPath_InjDb
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Definitions.Def_WeldedPath_exactCpO
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_WeldedPath_Supplement_projGood
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_WeldedPath_Supplement_pCross
import Definitions.Def_WeldedPath_bEdge
import Definitions.Def_WeldedPath_Nb
import Definitions.Def_WeldedPath_Supplement_pWt
import Theorems.Thm_WeldedPath_forest_coefficient_stability
import Mathlib.RingTheory.Noetherian.Basic

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

-- Solutions.WeldedPathRegisterIsometry
section

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open scoped BigOperators

variable {Ω C X Y : Type*} [Fintype Ω] [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X] [DecidableEq Y]

theorem controlled_norm (T : C → Hil X →L[ℂ] Hil Y)
    (hT : ∀ c ψ, ‖T c ψ‖ = ‖ψ‖) (ψ : Hil (C × X)) : ‖controlled T ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← sum_slice_norm_sq, ← sum_slice_norm_sq]
  apply Finset.sum_congr rfl
  intro c _
  have hs : slice (controlled T ψ) c = T c (slice ψ c) := by
    ext y
    exact controlled_apply T ψ c y
  rw [hs, hT]

theorem ofBasis_partImg_norm (e : Ω ≃ C × X)
    (T : C → Hil X →L[ℂ] Hil X) (hT : ∀ c x, ‖T c x‖ = ‖x‖)
    (ψ : Hil Ω) :
    ‖ofBasis (fun p => partImg (T (e p).1) (e p).2
      (fun x => e.symm ((e p).1, x))) ψ‖ = ‖ψ‖ := by
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
  change ‖U ψ‖ = ‖ψ‖
  rw [← basisMap_equiv_norm e (U ψ), heq, controlled_norm T hT,
    basisMap_equiv_norm e ψ]

theorem partImg_eq_basisMap (T : Hil X →L[ℂ] Hil X) (x : X) (put : X → Ω) :
    partImg T x put = basisMap put (T (ket x)) := by
  conv_rhs => rw [← sum_basis (T (ket x))]
  simp only [partImg, map_sum, map_smul, basisMap_ket, inner_ket]

theorem maps_eq_of_support (S T : Hil X →L[ℂ] Hil Y) (ψ : Hil X)
    (h : ∀ x, ψ x ≠ 0 → S (ket x) = T (ket x)) : S ψ = T ψ := by
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ψ x = 0
  · simp only [hx, zero_smul]
  · rw [h x hx]

end WeldedPath.RegisterTransport

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

-- Solutions.WeldedPathControlApproximation
section

namespace WeldedPath.ControlApproximation

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open RegisterTransport TensorOperators
open scoped BigOperators

variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq X] [DecidableEq Y]

theorem partImg_control (T : Hil X →L[ℂ] Hil X) (x : X) (c : C) (f : X → Y) :
    partImg T x (fun z => (c, f z)) = ketTensor (ket c) (partImg T x f) := by
  ext ⟨d,y⟩
  by_cases h : d = c
  · subst d
    simp [partImg, ketTensor_apply, ket_apply]
  · simp [partImg, ketTensor_apply, ket_apply, h]

theorem projection_residual_le (S : Submodule ℂ (Hil X)) (v w : Hil X) (hw : w ∈ S) :
    ‖v - S.starProjection v‖ ≤ ‖v - w‖ := by
  have he : v - S.starProjection v = Sᗮ.starProjection (v - w) := by
    rw [map_sub, S.starProjection_orthogonal_apply_eq_zero hw, sub_zero,
      Submodule.starProjection_orthogonal']
    rfl
  rw [he]
  exact Sᗮ.norm_starProjection_apply_le _

theorem controlled_projection_sq_bound (T : C → Hil X →L[ℂ] Hil X)
    (S S' : Submodule ℂ (Hil X)) (K : ℝ) (hK : 0 ≤ K)
    (hT : ∀ c v, v ∈ S → ∃ w ∈ S', ‖T c v - w‖ ^ 2 ≤ K * ‖v‖ ^ 2)
    (ψ : Hil (C × X)) :
    ‖(((1 : Hil (C × X) →L[ℂ] Hil (C × X)) - opTensor (1 : Hil C →L[ℂ] Hil C) S'.starProjection).comp
      ((controlled T).comp (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection))) ψ‖ ^ 2 ≤ K * ‖ψ‖ ^ 2 := by
  let R := ((1 : Hil (C × X) →L[ℂ] Hil (C × X)) - opTensor (1 : Hil C →L[ℂ] Hil C) S'.starProjection).comp
    ((controlled T).comp (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection))
  have hs (c : C) : slice (R ψ) c = T c (S.starProjection (slice ψ c)) -
      S'.starProjection (T c (S.starProjection (slice ψ c))) := by
    have hp : slice (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection ψ) c =
        S.starProjection (slice ψ c) := by
      ext x
      exact opTensor_one_apply _ ψ c x
    have ht : slice (controlled T (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection ψ)) c =
        T c (S.starProjection (slice ψ c)) := by
      ext x
      rw [show slice (controlled T (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection ψ)) c x =
        controlled T (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection ψ) (c,x) from rfl,
        controlled_apply, hp]
    ext x
    change (controlled T (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection ψ)) (c,x) -
      (opTensor (1 : Hil C →L[ℂ] Hil C) S'.starProjection (controlled T (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection ψ))) (c,x) = _
    rw [opTensor_one_apply, ht]
    exact congrArg (fun z : Hil X => z x -
      S'.starProjection (T c (S.starProjection (slice ψ c))) x) ht
  change ‖R ψ‖ ^ 2 ≤ _
  rw [← sum_slice_norm_sq]
  calc
    _ ≤ ∑ c, K * ‖slice ψ c‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      obtain ⟨w,hw,hb⟩ := hT c _ (S.starProjection_apply_mem (slice ψ c))
      rw [hs]
      calc
        _ ≤ ‖T c (S.starProjection (slice ψ c)) - w‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (projection_residual_le S' _ w hw) 2
        _ ≤ K * ‖S.starProjection (slice ψ c)‖ ^ 2 := hb
        _ ≤ K * ‖slice ψ c‖ ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (S.norm_starProjection_apply_le _) 2) hK
    _ = _ := by rw [← Finset.mul_sum, sum_slice_norm_sq]

theorem controlled_projection_norm_bound (T : C → Hil X →L[ℂ] Hil X)
    (S S' : Submodule ℂ (Hil X)) (K : ℝ) (hK : 0 ≤ K)
    (hT : ∀ c v, v ∈ S → ∃ w ∈ S', ‖T c v - w‖ ^ 2 ≤ K * ‖v‖ ^ 2) :
    ‖((1 : Hil (C × X) →L[ℂ] Hil (C × X)) - opTensor (1 : Hil C →L[ℂ] Hil C) S'.starProjection).comp
      ((controlled T).comp (opTensor (1 : Hil C →L[ℂ] Hil C) S.starProjection))‖ ≤
      Real.sqrt K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg K)
  intro ψ
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg K) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hK]
  exact controlled_projection_sq_bound T S S' K hK hT ψ

end WeldedPath.ControlApproximation

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

-- Solutions.WeightedForestFactorization
section

/-! Finite weighted laws split by a separator.  All identities also cover zero
normalizers: division is the ordinary totalized division on `ℝ`. -/

namespace FiniteWeightedForest

open scoped BigOperators

section ProductLaws

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

/-- Reindexing a product of two finite weights factors its normalizer. -/
theorem sum_factor {R : Type*} [CommSemiring R]
    (e : Ω ≃ A × B) (f : A → R) (g : B → R) :
    (∑ ω, f (e ω).1 * g (e ω).2) = (∑ a, f a) * ∑ b, g b := by
  rw [Fintype.sum_equiv e _ (fun p => f p.1 * g p.2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- A centered function of one branch is orthogonal to every function of the
other branch. With `R = ℂ`, the first function may include complex conjugation. -/
theorem weighted_centered_sum {R : Type*} [CommSemiring R]
    (e : Ω ≃ A × B) (f u : A → R) (g v : B → R)
    (hu : ∑ a, f a * u a = 0) :
    (∑ ω, f (e ω).1 * g (e ω).2 * (u (e ω).1 * v (e ω).2)) = 0 := by
  calc
    _ = ∑ ω, (f (e ω).1 * u (e ω).1) * (g (e ω).2 * v (e ω).2) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = (∑ a, f a * u a) * ∑ b, g b * v b :=
      sum_factor e (fun a => f a * u a) (fun b => g b * v b)
    _ = 0 := by rw [hu, zero_mul]

/-- A constant shared factor cancels from a normalized finite law. -/
theorem normalize_scale (w : Ω → ℝ) (c : ℝ) (hc : c ≠ 0) (ω : Ω) :
    (c * w ω) / (∑ η, c * w η) = w ω / ∑ η, w η := by
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- The normalized product law is the product of the normalized branch laws. -/
theorem normalize_factor (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ) (ω : Ω) :
    (f (e ω).1 * g (e ω).2) / (∑ η, f (e η).1 * g (e η).2) =
      (f (e ω).1 / ∑ a, f a) * (g (e ω).2 / ∑ b, g b) := by
  rw [sum_factor]
  exact (div_mul_div_comm _ _ _ _).symm

/-- Conditional weights on a rectangular event remain a product law. -/
theorem conditional_factor (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ)
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q] (ω : Ω) :
    (if P (e ω).1 ∧ Q (e ω).2 then f (e ω).1 * g (e ω).2 else 0) /
      (∑ η, if P (e η).1 ∧ Q (e η).2 then f (e η).1 * g (e η).2 else 0) =
      ((if P (e ω).1 then f (e ω).1 else 0) /
        ∑ a, if P a then f a else 0) *
      ((if Q (e ω).2 then g (e ω).2 else 0) /
        ∑ b, if Q b then g b else 0) := by
  have h (a : A) (b : B) :
      (if P a ∧ Q b then f a * g b else 0) =
        (if P a then f a else 0) * (if Q b then g b else 0) := by
    split_ifs <;> simp_all
  simp_rw [h]
  exact normalize_factor e (fun a => if P a then f a else 0)
    (fun b => if Q b then g b else 0) ω

/-- Fixing the two endpoints of a bridge makes its kernel a constant, so the
two sides are conditionally independent. No positivity assumptions are needed
apart from the bridge value being nonzero. -/
theorem bridge_conditional_factor {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ)
    (left : A → X) (right : B → Y) (K : X → Y → ℝ)
    (x : X) (y : Y) (hK : K x y ≠ 0) (ω : Ω) :
    (if left (e ω).1 = x ∧ right (e ω).2 = y then
        f (e ω).1 * g (e ω).2 * K (left (e ω).1) (right (e ω).2) else 0) /
      (∑ η, if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 * K (left (e η).1) (right (e η).2) else 0) =
      ((if left (e ω).1 = x then f (e ω).1 else 0) /
        ∑ a, if left a = x then f a else 0) *
      ((if right (e ω).2 = y then g (e ω).2 else 0) /
        ∑ b, if right b = y then g b else 0) := by
  have h (η : Ω) :
      (if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 * K (left (e η).1) (right (e η).2) else 0) =
      K x y * (if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 else 0) := by
    by_cases hxy : left (e η).1 = x ∧ right (e η).2 = y
    · simp [hxy, hxy.1, hxy.2, mul_comm]
    · simp [hxy]
  simp_rw [h]
  rw [normalize_scale (fun η => if left (e η).1 = x ∧ right (e η).2 = y then
    f (e η).1 * g (e η).2 else 0) _ hK]
  exact conditional_factor e f g (fun a => left a = x) (fun b => right b = y) ω

end ProductLaws

section VertexPartition

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]

/-- Restrict an assignment to the two sides of a finite vertex separator. -/
def splitAssignment (S : Finset V) :
    (V → X) ≃ (({v // v ∈ S} → X) × ({v // v ∉ S} → X)) :=
  Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => X)

@[simp] theorem splitAssignment_left (S : Finset V) (φ : V → X) (u : {v // v ∈ S}) :
    (splitAssignment S φ).1 u = φ u := rfl

@[simp] theorem splitAssignment_right (S : Finset V) (φ : V → X) (u : {v // v ∉ S}) :
    (splitAssignment S φ).2 u = φ u := rfl

theorem sum_split (S : Finset V) (f : ({v // v ∈ S} → X) → ℝ)
    (g : ({v // v ∉ S} → X) → ℝ) :
    (∑ φ : V → X, f (fun u => φ u) * g (fun u => φ u)) =
      (∑ a, f a) * ∑ b, g b :=
  sum_factor (splitAssignment S) f g

end VertexPartition

section EdgeProducts

variable {V X : Type*} [DecidableEq V]

/-- A product of possibly edge-dependent transition weights. -/
noncomputable def edgeWeight (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (φ : V → X) : ℝ := ∏ p ∈ E, K p (φ p.1) (φ p.2)

/-- Deleting one stored edge removes exactly its kernel factor. -/
theorem edgeWeight_erase (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (φ : V → X) (e : V × V) (he : e ∈ E) :
    edgeWeight E K φ = edgeWeight (E.erase e) K φ * K e (φ e.1) (φ e.2) := by
  classical
  exact (Finset.prod_erase_mul E (fun p => K p (φ p.1) (φ p.2)) he).symm

/-- The remaining product separates by the side containing the first endpoint.
For a graph separator, both endpoints of every remaining edge lie on this side. -/
theorem edgeWeight_split (E : Finset (V × V)) (S : Finset V)
    (K : (V × V) → X → X → ℝ) (φ : V → X) :
    edgeWeight E K φ =
      edgeWeight (E.filter (fun p => p.1 ∈ S)) K φ *
      edgeWeight (E.filter (fun p => p.1 ∉ S)) K φ := by
  classical
  exact (Finset.prod_filter_mul_prod_filter_not E (fun p => p.1 ∈ S)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Exact one-edge separator factorization of an arbitrary edge-weight product. -/
theorem edgeWeight_bridge (E : Finset (V × V)) (S : Finset V)
    (K : (V × V) → X → X → ℝ) (φ : V → X) (e : V × V) (he : e ∈ E) :
    edgeWeight E K φ =
      edgeWeight ((E.erase e).filter (fun p => p.1 ∈ S)) K φ *
      edgeWeight ((E.erase e).filter (fun p => p.1 ∉ S)) K φ *
      K e (φ e.1) (φ e.2) := by
  rw [edgeWeight_erase E K φ e he, edgeWeight_split (E.erase e) S K φ]

end EdgeProducts

end FiniteWeightedForest

end

-- Solutions.WeightedForestSeparator
section

namespace FiniteWeightedForest

open scoped BigOperators

section BranchWeights

variable {V X : Type*} [DecidableEq V] [Zero X]

/-- Extend a branch assignment by zero off that branch. Off-branch values do
not affect the branch weight when all its edges stay in the branch. -/
def extendAssignment (P : V → Prop) [DecidablePred P] (a : {v // P v} → X) (v : V) : X :=
  if h : P v then a ⟨v, h⟩ else 0

noncomputable def branchWeight (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (a : {v // P v} → X) : ℝ :=
  edgeWeight (E.filter (fun p => P p.1)) K (extendAssignment P a)

theorem branchWeight_restrict (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (φ : V → X)
    (hclosed : ∀ p ∈ E, P p.1 ↔ P p.2) :
    branchWeight E P K (fun v => φ v) =
      edgeWeight (E.filter (fun p => P p.1)) K φ := by
  classical
  unfold branchWeight edgeWeight
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hpE, hpP⟩ := Finset.mem_filter.mp hp
  simp [extendAssignment, hpP, (hclosed p hpE).mp hpP]

/-- An edge product on a graph with a one-edge separator is a product of its
two branch weights and the separating edge kernel. -/
theorem edgeWeight_bridge_branches (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (φ : V → X)
    (e : V × V) (he : e ∈ E)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2) :
    edgeWeight E K φ =
      branchWeight (E.erase e) P K (fun v => φ v) *
      branchWeight (E.erase e) (fun v => ¬P v) K (fun v => φ v) *
      K e (φ e.1) (φ e.2) := by
  classical
  rw [branchWeight_restrict _ P _ _ hclosed,
    branchWeight_restrict _ (fun v => ¬P v) _ _ (fun p hp => not_congr (hclosed p hp)),
    edgeWeight_erase E K φ e he]
  congr 1
  exact (Finset.prod_filter_mul_prod_filter_not (E.erase e) (fun p => P p.1)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Exact conditional independence of the branches of a weighted tree after
the values of the two endpoints of a deleted edge are fixed. -/
theorem tree_bridge_conditional_factor [Fintype V] [Fintype X] [DecidableEq X]
    (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (e : V × V) (he : e ∈ E)
    (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (x y : X) (hK : K e x y ≠ 0) (φ : V → X) :
    (if φ e.1 = x ∧ φ e.2 = y then edgeWeight E K φ else 0) /
      (∑ ψ : V → X, if ψ e.1 = x ∧ ψ e.2 = y then edgeWeight E K ψ else 0) =
      ((if φ e.1 = x then branchWeight (E.erase e) P K (fun v => φ v) else 0) /
        ∑ a : {v // P v} → X,
          if a ⟨e.1, hleft⟩ = x then branchWeight (E.erase e) P K a else 0) *
      ((if φ e.2 = y then branchWeight (E.erase e) (fun v => ¬P v) K
          (fun v => φ v) else 0) /
        ∑ b : {v // ¬P v} → X,
          if b ⟨e.2, hright⟩ = y then branchWeight (E.erase e) (fun v => ¬P v) K b else 0) := by
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (ψ : V → X) := edgeWeight_bridge_branches E P K ψ e he hclosed
  simp_rw [hfactor]
  exact bridge_conditional_factor split
    (branchWeight (E.erase e) P K) (branchWeight (E.erase e) (fun v => ¬P v) K)
    (fun a => a ⟨e.1, hleft⟩) (fun b => b ⟨e.2, hright⟩) (K e) x y hK φ

end BranchWeights

section SupportedWeights

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Zero X]

/-- Edge-product weight with arbitrary restrictions at individual vertices. -/
noncomputable def forestWeight (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (allowed : V → X → Prop) (φ : V → X) : ℝ := by
  classical
  exact if ∀ v, allowed v (φ v) then edgeWeight E K φ else 0

noncomputable def supportedBranchWeight (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (a : {v // P v} → X) : ℝ := by
  classical
  exact if ∀ v : {v // P v}, allowed v.val (a v) then branchWeight E P K a else 0

theorem forestWeight_bridge_branches (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (φ : V → X) (e : V × V) (he : e ∈ E)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2) :
    forestWeight E K allowed φ =
      supportedBranchWeight (E.erase e) P K allowed (fun v => φ v) *
      supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed (fun v => φ v) *
      K e (φ e.1) (φ e.2) := by
  classical
  have hall : (∀ v, allowed v (φ v)) ↔
      (∀ v : {v // P v}, allowed v (φ v)) ∧
        (∀ v : {v // ¬P v}, allowed v (φ v)) := by
    constructor
    · intro h
      exact ⟨fun v => h v, fun v => h v⟩
    · rintro ⟨hl, hr⟩ v
      by_cases hv : P v
      · exact hl ⟨v, hv⟩
      · exact hr ⟨v, hv⟩
  unfold forestWeight supportedBranchWeight
  simp only [hall, edgeWeight_bridge_branches E P K φ e he hclosed,
    ite_and, mul_ite, ite_mul, mul_zero, zero_mul]
  split_ifs <;> rfl

/-- The separator law remains exact after imposing any local vertex support
conditions, including the allowed physical vertex set in `AbsForest.muComp`. -/
theorem supported_tree_bridge_conditional_factor [DecidableEq X]
    (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (e : V × V) (he : e ∈ E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (x y : X) (hK : K e x y ≠ 0) (φ : V → X) :
    (if φ e.1 = x ∧ φ e.2 = y then forestWeight E K allowed φ else 0) /
      (∑ ψ : V → X, if ψ e.1 = x ∧ ψ e.2 = y then forestWeight E K allowed ψ else 0) =
      ((if φ e.1 = x then supportedBranchWeight (E.erase e) P K allowed
          (fun v => φ v) else 0) /
        ∑ a : {v // P v} → X,
          if a ⟨e.1, hleft⟩ = x then supportedBranchWeight (E.erase e) P K allowed a else 0) *
      ((if φ e.2 = y then supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed
          (fun v => φ v) else 0) /
        ∑ b : {v // ¬P v} → X,
          if b ⟨e.2, hright⟩ = y then
            supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed b else 0) := by
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (ψ : V → X) := forestWeight_bridge_branches E P K allowed ψ e he hclosed
  simp_rw [hfactor]
  exact bridge_conditional_factor split
    (supportedBranchWeight (E.erase e) P K allowed)
    (supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed)
    (fun a => a ⟨e.1, hleft⟩) (fun b => b ⟨e.2, hright⟩) (K e) x y hK φ

end SupportedWeights

section ForestCuts

variable {V : Type*} [LinearOrder V]

def edgeGraph (E : Finset (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ E)

/-- With one increasing orientation per edge, erasing a stored pair deletes
the corresponding undirected edge. -/
theorem edgeGraph_erase_le_delete (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) (he : e ∈ E) :
    edgeGraph (E.erase e) ≤ (edgeGraph E).deleteEdges {s(e.1, e.2)} := by
  intro u v huv
  obtain ⟨hne, huv | hvu⟩ := huv
  · obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp huv
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨hne, Or.inl hmem⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · exact hneq (Prod.ext hu hv)
    · have h := horder (u, v) hmem
      have heo := horder e he
      simp only [hu, hv] at h
      exact (lt_asymm h heo)
  · obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp hvu
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨hne, Or.inr hmem⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · have h := horder (v, u) hmem
      have heo := horder e he
      simp only [hu, hv] at h
      exact (lt_asymm h heo)
    · exact hneq (Prod.ext hv hu)

/-- The endpoints of a forest edge belong to different components after it
is erased. -/
theorem forest_cut_not_reachable (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) (hforest : (edgeGraph E).IsAcyclic)
    (he : e ∈ E) : ¬(edgeGraph (E.erase e)).Reachable e.1 e.2 := by
  have hadj : (edgeGraph E).Adj e.1 e.2 := ⟨ne_of_lt (horder e he), Or.inl he⟩
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hforest) hadj
  intro hr
  exact hb (hr.mono (edgeGraph_erase_le_delete E e horder he))

/-- No remaining edge crosses the component cut, so its kernel depends only
on the coordinates of one branch. -/
theorem forest_cut_closed (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) :
    ∀ p ∈ E.erase e,
      (edgeGraph (E.erase e)).Reachable e.1 p.1 ↔
        (edgeGraph (E.erase e)).Reachable e.1 p.2 := by
  intro p hp
  have hpE := (Finset.mem_erase.mp hp).2
  have hr : (edgeGraph (E.erase e)).Reachable p.1 p.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (horder p hpE), Or.inl hp⟩
  exact ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩

end ForestCuts

end FiniteWeightedForest

end

-- Solutions.WeldedPathForestFactorization
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest

variable {n : ℕ}

noncomputable def componentEdges (H : AbsForest n) (s : Fin H.k) :
    Finset (Fin H.k × Fin H.k) := by
  classical
  exact H.E.filter (fun p => p.1 ∈ H.comp s)

noncomputable def componentKernel (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (p : Fin H.k × Fin H.k) (x y : Label n) : ℝ :=
  kappa l G (H.color p) x.val y.val

def componentAllowed (l : ℕ) (H : AbsForest n) (s u : Fin H.k) (x : Label n) : Prop :=
  u ∈ H.comp s → x.val ∈ Vmid n l ∪ Vbd n l

/-- The assignment-independent prefactor in the canonical definition of
`muComp` for a component with at least one edge. -/
noncomputable def componentScale (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) : ℝ := by
  classical
  let V := Vmid n l ∪ Vbd n l
  let Z := (1 / (V.card : ℝ)) *
    ∑ ψ ∈ Finset.univ.filter (fun ψ : Fin H.k → Label n =>
      (∀ u ∈ H.comp s, (ψ u).val ∈ V) ∧ (∀ u, u ∉ H.comp s → ψ u = 0)),
        edgeWeight (componentEdges H s) (componentKernel l G H) ψ
  exact (1 / Z) * (1 / (V.card : ℝ))

/-- The canonical reference component measure is exactly a common scalar
times the edge-product law with its local vertex support restrictions. -/
theorem muComp_eq_scale_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ : Fin H.k → Label n) :
    H.muComp l G s φ = componentScale l G H s *
      forestWeight (componentEdges H s) (componentKernel l G H) (componentAllowed l H s) φ := by
  classical
  unfold AbsForest.muComp
  simp only [hsize, ite_false]
  unfold componentScale forestWeight componentAllowed componentEdges componentKernel edgeWeight
  simp only [mul_ite, mul_zero]

theorem componentScale_ne_zero (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ₀ : Fin H.k → Label n)
    (hμ : H.muComp l G s φ₀ ≠ 0) : componentScale l G H s ≠ 0 := by
  rw [muComp_eq_scale_forestWeight l G H s hsize φ₀] at hμ
  exact (mul_ne_zero_iff.mp hμ).1

/-- Conditioning the reference component measure cancels its global
normalizer. The resulting finite law is precisely the conditioned supported
edge-product law. -/
theorem muComp_condition_eq_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ₀ : Fin H.k → Label n)
    (hμ : H.muComp l G s φ₀ ≠ 0) (T : (Fin H.k → Label n) → Prop)
    [DecidablePred T] (φ : Fin H.k → Label n) :
    (if T φ then H.muComp l G s φ else 0) /
      (∑ ψ, if T ψ then H.muComp l G s ψ else 0) =
    (if T φ then forestWeight (componentEdges H s) (componentKernel l G H)
        (componentAllowed l H s) φ else 0) /
      (∑ ψ, if T ψ then forestWeight (componentEdges H s) (componentKernel l G H)
        (componentAllowed l H s) ψ else 0) := by
  have h (ψ : Fin H.k → Label n) :
      (if T ψ then H.muComp l G s ψ else 0) =
      componentScale l G H s *
        (if T ψ then forestWeight (componentEdges H s) (componentKernel l G H)
          (componentAllowed l H s) ψ else 0) := by
    rw [muComp_eq_scale_forestWeight l G H s hsize ψ]
    split_ifs <;> simp
  simp_rw [h]
  exact normalize_scale (fun ψ => if T ψ then
    forestWeight (componentEdges H s) (componentKernel l G H) (componentAllowed l H s) ψ else 0)
    _ (componentScale_ne_zero l G H s hsize φ₀ hμ) φ

theorem componentEdges_ordered (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k) :
    ∀ p ∈ componentEdges H s, p.1 < p.2 := by
  classical
  intro p hp
  exact hH.1 p (Finset.mem_filter.mp hp).1

theorem componentEdges_acyclic (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k) :
    (edgeGraph (componentEdges H s)).IsAcyclic := by
  apply hH.2.1.anti
  intro u v h
  rcases h with ⟨hne, h | h⟩
  · exact ⟨hne, Or.inl (Finset.mem_filter.mp h).1⟩
  · exact ⟨hne, Or.inr (Finset.mem_filter.mp h).1⟩

theorem component_card_ne_one_of_edge (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) : (H.comp s).card ≠ 1 := by
  classical
  obtain ⟨heE, he₁⟩ := Finset.mem_filter.mp he
  have hr : H.graph.Reachable e.1 e.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 e heE), Or.inl heE⟩
  have he₂ : e.2 ∈ H.comp s := by
    simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ ⊢
    exact he₁.trans hr
  intro hsize
  exact (ne_of_lt (hH.1 e heE)) ((Finset.card_le_one.mp hsize.le) e.1 he₁ e.2 he₂)

def componentCut (H : AbsForest n) (s : Fin H.k) (e : Fin H.k × Fin H.k)
    (u : Fin H.k) : Prop := (edgeGraph ((componentEdges H s).erase e)).Reachable e.1 u

/-- Every forest edge supplies a genuine separator for the factorization
theorems, with no additional graph assumption left to discharge. -/
theorem componentCut_spec (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) :
    componentCut H s e e.1 ∧ ¬componentCut H s e e.2 ∧
      ∀ p ∈ (componentEdges H s).erase e,
        componentCut H s e p.1 ↔ componentCut H s e p.2 := by
  refine ⟨SimpleGraph.Reachable.refl _, ?_, ?_⟩
  · exact forest_cut_not_reachable _ _ (componentEdges_ordered H hH s)
      (componentEdges_acyclic H hH s) he
  · exact forest_cut_closed _ _ (componentEdges_ordered H hH s)

/-- Unnormalized branch factorization of the actual canonical `muComp`.
Together with `muComp_condition_eq_forestWeight` and
`supported_tree_bridge_conditional_factor`, this gives its exact normalized
endpoint-conditioned independence law. -/
theorem muComp_bridge_factor (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (e : Fin H.k × Fin H.k)
    (he : e ∈ componentEdges H s) (φ : Fin H.k → Label n) :
    let P := componentCut H s e
    letI : DecidablePred P := Classical.decPred P
    H.muComp l G s φ = componentScale l G H s *
      (supportedBranchWeight ((componentEdges H s).erase e) P
        (componentKernel l G H) (componentAllowed l H s) (fun v => φ v) *
      supportedBranchWeight ((componentEdges H s).erase e) (fun v => ¬P v)
        (componentKernel l G H) (componentAllowed l H s) (fun v => φ v) *
      kappa l G (H.color e) (φ e.1).val (φ e.2).val) := by
  classical
  dsimp only
  rw [muComp_eq_scale_forestWeight l G H s (component_card_ne_one_of_edge H hH s e he) φ]
  congr 1
  exact forestWeight_bridge_branches _ _ _ _ _ _ he (componentCut_spec H hH s e he).2.2

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathFixedData
section

namespace WeldedPath.Supplement.FixedData

variable {n : ℕ}

lemma reachable_closed {V : Type*} {J : SimpleGraph V} (P : V → Prop)
    (hstep : ∀ u v, P u → J.Adj u v → P v) {u v : V} (h : J.Reachable u v) :
    P u → P v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons huv w ih => exact fun hu => ih (hstep _ _ hu huv)

/-- Agreement of incident edges on a component suffices to preserve that
entire component; arbitrary edges wholly outside it are irrelevant. -/
lemma reachable_iff_of_adj_at_component {V : Type*} (J K : SimpleGraph V) (s : V)
    (hadj : ∀ u v, J.Reachable s u → (J.Adj u v ↔ K.Adj u v)) (v : V) :
    J.Reachable s v ↔ K.Reachable s v := by
  constructor
  · intro hv
    have h := reachable_closed (fun u => J.Reachable s u ∧ K.Reachable s u)
      (fun u v hu huv => ⟨hu.1.trans huv.reachable,
        hu.2.trans ((hadj u v hu.1).mp huv).reachable⟩) hv
        ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩
    exact h.2
  · intro hv
    exact reachable_closed (fun u => J.Reachable s u)
      (fun u v hu huv => hu.trans ((hadj u v hu).mpr huv).reachable) hv
      (SimpleGraph.Reachable.refl _)

lemma ctree_subset_sfix (H : AbsForest n) (φ : Fin H.k → Label n) (s : Fin H.k) :
    H.Ctree φ s ⊆ H.Sfix φ s := by
  classical
  exact Finset.subset_union_left

/-- Every stored edge touching the selected tree component has both its
endpoints in the recorded fixed set. -/
lemma edge_endpoints_mem_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (s : Fin H.k) (p : Fin H.k × Fin H.k) (hp : p ∈ H.E)
    (htouch : p.1 ∈ H.Ctree φ s ∨ p.2 ∈ H.Ctree φ s) :
    p.1 ∈ H.Sfix φ s ∧ p.2 ∈ H.Sfix φ s := by
  classical
  by_cases hw : H.IsWeldUnder φ p
  · rcases htouch with h₁ | h₂
    · refine ⟨ctree_subset_sfix H φ s h₁, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hw, Or.inl ⟨h₁, rfl⟩⟩)
    · refine ⟨?_, ctree_subset_sfix H φ s h₂⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hw, Or.inr ⟨h₂, rfl⟩⟩)
  · have hr : (H.treeGraph φ).Reachable p.1 p.2 :=
      SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 p hp), Or.inl ⟨hp, hw⟩⟩
    rcases htouch with h₁ | h₂
    · have h₂ : p.2 ∈ H.Ctree φ s := by
        simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ ⊢
        exact h₁.trans hr
      exact ⟨ctree_subset_sfix H φ s h₁, ctree_subset_sfix H φ s h₂⟩
    · have h₁ : p.1 ∈ H.Ctree φ s := by
        simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and] at h₂ ⊢
        exact h₂.trans hr.symm
      exact ⟨ctree_subset_sfix H φ s h₁, ctree_subset_sfix H φ s h₂⟩

lemma weld_iff_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E)
    (htouch : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s) :
    H.IsWeldUnder φ p ↔ H.IsWeldUnder φ₀ p := by
  obtain ⟨h₁, h₂⟩ := edge_endpoints_mem_sfix H hH φ₀ s p hp htouch
  simp only [AbsForest.IsWeldUnder, hφ p.1 h₁, hφ p.2 h₂]

lemma treeGraph_adj_iff_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u)
    (u v : Fin H.k) (hu : u ∈ H.Ctree φ₀ s) :
    (H.treeGraph φ).Adj u v ↔ (H.treeGraph φ₀).Adj u v := by
  have h₁ (hp : (u, v) ∈ H.E) :=
    weld_iff_of_agree_sfix H hH φ φ₀ s hφ (u, v) hp (Or.inl hu)
  have h₂ (hp : (v, u) ∈ H.E) :=
    weld_iff_of_agree_sfix H hH φ φ₀ s hφ (v, u) hp (Or.inr hu)
  constructor
  · rintro ⟨hne, ⟨hp, hn⟩ | ⟨hp, hn⟩⟩
    · exact ⟨hne, Or.inl ⟨hp, (not_congr (h₁ hp)).mp hn⟩⟩
    · exact ⟨hne, Or.inr ⟨hp, (not_congr (h₂ hp)).mp hn⟩⟩
  · rintro ⟨hne, ⟨hp, hn⟩ | ⟨hp, hn⟩⟩
    · exact ⟨hne, Or.inl ⟨hp, (not_congr (h₁ hp)).mpr hn⟩⟩
    · exact ⟨hne, Or.inr ⟨hp, (not_congr (h₂ hp)).mpr hn⟩⟩

lemma ctree_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Ctree φ s = H.Ctree φ₀ s := by
  classical
  apply Finset.ext
  intro v
  simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and]
  apply (reachable_iff_of_adj_at_component (H.treeGraph φ₀) (H.treeGraph φ) s ?_ v).symm
  intro u v hu
  apply (treeGraph_adj_iff_of_agree_sfix H hH φ φ₀ s hφ u v ?_).symm
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩

lemma sfix_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Sfix φ s = H.Sfix φ₀ s := by
  classical
  have hC := ctree_eq_of_agree_sfix H hH φ φ₀ s hφ
  unfold AbsForest.Sfix
  rw [hC]
  congr 1
  apply Finset.filter_congr
  intro u _
  constructor
  · rintro ⟨p, hp, hw, h⟩
    have ht : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s := by
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    exact ⟨p, hp, (weld_iff_of_agree_sfix H hH φ φ₀ s hφ p hp ht).mp hw, h⟩
  · rintro ⟨p, hp, hw, h⟩
    have ht : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s := by
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    exact ⟨p, hp, (weld_iff_of_agree_sfix H hH φ φ₀ s hφ p hp ht).mpr hw, h⟩

lemma wfix_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Wfix φ s = H.Wfix φ₀ s := by
  classical
  have hC := ctree_eq_of_agree_sfix H hH φ φ₀ s hφ
  have hS := sfix_eq_of_agree_sfix H hH φ φ₀ s hφ
  unfold AbsForest.Wfix
  rw [hC, hS]
  congr 2
  · apply Finset.image_congr
    intro u hu
    exact congrArg (fun x : Label n => (u, x.val)) (hφ u (ctree_subset_sfix H φ₀ s hu))
  · apply Finset.image_congr
    intro u hu
    exact congrArg (fun x : Label n => (u, x.val)) (hφ u (Finset.mem_sdiff.mp hu).1)

lemma eq_on_of_image_graph_eq {V X : Type*} [DecidableEq V] [DecidableEq X]
    (A B : Finset V) (f g : V → X)
    (h : A.image (fun v => (v, f v)) = B.image (fun v => (v, g v))) :
    ∀ u ∈ B, f u = g u := by
  intro u hu
  have hm : (u, g u) ∈ A.image (fun v => (v, f v)) := by
    rw [h]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
  have hvu : v = u := congrArg Prod.fst hv
  subst v
  exact congrArg Prod.snd hv

/-- Fixed data is exactly a coordinate-fixing event on its recorded fixed
set. This is valid for all assignments, including those with zero reference
weight; no probabilistic conditioning assumption is hidden in the statement. -/
theorem wfix_eq_iff_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k) :
    H.Wfix φ s = H.Wfix φ₀ s ↔ ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u := by
  classical
  constructor
  · intro hw u hu
    have hC := congrArg (fun t => t.2.1) hw
    have hS := congrArg (fun t => t.2.2) hw
    apply Fin.ext
    by_cases huc : u ∈ H.Ctree φ₀ s
    · exact eq_on_of_image_graph_eq _ _ (fun v => (φ v).val) (fun v => (φ₀ v).val) hC u huc
    · exact eq_on_of_image_graph_eq _ _ (fun v => (φ v).val) (fun v => (φ₀ v).val) hS u
        (Finset.mem_sdiff.mpr ⟨hu, huc⟩)
  · exact wfix_eq_of_agree_sfix H hH φ φ₀ s

/-- The fixed-data and boundary conditions of a description are local
restrictions on individual vertex labels. Injectivity is deliberately not
included: it is the separate collision condition in the good space. -/
def coordinateCondition (D : Description n) (B : Finset ℕ) (u : Fin D.H.k)
    (x : Label n) : Prop :=
  (∀ s ∈ D.sel, u ∈ D.H.Sfix D.ϕ₀ s → x = D.ϕ₀ u) ∧
  (∀ s ∈ D.sel, D.H.graph.Reachable s u →
    u ∉ D.H.Ctree D.ϕ₀ s → x.val ∉ B)

theorem description_conditions_iff (D : Description n) (hD : D.IsValid)
    (B : Finset ℕ) (φ : Fin D.H.k → Label n) :
    ((∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s) ∧
      (∀ s ∈ D.sel, ∀ u, D.H.graph.Reachable s u →
        u ∉ D.H.Ctree φ s → (φ u).val ∉ B)) ↔
      ∀ u, coordinateCondition D B u (φ u) := by
  constructor
  · rintro ⟨hw, hb⟩ u
    constructor
    · intro s hs hu
      exact (wfix_eq_iff_agree_sfix D.H hD.1 φ D.ϕ₀ s).mp (hw s hs) u hu
    · intro s hs hr hu
      have hC : D.H.Ctree φ s = D.H.Ctree D.ϕ₀ s := congrArg Prod.fst (hw s hs)
      exact hb s hs u hr (hC.symm ▸ hu)
  · intro h
    have hw : ∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s := by
      intro s hs
      apply (wfix_eq_iff_agree_sfix D.H hD.1 φ D.ϕ₀ s).mpr
      intro u hu
      exact (h u).1 s hs hu
    refine ⟨hw, ?_⟩
    intro s hs u hr hu
    have hC : D.H.Ctree φ s = D.H.Ctree D.ϕ₀ s := congrArg Prod.fst (hw s hs)
    exact (h u).2 s hs hr (hC ▸ hu)

theorem isGood_iff_coordinateCondition (l : ℕ) (G : WeldedInstance n)
    (D : Description n) (hD : D.IsValid) (B : Finset ℕ) (φ : Fin D.H.k → Label n) :
    D.IsGood l G B φ ↔
      0 < D.H.muRef l G φ ∧ (∀ u, coordinateCondition D B u (φ u)) ∧
        Function.Injective φ := by
  constructor
  · rintro ⟨hμ, hw, hb, hi⟩
    exact ⟨hμ, (description_conditions_iff D hD B φ).mp ⟨hw, hb⟩, hi⟩
  · rintro ⟨hμ, hc, hi⟩
    obtain ⟨hw, hb⟩ := (description_conditions_iff D hD B φ).mpr hc
    exact ⟨hμ, hw, hb, hi⟩

end WeldedPath.Supplement.FixedData

end

-- Solutions.WeldedPathReferenceProduct
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest
open Classical

variable {n : ℕ}

noncomputable def compRoot (H : AbsForest n) (u : Fin H.k) : Fin H.k :=
  (H.comp u).min' ⟨u, by simp [AbsForest.comp]⟩

lemma compRoot_reachable (H : AbsForest n) (u : Fin H.k) :
    H.graph.Reachable (compRoot H u) u := by
  have h := Finset.min'_mem (H.comp u) ⟨u, by simp [AbsForest.comp]⟩
  exact ((Finset.mem_filter.mp h).2).symm

lemma compRoot_isRoot (H : AbsForest n) (u : Fin H.k) : H.IsCompRoot (compRoot H u) := by
  intro v hv
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (compRoot_reachable H u).symm.trans hv⟩)

lemma mem_comp_iff_root_eq (H : AbsForest n) (s u : Fin H.k) (hs : H.IsCompRoot s) :
    u ∈ H.comp s ↔ compRoot H u = s := by
  classical
  constructor
  · intro hu
    have hsu := (Finset.mem_filter.mp hu).2
    have hru := compRoot_reachable H u
    exact le_antisymm ((compRoot_isRoot H u) s (hru.trans hsu.symm))
      (hs _ (hsu.trans hru.symm))
  · intro heq
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, heq ▸ compRoot_reachable H u⟩

/-- Component edge products partition the full stored-edge product exactly. -/
theorem prod_component_edgeWeight (H : AbsForest n)
    (K : (Fin H.k × Fin H.k) → Label n → Label n → ℝ) (φ : Fin H.k → Label n) :
    (∏ s ∈ Finset.univ.filter H.IsCompRoot, edgeWeight (componentEdges H s) K φ) =
      edgeWeight H.E K φ := by
  classical
  calc
    _ = ∏ s ∈ Finset.univ.filter H.IsCompRoot,
        ∏ p ∈ H.E.filter (fun p => compRoot H p.1 = s), K p (φ p.1) (φ p.2) := by
      apply Finset.prod_congr rfl
      intro s hs
      have hsroot := (Finset.mem_filter.mp hs).2
      unfold edgeWeight componentEdges
      congr 1
      exact Finset.filter_congr (fun p _ => mem_comp_iff_root_eq H s p.1 hsroot)
    _ = _ := Finset.prod_fiberwise_of_maps_to
      (fun p _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, compRoot_isRoot H p.1⟩)
      (fun p => K p (φ p.1) (φ p.2))

noncomputable def referenceScale (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) : ℝ := by
  classical
  exact ∏ s ∈ Finset.univ.filter H.IsCompRoot,
    if (H.comp s).card = 1 then 1 / (labelBound n : ℝ) else componentScale l G H s

def referenceAllowed (l : ℕ) (H : AbsForest n) (u : Fin H.k) (x : Label n) : Prop :=
  (H.IsCompRoot u → (H.comp u).card = 1 → 1 ≤ x.val) ∧
  (∀ s, H.IsCompRoot s → (H.comp s).card ≠ 1 → u ∈ H.comp s →
    x.val ∈ Vmid n l ∪ Vbd n l)

noncomputable def componentCondition (l : ℕ) (H : AbsForest n) (s : Fin H.k)
    (φ : Fin H.k → Label n) : Prop := by
  classical
  exact if (H.comp s).card = 1 then 1 ≤ (φ s).val else
    ∀ u ∈ H.comp s, (φ u).val ∈ Vmid n l ∪ Vbd n l

lemma muComp_eq_componentCondition (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    H.muComp l G s φ =
      (if (H.comp s).card = 1 then 1 / (labelBound n : ℝ) else componentScale l G H s) *
      (if componentCondition l H s φ then
        edgeWeight (componentEdges H s) (componentKernel l G H) φ else 0) := by
  classical
  by_cases hs : (H.comp s).card = 1
  · have hE : componentEdges H s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact component_card_ne_one_of_edge H hH s e he hs
    simp [AbsForest.muComp, hs, componentCondition, hE, edgeWeight]
  · rw [muComp_eq_scale_forestWeight l G H s hs φ]
    simp only [hs, ite_false, componentCondition, forestWeight, componentAllowed]
    split_ifs <;> simp_all

lemma componentConditions_iff (l : ℕ) (H : AbsForest n) (φ : Fin H.k → Label n) :
    (∀ s ∈ Finset.univ.filter H.IsCompRoot, componentCondition l H s φ) ↔
      ∀ u, referenceAllowed l H u (φ u) := by
  classical
  constructor
  · intro h u
    constructor
    · intro hu hs
      have hsu := h u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      simpa [componentCondition, hs] using hsu
    · intro s hs hsize hu
      have hsu := h s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
      have hsu' : ∀ u ∈ H.comp s, (φ u).val ∈ Vmid n l ∪ Vbd n l := by
        simpa [componentCondition, hsize] using hsu
      exact hsu' u hu
  · intro h s hs
    have hsroot := (Finset.mem_filter.mp hs).2
    by_cases hsize : (H.comp s).card = 1
    · simpa [componentCondition, hsize] using (h s).1 hsroot hsize
    · simp only [componentCondition, hsize, ite_false]
      intro u hu
      exact (h u).2 s hsroot hsize hu

/-- The actual canonical reference law is one assignment-independent
constant times the full forest edge product and unary support constraints.
This includes singleton components and zero normalizers. -/
theorem muRef_eq_scale_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ : Fin H.k → Label n) :
    H.muRef l G φ = referenceScale l G H *
      forestWeight H.E (componentKernel l G H) (referenceAllowed l H) φ := by
  classical
  unfold AbsForest.muRef
  simp_rw [muComp_eq_componentCondition l G H hH]
  rw [Finset.prod_mul_distrib]
  change referenceScale l G H * _ = referenceScale l G H * _
  congr 1
  rw [Finset.prod_ite_zero, prod_component_edgeWeight]
  simp only [forestWeight, componentConditions_iff]
  split_ifs <;> rfl

theorem referenceScale_ne_zero (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ₀ : Fin H.k → Label n) (hμ : H.muRef l G φ₀ ≠ 0) :
    referenceScale l G H ≠ 0 := by
  rw [muRef_eq_scale_forestWeight l G H hH φ₀] at hμ
  exact (mul_ne_zero_iff.mp hμ).1

/-- Any conditioning event cancels the reference normalizer. This leaves
only the local graph weight for the subsequent stochastic-process analysis. -/
theorem muRef_condition_eq_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ₀ : Fin H.k → Label n) (hμ : H.muRef l G φ₀ ≠ 0)
    (T : (Fin H.k → Label n) → Prop) [DecidablePred T] (φ : Fin H.k → Label n) :
    (if T φ then H.muRef l G φ else 0) /
      (∑ ψ, if T ψ then H.muRef l G ψ else 0) =
    (if T φ then forestWeight H.E (componentKernel l G H) (referenceAllowed l H) φ else 0) /
      (∑ ψ, if T ψ then forestWeight H.E (componentKernel l G H) (referenceAllowed l H) ψ else 0) := by
  have h (ψ : Fin H.k → Label n) :
      (if T ψ then H.muRef l G ψ else 0) = referenceScale l G H *
        (if T ψ then forestWeight H.E (componentKernel l G H) (referenceAllowed l H) ψ else 0) := by
    rw [muRef_eq_scale_forestWeight l G H hH ψ]
    split_ifs <;> simp
  simp_rw [h]
  exact normalize_scale (fun ψ => if T ψ then
    forestWeight H.E (componentKernel l G H) (referenceAllowed l H) ψ else 0)
    _ (referenceScale_ne_zero l G H hH φ₀ hμ) φ

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathGraphDepth
section

namespace WeldedPath.LoopProof

lemma pow_root_ge_two (n : ℕ) : 2 ≤ 2 ^ (n + 1) := by
  have h := Nat.two_pow_pos n
  rw [pow_succ]
  omega

lemma numV_eq (n : ℕ) : numV n = 2 * (2 ^ (n + 1) - 1) := by
  have h := pow_root_ge_two n
  unfold numV
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  omega

lemma col_zero (n : ℕ) : col n 0 = 0 := by
  have h := pow_root_ge_two n
  simp [col, show 0 < 2 ^ (n + 1) - 1 by omega]

lemma col_exit (n : ℕ) : col n (exitIdx n) = 2 * n + 1 := by
  simp [col, exitIdx]

lemma log_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) :
    Nat.log 2 (v + 1) ≤ n := by
  have h : v + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : v + 1 ≠ 0)).2 h
  omega

lemma log_right_le (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) ≤ n := by
  have hn := pow_root_ge_two n
  rw [IsVertex, numV_eq] at hv
  have h : v - (2 ^ (n + 1) - 1) + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2)
    (by omega : v - (2 ^ (n + 1) - 1) + 1 ≠ 0)).2 h
  omega

lemma col_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) : col n v ≤ n := by
  simpa [col, hv] using log_left_le n v hv

lemma col_right_ge (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    n + 1 ≤ col n v := by
  have hd := log_right_le n v hv hr
  simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1)]
  omega

lemma col_bounds (n v : ℕ) (hv : IsVertex n v) : col n v ≤ 2 * n + 1 := by
  by_cases h : v < 2 ^ (n + 1) - 1
  · have := col_left_le n v h
    omega
  · simp only [col, if_neg h]
    omega

lemma parent_spec {n v p : ℕ} (hp : parent n v = some p) :
    IsVertex n v ∧ IsVertex n p ∧
      ((col n p + 1 = col n v ∧ col n v ≤ n) ∨
        (col n v + 1 = col n p ∧ n + 1 ≤ col n v)) := by
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    have hv := h.1
    have hvleft : v < 2 ^ (n + 1) - 1 := by
      by_contra hh
      have := col_right_ge n v hv (by omega)
      omega
    have hvpos : 1 ≤ v := by
      by_contra hh
      have heq : v = 0 := by omega
      subst v
      simp [col_zero] at h
    have hpval : p = (v - 1) / 2 := by simpa using hp.symm
    have hpv : p < v := by omega
    have hpV : IsVertex n p := by unfold IsVertex at *; omega
    have hpleft : p < 2 ^ (n + 1) - 1 := by omega
    have hdiv : p + 1 = (v + 1) / 2 := by omega
    have hlog : Nat.log 2 (p + 1) = Nat.log 2 (v + 1) - 1 := by
      rw [hdiv, Nat.log_div_base]
    have hcols : col n p + 1 = col n v := by
      simp only [col, if_pos hvleft] at h
      simp only [col, if_pos hpleft, if_pos hvleft]
      omega
    exact ⟨hv, hpV, Or.inl ⟨hcols, h.2.2⟩⟩
  next h =>
    split at hp
    next h' =>
      have hv := h'.1
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc : col n v = 2 * n + 1 := by
          simpa [heq, exitIdx] using col_exit n
        omega
      have hvbig : 2 ^ (n + 1) ≤ v := by omega
      have hpval : p = (v - 2 ^ (n + 1)) / 2 + 2 ^ (n + 1) - 1 := by
        simpa using hp.symm
      have hpv : p < v := by omega
      have hpV : IsVertex n p := by unfold IsVertex at *; omega
      have hpright : 2 ^ (n + 1) - 1 ≤ p := by omega
      have hdiv : p - (2 ^ (n + 1) - 1) + 1 =
          (v - (2 ^ (n + 1) - 1) + 1) / 2 := by omega
      have hlog : Nat.log 2 (p - (2 ^ (n + 1) - 1) + 1) =
          Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) - 1 := by
        rw [hdiv, Nat.log_div_base]
      have hd := log_right_le n v hv hvright
      have hdpos : 1 ≤ Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) := by
        have := Nat.log_pos (by decide : 1 < 2)
          (show 2 ≤ v - (2 ^ (n + 1) - 1) + 1 by omega)
        omega
      have hcols : col n v + 1 = col n p := by
        simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1),
          if_neg (by omega : ¬ p < 2 ^ (n + 1) - 1)]
        omega
      exact ⟨hv, hpV, Or.inr ⟨hcols, h'.2.1⟩⟩
    next h' => simp at hp

lemma parent_eq_exit_imp {n v : ℕ} (hp : parent n v = some (exitIdx n)) :
    v = 2 ^ (n + 1) ∨ v = 2 ^ (n + 1) + 1 := by
  have hs := parent_spec hp
  have hc := col_exit n
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    rcases hs.2.2 with hleft | hright <;> omega
  next h =>
    split at hp
    next h' =>
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc' : col n v = 2 * n + 1 := by simpa [heq, exitIdx] using col_exit n
        omega
      simp only [Option.some.injEq, exitIdx] at hp
      omega
    next h' => simp at hp

lemma tree_mem_iff {n : ℕ} {G : WeldedInstance n} {v : ℕ} :
    Edge.tree v ∈ G.edges ↔ IsVertex n v ∧ (parent n v).isSome := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges, IsVertex]

lemma weld_mem_iff {n : ℕ} {G : WeldedInstance n} {u w : ℕ} :
    Edge.weld u w ∈ G.edges ↔ (u, w) ∈ G.weld := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges]

lemma edge_endpoints {n : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e : Edge} (he : e ∈ G.edges) :
    IsVertex n e.tail ∧ IsVertex n (e.head n) ∧
      (col n e.tail + 1 = col n (e.head n) ∨ col n (e.head n) + 1 = col n e.tail) := by
  cases e with
  | tree v =>
    have hv := tree_mem_iff.mp he
    cases hp : parent n v with
    | none => simp [hp] at hv
    | some p =>
      have hs := parent_spec hp
      simp only [Edge.tail, Edge.head, hp, Option.getD_some]
      exact ⟨hs.1, hs.2.1, hs.2.2.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)⟩
  | weld u w =>
    have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
    dsimp only at hw
    simp only [Edge.tail, Edge.head]
    exact ⟨hw.1, hw.2.2.1, Or.inl (by omega)⟩

lemma tree_head_col {n : ℕ} {G : WeldedInstance n} {v : ℕ}
    (he : Edge.tree v ∈ G.edges) :
    col n ((Edge.tree v).head n) = if col n v ≤ n then col n v - 1 else col n v + 1 := by
  have hv := tree_mem_iff.mp he
  cases hp : parent n v with
  | none => simp [hp] at hv
  | some p =>
    have hs := (parent_spec hp).2.2
    simp only [Edge.head, hp, Option.getD_some]
    rcases hs with h | h
    · rw [if_pos h.2]
      omega
    · rw [if_neg (by omega : ¬ col n v ≤ n)]
      omega

lemma same_class_cols {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e e' : Edge} (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hclass : G.bEdge l e = G.bEdge l e') (hnone : G.bEdge l e ≠ none) :
    col n e.tail = col n e'.tail ∧ col n (e.head n) = col n (e'.head n) := by
  cases e with
  | tree v =>
    have hv : n - l ≤ col n v ∧ col n v ≤ n + l := by
      by_contra h
      simp only [WeldedInstance.bEdge, if_neg h, ne_eq, not_true_eq_false] at hnone
    cases e' with
    | tree w =>
      have hw : n - l ≤ col n w ∧ col n w ≤ n + l := by
        by_contra h
        simp only [WeldedInstance.bEdge, if_pos hv, if_neg h, reduceCtorEq] at hclass
      have hc : col n v = col n w := by
        have hboth : col n v = col n w ∧ G.color (.tree v) = G.color (.tree w) := by
          simpa only [WeldedInstance.bEdge, if_pos hv, if_pos hw,
            Option.some.injEq, EdgeClass.tr.injEq] using hclass
        exact hboth.1
      refine ⟨hc, ?_⟩
      rw [tree_head_col he, tree_head_col he', hc]
    | weld u w => simp [WeldedInstance.bEdge, hv] at hclass
  | weld u w =>
    cases e' with
    | tree v =>
      simp only [WeldedInstance.bEdge] at hclass
      split at hclass <;> simp_all
    | weld u' w' =>
      have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
      have hw' := hG.1.1 (u', w') (weld_mem_iff.mp he')
      dsimp only at hw hw'
      simp only [Edge.tail, Edge.head]
      exact ⟨by omega, by omega⟩

end WeldedPath.LoopProof

end

-- Solutions.WeldedPathCrossingExclusion
section

namespace WeldedPath.Supplement.CrossingExclusion

open WeldedInstance InjDb
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma reachable_preserves {X : Type*} {J : SimpleGraph X} (P : X → Prop)
    (h : ∀ u v, J.Adj u v → (P u ↔ P v)) {u v : X} (hr : J.Reachable u v) :
    P u ↔ P v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons huv _ ih => exact (h _ _ huv).trans ih

lemma edge_adj (H : AbsForest n) (hH : H.IsValid) {p : Fin H.k × Fin H.k}
    (hp : p ∈ H.E) : H.graph.Adj p.1 p.2 := by
  exact ⟨ne_of_lt (hH.1 p hp), Or.inl hp⟩

lemma comp_root_exists (H : AbsForest n) (u : Fin H.k) :
    ∃ s, H.IsCompRoot s ∧ H.graph.Reachable s u := by
  classical
  have hu : u ∈ H.comp u := by simp [AbsForest.comp]
  let s := (H.comp u).min' ⟨u, hu⟩
  have hs : H.graph.Reachable u s := (Finset.mem_filter.mp
    (Finset.min'_mem (H.comp u) ⟨u, hu⟩)).2
  refine ⟨s, ?_, hs.symm⟩
  intro v hv
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.trans hv⟩)

lemma edge_kappa_ne_zero (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0)
    {p : Fin H.k × Fin H.k} (hp : p ∈ H.E) :
    kappa l G (H.color p) (ϕ p.1).1 (ϕ p.2).1 ≠ 0 := by
  classical
  obtain ⟨s, hs, hsu⟩ := comp_root_exists H p.1
  have hsu' : p.1 ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsu⟩
  have hsv : p.2 ∈ H.comp s := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hsu.trans (edge_adj H hH hp).reachable⟩
  have hcard : (H.comp s).card ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have h1 : p.1 = a := by simpa only [ha, Finset.mem_singleton] using hsu'
    have h2 : p.2 = a := by simpa only [ha, Finset.mem_singleton] using hsv
    have heq : p.1 = p.2 := h1.trans h2.symm
    exact (ne_of_lt (hH.1 p hp)) heq
  have hc : H.muComp l G s ϕ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hmu) s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  unfold AbsForest.muComp at hc
  dsimp only at hc
  rw [if_neg hcard] at hc
  split at hc
  · have hw := (mul_ne_zero_iff.mp hc).2
    exact (Finset.prod_ne_zero_iff.mp hw) p (Finset.mem_filter.mpr ⟨hp, hsu'⟩)
  · exact False.elim (hc rfl)

lemma permData_orientation {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (h : permData l G u α = some ⟨b, e, t⟩) :
    (t = true → u = e.1.tail) ∧ (t = false → u = e.1.head n) := by
  classical
  unfold permData at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases h
        rename_i e' he' hh
        have hi := (Classical.choose_spec hh.2).2.2
        constructor
        · intro ht
          simpa using ht
        · intro ht
          have hnt : u ≠ e'.tail := by simpa using ht
          exact hi.resolve_left hnt
      · simp at h

lemma class_pair_half (hG : G.IsValid) {e e' : Edge}
    (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hc : G.bEdge l e = G.bEdge l e') (hne : G.bEdge l e ≠ none) :
    IsVertex n e.tail ∧ IsVertex n (e'.head n) ∧
      ((col n e.tail ≤ n ↔ col n (e'.head n) ≤ n) ∨
        (e.tail ∈ Vweld n ∧ e'.head n ∈ Vweld n)) := by
  have hends := LoopProof.edge_endpoints hG he
  have hends' := LoopProof.edge_endpoints hG he'
  have hcols := LoopProof.same_class_cols hG he he' hc hne
  refine ⟨hends.1, hends'.2.1, ?_⟩
  cases e with
  | tree v =>
    left
    rw [← hcols.2, LoopProof.tree_head_col he]
    simp only [Edge.tail]
    split <;> omega
  | weld u w =>
    right
    have hw := hG.1.1 (u, w) (LoopProof.weld_mem_iff.mp he)
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw.1, Or.inl hw.2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hends'.2.1,
        Or.inr (by simpa only [Edge.head] using hcols.2.symm.trans hw.2.2.2)⟩

lemma kappa_half (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) :
    (col n u ≤ n ↔ col n v ≤ n) ∨ (u ∈ Vweld n ∧ v ∈ Vweld n) := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hor := permData_orientation hpd
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (fun g => g.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    have he := Finset.mem_filter.mp e.2
    rcases hm with ⟨ht, hv⟩ | ⟨ht, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.1 ht]
      exact (class_pair_half hG he.1 he'.1 (he.2.trans he'.2.symm)
        (by simp [he.2])).2.2
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.2 ht]
      rcases (class_pair_half hG he'.1 he.1 (he'.2.trans he.2.symm)
        (by simp [he'.2])).2.2 with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm

lemma tree_reachable_half (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0) {u v : Fin H.k}
    (hr : (H.treeGraph ϕ).Reachable u v) :
    col n (ϕ u).1 ≤ n ↔ col n (ϕ v).1 ≤ n := by
  apply reachable_preserves (fun u => col n (ϕ u).1 ≤ n) _ hr
  intro a b hab
  rcases hab.2 with ⟨he, hn⟩ | ⟨he, hn⟩
  · exact (kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn
  · exact ((kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn).symm

lemma recorded_adj_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) {I : Db l G} (hI : H.IsDbOf l G ϕ I)
    {a c : ℕ} (hac : (recordedGraph l G I.2).Adj a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
  have one : ∀ a c, (∃ (b : PClass n l) (j j' : Fin (classSize l G b)),
      I.2 b j = some j' ∧ a = ((edgeIdx l G b).symm j).1.tail ∧
      c = ((edgeIdx l G b).symm j').1.head n) →
      ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
    rintro a c ⟨b, j, j', hj, rfl, rfl⟩
    obtain ⟨p, hp, h⟩ := (hI.2 b j j').mp hj
    dsimp only at h
    rcases h with h | h
    · exact ⟨p.1, p.2, h.2.2.1, h.2.2.2, edge_adj H hH hp⟩
    · exact ⟨p.2, p.1, h.2.2.1, h.2.2.2, (edge_adj H hH hp).symm⟩
  rcases hac.2 with h | h
  · exact one _ _ h
  · obtain ⟨u, v, hu, hv, huv⟩ := one _ _ h
    exact ⟨v, u, hv, hu, huv.symm⟩

lemma recorded_reachable_lift_from (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ}
    (hac : (recordedGraph l G I.2).Reachable a c)
    (u : Fin H.k) (hu : (ϕ u).1 = a) :
    ∃ v, (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  induction w generalizing u with
  | nil => exact ⟨u, hu, .refl _⟩
  | cons hab w ih =>
    obtain ⟨x, y, hx, hy, hxy⟩ := recorded_adj_lift H hH ϕ hI hab
    have hux : u = x := hinj (Fin.ext (hu.trans hx.symm))
    obtain ⟨v, hv, hyv⟩ := ih y hy
    subst x
    exact ⟨v, hv, hxy.reachable.trans hyv⟩

lemma recorded_reachable_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ} (hne : a ≠ c)
    (hac : (recordedGraph l G I.2).Reachable a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons hab w =>
    obtain ⟨u, y, hu, hy, huy⟩ := recorded_adj_lift H hH ϕ hI hab
    obtain ⟨v, hv, hyv⟩ := recorded_reachable_lift_from H hH ϕ hinj hI w.reachable y hy
    exact ⟨u, v, hu, hv, huy.reachable.trans hyv⟩

lemma good_database_not_crossing (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    (D : Description n) (hD : D.IsValid) (ϕ : Fin D.H.k → Label n)
    (hg : D.IsGood l G (Vbd n l) ϕ) (I : Db l G) (hI : D.H.IsDbOf l G ϕ I) :
    ¬ HasCrossing l G I.2 := by
  classical
  rintro ⟨a, c, ha, hacol, hc, hccol, hr⟩
  have hne : a ≠ c := by intro h; subst c; omega
  obtain ⟨u, v, hu, hv, huv⟩ := recorded_reachable_lift D.H hD.1 ϕ hg.2.2.2 hI hne hr
  obtain ⟨s, hs, _⟩ := hD.2 u
  have hsu := hs.2.symm
  have hsv := hsu.trans huv
  have hub : (ϕ u).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hu] using Finset.mem_range.mpr ha,
      Or.inl (by simpa only [hu] using hacol)⟩
  have hvb : (ϕ v).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hv] using Finset.mem_range.mpr hc,
      Or.inr (Or.inr (Or.inr (by simpa only [hv] using hccol)))⟩
  have hut : u ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 u hsu h hub
  have hvt : v ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 v hsv h hvb
  have htree : (D.H.treeGraph ϕ).Reachable u v :=
    (Finset.mem_filter.mp hut).2.symm.trans (Finset.mem_filter.mp hvt).2
  have hhalf := tree_reachable_half hG D.H hD.1 ϕ (ne_of_gt hg.1) htree
  rw [hu, hv, hacol, hccol] at hhalf
  omega

end WeldedPath.Supplement.CrossingExclusion

end

-- Solutions.WeldedPathExitDegree
section

namespace WeldedPath.LoopProof

open WeldedInstance

lemma exit_col (n : ℕ) : col n (exitIdx n) = 2 * n + 1 := by
  simp [col, exitIdx]

lemma exit_parent_none (n : ℕ) : parent n (exitIdx n) = none := by
  have h1 : ¬ (IsVertex n (exitIdx n) ∧ 1 ≤ col n (exitIdx n) ∧
      col n (exitIdx n) ≤ n) := by rw [exit_col]; omega
  have h2 : ¬ (IsVertex n (exitIdx n) ∧ n + 1 ≤ col n (exitIdx n) ∧
      col n (exitIdx n) ≤ 2 * n) := by rw [exit_col]; omega
  rw [parent, if_neg h1, if_neg h2]

lemma root_size_bounds (n : ℕ) (hn : 2 ≤ n) :
    4 ≤ 2 ^ (n + 1) ∧ 2 ^ (n + 1) + 1 < numV n := by
  have hp : 4 ≤ 2 ^ (n + 1) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨hp, ?_⟩
  unfold numV
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  omega

lemma exit_isVertex (n : ℕ) (hn : 2 ≤ n) : IsVertex n (exitIdx n) := by
  have h := root_size_bounds n hn
  unfold IsVertex exitIdx
  omega

lemma exit_child_col (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    col n (2 ^ (n + 1) + j) = 2 * n := by
  have hp := (root_size_bounds n hn).1
  have hlt : ¬2 ^ (n + 1) + j < 2 ^ (n + 1) - 1 := by omega
  have hdiff : 2 ^ (n + 1) + j - (2 ^ (n + 1) - 1) + 1 = j + 2 := by omega
  simp only [col, hlt, if_false, hdiff]
  have hjcases : j = 0 ∨ j = 1 := by omega
  rcases hjcases with rfl | rfl <;> norm_num <;> omega

lemma exit_child_parent (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    parent n (2 ^ (n + 1) + j) = some (exitIdx n) := by
  have hv : IsVertex n (2 ^ (n + 1) + j) := by
    have h := (root_size_bounds n hn).2
    unfold IsVertex
    omega
  have hc := exit_child_col n hn j hj
  have hfirst : ¬(IsVertex n (2 ^ (n + 1) + j) ∧
      1 ≤ col n (2 ^ (n + 1) + j) ∧ col n (2 ^ (n + 1) + j) ≤ n) := by
    rw [hc]
    omega
  have hsecond : IsVertex n (2 ^ (n + 1) + j) ∧
      n + 1 ≤ col n (2 ^ (n + 1) + j) ∧ col n (2 ^ (n + 1) + j) ≤ 2 * n := by
    rw [hc]
    exact ⟨hv, by omega, le_refl _⟩
  rw [parent, if_neg hfirst, if_pos hsecond]
  simp [Nat.add_sub_cancel_left, show j / 2 = 0 by omega, exitIdx]

lemma exit_child_edge (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n)
    (j : ℕ) (hj : j ≤ 1) : Edge.tree (2 ^ (n + 1) + j) ∈ G.edges := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨2 ^ (n + 1) + j, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · have h := (root_size_bounds n hn).2
    omega
  · rw [exit_child_parent n hn j hj]
    rfl

lemma exit_child_incident (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    (Edge.tree (2 ^ (n + 1) + j)).Incident n (exitIdx n) := by
  right
  simp [Edge.head, exit_child_parent n hn j hj]

lemma exit_child_bEdge (n l : ℕ) (hn : 2 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (j : ℕ) (hj : j ≤ 1) (hn4 : 4 ≤ n) :
    G.bEdge l (.tree (2 ^ (n + 1) + j)) = none := by
  have h : ¬(n - l ≤ col n (2 ^ (n + 1) + j) ∧
      col n (2 ^ (n + 1) + j) ≤ n + l) := by
    rw [exit_child_col n hn j hj]
    omega
  rw [WeldedInstance.bEdge, if_neg h]

lemma eAlpha_of_edge {n : ℕ} (G : WeldedInstance n) (hG : G.IsProperColoring)
    (e : Edge) (he : e ∈ G.edges) (v : ℕ) (hi : e.Incident n v) :
    G.eAlpha v (G.color e) = some e := by
  classical
  unfold WeldedInstance.eAlpha
  split_ifs with h
  · congr 1
    have hs := Classical.choose_spec h
    by_contra hne
    exact hG (Classical.choose h) hs.1 e he hne ⟨v, hs.2.2, hi⟩ hs.2.1
  · exact False.elim (h ⟨e, he, rfl, hi⟩)

lemma exit_incident_cases (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n)
    (hG : G.IsValid) (e : Edge) (he : e ∈ G.edges) (hi : e.Incident n (exitIdx n)) :
    e = .tree (2 ^ (n + 1)) ∨ e = .tree (2 ^ (n + 1) + 1) := by
  classical
  cases e with
  | tree v =>
    have ht : v < numV n ∧ (parent n v).isSome := by
      simpa [WeldedInstance.edges, treeEdges, weldEdges] using he
    cases hp : parent n v with
    | none => simp [hp] at ht
    | some p =>
      have hne : v ≠ exitIdx n := by
        intro hv
        subst v
        rw [exit_parent_none] at hp
        contradiction
      have hvr : exitIdx n = p := by
        simpa [Edge.Incident, Edge.tail, Edge.head, hp, Ne.symm hne] using hi
      have hpar : parent n v = some (exitIdx n) := by simpa [hvr] using hp
      rcases parent_eq_exit_imp hpar with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | weld u w =>
    have hw : (u, w) ∈ G.weld := by
      simpa [WeldedInstance.edges, treeEdges, weldEdges] using he
    rcases hG.1.1 (u, w) hw with ⟨hu, hcu, hw', hcw⟩
    change col n u = n at hcu
    change col n w = n + 1 at hcw
    have hc := exit_col n
    rcases hi with hi | hi
    · change exitIdx n = u at hi
      rw [hi] at hc
      omega
    · change exitIdx n = w at hi
      rw [hi] at hc
      omega

lemma exit_colors_ne (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n) (hG : G.IsValid) :
    G.color (.tree (2 ^ (n + 1))) ≠ G.color (.tree (2 ^ (n + 1) + 1)) := by
  apply hG.2
    (.tree (2 ^ (n + 1))) (by simpa using exit_child_edge n hn G 0 (by omega))
    (.tree (2 ^ (n + 1) + 1)) (exit_child_edge n hn G 1 (by omega))
  · simp
  · exact ⟨exitIdx n, by simpa using exit_child_incident n hn 0 (by omega),
      exit_child_incident n hn 1 (by omega)⟩

lemma exit_neighbor (n l : ℕ) (hn : 4 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid) (π : Equiv.Perm G.edges) (α : Fin 3) :
    G.Nb l π (exitIdx n) α =
      if α = G.color (.tree (2 ^ (n + 1))) then 2 ^ (n + 1)
      else if α = G.color (.tree (2 ^ (n + 1) + 1)) then 2 ^ (n + 1) + 1
      else exitIdx n := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hv := exit_isVertex n hn2
  have hp0 := exit_child_parent n hn2 0 (by omega)
  have hp1 := exit_child_parent n hn2 1 (by omega)
  have hb0 := exit_child_bEdge n l hn2 hl G 0 (by omega) hn
  have hb1 := exit_child_bEdge n l hn2 hl G 1 (by omega) hn
  have he0 : Edge.tree (2 ^ (n + 1)) ∈ G.edges := by
    simpa using exit_child_edge n hn2 G 0 (by omega)
  have he1 := exit_child_edge n hn2 G 1 (by omega)
  have hi0 : (Edge.tree (2 ^ (n + 1))).Incident n (exitIdx n) := by
    simpa using exit_child_incident n hn2 0 (by omega)
  have hi1 := exit_child_incident n hn2 1 (by omega)
  have hne0 : exitIdx n ≠ 2 ^ (n + 1) := by
    have h := (root_size_bounds n hn2).1
    unfold exitIdx
    omega
  have hne1 : exitIdx n ≠ 2 ^ (n + 1) + 1 := by
    unfold exitIdx
    omega
  by_cases h0 : α = G.color (.tree (2 ^ (n + 1)))
  · subst α
    have ha := eAlpha_of_edge G hG.2 _ he0 _ hi0
    simp only [Nat.add_zero] at hp0 hb0
    simp [Nb, hv, ha, he0, hb0, Edge.tail, Edge.head, hp0, hne0]
  · by_cases h1 : α = G.color (.tree (2 ^ (n + 1) + 1))
    · subst α
      have ha := eAlpha_of_edge G hG.2 _ he1 _ hi1
      simp [Nb, hv, ha, he1, hb1, Edge.tail, Edge.head, hp1, hne1, h0]
    · have ha : G.eAlpha (exitIdx n) α = none := by
        unfold WeldedInstance.eAlpha
        split_ifs with h
        · obtain ⟨e, he, hc, hi⟩ := h
          rcases exit_incident_cases n hn2 G hG e he hi with rfl | rfl
          · exact False.elim (h0 hc.symm)
          · exact False.elim (h1 hc.symm)
        · rfl
      simp [Nb, hv, ha, h0, h1]

lemma exit_child_lt_label (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n + 1) + 1 < labelBound n + 1 := by
  have hp : 2 ^ (n + 2) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ] at hp
  have hb := (root_size_bounds n hn).1
  unfold labelBound
  omega

lemma exit_Fnat_ne_iff (n l : ℕ) (hn : 4 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (α : Fin 3) :
    Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠ (σ.1 (exitLabelIdx n)).val ↔
      α = G.color (.tree (2 ^ (n + 1))) ∨
      α = G.color (.tree (2 ^ (n + 1) + 1)) := by
  classical
  have hb := exit_child_lt_label n (by omega)
  have hr : exitIdx n < labelBound n + 1 := (exitLabelIdx n).isLt
  have hN : G.Nb l σ.2 (exitIdx n) α < labelBound n + 1 := by
    rw [exit_neighbor n l hn hl G hG σ.2 α]
    split_ifs <;> omega
  have hne0 : 2 ^ (n + 1) ≠ exitIdx n := by
    have hp := (root_size_bounds n (by omega)).1
    unfold exitIdx
    omega
  have hne1 : 2 ^ (n + 1) + 1 ≠ exitIdx n := by unfold exitIdx; omega
  have heq : Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
      (σ.1 (exitLabelIdx n)).val ↔ G.Nb l σ.2 (exitIdx n) α ≠ exitIdx n := by
    unfold Supplement.Fnat
    rw [dif_pos (σ.1 (exitLabelIdx n)).isLt]
    change (G.F l σ (σ.1 (exitLabelIdx n)) α).val ≠ (σ.1 (exitLabelIdx n)).val ↔ _
    unfold WeldedInstance.F
    simp only [Equiv.symm_apply_apply]
    change (if h : G.Nb l σ.2 (exitIdx n) α < labelBound n + 1 then
      σ.1 ⟨G.Nb l σ.2 (exitIdx n) α, h⟩ else σ.1 (exitLabelIdx n)).val ≠
        (σ.1 (exitLabelIdx n)).val ↔ _
    rw [dif_pos hN]
    constructor
    · intro hnot hval
      apply hnot
      have hx : (⟨G.Nb l σ.2 (exitIdx n) α, hN⟩ : Label n) = exitLabelIdx n :=
        Fin.ext hval
      rw [hx]
    · intro hnot hval
      apply hnot
      have hx := σ.1.injective (Fin.ext hval)
      exact congrArg Fin.val hx
  rw [heq, exit_neighbor n l hn hl G hG σ.2 α]
  split_ifs with h0 h1 <;> simp_all

theorem exit_degree (n l : ℕ) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) :
    (Finset.univ.filter fun α : Fin 3 =>
      Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
        (σ.1 (exitLabelIdx n)).val).card = 2 := by
  classical
  have hset : (Finset.univ.filter fun α : Fin 3 =>
      Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
        (σ.1 (exitLabelIdx n)).val) =
      {G.color (.tree (2 ^ (n + 1))), G.color (.tree (2 ^ (n + 1) + 1))} := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, exit_Fnat_ne_iff n l (by omega) hln G hG σ α]
  rw [hset]
  simp [exit_colors_ne n (by omega) G hG]

end WeldedPath.LoopProof

end

-- Solutions.WeldedPathKappaKernel
section

namespace WeldedPath.Supplement.KappaKernel

open WeldedInstance
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma kappa_nonneg (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u v : ℕ) :
    0 ≤ kappa l G α u v := by
  classical
  unfold kappa
  split <;> positivity

lemma sum_uniform_finset_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (S : Finset ℕ) (m : ℕ) (hSm : S.card ≤ m) :
    (∑ x, if f x ∈ S then 1 / (m : ℝ) else 0) ≤ 1 := by
  classical
  have hc : (Finset.univ.filter fun x => f x ∈ S).card ≤ m := by
    apply le_trans _ hSm
    exact Finset.card_le_card_of_injOn f
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun _ _ _ _ h => hf h)
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hcr : ((Finset.univ.filter fun x => f x ∈ S).card : ℝ) ≤ m := by
      exact_mod_cast hc
    calc
      _ = ((Finset.univ.filter fun x => f x ∈ S).card : ℝ) * (1 / (m : ℝ)) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (m : ℝ) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hcr (by positivity)
      _ = 1 := by field_simp

lemma kappa_row_sum_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u : ℕ) :
    (∑ x, kappa l G α u (f x)) ≤ 1 := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd]
  | some d =>
    obtain ⟨b, e, t⟩ := d
    cases t
    · simpa only [kappa, hpd, Bool.false_eq_true, false_and, true_and, false_or] using
        sum_uniform_finset_le_one f hf ((G.classEdges l b.1).image Edge.tail)
          (classSize l G b) (Finset.card_image_le)
    · simpa only [kappa, hpd, Bool.true_eq_false, false_and, true_and, or_false] using
        sum_uniform_finset_le_one f hf ((G.classEdges l b.1).image (Edge.head n))
          (classSize l G b) (Finset.card_image_le)

def classColor : EdgeClass → Fin 3
  | .tr _ α => α
  | .wld α => α

lemma bEdge_color {e : Edge} {b : EdgeClass} (he : G.bEdge l e = some b) :
    G.color e = classColor b := by
  cases e with
  | tree v =>
    simp only [WeldedInstance.bEdge] at he
    split at he
    · cases he
      rfl
    · simp at he
  | weld u v =>
    simp only [WeldedInstance.bEdge] at he
    cases he
    rfl

lemma class_color {b : PClass n l} {e e' : Edge}
    (he : e ∈ G.classEdges l b.1) (he' : e' ∈ G.classEdges l b.1) :
    G.color e = G.color e' :=
  (bEdge_color (Finset.mem_filter.mp he).2).trans
    (bEdge_color (Finset.mem_filter.mp he').2).symm

lemma eAlpha_spec {u : ℕ} {α : Fin 3} {e : Edge} (h : G.eAlpha u α = some e) :
    e ∈ G.edges ∧ G.color e = α ∧ e.Incident n u := by
  classical
  unfold WeldedInstance.eAlpha at h
  split at h
  · rename_i hh
    have hs := Classical.choose_spec hh
    cases h
    exact hs
  · simp at h

lemma permData_eAlpha {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (h : permData l G u α = some ⟨b, e, t⟩) : G.eAlpha u α = some e.1 := by
  classical
  unfold permData at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases h
        assumption
      · simp at h

lemma classData_ext {b b' : PClass n l} {e : ↥(G.classEdges l b.1)}
    {e' : ↥(G.classEdges l b'.1)} {t t' : Bool} (hb : b = b')
    (he : e.1 = e'.1) (ht : t = t') :
    (⟨b, e, t⟩ : (c : PClass n l) × ↥(G.classEdges l c.1) × Bool) = ⟨b', e', t'⟩ := by
  subst b'
  have he' : e = e' := Subtype.ext he
  subst e'
  subst t'
  rfl

lemma permData_of_class_edge (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (u : ℕ) (hu : e.1.Incident n u) :
    permData l G u (G.color e.1) = some ⟨b, e, decide (u = e.1.tail)⟩ := by
  classical
  have he := Finset.mem_filter.mp e.2
  have hv : IsVertex n u := by
    rcases hu with rfl | rfl
    · exact (LoopProof.edge_endpoints hG he.1).1
    · exact (LoopProof.edge_endpoints hG he.1).2.1
  have ha := LoopProof.eAlpha_of_edge G hG.2 e.1 he.1 u hu
  unfold permData
  simp only [if_neg (not_not.mpr hv), ha]
  split
  · rename_i hh
    have hb : Classical.choose hh.2 = b.1 :=
      Option.some.inj ((Classical.choose_spec hh.2).2.1.symm.trans he.2)
    have hb' : (⟨Classical.choose hh.2, (Classical.choose_spec hh.2).1⟩ : PClass n l) = b :=
      Subtype.ext hb
    apply congrArg some
    exact classData_ext hb' rfl rfl
  · rename_i hh
    exact False.elim (hh ⟨he.1, b.1, b.2, he.2, hu⟩)

lemma class_tail_head_ne (hG : G.IsValid) {b : PClass n l}
    (e e' : ↥(G.classEdges l b.1)) : e.1.tail ≠ e'.1.head n := by
  have he := Finset.mem_filter.mp e.2
  have he' := Finset.mem_filter.mp e'.2
  have hc := LoopProof.same_class_cols hG he.1 he'.1
    (he.2.trans he'.2.symm) (by simp [he.2])
  have hd := (LoopProof.edge_endpoints hG he.1).2.2
  intro h
  have hv := congrArg (col n) h
  omega

lemma kappa_tail (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (v : ℕ) :
    kappa l G (G.color e.1) e.1.tail v =
      if v ∈ (G.classEdges l b.1).image (Edge.head n) then
        1 / (classSize l G b : ℝ) else 0 := by
  classical
  have hp := permData_of_class_edge hG e e.1.tail (Or.inl rfl)
  simp only [kappa, hp, decide_true, true_and, Bool.true_eq_false, false_and, or_false]

lemma kappa_head (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (v : ℕ) :
    kappa l G (G.color e.1) (e.1.head n) v =
      if v ∈ (G.classEdges l b.1).image Edge.tail then
        1 / (classSize l G b : ℝ) else 0 := by
  classical
  have hp := permData_of_class_edge hG e (e.1.head n) (Or.inr rfl)
  have hn : e.1.head n ≠ e.1.tail := (class_tail_head_ne hG e e).symm
  simp only [kappa, hp, decide_eq_false hn, Bool.false_eq_true, false_and,
    true_and, false_or]

lemma kappa_between_class (hG : G.IsValid) {b : PClass n l}
    (e e' : ↥(G.classEdges l b.1)) :
    kappa l G (G.color e.1) e.1.tail (e'.1.head n) =
      kappa l G (G.color e.1) (e'.1.head n) e.1.tail := by
  classical
  have hf : kappa l G (G.color e.1) e.1.tail (e'.1.head n) =
      1 / (classSize l G b : ℝ) := by
    rw [kappa_tail hG e]
    rw [if_pos (Finset.mem_image.mpr ⟨e'.1, e'.2, rfl⟩)]
  have hr : kappa l G (G.color e.1) (e'.1.head n) e.1.tail =
      1 / (classSize l G b : ℝ) := by
    rw [class_color e.2 e'.2, kappa_head hG e']
    rw [if_pos (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)]
  exact hf.trans hr.symm

lemma kappa_symm_of_ne_zero (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) : kappa l G α u v = kappa l G α v u := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hor := CrossingExclusion.permData_orientation hpd
    have hec := (eAlpha_spec (permData_eAlpha hpd)).2.1
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (Edge.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    rw [← hec]
    rcases hm with ⟨ht, hv⟩ | ⟨ht, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      rw [hor.1 ht]
      exact kappa_between_class hG e ⟨e', he'⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      rw [hor.2 ht, class_color e.2 he']
      exact (kappa_between_class hG ⟨e', he'⟩ e).symm

lemma kappa_symm (hG : G.IsValid) (α : Fin 3) (u v : ℕ) :
    kappa l G α u v = kappa l G α v u := by
  by_cases h : kappa l G α u v = 0
  · have hr : kappa l G α v u = 0 := by
      by_contra hn
      exact hn ((kappa_symm_of_ne_zero hG hn).trans h)
    exact h.trans hr.symm
  · exact kappa_symm_of_ne_zero hG h

lemma kappa_zero_of_not_vertex_left (l : ℕ) (G : WeldedInstance n)
    (α : Fin 3) {u : ℕ} (hu : ¬ IsVertex n u) (v : ℕ) :
    kappa l G α u v = 0 := by
  classical
  simp [kappa, permData, hu]

lemma kappa_zero_of_not_vertex_right (hG : G.IsValid) (α : Fin 3)
    (u : ℕ) {v : ℕ} (hv : ¬ IsVertex n v) : kappa l G α u v = 0 := by
  rw [kappa_symm hG α u v]
  exact kappa_zero_of_not_vertex_left l G α hv u

lemma kappa_le_inv_classSize {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (hpd : permData l G u α = some ⟨b, e, t⟩) (v : ℕ) :
    kappa l G α u v ≤ 1 / (classSize l G b : ℝ) := by
  classical
  simp only [kappa, hpd]
  split
  · exact le_rfl
  · positivity

lemma kappa_column_sum_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (hG : G.IsValid) (α : Fin 3) (v : ℕ) :
    (∑ x, kappa l G α (f x) v) ≤ 1 := by
  simp_rw [kappa_symm hG α _ v]
  exact kappa_row_sum_le_one f hf l G α v

lemma kappa_label_row_sum_le_one (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u : ℕ) :
    (∑ v : Label n, kappa l G α u v.1) ≤ 1 :=
  kappa_row_sum_le_one Fin.val Fin.val_injective l G α u

lemma kappa_label_column_sum_le_one (hG : G.IsValid) (α : Fin 3) (v : ℕ) :
    (∑ u : Label n, kappa l G α u.1 v) ≤ 1 :=
  kappa_column_sum_le_one Fin.val Fin.val_injective hG α v

lemma kappa_finset_row_sum_le_one (S : Finset ℕ) (l : ℕ) (G : WeldedInstance n)
    (α : Fin 3) (u : ℕ) : (∑ v ∈ S, kappa l G α u v) ≤ 1 := by
  simpa only [Finset.sum_coe_sort] using
    kappa_row_sum_le_one (fun v : S => v.1) Subtype.val_injective l G α u

lemma kappa_finset_column_sum_le_one (S : Finset ℕ) (hG : G.IsValid)
    (α : Fin 3) (v : ℕ) : (∑ u ∈ S, kappa l G α u v) ≤ 1 := by
  calc
    _ = ∑ u ∈ S, kappa l G α v u := by
      apply Finset.sum_congr rfl
      intro u _
      exact kappa_symm hG α u v
    _ ≤ 1 := kappa_finset_row_sum_le_one S l G α v

lemma finite_kernel_point_bound {X Y : Type*} [Fintype X]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y ≤ 1) (p : X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (y : Y) :
    (∑ x, p x * K x y) ≤ M := by
  calc
    _ ≤ ∑ x, M * K x y := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (hp x) (hK x y)
    _ = M * ∑ x, K x y := (Finset.mul_sum _ _ _).symm
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (hcol y) hM
    _ = M := mul_one M

lemma finite_kernel_abs_bound {X Y : Type*} [Fintype X]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y ≤ 1) (p : X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) (y : Y) :
    |∑ x, p x * K x y| ≤ M := by
  calc
    _ ≤ ∑ x, |p x * K x y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |p x| * K x y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hK x y)]
    _ ≤ M := finite_kernel_point_bound K hK hcol (fun x => |p x|) M hM hp y

lemma finite_kernel_mass_le {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → ℝ) (hrow : ∀ x, ∑ y, K x y ≤ 1)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ y, ∑ x, p x * K x y) ≤ ∑ x, p x := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow x) (hp x)

lemma kappa_step_nonneg (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) (y : ℕ) :
    0 ≤ ∑ x : Label n, p x * kappa l G α x.1 y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (kappa_nonneg l G α x.1 y)

lemma kappa_step_mass_le (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ y : Label n, ∑ x : Label n, p x * kappa l G α x.1 y.1) ≤ ∑ x, p x :=
  finite_kernel_mass_le (fun x y : Label n => kappa l G α x.1 y.1)
    (fun x => kappa_label_row_sum_le_one l G α x.1) p hp

lemma kappa_propagates_point_bound (hG : G.IsValid) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (y : ℕ) :
    (∑ x : Label n, p x * kappa l G α x.1 y) ≤ M :=
  finite_kernel_point_bound (fun x : Label n => kappa l G α x.1)
    (fun x y => kappa_nonneg l G α x.1 y)
    (fun y => kappa_label_column_sum_le_one hG α y) p M hM hp y

lemma kappa_propagates_abs_bound (hG : G.IsValid) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) (y : ℕ) :
    |∑ x : Label n, p x * kappa l G α x.1 y| ≤ M :=
  finite_kernel_abs_bound (fun x : Label n => kappa l G α x.1)
    (fun x y => kappa_nonneg l G α x.1 y)
    (fun y => kappa_label_column_sum_le_one hG α y) p M hM hp y

end WeldedPath.Supplement.KappaKernel

end

-- Solutions.WeldedPathReferenceConditioning
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest
open Classical

variable {n : ℕ}

lemma component_edgeWeight_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (E : Finset (Fin H.k × Fin H.k)) (φ : Fin H.k → Label n) :
    0 ≤ edgeWeight E (componentKernel l G H) φ := by
  apply Finset.prod_nonneg
  intro p _
  exact KappaKernel.kappa_nonneg l G (H.color p) (φ p.1).val (φ p.2).val

lemma componentScale_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) : 0 ≤ componentScale l G H s := by
  unfold componentScale
  apply mul_nonneg
  · apply one_div_nonneg.mpr
    apply mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro φ _
    exact component_edgeWeight_nonneg l G H _ φ
  · exact one_div_nonneg.mpr (Nat.cast_nonneg _)

lemma muComp_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    0 ≤ H.muComp l G s φ := by
  rw [muComp_eq_componentCondition l G H hH s φ]
  apply mul_nonneg
  · split_ifs
    · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    · exact componentScale_nonneg l G H s
  · split_ifs
    · exact component_edgeWeight_nonneg l G H _ φ
    · exact le_rfl

lemma muRef_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ : Fin H.k → Label n) : 0 ≤ H.muRef l G φ := by
  exact Finset.prod_nonneg fun s _ => muComp_nonneg l G H hH s φ

lemma referenceScale_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) :
    0 ≤ referenceScale l G H := by
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · exact componentScale_nonneg l G H s

lemma referenceScale_pos (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ₀ : Fin H.k → Label n) (hμ : H.muRef l G φ₀ ≠ 0) :
    0 < referenceScale l G H :=
  lt_of_le_of_ne (referenceScale_nonneg l G H)
    (Ne.symm (referenceScale_ne_zero l G H hH φ₀ hμ))

/-- The unnormalized description law before removing collisions. -/
noncomputable def descriptionWeight (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (D : Description n) (φ : Fin D.H.k → Label n) : ℝ :=
  if (∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s) ∧
      (∀ s ∈ D.sel, ∀ u, D.H.graph.Reachable s u →
        u ∉ D.H.Ctree φ s → (φ u).val ∉ B)
  then D.H.muRef l G φ else 0

/-- The description law is an explicit supported edge-product law. In
particular the fixed-data event itself introduces no dependence between
branches beyond their common fixed endpoint labels. -/
theorem descriptionWeight_eq_forestWeight (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (D : Description n) (hD : D.IsValid) (φ : Fin D.H.k → Label n) :
    descriptionWeight l G B D φ = referenceScale l G D.H *
      forestWeight D.H.E (componentKernel l G D.H)
        (fun u x => referenceAllowed l D.H u x ∧ FixedData.coordinateCondition D B u x) φ := by
  unfold descriptionWeight
  simp only [FixedData.description_conditions_iff D hD B φ,
    muRef_eq_scale_forestWeight l G D.H hD.1 φ]
  unfold forestWeight
  simp only [forall_and, ite_and, mul_ite, mul_zero]
  split_ifs <;> rfl

/-- The only remaining restriction between the supported description law
and the good-assignment law is the injectivity (collision-free) mask. -/
theorem good_weight_eq_injective_mask (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (D : Description n) (hD : D.IsValid) (φ : Fin D.H.k → Label n) :
    (if D.IsGood l G B φ then D.H.muRef l G φ else 0) =
      if Function.Injective φ then descriptionWeight l G B D φ else 0 := by
  have hnonneg := muRef_nonneg l G D.H hD.1 φ
  by_cases hμ : 0 < D.H.muRef l G φ
  · simp only [FixedData.isGood_iff_coordinateCondition l G D hD B φ,
      descriptionWeight, FixedData.description_conditions_iff D hD B φ, hμ, true_and]
    split_ifs <;> simp_all
  · have hzero : D.H.muRef l G φ = 0 := le_antisymm (le_of_not_gt hμ) hnonneg
    simp [hzero, descriptionWeight]

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathWeightedCoefficients
section

namespace WeldedPath.WeightedCoefficients

open scoped BigOperators
open HilbertSupport

variable {Ω D ι : Type*} [Fintype Ω] [Fintype ι]

/-- The coordinate subspace supported on an event. -/
def eventSpace (P : Ω → Prop) : Submodule ℂ (Hil Ω) where
  carrier := {f | ∀ ω, ¬ P ω → f ω = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg ω hω; simp [hf ω hω, hg ω hω]
  smul_mem' := by intro c f hf ω hω; simp [hf ω hω]

/-- The finite coordinate mask really is the orthogonal event projection. -/
theorem eventSpace_projection [DecidableEq Ω] (P : Ω → Prop) [DecidablePred P]
    (f : Hil Ω) : (eventSpace P).starProjection f = diagProj P f := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · intro ω hω
    simp [diagProj_apply, hω]
  · intro g hg
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hω : P ω
    · simp [diagProj_apply, hω]
    · simp [diagProj_apply, hω, hg ω hω]

theorem eventSpace_orthogonal [DecidableEq Ω] (P : Ω → Prop) :
    (eventSpace P)ᗮ = eventSpace (fun ω => ¬ P ω) := by
  classical
  ext f
  rw [← (eventSpace P).starProjection_apply_eq_zero_iff, eventSpace_projection,
    diagProj_zero_iff]
  change (∀ ω, P ω → f ω = 0) ↔ (∀ ω, ¬ ¬ P ω → f ω = 0)
  simp only [not_not]

/-- A union bound on squared coordinate-projection norms, valid for arbitrary amplitudes. -/
theorem event_union_norm_sq [DecidableEq Ω] (P : ι → Ω → Prop) (f : Hil Ω) :
    ‖(eventSpace (fun ω => ∃ i, P i ω)).starProjection f‖ ^ 2 ≤
      ∑ i, ‖(eventSpace (P i)).starProjection f‖ ^ 2 := by
  classical
  simp only [eventSpace_projection, EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : ∃ i, P i ω
  · obtain ⟨i, hi⟩ := hω
    simp only [diagProj_apply, if_pos (show ∃ j, P j ω from ⟨i, hi⟩)]
    calc
      ‖f ω‖ ^ 2 = ‖if P i ω then f ω else 0‖ ^ 2 := by rw [if_pos hi]
      _ ≤ ∑ j, ‖if P j ω then f ω else 0‖ ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg ‖if P j ω then f ω else 0‖)
          (Finset.mem_univ i)
  · simp only [diagProj_apply, if_neg hω, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Lift a coefficient function into the Hilbert space with square-root density. -/
noncomputable def lift (μ : Ω → ℝ) (f : Ω → ℂ) : Hil Ω :=
  WithLp.toLp 2 (fun ω => (Real.sqrt (μ ω) : ℂ) * f ω)

theorem lift_norm_sq (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (f : Ω → ℂ) :
    ‖lift μ f‖ ^ 2 = ∑ ω, μ ω * ‖f ω‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ω _
  change ‖(Real.sqrt (μ ω) : ℂ) * f ω‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hμ ω)]

theorem masked_lift_norm_sq [DecidableEq Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℂ) :
    ‖(eventSpace P).starProjection (lift μ f)‖ ^ 2 =
      ∑ ω, (if P ω then μ ω else 0) * ‖f ω‖ ^ 2 := by
  rw [eventSpace_projection, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : P ω
  · simp only [diagProj_apply, if_pos hω]
    change ‖(Real.sqrt (μ ω) : ℂ) * f ω‖ ^ 2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hμ ω)]
  · simp [diagProj_apply, hω]

theorem sum_by_data {R : Type*} [CommSemiring R] [DecidableEq D]
    (μ : Ω → R) (data : Ω → D) (h : D → R) :
    (∑ ω, μ ω * h (data ω)) =
      ∑ d ∈ Finset.univ.image data, h d * ∑ ω, if data ω = d then μ ω else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [mul_ite, mul_comm, Finset.mem_image_of_mem data (Finset.mem_univ ω)]

/-- Conditional probability bounds control the energy of every coefficient
function measurable with respect to the fixed data, including arbitrary phases. -/
theorem conditional_event_bound [DecidableEq Ω] [DecidableEq D]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (data : Ω → D)
    (P : Ω → Prop) [DecidablePred P] (ε : ℝ)
    (hbound : ∀ d, (∑ ω, if data ω = d ∧ P ω then μ ω else 0) ≤
      ε * ∑ ω, if data ω = d then μ ω else 0)
    (h : D → ℂ) :
    ‖(eventSpace P).starProjection (lift μ (h ∘ data))‖ ^ 2 ≤
      ε * ‖lift μ (h ∘ data)‖ ^ 2 := by
  rw [masked_lift_norm_sq μ hμ, lift_norm_sq μ hμ]
  simp only [Function.comp_apply]
  rw [sum_by_data (fun ω => if P ω then μ ω else 0) data (fun d => ‖h d‖ ^ 2),
    sum_by_data μ data (fun d => ‖h d‖ ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have he : (∑ ω, if data ω = d then (if P ω then μ ω else 0) else 0) =
      ∑ ω, if data ω = d ∧ P ω then μ ω else 0 := by
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp_all
  rw [he]
  calc
    _ ≤ ‖h d‖ ^ 2 * (ε * ∑ ω, if data ω = d then μ ω else 0) :=
      mul_le_mul_of_nonneg_left (hbound d) (sq_nonneg _)
    _ = _ := by ring

end WeldedPath.WeightedCoefficients

end

-- Solutions.WeldedPathDescriptionAmplitude
section

namespace WeldedPath.Supplement.DescriptionCoefficients

open Classical ForestFactorization
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n : ℕ}

noncomputable def amplitude (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) :
    Hil (Fin H.k → Label n) :=
  WithLp.toLp 2 (fun φ => (Real.sqrt (descriptionWeight l G B ⟨H, sel, φ₀⟩ φ) : ℂ))

def descriptionGenerators (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (B : Finset ℕ) :
    Set (Hil (Fin H.k → Label n)) :=
  {f | ∃ sel φ₀, (Description.mk H sel φ₀).IsValid ∧ f = amplitude l G H B sel φ₀}

noncomputable def descriptionSpan (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) : Submodule ℂ (Hil (Fin H.k → Label n)) :=
  Submodule.span ℂ (descriptionGenerators l G H B)

theorem amplitude_injective_projection (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) :
    (eventSpace Function.Injective).starProjection (amplitude l G H B sel φ₀) =
      WithLp.toLp 2 (fun φ => if (Description.mk H sel φ₀).IsGood l G B φ then
        (Real.sqrt (H.muRef l G φ) : ℂ) else 0) := by
  ext φ
  rw [eventSpace_projection, diagProj_apply]
  change (if Function.Injective φ then
    (Real.sqrt (descriptionWeight l G B ⟨H, sel, φ₀⟩ φ) : ℂ) else 0) = _
  have hh := good_weight_eq_injective_mask l G B (Description.mk H sel φ₀) hD φ
  have he := congrArg (fun x : ℝ => (Real.sqrt x : ℂ)) hh
  by_cases hg : (Description.mk H sel φ₀).IsGood l G B φ <;>
    by_cases hi : Function.Injective φ <;>
    simpa only [hg, hi, if_true, if_false, Real.sqrt_zero, Complex.ofReal_zero] using he.symm

end WeldedPath.Supplement.DescriptionCoefficients

end

-- Solutions.WeldedPathDisconnectedPairs
section
namespace WeldedPath.Supplement.DisconnectedStability
open Classical DescriptionCoefficients
variable {n l : ℕ} {G : WeldedInstance n}
noncomputable abbrev coefficientSpace (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) : Submodule ℂ (Hil (Fin H.k → Label n)) :=
  descriptionSpan l G H B
end WeldedPath.Supplement.DisconnectedStability

end

-- Solutions.WeldedPathDescriptionSpan
section
namespace WeldedPath.Supplement.DescriptionCoefficients
open Classical DisconnectedStability
variable {n : ℕ}
theorem coefficientSpace_eq_descriptionSpan (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ) :
    coefficientSpace l G H B = descriptionSpan l G H B := rfl
theorem amplitude_mem_coefficientSpace (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) :
    amplitude l G H B sel φ₀ ∈ coefficientSpace l G H B :=
  Submodule.subset_span ⟨sel,φ₀,hD,rfl⟩
end WeldedPath.Supplement.DescriptionCoefficients

end

-- Solutions.WeldedPathLabelBookkeeping
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DescriptionCoefficients CompressedPrimitive InjDb
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable abbrev withLabel (H : AbsForest n) (u : Fin H.k)
    (a : Option (Fin (labelBound n))) : AbsForest n :=
  { H with lab := Function.update H.lab u a }

@[simp] lemma withLabel_self (H : AbsForest n) (u : Fin H.k)
    (a : Option (Fin (labelBound n))) : (withLabel H u a).lab u = a :=
  Function.update_self _ _ _

@[simp] lemma withLabel_other (H : AbsForest n) (u v : Fin H.k)
    (a : Option (Fin (labelBound n))) (hvu : v ≠ u) :
    (withLabel H u a).lab v = H.lab v := Function.update_of_ne hvu _ _

theorem insert_valid (H : AbsForest n) (hH : H.IsValid) (u : Fin H.k)
    (a : Fin (labelBound n)) (hfresh : ∀ v, H.lab v ≠ some a) :
    (withLabel H u (some a)).IsValid := by
  refine ⟨hH.1, hH.2.1, hH.2.2.1, ?_, ?_⟩
  · intro v w j hv hw
    by_cases hvu : v = u
    · subst v
      have haj : a = j := Option.some.inj ((withLabel_self H u (some a)).symm.trans hv)
      by_cases hwu : w = u
      · exact hwu.symm
      · have hw' : H.lab w = some a := by
          rw [haj]
          exact (withLabel_other H u w _ hwu).symm.trans hw
        exact (hfresh w hw').elim
    · by_cases hwu : w = u
      · subst w
        have haj : a = j := Option.some.inj ((withLabel_self H u (some a)).symm.trans hw)
        have hv' : H.lab v = some a := by
          rw [haj]
          exact (withLabel_other H u v _ hvu).symm.trans hv
        exact (hfresh v hv').elim
      · exact hH.2.2.2.1 v w j
          ((withLabel_other H u v _ hvu).symm.trans hv)
          ((withLabel_other H u w _ hwu).symm.trans hw)
  · intro v
    by_cases hvu : v = u
    · subst v
      exact Or.inl (by simp only [Function.update_self, Option.isSome_some])
    · rcases hH.2.2.2.2 v with hv | hv
      · exact Or.inl (by simpa only [Function.update_of_ne hvu] using hv)
      · exact Or.inr hv

theorem erase_valid (H : AbsForest n) (hH : H.IsValid) (u : Fin H.k)
    (hu : ∃ e ∈ H.E, e.1 = u ∨ e.2 = u) : (withLabel H u none).IsValid := by
  refine ⟨hH.1, hH.2.1, hH.2.2.1, ?_, ?_⟩
  · intro v w j hv hw
    have hvu : v ≠ u := by
      intro h
      subst v
      have hn := (withLabel_self H u none).symm.trans hv
      cases hn
    have hwu : w ≠ u := by
      intro h
      subst w
      have hn := (withLabel_self H u none).symm.trans hw
      cases hn
    exact hH.2.2.2.1 v w j
      ((withLabel_other H u v _ hvu).symm.trans hv)
      ((withLabel_other H u w _ hwu).symm.trans hw)
  · intro v
    by_cases hvu : v = u
    · subst v; exact Or.inr hu
    · rcases hH.2.2.2.2 v with hv | hv
      · exact Or.inl (by simpa only [Function.update_of_ne hvu] using hv)
      · exact Or.inr hv

@[simp] theorem muRef_withLabel (H : AbsForest n) (u : Fin H.k)
    (a : Option (Fin (labelBound n))) (φ : Fin H.k → Label n) :
    (withLabel H u a).muRef l G φ = H.muRef l G φ := rfl

@[simp] theorem wfix_withLabel (H : AbsForest n) (u : Fin H.k)
    (a : Option (Fin (labelBound n))) (φ : Fin H.k → Label n) (v : Fin H.k) :
    (withLabel H u a).Wfix φ v = H.Wfix φ v := rfl

theorem amplitude_withLabel (H : AbsForest n) (u : Fin H.k)
    (a : Option (Fin (labelBound n))) (B : Finset ℕ) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) :
    amplitude l G (withLabel H u a) B sel φ₀ = amplitude l G H B sel φ₀ := rfl

theorem description_valid_withLabel (H : AbsForest n) (u : Fin H.k)
    (a : Option (Fin (labelBound n))) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) (hnew : (withLabel H u a).IsValid) :
    (Description.mk (withLabel H u a) sel φ₀).IsValid := ⟨hnew, hD.2⟩

theorem insert_records (H : AbsForest n) (u : Fin H.k)
    (a : Fin (labelBound n)) (hu : H.lab u = none) :
    (withLabel H u (some a)).records = H.records + 1 := by
  have hs : (Finset.univ.filter (fun v => ((withLabel H u (some a)).lab v).isSome)) =
      insert u (Finset.univ.filter (fun v => (H.lab v).isSome)) := by
    ext v
    by_cases hv : v = u
    · subst v; simp only [Finset.mem_filter, Finset.mem_univ, Function.update_self,
        Option.isSome_some, Bool.true_eq, and_self, Finset.mem_insert, true_or]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Function.update_of_ne hv, hv, false_or]
  have hn : u ∉ Finset.univ.filter (fun v => (H.lab v).isSome) := by simp [hu]
  unfold AbsForest.records
  rw [hs, Finset.card_insert_of_notMem hn]
  change H.E.card + (_ + 1) = H.E.card + _ + 1
  omega

theorem erase_records (H : AbsForest n) (u : Fin H.k)
    (a : Fin (labelBound n)) (hu : H.lab u = some a) :
    (withLabel H u none).records + 1 = H.records := by
  have hs : (Finset.univ.filter (fun v => ((withLabel H u none).lab v).isSome)) =
      (Finset.univ.filter (fun v => (H.lab v).isSome)).erase u := by
    ext v
    by_cases hv : v = u
    · subst v; simp only [Finset.mem_filter, Finset.mem_univ, Function.update_self,
        Option.isSome_none, Bool.false_eq_true, and_false, Finset.mem_erase, ne_eq, not_true_eq_false,
        false_and]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Function.update_of_ne hv, ne_eq, hv, not_false_eq_true]
  have hm : u ∈ Finset.univ.filter (fun v => (H.lab v).isSome) := by simp [hu]
  have hc := Finset.card_erase_add_one hm
  unfold AbsForest.records
  rw [hs]
  change H.E.card + _ + 1 = H.E.card + _
  omega

lemma vertex_ne_of_index_ne (H : AbsForest n) (φ : Fin H.k → Label n)
    (u v : Fin H.k) (x i : Fin (labelBound n)) (hx : (φ u).val = x.val + 1)
    (hi : (φ v).val = i.val + 1) (hix : i ≠ x) : v ≠ u := by
  intro h
  subst v
  exact hix (Fin.ext (Nat.add_right_cancel (hi.symm.trans hx)))

theorem label_db_unset (H : AbsForest n) (φ : Fin H.k → Label n)
    (hφ : Function.Injective φ) (I : Db l G) (hI : H.IsDbOf l G φ I)
    (u : Fin H.k) (x : Fin (labelBound n)) (hx : (φ u).val = x.val + 1)
    (hu : H.lab u = none) : I.1 x = none := by
  cases hh : I.1 x with
  | none => rfl
  | some j =>
    obtain ⟨v, hv, hvj⟩ := (hI.1 x j).mp hh
    have hvu := hφ (Fin.ext (hv.trans hx.symm))
    subst v
    rw [hu] at hvj
    cases hvj

theorem label_db_unused (H : AbsForest n) (φ : Fin H.k → Label n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (a : Fin (labelBound n))
    (ha : ∀ v, H.lab v ≠ some a) : I.1.symm a = none := by
  cases hh : I.1.symm a with
  | none => rfl
  | some x =>
    have hx := (I.1.inv x a).mp hh
    obtain ⟨v, _, hva⟩ := (hI.1 x a).mp hx
    exact (ha v hva).elim

theorem isDbOf_insertLabel (H : AbsForest n) (φ : Fin H.k → Label n)
    (hφ : Function.Injective φ) (I : Db l G) (hI : H.IsDbOf l G φ I)
    (u : Fin H.k) (x a : Fin (labelBound n)) (hx : (φ u).val = x.val + 1)
    (hu : H.lab u = none) (ha : ∀ v, H.lab v ≠ some a) :
    (withLabel H u (some a)).IsDbOf l G φ (I.1.addPair x a, I.2) := by
  have hdom := label_db_unset H φ hφ I hI u x hx hu
  have him := label_db_unused H φ I hI a ha
  refine ⟨?_, hI.2⟩
  intro i j
  by_cases hix : i = x
  · subst i
    rw [addPair_apply_self _ x a hdom him]
    constructor
    · intro haj
      exact ⟨u, hx, (withLabel_self H u (some a)).trans haj⟩
    · rintro ⟨v, hv, hvj⟩
      have hvu := hφ (Fin.ext (hv.trans hx.symm))
      subst v
      exact (withLabel_self H u (some a)).symm.trans hvj
  · rw [addPair_apply_other _ x a i hdom him hix, hI.1]
    constructor
    · rintro ⟨v, hv, hvj⟩
      exact ⟨v, hv, (withLabel_other H u v _ (vertex_ne_of_index_ne H φ u v x i hx hv hix)).trans hvj⟩
    · rintro ⟨v, hv, hvj⟩
      exact ⟨v, hv, (withLabel_other H u v _ (vertex_ne_of_index_ne H φ u v x i hx hv hix)).symm.trans hvj⟩

theorem isDbOf_eraseLabel (H : AbsForest n) (φ : Fin H.k → Label n)
    (hφ : Function.Injective φ) (I : Db l G) (hI : H.IsDbOf l G φ I)
    (u : Fin H.k) (x : Fin (labelBound n)) (hx : (φ u).val = x.val + 1) :
    (withLabel H u none).IsDbOf l G φ (eraseAt I.1 x, I.2) := by
  refine ⟨?_, hI.2⟩
  intro i j
  by_cases hix : i = x
  · subst i
    rw [eraseAt_self]
    constructor
    · intro h; cases h
    · rintro ⟨v, hv, hvj⟩
      have hvu := hφ (Fin.ext (hv.trans hx.symm))
      subst v
      rw [withLabel_self] at hvj
      cases hvj
  · rw [eraseAt_apply, if_neg hix, hI.1]
    constructor
    · rintro ⟨v, hv, hvj⟩
      exact ⟨v, hv, (withLabel_other H u v _ (vertex_ne_of_index_ne H φ u v x i hx hv hix)).trans hvj⟩
    · rintro ⟨v, hv, hvj⟩
      exact ⟨v, hv, (withLabel_other H u v _ (vertex_ne_of_index_ne H φ u v x i hx hv hix)).symm.trans hvj⟩

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathWeldClasses
section

namespace WeldedPath.WeldClasses

open Classical LoopProof

theorem mem_weld_class {n l : ℕ} {G : WeldedInstance n} (α : Fin 3) (e : Edge) :
    e ∈ G.classEdges l (.wld α) ↔ e ∈ G.weldEdges ∧ G.color e = α := by
  cases e with
  | tree v =>
    by_cases h : n - l ≤ col n v ∧ col n v ≤ n + l <;>
      simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.weldEdges, h]
  | weld u w =>
    simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.edges,
      WeldedInstance.treeEdges, WeldedInstance.weldEdges]

theorem weld_classes_disjoint {n l : ℕ} (G : WeldedInstance n) {α β : Fin 3}
    (h : α ≠ β) : Disjoint (G.classEdges l (.wld α)) (G.classEdges l (.wld β)) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact h (((mem_weld_class α e).mp he).2.symm.trans ((mem_weld_class β e).mp he').2)

theorem tail_injective {n l : ℕ} {G : WeldedInstance n} (hG : G.IsProperColoring)
    (α : Fin 3) : Set.InjOn Edge.tail (G.classEdges l (.wld α)) := by
  intro e he e' he' htail
  by_contra hne
  have hc := hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.tail, Or.inl rfl, Or.inl htail⟩
  exact hc (((mem_weld_class α e).mp he).2.trans ((mem_weld_class α e').mp he').2.symm)

theorem head_injective {n l : ℕ} {G : WeldedInstance n} (hG : G.IsProperColoring)
    (α : Fin 3) : Set.InjOn (Edge.head n) (G.classEdges l (.wld α)) := by
  intro e he e' he' hhead
  by_contra hne
  have hc := hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.head n, Or.inr rfl, Or.inr hhead⟩
  exact hc (((mem_weld_class α e).mp he).2.trans ((mem_weld_class α e').mp he').2.symm)

theorem left_leaf_bounds {n v : ℕ} (hv : IsVertex n v) (hc : col n v = n) :
    2 ^ n - 1 ≤ v ∧ v < 2 ^ (n + 1) - 1 := by
  have hleft : v < 2 ^ (n + 1) - 1 := by
    by_contra h
    have hh := col_right_ge n v hv (by omega)
    omega
  have hlog : Nat.log 2 (v + 1) = n := by simpa [col, hleft] using hc
  have hh := Nat.pow_log_le_self 2 (by omega : v + 1 ≠ 0)
  rw [hlog] at hh
  exact ⟨by omega, hleft⟩

theorem left_leaf_of_bounds {n v : ℕ} (hn : 1 ≤ n)
    (hlo : 2 ^ n - 1 ≤ v) (hhi : v < 2 ^ (n + 1) - 1) :
    IsVertex n v ∧ col n v = n ∧ parent n v = some ((v - 1) / 2) := by
  have hpow := Nat.two_pow_pos n
  have hroot := pow_root_ge_two n
  have hv : IsVertex n v := by
    rw [IsVertex, numV_eq]
    omega
  have hc : col n v = n := by
    rw [col, if_pos hhi]
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  refine ⟨hv, hc, ?_⟩
  simp [parent, hv, hc, hn]

theorem weld_class_tail_bounds {n l : ℕ} {G : WeldedInstance n} (hG : G.IsWeld)
    {α : Fin 3} {e : Edge} (he : e ∈ G.classEdges l (.wld α)) :
    2 ^ n - 1 ≤ e.tail ∧ e.tail < 2 ^ (n + 1) - 1 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ((mem_weld_class α e).mp he).1
  have hh := hG.1 p hp
  exact left_leaf_bounds hh.1 hh.2.1

theorem weld_class_card_le {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (α : Fin 3) : (G.classEdges l (.wld α)).card ≤ 2 ^ n := by
  have hh := Finset.card_le_card_of_injOn Edge.tail
    (s := G.classEdges l (.wld α)) (t := Finset.Ico (2 ^ n - 1) (2 ^ (n + 1) - 1))
    (fun e he => Finset.mem_Ico.mpr (weld_class_tail_bounds hG.1 he))
    (tail_injective hG.2 α)
  have hp := Nat.two_pow_pos n
  have hcard : (Finset.Ico (2 ^ n - 1) (2 ^ (n + 1) - 1)).card = 2 ^ n := by
    rw [Nat.card_Ico, pow_succ]
    omega
  simpa only [hcard] using hh

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem weld_color_at_leaf {n l v : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (hv : IsVertex n v) (hc : col n v = n) (α : Fin 3)
    (htc : G.color (.tree v) ≠ α) :
    ∃ e ∈ G.classEdges l (.wld α), e.tail = v := by
  have hbounds := left_leaf_bounds hv hc
  have hpv := (left_leaf_of_bounds hn hbounds.1 hbounds.2).2.2
  have ht : Edge.tree v ∈ G.edges := tree_mem_iff.mpr ⟨hv, by simp [hpv]⟩
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp (hG.1.2.1 v ⟨hv, Or.inl hc⟩)
  have hp : p ∈ G.weld ∧ (p.1 = v ∨ p.2 = v) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hq : q ∈ G.weld ∧ (q.1 = v ∨ q.2 = v) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hpt : p.1 = v := by
    rcases hp.2 with h | h
    · exact h
    · have hh := (hG.1.1 p hp.1).2.2.2
      rw [h, hc] at hh
      omega
  have hqt : q.1 = v := by
    rcases hq.2 with h | h
    · exact h
    · have hh := (hG.1.1 q hq.1).2.2.2
      rw [h, hc] at hh
      omega
  have hep : Edge.weld p.1 p.2 ∈ G.edges := weld_mem_iff.mpr hp.1
  have heq : Edge.weld q.1 q.2 ∈ G.edges := weld_mem_iff.mpr hq.1
  have htp := hG.2 (.tree v) ht (.weld p.1 p.2) hep (by simp)
    ⟨v, Or.inl rfl, Or.inl hpt.symm⟩
  have htq := hG.2 (.tree v) ht (.weld q.1 q.2) heq (by simp)
    ⟨v, Or.inl rfl, Or.inl hqt.symm⟩
  have hpq' : Edge.weld p.1 p.2 ≠ Edge.weld q.1 q.2 := by
    intro h
    exact hpq (Prod.ext (congrArg Edge.tail h) (congrArg (Edge.head n) h))
  have hpqc := hG.2 (.weld p.1 p.2) hep (.weld q.1 q.2) heq hpq'
    ⟨v, Or.inl hpt.symm, Or.inl hqt.symm⟩
  rcases three_colors_cover (G.color (.tree v)) (G.color (.weld p.1 p.2))
      (G.color (.weld q.1 q.2)) α htp htq hpqc with h | h | h
  · exact (htc h.symm).elim
  · refine ⟨.weld p.1 p.2, (mem_weld_class α _).mpr ⟨?_, h.symm⟩, hpt⟩
    exact Finset.mem_image.mpr ⟨p, hp.1, rfl⟩
  · refine ⟨.weld q.1 q.2, (mem_weld_class α _).mpr ⟨?_, h.symm⟩, hqt⟩
    exact Finset.mem_image.mpr ⟨q, hq.1, rfl⟩

theorem weld_class_card_ge {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (α : Fin 3) : 2 ^ (n - 1) ≤ (G.classEdges l (.wld α)).card := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) (by omega)
      _ = 2 * 2 ^ (n - 1) := by rw [pow_succ, Nat.mul_comm]
  have hpow' : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have hpos := Nat.two_pow_pos (n - 1)
  have hpairs (j : Fin (2 ^ (n - 1))) :
      ∃ e ∈ G.classEdges l (.wld α),
        e.tail = 2 ^ n - 1 + 2 * j.val ∨ e.tail = 2 ^ n - 1 + 2 * j.val + 1 := by
    let u := 2 ^ n - 1 + 2 * j.val
    have hj := j.isLt
    have hu := left_leaf_of_bounds (v := u) hn (by dsimp [u]; omega)
      (by dsimp [u]; omega)
    have hu' := left_leaf_of_bounds (v := u + 1) hn (by dsimp [u]; omega)
      (by dsimp [u]; omega)
    have ht : Edge.tree u ∈ G.edges := tree_mem_iff.mpr ⟨hu.1, by simp [hu.2.2]⟩
    have ht' : Edge.tree (u + 1) ∈ G.edges := tree_mem_iff.mpr ⟨hu'.1, by simp [hu'.2.2]⟩
    have hparent : (u - 1) / 2 = u / 2 := by dsimp [u]; omega
    have hcolors : G.color (.tree u) ≠ G.color (.tree (u + 1)) := by
      apply hG.2 (.tree u) ht (.tree (u + 1)) ht' (by simp)
      refine ⟨(u - 1) / 2, Or.inr ?_, Or.inr ?_⟩
      · simp [Edge.head, hu.2.2]
      · simp [Edge.head, hu'.2.2, hparent]
    by_cases hcu : G.color (.tree u) ≠ α
    · obtain ⟨e, he, htail⟩ := weld_color_at_leaf hG hn hu.1 hu.2.1 α hcu
      exact ⟨e, he, Or.inl htail⟩
    · have hcu' : G.color (.tree (u + 1)) ≠ α := by
        intro h
        exact hcolors ((not_ne_iff.mp hcu).trans h.symm)
      obtain ⟨e, he, htail⟩ := weld_color_at_leaf hG hn hu'.1 hu'.2.1 α hcu'
      exact ⟨e, he, Or.inr htail⟩
  choose f hf using hpairs
  let F : Fin (2 ^ (n - 1)) → G.classEdges l (.wld α) := fun j => ⟨f j, (hf j).1⟩
  have hinj : Function.Injective F := by
    intro j k h
    have heq : f j = f k := congrArg Subtype.val h
    have ht := congrArg Edge.tail heq
    rcases (hf j).2 with hj | hj <;> rcases (hf k).2 with hk | hk <;>
      apply Fin.ext <;> omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective F hinj

theorem weld_class_card_bounds {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (α : Fin 3) :
    2 ^ (n - 1) ≤ (G.classEdges l (.wld α)).card ∧
      (G.classEdges l (.wld α)).card ≤ 2 ^ n :=
  ⟨weld_class_card_ge hG hn α, weld_class_card_le hG α⟩

end WeldedPath.WeldClasses

end

-- Solutions.WeldedPathNearWeldClasses
section

namespace WeldedPath.NearWeldClasses

open Classical LoopProof

/-- Heap coordinates in either of the two binary trees. -/
def heapNode (n : ℕ) (right : Bool) (u : ℕ) : ℕ :=
  (if right then 2 ^ (n + 1) - 1 else 0) + u

def heapCol (n : ℕ) (right : Bool) (d : ℕ) : ℕ :=
  if right then 2 * n + 1 - d else d

theorem heap_node_spec {n d u : ℕ} (right : Bool)
    (hd : 1 ≤ d) (hdn : d ≤ n)
    (hlo : 2 ^ d - 1 ≤ u) (hhi : u < 2 ^ (d + 1) - 1) :
    IsVertex n (heapNode n right u) ∧
      col n (heapNode n right u) = heapCol n right d ∧
      parent n (heapNode n right u) = some (heapNode n right ((u - 1) / 2)) := by
  have hroot := pow_root_ge_two n
  have hpow := Nat.two_pow_pos d
  have hdpow : 2 ≤ 2 ^ d := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  have hupper : u < 2 ^ (n + 1) - 1 := by
    have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2)
      (show d + 1 ≤ n + 1 by omega)
    omega
  have hlog : Nat.log 2 (u + 1) = d :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  have hup : 1 ≤ u := by omega
  cases right with
  | false =>
    simp only [heapNode, Bool.false_eq_true, if_false, zero_add, heapCol]
    have hv : IsVertex n u := by rw [IsVertex, numV_eq]; omega
    have hc : col n u = d := by simp [col, hupper, hlog]
    refine ⟨hv, hc, ?_⟩
    simp [parent, hv, hc, hd, hdn]
  | true =>
    simp only [heapNode, if_true, heapCol]
    let R := 2 ^ (n + 1) - 1
    have hv : IsVertex n (R + u) := by
      rw [IsVertex, numV_eq]
      dsimp [R]
      omega
    have hc : col n (R + u) = 2 * n + 1 - d := by
      rw [col, if_neg (by dsimp [R]; omega)]
      change 2 * n + 1 - Nat.log 2 (R + u - R + 1) = _
      rw [Nat.add_sub_cancel_left, hlog]
    refine ⟨hv, hc, ?_⟩
    have hfirst : ¬ (IsVertex n (R + u) ∧ 1 ≤ col n (R + u) ∧
        col n (R + u) ≤ n) := by rw [hc]; omega
    have hsecond : IsVertex n (R + u) ∧ n + 1 ≤ col n (R + u) ∧
        col n (R + u) ≤ 2 * n := by rw [hc]; exact ⟨hv, by omega, by omega⟩
    change parent n (R + u) = some (R + (u - 1) / 2)
    rw [parent, if_neg hfirst, if_pos hsecond]
    congr 1
    dsimp [R]
    omega

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem child_color_of_parent_ne {n : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (p a b : ℕ)
    (hp : Edge.tree p ∈ G.edges) (ha : Edge.tree a ∈ G.edges)
    (hb : Edge.tree b ∈ G.edges) (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hapar : parent n a = some p) (hbpar : parent n b = some p)
    (α : Fin 3) (hc : G.color (.tree p) ≠ α) :
    G.color (.tree a) = α ∨ G.color (.tree b) = α := by
  have hca := hG (.tree p) hp (.tree a) ha (by simpa using hpa)
    ⟨p, Or.inl rfl, Or.inr (by simp [Edge.head, hapar])⟩
  have hcb := hG (.tree p) hp (.tree b) hb (by simpa using hpb)
    ⟨p, Or.inl rfl, Or.inr (by simp [Edge.head, hbpar])⟩
  have hcab := hG (.tree a) ha (.tree b) hb (by simpa using hab)
    ⟨p, Or.inr (by simp [Edge.head, hapar]), Or.inr (by simp [Edge.head, hbpar])⟩
  rcases three_colors_cover _ _ _ α hca hcb hcab with h | h | h
  · exact (hc h.symm).elim
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem pow_two_levels {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n = 4 * 2 ^ (n - 2) ∧ 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
  constructor
  · rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    omega
  · rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    omega

theorem quad_leaf_spec {n : ℕ} (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (k : Fin 4) :
    IsVertex n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) ∧
      col n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) = heapCol n right n ∧
      parent n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) =
        some (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val / 2)) := by
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hsucc : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have hj := j.isLt
  have hk := k.isLt
  have hs := heap_node_spec (n := n) (d := n)
    (u := 2 ^ n - 1 + 4 * j.val + k.val) right (by omega) le_rfl (by omega) (by omega)
  have hdiv : (2 ^ n - 1 + 4 * j.val + k.val - 1) / 2 =
      2 ^ (n - 1) - 1 + 2 * j.val + k.val / 2 := by omega
  simpa only [hdiv] using hs

theorem quad_parent_spec {n : ℕ} (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (k : Fin 2) :
    IsVertex n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) ∧
      col n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) =
        heapCol n right (n - 1) ∧
      parent n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) =
        some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hsucc : 2 ^ ((n - 1) + 1) = 2 ^ n := congrArg (2 ^ ·) (by omega)
  have hj := j.isLt
  have hk := k.isLt
  have hs := heap_node_spec (n := n) (d := n - 1)
    (u := 2 ^ (n - 1) - 1 + 2 * j.val + k.val) right
    (by omega) (by omega) (by omega) (by omega)
  have hdiv : (2 ^ (n - 1) - 1 + 2 * j.val + k.val - 1) / 2 =
      2 ^ (n - 2) - 1 + j.val := by omega
  simpa only [hdiv] using hs

theorem leaf_quad_has_color {n : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (α : Fin 3) :
    ∃ k : Fin 4,
      G.color (.tree (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val))) = α := by
  let v (k : Fin 4) := heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)
  let p (k : Fin 2) := heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hv (k : Fin 4) : Edge.tree (v k) ∈ G.edges := by
    apply tree_mem_iff.mpr
    have hs := quad_leaf_spec hn right j k
    exact ⟨hs.1, by simp [v, hs.2.2]⟩
  have hpm (k : Fin 2) : Edge.tree (p k) ∈ G.edges := by
    apply tree_mem_iff.mpr
    have hs := quad_parent_spec hn right j k
    exact ⟨hs.1, by simp [p, hs.2.2]⟩
  have hpar0 : parent n (v 0) = some (p 0) := by
    simpa [v, p] using (quad_leaf_spec hn right j 0).2.2
  have hpar1 : parent n (v 1) = some (p 0) := by
    simpa [v, p] using (quad_leaf_spec hn right j 1).2.2
  have hpar2 : parent n (v 2) = some (p 1) := by
    simpa [v, p] using (quad_leaf_spec hn right j 2).2.2
  have hpar3 : parent n (v 3) = some (p 1) := by
    simpa [v, p] using (quad_leaf_spec hn right j 3).2.2
  have hpp0 : parent n (p 0) = some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
    simpa [p] using (quad_parent_spec hn right j 0).2.2
  have hpp1 : parent n (p 1) = some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
    simpa [p] using (quad_parent_spec hn right j 1).2.2
  have hpn : p 0 ≠ p 1 := by dsimp [p, heapNode]; omega
  have hpc : G.color (.tree (p 0)) ≠ G.color (.tree (p 1)) := by
    apply hG (.tree (p 0)) (hpm 0) (.tree (p 1)) (hpm 1) (by simpa using hpn)
    refine ⟨heapNode n right (2 ^ (n - 2) - 1 + j.val), Or.inr ?_, Or.inr ?_⟩ <;>
      simp [Edge.head, hpp0, hpp1]
  by_cases hc : G.color (.tree (p 0)) ≠ α
  · have hh := child_color_of_parent_ne hG (p 0) (v 0) (v 1) (hpm 0) (hv 0) (hv 1)
      (by dsimp [p, v, heapNode]; omega) (by dsimp [p, v, heapNode]; omega)
      (by dsimp [v, heapNode]; omega) hpar0 hpar1 α hc
    rcases hh with hh | hh
    · exact ⟨0, hh⟩
    · exact ⟨1, hh⟩
  · have hc' : G.color (.tree (p 1)) ≠ α := by
      intro hh
      exact hpc ((not_ne_iff.mp hc).trans hh.symm)
    have hh := child_color_of_parent_ne hG (p 1) (v 2) (v 3) (hpm 1) (hv 2) (hv 3)
      (by dsimp [p, v, heapNode]; omega) (by dsimp [p, v, heapNode]; omega)
      (by dsimp [v, heapNode]; omega) hpar2 hpar3 α hc'
    rcases hh with hh | hh
    · exact ⟨2, hh⟩
    · exact ⟨3, hh⟩

theorem tree_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (right : Bool)
    (hmid : n - l ≤ heapCol n right n ∧ heapCol n right n ≤ n + l)
    (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr (heapCol n right n) α)).card := by
  choose k hk using fun j : Fin (2 ^ (n - 2)) => leaf_quad_has_color hG hn right j α
  let v (j : Fin (2 ^ (n - 2))) := heapNode n right (2 ^ n - 1 + 4 * j.val + (k j).val)
  have hm (j : Fin (2 ^ (n - 2))) :
      Edge.tree (v j) ∈ G.classEdges l (.tr (heapCol n right n) α) := by
    have hs := quad_leaf_spec hn right j (k j)
    refine Finset.mem_filter.mpr ⟨tree_mem_iff.mpr ⟨hs.1, ?_⟩, ?_⟩
    · simp [v, hs.2.2]
    · change G.bEdge l (.tree (v j)) = some (.tr (heapCol n right n) α)
      simp only [WeldedInstance.bEdge]
      change (if n - l ≤ col n (v j) ∧ col n (v j) ≤ n + l then
        some (EdgeClass.tr (col n (v j)) (G.color (.tree (v j)))) else none) = _
      rw [show col n (v j) = heapCol n right n from hs.2.1, if_pos hmid]
      exact congrArg (fun c => some (EdgeClass.tr (heapCol n right n) c)) (hk j)
  let F : Fin (2 ^ (n - 2)) → G.classEdges l (.tr (heapCol n right n) α) :=
    fun j => ⟨.tree (v j), hm j⟩
  have hinj : Function.Injective F := by
    intro j j' heq
    have hv : v j = v j' := Edge.tree.inj (congrArg Subtype.val heq)
    have hj := (k j).isLt
    have hj' := (k j').isLt
    dsimp [v, heapNode] at hv
    apply Fin.ext
    omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective F hinj

theorem left_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr n α)).card := by
  exact tree_class_card_ge hG hn false ⟨Nat.sub_le n l, Nat.le_add_right n l⟩ α

theorem right_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (hl : 1 ≤ l) (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr (n + 1) α)).card := by
  have hc : heapCol n true n = n + 1 := by unfold heapCol; simp only [if_true]; omega
  have hh := tree_class_card_ge (l := l) hG hn true (by rw [hc]; constructor <;> omega) α
  simpa only [hc] using hh

theorem reciprocal_le_four_dyadic {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ^ (n - 2) ≤ m) :
    1 / (m : ℝ) ≤ 4 / (2 : ℝ) ^ n := by
  have hmp : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (Nat.two_pow_pos (n - 2)) hm)
  apply (div_le_div_iff₀ hmp (by positivity : (0 : ℝ) < 2 ^ n)).mpr
  simp only [one_mul]
  have hp : 2 ^ n ≤ 4 * m := by
    rw [(pow_two_levels hn).1]
    exact Nat.mul_le_mul_left 4 hm
  exact_mod_cast hp

theorem left_class_reciprocal_le {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (α : Fin 3) :
    1 / ((G.classEdges l (.tr n α)).card : ℝ) ≤ 4 / (2 : ℝ) ^ n :=
  reciprocal_le_four_dyadic hn (left_class_card_ge hG hn α)

theorem right_class_reciprocal_le {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (hl : 1 ≤ l) (α : Fin 3) :
    1 / ((G.classEdges l (.tr (n + 1) α)).card : ℝ) ≤ 4 / (2 : ℝ) ^ n :=
  reciprocal_le_four_dyadic hn (right_class_card_ge hG hn hl α)

end WeldedPath.NearWeldClasses

end

-- Solutions.WeldedPathMidPermData
section

namespace WeldedPath.Supplement.MidPermData

open Classical WeldedInstance LoopProof NearWeldClasses KappaKernel

variable {n l : ℕ} {G : WeldedInstance n}

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem color_of_three_incident (hG : G.IsProperColoring) (u : ℕ)
    (e f g : Edge) (he : e ∈ G.edges) (hf : f ∈ G.edges) (hg : g ∈ G.edges)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hie : e.Incident n u) (hif : f.Incident n u) (hig : g.Incident n u)
    (α : Fin 3) : ∃ a ∈ G.edges, G.color a = α ∧ a.Incident n u := by
  have hcf := hG e he f hf hef ⟨u, hie, hif⟩
  have hcg := hG e he g hg heg ⟨u, hie, hig⟩
  have hcfg := hG f hf g hg hfg ⟨u, hif, hig⟩
  rcases three_colors_cover _ _ _ α hcf hcg hcfg with h | h | h
  · exact ⟨e, he, h.symm, hie⟩
  · exact ⟨f, hf, h.symm, hif⟩
  · exact ⟨g, hg, h.symm, hig⟩

theorem tree_mem_of_nonroot {u : ℕ} (hu : IsVertex n u)
    (hlo : 0 < col n u) (hhi : col n u < 2 * n + 1) : Edge.tree u ∈ G.edges := by
  apply tree_mem_iff.mpr
  refine ⟨hu, ?_⟩
  unfold parent
  split_ifs <;> simp_all <;> omega

theorem color_at_leaf (hG : G.IsValid) {u : ℕ} (hu : IsLeaf n u)
    (ht : Edge.tree u ∈ G.edges) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n u := by
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp (hG.1.2.1 u hu)
  have hp : p ∈ G.weld ∧ (p.1 = u ∨ p.2 = u) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hq : q ∈ G.weld ∧ (q.1 = u ∨ q.2 = u) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hep : Edge.weld p.1 p.2 ∈ G.edges := weld_mem_iff.mpr hp.1
  have heq : Edge.weld q.1 q.2 ∈ G.edges := weld_mem_iff.mpr hq.1
  have hip : (Edge.weld p.1 p.2).Incident n u := by
    rcases hp.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hiq : (Edge.weld q.1 q.2).Incident n u := by
    rcases hq.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hpq' : Edge.weld p.1 p.2 ≠ Edge.weld q.1 q.2 := by
    intro h
    exact hpq (Prod.ext (congrArg Edge.tail h) (congrArg (Edge.head n) h))
  exact color_of_three_incident hG.2 u (.tree u) (.weld p.1 p.2) (.weld q.1 q.2)
    ht hep heq (by simp) (by simp) hpq' (Or.inl rfl) hip hiq α

theorem color_at_heap_internal (hG : G.IsProperColoring) (right : Bool)
    {d w : ℕ} (hd : 1 ≤ d) (hdn : d < n)
    (hlo : 2 ^ d - 1 ≤ w) (hhi : w < 2 ^ (d + 1) - 1) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n (heapNode n right w) := by
  have hw := heap_node_spec right hd (Nat.le_of_lt hdn) hlo hhi
  have hdp := Nat.two_pow_pos d
  have hds : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
  have hds' : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]
  have ha := heap_node_spec (n := n) (d := d + 1) (u := 2 * w + 1)
    right (by omega) (by omega) (by omega) (by omega)
  have hb := heap_node_spec (n := n) (d := d + 1) (u := 2 * w + 2)
    right (by omega) (by omega) (by omega) (by omega)
  have hpa : parent n (heapNode n right (2 * w + 1)) = some (heapNode n right w) := by
    simpa only [show (2 * w + 1 - 1) / 2 = w by omega] using ha.2.2
  have hpb : parent n (heapNode n right (2 * w + 2)) = some (heapNode n right w) := by
    simpa only [show (2 * w + 2 - 1) / 2 = w by omega] using hb.2.2
  have hwE : Edge.tree (heapNode n right w) ∈ G.edges :=
    tree_mem_iff.mpr ⟨hw.1, by simp [hw.2.2]⟩
  have haE : Edge.tree (heapNode n right (2 * w + 1)) ∈ G.edges :=
    tree_mem_iff.mpr ⟨ha.1, by simp [hpa]⟩
  have hbE : Edge.tree (heapNode n right (2 * w + 2)) ∈ G.edges :=
    tree_mem_iff.mpr ⟨hb.1, by simp [hpb]⟩
  apply color_of_three_incident hG (heapNode n right w)
    (.tree (heapNode n right w)) (.tree (heapNode n right (2 * w + 1)))
    (.tree (heapNode n right (2 * w + 2))) hwE haE hbE
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · exact Or.inl rfl
  · exact Or.inr (by simp [Edge.head, hpa])
  · exact Or.inr (by simp [Edge.head, hpb])

theorem color_at_nonroot (hG : G.IsValid) {u : ℕ} (hu : IsVertex n u)
    (hlo : 0 < col n u) (hhi : col n u < 2 * n + 1) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n u := by
  by_cases hleaf : col n u = n ∨ col n u = n + 1
  · exact color_at_leaf hG ⟨hu, hleaf⟩ (tree_mem_of_nonroot hu hlo hhi) α
  · by_cases hleft : u < 2 ^ (n + 1) - 1
    · let d := Nat.log 2 (u + 1)
      have hc : col n u = d := by simp [col, hleft, d]
      have hd : 1 ≤ d := by omega
      have hdn : d < n := by
        have hh := log_left_le n u hleft
        dsimp [d]
        omega
      have hlow := Nat.pow_log_le_self 2 (by omega : u + 1 ≠ 0)
      have hupp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (u + 1)
      have hh := color_at_heap_internal (w := u) hG.2 false hd hdn
        (by dsimp [d]; omega) (by dsimp [d]; omega) α
      simpa only [heapNode, Bool.false_eq_true, if_false, zero_add] using hh
    · let R := 2 ^ (n + 1) - 1
      let w := u - R
      let d := Nat.log 2 (w + 1)
      have hR : R ≤ u := by dsimp [R]; omega
      have heq : heapNode n true w = u := by dsimp [heapNode, w]; omega
      have hc : col n u = 2 * n + 1 - d := by
        simp only [col, if_neg hleft]
        rfl
      have hdnle : d ≤ n := log_right_le n u hu hR
      have hd : 1 ≤ d := by omega
      have hdn : d < n := by omega
      have hlow := Nat.pow_log_le_self 2 (by omega : w + 1 ≠ 0)
      have hupp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (w + 1)
      have hh := color_at_heap_internal (w := w) hG.2 true hd hdn
        (by dsimp [d]; omega) (by dsimp [d]; omega) α
      simpa only [heq] using hh

theorem incident_mid_class (hG : G.IsValid) {u : ℕ} {e : Edge}
    (he : e ∈ G.edges) (hi : e.Incident n u) (hu : u ∈ Vmid n l) :
    ∃ b : PClass n l, e ∈ G.classEdges l b.1 := by
  have hum := (Finset.mem_filter.mp hu).2
  cases e with
  | tree w =>
    have hadj := (edge_endpoints hG he).2.2
    have hm : n - l ≤ col n w ∧ col n w ≤ n + l := by
      rcases hi with hi | hi
      · change u = w at hi
        rw [hi] at hum
        omega
      · change u = (Edge.tree w).head n at hi
        rw [hi] at hum
        change col n w + 1 = col n ((Edge.tree w).head n) ∨
          col n ((Edge.tree w).head n) + 1 = col n w at hadj
        omega
    let b : PClass n l := ⟨.tr (col n w) (G.color (.tree w)), by simp [BEdge, hm]; omega⟩
    refine ⟨b, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    simp [b, WeldedInstance.bEdge, hm]
  | weld a c =>
    let b : PClass n l := ⟨.wld (G.color (.weld a c)), by simp [BEdge]⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨he, rfl⟩⟩

theorem permData_ne_none_of_mem_Vmid (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vmid n l) (α : Fin 3) :
    permData l G u α ≠ none := by
  have huv := Finset.mem_filter.mp hu
  have hv : IsVertex n u := Finset.mem_range.mp huv.1
  obtain ⟨e, he, hc, hi⟩ := color_at_nonroot hG hv (by omega) (by omega) α
  obtain ⟨b, hb⟩ := incident_mid_class hG he hi hu
  have hp := permData_of_class_edge hG (⟨e, hb⟩ : G.classEdges l b.1) u hi
  rw [hc] at hp
  rw [hp]
  simp

end WeldedPath.Supplement.MidPermData

end

-- Solutions.WeldedPathKappaWalk
section

namespace WeldedPath.Supplement.KappaWalk

open WeldedInstance KappaKernel
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma class_tail_injective (hG : G.IsProperColoring) (b : PClass n l) :
    Set.InjOn Edge.tail (G.classEdges l b.1) := by
  intro e he e' he' htail
  by_contra hne
  exact (hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.tail, Or.inl rfl, Or.inl htail⟩) (class_color he he')

lemma class_head_injective (hG : G.IsProperColoring) (b : PClass n l) :
    Set.InjOn (Edge.head n) (G.classEdges l b.1) := by
  intro e he e' he' hhead
  by_contra hne
  exact (hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.head n, Or.inr rfl, Or.inr hhead⟩) (class_color he he')

lemma vertex_lt_label (hn : 2 ≤ n) {v : ℕ} (hv : IsVertex n v) :
    v < labelBound n + 1 := by
  have hp : 2 ^ (n + 2) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold IsVertex numV at hv
  unfold labelBound
  omega

lemma sum_uniform_label_eq_one (S : Finset ℕ) (m : ℕ)
    (hc : S.card = m) (hm : 0 < m) (hS : ∀ v ∈ S, v < labelBound n + 1) :
    (∑ v : Label n, if v.1 ∈ S then 1 / (m : ℝ) else 0) = 1 := by
  classical
  have hcard : (Finset.univ.filter fun v : Label n => v.1 ∈ S).card = S.card := by
    apply Finset.card_bij (fun v _ => v.1)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv w hw h
      exact Fin.ext h
    · intro v hv
      exact ⟨⟨v, hS v hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard, hc]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

lemma kappa_label_row_sum_eq_one (hG : G.IsValid) (hn : 2 ≤ n)
    {u : ℕ} {α : Fin 3} {b : PClass n l} {e : ↥(G.classEdges l b.1)} {t : Bool}
    (hpd : permData l G u α = some ⟨b, e, t⟩) :
    (∑ v : Label n, kappa l G α u v.1) = 1 := by
  classical
  have hm : 0 < classSize l G b := Finset.card_pos.mpr ⟨e.1, e.2⟩
  cases t
  · simpa only [kappa, hpd, Bool.false_eq_true, false_and, true_and, false_or] using
      sum_uniform_label_eq_one ((G.classEdges l b.1).image Edge.tail) (classSize l G b)
        (Finset.card_image_iff.mpr (class_tail_injective hG.2 b)) hm (by
          intro v hv
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
          exact vertex_lt_label hn (LoopProof.edge_endpoints hG (Finset.mem_filter.mp hf).1).1)
  · simpa only [kappa, hpd, Bool.true_eq_false, false_and, true_and, or_false] using
      sum_uniform_label_eq_one ((G.classEdges l b.1).image (Edge.head n)) (classSize l G b)
        (Finset.card_image_iff.mpr (class_head_injective hG.2 b)) hm (by
          intro v hv
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
          exact vertex_lt_label hn (LoopProof.edge_endpoints hG (Finset.mem_filter.mp hf).1).2.1)

lemma mem_region_of_col {v : ℕ} (hv : IsVertex n v)
    (hlo : n - l - 1 ≤ col n v) (hhi : col n v ≤ n + l + 1) :
    v ∈ Vmid n l ∪ Vbd n l := by
  by_cases hm : n - l < col n v ∧ col n v < n + l
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv, hm⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hv, by omega⟩))

lemma class_endpoints_region (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) :
    e.1.tail ∈ Vmid n l ∪ Vbd n l ∧ e.1.head n ∈ Vmid n l ∪ Vbd n l := by
  have he := Finset.mem_filter.mp e.2
  have hend := LoopProof.edge_endpoints hG he.1
  obtain ⟨e, hem⟩ := e
  cases e with
  | tree v =>
    dsimp only at he hend ⊢
    have hc : n - l ≤ col n v ∧ col n v ≤ n + l := by
      by_contra h
      have hb := he.2
      simp only [WeldedInstance.bEdge, if_neg h] at hb
      cases hb
    simp only [Edge.tail] at hend ⊢
    constructor
    · apply mem_region_of_col hend.1 <;> omega
    · apply mem_region_of_col hend.2.1 <;> rcases hend.2.2 with h | h <;> omega
  | weld u v =>
    dsimp only at he hend ⊢
    have hw := hG.1.1 (u, v) (LoopProof.weld_mem_iff.mp he.1)
    dsimp only at hw
    simp only [Edge.tail, Edge.head] at hend ⊢
    constructor
    · apply mem_region_of_col hend.1 <;> omega
    · apply mem_region_of_col hend.2.1 <;> omega

lemma kappa_output_region (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) : v ∈ Vmid n l ∪ Vbd n l := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (Edge.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    rcases hm with ⟨_, hv⟩ | ⟨_, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      exact (class_endpoints_region hG ⟨e', he'⟩).2
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      exact (class_endpoints_region hG ⟨e', he'⟩).1

lemma kappa_zero_outside_region (hG : G.IsValid) (α : Fin 3) (u v : ℕ)
    (hv : v ∉ Vmid n l ∪ Vbd n l) : kappa l G α u v = 0 := by
  by_contra h
  exact hv (kappa_output_region hG h)

noncomputable def step (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) : Label n → ℝ := fun y =>
  ∑ x : Label n, p x * kappa l G α x.1 y.1

noncomputable def walk (l : ℕ) (G : WeldedInstance n) :
    List (Fin 3) → (Label n → ℝ) → (Label n → ℝ)
  | [], p => p
  | α :: cs, p => walk l G cs (step l G α p)

lemma walk_nonneg (l : ℕ) (G : WeldedInstance n) (cs : List (Fin 3))
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) : ∀ x, 0 ≤ walk l G cs p x := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_step_nonneg l G α p hp x.1)

lemma walk_point_bound (hG : G.IsValid) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    ∀ x, walk l G cs p x ≤ M := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_propagates_point_bound hG α p M hM hp x.1)

lemma walk_abs_bound (hG : G.IsValid) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) :
    ∀ x, |walk l G cs p x| ≤ M := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_propagates_abs_bound hG α p M hM hp x.1)

lemma walk_mass_le (l : ℕ) (G : WeldedInstance n) (cs : List (Fin 3))
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ x, walk l G cs p x) ≤ ∑ x, p x := by
  induction cs generalizing p with
  | nil => exact le_rfl
  | cons α cs ih =>
    exact (ih (step l G α p) (fun x => kappa_step_nonneg l G α p hp x.1)).trans
      (kappa_step_mass_le l G α p hp)

noncomputable def kill (B : Finset ℕ) (p : Label n → ℝ) : Label n → ℝ :=
  fun x => if x.1 ∈ B then 0 else p x

noncomputable def safeWalk (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) :
    List (Fin 3) → (Label n → ℝ) → (Label n → ℝ)
  | [], p => kill B p
  | α :: cs, p => safeWalk l G B cs (step l G α (kill B p))

lemma kill_nonneg (B : Finset ℕ) (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ kill B p x := by
  intro x
  unfold kill
  split
  · exact le_rfl
  · exact hp x

lemma kill_point_bound (B : Finset ℕ) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) : ∀ x, kill B p x ≤ M := by
  intro x
  unfold kill
  split
  · exact hM
  · exact hp x

lemma kill_mass_loss (B : Finset ℕ) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    (∑ x, p x) - (B.card : ℝ) * M ≤ ∑ x, kill B p x := by
  classical
  let T := Finset.univ.filter fun x : Label n => x.1 ∈ B
  have hcard : T.card ≤ B.card := Finset.card_le_card_of_injOn Fin.val
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun _ _ _ _ h => Fin.ext h)
  have hbad : (∑ x : Label n, if x.1 ∈ B then p x else 0) ≤ (B.card : ℝ) * M := by
    calc
      _ ≤ ∑ x : Label n, if x.1 ∈ B then M else 0 := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs
        · exact hp x
        · exact le_rfl
      _ = (T.card : ℝ) * M := by
        rw [← Finset.sum_filter]
        simp [T]
      _ ≤ (B.card : ℝ) * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
  have hid : (∑ x, p x) = (∑ x, kill B p x) + ∑ x, if x.1 ∈ B then p x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    unfold kill
    split_ifs <;> simp
  linarith

lemma safeWalk_nonneg (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (cs : List (Fin 3)) (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ safeWalk l G B cs p x := by
  induction cs generalizing p with
  | nil => exact kill_nonneg B p hp
  | cons α cs ih =>
    exact ih _ (fun x => kappa_step_nonneg l G α _ (kill_nonneg B p hp) x.1)

lemma safeWalk_point_bound (hG : G.IsValid) (B : Finset ℕ) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    ∀ x, safeWalk l G B cs p x ≤ M := by
  induction cs generalizing p with
  | nil => exact kill_point_bound B p M hM hp
  | cons α cs ih =>
    exact ih _ (fun x => kappa_propagates_point_bound hG α _ M hM
      (kill_point_bound B p M hM hp) x.1)

lemma step_mass_eq_of_support (α : Fin 3) (p : Label n → ℝ) (S : Finset ℕ)
    (hp : ∀ x, x.1 ∉ S → p x = 0)
    (hrow : ∀ x : Label n, x.1 ∈ S → (∑ y : Label n, kappa l G α x.1 y.1) = 1) :
    (∑ x, step l G α p x) = ∑ x, p x := by
  unfold step
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : x.1 ∈ S
  · rw [hrow x hx, mul_one]
  · rw [hp x hx, zero_mul]

lemma safeWalk_mass_lower (hG : G.IsValid) (S B : Finset ℕ)
    (hstay : ∀ α : Fin 3, ∀ x y : Label n, y.1 ∉ S → kappa l G α x.1 y.1 = 0)
    (hrow : ∀ α : Fin 3, ∀ x : Label n, x.1 ∈ S → x.1 ∉ B →
      (∑ y : Label n, kappa l G α x.1 y.1) = 1)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (hsupp : ∀ x, x.1 ∉ S → p x = 0) :
    (∑ x, p x) - ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * M ≤
      ∑ x, safeWalk l G B cs p x := by
  classical
  induction cs generalizing p with
  | nil => simpa [safeWalk] using kill_mass_loss B p M hM hp
  | cons α cs ih =>
    have hcap : ∀ x, step l G α (kill B p) x ≤ M :=
      fun x => kappa_propagates_point_bound hG α _ M hM
        (kill_point_bound B p M hM hp) x.1
    have hs : ∀ x, x.1 ∉ S → step l G α (kill B p) x = 0 := by
      intro y hy
      unfold step
      apply Finset.sum_eq_zero
      intro x _
      rw [hstay α x y hy, mul_zero]
    have heq : (∑ x, step l G α (kill B p) x) = ∑ x, kill B p x := by
      apply step_mass_eq_of_support α _ (S \ B)
      · intro x hx
        by_cases hb : x.1 ∈ B
        · simp [kill, hb]
        · have hns : x.1 ∉ S := by simpa [Finset.mem_sdiff, hb] using hx
          simp [kill, hb, hsupp x hns]
      · intro x hx
        exact hrow α x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
    have hi := ih _ hcap hs
    have hloss := kill_mass_loss B p M hM hp
    rw [heq] at hi
    simp only [safeWalk, List.length_cons, Nat.cast_add, Nat.cast_one] at *
    nlinarith

lemma safeWalk_conditioned_point_bound (hG : G.IsValid) (B : Finset ℕ)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M)
    (hsurv : (1 / 2 : ℝ) ≤ ∑ x, safeWalk l G B cs p x) (y : Label n) :
    safeWalk l G B cs p y / (∑ x, safeWalk l G B cs p x) ≤ 2 * M := by
  have hz : 0 < ∑ x, safeWalk l G B cs p x := by linarith
  apply (div_le_iff₀ hz).mpr
  have hy := safeWalk_point_bound (l := l) hG B cs p M hM hp y
  nlinarith

lemma kappa_mid_row_sum_eq_one (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vmid n l) (α : Fin 3) :
    (∑ y : Label n, kappa l G α u y.1) = 1 := by
  have hne := MidPermData.permData_ne_none_of_mem_Vmid hG hn hl hln hu α
  cases hpd : permData l G u α with
  | none => exact False.elim (hne hpd)
  | some d =>
    obtain ⟨b, e, t⟩ := d
    exact kappa_label_row_sum_eq_one hG (by omega) hpd

lemma weld_mem_mid (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    {u : ℕ} (hu : u ∈ Vweld n) : u ∈ Vmid n l := by
  obtain ⟨hv, hc⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨hv, by rcases hc with hc | hc <;> omega⟩

lemma kappa_weld_row_sum_eq_one (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vweld n) (α : Fin 3) :
    (∑ y : Label n, kappa l G α u y.1) = 1 :=
  kappa_mid_row_sum_eq_one hG hn hl hln (weld_mem_mid hn hl hln hu) α

lemma safeWalk_region_mass_lower (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M)
    (hsupp : ∀ x, x.1 ∉ Vmid n l ∪ Vbd n l → p x = 0) :
    (∑ x, p x) - ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * M ≤
      ∑ x, safeWalk l G B cs p x := by
  apply safeWalk_mass_lower hG (Vmid n l ∪ Vbd n l) B
    (fun α x y hy => kappa_zero_outside_region hG α x.1 y.1 hy) _ cs p M hM hp hsupp
  intro α x hx hb
  have hmid : x.1 ∈ Vmid n l := (Finset.mem_union.mp hx).resolve_right (fun h => hb (hB h))
  exact kappa_mid_row_sum_eq_one hG hn hl hln hmid α

lemma safeWalk_region_normalized_bound (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (cs : List (Fin 3)) (p : Label n → ℝ)
    (hp : ∀ x, p x ≤ 4 / (2 : ℝ) ^ n) (hmass : (∑ x, p x) = 1)
    (hsupp : ∀ x, x.1 ∉ Vmid n l ∪ Vbd n l → p x = 0)
    (hsmall : ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (y : Label n) :
    safeWalk l G B cs p y / (∑ x, safeWalk l G B cs p x) ≤ 8 / (2 : ℝ) ^ n := by
  have hs := safeWalk_region_mass_lower hG hn hl hln B hB cs p _ (by positivity) hp hsupp
  rw [hmass] at hs
  have hsurv : (1 / 2 : ℝ) ≤ ∑ x, safeWalk l G B cs p x := by linarith
  have hb := safeWalk_conditioned_point_bound hG B cs p _ (by positivity) hp hsurv y
  convert hb using 1 <;> ring

end WeldedPath.Supplement.KappaWalk

end

-- Solutions.WeldedPathAssignmentDatabase
section

namespace WeldedPath.Supplement.AssignmentDatabase

open Classical KappaKernel KappaWalk

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def relFun {A B : Type*} (R : A → B → Prop) (a : A) : Option B :=
  if h : ∃ b, R a b then some (Classical.choose h) else none

lemma relFun_eq_some {A B : Type*} (R : A → B → Prop)
    (hR : ∀ a b c, R a b → R a c → b = c) (a : A) (b : B) :
    relFun R a = some b ↔ R a b := by
  unfold relFun
  by_cases h : ∃ c, R a c
  · rw [dif_pos h, Option.some.injEq]
    constructor
    · intro he
      rw [← he]
      exact Classical.choose_spec h
    · exact fun hb => hR a _ b (Classical.choose_spec h) hb
  · rw [dif_neg h]
    constructor
    · intro he
      cases he
    · intro hb
      exact (h ⟨b, hb⟩).elim

noncomputable def relationPEquiv {A B : Type*} (R : A → B → Prop)
    (hR : ∀ a b c, R a b → R a c → b = c)
    (hL : ∀ a b c, R a c → R b c → a = b) : PEquiv A B where
  toFun := relFun R
  invFun := relFun (fun b a => R a b)
  inv a b := by
    rw [relFun_eq_some _ (fun c a b => hL a b c), relFun_eq_some R hR]

lemma relationPEquiv_apply {A B : Type*} (R : A → B → Prop)
    (hR : ∀ a b c, R a b → R a c → b = c)
    (hL : ∀ a b c, R a c → R b c → a = b) (a : A) (b : B) :
    relationPEquiv R hR hL a = some b ↔ R a b := relFun_eq_some R hR a b

lemma pequiv_eq_of_graph_eq {A B : Type*} (I J : PEquiv A B)
    (h : ∀ a b, I a = some b ↔ J a = some b) : I = J := by
  apply PEquiv.ext
  intro a
  cases hi : I a with
  | none =>
    cases hj : J a with
    | none => rfl
    | some b =>
      have he := (h a b).mpr hj
      rw [hi] at he
      cases he
  | some b => exact ((h a b).mp hi).symm

theorem isDbOf_unique (H : AbsForest n) (φ : Fin H.k → Label n)
    (I J : Db l G) (hI : H.IsDbOf l G φ I) (hJ : H.IsDbOf l G φ J) : I = J := by
  apply Prod.ext
  · exact pequiv_eq_of_graph_eq I.1 J.1 (fun a b => (hI.1 a b).trans (hJ.1 a b).symm)
  · funext b
    exact pequiv_eq_of_graph_eq (I.2 b) (J.2 b)
      (fun i j => (hI.2 b i j).trans (hJ.2 b i j).symm)

def labelRel (H : AbsForest n) (φ : Fin H.k → Label n)
    (i j : Fin (labelBound n)) : Prop :=
  ∃ u, (φ u).1 = i.1 + 1 ∧ H.lab u = some j

def edgeRel (H : AbsForest n) (φ : Fin H.k → Label n) (b : PClass n l)
    (j j' : Fin (classSize l G b)) : Prop :=
  ∃ p ∈ H.E,
    let e₁ := ((edgeIdx l G b).symm j).1
    let e₂ := ((edgeIdx l G b).symm j').1
    let α := H.color p
    (G.eAlpha (φ p.1).1 α = some e₁ ∧ G.eAlpha (φ p.2).1 α = some e₂ ∧
      (φ p.1).1 = e₁.tail ∧ (φ p.2).1 = e₂.head n) ∨
    (G.eAlpha (φ p.2).1 α = some e₁ ∧ G.eAlpha (φ p.1).1 α = some e₂ ∧
      (φ p.2).1 = e₁.tail ∧ (φ p.1).1 = e₂.head n)

lemma labelRel_right_unique (H : AbsForest n) (φ : Fin H.k → Label n)
    (hφ : Function.Injective φ) :
    ∀ i j k, labelRel H φ i j → labelRel H φ i k → j = k := by
  rintro i j k ⟨u, hu, hj⟩ ⟨v, hv, hk⟩
  have huv := hφ (Fin.ext (hu.trans hv.symm))
  subst v
  exact Option.some.inj (hj.symm.trans hk)

lemma labelRel_left_unique (H : AbsForest n) (hH : H.IsValid) (φ : Fin H.k → Label n) :
    ∀ i j k, labelRel H φ i k → labelRel H φ j k → i = j := by
  rintro i j k ⟨u, hu, hi⟩ ⟨v, hv, hj⟩
  have huv := hH.2.2.2.1 u v k hi hj
  subst v
  apply Fin.ext
  omega

lemma color_partner_unique (H : AbsForest n) (hH : H.IsValid)
    (p p' : Fin H.k × Fin H.k) (hp : p ∈ H.E) (hp' : p' ∈ H.E)
    (hc : H.color p = H.color p') (u v w : Fin H.k)
    (he : p = (u, v) ∨ p = (v, u)) (he' : p' = (u, w) ∨ p' = (w, u)) : v = w := by
  have hpeq : p = p' := by
    by_contra hne
    apply (hH.2.2.1 p hp p' hp' hne ?_) hc
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;> simp
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;>
    simp only [Prod.mk.injEq] at hpeq <;> aesop

lemma edgeRel_witness (H : AbsForest n) (φ : Fin H.k → Label n) (b : PClass n l)
    (j j' : Fin (classSize l G b)) (h : edgeRel H φ b j j') :
    ∃ u v p, p ∈ H.E ∧ (p = (u, v) ∨ p = (v, u)) ∧
      H.color p = classColor b.val ∧
      (φ u).1 = ((edgeIdx l G b).symm j).1.tail ∧
      (φ v).1 = ((edgeIdx l G b).symm j').1.head n := by
  obtain ⟨p, hp, h⟩ := h
  have he := bEdge_color (Finset.mem_filter.mp ((edgeIdx l G b).symm j).property).2
  rcases h with h | h
  · exact ⟨p.1, p.2, p, hp, Or.inl rfl,
      (eAlpha_spec h.1).2.1.symm.trans he, h.2.2.1, h.2.2.2⟩
  · exact ⟨p.2, p.1, p, hp, Or.inr rfl,
      (eAlpha_spec h.1).2.1.symm.trans he, h.2.2.1, h.2.2.2⟩

lemma edgeRel_right_unique (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ)
    (hG : G.IsProperColoring) (b : PClass n l) :
    ∀ i j k : Fin (classSize l G b),
      edgeRel (G := G) H φ b i j → edgeRel (G := G) H φ b i k → j = k := by
  intro i j k hij hik
  obtain ⟨u, v, p, hp, he, hc, hu, hv⟩ := edgeRel_witness H φ b i j hij
  obtain ⟨u', v', p', hp', he', hc', hu', hv'⟩ := edgeRel_witness H φ b i k hik
  have huu := hφ (Fin.ext (hu.trans hu'.symm))
  subst u'
  have hvv := color_partner_unique H hH p p' hp hp' (hc.trans hc'.symm) u v v' he he'
  subst v'
  apply (edgeIdx l G b).symm.injective
  apply Subtype.ext
  exact class_head_injective hG b ((edgeIdx l G b).symm j).property
    ((edgeIdx l G b).symm k).property (hv.symm.trans hv')

lemma edgeRel_left_unique (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ)
    (hG : G.IsProperColoring) (b : PClass n l) :
    ∀ i j k : Fin (classSize l G b),
      edgeRel (G := G) H φ b i k → edgeRel (G := G) H φ b j k → i = j := by
  intro i j k hik hjk
  obtain ⟨u, v, p, hp, he, hc, hu, hv⟩ := edgeRel_witness H φ b i k hik
  obtain ⟨u', v', p', hp', he', hc', hu', hv'⟩ := edgeRel_witness H φ b j k hjk
  have hvv := hφ (Fin.ext (hv.trans hv'.symm))
  subst v'
  have huu := color_partner_unique H hH p p' hp hp' (hc.trans hc'.symm) v u u'
    he.symm he'.symm
  subst u'
  apply (edgeIdx l G b).symm.injective
  apply Subtype.ext
  exact class_tail_injective hG b ((edgeIdx l G b).symm i).property
    ((edgeIdx l G b).symm j).property (hu.symm.trans hu')

noncomputable def assignmentDb (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hG : G.IsProperColoring) : Db l G :=
  (relationPEquiv (labelRel H φ) (labelRel_right_unique H φ hφ) (labelRel_left_unique H hH φ),
    fun b => relationPEquiv (edgeRel H φ b) (edgeRel_right_unique H hH φ hφ hG b)
      (edgeRel_left_unique H hH φ hφ hG b))

theorem assignmentDb_isDbOf (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hG : G.IsProperColoring) :
    H.IsDbOf l G φ (assignmentDb H hH φ hφ hG) := by
  constructor
  · intro i j
    exact relationPEquiv_apply (labelRel H φ) (labelRel_right_unique H φ hφ)
      (labelRel_left_unique H hH φ) i j
  · intro b i j
    exact relationPEquiv_apply (edgeRel H φ b) (edgeRel_right_unique H hH φ hφ hG b)
      (edgeRel_left_unique H hH φ hφ hG b) i j

theorem isDbOf_exists_unique (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hG : G.IsProperColoring) :
    ∃! I : Db l G, H.IsDbOf l G φ I := by
  refine ⟨assignmentDb H hH φ hφ hG, assignmentDb_isDbOf H hH φ hφ hG, ?_⟩
  intro J hJ
  exact isDbOf_unique H φ J _ hJ (assignmentDb_isDbOf H hH φ hφ hG)

def edgeRecord (H : AbsForest n) (φ : Fin H.k → Label n) (b : PClass n l)
    (p : Fin H.k × Fin H.k) (j j' : Fin (classSize l G b)) : Prop :=
  let e₁ := ((edgeIdx l G b).symm j).1
  let e₂ := ((edgeIdx l G b).symm j').1
  let α := H.color p
  (G.eAlpha (φ p.1).1 α = some e₁ ∧ G.eAlpha (φ p.2).1 α = some e₂ ∧
    (φ p.1).1 = e₁.tail ∧ (φ p.2).1 = e₂.head n) ∨
  (G.eAlpha (φ p.2).1 α = some e₁ ∧ G.eAlpha (φ p.1).1 α = some e₂ ∧
    (φ p.2).1 = e₁.tail ∧ (φ p.1).1 = e₂.head n)

theorem kappa_edge_record (hG : G.IsValid) (H : AbsForest n)
    (φ : Fin H.k → Label n) (p : Fin H.k × Fin H.k)
    (hk : kappa l G (H.color p) (φ p.1).1 (φ p.2).1 ≠ 0) :
    ∃ (b : PClass n l) (i j : Fin (classSize l G b)), edgeRecord H φ b p i j := by
  cases hpd : permData l G (φ p.1).1 (H.color p) with
  | none => exact (hk (by simp [kappa, hpd])).elim
  | some d =>
    rcases d with ⟨b, e, t⟩
    have heα := permData_eAlpha hpd
    have hcol := (eAlpha_spec heα).2.1
    have hor := CrossingExclusion.permData_orientation hpd
    cases t
    · have hm : (φ p.2).1 ∈ (G.classEdges l b.1).image Edge.tail := by
        by_contra hh
        exact hk (by simp [kappa, hpd, hh])
      obtain ⟨g, hg, htail⟩ := Finset.mem_image.mp hm
      let g' : ↥(G.classEdges l b.1) := ⟨g, hg⟩
      have hcg : G.color g = H.color p := (class_color hg e.property).trans hcol
      have hgα : G.eAlpha (φ p.2).1 (H.color p) = some g := by
        rw [← hcg]
        exact LoopProof.eAlpha_of_edge G hG.2 g (Finset.mem_filter.mp hg).1 _
          (Or.inl htail.symm)
      refine ⟨b, edgeIdx l G b g', edgeIdx l G b e, ?_⟩
      simp only [edgeRecord, Equiv.symm_apply_apply]
      exact Or.inr ⟨hgα, heα, htail.symm, hor.2 rfl⟩
    · have hm : (φ p.2).1 ∈ (G.classEdges l b.1).image (Edge.head n) := by
        by_contra hh
        exact hk (by simp [kappa, hpd, hh])
      obtain ⟨g, hg, hhead⟩ := Finset.mem_image.mp hm
      let g' : ↥(G.classEdges l b.1) := ⟨g, hg⟩
      have hcg : G.color g = H.color p := (class_color hg e.property).trans hcol
      have hgα : G.eAlpha (φ p.2).1 (H.color p) = some g := by
        rw [← hcg]
        exact LoopProof.eAlpha_of_edge G hG.2 g (Finset.mem_filter.mp hg).1 _
          (Or.inr hhead.symm)
      refine ⟨b, edgeIdx l G b e, edgeIdx l G b g', ?_⟩
      simp only [edgeRecord, Equiv.symm_apply_apply]
      exact Or.inl ⟨heα, hgα, hor.1 rfl, hhead.symm⟩

theorem positive_mu_edge_record (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hμ : H.muRef l G φ ≠ 0)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E) :
    ∃ (b : PClass n l) (i j : Fin (classSize l G b)), edgeRecord H φ b p i j :=
  kappa_edge_record hG H φ p (CrossingExclusion.edge_kappa_ne_zero H hH φ hμ hp)

theorem isDbOf_covers_edge (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hμ : H.muRef l G φ ≠ 0)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (p : Fin H.k × Fin H.k) (hp : p ∈ H.E) :
    ∃ (b : PClass n l) (i j : Fin (classSize l G b)),
      edgeRecord H φ b p i j ∧ I.2 b i = some j := by
  obtain ⟨b, i, j, hrec⟩ := positive_mu_edge_record hG H hH φ hμ p hp
  exact ⟨b, i, j, hrec, (hI.2 b i j).mpr ⟨p, hp, hrec⟩⟩

theorem positive_mu_vertex_nonzero (H : AbsForest n) (φ : Fin H.k → Label n)
    (hμ : H.muRef l G φ ≠ 0) (hln : l + 2 ≤ n) (u : Fin H.k) : 1 ≤ (φ u).1 := by
  obtain ⟨s, hs, hsu⟩ := CrossingExclusion.comp_root_exists H u
  have hu : u ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsu⟩
  have hss : s ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl _⟩
  have hc : H.muComp l G s φ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hμ) s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  by_cases hcard : (H.comp s).card = 1
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    have huv : u = v := by simpa only [hv, Finset.mem_singleton] using hu
    have hsv : s = v := by simpa only [hv, Finset.mem_singleton] using hss
    have hus : u = s := huv.trans hsv.symm
    have hpos : 1 ≤ (φ s).1 := by
      by_contra hh
      exact hc (by simp [AbsForest.muComp, hcard, hh])
    simpa only [hus] using hpos
  · have hregion : (φ u).1 ∈ Vmid n l ∪ Vbd n l := by
      unfold AbsForest.muComp at hc
      dsimp only at hc
      rw [if_neg hcard] at hc
      split at hc
      · rename_i ha
        exact ha u hu
      · exact (hc rfl).elim
    by_contra hh
    have hz : (φ u).1 = 0 := by omega
    rcases Finset.mem_union.mp hregion with hm | hb
    · have hc0 := (Finset.mem_filter.mp hm).2
      rw [hz, LoopProof.col_zero] at hc0
      omega
    · have hc0 := (Finset.mem_filter.mp hb).2
      rw [hz, LoopProof.col_zero] at hc0
      rcases hc0 with h | h | h | h <;> omega

theorem isDbOf_covers_label (H : AbsForest n) (φ : Fin H.k → Label n)
    (hμ : H.muRef l G φ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (u : Fin H.k)
    (j : Fin (labelBound n)) (hj : H.lab u = some j) :
    ∃ i : Fin (labelBound n), (φ u).1 = i.1 + 1 ∧ I.1 i = some j := by
  have hp := positive_mu_vertex_nonzero H φ hμ hln u
  have hb := (φ u).isLt
  let i : Fin (labelBound n) := ⟨(φ u).1 - 1, by omega⟩
  have hi : (φ u).1 = i.1 + 1 := by dsimp [i]; omega
  exact ⟨i, hi, (hI.1 i j).mpr ⟨u, hi, hj⟩⟩

end WeldedPath.Supplement.AssignmentDatabase

end

-- Solutions.WeldedPathLabelDatabaseSize
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

def vertexLabelIndex (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (u : Fin H.k) : Fin (labelBound n) :=
  ⟨(φ u).val - 1, by have hi := (φ u).isLt; have hu := hp u; change _ < labelBound n; omega⟩

lemma vertexLabelIndex_val (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (u : Fin H.k) :
    (φ u).val = (vertexLabelIndex H φ hp u).val + 1 := by
  have hu := hp u
  change (φ u).val = (φ u).val - 1 + 1
  omega

lemma vertexLabelIndex_injective (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (hφ : Function.Injective φ) :
    Function.Injective (vertexLabelIndex H φ hp) := by
  intro u v huv
  apply hφ
  apply Fin.ext
  rw [vertexLabelIndex_val H φ hp u, vertexLabelIndex_val H φ hp v, huv]

theorem isDbOf_label_at_vertex (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (hφ : Function.Injective φ)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (u : Fin H.k) :
    I.1 (vertexLabelIndex H φ hp u) = H.lab u := by
  have hs (j : Fin (labelBound n)) : I.1 (vertexLabelIndex H φ hp u) = some j ↔ H.lab u = some j := by
    rw [hI.1]
    constructor
    · rintro ⟨v, hv, hvj⟩
      have he : v = u := hφ (Fin.ext (hv.trans (vertexLabelIndex_val H φ hp u).symm))
      exact he ▸ hvj
    · intro huj; exact ⟨u, vertexLabelIndex_val H φ hp u, huj⟩
  cases hu : H.lab u with
  | some j => exact (hs j).mpr hu
  | none =>
    cases hi : I.1 (vertexLabelIndex H φ hp u) with
    | none => rfl
    | some j =>
      have hh := (hs j).mp hi
      rw [hu] at hh
      cases hh

theorem isDbOf_label_size (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (hφ : Function.Injective φ)
    (I : Db l G) (hI : H.IsDbOf l G φ I) :
    I.1.size = (Finset.univ.filter (fun u => (H.lab u).isSome)).card := by
  symm
  apply Finset.card_bij (fun u _ => vertexLabelIndex H φ hp u)
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [isDbOf_label_at_vertex H φ hp hφ I hI]
      exact (Finset.mem_filter.mp hu).2⟩
  · intro u hu v hv huv
    exact vertexLabelIndex_injective H φ hp hφ huv
  · intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    cases hi : I.1 x with
    | none => simp only [hi, Option.isSome_none, Bool.false_eq_true] at hh
    | some j =>
      obtain ⟨u, hu, huj⟩ := (hI.1 x j).mp hi
      refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp only [huj, Option.isSome_some]
      · apply Fin.ext
        have hv := vertexLabelIndex_val H φ hp u
        omega

theorem isDbOf_label_size_of_mu (H : AbsForest n) (φ : Fin H.k → Label n)
    (hμ : H.muRef l G φ ≠ 0) (hln : l + 2 ≤ n) (hφ : Function.Injective φ)
    (I : Db l G) (hI : H.IsDbOf l G φ I) :
    I.1.size = (Finset.univ.filter (fun u => (H.lab u).isSome)).card :=
  isDbOf_label_size H φ (positive_mu_vertex_nonzero H φ hμ hln) hφ I hI

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathDatabaseSupport
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

def recordedVertex (l : ℕ) (G : WeldedInstance n) (I : Db l G) (v : ℕ) : Prop :=
  (∃ i j, I.1 i = some j ∧ v = i.1 + 1) ∨
  (∃ (b : PClass n l) (i j : Fin (classSize l G b)), I.2 b i = some j ∧
    (v = ((edgeIdx l G b).symm i).1.tail ∨ v = ((edgeIdx l G b).symm j).1.head n))

theorem isDbOf_recordedVertex (H : AbsForest n) (φ : Fin H.k → Label n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (v : ℕ) (hv : recordedVertex l G I v) :
    ∃ u, (φ u).1 = v := by
  rcases hv with ⟨i, j, hij, hv⟩ | ⟨b, i, j, hij, hv⟩
  · obtain ⟨u, hu, _⟩ := (hI.1 i j).mp hij
    exact ⟨u, hu.trans hv.symm⟩
  · obtain ⟨p, _, hrec⟩ := (hI.2 b i j).mp hij
    rcases hrec with h | h
    · rcases hv with hv | hv
      · exact ⟨p.1, h.2.2.1.trans hv.symm⟩
      · exact ⟨p.2, h.2.2.2.trans hv.symm⟩
    · rcases hv with hv | hv
      · exact ⟨p.2, h.2.2.1.trans hv.symm⟩
      · exact ⟨p.1, h.2.2.2.trans hv.symm⟩

theorem recordedVertex_of_isDbOf (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hμ : H.muRef l G φ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (u : Fin H.k) :
    recordedVertex l G I (φ u).1 := by
  rcases hH.2.2.2.2 u with hu | ⟨p, hp, hu⟩
  · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hu
    obtain ⟨i, hi, hij⟩ := isDbOf_covers_label H φ hμ hln I hI u j hj
    exact Or.inl ⟨i, j, hij, hi⟩
  · obtain ⟨b, i, j, hrec, hij⟩ := isDbOf_covers_edge hG H hH φ hμ I hI p hp
    apply Or.inr
    refine ⟨b, i, j, hij, ?_⟩
    rcases hu with hu | hu
    · rw [← hu]
      rcases hrec with h | h
      · exact Or.inl h.2.2.1
      · exact Or.inr h.2.2.2
    · rw [← hu]
      rcases hrec with h | h
      · exact Or.inr h.2.2.2
      · exact Or.inl h.2.2.1

theorem recordedVertex_iff (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hμ : H.muRef l G φ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (v : ℕ) :
    recordedVertex l G I v ↔ ∃ u, (φ u).1 = v := by
  constructor
  · exact isDbOf_recordedVertex H φ I hI v
  · rintro ⟨u, rfl⟩
    exact recordedVertex_of_isDbOf hG H hH φ hμ hln I hI u

theorem isDbOf_same_range (hG : G.IsValid)
    (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (hφμ : H.muRef l G φ ≠ 0) (hψμ : K.muRef l G ψ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I) :
    Set.range φ = Set.range ψ := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    have hr := recordedVertex_of_isDbOf hG H hH φ hφμ hln I hI u
    obtain ⟨w, hw⟩ := isDbOf_recordedVertex K ψ I hJ _ hr
    exact ⟨w, Fin.ext hw⟩
  · rintro ⟨u, rfl⟩
    have hr := recordedVertex_of_isDbOf hG K hK ψ hψμ hln I hJ u
    obtain ⟨w, hw⟩ := isDbOf_recordedVertex H φ I hI _ hr
    exact ⟨w, Fin.ext hw⟩

noncomputable def assignmentEquiv {A B X : Type*} (φ : A → X) (ψ : B → X)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hr : Set.range φ = Set.range ψ) :
    A ≃ B :=
  ((Equiv.ofInjective φ hφ).trans (Equiv.setCongr hr)).trans (Equiv.ofInjective ψ hψ).symm

theorem assignmentEquiv_apply {A B X : Type*} (φ : A → X) (ψ : B → X)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hr : Set.range φ = Set.range ψ)
    (a : A) : ψ (assignmentEquiv φ ψ hφ hψ hr a) = φ a := by
  unfold assignmentEquiv
  exact Equiv.apply_ofInjective_symm hψ _

theorem assignmentEquiv_unique {A B X : Type*} (φ : A → X) (ψ : B → X)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hr : Set.range φ = Set.range ψ)
    (e : A ≃ B) (he : ∀ a, ψ (e a) = φ a) : e = assignmentEquiv φ ψ hφ hψ hr := by
  apply Equiv.ext
  intro a
  exact hψ ((he a).trans (assignmentEquiv_apply φ ψ hφ hψ hr a).symm)

theorem isDbOf_vertex_equiv (hG : G.IsValid)
    (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφμ : H.muRef l G φ ≠ 0) (hψμ : K.muRef l G ψ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I) :
    ∃! e : Fin H.k ≃ Fin K.k, ∀ u, ψ (e u) = φ u := by
  let hr := isDbOf_same_range hG H K hH hK φ ψ hφμ hψμ hln I hI hJ
  exact ⟨assignmentEquiv φ ψ hφ hψ hr, assignmentEquiv_apply φ ψ hφ hψ hr,
    fun e he => assignmentEquiv_unique φ ψ hφ hψ hr e he⟩

theorem label_eq_of_isDbOf (H K : AbsForest n)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I)
    (u : Fin H.k) (v : Fin K.k) (he : φ u = ψ v) (hpos : 1 ≤ (φ u).1) :
    H.lab u = K.lab v := by
  have hb := (φ u).isLt
  let i : Fin (labelBound n) := ⟨(φ u).1 - 1, by omega⟩
  have hi : (φ u).1 = i.1 + 1 := by dsimp [i]; omega
  have hv : (ψ v).1 = i.1 + 1 := (congrArg Fin.val he).symm.trans hi
  have hh (j : Fin (labelBound n)) : H.lab u = some j ↔ K.lab v = some j := by
    constructor
    · intro hj
      have hrec := (hI.1 i j).mpr ⟨u, hi, hj⟩
      obtain ⟨w, hw, hwj⟩ := (hJ.1 i j).mp hrec
      have heq := hψ (Fin.ext (hw.trans hv.symm))
      simpa only [heq] using hwj
    · intro hj
      have hrec := (hJ.1 i j).mpr ⟨v, hv, hj⟩
      obtain ⟨w, hw, hwj⟩ := (hI.1 i j).mp hrec
      have heq := hφ (Fin.ext (hw.trans hi.symm))
      simpa only [heq] using hwj
  cases hu : H.lab u with
  | none =>
    cases hv' : K.lab v with
    | none => rfl
    | some j =>
      have hbad := (hh j).mpr hv'
      rw [hu] at hbad
      cases hbad
  | some j => exact ((hh j).mp hu).symm

theorem vertex_equiv_preserves_labels (H K : AbsForest n)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφμ : H.muRef l G φ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I)
    (e : Fin H.k ≃ Fin K.k) (he : ∀ u, ψ (e u) = φ u) (u : Fin H.k) :
    K.lab (e u) = H.lab u :=
  (label_eq_of_isDbOf H K φ ψ hφ hψ I hI hJ u (e u) (he u).symm
    (positive_mu_vertex_nonzero H φ hφμ hln u)).symm

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathDatabaseIsomorphism
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

def ColoredAdj (H : AbsForest n) (u v : Fin H.k) (α : Fin 3) : Prop :=
  ∃ p ∈ H.E, (p = (u, v) ∨ p = (v, u)) ∧ H.color p = α

def IsForestIso (H K : AbsForest n) (e : Fin H.k ≃ Fin K.k) : Prop :=
  (∀ u, K.lab (e u) = H.lab u) ∧
    ∀ u v α, ColoredAdj H u v α ↔ ColoredAdj K (e u) (e v) α

theorem edgeRecord_matching (H K : AbsForest n)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (b : PClass n l)
    (p : Fin H.k × Fin H.k) (q : Fin K.k × Fin K.k)
    (i j : Fin (classSize l G b))
    (hp : edgeRecord H φ b p i j) (hq : edgeRecord K ψ b q i j) :
    H.color p = K.color q ∧
      ((φ p.1 = ψ q.1 ∧ φ p.2 = ψ q.2) ∨ (φ p.1 = ψ q.2 ∧ φ p.2 = ψ q.1)) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact ⟨(KappaKernel.eAlpha_spec hp.1).2.1.symm.trans
        (KappaKernel.eAlpha_spec hq.1).2.1,
      Or.inl ⟨Fin.ext (hp.2.2.1.trans hq.2.2.1.symm),
        Fin.ext (hp.2.2.2.trans hq.2.2.2.symm)⟩⟩
  · exact ⟨(KappaKernel.eAlpha_spec hp.1).2.1.symm.trans
        (KappaKernel.eAlpha_spec hq.1).2.1,
      Or.inr ⟨Fin.ext (hp.2.2.1.trans hq.2.2.1.symm),
        Fin.ext (hp.2.2.2.trans hq.2.2.2.symm)⟩⟩
  · exact ⟨(KappaKernel.eAlpha_spec hp.1).2.1.symm.trans
        (KappaKernel.eAlpha_spec hq.1).2.1,
      Or.inr ⟨Fin.ext (hp.2.2.2.trans hq.2.2.2.symm),
        Fin.ext (hp.2.2.1.trans hq.2.2.1.symm)⟩⟩
  · exact ⟨(KappaKernel.eAlpha_spec hp.1).2.1.symm.trans
        (KappaKernel.eAlpha_spec hq.1).2.1,
      Or.inl ⟨Fin.ext (hp.2.2.2.trans hq.2.2.2.symm),
        Fin.ext (hp.2.2.1.trans hq.2.2.1.symm)⟩⟩

theorem isDbOf_edge_transport (hG : G.IsValid) (H K : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (hψ : Function.Injective ψ)
    (hφμ : H.muRef l G φ ≠ 0) (I : Db l G)
    (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I)
    (e : Fin H.k ≃ Fin K.k) (he : ∀ u, ψ (e u) = φ u)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E) :
    ∃ q ∈ K.E, K.color q = H.color p ∧
      (q = (e p.1, e p.2) ∨ q = (e p.2, e p.1)) := by
  obtain ⟨b, i, j, hp', hij⟩ := isDbOf_covers_edge hG H hH φ hφμ I hI p hp
  obtain ⟨q, hq, hq'⟩ := (hJ.2 b i j).mp hij
  obtain ⟨hc, hpq⟩ := edgeRecord_matching H K φ ψ b p q i j hp' hq'
  refine ⟨q, hq, hc.symm, ?_⟩
  rcases hpq with h | h
  · exact Or.inl (Prod.ext (hψ (h.1.symm.trans (he p.1).symm))
      (hψ (h.2.symm.trans (he p.2).symm)))
  · exact Or.inr (Prod.ext (hψ (h.2.symm.trans (he p.2).symm))
      (hψ (h.1.symm.trans (he p.1).symm)))

theorem isDbOf_coloredAdj_transport (hG : G.IsValid) (H K : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (hψ : Function.Injective ψ)
    (hφμ : H.muRef l G φ ≠ 0) (I : Db l G)
    (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I)
    (e : Fin H.k ≃ Fin K.k) (he : ∀ u, ψ (e u) = φ u)
    (u v : Fin H.k) (α : Fin 3) (h : ColoredAdj H u v α) :
    ColoredAdj K (e u) (e v) α := by
  obtain ⟨p, hp, huv, hc⟩ := h
  obtain ⟨q, hq, hqc, hqe⟩ := isDbOf_edge_transport hG H K hH φ ψ hψ hφμ I hI hJ e he p hp
  refine ⟨q, hq, ?_, hqc.trans hc⟩
  rcases huv with rfl | rfl
  · exact hqe
  · exact hqe.symm

theorem vertex_equiv_isForestIso (hG : G.IsValid)
    (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφμ : H.muRef l G φ ≠ 0) (hψμ : K.muRef l G ψ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I)
    (e : Fin H.k ≃ Fin K.k) (he : ∀ u, ψ (e u) = φ u) : IsForestIso H K e := by
  refine ⟨vertex_equiv_preserves_labels H K φ ψ hφ hψ hφμ hln I hI hJ e he, ?_⟩
  intro u v α
  constructor
  · exact isDbOf_coloredAdj_transport hG H K hH φ ψ hψ hφμ I hI hJ e he u v α
  · intro h
    have he' : ∀ w, φ (e.symm w) = ψ w := by
      intro w
      simpa only [Equiv.apply_symm_apply] using (he (e.symm w)).symm
    simpa only [Equiv.symm_apply_apply] using
      isDbOf_coloredAdj_transport hG K H hK ψ φ hφ hψμ I hJ hI e.symm he' (e u) (e v) α h

theorem isDbOf_forest_equiv (hG : G.IsValid)
    (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφμ : H.muRef l G φ ≠ 0) (hψμ : K.muRef l G ψ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (hJ : K.IsDbOf l G ψ I) :
    ∃! e : Fin H.k ≃ Fin K.k, IsForestIso H K e ∧ ∀ u, ψ (e u) = φ u := by
  obtain ⟨e, he, hunique⟩ := isDbOf_vertex_equiv hG H K hH hK φ ψ hφ hψ hφμ hψμ hln I hI hJ
  exact ⟨e, ⟨vertex_equiv_isForestIso hG H K hH hK φ ψ hφ hψ hφμ hψμ hln I hI hJ e he, he⟩,
    fun e' he' => hunique e' he'.2⟩

theorem IsForestIso.symm (H K : AbsForest n) (e : Fin H.k ≃ Fin K.k)
    (h : IsForestIso H K e) : IsForestIso K H e.symm := by
  constructor
  · intro u
    simpa only [Equiv.apply_symm_apply] using (h.1 (e.symm u)).symm
  · intro u v α
    simpa only [Equiv.apply_symm_apply] using (h.2 (e.symm u) (e.symm v) α).symm

theorem edgeRecord_transport (H K : AbsForest n)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (e : Fin H.k ≃ Fin K.k) (he : ∀ u, ψ (e u) = φ u)
    (p : Fin H.k × Fin H.k) (q : Fin K.k × Fin K.k)
    (hc : K.color q = H.color p)
    (hq : q = (e p.1, e p.2) ∨ q = (e p.2, e p.1))
    (b : PClass n l) (i j : Fin (classSize l G b))
    (hp : edgeRecord H φ b p i j) : edgeRecord K ψ b q i j := by
  rcases hq with rfl | rfl
  · simpa only [edgeRecord, hc, he] using hp
  · simpa only [edgeRecord, hc, he, or_comm] using hp

theorem edgeRel_of_forestIso (H K : AbsForest n)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (e : Fin H.k ≃ Fin K.k) (he : ∀ u, ψ (e u) = φ u) (hiso : IsForestIso H K e)
    (b : PClass n l) (i j : Fin (classSize l G b))
    (h : edgeRel H φ b i j) : edgeRel K ψ b i j := by
  obtain ⟨p, hp, hrec⟩ := h
  have hadj : ColoredAdj H p.1 p.2 (H.color p) := ⟨p, hp, Or.inl rfl, rfl⟩
  obtain ⟨q, hq, hqe, hqc⟩ := (hiso.2 p.1 p.2 (H.color p)).mp hadj
  exact ⟨q, hq, edgeRecord_transport H K φ ψ e he p q hqc hqe b i j hrec⟩

theorem isDbOf_of_forestIso (H K : AbsForest n)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n)
    (e : Fin H.k ≃ Fin K.k) (he : ∀ u, ψ (e u) = φ u) (hiso : IsForestIso H K e)
    (I : Db l G) (hI : H.IsDbOf l G φ I) : K.IsDbOf l G ψ I := by
  have he' : ∀ u, φ (e.symm u) = ψ u := by
    intro u
    simpa only [Equiv.apply_symm_apply] using (he (e.symm u)).symm
  constructor
  · intro i j
    rw [hI.1 i j]
    constructor
    · rintro ⟨u, hu, hj⟩
      exact ⟨e u, (congrArg Fin.val (he u)).trans hu, (hiso.1 u).trans hj⟩
    · rintro ⟨u, hu, hj⟩
      refine ⟨e.symm u, (congrArg Fin.val (he' u)).trans hu, ?_⟩
      rw [← hiso.1 (e.symm u), Equiv.apply_symm_apply]
      exact hj
  · intro b i j
    rw [hI.2 b i j]
    change edgeRel H φ b i j ↔ edgeRel K ψ b i j
    exact ⟨edgeRel_of_forestIso H K φ ψ e he hiso b i j,
      edgeRel_of_forestIso K H ψ φ e.symm he' (hiso.symm H K e) b i j⟩

theorem adj_iff_coloredAdj (H : AbsForest n) (hH : H.IsValid) (u v : Fin H.k) :
    H.graph.Adj u v ↔ ∃ α, ColoredAdj H u v α := by
  constructor
  · rintro ⟨hne, huv | hvu⟩
    · exact ⟨H.color (u, v), (u, v), huv, Or.inl rfl, rfl⟩
    · exact ⟨H.color (v, u), (v, u), hvu, Or.inr rfl, rfl⟩
  · rintro ⟨α, p, hp, he, hc⟩
    rcases he with rfl | rfl
    · exact ⟨ne_of_lt (hH.1 _ hp), Or.inl hp⟩
    · exact ⟨(ne_of_lt (hH.1 _ hp)).symm, Or.inr hp⟩

noncomputable def graphIso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) : H.graph ≃g K.graph where
  toEquiv := e
  map_rel_iff' := by
    intro u v
    rw [adj_iff_coloredAdj K hK, adj_iff_coloredAdj H hH]
    exact exists_congr fun α => (hiso.2 u v α).symm

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathForestAutomorphisms
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical ForestFactorization FiniteWeightedForest

variable {n l : ℕ} {G : WeldedInstance n}

def mapEdge {a b : ℕ} (e : Fin a ≃ Fin b) (p : Fin a × Fin a) : Fin b × Fin b :=
  if e p.1 < e p.2 then (e p.1, e p.2) else (e p.2, e p.1)

lemma mapEdge_eq_of_ordered {a b : ℕ} (e : Fin a ≃ Fin b)
    (p : Fin a × Fin a) (q : Fin b × Fin b) (hq : q.1 < q.2)
    (he : q = (e p.1, e p.2) ∨ q = (e p.2, e p.1)) : mapEdge e p = q := by
  rcases he with rfl | rfl
  · exact if_pos hq
  · exact if_neg (not_lt.mpr (le_of_lt hq))

lemma mapEdge_mem (H K : AbsForest n) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E) : mapEdge e p ∈ K.E := by
  obtain ⟨q, hq, he, hc⟩ := (hiso.2 p.1 p.2 (H.color p)).mp
    ⟨p, hp, Or.inl rfl, rfl⟩
  rw [mapEdge_eq_of_ordered e p q (hK.1 q hq) he]
  exact hq

lemma mapEdge_color (H K : AbsForest n) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E) : K.color (mapEdge e p) = H.color p := by
  obtain ⟨q, hq, he, hc⟩ := (hiso.2 p.1 p.2 (H.color p)).mp
    ⟨p, hp, Or.inl rfl, rfl⟩
  rw [mapEdge_eq_of_ordered e p q (hK.1 q hq) he]
  exact hc

lemma mapEdge_symm_apply {a b : ℕ} (e : Fin a ≃ Fin b) (p : Fin a × Fin a)
    (hp : p.1 < p.2) : mapEdge e.symm (mapEdge e p) = p := by
  by_cases he : e p.1 < e p.2
  · simp [mapEdge, he, hp]
  · simp [mapEdge, he, not_lt.mpr (le_of_lt hp)]

noncomputable def edgeEquiv (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) : ↥H.E ≃ ↥K.E where
  toFun p := ⟨mapEdge e p.1, mapEdge_mem H K hK e hiso p.1 p.2⟩
  invFun q := ⟨mapEdge e.symm q.1, mapEdge_mem K H hH e.symm (hiso.symm H K e) q.1 q.2⟩
  left_inv p := Subtype.ext (mapEdge_symm_apply e p.1 (hH.1 p.1 p.2))
  right_inv q := Subtype.ext (mapEdge_symm_apply e.symm q.1 (hK.1 q.1 q.2))

lemma edgeWeight_iso (hG : G.IsValid) (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    edgeWeight H.E (componentKernel l G H) φ = edgeWeight K.E (componentKernel l G K) ψ := by
  unfold edgeWeight
  rw [← Finset.prod_coe_sort H.E (fun p => componentKernel l G H p (φ p.1) (φ p.2)),
    ← Finset.prod_coe_sort K.E (fun p => componentKernel l G K p (ψ p.1) (ψ p.2))]
  apply Fintype.prod_equiv (edgeEquiv H K hH hK e hiso)
  intro p
  change kappa l G (H.color p.1) (φ p.1.1).1 (φ p.1.2).1 =
    kappa l G (K.color (mapEdge e p.1)) (ψ (mapEdge e p.1).1).1 (ψ (mapEdge e p.1).2).1
  rw [mapEdge_color H K hK e hiso p.1 p.2]
  unfold mapEdge
  split_ifs
  · simp only [he]
  · simp only [he]
    exact KappaKernel.kappa_symm hG _ _ _

lemma comp_eq_of_reachable (H : AbsForest n) (u v : Fin H.k)
    (h : H.graph.Reachable u v) : H.comp u = H.comp v := by
  ext w
  simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hw => h.symm.trans hw, fun hw => h.trans hw⟩

lemma referenceAllowed_iff (l : ℕ) (H : AbsForest n) (u : Fin H.k) (x : Label n) :
    referenceAllowed l H u x ↔
      if (H.comp u).card = 1 then 1 ≤ x.1 else x.1 ∈ Vmid n l ∪ Vbd n l := by
  obtain ⟨s, hs, hsu⟩ := CrossingExclusion.comp_root_exists H u
  have hc : H.comp s = H.comp u := comp_eq_of_reachable H s u hsu
  have hu : u ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsu⟩
  constructor
  · intro h
    split_ifs with hcard
    · have heq : s = u := by
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hc.symm ▸ hcard)
        have hss : s ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl _⟩
        have hs' : s = v := by simpa only [hv, Finset.mem_singleton] using hss
        have hu' : u = v := by simpa only [hv, Finset.mem_singleton] using hu
        exact hs'.trans hu'.symm
      subst s
      exact h.1 hs hcard
    · exact h.2 s hs (hc.symm ▸ hcard) hu
  · intro h
    constructor
    · intro hr hcard
      simpa only [hcard, ite_true] using h
    · intro v hv hcard huv
      have hc' := comp_eq_of_reachable H v u (Finset.mem_filter.mp huv).2
      have hcard' : (H.comp u).card ≠ 1 := hc' ▸ hcard
      simpa only [hcard', ite_false] using h

lemma comp_image_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) (u : Fin H.k) :
    (H.comp u).image e = K.comp (e u) := by
  ext v
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (graphIso H K hH hK e hiso).reachable_iff.mpr (Finset.mem_filter.mp hw).2
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (graphIso H K hH hK e hiso).reachable_iff.mp
    change K.graph.Reachable (e u) (e (e.symm v))
    simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hv).2

lemma referenceAllowed_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) (u : Fin H.k) (x : Label n) :
    referenceAllowed l H u x ↔ referenceAllowed l K (e u) x := by
  have hc : (H.comp u).card = (K.comp (e u)).card := by
    rw [← comp_image_iso H K hH hK e hiso u]
    exact (Finset.card_image_of_injective _ e.injective).symm
  simp only [referenceAllowed_iff, hc]

theorem muRef_automorphism (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k ≃ Fin H.k) (hiso : IsForestIso H H e)
    (φ ψ : Fin H.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    H.muRef l G φ = H.muRef l G ψ := by
  rw [muRef_eq_scale_forestWeight l G H hH, muRef_eq_scale_forestWeight l G H hH]
  congr 1
  unfold forestWeight
  have ha : (∀ u, referenceAllowed l H u (φ u)) ↔
      ∀ u, referenceAllowed l H u (ψ u) := by
    constructor
    · intro h v
      have hh := (referenceAllowed_iso H H hH hH e hiso (e.symm v) (φ (e.symm v))).mp
        (h (e.symm v))
      simpa only [← he, Equiv.apply_symm_apply] using hh
    · intro h u
      apply (referenceAllowed_iso H H hH hH e hiso u (φ u)).mpr
      simpa only [he] using h (e u)
  by_cases h : ∀ u, referenceAllowed l H u (φ u)
  · rw [if_pos h, if_pos (ha.mp h)]
    exact edgeWeight_iso hG H H hH hH e hiso φ ψ he
  · rw [if_neg h, if_neg (fun hh => h (ha.mpr hh))]

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathDatabaseFibers
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

abbrev ForestAut (H : AbsForest n) := {e : Fin H.k ≃ Fin H.k // IsForestIso H H e}

def AssignmentFiber (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (I : Db l G) :=
  {φ : Fin H.k → Label n // Function.Injective φ ∧ H.muRef l G φ ≠ 0 ∧ H.IsDbOf l G φ I}

noncomputable instance (H : AbsForest n) : Fintype (ForestAut H) := inferInstance

theorem forestAut_card_pos (H : AbsForest n) : 0 < Fintype.card (ForestAut H) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨Equiv.refl _, ⟨fun _ => rfl, fun _ _ _ => Iff.rfl⟩⟩⟩

noncomputable instance (H : AbsForest n) (I : Db l G) : Fintype (AssignmentFiber l G H I) :=
  inferInstanceAs (Fintype {φ : Fin H.k → Label n //
    Function.Injective φ ∧ H.muRef l G φ ≠ 0 ∧ H.IsDbOf l G φ I})

noncomputable def autToFiber (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hμ : H.muRef l G φ ≠ 0)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (a : ForestAut H) : AssignmentFiber l G H I := by
  let ψ : Fin H.k → Label n := φ ∘ a.1.symm
  have he : ∀ u, ψ (a.1 u) = φ u := fun u => congrArg φ (a.1.symm_apply_apply u)
  exact ⟨ψ, hφ.comp a.1.symm.injective,
    (muRef_automorphism hG H hH a.1 a.2 φ ψ he) ▸ hμ,
    isDbOf_of_forestIso H H φ ψ a.1 he a.2 I hI⟩

lemma autToFiber_injective (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hμ : H.muRef l G φ ≠ 0)
    (I : Db l G) (hI : H.IsDbOf l G φ I) :
    Function.Injective (autToFiber hG H hH φ hφ hμ I hI) := by
  intro a b hab
  have hf : (φ ∘ a.1.symm) = (φ ∘ b.1.symm) := congrArg Subtype.val hab
  apply Subtype.ext
  have hs : a.1.symm = b.1.symm := Equiv.ext fun u => hφ (congrFun hf u)
  exact congrArg Equiv.symm hs

lemma autToFiber_surjective (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hμ : H.muRef l G φ ≠ 0)
    (hln : l + 2 ≤ n) (I : Db l G) (hI : H.IsDbOf l G φ I) :
    Function.Surjective (autToFiber hG H hH φ hφ hμ I hI) := by
  intro ψ
  obtain ⟨e, ⟨he, hmatch⟩, _⟩ := isDbOf_forest_equiv hG H H hH hH φ ψ.1 hφ ψ.2.1
    hμ ψ.2.2.1 hln I hI ψ.2.2.2
  refine ⟨⟨e, he⟩, ?_⟩
  apply Subtype.ext
  funext u
  change φ (e.symm u) = ψ.1 u
  simpa only [Equiv.apply_symm_apply] using (hmatch (e.symm u)).symm

noncomputable def automorphismFiberEquiv (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hμ : H.muRef l G φ ≠ 0)
    (hln : l + 2 ≤ n) (I : Db l G) (hI : H.IsDbOf l G φ I) :
    ForestAut H ≃ AssignmentFiber l G H I :=
  Equiv.ofBijective (autToFiber hG H hH φ hφ hμ I hI)
    ⟨autToFiber_injective hG H hH φ hφ hμ I hI,
      autToFiber_surjective hG H hH φ hφ hμ hln I hI⟩

theorem assignmentFiber_card (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hμ : H.muRef l G φ ≠ 0)
    (hln : l + 2 ≤ n) (I : Db l G) (hI : H.IsDbOf l G φ I) :
    Fintype.card (AssignmentFiber l G H I) = Fintype.card (ForestAut H) :=
  (Fintype.card_congr (automorphismFiberEquiv hG H hH φ hφ hμ hln I hI)).symm

theorem same_database_muRef (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (φ ψ : Fin H.k → Label n) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφμ : H.muRef l G φ ≠ 0) (hψμ : H.muRef l G ψ ≠ 0) (hln : l + 2 ≤ n)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (hJ : H.IsDbOf l G ψ I) :
    H.muRef l G φ = H.muRef l G ψ := by
  obtain ⟨e, ⟨hiso, he⟩, _⟩ := isDbOf_forest_equiv hG H H hH hH φ ψ hφ hψ hφμ hψμ
    hln I hI hJ
  exact muRef_automorphism hG H hH e hiso φ ψ he

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.UniformFiberEncoding
section

namespace WeldedPath.UniformFiberEncoding

open Classical
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def pushforward (f : A → B) (ψ : Hil A) : Hil B :=
  WithLp.toLp 2 (fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), ψ a)

theorem pushforward_eq_sum (f : A → B) (ψ : Hil A) :
    pushforward f ψ = ∑ a, ψ a • ket (f a) := by
  ext b
  simp [pushforward, HilbertSupport.ket_apply, Finset.sum_filter, eq_comm]

theorem norm_pushforward_sq (f : A → B) (m : ℕ)
    (hcount : ∀ a, (Finset.univ.filter (fun x => f x = f a)).card = m)
    (ψ : Hil A) (hconst : ∀ a a', f a = f a' → ψ a = ψ a') :
    ‖pushforward f ψ‖ ^ 2 = (m : ℝ) * ‖ψ‖ ^ 2 := by
  have hpoint (b : B) :
      ‖∑ a ∈ Finset.univ.filter (fun a => f a = b), ψ a‖ ^ 2 =
        (m : ℝ) * ∑ a ∈ Finset.univ.filter (fun a => f a = b), ‖ψ a‖ ^ 2 := by
    by_cases hb : (Finset.univ.filter (fun a => f a = b)).Nonempty
    · obtain ⟨a, ha⟩ := hb
      have hab : f a = b := (Finset.mem_filter.mp ha).2
      have hc : (Finset.univ.filter (fun a => f a = b)).card = m := by
        simpa only [hab] using hcount a
      have he (x) (hx : x ∈ Finset.univ.filter (fun a => f a = b)) : ψ x = ψ a :=
        hconst x a ((Finset.mem_filter.mp hx).2.trans hab.symm)
      rw [Finset.sum_congr rfl he,
        Finset.sum_congr rfl (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he x hx))]
      simp only [Finset.sum_const, hc, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
      ring
    · have he := Finset.not_nonempty_iff_eq_empty.mp hb
      simp only [he, Finset.sum_empty, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ b, ‖∑ a ∈ Finset.univ.filter (fun a => f a = b), ψ a‖ ^ 2) = _
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (f a)) (fun a => ‖ψ a‖ ^ 2)

noncomputable def fiberAverage (f : A → B) (m : ℕ) (ψ : Hil A) : Hil A :=
  WithLp.toLp 2 (fun a => (m : ℂ)⁻¹ * pushforward f ψ (f a))

theorem fiberAverage_constant (f : A → B) (m : ℕ) (ψ : Hil A)
    (a a' : A) (h : f a = f a') : fiberAverage f m ψ a = fiberAverage f m ψ a' := by
  change (m : ℂ)⁻¹ * pushforward f ψ (f a) = (m : ℂ)⁻¹ * pushforward f ψ (f a')
  rw [h]

theorem pushforward_fiberAverage (f : A → B) (m : ℕ) (hm : 0 < m)
    (hcount : ∀ a, (Finset.univ.filter (fun x => f x = f a)).card = m) (ψ : Hil A) :
    pushforward f (fiberAverage f m ψ) = pushforward f ψ := by
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  ext b
  by_cases hb : (Finset.univ.filter (fun a => f a = b)).Nonempty
  · obtain ⟨a, ha⟩ := hb
    have hab := (Finset.mem_filter.mp ha).2
    have hc : (Finset.univ.filter (fun a => f a = b)).card = m := by
      simpa only [hab] using hcount a
    change (∑ a ∈ Finset.univ.filter (fun a => f a = b),
      (m : ℂ)⁻¹ * pushforward f ψ (f a)) = pushforward f ψ b
    rw [Finset.sum_congr rfl (fun a ha => congrArg
      (fun x => (m : ℂ)⁻¹ * pushforward f ψ x) (Finset.mem_filter.mp ha).2)]
    simp only [Finset.sum_const, hc, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hm', one_mul]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hb
    change (∑ a ∈ Finset.univ.filter (fun a => f a = b), fiberAverage f m ψ a) =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), ψ a
    rw [he, Finset.sum_empty, Finset.sum_empty]

theorem norm_pushforward_sq_average (f : A → B) (m : ℕ) (hm : 0 < m)
    (hcount : ∀ a, (Finset.univ.filter (fun x => f x = f a)).card = m) (ψ : Hil A) :
    ‖pushforward f ψ‖ ^ 2 = (m : ℝ) * ‖fiberAverage f m ψ‖ ^ 2 := by
  rw [← pushforward_fiberAverage f m hm hcount ψ]
  exact norm_pushforward_sq f m hcount _ (fiberAverage_constant f m ψ)

end WeldedPath.UniformFiberEncoding

end

-- Solutions.WeldedPathDatabaseEncoding
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

def SupportedAssignment (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) :=
  {φ : Fin H.k → Label n // Function.Injective φ ∧ H.muRef l G φ ≠ 0}

noncomputable instance (H : AbsForest n) : Fintype (SupportedAssignment l G H) :=
  inferInstanceAs (Fintype {φ : Fin H.k → Label n // Function.Injective φ ∧ H.muRef l G φ ≠ 0})

noncomputable def encodedDb (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ : SupportedAssignment l G H) : Db l G := assignmentDb H hH φ.1 φ.2.1 hG

lemma encodedDb_isDbOf (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ : SupportedAssignment l G H) : H.IsDbOf l G φ.1 (encodedDb H hH hG φ) :=
  assignmentDb_isDbOf H hH φ.1 φ.2.1 hG

noncomputable def encodedFiberEquiv (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (I : Db l G) : {φ : SupportedAssignment l G H // encodedDb H hH hG φ = I} ≃
      AssignmentFiber l G H I where
  toFun φ := by
    refine ⟨φ.1.1, φ.1.2.1, φ.1.2.2, ?_⟩
    have h := encodedDb_isDbOf H hH hG φ.1
    rw [φ.2] at h
    exact h
  invFun φ := ⟨⟨φ.1, φ.2.1, φ.2.2.1⟩,
    isDbOf_unique H φ.1 _ I (assignmentDb_isDbOf H hH φ.1 φ.2.1 hG) φ.2.2.2⟩
  left_inv φ := rfl
  right_inv φ := rfl

lemma encodedDb_fiber_card (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (φ : SupportedAssignment l G H) :
    (Finset.univ.filter (fun ψ => encodedDb H hH hG.2 ψ = encodedDb H hH hG.2 φ)).card =
      Fintype.card (ForestAut H) := by
  rw [← Fintype.card_subtype (fun ψ => encodedDb H hH hG.2 ψ = encodedDb H hH hG.2 φ)]
  rw [Fintype.card_congr (encodedFiberEquiv H hH hG.2 (encodedDb H hH hG.2 φ))]
  exact assignmentFiber_card hG H hH φ.1 φ.2.1 φ.2.2 hln _ (encodedDb_isDbOf H hH hG.2 φ)

noncomputable def encodeState (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (ψ : Hil (SupportedAssignment l G H)) : Hil (Db l G) :=
  UniformFiberEncoding.pushforward (encodedDb H hH hG) ψ

theorem encodeState_eq_basisMap (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (ψ : Hil (SupportedAssignment l G H)) :
    encodeState H hH hG ψ = basisMap (encodedDb H hH hG) ψ := by
  rw [encodeState, UniformFiberEncoding.pushforward_eq_sum]
  simp only [basisMap, ContinuousLinearMap.sum_apply, HilbertSupport.ketBra_apply,
    HilbertSupport.inner_ket]
  apply Finset.sum_congr rfl
  intro φ _
  apply congrArg (fun v => ψ φ • v)
  ext I
  simp only [HilbertSupport.ket_apply] <;> split_ifs <;> rfl

theorem encodeState_norm_sq (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (ψ : Hil (SupportedAssignment l G H))
    (hψ : ∀ φ χ : SupportedAssignment l G H, ∀ e : Fin H.k ≃ Fin H.k,
      IsForestIso H H e → (∀ u, χ.1 (e u) = φ.1 u) → ψ φ = ψ χ) :
    ‖encodeState H hH hG.2 ψ‖ ^ 2 = (Fintype.card (ForestAut H) : ℝ) * ‖ψ‖ ^ 2 := by
  refine UniformFiberEncoding.norm_pushforward_sq _ _ ?_ ψ ?_
  · intro φ
    convert encodedDb_fiber_card hG H hH hln φ using 1
    congr 1
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro φ χ he
    have hI := encodedDb_isDbOf H hH hG.2 φ
    have hJ := encodedDb_isDbOf H hH hG.2 χ
    rw [← he] at hJ
    obtain ⟨e, ⟨hiso, hmatch⟩, _⟩ := isDbOf_forest_equiv hG H H hH hH φ.1 χ.1 φ.2.1 χ.2.1
      φ.2.2 χ.2.2 hln _ hI hJ
    exact hψ φ χ e hiso hmatch

noncomputable def symmetrizeState (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (ψ : Hil (SupportedAssignment l G H)) : Hil (SupportedAssignment l G H) :=
  UniformFiberEncoding.fiberAverage (encodedDb H hH hG) (Fintype.card (ForestAut H)) ψ

theorem encodeState_symmetrize (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (ψ : Hil (SupportedAssignment l G H)) :
    encodeState H hH hG.2 (symmetrizeState H hH hG.2 ψ) = encodeState H hH hG.2 ψ := by
  apply UniformFiberEncoding.pushforward_fiberAverage _ _ (forestAut_card_pos H) ?_ ψ
  intro φ
  convert encodedDb_fiber_card hG H hH hln φ using 1
  congr 1
  ext χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem encodeState_norm_sq_symmetrize (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (ψ : Hil (SupportedAssignment l G H)) :
    ‖encodeState H hH hG.2 ψ‖ ^ 2 =
      (Fintype.card (ForestAut H) : ℝ) * ‖symmetrizeState H hH hG.2 ψ‖ ^ 2 := by
  apply UniformFiberEncoding.norm_pushforward_sq_average _ _ (forestAut_card_pos H) ?_ ψ
  intro φ
  convert encodedDb_fiber_card hG H hH hln φ using 1
  congr 1
  ext χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem database_sum_eq_ket (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hG : G.IsProperColoring) :
    (∑ I ∈ Finset.univ.filter (fun I => H.IsDbOf l G φ I), ket I) =
      ket (assignmentDb H hH φ hφ hG) := by
  have hf : Finset.univ.filter (fun I => H.IsDbOf l G φ I) =
      {assignmentDb H hH φ hφ hG} := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hI
      exact isDbOf_unique H φ I _ hI (assignmentDb_isDbOf H hH φ hφ hG)
    · rintro rfl
      exact assignmentDb_isDbOf H hH φ hφ hG
  rw [hf, Finset.sum_singleton]

noncomputable def totalDb (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ : Fin H.k → Label n) : Db l G :=
  if hφ : Function.Injective φ then assignmentDb H hH φ hφ hG else emptyDb l G

lemma encodedDb_eq_totalDb (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ : SupportedAssignment l G H) : encodedDb H hH hG φ = totalDb H hH hG φ.1 := by
  simp only [totalDb, dif_pos φ.2.1, encodedDb]

theorem gVec_eq_total_sum (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (B : Finset ℕ) : D.gVec l G B =
      ∑ φ, if D.IsGood l G B φ then
        (Real.sqrt (D.H.muRef l G φ) : ℂ) • ket (totalDb D.H hD.1 hG φ) else 0 := by
  unfold Description.gVec
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro φ _
  by_cases hφ : D.IsGood l G B φ
  · rw [if_pos hφ, if_pos hφ, database_sum_eq_ket D.H hD.1 φ hφ.2.2.2 hG]
    simp only [totalDb, dif_pos hφ.2.2.2]
  · rw [if_neg hφ, if_neg hφ]

noncomputable def goodAssignmentState (D : Description n) (B : Finset ℕ) :
    Hil (SupportedAssignment l G D.H) :=
  WithLp.toLp 2 (fun φ => if D.IsGood l G B φ.1 then (Real.sqrt (D.H.muRef l G φ.1) : ℂ) else 0)

theorem encode_goodAssignmentState (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (B : Finset ℕ) : encodeState D.H hD.1 hG (goodAssignmentState D B) = D.gVec l G B := by
  let f : (Fin D.H.k → Label n) → Hil (Db l G) := fun φ =>
    (if D.IsGood l G B φ then (Real.sqrt (D.H.muRef l G φ) : ℂ) else 0) •
      ket (totalDb D.H hD.1 hG φ)
  calc
    _ = ∑ φ : SupportedAssignment l G D.H, f φ.1 := by
      rw [encodeState, UniformFiberEncoding.pushforward_eq_sum]
      apply Finset.sum_congr rfl
      intro φ _
      rw [encodedDb_eq_totalDb]
      ext I
      simp only [f, goodAssignmentState, PiLp.toLp_apply, PiLp.smul_apply,
        HilbertSupport.ket_apply] <;> split_ifs <;> rfl
    _ = ∑ φ ∈ Finset.univ.filter (fun φ : Fin D.H.k → Label n =>
        Function.Injective φ ∧ D.H.muRef l G φ ≠ 0), f φ :=
      (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by
      rw [gVec_eq_total_sum hG D hD B, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro φ _
      by_cases hφ : D.IsGood l G B φ
      · have hp : Function.Injective φ ∧ D.H.muRef l G φ ≠ 0 :=
          ⟨hφ.2.2.2, ne_of_gt hφ.1⟩
        simp only [f, if_pos hφ, if_pos hp]
      · simp only [f, hφ, if_false, zero_smul, ite_self]

theorem gVec_norm_sq (hG : G.IsValid) (D : Description n) (hD : D.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) :
    ‖D.gVec l G B‖ ^ 2 = (Fintype.card (ForestAut D.H) : ℝ) *
      ‖symmetrizeState D.H hD.1 hG.2 (goodAssignmentState (l := l) D B)‖ ^ 2 := by
  rw [← encode_goodAssignmentState hG.2 D hD B]
  exact encodeState_norm_sq_symmetrize hG D.H hD.1 hln _

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathIsolatedVertex
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical CompressedPrimitive
open scoped BigOperators

variable {n : ℕ}

def liftEdge {k : ℕ} (p : Fin k × Fin k) : Fin (k + 1) × Fin (k + 1) :=
  (p.1.castSucc, p.2.castSucc)

lemma liftEdge_injective {k : ℕ} : Function.Injective (@liftEdge k) := by
  intro p q h
  exact Prod.ext (Fin.castSucc_injective _ (congrArg Prod.fst h))
    (Fin.castSucc_injective _ (congrArg Prod.snd h))

lemma mem_image_injective {X Y : Type*} [DecidableEq Y] (f : X → Y)
    (hf : Function.Injective f) (s : Finset X) (x : X) : f x ∈ s.image f ↔ x ∈ s := by
  constructor
  · rintro h
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
    exact hf he ▸ hy
  · intro hx; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

noncomputable abbrev addIsolated (H : AbsForest n) (a : Fin (labelBound n)) : AbsForest n where
  k := H.k + 1
  E := H.E.image liftEdge
  color p := Fin.lastCases 0 (fun u => Fin.lastCases 0 (fun v => H.color (u, v)) p.2) p.1
  lab := Fin.snoc H.lab (some a)

@[simp] lemma addIsolated_lab_old (H : AbsForest n) (a : Fin (labelBound n)) (u : Fin H.k) :
    (addIsolated H a).lab u.castSucc = H.lab u := by
  simp only [Fin.snoc_castSucc]

@[simp] lemma addIsolated_lab_last (H : AbsForest n) (a : Fin (labelBound n)) :
    (addIsolated H a).lab (Fin.last H.k) = some a := by
  simp only [Fin.snoc_last]

@[simp] lemma addIsolated_color (H : AbsForest n) (a : Fin (labelBound n))
    (p : Fin H.k × Fin H.k) : (addIsolated H a).color (liftEdge p) = H.color p := by
  simp only [addIsolated, liftEdge, Fin.lastCases_castSucc]

@[simp] lemma addIsolated_edge (H : AbsForest n) (a : Fin (labelBound n))
    (p : Fin H.k × Fin H.k) : liftEdge p ∈ (addIsolated H a).E ↔ p ∈ H.E := by
  exact mem_image_injective liftEdge liftEdge_injective H.E p

lemma addIsolated_edge_old (H : AbsForest n) (a : Fin (labelBound n))
    (p : Fin (H.k + 1) × Fin (H.k + 1)) (hp : p ∈ (addIsolated H a).E) :
    ∃ q ∈ H.E, liftEdge q = p := Finset.mem_image.mp hp

lemma addIsolated_no_edge_last (H : AbsForest n) (a : Fin (labelBound n))
    (p : Fin (H.k + 1) × Fin (H.k + 1)) (hp : p ∈ (addIsolated H a).E) :
    p.1 ≠ Fin.last H.k ∧ p.2 ≠ Fin.last H.k := by
  obtain ⟨q, _, rfl⟩ := addIsolated_edge_old H a p hp
  exact ⟨Fin.castSucc_ne_last _, Fin.castSucc_ne_last _⟩

lemma addIsolated_adj_old (H : AbsForest n) (a : Fin (labelBound n)) (u v : Fin H.k) :
    (addIsolated H a).graph.Adj u.castSucc v.castSucc ↔ H.graph.Adj u v := by
  change (u.castSucc ≠ v.castSucc ∧ (_ ∨ _)) ↔ (u ≠ v ∧ (_ ∨ _))
  rw [ne_eq, Fin.castSucc_inj, ← ne_eq]
  exact and_congr_right fun _ => or_congr (addIsolated_edge H a (u,v))
    (addIsolated_edge H a (v,u))

lemma addIsolated_not_adj_last (H : AbsForest n) (a : Fin (labelBound n))
    (u : Fin (H.k + 1)) : ¬ (addIsolated H a).graph.Adj (Fin.last H.k) u := by
  rintro ⟨_, hp | hp⟩
  · exact (addIsolated_no_edge_last H a _ hp).1 rfl
  · exact (addIsolated_no_edge_last H a _ hp).2 rfl

noncomputable def oldVertexEquiv (k : ℕ) :
    {u : Fin (k + 1) // u ≠ Fin.last k} ≃ Fin k where
  toFun u := u.val.castPred u.property
  invFun u := ⟨u.castSucc, Fin.castSucc_ne_last u⟩
  left_inv u := Subtype.ext (Fin.castSucc_castPred u.val u.property)
  right_inv u := Fin.castPred_castSucc

noncomputable def addIsolated_oldGraphIso (H : AbsForest n) (a : Fin (labelBound n)) :
    (addIsolated H a).graph.induce {u | u ≠ Fin.last H.k} ≃g H.graph where
  __ := oldVertexEquiv H.k
  map_rel_iff' := by
    intro u v
    change H.graph.Adj (u.val.castPred u.property) (v.val.castPred v.property) ↔
      (addIsolated H a).graph.Adj u.val v.val
    rw [← addIsolated_adj_old H a, Fin.castSucc_castPred, Fin.castSucc_castPred]

lemma addIsolated_acyclic (H : AbsForest n) (a : Fin (labelBound n))
    (hH : H.graph.IsAcyclic) : (addIsolated H a).graph.IsAcyclic := by
  have hlast : ∀ c : (addIsolated H a).graph.Walk (Fin.last H.k) (Fin.last H.k),
      ¬ c.IsCycle := by
    intro c
    cases c with
    | nil => exact SimpleGraph.Walk.not_isCycle_nil
    | cons h p => exact (addIsolated_not_adj_last H a _ h).elim
  intro u c hc
  have hs : ∀ x ∈ c.support, x ∈ {v : Fin (H.k + 1) | v ≠ Fin.last H.k} := by
    intro x hx hxl
    subst x
    exact hlast (c.rotate (Fin.last H.k) hx) (hc.rotate hx)
  have hi : (c.induce _ hs).IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    rw [SimpleGraph.Walk.map_induce]
    exact hc
  exact ((addIsolated_oldGraphIso H a).isAcyclic_iff.mpr hH) _ hi

theorem addIsolated_valid (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a) :
    (addIsolated H a).IsValid := by
  refine ⟨?_, addIsolated_acyclic H a hH.2.1, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := addIsolated_edge_old H a p hp
    exact hH.1 q hq
  · intro p hp q hq hpq hadj
    obtain ⟨p', hp', rfl⟩ := addIsolated_edge_old H a p hp
    obtain ⟨q', hq', rfl⟩ := addIsolated_edge_old H a q hq
    rw [addIsolated_color, addIsolated_color]
    apply hH.2.2.1 p' hp' q' hq' (fun h => hpq (congrArg liftEdge h))
    simpa only [liftEdge, Fin.castSucc_inj] using hadj
  · intro u v j hu hv
    induction u using Fin.lastCases with
    | last =>
      have haj : a = j := Option.some.inj ((addIsolated_lab_last H a).symm.trans hu)
      induction v using Fin.lastCases with
      | last => rfl
      | cast v => exact (ha v (by simpa only [Fin.snoc_castSucc, ← haj] using hv)).elim
    | cast u =>
      induction v using Fin.lastCases with
      | last =>
        have haj : a = j := Option.some.inj ((addIsolated_lab_last H a).symm.trans hv)
        exact (ha u (by simpa only [Fin.snoc_castSucc, ← haj] using hu)).elim
      | cast v =>
        exact congrArg Fin.castSucc (hH.2.2.2.1 u v j
          ((addIsolated_lab_old H a u).symm.trans hu)
          ((addIsolated_lab_old H a v).symm.trans hv))
  · intro u
    induction u using Fin.lastCases with
    | last => exact Or.inl (by simp only [Fin.snoc_last, Option.isSome_some])
    | cast u =>
      rcases hH.2.2.2.2 u with hu | ⟨p,hp,hpu⟩
      · exact Or.inl (by simpa only [Fin.snoc_castSucc] using hu)
      · exact Or.inr ⟨liftEdge p, (addIsolated_edge H a p).mpr hp,
          hpu.imp (congrArg Fin.castSucc) (congrArg Fin.castSucc)⟩

theorem addIsolated_records (H : AbsForest n) (a : Fin (labelBound n)) :
    (addIsolated H a).records = H.records + 1 := by
  have hs : (Finset.univ.filter (fun u => ((addIsolated H a).lab u).isSome)) =
      insert (Fin.last H.k)
        ((Finset.univ.filter (fun u => (H.lab u).isSome)).image Fin.castSucc) := by
    ext u
    induction u using Fin.lastCases with
    | last => simp [addIsolated, Fin.snoc_last, Fin.castSucc_ne_last]
    | cast u =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.castSucc_ne_last, false_or, Finset.mem_image, Fin.snoc_castSucc]
      constructor
      · intro hu; exact ⟨u, hu, rfl⟩
      · rintro ⟨v, hv, he⟩
        exact Fin.castSucc_injective _ he ▸ hv
  have hn : Fin.last H.k ∉
      ((Finset.univ.filter (fun u => (H.lab u).isSome)).image Fin.castSucc) := by
    rintro h
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
    exact Fin.castSucc_ne_last u hu
  unfold AbsForest.records
  rw [hs, Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
  change (H.E.image liftEdge).card + (_ + 1) = _
  rw [Finset.card_image_of_injective _ liftEdge_injective]
  omega

theorem isDbOf_addIsolated {l : ℕ} {G : WeldedInstance n}
    (H : AbsForest n) (φ : Fin H.k → Label n) (I : Db l G)
    (hI : H.IsDbOf l G φ I) (x a : Fin (labelBound n))
    (hx : ∀ u, (φ u).val ≠ x.val + 1) (ha : ∀ u, H.lab u ≠ some a)
    (ψ : Fin (H.k + 1) → Label n) (hψ : ∀ u, ψ u.castSucc = φ u)
    (hlast : (ψ (Fin.last H.k)).val = x.val + 1) :
    (addIsolated H a).IsDbOf l G ψ (I.1.addPair x a, I.2) := by
  have hdom : I.1 x = none := by
    cases hh : I.1 x with
    | none => rfl
    | some j =>
      obtain ⟨u, hu, _⟩ := (hI.1 x j).mp hh
      exact (hx u hu).elim
  have him := label_db_unused H φ I hI a ha
  refine ⟨?_, ?_⟩
  · intro i j
    by_cases hix : i = x
    · subst i
      rw [addPair_apply_self _ x a hdom him]
      constructor
      · intro haj
        exact ⟨Fin.last H.k, hlast, (addIsolated_lab_last H a).trans haj⟩
      · rintro ⟨u, hu, huj⟩
        induction u using Fin.lastCases with
        | last => exact (addIsolated_lab_last H a).symm.trans huj
        | cast u => exact (hx u (by simpa only [hψ] using hu)).elim
    · rw [addPair_apply_other _ x a i hdom him hix, hI.1]
      constructor
      · rintro ⟨u, hu, huj⟩
        exact ⟨u.castSucc, (congrArg Fin.val (hψ u)).trans hu,
          (addIsolated_lab_old H a u).trans huj⟩
      · rintro ⟨u, hu, huj⟩
        induction u using Fin.lastCases with
        | last => exact (hix (Fin.ext (Nat.add_right_cancel (hu.symm.trans hlast)))).elim
        | cast u =>
          exact ⟨u, (congrArg Fin.val (hψ u)).symm.trans hu,
            (addIsolated_lab_old H a u).symm.trans huj⟩
  · intro b j j'
    rw [hI.2]
    constructor
    · rintro ⟨p, hp, he⟩
      refine ⟨liftEdge p, (addIsolated_edge H a p).mpr hp, ?_⟩
      simpa only [addIsolated_color, liftEdge, Fin.lastCases_castSucc, hψ] using he
    · rintro ⟨p, hp, he⟩
      obtain ⟨q, hq, rfl⟩ := addIsolated_edge_old H a p hp
      exact ⟨q, hq, by simpa only [addIsolated_color, liftEdge, Fin.lastCases_castSucc, hψ] using he⟩

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathFixedDataIsomorphism
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n : ℕ}

lemma tree_adj_iff (H : AbsForest n) (φ : Fin H.k → Label n) (u v : Fin H.k) :
    (H.treeGraph φ).Adj u v ↔
      H.graph.Adj u v ∧ ¬ ((φ u).val ∈ Vweld n ∧ (φ v).val ∈ Vweld n) := by
  change (u ≠ v ∧ (((u,v) ∈ H.E ∧ ¬ _) ∨ ((v,u) ∈ H.E ∧ ¬ _))) ↔ _
  simp only [AbsForest.IsWeldUnder]
  change (u ≠ v ∧ (((u,v) ∈ H.E ∧ ¬ _) ∨ ((v,u) ∈ H.E ∧ ¬ _))) ↔
    (u ≠ v ∧ ((u,v) ∈ H.E ∨ (v,u) ∈ H.E)) ∧ ¬ _
  tauto

noncomputable def treeGraphIso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    H.treeGraph φ ≃g K.treeGraph ψ where
  toEquiv := e
  map_rel_iff' := by
    intro u v
    rw [tree_adj_iff, tree_adj_iff, he, he]
    exact and_congr (graphIso H K hH hK e hiso).map_rel_iff Iff.rfl

lemma ctree_mem_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u)
    (u v : Fin H.k) : e u ∈ K.Ctree ψ (e v) ↔ u ∈ H.Ctree φ v := by
  simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (treeGraphIso H K hH hK e hiso φ ψ he).reachable_iff

lemma sfix_mem_iff_closed_neighborhood (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (u v : Fin H.k) :
    u ∈ H.Sfix φ v ↔ u ∈ H.Ctree φ v ∨
      ∃ w ∈ H.Ctree φ v, H.graph.Adj w u := by
  constructor
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Or.inl hu
    · obtain ⟨p,hp,_,hpv⟩ := (Finset.mem_filter.mp hu).2
      rcases hpv with ⟨hv,rfl⟩ | ⟨hv,rfl⟩
      · exact Or.inr ⟨p.1,hv,ne_of_lt (hH.1 p hp),Or.inl hp⟩
      · exact Or.inr ⟨p.2,hv,(ne_of_lt (hH.1 p hp)).symm,Or.inr hp⟩
  · rintro (hu | ⟨w,hw,hwu⟩)
    · exact FixedData.ctree_subset_sfix H φ v hu
    · rcases hwu with ⟨_,hp|hp⟩
      · exact (FixedData.edge_endpoints_mem_sfix H hH φ v (w,u) hp (Or.inl hw)).2
      · exact (FixedData.edge_endpoints_mem_sfix H hH φ v (u,w) hp (Or.inr hw)).1

lemma sfix_mem_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u)
    (u v : Fin H.k) : e u ∈ K.Sfix ψ (e v) ↔ u ∈ H.Sfix φ v := by
  rw [sfix_mem_iff_closed_neighborhood K hK, sfix_mem_iff_closed_neighborhood H hH,
    ctree_mem_iso H K hH hK e hiso φ ψ he]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨w,hw,hwu⟩
    obtain ⟨w,rfl⟩ := e.surjective w
    exact ⟨w,(ctree_mem_iso H K hH hK e hiso φ ψ he w v).mp hw,
      (graphIso H K hH hK e hiso).map_rel_iff.mp hwu⟩
  · rintro ⟨w,hw,hwu⟩
    exact ⟨e w,(ctree_mem_iso H K hH hK e hiso φ ψ he w v).mpr hw,
      (graphIso H K hH hK e hiso).map_rel_iff.mpr hwu⟩

lemma wfix_fiber_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (φ φ₀ : Fin H.k → Label n) (ψ ψ₀ : Fin K.k → Label n)
    (he : ∀ u, ψ (e u) = φ u) (he₀ : ∀ u, ψ₀ (e u) = φ₀ u) (v : Fin H.k) :
    K.Wfix ψ (e v) = K.Wfix ψ₀ (e v) ↔ H.Wfix φ v = H.Wfix φ₀ v := by
  rw [FixedData.wfix_eq_iff_agree_sfix K hK, FixedData.wfix_eq_iff_agree_sfix H hH]
  constructor
  · intro h u hu
    simpa only [he,he₀] using h (e u) ((sfix_mem_iso H K hH hK e hiso φ₀ ψ₀ he₀ u v).mpr hu)
  · intro h u hu
    obtain ⟨u,rfl⟩ := e.surjective u
    rw [he,he₀]
    exact h u ((sfix_mem_iso H K hH hK e hiso φ₀ ψ₀ he₀ u v).mp hu)

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathIsolatedFixedData
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}

lemma addIsolated_tree_adj_old (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) (u v : Fin H.k) :
    ((addIsolated H a).treeGraph ψ).Adj u.castSucc v.castSucc ↔
      (H.treeGraph (fun w => ψ w.castSucc)).Adj u v := by
  rw [tree_adj_iff,tree_adj_iff,addIsolated_adj_old]

lemma addIsolated_tree_not_adj_last (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) (u : Fin (H.k+1)) :
    ¬ ((addIsolated H a).treeGraph ψ).Adj (Fin.last H.k) u :=
  fun h => addIsolated_not_adj_last H a u ((tree_adj_iff _ _ _ _).mp h).1

lemma addIsolated_tree_reachable_last (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) (u : Fin (H.k+1)) :
    ((addIsolated H a).treeGraph ψ).Reachable (Fin.last H.k) u ↔ u = Fin.last H.k := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact (addIsolated_tree_not_adj_last H a ψ _ h).elim
  · rintro rfl
    exact .refl _

noncomputable abbrev addIsolated_tree_embedding (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) :
    H.treeGraph (fun w => ψ w.castSucc) ↪g (addIsolated H a).treeGraph ψ where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective _
  map_rel_iff' := by
    intro u v
    exact addIsolated_tree_adj_old H a ψ u v

noncomputable abbrev addIsolated_tree_oldIso (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) :
    ((addIsolated H a).treeGraph ψ).induce {u | u ≠ Fin.last H.k} ≃g
      H.treeGraph (fun w => ψ w.castSucc) where
  __ := oldVertexEquiv H.k
  map_rel_iff' := by
    intro u v
    change (H.treeGraph (fun w => ψ w.castSucc)).Adj
      (u.val.castPred u.property) (v.val.castPred v.property) ↔
      ((addIsolated H a).treeGraph ψ).Adj u.val v.val
    rw [← addIsolated_tree_adj_old H a ψ,Fin.castSucc_castPred,Fin.castSucc_castPred]

lemma addIsolated_tree_reachable_old (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) (u v : Fin H.k) :
    ((addIsolated H a).treeGraph ψ).Reachable u.castSucc v.castSucc ↔
      (H.treeGraph (fun w => ψ w.castSucc)).Reachable u v := by
  constructor
  · rintro ⟨p⟩
    have hs : ∀ x ∈ p.support, x ∈ {v : Fin (H.k+1) | v ≠ Fin.last H.k} := by
      intro x hx hxl
      have hr := (p.takeUntil x hx).reachable.symm
      rw [hxl] at hr
      exact Fin.castSucc_ne_last u ((addIsolated_tree_reachable_last H a ψ _).mp hr)
    have hr := (p.induce _ hs).reachable.map (addIsolated_tree_oldIso H a ψ).toHom
    change (H.treeGraph (fun w => ψ w.castSucc)).Reachable
      (u.castSucc.castPred (Fin.castSucc_ne_last u))
      (v.castSucc.castPred (Fin.castSucc_ne_last v)) at hr
    simpa only [Fin.castPred_castSucc] using hr
  · intro h
    exact h.map (addIsolated_tree_embedding H a ψ).toHom

lemma addIsolated_ctree_last (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) :
    (addIsolated H a).Ctree ψ (Fin.last H.k) = {Fin.last H.k} := by
  ext u
  simp only [AbsForest.Ctree,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  exact addIsolated_tree_reachable_last H a ψ u

lemma addIsolated_ctree_old (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k+1) → Label n) (s : Fin H.k) :
    (addIsolated H a).Ctree ψ s.castSucc =
      (H.Ctree (fun w => ψ w.castSucc) s).image Fin.castSucc := by
  ext u
  induction u using Fin.lastCases with
  | last =>
    have hn : ¬ ((addIsolated H a).treeGraph ψ).Reachable s.castSucc (Fin.last H.k) := by
      intro h
      exact Fin.castSucc_ne_last s ((addIsolated_tree_reachable_last H a ψ _).mp h.symm)
    simp only [AbsForest.Ctree,Finset.mem_filter,Finset.mem_univ,true_and,hn,Finset.mem_image]
    exact (iff_false_intro (by rintro ⟨v,_,hv⟩; exact Fin.castSucc_ne_last v hv)).symm
  | cast u =>
    rw [mem_image_injective Fin.castSucc (Fin.castSucc_injective _)]
    simp only [AbsForest.Ctree,Finset.mem_filter,Finset.mem_univ,true_and]
    exact addIsolated_tree_reachable_old H a ψ s u

lemma addIsolated_sfix_last (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u,H.lab u ≠ some a)
    (ψ : Fin (H.k+1) → Label n) :
    (addIsolated H a).Sfix ψ (Fin.last H.k) = {Fin.last H.k} := by
  ext u
  rw [sfix_mem_iff_closed_neighborhood _ (addIsolated_valid H hH a ha),addIsolated_ctree_last]
  simp only [Finset.mem_singleton,exists_eq_left]
  exact or_iff_left (addIsolated_not_adj_last H a u)

lemma addIsolated_sfix_old (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u,H.lab u ≠ some a)
    (ψ : Fin (H.k+1) → Label n) (s : Fin H.k) :
    (addIsolated H a).Sfix ψ s.castSucc =
      (H.Sfix (fun w => ψ w.castSucc) s).image Fin.castSucc := by
  ext u
  rw [sfix_mem_iff_closed_neighborhood _ (addIsolated_valid H hH a ha),addIsolated_ctree_old]
  constructor
  · rintro (hu | ⟨v,hv,hvu⟩)
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_image.mpr ⟨w,FixedData.ctree_subset_sfix H _ s hw,rfl⟩
    · obtain ⟨v,hvOld,rfl⟩ := Finset.mem_image.mp hv
      induction u using Fin.lastCases with
      | last => exact (addIsolated_not_adj_last H a _ hvu.symm).elim
      | cast u =>
        exact Finset.mem_image.mpr ⟨u,(sfix_mem_iff_closed_neighborhood H hH _ u s).mpr
          (Or.inr ⟨v,hvOld,(addIsolated_adj_old H a v u).mp hvu⟩),rfl⟩
  · intro hu
    obtain ⟨u,huOld,rfl⟩ := Finset.mem_image.mp hu
    rcases (sfix_mem_iff_closed_neighborhood H hH _ u s).mp huOld with hu | ⟨v,hv,hvu⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
    · exact Or.inr ⟨v.castSucc,Finset.mem_image.mpr ⟨v,hv,rfl⟩,
        (addIsolated_adj_old H a v u).mpr hvu⟩

theorem addIsolated_wfix_fiber_old (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u,H.lab u ≠ some a)
    (ψ χ : Fin (H.k+1) → Label n) (s : Fin H.k) :
    (addIsolated H a).Wfix ψ s.castSucc = (addIsolated H a).Wfix χ s.castSucc ↔
      H.Wfix (fun w => ψ w.castSucc) s = H.Wfix (fun w => χ w.castSucc) s := by
  rw [FixedData.wfix_eq_iff_agree_sfix _ (addIsolated_valid H hH a ha),
    addIsolated_sfix_old H hH a ha,FixedData.wfix_eq_iff_agree_sfix H hH]
  constructor
  · intro h u hu
    exact h u.castSucc (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
  · intro h u hu
    obtain ⟨u,huOld,rfl⟩ := Finset.mem_image.mp hu
    exact h u huOld

theorem addIsolated_wfix_fiber_last (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u,H.lab u ≠ some a)
    (ψ χ : Fin (H.k+1) → Label n) :
    (addIsolated H a).Wfix ψ (Fin.last H.k) = (addIsolated H a).Wfix χ (Fin.last H.k) ↔
      ψ (Fin.last H.k) = χ (Fin.last H.k) := by
  rw [FixedData.wfix_eq_iff_agree_sfix _ (addIsolated_valid H hH a ha),addIsolated_sfix_last H hH a ha]
  simp only [Finset.mem_singleton,forall_eq]

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathIsolatedMeasure
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical ForestFactorization FiniteWeightedForest
open scoped BigOperators

variable {n : ℕ}

lemma addIsolated_reachable_last (H : AbsForest n) (a : Fin (labelBound n))
    (u : Fin (H.k + 1)) :
    (addIsolated H a).graph.Reachable (Fin.last H.k) u ↔ u = Fin.last H.k := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact (addIsolated_not_adj_last H a _ h).elim
  · rintro rfl; exact .refl _

noncomputable def addIsolated_embedding (H : AbsForest n) (a : Fin (labelBound n)) :
    H.graph ↪g (addIsolated H a).graph where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective _
  map_rel_iff' := fun {u v} => addIsolated_adj_old H a u v

lemma addIsolated_reachable_old (H : AbsForest n) (a : Fin (labelBound n))
    (u v : Fin H.k) :
    (addIsolated H a).graph.Reachable u.castSucc v.castSucc ↔ H.graph.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    have hs : ∀ x ∈ p.support, x ∈ {v : Fin (H.k + 1) | v ≠ Fin.last H.k} := by
      intro x hx hxl
      have hr := (p.takeUntil x hx).reachable.symm
      rw [hxl] at hr
      exact Fin.castSucc_ne_last u ((addIsolated_reachable_last H a _).mp hr)
    have hr := (p.induce _ hs).reachable.map (addIsolated_oldGraphIso H a).toHom
    change H.graph.Reachable (u.castSucc.castPred (Fin.castSucc_ne_last u))
      (v.castSucc.castPred (Fin.castSucc_ne_last v)) at hr
    simpa only [Fin.castPred_castSucc] using hr
  · intro h
    have hh := h.map (addIsolated_embedding H a).toHom
    change (addIsolated H a).graph.Reachable u.castSucc v.castSucc at hh
    exact hh

lemma addIsolated_comp_last (H : AbsForest n) (a : Fin (labelBound n)) :
    (addIsolated H a).comp (Fin.last H.k) = {Fin.last H.k} := by
  ext u
  simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  exact addIsolated_reachable_last H a u

lemma addIsolated_comp_old (H : AbsForest n) (a : Fin (labelBound n)) (s : Fin H.k) :
    (addIsolated H a).comp s.castSucc = (H.comp s).image Fin.castSucc := by
  ext u
  induction u using Fin.lastCases with
  | last =>
    have hn : ¬(addIsolated H a).graph.Reachable s.castSucc (Fin.last H.k) := by
      intro h
      exact Fin.castSucc_ne_last s ((addIsolated_reachable_last H a _).mp h.symm)
    simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and, hn,
      Finset.mem_image]
    exact iff_false_intro (by rintro ⟨v, _, hv⟩; exact Fin.castSucc_ne_last v hv) |>.symm
  | cast u =>
    rw [mem_image_injective Fin.castSucc (Fin.castSucc_injective _) (H.comp s) u]
    simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact addIsolated_reachable_old H a s u

lemma addIsolated_root_old (H : AbsForest n) (a : Fin (labelBound n)) (s : Fin H.k) :
    (addIsolated H a).IsCompRoot s.castSucc ↔ H.IsCompRoot s := by
  constructor
  · intro h v hv
    exact h v.castSucc ((addIsolated_reachable_old H a s v).mpr hv)
  · intro h v hv
    induction v using Fin.lastCases with
    | last => exact Fin.le_last _
    | cast v => exact h v ((addIsolated_reachable_old H a s v).mp hv)

lemma addIsolated_root_last (H : AbsForest n) (a : Fin (labelBound n)) :
    (addIsolated H a).IsCompRoot (Fin.last H.k) := by
  intro u hu
  rw [(addIsolated_reachable_last H a u).mp hu]

lemma addIsolated_componentEdges (H : AbsForest n) (a : Fin (labelBound n))
    (s : Fin H.k) :
    componentEdges (addIsolated H a) s.castSucc = (componentEdges H s).image liftEdge := by
  ext p
  constructor
  · rintro hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨q, hq, rfl⟩ := addIsolated_edge_old H a p hp
    refine Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩, rfl⟩
    rw [addIsolated_comp_old] at hs
    exact (mem_image_injective Fin.castSucc (Fin.castSucc_injective _) (H.comp s) q.1).mp hs
  · rintro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq, hs⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(addIsolated_edge H a q).mpr hq,
      by rw [addIsolated_comp_old]; exact Finset.mem_image.mpr ⟨q.1, hs, rfl⟩⟩

lemma addIsolated_edgeWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (a : Fin (labelBound n)) (s : Fin H.k) (ψ : Fin (H.k + 1) → Label n) :
    edgeWeight (componentEdges (addIsolated H a) s.castSucc)
        (componentKernel l G (addIsolated H a)) ψ =
      edgeWeight (componentEdges H s) (componentKernel l G H) (fun u => ψ u.castSucc) := by
  rw [addIsolated_componentEdges]
  unfold edgeWeight
  rw [Finset.prod_image (fun p _ q _ hpq => liftEdge_injective hpq)]
  apply Finset.prod_congr rfl
  intro p hp
  change kappa l G ((addIsolated H a).color (liftEdge p)) _ _ = _
  rw [addIsolated_color]
  rfl

lemma addIsolated_component_all (H : AbsForest n) (a : Fin (labelBound n))
    (s : Fin H.k) (ψ : Fin (H.k + 1) → Label n) (P : Label n → Prop) :
    (∀ u ∈ (addIsolated H a).comp s.castSucc, P (ψ u)) ↔
      ∀ u ∈ H.comp s, P (ψ u.castSucc) := by
  rw [addIsolated_comp_old]
  constructor
  · intro h u hu; exact h _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact h v hv

lemma addIsolated_component_off (H : AbsForest n) (a : Fin (labelBound n))
    (s : Fin H.k) (ψ : Fin (H.k + 1) → Label n) :
    (∀ u, u ∉ (addIsolated H a).comp s.castSucc → ψ u = 0) ↔
      (∀ u, u ∉ H.comp s → ψ u.castSucc = 0) ∧ ψ (Fin.last H.k) = 0 := by
  rw [addIsolated_comp_old]
  have hlast : Fin.last H.k ∉ (H.comp s).image Fin.castSucc := by
    rintro hh
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hh
    exact Fin.castSucc_ne_last u hu
  constructor
  · intro h
    exact ⟨fun u hu => h _ (fun hh => hu ((mem_image_injective Fin.castSucc
      (Fin.castSucc_injective _) (H.comp s) u).mp hh)), h _ hlast⟩
  · rintro ⟨h, hl⟩ u hu
    induction u using Fin.lastCases with
    | last => exact hl
    | cast u => exact h u (fun hh => hu (Finset.mem_image.mpr ⟨u, hh, rfl⟩))

theorem addIsolated_supported_sum (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (a : Fin (labelBound n)) (s : Fin H.k) (V : Finset ℕ) :
    (∑ φ ∈ Finset.univ.filter (fun φ : Fin H.k → Label n =>
      (∀ u ∈ H.comp s, (φ u).val ∈ V) ∧ (∀ u, u ∉ H.comp s → φ u = 0)),
        edgeWeight (componentEdges H s) (componentKernel l G H) φ) =
      ∑ ψ ∈ Finset.univ.filter (fun ψ : Fin (H.k + 1) → Label n =>
        (∀ u ∈ (addIsolated H a).comp s.castSucc, (ψ u).val ∈ V) ∧
        (∀ u, u ∉ (addIsolated H a).comp s.castSucc → ψ u = 0)),
          edgeWeight (componentEdges (addIsolated H a) s.castSucc)
            (componentKernel l G (addIsolated H a)) ψ := by
  apply Finset.sum_bij (fun (φ : Fin H.k → Label n) _ =>
    (Fin.snoc φ 0 : Fin (H.k + 1) → Label n))
  · intro φ hφ
    obtain ⟨hφ, hzero⟩ := (Finset.mem_filter.mp hφ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · apply (addIsolated_component_all H a s
        (Fin.snoc φ 0 : Fin (H.k + 1) → Label n) (fun x => x.val ∈ V)).mpr
      simpa only [Fin.snoc_castSucc] using hφ
    · apply (addIsolated_component_off H a s _).mpr
      constructor
      · simpa only [Fin.snoc_castSucc] using hzero
      · simp only [Fin.snoc_last]
  · intro φ _ φ' _ h
    funext u
    have hh := congrFun h u.castSucc
    simpa only [Fin.snoc_castSucc] using hh
  · intro ψ hψ
    obtain ⟨hψ, hzero⟩ := (Finset.mem_filter.mp hψ).2
    have hz := (addIsolated_component_off H a s ψ).mp hzero
    refine ⟨fun u => ψ u.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (addIsolated_component_all H a s ψ (fun x => x.val ∈ V)).mp hψ, hz.1⟩, ?_⟩
    funext u
    induction u using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hz.2.symm
    | cast u => simp only [Fin.snoc_castSucc]
  · intro φ _
    symm
    simpa only [Fin.snoc_castSucc] using addIsolated_edgeWeight l G H a s (Fin.snoc φ 0)

lemma addIsolated_componentScale (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (a : Fin (labelBound n)) (s : Fin H.k) :
    componentScale l G (addIsolated H a) s.castSucc = componentScale l G H s := by
  unfold componentScale
  dsimp only
  rw [← addIsolated_supported_sum l G H a s]

lemma addIsolated_componentCondition (l : ℕ) (H : AbsForest n)
    (a : Fin (labelBound n)) (s : Fin H.k) (ψ : Fin (H.k + 1) → Label n) :
    componentCondition l (addIsolated H a) s.castSucc ψ ↔
      componentCondition l H s (fun u => ψ u.castSucc) := by
  unfold componentCondition
  rw [addIsolated_comp_old, Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
  split_ifs
  · rfl
  · simpa only [addIsolated_comp_old] using
      addIsolated_component_all H a s ψ (fun x => x.val ∈ Vmid n l ∪ Vbd n l)

theorem addIsolated_muComp_old (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (s : Fin H.k) (ψ : Fin (H.k + 1) → Label n) :
    (addIsolated H a).muComp l G s.castSucc ψ = H.muComp l G s (fun u => ψ u.castSucc) := by
  rw [muComp_eq_componentCondition l G _ (addIsolated_valid H hH a ha),
    muComp_eq_componentCondition l G H hH,
    addIsolated_comp_old, Finset.card_image_of_injective _ (Fin.castSucc_injective _),
    addIsolated_componentScale, addIsolated_edgeWeight,
    propext (addIsolated_componentCondition l H a s ψ)]

lemma addIsolated_roots (H : AbsForest n) (a : Fin (labelBound n)) :
    Finset.univ.filter (addIsolated H a).IsCompRoot =
      insert (Fin.last H.k) ((Finset.univ.filter H.IsCompRoot).image Fin.castSucc) := by
  ext u
  induction u using Fin.lastCases with
  | last => simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      addIsolated_root_last, Finset.mem_insert, true_or]
  | cast u =>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, addIsolated_root_old,
      Finset.mem_insert, Fin.castSucc_ne_last, false_or]
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (mem_image_injective Fin.castSucc (Fin.castSucc_injective _)
        (Finset.univ.filter H.IsCompRoot) u).symm

theorem addIsolated_muRef (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (ψ : Fin (H.k + 1) → Label n) :
    (addIsolated H a).muRef l G ψ = H.muRef l G (fun u => ψ u.castSucc) *
      (if 1 ≤ (ψ (Fin.last H.k)).val then 1 / (labelBound n : ℝ) else 0) := by
  have hn : Fin.last H.k ∉ (Finset.univ.filter H.IsCompRoot).image Fin.castSucc := by
    rintro hh
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hh
    exact Fin.castSucc_ne_last u hu
  unfold AbsForest.muRef
  rw [addIsolated_roots, Finset.prod_insert hn,
    Finset.prod_image (fun u _ v _ h => Fin.castSucc_injective _ h)]
  have hl : (addIsolated H a).muComp l G (Fin.last H.k) ψ =
      (if 1 ≤ (ψ (Fin.last H.k)).val then 1 / (labelBound n : ℝ) else 0) := by
    simp only [AbsForest.muComp, addIsolated_comp_last, Finset.card_singleton, ite_true]
  rw [hl, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro u hu
  exact addIsolated_muComp_old l G H hH a ha u ψ

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathIsolatedDescription
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical ForestFactorization

variable {n : ℕ}

noncomputable abbrev addIsolatedDescription (D : Description n)
    (a : Fin (labelBound n)) (x : Label n) : Description n :=
  ⟨addIsolated D.H a,insert (Fin.last D.H.k) (D.sel.image Fin.castSucc),Fin.snoc D.ϕ₀ x⟩

theorem addIsolatedDescription_valid (D : Description n) (hD : D.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u,D.H.lab u ≠ some a) (x : Label n) :
    (addIsolatedDescription D a x).IsValid := by
  refine ⟨addIsolated_valid D.H hD.1 a ha,?_⟩
  intro u
  induction u using Fin.lastCases with
  | last =>
    refine ⟨Fin.last D.H.k,⟨Finset.mem_insert_self _ _,.refl _⟩,?_⟩
    intro s hs
    exact (addIsolated_reachable_last D.H a s).mp hs.2
  | cast u =>
    obtain ⟨s,hs,hunique⟩ := hD.2 u
    refine ⟨s.castSucc,⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s,hs.1,rfl⟩),
      (addIsolated_reachable_old D.H a u s).mpr hs.2⟩,?_⟩
    intro v hv
    induction v using Fin.lastCases with
    | last =>
      exact (Fin.castSucc_ne_last u ((addIsolated_reachable_last D.H a _).mp hv.2.symm)).elim
    | cast v =>
      apply congrArg Fin.castSucc
      apply hunique v
      refine ⟨?_,(addIsolated_reachable_old D.H a u v).mp hv.2⟩
      exact (mem_image_injective Fin.castSucc (Fin.castSucc_injective _) D.sel v).mp
        ((Finset.mem_insert.mp hv.1).resolve_left (Fin.castSucc_ne_last v))

theorem addIsolatedDescription_fixed (D : Description n) (hD : D.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u,D.H.lab u ≠ some a) (x : Label n)
    (ψ : Fin (D.H.k+1) → Label n) :
    (∀ s ∈ (addIsolatedDescription D a x).sel,
      (addIsolated D.H a).Wfix ψ s = (addIsolated D.H a).Wfix (Fin.snoc D.ϕ₀ x) s) ↔
      (ψ (Fin.last D.H.k) = x ∧
        ∀ s ∈ D.sel,D.H.Wfix (fun u => ψ u.castSucc) s = D.H.Wfix D.ϕ₀ s) := by
  simp only [Finset.forall_mem_insert,Finset.forall_mem_image,
    addIsolated_wfix_fiber_last D.H hD.1 a ha,
    addIsolated_wfix_fiber_old D.H hD.1 a ha,Fin.snoc_last,Fin.snoc_castSucc]

lemma addIsolated_boundary_old (H : AbsForest n) (a : Fin (labelBound n))
    (B : Finset ℕ) (ψ : Fin (H.k+1) → Label n) (s : Fin H.k) :
    (∀ u,(addIsolated H a).graph.Reachable s.castSucc u →
      u ∉ (addIsolated H a).Ctree ψ s.castSucc → (ψ u).val ∉ B) ↔
    ∀ u,H.graph.Reachable s u → u ∉ H.Ctree (fun v => ψ v.castSucc) s →
      (ψ u.castSucc).val ∉ B := by
  constructor
  · intro h u hr hc
    apply h u.castSucc ((addIsolated_reachable_old H a s u).mpr hr)
    rw [addIsolated_ctree_old,mem_image_injective Fin.castSucc (Fin.castSucc_injective _)]
    exact hc
  · intro h u hr hc
    induction u using Fin.lastCases with
    | last => exact (Fin.castSucc_ne_last s ((addIsolated_reachable_last H a _).mp hr.symm)).elim
    | cast u =>
      apply h u ((addIsolated_reachable_old H a s u).mp hr)
      rwa [addIsolated_ctree_old,mem_image_injective Fin.castSucc (Fin.castSucc_injective _)] at hc

lemma addIsolated_boundary_last (H : AbsForest n) (a : Fin (labelBound n))
    (B : Finset ℕ) (ψ : Fin (H.k+1) → Label n) :
    ∀ u,(addIsolated H a).graph.Reachable (Fin.last H.k) u →
      u ∉ (addIsolated H a).Ctree ψ (Fin.last H.k) → (ψ u).val ∉ B := by
  intro u hr hc
  obtain rfl := (addIsolated_reachable_last H a u).mp hr
  exact (hc (by rw [addIsolated_ctree_last]; exact Finset.mem_singleton_self _)).elim

theorem addIsolatedDescription_boundary (D : Description n) (a : Fin (labelBound n))
    (x : Label n) (B : Finset ℕ) (ψ : Fin (D.H.k+1) → Label n) :
    (∀ s ∈ (addIsolatedDescription D a x).sel,∀ u,
      (addIsolated D.H a).graph.Reachable s u →
      u ∉ (addIsolated D.H a).Ctree ψ s → (ψ u).val ∉ B) ↔
    ∀ s ∈ D.sel,∀ u,D.H.graph.Reachable s u →
      u ∉ D.H.Ctree (fun v => ψ v.castSucc) s → (ψ u.castSucc).val ∉ B := by
  simp only [Finset.forall_mem_insert,Finset.forall_mem_image]
  constructor
  · rintro ⟨_,h⟩ s hs
    exact (addIsolated_boundary_old D.H a B ψ s).mp (@h s hs)
  · intro h
    refine ⟨addIsolated_boundary_last D.H a B ψ,?_⟩
    intro s hs
    exact (addIsolated_boundary_old D.H a B ψ s).mpr (h s hs)

theorem addIsolatedDescription_weight (l : ℕ) (G : WeldedInstance n)
    (D : Description n) (hD : D.IsValid) (a : Fin (labelBound n))
    (ha : ∀ u,D.H.lab u ≠ some a) (x : Label n) (B : Finset ℕ)
    (ψ : Fin (D.H.k+1) → Label n) :
    descriptionWeight l G B (addIsolatedDescription D a x) ψ =
      descriptionWeight l G B D (fun u => ψ u.castSucc) *
        (if ψ (Fin.last D.H.k) = x ∧ 1 ≤ (ψ (Fin.last D.H.k)).val
          then 1 / (labelBound n : ℝ) else 0) := by
  unfold descriptionWeight
  rw [addIsolatedDescription_fixed D hD a ha x ψ,
    addIsolatedDescription_boundary D a x B ψ,
    addIsolated_muRef l G D.H hD.1 a ha ψ]
  have halg (P Q R S : Prop) (u v : ℝ) :
      (if (P ∧ Q) ∧ R then u * (if S then v else 0) else 0) =
        (if Q ∧ R then u else 0) * (if P ∧ S then v else 0) := by
    by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> by_cases hS : S <;>
      simp only [hP,hQ,hR,hS,true_and,false_and,and_true,and_false,if_true,if_false,mul_zero,zero_mul]
  have hh := halg (ψ (Fin.last D.H.k) = x)
    (∀ s ∈ D.sel,D.H.Wfix (fun u => ψ u.castSucc) s = D.H.Wfix D.ϕ₀ s)
    (∀ s ∈ D.sel,∀ u,D.H.graph.Reachable s u →
      u ∉ D.H.Ctree (fun v => ψ v.castSucc) s → (ψ u.castSucc).val ∉ B)
    (1 ≤ (ψ (Fin.last D.H.k)).val)
    (D.H.muRef l G (fun u => ψ u.castSucc)) (1 / (labelBound n : ℝ))
  convert hh using 1 <;> split_ifs <;> rfl

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathLabelCoefficientTransport
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DescriptionCoefficients

variable {n l : ℕ} {G : WeldedInstance n}

theorem descriptionSpan_withLabel (H : AbsForest n) (hH : H.IsValid) (u : Fin H.k)
    (a : Option (Fin (labelBound n))) (hnew : (withLabel H u a).IsValid)
    (B : Finset ℕ) :
    descriptionSpan l G (withLabel H u a) B = descriptionSpan l G H B := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro f ⟨sel, φ₀, hD, rfl⟩
    exact ⟨sel, φ₀, ⟨hH, hD.2⟩, amplitude_withLabel H u a B sel φ₀⟩
  · apply Submodule.span_mono
    rintro f ⟨sel, φ₀, hD, rfl⟩
    exact ⟨sel, φ₀, description_valid_withLabel H u a sel φ₀ hD hnew,
      (amplitude_withLabel H u a B sel φ₀).symm⟩

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathLabelInsertion
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport RegisterTransport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

def labelOfIndex (x : Fin (labelBound n)) : Label n := ⟨x.val + 1, Nat.succ_lt_succ x.isLt⟩

lemma labelOfIndex_vertexLabelIndex (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (u : Fin H.k) :
    labelOfIndex (vertexLabelIndex H φ hp u) = φ u :=
  Fin.ext (vertexLabelIndex_val H φ hp u).symm

noncomputable def freshPositions (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) : Finset (Fin (labelBound n)) :=
  Finset.univ.filter (fun x => ∀ u, vertexLabelIndex H φ hp u ≠ x)

lemma fresh_position_unused (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (I : Db l G) (hI : H.IsDbOf l G φ I)
    (x : Fin (labelBound n)) (hx : x ∈ freshPositions H φ hp) : I.1 x = none := by
  cases hi : I.1 x with
  | none => rfl
  | some a =>
    obtain ⟨u, hu, _⟩ := (hI.1 x a).mp hi
    have he : vertexLabelIndex H φ hp u = x := by
      apply Fin.ext
      have hv := vertexLabelIndex_val H φ hp u
      omega
    exact ((Finset.mem_filter.mp hx).2 u he).elim

lemma unused_positions_split (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (hφ : Function.Injective φ)
    (I : Db l G) (hI : H.IsDbOf l G φ I) :
    Finset.univ.filter (fun x => I.1 x = none) =
      (Finset.univ.filter (fun u => H.lab u = none)).image (vertexLabelIndex H φ hp) ∪
        freshPositions H φ hp := by
  ext x
  constructor
  · intro hx
    by_cases h : ∃ u, vertexLabelIndex H φ hp u = x
    · obtain ⟨u, rfl⟩ := h
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact (isDbOf_label_at_vertex H φ hp hφ I hI u).symm.trans (Finset.mem_filter.mp hx).2
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => h ⟨u, hu⟩⟩
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact (isDbOf_label_at_vertex H φ hp hφ I hI u).trans (Finset.mem_filter.mp hu).2
    · exact fresh_position_unused H φ hp I hI x hx

lemma existing_fresh_disjoint (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) :
    Disjoint ((Finset.univ.filter (fun u => H.lab u = none)).image (vertexLabelIndex H φ hp))
      (freshPositions H φ hp) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_filter.mp hx').2 u rfl

theorem sum_unused_positions {A : Type*} [AddCommMonoid A]
    (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (hφ : Function.Injective φ)
    (I : Db l G) (hI : H.IsDbOf l G φ I) (F : Fin (labelBound n) → A) :
    (∑ x ∈ Finset.univ.filter (fun x => I.1 x = none), F x) =
      (∑ u ∈ Finset.univ.filter (fun u => H.lab u = none), F (vertexLabelIndex H φ hp u)) +
        ∑ x ∈ freshPositions H φ hp, F x := by
  rw [unused_positions_split H φ hp hφ I hI, Finset.sum_union (existing_fresh_disjoint H φ hp),
    Finset.sum_image (fun u _ v _ h => vertexLabelIndex_injective H φ hp hφ h)]

noncomputable def insertionBasis (a : Fin (labelBound n)) (I : Db l G) : Hil (Db l G) :=
  if I.1.symm a = none then
    ∑ x ∈ Finset.univ.filter (fun x => I.1 x = none), ket (I.1.addPair x a, I.2)
  else 0

noncomputable def insertion (a : Fin (labelBound n)) : Hil (Db l G) →L[ℂ] Hil (Db l G) :=
  ofBasis (insertionBasis a)

noncomputable def normalizedInsertion (r : ℕ) (a : Fin (labelBound n)) :
    Hil (Db l G) →L[ℂ] Hil (Db l G) :=
  (((Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹ : ℂ) • insertion a)

theorem insertion_ket (a : Fin (labelBound n)) (I : Db l G) (ha : I.1.symm a = none) :
    insertion a (ket I) =
      ∑ x ∈ Finset.univ.filter (fun x => I.1 x = none), ket (I.1.addPair x a, I.2) := by
  rw [insertion, ofBasis_ket, insertionBasis, if_pos ha]

theorem insertion_ket_split (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (hφ : Function.Injective φ)
    (I : Db l G) (hI : H.IsDbOf l G φ I)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a) :
    insertion a (ket I) =
      (∑ u ∈ Finset.univ.filter (fun u => H.lab u = none),
        ket (I.1.addPair (vertexLabelIndex H φ hp u) a, I.2)) +
      ∑ x ∈ freshPositions H φ hp, ket (I.1.addPair x a, I.2) := by
  rw [insertion_ket a I (label_db_unused H φ I hI a ha)]
  exact sum_unused_positions H φ hp hφ I hI _

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathLabelInsertionGenerators
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable abbrev relabelDescription (D : Description n) (u : Fin D.H.k)
    (a : Fin (labelBound n)) : Description n := ⟨withLabel D.H u (some a), D.sel, D.ϕ₀⟩

lemma relabelDescription_valid (D : Description n) (hD : D.IsValid)
    (u : Fin D.H.k) (a : Fin (labelBound n)) (ha : ∀ v, D.H.lab v ≠ some a) :
    (relabelDescription D u a).IsValid :=
  description_valid_withLabel D.H u (some a) D.sel D.ϕ₀ hD (insert_valid D.H hD.1 u a ha)

lemma relabelDescription_good (D : Description n) (u : Fin D.H.k)
    (a : Fin (labelBound n)) (B : Finset ℕ) (φ : Fin D.H.k → Label n) :
    (relabelDescription D u a).IsGood l G B φ ↔ D.IsGood l G B φ := Iff.rfl

lemma totalDb_isDbOf (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) :
    H.IsDbOf l G φ (totalDb (l := l) H hH hG φ) := by
  rw [totalDb, dif_pos hφ]
  exact assignmentDb_isDbOf H hH φ hφ hG

lemma totalDb_relabel (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hp : ∀ v, 1 ≤ (φ v).val)
    (u : Fin H.k) (hu : H.lab u = none) (a : Fin (labelBound n))
    (ha : ∀ v, H.lab v ≠ some a) :
    totalDb (l := l) (withLabel H u (some a)) (insert_valid H hH u a ha) hG φ =
      ((totalDb (l := l) H hH hG φ).1.addPair (vertexLabelIndex H φ hp u) a, (totalDb (l := l) H hH hG φ).2) := by
  apply isDbOf_unique (withLabel H u (some a)) φ
  · exact totalDb_isDbOf _ (insert_valid H hH u a ha) hG φ hφ
  · exact isDbOf_insertLabel H φ hφ _ (totalDb_isDbOf H hH hG φ hφ)
      u _ a (vertexLabelIndex_val H φ hp u) hu ha

noncomputable def freshRemainder (D : Description n) (hD : D.IsValid)
    (hG : G.IsProperColoring) (hln : l + 2 ≤ n) (B : Finset ℕ)
    (a : Fin (labelBound n)) : Hil (Db l G) :=
  ∑ φ, if hφ : D.IsGood l G B φ then
    (Real.sqrt (D.H.muRef l G φ) : ℂ) •
      ∑ x ∈ freshPositions D.H φ (positive_mu_vertex_nonzero D.H φ (ne_of_gt hφ.1) hln),
        ket ((totalDb (l := l) D.H hD.1 hG φ).1.addPair x a, (totalDb (l := l) D.H hD.1 hG φ).2)
  else 0

theorem insertion_gVec_split (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (a : Fin (labelBound n))
    (ha : ∀ u, D.H.lab u ≠ some a) :
    insertion a (D.gVec l G B) =
      (∑ u ∈ Finset.univ.filter (fun u => D.H.lab u = none),
        (relabelDescription D u a).gVec l G B) + freshRemainder D hD hG hln B a := by
  have hknown : (∑ u ∈ Finset.univ.filter (fun u => D.H.lab u = none),
      (relabelDescription D u a).gVec l G B) =
      ∑ φ, ∑ u ∈ Finset.univ.filter (fun u => D.H.lab u = none),
        if D.IsGood l G B φ then
          (Real.sqrt (D.H.muRef l G φ) : ℂ) •
            ket (totalDb (l := l) (withLabel D.H u (some a)) (insert_valid D.H hD.1 u a ha) hG φ)
        else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [gVec_eq_total_sum hG _ (relabelDescription_valid D hD u a ha) B]
    rfl
  rw [hknown, freshRemainder, ← Finset.sum_add_distrib,
    gVec_eq_total_sum hG D hD B, map_sum]
  apply Finset.sum_congr rfl
  intro φ hφuniv
  by_cases hφ : D.IsGood l G B φ
  · rw [if_pos hφ, map_smul, dif_pos hφ]
    let hp := positive_mu_vertex_nonzero D.H φ (ne_of_gt hφ.1) hln
    rw [insertion_ket_split D.H φ hp hφ.2.2.2 _
      (totalDb_isDbOf D.H hD.1 hG φ hφ.2.2.2) a ha, smul_add, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [if_pos hφ, totalDb_relabel D.H hD.1 hG φ hφ.2.2.2 hp u
      (Finset.mem_filter.mp hu).2 a ha]
  · rw [if_neg hφ, map_zero, dif_neg hφ]
    simp only [if_neg hφ, Finset.sum_const_zero, zero_add]

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathDatabaseSectors
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}

theorem encodedDb_ne_of_not_isomorphic (hG : G.IsValid)
    (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid) (hln : l + 2 ≤ n)
    (hnot : ¬ ∃ e : Fin H.k ≃ Fin K.k, IsForestIso H K e)
    (φ : SupportedAssignment l G H) (ψ : SupportedAssignment l G K) :
    encodedDb H hH hG.2 φ ≠ encodedDb K hK hG.2 ψ := by
  intro he
  have hI := encodedDb_isDbOf H hH hG.2 φ
  have hJ := encodedDb_isDbOf K hK hG.2 ψ
  rw [← he] at hJ
  obtain ⟨e, ⟨hiso, _⟩, _⟩ := isDbOf_forest_equiv hG H K hH hK φ.1 ψ.1 φ.2.1 ψ.2.1
    φ.2.2 ψ.2.2 hln _ hI hJ
  exact hnot ⟨e, hiso⟩

theorem encodeState_orthogonal (hG : G.IsValid)
    (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid) (hln : l + 2 ≤ n)
    (hnot : ¬ ∃ e : Fin H.k ≃ Fin K.k, IsForestIso H K e)
    (ψ : Hil (SupportedAssignment l G H)) (χ : Hil (SupportedAssignment l G K)) :
    inner ℂ (encodeState H hH hG.2 ψ) (encodeState K hK hG.2 χ) = 0 := by
  rw [encodeState, UniformFiberEncoding.pushforward_eq_sum,
    encodeState, UniformFiberEncoding.pushforward_eq_sum]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_eq_zero
  intro φ _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro θ _
  have hne := encodedDb_ne_of_not_isomorphic hG H K hH hK hln hnot θ φ
  simp only [HilbertSupport.inner_ket, HilbertSupport.ket_apply, if_neg hne,
    mul_zero, zero_mul]

theorem encodedDb_eq_of_matching (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ ψ : SupportedAssignment l G H) (e : Fin H.k ≃ Fin H.k)
    (hiso : IsForestIso H H e) (he : ∀ u, ψ.1 (e u) = φ.1 u) :
    encodedDb H hH hG φ = encodedDb H hH hG ψ :=
  AssignmentDatabase.isDbOf_unique H ψ.1 _ _
    (isDbOf_of_forestIso H H φ.1 ψ.1 e he hiso _ (encodedDb_isDbOf H hH hG φ))
    (encodedDb_isDbOf H hH hG ψ)

def invariantSpace (H : AbsForest n) : Submodule ℂ (Hil (SupportedAssignment l G H)) where
  carrier := {ψ | ∀ φ χ : SupportedAssignment l G H, ∀ e : Fin H.k ≃ Fin H.k,
    IsForestIso H H e → (∀ u, χ.1 (e u) = φ.1 u) → ψ φ = ψ χ}
  zero_mem' := by
    intro φ χ e he hm
    rfl
  add_mem' := by
    intro ψ χ hψ hχ φ θ e he hm
    change ψ φ + χ φ = ψ θ + χ θ
    rw [hψ φ θ e he hm, hχ φ θ e he hm]
  smul_mem' := by
    intro c ψ hψ φ θ e he hm
    change c • ψ φ = c • ψ θ
    rw [hψ φ θ e he hm]

lemma symmetrizeState_mem_invariantSpace (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (ψ : Hil (SupportedAssignment l G H)) :
    symmetrizeState H hH hG ψ ∈ invariantSpace H := by
  intro φ χ e hiso he
  exact UniformFiberEncoding.fiberAverage_constant _ _ ψ φ χ
    (encodedDb_eq_of_matching H hH hG φ χ e hiso he)

/-- The canonical good vectors with one fixed abstract forest. -/
noncomputable def fixedForestGoodSpace (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) : Submodule ℂ (Hil (Db l G)) :=
  Submodule.span ℂ {v | ∃ (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n),
    (Description.mk H sel φ₀).IsValid ∧ v = (Description.mk H sel φ₀).gVec l G B}

noncomputable def invariantGoodSpace (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (B : Finset ℕ) : Submodule ℂ (Hil (SupportedAssignment l G H)) :=
  Submodule.span ℂ {v | ∃ (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n),
    (Description.mk H sel φ₀).IsValid ∧ v = symmetrizeState H hH hG
      (goodAssignmentState (Description.mk H sel φ₀) B)}

lemma invariantGoodSpace_le (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (B : Finset ℕ) :
    invariantGoodSpace (l := l) H hH hG B ≤ invariantSpace H := by
  apply Submodule.span_le.mpr
  rintro v ⟨sel, φ₀, hD, rfl⟩
  exact symmetrizeState_mem_invariantSpace H hH hG _

theorem map_invariantGoodSpace (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) :
    (invariantGoodSpace H hH hG.2 B).map (basisMap (encodedDb H hH hG.2)).toLinearMap =
      fixedForestGoodSpace l G H B := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro v ⟨sel, φ₀, hD, rfl⟩
    change basisMap (encodedDb H hH hG.2) _ ∈ fixedForestGoodSpace l G H B
    rw [← encodeState_eq_basisMap, encodeState_symmetrize hG H hH hln,
      encode_goodAssignmentState hG.2 _ hD B]
    exact Submodule.subset_span ⟨sel, φ₀, hD, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨sel, φ₀, hD, rfl⟩
    refine ⟨symmetrizeState H hH hG.2 (goodAssignmentState (Description.mk H sel φ₀) B),
      Submodule.subset_span ⟨sel, φ₀, hD, rfl⟩, ?_⟩
    change basisMap (encodedDb H hH hG.2) _ = _
    rw [← encodeState_eq_basisMap, encodeState_symmetrize hG H hH hln,
      encode_goodAssignmentState hG.2 _ hD B]

theorem fixedForestGoodSpace_representation (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (v : Hil (Db l G))
    (hv : v ∈ fixedForestGoodSpace l G H B) :
    ∃! ψ : Hil (SupportedAssignment l G H), ψ ∈ invariantGoodSpace H hH hG.2 B ∧
      encodeState H hH hG.2 ψ = v ∧
      (Fintype.card (ForestAut H) : ℝ) * ‖ψ‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← map_invariantGoodSpace hG H hH hln B] at hv
  obtain ⟨ψ, hψ, hψv⟩ := hv
  have he : encodeState H hH hG.2 ψ = v := by
    rw [encodeState_eq_basisMap]
    exact hψv
  have hn := encodeState_norm_sq hG H hH hln ψ (invariantGoodSpace_le H hH hG.2 B hψ)
  refine ⟨ψ, ⟨hψ, he, by simpa only [he] using hn.symm⟩, ?_⟩
  intro χ hχ
  have hdiff : χ - ψ ∈ invariantGoodSpace H hH hG.2 B :=
    (invariantGoodSpace H hH hG.2 B).sub_mem hχ.1 hψ
  have hzero : encodeState H hH hG.2 (χ - ψ) = 0 := by
    simp only [encodeState_eq_basisMap, map_sub]
    rw [← encodeState_eq_basisMap, ← encodeState_eq_basisMap, hχ.2.1, he, sub_self]
  have hs := encodeState_norm_sq hG H hH hln (χ - ψ)
    (invariantGoodSpace_le H hH hG.2 B hdiff)
  have hpos : (0 : ℝ) < Fintype.card (ForestAut H) := Nat.cast_pos.mpr (forestAut_card_pos H)
  rw [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hs
  have hz : ‖χ - ψ‖ ^ 2 = 0 := (mul_eq_zero.mp hs.symm).resolve_left (ne_of_gt hpos)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem fixedForestGoodSpace_le_goodSpace (H : AbsForest n) (B : Finset ℕ) (t : ℕ)
    (ht : H.records ≤ t) : fixedForestGoodSpace l G H B ≤ goodSpace l G B t := by
  apply Submodule.span_le.mpr
  rintro v ⟨sel, φ₀, hD, rfl⟩
  exact Submodule.subset_span ⟨Description.mk H sel φ₀, hD, ht, rfl⟩

theorem goodSpace_eq_iSup_fixedForest (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) (t : ℕ) :
    goodSpace l G B t = ⨆ H : {H : AbsForest n // H.IsValid ∧ H.records ≤ t},
      fixedForestGoodSpace l G H.1 B := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨D, hD, ht, rfl⟩
    exact (le_iSup (fun H : {H : AbsForest n // H.IsValid ∧ H.records ≤ t} =>
      fixedForestGoodSpace l G H.1 B) ⟨D.H, hD.1, ht⟩)
      (Submodule.subset_span ⟨D.sel, D.ϕ₀, hD, rfl⟩)
  · exact iSup_le fun H => fixedForestGoodSpace_le_goodSpace H.1 B t H.2.2

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathLabelDeletion
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport RegisterTransport CompressedPrimitive
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def deletionBasis (a : Fin (labelBound n)) (I : Db l G) : Hil (Db l G) :=
  match I.1.symm a with
  | none => 0
  | some x => ket (eraseAt I.1 x, I.2)

noncomputable def deletion (a : Fin (labelBound n)) : Hil (Db l G) →L[ℂ] Hil (Db l G) :=
  ofBasis (deletionBasis a)

theorem deletion_ket (a : Fin (labelBound n)) (I : Db l G) (x : Fin (labelBound n))
    (hx : I.1.symm a = some x) : deletion a (ket I) = ket (eraseAt I.1 x, I.2) := by
  rw [deletion, ofBasis_ket, deletionBasis, hx]

noncomputable abbrev eraseDescription (D : Description n) (u : Fin D.H.k) : Description n :=
  ⟨withLabel D.H u none, D.sel, D.ϕ₀⟩

lemma eraseDescription_valid (D : Description n) (hD : D.IsValid) (u : Fin D.H.k)
    (hu : ∃ p ∈ D.H.E, p.1 = u ∨ p.2 = u) : (eraseDescription D u).IsValid :=
  description_valid_withLabel D.H u none D.sel D.ϕ₀ hD (erase_valid D.H hD.1 u hu)

lemma totalDb_eraseLabel (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (hp : ∀ v, 1 ≤ (φ v).val)
    (u : Fin H.k) (hu : ∃ p ∈ H.E, p.1 = u ∨ p.2 = u) :
    totalDb (l := l) (withLabel H u none) (erase_valid H hH u hu) hG φ =
      (eraseAt (totalDb (l := l) H hH hG φ).1 (vertexLabelIndex H φ hp u),
        (totalDb (l := l) H hH hG φ).2) := by
  apply isDbOf_unique (withLabel H u none) φ
  · exact totalDb_isDbOf _ (erase_valid H hH u hu) hG φ hφ
  · exact isDbOf_eraseLabel H φ hφ _ (totalDb_isDbOf H hH hG φ hφ)
      u _ (vertexLabelIndex_val H φ hp u)

theorem deletion_gVec_incident (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (a : Fin (labelBound n)) (u : Fin D.H.k)
    (hua : D.H.lab u = some a) (hu : ∃ p ∈ D.H.E, p.1 = u ∨ p.2 = u) :
    deletion a (D.gVec l G B) = (eraseDescription D u).gVec l G B := by
  rw [gVec_eq_total_sum hG D hD B,
    gVec_eq_total_sum hG _ (eraseDescription_valid D hD u hu) B, map_sum]
  apply Finset.sum_congr rfl
  intro φ hφuniv
  change deletion a (if D.IsGood l G B φ then _ else _) =
    (if D.IsGood l G B φ then _ else _)
  by_cases hφ : D.IsGood l G B φ
  · rw [if_pos hφ, if_pos hφ, map_smul]
    let hp := positive_mu_vertex_nonzero D.H φ (ne_of_gt hφ.1) hln
    have hi := (totalDb_isDbOf (l := l) D.H hD.1 hG φ hφ.2.2.2).1
      (vertexLabelIndex D.H φ hp u) a |>.mpr ⟨u, vertexLabelIndex_val D.H φ hp u, hua⟩
    have hs := ((totalDb (l := l) D.H hD.1 hG φ).1.inv (vertexLabelIndex D.H φ hp u) a).mpr hi
    rw [deletion_ket a _ _ hs, totalDb_eraseLabel D.H hD.1 hG φ hφ.2.2.2 hp u hu]
    rfl
  · rw [if_neg hφ, if_neg hφ, map_zero]

theorem deletion_mem_incident_fixedForest (hG : G.IsProperColoring) (H : AbsForest n)
    (hH : H.IsValid) (hln : l + 2 ≤ n) (B : Finset ℕ) (a : Fin (labelBound n))
    (u : Fin H.k) (hua : H.lab u = some a) (hu : ∃ p ∈ H.E, p.1 = u ∨ p.2 = u)
    (f : Hil (Db l G)) (hf : f ∈ fixedForestGoodSpace l G H B) :
    deletion a f ∈ fixedForestGoodSpace l G (withLabel H u none) B := by
  have hle : fixedForestGoodSpace l G H B ≤
      (fixedForestGoodSpace l G (withLabel H u none) B).comap (deletion a).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨sel,φ₀,hD,rfl⟩
    change deletion a ((Description.mk H sel φ₀).gVec l G B) ∈
      fixedForestGoodSpace l G (withLabel H u none) B
    rw [deletion_gVec_incident hG _ hD hln B a u hua hu]
    exact Submodule.subset_span ⟨sel,φ₀,eraseDescription_valid _ hD u hu,rfl⟩
  exact hle hf

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathInverseLabelFormula
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical CompressedPrimitive RegisterTransport HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def inverseLabel (a : Fin (labelBound n)) : Hil (Db l G) →L[ℂ] Hil (Db l G) :=
  ofBasis (fun I => partImg (pCinv (labelBound n) a) I.1 (fun L => (L, I.2)))

theorem inverseLabel_norm (a : Fin (labelBound n)) (ψ : Hil (Db l G)) :
    ‖inverseLabel a ψ‖ = ‖ψ‖ :=
  ofBasis_partImg_norm (Equiv.prodComm _ _) (fun _ => pCinv (labelBound n) a)
    (fun _ ψ => pCinv_norm_map (labelBound n) a ψ) ψ

theorem embed_plusInv (L : LabelDb n) (C : EdgeDb l G) (a : Fin (labelBound n))
    (ha : L.symm a = none) :
    basisMap (fun L' : LabelDb n => (L', C)) (plusInv L a) =
      ((Real.sqrt ((labelBound n - L.size : ℕ) : ℝ))⁻¹ : ℂ) • insertion a (ket (L, C)) := by
  rw [insertion_ket a (L, C) ha]
  simp only [plusInv, map_smul, map_sum, basisMap_ket]

theorem inverseLabel_ket_unset (r : ℕ) (a : Fin (labelBound n)) (I : Db l G)
    (ha : I.1.symm a = none) (hr : I.1.size = r) :
    inverseLabel a (ket I) = normalizedInsertion r a (ket I) := by
  rw [inverseLabel, ofBasis_ket, partImg_eq_basisMap, pCinv_ket_unset I.1 a ha,
    embed_plusInv I.1 I.2 a ha, hr]
  rfl

theorem inverseLabel_unset (r : ℕ) (a : Fin (labelBound n)) (ψ : Hil (Db l G))
    (hψ : ∀ I, ψ I ≠ 0 → I.1.symm a = none ∧ I.1.size = r) :
    inverseLabel a ψ = normalizedInsertion r a ψ :=
  maps_eq_of_support _ _ ψ (fun I hI => inverseLabel_ket_unset r a I (hψ I hI).1 (hψ I hI).2)

theorem normalizedInsertion_norm (r : ℕ) (a : Fin (labelBound n)) (ψ : Hil (Db l G))
    (hψ : ∀ I, ψ I ≠ 0 → I.1.symm a = none ∧ I.1.size = r) :
    ‖normalizedInsertion r a ψ‖ = ‖ψ‖ := by
  rw [← inverseLabel_unset r a ψ hψ, inverseLabel_norm]

theorem inverseLabel_ket_used (r : ℕ) (a : Fin (labelBound n)) (I : Db l G)
    (x : Fin (labelBound n)) (hx : I.1.symm a = some x) (hr : I.1.size = r + 1) :
    let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
    inverseLabel a (ket I) = ket I + c • deletion a (ket I) -
      c ^ 2 • insertion a (deletion a (ket I)) := by
  dsimp only
  have hxa : I.1 x = some a := (I.1.inv x a).mp hx
  let L := eraseAt I.1 x
  have hLx : L x = none := eraseAt_self I.1 x
  have hLa : L.symm a = none := eraseAt_unused I.1 x a hxa
  have hLsize : L.size = r := by
    have he := eraseAt_size I.1 x a hxa
    dsimp [L]
    omega
  have hrecover : L.addPair x a = I.1 := eraseAt_add I.1 x a hxa
  have he := pCinv_ket_added L a x hLa hLx
  rw [hrecover, hLsize] at he
  rw [inverseLabel, ofBasis_ket, partImg_eq_basisMap, he]
  simp only [map_add, map_smul, map_sub, basisMap_ket]
  rw [embed_plusInv L I.2 a hLa, hLsize, deletion_ket a I x hx]
  change ket I + _ • (ket (L, I.2) - _ • insertion a (ket (L, I.2))) = _
  simp only [smul_sub, smul_smul, pow_two, add_sub_assoc]
  rfl

theorem inverseLabel_used (r : ℕ) (a : Fin (labelBound n)) (ψ : Hil (Db l G))
    (hψ : ∀ I, ψ I ≠ 0 → I.1.symm a ≠ none ∧ I.1.size = r + 1) :
    let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
    inverseLabel a ψ = ψ + c • deletion a ψ - c ^ 2 • insertion a (deletion a ψ) := by
  dsimp only
  let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
  let R : Hil (Db l G) →L[ℂ] Hil (Db l G) :=
    1 + c • deletion a - c ^ 2 • (insertion a).comp (deletion a)
  have he : inverseLabel a ψ = R ψ := by
    apply maps_eq_of_support
    intro I hI
    obtain ⟨hused, hsize⟩ := hψ I hI
    cases hx : I.1.symm a with
    | none => exact (hused hx).elim
    | some x => exact inverseLabel_ket_used r a I x hx hsize
  exact he

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathInverseLabelApproximation
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical CompressedPrimitive RegisterTransport

variable {n l : ℕ} {G : WeldedInstance n}

theorem inverseLabel_ket_used_recompression (r : ℕ) (a : Fin (labelBound n)) (I : Db l G)
    (x : Fin (labelBound n)) (hx : I.1.symm a = some x) (hr : I.1.size = r + 1) :
    let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
    inverseLabel a (ket I) = ket I + c • deletion a (ket I) -
      inverseLabel a (c • deletion a (ket I)) := by
  dsimp only
  have hxa : I.1 x = some a := (I.1.inv x a).mp hx
  have hsize : (eraseAt I.1 x).size = r := by
    have he := eraseAt_size I.1 x a hxa
    omega
  rw [inverseLabel_ket_used r a I x hx hr, deletion_ket a I x hx, map_smul,
    inverseLabel_ket_unset r a (eraseAt I.1 x, I.2)
      (eraseAt_unused I.1 x a hxa) hsize]
  simp only [normalizedInsertion, ContinuousLinearMap.smul_apply, smul_smul, pow_two]

theorem inverseLabel_used_recompression (r : ℕ) (a : Fin (labelBound n)) (ψ : Hil (Db l G))
    (hψ : ∀ I, ψ I ≠ 0 → I.1.symm a ≠ none ∧ I.1.size = r + 1) :
    let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
    inverseLabel a ψ = ψ + c • deletion a ψ - inverseLabel a (c • deletion a ψ) := by
  dsimp only
  let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
  let R : Hil (Db l G) →L[ℂ] Hil (Db l G) :=
    1 + c • deletion a - (inverseLabel a).comp (c • deletion a)
  have he : inverseLabel a ψ = R ψ := by
    apply maps_eq_of_support
    intro I hI
    obtain ⟨hused, hsize⟩ := hψ I hI
    cases hx : I.1.symm a with
    | none => exact (hused hx).elim
    | some x => exact inverseLabel_ket_used_recompression r a I x hx hsize
  exact he

theorem inverseLabel_approximation_error (r : ℕ) (a : Fin (labelBound n))
    (ψ w : Hil (Db l G))
    (hψ : ∀ I, ψ I ≠ 0 → I.1.symm a ≠ none ∧ I.1.size = r + 1) :
    let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
    ‖inverseLabel a ψ - (ψ + w - inverseLabel a w)‖ ≤
      2 * ‖c • deletion a ψ - w‖ := by
  dsimp only
  let c : ℂ := (Real.sqrt ((labelBound n - r : ℕ) : ℝ))⁻¹
  have he : inverseLabel a ψ - (ψ + w - inverseLabel a w) =
      (c • deletion a ψ - w) - inverseLabel a (c • deletion a ψ - w) := by
    rw [inverseLabel_used_recompression r a ψ hψ, map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖c • deletion a ψ - w‖ + ‖inverseLabel a (c • deletion a ψ - w)‖ := norm_sub_le _ _
    _ = _ := by rw [inverseLabel_norm]; ring

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathInverseLabelControl
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical QAlgorithms HilbertSupport RegisterTransport ControlledOperators EncodedOracleUnitary ControlApproximation

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def inverseLabelControl (q : QReg n) : Hil (Db l G) →L[ℂ] Hil (Db l G) :=
  match toIdx n (bitsToNat q.1.1) with
  | some a => inverseLabel a
  | none => 1

theorem pCinvLab_eq_controlled : pCinvLab l G = controlled (inverseLabelControl (l:=l) (G:=G)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply maps_eq_of_support
  intro p _
  rw [pCinvLab, ofBasis_ket, controlled_ket]
  unfold inverseLabelControl
  cases h : toIdx n (bitsToNat p.1.1.1) with
  | none => exact (tensor_ket_eq p.1 p.2).symm
  | some a =>
    simp only [inverseLabel, ofBasis_ket]
    exact partImg_control _ _ p.1 (fun L => (L,p.2.2))

theorem pCinvLab_norm (ψ : Hil (QReg n × Db l G)) : ‖pCinvLab l G ψ‖ = ‖ψ‖ := by
  rw [pCinvLab_eq_controlled]
  apply controlled_norm
  intro q v
  unfold inverseLabelControl
  cases toIdx n (bitsToNat q.1.1) with
  | none => rfl
  | some a => exact inverseLabel_norm a v

theorem goodSpace_mono_records (B : Finset ℕ) {s t : ℕ} (hst : s ≤ t) :
    goodSpace l G B s ≤ goodSpace l G B t := by
  apply Submodule.span_mono
  rintro v ⟨D,hD,hs,he⟩
  exact ⟨D,hD,hs.trans hst,he⟩

theorem pCinvLab_good_leakage_of_db_bound (B : Finset ℕ) (t : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hdb : ∀ (a : Fin (labelBound n)) v, v ∈ goodSpace l G B t →
      ∃ w ∈ goodSpace l G B (t+1), ‖inverseLabel a v - w‖ ^ 2 ≤ K * ‖v‖ ^ 2) :
    ‖((1 : Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G)) -
        projGoodB l G B (t+1)).comp ((pCinvLab l G).comp (projGoodB l G B t))‖ ≤
      Real.sqrt K := by
  rw [pCinvLab_eq_controlled]
  apply controlled_projection_norm_bound _ (goodSpace l G B t) (goodSpace l G B (t+1)) K hK
  intro q v hv
  unfold inverseLabelControl
  cases toIdx n (bitsToNat q.1.1) with
  | some a => exact hdb a v hv
  | none =>
    refine ⟨v, goodSpace_mono_records B (Nat.le_succ t) hv, ?_⟩
    change ‖v - v‖ ^ 2 ≤ _
    simp only [sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0)]
    exact mul_nonneg hK (sq_nonneg _)

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathLabelSectorSupport
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem label_count_le_records (H : AbsForest n) :
    (Finset.univ.filter (fun u => (H.lab u).isSome)).card ≤ H.records := by
  unfold AbsForest.records
  omega

theorem label_count_pos_of_used (H : AbsForest n) (u : Fin H.k)
    (a : Fin (labelBound n)) (hu : H.lab u = some a) :
    0 < (Finset.univ.filter (fun u => (H.lab u).isSome)).card := by
  apply Finset.card_pos.mpr
  exact ⟨u, by simp only [Finset.mem_filter, Finset.mem_univ, hu, Option.isSome_some,
    Bool.true_eq, and_self]⟩

theorem erase_label_count (H : AbsForest n) (u : Fin H.k)
    (a : Fin (labelBound n)) (hu : H.lab u = some a) :
    (Finset.univ.filter (fun v => ((withLabel H u none).lab v).isSome)).card + 1 =
      (Finset.univ.filter (fun v => (H.lab v).isSome)).card := by
  have h := erase_records H u a hu
  unfold AbsForest.records at h
  change H.E.card + _ + 1 = H.E.card + _ at h
  omega

theorem encoded_support (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (ψ : Hil (SupportedAssignment l G H)) (I : Db l G)
    (hI : encodeState H hH hG ψ I ≠ 0) :
    ∃ φ : SupportedAssignment l G H, encodedDb H hH hG φ = I := by
  by_contra hn
  apply hI
  simp only [encodeState, UniformFiberEncoding.pushforward, PiLp.toLp_apply]
  apply Finset.sum_eq_zero
  intro φ hφ
  simp only [Finset.mem_filter] at hφ
  exact False.elim (hn ⟨φ, hφ.2⟩)

theorem fixedForest_support (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (v : Hil (Db l G))
    (hv : v ∈ fixedForestGoodSpace l G H B) (I : Db l G) (hI : v I ≠ 0) :
    ∃ φ : Fin H.k → Label n, Function.Injective φ ∧ H.muRef l G φ ≠ 0 ∧
      H.IsDbOf l G φ I := by
  obtain ⟨ψ, ⟨hψ, he, hnorm⟩, huniq⟩ :=
    fixedForestGoodSpace_representation hG H hH hln B v hv
  obtain ⟨φ, hφ⟩ := encoded_support H hH hG.2 ψ I (by simpa only [he] using hI)
  refine ⟨φ.1, φ.2.1, φ.2.2, ?_⟩
  exact hφ ▸ encodedDb_isDbOf H hH hG.2 φ

theorem fixedForest_label_size (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (v : Hil (Db l G))
    (hv : v ∈ fixedForestGoodSpace l G H B) (I : Db l G) (hI : v I ≠ 0) :
    I.1.size = (Finset.univ.filter (fun u => (H.lab u).isSome)).card := by
  obtain ⟨φ, hi, hm, hdb⟩ := fixedForest_support hG H hH hln B v hv I hI
  exact isDbOf_label_size_of_mu H φ hm hln hi I hdb

theorem fixedForest_label_unused_iff (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (v : Hil (Db l G))
    (hv : v ∈ fixedForestGoodSpace l G H B) (I : Db l G) (hI : v I ≠ 0)
    (a : Fin (labelBound n)) : I.1.symm a = none ↔ ∀ u, H.lab u ≠ some a := by
  obtain ⟨φ, hi, hm, hdb⟩ := fixedForest_support hG H hH hln B v hv I hI
  constructor
  · intro ha u hu
    have hp := positive_mu_vertex_nonzero H φ hm hln
    have he := isDbOf_label_at_vertex H φ hp hi I hdb u
    rw [hu] at he
    have hs : I.1.symm a = some (vertexLabelIndex H φ hp u) := (I.1.inv _ a).mpr he
    have hbad := hs.symm.trans ha
    cases hbad
  · exact label_db_unused H φ I hdb a

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathIsolatedDatabase
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical CompressedPrimitive

variable {n l : ℕ} {G : WeldedInstance n}

theorem isDbOf_removeIsolated (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k + 1) → Label n) (hψ : Function.Injective ψ) (I : Db l G)
    (hI : (addIsolated H a).IsDbOf l G ψ I) (x : Fin (labelBound n))
    (hx : (ψ (Fin.last H.k)).val = x.val + 1) :
    H.IsDbOf l G (fun u => ψ u.castSucc) (eraseAt I.1 x, I.2) := by
  have he := isDbOf_eraseLabel (addIsolated H a) ψ hψ I hI (Fin.last H.k) x hx
  refine ⟨?_, ?_⟩
  · intro i j
    rw [he.1]
    constructor
    · rintro ⟨u, hu, huj⟩
      induction u using Fin.lastCases with
      | last =>
        have hn := (withLabel_self (addIsolated H a) (Fin.last H.k) none).symm.trans huj
        cases hn
      | cast u =>
        refine ⟨u, hu, ?_⟩
        exact (addIsolated_lab_old H a u).symm.trans
          ((withLabel_other (addIsolated H a) (Fin.last H.k) u.castSucc none
            (Fin.castSucc_ne_last u)).symm.trans huj)
    · rintro ⟨u, hu, huj⟩
      exact ⟨u.castSucc, hu,
        (withLabel_other (addIsolated H a) (Fin.last H.k) u.castSucc none
          (Fin.castSucc_ne_last u)).trans ((addIsolated_lab_old H a u).trans huj)⟩
  · intro b j j'
    rw [hI.2]
    constructor
    · rintro ⟨p, hp, hp'⟩
      obtain ⟨q, hq, rfl⟩ := addIsolated_edge_old H a p hp
      exact ⟨q, hq, by simpa only [liftEdge, Fin.lastCases_castSucc] using hp'⟩
    · rintro ⟨p, hp, hp'⟩
      exact ⟨liftEdge p, (addIsolated_edge H a p).mpr hp,
        by simpa only [liftEdge, Fin.lastCases_castSucc] using hp'⟩

theorem isolated_record_present (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k + 1) → Label n) (I : Db l G)
    (hI : (addIsolated H a).IsDbOf l G ψ I) (x : Fin (labelBound n))
    (hx : (ψ (Fin.last H.k)).val = x.val + 1) : I.1 x = some a := by
  exact (hI.1 x a).mpr ⟨Fin.last H.k, hx, addIsolated_lab_last H a⟩

theorem isolated_database_recovered (H : AbsForest n) (a : Fin (labelBound n))
    (ψ : Fin (H.k + 1) → Label n) (I : Db l G)
    (hI : (addIsolated H a).IsDbOf l G ψ I) (x : Fin (labelBound n))
    (hx : (ψ (Fin.last H.k)).val = x.val + 1) :
    ((eraseAt I.1 x).addPair x a, I.2) = I := by
  exact Prod.ext (eraseAt_add I.1 x a (isolated_record_present H a ψ I hI x hx)) rfl

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathLabelInsertionFresh
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma injective_last_iff {k : ℕ} {A : Type*} (ψ : Fin (k+1) → A) :
    Function.Injective ψ ↔ Function.Injective (fun u : Fin k => ψ u.castSucc) ∧
      ∀ u : Fin k, ψ u.castSucc ≠ ψ (Fin.last k) := by
  constructor
  · intro h
    exact ⟨fun u v huv => Fin.castSucc_injective _ (h huv),
      fun u hu => Fin.castSucc_ne_last u (h hu)⟩
  · rintro ⟨h, hn⟩ u v huv
    induction u using Fin.lastCases with
    | last =>
      induction v using Fin.lastCases with
      | last => rfl
      | cast v => exact (hn v huv.symm).elim
    | cast u =>
      induction v using Fin.lastCases with
      | last => exact (hn u huv).elim
      | cast v => exact congrArg Fin.castSucc (h huv)

lemma labelBound_real_pos (n : ℕ) : 0 < (labelBound n : ℝ) := by
  exact_mod_cast (Nat.two_pow_pos (2 * n))

theorem addIsolatedDescription_good (D : Description n) (hD : D.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u, D.H.lab u ≠ some a)
    (x : Label n) (B : Finset ℕ) (ψ : Fin (D.H.k+1) → Label n) :
    (addIsolatedDescription D a x).IsGood l G B ψ ↔
      D.IsGood l G B (fun u => ψ u.castSucc) ∧ ψ (Fin.last D.H.k) = x ∧
        1 ≤ x.val ∧ ∀ u : Fin D.H.k, ψ u.castSucc ≠ x := by
  have hm := one_div_pos.mpr (labelBound_real_pos n)
  have hμ : 0 < (addIsolated D.H a).muRef l G ψ ↔
      0 < D.H.muRef l G (fun u => ψ u.castSucc) ∧ 1 ≤ (ψ (Fin.last D.H.k)).val := by
    rw [addIsolated_muRef l G D.H hD.1 a ha ψ]
    by_cases hp : 1 ≤ (ψ (Fin.last D.H.k)).val
    · rw [if_pos hp, mul_pos_iff_of_pos_right hm]
      exact (and_iff_left hp).symm
    · simp only [hp, if_false, mul_zero, lt_self_iff_false, and_false]
  change (0 < (addIsolated D.H a).muRef l G ψ ∧ _ ∧ _ ∧ Function.Injective ψ) ↔ _
  rw [hμ, addIsolatedDescription_fixed D hD a ha x ψ,
    addIsolatedDescription_boundary D a x B ψ, injective_last_iff]
  constructor
  · rintro ⟨⟨hμ,hpos⟩,⟨hx,hfix⟩,hbd,hinj,hfree⟩
    exact ⟨⟨hμ,hfix,hbd,hinj⟩,hx,hx ▸ hpos,fun u => hx ▸ hfree u⟩
  · rintro ⟨hDgood,hx,hpos,hfree⟩
    exact ⟨⟨hDgood.1,hx.symm ▸ hpos⟩,⟨hx,hDgood.2.1⟩,hDgood.2.2.1,
      hDgood.2.2.2,fun u => hx.symm ▸ hfree u⟩

lemma freshPositions_iff (H : AbsForest n) (φ : Fin H.k → Label n)
    (hp : ∀ u, 1 ≤ (φ u).val) (x : Fin (labelBound n)) :
    x ∈ freshPositions H φ hp ↔ ∀ u, φ u ≠ labelOfIndex x := by
  simp only [freshPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h u hu
    apply h u
    apply Fin.ext
    have hv := vertexLabelIndex_val H φ hp u
    have hh := congrArg Fin.val hu
    change (φ u).val = x.val + 1 at hh
    omega
  · intro h u hu
    apply h u
    rw [← hu, labelOfIndex_vertexLabelIndex]

lemma sum_assignments_snoc {k : ℕ} {A B : Type*} [Fintype A] [AddCommMonoid B]
    (F : (Fin (k+1) → A) → B) :
    (∑ ψ, F ψ) = ∑ x : A, ∑ φ : Fin k → A, F (Fin.snoc φ x) := by
  calc
    _ = ∑ p : A × (Fin k → A), F (Fin.snoc p.2 p.1) :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k+1) => A))
        (fun p => F (Fin.snoc p.2 p.1)) F (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type]

lemma sqrt_normalize_isolated (m r : ℝ) (hm : 0 < m) :
    Real.sqrt m * Real.sqrt (r * (1 / m)) = Real.sqrt r := by
  rw [← Real.sqrt_mul (le_of_lt hm)]
  congr 1
  field_simp

lemma totalDb_addIsolated (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ) (x : Fin (labelBound n))
    (hf : ∀ u, φ u ≠ labelOfIndex x) :
    totalDb (l := l) (addIsolated H a) (addIsolated_valid H hH a ha) hG
        (Fin.snoc φ (labelOfIndex x)) =
      ((totalDb (l := l) H hH hG φ).1.addPair x a, (totalDb (l := l) H hH hG φ).2) := by
  have hi : Function.Injective (Fin.snoc φ (labelOfIndex x) : Fin (H.k+1) → Label n) := by
    apply (injective_last_iff _).mpr
    simpa only [Fin.snoc_castSucc, Fin.snoc_last] using And.intro hφ hf
  apply isDbOf_unique (addIsolated H a) (Fin.snoc φ (labelOfIndex x))
  · exact totalDb_isDbOf _ (addIsolated_valid H hH a ha) hG _ hi
  · apply isDbOf_addIsolated H φ _ (totalDb_isDbOf H hH hG φ hφ) x a
    · intro u hu
      exact hf u (Fin.ext hu)
    · exact ha
    · intro u; simp only [Fin.snoc_castSucc]
    · simp only [Fin.snoc_last, labelOfIndex]

theorem scaled_isolated_gVec (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (B : Finset ℕ) (a : Fin (labelBound n)) (ha : ∀ u, D.H.lab u ≠ some a)
    (x : Fin (labelBound n)) :
    (Real.sqrt (labelBound n : ℝ) : ℂ) •
        (addIsolatedDescription D a (labelOfIndex x)).gVec l G B =
      ∑ φ, if D.IsGood l G B φ ∧ ∀ u, φ u ≠ labelOfIndex x then
        (Real.sqrt (D.H.muRef l G φ) : ℂ) •
          ket ((totalDb (l := l) D.H hD.1 hG φ).1.addPair x a, (totalDb (l := l) D.H hD.1 hG φ).2)
      else 0 := by
  rw [gVec_eq_total_sum hG _ (addIsolatedDescription_valid D hD a ha (labelOfIndex x)) B,
    sum_assignments_snoc]
  have hsum : (∑ y : Label n, ∑ φ : Fin D.H.k → Label n,
      if (addIsolatedDescription D a (labelOfIndex x)).IsGood l G B (Fin.snoc φ y) then
        (Real.sqrt ((addIsolated D.H a).muRef l G (Fin.snoc φ y)) : ℂ) •
          ket (totalDb (l := l) (addIsolated D.H a) (addIsolated_valid D.H hD.1 a ha) hG (Fin.snoc φ y))
      else 0) =
      ∑ φ : Fin D.H.k → Label n,
      if (addIsolatedDescription D a (labelOfIndex x)).IsGood l G B (Fin.snoc φ (labelOfIndex x)) then
        (Real.sqrt ((addIsolated D.H a).muRef l G (Fin.snoc φ (labelOfIndex x))) : ℂ) •
          ket (totalDb (l := l) (addIsolated D.H a) (addIsolated_valid D.H hD.1 a ha) hG
            (Fin.snoc φ (labelOfIndex x))) else 0 := by
    apply Finset.sum_eq_single (labelOfIndex x)
    · intro y hy hxy
      apply Finset.sum_eq_zero
      intro φ hφ
      apply if_neg
      intro hh
      have he := ((addIsolatedDescription_good D hD a ha (labelOfIndex x) B (Fin.snoc φ y)).mp hh).2.1
      exact hxy (by simpa only [Fin.snoc_last] using he)
    · intro hh; exact (hh (Finset.mem_univ _)).elim
  rw [hsum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro φ hφuniv
  have hp : 1 ≤ (labelOfIndex x).val := by change 1 ≤ x.val + 1; omega
  have hg : (addIsolatedDescription D a (labelOfIndex x)).IsGood l G B
      (Fin.snoc φ (labelOfIndex x)) ↔ D.IsGood l G B φ ∧ ∀ u, φ u ≠ labelOfIndex x := by
    simpa only [Fin.snoc_castSucc, Fin.snoc_last, hp, and_self, true_and, and_true] using
      addIsolatedDescription_good D hD a ha (labelOfIndex x) B (Fin.snoc φ (labelOfIndex x))
  by_cases hφ : D.IsGood l G B φ ∧ ∀ u, φ u ≠ labelOfIndex x
  · rw [if_pos (hg.mpr hφ), if_pos hφ, smul_smul,
      totalDb_addIsolated D.H hD.1 hG a ha φ hφ.1.2.2.2 x hφ.2,
      addIsolated_muRef l G D.H hD.1 a ha]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, if_pos hp]
    congr 1
    exact_mod_cast sqrt_normalize_isolated (labelBound n : ℝ) (D.H.muRef l G φ) (labelBound_real_pos n)
  · rw [if_neg (fun h => hφ (hg.mp h)), if_neg hφ, smul_zero]

theorem freshRemainder_eq_isolated (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (a : Fin (labelBound n))
    (ha : ∀ u, D.H.lab u ≠ some a) :
    freshRemainder D hD hG hln B a = (Real.sqrt (labelBound n : ℝ) : ℂ) •
      ∑ x : Fin (labelBound n), (addIsolatedDescription D a (labelOfIndex x)).gVec l G B := by
  rw [Finset.smul_sum]
  simp_rw [scaled_isolated_gVec hG D hD B a ha]
  rw [Finset.sum_comm]
  unfold freshRemainder
  apply Finset.sum_congr rfl
  intro φ hφuniv
  by_cases hφ : D.IsGood l G B φ
  · rw [dif_pos hφ, Finset.smul_sum]
    unfold freshPositions
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    have hf := freshPositions_iff D.H φ
      (positive_mu_vertex_nonzero D.H φ (ne_of_gt hφ.1) hln) x
    simp only [freshPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    by_cases h : ∀ u, vertexLabelIndex D.H φ
        (positive_mu_vertex_nonzero D.H φ (ne_of_gt hφ.1) hln) u ≠ x
    · rw [if_pos h, if_pos ⟨hφ,hf.mp h⟩]
    · rw [if_neg h, if_neg (fun hh => h (hf.mpr hh.2))]
  · rw [dif_neg hφ]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    exact if_neg (fun h => hφ h.1)

theorem insertion_gVec (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (a : Fin (labelBound n))
    (ha : ∀ u, D.H.lab u ≠ some a) :
    insertion a (D.gVec l G B) =
      (∑ u ∈ Finset.univ.filter (fun u => D.H.lab u = none),
        (relabelDescription D u a).gVec l G B) +
      (Real.sqrt (labelBound n : ℝ) : ℂ) •
        ∑ x : Fin (labelBound n), (addIsolatedDescription D a (labelOfIndex x)).gVec l G B := by
  rw [insertion_gVec_split hG D hD hln B a ha, freshRemainder_eq_isolated hG D hD hln B a ha]

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathSupportedRestriction
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical WeightedCoefficients HilbertSupport

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def restrictState (H : AbsForest n) (f : Hil (Fin H.k → Label n)) :
    Hil (SupportedAssignment l G H) := WithLp.toLp 2 (fun φ => f φ.1)

theorem restrictState_projection (H : AbsForest n) (f : Hil (Fin H.k → Label n)) :
    restrictState (l := l) (G := G) H ((eventSpace Function.Injective).starProjection f) =
      restrictState H f := by
  ext φ
  change (eventSpace Function.Injective).starProjection f φ.1 = f φ.1
  rw [eventSpace_projection, diagProj_apply, if_pos φ.2.1]

theorem norm_restrict_sq_eq_injective_projection (H : AbsForest n)
    (f : Hil (Fin H.k → Label n)) (hf : ∀ φ, H.muRef l G φ = 0 → f φ = 0) :
    ‖restrictState (l := l) (G := G) H f‖ ^ 2 =
      ‖(eventSpace Function.Injective).starProjection f‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  trans ∑ φ ∈ Finset.univ.filter (fun φ : Fin H.k → Label n =>
      Function.Injective φ ∧ H.muRef l G φ ≠ 0), ‖f φ‖ ^ 2
  · exact (Finset.sum_subtype _ (by simp) (fun φ => ‖f φ‖ ^ 2)).symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro φ _
  by_cases hi : Function.Injective φ
  · by_cases hm : H.muRef l G φ = 0
    · simp only [hi, hm, ne_eq, not_true_eq_false, and_false, if_false,
        eventSpace_projection, diagProj_apply, if_true, hf φ hm, norm_zero,
        zero_pow (by decide : 2 ≠ 0)]
    · rw [if_pos ⟨hi, hm⟩, eventSpace_projection, diagProj_apply, if_pos hi]
  · simp only [hi, false_and, if_false, eventSpace_projection, diagProj_apply,
      norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem norm_encode_restrict_sq (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (f : Hil (Fin H.k → Label n))
    (hf : ∀ φ, H.muRef l G φ = 0 → f φ = 0)
    (hinv : ∀ (φ ψ : Fin H.k → Label n) (e : Fin H.k ≃ Fin H.k),
      IsForestIso H H e → (∀ u, ψ (e u) = φ u) → f φ = f ψ) :
    ‖encodeState H hH hG.2 (restrictState (l := l) (G := G) H f)‖ ^ 2 =
      (Fintype.card (ForestAut H) : ℝ) *
        ‖(eventSpace Function.Injective).starProjection f‖ ^ 2 := by
  rw [encodeState_norm_sq hG H hH hln _ (fun φ ψ e he hm => hinv φ.1 ψ.1 e he hm),
    norm_restrict_sq_eq_injective_projection H f hf]

theorem restrict_goodAmplitude (D : Description n) (B : Finset ℕ) :
    restrictState (l := l) (G := G) D.H
      (WithLp.toLp 2 (fun φ => if D.IsGood l G B φ then (Real.sqrt (D.H.muRef l G φ) : ℂ) else 0)) =
      goodAssignmentState D B := rfl

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathAutomorphismAverage
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def autAssignment (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (a : ForestAut H) (φ : SupportedAssignment l G H) : SupportedAssignment l G H := by
  let χ := autToFiber hG H hH φ.1 φ.2.1 φ.2.2 (encodedDb H hH hG.2 φ)
    (encodedDb_isDbOf H hH hG.2 φ) a
  exact ⟨χ.1, χ.2.1, χ.2.2.1⟩

theorem autAssignment_apply (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (a : ForestAut H) (φ : SupportedAssignment l G H) (u : Fin H.k) :
    (autAssignment hG H hH a φ).1 u = φ.1 (a.1.symm u) := rfl

noncomputable def autEncodedFiberEquiv (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (φ : SupportedAssignment l G H) :
    ForestAut H ≃ {χ : SupportedAssignment l G H //
      encodedDb H hH hG.2 χ = encodedDb H hH hG.2 φ} :=
  (automorphismFiberEquiv hG H hH φ.1 φ.2.1 φ.2.2 hln (encodedDb H hH hG.2 φ)
    (encodedDb_isDbOf H hH hG.2 φ)).trans
    (encodedFiberEquiv H hH hG.2 (encodedDb H hH hG.2 φ)).symm

theorem symmetrizeState_eq_autAverage (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (ψ : Hil (SupportedAssignment l G H)) (φ : SupportedAssignment l G H) :
    symmetrizeState H hH hG.2 ψ φ = (Fintype.card (ForestAut H) : ℂ)⁻¹ *
      ∑ a : ForestAut H, ψ (autAssignment hG H hH a φ) := by
  have hs := Fintype.sum_equiv (autEncodedFiberEquiv hG H hH hln φ)
    (fun a : ForestAut H => ψ (autAssignment hG H hH a φ))
    (fun χ : {χ : SupportedAssignment l G H //
      encodedDb H hH hG.2 χ = encodedDb H hH hG.2 φ} => ψ χ.1)
    (fun a => rfl)
  have ht : (∑ χ ∈ Finset.univ.filter
      (fun χ => encodedDb H hH hG.2 χ = encodedDb H hH hG.2 φ), ψ χ) =
      ∑ a : ForestAut H, ψ (autAssignment hG H hH a φ) :=
    (Finset.sum_subtype _ (by simp) (fun χ => ψ χ)).trans hs.symm
  simp only [symmetrizeState, UniformFiberEncoding.fiberAverage,
    UniformFiberEncoding.pushforward, PiLp.toLp_apply]
  congr 1
  convert ht using 1
  congr 1
  ext χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathCoefficientTransport
section

namespace WeldedPath.CoefficientTransport

open Classical WeightedCoefficients HilbertSupport

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

noncomputable def reindex (e : X ≃ Y) : Hil X ≃ₗᵢ[ℂ] Hil Y :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem reindex_apply (e : X ≃ Y) (f : Hil X) (y : Y) :
    reindex e f y = f (e.symm y) := rfl

theorem reindex_event (e : X ≃ Y) (P : X → Prop) (f : Hil X) :
    reindex e ((eventSpace P).starProjection f) =
      (eventSpace (fun y => P (e.symm y))).starProjection (reindex e f) := by
  ext y
  simp [eventSpace_projection, diagProj_apply]

theorem reindex_event_norm (e : X ≃ Y) (P : X → Prop) (f : Hil X) :
    ‖(eventSpace P).starProjection f‖ =
      ‖(eventSpace (fun y => P (e.symm y))).starProjection (reindex e f)‖ := by
  rw [← reindex_event, (reindex e).norm_map]

theorem map_eventSpace (e : X ≃ Y) (P : X → Prop) :
    (eventSpace P).map (reindex e).toLinearMap = eventSpace (fun y => P (e.symm y)) := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩ y hy
    exact hf (e.symm y) hy
  · intro hg
    refine ⟨(reindex e).symm g, ?_, (reindex e).apply_symm_apply g⟩
    intro x hx
    have he : (reindex e).symm g x = g (e x) := by
      have hh := congrArg (fun f : Hil Y => f (e x)) ((reindex e).apply_symm_apply g)
      simpa only [reindex_apply, Equiv.symm_apply_apply] using hh
    rw [he]
    exact hg (e x) (by simpa only [Equiv.symm_apply_apply] using hx)

theorem map_minimal {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (S R : Submodule ℂ E) (f : E)
    (hf : f ∈ (S ⊓ Rᗮ)ᗮ) :
    U f ∈ (S.map U.toLinearMap ⊓ (R.map U.toLinearMap)ᗮ)ᗮ := by
  have hmem : U f ∈ ((S ⊓ Rᗮ)ᗮ).map U.toLinearMap := ⟨f,hf,rfl⟩
  rw [(S ⊓ Rᗮ).map_orthogonal_equiv U,
    Submodule.map_inf U.toLinearMap U.injective, R.map_orthogonal_equiv U] at hmem
  exact hmem

end WeldedPath.CoefficientTransport

end

-- Solutions.WeldedPathAssignmentAutomorphisms
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical
open WeldedPath.CoefficientTransport WeldedPath.WeightedCoefficients

variable {n : ℕ}

def assignmentPerm (H : AbsForest n) (e : Fin H.k ≃ Fin H.k) :
    Equiv.Perm (Fin H.k → Label n) where
  toFun φ u := φ (e.symm u)
  invFun φ u := φ (e u)
  left_inv φ := by funext u; simp
  right_inv φ := by funext u; simp

noncomputable def autState (H : AbsForest n) (e : Fin H.k ≃ Fin H.k) :
    Hil (Fin H.k → Label n) ≃ₗᵢ[ℂ] Hil (Fin H.k → Label n) :=
  reindex (assignmentPerm H e)

@[simp] theorem autState_apply (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (f : Hil (Fin H.k → Label n)) (φ : Fin H.k → Label n) :
    autState H e f φ = f (fun u => φ (e u)) := rfl

@[simp] theorem autState_symm_apply (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (f : Hil (Fin H.k → Label n)) : autState H e.symm (autState H e f) = f := by
  ext φ
  simp only [autState_apply, Equiv.symm_apply_apply]

@[simp] theorem autState_apply_symm (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (f : Hil (Fin H.k → Label n)) : autState H e (autState H e.symm f) = f := by
  ext φ
  simp only [autState_apply, Equiv.apply_symm_apply]

lemma assignmentPerm_symm_injective_iff (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (φ : Fin H.k → Label n) :
    Function.Injective ((assignmentPerm H e).symm φ) ↔ Function.Injective φ := by
  constructor
  · intro h u v huv
    apply e.symm.injective
    apply h
    change φ (e (e.symm u)) = φ (e (e.symm v))
    simpa only [Equiv.apply_symm_apply] using huv
  · intro h u v huv
    exact e.injective (h huv)

theorem autState_event (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (f : Hil (Fin H.k → Label n)) :
    autState H e ((eventSpace Function.Injective).starProjection f) =
      (eventSpace Function.Injective).starProjection (autState H e f) := by
  have h := reindex_event (assignmentPerm H e) Function.Injective f
  simpa only [autState,assignmentPerm_symm_injective_iff] using h

theorem autState_map_injective (H : AbsForest n) (e : Fin H.k ≃ Fin H.k) :
    (eventSpace (Function.Injective : (Fin H.k → Label n) → Prop)).map
      (autState H e).toLinearMap = eventSpace Function.Injective := by
  have h := map_eventSpace (assignmentPerm H e) Function.Injective
  simpa only [autState,assignmentPerm_symm_injective_iff] using h

theorem minimal_invariant_of_map (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (S : Submodule ℂ (Hil (Fin H.k → Label n)))
    (hS : S.map (autState H e).toLinearMap = S)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ S)
    (hm : f ∈ (S ⊓ (eventSpace Function.Injective)ᗮ)ᗮ)
    (hi : autState H e ((eventSpace Function.Injective).starProjection f) =
      (eventSpace Function.Injective).starProjection f) : autState H e f = f := by
  have hf' : autState H e f ∈ S := hS ▸ (show autState H e f ∈ S.map (autState H e).toLinearMap from ⟨f,hf,rfl⟩)
  have hm' := map_minimal (autState H e) S (eventSpace Function.Injective) f hm
  rw [hS,autState_map_injective] at hm'
  apply WeldedPath.CoefficientStability.projection_injective_on_minimal S
    (eventSpace Function.Injective) hf' hf hm' hm
  rw [← autState_event,hi]

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathDescriptionAutomorphisms
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical ForestFactorization

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable abbrev renameDescription (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) : Description n :=
  ⟨H,sel.image e,fun u => φ₀ (e.symm u)⟩

lemma renameDescription_valid (H : AbsForest n) (e : Fin H.k ≃ Fin H.k)
    (hiso : IsForestIso H H e) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) : (renameDescription H e sel φ₀).IsValid := by
  refine ⟨hD.1,?_⟩
  intro u
  obtain ⟨s,hs,hunique⟩ := hD.2 (e.symm u)
  refine ⟨e s,⟨Finset.mem_image.mpr ⟨s,hs.1,rfl⟩,?_⟩,?_⟩
  · have h := (graphIso H H hD.1 hD.1 e hiso).reachable_iff.mpr hs.2
    change H.graph.Reachable (e (e.symm u)) (e s) at h
    change H.graph.Reachable u (e s)
    rw [e.apply_symm_apply] at h
    exact h
  · intro t ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht.1
    apply congrArg e
    apply hunique v
    refine ⟨hv,?_⟩
    apply (graphIso H H hD.1 hD.1 e hiso).reachable_iff.mp
    change H.graph.Reachable (e (e.symm u)) (e v)
    rw [e.apply_symm_apply]
    exact ht.2

lemma description_conditions_rename (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k ≃ Fin H.k) (hiso : IsForestIso H H e)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ φ ψ : Fin H.k → Label n)
    (he : ∀ u, ψ (e u) = φ u) :
    ((∀ s ∈ sel.image e, H.Wfix ψ s = H.Wfix (fun u => φ₀ (e.symm u)) s) ∧
      (∀ s ∈ sel.image e, ∀ u, H.graph.Reachable s u →
        u ∉ H.Ctree ψ s → (ψ u).val ∉ B)) ↔
    ((∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
      (∀ s ∈ sel, ∀ u, H.graph.Reachable s u →
        u ∉ H.Ctree φ s → (φ u).val ∉ B)) := by
  have he₀ : ∀ u, (fun v => φ₀ (e.symm v)) (e u) = φ₀ u := by simp
  constructor
  · rintro ⟨hw,hB⟩
    constructor
    · intro s hs
      exact (wfix_fiber_iso H H hH hH e hiso φ φ₀ ψ _ he he₀ s).mp
        (hw (e s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩))
    · intro s hs u hr hc
      have h := hB (e s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩) (e u)
        ((graphIso H H hH hH e hiso).reachable_iff.mpr hr)
        (fun hu => hc ((ctree_mem_iso H H hH hH e hiso φ ψ he u s).mp hu))
      simpa only [he] using h
  · rintro ⟨hw,hB⟩
    constructor
    · intro s hs
      obtain ⟨s,hsel,rfl⟩ := Finset.mem_image.mp hs
      exact (wfix_fiber_iso H H hH hH e hiso φ φ₀ ψ _ he he₀ s).mpr (hw s hsel)
    · intro s hs u hr hc
      obtain ⟨s,hsel,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨u,rfl⟩ := e.surjective u
      rw [he]
      exact hB s hsel u ((graphIso H H hH hH e hiso).reachable_iff.mp hr)
        (fun hu => hc ((ctree_mem_iso H H hH hH e hiso φ ψ he u s).mpr hu))

theorem descriptionWeight_rename (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k ≃ Fin H.k) (hiso : IsForestIso H H e)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ φ ψ : Fin H.k → Label n)
    (he : ∀ u, ψ (e u) = φ u) :
    descriptionWeight l G B (renameDescription H e sel φ₀) ψ =
      descriptionWeight l G B (Description.mk H sel φ₀) φ := by
  unfold descriptionWeight renameDescription
  simp only [description_conditions_rename H hH e hiso B sel φ₀ φ ψ he,
    muRef_automorphism hG H hH e hiso φ ψ he]

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathDisconnectedStability
section

namespace WeldedPath.Supplement.DisconnectedStability

open Classical DescriptionCoefficients
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

private theorem minimal_from_representative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S R : Submodule ℂ E) (f₀ g : E) (hg : g ∈ S)
    (hproj : R.starProjection g = R.starProjection f₀)
    (hbound : ‖g‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2) :
    ∃! f : E, f ∈ S ∧ f ∈ (S ⊓ Rᗮ)ᗮ ∧
      R.starProjection f = R.starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2 := by
  let K := S ⊓ Rᗮ
  let f := g - K.starProjection g
  have hk : K.starProjection g ∈ K := K.starProjection_apply_mem g
  have hfS : f ∈ S := S.sub_mem hg hk.1
  have hfK : f ∈ Kᗮ := K.sub_starProjection_mem_orthogonal g
  have hpf : R.starProjection f = R.starProjection f₀ := by
    have hz : R.starProjection (K.starProjection g) = 0 :=
      R.starProjection_apply_eq_zero_iff.mpr hk.2
    dsimp [f]
    rw [map_sub, hz, sub_zero, hproj]
  have hnf : ‖f‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    have h := K.norm_sq_eq_add_norm_sq_starProjection g
    have heq : Kᗮ.starProjection g = f := by
      rw [Submodule.starProjection_orthogonal]
      rfl
    rw [heq] at h
    nlinarith [sq_nonneg ‖K.starProjection g‖]
  refine ⟨f, ⟨hfS, hfK, hpf, hnf.trans hbound⟩, ?_⟩
  intro f' hf'
  exact CoefficientStability.projection_injective_on_minimal S R
    hf'.1 hfS hf'.2.1 hfK (hf'.2.2.1.trans hpf.symm)

set_option maxHeartbeats 800000 in
theorem disconnected_stable_representative (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (H.k : ℝ) ^ 3 *
      (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (f₀ : Hil (Fin H.k → Label n)) (hf₀ : f₀ ∈ coefficientSpace l G H B) :
    ∃! f : Hil (Fin H.k → Label n), f ∈ coefficientSpace l G H B ∧
      f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (eventSpace Function.Injective).starProjection f =
        (eventSpace Function.Injective).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 := by
  let literal := fun (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) =>
      (WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
        if (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
          (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
        then (Real.sqrt (H.muRef l G φ) : ℂ) else 0) : Hil (Fin H.k → Label n))
  let S := Submodule.span ℂ {f | ∃ sel φ₀,
    (Description.mk H sel φ₀).IsValid ∧ f = literal sel φ₀}
  have he (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) :
      amplitude l G H B sel φ₀ = literal sel φ₀ := by
    ext φ
    change (Real.sqrt (if (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
        (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
      then H.muRef l G φ else 0) : ℂ) = _
    by_cases h : (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
        (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
    · simp only [literal, PiLp.toLp_apply, if_pos h]
    · simp only [literal, PiLp.toLp_apply, if_neg h, Real.sqrt_zero, Complex.ofReal_zero]
  have hS : coefficientSpace l G H B = S := by
    trans descriptionSpan l G H B
    · exact coefficientSpace_eq_descriptionSpan l G H hH B
    unfold descriptionSpan S
    congr 1
    ext f
    constructor
    · rintro ⟨sel, φ₀, hD, rfl⟩
      exact ⟨sel, φ₀, hD, he sel φ₀⟩
    · rintro ⟨sel, φ₀, hD, rfl⟩
      exact ⟨sel, φ₀, hD, (he sel φ₀).symm⟩
  have hf₀S : f₀ ∈ S := hS ▸ hf₀
  obtain ⟨g, hg, hp, hnrm⟩ := WeldedPath.forest_coefficient_stability n l hn hl hln
    G hG H hH B hB hBw hsurvive hcollision f₀ hf₀S
  have hgS : g ∈ coefficientSpace l G H B := hS.symm ▸ hg
  have hproj : (eventSpace Function.Injective).starProjection g =
      (eventSpace Function.Injective).starProjection f₀ := by
    ext φ
    simp only [eventSpace_projection, diagProj_apply]
    split_ifs with hφ
    · exact hp φ hφ
    · rfl
  have hsum : (∑ φ, if Function.Injective φ then ‖f₀ φ‖ ^ 2 else 0) =
      ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 := by
    rw [eventSpace_projection, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro φ _
    by_cases hφ : Function.Injective φ <;> simp [diagProj_apply, hφ]
  rw [hsum] at hnrm
  exact minimal_from_representative (coefficientSpace l G H B)
    (eventSpace Function.Injective) f₀ g hgS hproj hnrm

end WeldedPath.Supplement.DisconnectedStability

end

-- Solutions.WeldedPathCoefficientAutomorphisms
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical DescriptionCoefficients ForestFactorization DisconnectedStability
open WeldedPath.WeightedCoefficients

variable {n l : ℕ} {G : WeldedInstance n}

theorem autState_amplitude (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k ≃ Fin H.k) (hiso : IsForestIso H H e)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) :
    autState H e (amplitude l G H B sel φ₀) =
      amplitude l G H B (sel.image e) (fun u => φ₀ (e.symm u)) := by
  ext ψ
  change (Real.sqrt (descriptionWeight l G B ⟨H,sel,φ₀⟩ (fun u => ψ (e u))) : ℂ) =
    (Real.sqrt (descriptionWeight l G B ⟨H,sel.image e,fun u => φ₀ (e.symm u)⟩ ψ) : ℂ)
  rw [descriptionWeight_rename hG H hH e hiso B sel φ₀ (fun u => ψ (e u)) ψ (fun _ => rfl)]

theorem autState_mem_descriptionSpan (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k ≃ Fin H.k) (hiso : IsForestIso H H e) (B : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ descriptionSpan l G H B) :
    autState H e f ∈ descriptionSpan l G H B := by
  change f ∈ Submodule.span ℂ (descriptionGenerators l G H B) at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨sel,φ₀,hD,rfl⟩ := hg
    rw [autState_amplitude hG H hH e hiso]
    exact Submodule.subset_span ⟨sel.image e,fun u => φ₀ (e.symm u),
      renameDescription_valid H e hiso sel φ₀ hD,rfl⟩
  | zero => simpa only [map_zero] using (descriptionSpan l G H B).zero_mem
  | add g h hg hh ihg ihh =>
    simpa only [map_add] using (descriptionSpan l G H B).add_mem ihg ihh
  | smul c g hg ih =>
    simpa only [map_smul] using (descriptionSpan l G H B).smul_mem c ih

theorem autState_map_coefficientSpace (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k ≃ Fin H.k) (hiso : IsForestIso H H e) (B : Finset ℕ) :
    (coefficientSpace l G H B).map (autState H e).toLinearMap = coefficientSpace l G H B := by
  have hS : coefficientSpace l G H B = descriptionSpan l G H B :=
    coefficientSpace_eq_descriptionSpan l G H hH B
  rw [hS]
  apply le_antisymm
  · rintro f ⟨g,hg,rfl⟩
    exact autState_mem_descriptionSpan hG H hH e hiso B g hg
  · intro f hf
    exact ⟨autState H e.symm f,
      autState_mem_descriptionSpan hG H hH e.symm (hiso.symm H H e) B f hf,
      autState_apply_symm H e f⟩

theorem coefficient_zero_of_muRef_zero (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (f : Hil (Fin H.k → Label n)) (hf : f ∈ coefficientSpace l G H B)
    (φ : Fin H.k → Label n) (hμ : H.muRef l G φ = 0) : f φ = 0 := by
  have hS : coefficientSpace l G H B = descriptionSpan l G H B :=
    coefficientSpace_eq_descriptionSpan l G H hH B
  have hle : descriptionSpan l G H B ≤ eventSpace (fun ψ => H.muRef l G ψ ≠ 0) := by
    apply Submodule.span_le.mpr
    rintro g ⟨sel,φ₀,hD,rfl⟩ ψ hψ
    have hzero : H.muRef l G ψ = 0 := not_not.mp hψ
    simp [amplitude,descriptionWeight,hzero]
  exact hle (hS ▸ hf) φ (by simpa only [hμ,ne_eq,not_true_eq_false,not_false_eq_true])

theorem coefficient_minimal_invariant (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (f : Hil (Fin H.k → Label n)) (hf : f ∈ coefficientSpace l G H B)
    (hm : f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ)
    (e : Fin H.k ≃ Fin H.k) (hiso : IsForestIso H H e)
    (hi : autState H e ((eventSpace Function.Injective).starProjection f) =
      (eventSpace Function.Injective).starProjection f) : autState H e f = f :=
  minimal_invariant_of_map H e (coefficientSpace l G H B)
    (autState_map_coefficientSpace hG H hH e hiso B) f hf hm hi

theorem invariant_values_of_autState (H : AbsForest n) (f : Hil (Fin H.k → Label n))
    (hi : ∀ e : Fin H.k ≃ Fin H.k, IsForestIso H H e → autState H e f = f)
    (φ ψ : Fin H.k → Label n) (e : Fin H.k ≃ Fin H.k)
    (hiso : IsForestIso H H e) (he : ∀ u, ψ (e u) = φ u) : f φ = f ψ := by
  have h := congrArg (fun g : Hil (Fin H.k → Label n) => g ψ) (hi e hiso)
  simpa only [autState_apply,funext he] using h

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathDatabaseStableRepresentation
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical DescriptionCoefficients DisconnectedStability WeightedCoefficients

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def restrictionLinear (H : AbsForest n) :
    Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (SupportedAssignment l G H) where
  toFun := restrictState H
  map_add' f g := by ext φ; rfl
  map_smul' c f := by ext φ; rfl

noncomputable def averageFull (H : AbsForest n) (f : Hil (Fin H.k → Label n)) :
    Hil (Fin H.k → Label n) :=
  (Fintype.card (ForestAut H) : ℂ)⁻¹ • ∑ a : ForestAut H, autState H a.1.symm f

theorem restrict_averageFull (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (f : Hil (Fin H.k → Label n)) :
    restrictState (l := l) (G := G) H (averageFull H f) =
      symmetrizeState H hH hG.2 (restrictState H f) := by
  ext φ
  rw [symmetrizeState_eq_autAverage hG H hH hln]
  simp only [restrictState, averageFull, PiLp.toLp_apply, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, autState_apply, smul_eq_mul]
  congr 1

theorem averageFull_mem_coefficientSpace (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (f : Hil (Fin H.k → Label n)) (hf : f ∈ coefficientSpace l G H B) :
    averageFull H f ∈ coefficientSpace l G H B := by
  apply (coefficientSpace l G H B).smul_mem
  apply (coefficientSpace l G H B).sum_mem
  intro a _
  rw [← autState_map_coefficientSpace hG H hH a.1.symm (a.2.symm H H a.1) B]
  exact ⟨f, hf, rfl⟩

theorem restrict_amplitude (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) :
    restrictState (l := l) (G := G) H (amplitude l G H B sel φ₀) =
      goodAssignmentState (Description.mk H sel φ₀) B := by
  rw [← restrictState_projection H (amplitude l G H B sel φ₀),
    amplitude_injective_projection l G H B sel φ₀ hD]
  rfl

theorem invariantGoodSpace_le_restriction_coefficientSpace (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (hln : l + 2 ≤ n) (B : Finset ℕ) :
    invariantGoodSpace (l := l) H hH hG.2 B ≤
      (coefficientSpace l G H B).map (restrictionLinear (l := l) (G := G) H) := by
  apply Submodule.span_le.mpr
  rintro ψ ⟨sel, φ₀, hD, rfl⟩
  refine ⟨averageFull H (amplitude l G H B sel φ₀),
    averageFull_mem_coefficientSpace hG H hH B _
      (amplitude_mem_coefficientSpace l G H B sel φ₀ hD), ?_⟩
  change restrictState H (averageFull H _) = _
  rw [restrict_averageFull hG H hH hln, restrict_amplitude l G H B sel φ₀ hD]

theorem injectiveProjection_invariant_of_restriction (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (f : Hil (Fin H.k → Label n))
    (hf : ∀ φ, H.muRef l G φ = 0 → f φ = 0)
    (hi : restrictState (l := l) (G := G) H f ∈ invariantSpace H)
    (e : Fin H.k ≃ Fin H.k) (he : IsForestIso H H e) :
    autState H e ((eventSpace Function.Injective).starProjection f) =
      (eventSpace Function.Injective).starProjection f := by
  ext φ
  rw [autState_apply, eventSpace_projection, HilbertSupport.diagProj_apply,
    HilbertSupport.diagProj_apply]
  have hinj : Function.Injective (fun u => φ (e u)) ↔ Function.Injective φ :=
    assignmentPerm_symm_injective_iff H e φ
  by_cases hφ : Function.Injective φ
  · rw [if_pos (hinj.mpr hφ), if_pos hφ]
    have hμeq := muRef_automorphism (l := l) hG H hH e he (fun u => φ (e u)) φ (fun _ => rfl)
    by_cases hμ : H.muRef l G φ = 0
    · rw [hf φ hμ, hf _ (hμeq.trans hμ)]
    · let a : SupportedAssignment l G H := ⟨φ, hφ, hμ⟩
      let b : SupportedAssignment l G H :=
        ⟨fun u => φ (e u), hinj.mpr hφ, fun h => hμ (hμeq.symm.trans h)⟩
      exact hi b a e he (fun _ => rfl)
  · rw [if_neg (fun h => hφ (hinj.mp h)), if_neg hφ]

theorem database_stable_representative (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (v : Hil (Db l G)) (hv : v ∈ fixedForestGoodSpace l G H B) :
    ∃ f : Hil (Fin H.k → Label n),
      f ∈ coefficientSpace l G H B ∧
      f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (∀ e : Fin H.k ≃ Fin H.k, IsForestIso H H e → autState H e f = f) ∧
      encodeState H hH hG.2 (restrictState (l := l) (G := G) H f) = v ∧
      (Fintype.card (ForestAut H) : ℝ) * ‖f‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  have hln' : l + 2 ≤ n := by omega
  obtain ⟨ψ, ⟨hψ, henc, hnorm⟩, _⟩ :=
    fixedForestGoodSpace_representation hG H hH hln' B v hv
  obtain ⟨f₀, hf₀, hr₀⟩ :=
    invariantGoodSpace_le_restriction_coefficientSpace hG H hH hln' B hψ
  obtain ⟨f, ⟨hf, hm, hp, hbound⟩, _⟩ := disconnected_stable_representative H hH
    hG hn hl hln B hB hBw hsurvive hcollision f₀ hf₀
  have hr : restrictState (l := l) (G := G) H f = ψ := by
    calc
      _ = restrictState H ((eventSpace Function.Injective).starProjection f) :=
        (restrictState_projection H f).symm
      _ = restrictState H ((eventSpace Function.Injective).starProjection f₀) := congrArg _ hp
      _ = restrictState H f₀ := restrictState_projection H f₀
      _ = ψ := hr₀
  have hfzero := coefficient_zero_of_muRef_zero H hH B f hf
  have hinv : ∀ e : Fin H.k ≃ Fin H.k, IsForestIso H H e → autState H e f = f := by
    intro e he
    apply coefficient_minimal_invariant hG H hH B f hf hm e he
    apply injectiveProjection_invariant_of_restriction hG H hH f hfzero _ e he
    rw [hr]
    exact invariantGoodSpace_le H hH hG.2 B hψ
  refine ⟨f, hf, hm, hinv, by rw [hr]; exact henc, ?_⟩
  have hnorm' : (Fintype.card (ForestAut H) : ℝ) *
      ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← norm_restrict_sq_eq_injective_projection H f₀
      (coefficient_zero_of_muRef_zero H hH B f₀ hf₀)]
    change (Fintype.card (ForestAut H) : ℝ) * ‖restrictionLinear H f₀‖ ^ 2 = _
    rw [hr₀]
    exact hnorm
  calc
    _ ≤ (Fintype.card (ForestAut H) : ℝ) *
        (2 * ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = 2 * ‖v‖ ^ 2 := by nlinarith [hnorm']

theorem invariant_minimal_encoding_injective (hG : G.IsValid) (H : AbsForest n)
    (hH : H.IsValid) (hln : l + 2 ≤ n) (B : Finset ℕ)
    (f g : Hil (Fin H.k → Label n))
    (hf : f ∈ coefficientSpace l G H B) (hg : g ∈ coefficientSpace l G H B)
    (hfm : f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ)
    (hgm : g ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ)
    (hfi : ∀ e : Fin H.k ≃ Fin H.k, IsForestIso H H e → autState H e f = f)
    (hgi : ∀ e : Fin H.k ≃ Fin H.k, IsForestIso H H e → autState H e g = g)
    (he : encodeState H hH hG.2 (restrictState (l := l) (G := G) H f) =
      encodeState H hH hG.2 (restrictState H g)) : f = g := by
  have hμ : ∀ φ, H.muRef l G φ = 0 → (f - g) φ = 0 := by
    intro φ hφ
    change f φ - g φ = 0
    rw [coefficient_zero_of_muRef_zero H hH B f hf φ hφ,
      coefficient_zero_of_muRef_zero H hH B g hg φ hφ, sub_self]
  have hi : ∀ e : Fin H.k ≃ Fin H.k, IsForestIso H H e → autState H e (f - g) = f - g := by
    intro e he
    rw [map_sub, hfi e he, hgi e he]
  have hz : encodeState H hH hG.2 (restrictState (l := l) (G := G) H (f - g)) = 0 := by
    have hr : restrictState (l := l) (G := G) H (f - g) = restrictState H f - restrictState H g := rfl
    rw [hr, encodeState_eq_basisMap, map_sub, ← encodeState_eq_basisMap,
      ← encodeState_eq_basisMap, he, sub_self]
  have hs := norm_encode_restrict_sq hG H hH hln (f - g) hμ
    (invariant_values_of_autState H (f - g) hi)
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hs
  have ha : (Fintype.card (ForestAut H) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (forestAut_card_pos H))
  have hnorm := (mul_eq_zero.mp hs.symm).resolve_left ha
  have hproj : (eventSpace Function.Injective).starProjection (f - g) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  rw [map_sub, sub_eq_zero] at hproj
  exact CoefficientStability.projection_injective_on_minimal (coefficientSpace l G H B)
    (eventSpace Function.Injective) hf hg hfm hgm hproj

theorem database_unique_stable_representative (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (v : Hil (Db l G)) (hv : v ∈ fixedForestGoodSpace l G H B) :
    ∃! f : Hil (Fin H.k → Label n),
      f ∈ coefficientSpace l G H B ∧
      f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (∀ e : Fin H.k ≃ Fin H.k, IsForestIso H H e → autState H e f = f) ∧
      encodeState H hH hG.2 (restrictState (l := l) (G := G) H f) = v ∧
      (Fintype.card (ForestAut H) : ℝ) * ‖f‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  obtain ⟨f, hf⟩ := database_stable_representative hG H hH hn hl hln B hB hBw hsurvive hcollision v hv
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact invariant_minimal_encoding_injective hG H hH (by omega) B g f hg.1 hf.1 hg.2.1 hf.2.1
    hg.2.2.1 hf.2.2.1 (hg.2.2.2.1.trans hf.2.2.2.1.symm)

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathIsolatedPartialSum
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping DescriptionCoefficients DisconnectedStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def sumLast (k : ℕ) : Hil (Fin (k+1) → Label n) →ₗ[ℂ] Hil (Fin k → Label n) where
  toFun f := WithLp.toLp 2 (fun φ => ∑ x : Label n, f (Fin.snoc φ x))
  map_add' f g := by
    ext φ
    change (∑ x : Label n, (f (Fin.snoc φ x) + g (Fin.snoc φ x))) = _
    exact Finset.sum_add_distrib
  map_smul' c f := by
    ext φ
    change (∑ x : Label n, c * f (Fin.snoc φ x)) = c * ∑ x : Label n, f (Fin.snoc φ x)
    rw [Finset.mul_sum]

noncomputable def dropLastSelection (H : AbsForest n) (sel : Finset (Fin (H.k+1))) :
    Finset (Fin H.k) := Finset.univ.filter (fun u => u.castSucc ∈ sel)

lemma isolated_selected_last (H : AbsForest n) (a : Fin (labelBound n))
    (sel : Finset (Fin (H.k+1))) (φ₀ : Fin (H.k+1) → Label n)
    (hD : (Description.mk (addIsolated H a) sel φ₀).IsValid) : Fin.last H.k ∈ sel := by
  obtain ⟨s,hs,huniq⟩ := hD.2 (Fin.last H.k)
  exact (addIsolated_reachable_last H a s).mp hs.2 ▸ hs.1

lemma isolated_selection_eq (H : AbsForest n) (a : Fin (labelBound n))
    (sel : Finset (Fin (H.k+1))) (φ₀ : Fin (H.k+1) → Label n)
    (hD : (Description.mk (addIsolated H a) sel φ₀).IsValid) :
    sel = insert (Fin.last H.k) ((dropLastSelection H sel).image Fin.castSucc) := by
  ext u
  induction u using Fin.lastCases with
  | last => simp only [isolated_selected_last H a sel φ₀ hD, Finset.mem_insert, true_or]
  | cast u =>
    rw [Finset.mem_insert]
    simp only [Fin.castSucc_ne_last, false_or]
    rw [mem_image_injective Fin.castSucc (Fin.castSucc_injective _) (dropLastSelection H sel) u]
    change u.castSucc ∈ sel ↔ u ∈ Finset.univ.filter (fun v : Fin H.k => v.castSucc ∈ sel)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma dropLastDescription_valid (H : AbsForest n) (hH : H.IsValid) (a : Fin (labelBound n))
    (sel : Finset (Fin (H.k+1))) (φ₀ : Fin (H.k+1) → Label n)
    (hD : (Description.mk (addIsolated H a) sel φ₀).IsValid) :
    (Description.mk H (dropLastSelection H sel) (fun u => φ₀ u.castSucc)).IsValid := by
  refine ⟨hH,?_⟩
  intro u
  obtain ⟨s,hs,huniq⟩ := hD.2 u.castSucc
  induction s using Fin.lastCases with
  | last =>
    exact (Fin.castSucc_ne_last u ((addIsolated_reachable_last H a u.castSucc).mp hs.2.symm)).elim
  | cast s =>
    refine ⟨s,⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.1⟩,
      (addIsolated_reachable_old H a u s).mp hs.2⟩,?_⟩
    intro v hv
    exact Fin.castSucc_injective _ (huniq v.castSucc
      ⟨(Finset.mem_filter.mp hv.1).2, (addIsolated_reachable_old H a u v).mpr hv.2⟩)

theorem sumLast_isolated_amplitude (D : Description n) (hD : D.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u, D.H.lab u ≠ some a) (x : Label n) (B : Finset ℕ) :
    sumLast D.H.k (amplitude l G (addIsolated D.H a) B
      (insert (Fin.last D.H.k) (D.sel.image Fin.castSucc)) (Fin.snoc D.ϕ₀ x)) =
      if 1 ≤ x.val then (Real.sqrt (1 / (labelBound n : ℝ)) : ℂ) •
        amplitude l G D.H B D.sel D.ϕ₀ else 0 := by
  ext φ
  change (∑ y : Label n, (Real.sqrt
    (ForestFactorization.descriptionWeight l G B (addIsolatedDescription D a x) (Fin.snoc φ y)) : ℂ)) = _
  rw [Finset.sum_eq_single x]
  · rw [addIsolatedDescription_weight l G D hD a ha x B]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, true_and]
    by_cases hx : 1 ≤ x.val
    · rw [if_pos hx, if_pos hx]
      change (Real.sqrt (ForestFactorization.descriptionWeight l G B D φ * (1 / (labelBound n : ℝ))) : ℂ) =
        (Real.sqrt (1 / (labelBound n : ℝ)) : ℂ) * (Real.sqrt (ForestFactorization.descriptionWeight l G B D φ) : ℂ)
      rw [mul_comm (ForestFactorization.descriptionWeight l G B D φ),
        Real.sqrt_mul (one_div_nonneg.mpr (Nat.cast_nonneg _)), Complex.ofReal_mul]
    · rw [if_neg hx, if_neg hx]
      simp only [mul_zero, Real.sqrt_zero, Complex.ofReal_zero, PiLp.zero_apply]
  · intro y hy hxy
    rw [addIsolatedDescription_weight l G D hD a ha x B]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hxy, false_and, if_false, mul_zero,
      Real.sqrt_zero, Complex.ofReal_zero]
  · intro hx; exact (hx (Finset.mem_univ _)).elim

theorem sumLast_mem_descriptionSpan (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a) (B : Finset ℕ)
    (f : Hil (Fin (H.k+1) → Label n)) (hf : f ∈ descriptionSpan l G (addIsolated H a) B) :
    sumLast H.k f ∈ descriptionSpan l G H B := by
  have hle : descriptionSpan l G (addIsolated H a) B ≤
      (descriptionSpan l G H B).comap (sumLast H.k) := by
    apply Submodule.span_le.mpr
    rintro v ⟨sel,φ₀,hD,rfl⟩
    change sumLast H.k (amplitude l G (addIsolated H a) B sel φ₀) ∈ descriptionSpan l G H B
    have hs := isolated_selection_eq H a sel φ₀ hD
    have hr : (Fin.snoc (fun u => φ₀ u.castSucc) (φ₀ (Fin.last H.k)) : Fin (H.k+1) → Label n) = φ₀ :=
      Fin.snoc_init_self _
    have hdrop := dropLastDescription_valid H hH a sel φ₀ hD
    rw [hs, ← hr]
    rw [sumLast_isolated_amplitude (Description.mk H (dropLastSelection H sel) (fun u => φ₀ u.castSucc))
      hdrop a ha (φ₀ (Fin.last H.k)) B]
    split_ifs
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨dropLastSelection H sel, (fun u => φ₀ u.castSucc), hdrop, rfl⟩
    · exact Submodule.zero_mem _
  exact hle hf

theorem sumLast_mem_coefficientSpace (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a) (B : Finset ℕ)
    (f : Hil (Fin (H.k+1) → Label n)) (hf : f ∈ coefficientSpace l G (addIsolated H a) B) :
    sumLast H.k f ∈ coefficientSpace l G H B := by
  have hS : coefficientSpace l G H B = descriptionSpan l G H B :=
    coefficientSpace_eq_descriptionSpan l G H hH B
  have hT : coefficientSpace l G (addIsolated H a) B = descriptionSpan l G (addIsolated H a) B :=
    coefficientSpace_eq_descriptionSpan l G _ (addIsolated_valid H hH a ha) B
  exact hS.symm ▸ sumLast_mem_descriptionSpan H hH a ha B f (hT ▸ hf)

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathExcludedPartialSum
section

namespace WeldedPath.ExcludedPartialSum

open Classical
open scoped BigOperators

variable {U X : Type*} [Fintype U] [Fintype X]

noncomputable def partialSum (E : X → Finset U) (ψ : Hil (U × X)) : Hil X :=
  WithLp.toLp 2 (fun x => ∑ u ∈ E x, ψ (u, x))

theorem partialSum_norm_sq_le (E : X → Finset U) (k : ℕ) (hE : ∀ x, (E x).card ≤ k)
    (ψ : Hil (U × X)) : ‖partialSum E ψ‖ ^ 2 ≤ (k : ℝ) * ‖ψ‖ ^ 2 := by
  have hrow (x : X) : ‖∑ u ∈ E x, ψ (u, x)‖ ^ 2 ≤
      (k : ℝ) * ∑ u : U, ‖ψ (u, x)‖ ^ 2 := by
    have hn : ‖∑ u ∈ E x, ψ (u, x)‖ ≤ ∑ u ∈ E x, ‖ψ (u, x)‖ := norm_sum_le _ _
    have hsq := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr hn
    calc
      _ ≤ (∑ u ∈ E x, ‖ψ (u, x)‖) ^ 2 := hsq
      _ ≤ ((E x).card : ℝ) * ∑ u ∈ E x, ‖ψ (u, x)‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (k : ℝ) * ∑ u : U, ‖ψ (u, x)‖ ^ 2 := by
        apply mul_le_mul (by exact_mod_cast hE x) _ (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  calc
    _ = ∑ x, ‖∑ u ∈ E x, ψ (u, x)‖ ^ 2 := EuclideanSpace.norm_sq_eq _
    _ ≤ ∑ x, (k : ℝ) * ∑ u : U, ‖ψ (u, x)‖ ^ 2 := Finset.sum_le_sum fun x _ => hrow x
    _ = (k : ℝ) * ‖ψ‖ ^ 2 := by
      rw [← Finset.mul_sum, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]

/-- Summing over at most k omitted positions in every fiber costs k/m in
squared norm, including arbitrary spectator coordinates and coherent input. -/
theorem normalized_partialSum_bound (E : X → Finset U) (k : ℕ)
    (hE : ∀ x, (E x).card ≤ k) (m : ℝ) (hm : 0 ≤ m) (ψ : Hil (U × X)) :
    ‖((Real.sqrt m)⁻¹ : ℂ) • partialSum E ψ‖ ^ 2 ≤
      ((k : ℝ) / m) * ‖ψ‖ ^ 2 := by
  rw [norm_smul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg m), inv_pow, Real.sq_sqrt hm]
  calc
    _ ≤ m⁻¹ * ((k : ℝ) * ‖ψ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (partialSum_norm_sq_le E k hE ψ) (inv_nonneg.mpr hm)
    _ = _ := by ring

end WeldedPath.ExcludedPartialSum

end

-- Solutions.WeldedPathIsolatedOmission
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical
open scoped BigOperators

variable {n : ℕ}

noncomputable def usedLabels {k : ℕ} (φ : Fin k → Label n) : Finset (Label n) :=
  Finset.univ.image φ

noncomputable def availableLabels {k : ℕ} (φ : Fin k → Label n) : Finset (Label n) :=
  Finset.univ \ usedLabels φ

lemma mem_availableLabels {k : ℕ} (φ : Fin k → Label n) (x : Label n) :
    x ∈ availableLabels φ ↔ ∀ u, φ u ≠ x := by
  simp only [availableLabels, usedLabels, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image, not_exists, not_and, forall_const]

noncomputable def freeSumLast (k : ℕ) : Hil (Fin (k+1) → Label n) →ₗ[ℂ] Hil (Fin k → Label n) where
  toFun f := WithLp.toLp 2 (fun φ => ∑ x ∈ availableLabels φ, f (Fin.snoc φ x))
  map_add' f g := by
    ext φ
    change (∑ x ∈ availableLabels φ, (f (Fin.snoc φ x) + g (Fin.snoc φ x))) = _
    exact Finset.sum_add_distrib
  map_smul' c f := by
    ext φ
    change (∑ x ∈ availableLabels φ, c * f (Fin.snoc φ x)) = c * ∑ x ∈ availableLabels φ, f (Fin.snoc φ x)
    rw [Finset.mul_sum]

noncomputable def snocCoordinates (k : ℕ) :
    Hil (Fin (k+1) → Label n) ≃ₗᵢ[ℂ] Hil (Label n × (Fin k → Label n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fin.snocEquiv (fun _ : Fin (k+1) => Label n)).symm

@[simp] lemma snocCoordinates_apply (k : ℕ) (f : Hil (Fin (k+1) → Label n))
    (x : Label n) (φ : Fin k → Label n) : snocCoordinates k f (x,φ) = f (Fin.snoc φ x) := rfl

lemma omission_eq_partialSum (k : ℕ) (f : Hil (Fin (k+1) → Label n)) :
    sumLast k f - freeSumLast k f =
      ExcludedPartialSum.partialSum usedLabels (snocCoordinates k f) := by
  ext φ
  change (∑ x : Label n, f (Fin.snoc φ x)) -
    (∑ x ∈ Finset.univ \ usedLabels φ, f (Fin.snoc φ x)) =
      ∑ x ∈ usedLabels φ, f (Fin.snoc φ x)
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
  abel

theorem isolated_omission_bound (k : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (f : Hil (Fin (k+1) → Label n)) :
    ‖((Real.sqrt m)⁻¹ : ℂ) • (sumLast k f - freeSumLast k f)‖ ^ 2 ≤
      ((k : ℝ) / m) * ‖f‖ ^ 2 := by
  have hcard (φ : Fin k → Label n) : (usedLabels φ).card ≤ k := by
    exact (Finset.card_image_le).trans (by simp)
  have hb := ExcludedPartialSum.normalized_partialSum_bound usedLabels k hcard m hm (snocCoordinates k f)
  rw [← omission_eq_partialSum, (snocCoordinates k).norm_map] at hb
  exact hb

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.UniformFiberEncodingBound
section

namespace WeldedPath.UniformFiberEncoding

open Classical
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]

theorem norm_pushforward_sq_le (f : A → B) (m : ℕ)
    (hcount : ∀ a, (Finset.univ.filter (fun x => f x = f a)).card = m)
    (ψ : Hil A) : ‖pushforward f ψ‖ ^ 2 ≤ (m : ℝ) * ‖ψ‖ ^ 2 := by
  have hpoint (b : B) :
      ‖∑ a ∈ Finset.univ.filter (fun a => f a = b), ψ a‖ ^ 2 ≤
        (m : ℝ) * ∑ a ∈ Finset.univ.filter (fun a => f a = b), ‖ψ a‖ ^ 2 := by
    by_cases hb : (Finset.univ.filter (fun a => f a = b)).Nonempty
    · obtain ⟨a, ha⟩ := hb
      have hab : f a = b := (Finset.mem_filter.mp ha).2
      have hc : (Finset.univ.filter (fun a => f a = b)).card = m := by
        simpa only [hab] using hcount a
      calc
        _ ≤ (∑ a ∈ Finset.univ.filter (fun a => f a = b), ‖ψ a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [hc] using sq_sum_le_card_mul_sum_sq
            (s := Finset.univ.filter (fun a => f a = b)) (f := fun a => ‖ψ a‖)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hb
      simp only [he, Finset.sum_empty, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
        le_refl]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ b, ‖∑ a ∈ Finset.univ.filter (fun a => f a = b), ψ a‖ ^ 2) ≤ _
  calc
    _ ≤ ∑ b, (m : ℝ) * ∑ a ∈ Finset.univ.filter (fun a => f a = b), ‖ψ a‖ ^ 2 :=
      Finset.sum_le_sum (fun b _ => hpoint b)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (f a)) (fun a => ‖ψ a‖ ^ 2)

end WeldedPath.UniformFiberEncoding

end

-- Solutions.WeldedPathDatabaseEncodingBound
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}

theorem encodeState_norm_sq_le (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (ψ : Hil (SupportedAssignment l G H)) :
    ‖encodeState H hH hG.2 ψ‖ ^ 2 ≤ (Fintype.card (ForestAut H) : ℝ) * ‖ψ‖ ^ 2 := by
  refine UniformFiberEncoding.norm_pushforward_sq_le _ _ ?_ ψ
  intro φ
  convert encodedDb_fiber_card hG H hH hln φ using 1
  congr 1
  ext χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathFullEncoding
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical DescriptionCoefficients DisconnectedStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def fullEncoding (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) : Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Db l G) :=
  (basisMap (encodedDb H hH hG)).toLinearMap.comp (restrictionLinear H)

lemma fullEncoding_apply (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (f : Hil (Fin H.k → Label n)) :
    fullEncoding (l := l) H hH hG f = encodeState H hH hG (restrictState H f) := by
  rw [encodeState_eq_basisMap]
  rfl

theorem fullEncoding_eq_sum (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (f : Hil (Fin H.k → Label n))
    (hf : ∀ φ, H.muRef l G φ = 0 → f φ = 0) :
    fullEncoding (l := l) H hH hG f = ∑ φ, if Function.Injective φ then
      f φ • ket (totalDb H hH hG φ) else 0 := by
  let z : (Fin H.k → Label n) → Hil (Db l G) := fun φ => f φ • ket (totalDb H hH hG φ)
  calc
    _ = ∑ φ : SupportedAssignment l G H, z φ.1 := by
      rw [fullEncoding_apply, encodeState, UniformFiberEncoding.pushforward_eq_sum]
      apply Finset.sum_congr rfl
      intro φ _
      rw [encodedDb_eq_totalDb]
      simp only [restrictState, WithLp.ofLp_toLp, z]
      congr 1
      ext I
      simp only [ket, EuclideanSpace.single_apply]
      split_ifs <;> rfl
    _ = ∑ φ ∈ Finset.univ.filter (fun φ : Fin H.k → Label n =>
        Function.Injective φ ∧ H.muRef l G φ ≠ 0), z φ :=
      (Finset.sum_subtype _ (by simp) z).symm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro φ _
      by_cases hi : Function.Injective φ
      · by_cases hμ : H.muRef l G φ = 0
        · simp [hi, hμ, hf φ hμ, z]
        · rw [if_pos ⟨hi, hμ⟩, if_pos hi]
      · simp only [hi, false_and, ite_false]

theorem fullEncoding_amplitude (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (B : Finset ℕ) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) (hD : (Description.mk H sel φ₀).IsValid) :
    fullEncoding H hH hG (amplitude l G H B sel φ₀) =
      (Description.mk H sel φ₀).gVec l G B := by
  rw [fullEncoding_apply, restrict_amplitude l G H B sel φ₀ hD]
  exact encode_goodAssignmentState hG _ hD B

theorem fullEncoding_mem_fixedForestGoodSpace (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (B : Finset ℕ) (f : Hil (Fin H.k → Label n))
    (hf : f ∈ coefficientSpace l G H B) :
    fullEncoding H hH hG f ∈ fixedForestGoodSpace l G H B := by
  have hle : coefficientSpace l G H B ≤
      (fixedForestGoodSpace l G H B).comap (fullEncoding H hH hG) := by
    have hS : coefficientSpace l G H B = descriptionSpan l G H B :=
      coefficientSpace_eq_descriptionSpan l G H hH B
    rw [hS]
    apply Submodule.span_le.mpr
    rintro v ⟨sel, φ₀, hD, rfl⟩
    change fullEncoding H hH hG (amplitude l G H B sel φ₀) ∈ fixedForestGoodSpace l G H B
    rw [fullEncoding_amplitude H hH hG B sel φ₀ hD]
    exact Submodule.subset_span ⟨sel, φ₀, hD, rfl⟩
  exact hle hf

theorem fullEncoding_map_coefficientSpace (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (B : Finset ℕ) :
    (coefficientSpace l G H B).map (fullEncoding H hH hG) =
      fixedForestGoodSpace l G H B := by
  apply le_antisymm
  · rintro v ⟨f, hf, rfl⟩
    exact fullEncoding_mem_fixedForestGoodSpace H hH hG B f hf
  · apply Submodule.span_le.mpr
    rintro v ⟨sel, φ₀, hD, rfl⟩
    exact ⟨amplitude l G H B sel φ₀,
      amplitude_mem_coefficientSpace l G H B sel φ₀ hD,
      fullEncoding_amplitude H hH hG B sel φ₀ hD⟩

lemma restrictState_norm_sq_le (H : AbsForest n) (f : Hil (Fin H.k → Label n)) :
    ‖restrictState (l := l) (G := G) H f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ φ : SupportedAssignment l G H, ‖f φ.1‖ ^ 2) ≤ _
  calc
    _ = ∑ φ ∈ Finset.univ.filter (fun φ : Fin H.k → Label n =>
        Function.Injective φ ∧ H.muRef l G φ ≠ 0), ‖f φ‖ ^ 2 :=
      (Finset.sum_subtype _ (by simp) (fun φ => ‖f φ‖ ^ 2)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun φ _ _ => sq_nonneg ‖f φ‖)

theorem fullEncoding_norm_sq_le (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (hln : l + 2 ≤ n) (f : Hil (Fin H.k → Label n)) :
    ‖fullEncoding (l := l) H hH hG.2 f‖ ^ 2 ≤
      (Fintype.card (ForestAut H) : ℝ) * ‖f‖ ^ 2 := by
  rw [fullEncoding_apply]
  exact (encodeState_norm_sq_le hG H hH hln _).trans
    (mul_le_mul_of_nonneg_left (restrictState_norm_sq_le H f) (Nat.cast_nonneg _))

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathIsolatedEncoding
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport DisconnectedStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

def positiveIndex (y : Label n) (hy : 1 ≤ y.val) : Fin (labelBound n) :=
  ⟨y.val - 1, by have hi := y.isLt; change _ < labelBound n; omega⟩

lemma positiveIndex_val (y : Label n) (hy : 1 ≤ y.val) : y.val = (positiveIndex y hy).val + 1 := by
  change y.val = y.val - 1 + 1
  omega

lemma deletion_totalDb_isolated (H : AbsForest n) (hH : H.IsValid) (hG : G.IsProperColoring)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (φ : Fin H.k → Label n) (hφ : Function.Injective φ)
    (y : Label n) (hy : 1 ≤ y.val) (hf : ∀ u, φ u ≠ y) :
    deletion a (ket (totalDb (l := l) (addIsolated H a) (addIsolated_valid H hH a ha)
      hG (Fin.snoc φ y))) = ket (totalDb (l := l) H hH hG φ) := by
  have hi : Function.Injective (Fin.snoc φ y : Fin (H.k+1) → Label n) := by
    apply (injective_last_iff _).mpr
    simpa only [Fin.snoc_castSucc, Fin.snoc_last] using And.intro hφ hf
  let I := totalDb (l := l) (addIsolated H a) (addIsolated_valid H hH a ha) hG (Fin.snoc φ y)
  have hI : (addIsolated H a).IsDbOf l G (Fin.snoc φ y) I :=
    totalDb_isDbOf _ (addIsolated_valid H hH a ha) hG _ hi
  have hxy : ((Fin.snoc φ y : Fin (H.k+1) → Label n) (Fin.last H.k)).val =
      (positiveIndex y hy).val + 1 := by
    simpa only [Fin.snoc_last] using positiveIndex_val y hy
  have hrec := isolated_record_present H a (Fin.snoc φ y) I hI (positiveIndex y hy) hxy
  have him : I.1.symm a = some (positiveIndex y hy) := (I.1.inv _ a).mpr hrec
  change deletion a (ket I) = _
  rw [deletion_ket a I _ him]
  congr 1
  apply isDbOf_unique H φ
  · have hh := isDbOf_removeIsolated H a (Fin.snoc φ y) hi I hI (positiveIndex y hy) hxy
    simpa only [Fin.snoc_castSucc] using hh
  · exact totalDb_isDbOf H hH hG φ hφ

lemma isolated_f_zero_at_zero_last (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (f : Hil (Fin (H.k+1) → Label n))
    (hf : ∀ ψ, (addIsolated H a).muRef l G ψ = 0 → f ψ = 0)
    (φ : Fin H.k → Label n) (y : Label n) (hy : ¬ 1 ≤ y.val) : f (Fin.snoc φ y) = 0 := by
  apply hf
  rw [addIsolated_muRef l G H hH a ha]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, if_neg hy, mul_zero]

lemma freeSumLast_zero_of_muRef_zero (H : AbsForest n) (hH : H.IsValid)
    (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (f : Hil (Fin (H.k+1) → Label n))
    (hf : ∀ ψ, (addIsolated H a).muRef l G ψ = 0 → f ψ = 0)
    (φ : Fin H.k → Label n) (hφ : H.muRef l G φ = 0) : freeSumLast H.k f φ = 0 := by
  change (∑ y ∈ availableLabels φ, f (Fin.snoc φ y)) = 0
  apply Finset.sum_eq_zero
  intro y hy
  apply hf
  rw [addIsolated_muRef l G H hH a ha]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hφ, zero_mul]

theorem deletion_fullEncoding_isolated (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (f : Hil (Fin (H.k+1) → Label n))
    (hf : ∀ ψ, (addIsolated H a).muRef l G ψ = 0 → f ψ = 0) :
    deletion a (fullEncoding (l := l) (addIsolated H a) (addIsolated_valid H hH a ha) hG f) =
      fullEncoding (l := l) H hH hG (freeSumLast H.k f) := by
  rw [fullEncoding_eq_sum _ (addIsolated_valid H hH a ha) hG f hf,
    fullEncoding_eq_sum H hH hG _ (freeSumLast_zero_of_muRef_zero H hH a ha f hf),
    map_sum, sum_assignments_snoc, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro φ hφuniv
  by_cases hφ : Function.Injective φ
  · rw [if_pos hφ]
    change (∑ y : Label n, deletion a
      (if Function.Injective (Fin.snoc φ y : Fin (H.k+1) → Label n) then
        f (Fin.snoc φ y) • ket (totalDb (l := l) (addIsolated H a)
          (addIsolated_valid H hH a ha) hG (Fin.snoc φ y)) else 0)) =
      (∑ y ∈ availableLabels φ, f (Fin.snoc φ y)) • ket (totalDb (l := l) H hH hG φ)
    rw [Finset.sum_smul]
    have hs : availableLabels φ = Finset.univ.filter (fun y => ∀ u, φ u ≠ y) := by
      ext y
      simp only [mem_availableLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hyuniv
    by_cases hfree : ∀ u, φ u ≠ y
    · have hi : Function.Injective (Fin.snoc φ y : Fin (H.k+1) → Label n) := by
        apply (injective_last_iff _).mpr
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using And.intro hφ hfree
      rw [if_pos hi, map_smul, if_pos hfree]
      by_cases hy : 1 ≤ y.val
      · rw [deletion_totalDb_isolated H hH hG a ha φ hφ y hy hfree]
      · rw [isolated_f_zero_at_zero_last H hH a ha f hf φ y hy, zero_smul, zero_smul]
    · have hi : ¬ Function.Injective (Fin.snoc φ y : Fin (H.k+1) → Label n) := by
        intro hi
        have hh := (injective_last_iff _).mp hi |>.2
        exact hfree (by simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hh)
      rw [if_neg hi, map_zero, if_neg hfree]
  · rw [if_neg hφ]
    apply Finset.sum_eq_zero
    intro y hy
    have hi : ¬ Function.Injective (Fin.snoc φ y : Fin (H.k+1) → Label n) := by
      intro hi
      have hh := (injective_last_iff _).mp hi |>.1
      exact hφ (by simpa only [Fin.snoc_castSucc] using hh)
    rw [if_neg hi, map_zero]

theorem deletion_mem_encoding_range_isolated (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (B : Finset ℕ) (v : Hil (Db l G))
    (hv : v ∈ fixedForestGoodSpace l G (addIsolated H a) B) :
    deletion a v ∈ LinearMap.range (fullEncoding (l := l) H hH hG) := by
  rw [← fullEncoding_map_coefficientSpace _ (addIsolated_valid H hH a ha) hG B] at hv
  obtain ⟨f, hf, rfl⟩ := hv
  exact ⟨freeSumLast H.k f,
    (deletion_fullEncoding_isolated H hH hG a ha f
      (coefficient_zero_of_muRef_zero _ (addIsolated_valid H hH a ha) B f hf)).symm⟩

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathIsolatedAutomorphisms
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}

noncomputable def extendLast {k : ℕ} (e : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k+1)) :=
  finSuccEquivLast.trans ((Equiv.optionCongr e).trans finSuccEquivLast.symm)

@[simp] lemma extendLast_old {k : ℕ} (e : Equiv.Perm (Fin k)) (u : Fin k) :
    extendLast e u.castSucc = (e u).castSucc := by simp [extendLast]

@[simp] lemma extendLast_last {k : ℕ} (e : Equiv.Perm (Fin k)) :
    extendLast e (Fin.last k) = Fin.last k := by simp [extendLast]

noncomputable def restrictLast {k : ℕ} (e : Equiv.Perm (Fin (k+1)))
    (he : e (Fin.last k) = Fin.last k) : Equiv.Perm (Fin k) :=
  (oldVertexEquiv k).symm.trans ((e.subtypeEquiv (fun u => by
    constructor
    · intro hu heu
      exact hu (e.injective (heu.trans he.symm))
    · intro heu hu
      exact heu (hu ▸ he))).trans (oldVertexEquiv k))

lemma restrictLast_old {k : ℕ} (e : Equiv.Perm (Fin (k+1)))
    (he : e (Fin.last k) = Fin.last k) (u : Fin k) :
    (restrictLast e he u).castSucc = e u.castSucc := by
  have hu : e u.castSucc ≠ Fin.last k := by
    intro h
    exact Fin.castSucc_ne_last u (e.injective (h.trans he.symm))
  change ((e u.castSucc).castPred hu).castSucc = e u.castSucc
  exact Fin.castSucc_castPred _ hu

lemma addIsolated_coloredAdj_old (H : AbsForest n) (a : Fin (labelBound n))
    (u v : Fin H.k) (α : Fin 3) :
    ColoredAdj (addIsolated H a) u.castSucc v.castSucc α ↔ ColoredAdj H u v α := by
  constructor
  · rintro ⟨p,hp,he,hc⟩
    obtain ⟨⟨w,z⟩,hpOld,rfl⟩ := addIsolated_edge_old H a p hp
    refine ⟨(w,z),hpOld,?_,?_⟩
    · simpa only [liftEdge,Prod.mk.injEq,Fin.castSucc_inj] using he
    · simpa only [liftEdge,Fin.lastCases_castSucc] using hc
  · rintro ⟨p,hp,he,hc⟩
    refine ⟨liftEdge p,(addIsolated_edge H a p).mpr hp,?_,?_⟩
    · rcases he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · simpa only [liftEdge,Fin.lastCases_castSucc] using hc

lemma addIsolated_not_coloredAdj_last (H : AbsForest n) (a : Fin (labelBound n))
    (u : Fin (H.k+1)) (α : Fin 3) :
    ¬ ColoredAdj (addIsolated H a) (Fin.last H.k) u α := by
  rintro ⟨p,hp,he,_⟩
  rcases he with rfl | rfl
  · exact (addIsolated_no_edge_last H a _ hp).1 rfl
  · exact (addIsolated_no_edge_last H a _ hp).2 rfl

lemma addIsolated_not_coloredAdj_last_right (H : AbsForest n) (a : Fin (labelBound n))
    (u : Fin (H.k+1)) (α : Fin 3) :
    ¬ ColoredAdj (addIsolated H a) u (Fin.last H.k) α := by
  rintro ⟨p,hp,he,hc⟩
  exact addIsolated_not_coloredAdj_last H a u α ⟨p,hp,he.symm,hc⟩

lemma extendLast_isForestIso (H : AbsForest n) (a : Fin (labelBound n)) (e : ForestAut H) :
    IsForestIso (addIsolated H a) (addIsolated H a) (extendLast e.1) := by
  constructor
  · intro u
    induction u using Fin.lastCases with
    | last => rw [extendLast_last]
    | cast u =>
      rw [extendLast_old,addIsolated_lab_old,addIsolated_lab_old]
      exact e.2.1 u
  · intro u v α
    induction u using Fin.lastCases with
    | last =>
      rw [extendLast_last]
      exact iff_of_false (addIsolated_not_coloredAdj_last H a v α)
        (addIsolated_not_coloredAdj_last H a _ α)
    | cast u =>
      induction v using Fin.lastCases with
      | last =>
        rw [extendLast_last]
        exact iff_of_false (addIsolated_not_coloredAdj_last_right H a _ α)
          (addIsolated_not_coloredAdj_last_right H a _ α)
      | cast v =>
        rw [extendLast_old,extendLast_old,addIsolated_coloredAdj_old,addIsolated_coloredAdj_old]
        exact e.2.2 u v α

lemma addIsolated_aut_fixes_last (H : AbsForest n) (a : Fin (labelBound n))
    (ha : ∀ u,H.lab u ≠ some a) (e : ForestAut (addIsolated H a)) :
    e.1 (Fin.last H.k) = Fin.last H.k := by
  by_contra he
  let u := (e.1 (Fin.last H.k)).castPred he
  have hu : u.castSucc = e.1 (Fin.last H.k) := Fin.castSucc_castPred _ _
  apply ha u
  rw [← addIsolated_lab_old H a u,hu,e.2.1,addIsolated_lab_last]

lemma restrictLast_isForestIso (H : AbsForest n) (a : Fin (labelBound n))
    (e : ForestAut (addIsolated H a)) (he : e.1 (Fin.last H.k) = Fin.last H.k) :
    IsForestIso H H (restrictLast e.1 he) := by
  constructor
  · intro u
    have h := e.2.1 u.castSucc
    rw [← restrictLast_old e.1 he u,addIsolated_lab_old,addIsolated_lab_old] at h
    exact h
  · intro u v α
    calc
      ColoredAdj H u v α ↔ ColoredAdj (addIsolated H a) u.castSucc v.castSucc α :=
        (addIsolated_coloredAdj_old H a u v α).symm
      _ ↔ ColoredAdj (addIsolated H a) (e.1 u.castSucc) (e.1 v.castSucc) α :=
        e.2.2 u.castSucc v.castSucc α
      _ ↔ ColoredAdj H (restrictLast e.1 he u) (restrictLast e.1 he v) α := by
        rw [← restrictLast_old e.1 he u,← restrictLast_old e.1 he v,addIsolated_coloredAdj_old]

noncomputable def addIsolated_autEquiv (H : AbsForest n) (a : Fin (labelBound n))
    (ha : ∀ u,H.lab u ≠ some a) : ForestAut H ≃ ForestAut (addIsolated H a) where
  toFun e := ⟨extendLast e.1,extendLast_isForestIso H a e⟩
  invFun e := ⟨restrictLast e.1 (addIsolated_aut_fixes_last H a ha e),
    restrictLast_isForestIso H a e _⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro u
    apply Fin.castSucc_injective
    rw [restrictLast_old,extendLast_old]
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro u
    induction u using Fin.lastCases with
    | last =>
      rw [extendLast_last,addIsolated_aut_fixes_last H a ha e]
    | cast u => rw [extendLast_old,restrictLast_old]

theorem addIsolated_aut_card (H : AbsForest n) (a : Fin (labelBound n))
    (ha : ∀ u,H.lab u ≠ some a) :
    Fintype.card (ForestAut (addIsolated H a)) = Fintype.card (ForestAut H) :=
  (Fintype.card_congr (addIsolated_autEquiv H a ha)).symm

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathDeleteIsolated
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}

def IsIsolated (H : AbsForest n) (y : Fin H.k) : Prop :=
  ∀ p ∈ H.E, p.1 ≠ y ∧ p.2 ≠ y

noncomputable def remainingVertexEquiv (H : AbsForest n) (y : Fin H.k) :
    Fin ((Finset.univ.erase y).card) ≃o (Finset.univ.erase y : Finset (Fin H.k)) :=
  (Finset.univ.erase y).orderIsoOfFin rfl

noncomputable def remainingVertex (H : AbsForest n) (y : Fin H.k)
    (u : Fin ((Finset.univ.erase y).card)) : Fin H.k := (remainingVertexEquiv H y u).val

lemma remainingVertex_ne (H : AbsForest n) (y : Fin H.k)
    (u : Fin ((Finset.univ.erase y).card)) : remainingVertex H y u ≠ y :=
  (Finset.mem_erase.mp (remainingVertexEquiv H y u).property).1

lemma remainingVertex_injective (H : AbsForest n) (y : Fin H.k) :
    Function.Injective (remainingVertex H y) := by
  intro u v huv
  exact (remainingVertexEquiv H y).injective (Subtype.ext huv)

lemma remainingVertex_surjective (H : AbsForest n) (y u : Fin H.k) (huy : u ≠ y) :
    ∃ v, remainingVertex H y v = u := by
  refine ⟨(remainingVertexEquiv H y).symm ⟨u, Finset.mem_erase.mpr ⟨huy, Finset.mem_univ _⟩⟩, ?_⟩
  exact congrArg Subtype.val ((remainingVertexEquiv H y).apply_symm_apply _)

noncomputable def remainingEdge (H : AbsForest n) (y : Fin H.k)
    (p : Fin ((Finset.univ.erase y).card) × Fin ((Finset.univ.erase y).card)) :
    Fin H.k × Fin H.k := (remainingVertex H y p.1, remainingVertex H y p.2)

lemma remainingEdge_injective (H : AbsForest n) (y : Fin H.k) :
    Function.Injective (remainingEdge H y) := by
  intro p q hpq
  exact Prod.ext (remainingVertex_injective H y (congrArg Prod.fst hpq))
    (remainingVertex_injective H y (congrArg Prod.snd hpq))

noncomputable abbrev deleteIsolated (H : AbsForest n) (y : Fin H.k) : AbsForest n where
  k := (Finset.univ.erase y).card
  E := Finset.univ.filter (fun p => remainingEdge H y p ∈ H.E)
  color p := H.color (remainingEdge H y p)
  lab u := H.lab (remainingVertex H y u)

lemma deleteIsolated_vertices (H : AbsForest n) (y : Fin H.k) :
    (deleteIsolated H y).k + 1 = H.k := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_erase_add_one (Finset.mem_univ y)

lemma deleteIsolated_edge (H : AbsForest n) (y : Fin H.k)
    (p : Fin (deleteIsolated H y).k × Fin (deleteIsolated H y).k) :
    p ∈ (deleteIsolated H y).E ↔ remainingEdge H y p ∈ H.E := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

lemma deleteIsolated_edge_surj (H : AbsForest n) (y : Fin H.k) (hy : IsIsolated H y)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E) :
    ∃ q ∈ (deleteIsolated H y).E, remainingEdge H y q = p := by
  obtain ⟨u, hu⟩ := remainingVertex_surjective H y p.1 (hy p hp).1
  obtain ⟨v, hv⟩ := remainingVertex_surjective H y p.2 (hy p hp).2
  have he : remainingEdge H y (u,v) = p := Prod.ext hu hv
  exact ⟨(u,v), (deleteIsolated_edge H y _).mpr (he.symm ▸ hp), he⟩

noncomputable def deleteIsolated_graphEmbedding (H : AbsForest n) (y : Fin H.k) :
    (deleteIsolated H y).graph ↪g H.graph where
  toFun := remainingVertex H y
  inj' := remainingVertex_injective H y
  map_rel_iff' := by
    intro u v
    change (remainingVertex H y u ≠ remainingVertex H y v ∧
      (remainingEdge H y (u,v) ∈ H.E ∨ remainingEdge H y (v,u) ∈ H.E)) ↔
      (u ≠ v ∧ ((u,v) ∈ (deleteIsolated H y).E ∨ (v,u) ∈ (deleteIsolated H y).E))
    rw [ne_eq, (remainingVertex_injective H y).eq_iff, ← ne_eq]
    exact and_congr_right fun _ => or_congr (deleteIsolated_edge H y (u,v)).symm
      (deleteIsolated_edge H y (v,u)).symm

theorem deleteIsolated_valid (H : AbsForest n) (hH : H.IsValid)
    (y : Fin H.k) (hy : IsIsolated H y) : (deleteIsolated H y).IsValid := by
  refine ⟨?_, hH.2.1.embedding (deleteIsolated_graphEmbedding H y), ?_, ?_, ?_⟩
  · intro p hp
    exact (remainingVertexEquiv H y).lt_iff_lt.mp (hH.1 _ ((deleteIsolated_edge H y p).mp hp))
  · intro p hp q hq hpq hshare
    apply hH.2.2.1 (remainingEdge H y p) ((deleteIsolated_edge H y p).mp hp)
      (remainingEdge H y q) ((deleteIsolated_edge H y q).mp hq)
      (fun he => hpq (remainingEdge_injective H y he))
    exact hshare.imp (congrArg (remainingVertex H y))
      (fun h => h.imp (congrArg (remainingVertex H y))
        (fun h => h.imp (congrArg (remainingVertex H y)) (congrArg (remainingVertex H y))))
  · intro u v j hu hv
    exact remainingVertex_injective H y (hH.2.2.2.1 _ _ j hu hv)
  · intro u
    rcases hH.2.2.2.2 (remainingVertex H y u) with hu | ⟨p,hp,hpu⟩
    · exact Or.inl hu
    · obtain ⟨q,hq,he⟩ := deleteIsolated_edge_surj H y hy p hp
      refine Or.inr ⟨q,hq,?_⟩
      rw [← he] at hpu
      rcases hpu with h | h
      · exact Or.inl (remainingVertex_injective H y h)
      · exact Or.inr (remainingVertex_injective H y h)

noncomputable def restoreVertex (H : AbsForest n) (y : Fin H.k) :
    Fin ((deleteIsolated H y).k + 1) → Fin H.k := Fin.snoc (remainingVertex H y) y

@[simp] lemma restoreVertex_old (H : AbsForest n) (y : Fin H.k) (u : Fin (deleteIsolated H y).k) :
    restoreVertex H y u.castSucc = remainingVertex H y u := by
  simp only [restoreVertex, Fin.snoc_castSucc]

@[simp] lemma restoreVertex_last (H : AbsForest n) (y : Fin H.k) :
    restoreVertex H y (Fin.last (deleteIsolated H y).k) = y := by
  simp only [restoreVertex, Fin.snoc_last]

lemma restoreVertex_bijective (H : AbsForest n) (y : Fin H.k) :
    Function.Bijective (restoreVertex H y) := by
  constructor
  · intro u v huv
    induction u using Fin.lastCases with
    | last =>
      induction v using Fin.lastCases with
      | last => rfl
      | cast v => exact (remainingVertex_ne H y v
          (by simpa only [restoreVertex, Fin.snoc_last, Fin.snoc_castSucc] using huv.symm)).elim
    | cast u =>
      induction v using Fin.lastCases with
      | last => exact (remainingVertex_ne H y u
          (by simpa only [restoreVertex, Fin.snoc_last, Fin.snoc_castSucc] using huv)).elim
      | cast v =>
        exact congrArg Fin.castSucc (remainingVertex_injective H y (by simpa using huv))
  · intro u
    by_cases hu : u = y
    · exact ⟨Fin.last _, (restoreVertex_last H y).trans hu.symm⟩
    · obtain ⟨v,hv⟩ := remainingVertex_surjective H y u hu
      exact ⟨v.castSucc, (restoreVertex_old H y v).trans hv⟩

noncomputable def restoreEquiv (H : AbsForest n) (y : Fin H.k) :
    Fin ((deleteIsolated H y).k + 1) ≃ Fin H.k :=
  Equiv.ofBijective (restoreVertex H y) (restoreVertex_bijective H y)

lemma deleted_label_fresh (H : AbsForest n) (hH : H.IsValid) (y : Fin H.k)
    (a : Fin (labelBound n)) (hya : H.lab y = some a) :
    ∀ u, (deleteIsolated H y).lab u ≠ some a := by
  intro u hu
  exact remainingVertex_ne H y u (hH.2.2.2.1 _ y a hu hya)

@[simp] lemma restoreEquiv_old (H : AbsForest n) (y : Fin H.k)
    (u : Fin (deleteIsolated H y).k) :
    restoreEquiv H y u.castSucc = remainingVertex H y u := restoreVertex_old H y u

@[simp] lemma restoreEquiv_last (H : AbsForest n) (y : Fin H.k) :
    restoreEquiv H y (Fin.last (deleteIsolated H y).k) = y := restoreVertex_last H y

theorem restore_isForestIso (H : AbsForest n) (y : Fin H.k) (hy : IsIsolated H y)
    (a : Fin (labelBound n)) (hya : H.lab y = some a) :
    IsForestIso (addIsolated (deleteIsolated H y) a) H (restoreEquiv H y) := by
  constructor
  · intro u
    induction u using Fin.lastCases with
    | last => rw [restoreEquiv_last, addIsolated_lab_last]; exact hya
    | cast u => rw [restoreEquiv_old, addIsolated_lab_old]
  · intro u v α
    constructor
    · rintro ⟨p,hp,hp',hc⟩
      obtain ⟨q,hq,rfl⟩ := addIsolated_edge_old (deleteIsolated H y) a p hp
      refine ⟨remainingEdge H y q, (deleteIsolated_edge H y q).mp hq, ?_, ?_⟩
      · rcases hp' with hp' | hp'
        · apply Or.inl
          have h := congrArg (fun p => (restoreEquiv H y p.1, restoreEquiv H y p.2)) hp'
          simpa only [liftEdge, restoreEquiv_old, remainingEdge] using h
        · apply Or.inr
          have h := congrArg (fun p => (restoreEquiv H y p.1, restoreEquiv H y p.2)) hp'
          simpa only [liftEdge, restoreEquiv_old, remainingEdge] using h
      · exact (addIsolated_color (deleteIsolated H y) a q).symm.trans hc
    · rintro ⟨p,hp,hp',hc⟩
      obtain ⟨q,hq,he⟩ := deleteIsolated_edge_surj H y hy p hp
      refine ⟨liftEdge q, (addIsolated_edge (deleteIsolated H y) a q).mpr hq, ?_, ?_⟩
      · have hm : (restoreEquiv H y (liftEdge q).1, restoreEquiv H y (liftEdge q).2) = p := by
          simpa only [liftEdge, restoreEquiv_old, remainingEdge] using he
        rcases hp' with hp' | hp'
        · exact Or.inl (Prod.ext ((restoreEquiv H y).injective (congrArg Prod.fst (hm.trans hp')))
            ((restoreEquiv H y).injective (congrArg Prod.snd (hm.trans hp'))))
        · exact Or.inr (Prod.ext ((restoreEquiv H y).injective (congrArg Prod.fst (hm.trans hp')))
            ((restoreEquiv H y).injective (congrArg Prod.snd (hm.trans hp'))))
      · rw [addIsolated_color]
        exact (congrArg H.color he).trans hc

theorem records_isForestIso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) : H.records = K.records := by
  have he : H.E.card = K.E.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (edgeEquiv H K hH hK e hiso)
  have hl : (Finset.univ.filter (fun u => (H.lab u).isSome)).card =
      (Finset.univ.filter (fun u => (K.lab u).isSome)).card := by
    apply Finset.card_bij (fun u _ => e u)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rw [hiso.1]; exact (Finset.mem_filter.mp hu).2⟩
    · intro u hu v hv huv; exact e.injective huv
    · intro v hv
      refine ⟨e.symm v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply v⟩
      rw [← hiso.1, Equiv.apply_symm_apply]
      exact (Finset.mem_filter.mp hv).2
  exact congrArg₂ (· + ·) he hl

theorem deleteIsolated_records (H : AbsForest n) (hH : H.IsValid)
    (y : Fin H.k) (hy : IsIsolated H y) (a : Fin (labelBound n)) (hya : H.lab y = some a) :
    (deleteIsolated H y).records + 1 = H.records := by
  have hK := deleteIsolated_valid H hH y hy
  have ha := deleted_label_fresh H hH y a hya
  have he := records_isForestIso (addIsolated (deleteIsolated H y) a) H
    (addIsolated_valid _ hK a ha) hH (restoreEquiv H y) (restore_isForestIso H y hy a hya)
  simpa only [addIsolated_records] using he

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathForestIsomorphismMeasure
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical ForestFactorization FiniteWeightedForest

variable {n l : ℕ} {G : WeldedInstance n}

lemma mem_comp_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) (s u : Fin H.k) :
    e u ∈ K.comp (e s) ↔ u ∈ H.comp s := by
  rw [← comp_image_iso H K hH hK e hiso]
  exact Finset.mem_image.trans ⟨fun ⟨v, hv, he⟩ => e.injective he ▸ hv,
    fun hu => ⟨u, hu, rfl⟩⟩

lemma component_edge_mem_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) (s : Fin H.k)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E) :
    mapEdge e p ∈ componentEdges K (e s) ↔ p ∈ componentEdges H s := by
  have hr : H.graph.Reachable p.1 p.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 p hp), Or.inl hp⟩
  have hc : p.2 ∈ H.comp s ↔ p.1 ∈ H.comp s := by
    simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans hr.symm, fun h => h.trans hr⟩
  simp only [componentEdges, Finset.mem_filter, hp, mapEdge_mem H K hK e hiso p hp,
    true_and]
  unfold mapEdge
  split_ifs <;> simp only [mem_comp_iso H K hH hK e hiso, hc]

noncomputable def componentEdgeEquiv (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) (s : Fin H.k) :
    ↥(componentEdges H s) ≃ ↥(componentEdges K (e s)) where
  toFun p := ⟨mapEdge e p.1, (component_edge_mem_iso H K hH hK e hiso s p.1
    (Finset.mem_filter.mp p.2).1).mpr p.2⟩
  invFun q := ⟨mapEdge e.symm q.1, by
    have h := (component_edge_mem_iso K H hK hH e.symm (hiso.symm H K e) (e s)
      q.1 (Finset.mem_filter.mp q.2).1).mpr q.2
    simpa only [Equiv.symm_apply_apply] using h⟩
  left_inv p := Subtype.ext (mapEdge_symm_apply e p.1 (hH.1 _ (Finset.mem_filter.mp p.2).1))
  right_inv q := Subtype.ext
    (mapEdge_symm_apply e.symm q.1 (hK.1 _ (Finset.mem_filter.mp q.2).1))

lemma component_edgeWeight_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e) (s : Fin H.k)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    edgeWeight (componentEdges H s) (componentKernel l G H) φ =
      edgeWeight (componentEdges K (e s)) (componentKernel l G K) ψ := by
  unfold edgeWeight
  rw [← Finset.prod_coe_sort (componentEdges H s),
    ← Finset.prod_coe_sort (componentEdges K (e s))]
  apply Fintype.prod_equiv (componentEdgeEquiv H K hH hK e hiso s)
  intro p
  change kappa l G (H.color p.1) (φ p.1.1).1 (φ p.1.2).1 =
    kappa l G (K.color (mapEdge e p.1)) (ψ (mapEdge e p.1).1).1 (ψ (mapEdge e p.1).2).1
  rw [mapEdge_color H K hK e hiso p.1 (Finset.mem_filter.mp p.2).1]
  unfold mapEdge
  split_ifs
  · simp only [he]
  · simp only [he]
    exact KappaKernel.kappa_symm hG _ _ _

lemma component_support_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) (s : Fin H.k)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u)
    (V : Finset ℕ) :
    (∀ u ∈ H.comp s, (φ u).val ∈ V) ↔ ∀ v ∈ K.comp (e s), (ψ v).val ∈ V := by
  constructor
  · intro h v hv
    have hm : e.symm v ∈ H.comp s :=
      (mem_comp_iso H K hH hK e hiso s _).mp (by simpa using hv)
    simpa only [← he, Equiv.apply_symm_apply] using h _ hm
  · intro h u hu
    simpa only [he] using h (e u) ((mem_comp_iso H K hH hK e hiso s u).mpr hu)

lemma component_zero_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) (s : Fin H.k)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    (∀ u, u ∉ H.comp s → φ u = 0) ↔ ∀ v, v ∉ K.comp (e s) → ψ v = 0 := by
  constructor
  · intro h v hv
    have hm : e.symm v ∉ H.comp s := by
      intro hm
      exact hv (by simpa using (mem_comp_iso H K hH hK e hiso s _).mpr hm)
    simpa only [← he, Equiv.apply_symm_apply] using h _ hm
  · intro h u hu
    simpa only [he] using h (e u) (fun hm => hu ((mem_comp_iso H K hH hK e hiso s u).mp hm))

noncomputable def forestAssignmentEquiv (H K : AbsForest n) (e : Fin H.k ≃ Fin K.k) :
    (Fin H.k → Label n) ≃ (Fin K.k → Label n) where
  toFun φ := fun v => φ (e.symm v)
  invFun ψ := fun u => ψ (e u)
  left_inv φ := by funext u; simp
  right_inv ψ := by funext v; simp

lemma componentScale_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e) (s : Fin H.k) :
    componentScale l G H s = componentScale l G K (e s) := by
  unfold componentScale
  dsimp only
  apply congrArg (fun z : ℝ => (1 / ((1 / ((Vmid n l ∪ Vbd n l).card : ℝ)) * z)) *
    (1 / ((Vmid n l ∪ Vbd n l).card : ℝ)))
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (forestAssignmentEquiv H K e)
  intro φ
  have he : ∀ u, forestAssignmentEquiv H K e φ (e u) = φ u := by
    intro u; simp [forestAssignmentEquiv]
  have hc := component_support_iso H K hH hK e hiso s φ _ he (Vmid n l ∪ Vbd n l)
  have hz := component_zero_iso H K hH hK e hiso s φ _ he
  by_cases h : (∀ u ∈ H.comp s, (φ u).val ∈ Vmid n l ∪ Vbd n l) ∧
      (∀ u, u ∉ H.comp s → φ u = 0)
  · rw [if_pos h, if_pos ⟨hc.mp h.1, hz.mp h.2⟩]
    exact component_edgeWeight_iso hG H K hH hK e hiso s φ _ he
  · rw [if_neg h, if_neg (fun hh => h ⟨hc.mpr hh.1, hz.mpr hh.2⟩)]

theorem muComp_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e) (s : Fin H.k)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    H.muComp l G s φ = K.muComp l G (e s) ψ := by
  have hcard : (H.comp s).card = (K.comp (e s)).card := by
    rw [← comp_image_iso H K hH hK e hiso s, Finset.card_image_of_injective _ e.injective]
  rw [muComp_eq_componentCondition l G H hH, muComp_eq_componentCondition l G K hK]
  rw [← hcard, ← componentScale_iso hG H K hH hK e hiso s,
    ← component_edgeWeight_iso hG H K hH hK e hiso s φ ψ he]
  congr 1
  have hc : componentCondition l H s φ ↔ componentCondition l K (e s) ψ := by
    unfold componentCondition
    rw [← hcard, he]
    split_ifs
    · rfl
    · exact component_support_iso H K hH hK e hiso s φ ψ he _
  simp only [hc]

lemma muComp_eq_of_reachable (H : AbsForest n) (s t : Fin H.k)
    (hst : H.graph.Reachable s t) (φ : Fin H.k → Label n) :
    H.muComp l G s φ = H.muComp l G t φ := by
  have hc := comp_eq_of_reachable H s t hst
  by_cases h : (H.comp s).card = 1
  · have hs : s ∈ H.comp s := by simp [AbsForest.comp]
    have ht : t ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hst⟩
    have he := (Finset.card_le_one.mp h.le) s hs t ht
    subst t
    rfl
  · simp only [AbsForest.muComp, ← hc, h, ite_false]

noncomputable def rootEquiv (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e) :
    {s // H.IsCompRoot s} ≃ {t // K.IsCompRoot t} where
  toFun s := ⟨compRoot K (e s.1), compRoot_isRoot K _⟩
  invFun t := ⟨compRoot H (e.symm t.1), compRoot_isRoot H _⟩
  left_inv s := by
    apply Subtype.ext
    apply (mem_comp_iff_root_eq H s.1 _ s.2).mp
    apply (mem_comp_iso H K hH hK e hiso s.1 _).mp
    simp only [Equiv.apply_symm_apply]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (compRoot_reachable K (e s.1)).symm⟩
  right_inv t := by
    apply Subtype.ext
    apply (mem_comp_iff_root_eq K t.1 _ t.2).mp
    have hr := (compRoot_reachable H (e.symm t.1)).symm
    have hr' := (graphIso H K hH hK e hiso).reachable_iff.mpr hr
    change K.graph.Reachable (e (e.symm t.1)) (e (compRoot H (e.symm t.1))) at hr'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [Equiv.apply_symm_apply] using hr'⟩

theorem muRef_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    H.muRef l G φ = K.muRef l G ψ := by
  unfold AbsForest.muRef
  rw [Finset.prod_subtype (p := H.IsCompRoot) (Finset.univ.filter H.IsCompRoot)
    (fun s => by simp),
    Finset.prod_subtype (p := K.IsCompRoot) (Finset.univ.filter K.IsCompRoot)
      (fun s => by simp)]
  apply Fintype.prod_equiv (rootEquiv H K hH hK e hiso)
  intro s
  change H.muComp l G s.1 φ = K.muComp l G (compRoot K (e s.1)) ψ
  rw [muComp_iso hG H K hH hK e hiso s.1 φ ψ he]
  exact muComp_eq_of_reachable K _ _ (compRoot_reachable K (e s.1)).symm ψ

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.FiniteOrthogonalSectors
section

namespace FiniteOrthogonalSectors

open Classical
open scoped BigOperators

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

/-- The distinct nonzero spaces in a possibly infinite presentation. -/
abbrev Sector (S : ι → Submodule ℂ E) :=
  {P : Submodule ℂ E // P ≠ ⊥ ∧ ∃ i, S i = P}

noncomputable def representative (S : ι → Submodule ℂ E) (P : Sector S) : ι :=
  P.2.2.choose

lemma representative_space (S : ι → Submodule ℂ E) (P : Sector S) :
    S (representative S P) = P.1 := P.2.2.choose_spec

lemma orthogonal (S : ι → Submodule ℂ E)
    (hS : ∀ i j, S i = S j ∨ ∀ x ∈ S i, ∀ y ∈ S j, inner ℂ x y = 0) :
    OrthogonalFamily ℂ (fun P : Sector S => P.1) (fun P => P.1.subtypeₗᵢ) := by
  intro P Q hPQ x y
  obtain h | h := hS (representative S P) (representative S Q)
  · exact False.elim (hPQ (Subtype.ext (by simpa only [representative_space] using h)))
  · apply h x.1 _ y.1 _
    · simpa only [representative_space] using x.2
    · simpa only [representative_space] using y.2

theorem finite (S : ι → Submodule ℂ E)
    (hS : ∀ i j, S i = S j ∨ ∀ x ∈ S i, ∀ y ∈ S j, inner ℂ x y = 0) :
    Finite (Sector S) := by
  exact WellFoundedGT.finite_of_iSupIndep (orthogonal S hS).independent (fun P => P.2.1)

lemma iSup_eq (S : ι → Submodule ℂ E) : (⨆ P : Sector S, P.1) = ⨆ i, S i := by
  apply le_antisymm
  · apply iSup_le
    intro P
    rw [← representative_space S P]
    exact le_iSup S _
  · apply iSup_le
    intro i
    by_cases hi : S i = ⊥
    · simp only [hi, bot_le]
    · exact le_iSup (fun P : Sector S => P.1) ⟨S i, hi, i, rfl⟩

/-- Every vector in the full span is the sum of its finitely many orthogonal
sector components, with exact Pythagoras. The index type identifies equal
spaces, so a repeated presentation cannot introduce duplicate components. -/
theorem decomposition (S : ι → Submodule ℂ E)
    (hS : ∀ i j, S i = S j ∨ ∀ x ∈ S i, ∀ y ∈ S j, inner ℂ x y = 0)
    (x : E) (hx : x ∈ ⨆ i, S i) :
    letI : Finite (Sector S) := finite S hS
    letI : Fintype (Sector S) := Fintype.ofFinite _
    ∃ v : Sector S → E,
      (∀ P, v P ∈ S (representative S P)) ∧
      (∑ P, v P) = x ∧ (∑ P, ‖v P‖ ^ 2) = ‖x‖ ^ 2 := by
  letI : Finite (Sector S) := finite S hS
  letI : Fintype (Sector S) := Fintype.ofFinite _
  let v : Sector S → E := fun P => P.1.starProjection x
  have hv : ∀ P : Sector S, v P ∈ P.1 :=
    fun P => (P.1.orthogonalProjectionOnto x).property
  have hsum : (∑ P, v P) = x := by
    exact (orthogonal S hS).sum_projection_of_mem_iSup x ((iSup_eq S).symm ▸ hx)
  refine ⟨v, ?_, hsum, ?_⟩
  · intro P
    simpa only [representative_space] using hv P
  · have hh := (orthogonal S hS).norm_sum (fun P => ⟨v P, hv P⟩) Finset.univ
    change ‖∑ P, v P‖ ^ 2 = ∑ P, ‖v P‖ ^ 2 at hh
    rw [hsum] at hh
    exact hh.symm

end FiniteOrthogonalSectors

end

-- Solutions.WeldedPathGoodSpaceIsomorphism
section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable abbrev transportDescription (H K : AbsForest n) (e : Fin H.k ≃ Fin K.k)
    (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) : Description n :=
  ⟨K, sel.image e, fun u => φ₀ (e.symm u)⟩

lemma transportDescription_valid (H K : AbsForest n) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) :
    (transportDescription H K e sel φ₀).IsValid := by
  refine ⟨hK, ?_⟩
  intro u
  obtain ⟨s, hs, hunique⟩ := hD.2 (e.symm u)
  refine ⟨e s, ⟨Finset.mem_image.mpr ⟨s, hs.1, rfl⟩, ?_⟩, ?_⟩
  · have h := (graphIso H K hD.1 hK e hiso).reachable_iff.mpr hs.2
    change K.graph.Reachable (e (e.symm u)) (e s) at h
    simpa only [Equiv.apply_symm_apply] using h
  · intro t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht.1
    apply congrArg e
    apply hunique v
    refine ⟨hv, ?_⟩
    apply (graphIso H K hD.1 hK e hiso).reachable_iff.mp
    change K.graph.Reachable (e (e.symm u)) (e v)
    simpa only [Equiv.apply_symm_apply] using ht.2

lemma description_conditions_iso (H K : AbsForest n) (hH : H.IsValid) (hK : K.IsValid)
    (e : Fin H.k ≃ Fin K.k) (hiso : IsForestIso H K e)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ φ : Fin H.k → Label n)
    (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    ((∀ s ∈ sel.image e, K.Wfix ψ s = K.Wfix (fun u => φ₀ (e.symm u)) s) ∧
      (∀ s ∈ sel.image e, ∀ u, K.graph.Reachable s u →
        u ∉ K.Ctree ψ s → (ψ u).val ∉ B)) ↔
    ((∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
      (∀ s ∈ sel, ∀ u, H.graph.Reachable s u →
        u ∉ H.Ctree φ s → (φ u).val ∉ B)) := by
  have he₀ : ∀ u, (fun v => φ₀ (e.symm v)) (e u) = φ₀ u := by simp
  constructor
  · rintro ⟨hw, hB⟩
    constructor
    · intro s hs
      exact (wfix_fiber_iso H K hH hK e hiso φ φ₀ ψ _ he he₀ s).mp
        (hw (e s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩))
    · intro s hs u hr hc
      have h := hB (e s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩) (e u)
        ((graphIso H K hH hK e hiso).reachable_iff.mpr hr)
        (fun hu => hc ((ctree_mem_iso H K hH hK e hiso φ ψ he u s).mp hu))
      simpa only [he] using h
  · rintro ⟨hw, hB⟩
    constructor
    · intro s hs
      obtain ⟨s, hsel, rfl⟩ := Finset.mem_image.mp hs
      exact (wfix_fiber_iso H K hH hK e hiso φ φ₀ ψ _ he he₀ s).mpr (hw s hsel)
    · intro s hs u hr hc
      obtain ⟨s, hsel, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨u, rfl⟩ := e.surjective u
      rw [he]
      exact hB s hsel u ((graphIso H K hH hK e hiso).reachable_iff.mp hr)
        (fun hu => hc ((ctree_mem_iso H K hH hK e hiso φ ψ he u s).mpr hu))

lemma injective_assignment_iso (H K : AbsForest n) (e : Fin H.k ≃ Fin K.k)
    (φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    Function.Injective φ ↔ Function.Injective ψ := by
  constructor
  · intro h x y hxy
    apply e.symm.injective
    apply h
    simpa only [← he, Equiv.apply_symm_apply] using hxy
  · intro h u v huv
    apply e.injective
    apply h
    simpa only [he] using huv

theorem isGood_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e) (B : Finset ℕ) (sel : Finset (Fin H.k))
    (φ₀ φ : Fin H.k → Label n) (ψ : Fin K.k → Label n) (he : ∀ u, ψ (e u) = φ u) :
    (transportDescription H K e sel φ₀).IsGood l G B ψ ↔
      (Description.mk H sel φ₀).IsGood l G B φ := by
  unfold Description.IsGood transportDescription
  change (0 < K.muRef l G ψ ∧ _ ∧ _ ∧ _) ↔ (0 < H.muRef l G φ ∧ _ ∧ _ ∧ _)
  rw [← muRef_iso hG H K hH hK e hiso φ ψ he]
  have hc := description_conditions_iso H K hH hK e hiso B sel φ₀ φ ψ he
  have hi := injective_assignment_iso H K e φ ψ he
  tauto

theorem gVec_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e) (B : Finset ℕ) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) :
    (Description.mk H sel φ₀).gVec l G B =
      (transportDescription H K e sel φ₀).gVec l G B := by
  unfold Description.gVec
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (forestAssignmentEquiv H K e)
  intro φ
  let ψ := forestAssignmentEquiv H K e φ
  have he : ∀ u, ψ (e u) = φ u := by intro u; simp [ψ, forestAssignmentEquiv]
  have hg := isGood_iso (l := l) hG H K hH hK e hiso B sel φ₀ φ ψ he
  change (if (Description.mk H sel φ₀).IsGood l G B φ then _ else _) =
    (if (transportDescription H K e sel φ₀).IsGood l G B ψ then _ else _)
  rw [hg]
  split_ifs
  · rw [muRef_iso hG H K hH hK e hiso φ ψ he]
    congr 1
    apply Finset.sum_congr rfl
    intro I _
    have hdb : H.IsDbOf l G φ I ↔ K.IsDbOf l G ψ I := by
      constructor
      · exact isDbOf_of_forestIso H K φ ψ e he hiso I
      · apply isDbOf_of_forestIso K H ψ φ e.symm _ (hiso.symm H K e) I
        intro v
        simpa only [Equiv.apply_symm_apply] using (he (e.symm v)).symm
    simp only [hdb]
    split_ifs <;> rfl
  · rfl

theorem fixedForestGoodSpace_le_of_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e) (B : Finset ℕ) :
    fixedForestGoodSpace l G H B ≤ fixedForestGoodSpace l G K B := by
  apply Submodule.span_le.mpr
  rintro v ⟨sel, φ₀, hD, rfl⟩
  rw [gVec_iso hG H K hH hK e hiso B sel φ₀]
  exact Submodule.subset_span ⟨sel.image e, (fun u => φ₀ (e.symm u)),
    transportDescription_valid H K hK e hiso sel φ₀ hD, rfl⟩

theorem fixedForestGoodSpace_eq_of_iso (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (e : Fin H.k ≃ Fin K.k)
    (hiso : IsForestIso H K e) (B : Finset ℕ) :
    fixedForestGoodSpace l G H B = fixedForestGoodSpace l G K B :=
  le_antisymm (fixedForestGoodSpace_le_of_iso hG H K hH hK e hiso B)
    (fixedForestGoodSpace_le_of_iso hG K H hK hH e.symm (hiso.symm H K e) B)

theorem fixedForestGoodSpace_orthogonal (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (hln : l + 2 ≤ n)
    (hnot : ¬ ∃ e : Fin H.k ≃ Fin K.k, IsForestIso H K e) (B : Finset ℕ)
    (x : Hil (Db l G)) (hx : x ∈ fixedForestGoodSpace l G H B)
    (y : Hil (Db l G)) (hy : y ∈ fixedForestGoodSpace l G K B) :
    inner ℂ x y = 0 := by
  obtain ⟨ψ, ⟨_, hψ, _⟩, _⟩ := fixedForestGoodSpace_representation hG H hH hln B x hx
  obtain ⟨χ, ⟨_, hχ, _⟩, _⟩ := fixedForestGoodSpace_representation hG K hK hln B y hy
  rw [← hψ, ← hχ]
  exact encodeState_orthogonal hG H K hH hK hln hnot ψ χ

theorem fixedForestGoodSpace_equal_or_orthogonal (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (hln : l + 2 ≤ n) (B : Finset ℕ) :
    fixedForestGoodSpace l G H B = fixedForestGoodSpace l G K B ∨
      ∀ x ∈ fixedForestGoodSpace l G H B, ∀ y ∈ fixedForestGoodSpace l G K B,
        inner ℂ x y = 0 := by
  by_cases hi : ∃ e : Fin H.k ≃ Fin K.k, IsForestIso H K e
  · obtain ⟨e, he⟩ := hi
    exact Or.inl (fixedForestGoodSpace_eq_of_iso hG H K hH hK e he B)
  · exact Or.inr (fixedForestGoodSpace_orthogonal hG H K hH hK hln hi B)

noncomputable abbrev goodSectorFamily (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) (t : ℕ)
    (H : {H : AbsForest n // H.IsValid ∧ H.records ≤ t}) :=
  fixedForestGoodSpace l G H.1 B

abbrev GoodSector (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) (t : ℕ) :=
  FiniteOrthogonalSectors.Sector (goodSectorFamily l G B t)

theorem goodSector_finite (hG : G.IsValid) (hln : l + 2 ≤ n) (B : Finset ℕ) (t : ℕ) :
    Finite (GoodSector l G B t) :=
  FiniteOrthogonalSectors.finite (goodSectorFamily l G B t) (fun H K =>
    fixedForestGoodSpace_equal_or_orthogonal hG H.1 K.1 H.2.1 K.2.1 hln B)

/-- An exact finite orthogonal decomposition of the canonical good space.
Repeated isomorphic forest presentations contribute only one sector. -/
theorem goodSpace_orthogonal_decomposition (hG : G.IsValid) (hln : l + 2 ≤ n)
    (B : Finset ℕ) (t : ℕ) (x : Hil (Db l G)) (hx : x ∈ goodSpace l G B t) :
    letI : Finite (GoodSector l G B t) := goodSector_finite hG hln B t
    letI : Fintype (GoodSector l G B t) := Fintype.ofFinite _
    ∃ v : GoodSector l G B t → Hil (Db l G),
      (∀ P, v P ∈ goodSectorFamily l G B t
        (FiniteOrthogonalSectors.representative (goodSectorFamily l G B t) P)) ∧
      (∑ P, v P) = x ∧ (∑ P, ‖v P‖ ^ 2) = ‖x‖ ^ 2 := by
  apply FiniteOrthogonalSectors.decomposition (goodSectorFamily l G B t)
    (fun H K => fixedForestGoodSpace_equal_or_orthogonal hG H.1 K.1 H.2.1 K.2.1 hln B)
  rwa [goodSpace_eq_iSup_fixedForest l G B t] at hx

end WeldedPath.Supplement.DatabaseSupport

end

-- Solutions.WeldedPathIsolatedDeletionBound
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping DatabaseSupport DisconnectedStability

variable {n l : ℕ} {G : WeldedInstance n}

/-- Deleting a uniquely labeled isolated vertex is close to the good space of the
remaining forest. The omitted terms are exactly collisions with an old vertex. -/
theorem isolated_deletion_approximation (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (a : Fin (labelBound n))
    (ha : ∀ u, H.lab u ≠ some a)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : ((H.k + 1 : ℕ) : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * ((H.k + 1 : ℕ) : ℝ) ^ 3 *
      (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (m : ℝ) (hm : 0 ≤ m)
    (v : Hil (Db l G)) (hv : v ∈ fixedForestGoodSpace l G (addIsolated H a) B) :
    ∃ w ∈ fixedForestGoodSpace l G H B,
      ‖((Real.sqrt m)⁻¹ : ℂ) • deletion a v - w‖ ^ 2 ≤
        (2 * (H.k : ℝ) / m) * ‖v‖ ^ 2 := by
  have hnew := addIsolated_valid H hH a ha
  obtain ⟨f, hf, hminimal, hinv, henc, hnorm⟩ :=
    database_stable_representative hG (addIsolated H a) hnew hn hl hln B hB hBw
      hsurvive hcollision v hv
  have hfzero := coefficient_zero_of_muRef_zero (addIsolated H a) hnew B f hf
  have henc' : fullEncoding (l := l) (addIsolated H a) hnew hG.2 f = v :=
    (fullEncoding_apply _ hnew hG.2 f).trans henc
  have hdel := deletion_fullEncoding_isolated H hH hG.2 a ha f hfzero
  rw [henc'] at hdel
  let c : ℂ := (Real.sqrt m)⁻¹
  let w := c • fullEncoding (l := l) H hH hG.2 (sumLast H.k f)
  refine ⟨w, ?_, ?_⟩
  · exact (fixedForestGoodSpace l G H B).smul_mem c
      (fullEncoding_mem_fixedForestGoodSpace H hH hG.2 B _
        (sumLast_mem_coefficientSpace H hH a ha B f hf))
  · have herr : c • deletion a v - w =
        -(fullEncoding (l := l) H hH hG.2
          (c • (sumLast H.k f - freeSumLast H.k f))) := by
      dsimp [w]
      rw [hdel, map_smul, map_sub, smul_sub]
      abel
    change ‖c • deletion a v - w‖ ^ 2 ≤ _
    calc
      _ = ‖fullEncoding (l := l) H hH hG.2
          (c • (sumLast H.k f - freeSumLast H.k f))‖ ^ 2 := by rw [herr, norm_neg]
      _ ≤ (Fintype.card (ForestAut H) : ℝ) *
          ‖c • (sumLast H.k f - freeSumLast H.k f)‖ ^ 2 :=
        fullEncoding_norm_sq_le hG H hH (by omega) _
      _ ≤ (Fintype.card (ForestAut H) : ℝ) *
          (((H.k : ℝ) / m) * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (isolated_omission_bound H.k m hm f) (Nat.cast_nonneg _)
      _ = ((H.k : ℝ) / m) *
          ((Fintype.card (ForestAut (addIsolated H a)) : ℝ) * ‖f‖ ^ 2) := by
        rw [addIsolated_aut_card H a ha]
        ring
      _ ≤ ((H.k : ℝ) / m) * (2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg (Nat.cast_nonneg _) hm)
      _ = _ := by ring

theorem isolated_vertex_deletion_approximation (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (y : Fin H.k) (hy : IsIsolated H y)
    (a : Fin (labelBound n)) (hya : H.lab y = some a)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (H.k : ℝ) ^ 3 *
      (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (m : ℝ) (hm : 0 ≤ m)
    (v : Hil (Db l G)) (hv : v ∈ fixedForestGoodSpace l G H B) :
    ∃ w ∈ fixedForestGoodSpace l G (deleteIsolated H y) B,
      ‖((Real.sqrt m)⁻¹ : ℂ) • deletion a v - w‖ ^ 2 ≤
        (2 * ((deleteIsolated H y).k : ℝ) / m) * ‖v‖ ^ 2 := by
  have hK := deleteIsolated_valid H hH y hy
  have ha := deleted_label_fresh H hH y a hya
  have hnew := addIsolated_valid (deleteIsolated H y) hK a ha
  have heq := fixedForestGoodSpace_eq_of_iso (l := l) hG
    (addIsolated (deleteIsolated H y) a) H hnew hH (restoreEquiv H y)
    (restore_isForestIso H y hy a hya) B
  have hv' : v ∈ fixedForestGoodSpace l G (addIsolated (deleteIsolated H y) a) B :=
    heq.symm ▸ hv
  apply isolated_deletion_approximation hG (deleteIsolated H y) hK a ha
    hn hl hln B hB hBw ?_ ?_ m hm v hv'
  · simpa only [deleteIsolated_vertices H y] using hsurvive
  · simpa only [deleteIsolated_vertices H y] using hcollision

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathIsolatedSectorInjectivity
section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}

noncomputable def extendIsolatedEquiv {k m : ℕ} (e : Fin k ≃ Fin m) :
    Fin (k+1) ≃ Fin (m+1) :=
  finSuccEquivLast.trans ((Equiv.optionCongr e).trans finSuccEquivLast.symm)

@[simp] lemma extendIsolatedEquiv_old {k m : ℕ} (e : Fin k ≃ Fin m) (u : Fin k) :
    extendIsolatedEquiv e u.castSucc = (e u).castSucc := by simp [extendIsolatedEquiv]

@[simp] lemma extendIsolatedEquiv_last {k m : ℕ} (e : Fin k ≃ Fin m) :
    extendIsolatedEquiv e (Fin.last k) = Fin.last m := by simp [extendIsolatedEquiv]

theorem addIsolated_isForestIso (H K : AbsForest n) (a : Fin (labelBound n))
    (e : Fin H.k ≃ Fin K.k) (he : IsForestIso H K e) :
    IsForestIso (addIsolated H a) (addIsolated K a) (extendIsolatedEquiv e) := by
  constructor
  · intro u
    induction u using Fin.lastCases with
    | last => simp only [extendIsolatedEquiv_last, Fin.snoc_last]
    | cast u =>
      rw [extendIsolatedEquiv_old, addIsolated_lab_old, addIsolated_lab_old]
      exact he.1 u
  · intro u v α
    induction u using Fin.lastCases with
    | last =>
      rw [extendIsolatedEquiv_last]
      exact iff_of_false (addIsolated_not_coloredAdj_last H a v α)
        (addIsolated_not_coloredAdj_last K a _ α)
    | cast u =>
      induction v using Fin.lastCases with
      | last =>
        rw [extendIsolatedEquiv_last]
        exact iff_of_false (addIsolated_not_coloredAdj_last_right H a _ α)
          (addIsolated_not_coloredAdj_last_right K a _ α)
      | cast v =>
        rw [extendIsolatedEquiv_old, extendIsolatedEquiv_old,
          addIsolated_coloredAdj_old, addIsolated_coloredAdj_old]
        exact he.2 u v α

theorem forestIso_comp (H K L : AbsForest n) (e : Fin H.k ≃ Fin K.k)
    (f : Fin K.k ≃ Fin L.k) (he : IsForestIso H K e) (hf : IsForestIso K L f) :
    IsForestIso H L (e.trans f) := by
  constructor
  · intro u
    exact (hf.1 (e u)).trans (he.1 u)
  · intro u v α
    exact (he.2 u v α).trans (hf.2 (e u) (e v) α)

/-- Removing the isolated vertex carrying a fixed label cannot merge two
nonisomorphic forest sectors: the removed vertex can be restored canonically. -/
theorem deleteIsolated_iso_implies_original_iso (H K : AbsForest n)
    (u : Fin H.k) (hu : IsIsolated H u) (v : Fin K.k) (hv : IsIsolated K v)
    (a : Fin (labelBound n)) (hua : H.lab u = some a) (hva : K.lab v = some a)
    (e : Fin (deleteIsolated H u).k ≃ Fin (deleteIsolated K v).k)
    (he : IsForestIso (deleteIsolated H u) (deleteIsolated K v) e) :
    ∃ f : Fin H.k ≃ Fin K.k, IsForestIso H K f := by
  let d := extendIsolatedEquiv e
  have hd := addIsolated_isForestIso (deleteIsolated H u) (deleteIsolated K v) a e he
  have hH := restore_isForestIso H u hu a hua
  have hK := restore_isForestIso K v hv a hva
  refine ⟨((restoreEquiv H u).symm.trans d).trans (restoreEquiv K v), ?_⟩
  exact forestIso_comp _ _ _ _ _
    (forestIso_comp _ _ _ _ _ (hH.symm _ _ _) hd) hK

end WeldedPath.Supplement.LabelBookkeeping

end

-- Solutions.WeldedPathIsolatedDeletionOrthogonality
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping DatabaseSupport DisconnectedStability

variable {n l : ℕ} {G : WeldedInstance n}

theorem fixedForestGoodSpace_le_encoding_range (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsProperColoring) (B : Finset ℕ) :
    fixedForestGoodSpace l G H B ≤ LinearMap.range (fullEncoding (l := l) H hH hG) := by
  rw [← fullEncoding_map_coefficientSpace H hH hG B]
  rintro v ⟨f, hf, rfl⟩
  exact ⟨f, rfl⟩

theorem deletion_mem_encoding_range (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (u : Fin H.k) (hu : IsIsolated H u) (a : Fin (labelBound n)) (hua : H.lab u = some a)
    (B : Finset ℕ) (v : Hil (Db l G)) (hv : v ∈ fixedForestGoodSpace l G H B) :
    deletion a v ∈ LinearMap.range
      (fullEncoding (l := l) (deleteIsolated H u) (deleteIsolated_valid H hH u hu) hG.2) := by
  have hK := deleteIsolated_valid H hH u hu
  have ha := deleted_label_fresh H hH u a hua
  have hnew := addIsolated_valid (deleteIsolated H u) hK a ha
  have heq := fixedForestGoodSpace_eq_of_iso (l := l) hG
    (addIsolated (deleteIsolated H u) a) H hnew hH (restoreEquiv H u)
    (restore_isForestIso H u hu a hua) B
  exact deletion_mem_encoding_range_isolated (deleteIsolated H u) hK hG.2 a ha B v (heq.symm ▸ hv)

theorem encoding_ranges_orthogonal (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (hln : l + 2 ≤ n)
    (hnot : ¬ ∃ e : Fin H.k ≃ Fin K.k, IsForestIso H K e)
    (x : Hil (Db l G)) (hx : x ∈ LinearMap.range (fullEncoding (l := l) H hH hG.2))
    (y : Hil (Db l G)) (hy : y ∈ LinearMap.range (fullEncoding (l := l) K hK hG.2)) :
    inner ℂ x y = 0 := by
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := hy
  rw [fullEncoding_apply, fullEncoding_apply]
  exact encodeState_orthogonal hG H K hH hK hln hnot _ _

/-- Collision errors from deleting the same unique partial label in different
forest sectors are orthogonal, including arbitrary coherent coefficients. -/
theorem isolated_deletion_errors_orthogonal (hG : G.IsValid) (H K : AbsForest n)
    (hH : H.IsValid) (hK : K.IsValid) (hln : l + 2 ≤ n)
    (hnot : ¬ ∃ e : Fin H.k ≃ Fin K.k, IsForestIso H K e)
    (u : Fin H.k) (hu : IsIsolated H u) (v : Fin K.k) (hv : IsIsolated K v)
    (a : Fin (labelBound n)) (hua : H.lab u = some a) (hva : K.lab v = some a)
    (B : Finset ℕ) (c d : ℂ)
    (x : Hil (Db l G)) (hx : x ∈ fixedForestGoodSpace l G H B)
    (y : Hil (Db l G)) (hy : y ∈ fixedForestGoodSpace l G K B)
    (w : Hil (Db l G)) (hw : w ∈ fixedForestGoodSpace l G (deleteIsolated H u) B)
    (z : Hil (Db l G)) (hz : z ∈ fixedForestGoodSpace l G (deleteIsolated K v) B) :
    inner ℂ (c • deletion a x - w) (d • deletion a y - z) = 0 := by
  have hDH := deleteIsolated_valid H hH u hu
  have hDK := deleteIsolated_valid K hK v hv
  apply encoding_ranges_orthogonal hG (deleteIsolated H u) (deleteIsolated K v)
    hDH hDK hln ?_ _ ?_ _ ?_
  · rintro ⟨e, he⟩
    exact hnot (deleteIsolated_iso_implies_original_iso H K u hu v hv a hua hva e he)
  · exact (LinearMap.range (fullEncoding (l := l) (deleteIsolated H u) hDH hG.2)).sub_mem
      ((LinearMap.range _).smul_mem c (deletion_mem_encoding_range hG H hH u hu a hua B x hx))
      (fixedForestGoodSpace_le_encoding_range _ hDH hG.2 B hw)
  · exact (LinearMap.range (fullEncoding (l := l) (deleteIsolated K v) hDK hG.2)).sub_mem
      ((LinearMap.range _).smul_mem d (deletion_mem_encoding_range hG K hK v hv a hva B y hy))
      (fixedForestGoodSpace_le_encoding_range _ hDK hG.2 B hz)

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathLabelInsertionGoodSpace
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport RegisterTransport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma insertion_ket_used (a : Fin (labelBound n)) (I : Db l G) (ha : I.1.symm a ≠ none) :
    insertion a (ket I) = 0 := by
  rw [insertion, ofBasis_ket, insertionBasis, if_neg ha]

theorem insertion_gVec_used (hG : G.IsProperColoring) (D : Description n) (hD : D.IsValid)
    (hln : l + 2 ≤ n) (B : Finset ℕ) (a : Fin (labelBound n))
    (u : Fin D.H.k) (hu : D.H.lab u = some a) : insertion a (D.gVec l G B) = 0 := by
  rw [gVec_eq_total_sum hG D hD B, map_sum]
  apply Finset.sum_eq_zero
  intro φ hφuniv
  by_cases hφ : D.IsGood l G B φ
  · rw [if_pos hφ, map_smul]
    let hp := positive_mu_vertex_nonzero D.H φ (ne_of_gt hφ.1) hln
    have hi := (totalDb_isDbOf (l := l) D.H hD.1 hG φ hφ.2.2.2).1
      (vertexLabelIndex D.H φ hp u) a |>.mpr ⟨u, vertexLabelIndex_val D.H φ hp u, hu⟩
    have hs := ((totalDb (l := l) D.H hD.1 hG φ).1.inv (vertexLabelIndex D.H φ hp u) a).mpr hi
    have hne : (totalDb (l := l) D.H hD.1 hG φ).1.symm a ≠ none := by
      intro hh
      have hbad := hs.symm.trans hh
      cases hbad
    rw [insertion_ket_used a _ hne, smul_zero]
  · rw [if_neg hφ, map_zero]

theorem insertion_mem_goodSpace (hG : G.IsProperColoring) (hln : l + 2 ≤ n)
    (B : Finset ℕ) (t : ℕ) (a : Fin (labelBound n))
    (f : Hil (Db l G)) (hf : f ∈ goodSpace l G B t) :
    insertion a f ∈ goodSpace l G B (t+1) := by
  have hle : goodSpace l G B t ≤
      (goodSpace l G B (t+1)).comap (insertion a).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨D,hD,ht,rfl⟩
    change insertion a (D.gVec l G B) ∈ goodSpace l G B (t+1)
    by_cases ha : ∀ u, D.H.lab u ≠ some a
    · rw [insertion_gVec hG D hD hln B a ha]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro u hu
        apply Submodule.subset_span
        refine ⟨relabelDescription D u a, relabelDescription_valid D hD u a ha, ?_, rfl⟩
        change (withLabel D.H u (some a)).records ≤ t+1
        rw [insert_records D.H u a (Finset.mem_filter.mp hu).2]
        omega
      · apply Submodule.smul_mem
        apply Submodule.sum_mem
        intro x hx
        apply Submodule.subset_span
        refine ⟨addIsolatedDescription D a (labelOfIndex x),
          addIsolatedDescription_valid D hD a ha (labelOfIndex x), ?_, rfl⟩
        change (addIsolated D.H a).records ≤ t+1
        rw [addIsolated_records]
        omega
    · push_neg at ha
      obtain ⟨u,hu⟩ := ha
      rw [insertion_gVec_used hG D hD hln B a u hu]
      exact Submodule.zero_mem _
  exact hle hf

theorem normalizedInsertion_mem_goodSpace (hG : G.IsProperColoring) (hln : l + 2 ≤ n)
    (B : Finset ℕ) (t r : ℕ) (a : Fin (labelBound n))
    (f : Hil (Db l G)) (hf : f ∈ goodSpace l G B t) :
    normalizedInsertion r a f ∈ goodSpace l G B (t+1) := by
  exact Submodule.smul_mem _ _ (insertion_mem_goodSpace hG hln B t a f hf)

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathReferenceSizes
section

namespace WeldedPath.Supplement.ReferenceSizes

open Classical LoopProof

theorem boundary_card_le {n l : ℕ} (hl : 1 ≤ l) (hln : l ≤ n) :
    (Vbd n l).card ≤ 6 * 2 ^ (n - l) := by
  let R := 2 ^ (n + 1) - 1
  have hsub : Vbd n l ⊆ Finset.range (2 ^ (n - l + 1)) ∪
      (Finset.range (2 ^ (n - l + 2))).image (fun v => R + v) := by
    intro v hv
    have hmem := Finset.mem_filter.mp hv
    have hV : IsVertex n v := Finset.mem_range.mp hmem.1
    by_cases hleft : v < R
    · apply Finset.mem_union_left
      have hcol := col_left_le n v hleft
      have hcl : col n v ≤ n - l := by
        rcases hmem.2 with h | h | h | h <;> omega
      have hd : Nat.log 2 (v + 1) ≤ n - l := by
        simpa only [col, if_pos (show v < 2 ^ (n + 1) - 1 from hleft)] using hcl
      have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (v + 1)
      have hm : 2 ^ (Nat.log 2 (v + 1) + 1) ≤ 2 ^ (n - l + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact Finset.mem_range.mpr (by omega)
    · apply Finset.mem_union_right
      have hright : R ≤ v := by omega
      have hcol := col_right_ge n v hV hright
      have hcl : n + l ≤ col n v := by
        rcases hmem.2 with h | h | h | h <;> omega
      have hd0 := log_right_le n v hV hright
      have hd : Nat.log 2 (v - R + 1) ≤ n - l + 1 := by
        simp only [col, if_neg (show ¬ v < 2 ^ (n + 1) - 1 from hleft)] at hcl
        dsimp [R] at *
        omega
      have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (v - R + 1)
      have hm : 2 ^ (Nat.log 2 (v - R + 1) + 1) ≤ 2 ^ (n - l + 2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact Finset.mem_image.mpr ⟨v - R, Finset.mem_range.mpr (by omega), by omega⟩
  calc
    _ ≤ (Finset.range (2 ^ (n - l + 1)) ∪
        (Finset.range (2 ^ (n - l + 2))).image (fun v => R + v)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.range (2 ^ (n - l + 1))).card +
        ((Finset.range (2 ^ (n - l + 2))).image (fun v => R + v)).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.range (2 ^ (n - l + 1))).card +
        (Finset.range (2 ^ (n - l + 2))).card := Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by simp only [Finset.card_range, pow_add]; ring

theorem boundary_disjoint_weld {n l : ℕ} (hl : 2 ≤ l) (hln : l ≤ n) :
    Disjoint (Vbd n l) (Vweld n) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hb := (Finset.mem_filter.mp hv).2
  have hw' := (Finset.mem_filter.mp hw).2
  rcases hb with hb | hb | hb | hb <;> rcases hw' with hw' | hw' <;> omega

/-- No abstract vertex is unrecorded and isolated, so the record budget
controls the number of vertices without any hidden graph-size parameter. -/
theorem forest_vertices_le_twice_records {n : ℕ} (H : AbsForest n) (hH : H.IsValid) :
    H.k ≤ 2 * H.records := by
  let L := Finset.univ.filter fun u => (H.lab u).isSome
  have hs : (Finset.univ : Finset (Fin H.k)) ⊆
      L ∪ (H.E.image Prod.fst ∪ H.E.image Prod.snd) := by
    intro u _
    rcases hH.2.2.2.2 u with hu | ⟨p, hp, hu | hu⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, hu⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, hu⟩))
  have hc := Finset.card_le_card hs
  have h₁ := Finset.card_union_le L (H.E.image Prod.fst ∪ H.E.image Prod.snd)
  have h₂ := Finset.card_union_le (H.E.image Prod.fst) (H.E.image Prod.snd)
  have h₃ := Finset.card_image_le (s := H.E) (f := Prod.fst)
  have h₄ := Finset.card_image_le (s := H.E) (f := Prod.snd)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  change H.k ≤ 2 * (H.E.card + L.card)
  omega

end WeldedPath.Supplement.ReferenceSizes

end

-- Solutions.WeldedPathInverseLabelSector
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping DatabaseSupport ReferenceSizes

variable {n l : ℕ} {G : WeldedInstance n}

theorem inverseLabel_mem_fresh_fixedForest (hG : G.IsValid) (H : AbsForest n)
    (hH : H.IsValid) (hln : l + 2 ≤ n) (B : Finset ℕ) (t : ℕ)
    (ht : H.records ≤ t) (a : Fin (labelBound n)) (ha : ∀ u, H.lab u ≠ some a)
    (v : Hil (Db l G)) (hv : v ∈ fixedForestGoodSpace l G H B) :
    inverseLabel a v ∈ goodSpace l G B (t+1) := by
  rw [inverseLabel_unset (Finset.univ.filter (fun u => (H.lab u).isSome)).card a v
    (fun I hI => ⟨(fixedForest_label_unused_iff hG H hH hln B v hv I hI a).mpr ha,
      fixedForest_label_size hG H hH hln B v hv I hI⟩)]
  exact normalizedInsertion_mem_goodSpace hG.2 hln B t _ a v
    (fixedForestGoodSpace_le_goodSpace H B t ht hv)

/-- A fixed-forest inverse-label query admits a good approximation with one
orthogonal deletion error. Only an isolated vertex carrying the query label
can produce that error. -/
theorem inverseLabel_sector_approximation (hG : G.IsValid) (H : AbsForest n)
    (hH : H.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (t : ℕ) (ht : H.records ≤ t) (htM : t ≤ labelBound n)
    (a : Fin (labelBound n)) (v : Hil (Db l G)) (hv : v ∈ fixedForestGoodSpace l G H B) :
    ∃ w e : Hil (Db l G), w ∈ goodSpace l G B (t+1) ∧
      inverseLabel a v = w + e - inverseLabel a e ∧
      ‖e‖ ^ 2 ≤ (4 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) * ‖v‖ ^ 2 ∧
      (e = 0 ∨ ∃ (u : Fin H.k) (hu : IsIsolated H u), H.lab u = some a ∧
        e ∈ LinearMap.range (fullEncoding (l := l) (deleteIsolated H u)
          (deleteIsolated_valid H hH u hu) hG.2)) := by
  have hln' : l + 2 ≤ n := by omega
  have hnonneg : 0 ≤ (4 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) * ‖v‖ ^ 2 := by
    positivity
  by_cases ha : ∀ u, H.lab u ≠ some a
  · refine ⟨inverseLabel a v, 0,
      inverseLabel_mem_fresh_fixedForest hG H hH hln' B t ht a ha v hv, ?_, ?_, Or.inl rfl⟩
    · simp only [add_zero, map_zero, sub_zero]
    · simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using hnonneg
  · obtain ⟨u, hua⟩ : ∃ u, H.lab u = some a := by simpa only [not_forall, not_not] using ha
    let r := (Finset.univ.filter (fun u => (H.lab u).isSome)).card - 1
    let m : ℝ := ((labelBound n - r : ℕ) : ℝ)
    let c : ℂ := (Real.sqrt m)⁻¹
    have hcount := label_count_pos_of_used H u a hua
    have hsupport : ∀ I, v I ≠ 0 → I.1.symm a ≠ none ∧ I.1.size = r+1 := by
      intro I hI
      refine ⟨?_, ?_⟩
      · intro he
        exact (fixedForest_label_unused_iff hG H hH hln' B v hv I hI a).mp he u hua
      · rw [fixedForest_label_size hG H hH hln' B v hv I hI]
        dsimp [r]
        omega
    have heq : inverseLabel a v = v + c • deletion a v - inverseLabel a (c • deletion a v) :=
      inverseLabel_used_recompression r a v hsupport
    have hvGood : v ∈ goodSpace l G B (t+1) :=
      fixedForestGoodSpace_le_goodSpace H B (t+1) (by omega) hv
    by_cases hu : IsIsolated H u
    · have hD := deleteIsolated_valid H hH u hu
      have hDa := deleted_label_fresh H hH u a hua
      obtain ⟨z, hz, hbound⟩ := isolated_vertex_deletion_approximation hG H hH u hu a hua
        hn hl hln B hB hBw hsurvive hcollision m (Nat.cast_nonneg _) v hv
      have hrecords := deleteIsolated_records H hH u hu a hua
      have hzGood := fixedForestGoodSpace_le_goodSpace (deleteIsolated H u) B (t+1) (by omega) hz
      have hzInv := inverseLabel_mem_fresh_fixedForest hG (deleteIsolated H u) hD hln' B t
        (by omega) a hDa z hz
      refine ⟨v + z - inverseLabel a z, c • deletion a v - z,
        (goodSpace l G B (t+1)).sub_mem ((goodSpace l G B (t+1)).add_mem hvGood hzGood) hzInv,
        ?_, ?_, Or.inr ⟨u, hu, hua, ?_⟩⟩
      · rw [heq, map_sub]
        abel
      · have hk := forest_vertices_le_twice_records H hH
        have hkD := deleteIsolated_vertices H u
        have hkR : ((deleteIsolated H u).k : ℝ) ≤ 2 * (t : ℝ) := by
          exact_mod_cast (show (deleteIsolated H u).k ≤ 2*t by omega)
        have hlabels := label_count_le_records H
        have hd : labelBound n - t + 1 ≤ labelBound n - r := by dsimp [r]; omega
        have hdR : ((labelBound n - t + 1 : ℕ) : ℝ) ≤ m := by
          dsimp [m]
          exact_mod_cast hd
        have hdpos : (0 : ℝ) < ((labelBound n - t + 1 : ℕ) : ℝ) := by positivity
        have hratio : 2 * ((deleteIsolated H u).k : ℝ) / m ≤
            4 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ) := by
          calc
            _ ≤ (4 * (t : ℝ)) / m := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
            _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hdpos hdR
        exact hbound.trans (mul_le_mul_of_nonneg_right hratio (sq_nonneg _))
      · exact (LinearMap.range (fullEncoding (l := l) (deleteIsolated H u) hD hG.2)).sub_mem
          ((LinearMap.range _).smul_mem c (deletion_mem_encoding_range hG H hH u hu a hua B v hv))
          (fixedForestGoodSpace_le_encoding_range _ hD hG.2 B hz)
    · have hincident : ∃ p ∈ H.E, p.1 = u ∨ p.2 = u := by
        by_contra hh
        apply hu
        intro p hp
        exact ⟨fun he => hh ⟨p, hp, Or.inl he⟩, fun he => hh ⟨p, hp, Or.inr he⟩⟩
      have hD := erase_valid H hH u hincident
      have hDel := deletion_mem_incident_fixedForest hG.2 H hH hln' B a u hua hincident v hv
      have hrecords := erase_records H u a hua
      have hDa : ∀ y, (withLabel H u none).lab y ≠ some a := by
        intro y hy
        by_cases hyu : y = u
        · subst y
          have hbad := (withLabel_self H u none).symm.trans hy
          cases hbad
        · have he : H.lab y = some a := by simpa only [Function.update_of_ne hyu] using hy
          exact hyu (hH.2.2.2.1 y u a he hua)
      have hz : c • deletion a v ∈ fixedForestGoodSpace l G (withLabel H u none) B :=
        (fixedForestGoodSpace l G (withLabel H u none) B).smul_mem c hDel
      have hzGood := fixedForestGoodSpace_le_goodSpace (withLabel H u none) B (t+1) (by omega) hz
      have hzInv := inverseLabel_mem_fresh_fixedForest hG (withLabel H u none) hD hln' B t
        (by omega) a hDa _ hz
      refine ⟨v + c • deletion a v - inverseLabel a (c • deletion a v), 0,
        (goodSpace l G B (t+1)).sub_mem ((goodSpace l G B (t+1)).add_mem hvGood hzGood) hzInv,
        ?_, ?_, Or.inl rfl⟩
      · simpa only [add_zero, map_zero, sub_zero] using heq
      · simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using hnonneg

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathInverseLabelGoodSpace
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping DatabaseSupport ReferenceSizes CoefficientStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

/-- The inverse label-compression stage preserves the good space up to the
collision loss of an isolated queried vertex, with no forest-sector factor. -/
theorem inverseLabel_goodSpace_approximation (hG : G.IsValid)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (t : ℕ) (htM : t ≤ labelBound n)
    (hsurvive : (2 * (t : ℝ)) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (2 * (t : ℝ)) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (a : Fin (labelBound n)) (v : Hil (Db l G)) (hv : v ∈ goodSpace l G B t) :
    ∃ w ∈ goodSpace l G B (t+1),
      ‖inverseLabel a v - w‖ ^ 2 ≤
        (16 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) * ‖v‖ ^ 2 := by
  have hln' : l + 2 ≤ n := by omega
  letI : Finite (GoodSector l G B t) := goodSector_finite hG hln' B t
  letI : Fintype (GoodSector l G B t) := Fintype.ofFinite _
  let F (P : GoodSector l G B t) :=
    FiniteOrthogonalSectors.representative (goodSectorFamily l G B t) P
  obtain ⟨x, hx, hsum, hnorm⟩ := goodSpace_orthogonal_decomposition hG hln' B t v hv
  have hlocal (P : GoodSector l G B t) := by
    have hk : ((F P).1.k : ℝ) ≤ 2 * (t : ℝ) := by
      have hh := forest_vertices_le_twice_records (F P).1 (F P).2.1
      exact_mod_cast (show (F P).1.k ≤ 2*t by have := (F P).2.2; omega)
    have hs : (((F P).1.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n)) ≤ 1 / 2 := by
      calc
        _ ≤ (2 * (t : ℝ)) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) := by gcongr
        _ ≤ _ := hsurvive
    have hc : 2 * ((F P).1.k : ℝ)^3 * (96 * ((n : ℝ)+1) / (2 : ℝ)^n) ≤ 1/2 := by
      calc
        _ ≤ 2 * (2 * (t : ℝ))^3 * (96 * ((n : ℝ)+1) / (2 : ℝ)^n) := by gcongr
        _ ≤ _ := hcollision
    exact inverseLabel_sector_approximation hG (F P).1 (F P).2.1 hn hl hln B hB hBw
      hs hc t (F P).2.2 htM a (x P) (hx P)
  choose w e hw he hbound hkind using hlocal
  have hnot (P Q : GoodSector l G B t) (hPQ : P ≠ Q) :
      ¬ ∃ f : Fin (F P).1.k ≃ Fin (F Q).1.k, IsForestIso (F P).1 (F Q).1 f := by
    rintro ⟨f, hf⟩
    apply hPQ
    apply Subtype.ext
    calc
      P.1 = goodSectorFamily l G B t (F P) :=
        (FiniteOrthogonalSectors.representative_space _ P).symm
      _ = goodSectorFamily l G B t (F Q) :=
        fixedForestGoodSpace_eq_of_iso hG (F P).1 (F Q).1 (F P).2.1 (F Q).2.1 f hf B
      _ = Q.1 := FiniteOrthogonalSectors.representative_space _ Q
  have horth : ∀ P Q : GoodSector l G B t, P ≠ Q → inner ℂ (e P) (e Q) = 0 := by
    intro P Q hPQ
    rcases hkind P with hzero | ⟨u, hu, hua, hPe⟩
    · rw [hzero, inner_zero_left]
    rcases hkind Q with hzero | ⟨z, hz, hza, hQe⟩
    · rw [hzero, inner_zero_right]
    apply encoding_ranges_orthogonal hG (deleteIsolated (F P).1 u) (deleteIsolated (F Q).1 z)
      (deleteIsolated_valid _ (F P).2.1 u hu) (deleteIsolated_valid _ (F Q).2.1 z hz)
      hln' ?_ _ hPe _ hQe
    rintro ⟨f, hf⟩
    exact hnot P Q hPQ
      (deleteIsolated_iso_implies_original_iso (F P).1 (F Q).1 u hu z hz a hua hza f hf)
  let E := ∑ P, e P
  let W := ∑ P, w P
  have hE : ‖E‖ ^ 2 ≤
      (4 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) * ‖v‖ ^ 2 := by
    dsimp [E]
    rw [norm_sum_sq_orthogonal _ horth]
    calc
      _ ≤ ∑ P, (4 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) * ‖x P‖ ^ 2 :=
        Finset.sum_le_sum (fun P _ => hbound P)
      _ = _ := by rw [← Finset.mul_sum, hnorm]
  refine ⟨W, (goodSpace l G B (t+1)).sum_mem (fun P _ => hw P), ?_⟩
  have herr : inverseLabel a v - W = E - inverseLabel a E := by
    rw [← hsum, map_sum]
    dsimp [E, W]
    simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sum]
    abel
  have hnormerr : ‖inverseLabel a v - W‖ ≤ 2 * ‖E‖ := by
    rw [herr]
    calc
      _ ≤ ‖E‖ + ‖inverseLabel a E‖ := norm_sub_le _ _
      _ = _ := by rw [inverseLabel_norm]; ring
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnormerr 2
  calc
    _ ≤ 4 * ‖E‖ ^ 2 := by nlinarith
    _ ≤ 4 * ((4 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hE (by norm_num)
    _ = _ := by ring

end WeldedPath.Supplement.LabelInsertion

end

-- Solutions.WeldedPathInverseLabelQueryBound
section

namespace WeldedPath.Supplement.LabelInsertion

open Classical

variable {n l : ℕ} {G : WeldedInstance n}

/-- The canonical coherently controlled inverse-label stage satisfies Lemma4.7's
good-space bound with an explicit constant. -/
theorem pCinvLab_good_leakage (hG : G.IsValid)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (t : ℕ) (htM : t ≤ labelBound n)
    (hsurvive : (2 * (t : ℝ)) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (2 * (t : ℝ)) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2) :
    ‖((1 : Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G)) -
        projGoodB l G B (t+1)).comp ((pCinvLab l G).comp (projGoodB l G B t))‖ ≤
      Real.sqrt (16 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) := by
  apply pCinvLab_good_leakage_of_db_bound B t _ (by positivity)
  exact inverseLabel_goodSpace_approximation hG hn hl hln B hB hBw t htM hsurvive hcollision

end WeldedPath.Supplement.LabelInsertion

end

open Classical WeldedPath WeldedPath.Supplement

theorem solution {n l : ℕ} (G : WeldedInstance n)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (t : ℕ) (htM : t ≤ labelBound n)
    (hsurvive : (2 * (t : ℝ)) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (2 * (t : ℝ)) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2) :
    ‖((1 : Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G)) -
        projGoodB l G B (t+1)).comp ((pCinvLab l G).comp (projGoodB l G B t))‖ ≤
      Real.sqrt (16 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) := by
  exact LabelInsertion.pCinvLab_good_leakage hG hn hl hln B hB hBw t htM hsurvive hcollision
