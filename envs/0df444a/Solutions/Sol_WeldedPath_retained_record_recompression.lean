-- Prove2me | solution 1 for WeldedPath.retained_record_recompression
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T23:00:43.830974+00:00
-- url     : https://prove2.me/submissions/8ccc8240-669d-45bf-a385-3b97925a38cc

import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Definitions.Def_WeldedPath_InjDb
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Definitions.Def_WeldedPath_exactCpO
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_WeldedPath_Supplement_exactCpWT

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

open Classical WeldedPath

universe u

theorem solution :
    ∀ s : ℕ,
      (∀ (I : InjDb s) (x y : Fin s), I x = some y →
        ‖(pC s x - 1) (ket I)‖ ^ 2 = 2 / ((s - I.size + 1 : ℕ) : ℝ)) ∧
      (∀ (C : Type u) [Fintype C] [DecidableEq C]
        (r : ℕ), r ≤ s → ∀ (x y : C → Fin s) (ψ : Hil (C × InjDb s)),
        (∀ c I, ψ (c, I) ≠ 0 → I (x c) = some (y c) ∧ I.size ≤ r) →
        ‖controlled (fun c => pC s (x c) - 1) ψ‖ ≤
          Real.sqrt (2 / ((s - r + 1 : ℕ) : ℝ)) * ‖ψ‖) := by
  intro s
  constructor
  · exact fun I x y hxy => CompressedPrimitive.pC_known_error_sq I x y hxy
  · intro C _ _ r hr x y ψ hψ
    exact CompressedPrimitive.pC_retained_control_norm_bound x y r hr ψ hψ
