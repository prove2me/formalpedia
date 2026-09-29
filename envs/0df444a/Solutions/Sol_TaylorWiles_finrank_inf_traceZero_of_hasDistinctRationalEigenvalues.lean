-- Prove2me | solution 1 for TaylorWiles.finrank_inf_traceZero_of_hasDistinctRationalEigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b34719d3-368d-5bef-a186-f8d76bd54dc9

import Mathlib
import Definitions.Def_Deformations_TaylorWilesLocal
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues

open Module TaylorWiles

universe u

set_option autoImplicit false

open Module

namespace Ws14Port
namespace TaylorWiles

open _root_.TaylorWiles (adAction adAction_apply disc traceZero mem_traceZero_iff)

variable {k : Type*} [Field k]

local notation "M₂ " k => Matrix (Fin 2) (Fin 2) k

lemma disc_eq_sq_sub {M : M₂ k} {α β : k} (htr : M.trace = α + β) (hdet : M.det = α * β) :
    disc M = (α - β) ^ 2 := by
  rw [disc, htr, hdet]; ring

lemma adAction_one (M : M₂ k) : adAction M 1 = 0 := by
  simp

lemma adAction_self (M : M₂ k) : adAction M M = 0 := by
  simp

lemma trace_adAction (M X : M₂ k) : (adAction M X).trace = 0 := by
  rw [adAction_apply, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

private lemma pow_three_apply (f : Module.End k (M₂ k)) (X : M₂ k) :
    (f ^ 3) X = f (f (f X)) := by
  rw [pow_succ, pow_succ, pow_one]
  rfl

theorem cube_adAction (M : M₂ k) : adAction M ^ 3 = disc M • adAction M := by
  apply LinearMap.ext
  intro X
  rw [pow_three_apply, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, LinearMap.smul_apply, adAction_apply, disc,
    Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

section Decomposition

variable {M : M₂ k} (hM : disc M ≠ 0)

include hM in

theorem ker_adAction_sq (X : M₂ k) (h : adAction M (adAction M X) = 0) :
    adAction M X = 0 := by
  have h3 : (adAction M ^ 3) X = 0 := by
    rw [pow_three_apply, h, map_zero]
  rw [cube_adAction, LinearMap.smul_apply] at h3
  exact (smul_eq_zero.mp h3).resolve_left hM

include hM in

theorem disjoint_ker_range_adAction :
    LinearMap.ker (adAction M) ⊓ LinearMap.range (adAction M) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro Y ⟨hker, X, rfl⟩
  exact ker_adAction_sq hM X hker

include hM in

theorem sup_ker_range_adAction :
    LinearMap.ker (adAction M) ⊔ LinearMap.range (adAction M) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  have hdecomp : X = (X - (disc M)⁻¹ • adAction M (adAction M X)) +
      (disc M)⁻¹ • adAction M (adAction M X) := by abel
  rw [hdecomp]
  refine Submodule.add_mem_sup ?_ ?_
  ·
    rw [LinearMap.mem_ker, map_sub, map_smul]
    have h3 : adAction M (adAction M (adAction M X)) = disc M • adAction M X := by
      rw [← pow_three_apply, cube_adAction, LinearMap.smul_apply]
    rw [h3, smul_smul, inv_mul_cancel₀ hM, one_smul, sub_self]
  ·
    exact Submodule.smul_mem _ _ ⟨adAction M X, rfl⟩

include hM in

theorem isCompl_ker_range_adAction :
    IsCompl (LinearMap.ker (adAction M)) (LinearMap.range (adAction M)) :=
  ⟨disjoint_iff.mpr (disjoint_ker_range_adAction hM),
    codisjoint_iff.mpr (sup_ker_range_adAction hM)⟩

end Decomposition

section Centralizer

lemma eq_zero_of_kills_two {N : M₂ k} {v w : Fin 2 → k}
    (hv : N.mulVec v = 0) (hw : N.mulVec w = 0) (hD : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    N = 0 := by

  have hkill : ∀ a b : k, N.mulVec (a • v + b • w) = 0 := by
    intro a b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hw, smul_zero,
      smul_zero, add_zero]
  set D := v 0 * w 1 - v 1 * w 0 with hDdef

  have he0 : (w 1 : k) • v + (-(v 1)) • w = D • ![1, 0] := by
    funext i
    fin_cases i <;> simp [hDdef] <;> ring
  have he1 : (-(w 0) : k) • v + (v 0) • w = D • ![0, 1] := by
    funext i
    fin_cases i <;> simp [hDdef] <;> ring

  have h0 : D • N.mulVec ![1, 0] = 0 := by
    rw [← Matrix.mulVec_smul, ← he0]; exact hkill _ _
  have h1 : D • N.mulVec ![0, 1] = 0 := by
    rw [← Matrix.mulVec_smul, ← he1]; exact hkill _ _
  have h0' : N.mulVec ![1, 0] = 0 := (smul_eq_zero.mp h0).resolve_left hD
  have h1' : N.mulVec ![0, 1] = 0 := (smul_eq_zero.mp h1).resolve_left hD

  have hc0 : ∀ i, N i 0 = 0 := fun i => by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h0' i
  have hc1 : ∀ i, N i 1 = 0 := fun i => by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1' i
  ext i j
  have hj0 := hc0 i
  have hj1 := hc1 i
  fin_cases j
  · simpa using hj0
  · simpa using hj1

lemma exists_cyclic_vec {M : M₂ k} (hM : M 1 0 ≠ 0 ∨ M 0 1 ≠ 0 ∨ M 0 0 ≠ M 1 1) :
    ∃ v : Fin 2 → k, v 0 * (M.mulVec v) 1 - v 1 * (M.mulVec v) 0 ≠ 0 := by
  by_cases h10 : M 1 0 = 0
  · by_cases h01 : M 0 1 = 0
    ·
      have hd : M 0 0 ≠ M 1 1 := by
        rcases hM with h | h | h
        · exact absurd h10 h
        · exact absurd h01 h
        · exact h
      refine ⟨![1, 1], fun hcontra => hd ?_⟩
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hcontra
      linear_combination -hcontra + h10 - h01
    ·
      refine ⟨![0, 1], fun hcontra => h01 ?_⟩
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hcontra
      linear_combination -hcontra
  ·
    refine ⟨![1, 0], fun hcontra => h10 ?_⟩
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hcontra
    linear_combination hcontra

lemma entries_of_disc_ne_zero {M : M₂ k} (hM : disc M ≠ 0) :
    M 1 0 ≠ 0 ∨ M 0 1 ≠ 0 ∨ M 0 0 ≠ M 1 1 := by
  by_contra hcontra
  simp only [not_or, not_ne_iff] at hcontra
  obtain ⟨h10, h01, hd⟩ := hcontra
  apply hM
  rw [disc, Matrix.trace_fin_two, Matrix.det_fin_two, h10, h01, hd]
  ring

lemma linearIndependent_one_self {M : M₂ k}
    (hM : M 1 0 ≠ 0 ∨ M 0 1 ≠ 0 ∨ M 0 0 ≠ M 1 1) :
    LinearIndependent k ![(1 : M₂ k), M] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst

  have happ : ∀ i j : Fin 2, s * (1 : M₂ k) i j + t * M i j = 0 := by
    intro i j
    have h := congrFun (congrFun hst i) j
    simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  have h01 := happ 0 1
  have h10 := happ 1 0
  have h00 := happ 0 0
  have h11 := happ 1 1
  rw [Matrix.one_apply_ne (by decide), mul_zero, zero_add] at h01
  rw [Matrix.one_apply_ne (by decide), mul_zero, zero_add] at h10
  rw [Matrix.one_apply_eq, mul_one] at h00
  rw [Matrix.one_apply_eq, mul_one] at h11

  have ht : t = 0 := by
    by_contra ht
    have hM01 : M 0 1 = 0 := by
      rcases mul_eq_zero.mp h01 with h | h
      · exact absurd h ht
      · exact h
    have hM10 : M 1 0 = 0 := by
      rcases mul_eq_zero.mp h10 with h | h
      · exact absurd h ht
      · exact h
    have hMd : M 0 0 = M 1 1 :=
      mul_left_cancel₀ ht (by linear_combination h00 - h11)
    rcases hM with h | h | h
    · exact h hM10
    · exact h hM01
    · exact h hMd
  subst ht
  rw [zero_mul, add_zero] at h00
  exact ⟨h00, rfl⟩

variable {M : M₂ k}

lemma one_mem_ker_adAction (M : M₂ k) : (1 : M₂ k) ∈ LinearMap.ker (adAction M) :=
  LinearMap.mem_ker.mpr (adAction_one M)

lemma self_mem_ker_adAction (M : M₂ k) : M ∈ LinearMap.ker (adAction M) :=
  LinearMap.mem_ker.mpr (adAction_self M)

lemma span_le_ker_adAction :
    Submodule.span k {(1 : M₂ k), M} ≤ LinearMap.ker (adAction M) := by
  rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨one_mem_ker_adAction M, self_mem_ker_adAction M⟩

lemma finrank_matrix_fin_two : finrank k (M₂ k) = 4 := by
  rw [Module.finrank_matrix]
  simp

theorem finrank_ker_adAction (hM : disc M ≠ 0) :
    finrank k (LinearMap.ker (adAction M)) = 2 := by
  have hentries := entries_of_disc_ne_zero hM

  have hge : 2 ≤ finrank k (LinearMap.ker (adAction M)) := by
    have hspan : finrank k (Submodule.span k (Set.range ![(1 : M₂ k), M])) = 2 := by
      rw [finrank_span_eq_card (linearIndependent_one_self hentries)]
      simp
    have hmono : finrank k (Submodule.span k (Set.range ![(1 : M₂ k), M])) ≤
        finrank k (LinearMap.ker (adAction M)) := by
      apply Submodule.finrank_mono
      rw [show Set.range ![(1 : M₂ k), M] = {(1 : M₂ k), M} from
        Matrix.range_cons_cons_empty _ _ _]
      exact span_le_ker_adAction
    omega

  obtain ⟨v, hv⟩ := exists_cyclic_vec hentries
  have hle : finrank k (LinearMap.ker (adAction M)) ≤ 2 := by
    let ev : LinearMap.ker (adAction M) →ₗ[k] (Fin 2 → k) :=
      { toFun := fun X => (X : M₂ k).mulVec v
        map_add' := fun X Y => by
          simp only [Submodule.coe_add, Matrix.add_mulVec]
        map_smul' := fun c X => by
          simp only [SetLike.val_smul, Matrix.smul_mulVec, RingHom.id_apply] }
    have hinj : Function.Injective ev := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨X, hX⟩ hXv
      have hcomm : M * X = X * M := by
        have h := LinearMap.mem_ker.mp hX
        rw [adAction_apply] at h
        exact sub_eq_zero.mp h
      have hXv' : X.mulVec v = 0 := hXv
      have hXMv : X.mulVec (M.mulVec v) = 0 := by
        rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hXv',
          Matrix.mulVec_zero]
      exact Subtype.ext (eq_zero_of_kills_two hXv' hXMv hv)
    calc finrank k (LinearMap.ker (adAction M)) ≤ finrank k (Fin 2 → k) :=
          LinearMap.finrank_le_finrank_of_injective hinj
      _ = 2 := Module.finrank_fin_fun k
  omega

theorem finrank_range_adAction (hM : disc M ≠ 0) :
    finrank k (LinearMap.range (adAction M)) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (adAction M)
  rw [finrank_ker_adAction hM, finrank_matrix_fin_two] at h
  omega

end Centralizer

section TraceZero

lemma finrank_traceZero : finrank k (traceZero k) = 3 := by
  have hsurj : Function.Surjective (Matrix.traceLinearMap (Fin 2) k k) := fun c =>
    ⟨!![c, 0; 0, 0], by simp [Matrix.trace_fin_two]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) k k)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    finrank_matrix_fin_two] at h
  show finrank k (LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)) = 3
  omega

lemma range_adAction_le_traceZero (M : M₂ k) :
    LinearMap.range (adAction M) ≤ traceZero k := by
  rintro Y ⟨X, rfl⟩
  exact trace_adAction M X

variable {M : M₂ k}

lemma traceless_part_mem (M : M₂ k) :
    M.trace • (1 : M₂ k) - (2 : k) • M ∈ LinearMap.ker (adAction M) ⊓ traceZero k := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, map_smul, map_smul, adAction_one, adAction_self,
      smul_zero, smul_zero, sub_self]
  · rw [mem_traceZero_iff, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one]
    simp only [smul_eq_mul, Fintype.card_fin, Nat.cast_ofNat]
    ring

lemma traceless_part_ne_zero (h2 : (2 : k) ≠ 0)
    (hM : M 1 0 ≠ 0 ∨ M 0 1 ≠ 0 ∨ M 0 0 ≠ M 1 1) :
    M.trace • (1 : M₂ k) - (2 : k) • M ≠ 0 := by
  intro hcontra

  have happ : ∀ i j : Fin 2, M.trace * (1 : M₂ k) i j - 2 * M i j = 0 := by
    intro i j
    have h := congrFun (congrFun hcontra i) j
    simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
  have h01 := happ 0 1
  have h10 := happ 1 0
  have h00 := happ 0 0
  have h11 := happ 1 1
  rw [Matrix.one_apply_ne (by decide), mul_zero, zero_sub, neg_eq_zero] at h01
  rw [Matrix.one_apply_ne (by decide), mul_zero, zero_sub, neg_eq_zero] at h10
  rw [Matrix.one_apply_eq, mul_one] at h00
  rw [Matrix.one_apply_eq, mul_one] at h11
  rcases hM with h | h | h
  · exact h ((mul_eq_zero.mp h10).resolve_left h2)
  · exact h ((mul_eq_zero.mp h01).resolve_left h2)
  · exact h (mul_left_cancel₀ h2 (by linear_combination h11 - h00))

lemma not_ker_le_traceZero (h2 : (2 : k) ≠ 0) :
    ¬ LinearMap.ker (adAction M) ≤ traceZero k := by
  intro hle
  have h := mem_traceZero_iff.mp (hle (one_mem_ker_adAction M))
  rw [Matrix.trace_one] at h
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  exact h2 h

theorem finrank_inf_traceZero (h2 : (2 : k) ≠ 0) (hM : disc M ≠ 0) :
    finrank k (LinearMap.ker (adAction M) ⊓ traceZero k : Submodule k (M₂ k)) = 1 := by

  have hne : M.trace • (1 : M₂ k) - (2 : k) • M ≠ 0 :=
    traceless_part_ne_zero h2 (entries_of_disc_ne_zero hM)
  have hge : 1 ≤ finrank k
      (LinearMap.ker (adAction M) ⊓ traceZero k : Submodule k (M₂ k)) := by
    have hspan : finrank k
        (Submodule.span k {M.trace • (1 : M₂ k) - (2 : k) • M}) = 1 :=
      finrank_span_singleton hne
    have hmono : finrank k
        (Submodule.span k {M.trace • (1 : M₂ k) - (2 : k) • M}) ≤
        finrank k (LinearMap.ker (adAction M) ⊓ traceZero k : Submodule k (M₂ k)) :=
      Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (traceless_part_mem M))
    omega

  have hlt : (LinearMap.ker (adAction M) ⊓ traceZero k : Submodule k (M₂ k)) <
      LinearMap.ker (adAction M) :=
    lt_of_le_of_ne inf_le_left fun hcontra =>
      not_ker_le_traceZero h2 (hcontra ▸ inf_le_right)
  have hle := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_ker_adAction hM] at hle
  omega

lemma disjoint_inf_traceZero_range (hM : disc M ≠ 0) :
    (LinearMap.ker (adAction M) ⊓ traceZero k) ⊓ LinearMap.range (adAction M) = ⊥ := by
  rw [← le_bot_iff]
  calc (LinearMap.ker (adAction M) ⊓ traceZero k) ⊓ LinearMap.range (adAction M) ≤
      LinearMap.ker (adAction M) ⊓ LinearMap.range (adAction M) :=
        inf_le_inf_right _ inf_le_left
    _ = ⊥ := disjoint_ker_range_adAction hM

theorem sup_inf_traceZero_range (h2 : (2 : k) ≠ 0) (hM : disc M ≠ 0) :
    (LinearMap.ker (adAction M) ⊓ traceZero k) ⊔ LinearMap.range (adAction M) =
      traceZero k := by

  have hle : (LinearMap.ker (adAction M) ⊓ traceZero k) ⊔ LinearMap.range (adAction M) ≤
      traceZero k := sup_le inf_le_right (range_adAction_le_traceZero M)

  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (adAction M) ⊓ traceZero k) (LinearMap.range (adAction M))
  rw [disjoint_inf_traceZero_range hM, finrank_inf_traceZero h2 hM,
    finrank_range_adAction hM] at hsum
  rw [finrank_traceZero]
  simp only [finrank_bot] at hsum
  omega

theorem range_lt_traceZero (hM : disc M ≠ 0) :
    LinearMap.range (adAction M) < traceZero k := by
  refine lt_of_le_of_ne (range_adAction_le_traceZero M) fun hcontra => ?_
  have h2' := finrank_range_adAction hM
  rw [hcontra, finrank_traceZero] at h2'
  omega

theorem exists_notMem_range_adAction (h2 : (2 : k) ≠ 0) (hM : disc M ≠ 0) :
    ∃ X ∈ traceZero k, X ≠ 0 ∧ X ∉ LinearMap.range (adAction M) := by
  refine ⟨M.trace • (1 : M₂ k) - (2 : k) • M, (traceless_part_mem M).2,
    traceless_part_ne_zero h2 (entries_of_disc_ne_zero hM), fun hmem => ?_⟩
  have hboth : M.trace • (1 : M₂ k) - (2 : k) • M ∈
      LinearMap.ker (adAction M) ⊓ LinearMap.range (adAction M) :=
    ⟨(traceless_part_mem M).1, hmem⟩
  rw [disjoint_ker_range_adAction hM, Submodule.mem_bot] at hboth
  exact traceless_part_ne_zero h2 (entries_of_disc_ne_zero hM) hboth

end TraceZero

section Conjugation

variable {N N' : M₂ k}

theorem conj_eq_self_iff_commute (hNN' : N * N' = 1) (hN'N : N' * N = 1) (X : M₂ k) :
    N * X * N' = X ↔ adAction N X = 0 := by
  rw [adAction_apply, sub_eq_zero]
  constructor
  · intro h
    calc N * X = N * X * (N' * N) := by rw [hN'N, mul_one]
      _ = N * X * N' * N := by rw [← mul_assoc]
      _ = X * N := by rw [h]
  · intro h
    calc N * X * N' = X * N * N' := by rw [h]
      _ = X := by rw [mul_assoc, hNN', mul_one]

theorem conj_sub_self_eq_adAction_mul (hN'N : N' * N = 1) (X : M₂ k) :
    N * X * N' - X = adAction N (X * N') := by
  rw [adAction_apply, mul_assoc]
  congr 1
  rw [mul_assoc, hN'N, mul_one]

end Conjugation
end Ws14Port.TaylorWiles

namespace Ws14Port

theorem disc_ne_zero' {k : Type u} [Field k] {M : Matrix (Fin 2) (Fin 2) k} (h : M.HasDistinctRationalEigenvalues) : TaylorWiles.disc M ≠ 0 := by
  obtain ⟨α, β, hne, htr, hdet⟩ := h
  rw [show TaylorWiles.disc M = (α - β) ^ 2 by rw [TaylorWiles.disc, htr, hdet]; ring]
  exact pow_ne_zero 2 (sub_ne_zero.mpr hne)

end Ws14Port

theorem solution {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) k} (hM : M.HasDistinctRationalEigenvalues) :
    finrank k (LinearMap.ker (TaylorWiles.adAction M) ⊓ TaylorWiles.traceZero k : Submodule k (Matrix (Fin 2) (Fin 2) k)) = 1 := by
  exact Ws14Port.TaylorWiles.finrank_inf_traceZero h2 (Ws14Port.disc_ne_zero' hM)

end S_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues
end P2MW
export P2MW.S_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues (solution)
