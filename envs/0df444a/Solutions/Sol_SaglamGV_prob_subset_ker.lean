-- Prove2me | solution 1 for SaglamGV.prob_subset_ker
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T12:09:24.822705+00:00
-- url     : https://prove2.me/submissions/e1f7e525-dbdb-4088-8549-0beea43fa89b

import Theorems.Thm_SaglamGV_circuit_sum_rank
import Definitions.Def_SaglamGV_Params
set_option autoImplicit false
open Finset Matrix Submodule SaglamGV

private lemma count_annihilating (n m : ℕ) (S : Finset (Fin n → ZMod 2)) :
    (Finset.univ.filter (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦
      ∀ x ∈ S, M *ᵥ x = 0)).card =
      2 ^ (m * (n - Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))))) := by
  classical
  let U := Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))
  let V := Fin n → ZMod 2
  let W := Fin m → ZMod 2
  let P := fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦ ∀ x ∈ S, M *ᵥ x = 0
  let _ : Fintype (V ⧸ U) := Fintype.ofFinite _
  let _ : Fintype ((V ⧸ U) →ₗ[ZMod 2] W) :=
    Fintype.ofInjective (fun f ↦ (f : (V ⧸ U) → W)) DFunLike.coe_injective
  let e : {M // P M} ≃ ((V ⧸ U) →ₗ[ZMod 2] W) :=
    { toFun := fun M ↦ U.liftQ (Matrix.toLin' M.val) (by
        apply Submodule.span_le.mpr
        intro x hx
        exact M.property x hx)
      invFun := fun f ↦ ⟨LinearMap.toMatrix' (f.comp U.mkQ), by
        intro x hx
        rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
        have hxU : x ∈ U := Submodule.subset_span hx
        have hx0 : U.mkQ x = 0 := by simpa using hxU
        rw [hx0, map_zero]⟩
      left_inv := by
        intro M
        apply Subtype.ext
        apply Matrix.toLin'.injective
        simp only [Matrix.toLin'_toMatrix', Submodule.liftQ_mkQ]
      right_inv := by
        intro f
        apply LinearMap.ext
        intro q
        refine Submodule.Quotient.induction_on U q (fun x ↦ ?_)
        simp }
  rw [← Fintype.card_subtype P, Fintype.card_congr e]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, Module.finrank_linearMap]
  have hQ : Module.finrank (ZMod 2) (V ⧸ U) = n - Module.finrank (ZMod 2) U := by
    rw [Submodule.finrank_quotient, Module.finrank_pi, Fintype.card_fin]
  rw [hQ]
  simp only [W, Module.finrank_pi, Fintype.card_fin]
  rw [Nat.mul_comm]

theorem solution (n d m ℓ : ℕ) (S : Finset (Fin n → ZMod 2))
    (hS : S ∈ circuits n d ℓ) :
    probM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦ ∀ x ∈ S, M *ᵥ x = 0) =
        ((2 : ℝ) ^ (m * (ℓ - 1)))⁻¹ ∧
      ((2 : ℝ) ^ (m * (ℓ - 1)))⁻¹ =
        (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) := by
  classical
  have hstruct := SaglamGV.circuit_sum_rank n d ℓ S hS
  have hrank := hstruct.2.1
  have hk : ℓ - 1 ≤ n := by
    have h := (Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))).finrank_le
    simpa only [hrank, Module.finrank_pi, Fintype.card_fin] using h
  constructor
  · have hcount :
        ((Finset.univ.filter (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦
          ∀ x ∈ S, M *ᵥ x = 0)).card : ℝ) = (2 : ℝ) ^ (m * (n - (ℓ - 1))) := by
      have h := count_annihilating n m S
      rw [hrank] at h
      exact_mod_cast h
    have hexp : m * (n - (ℓ - 1)) + m * (ℓ - 1) = m * n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hk]
    have hpow : (2 : ℝ) ^ (m * n) =
        (2 : ℝ) ^ (m * (n - (ℓ - 1))) * (2 : ℝ) ^ (m * (ℓ - 1)) := by
      rw [← pow_add, hexp]
    have hprob : probM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦
        ∀ x ∈ S, M *ᵥ x = 0) =
        ((Finset.univ.filter (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦
          ∀ x ∈ S, M *ᵥ x = 0)).card : ℝ) / (2 : ℝ) ^ (m * n) := by
      unfold probM avgM
      congr 1
      rw [Finset.natCast_card_filter]
      apply Finset.sum_congr (by ext; simp)
      intro M _
      dsimp only
      split_ifs <;> rfl
    rw [hprob]
    rw [hcount, hpow]
    field_simp
  · have hsub : S ⊆ ballP n d := by
      exact Finset.mem_powerset.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
    have hcard : S.card = ℓ := (Finset.mem_filter.mp hS).2
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    have hv : (vol n d : ℝ) ≠ 0 := by
      have hpos : 0 < vol n d := Finset.card_pos.mpr ⟨x, hsub hx⟩
      exact_mod_cast Nat.ne_of_gt hpos
    have ht : tau n d m / (vol n d : ℝ) = ((2 : ℝ) ^ m)⁻¹ := by
      unfold tau
      field_simp
    rw [ht, inv_pow, ← pow_mul]
