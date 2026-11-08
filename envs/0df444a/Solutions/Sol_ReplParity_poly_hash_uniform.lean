-- Prove2me | solution 1 for ReplParity.poly_hash_uniform
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:52:19.287288+00:00
-- url     : https://prove2.me/submissions/a4164ef1-ebe4-4520-850f-a7c1c06aa58c

import Mathlib
import Definitions.Def_ReplParity_tokenMinHash

open ReplParity in
theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] (κ : ℕ)
    (x : Fin (2 * κ) → F) (hx : Function.Injective x) :
    Function.Bijective (fun c : Fin (2 * κ) → F => fun i => polyHash c (x i)) ∧
    ∀ t : Fin (2 * κ) → F,
      (Finset.univ.filter (fun c : Fin (2 * κ) → F => (fun i => polyHash c (x i)) = t)).card = 1 := by
  have heq : (fun c : Fin (2 * κ) → F => fun i => polyHash c (x i)) =
      (Matrix.vandermonde x).mulVec := by
    funext c i
    simp only [polyHash, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hinj : Function.Injective (fun c : Fin (2 * κ) → F => fun i => polyHash c (x i)) := by
    rw [heq, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hx
  have hbij := Finite.injective_iff_bijective.mp hinj
  refine ⟨hbij, fun t => ?_⟩
  obtain ⟨c, hc⟩ := hbij.2 t
  rw [Finset.card_eq_one]
  refine ⟨c, ?_⟩
  ext c'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    exact hinj (h.trans hc.symm)
  · rintro rfl
    exact hc
