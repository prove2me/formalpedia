-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.prefix_prod_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:37:36.783122+00:00
-- url     : https://prove2.me/submissions/5bc380c7-c67c-4993-b4d4-6c4de406777a

import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_sub_gs_mem
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_det_gram_eq
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_apply
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_eq_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_inner_b_of_lt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (e : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (hU : LinearIndependent ℝ (fun i => fB 1 (e i))) (k : Fin d) :
    1 ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 := by
  classical
  set v : Fin d → EuclideanSpace ℝ (Fin d) := fun i => fB 1 (e i) with hv_def
  have hk : k.val + 1 ≤ d := k.isLt
  obtain ⟨w, hw_def⟩ : ∃ w : Fin (k.val + 1) → EuclideanSpace ℝ (Fin d),
      w = fun i => v (Fin.castLE hk i) := ⟨_, rfl⟩
  have hwi : ∀ i, w i = v (Fin.castLE hk i) := fun i => by rw [hw_def]
  have hw : LinearIndependent ℝ w := by
    rw [hw_def]; exact hU.comp _ (Fin.castLE_injective hk)
  have hgs : ∀ i, gs w i = gs v (Fin.castLE hk i) := by
    intro i
    apply gs_eq_of w i (gs v (Fin.castLE hk i))
    · rw [hwi i]
      refine Submodule.span_mono ?_ (b_sub_gs_mem v (Fin.castLE hk i))
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j.val < i.val := Set.mem_Iio.mp hj
      refine ⟨⟨j.val, by omega⟩, Fin.lt_iff_val_lt_val.mpr hj', ?_⟩
      rw [hwi]
      exact congrArg v (Fin.ext rfl)
    · intro j hj
      rw [hwi j]
      exact gs_inner_b_of_lt v (show Fin.castLE hk j < Fin.castLE hk i from hj)
  have hprod : ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs v j‖ ^ 2 =
      ∏ i, ‖gs w i‖ ^ 2 := by
    symm
    refine Finset.prod_bij (fun i _ => Fin.castLE hk i) ?_ ?_ ?_ ?_
    · intro i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Fin.le_iff_val_le_val, Fin.coe_castLE]
      have := i.isLt
      omega
    · intro a _ b _ h
      exact Fin.castLE_injective hk h
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hj' : j.val ≤ k.val := Fin.le_iff_val_le_val.mp hj
      exact ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro i _
      rw [hgs i]
  have hdet := det_gram_eq w hw
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) ℤ,
      Matrix.gram ℝ w = G.map (Int.cast) := by
    refine ⟨Matrix.of fun a b => ∑ l, e (Fin.castLE hk a) l * e (Fin.castLE hk b) l, ?_⟩
    ext a b
    rw [Matrix.gram_apply, Matrix.map_apply, Matrix.of_apply, hwi, hwi]
    simp [hv_def, fB_apply, toReal, PiLp.inner_apply, Matrix.one_mulVec, mul_comm]
  have hdetZ : (Matrix.gram ℝ w).det = ((G.det : ℤ) : ℝ) := by
    rw [hG]
    have := (Int.castRingHom ℝ).map_det G
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hpos : 0 < ∏ i, ‖gs w i‖ ^ 2 := by
    apply Finset.prod_pos
    intro i _
    exact pow_pos (norm_pos_iff.mpr (gs_ne_zero w hw i)) 2
  have h0 : (0 : ℝ) < (G.det : ℝ) := by rw [← hdetZ, hdet]; exact hpos
  have h1 : (0 : ℤ) < G.det := by exact_mod_cast h0
  have h2 : (1 : ℤ) ≤ G.det := by omega
  rw [hprod, ← hdet, hdetZ]
  exact_mod_cast h2
end ReciprocityTheory.ReducedBases.T2
