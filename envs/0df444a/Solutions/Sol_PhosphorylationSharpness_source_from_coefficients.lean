-- Prove2me | solution 1 for PhosphorylationSharpness.source_from_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:28:21.608785+00:00
-- url     : https://prove2.me/submissions/91aba060-7a61-4c43-8759-3051e9d676ee

import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Definitions.Def_proofs_PhosphorylationSharpness_Source
import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
import Theorems.Thm_PhosphorylationSharpness_dense_inventory
import Theorems.Thm_PhosphorylationSharpness_dense_inventory_product
import Theorems.Thm_PhosphorylationSharpness_root_totals
import Theorems.Thm_PhosphorylationSharpness_DensePositive_eval_pos
import Theorems.Thm_PhosphorylationSharpness_ratio_pos
import Theorems.Thm_PhosphorylationSharpness_reconstruct_equilibrium
import Theorems.Thm_PhosphorylationSharpness_reconstruct_positive
import Theorems.Thm_PhosphorylationSharpness_reconstruct_totals


set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {m : ℕ} (B D : ℝ[X])
    (hB : DensePositive B m) (hD : DensePositive D m) (r x : ℝ)
    (hx : 1 < x)
    (hrel : (x-1)*(B.eval (ratio x)-r*D.eval (ratio x))=
      2*(r-ratio x)*D.eval (ratio x)) :
    let A := (1+X)*D
    let t := fun i : Fin (m+2) => A.coeff i
    let b := fun i : Fin (m+1) => B.coeff i
    let d := fun i : Fin (m+1) => D.coeff i
    let z := reconstruct t b d (ratio x) (rootS x (D.eval (ratio x))) (rootF x)
    z.Positive ∧ Equilibrium (realize t b d) z ∧
      totalE z=2*r ∧ totalF z=2 ∧ totalS z=2*(r+1) := by
  dsimp only
  have hA := dense_inventory_product hD
  have ht : ∀ i : Fin (m+2), 0 < (((1+X)*D : ℝ[X]).coeff i) :=
    fun i => hA.1 i (by omega)
  have hb : ∀ i : Fin (m+1), 0 < B.coeff i := fun i => hB.1 i (by omega)
  have hd : ∀ i : Fin (m+1), 0 < D.coeff i := fun i => hD.1 i (by omega)
  have hu := ratio_pos hx
  have hdv := hD.eval_pos hu
  have hs : 0 < rootS x (D.eval (ratio x)) := by
    exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hu) hdv)
  have hf : 0 < rootF x := div_pos (by norm_num) (by linarith)
  refine ⟨reconstruct_positive _ _ _ ht hb hd hu hs hf,
    reconstruct_equilibrium _ _ _ ht hb _ _ _, ?_⟩
  have h := reconstruct_totals (fun i : Fin (m+2) => (((1+X)*D : ℝ[X]).coeff i))
    (fun i : Fin (m+1) => B.coeff i) (fun i : Fin (m+1) => D.coeff i)
    (ratio x) (rootS x (D.eval (ratio x))) (rootF x)
  rw [dense_inventory hB, dense_inventory hD, dense_inventory hA] at h
  simp only [eval_mul, eval_add, eval_one, eval_X] at h
  obtain ⟨he,hf,hs⟩ := root_totals x r (B.eval (ratio x)) (D.eval (ratio x)) hx hdv hrel
  exact ⟨h.1.trans he, h.2.1.trans hf, h.2.2.trans hs⟩
end PhosphorylationSharpness
