-- Prove2me | solution 1 for PhosphorylationSharpness.reconstruct_totals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:02.163067+00:00
-- url     : https://prove2.me/submissions/8a1884ec-ad4c-4ecd-a5cb-072d844770b3

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Source

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open scoped BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) :
    totalE (reconstruct t B D u s f)=u*f*(1+s*inventory B u) ∧
    totalF (reconstruct t B D u s f)=f*(1+s*u*inventory D u) ∧
    totalS (reconstruct t B D u s f)=s*inventory t u+u*s*f*(inventory B u+inventory D u) := by
  have hc (v : Fin n → ℝ) : (∑ i, v i*u^(i.val+1)*s*f) = u*s*f*inventory v u := by
    simp only [inventory, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  have hs : (∑ i, t i*u^i.val*s) = s*inventory t u := by
    simp only [inventory, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [totalE, totalF, totalS, reconstruct, hc, hs]
  constructor
  · ring
  constructor <;> ring
end PhosphorylationSharpness
