-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.card_shell401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:10:56.817297+00:00
-- url     : https://prove2.me/submissions/633b291c-e79a-4142-a386-7c9a0c15f63a

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
section
open scoped BigOperators
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
private theorem lpsShell401CountIndicator (p : ShellIndex401 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ t : ShellIndex401, if p t then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
private theorem lpsShell401SumCoordinates (f : Fin 10 × Fin 41 × Fin 41 × Fin 41 → ℕ) :
    (∑ t, f t) = ∑ a : Fin 10, ∑ b : Fin 41, ∑ c : Fin 41, ∑ d : Fin 41, f (a,b,c,d) := by
  simp only [Fintype.sum_prod_type]
private theorem lpsShell401Decomposition : shell401.card = ∑ a : Fin 10, lpsShell401Chunk a := by
  let e : ShellIndex401 ≃ Fin 10 × Fin 41 × Fin 41 × Fin 41 := {
    toFun := fun t => (t.aIndex, t.bIndex, t.cIndex, t.dIndex)
    invFun := fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
    left_inv := by intro t; cases t; rfl
    right_inv := by intro t; rfl }
  calc
    shell401.card = ∑ t : ShellIndex401, if t.HasNorm401 then 1 else 0 := by
      exact lpsShell401CountIndicator ShellIndex401.HasNorm401
    _ = ∑ t : Fin 10 × Fin 41 × Fin 41 × Fin 41,
          lpsShell401Summand t.1 t.2.1 t.2.2.1 t.2.2.2 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ a : Fin 10, lpsShell401Chunk a := lpsShell401SumCoordinates _
private theorem lpsShell401Chunk0 : lpsShell401Chunk 0 = 30 := by decide +kernel
private theorem lpsShell401Chunk1 : lpsShell401Chunk 1 = 108 := by decide +kernel
private theorem lpsShell401Chunk2 : lpsShell401Chunk 2 = 96 := by decide +kernel
private theorem lpsShell401Chunk3 : lpsShell401Chunk 3 = 24 := by decide +kernel
private theorem lpsShell401Chunk4 : lpsShell401Chunk 4 = 24 := by decide +kernel
private theorem lpsShell401Chunk5 : lpsShell401Chunk 5 = 48 := by decide +kernel
private theorem lpsShell401Chunk6 : lpsShell401Chunk 6 = 24 := by decide +kernel
private theorem lpsShell401Chunk7 : lpsShell401Chunk 7 = 24 := by decide +kernel
private theorem lpsShell401Chunk8 : lpsShell401Chunk 8 = 0 := by decide +kernel
private theorem lpsShell401Chunk9 : lpsShell401Chunk 9 = 24 := by decide +kernel
private theorem lpsShell401ChunkCounts (a : Fin 10) : lpsShell401Chunk a = ![30,108,96,24,24,48,24,24,0,24] a := by
  fin_cases a
  · exact lpsShell401Chunk0
  · exact lpsShell401Chunk1
  · exact lpsShell401Chunk2
  · exact lpsShell401Chunk3
  · exact lpsShell401Chunk4
  · exact lpsShell401Chunk5
  · exact lpsShell401Chunk6
  · exact lpsShell401Chunk7
  · exact lpsShell401Chunk8
  · exact lpsShell401Chunk9
end QEC.Coding.BalancedProduct.LPSGenerators
end

set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
namespace QEC.Coding.BalancedProduct.LPSGenerators
theorem _root_.solution : shell401.card = 402 := by
  calc
    shell401.card = ∑ a : Fin 10, lpsShell401Chunk a := lpsShell401Decomposition
    _ = ∑ a : Fin 10, ![30,108,96,24,24,48,24,24,0,24] a :=
      Finset.sum_congr rfl (fun a _ => lpsShell401ChunkCounts a)
    _ = 402 := by decide +kernel
end QEC.Coding.BalancedProduct.LPSGenerators
