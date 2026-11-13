-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.nuGridSupply_swap
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:51:57.541197+00:00
-- url     : https://prove2.me/submissions/ab756fd4-be67-4137-a18f-07459fec5f36

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SwappedNuGridSupply.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/SwappedNuGridSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open scoped FiniteInduce

variable {G : Type*} [Group G]

section

/-- **Peterfalvi (13.1.e)/(4.3)–(4.9), swapped form**: the original `μ`-grid fields,
transposed, supply every `ν`-grid field needed by a second application of `Hypothesis.swap`.

For the support field, an arbitrary type-`P` datum reconciled with the swapped hypothesis has
the same `W`, `W₁`, and `W₂` as the original `Sdata`; hence it defines the same regular set
`typePV` and the same honest `A₀` support. -/
theorem _root_.solution [Finite G]
    (hyp : Hypothesis (G := G))
    (hV : IsMulCommutative ↥hyp.V)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (pins : NuGridSupplyData hyp) :
    NuGridSupplyData (hyp.swap hV Tdata hU hW1 hW2 pins) := by
  refine {
    nu_irreducible := fun i j => hyp.mu_irreducible j i
    nu_row_injective := fun i => hyp.mu_col_injective i
    nu_orthonormal := ?_
    nu_degree_modEq_deltaPrime := fun i j => hyp.mu_degree_modEq_delta j i
    deltaPrime_zero_eq_one := hyp.delta_zero_eq_one
    nu_rowSum_eq_induce := hyp.mu_colSum_eq_induce
    nu_reducible_dichotomy := hyp.mu_reducible_dichotomy
    nu_diff_support := ?_
    nu_apply_of_not_mem_W1 := fun i j w hwW hwT hw =>
      hyp.mu_apply_of_not_mem_W2 j i w hwW hwT hw
    nu_conj := fun i j => hyp.mu_conj j i }
  · intro i k j l
    unfold Hypothesis.swap at i k j l ⊢
    rw [hyp.mu_orthonormal j l i k]
    simp only [and_comm]
  · intro Sdata hU' hW1' hW2' j i k hi hk hdeg
    change TypePData hyp.S at Sdata
    change Sdata.U = hyp.U at hU'
    change Sdata.W1 = hyp.W1 at hW1'
    change Sdata.W2 = hyp.W2 at hW2'
    have hPV : OddOrder.GroupTheory.typePV hyp.S Sdata =
        OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
      unfold OddOrder.GroupTheory.typePV
      rw [Sdata.W_eq, hyp.Sdata.W_eq, hW1', hW2',
        hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]
    have hA0 : S10.typePACore0 hyp.S Sdata = S10.typePACore0 hyp.S hyp.Sdata := by
      simp only [S10.typePACore0, hPV]
    change (hyp.mu j i - hyp.mu j k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S Sdata) hyp.S
    rw [hA0]
    exact hyp.mu_diff_support j hi hk hdeg

end

end OddOrder.Peterfalvi.S15
