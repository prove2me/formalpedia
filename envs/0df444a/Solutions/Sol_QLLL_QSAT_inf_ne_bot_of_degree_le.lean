-- Prove2me | solution 1 for QLLL.QSAT.inf_ne_bot_of_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:51:38.914263+00:00
-- url     : https://prove2.me/submissions/12b6fa90-97e1-4655-b1a3-90b9bd00fc5b

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Theorems.Thm_QLLL_QSAT_finrank_inf_liftL_liftR
import Theorems.Thm_QLLL_Valuation_lll_symmetric
import Mathlib

-- inline helpers from QuantumLocalLemma.Quantum.KQSAT.Basic
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# k-QSAT and the locality structure

Towards Corollary 16 of arXiv:0911.1696: a `k`-QSAT instance of projectors of
rank at most `r` in which every qubit appears in at most `2 ^ k / (e * r * k)`
projectors is satisfiable.

## Design

The paper works in `⨂ i, H i`. We avoid `PiTensorProduct` entirely by using the
configuration model: the state space of `n` qubits is the space of functions
from bit strings to `ℂ`,
``
H n = (Fin n → Fin 2) → ℂ
``
which is *the same* finite dimensional space, but with locality expressed as an
explicit bipartition of the index type rather than as a tensor factorisation.
Every dimension is then a cardinality.

A constraint supported on a set `S` of qubits is a subspace of the form
`lift S Y`: those `f` all of whose `S`-slices lie in `Y`. This is the
configuration-model description of `Y ⊗ (everything else)`.

## Main results

* `IsSupportedOn.mono` : support is monotone in the set of qubits.
* `finrank_inf_liftL_liftR` : the product rule `dim (U ⊗ W) = dim U * dim W`, in
  the configuration model.
* `relDim_inf_of_isSupportedOn_compl` : a subspace cut out on `S` and one cut out
  on `Sᶜ` are R-independent. This is the crux of the paper's Lemma 11.
* `mutuallyIndepOn_of_isSupportedOn` : Lemma 11, mutual R-independence.
* `inf_ne_bot_of_degree_le`, `inf_lift_ne_bot` : Corollary 16.
-/

namespace QLLL.QSAT

open Finset Module

variable {n : ℕ}

@[simp] theorem lift_top (S : Finset (Fin n)) : lift S ⊤ = ⊤ := by
  simp [lift]

theorem lift_inf (S : Finset (Fin n)) (Y Z : Submodule ℂ (HIn S)) :
    lift S Y ⊓ lift S Z = lift S (Y ⊓ Z) := by
  simp only [lift, Submodule.comap_inf]
  refine le_antisymm (le_iInf fun b => ?_)
    (le_inf (le_iInf fun b => ?_) (le_iInf fun b => ?_))
  · exact le_inf (inf_le_left.trans (iInf_le _ b)) (inf_le_right.trans (iInf_le _ b))
  · exact (iInf_le _ b).trans inf_le_left
  · exact (iInf_le _ b).trans inf_le_right

theorem isSupportedOn_top (S : Finset (Fin n)) : IsSupportedOn S (⊤ : Submodule ℂ (H n)) :=
  ⟨⊤, (lift_top S).symm⟩

theorem IsSupportedOn.inf {S : Finset (Fin n)} {P Q : Submodule ℂ (H n)}
    (hP : IsSupportedOn S P) (hQ : IsSupportedOn S Q) : IsSupportedOn S (P ⊓ Q) := by
  obtain ⟨Y, rfl⟩ := hP
  obtain ⟨Z, rfl⟩ := hQ
  exact ⟨Y ⊓ Z, lift_inf S Y Z⟩

/-! ### Support is monotone

Enlarging the set of qubits. If `S ⊆ T`, a `T`-configuration splits into its
`S`-part and its `T \ S`-part, and a configuration outside `S` splits into its
`T \ S`-part and its part outside `T`. Slicing at `S` therefore factors as
slicing at `T` followed by a relative slice, which is all that is needed. -/

theorem exists_combOut_eq {S T : Finset (Fin n)} (hST : S ⊆ T) (b : CfgOut S) :
    ∃ (d : CfgMid S T) (c : CfgOut T), combOut d c = b := by
  refine ⟨fun i => b ⟨i.1, i.2.2⟩, fun i => b ⟨i.1, fun h => i.2 (hST h)⟩, ?_⟩
  funext i
  by_cases h : i.1 ∈ T <;> simp [combOut, h]

theorem cfgEquiv_symm_combIn {S T : Finset (Fin n)} (hST : S ⊆ T) (a : CfgIn S)
    (d : CfgMid S T) (c : CfgOut T) :
    (cfgEquiv T).symm (combIn a d, c) = (cfgEquiv S).symm (a, combOut d c) := by
  funext i
  by_cases hiS : i ∈ S
  · have hiT : i ∈ T := hST hiS
    simp [cfgEquiv, Equiv.piEquivPiSubtypeProd, hiS, hiT, combIn]
  · by_cases hiT : i ∈ T
    · simp [cfgEquiv, Equiv.piEquivPiSubtypeProd, hiS, hiT, combIn, combOut]
    · simp [cfgEquiv, Equiv.piEquivPiSubtypeProd, hiS, hiT, combOut]

theorem relSlice_sliceMap {S T : Finset (Fin n)} (hST : S ⊆ T) (d : CfgMid S T)
    (c : CfgOut T) (f : H n) :
    relSlice d (sliceMap T c f) = sliceMap S (combOut d c) f := by
  funext a
  simp only [relSlice, sliceMap, LinearMap.funLeft_apply]
  rw [cfgEquiv_symm_combIn hST]

/-- Support is monotone: a constraint on `S` is in particular a constraint on
any larger set of qubits. -/
theorem IsSupportedOn.mono {S T : Finset (Fin n)} {P : Submodule ℂ (H n)}
    (hST : S ⊆ T) (hP : IsSupportedOn S P) : IsSupportedOn T P := by
  obtain ⟨Y, rfl⟩ := hP
  refine ⟨⨅ d : CfgMid S T, Submodule.comap (relSlice d) Y, ?_⟩
  ext f
  simp only [lift, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h c d
    rw [relSlice_sliceMap hST]
    exact h _
  · intro h b
    obtain ⟨d, c, rfl⟩ := exists_combOut_eq hST b
    have hcd := h c d
    rwa [relSlice_sliceMap hST] at hcd

/-- An intersection over a finite index set of subspaces supported on `S` is
supported on `S`. -/
theorem isSupportedOn_finsetInf {S : Finset (Fin n)} {ι : Type*}
    (P : ι → Submodule ℂ (H n)) (T : Finset ι)
    (hP : ∀ i ∈ T, IsSupportedOn S (P i)) : IsSupportedOn S (T.inf P) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using isSupportedOn_top S
  | @insert j T' hj ih =>
    rw [Finset.inf_insert]
    exact (hP j (Finset.mem_insert_self j T')).inf
      (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

/-! ## The crux, in Kronecker form

Locality in the configuration model is a Kronecker product: reindexing
`Cfg n ≃ CfgIn S × CfgOut S` turns an operator supported on `S` into a matrix of
the form `p ⊗ₖ 1`, and one supported on `Sᶜ` into `1 ⊗ₖ q`. The dimension count
behind the paper's Lemma 11 then reduces to Kronecker algebra, all of which is
already in Mathlib: `Matrix.mul_kronecker_mul`, `Matrix.one_kronecker`,
`Matrix.trace_kronecker`.

This formulation supersedes an earlier one in terms of `Submodule.map₂`. It is
shorter because it needs exactly one fact Mathlib lacks, recorded below, rather
than a theory of product subspaces.

The same modelling convention (configurations, ground spaces as `Submodule`s,
local terms as orthogonal projectors via `Submodule.starProjection`) is used by
TNLean for parent Hamiltonians of matrix product states.
-/

section Crux

open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

end Crux

/-! ## The product rule for an abstract two-factor split

Stated for the concrete product index type `A × B`, so that it can be
instantiated at the splitting `Cfg n ≃ CfgIn S × CfgOut S` in either order.
-/

section Split

open scoped Kronecker

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem colSlice_apply (b : B) (f : (A × B) → ℂ) (a : A) :
    colSlice b f a = f (a, b) := rfl

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem rowSlice_apply (a : A) (f : (A × B) → ℂ) (b : B) :
    rowSlice a f b = f (a, b) := rfl

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem liftL_top :
    liftL (⊤ : Submodule ℂ (A → ℂ)) = (⊤ : Submodule ℂ ((A × B) → ℂ)) := by
  simp [liftL]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem liftR_top :
    liftR (⊤ : Submodule ℂ (B → ℂ)) = (⊤ : Submodule ℂ ((A × B) → ℂ)) := by
  simp [liftR]

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
theorem finrank_liftL [Finite A] (Y : Submodule ℂ (A → ℂ)) :
    Module.finrank ℂ (liftL Y : Submodule ℂ ((A × B) → ℂ))
      = Module.finrank ℂ Y * Fintype.card B := by
  have h := finrank_inf_liftL_liftR Y (⊤ : Submodule ℂ (B → ℂ))
  rw [liftR_top, inf_top_eq] at h
  rw [h, finrank_top, Module.finrank_fintype_fun_eq_card]

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem finrank_liftR [Finite B] (W : Submodule ℂ (B → ℂ)) :
    Module.finrank ℂ (liftR W : Submodule ℂ ((A × B) → ℂ))
      = Fintype.card A * Module.finrank ℂ W := by
  have h := finrank_inf_liftL_liftR (⊤ : Submodule ℂ (A → ℂ)) W
  rw [liftL_top, top_inf_eq] at h
  rw [h, finrank_top, Module.finrank_fintype_fun_eq_card]

end Split

/-! ## Transporting the product rule to the qubit splitting -/

section Transport

variable {n : ℕ} {S : Finset (Fin n)}

theorem splitEquiv_apply (g : (CfgIn S × CfgOut S) → ℂ) (c : Cfg n) :
    splitEquiv S g c = g (cfgEquiv S c) := rfl

theorem sliceMap_splitEquiv (b : CfgOut S) (g : (CfgIn S × CfgOut S) → ℂ) :
    sliceMap S b (splitEquiv S g) = colSlice b g := by
  funext a
  simp only [sliceMap, LinearMap.funLeft_apply, splitEquiv_apply, Equiv.apply_symm_apply,
    colSlice_apply]

theorem comap_splitEquiv_lift (Y : Submodule ℂ (HIn S)) :
    Submodule.comap (splitEquiv S : ((CfgIn S × CfgOut S) → ℂ) →ₗ[ℂ] H n) (lift S Y)
      = liftL Y := by
  ext g
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, lift, liftL, Submodule.mem_iInf,
    Submodule.mem_comap]
  constructor
  · intro h b
    rw [← sliceMap_splitEquiv]
    exact h b
  · intro h b
    rw [sliceMap_splitEquiv]
    exact h b

theorem finrank_H (n : ℕ) (S : Finset (Fin n)) :
    Module.finrank ℂ (H n) = Fintype.card (CfgIn S) * Fintype.card (CfgOut S) := by
  rw [Module.finrank_fintype_fun_eq_card, ← Fintype.card_prod]
  exact Fintype.card_congr (cfgEquiv S)

/-! ### The complementary side

`CfgOut S` and `CfgIn Sᶜ` carry the same data, as do `CfgIn S` and `CfgOut Sᶜ`,
so a subspace supported on `Sᶜ` is a right lift for the splitting at `S`. -/

theorem cfgEquiv_compl_symm (a : CfgIn Sᶜ) (b : CfgOut Sᶜ) :
    (cfgEquiv Sᶜ).symm (a, b)
      = (cfgEquiv S).symm (outComplEquivIn S b, inComplEquivOut S a) := by
  funext i
  by_cases hi : i ∈ S
  · have hi' : i ∉ Sᶜ := Finset.notMem_compl.mpr hi
    simp [cfgEquiv, Equiv.piEquivPiSubtypeProd, hi, outComplEquivIn]
  · have hi' : i ∈ Sᶜ := Finset.mem_compl.mpr hi
    simp [cfgEquiv, Equiv.piEquivPiSubtypeProd, hi, inComplEquivOut]

theorem sliceMap_compl_splitEquiv (b : CfgOut Sᶜ) (g : (CfgIn S × CfgOut S) → ℂ) :
    sliceMap Sᶜ b (splitEquiv S g)
      = LinearMap.funLeft ℂ ℂ (inComplEquivOut S) (rowSlice (outComplEquivIn S b) g) := by
  funext a
  simp only [sliceMap, LinearMap.funLeft_apply, splitEquiv_apply, cfgEquiv_compl_symm,
    Equiv.apply_symm_apply, rowSlice_apply]

theorem exists_liftR_of_isSupportedOn_compl {Q : Submodule ℂ (H n)}
    (hQ : IsSupportedOn Sᶜ Q) :
    ∃ W : Submodule ℂ (CfgOut S → ℂ),
      Submodule.comap (splitEquiv S : ((CfgIn S × CfgOut S) → ℂ) →ₗ[ℂ] H n) Q
        = liftR W := by
  obtain ⟨W', rfl⟩ := hQ
  refine ⟨Submodule.comap
    ((LinearEquiv.funCongrLeft ℂ ℂ (inComplEquivOut S) :
      (CfgOut S → ℂ) ≃ₗ[ℂ] (CfgIn Sᶜ → ℂ)) : (CfgOut S → ℂ) →ₗ[ℂ] (CfgIn Sᶜ → ℂ)) W', ?_⟩
  ext g
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, lift, liftR, Submodule.mem_iInf,
    Submodule.mem_comap, LinearEquiv.funCongrLeft_apply]
  constructor
  · intro h a'
    have hb := h ((outComplEquivIn S).symm a')
    rwa [sliceMap_compl_splitEquiv, Equiv.apply_symm_apply] at hb
  · intro h b
    rw [sliceMap_compl_splitEquiv]
    exact h _

theorem finrank_comap_splitEquiv (P : Submodule ℂ (H n)) :
    Module.finrank ℂ
        (Submodule.comap (splitEquiv S : ((CfgIn S × CfgOut S) → ℂ) →ₗ[ℂ] H n) P)
      = Module.finrank ℂ P := by
  rw [Submodule.comap_equiv_eq_map_symm]
  exact ((splitEquiv S).symm.submoduleMap P).finrank_eq.symm

end Transport

/-- **The crux.** A subspace cut out on `S` and a subspace cut out on `Sᶜ` are
R-independent. This is the configuration-model form of the tensor product step
in the paper's Lemma 11: in tensor language it says
`dim ((U ⊗ B) ⊓ (A ⊗ W)) = dim U * dim W`.

Mathlib knows `Module.finrank_tensorProduct` but has no lattice theory for
subspaces of the form `U ⊗ B` inside `A ⊗ B`, so this has to be built. -/
theorem relDim_inf_of_isSupportedOn_compl {S : Finset (Fin n)}
    {P Q : Submodule ℂ (H n)} (hP : IsSupportedOn S P) (hQ : IsSupportedOn Sᶜ Q) :
    relDim (P ⊓ Q) = relDim P * relDim Q := by
  obtain ⟨Y, rfl⟩ := hP
  obtain ⟨W, hWeq⟩ := exists_liftR_of_isSupportedOn_compl hQ
  have hP' := finrank_comap_splitEquiv (S := S) (lift S Y)
  rw [comap_splitEquiv_lift, finrank_liftL] at hP'
  have hQ' := finrank_comap_splitEquiv (S := S) Q
  rw [hWeq, finrank_liftR] at hQ'
  have hPQ := finrank_comap_splitEquiv (S := S) (lift S Y ⊓ Q)
  rw [Submodule.comap_inf, comap_splitEquiv_lift, hWeq, finrank_inf_liftL_liftR] at hPQ
  have hcA : (Fintype.card (CfgIn S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (CfgIn S) := Fintype.card_pos
    positivity
  have hcB : (Fintype.card (CfgOut S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (CfgOut S) := Fintype.card_pos
    positivity
  simp only [relDim, ← hP', ← hQ', ← hPQ, finrank_H n S]
  push_cast
  field_simp

/-- **Lemma 11.** A constraint supported on `S` is mutually R-independent of any
family of constraints supported away from `S`. -/
theorem mutuallyIndepOn_of_isSupportedOn {S : Finset (Fin n)}
    {P : Submodule ℂ (H n)} (hP : IsSupportedOn S P) {ι : Type*}
    (Y : ι → Submodule ℂ (H n)) (T : Finset ι)
    (hY : ∀ i ∈ T, ∃ Sᵢ : Finset (Fin n), Sᵢ ⊆ Sᶜ ∧ IsSupportedOn Sᵢ (Y i)) :
    (relDimValuation (𝕜 := ℂ) (V := H n)).MutuallyIndepOn P Y T := by
  intro T' hT'
  have hQ : IsSupportedOn Sᶜ (T'.inf Y) := by
    refine isSupportedOn_finsetInf Y T' fun i hi => ?_
    obtain ⟨Sᵢ, hsub, hsupp⟩ := hY i (hT' hi)
    exact hsupp.mono hsub
  exact relDim_inf_of_isSupportedOn_compl hP hQ

/-! ## Corollary 16: k-QSAT

The combinatorial half is identical to the classical case in `QuantumLocalLemma.Classical.KSAT`:
constraints on `k` qubits each, every qubit touched by at most `D` constraints,
so each constraint overlaps at most `k (D - 1)` others.
-/

/-- A constraint on `k` qubits overlaps at most `k * D'` others, when every
qubit is touched by at most `D' + 1` constraints. -/
theorem card_overlap_le {m : ℕ} (Sq : Fin m → Finset (Fin n)) (k D' : ℕ)
    (hcard : ∀ i, (Sq i).card = k)
    (hdeg : ∀ v : Fin n, (univ.filter fun i => v ∈ Sq i).card ≤ D' + 1) (i : Fin m) :
    (univ.filter fun j => j ≠ i ∧ (Sq i ∩ Sq j).Nonempty).card ≤ k * D' := by
  classical
  have hsub : (univ.filter fun j => j ≠ i ∧ (Sq i ∩ Sq j).Nonempty)
      ⊆ (Sq i).biUnion fun v => (univ.filter fun j : Fin m => v ∈ Sq j).erase i := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hji, v, hv⟩ := hj
    rw [Finset.mem_inter] at hv
    exact Finset.mem_biUnion.mpr ⟨v, hv.1, Finset.mem_erase.mpr ⟨hji,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2⟩⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  calc ∑ v ∈ Sq i, ((univ.filter fun j : Fin m => v ∈ Sq j).erase i).card
      ≤ ∑ _v ∈ Sq i, D' := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hi : i ∈ univ.filter fun j : Fin m => v ∈ Sq j :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        rw [Finset.card_erase_of_mem hi]
        have := hdeg v
        omega
    _ = (Sq i).card * D' := by rw [Finset.sum_const, smul_eq_mul]
    _ = k * D' := by rw [hcard i]

end QLLL.QSAT


section

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}

theorem solution {m : ℕ} {Sq : Fin m → Finset (Fin n)}
    {X : Fin m → Submodule ℂ (H n)} {k D' : ℕ} {p : ℝ}
    (hsupp : ∀ i, IsSupportedOn (Sq i) (X i))
    (hcard : ∀ i, (Sq i).card = k)
    (hX : ∀ i, 1 - p ≤ relDim (X i))
    (hdeg : ∀ v : Fin n, (univ.filter fun i => v ∈ Sq i).card ≤ D' + 1)
    (hp : p * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    univ.inf X ≠ ⊥ := by
  classical
  set Γ : Fin m → Finset (Fin m) := fun i =>
    univ.filter fun j => j ≠ i ∧ (Sq i ∩ Sq j).Nonempty with hΓ
  have hdep : (relDimValuation (𝕜 := ℂ) (V := H n)).IsDependencyGraph X Γ := by
    intro i
    refine mutuallyIndepOn_of_isSupportedOn (hsupp i) X _ ?_
    intro j hj
    refine ⟨Sq j, ?_, hsupp j⟩
    rw [Finset.mem_erase, Finset.mem_sdiff] at hj
    obtain ⟨hji, -, hjΓ⟩ := hj
    simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hjΓ
    have hempty := hjΓ hji
    intro v hv
    rw [Finset.mem_compl]
    intro hvi
    exact hempty ⟨v, Finset.mem_inter.mpr ⟨hvi, hv⟩⟩
  have hdegΓ : ∀ i, (Γ i).card ≤ k * D' := fun i =>
    card_overlap_le Sq k D' hcard hdeg i
  have hpos := Valuation.lll_symmetric (relDimValuation (𝕜 := ℂ) (V := H n))
    hdep hdegΓ hX hp
  intro hbot
  rw [hbot, (relDimValuation (𝕜 := ℂ) (V := H n)).map_bot'] at hpos
  exact lt_irrefl 0 hpos

end
