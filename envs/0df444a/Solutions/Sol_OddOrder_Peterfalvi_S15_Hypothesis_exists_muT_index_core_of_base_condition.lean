-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.exists_muT_index_core_of_base_condition
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:01:39.625509+00:00
-- url     : https://prove2.me/submissions/1ab13142-6f2e-4ab3-8ee5-e2b5f44cceec

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_Building78C.lean
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorBasic.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_Tau1T.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_sharp_tau_eq_induce
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_K_mem_zSpan_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_K_mem_zSpan_sSet_irr_T

-- ===== OddOrder/Peterfalvi/S09_Building78C.lean =====
namespace OddOrder.Peterfalvi.S09.Cert

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L]

/-- **The chosen-base normalization pins `ζ₀ = Ind_H^L φ₀`.** -/
theorem hypothesis76OfDadeBase_zeta_zero
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    (φ₀ :
      haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
      IrreducibleCharacter ↥(H.subgroupOf L)) :
    haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    (hypothesis76OfDadeBase H71 hτ H hHL hHnorm hAH φ₀).zeta 0
      = ClassFunction.induce (H.subgroupOf L) (φ₀ : ClassFunction ↥(H.subgroupOf L) ℂ) := by
  have hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  let : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  unfold hypothesis76OfDadeBase hypothesis76OfFamily
  dsimp only
  rw [Equiv.swap_apply_left]
  have h := Classical.choose_spec ((distinctInducedFamily (H.subgroupOf L)).cover φ₀)
  dsimp only at h
  exact h

end OddOrder.Peterfalvi.S09.Cert

-- ===== OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorBasic.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

theorem mem_sSet [Finite G] {data : TypesIIIIIIVSetup M} {φ : ClassFunction ↥M ℂ} :
    φ ∈ sSet data ↔ ∃ χ ∈ xiSet data, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S15_CaseACoherence.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

set_option linter.unusedFintypeInType false in
/-- **Constituent kernel step for (1.5.a)** (Coq `S1cases` inner kernel argument), stated
generically.  For subgroups `P0, K'` of a finite group `Γ`, an irreducible `s ∈ Irr(Γ)`, and an
irreducible `θ'` of `K'` with `P0.subgroupOf K' ⊄ ker θ'`: if `θ'` is a constituent of
`Res_{K'} s` (`⟨θ', Res_{K'} s⟩ ≠ 0`), then `P0 ⊄ ker s`.

**Contrapositive.**  `P0 ⊆ ker s` makes `Res_{K'} s` trivial on `P0.subgroupOf K'`
(`characterKernel_restrict_subgroupOf`); `θ'`, a constituent of the genuine character `Res_{K'} s`
(`isCharacter_restrict`), inherits the containment
(`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), so `P0.subgroupOf K' ⊆ ker θ'`,
contradicting the hypothesis.  This is the `S`-instance analogue of the leaf
`PrimeTIResidue.constituent_P_not_subset_ker`, grounded on the honest `S'`-family — no
`PrimeTIResidueData` and no prime-TI dichotomy is used. -/
theorem constituent_P_not_subset_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] (P0 K' : Subgroup Γ) [Fintype ↥K']
    [Invertible (Nat.card ↥K' : ℂ)]
    (θ' : ClassFunction ↥K' ℂ)
    (hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ'P : ¬ ((P0.subgroupOf K' : Set ↥K') ⊆ OddOrder.Peterfalvi.S03.characterKernel θ'))
    (s : OddOrder.RepresentationTheory.IrreducibleCharacter Γ)
    (hs : ClassFunction.inner θ' (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) ≠ 0) :
    ¬ ((P0 : Set Γ) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction Γ ℂ)) := by
  intro hker
  have hResChar : IsCharacter (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter K'
  have hinner' : ClassFunction.inner
      (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) θ' ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    exact star_ne_zero.mpr hs
  have hResker : ((P0.subgroupOf K') : Set ↥K') ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf K' hker
  exact hθ'P fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hθ'irr hinner' (hResker hx)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_Tau1T.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c)-at-`T`, the ν-row formula for `τ₁T = tau1T_ofHonest`** (mirror of
`tau1S_ofHonest_muColumn_formula`; Coq `FTtypeP_coherence` with `typeP_TIred_coherent`'s
global-sign disjunction, transposed): the (9.11)-`T` coherent extension sends every reducible
ν-row sum `ν_i = ∑_j ν_{ij}` (`i ≠ 0`) to the aligned `η`-row sum `∑_j η_{ij}` — either
uniformly, or (the `q = 3` sign-flip exception) with a global negative sign and the two nonzero
rows swapped.  The `.choose_spec` of the pinned carrier. -/
theorem Hypothesis.tau1T_ofHonest_nuRow_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = ∑ j : Fin hyp.p, hyp.eta i j) ∨
    (hyp.q = 3 ∧ ∀ i i' : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      i' ≠ ⟨0, hyp.q_prime.pos⟩ → i ≠ i' →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = -∑ j : Fin hyp.p, hyp.eta i' j) :=
  (hyp.sSet_coherent_indT_A_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief).choose_spec

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁T = Ind_T^G` on the `A(T)`-supported span** (mirror of
`tau1S_ofHonest_extends_on_supported`; the (13.2.e) agreement, the conjunct-3 producer of the
(13.4) θ-package): the coherent extension agrees with plain induction on every `A(T)`-supported
lattice element of `ℤ[𝒯]`. -/
theorem Hypothesis.tau1T_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (φ : ClassFunction ↥hyp.T ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) :
    hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief φ
      = ClassFunction.induce hyp.T φ := by
  have h := (hyp.coherentIndT_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2
    chief).extends_on_supported φ hφ
  simpa [Hypothesis.tau1T_ofHonest, Hypothesis.indT_apply] using h

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.3.b)-at-`T` for `τ₁T = tau1T_ofHonest`** (the conjunct-4 producer of the (13.4)
θ-package): the `τ₁T`-image of an irreducible `𝒯`-member is orthogonal to the entire `η`-grid.
The engine `coherentIndT_image_inner_eta_eq_zero` instantiated at the pinned carrier, with the
family inputs discharged from the landed `𝒯`-facts (conjugate-closure, no-real via `|T|` odd,
conjugate-difference `A(T)`-support). -/
theorem Hypothesis.tau1T_ofHonest_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {ζ : ClassFunction ↥hyp.T ℂ} (hζ : ζ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief ζ)
        (hyp.eta i j) = 0 :=
  coherentIndT_image_inner_eta_eq_zero hG hnoV hyp hTP Tdata hW1 hW2
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd))
    (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG))
    (fun ζ' hζ' => by
      rw [show ζ' - ζ'.conj = -(ζ'.conj - ζ') from by abel, ClassFunction.support_neg]
      exact hyp.sSet_member_conjDiff_supported_T hG hvd hζ')
    (hyp.coherentIndT_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief) hζ hζirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`ℤ[𝒯]`-elements are supported in `A(T) ∪ {1}`** (mirror of `zSpan_sSet_support_subset`):
the `zSpan`-closure of the member-level support fact `sSet_member_support_subset_T`. -/
theorem Hypothesis.zSpan_sSet_support_subset_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T ∪ {1} := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hyp.sSet_member_support_subset_T hG hvd hx
  | zero => simp
  | add x y _ _ hx hy =>
      exact (ClassFunction.support_add_subset x y).trans (Set.union_subset hx hy)
  | smul z x _ hx =>
      refine subset_trans ?_ hx
      rw [← Int.cast_smul_eq_zsmul ℂ z x]
      exact ClassFunction.support_smul_subset _ x

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Degree-`0` elements of `ℤ[𝒯]` are `A(T)`-supported** (mirror of
`zSpan_sSet_degree_zero_support`; the (13.2.e)-input support step for the
`tau1T_apply_induce_sub` supply). -/
theorem Hypothesis.zSpan_sSet_degree_zero_support_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)))
    (hφ1 : φ (1 : ↥hyp.T) = 0) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  intro z hz
  rcases hyp.zSpan_sSet_support_subset_T hG hvd hφ hz with h | h
  · exact h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact absurd hφ1 hz

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁T`-images of `ℤ[𝒯 ∩ Irr T]` are orthogonal to the `η`-grid** (mirror of
`tau1S_ofHonest_zSpanIrr_inner_eta`): span induction over the (5.3.b)-`T` crux. -/
theorem Hypothesis.tau1T_ofHonest_zSpanIrr_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (i : Fin hyp.q) (j : Fin hyp.p)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) ∧
        OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ}) :
    ClassFunction.inner
      (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief φ)
      (hyp.eta i j) = 0 := by
  have := hyp.finiteG
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      exact hyp.tau1T_ofHonest_image_inner_eta_eq_zero hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief hζ.1 hζ.2 i j
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(4.1)+(5.3.b) conjunct-4 producer for the (13.4) θ-package** (mirror of
`tau1S_ofHonest_induce_inner_eta`): for an irreducible `θ` on `K = QD` (`Q ⊄ Ker θ`) whose
induction `Ind_K^T θ` is irreducible, the `τ₁T`-image is orthogonal to the whole `η`-grid.
Composition of the `ℤ[𝒯 ∩ Irr T]` membership (`induce_K_mem_zSpan_sSet_irr_T`) with the
span-level grid orthogonality (`tau1T_ofHonest_zSpanIrr_inner_eta`). -/
theorem Hypothesis.tau1T_ofHonest_induce_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (i : Fin hyp.q) (j : Fin hyp.p)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) :
    ClassFunction.inner (hyp.eta i j)
      (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) = 0 := by
  have := hyp.finiteG
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1T_ofHonest_zSpanIrr_inner_eta hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief i j
      (hyp.induce_K_mem_zSpan_sSet_irr_T hG pins hvd θ hθ hθQ hind),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.2.e) conjunct-3 producer for the (13.4) θ-package** (mirror of
`tau1S_ofHonest_apply_induce_sub`, with the degree-`1` hypotheses explicit instead of routing
through `K`-commutativity): for degree-one irreducibles `θ, θ'` on `K = QD` with `Q ⊄ Ker`
both, `τ₁T` agrees with `Ind_T^G` on the difference `Ind_K θ − Ind_K θ'`.  Both inductions lie
in `ℤ[𝒯]` (`induce_K_mem_zSpan_T`); the difference vanishes at `1` (equal degrees `[T:K]`), so
it is `A(T)`-supported (`zSpan_sSet_degree_zero_support_T`) and `extends_on_supported`
evaluates `τ₁T` as `Ind_T^G` there. -/
theorem Hypothesis.tau1T_ofHonest_apply_induce_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (θ θ' : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ1 : θ 1 = 1) (hθ'1 : θ' 1 = 1)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'Q : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
          - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ')
      = ClassFunction.induce hyp.T
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
            - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ') := by
  have := hyp.finiteG
  have hmem := hyp.induce_K_mem_zSpan_T hG hvd θ hθ hθQ
  have hmem' := hyp.induce_K_mem_zSpan_T hG hvd θ' hθ' hθ'Q
  have hsub : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
      ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :=
    Submodule.sub_mem _ hmem hmem'
  have hdeg : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ') (1 : ↥hyp.T) = 0 := by
    rw [ClassFunction.sub_apply,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, hθ'1, sub_self]
  exact hyp.tau1T_ofHonest_extends_on_supported hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief _
    ⟨hsub, hyp.zSpan_sSet_degree_zero_support_T hG hvd hsub hdeg⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The chosen-base `(T, Q^#)` family pins `ζ₀ = Ind_Q^T φ₀`** (mirror of
`H_sharp_hypothesis76_base_zeta_zero`). -/
theorem Q_sharp_hypothesis76_base_zeta_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
    (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta 0
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
  unfold Q_sharp_hypothesis76_base
  exact OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase_zeta_zero _ _ _ _ _ _ _

set_option maxHeartbeats 1600000 in
-- The (7.6)-family bookkeeping (constituent expansion + per-index coefficient computation)
-- elaborates as a single large proof term; the default budget covers only part of it.
open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side (13.3.c) distinguished index over a chosen base, general form**
(Peterfalvi (13.8)-for-`T`, issue 0116):
with the (7.6) family `Q_sharp_hypothesis76_base` based at `ζ₀ = Ind_Q^T φ₀` (`Q ⊄ Ker φ₀`,
and either `Ind φ₀` irreducible or its `η₁₀` coefficient zero), under `D = ⊥` (so
`K = QD = Q`) there is a family index `i₁` carrying a
ν-row (`ζ_{i₁} = ν_r = ∑_j ν_{rj}`) with `⟨τψ_{i₁}, η₁₀⟩ = δ = ±1`, and every other
`Q`-nonkernel coefficient vanishes; `‖ζ_{i₁}‖² = p` and `ζ_{i₁}(1) = pv`.

Lives here (not `S15_Tau1T`) because `Q_sharp_hypothesis76_base` is declared in this file,
which imports `S15_Tau1T` (the reverse import would be a cycle).  The commutativity of `Q`
(the abelian half of the (13.2.b)-for-`T` `Q_elementaryAbelian`, constructed from the general
type-`P` chief-factor collapse) enters as the explicit input `hQcomm`: it pins the
family degrees (`ζ_i(1) = [T:Q]`, so `d ≡ 1`) and the degree-one hypotheses of the (13.2.e)
bridge `tau1T_ofHonest_apply_induce_sub`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T))
    (hφ₀Q : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
        Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)))
    (hφ₀base :
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∨
        ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
              (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0) :
    ∃ (i₁ : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1)) (δ : ℤ), 0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1 = ((hyp.p * hyp.v : ℕ) : ℂ) := by
  classical
  set data := hyp.toTypesIIIIIIVSetupT hG hvd with hdata
  set HU : Subgroup ↥hyp.T := huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.T).subgroupOf hyp.T :=
    huSub_eq_derivedInG_subgroupOf data
  have hHUnorm : HU.Normal := huSub_normal data
  -- Subgroup bookkeeping: `Q ≤ T`, `Q.subgroupOf T` normal & abelian, `K = QD = Q` (`hD`),
  -- `Q ≤ T' = HU`.
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hQnorm : (hyp.Q.subgroupOf hyp.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr (by
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  have hQsubComm : IsMulCommutative ↥(hyp.Q.subgroupOf hyp.T) := by
    have e := Subgroup.subgroupOfEquivOfLe hQT
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hQcomm.is_comm.comm (e a) (e b))⟩⟩
  have hKQ : hyp.K.subgroupOf hyp.T = hyp.Q.subgroupOf hyp.T := by
    have h : hyp.K = hyp.Q := by
      change hyp.Q ⊔ hyp.D = hyp.Q
      rw [hD, sup_bot_eq]
    rw [h]
  have hQle : hyp.Q.subgroupOf hyp.T ≤ HU := by
    rw [hHUeq]
    refine Subgroup.subgroupOf_mono hyp.T ?_
    rw [hyp.T_deriv_eq_QV]
    exact le_sup_left
  -- degree-one values on `Irr (Q.subgroupOf T)` (from `hQcomm`)
  have hdeg1 : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ → θ 1 = 1 := fun _ hθ =>
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ
  -- η-row inner products against `η₁₀`
  have hetaRow : ∀ a : Fin hyp.q,
      ClassFunction.inner (∑ j : Fin hyp.p, hyp.eta a j) hyp.eta10
        = if a = ⟨1, hyp.q_prime.one_lt⟩ then 1 else 0 := by
    intro a
    rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ from rfl,
      OddOrder.RepresentationTheory.inner_sum_left]
    by_cases ha : a = ⟨1, hyp.q_prime.one_lt⟩
    · rw [if_pos ha,
        Finset.sum_eq_single_of_mem ⟨0, hyp.p_prime.pos⟩ (Finset.mem_univ _)
          (fun j _ hj => by
            rw [hyp.eta_orthonormal a ⟨1, hyp.q_prime.one_lt⟩ j ⟨0, hyp.p_prime.pos⟩,
              if_neg (fun h => hj h.2)]),
        hyp.eta_orthonormal a ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩,
        if_pos ⟨ha, rfl⟩]
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hyp.eta_orthonormal a ⟨1, hyp.q_prime.one_lt⟩ j ⟨0, hyp.p_prime.pos⟩,
        if_neg (fun h => ha h.1)]
  -- the pinned (13.3.c)-`T` row: a nonzero row `r` and a sign `δ = ±1` with
  -- `⟨τ₁T(ν_r), η₁₀⟩ = δ`, all other nonzero rows `τ₁T`-orthogonal to `η₁₀`
  obtain ⟨r, δ, hr0, hδpm, hkeyr, hkey⟩ :
      ∃ (r : Fin hyp.q) (δ : ℤ), r ≠ ⟨0, hyp.q_prime.pos⟩ ∧ (δ = 1 ∨ δ = -1) ∧
        ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (∑ j : Fin hyp.p, hyp.nu r j)) hyp.eta10 = (δ : ℂ) ∧
        ∀ s : Fin hyp.q, s ≠ ⟨0, hyp.q_prime.pos⟩ → s ≠ r →
          ClassFunction.inner
            (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
              (∑ j : Fin hyp.p, hyp.nu s j)) hyp.eta10 = 0 := by
    have h1q : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) one_ne_zero
    rcases hyp.tau1T_ofHonest_nuRow_formula hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief with
      hclean | ⟨hq3, hflip⟩
    · -- clean branch: `r = 1`, `δ = 1`
      refine ⟨⟨1, hyp.q_prime.one_lt⟩, 1, h1q, Or.inl rfl, ?_, ?_⟩
      · rw [hclean ⟨1, hyp.q_prime.one_lt⟩ h1q, hetaRow, if_pos rfl]
        norm_num
      · intro s hs0 hsr
        rw [hclean s hs0, hetaRow, if_neg hsr]
    · -- `q = 3` sign-flip branch: `r = 2`, `δ = −1` (row 2 flips onto η-row 1)
      have h2lt : 2 < hyp.q := by omega
      have h2q : (⟨2, h2lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
        intro h
        exact absurd (congrArg Fin.val h) (by norm_num)
      have h21 : (⟨2, h2lt⟩ : Fin hyp.q) ≠ ⟨1, hyp.q_prime.one_lt⟩ := by
        intro h
        exact absurd (congrArg Fin.val h) (by norm_num)
      refine ⟨⟨2, h2lt⟩, -1, h2q, Or.inr rfl, ?_, ?_⟩
      · rw [hflip ⟨2, h2lt⟩ ⟨1, hyp.q_prime.one_lt⟩ h2q h1q h21,
          ClassFunction.inner_neg_left, hetaRow, if_pos rfl]
        norm_num
      · intro s hs0 hsr
        have hs1 : s = ⟨1, hyp.q_prime.one_lt⟩ := by
          have hlt := s.isLt
          have hv0 : s.val ≠ 0 := fun h => hs0 (Fin.ext h)
          have hv2 : s.val ≠ 2 := fun h => hsr (Fin.ext h)
          have hv1 : s.val = 1 := by omega
          exact Fin.ext hv1
        subst hs1
        rw [hflip ⟨1, hyp.q_prime.one_lt⟩ ⟨2, h2lt⟩ h1q h2q (fun h => h21 h.symm),
          ClassFunction.inner_neg_left, hetaRow, if_neg h21, neg_zero]
  -- (13.3.a)-at-`T`: `ν_r = Ind_K^T θ_r`, transported to the `Q`-spelling via `K = Q`
  obtain ⟨θr, hθrirr, hθr1, hνeqK⟩ := hyp.nu_i_isIndQD hG pins r hr0
  set θrQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKQ.symm).toMonoidHom θr with hθrQdef
  have hθrQirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θrQ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKQ.symm).surjective hθrirr
  have hνeqQ : (∑ j : Fin hyp.p, hyp.nu r j)
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θrQ := by
    rw [hνeqK]
    exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ.symm θr).symm
  have hνmem : (∑ j : Fin hyp.p, hyp.nu r j) ∈ sSet data :=
    sOf_subset_sSet data chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief r hr0)
  -- `Q ⊄ Ker ν_r`: the `𝒳`-source witness survives kernel descent through `HU ⊴ T`
  have hQkerNu : ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (∑ j : Fin hyp.p, hyp.nu r j)) := by
    intro hsub
    obtain ⟨ξ, hξ, hξeq⟩ := hνmem
    have hξker : ¬ ((hInHu data : Set ↥HU) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (ξ : ClassFunction ↥HU ℂ)) := hξ
    obtain ⟨x, hxIn, hxKer⟩ := Set.not_subset.mp hξker
    have hxQ : ((x : ↥hyp.T)) ∈ hyp.Q.subgroupOf hyp.T := by
      have h1 : ((x : ↥hyp.T)) ∈ data.H.subgroupOf hyp.T :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hxIn)
      rwa [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at h1
    have hxker2 : ((x : ↥hyp.T)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce HU (ξ : ClassFunction ↥HU ℂ)) := by
      have h2 := hsub hxQ
      rwa [hξeq, induceHU_eq_induce data] at h2
    have hdesc := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ξ.isIrreducible x.2 hxker2
    exact hxKer (by simpa using hdesc)
  -- full-group kernel negation for the transported source `θrQ`
  have hθrQfull : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
      Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θrQ) := by
    intro hker
    apply hQkerNu
    rw [hνeqQ]
    exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf le_rfl θrQ hker
  -- `Q`-spelled τ₁T bricks, transported through `K.subgroupOf T = Q.subgroupOf T`
  have himgQ : ((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T)).map
      (MulEquiv.subgroupCongr hKQ).toMonoidHom
      = (hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hkerK : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
          Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ)) := by
    intro θ hθ hcon
    rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff, himgQ] at hcon
    exact hθ hcon
  have hbridgeQ : ∀ θ θ' : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ') →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
            - ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ')
        = ClassFunction.induce hyp.T
            (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
              - ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ') := by
    intro θ θ' hθirr hθ'irr hθQ hθ'Q
    have h := hyp.tau1T_ofHonest_apply_induce_sub hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ)
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ')
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.subgroupCongr hKQ).surjective hθirr)
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.subgroupCongr hKQ).surjective hθ'irr)
      (by rw [ClassFunction.compHom_apply, map_one, hdeg1 θ hθirr])
      (by rw [ClassFunction.compHom_apply, map_one, hdeg1 θ' hθ'irr])
      (hkerK θ hθQ) (hkerK θ' hθ'Q)
    rwa [OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ,
      OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ'] at h
  have hetaQbrick : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ) →
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)) hyp.eta10 = 0 := by
    intro θ hθirr hθQ hind
    have h := hyp.tau1T_ofHonest_induce_inner_eta hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ)
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.subgroupCongr hKQ).surjective hθirr)
      (hkerK θ hθQ)
      (by rwa [OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ])
    rw [OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ] at h
    rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ from rfl,
      OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  have hφ₀eta : ClassFunction.inner
      (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0 := by
    rcases hφ₀base with hφ₀irr | hφ₀orth
    · exact hetaQbrick (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)
        φ₀.isIrreducible hφ₀Q hφ₀irr
    · exact hφ₀orth
  -- distinct `Q`-inductions are orthogonal
  have hInd0 : ∀ θ ψ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.Q.subgroupOf hyp.T),
      ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (θ : ClassFunction _ ℂ)
          ≠ ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (ψ : ClassFunction _ ℂ) →
      ClassFunction.inner
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (θ : ClassFunction _ ℂ))
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (ψ : ClassFunction _ ℂ)) = 0 := by
    intro θ ψ hne
    refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ ψ
      (fun g heq => hne ?_)
    have h1 : ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
        ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g θ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
            ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (θ : ClassFunction _ ℂ) := by
      rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
      exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
        (G := ↥hyp.T) (H := hyp.Q.subgroupOf hyp.T) g _
    rw [← h1, heq]
  -- ⟨τ₁T(Ind_Q^T θ), η₁₀⟩ = 0 for every `Q`-nonkernel irreducible source with `Ind θ ≠ ν_r`:
  -- two-stage constituent expansion over `HU`, per-constituent (5.3.b)/(13.3.c) dispatch
  have hTau1IndEta : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ ≠ ∑ j : Fin hyp.p, hyp.nu r j →
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)) hyp.eta10 = 0 := by
    intro θ hθirr hθQ hθne
    -- transport onto `Q-in-HU`
    have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ) :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe hQle).surjective hθirr
    have hθ'Q : ¬ ((((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
          ((hyp.Q.subgroupOf hyp.T).subgroupOf HU) :
        Set ↥((hyp.Q.subgroupOf hyp.T).subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      have himg : (((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
            ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom
          = (hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]
      exact hθQ
    -- two-stage constituent expansion with `ℕ`-coefficients
    have hzeta : ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
        = ∑ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
            ClassFunction.inner
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)
              (ClassFunction.restrict ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
                (s : ClassFunction ↥HU ℂ))
              • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
      rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hQle θ,
        OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ),
        ClassFunction.induce_sum]
      exact Finset.sum_congr rfl fun s _ => ClassFunction.induce_smul _ _ _
    have hcoefNat : ∀ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, ∃ n : ℕ,
        ClassFunction.inner
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)
          (ClassFunction.restrict ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
            (s : ClassFunction ↥HU ℂ)) = (n : ℂ) := by
      intro s
      have hResChar : IsCharacter (ClassFunction.restrict
          ((hyp.Q.subgroupOf hyp.T).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
        OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
      obtain ⟨n, hn⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
      exact ⟨n, by rw [OddOrder.RepresentationTheory.inner_conj_symm, hn, star_natCast]⟩
    choose k hk using hcoefNat
    have hmem : ∀ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, k s ≠ 0 →
        ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈ sSet data := by
      intro s hks
      rw [mem_sSet]
      refine ⟨s, ?_, rfl⟩
      change ¬ ((hInHu data : Set ↥HU) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
      have hHInHu : (hInHu data : Set ↥HU)
          = ((hyp.Q.subgroupOf hyp.T).subgroupOf HU : Set ↥HU) := by
        congr 1
        change (data.H.subgroupOf hyp.T).subgroupOf HU
          = (hyp.Q.subgroupOf hyp.T).subgroupOf HU
        rw [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
      rw [hHInHu]
      have hs : ClassFunction.inner
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)
          (ClassFunction.restrict ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
            (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
        rw [hk s]
        exact_mod_cast hks
      exact constituent_P_not_subset_characterKernel ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
        ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ) hθ'irr hθ'Q s hs
    -- expand the τ₁T-image and dispatch per constituent
    have hzetaN : ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
        = ∑ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
            k s • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
      rw [hzeta]
      exact Finset.sum_congr rfl fun s _ => by rw [hk s, Nat.cast_smul_eq_nsmul]
    rw [hzetaN, map_sum, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun s _ => ?_
    rcases Nat.eq_zero_or_pos (k s) with hk0 | hkpos
    · rw [hk0, zero_smul, map_zero, ClassFunction.inner_zero_left]
    · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ (k s), ClassFunction.inner_smul_left]
      suffices hterm0 : ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))) hyp.eta10 = 0 by
        rw [hterm0, mul_zero]
      by_cases hsirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
          (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
      · -- irreducible constituent: (5.3.b)-`T` grid orthogonality
        exact hyp.tau1T_ofHonest_image_inner_eta_eq_zero hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief (hmem s hkpos.ne') hsirr ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      · -- reducible constituent: a nonzero ν-row `ν_{s₀}` with `s₀ ≠ r`
        obtain ⟨s₀, hs₀ne, heqrow⟩ :=
          hyp.sSet_reducible_eq_nuRowSum hG pins hvd (hmem s hkpos.ne') hsirr
        by_cases hs₀r : s₀ = r
        · -- `s₀ = r` would make `ν_r` a constituent of `Ind_Q θ`, contradicting
          -- `⟨Ind_Q θ, ν_r⟩ = 0` (distinct-source `Q`-inductions are orthogonal)
          exfalso
          subst hs₀r
          have hzmu : ClassFunction.inner (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)
              (∑ j : Fin hyp.p, hyp.nu s₀ j) = 0 := by
            rw [hνeqQ]
            exact hInd0 ⟨θ, hθirr⟩ ⟨θrQ, hθrQirr⟩ fun h => hθne (h.trans hνeqQ.symm)
          have hexp : ClassFunction.inner (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)
              (∑ j : Fin hyp.p, hyp.nu s₀ j)
              = ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, (k s' : ℂ) *
                  ClassFunction.inner (ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ))
                    (∑ j : Fin hyp.p, hyp.nu s₀ j) := by
            rw [hzeta, OddOrder.RepresentationTheory.inner_sum_left]
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [hk s', ClassFunction.inner_smul_left]
          have hterm : ∀ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, ∃ n : ℕ,
              (k s' : ℂ) * ClassFunction.inner
                (ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ))
                (∑ j : Fin hyp.p, hyp.nu s₀ j) = (n : ℂ) := by
            intro s'
            rcases Nat.eq_zero_or_pos (k s') with h0 | hpos
            · exact ⟨0, by rw [h0]; simp⟩
            · by_cases heq : ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ)
                  = ∑ j : Fin hyp.p, hyp.nu s₀ j
              · refine ⟨k s' * hyp.p, ?_⟩
                rw [heq, hyp.nuRow_inner pins s₀ s₀, if_pos rfl]
                push_cast
                ring
              · exact ⟨0, by rw [sSet_pairwiseOrthogonal data (hmem s' hpos.ne') hνmem heq,
                  mul_zero, Nat.cast_zero]⟩
          choose n hn using hterm
          have hsumC : ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
              ((n s' : ℕ) : ℂ) = 0 := by
            rw [Finset.sum_congr rfl fun s' _ => (hn s').symm, ← hexp, hzmu]
          have hsumN : ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
              n s' = 0 := by
            rw [← Nat.cast_sum] at hsumC
            exact_mod_cast hsumC
          have hn0 : n s = 0 := (Finset.sum_eq_zero_iff.mp hsumN) s (Finset.mem_univ s)
          have hcontra : ((n s : ℕ) : ℂ) ≠ 0 := by
            rw [← hn s, heqrow, hyp.nuRow_inner pins s₀ s₀, if_pos rfl]
            exact mul_ne_zero (Nat.cast_ne_zero.mpr hkpos.ne')
              (Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne')
          exact hcontra (by rw [hn0, Nat.cast_zero])
        · -- `s₀ ≠ r`: the pinned η-row inner product vanishes
          rw [heqrow]
          exact hkey s₀ hs₀ne hs₀r
  -- the distinguished family index: the family cover at the transported ν_r-source
  obtain ⟨i₁, hi₁0⟩ :=
    (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_family_cover ⟨θrQ, hθrQirr⟩
  have hζi₁ : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁
      = ∑ j : Fin hyp.p, hyp.nu r j := by
    rw [hi₁0, hνeqQ]
    congr!
  have hζ0 : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta 0
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) :=
    Q_sharp_hypothesis76_base_zeta_zero hG hyp hvd φ₀
  have hi₁pos : 0 < i₁ := by
    rw [Fin.pos_iff_ne_zero]
    intro h0
    have hbaseEq : (∑ j : Fin hyp.p, hyp.nu r j)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
      rw [← hζi₁, h0, hζ0]
    have hinnerEq := congrArg
      (fun χ : ClassFunction ↥hyp.T ℂ => ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief χ) hyp.eta10)
      hbaseEq
    rw [hkeyr, hφ₀eta] at hinnerEq
    rcases hδpm with hδ | hδ <;> rw [hδ] at hinnerEq <;> norm_num at hinnerEq
  -- family degrees are constant (`Q` abelian) ⟹ `d ≡ 1`
  have hzeta_one : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j 1
        = ((hyp.Q.subgroupOf hyp.T).index : ℂ) := by
    intro j
    obtain ⟨θ0, hθ0⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced j
    obtain ⟨θQ, hθQirr, hθQeq⟩ : ∃ θQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θQ ∧
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j
          = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θQ :=
      ⟨θ0.val, θ0.2, by rw [hθ0]; congr!⟩
    rw [hθQeq, ClassFunction.induce_apply_one, hdeg1 θQ hθQirr, mul_one]
  have hidx0 : ((hyp.Q.subgroupOf hyp.T).index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := hyp.Q.subgroupOf hyp.T)
  have hd1 : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).d j = 1 := by
    intro j
    have h := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- conjunct 4: the distinguished coefficient is `δ`
  have hc1 : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) := by
    rw [show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁
        = ClassFunction.inner
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
              ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i₁)) hyp.eta10 from rfl,
      show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
        = (Q_sharp_hypothesis71 hG hyp hvd).τ from rfl,
      Q_sharp_tau_eq_induce hG hyp hvd]
    have hψ : (((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i₁) :
        ClassFunction ↥hyp.T ℂ)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θrQ
          - ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
              (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 i₁, one_smul, hζi₁, hζ0, hνeqQ]
    rw [hψ,
      ← hbridgeQ θrQ (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) hθrQirr
        φ₀.isIrreducible hθrQfull hφ₀Q,
      map_sub, ClassFunction.inner_sub_left, ← hνeqQ, hkeyr,
      hφ₀eta,
      sub_zero]
  -- conjunct 5: all other `Q`-nonkernel coefficients vanish
  have hmid : ∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0 := by
    intro i _hipos hine hiP
    obtain ⟨θi0, hθi0⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced i
    obtain ⟨θiQ, hθiQirr, hθiQeq⟩ : ∃ θiQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θiQ ∧
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i
          = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θiQ :=
      ⟨θi0.val, θi0.2, by rw [hθi0]; congr!⟩
    have hθiQfull : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
        Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θiQ) := by
      intro hker
      apply hiP
      rw [hθiQeq]
      exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf le_rfl θiQ hker
    have hne : ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θiQ
        ≠ ∑ j : Fin hyp.p, hyp.nu r j := by
      intro heq
      exact hine ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_injective
        (by rw [hθiQeq, heq, hζi₁]))
    rw [show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i
        = ClassFunction.inner
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
              ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i)) hyp.eta10 from rfl,
      show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
        = (Q_sharp_hypothesis71 hG hyp hvd).τ from rfl,
      Q_sharp_tau_eq_induce hG hyp hvd]
    have hψi : (((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i) :
        ClassFunction ↥hyp.T ℂ)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θiQ
          - ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
              (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 i, one_smul, hθiQeq, hζ0]
    rw [hψi,
      ← hbridgeQ θiQ (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)
        hθiQirr φ₀.isIrreducible hθiQfull hφ₀Q,
      map_sub, ClassFunction.inner_sub_left,
      hφ₀eta,
      hTau1IndEta θiQ hθiQirr hθiQfull hne,
      sub_zero]
  -- conjuncts 6, 7 and the sign square
  have hnormSq : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) := by
    rw [show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁
        = ClassFunction.inner ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁) from rfl,
      hζi₁, hyp.nuRow_inner pins r r, if_pos rfl]
  have hdegVal : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1
      = ((hyp.p * hyp.v : ℕ) : ℂ) := by
    rw [hζi₁, hyp.nuRow_apply_one hG pins r hr0]
    push_cast
    ring
  have hδ2 : δ ^ 2 = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  refine ⟨i₁, δ, hi₁pos, ?_, hδ2, hc1, hmid, hnormSq, hdegVal⟩
  rw [hζi₁]
  exact hQkerNu

end OddOrder.Peterfalvi.S15
