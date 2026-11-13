-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:34:12.694905+00:00
-- url     : https://prove2.me/submissions/b3e083a5-ef6a-4a4c-b4c3-cf17de608faf

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeClifford.lean
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/LocalTaxonomy.lean
--   OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean
--   OddOrder/GroupTheory/RepresentationTheory/InducedDegreeSum.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP

-- ===== OddOrder/Peterfalvi/S06_CertainTypeClifford.lean =====
namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S05

variable {L : Type*} [Group L] [Fintype L]

namespace Hypothesis

variable (h : Hypothesis L)

section Recipe

variable [Invertible (Nat.card L : ℂ)]
  [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]

variable [Invertible (Nat.card ↥h.K : ℂ)]

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.b), `Ind^L_K χ ≠ μ_{ij}`**: for `χ` not among the `χ_j`, the irreducible
`Ind^L_K χ` is distinct from every certain-type character.  By Frobenius reciprocity
`⟨Ind^L_K χ, μ_{ij}⟩ = ⟨χ, Res^L_K μ_{ij}⟩ = ⟨χ, χ_j⟩ = 0` (`restrict_certainType_eq`, `χ ≠ χ_j`),
whereas `⟨μ_{ij}, μ_{ij}⟩ = 1`. -/
theorem induce_ne_certainType_of_forall_chiRestrict_ne [NeZero (Nat.card h.W1)]
    {χ : IrreducibleCharacter ↥h.K} (hχ : ∀ χ₂, h.chiRestrict χ₂ ≠ χ)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)
      ≠ ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) := by
  have := h.K_normal
  have : Fintype ↥h.K := Fintype.ofFinite _
  intro heq
  have hinner : ClassFunction.inner (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ))
      ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) = 0 := by
    rw [ClassFunction.inner_induce_eq_inner_restrict h.K (χ : ClassFunction ↥h.K ℂ)
      ((h.columnFamily χ₂).mu i : ClassFunction L ℂ), h.restrict_certainType_eq χ₂ i,
      ← h.coe_chiRestrict χ₂, irreducibleCharacter_inner_eq_ite,
      if_neg (Ne.symm (hχ χ₂))]
  rw [heq, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hinner
  exact one_ne_zero hinner

end Recipe

end Hypothesis

end OddOrder.Peterfalvi.S06

-- ===== OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/LocalTaxonomy.lean =====
namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Support-set bridge (all types)**: Peterfalvi's `A_1(M) = M_s#` coincides with BG's
`\widetilde M = M_σ#` (`sigmaSharp`) for a maximal subgroup of its classified type.  Immediate from
`A_1(M) = M_s#`, `M_s = M_σ` (`mainSubgroup_eq_Msigma`, Peterfalvi (8.10)), and `M̃ = M_σ#`.
Generalises the type-I/II support bridge to all five types; supplies the BG↔Pf support
identification
behind `BGTheoremECoverData`'s `thickenedA1`/covering fields (issue 8020). -/
theorem A1_eq_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {tau : PeterfalviType} (htau : HasPeterfalviType tau M) :
    A1 M tau = sigmaSharp M := by
  change sharpSubgroup (mainSubgroup M tau) = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)
  rw [mainSubgroup_eq_Msigma hG hM htau]

end OddOrder.BG.Ch4.S16

-- ===== OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean =====
namespace OddOrder.RepresentationTheory

open scoped BigOperators

open OddOrder.Peterfalvi.S07 (zSpan)

namespace PrimeTIResidueData

variable {S : Type*} [Group S] [Fintype S] [Invertible (Nat.card S : ℂ)]

variable {PU : Subgroup S} [Fintype ↥PU] [Invertible (Nat.card ↥PU : ℂ)]

variable {q p : ℕ} [NeZero q] [NeZero p]

variable (D : PrimeTIResidueData S PU q p)

/-- **`cfInd_prTIres`** (Coq `PFsection4.v:594`): `Ind_{PU}^S (chi_ j) = μ_j`.  Immediate
from the `ind_chi` field and the definition of `primeTIred`. -/
theorem cfInd_prTIres (j : Fin p) :
    ClassFunction.induce PU (D.chi j : ClassFunction ↥PU ℂ) = D.primeTIred j :=
  D.ind_chi j

/-- Each `μ_j` is a **genuine character** (Coq `prTIred_char`): a finite sum of
irreducible characters. -/
theorem prTIred_char (j : Fin p) : IsCharacter (D.primeTIred j) := by
  refine IsCharacter.sum fun i _ => ?_
  exact (D.mu2 i j).isIrreducible.isCharacter

/-- **`cfdot_prTIirr_red`** (Coq `PFsection4.v:452`): `⟨mu2 i j, μ_k⟩ = [j = k]`.

Expanding `μ_k = ∑_{i'} mu2 i' k` and using orthonormality of the `mu2`, the sum over `i'`
collapses to the single term `i' = i` (present iff `j = k`). -/
theorem cfdot_prTIirr_red (i : Fin q) (j k : Fin p) :
    ClassFunction.inner (D.mu2 i j : ClassFunction S ℂ) (D.primeTIred k)
      = (if j = k then 1 else 0) := by
  classical
  rw [primeTIred, inner_sum_right]
  -- each summand is the orthonormality value `[i = i' ∧ j = k]`
  have hval : ∀ i' : Fin q,
      ClassFunction.inner (D.mu2 i j : ClassFunction S ℂ) (D.mu2 i' k : ClassFunction S ℂ)
        = (if i = i' ∧ j = k then 1 else 0) := fun i' => D.mu2_orthonormal i i' j k
  rw [Finset.sum_congr rfl fun i' _ => hval i']
  by_cases hjk : j = k
  · -- only the `i' = i` term survives
    rw [if_pos hjk]
    have hcond : ∀ i' : Fin q, (i = i' ∧ j = k) ↔ i = i' := fun i' => by
      simp [hjk]
    simp only [hcond]
    rw [Finset.sum_ite_eq Finset.univ i (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ i)]
  · -- every term vanishes
    rw [if_neg hjk]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [if_neg fun h => hjk h.2]

/-- **`cfdot_prTIred`** (Coq `PFsection4.v:459`): `⟨μ_{j₁}, μ_{j₂}⟩ = [j₁ = j₂] · q`. -/
theorem cfdot_prTIred (j₁ j₂ : Fin p) :
    ClassFunction.inner (D.primeTIred j₁) (D.primeTIred j₂)
      = (if j₁ = j₂ then (q : ℂ) else 0) := by
  classical
  -- expand the left column-sum, then use `cfdot_prTIirr_red` termwise
  rw [primeTIred, inner_sum_left]
  rw [Finset.sum_congr rfl fun i _ => D.cfdot_prTIirr_red i j₁ j₂]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  by_cases hjk : j₁ = j₂
  · rw [if_pos hjk, if_pos hjk, nsmul_eq_mul, mul_one]
  · rw [if_neg hjk, if_neg hjk, nsmul_eq_mul, mul_zero]

/-- **`cfnorm_prTIred`** (Coq `PFsection4.v:465`): `⟨μ_j⟩ = q = #|W1|`. -/
theorem cfnorm_prTIred (j : Fin p) :
    ClassFunction.inner (D.primeTIred j) (D.primeTIred j) = (q : ℂ) := by
  rw [cfdot_prTIred, if_pos rfl]

/-- **`prTIres0`** (Coq `PFsection4.v:608`): the `0`-residue is the trivial character. -/
theorem prTIres0 : (D.chi 0 : ClassFunction ↥PU ℂ) = trivialClassFunction ↥PU :=
  D.chi_zero

/-- Each `μ_j` is a **virtual character** (`μ_j ∈ ℤ[Irr S]`): it is a genuine character
(`prTIred_char`), and every genuine character lies in `ZIrr`. -/
theorem prTIred_mem_ZIrr (j : Fin p) : D.primeTIred j ∈ ZIrr S :=
  (D.prTIred_char j).mem_ZIrr

end PrimeTIResidueData

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S06.Hypothesis

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L] (h : Hypothesis L)
  [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] [Invertible (Nat.card ↥h.K : ℂ)]
  [NeZero (Nat.card h.W1)] [NeZero (Nat.card h.W2)]

omit [Fintype ↥(h.W1 ⊔ h.W2)] [NeZero (Nat.card ↥h.W2)] in
/-- **Peterfalvi (4.5.b) `prTIres_irr_cases`, assembled.**  Every `χ ∈ Irr(K)` is either a residue
`χ_j` (`= chiRestrict χ₂` for some `W₂`-column `χ₂`) or induces to a *fresh* irreducible of `L`
distinct from every certain-type character `μ_{ij}`.  The residue case is by definition; the
induced-irreducible case is the S06 inertia computation
(`induce_isIrreducible_of_forall_chiRestrict_ne`
+ `induce_ne_certainType_of_forall_chiRestrict_ne`). This is the deep field of a
`PrimeTIResidueData`
constructor built from an `S06.Hypothesis` (issue 9014). -/
theorem prTIres_irr_dichotomy (χ : IrreducibleCharacter ↥h.K) :
    (∃ χ₂, h.chiRestrict χ₂ = χ) ∨
      (IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)) ∧
        ∀ (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)),
          ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)
            ≠ ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)) := by
  by_cases hcase : ∃ χ₂, h.chiRestrict χ₂ = χ
  · exact Or.inl hcase
  · push Not at hcase
    exact Or.inr ⟨h.induce_isIrreducible_of_forall_chiRestrict_ne hcase,
      fun χ₂ i => h.induce_ne_certainType_of_forall_chiRestrict_ne hcase χ₂ i⟩

/-- **`PrimeTIResidueData` from the certain-type `S06.Hypothesis`** (the bridge of issue 9014,
discharging the deep field `prTIres_irr_cases` via `prTIres_irr_dichotomy`).  Given a subgroup
`H : Subgroup ↥h.K` with `W₂ ≤ H` (the (4.6.c) covering condition on the kernel family `P := H`),
assembles the residue grid `S = L`, `PU = K`, `q = |W₁|`, `p = |W₂|` from the S06 column machinery:
`mu2 i j := (columnFamily (e j)).mu i`, `chi j := chiRestrict (e j)` (`e = charGroupW2Equiv`).
Every field is a genuine S06 theorem — orthonormality (`columnFamily_mu_ne` + `injective`),
restriction (`coe_chiRestrict`), induction (`induce_restrict_certainType_eq`), the trivial residue
(`chiRestrict_one_eq_trivial` via `charGroupW2Equiv_zero`), the `(4.7)` kernel non-containment
(`not_subset_characterKernel_chiRestrict_of_ne_one`), and the `(4.5.b)` dichotomy
(`prTIres_irr_dichotomy`). -/
noncomputable def _root_.OddOrder.RepresentationTheory.PrimeTIResidueData.ofS06Hypothesis
    [Fintype ↥h.K] (H : Subgroup ↥h.K) (hW2H : h.W2.subgroupOf h.K ≤ H) :
    PrimeTIResidueData L h.K (Nat.card h.W1) (Nat.card h.W2) :=
  { mu2 := fun i j => (h.columnFamily (h.charGroupW2Equiv j)).mu i
    chi := fun j => h.chiRestrict (h.charGroupW2Equiv j)
    mu2_orthonormal := fun i i' j j' => by
      classical
      rw [irreducibleCharacter_inner_eq_ite]
      by_cases hjj' : j = j'
      · subst hjj'
        by_cases hii' : i = i'
        · subst hii'; simp
        · rw [if_neg (fun hc => hii' ((h.columnFamily (h.charGroupW2Equiv j)).injective hc)),
            if_neg (by simp [hii'])]
      · rw [if_neg (h.columnFamily_mu_ne (fun hc => hjj' (h.charGroupW2Equiv.injective hc)) i i'),
          if_neg (by simp [hjj'])]
    chi_res := fun j => h.coe_chiRestrict (h.charGroupW2Equiv j)
    ind_chi := fun j => by
      rw [h.coe_chiRestrict (h.charGroupW2Equiv j),
        h.induce_restrict_certainType_eq (h.charGroupW2Equiv j)]
    chi_zero := by
      rw [charGroupW2Equiv_zero, h.chiRestrict_one_eq_trivial,
        IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    P := H
    cfker_prTIres := fun j hj => by
      have hne1 : h.charGroupW2Equiv j ≠ 1 := by
        rw [← charGroupW2Equiv_zero (h := h)]
        exact fun hc => hj (h.charGroupW2Equiv.injective hc)
      intro hHker
      exact h.not_subset_characterKernel_chiRestrict_of_ne_one hne1
        (Set.Subset.trans (SetLike.coe_subset_coe.mpr hW2H) hHker)
    prTIres_irr_cases := fun θ => by
      rcases h.prTIres_irr_dichotomy θ with ⟨χ₂, hχ₂⟩ | ⟨hirr, hne⟩
      · refine Or.inl ⟨h.charGroupW2Equiv.symm χ₂, ?_⟩
        rw [Equiv.apply_symm_apply, hχ₂]
      · exact Or.inr ⟨hirr, fun i j => hne (h.charGroupW2Equiv j) i⟩ }

end OddOrder.Peterfalvi.S06.Hypothesis

-- ===== OddOrder/GroupTheory/RepresentationTheory/InducedDegreeSum.lean =====
set_option linter.unusedFintypeInType false

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable [Fintype G] [Fintype ↥H]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]

omit [Fintype G] [Fintype ↥H] [Invertible (Nat.card G : ℂ)]
  [Invertible (Nat.card ↥H : ℂ)] in
/-- Conjugating the trivial irreducible character gives back the trivial character. -/
theorem IrreducibleCharacter.conjBy_trivial (g : G) :
    IrreducibleCharacter.conjBy g (trivialIrreducibleCharacter ↥H)
      = trivialIrreducibleCharacter ↥H := by
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.coe_conjBy]
  ext x
  rw [ClassFunction.conjBy_apply]
  rfl

/-- **The trivial induced character is orthogonal to a nontrivial induced irreducible**, swapped
form.  `⟨Ind_H^G 1_H, Ind_H^G φ⟩ = 0` for `φ ≠ 1_H`: every Mackey summand `⟨1_H, φ^{x⁻¹}⟩`
vanishes since `φ^{x⁻¹} ≠ 1_H` (conjugation preserves nontriviality). -/
theorem inner_induce_trivial_induce_eq_zero
    {φ : IrreducibleCharacter ↥H} (hφ : φ ≠ trivialIrreducibleCharacter ↥H) :
    ClassFunction.inner (induce H (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ))
      (induce H (φ : ClassFunction ↥H ℂ)) = 0 := by
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  apply mul_left_cancel₀ hcardH
  rw [mul_zero, card_mul_inner_induce]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [← IrreducibleCharacter.coe_conjBy, irreducibleCharacter_inner_eq_ite, if_neg]
  intro h
  refine hφ ?_
  have := congrArg (IrreducibleCharacter.conjBy (G := G) x) h.symm
  rwa [IrreducibleCharacter.conjBy_conjBy_inv,
    IrreducibleCharacter.conjBy_trivial (H := H) x] at this

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **The `T`-side derived complement `T = T' ⋊ W₂`, index `[T : T'] = p`** (Coq
`index_sdprod defT`, `p = |W2|`).  From the base `W2_isComplement_T_deriv` (`T' ⋊ W₂ = T`, available
ungated at the §16 construction) and `p = |W2|` (`p_eq_card_W2`).  The degree factor of Coq
`calT1_1p` (`Ind_{QV}^T θ (1) = [T:QV]·θ(1) = p` for linear `θ`). -/
theorem T_derived_index_eq_p (hyp : Hypothesis (G := G)) :
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T).index = hyp.base.p := by
  have hW2_le_T : hyp.base.W2 ≤ hyp.base.T := by
    have h1 : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
    have h2 : hyp.base.W ≤ hyp.base.T := by rw [hyp.base.W_eq_inter]; exact inf_le_right
    exact h1.trans h2
  rw [hyp.base.W2_isComplement_T_deriv.symm.index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2_le_T).toEquiv, hyp.base.p_eq_card_W2]

/-- **`(QV = T')` is normal in `↥T` with index `p`** (`T = T' ⋊ W₂`, `p = |W₂|`).  The
`↥T`-side normal subgroup and the `[T:QV] = p` degree/orbit factor consumed by the `calT1` count,
repackaged from `T_derived_index_eq_p` as a statement about `(derivedInG T).subgroupOf T`
(the shape `card_image_induce_eq_div` needs: `H.index` for `H ◁ ↥T`). -/
theorem T_derivedSubgroupOf_normal (hyp : Hypothesis (G := G)) :
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal := by
  rw [show (derivedInG hyp.base.T).subgroupOf hyp.base.T = _root_.commutator ↥hyp.base.T by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective hyp.base.T.subtype_injective]]
  infer_instance

/-- **The intrinsic type-III cyclic factor has order `p`** (ungated): `|td.typeP.W₁| = [T:T'] = p`.
`td.typeP.W₁` complements `T' = derivedInG T` in `T` (`M_complement`), so `|W₁| = [T:T']`
(`card_W1_eq_derived_index`), and `[T:T'] = p` (`T_derived_index_eq_p`).  This is the orbit-size /
degree factor of `calT1` (Coq `index_sdprod defT`, `p = |W₂|`; note the intrinsic `.W₁` is the
`T'`-complement, matching Coq's `W₂` — the abstract-Hypothesis `W₂` — **not** the abstract `W₁`). -/
theorem T_typeIII_card_W1 [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Nat.card ↥td.typeP.W1 = hyp.base.p := by
  rw [td.typeP.card_W1_eq_derived_index, T_derived_index_eq_p hyp]

/-- **The T-side Dade support `A₁(T) = T_σ^#` is exactly `(T')^# = QV^#`** (issue 9072, step 3
support identity).  For type-III `T`, the Peterfalvi "main subgroup" `T_s = T'` (`mainSubgroup .III
=
derivedInG`), and the support bridge `A1_eq_sigmaSharp`
(Peterfalvi (8.10) + `mainSubgroup_eq_Msigma`,
here `T' = M_σ(T)` for the type-`P₁` regime that type-III inhabits) gives
`sigmaSharp T = A₁(T) = (T_s)^# = (T')^#`.  Concretely
`sigmaSharp T = (derivedInG T : Set G) \ {1}`.

This is the linchpin making the (14.9) coherence support facts derivable *without* any cross-lane
type-`P` char structure: the induced members `Ind_{QV}^T θ` vanish off the normal `QV = T' =
derivedInG T`, so their differences are automatically supported in `sigmaSharp T =
(T')^#` — matching
the Dade domain of `tSideDadeMap`.  (Coq `FTcore_eq_der1`: for `FTtype T > 2`, `T_s = T^{(1)}`; the
member differences `nu_0 − zeta ∈ 'CF(T, QV^#) = 'CF(T, 'A1(T))`, PFsection14.v:785--790.) -/
theorem T_typeIII_sigmaSharp_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} := by
  have := hyp.base.finiteG
  -- `A1 T .III = sigmaSharp T` (support bridge), and `A1 T .III = sharpSubgroup (derivedInG T)`
  -- since `mainSubgroup .III = derivedInG`.
  have hA1 : OddOrder.GroupTheory.A1 hyp.base.T OddOrder.GroupTheory.PeterfalviType.III
      = OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.BG.Ch4.S16.A1_eq_sigmaSharp hG hyp.base.T_maximal hIII
  rw [← hA1]
  rfl

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), source data for the T-side projection.**
The concrete prime-TI anchor `ν₀ = Ind_{T'}^T 1_{T'}` has self-inner-product `p`
and is orthogonal to every `Ind_{T'}^T θ` with `θ ≠ 1`.

These are Coq's `cfnorm_prTIred` and `omuS1` inputs in the norm-rigidity proof of
`FTtype34_structure`. Keeping the universal induced-family orthogonality alongside
the concrete anchor avoids replacing the (11.9)(a) projection by an opaque coefficient
assumption downstream.  This strengthened producer also retains the defining equality
`primeTIred 0 = Ind_{T'}^T 1`. -/
theorem exists_typeIII_primeTIredZero_with_projectionData_galois_and_eq_induce [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0 ν0 = (hyp.base.p : ℂ) ∧
        (∀ θ : IrreducibleCharacter
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T),
          θ ≠ trivialIrreducibleCharacter _ →
          ClassFunction.inner ν0
            (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
              θ.toClassFunction) = 0) ∧
        (∀ sigma : ℂ ≃+* ℂ,
          ClassFunction.mapRingEquiv sigma ν0 = ν0) ∧
        ν0 = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (trivialClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) := by
  classical
  let td : OddOrder.GroupTheory.TypeIIIData hyp.base.T := hIII.some
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIII hG hyp.base.T_maximal hIII
  let s06 : OddOrder.Peterfalvi.S06.Hypothesis ↥hyp.base.T :=
    OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis td.typeP hG.odd
      (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime
        hG hyp.base.T_maximal hP td.typeP)
  let : NeZero (Nat.card ↥s06.W1) := ⟨Nat.card_pos.ne'⟩
  let : NeZero (Nat.card ↥s06.W2) := ⟨Nat.card_pos.ne'⟩
  let residue : PrimeTIResidueData ↥hyp.base.T s06.K
      (Nat.card ↥s06.W1) (Nat.card ↥s06.W2) :=
    PrimeTIResidueData.ofS06Hypothesis s06 ⊤ le_top
  refine ⟨residue.primeTIred 0, residue.prTIred_mem_ZIrr 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (residue.primeTIred 0).conj = residue.primeTIred 0
    rw [← residue.cfInd_prTIres 0, residue.prTIres0,
      ClassFunction.induce_conj, trivialClassFunction_isReal]
  · have : s06.K.Normal := s06.K_normal
    change (residue.primeTIred 0).support ⊆ (s06.K : Set ↥hyp.base.T)
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    exact ClassFunction.support_induce_subset_of_normal s06.K
      (trivialClassFunction ↥s06.K)
  · calc
      residue.primeTIred 0 1 = (Nat.card ↥s06.W1 : ℂ) := by
        rw [← residue.cfInd_prTIres 0, residue.prTIres0,
          ClassFunction.induce_apply_one, s06.index_K_eq,
          trivialClassFunction_apply, mul_one]
      _ = (Nat.card ↥td.typeP.W1 : ℂ) := by
        congr 1
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe td.typeP.W1_le).toEquiv
      _ = (hyp.base.p : ℂ) := by rw [T_typeIII_card_W1 hyp td]
  · rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    have hconst :
        OddOrder.Peterfalvi.S09.Hypothesis71.constOne ↥hyp.base.T =
          trivialClassFunction ↥hyp.base.T := by
      ext t
      simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne]
    rw [← hconst]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one s06.K
  · calc
      ClassFunction.inner (residue.primeTIred 0) (residue.primeTIred 0) =
          (Nat.card ↥s06.W1 : ℂ) := residue.cfnorm_prTIred 0
      _ = (Nat.card ↥td.typeP.W1 : ℂ) := by
        congr 1
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe td.typeP.W1_le).toEquiv
      _ = (hyp.base.p : ℂ) := by rw [T_typeIII_card_W1 hyp td]
  · intro θ hθ
    change ClassFunction.inner (residue.primeTIred 0)
        (ClassFunction.induce s06.K θ.toClassFunction) = 0
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    exact OddOrder.RepresentationTheory.inner_induce_trivial_induce_eq_zero hθ
  · intro sigma
    rw [← residue.cfInd_prTIres 0, residue.prTIres0,
      ClassFunction.mapRingEquiv_induce]
    congr 1
    ext x
    simp [ClassFunction.mapRingEquiv_apply, trivialClassFunction_apply]
  · rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    change ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        (trivialClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) = _
    rfl

open scoped Classical in
/-- A `calT1` source induced from the normal subgroup `T'` is supported on `T'`. -/
theorem typeIII_induced_source_support [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T]
    [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible
      (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) :
    (ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θ.toClassFunction).support ⊆
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T :
        Set ↥hyp.base.T) := by
  have : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  have : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  intro x hx
  by_contra h
  apply ClassFunction.mem_support.mp hx
  exact ClassFunction.induce_eq_zero_of_not_mem_normal θ.toClassFunction h

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the normed bridge retains anchor orthogonality.**
This is the projection-ready form of
`exists_typeIII_induced_primeTIDifference_with_norm`: the same canonical prime-TI
anchor is kept orthogonal to the induced source and its conjugate. -/
theorem _root_.solution
    [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [fintypeT : Fintype ↥hyp.base.T]
    [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [invertibleT : Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [invertibleK :
      Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθne : θ ≠ trivialIrreducibleCharacter _)
    (hζirr : IsIrreducibleCharacter
      (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
    (hζ1 : ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction 1 =
        (hyp.base.p : ℂ)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            ∈ ZIrr ↥hyp.base.T ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) ∈ ZIrr G ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) 1 = 0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj =
            ν0 - (ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) = 0 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj = 0 ∧
        ClassFunction.inner
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        ClassFunction.inner
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        (∀ sigma : ℂ ≃+* ℂ,
          ClassFunction.mapRingEquiv sigma ν0 = ν0) ∧
        ν0 = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (trivialClassFunction
            ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) := by
  have hfg : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hft : fintypeT =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype hyp.base.T :=
    Subsingleton.elim _ _
  subst fintypeT
  have hig : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hit : invertibleT =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC hyp.base.T :=
    Subsingleton.elim _ _
  subst invertibleT
  have hik : invertibleK =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Subsingleton.elim _ _
  subst invertibleK
  let ζ := ClassFunction.induce
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction
  change IsIrreducibleCharacter ζ at hζirr
  change ζ 1 = (hyp.base.p : ℂ) at hζ1
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hνnorm, hνorth, hνfixed, hνeq⟩ :=
    exists_typeIII_primeTIredZero_with_projectionData_galois_and_eq_induce
      hG hyp hIII
  let θc : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) :=
    ⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
      θ.isIrreducible.conj⟩
  have hθcne : θc ≠ trivialIrreducibleCharacter _ :=
    OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.irreducibleCharacter_conj_ne_trivial
      hθne
  have hνζ : ClassFunction.inner ν0 ζ = 0 := hνorth θ hθne
  have hνζc : ClassFunction.inner ν0 ζ.conj = 0 := by
    rw [ClassFunction.induce_conj
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
      (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)]
    exact hνorth θc hθcne
  have hζsupp : ζ.support ⊆
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) :=
    typeIII_induced_source_support hyp θ
  have hβZ : ν0 - ζ ∈ ZIrr ↥hyp.base.T :=
    (ZIrr ↥hyp.base.T).sub_mem hνZ hζirr.mem_ZIrr
  have hA : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
      (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hβsupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro x hx
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      rcases ClassFunction.support_sub_subset ν0 ζ hx with hx | hx
      · exact hνsupp hx
      · exact hζsupp hx
    have hx1 : x ≠ 1 := by
      intro he
      apply ClassFunction.mem_support.mp hx
      rw [he, ClassFunction.sub_apply, hν1, hζ1, sub_self]
    exact (OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hA x).2 ⟨hxK, hx1⟩
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hτZ : tSideDadeMap hyp hG (ν0 - ζ) ∈ ZIrr G := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        side.dade hβsupp hβZ)
  have hτ1 : tSideDadeMap hyp hG (ν0 - ζ) 1 = 0 := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        side.dade hβsupp)
  have hζν : ClassFunction.inner ζ ν0 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hνζ, star_zero]
  have hβnorm : ClassFunction.inner (ν0 - ζ) (ν0 - ζ) =
      ((hyp.base.p : ℕ) + 1 : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hνnorm, hνζ, hζν, hζirr.inner_self_eq_one]
    ring
  have hτnorm : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
      (tSideDadeMap hyp hG (ν0 - ζ)) = ((hyp.base.p : ℕ) + 1 : ℂ) := by
    have hS : ∀ s ∈ ({ν0 - ζ} : Set (ClassFunction ↥hyp.base.T ℂ)),
        s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
      intro s hs
      simpa only [Set.mem_singleton_iff] using hs ▸ hβsupp
    rw [show tSideDadeMap hyp hG =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData) from rfl]
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      side.dade hS
      (Submodule.subset_span (Set.mem_singleton (ν0 - ζ)))
      (Submodule.subset_span (Set.mem_singleton (ν0 - ζ))), hβnorm]
  refine ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, ?_, hνone,
    hνζ, hνζc, hβnorm, hτnorm, hνfixed, hνeq⟩
  rw [ClassFunction.conj_sub, hνR]

end OddOrder.Peterfalvi.S16
