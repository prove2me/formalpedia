-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.T_typeIII_calT1_isCoherent
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:06:32.055962+00:00
-- url     : https://prove2.me/submissions/b74dbc19-dc60-40e3-ab7d-983bf25847ab

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/LocalTaxonomy.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

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

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Peterfalvi (14.9): assembling the T-side `S07.Hypothesis` (`hyp07`)** (issue 9072, steps 2--4)
— the coherence-carrier constructor feeding `T_typeIII_calT1_coherent`.

Given the `calT1` family `𝒯 =` non-principal conjugate-closed `Irr(QV/Q)`-inflated sources (matching
`T_typeIII_calT1_card`/`calT1_image_induce_card_eq`), with:
* `hinertia : I_T(θ) = QV` for each `θ ∈ 𝒯` (⟹ `Ind_{QV}^T θ` irreducible), the same inertia fact
  feeding the count;
* `hne : θ ≠ 1` for each `θ ∈ 𝒯` (non-principal sources);
* `hconj𝒯 : θ ∈ 𝒯 ⟹ ⟨θ̄, θ.isIrreducible.conj⟩ ∈ 𝒯` (`𝒯` conjugate-closed, since `Irr` is);

this constructs the T-side `S07.Hypothesis calT1_set (supportInSubgroup (sigmaSharp T) T)` via the
in-repo assembler `S07.irrSubcoherent`, threading:
* `τ = tSideDadeMap hyp hG` (the genuine §10 Dade integral character map);
* the family predicates `S03.ClosedUnderConjugate`/`HasNoRealCharacters`/`PairwiseOrthogonal`, all
  derived from the induced-irreducible structure alone (Frobenius-analogous to the type-I
  `S14.Sset_*` witnesses): closure via `induce_conj`, no-real via
  `not_isReal_of_ne_trivial_of_odd_card'`
  (odd `|T|`, `Ind θ ≠ 1`), orthogonality via `irreducibleCharacter_inner_eq_ite`;
* the per-member `CharacterDifferenceImage` via `S07.dadeCharacterDifferenceImageOfDiff` (fed the
  conjugate-difference support `(χ̄ − χ).support ⊆ supportInSubgroup (sigmaSharp T) T`, from the
  member vanishing off `QV = T'` and `sigmaSharp T = (T')^#` = `T_typeIII_sigmaSharp_eq`);
* the isometry `tSideDadeMap_isometry_diff` (fed the family-supportedness `hSsupp`).

Everything here is **ungated**: it needs only the intrinsic type-III support identity
`T_typeIII_sigmaSharp_eq` and the induced-character bricks, no S-side βₛ / (13.12) input.  Its
output
is exactly the `hyp07` argument that `T_typeIII_calT1_coherent` consumes to produce coherence. -/
noncomputable def T_typeIII_hyp07 [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (hconj𝒯 : ∀ θ ∈ 𝒯,
      (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
        θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) := by
  classical
  haveI := hyp.base.finiteG
  -- `T` has odd order (subgroup of the odd `G`).
  have hodd : Odd (Nat.card ↥hyp.base.T) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.T)
  -- `K = QV.subgroupOf T` is normal in `T` (`QV = T' = derivedInG T ⊴ T`).
  haveI hKnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  -- The support identity `sigmaSharp T = (derivedInG T)^#`.
  have hAK : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  -- Membership form: `x ∈ A ↔ x ∈ K ∧ x ≠ 1`.
  have hmemA : ∀ x : ↥hyp.base.T,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ↔
        (x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T ∧ x ≠ 1) := fun x =>
    OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAK x
  -- Each member of `calT1_set` is `Ind_K θ` for a non-principal `θ ∈ 𝒯`.
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  -- `Ind_K θ ≠ 1` (else `⟨Ind θ, 1⟩ = 1 ≠ 0 = ⟨Ind θ, 1⟩`), for non-principal `θ`.
  have hInd_ne_triv : ∀ θ (hθ : θ ∈ 𝒯),
      (⟨ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction,
        isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θ (hinertia θ hθ)⟩ :
        IrreducibleCharacter ↥hyp.base.T) ≠ trivialIrreducibleCharacter _ := by
    intro θ hθ hcontra
    -- `Res_K 1 = 1`, so `⟨Ind_K θ, 1⟩ = ⟨θ, Res 1⟩ = ⟨θ, 1⟩ = 0` (`θ ≠ 1`), contradicting `= 1`.
    have hrestrict : ClassFunction.restrict ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ)
        = (trivialIrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) :
            ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ) := by
      ext x
      simp [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply]
    have hzero : ClassFunction.inner
        (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ))
        (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ) = 0 := by
      rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
        irreducibleCharacter_inner_eq_ite, if_neg (hne θ hθ)]
    have hcf : ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)
        = (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ) :=
      congrArg (fun c : IrreducibleCharacter ↥hyp.base.T => (c : ClassFunction ↥hyp.base.T ℂ))
        hcontra
    rw [hcf, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hzero
    exact one_ne_zero hzero
  -- (a) `S03.HasNoRealCharacters calT1_set`: each member is a nontrivial irreducible of the odd
  -- `T`.
  have hreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters calT1_set := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact not_isReal_of_ne_trivial_of_odd_card' (G := ↥hyp.base.T) hodd
      (χ := ⟨ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction,
        isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θ (hinertia θ hθ)⟩)
      (hInd_ne_triv θ hθ)
  -- (b) `S03.PairwiseOrthogonal calT1_set`: distinct irreducible members are orthogonal.
  have hortho : OddOrder.Peterfalvi.S03.PairwiseOrthogonal calT1_set := by
    intro χ ψ hχ hψ hne'
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    obtain ⟨θ', hθ', rfl⟩ := hmem_form ψ hψ
    have hχirr := isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
    have hψirr := isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ' (hinertia θ' hθ')
    rw [show ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction
          = ((⟨_, hχirr⟩ : IrreducibleCharacter ↥hyp.base.T) : ClassFunction ↥hyp.base.T ℂ)
            from rfl,
      show ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ'.toClassFunction
          = ((⟨_, hψirr⟩ : IrreducibleCharacter ↥hyp.base.T) : ClassFunction ↥hyp.base.T ℂ)
            from rfl,
      irreducibleCharacter_inner_eq_ite, if_neg]
    intro h
    exact hne' (congrArg
      (fun c : IrreducibleCharacter ↥hyp.base.T => (c : ClassFunction ↥hyp.base.T ℂ)) h)
  -- (c) `S03.ClosedUnderConjugate calT1_set`: `(Ind_K θ)^ = Ind_K θ̄` and `θ̄ ∈ 𝒯`.
  have hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate calT1_set := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    rw [hcalT1, Finset.mem_coe, Finset.mem_image]
    refine ⟨⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
      θ.isIrreducible.conj⟩, hconj𝒯 θ hθ, ?_⟩
    -- `Ind_K (θ̄) = (Ind_K θ)^`.
    exact (ClassFunction.induce_conj ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
      (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)).symm
  -- Support of the conjugate difference `χ̄ − χ` for a member `χ = Ind_K θ`: `⊆ A = (T')^#`.
  have hconjDiff_supp : ∀ χ ∈ calT1_set,
      ((χ : ClassFunction ↥hyp.base.T ℂ).conj - χ).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    intro x hx
    have hx0 : ((ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θ.toClassFunction).conj
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply] at hx0
    -- Off `K`, `Ind θ` vanishes (normal `K`), so the difference vanishes.
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θ.toClassFunction h]
      simp
    -- At `1`, `Ind θ (1)` is a real (natural) degree, so the conjugate difference vanishes.
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      obtain ⟨n, -, hn1, -⟩ :=
        (isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
          (hinertia θ hθ)).exists_natDegree_charValue_one_dvd_card
      rw [hn1, star_natCast, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Support of a member *difference* `a − b`: `⊆ A` (both vanish off `K`, and `a(1) = b(1) = p`).
  have hdiff_supp : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro a ha b hb
    obtain ⟨θa, hθa, rfl⟩ := hmem_form a ha
    obtain ⟨θb, hθb, rfl⟩ := hmem_form b hb
    intro x hx
    have hx0 : (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θa.toClassFunction
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θb.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply] at hx0
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θa.toClassFunction h,
        ClassFunction.induce_eq_zero_of_not_mem_normal θb.toClassFunction h, sub_zero]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      -- Both degrees are `[T:K]·θ(1) = [T:K]·1` (linear sources), so the difference vanishes at 1.
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one,
        hlinear θa hθa, hlinear θb hθb, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Each member is irreducible (packaged from its `Ind_K θ` form).
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- Per-member `CharacterDifferenceImage` from the Dade map (difference-support form).
  have Rdatum : ∀ χ ∈ calT1_set, OddOrder.Peterfalvi.S07.CharacterDifferenceImage
      (L := ↥hyp.base.T) (G := G) (tSideDadeMap hyp hG) χ := fun χ hχ =>
    -- Package `χ` (an irreducible member) as an `IrreducibleCharacter ↥T`; `(ζ : CF) = χ` by `rfl`.
    OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
      (tSideDadeSupport_nonempty hG hyp).some.dade
      ⟨χ, hirr χ hχ⟩ (hreal hχ) (hconjDiff_supp _ hχ)
  -- Assemble via the (5.3)(a) `irrSubcoherent` (0099 form: `hconjsupp` + `zSupportedSpan` isometry,
  -- the latter unconditional from the Dade pair brick).
  exact OddOrder.Peterfalvi.S07.irrSubcoherent (S := calT1_set) (tSideDadeMap hyp hG) _ Rdatum
    hconj hreal hortho
    (fun χ hχ => hdiff_supp χ hχ χ.conj (hconj hχ))
    (fun φ ψ hφ hψ => by
      simp only [tSideDadeMap]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (tSideDadeSupport_nonempty hG hyp).some.dade
        hφ.2 hψ.2)

open scoped Classical in
/-- **Peterfalvi (14.9): `calT1` is coherent** (Coq `PFsection14.v:750--751`
`have [tau1T cohT1]: coherent calT1 T^# tauT`, via
`apply/(uniform_degree_coherence scohT1)/(@all_pred1_constant _ p%:R)`) — the **coherence skeleton**
isolating the T-side type-`P` Dade setup as the single deep residual.

`calT1 = {Ind_{QV}^T θ | θ ∈ 𝒯}` (`QV = T' = derivedInG T`, `Q = M_F`, `𝒯 =` non-principal inflated
`Irr(QV/Q)`), realized here as the `Set`-coercion of the `Finset` image (matching
`T_typeIII_calT1_card`/`calT1_image_induce_card_eq`).  Given the **Dade setup** as the input
`hyp07 : S07.Hypothesis calT1_set A` (the Coq `subcoherent calT1 tauT rmR_T` = `FTtypeP_coh_base`,
carrying `tauT` and the seven §5.2 fields), this produces coherence via the proven engine
`S07.coherent_of_constant_degree` (Coq `uniform_degree_coherence`), **proving everything else** from
`calT1`'s structure + the proven count:

* `hirr` — each `ζ = Ind_{QV}^T θ (θ ∈ 𝒯)` is irreducible
(`isIrreducibleCharacter_induce_of_inertia_eq`
  fed the inertia fact `hinertia : I_T(θ) = QV`, the same input feeding the count), so `⟨ζ,ζ⟩ = 1`
  (`IsIrreducibleCharacter.inner_self_eq_one`);
* `hconst`/`hdeg0` — each `ζ` has degree `ζ(1) = [T:QV]·θ(1) = p·1 = p ≠ 0`
  (`ClassFunction.induce_apply_one` + `T_derived_index_eq_p` `[T:QV] = p` + linearity
  `hlinear : θ(1) = 1`, since `θ` inflates from the abelian `QV/Q ≅ V`), i.e. Coq's
  `all_pred1_constant p`;
* `hSfin` — `calT1_set` is the image of a `Finset`, hence finite.

The residual — **the T-side type-`P` Dade isometry construction** (Coq `FTtypeP_coh_base`, a
from-scratch
§4/§5 build with **no** existing type-`P` Dade base in the repo) — is precisely the input `hyp07`
together with the three genuinely Dade/support-dependent facts, kept as explicit hypotheses (each
cited from `hyp07`'s concrete Dade map at the call site, exactly as the §14 type-I assembly
discharges
them via `dadeIntegralCharacterMap_mem_ZIrr_of_supported` etc.):

* `hZIrr : ∀ a b ∈ calT1_set, hyp07.tau (a − b) ∈ ZIrr G` — the Dade-map integrality on member
  differences (Coq `Ztau1T` from the `subcoherent` datum);
* `h1A : (1 : ↥T) ∉ A` and `hsuppdiff : ∀ a b ∈ calT1_set, (a − b).support ⊆ A` — the
support/`A`-facts
  (Coq `A = T^#`, so `1 ∉ A` and every member difference vanishes off `T^#`);
* `hcard2 : 2 ≤ calT1_set.ncard` — the size bound `2 ≤ (|V|−1)/p` (arithmetic on `|V|`, from the
proven
  count `T_typeIII_calT1_card`; kept explicit since it needs a `|V|`-lower bound not carried by the
  intrinsic datum here).

This is the honest §16 coherence assembly point for (14.9): it consumes only the verified bricks
(`isIrreducibleCharacter_induce_of_inertia_eq`, `induce_apply_one`, `T_derived_index_eq_p`,
`coherent_of_constant_degree`) and the parameterized Dade setup, leaving the type-`P` Dade base as
the
single precisely-scoped deep obligation.  Its output feeds the (14.9) Γ-Bessel bound
`T_typeIII_ratio_le` (Coq `cohT1` consumed at PFsection14.v:769
`have [[Itau1T Ztau1T] Dtau1T] := cohT1`). -/
theorem T_typeIII_calT1_coherent [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hlinear : ∀ θ ∈ 𝒯,
      (θ.toClassFunction : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (A : Set ↥hyp.base.T)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set A)
    (hZIrr : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, hyp07.tau (a - b) ∈ ZIrr G)
    (h1A : (1 : ↥hyp.base.T) ∉ A)
    (hsuppdiff : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆ A)
    (hcard2 : 2 ≤ calT1_set.ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp07.tau calT1_set A) := by
  have : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  have := hyp.base.finiteG
  -- `calT1_set` is finite (image of a `Finset`).
  have hSfin : calT1_set.Finite := by rw [hcalT1]; exact (Finset.finite_toSet _)
  -- The `[T:QV] = p` index (degree factor) and its positivity.
  have hindex : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).index = hyp.base.p :=
    T_derived_index_eq_p hyp
  have hp_ne : (hyp.base.p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hyp.base.p_prime.pos.ne'
  -- Each member `ζ = Ind_{QV}^T θ` is irreducible; extract its source `θ ∈ 𝒯` and its degree `= p`.
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  have hirr : ∀ ζ ∈ calT1_set, IsIrreducibleCharacter ζ := by
    intro ζ hζ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form ζ hζ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  have hdeg : ∀ ζ ∈ calT1_set, (ζ : ↥hyp.base.T → ℂ) 1 = (hyp.base.p : ℂ) := by
    intro ζ hζ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form ζ hζ
    rw [ClassFunction.induce_apply_one, hindex, hlinear θ hθ, mul_one]
  -- assemble and invoke the equal-degree coherence producer.
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree hyp07 hSfin hcard2 ?_ hZIrr ?_ ?_
    h1A hsuppdiff
  · exact fun ζ hζ => (hirr ζ hζ).inner_self_eq_one
  · exact fun a ha b hb => by rw [hdeg a ha, hdeg b hb]
  · exact fun a ha => by rw [hdeg a ha]; exact hp_ne

open scoped Classical in
/-- **Peterfalvi (14.9): `calT1` is coherent, end-to-end** (issue 9072, Stage-1 completion) — the
composition `T_typeIII_hyp07` ∘ `T_typeIII_calT1_coherent` that produces the coherent map `τ₁` from
the *intrinsic* family data alone (plus the gated size bound `hcard2`).  The T-side `S07.Hypothesis`
Dade package `hyp07` is now **constructed** (not posited) by `T_typeIII_hyp07`, and its three
support/integrality carriers are discharged here from the induced-character support facts:

* `hZIrr` — `τ_T(a − b) ∈ ZIrr G` via `S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported` (the
  member difference is `A₁(T)`-supported (`hdiff_supp`) and lies in `ℤ[Irr T]`);
* `h1A` — `1 ∉ A₁(T) = supportInSubgroup (sigmaSharp T) T` (`one_not_mem_supportInSubgroup_sharp`);
* `hsuppdiff` — member differences vanish off `A₁(T)` (the same `hdiff_supp`, from the members
  vanishing off `QV = T'` and `sigmaSharp T = (T')^#`).

The only *external* input is `hcard2 : 2 ≤ calT1_set.ncard` (`= (|V|−1)/p ≥ 2`, the size bound
needing
a `|V|`-lower bound — kept explicit, as in `T_typeIII_calT1_coherent`).  Output: the coherent
`τ₁ = hyp07.tau = tSideDadeMap hyp hG`-extension whose orthonormal image family feeds the (14.9)
Γ-Bessel bound. -/
theorem _root_.solution [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _)
    (hconj𝒯 : ∀ θ ∈ 𝒯,
      (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
        θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hcard2 : 2 ≤ calT1_set.ncard) :
    ∃ hyp07 : OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T),
      hyp07.tau = tSideDadeMap hyp hG ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp07.tau calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)) := by
  classical
  have := hyp.base.finiteG
  have : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  -- Support identity `sigmaSharp T = (derivedInG T)^#` and the sharp-membership form.
  have hAK : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hmemA : ∀ x : ↥hyp.base.T,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ↔
        (x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T ∧ x ≠ 1) := fun x =>
    OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAK x
  have hKnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- Member-difference support `⊆ A₁(T)` (`= hsuppdiff`).
  have hdiff_supp : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro a ha b hb
    obtain ⟨θa, hθa, rfl⟩ := hmem_form a ha
    obtain ⟨θb, hθb, rfl⟩ := hmem_form b hb
    intro x hx
    have hx0 : (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θa.toClassFunction
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θb.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply] at hx0
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θa.toClassFunction h,
        ClassFunction.induce_eq_zero_of_not_mem_normal θb.toClassFunction h, sub_zero]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one,
        hlinear θa hθa, hlinear θb hθb, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Build `hyp07` via `T_typeIII_hyp07`; its `.tau = tSideDadeMap hyp hG` (by `rfl`).
  set hyp07 := T_typeIII_hyp07 hyp hG hIII 𝒯 hinertia hne hlinear hconj𝒯 calT1_set hcalT1
    with hhyp07
  have htau : hyp07.tau = tSideDadeMap hyp hG := rfl
  refine ⟨hyp07, htau, ?_⟩
  -- `h1A`: `1 ∉ A₁(T)`.
  have h1A : (1 : ↥hyp.base.T) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    rw [hmemA 1]; rintro ⟨-, h⟩; exact h rfl
  -- `hZIrr`: `τ_T(a − b) ∈ ZIrr G` (member difference `A₁(T)`-supported + in `ℤ[Irr T]`).
  have hZIrr : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, hyp07.tau (a - b) ∈ ZIrr G := by
    intro a ha b hb
    rw [htau]
    simp only [tSideDadeMap]
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (tSideDadeSupport_nonempty hG hyp).some.dade
      (hdiff_supp a ha b hb) ?_
    exact Submodule.sub_mem _ (hirr a ha).mem_ZIrr (hirr b hb).mem_ZIrr
  -- Feed the coherence engine `T_typeIII_calT1_coherent`.
  exact T_typeIII_calT1_coherent hyp 𝒯 hinertia hlinear _ calT1_set hcalT1 hyp07 hZIrr h1A
    hdiff_supp hcard2

end OddOrder.Peterfalvi.S16
