-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.V_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:37:31.561628+00:00
-- url     : https://prove2.me/submissions/6da4aabd-7895-4b7c-a1e0-bc7e6e53f18a

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SingerField.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RepresentationTheory.Maschke
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Ring.GeomSum
import Theorems.Thm_OddOrder_RepresentationTheory_isSimpleModule_of_abelian_faithful_card
import Theorems.Thm_OddOrder_RepresentationTheory_exists_galoisField_repr_of_faithful_irreducible
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_elementaryAbelian_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_isMulCommutative_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S16_cyclotomic_ratio_gt_of_q_lt_p
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_side_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_ratio_le

-- ===== OddOrder/GroupTheory/RepresentationTheory/SingerField.lean =====
namespace OddOrder.RepresentationTheory

universe u

variable {p : ℕ} {C M : Type u} [CommGroup C] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) C) M]

section Irreducibility

variable {p : ℕ} [Fact p.Prime] {C M : Type u}
  [CommGroup C] [IsCyclic C] [Finite C]
  [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) C) M] [Finite M]

omit [IsCyclic C] in
/-- **Peterfalvi (14.2)(a), abstract form.**  A faithful action of an abelian group `C` of order
`(p^q-1)/(p-1)` on an `F_p`-module `M` of order `p^q` (`q` an *odd* prime) realizes `M` as the
Galois field `GF(p^q)` with `C` embedded in the multiplicative group `GF(p^q)ˣ`: there is an
additive isomorphism `e : M ≃+ GF(p^q)` and an injective `μ : C →* GF(p^q)ˣ` with
`e (c • x) = μ c · e x`.

This is the field-isomorphism that the Section 16 finite-field model (`FieldNormalizerData`)
requires: combine `isSimpleModule_of_abelian_faithful_card` (irreducibility), the Singer engine,
and `nonempty_ringEquiv_galoisField` (uniqueness of finite fields). -/
theorem exists_galoisField_repr {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    [NeZero (Nat.card C : ZMod p)]
    (hcardM : Nat.card M = p ^ q) (hcardC : Nat.card C = (p ^ q - 1) / (p - 1))
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    ∃ (e : M ≃+ GaloisField p q) (μ : C →* (GaloisField p q)ˣ),
      Function.Injective μ ∧
      ∀ (c : C) (x : M),
        e (MonoidAlgebra.of (ZMod p) C c • x) = (μ c : GaloisField p q) * e x := by
  have hsimp : IsSimpleModule (MonoidAlgebra (ZMod p) C) M :=
    isSimpleModule_of_abelian_faithful_card hq hqodd hcardM hcardC hfaith
  exact exists_galoisField_repr_of_faithful_irreducible hq.pos.ne' hcardM hfaith

end Irreducibility

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.17.a) T-side Fitting order (B1)**: `|Q| = |T_F| = q^p`.

This is the `S ↔ T` symmetric companion of `BasicStructureData.P_order` (`|P| = |S_F| = p^q`), now
**proven** for the (14.9) type-II member `T`: from `IsTypeII T`, the (9.3) Wielandt order relation
`typeII_III_IV_order_relations` on the reconciled type-`P` data of `T` (`reconciled_typePData_T`)
gives `|T_F| = |tpd.W2|^|tpd.W1| = |W₁|^|W₂| = q^p` (the intrinsic factors reconcile to
`tpd.W2 = W₁`,
`tpd.W1 = W₂`).  Combined with the automorphism-equivariance of `M_F`
(`maxNilpotentNormalHall_pointwise_smul`), it gives `|L_F| = q^p` for every `L` conjugate to `T`,
which is what the `L ~ T` exclusion of (13.17.a) uses.  The `IsTypeII T` hypothesis is threaded from
`exists_LHypothesis` (§16, via the (14.9) `T_typeII`). -/
theorem card_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨tpd, _htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have tdata : TypeIIData hyp.T := hTTypeII.some
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥tpd.W1).Prime := by
    rw [htpdW1, ← hyp.p_eq_card_W2]; exact hyp.p_prime
  have hTI := tdata.common.2.2
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, hTI⟩
      type_alt := Or.inl hTTypeII }).1 hTTypeII
  have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
  have hW2card : Nat.card ↥tpd.W2 = hyp.q := by
    rw [htpdW2, ← hyp.q_eq_card_W1]
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
  exact hord2

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.12), `T`-side `d = 1` in the Section 16 context** (issue 9077):
`V ⊓ C_G(Q) = ⊥`.  The honest (13.4) character-degree producer supplies `D = ⊥`, and the
canonical identity `D = V ⊓ C_G(Q)` turns it into the faithful-action statement.  This downstream
placement avoids the genuine import cycle from `S15_SAndTBasic` to the character-degree layer. -/
theorem Hypothesis.V_inf_centralizer_Q_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.base.V ⊓ Subgroup.centralizer (hyp.base.Q : Set G) = ⊥ := by
  rw [← hyp.base.D_eq]
  exact (T_side_caseB_facts hG hyp).1

/-- **Peterfalvi (11.9)/(14.9), the Type-IV exclusion** — the deep content of the type
determination, now discharged.  Coq `FTtype34_structure` (Peterfalvi (11.9), `PFsection11.v:1001`,
consumed at `PFsection14.v:735`) pins a non-type-II type-`P` maximal `T` to Type III (not IV) via
the character/Galois argument `suffices galM : typeP_Galois MtypeP` (`PFsection11.v:1139`) — the
`η`-grid projection computation `a₁₁ = a₁₀ = 0`.

Formalised as the universal (11.9.c) Type-IV exclusion `not_isTypeIV_of_mem_maximalSubgroups`
(`S13_NonGaloisExclusion`, sorry-free): the `IsMulCommutative V` residual that used to live here
follows from `cyclic V ⟸ typeP_Galois T`, whose full §5–§13 chain
(`not_isTypeIV_of_hypothesis`/`U_isCyclic_of_hypothesis`) is landed.  The direct cite became
possible once the §12–16 import inversion (issue 9093) removed `S13_NonGaloisExclusion`'s
transitive dependency on §16. -/
theorem T_not_isTypeIV_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    ¬ OddOrder.GroupTheory.IsTypeIV hyp.base.T :=
  OddOrder.Peterfalvi.S13.not_isTypeIV_of_mem_maximalSubgroups hG hyp.base.T_maximal

/-- **Peterfalvi (14.9), the type determination** — Coq `PFsection14`
`have [_ _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2` (line 735): a type-`P` maximal
subgroup that is *not* type II is type III.  In σ-theoretic terms, `IsTypeP1 T` (equivalently
`¬ IsTypeP2 T` given `IsTypeP T`) forces `T` to be structurally Type III.

**Fully reduced to the single (11.9) residual `T_not_isTypeIV_of_isTypeP1`.**  The type dictionary
`proposition_type_classification` (BG Prop 16.1, proven) gives, from `IsTypeP1 T`, either Type
III/IV
(if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).  **Type V is excluded outright** by the (10.10)
hypothesis `hnoV` (instantiate with the axiom-clean `no_typeV_maximal_unconditional`,
`S12_Noncoherence`; issue 9087), so `M_F ≠ M_σ` and `T` is Type III or IV. Excluding Type IV — the
genuine (11.9) Galois/character
content — is the isolated residual `T_not_isTypeIV_of_isTypeP1`.  The Type-V exclusion and the
III/IV
structural wiring (incl. the `TypeIIIData.normalizer_le` field, bundled into the clause-(c)
disjunction) are proven here. -/
theorem T_isTypeIII_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    OddOrder.GroupTheory.IsTypeIII hyp.base.T := by
  -- Type dictionary (BG Prop 16.1): `IsTypeP1 T` ⟹ III/IV (`M_F ≠ M_σ`) or V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
  -- Type V excluded universally by the (10.10) hypothesis `hnoV`, so `M_F ≠ M_σ`.
  have hMF : OddOrder.BG.Ch4.S15.MF hyp.base.T ≠ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := fun h =>
    hnoV ⟨hyp.base.T, hyp.base.T_maximal, hdV.mpr ⟨hP1, h⟩⟩
  -- `T` is Type III or IV; exclude IV by the (11.9) residual.
  exact (hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right (T_not_isTypeIV_of_isTypeP1 hG hyp hP1)

/-- **Peterfalvi (14.9), reduced to its canonical residual.**  Starting from the symmetric
(13.1) non-type-I carrier, `T` is sharpened to BG type `P₂` (`κ(T) ≠ σ'(T)`; Coq `PFsection14`
`FTtypeP_min_typeII : FTtype T == 2`).  The `IsTypeP T` conjunct is discharged honestly from
`T_nonI` (`isTypeP_of_isTypeNonI`).

The residual `κ(T) ≠ σ'(T)` is proved by the (14.9) contradiction, following Coq
`FTtypeP_min_typeII` (`apply: contraLR v1p_gt_u1q => notTtype2`): were `κ(T) = σ'(T)` (i.e.
`IsTypeP1 T`), then `T` is Type III (`T_isTypeIII_of_isTypeP1`, the `FTtype34_structure`
determination), whence the character body forces `(v − 1)/p ≤ (u − 1)/q` (`T_typeIII_ratio_le`) —
contradicting (14.8) `key_inequality`'s `(v − 1)/p > (u − 1)/q`.

The two deep pieces are isolated as `T_typeIII_ratio_le` (character body) and
`T_isTypeIII_of_isTypeP1` (type determination), both consumed below.  The `>` half is (14.8): its
pure cyclotomic comparison lives upstream in `KeyInequalityArithmetic`, while the two
group-theoretic
order inputs are the direct (13.4) producer `T_side_caseB_facts` and the (13.15) producer
`Hypothesis.u_le_cyclotomicQuotient`.  Thus no forward reference through the later
`key_inequality` theorem is needed. -/
theorem T_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.base.T_maximal hyp.base.T_nonI
  refine ⟨hP, ?_⟩
  -- (14.9), by contradiction (Coq `contraLR v1p_gt_u1q => notTtype2`): assume `κ(T) = σ'(T)`.
  intro hκeq
  -- Then `T` is type `P₁`, hence (Coq `FTtype34_structure`) structurally Type III.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := ⟨hP, hκeq⟩
  have hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T := T_isTypeIII_of_isTypeP1 hG hnoV hyp hP1
  -- The character body then gives the type-III Γ-bridge estimate `(v − 1)/p ≤ (u − 1)/q`.
  have hle : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) :=
    T_typeIII_ratio_le hG hnoV hncH0C hyp hIII
  -- The arithmetic half of (14.8), separated from the later `key_inequality` packaging.
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  -- Its T-side order input is the direct (13.4) producer, which is upstream of `T_isTypeP2`.
  have hvfull := (T_side_caseB_facts hG hyp).2
  -- The required S-side upper bound is the unconditional cyclotomic quotient estimate.
  have hu_le_full :
      hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    hyp.base.u_le_cyclotomicQuotient hG
  have hqpos : (0 : ℚ) < hyp.base.q := by
    exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right hu_le_full 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  have hgt : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
    rw [hvfull]
    exact lt_of_le_of_lt hu_div hratio
  exact absurd hle (not_le.mpr hgt)

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II.  `T` is of type `P₂`
(`T_isTypeP2`), and *every* type-`P₂` maximal subgroup is type II by the proven BG bridge
`isTypeII_of_isTypeP2`.  That bridge discharges
the deep `M'`-type-`F` structure — `IsTypeF (derivedInG T)` and `(T')_F = T_F` — internally
(`isTypeF_derivedInG_of_isTypeP2`), so the sole residual of (14.9) is the type-`P₂` fact
`T_isTypeP2`.
(Placed ahead of `exists_LHypothesis` so the §14 `T`-side chain — `typeII_overNormalizer_frobenius`
etc. — can cite `IsTypeII T` locally.) -/
theorem T_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.T_maximal (T_isTypeP2 hG hnoV hncH0C hyp)

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- `V` normalizes `Q` (`T`-side dual of `U_le_normalizer_P`): `Q = F(T)` is normal in `T` and
`V ≤ T' = Q V ≤ T` (`T_deriv_eq_QV`). -/
theorem V_le_normalizer_Q (hyp : Hypothesis (G := G)) :
    hyp.base.V ≤ Subgroup.normalizer hyp.base.Q := by
  have hV_le_deriv : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have hderiv_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hT_le_norm : hyp.base.T ≤ Subgroup.normalizer hyp.base.Q := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  exact (hV_le_deriv.trans hderiv_le_T).trans hT_le_norm

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b) for `T`**: `Q` is elementary abelian (13.2.b applied to the dual subgroup
`T`) — the canonical §15 obligation `Q_elementaryAbelian_T` (`T` type-II from `T_typeII` (14.9)). -/
theorem Q_elemAbelian_S [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
  OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T _hG hyp.base (T_typeII _hG hnoV hncH0C hyp)

open scoped IsMulCommutative in
/-- **Peterfalvi (13.2.a) for `T`**: the `T`-side complement `V` is cyclic.  `V` is the abelian
Frobenius kernel of the type-I-over-`N_G(V)` configuration.  This is the `T`/`V`-side dual of the
`S`/`U`-side field-model cyclicity (`exists_pv_field_repr`, still to be built): once the dual Singer
representation `μ : V ↪ 𝔽_{q^p}^×` is constructed from `V` abelian via
`isSimpleModule_of_abelian_faithful_card`, `V` cyclic follows.  Used to transport `K = V` (14.11) to
`K` cyclic in `MHypothesis_kernel_cyclic`. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) : IsCyclic ↥hyp.base.V := by
  let : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  have : NeZero hyp.base.q := ⟨hyp.base.q_prime.ne_zero⟩
  have hTII : IsTypeII hyp.base.T := T_typeII hG hnoV hncH0C hyp
  have hQea : IsElementaryAbelian hyp.base.q ↥hyp.base.Q := Q_elemAbelian_S hG hnoV hncH0C hyp
  have hQcomm : IsMulCommutative ↥hyp.base.Q := IsMulCommutative.of_comm hQea.comm
  let hVcomm : CommGroup ↥hyp.base.V :=
    { (inferInstance : Group ↥hyp.base.V) with
      mul_comm := fun a b =>
        (isMulCommutative_iff.mp
          (OddOrder.Peterfalvi.S15.isMulCommutative_V hG hyp.base hTII)) a b }
  -- `|V| = v = (q^p - 1)/(q - 1)`: `d = 1` from `D = V ⊓ C_G(Q) = ⊥` (13.12 dual), plus the
  -- `v`-value (14.4) `T_side_caseB_facts`.
  have hv_full : Nat.card ↥hyp.base.V =
      (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact hyp.V_inf_centralizer_Q_eq_bot hG
    have hd1 : hyp.base.d = 1 := by rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
    rw [hyp.base.card_V_eq_vd, hd1, mul_one]
    exact (T_side_caseB_facts hG hyp).2
  have hqsmul : ∀ x : Additive ↥hyp.base.Q, (hyp.base.q : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hQea.pow_eq_one x.toMul
  have hQmod : Module (ZMod hyp.base.q) (Additive ↥hyp.base.Q) :=
    AddCommGroup.zmodModule hqsmul
  -- the conjugation representation of `V` on `Additive ↥Q`
  let conjHom : ↥hyp.base.V →* MulAut ↥hyp.base.Q :=
    (Subgroup.normalizerMonoidHom (H := hyp.base.Q)).comp
      (Subgroup.inclusion (V_le_normalizer_Q hyp))
  let ρ : Representation (ZMod hyp.base.q) ↥hyp.base.V (Additive ↥hyp.base.Q) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥hyp.base.Q hyp.base.q).comp conjHom
  have hρ_apply : ∀ (c : ↥hyp.base.V) (a : Additive ↥hyp.base.Q),
      ρ c a = Additive.ofMul ((conjHom c) (Additive.toMul a)) := fun _ _ => rfl
  let hQmodAlg :
      Module (MonoidAlgebra (ZMod hyp.base.q) ↥hyp.base.V) (Additive ↥hyp.base.Q) :=
    Module.compHom (Additive ↥hyp.base.Q) (ρ.asAlgebraHom).toRingHom
  have hof_smul : ∀ (c : ↥hyp.base.V) (a : Additive ↥hyp.base.Q),
      MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • a =
        Additive.ofMul ((conjHom c) (Additive.toMul a)) := by
    intro c a
    have h : MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • a = ρ c a := by
      change (ρ.asAlgebraHom (MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c)) a = ρ c a
      rw [Representation.asAlgebraHom_of]
    rw [h, hρ_apply]
  have hNeZero : NeZero (Nat.card ↥hyp.base.V : ZMod hyp.base.q) := by
    refine ⟨fun h => ?_⟩
    rw [hv_full] at h
    have hdvd : hyp.base.q ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp h
    have hmod : (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) ≡ 1 [MOD hyp.base.q] := by
      have hsum_eq : ∑ k ∈ Finset.range hyp.base.p, hyp.base.q ^ k =
          (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
        Nat.geomSum_eq hyp.base.q_prime.two_le _
      rw [← hsum_eq, show hyp.base.p = (hyp.base.p - 1) + 1 by
          have := hyp.base.p_prime.pos; omega, Finset.sum_range_succ']
      have hzero : (∑ k ∈ Finset.range (hyp.base.p - 1), hyp.base.q ^ (k + 1)) ≡ 0
          [MOD hyp.base.q] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact Finset.dvd_sum fun k _ => dvd_pow_self hyp.base.q (Nat.succ_ne_zero k)
      simpa using hzero.add_right 1
    have hdvd1 : hyp.base.q ∣ 1 := by
      have h0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have h01 := h0.symm.trans hmod
      rwa [Nat.modEq_iff_dvd', Nat.sub_zero] at h01
      omega
    exact absurd (Nat.le_of_dvd one_pos hdvd1) (by have := hyp.base.q_prime.two_le; omega)
  have hcardM : Nat.card (Additive ↥hyp.base.Q) = hyp.base.q ^ hyp.base.p :=
    OddOrder.Peterfalvi.S15.card_Q_eq hG hyp.base hTII
  have hfaith : ∀ c : ↥hyp.base.V,
      (∀ x : Additive ↥hyp.base.Q,
          MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • x = x) → c = 1 := by
    intro c hc
    have hcomm : ∀ y : ↥hyp.base.Q, (c : G) * (y : G) = (y : G) * (c : G) := by
      intro y
      have h1 := hc (Additive.ofMul y)
      rw [hof_smul] at h1
      have h2 : (conjHom c) y = y := Additive.ofMul.injective (by simpa using h1)
      have h3 : (c : G) * (y : G) * (c : G)⁻¹ = (y : G) := congrArg Subtype.val h2
      rwa [mul_inv_eq_iff_eq_mul] at h3
    have hmem : (c : G) ∈ hyp.base.D := by
      rw [hyp.base.D_eq]
      exact ⟨c.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm ⟨y, hy⟩).symm)⟩
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact hyp.V_inf_centralizer_Q_eq_bot hG
    rw [hDbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨e0, μ, hμinj, _⟩ :=
    OddOrder.RepresentationTheory.exists_galoisField_repr
      (C := ↥hyp.base.V) (M := Additive ↥hyp.base.Q)
      hyp.base.p_prime hyp.base.p_odd hcardM hv_full hfaith
  -- `μ : V ↪ 𝔽_{q^p}ˣ` is injective and the finite-field unit group is cyclic, so `V` is cyclic.
  exact isCyclic_of_injective μ hμinj

end OddOrder.Peterfalvi.S16
