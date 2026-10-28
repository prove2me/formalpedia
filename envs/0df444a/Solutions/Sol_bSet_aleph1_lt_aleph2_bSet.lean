-- Prove2me | solution 1 for bSet.aleph1_lt_aleph2_bSet
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T02:07:00.294038+00:00
-- url     : https://prove2.me/submissions/c7935ac1-648a-4152-8cd1-a6bac64d0fc6

import Definitions.Def_CH_Cohen_Library10
/-
Physical source: Flypitch, Jesse Han and Floris van Doorn (Apache-2.0).
Lean 4 port: Ian Klatzco, with Claude.
Upstream commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.
Original notices and source statements are retained.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/- Source module: Definitions.Flypitch4.ToMathlib -/
section CohenSource_ToMathlib
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/to_mathlib.lean -/











set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w w'

/-! ## Lean 3 → Lean 4 Port: Renames and Drops

### Renames (for downstream file porters, search counts in src/)

1. `imp_self` → `ba_imp_self` (renamed to avoid collision with Lean 4 core `imp_self`)
   - Call sites: `src/henkin.lean:210`, `src/fol.lean:2097` (2 sites)

2. `le_trans'` → `le_trans_inf` (renamed to avoid collision with mathlib4 `ge_trans` alias and
   Lean 4 core `le_trans'` for lists)
   - Call sites: `src/bfol.lean:706`, `src/bvm.lean:64`, `:2475`, `:2481`,
   `src/bvm_extras.lean:2121`, `:2124` (6 sites)

3. `mk_union_le` → `mk_union_le_impl` (kept as wrapper; mathlib4 has `Cardinal.mk_union_le`)
   - Call site: `src/collapse.lean:570` — when collapse is ported, prefer
   `Cardinal.mk_union_le` over our wrapper

4. `nontrivial.bot_lt_top` → `nontrivial_bot_lt_top` (flattened from sub-namespace dot notation;
   class accessor pattern changes in Lean 4)
   - Call sites: `src/bfol.lean:790`, `src/bvm.lean:1596`, `src/zfc.lean:519`, `:534` (4 sites)

### Drops (declarations removed because they exist in mathlib4)

1. `congr1` and `rexact` tactics (src/to_mathlib.lean:492-510)
   - `congr1` was a custom tactic used in ~10 downstream Lean 3 proof sites
   - In Lean 4, `congr 1` (with a space) is a built-in tactic
   - When porting `fol`, `henkin`, `language_extension`, etc., translate `congr1` (no space) to
   `congr 1` (with space) inline rather than re-implementing

2. `complete_degenerate_boolean_algebra` (src/to_mathlib.lean:756)
   - Replaced by mathlib4's `PUnit.instCompleteBooleanAlgebra` in
   `Mathlib/Order/CompleteBooleanAlgebra.lean`
   - No downstream `src/` file uses this directly
-/

/-!
## function namespace

`Function.Injective.ne_iff` already exists in mathlib4. No redeclaration needed.
-/

/-! ## dvector type and namespace -/







namespace DVec

variable {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

































































































































end DVec

/-! ## set namespace -/

namespace Set









-- subset_sInter_iff is already in Mathlib as Set.subset_sInter_iff



end Set

/-! ## topological_space section -/

section TopologicalSpace

open TopologicalSpace Set Filter

variable {α : Type u} {β : Type v}
variable [t : TopologicalSpace α] [TopologicalSpace β]











end TopologicalSpace

/-! ## ordinal namespace -/

namespace Ordinal

variable {σ : Type*}





end Ordinal

/-! ## cardinal namespace -/

namespace Cardinal

open scoped Cardinal

-- Note: Cardinal.mk_union_le already exists in mathlib4 (explicit args version).
-- Downstream files use `mk_union_le` with implicit args; that's directly served
-- by the mathlib4 version since Lean can infer the args. No redeclaration needed.
-- The alias below makes it available for direct call without name conflicts:










end Cardinal

/-! ## nat namespace -/

namespace Nat





end Nat

/-! ## classical namespace (logic helpers) -/

namespace Classical











end Classical

/-! ## list namespace -/

namespace List







end List

/-! ## additional nat lemmas -/

namespace Nat



end Nat

/-! ## misc prop lemmas -/





/-! ## additional set lemmas -/

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}



























end Set

/-! ## nonempty namespace -/

namespace Nonempty

variable {α : Sort u} {β : Sort v}



end Nonempty

/-! ## arity' type and namespace -/



namespace Arity'

































end Arity'

/-! ## Miscellaneous lemmas -/



/-! ## Boolean algebra / lattice helpers -/













-- iSup/iInf distributivity (aliases for Lean 4 mathlib names)
private theorem inf_iSup_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    a ⊓ (⨆ (i : ι), s i) = ⨆ (i : ι), a ⊓ s i :=
  inf_iSup_eq a s

private theorem iSup_inf_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    (⨆ (i : ι), s i) ⊓ a = ⨆ (i : ι), (s i ⊓ a) := by
  rw [inf_comm, inf_iSup_eq']; simp_rw [inf_comm]





-- Aliases without `@[simp]`: mathlib4's `inf_idem`/`sup_idem` already carry `@[simp]`,
-- so adding `@[simp]` here would create duplicate rewrite rules.




-- Note: bot_lt_iff_not_le_bot and lt_top_iff_not_top_le already exist in mathlib4












open scoped Flypitch




























-- Note: Lean 4 already has a `imp_self` in core; use `ba_imp_self` for Boolean algebra version







private theorem le_of_sub_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : bᶜ ⊓ a = ⊥) : a ≤ b := by
  rw [inf_comm] at h
  exact disjoint_compl_right_iff.mp (disjoint_iff.mpr h)

private theorem le_neg_of_inf_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : b ⊓ a = ⊥) :
    a ≤ bᶜ := by
  apply le_of_sub_eq_bot; rwa [compl_compl]















-- Aliases without `@[simp]`: mathlib4's `iSup_option`/`iInf_option` already carry `@[simp]`.








































-- Note: le_trans' already exists in Mathlib (as alias for ge_trans)
-- Use le_trans_inf for our version















































private theorem nonzero_wit {β : Type*} [CompleteLattice β] {ι : Type*} {s : ι → β} :
    (⊥ < ⨆ i, s i) → ∃ j, ⊥ < s j := by
  intro H
  by_contra h
  push_neg at h
  simp only [bot_lt_iff_ne_bot, ne_eq, not_not] at h
  have key : ⨆ i, s i = ⊥ :=
    le_antisymm (iSup_le (fun j => (h j).le)) bot_le
  exact absurd (key ▸ H) (lt_irrefl ⊥)

private theorem nonzero_inf_of_nonzero_le_supr {α : Type*} [CompleteDistribLattice α] {ι : Type*}
    {s : ι → α} {Γ : α} (H_nonzero : ⊥ < Γ) (H : Γ ≤ ⨆ i, s i) : ∃ i, ⊥ < Γ ⊓ s i := by
  by_contra H'
  push_neg at H'
  simp only [bot_lt_iff_not_le_bot, not_not] at H'
  have H_absorb : Γ ⊓ ⨆ (i : ι), s i = Γ :=
    le_antisymm inf_le_left (le_inf le_rfl H)
  have : Γ ⊓ ⨆ (i : ι), s i ≤ ⊥ := by
    rw [inf_iSup_eq']; exact iSup_le H'
  rw [H_absorb] at this
  exact absurd (lt_of_lt_of_le H_nonzero this) (lt_irrefl ⊥)

private theorem nonzero_wit' {β : Type*} [CompleteDistribLattice β] {ι : Type*} {s : ι → β} {Γ : β}
    (H_nonzero : ⊥ < Γ) (H_le : Γ ≤ ⨆ i, s i) : ∃ j, ⊥ < s j ⊓ Γ := by
  obtain ⟨j, hj⟩ := nonzero_inf_of_nonzero_le_supr H_nonzero H_le
  exact ⟨j, by rwa [inf_comm]⟩











/-! ## tactic.interactive section — DEFERRED

  The tactic extensions (bv_intro, bv_cases_at, bv_or_elim_at, specialize_context,
  bv_split, bv_and_intro, bv_imp_elim_at, bv_mp, bv_imp_intro, bv_split_goal,
  bv_or_inr, bv_or_inl, bv_contradiction, tidy_context, bv_exfalso,
  bv_cases_on, bv_exists_intro, bv_specialize_at, bv_to_pi, bv_to_pi') need
  a complete rewrite for Lean 4's macro/elab system.

  These are deferred until downstream files actually need them.
  - Main block: See src/to_mathlib.lean:1252-1684 for the original definitions.
  - Early block also deferred: src/to_mathlib.lean:492-510 contained `congr1` and `rexact`
    tactics. `congr1` is used in roughly 10 downstream Lean 3 proof sites. In Lean 4,
    `congr 1` (with a space) is a built-in tactic, so when porting `fol`, `henkin`,
    `language_extension`, etc., translate `congr1` (no space) to `congr 1` (with space)
    inline rather than re-implementing the tactic.
-/

-- with_h_asms helper definition



end CohenSource_ToMathlib

/- Source module: Definitions.Flypitch4.PSetOrdinal -/
section CohenSource_PSetOrdinal
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/pSet_ordinal.lean (lines 1-500) — Task 6a -/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
## Port notes (src/pSet_ordinal.lean → Flypitch4.PSetOrdinal)

### Key API renames

- `tactic.tidy` → `aesop` / `simp` / hand proofs
- `ordinal.limit_rec_on` → `induction η using Ordinal.limitRecOn`
- `ordinal.is_limit` → `Order.IsSuccLimit`
- `ordinal.lt_succ` / `lt_succ_self` → `Order.lt_succ`
- `ordinal.succ η` → `Order.succ η`
- `pSet` → `PSet`; `pSet.equiv` → `PSet.Equiv`; `pSet.mem.mk` → `PSet.Mem.mk`
- `pSet.succ x = insert x x` → `PSet.succ_ord x`
- `ordinal.mk` (Lean 3) → `Ordinal.toPSet` (mathlib4, aliased as `PSet.ordinalMk`)
- `mem_Union` → `PSet.mem_sUnion`
- `Set` (Lean 3 ZFC quotient) → `ZFSet`
- `Set.regularity` → `ZFSet.regularity`
- `push_neg` → `push Not` (deprecated, warning only)
- `ZFSet.not_mem_empty` → `ZFSet.notMem_empty`
- `⟦x⟧ : ZFSet` → `ZFSet.mk x` (more reliable elaboration)
- `typein` (in PSet namespace) → `Ordinal.typein` (fully qualified)
- `PSet.Type ∅ = PEmpty` (not `ULift Empty` as in Lean 3)
- `ordinal.mk_zero_type` etc: adapted to mathlib4 universe conventions

### Namespace choices for 6b, 6c

All declarations in `namespace PSet`.
`ordinalMk = Ordinal.toPSet`.
`succ_ord = insert x x`.
-/

universe u

noncomputable section

-- ============================================================
-- Ordinal namespace: tiny helper
-- ============================================================

namespace Ordinal



end Ordinal

-- ============================================================
-- PSet namespace
-- Lines 30+ of src/pSet_ordinal.lean
-- ============================================================

namespace PSet

-- `ordinalMk η` = `Ordinal.toPSet η` (the von Neumann ordinal as a pre-set).


-- `succ_ord x = insert x x` — the pre-set ordinal successor.
-- Named `succ_ord` to avoid collision with `Order.succ`.


/-! ### Basic structural lemmas -/













-- typein of out.r is less than the ordinal itself


/-! ### Key facts about ordinalMk = Ordinal.toPSet -/

-- The type of `ordinalMk η` is `η.ToType`


-- Membership characterization (the main tool)


-- Elementary membership


-- The zero case: ordinalMk 0 ≡ ∅ (extensionally equivalent)
-- Note: this is Equiv, not equality, since Ordinal.ToType 0 ≠ PEmpty definitionally


-- For convenience in downstream proofs, state the simp lemma for ZFSet


-- For 6b/6c: type of ordinalMk 0 is empty.
-- Note: `Ordinal.ToType 0` is the empty type (mathlib provides
-- `isEmpty_toType_zero`) but it is not definitionally `PEmpty`, so we state
-- the result as `IsEmpty` rather than `= PEmpty`.


-- Successor: membership in ordinalMk(succ η) ↔ in ordinalMk η or ≡ ordinalMk η


-- `succ_ord`: the type is Option



















-- The type of ordinalMk for a limit ordinal is η.ToType




/-! ### Epsilon well-orders and pre-set ordinals -/

















-- PSet membership ↔ ZFSet membership






-- Helpers for insert membership


















-- Type of empty PSet is PEmpty (mathlib4: `PSet.empty = ⟨_, PEmpty.elim⟩`)
























-- Ord is invariant under PSet.Equiv


-- Key: ordinalMk (Order.succ η) ≡ succ_ord (ordinalMk η)
















-- card_ex: cardinal → PSet via ordinal


-- WARNING: is_func corresponds to bSet.is_function, not bSet.is_func
-- f ⊆ prod x y ∧ ∀z ∈ x, ∃! w, pair z w ∈ f








-- ============================================================
-- Task 6b additions: lines 512-1000 of src/pSet_ordinal.lean
-- ============================================================

/-! ### Injectivity of ordinalMk (src lines 512-618) -/









/-! ### Cardinal type size lemmas (src lines 620-666) -/





















/-! ### Ordinal arithmetic helpers (src lines 668-697) -/

open Cardinal in
private lemma two_eq_succ_one : (2 : Ordinal) = Order.succ 1 := by
  rw [Order.succ_eq_add_one]
  norm_cast





open Cardinal in
private lemma aleph_two_eq_succ_aleph_one :
    Cardinal.aleph 2 = Order.succ (Cardinal.aleph 1) := by
  -- succ_aleph : Order.succ (aleph o) = aleph (o + 1)
  -- so aleph (1 + 1) = aleph 2 and Order.succ (aleph 1) = aleph (1 + 1)
  have h2 : (2 : Ordinal) = 1 + 1 := two_eq_succ_one ▸ (Order.succ_eq_add_one 1).symm
  rw [h2, ← Cardinal.succ_aleph]

open Cardinal in
private lemma aleph_one_eq_succ_aleph_zero :
    Cardinal.aleph 1 = Order.succ ℵ₀ := by
  exact Cardinal.succ_aleph0.symm

open Cardinal in
private lemma is_regular_aleph_one : Cardinal.IsRegular (Cardinal.aleph 1) := by
  rw [aleph_one_eq_succ_aleph_zero]
  exact Cardinal.isRegular_succ le_rfl

open Cardinal in
private lemma is_regular_aleph_two : Cardinal.IsRegular (Cardinal.aleph 2) := by
  rw [aleph_two_eq_succ_aleph_one]
  exact Cardinal.isRegular_succ (Cardinal.aleph0_le_aleph 1)







/-! ### Subset helpers (src lines 698-704) -/





/-! ### ofNat lemmas (src lines 706-768) -/
-- In mathlib4, Lean 3's `of_nat` is `PSet.ofNat`.
-- Lean 3 omega.type = ℕ-indexed; mathlib4 uses ULift ℕ.

















/-! ### Transitivity and well-orders for omega (src lines 770-800) -/











/-! ### Pair and product for pSets (src lines 945-984) -/













/-! ### Injection predicates (src lines 986-990) -/







/-! ### Subset characterization via ZFSet (src/pSet_ordinal.lean:994-1000) -/



-- ============================================================
-- Task 6c additions: lines 1000-1391 of src/pSet_ordinal.lean
-- ============================================================

/-! ### is_func characterization (src lines 1002-1045) -/









/-! ### powerset_sound (src line 1047) -/



/-! ### set_of_indicator, functions, mem_functions_iff (src lines 1049-1067) -/







/-! ### card_ex_aleph_exists_mem (src line 1071) -/



/-! ### function.mk and related (src lines 1080-1132) -/

namespace function_mk









end function_mk

/-! ### P_ext predicate (src lines 1144-1161) -/











/-! ### mem_sep_iff (src line 1163) -/

-- PSet.sep for P_ext-respecting predicates
-- Note: must use `PSet.sep p x` explicitly (not `{z ∈ x | p z}` which resolves to Set.sep)


/-! ### sep_subset (src line 1134) -/



/-! ### sep_equiv_iff (src line 1179) -/



/-! ### mem_two (src line 1186) -/



/-! ### pair_mem.congr_right/left (src lines 1194-1215) -/









/-! ### section injects_powerset (src lines 1218-1369) -/

section injects_powerset

variable {x : PSet.{u}}

-- Abbreviation for functions x {0,1}


-- Predicate: "z maps to 0 under χ"


-- For each function χ in fx2, the "preimage of 0" subset of x


















-- Auxiliary: sep for predicate "pair z k ∈ w" is P_ext-respecting








end injects_powerset

/-! ### eq_of_is_func_of_eq (src line 1372) -/



/-! ### exists_mem_of_nonzero, exists_mem_of_regular (src lines 1384-1388) -/

private lemma exists_mem_of_nonzero {η : Ordinal} (H_nonzero : 0 < η) :
    ∃ z : PSet, z ∈ ordinalMk η :=
  ⟨ordinalMk 0, mk_mem_mk_of_lt H_nonzero⟩

open Cardinal in
private lemma exists_mem_of_regular {κ : Cardinal} (H_reg : Cardinal.IsRegular κ) :
    ∃ z : PSet, z ∈ card_ex κ :=
  exists_mem_of_nonzero H_reg.ord_pos

end PSet

end -- noncomputable section


end CohenSource_PSetOrdinal

/- Source module: Definitions.Flypitch4.Bvm -/
section CohenSource_Bvm
set_option autoImplicit false
local notation "ω'" => _root_.bSet.ω'
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bvm.lean lines 1-700 — Task 10a -/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch

/-! ## Namespace Lattice — natural deduction lemmas in BA -/

namespace Lattice

section natded
variable {𝔹 : Type*} [CompleteBooleanAlgebra 𝔹]

-- src/bvm.lean:21


-- src/bvm.lean:25


-- src/bvm.lean:29


-- src/bvm.lean:33


-- src/bvm.lean:37
private lemma bv_or_elim {b₁ b₂ c : 𝔹} (h : b₁ ≤ c) (h' : b₂ ≤ c) : b₁ ⊔ b₂ ≤ c :=
  sup_le h h'

-- src/bvm.lean:40


-- src/bvm.lean:43


-- src/bvm.lean:46
private lemma bv_exfalso {a b : 𝔹} (h : a ≤ ⊥) : a ≤ b :=
  le_trans h bot_le

-- src/bvm.lean:49


-- src/bvm.lean:53


-- src/bvm.lean:57


-- src/bvm.lean:61


-- src/bvm.lean:68


-- src/bvm.lean:72


-- src/bvm.lean:78


-- src/bvm.lean:82


-- src/bvm.lean:88


-- src/bvm.lean:91


-- src/bvm.lean:94


-- src/bvm.lean:97


-- src/bvm.lean:107


-- src/bvm.lean:122


-- src/bvm.lean:124


-- src/bvm.lean:126


-- src/bvm.lean:128 (bv_and.left → bv_and_left)


-- src/bvm.lean:131 (bv_and.right → bv_and_right)


-- src/bvm.lean:134


-- src/bvm.lean:137
private lemma bv_imp_intro_lemma {a b c : 𝔹} (h : a ⊓ b ≤ c) : a ≤ b ⟹ c := by
  rwa [deduction] at h

-- src/bvm.lean:140


-- src/bvm.lean:143


-- src/bvm.lean:146


-- src/bvm.lean:149


-- src/bvm.lean:152


-- src/bvm.lean:155


end natded
end Lattice

open Lattice

universe u

/-! ## pSet namespace — small additions -/

namespace PSet

-- src/bvm.lean:173-184


end PSet

/-! ## bSet — boolean-valued model of ZFC -/

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.


namespace bSet

open scoped Flypitch

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]



-- src/bvm.lean:203


-- src/bvm.lean:206


-- src/bvm.lean:208


-- src/bvm.lean:211


-- src/bvm.lean:215


-- src/bvm.lean:218


-- src/bvm.lean:221






-- src/bvm.lean:229


-- src/bvm.lean:232


-- src/bvm.lean:238






-- src/bvm.lean:255






-- src/bvm.lean:269


-- src/bvm.lean:278


-- src/bvm.lean:281




-- src/bvm.lean:286


-- src/bvm.lean:295


-- src/bvm.lean:298


-- src/bvm.lean:302


-- src/bvm.lean:305




-- src/bvm.lean:310


-- src/bvm.lean:313


-- src/bvm.lean:316


-- src/bvm.lean:319


-- src/bvm.lean:322


-- src/bvm.lean:328


-- src/bvm.lean:331


-- src/bvm.lean:334


-- src/bvm.lean:338


-- src/bvm.lean:341


-- src/bvm.lean:354




-- src/bvm.lean:361


-- src/bvm.lean:366


-- src/bvm.lean:381


-- src/bvm.lean:387


-- src/bvm.lean:393


-- src/bvm.lean:396


-- src/bvm.lean:399


-- src/bvm.lean:402


-- src/bvm.lean:406


-- src/bvm.lean:413


-- src/bvm.lean:472


-- src/bvm.lean:476


-- src/bvm.lean:478


-- src/bvm.lean:485


-- src/bvm.lean:493


-- src/bvm.lean:504


-- src/bvm.lean:514


-- src/bvm.lean:518


-- src/bvm.lean:531


-- src/bvm.lean:544


-- src/bvm.lean:549


-- src/bvm.lean:555


-- src/bvm.lean:560


-- src/bvm.lean:563


-- src/bvm.lean:566


-- src/bvm.lean:576


-- src/bvm.lean:587


-- src/bvm.lean:603


-- src/bvm.lean:616


-- src/bvm.lean:626


-- src/bvm.lean:634


-- src/bvm.lean:639


-- src/bvm.lean:642


-- src/bvm.lean:645


-- src/bvm.lean:648


-- src/bvm.lean:651


-- src/bvm.lean:654


-- src/bvm.lean:657


-- src/bvm.lean:660


-- src/bvm.lean:668


-- src/bvm.lean:676


-- src/bvm.lean:684


-- src/bvm.lean:687


-- src/bvm.lean:690


-- src/bvm.lean:693


-- src/bvm.lean:698


-- src/bvm.lean:702 (dropping the meta-tactic autoParam on H and H')


-- src/bvm.lean:712


-- src/bvm.lean:719


-- src/bvm.lean:723


-- src/bvm.lean:727


-- src/bvm.lean:729


-- src/bvm.lean:732


-- src/bvm.lean:742


-- src/bvm.lean:746


-- ============================================================
-- Task 10b: src/bvm.lean lines 750-1400
-- is_definite, empty lemmas, insert1 congr, singletons,
-- mixture, mixing_lemma, smallness, well_ordering,
-- mixing_corollaries, smallness', cores
-- ============================================================

-- src/bvm.lean:817


-- src/bvm.lean:819


-- src/bvm.lean:825


-- src/bvm.lean:828


-- src/bvm.lean:830


-- src/bvm.lean:833


-- src/bvm.lean:839


-- src/bvm.lean:845


-- src/bvm.lean:852


-- src/bvm.lean:842


-- src/bvm.lean:855


/-! ### singleton lemmas -/

-- src/bvm.lean:860


-- src/bvm.lean:863


-- src/bvm.lean:874


-- src/bvm.lean:877


-- src/bvm.lean:879


-- src/bvm.lean:881


-- src/bvm.lean:883


-- src/bvm.lean:885


/-! ### mixture / mixing lemma -/

-- src/bvm.lean:899


-- src/bvm.lean:904


-- src/bvm.lean:908


-- src/bvm.lean:921


-- src/bvm.lean:925


-- src/bvm.lean:933


-- src/bvm.lean:914


-- src/bvm.lean:937 — Mixing Lemma


-- src/bvm.lean:954


-- src/bvm.lean:957


/-! ### smallness -/

section smallness
variable {ϕ : bSet 𝔹 → 𝔹}

-- src/bvm.lean:988


-- src/bvm.lean:992


-- src/bvm.lean:995


-- src/bvm.lean:998


-- src/bvm.lean:1007


/-! ### well_ordering -/

section well_ordering
variable {α : Type*} (r : α → α → Prop) [IsWellOrder α r]
local infix:50 " ≺ " => r

-- src/bvm.lean:1013


-- src/bvm.lean:1015


-- src/bvm.lean:1017


end well_ordering

variable (r : type (@B_small_witness _ _ ϕ) → type (@B_small_witness _ _ ϕ) → Prop)
variable [IsWellOrder _ r]
local infix:50 " ≺ " => r

-- src/bvm.lean:1029


-- src/bvm.lean:1036


-- src/bvm.lean:1045


-- src/bvm.lean:1048


-- src/bvm.lean:1050


-- src/bvm.lean:1053


-- src/bvm.lean:1060


-- src/bvm.lean:1075
-- Note: the Lean 3 `antichain` means pairwise inf = ⊥, which is exactly witness_antichain_index.
-- The Lean 4 IsAntichain (· ≤ ·) is a different (unprovable here) notion, so we state the
-- correct pairwise-disjoint version.


-- src/bvm.lean:1082


-- src/bvm.lean:1085


end smallness

/-! ### maximum principle and AE_convert -/

-- src/bvm.lean:1107


-- src/bvm.lean:1131


-- src/bvm.lean:1134


-- src/bvm.lean:1138


-- src/bvm.lean:1141


-- src/bvm.lean:1155


-- src/bvm.lean:1164


/-! ### mixing corollaries -/

section mixing_corollaries

-- src/bvm.lean:1175-1208
variable (X u₁ u₂ : bSet 𝔹) (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (h_partition : a₁ ⊔ a₂ = ⊤)

-- src/bvm.lean:1178


-- src/bvm.lean:1192


end mixing_corollaries

/-! ### core_aux_lemma -/

-- src/bvm.lean:1210


-- src/bvm.lean:1229


/-! ### smallness' -/

section smallness'
variable {α : Type u} (ϕ' : bSet 𝔹 → α)

-- src/bvm.lean:1243


end smallness'

/-! ### cores -/

section cores

-- src/bvm.lean:1250


-- src/bvm.lean:1253


-- src/bvm.lean:1256


-- src/bvm.lean:1262


-- src/bvm.lean:1272


-- src/bvm.lean:1282


-- src/bvm.lean:1285


-- src/bvm.lean:1296


-- src/bvm.lean:1299


-- src/bvm.lean:1301


-- src/bvm.lean:1303


-- src/bvm.lean:1306


-- src/bvm.lean:1309


-- src/bvm.lean:1320


-- src/bvm.lean:1331


-- src/bvm.lean:1334


-- src/bvm.lean:1337


-- src/bvm.lean:1376


-- src/bvm.lean:1379


-- src/bvm.lean:1382


-- src/bvm.lean:1384


-- src/bvm.lean:1387


-- src/bvm.lean:1392


-- src/bvm.lean:1397


-- src/bvm.lean:1424
-- (these lemmas have complex `letI` formulations in Lean 3; skipped as auxiliary)


-- src/bvm.lean:1427


-- src/bvm.lean:1430


-- src/bvm.lean:1432


-- src/bvm.lean:1435


-- src/bvm.lean:1438


-- src/bvm.lean:1443


-- src/bvm.lean:1450


-- src/bvm.lean:1459


-- src/bvm.lean:1470


end cores

section check_names

/-! `check` is the canonical embedding of PSet into bSet.
Note that a check-name is not only definite, but recursively definite. -/

-- src/bvm.lean:1479


-- Postfix notation to match Lean 3 `̌ ` postfix notation


-- src/bvm.lean:1484


-- src/bvm.lean:1487


-- src/bvm.lean:1491


-- src/bvm.lean:1494 (this is trivially true in Lean 4)

-- src/bvm.lean:1497


-- src/bvm.lean:1500


-- src/bvm.lean:1503


-- src/bvm.lean:1506


-- src/bvm.lean:1509


-- src/bvm.lean:1512


-- src/bvm.lean:1516


-- src/bvm.lean:1519


-- src/bvm.lean:1521


-- src/bvm.lean:1523


-- src/bvm.lean:1527


-- src/bvm.lean:1530


-- src/bvm.lean:1536


-- src/bvm.lean:1544


-- src/bvm.lean:1556


-- src/bvm.lean:1560


-- src/bvm.lean:1564


-- src/bvm.lean:1573


-- src/bvm.lean:1581


-- src/bvm.lean:1600


-- src/bvm.lean:1609


-- src/bvm.lean:1612


-- src/bvm.lean:1619


-- src/bvm.lean:1625


-- src/bvm.lean:1628


-- src/bvm.lean:1640


-- src/bvm.lean:1650


-- src/bvm.lean:1662


-- src/bvm.lean:1665


-- src/bvm.lean:1671


-- src/bvm.lean:1678


-- src/bvm.lean:1684


-- src/bvm.lean:1691


-- src/bvm.lean:1699


-- src/bvm.lean:1702


-- src/bvm.lean:1713


-- src/bvm.lean:1746


-- src/bvm.lean:1755


-- src/bvm.lean:1762


-- src/bvm.lean:1766


-- src/bvm.lean:1775


-- src/bvm.lean:1787


end check_names

-- src/bvm.lean:1802-1836 — collect definitions (outside section to avoid section var issues)







-- src/bvm.lean:1814


-- src/bvm.lean:1825



-- src/bvm.lean:1844


-- src/bvm.lean:1860


-- src/bvm.lean:1871


-- src/bvm.lean:1888












-- src/bvm.lean:1971


-- src/bvm.lean:1978








-- src/bvm.lean:1993




-- src/bvm.lean:2026 (bSet_axiom_of_powerset' -- stub for downstream usage)
-- TODO: The full statement uses ⨅ (y : x.type) which has elaboration issues in Lean 4.
-- Replacing with equivalent formulation via bv_powerset_spec.
-- lemma bSet_axiom_of_powerset' {Γ : 𝔹} (u : bSet 𝔹) : ... := by sorry

-- src/bvm.lean:2080
-- Auxiliary: bv_powerset unfolds membership






-- src/bvm.lean:2074
-- Note: direct apply le_iInf fails for bSet-indexed iInf with ⇔ involving ⊆ᴮ
-- due to elaboration issue. We use an auxiliary lemma with an explicit u argument.




-- src/bvm.lean:2091


-- src/bvm.lean:2099


-- src/bvm.lean:2102


-- src/bvm.lean:2108






-- src/bvm.lean:2122


-- src/bvm.lean:2132


-- same as mem_subset.mk_iff, but with better ordering of terms on the RHS
-- src/bvm.lean:2137




-- src/bvm.lean:2147


-- src/bvm.lean:2163


-- src/bvm.lean:2169


-- src/bvm.lean:2184


-- src/bvm.lean:2191


-- src/bvm.lean:2199
section infinity
-- ω stands for PSet.omega throughout this section





-- src/bvm.lean:2207














-- src/bvm.lean:2234


















-- src/bvm.lean:2261


-- Helper: PSet-level membership gives check-level membership




-- src/bvm.lean:2270 (one_eq_singleton_zero) -- TODO: singleton notation for bSet
-- lemma one_eq_singleton_zero : Γ ≤ (1 : bSet 𝔹) =ᴮ {(0 : bSet 𝔹)} := by sorry





-- src/bvm.lean:2291


-- example {w : bSet 𝔹} : let ϕ := fun x => ⨅ z, z ∈ᴮ w ⊓ z ⊆ᴮ x ⊓ x ⊆ᴮ z; B_ext ϕ := by simp

end infinity

-- src/bvm.lean:2310








-- src/bvm.lean:2345
-- Auxiliary statement used in regularity_aux (with Γ = ⊤)








-- src/bvm.lean:2375
section zorns_lemma












end zorns_lemma

-- src/bvm.lean:2487
section comprehension
variable (ϕ : bSet 𝔹 → 𝔹) (x : bSet 𝔹) (H_congr : B_ext ϕ)









variable {ϕ} {H_congr}



variable (ϕ) (H_congr)



end comprehension

-- src/bvm.lean:2557










-- src/bvm.lean:2572






end bSet


end CohenSource_Bvm

/- Source module: Definitions.Flypitch4.BvmExtras -/
section CohenSource_BvmExtras
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bvm_extras.lean lines 1-700 — Task 14a -/



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch
open Lattice

universe u

namespace bSet

section extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]





-- src/bvm_extras.lean:24


-- src/bvm_extras.lean:27


-- src/bvm_extras.lean:30


-- src/bvm_extras.lean:33


-- src/bvm_extras.lean:36


-- src/bvm_extras.lean:39


-- src/bvm_extras.lean:42


-- src/bvm_extras.lean:45


-- src/bvm_extras.lean:48


-- src/bvm_extras.lean:56


-- src/bvm_extras.lean:62


-- src/bvm_extras.lean:69


-- src/bvm_extras.lean:78


-- src/bvm_extras.lean:81


-- src/bvm_extras.lean:84




-- src/bvm_extras.lean:88


-- src/bvm_extras.lean:90


-- src/bvm_extras.lean:92


-- src/bvm_extras.lean:94


-- src/bvm_extras.lean:112


-- src/bvm_extras.lean:126


-- src/bvm_extras.lean:132


-- src/bvm_extras.lean:139


-- src/bvm_extras.lean:146


-- src/bvm_extras.lean:150


-- src/bvm_extras.lean:158


-- src/bvm_extras.lean:166


-- src/bvm_extras.lean:179


-- src/bvm_extras.lean:182


-- src/bvm_extras.lean:185


-- src/bvm_extras.lean:204


-- src/bvm_extras.lean:207


-- src/bvm_extras.lean:209


-- src/bvm_extras.lean:216


-- src/bvm_extras.lean:219


-- src/bvm_extras.lean:222


-- src/bvm_extras.lean:225


-- src/bvm_extras.lean:240


-- src/bvm_extras.lean:243


-- src/bvm_extras.lean:246


-- src/bvm_extras.lean:257


-- src/bvm_extras.lean:260


-- src/bvm_extras.lean:263


-- src/bvm_extras.lean:265


-- src/bvm_extras.lean:270


-- src/bvm_extras.lean:273


-- src/bvm_extras.lean:276


-- src/bvm_extras.lean:287


-- src/bvm_extras.lean:297


-- src/bvm_extras.lean:316


-- src/bvm_extras.lean:330


-- src/bvm_extras.lean:333


-- src/bvm_extras.lean:342


-- src/bvm_extras.lean:345


-- src/bvm_extras.lean:349


-- src/bvm_extras.lean:353


-- src/bvm_extras.lean:355


-- src/bvm_extras.lean:357


-- src/bvm_extras.lean:360


-- src/bvm_extras.lean:362


-- src/bvm_extras.lean:366


-- src/bvm_extras.lean:371


-- src/bvm_extras.lean:389


-- src/bvm_extras.lean:392


-- src/bvm_extras.lean:400


-- src/bvm_extras.lean:408


-- src/bvm_extras.lean:411


-- src/bvm_extras.lean:415


-- src/bvm_extras.lean:428


-- src/bvm_extras.lean:441


-- src/bvm_extras.lean:448


-- src/bvm_extras.lean:465


-- src/bvm_extras.lean:489


-- src/bvm_extras.lean:494


-- src/bvm_extras.lean:499


-- src/bvm_extras.lean:506
-- (In Lean 4 port, PSet.pair is PSet.pSet_pair from PSetOrdinal.lean)


-- Auxiliary: propositional equality check (pSet_pair a b) = pair (check a) (check b)


-- src/bvm_extras.lean:514
-- (In Lean 4 port, PSet.prod is PSet.pSet_prod from PSetOrdinal.lean)


-- src/bvm_extras.lean:535


-- src/bvm_extras.lean:538


-- src/bvm_extras.lean:548


-- src/bvm_extras.lean:551


-- src/bvm_extras.lean:561


-- src/bvm_extras.lean:565


-- src/bvm_extras.lean:568
private lemma is_total_iff_is_total' {Γ : 𝔹} {x y f} :
    Γ ≤ is_total x y f ↔ Γ ≤ is_total' x y f := by
  -- Prove is_total = is_total' at the value level, then rewrite
  -- bounded_forall converts ⨅ i, x.bval i ⟹ ψ (x.func i) ↔ ⨅ w, w ∈ x ⟹ ψ w
  -- bounded_exists converts ⨆ j, y.bval j ⊓ ϕ (y.func j) ↔ ⨆ w, w ∈ y ⊓ ϕ w
  -- Prove is_total = is_total' using bounded_forall and bounded_exists
  suffices h : is_total x y f = is_total' x y f by rw [h]
  simp only [is_total, is_total']
  -- Step 1: expand inner ⨆ on LHS via bounded_exists
  have inner_eq : ∀ w₁ : bSet 𝔹, (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
      (⨆ j : y.type, y.bval j ⊓ pair w₁ (y.func j) ∈ᴮ f) :=
    fun w₁ => (@bounded_exists 𝔹 _ y (fun w₂ => pair w₁ w₂ ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right)).symm
  -- Step 2: expand outer ⨅ via bounded_forall
  rw [show (⨅ w₁ : bSet 𝔹, w₁ ∈ᴮ x ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
       (⨅ i : x.type, x.bval i ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair (x.func i) w₂ ∈ᴮ f) from
    (@bounded_forall 𝔹 _ x (fun w₁ => ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f)
      (h_congr := fun w₁ w₂ =>
        B_ext_iSup (h := fun w₂ => B_ext_inf B_ext_const B_ext_pair_mem_left) w₁ w₂)).symm]
  congr 1; ext i
  congr 1
  exact inner_eq (x.func i)

-- src/bvm_extras.lean:581




-- src/bvm_extras.lean:588


-- src/bvm_extras.lean:591


-- src/bvm_extras.lean:595


-- src/bvm_extras.lean:604
-- aka function extensionality


-- src/bvm_extras.lean:610
-- aka function extensionality


-- src/bvm_extras.lean:614


-- src/bvm_extras.lean:622
-- bounded image


-- src/bvm_extras.lean:625


-- src/bvm_extras.lean:628


-- src/bvm_extras.lean:638

-- src/bvm_extras.lean:649


-- src/bvm_extras.lean:658


-- src/bvm_extras.lean:668
-- bounded preimage


-- src/bvm_extras.lean:671


-- src/bvm_extras.lean:673




-- src/bvm_extras.lean:687


-- src/bvm_extras.lean:690


-- src/bvm_extras.lean:692


-- src/bvm_extras.lean:694


-- src/bvm_extras.lean:697


-- src/bvm_extras.lean:699


-- ============================================================
-- Task 14b: src/bvm_extras.lean lines 700-1300
-- ============================================================

-- src/bvm_extras.lean:702


-- src/bvm_extras.lean:709


-- src/bvm_extras.lean:716


-- src/bvm_extras.lean:727


-- src/bvm_extras.lean:740


-- src/bvm_extras.lean:757
-- Helper: membership in check f as iSup over indices




-- src/bvm_extras.lean:797


-- src/bvm_extras.lean:800


-- src/bvm_extras.lean:804


-- src/bvm_extras.lean:807


-- src/bvm_extras.lean:810


-- src/bvm_extras.lean:812


-- src/bvm_extras.lean:814


-- src/bvm_extras.lean:821


-- src/bvm_extras.lean:824


-- src/bvm_extras.lean:828


-- src/bvm_extras.lean:868


-- src/bvm_extras.lean:879
-- not really funext since it doesn't use extensionality in an essential way


-- src/bvm_extras.lean:891




-- src/bvm_extras.lean:897


-- src/bvm_extras.lean:900


-- src/bvm_extras.lean:913


-- src/bvm_extras.lean:921


-- src/bvm_extras.lean:931


-- src/bvm_extras.lean:938


-- src/bvm_extras.lean:946


-- src/bvm_extras.lean:950


-- src/bvm_extras.lean:952


-- src/bvm_extras.lean:954


-- src/bvm_extras.lean:963


-- src/bvm_extras.lean:969


-- src/bvm_extras.lean:972


-- src/bvm_extras.lean:981


-- src/bvm_extras.lean:983


-- src/bvm_extras.lean:985
-- larger_than y z = ⨆ S f, S ⊆ y ⊓ is_func' S z f ⊓ is_surj S z f
-- B_ext as function of z:
-- is_total S z f = ⨅ w₁, w₁ ∈ S ⟹ ⨆ w₂, w₂ ∈ z ⊓ pair w₁ w₂ ∈ f
-- is_surj S z f = ⨅ v, v ∈ z ⟹ ⨆ w, w ∈ S ⊓ pair w v ∈ f






-- src/bvm_extras.lean:988
-- larger_than z y = ⨆ S f, S ⊆ z ⊓ is_func' S y f ⊓ is_surj S y f
-- B_ext as function of z: S ⊆ z = ⨅ j, S.bval j ⟹ S.func j ∈ z


-- src/bvm_extras.lean:991
-- injects_into z y = ⨆ f, is_func' z y f ⊓ is_inj f
-- is_func' z y f = is_func f ⊓ is_total z y f
-- is_total z y f = ⨅ w₁, w₁ ∈ z ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
-- B_ext as function of z: w₁ ∈ z changes with z


-- src/bvm_extras.lean:994
-- injects_into y z = ⨆ f, is_func' y z f ⊓ is_inj f
-- B_ext as function of z (in codomain y→z)


-- ============================================================
-- src/bvm_extras.lean lines 1004-1300
-- ============================================================

-- src/bvm_extras.lean:1018
-- The pointed_extension construction: extends a partial surjection f : S ↠ y
-- to a total surjection x ↠ y by mapping elements outside S to b.
-- This definition uses subset.mk over (prod x y).type, with bval encoding
-- the condition.


-- src/bvm_extras.lean:1023


-- src/bvm_extras.lean:1072-1215: All lemmas about pointed_extension
-- These are sorry-stubbed since they require heavy tactic work.

-- src/bvm_extras.lean:1136
private lemma pointed_extension_is_func {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_func (pointed_extension b H_b H_S H_surj) := by
  -- pe = subset.mk φ over prod x y
  set pe := pointed_extension b H_b H_S H_surj
  set φ : (prod x y).type → 𝔹 := fun pr =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ y.func pr.2 =ᴮ b)
  have hpe_eq : pe = subset.mk φ := rfl
  have hmem_pe : ∀ (w v : bSet 𝔹), pair w v ∈ᴮ pe ≤
      ⨆ pr : (prod x y).type, pair w v =ᴮ (prod x y).func pr ⊓ (φ pr ⊓ (prod x y).bval pr) :=
    fun w v => hpe_eq ▸ mem_subset.mk_iff.mp le_rfl
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]
  -- Carry context through first membership iSup
  apply (le_inf (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans (hmem_pe w₁ v₁)))) le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans; apply iSup_le; intro pr₁; obtain ⟨i, j⟩ := pr₁
  simp only [prod_func, prod_bval, φ]
  -- Carry context through second membership iSup
  apply (le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans (hmem_pe w₂ v₂))))) le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans
  apply iSup_le; intro pr₂; obtain ⟨i', j'⟩ := pr₂
  simp only [prod_func, prod_bval, φ]
  -- Name the current context explicitly to enable type inference
  set ctx2 := (pair w₂ v₂ =ᴮ pair (x.func i') (y.func j') ⊓
      (((x.func i' ∈ᴮ S ⟹ pair (x.func i') (y.func j') ∈ᴮ f) ⊓ ((x.func i' ∈ᴮ S)ᶜ ⟹ y.func j' =ᴮ b)) ⊓
        (x.bval i' ⊓ y.bval j'))) ⊓
    ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓
        (((x.func i ∈ᴮ S ⟹ pair (x.func i) (y.func j) ∈ᴮ f) ⊓ ((x.func i ∈ᴮ S)ᶜ ⟹ y.func j =ᴮ b)) ⊓
          (x.bval i ⊓ y.bval j))) ⊓
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ pe ⊓ pair w₂ v₂ ∈ᴮ pe) ⊓ w₁ =ᴮ w₂))
  -- Extract components:
  -- pr₁chunk accessible via inf_le_right.trans inf_le_left
  -- pr₂chunk accessible via inf_le_left
  have hw1xi : ctx2 ≤ w₁ =ᴮ x.func i :=
    inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left))
  have hv1yj : ctx2 ≤ v₁ =ᴮ y.func j :=
    inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right))
  have hw2xi' : ctx2 ≤ w₂ =ᴮ x.func i' :=
    inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left)
  have hv2yj' : ctx2 ≤ v₂ =ᴮ y.func j' :=
    inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right)
  have hw12 : ctx2 ≤ w₁ =ᴮ w₂ := inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hφij : ctx2 ≤ (x.func i ∈ᴮ S ⟹ pair (x.func i) (y.func j) ∈ᴮ f) ⊓
      ((x.func i ∈ᴮ S)ᶜ ⟹ y.func j =ᴮ b) :=
    inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))
  have hφi'j' : ctx2 ≤ (x.func i' ∈ᴮ S ⟹ pair (x.func i') (y.func j') ∈ᴮ f) ⊓
      ((x.func i' ∈ᴮ S)ᶜ ⟹ y.func j' =ᴮ b) :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  -- x.func i =ᴮ x.func i' via w₁=xi, w₁=w₂, w₂=xi'
  have hxi_xi' : ctx2 ≤ x.func i =ᴮ x.func i' :=
    le_trans (le_inf (bv_symm hw1xi) (le_trans (le_inf hw12 hw2xi') bv_eq_trans)) bv_eq_trans
  -- Case split on x.func i ∈ S
  have h_em_i : ctx2 ≤ x.func i ∈ᴮ S ⊔ (x.func i ∈ᴮ S)ᶜ := le_top.trans (by rw [sup_compl_eq_top])
  apply le_trans (le_inf le_rfl h_em_i)
  apply bv_or_elim_right
  · -- Subcase: ctx2 ⊓ x.func i ∈ S ≤ v₁ =ᴮ v₂
    have hmem_S : ctx2 ⊓ x.func i ∈ᴮ S ≤ x.func i ∈ᴮ S := inf_le_right
    have hpair1_f : _ ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
      le_trans (le_inf (inf_le_left.trans (hφij.trans inf_le_left)) hmem_S) bv_imp_elim
    have hmem_S' : _ ≤ x.func i' ∈ᴮ S :=
      bv_rw' (H := bv_symm (inf_le_left.trans hxi_xi')) (h_congr := B_ext_mem_left)
        (H_new := hmem_S)
    have hpair2_f : _ ≤ pair (x.func i') (y.func j') ∈ᴮ f :=
      le_trans (le_inf (inf_le_left.trans (hφi'j'.trans inf_le_left)) hmem_S') bv_imp_elim
    -- is_func f from H_surj: go ctx2 → ctx2 → Γ → is_func' S y f → is_func f
    have his_func : ctx2 ⊓ x.func i ∈ᴮ S ≤ is_func f :=
      is_func_of_is_func' (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans
        (inf_le_left.trans (inf_le_left.trans (H_surj.trans inf_le_left))))))
    have hyfunc_eq : ctx2 ⊓ x.func i ∈ᴮ S ≤ y.func j =ᴮ y.func j' :=
      eq_of_is_func_of_eq his_func (inf_le_left.trans hxi_xi') hpair1_f hpair2_f
    -- v₁ =ᴮ v₂: chain v₁ =ᴮ yj =ᴮ yj' =ᴮ v₂
    exact le_trans (le_inf (le_trans (le_inf (inf_le_left.trans hv1yj) hyfunc_eq) bv_eq_trans)
          (bv_symm (inf_le_left.trans hv2yj')))
        bv_eq_trans
  · -- Subcase: ctx2 ⊓ (x.func i ∈ S)ᶜ ≤ v₁ =ᴮ v₂
    have hnot_S : ctx2 ⊓ (x.func i ∈ᴮ S)ᶜ ≤ (x.func i ∈ᴮ S)ᶜ := inf_le_right
    have hyj_b : _ ≤ y.func j =ᴮ b :=
      le_trans (le_inf (inf_le_left.trans (hφij.trans inf_le_right)) hnot_S) bv_imp_elim
    -- rewrite xi =ᴮ xi' to get xi' ∉ S from xi ∉ S
    have hnot_S' : _ ≤ (x.func i' ∈ᴮ S)ᶜ :=
      bv_rw' (H := bv_symm (inf_le_left.trans hxi_xi'))
        (h_congr := B_ext_neg (h := B_ext_mem_left (y := S))) (H_new := hnot_S)
    have hyj'_b : _ ≤ y.func j' =ᴮ b :=
      le_trans (le_inf (inf_le_left.trans (hφi'j'.trans inf_le_right)) hnot_S') bv_imp_elim
    -- v₁ =ᴮ v₂: chain v₁ =ᴮ yj =ᴮ b =ᴮ yj' =ᴮ v₂ (via bv_symm)
    exact le_trans (le_inf
          (le_trans (le_inf (inf_le_left.trans hv1yj) hyj_b) bv_eq_trans)
          (le_trans (le_inf (bv_symm hyj'_b) (bv_symm (inf_le_left.trans hv2yj'))) bv_eq_trans))
        bv_eq_trans

-- src/bvm_extras.lean:1177
private lemma pointed_extension_is_total {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_total x y (pointed_extension b H_b H_S H_surj) := by
  set pe := pointed_extension b H_b H_S H_surj
  set φ : (prod x y).type → 𝔹 := fun pr =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ y.func pr.2 =ᴮ b)
  -- Helper: pair (x.func i) (y.func j) ∈ pe given the bval conditions
  have hmem_pe_of_bval : ∀ (i : x.type) (j : y.type),
      ∀ {Δ : 𝔹}, Δ ≤ x.bval i → Δ ≤ y.bval j → Δ ≤ φ (i, j) →
      Δ ≤ pair (x.func i) (y.func j) ∈ᴮ pe := by
    intro i j Δ hxi hyj hφ
    show Δ ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]
    apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]
    exact le_inf bv_refl (le_inf hφ (le_inf hxi hyj))
  -- is_total x y pe = ⨅ w₁, w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ pe
  -- Use is_total' form to work with indices directly
  rw [is_total_iff_is_total']
  apply le_iInf; intro i; rw [← deduction]
  -- ctx₀ = Γ ⊓ x.bval i; case split on x.func i ∈ S
  -- Case split on x.func i ∈ S
  have h_split_i : Γ ⊓ x.bval i ≤ (Γ ⊓ x.bval i) ⊓ x.func i ∈ᴮ S ⊔
      (Γ ⊓ x.bval i) ⊓ (x.func i ∈ᴮ S)ᶜ := by
    rw [← inf_sup_left]; simp [sup_compl_eq_top]
  apply le_trans h_split_i; apply bv_or_elim
  · -- Case (Γ ⊓ x.bval i) ⊓ x.func i ∈ S: get v₂ from is_total S y f
    set ctx_iS := (Γ ⊓ x.bval i) ⊓ x.func i ∈ᴮ S
    have hxi_bval : ctx_iS ≤ x.bval i := inf_le_left.trans inf_le_right
    have hxi_mem_S : ctx_iS ≤ x.func i ∈ᴮ S := inf_le_right
    have htotal_S : ctx_iS ≤ is_total S y f :=
      is_total_of_is_func' (inf_le_left.trans (inf_le_left.trans (H_surj.trans inf_le_left)))
    have hget_v : _ ≤ ⨆ v₂, v₂ ∈ᴮ y ⊓ pair (x.func i) v₂ ∈ᴮ f :=
      le_trans (le_inf (le_trans htotal_S (iInf_le _ (x.func i))) hxi_mem_S) bv_imp_elim
    -- Carry through v₂ and get index j from v₂ ∈ y via bounded_exists
    apply le_trans (le_inf hget_v le_rfl); rw [iSup_inf_eq']; apply iSup_le; intro v₂
    -- v₂ ∈ y = ⨆ j, y.bval j ⊓ v₂ =ᴮ y.func j
    -- Context: (v₂ ∈ y ⊓ pair xi v₂ ∈ f) ⊓ ctx_iS
    have hv2_mem_y : (v₂ ∈ᴮ y ⊓ pair (x.func i) v₂ ∈ᴮ f) ⊓ ctx_iS ≤ v₂ ∈ᴮ y :=
      inf_le_left.trans inf_le_left
    apply le_trans (le_inf (hv2_mem_y.trans (le_of_eq mem_unfold)) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro j
    -- ctx_j: set explicit name for inference
    set ctx_j := (y.bval j ⊓ v₂ =ᴮ y.func j) ⊓ ((v₂ ∈ᴮ y ⊓ pair (x.func i) v₂ ∈ᴮ f) ⊓ ctx_iS)
    have hyj_bval : ctx_j ≤ y.bval j := inf_le_left.trans inf_le_left
    have hv2_yj : ctx_j ≤ v₂ =ᴮ y.func j := inf_le_left.trans inf_le_right
    have hpair_f : ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
      bv_rw' (H := bv_symm hv2_yj) (h_congr := B_ext_pair_mem_right)
        (H_new := inf_le_right.trans (inf_le_left.trans inf_le_right))
    -- Provide y.func j (index j) as witness for is_total'
    apply le_iSup_of_le j; refine le_inf hyj_bval ?_
    show ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]; apply le_iSup_of_le (i, j); simp only [prod_func, prod_bval]
    refine le_inf bv_refl (le_inf ?_
      (le_inf (inf_le_right.trans (inf_le_right.trans hxi_bval)) hyj_bval))
    -- φ (i, j) = (xi ∈ S ⟹ pair xi yj ∈ f) ⊓ ((xi ∈ S)ᶜ ⟹ yj = b)
    exact le_inf
      (bv_imp_intro_lemma (le_trans inf_le_left hpair_f))
      (bv_imp_intro_lemma (bv_exfalso (le_trans
        (le_inf (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
          inf_le_right)
        (le_of_eq inf_compl_eq_bot))))
  · -- Case ctx₀ ⊓ (x.func i ∈ S)ᶜ: use b ∈ y
    set ctx_notS := (Γ ⊓ x.bval i) ⊓ (x.func i ∈ᴮ S)ᶜ
    have hxi_bval : ctx_notS ≤ x.bval i := inf_le_left.trans inf_le_right
    have hnot_S : ctx_notS ≤ (x.func i ∈ᴮ S)ᶜ := inf_le_right
    have hb_mem_y : ctx_notS ≤ b ∈ᴮ y := inf_le_left.trans (inf_le_left.trans H_b)
    -- Get j from b ∈ y
    apply le_trans (le_inf (hb_mem_y.trans (le_of_eq mem_unfold)) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro j
    set ctx_jn := (y.bval j ⊓ b =ᴮ y.func j) ⊓ ctx_notS
    have hyj_bval : ctx_jn ≤ y.bval j := inf_le_left.trans inf_le_left
    have hb_yj : ctx_jn ≤ b =ᴮ y.func j := inf_le_left.trans inf_le_right
    -- Provide y.func j (index j) as witness for is_total'
    apply le_iSup_of_le j; refine le_inf hyj_bval ?_
    show ctx_jn ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]; apply le_iSup_of_le (i, j); simp only [prod_func, prod_bval]
    refine le_inf bv_refl (le_inf ?_ (le_inf (inf_le_right.trans hxi_bval) hyj_bval))
    -- φ (i, j)
    exact le_inf
      (bv_imp_intro_lemma (bv_exfalso (le_trans
        (le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans inf_le_right)))
        (le_of_eq inf_compl_eq_bot))))
      (bv_imp_intro_lemma (bv_symm (inf_le_left.trans hb_yj)))

-- src/bvm_extras.lean:1191
private lemma pointed_extension_is_func' {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_func' x y (pointed_extension b H_b H_S H_surj) :=
  le_inf (pointed_extension_is_func H_b H_S H_surj)
         (pointed_extension_is_total H_b H_S H_surj)

-- src/bvm_extras.lean:1198
private lemma pointed_extension_is_surj {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_surj x y (pointed_extension b H_b H_S H_surj) := by
  set pe := pointed_extension b H_b H_S H_surj
  set φ : (prod x y).type → 𝔹 := fun pr =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ y.func pr.2 =ᴮ b)
  -- is_surj x y pe = ⨅ v, v ∈ y ⟹ ⨆ w, w ∈ x ⊓ pair w v ∈ pe
  apply le_iInf; intro v; rw [← deduction]
  -- ctx₀ = Γ ⊓ v ∈ y
  -- Step 1: use is_surj S y f to get w ∈ S ⊓ pair w v ∈ f
  have hfunc'_Sf : Γ ⊓ v ∈ᴮ y ≤ is_func' S y f :=
    inf_le_left.trans (H_surj.trans inf_le_left)
  have hsurj_Sf : Γ ⊓ v ∈ᴮ y ≤ is_surj S y f :=
    inf_le_left.trans (H_surj.trans inf_le_right)
  have hv_mem_y : Γ ⊓ v ∈ᴮ y ≤ v ∈ᴮ y := inf_le_right
  have hget_w : _ ≤ ⨆ w, w ∈ᴮ S ⊓ pair w v ∈ᴮ f :=
    le_trans (le_inf (le_trans hsurj_Sf (iInf_le _ v)) hv_mem_y) bv_imp_elim
  -- Carry context through w
  apply le_trans (le_inf hget_w le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro w
  -- ctx_w = (w ∈ S ⊓ pair w v ∈ f) ⊓ ctx₀
  set ctx_w := (w ∈ᴮ S ⊓ pair w v ∈ᴮ f) ⊓ (Γ ⊓ v ∈ᴮ y)
  have hw_mem_S : ctx_w ≤ w ∈ᴮ S := inf_le_left.trans inf_le_left
  have hpair_wv_f : ctx_w ≤ pair w v ∈ᴮ f := inf_le_left.trans inf_le_right
  -- w ∈ x from H_S : S ⊆ x
  have hw_mem_x : ctx_w ≤ w ∈ᴮ x :=
    mem_of_mem_subset (inf_le_right.trans (inf_le_left.trans H_S)) hw_mem_S
  -- Get index i from w ∈ x
  apply le_trans (le_inf (hw_mem_x.trans (le_of_eq mem_unfold)) le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro i
  -- ctx_i = (x.bval i ⊓ w =ᴮ x.func i) ⊓ ctx_w
  set ctx_i := (x.bval i ⊓ w =ᴮ x.func i) ⊓ ctx_w
  have hxi_bval : ctx_i ≤ x.bval i := inf_le_left.trans inf_le_left
  have hw_xi : ctx_i ≤ w =ᴮ x.func i := inf_le_left.trans inf_le_right
  -- Get index j from v ∈ y
  apply le_trans (le_inf ((inf_le_right.trans (inf_le_right.trans hv_mem_y)).trans
    (le_of_eq mem_unfold)) le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro j
  -- ctx_j = (y.bval j ⊓ v =ᴮ y.func j) ⊓ ctx_i
  set ctx_j := (y.bval j ⊓ v =ᴮ y.func j) ⊓ ctx_i
  have hyj_bval : ctx_j ≤ y.bval j := inf_le_left.trans inf_le_left
  have hv_yj : ctx_j ≤ v =ᴮ y.func j := inf_le_left.trans inf_le_right
  -- xi ∈ S: from hw_xi and hw_mem_S (rewrite w =ᴮ xi to get xi ∈ S from w ∈ S)
  have hxi_mem_S : ctx_j ≤ x.func i ∈ᴮ S :=
    bv_rw' (H := bv_symm (inf_le_right.trans hw_xi))
      (h_congr := B_ext_mem_left)
      (H_new := inf_le_right.trans (inf_le_right.trans hw_mem_S))
  -- pair (x.func i) (y.func j) ∈ f: rewrite pair w v using w=xi and v=yj
  have hpair_ij_f : ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
    bv_rw' (H := bv_symm (pair_congr (inf_le_right.trans hw_xi) hv_yj))
      (h_congr := B_ext_mem_left)
      (H_new := inf_le_right.trans (inf_le_right.trans hpair_wv_f))
  -- Provide x.func i as witness for w in is_surj, with pair (x.func i) v ∈ pe
  apply le_iSup_of_le (x.func i)
  refine le_inf ?_ ?_
  · -- x.func i ∈ x: from x.bval i
    rw [mem_unfold]; apply le_iSup_of_le i
    exact le_inf (inf_le_right.trans hxi_bval) bv_refl
  · -- pair (x.func i) v ∈ pe: first show pair (x.func i) (y.func j) ∈ pe, then rewrite v =ᴮ y.func j
    apply bv_rw' (H := hv_yj) (h_congr := B_ext_pair_mem_right)
    show ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]; apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]
    refine le_inf bv_refl (le_inf ?_ (le_inf (inf_le_right.trans hxi_bval) hyj_bval))
    -- φ (i, j): (xi ∈ S ⟹ pair xi yj ∈ f) ⊓ ((xi ∈ S)ᶜ ⟹ yj = b)
    exact le_inf (bv_imp_intro_lemma (le_trans inf_le_left hpair_ij_f))
      (bv_imp_intro_lemma (bv_exfalso
        (le_trans (le_inf (inf_le_left.trans hxi_mem_S) inf_le_right)
          (le_of_eq inf_compl_eq_bot))))

-- src/bvm_extras.lean:1209
private lemma pointed_extension_spec {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ surjects_onto x y :=
  le_iSup_of_le (pointed_extension b H_b H_S H_surj)
    (le_inf (pointed_extension_is_func' H_b H_S H_surj)
            (pointed_extension_is_surj H_b H_S H_surj))

-- src/bvm_extras.lean:1220
private lemma surjects_onto_of_larger_than_and_exists_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (H_larger_than : Γ ≤ larger_than x y) (H_nonempty : Γ ≤ ⨆ w, w ∈ᴮ y) :
    Γ ≤ surjects_onto x y := by
  -- Extract b from H_nonempty = ⨆ w, w ∈ y
  obtain ⟨b, Hb⟩ := exists_convert H_nonempty B_ext_mem_left
  -- Extract S and f from H_larger_than = ⨆ S, ⨆ f, S ⊆ x ⊓ is_func' S y f ⊓ is_surj S y f
  -- via carry-context
  simp only [larger_than] at H_larger_than
  apply le_trans (le_inf H_larger_than le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro S
  simp_rw [iSup_inf_eq']; apply iSup_le; intro f
  -- ctx = (S ⊆ x ⊓ is_func' S y f ⊓ is_surj S y f) ⊓ Γ
  -- also need b ∈ y: carry it in from Hb
  apply le_trans (le_inf (inf_le_right.trans Hb) le_rfl)
  -- ctx_b = (b ∈ y) ⊓ ((S ⊆ x ⊓ is_func' S y f ⊓ is_surj S y f) ⊓ Γ)
  apply pointed_extension_spec
  · exact inf_le_left  -- b ∈ y
  · exact inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))  -- S ⊆ x
  · -- is_func' S y f ⊓ is_surj S y f
    exact le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
                 (inf_le_right.trans (inf_le_left.trans inf_le_right))

-- src/bvm_extras.lean:1230


-- src/bvm_extras.lean:1238


-- src/bvm_extras.lean:1273


-- src/bvm_extras.lean:1291


-- ============================================================
-- src/bvm_extras.lean lines 1300-1900
-- ============================================================

-- src/bvm_extras.lean:1301
-- Given a surjection f : x ↠ z and an injection g : y ↪ z, lift f along g to a surjection f' : x ↠ y.


-- src/bvm_extras.lean:1306


-- src/bvm_extras.lean:1318


-- src/bvm_extras.lean:1346


-- src/bvm_extras.lean:1362


-- src/bvm_extras.lean:1375


-- src/bvm_extras.lean:1404


-- src/bvm_extras.lean:1410


-- src/bvm_extras.lean:1422


-- src/bvm_extras.lean:1445


-- src/bvm_extras.lean:1457


-- src/bvm_extras.lean:1472


-- src/bvm_extras.lean:1486
-- (locally: ≺ means (larger_than x y)ᶜ, ≼ means injects_into x y)


-- src/bvm_extras.lean:1500


-- ============================================================
-- src/bvm_extras.lean:1513-1604: is_func'_comp section
-- ============================================================

-- src/bvm_extras.lean:1518


-- src/bvm_extras.lean:1521


-- src/bvm_extras.lean:1554


-- src/bvm_extras.lean:1565


-- src/bvm_extras.lean:1576


-- src/bvm_extras.lean:1583


-- src/bvm_extras.lean:1594


-- src/bvm_extras.lean:1606


-- src/bvm_extras.lean:1609


-- src/bvm_extras.lean:1616


-- src/bvm_extras.lean:1619


-- src/bvm_extras.lean:1625


-- src/bvm_extras.lean:1628


-- src/bvm_extras.lean:1636


-- src/bvm_extras.lean:1639


-- src/bvm_extras.lean:1653


-- src/bvm_extras.lean:1692


-- src/bvm_extras.lean:1700


-- src/bvm_extras.lean:1703


-- src/bvm_extras.lean:1705


-- src/bvm_extras.lean:1707


-- src/bvm_extras.lean:1709


-- ============================================================
-- src/bvm_extras.lean:1732-1798: function_mk' section
-- ============================================================

-- src/bvm_extras.lean:1740


-- src/bvm_extras.lean:1757


-- src/bvm_extras.lean:1767


-- src/bvm_extras.lean:1774


-- src/bvm_extras.lean:1780


-- src/bvm_extras.lean:1788


-- ============================================================
-- src/bvm_extras.lean:1800-1888: inj_inverse section
-- ============================================================

-- src/bvm_extras.lean:1806


-- src/bvm_extras.lean:1809


-- src/bvm_extras.lean:1841


-- src/bvm_extras.lean:1850


-- src/bvm_extras.lean:1858


-- src/bvm_extras.lean:1865


-- src/bvm_extras.lean:1875


-- src/bvm_extras.lean:1877


-- src/bvm_extras.lean:1880


-- ============================================================
-- src/bvm_extras.lean:1890-1900: injective_function_inverse section
-- ============================================================

section injective_function_inverse_section
variable {Γ : 𝔹}

-- src/bvm_extras.lean:1892


-- src/bvm_extras.lean:1895


-- src/bvm_extras.lean:1898


end injective_function_inverse_section

-- ============================================================
-- src/bvm_extras.lean:1902-1927: function_eval section
-- ============================================================

-- Helper: get existential from is_total


-- src/bvm_extras.lean:1906


-- src/bvm_extras.lean:1914


-- src/bvm_extras.lean:1921


-- src/bvm_extras.lean:1924


-- ============================================================
-- src/bvm_extras.lean:1930: surjects_onto_of_injects_into
-- ============================================================

-- src/bvm_extras.lean:1930


-- ============================================================
-- src/bvm_extras.lean:1956-1989: functionMk (= function.mk) and check''
-- ============================================================

-- src/bvm_extras.lean:1956: function.mk renamed to functionMk
-- (functionMk' already exists; this is a different construction called function.mk in Lean 3)










-- src/bvm_extras.lean:1972: check' named check'' to avoid collision






-- src/bvm_extras.lean:1978


-- src/bvm_extras.lean:2041


-- ============================================================
-- src/bvm_extras.lean:2080-2136: bot_of_mem_self, bot_of_mem_mem
-- ============================================================

-- src/bvm_extras.lean:2080


-- src/bvm_extras.lean:2093


-- src/bvm_extras.lean:2099


-- src/bvm_extras.lean:2110


-- src/bvm_extras.lean:2131


end extras

-- ============================================================
-- src/bvm_extras.lean:2140-2218: section check (inside bSet namespace)
-- ============================================================

section bSet_check_extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2154


-- src/bvm_extras.lean:2193


-- src/bvm_extras.lean:2203


-- src/bvm_extras.lean:2206


-- src/bvm_extras.lean:2209


-- src/bvm_extras.lean:2215


end bSet_check_extras

-- ============================================================
-- src/bvm_extras.lean:2220-2396: section powerset (inside bSet namespace)
-- ============================================================

section powerset_section
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable (x : bSet 𝔹)

-- src/bvm_extras.lean:2228
-- powerset_injects_F: maps (bv_powerset x).type → (functions x 𝟚).type
-- encodes χ ↦ characteristic function as subset of x × 𝟚


-- src/bvm_extras.lean:2231


-- Helper: under context Γ, if H_ba : χ_b ⊆ χ_a, then compl_a ⊆ compl_b (pointwise under Γ)


-- src/bvm_extras.lean:2249


-- src/bvm_extras.lean:2301


-- src/bvm_extras.lean:2318


-- src/bvm_extras.lean:2377


-- src/bvm_extras.lean:2387


-- src/bvm_extras.lean:2389


end powerset_section

-- ============================================================
-- src/bvm_extras.lean:2212: check_succ_eq_succ_check (needed by omega_is_omega)
-- ============================================================

-- src/bvm_extras.lean:2212


-- ============================================================
-- src/bvm_extras.lean:2398-2747: section ordinals
-- ============================================================

section ordinals
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2401


-- src/bvm_extras.lean:2403


-- src/bvm_extras.lean:2405


-- src/bvm_extras.lean:2408


-- src/bvm_extras.lean:2410


-- src/bvm_extras.lean:2413


-- src/bvm_extras.lean:2420


-- src/bvm_extras.lean:2422


-- src/bvm_extras.lean:2425


-- src/bvm_extras.lean:2428


-- src/bvm_extras.lean:2430


-- src/bvm_extras.lean:2438

-- src/bvm_extras.lean:2475


-- src/bvm_extras.lean:2478


-- src/bvm_extras.lean:2481


-- src/bvm_extras.lean:2484


-- src/bvm_extras.lean:2486


-- src/bvm_extras.lean:2520


-- src/bvm_extras.lean:2551


-- src/bvm_extras.lean:2638


-- src/bvm_extras.lean:2647


-- src/bvm_extras.lean:2665


-- src/bvm_extras.lean:2671


-- src/bvm_extras.lean:2674


-- src/bvm_extras.lean:2677


-- src/bvm_extras.lean:2680


-- src/bvm_extras.lean:2682


-- src/bvm_extras.lean:2684


-- src/bvm_extras.lean:2694


-- src/bvm_extras.lean:2701


-- src/bvm_extras.lean:2714


-- src/bvm_extras.lean:2717


-- src/bvm_extras.lean:2719


-- src/bvm_extras.lean:2721


-- src/bvm_extras.lean:2723


-- src/bvm_extras.lean:2727


-- src/bvm_extras.lean:2730


-- src/bvm_extras.lean:2736


-- src/bvm_extras.lean:2741


-- src/bvm_extras.lean:2743


end ordinals

-- ============================================================
-- src/bvm_extras.lean:2749-2793: section zorns_lemma
-- ============================================================

section zorns_lemma
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2753


end zorns_lemma

-- ============================================================
-- src/bvm_extras.lean:2795-2821: section CH
-- ============================================================

section CH
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2803


-- src/bvm_extras.lean:2805


-- src/bvm_extras.lean:2807


end CH

end bSet


end CohenSource_BvmExtras

/- Source module: Definitions.Flypitch4.SetTheoryExt -/
section CohenSource_SetTheoryExt
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/set_theory.lean -/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Lean 3 → Lean 4 Port: scope-narrowed slice of `src/set_theory.lean`

The original Lean 3 `set_theory.lean` (713 lines) bundles two largely independent
chunks of infrastructure:

1. **The delta-system lemma** and its supporting machinery (lines 1–388).
2. **CCC (Countable Chain Condition)** plus the **product topology** section
   (lines 389–713).

Cross-flypitch grep confirms only **two** symbols from this file are used by any
other Lean 3 source:

- `countable_chain_condition` — used by `src/regular_open_algebra.lean`.
- `countable_chain_condition_pi` — called once at `src/cantor_space.lean:436`.

Everything else (`is_delta_system` and friends, the `delta_system_lemma_*`
theorems, `pi_basis`, `pi_subbasis`, `support`, `extend`, `eq_on'`, …) is
internal scaffolding that the Lean 3 authors wrote but never ended up using on
the path to `independence_of_CH`. It has been dropped from the port.

If a future port needs the dropped material, the Lean 3 source remains
verbatim in `src/set_theory.lean` as a reference.

### Renames (Lean 3 → Lean 4)

- `pairwise_disjoint s` (set-valued, Lean 3) → `s.PairwiseDisjoint id`
-/

universe u v

open Set TopologicalSpace Cardinal

/-! ## CCC: Countable Chain Condition -/

section CCC

variable (α : Type u) [TopologicalSpace α]



variable {α}

private lemma countable_chain_condition_of_nonempty
    (h : ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → o ≠ ∅) → (∀ ⦃o⦄, o ∈ s → IsOpen o) →
      s.PairwiseDisjoint id → s.Countable) : countable_chain_condition α := by
  intro s open_s hs
  let s' : Set (Set α) := s \ {∅}
  have hs' : ∀ ⦃o : Set α⦄, o ∈ s' → o ≠ ∅ := fun o ho h2o => ho.2 (by rw [mem_singleton_iff, h2o])
  have open_s' : ∀ ⦃o : Set α⦄, o ∈ s' → IsOpen o := fun o ho => open_s ho.1
  have h2s' : s'.PairwiseDisjoint id := hs.subset diff_subset
  have hcountable : s'.Countable := h s' hs' open_s' h2s'
  exact (hcountable.insert ∅).mono (by rw [insert_diff_singleton]; exact subset_insert _ _)

/-- In a separable space, the CCC holds. -/
private lemma countable_chain_condition_of_separable_space [SeparableSpace α] :
    countable_chain_condition α := by
  intro s open_s hs
  suffices h : (s \ {(∅ : Set α)}).Countable by
    have hsub : s ⊆ insert (∅ : Set α) (s \ {∅}) := by
      intro o ho
      rcases eq_or_ne o ∅ with rfl | hne
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨ho, fun h => hne (Set.mem_singleton_iff.mp h)⟩)
    exact (h.insert ∅).mono hsub
  apply Set.PairwiseDisjoint.countable_of_isOpen (s := id) (a := s \ {(∅ : Set α)})
  · intro o ⟨ho, _⟩ o' ⟨ho', _⟩ hne
    exact hs ho ho' hne
  · intro o ⟨ho, _⟩; exact open_s ho
  · intro o ⟨_, hne⟩
    exact Set.nonempty_iff_ne_empty.mpr (fun h => hne (Set.mem_singleton_iff.mpr h))

private lemma countable_chain_condition_of_countable (h : #α ≤ ℵ₀) : countable_chain_condition α := by
  haveI : Countable α := Cardinal.mk_le_aleph0_iff.mp h
  haveI : SeparableSpace α := inferInstance
  exact countable_chain_condition_of_separable_space

/-- CCC is preserved when we can witness it on a topological basis. -/
private lemma countable_chain_condition_of_topological_basis (B : Set (Set α))
    (hB : IsTopologicalBasis B)
    (h : ∀ s : Set (Set α), s ⊆ B → s.PairwiseDisjoint id → s.Countable) :
    countable_chain_condition α := by
  apply countable_chain_condition_of_nonempty
  intro s s_nonempty s_open hs
  -- For each x ∈ s, choose a non-empty basis element b ⊆ x.
  have hpick : ∀ x : s, ∃ b : Set α, b ∈ B ∧ b ≠ ∅ ∧ b ⊆ x.1 := by
    rintro ⟨x, hx⟩
    have hxne : x.Nonempty := Set.nonempty_iff_ne_empty.mpr (s_nonempty hx)
    obtain ⟨y, hy⟩ := hxne
    obtain ⟨b, hbB, hyb, hbx⟩ := hB.isOpen_iff.mp (s_open hx) y hy
    refine ⟨b, hbB, ?_, hbx⟩
    intro hbe; rw [hbe] at hyb; exact hyb
  choose f hfB hfne hfsub using hpick
  -- s' = range of f.
  let s' : Set (Set α) := Set.range f
  have hs'B : s' ⊆ B := by rintro _ ⟨x, rfl⟩; exact hfB x
  have hs'pd : s'.PairwiseDisjoint id := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
    have hxy' : x ≠ y := by
      rintro rfl; exact hne rfl
    have h1 : (x : Set α) ≠ y := fun h => hxy' (Subtype.ext h)
    exact (hs x.2 y.2 h1).mono (hfsub x) (hfsub y)
  have hs'count : s'.Countable := h s' hs'B hs'pd
  -- Now f : s → s' is injective: f x non-empty subset of both x.1 and y.1
  -- forces x.1 = y.1 (else they would be disjoint).
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hxy' : (x : Set α) ≠ y := fun h => hne (Subtype.ext h)
    have hd : Disjoint (x : Set α) (y : Set α) := hs x.2 y.2 hxy'
    have : (f x).Nonempty := Set.nonempty_iff_ne_empty.mpr (hfne x)
    obtain ⟨z, hz⟩ := this
    have hzx : z ∈ (x : Set α) := hfsub x hz
    have hzy : z ∈ (y : Set α) := hfsub y (hxy ▸ hz)
    have : ¬ Disjoint (x : Set α) (y : Set α) := by
      rw [Set.not_disjoint_iff]; exact ⟨z, hzx, hzy⟩
    exact this hd
  -- Therefore s.Countable, since f : s → s' is injective.
  have hs_count : s.Countable := by
    have hsub : Countable (Set.range f) := hs'count.to_subtype
    have : Countable s := by
      have hf' : Function.Injective (fun x : s => (⟨f x, Set.mem_range_self x⟩ : Set.range f)) := by
        intro x y hxy
        exact hf_inj (Subtype.ext_iff.mp hxy)
      exact hf'.countable
    exact Set.countable_coe_iff.mp this
  exact hs_count

end CCC

/-! ## Δ-system lemma (uncountable case, for finite-set families) -/



namespace DeltaSystemAux

/-- Helper: an uncountable set has cardinality `> ℵ₀`. -/
private lemma aleph0_lt_of_not_countable {ι : Type v} {t : Set ι} (h : ¬ t.Countable) :
    ℵ₀ < #t := by
  rw [← not_le]
  intro hle
  exact h (Cardinal.le_aleph0_iff_set_countable.mp hle)



/-- Pigeonhole: an uncountable family `f : ι → ℕ` has an uncountable fiber. -/
private lemma exists_uncountable_fiber_nat {ι : Type v} (f : ι → ℕ)
    (hι : ¬ (Set.univ : Set ι).Countable) :
    ∃ n : ℕ, ¬ (f ⁻¹' {n}).Countable := by
  by_contra hne
  push_neg at hne
  -- ι = ⋃ n, f ⁻¹' {n}
  have huniv : (Set.univ : Set ι) = ⋃ n : ℕ, f ⁻¹' {n} := by
    ext x; simp
  apply hι
  rw [huniv]
  exact Set.countable_iUnion hne

/-- The Δ-system lemma for size-`n` families (induction on `n`).

If `A : ι → Set α` is an uncountable family of finite sets all of size `n`,
then there is an uncountable subfamily forming a Δ-system. -/
private theorem delta_system_size_n {α : Type u} {ι : Type v}
    (n : ℕ) (A : ι → Set α)
    (hι : ¬ (Set.univ : Set ι).Countable)
    (hA_fin : ∀ i, (A i).Finite)
    (hA_card : ∀ i, Set.ncard (A i) = n) :
    ∃ t : Set ι, ¬ t.Countable ∧ ∃ root : Set α,
      ∀ ⦃x⦄, x ∈ t → ∀ ⦃y⦄, y ∈ t → x ≠ y → A x ∩ A y = root := by
  induction n generalizing ι with
  | zero =>
    -- Every A i is empty.
    refine ⟨Set.univ, hι, ∅, ?_⟩
    intro x _ y _ _
    have hx : A x = ∅ := by
      have h0 : Set.ncard (A x) = 0 := hA_card x
      exact (Set.ncard_eq_zero (hA_fin x)).mp h0
    rw [hx, Set.empty_inter]
  | succ n ih =>
    by_cases hcase : ∃ x : α, ¬ {i | x ∈ A i}.Countable
    · -- Case 1: pick such x. Restrict to t₀ = {i | x ∈ A i}.
      obtain ⟨x, hx⟩ := hcase
      let t₀ : Set ι := {i | x ∈ A i}
      let A' : t₀ → Set α := fun i => A i.1 \ {x}
      have hA'_fin : ∀ i : t₀, (A' i).Finite := fun i => (hA_fin i.1).diff
      have hA'_card : ∀ i : t₀, Set.ncard (A' i) = n := by
        intro i
        have hxA : x ∈ A i.1 := i.2
        have h := Set.ncard_diff_singleton_add_one hxA (hA_fin i.1)
        have h2 : Set.ncard (A i.1) = n + 1 := hA_card i.1
        change Set.ncard (A i.1 \ {x}) = n
        omega
      have ht₀_ucnt : ¬ (Set.univ : Set t₀).Countable := by
        intro hc
        apply hx
        rw [Set.countable_univ_iff] at hc
        exact Set.countable_coe_iff.mp hc
      obtain ⟨t', ht'_ucnt, r', hr'⟩ := ih A' ht₀_ucnt hA'_fin hA'_card
      -- Push t' down to ι.
      let t : Set ι := Subtype.val '' t'
      have ht_inj : Set.InjOn (Subtype.val : t₀ → ι) t' := fun a _ b _ h => Subtype.ext h
      have ht_ucnt : ¬ t.Countable := by
        intro hc
        apply ht'_ucnt
        exact Set.countable_of_injective_of_countable_image ht_inj hc
      refine ⟨t, ht_ucnt, insert x r', ?_⟩
      rintro _ ⟨⟨a, ha₀⟩, hat', rfl⟩ _ ⟨⟨b, hb₀⟩, hbt', rfl⟩ hab
      have hab' : (⟨a, ha₀⟩ : t₀) ≠ ⟨b, hb₀⟩ := fun h => hab (congr_arg Subtype.val h)
      have h_intersect : A' ⟨a, ha₀⟩ ∩ A' ⟨b, hb₀⟩ = r' := hr' hat' hbt' hab'
      -- Compute A a ∩ A b = insert x r'.
      ext y
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨hya, hyb⟩
        by_cases hyx : y = x
        · exact Or.inl hyx
        · refine Or.inr ?_
          have hyA' : y ∈ A' ⟨a, ha₀⟩ ∩ A' ⟨b, hb₀⟩ := by
            refine ⟨⟨hya, ?_⟩, ⟨hyb, ?_⟩⟩ <;> simp [hyx]
          rw [h_intersect] at hyA'
          exact hyA'
      · rintro (rfl | hyr)
        · exact ⟨ha₀, hb₀⟩
        · have : y ∈ A' ⟨a, ha₀⟩ ∩ A' ⟨b, hb₀⟩ := by rw [h_intersect]; exact hyr
          exact ⟨this.1.1, this.2.1⟩
    · -- Case 2: every x ∈ α appears in countably many A i.
      push_neg at hcase
      -- Key fact: for any countable s : Set α, only countably many i have A i ∩ s ≠ ∅.
      have key : ∀ s : Set α, s.Countable →
          {i : ι | (A i ∩ s).Nonempty}.Countable := by
        intro s hs
        have hsub : {i : ι | (A i ∩ s).Nonempty} ⊆ ⋃ y ∈ s, {i | y ∈ A i} := by
          intro i ⟨y, hy⟩
          exact Set.mem_iUnion₂.mpr ⟨y, hy.2, hy.1⟩
        exact Set.Countable.mono hsub (hs.biUnion (fun y _ => hcase y))
      -- Each A i is nonempty (size n+1 > 0).
      have hAne : ∀ i, (A i).Nonempty := by
        intro i
        rw [← Set.ncard_pos (hA_fin i), hA_card i]
        omega
      -- Apply Zorn to get a maximal disjoint family.
      let P : Set ι → Prop := fun M => M.PairwiseDisjoint A
      have hP_chain : ∀ c ⊆ {M | P M}, IsChain (· ⊆ ·) c → ∃ ub ∈ {M | P M}, ∀ s ∈ c, s ⊆ ub := by
        intro c hc hchain
        refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
        rintro i ⟨M₁, hM₁c, hi⟩ j ⟨M₂, hM₂c, hj⟩ hij
        rcases hchain.total hM₁c hM₂c with hsub | hsub
        · exact (hc hM₂c) (hsub hi) hj hij
        · exact (hc hM₁c) hi (hsub hj) hij
      obtain ⟨M, hM_max⟩ := zorn_subset {M | P M} hP_chain
      have hM_S : P M := hM_max.prop
      -- Claim: M is uncountable.
      by_cases hM_cnt : M.Countable
      · -- Contradiction: extend M.
        let B : Set α := ⋃ i ∈ M, A i
        have hB_cnt : B.Countable :=
          hM_cnt.biUnion (fun i _ => (hA_fin i).countable)
        have hbad_cnt : {i : ι | (A i ∩ B).Nonempty}.Countable := key B hB_cnt
        -- Find i₀ ∉ {i | (A i ∩ B).Nonempty}.
        have hex : ∃ i : ι, ¬ (A i ∩ B).Nonempty := by
          by_contra hne
          push_neg at hne
          apply hι
          have huniv : (Set.univ : Set ι) ⊆ {i | (A i ∩ B).Nonempty} := fun i _ => hne i
          exact hbad_cnt.mono huniv
        obtain ⟨i₀, hi₀⟩ := hex
        rw [Set.not_nonempty_iff_eq_empty] at hi₀
        have hi₀_dis : ∀ i ∈ M, Disjoint (A i₀) (A i) := by
          intro i hi
          rw [Set.disjoint_iff_inter_eq_empty]
          have hsub : A i₀ ∩ A i ⊆ A i₀ ∩ B := fun y ⟨ha, hb⟩ =>
            ⟨ha, Set.mem_biUnion hi hb⟩
          exact Set.subset_eq_empty hsub hi₀
        have hi₀_notM : i₀ ∉ M := by
          intro hin
          have hAi : A i₀ ⊆ B := Set.subset_biUnion_of_mem hin
          obtain ⟨y, hy⟩ := hAne i₀
          have : y ∈ A i₀ ∩ B := ⟨hy, hAi hy⟩
          rw [hi₀] at this
          exact this.elim
        -- Build M' := insert i₀ M, still pairwise disjoint.
        let M' : Set ι := insert i₀ M
        have hM'_P : P M' := by
          intro a ha b hb hab
          simp only [M', Set.mem_insert_iff] at ha hb
          rcases ha with rfl | ha
          · rcases hb with rfl | hb
            · exact absurd rfl hab
            · exact hi₀_dis b hb
          · rcases hb with rfl | hb
            · exact (hi₀_dis a ha).symm
            · exact hM_S ha hb hab
        have hM_sub : M ⊆ M' := Set.subset_insert _ _
        have heq : M' = M := hM_max.eq_of_superset hM'_P hM_sub
        have hin : i₀ ∈ M := heq ▸ Set.mem_insert _ _
        exact absurd hin hi₀_notM
      -- M is uncountable: take t := M, root := ∅.
      refine ⟨M, hM_cnt, ∅, ?_⟩
      intro a ha b hb hab
      exact Set.disjoint_iff_inter_eq_empty.mp (hM_S ha hb hab)

end DeltaSystemAux

/-- The Δ-system lemma at `ω₁`: any uncountably-indexed family of finite sets
contains an uncountable Δ-subsystem. (Lean 3 source:
`src/set_theory.lean:308 (delta_system_lemma_uncountable)`.) -/
private theorem delta_system_lemma_aleph1
    {α : Type u} {ι : Type v} (A : ι → Set α)
    (hι : ℵ₀ < #ι) (h2A : ∀ i, (A i).Finite) :
    ∃ t : Set ι, ℵ₀ < #t ∧ IsDeltaSystem (fun i : t => A i.1) := by
  -- Step 1: pigeonhole on the size function. Some size `n` has uncountable preimage.
  have hι_uncnt : ¬ (Set.univ : Set ι).Countable := by
    intro hc
    have hCount : Countable ι := by
      rw [← Set.countable_univ_iff]; exact hc
    have : #ι ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr hCount
    exact absurd hι (not_lt.mpr this)
  let f : ι → ℕ := fun i => Set.ncard (A i)
  obtain ⟨n, hn⟩ := DeltaSystemAux.exists_uncountable_fiber_nat f hι_uncnt
  let t₀ : Set ι := f ⁻¹' {n}
  let A' : t₀ → Set α := fun i => A i.1
  have ht₀_uncnt : ¬ (Set.univ : Set t₀).Countable := by
    intro hc
    apply hn
    rw [Set.countable_univ_iff] at hc
    exact Set.countable_coe_iff.mp hc
  have hA'_fin : ∀ i : t₀, (A' i).Finite := fun i => h2A i.1
  have hA'_card : ∀ i : t₀, Set.ncard (A' i) = n := fun i => i.2
  obtain ⟨t', ht'_uncnt, root, hroot⟩ :=
    DeltaSystemAux.delta_system_size_n n A' ht₀_uncnt hA'_fin hA'_card
  let t : Set ι := Subtype.val '' t'
  have ht_inj : Set.InjOn (Subtype.val : t₀ → ι) t' := fun a _ b _ h => Subtype.ext h
  refine ⟨t, ?_, root, ?_⟩
  · -- t is uncountable.
    apply DeltaSystemAux.aleph0_lt_of_not_countable
    intro hc
    exact ht'_uncnt (Set.countable_of_injective_of_countable_image ht_inj hc)
  · -- Δ-system property.
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨a, hat', rfl⟩ := hx
    obtain ⟨b, hbt', rfl⟩ := hy
    have hab' : a ≠ b := by
      intro h; apply hxy
      apply Subtype.ext
      show (↑a : ι) = ↑b
      rw [h]
    exact hroot hat' hbt' hab'

/-! ## CCC for product topologies -/

variable {α : Type u} {β : α → Type v} [∀ x, TopologicalSpace (β x)]



private lemma isTopologicalBasis_piOpenBasis :
    IsTopologicalBasis (piOpenBasis (β := β)) :=
  isTopologicalBasis_pi (X := β) (T := fun _ => { U | IsOpen U })
    (fun _ => isTopologicalBasis_opens)

/-- Restricting a pi-basis element to a coordinate subset `R` yields an open
set in `(∀ x : R, β x)`. -/
private lemma isOpen_restrict_image_piOpenBasis
    (R : Set α) {S : Set (∀ x, β x)} (hS : S ∈ piOpenBasis (β := β)) :
    IsOpen ((fun f : ∀ x, β x => fun x : R => f x.1) '' S) := by
  classical
  obtain ⟨U, F, hU, rfl⟩ := hS
  -- Key claim: image equals an explicit pi cylinder in (∀ x : R, β x).
  by_cases hpi : ((F : Set α).pi U).Nonempty
  · -- Non-empty case: image = (F ∩ R).pi (U ∘ ↑)
    obtain ⟨f₀, hf₀⟩ := hpi
    have himg : (fun f : ∀ x, β x => fun x : R => f x.1) '' ((F : Set α).pi U) =
        (Subtype.val ⁻¹' (F : Set α) : Set R).pi (fun x : R => U x.1) := by
      ext g
      constructor
      · rintro ⟨f, hf, rfl⟩ ⟨x, hxR⟩ hxF
        exact hf x hxF
      · intro hg
        refine ⟨fun x => if hx : x ∈ R then g ⟨x, hx⟩ else f₀ x, ?_, ?_⟩
        · intro x hxF
          by_cases hxR : x ∈ R
          · simp only [dif_pos hxR]; exact hg ⟨x, hxR⟩ hxF
          · simp only [dif_neg hxR]; exact hf₀ x hxF
        · funext ⟨x, hxR⟩; simp only [dif_pos hxR]
    rw [himg]
    apply isTopologicalBasis_piOpenBasis.isOpen
    refine ⟨fun x : R => U x.1, F.subtype (· ∈ R), ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_subtype] at hx
      exact hU x.1 hx
    · ext g
      constructor
      · intro hg x hxF
        rw [Finset.mem_coe, Finset.mem_subtype] at hxF
        exact hg ⟨x, x.2⟩ hxF
      · intro hg ⟨x, hxR⟩ hxF
        have : (⟨x, hxR⟩ : R) ∈ F.subtype (· ∈ R) := by
          rw [Finset.mem_subtype]; exact hxF
        exact hg _ this
  · -- Empty case: image is empty.
    rw [Set.not_nonempty_iff_eq_empty] at hpi
    rw [hpi, Set.image_empty]
    exact isOpen_empty

/-- Disjoint pi-basis elements whose supports form a Δ-system with root `R`
have disjoint restrictions to `R`. -/
private lemma disjoint_restrict_image_of_delta
    {S₁ S₂ : Set (∀ x, β x)}
    {U₁ U₂ : ∀ x, Set (β x)} {F₁ F₂ : Finset α}
    (h₁ : S₁ = (F₁ : Set α).pi U₁) (h₂ : S₂ = (F₂ : Set α).pi U₂)
    (hd : Disjoint S₁ S₂) (R : Set α)
    (hroot : ((F₁ : Set α)) ∩ ((F₂ : Set α)) = R) :
    Disjoint ((fun f : ∀ x, β x => fun x : R => f x.1) '' S₁)
             ((fun f : ∀ x, β x => fun x : R => f x.1) '' S₂) := by
  classical
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro g ⟨⟨f₁, hf₁S, rfl⟩, ⟨f₂, hf₂S, hfeq⟩⟩
  -- Construct f := f₁ on F₁, f₂ off F₁. Then f ∈ S₁ and f ∈ S₂.
  rw [h₁] at hf₁S
  rw [h₂] at hf₂S
  let f : ∀ x, β x := fun x => if x ∈ F₁ then f₁ x else f₂ x
  have hfS₁ : f ∈ S₁ := by
    rw [h₁]
    intro x hxF
    simp only [Finset.mem_coe] at hxF
    show f x ∈ U₁ x
    simp only [f, if_pos hxF]
    exact hf₁S x hxF
  have hfS₂ : f ∈ S₂ := by
    rw [h₂]
    intro x hxF
    simp only [Finset.mem_coe] at hxF
    show f x ∈ U₂ x
    by_cases hx1 : x ∈ F₁
    · -- x ∈ F₁ ∩ F₂ ⊆ R; use that f₁ and f₂ agree on R
      have hxR : x ∈ R := by
        rw [← hroot]
        exact ⟨hx1, hxF⟩
      simp only [f, if_pos hx1]
      have heq : f₂ x = f₁ x := by
        have := congr_fun hfeq ⟨x, hxR⟩
        simpa using this
      rw [← heq]
      exact hf₂S x hxF
    · simp only [f, if_neg hx1]
      exact hf₂S x hxF
  exact (Set.disjoint_iff_forall_ne.mp hd hfS₁ hfS₂) rfl

private theorem countable_chain_condition_pi
    (h : ∀ s : Set α, s.Finite → countable_chain_condition (∀ x : s, β x)) :
    countable_chain_condition (∀ x, β x) := by
  classical
  apply countable_chain_condition_of_topological_basis (piOpenBasis (β := β))
    isTopologicalBasis_piOpenBasis
  intro C hC h2C
  by_contra h3Cne
  have h3C : ℵ₀ < #C := by
    by_contra hle
    push_neg at hle
    exact h3Cne (Cardinal.le_aleph0_iff_set_countable.mp hle)
  -- For each S ∈ C, choose its support data via the basis description.
  have hCdata : ∀ S : C, ∃ (U : ∀ x, Set (β x)) (F : Finset α),
      (∀ x ∈ F, IsOpen (U x)) ∧ S.1 = (F : Set α).pi U := by
    rintro ⟨S, hS⟩; exact hC hS
  choose U F hUopen hSeq using hCdata
  -- Apply Δ-system lemma to the supports F.
  let A : C → Set α := fun S => (F S : Set α)
  have hA_fin : ∀ S : C, (A S).Finite := fun S => Finset.finite_toSet _
  obtain ⟨C', hC'_card, R, hR⟩ := delta_system_lemma_aleph1 A h3C hA_fin
  -- The root R is finite.
  have h2R : R.Finite := by
    -- Any two distinct elements x, y ∈ C' give A x ∩ A y = R, and A x is finite.
    have : ∃ x y : C', x ≠ y := by
      by_contra hne
      push_neg at hne
      have hsub : Subsingleton C' := ⟨fun x y => hne x y⟩
      have hone : #C' ≤ 1 := Cardinal.mk_le_one_iff_set_subsingleton.mpr (by
        intro x hx y hy
        exact congr_arg Subtype.val (hsub.elim ⟨x, hx⟩ ⟨y, hy⟩))
      have : ℵ₀ < (1 : Cardinal) := lt_of_lt_of_le hC'_card hone
      have : ℵ₀ < ℵ₀ := this.trans_le (by simp)
      exact absurd this (lt_irrefl _)
    obtain ⟨x, y, hxy⟩ := this
    rw [← hR hxy]
    exact (hA_fin x.1).inter_of_left _
  -- Define π : (∀ x, β x) → (∀ x : R, β x) and the family D of restrictions.
  let π : (∀ x, β x) → (∀ x : R, β x) := fun f x => f x.1
  let D : Set (Set (∀ x : R, β x)) := (fun S : C' => π '' S.1.1) '' Set.univ
  -- Each member of D is open.
  have hD_open : ∀ ⦃o⦄, o ∈ D → IsOpen o := by
    rintro _ ⟨S, _, rfl⟩
    exact isOpen_restrict_image_piOpenBasis _ (hC S.1.2)
  -- Key lemma about disjoint images.
  have h2'D : ∀ S₁ S₂ : C', S₁ ≠ S₂ → Disjoint (π '' S₁.1.1) (π '' S₂.1.1) := by
    intro S₁ S₂ hne
    -- S₁ ≠ S₂ in C', so S₁.1 ≠ S₂.1 in C, so the underlying sets differ.
    have h12 : S₁.1.1 ≠ S₂.1.1 := fun heq => by
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    -- The C-pairwise-disjoint hypothesis gives Disjoint S₁.1.1 S₂.1.1.
    have hdis : Disjoint S₁.1.1 S₂.1.1 :=
      h2C S₁.1.2 S₂.1.2 h12
    -- Apply the support-extension lemma.
    apply disjoint_restrict_image_of_delta (hSeq S₁.1) (hSeq S₂.1) hdis R
    -- Need: F S₁.1 ∩ F S₂.1 (as Sets) = R
    have := hR (x := S₁) (y := S₂) hne
    -- A is fun S => (F S : Set α), so A S₁ = F S₁ as Set α.
    simpa [A] using this
  -- Members of D are pairwise disjoint.
  have hD_disj : D.PairwiseDisjoint id := by
    rintro _ ⟨S₁, _, rfl⟩ _ ⟨S₂, _, rfl⟩ hne
    have hS₁S₂ : S₁ ≠ S₂ := fun heq => by rw [heq] at hne; exact hne rfl
    exact h2'D S₁ S₂ hS₁S₂
  -- D is uncountable: π is injective on C'.
  -- Two basis elements with disjoint images are not equal,
  -- so the map S ↦ π '' S.1.1 is injective on C' (assuming non-empty images).
  have hD_card : ℵ₀ < #D := by
    -- The function S ↦ π '' S.1.1 is injective on { S : C' | S.1.1 ≠ ∅ }
    -- (because disjoint non-empty sets can't be equal). Plus, there's at most
    -- one S ∈ C' with S.1.1 = ∅. So #D ≥ #C' - 1 > ℵ₀.
    -- We use that an injective function from an uncountable set has uncountable image.
    let C'ne : Set C' := { S | S.1.1 ≠ ∅ }
    have hC'ne_card : ℵ₀ < #C'ne := by
      -- C' = C'ne ∪ (C' ∩ {empty}). The empty part has at most 1 element.
      -- More precisely, the set of S : C' with S.1.1 = ∅ has at most 1 element,
      -- since all such S have S.1.1 = ∅ (as a value in Set (∀ x, β x)),
      -- and S.1 is determined by S.1.1 (S.1 ∈ C is the set, no extra data).
      have hcompl : (C'ne)ᶜ ⊆ {S : C' | S.1.1 = ∅} := by
        intro S hS
        simp only [Set.mem_compl_iff, ne_eq, not_not] at hS
        change S.1.1 = ∅
        by_contra hne
        exact hS hne
      have hsub : { S : C' | S.1.1 = ∅ }.Subsingleton := by
        intro x hx y hy
        apply Subtype.ext
        apply Subtype.ext
        rw [hx, hy]
      have hsub_card : #({ S : C' | S.1.1 = ∅ } : Set C') ≤ 1 := by
        rw [Cardinal.mk_le_one_iff_set_subsingleton]
        exact hsub
      -- C' = univ = C'ne ∪ (C'ne)ᶜ; the latter has ≤ 1 element.
      have hsplit : (Set.univ : Set C') = C'ne ∪ (C'ne)ᶜ := (Set.union_compl_self _).symm
      have hcard_le : #C' ≤ #C'ne + #((C'ne)ᶜ : Set C') := by
        have hsplit2 : #(Set.univ : Set C') ≤ #C'ne + #((C'ne)ᶜ : Set C') := by
          have := Cardinal.mk_union_le C'ne (C'ne)ᶜ
          rw [Set.union_compl_self] at this
          exact this
        rwa [Cardinal.mk_univ] at hsplit2
      have hcompl_card : #((C'ne)ᶜ : Set C') ≤ 1 :=
        le_trans (Cardinal.mk_le_mk_of_subset hcompl) hsub_card
      -- ℵ₀ < #C' ≤ #C'ne + 1, and one cannot get a finite bump above ℵ₀.
      have h1 : ℵ₀ < #C'ne + #((C'ne)ᶜ : Set C') := lt_of_lt_of_le hC'_card hcard_le
      by_contra hle
      push_neg at hle
      have : #C'ne + #((C'ne)ᶜ : Set C') ≤ ℵ₀ := by
        have h_cmpl : #((C'ne)ᶜ : Set C') ≤ ℵ₀ := le_trans hcompl_card (by exact_mod_cast (one_le_aleph0))
        exact Cardinal.add_le_aleph0.mpr ⟨hle, h_cmpl⟩
      exact absurd h1 (not_lt.mpr this)
    -- Now define the injection from C'ne to D.
    -- Map: S ↦ π '' S.1.1. Need this is injective on C'ne and lands in D.
    let f : C'ne → D := fun S =>
      ⟨π '' S.1.1.1, S.1, trivial, rfl⟩
    have hf_inj : Function.Injective f := by
      intro S₁ S₂ hSeq
      have heq : π '' S₁.1.1.1 = π '' S₂.1.1.1 := by
        have := congr_arg Subtype.val hSeq
        exact this
      -- If S₁ ≠ S₂ as elements of C', then h2'D gives disjoint images, so they
      -- can't be equal AND non-empty.
      by_contra hne
      have hSne : S₁.1 ≠ S₂.1 := fun heq' => hne (Subtype.ext heq')
      have hdisj := h2'D S₁.1 S₂.1 hSne
      rw [heq] at hdisj
      -- π '' S₂.1.1 is disjoint from itself; so it's empty.
      have : π '' S₂.1.1.1 = ∅ := by
        rw [disjoint_self] at hdisj
        exact hdisj
      -- S₂.1.1.1 is non-empty (since S₂ ∈ C'ne), so π '' S₂.1.1.1 is non-empty.
      have hS₂ne : S₂.1.1.1 ≠ ∅ := S₂.2
      rw [Set.image_eq_empty] at this
      exact hS₂ne this
    -- Now ℵ₀ < #C'ne ≤ #D.
    have : #C'ne ≤ #D := Cardinal.mk_le_of_injective hf_inj
    exact lt_of_lt_of_le hC'ne_card this
  -- Apply CCC for (∀ x : R, β x) to get D countable, contradiction.
  have hD_count : D.Countable := h R h2R D hD_open hD_disj
  have : #D ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hD_count
  exact absurd hD_card (not_lt.mpr this)


end CohenSource_SetTheoryExt

/- Source module: Definitions.Flypitch4.RegularOpenAlgebra -/
section CohenSource_RegularOpenAlgebra
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/regular_open_algebra.lean (complete, lines 1-722).

Namespace: everything lives in `Flypitch` namespace to avoid clashing with mathlib's `IsRegular`.
The `ᵖ` postfix for `perp` is declared globally after the namespace.
-/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace

universe u

namespace Flypitch

/-! ## topology_lemmas section -/

section topology_lemmas

variable {α : Type u} [TopologicalSpace α]




























end topology_lemmas

/-! ## regular section -/

section regular

variable {α : Type u} [TopologicalSpace α]





end regular

end Flypitch

-- Declare ᵖ postfix globally (outside namespace)


/-! ## Lemmas about perp and IsRegularOpen in namespace Flypitch.Regular -/

namespace Flypitch.Regular

open Flypitch

variable {α : Type u} [TopologicalSpace α]


































































end Flypitch.Regular

/-! ## regular_algebra section

Port of: `section regular_algebra` (src/regular_open_algebra.lean lines 349-722).
Builds the complete Boolean algebra structure on regular open sets.
-/

namespace Flypitch

open Flypitch.Regular

/-! ### The type of regular open sets -/



namespace RegularOpens

variable {α : Type u} [TopologicalSpace α]





-- Helper: extract val image of a set of regular opens
-- (using Set.image (·.val) avoids the ↑𝒮 coercion issue in where blocks)






/-! ### Key set lemmas -/







/-! ### Order on RegularOpens (needed before instance) -/



/-! ### Auxiliary lemmas for the CBA instance -/









-- Auxiliary: sSup upper bound for a ∈ s


-- Auxiliary: sSup is least upper bound


-- Auxiliary: sInf lower bound for a ∈ s


-- Auxiliary: a ≤ sInf s when a ≤ all b ∈ s


/-! ### Complete Boolean Algebra instance

Build everything in one `where` block to avoid coherence issues.
-/



/-! ### Convenience simp lemmas (work once the instance is defined) -/

















/-! ### NontrivialCompleteBooleanAlgebra -/



/-! ### Density lemmas -/









/-! ### CCC for regular opens -/

/-- If α satisfies the CCC, so do its regular opens. Port of src:674. -/
private lemma CCC_regular_opens (h : countable_chain_condition α) : CCC (RegularOpens α) := by
  intro ι O hO h2O
  -- Step 1: O is injective on ι
  have O_inj : Function.Injective O := by
    intro x y hxy
    by_contra hne
    have hle := h2O x y hne
    rw [hxy, inf_idem] at hle
    exact (Std.not_le_of_gt (hO y)) hle
  -- Step 2: The composition Subtype.val ∘ O is also injective
  have hValInj : Function.Injective (Subtype.val ∘ O) :=
    Subtype.val_injective.comp O_inj
  -- Step 3: The range consists of open sets
  have hopen : ∀ ⦃o : Set α⦄, o ∈ Set.range (Subtype.val ∘ O) → IsOpen o := by
    rintro _ ⟨x, rfl⟩
    exact isOpen_of_isRegularOpen (O x).property
  -- Step 4: The range is pairwise disjoint
  have hpwd : (Set.range (Subtype.val ∘ O)).PairwiseDisjoint id := by
    intro a ha b hb hab
    rcases ha with ⟨x, rfl⟩
    rcases hb with ⟨y, rfl⟩
    have hne : x ≠ y := fun heq => hab (congr_arg (Subtype.val ∘ O) heq)
    have hle := h2O x y hne
    simp only [Function.onFun, id, Set.disjoint_left]
    intro z hz1 hz2
    have : z ∈ (O x ⊓ O y).val := by rw [inf_val]; exact ⟨hz1, hz2⟩
    have hbot : (O x ⊓ O y).val ⊆ (⊥ : RegularOpens α).val := hle
    exact absurd (hbot this) (by simp [bot_val])
  -- Step 5: Apply CCC for α and convert cardinal bound
  have hcnt := h _ hopen hpwd
  calc Cardinal.mk ι = Cardinal.mk (Set.range (Subtype.val ∘ O)) := (Cardinal.mk_range_eq _ hValInj).symm
    _ ≤ Cardinal.aleph0 := hcnt.le_aleph0

/-! ### bot_lt and fst lemmas -/











end RegularOpens

end Flypitch


end CohenSource_RegularOpenAlgebra

/- Source module: Definitions.Flypitch4.CantorSpace -/
section CohenSource_CantorSpace
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/cantor_space.lean (446 lines). -/







set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace

universe u v

/-! ## Global topology on `Set α` -/







































/-! ## CantorSpace namespace -/

namespace CantorSpace

variable {α : Type u}





















































































open Cardinal

private lemma countable_chain_condition_set {α : Type u} :
    countable_chain_condition (Set α) := by
  apply countable_chain_condition_pi
  intro s hs
  apply countable_chain_condition_of_countable
  apply le_of_lt
  haveI : Fintype ↑s := hs.fintype
  rw [Cardinal.mk_arrow]
  apply Cardinal.power_lt_aleph0
  · rw [show (#Prop : Cardinal) = #Bool from Cardinal.mk_congr equiv_Prop_bool]
    simp
  · exact Cardinal.mk_lt_aleph0

end CantorSpace


end CohenSource_CantorSpace

/- Source module: Definitions.Flypitch4.Forcing -/
section CohenSource_Forcing
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/forcing.lean (567 lines) — Task 18 -/





set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Compatibility with the source port's Mathlib revision.


open scoped Cardinal
open Flypitch Flypitch.Regular

universe u

namespace bSet

-- ============================================================
-- src/forcing.lean:34-103: section cardinal_preservation
-- ============================================================

section cardinal_preservation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing.lean:36-48
private lemma AE_of_check_larger_than_check'' {x y : PSet.{u}} (f : bSet 𝔹) {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ is_surj_onto (check x) (check y) f)
    (H_nonempty : ∃ z, z ∈ y) :
    ∀ i : y.Type, ∃ j : x.Type, ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by
  intro i
  -- is_surj_onto = is_func' ⊓ is_surj
  have H_func' : Γ ≤ is_func' (check x) (check y) f := le_trans H inf_le_left
  have H_surj : Γ ≤ is_surj (check x) (check y) f := le_trans H inf_le_right
  -- Apply is_surj at v = check (y.Func i): since check (y.Func i) ∈ check y by mem_check_of_mem
  -- get ⨆ w, w ∈ check x ⊓ pair w (check (y.Func i)) ∈ f
  have H_surj_i : Γ ≤ ⨆ w, w ∈ᴮ check x ⊓ pair w (check (y.Func i)) ∈ᴮ f := by
    have h_step := le_trans H_surj (iInf_le (f := fun v => v ∈ᴮ check y ⟹
        ⨆ w, w ∈ᴮ check x ⊓ pair w v ∈ᴮ f) (check (y.Func i)))
    exact le_trans (le_inf h_step mem_check_of_mem) (imp_inf_le _ _)
  -- Use bounded_exists to rewrite ⨆ w, w ∈ check x ⊓ ϕ w = ⨆ j, ϕ (check (x.Func j))
  rw [← @bounded_exists 𝔹 _ (check x) (fun w => pair w (check (y.Func i)) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)] at H_surj_i
  simp only [check_bval_top, top_inf_eq] at H_surj_i
  -- H_surj_i : Γ ≤ ⨆ j : x.Type, pair (check (x.Func (check_cast j))) (check (y.Func i)) ∈ᴮ f
  -- Combine with H_func' to get ⨆ j, is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ f
  have H_combined : ⊥ < ⨆ j : (check x : bSet 𝔹).type,
      is_func f ⊓ pair ((check x : bSet 𝔹).func j) (check (y.Func i)) ∈ᴮ f := by
    apply lt_of_lt_of_le H_nonzero
    calc Γ
        ≤ is_func' (check x) (check y) f ⊓ ⨆ j, pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          le_inf H_func' H_surj_i
      _ = ⨆ j, is_func' (check x) (check y) f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          inf_iSup_eq'
      _ ≤ ⨆ j, is_func f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          iSup_mono fun j => le_inf (is_func_of_is_func' inf_le_left) inf_le_right
  obtain ⟨j, Hj⟩ := nonzero_wit H_combined
  exact ⟨check_cast j, by rwa [← check_func]⟩

-- src/forcing.lean:50-56
private lemma AE_of_check_larger_than_check' {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ surjects_onto (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by
  -- surjects_onto (check x) (check y) = ⨆ f, is_func' (check x) (check y) f ⊓ is_surj ...
  -- Use maximum_principle to extract a specific f
  -- From surjects_onto, extract a concrete f using maximum_principle
  -- surjects_onto (check x) (check y) = ⨆ f, is_surj_onto (check x) (check y) f
  -- By maximum_principle, ∃ f, ⨆ g, is_surj_onto ... g = is_surj_onto ... f
  -- But B_ext proof for is_surj_onto f is needed; use is_function_right + simp
  -- B_ext (fun f => is_surj_onto (check x) (check y) f)
  -- = B_ext (fun f => is_func' x y f ⊓ is_surj x y f)
  -- = B_ext (fun f => (is_func f ⊓ is_total x y f) ⊓ is_surj x y f)
  -- Extract f from surjects_onto = ⨆ f, is_surj_onto (check x) (check y) f
  simp only [surjects_onto] at H
  obtain ⟨f, Hf⟩ := nonzero_wit' H_nonzero H
  -- Hf : ⊥ < is_surj_onto (check x) (check y) f ⊓ Γ
  -- Use the context Γ' = is_surj_onto f ⊓ Γ which is nonzero and ≤ is_surj_onto f
  have Hf_nonzero : ⊥ < is_surj_onto (check x) (check y) f ⊓ Γ := Hf
  have Hf_le : is_surj_onto (check x) (check y) f ⊓ Γ ≤ is_surj_onto (check x) (check y) f :=
    inf_le_left
  exact ⟨f, AE_of_check_larger_than_check'' f Hf_nonzero Hf_le H_mem⟩

-- src/forcing.lean:58-62
private lemma AE_of_check_larger_than_check {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ larger_than (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f :=
  AE_of_check_larger_than_check' H_nonzero
    (surjects_onto_of_larger_than_and_exists_mem H
      (by obtain ⟨z, hz⟩ := H_mem; exact le_trans le_top (le_iSup_of_le (check z) (check_mem hz))))
    H_mem

-- src/forcing.lean:63-100: not_CCC_of_uncountable_fiber
variable
  (η₁ η₂ : PSet.{u}) (H_infinite : Cardinal.aleph0 ≤ #(η₁.Type))
  (H_lt : #(η₁.Type) < #(η₂.Type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
  (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
  (H : ∀ β : η₂.Type, (⊥ : 𝔹) < is_func f ⊓ pair (check (η₁.Func (g β))) (check (η₂.Func β)) ∈ᴮ f)

include H_infinite H_lt H_inj₂ f H in
-- src/forcing.lean:71-100
private lemma not_CCC_of_uncountable_fiber
    (H_ex : ∃ ξ : η₁.Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ})) : ¬ CCC 𝔹 := by
  obtain ⟨ξ, H_ξ⟩ := H_ex
  let 𝓐 : (g⁻¹' {ξ}) → 𝔹 :=
    fun β => is_func f ⊓ pair (check (η₁.Func (g β.val))) (check (η₂.Func β.val)) ∈ᴮ f
  have 𝓐_nontriv : ∀ β, ⊥ < 𝓐 β := fun β => H β.val
  have 𝓐_anti : ∀ β₁ β₂ : (g⁻¹' {ξ}), β₁ ≠ β₂ → 𝓐 β₁ ⊓ 𝓐 β₂ ≤ ⊥ := by
    intro β₁ β₂ h_sep
    apply poset_yoneda; intro Γ a
    simp only [le_inf_iff] at a
    obtain ⟨ha₁, ha₂⟩ := a
    obtain ⟨H_func₁, H_mem₁⟩ := le_inf_iff.mp ha₁
    obtain ⟨_, H_mem₂⟩ := le_inf_iff.mp ha₂
    have hg₁ : g β₁.val = ξ := β₁.property
    have hg₂ : g β₂.val = ξ := β₂.property
    rw [hg₁] at H_mem₁; rw [hg₂] at H_mem₂
    have H_le_eq : Γ ≤ check (η₂.Func β₁.val) =ᴮ check (η₂.Func β₂.val) :=
      eq_of_is_func_of_eq H_func₁ bv_refl H_mem₁ H_mem₂
    apply le_trans H_le_eq
    rw [le_bot_iff]
    exact check_bv_eq_bot_of_not_equiv (H_inj₂ _ _ (fun heq => h_sep (Subtype.ext heq)))
  intro H_CCC
  exact absurd (le_antisymm (lt_iff_le_and_ne.mp H_ξ).1
    (H_CCC _ 𝓐 𝓐_nontriv 𝓐_anti)) (lt_iff_le_and_ne.mp H_ξ).2

end cardinal_preservation

end bSet

open bSet

-- ============================================================
-- src/forcing.lean:107-121: namespace PSet
-- ============================================================

namespace PSet

-- src/forcing.lean:109: ℵ₁ (as PSet)


-- src/forcing.lean:111: ℵ₂ (as PSet)


-- src/forcing.lean:113


-- src/forcing.lean:115-120: Union lemmas (not needed for the main result)

end PSet

open PSet

-- ============================================================
-- src/forcing.lean:125-133: 𝔹_cohen and instances
-- ============================================================



local notation "𝔹" => 𝔹_cohen





-- src/forcing.lean:134


-- src/forcing.lean:136


-- Type equality lemmas for cast operations
-- These hold because check x has .type = x.Type by the definition of check








-- src/forcing.lean:149-176: cast helper lemmas










-- src/forcing.lean:178-179
private theorem 𝔹_CCC : CCC 𝔹 :=
  Flypitch.RegularOpens.CCC_regular_opens CantorSpace.countable_chain_condition_set

local notation "𝒳" => Set (PSet.pSet_aleph2.Type × ℕ)

-- src/forcing.lean:187-191




-- src/forcing.lean:202-203


-- src/forcing.lean:205-209


-- src/forcing.lean:211-214: structure 𝒞


-- src/forcing.lean:216


-- src/forcing.lean:223-245: ι definition


open CantorSpace

-- src/forcing.lean:249-250


-- src/forcing.lean:252-272: 𝒞_dense_basis


-- src/forcing.lean:274-284: 𝒞_dense


-- src/forcing.lean:286-288


-- src/forcing.lean:292-299


-- src/forcing.lean:301-303


-- src/forcing.lean:305-319: 𝒞_nonzero


-- src/forcing.lean:323-350: 𝒞_disjoint_row


-- src/forcing.lean:352-353


-- ============================================================
-- src/forcing.lean:355-441: namespace cohen_real (inside namespace bSet)
-- ============================================================

namespace bSet

namespace cohen_real















-- src/forcing.lean:379-386


-- src/forcing.lean:388-398


-- src/forcing.lean:400-406




end cohen_real

-- ============================================================
-- src/forcing.lean:443-567: section neg_CH
-- ============================================================

section neg_CH
-- (still inside namespace bSet)

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)

-- src/forcing.lean:450-457
private lemma uncountable_fiber_of_regular' (κ₁ κ₂ : Cardinal) (H_inf : Cardinal.aleph0 ≤ κ₁)
    (H_lt : κ₁ < κ₂) (H : κ₂.ord.cof = κ₂) (α : Type u) (H_α : #α = κ₁)
    (β : Type u) (H_β : #β = κ₂) (g : β → α) :
    ∃ (ξ : α), Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by
  -- Use Cardinal.infinite_pigeonhole: if ℵ₀ ≤ #β and #α < (#β).ord.cof, then some fiber has #β
  have h₁ : Cardinal.aleph0 ≤ #β := H_β ▸ le_of_lt (lt_of_le_of_lt H_inf H_lt)
  have h₂ : #α < (#β).ord.cof := by
    rw [H_α, H_β, H]; exact H_lt
  obtain ⟨ξ, Hξ⟩ := Cardinal.infinite_pigeonhole g h₁ h₂
  -- Hξ : #(g⁻¹'{ξ}) = #β, and ℵ₀ ≤ #β = κ₂ > κ₁ ≥ ℵ₀
  refine ⟨ξ, ?_⟩
  rw [Hξ, H_β]
  exact lt_of_le_of_lt H_inf H_lt

-- src/forcing.lean:459-466


-- src/forcing.lean:468-487
private lemma cardinal_inequality_of_regular (κ₁ κ₂ : Cardinal)
    (H_reg₁ : Cardinal.IsRegular κ₁) (H_reg₂ : Cardinal.IsRegular κ₂)
    (H_inf : Cardinal.aleph0 ≤ κ₁) (H_lt : κ₁ < κ₂) {Γ : 𝔹} :
    Γ ≤ (larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)))ᶜ := by
  -- Prove by contradiction: if Γ ≤ larger_than κ₁ κ₂, derive ¬CCC 𝔹, contradicting 𝔹_CCC
  apply le_neg_of_inf_eq_bot
  rw [inf_comm]
  -- Goal: Γ ⊓ larger_than (check κ₁) (check κ₂) ≤ ⊥ ... actually need = ⊥
  -- wait le_neg_of_inf_eq_bot needs b ⊓ a = ⊥ to conclude a ≤ bᶜ
  -- So need larger_than ... ⊓ Γ = ⊥ i.e. Γ ⊓ larger_than ... = ⊥
  rw [eq_bot_iff]
  -- Goal: Γ ⊓ larger_than ... ≤ ⊥
  by_contra H_nonzero
  rw [← bot_lt_iff_not_le_bot] at H_nonzero
  -- Apply AE_of_check_larger_than_check to get f and g
  have H_larger : Γ ⊓ larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) ≤
      larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) := inf_le_right
  rcases AE_of_check_larger_than_check H_nonzero H_larger
    (PSet.exists_mem_of_regular H_reg₂) with ⟨f, Hf⟩
  -- Extract g : κ₂.Type → κ₁.Type from Hf
  obtain ⟨g, g_spec⟩ := Classical.axiomOfChoice Hf
  -- Use not_CCC_of_uncountable_fiber with the extracted g
  have H_inf₁ : Cardinal.aleph0 ≤ #((PSet.card_ex κ₁).Type) := by simp [H_inf]
  have H_lt₁ : #((PSet.card_ex κ₁).Type) < #((PSet.card_ex κ₂).Type) := by
    rw [@PSet.mk_type_mk_eq'' κ₁ H_inf, @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))]
    exact H_lt
  have H_inj₂₁ : ∀ i j, i ≠ j → ¬ PSet.Equiv ((PSet.card_ex κ₂).Func i) ((PSet.card_ex κ₂).Func j) :=
    fun i j h => PSet.ordinalMk_inj _ _ _ h
  have H_ex : ∃ ξ : (PSet.card_ex κ₁).Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by
    apply uncountable_fiber_of_regular' κ₁ κ₂ H_inf H_lt H_reg₂.cof_ord
    · exact @PSet.mk_type_mk_eq'' κ₁ H_inf
    · exact @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))
  exact absurd 𝔹_CCC (not_CCC_of_uncountable_fiber (PSet.card_ex κ₁) (PSet.card_ex κ₂)
    H_inf₁ H_lt₁ H_inj₂₁ f g g_spec H_ex)

-- src/forcing.lean:489-504


-- src/forcing.lean:507-509
private lemma aleph1_lt_aleph2_bSet_cohenProof02 : (⊤ : 𝔹) ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  cardinal_inequality_of_regular _ _ PSet.is_regular_aleph_one PSet.is_regular_aleph_two
    (Cardinal.aleph0_le_aleph 1) PSet.aleph_one_lt_aleph_two



-- src/forcing.lean:513-529: cohen_real.mk_ext


-- src/forcing.lean:531-532


-- src/forcing.lean:534-546


-- src/forcing.lean:548-550




-- src/forcing.lean:552-562


-- src/forcing.lean:564-565


end neg_CH

end bSet


end CohenSource_Forcing


theorem solution : @LE.le.{0} 𝔹_cohen
  (@Preorder.toLE.{0} 𝔹_cohen
    (@PartialOrder.toPreorder.{0} 𝔹_cohen
      (@ChainCompletePartialOrder.toPartialOrder.{0} 𝔹_cohen
        (@ChainCompletePartialOrder.instOfCompleteLattice.{0} 𝔹_cohen
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} 𝔹_cohen
            (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} 𝔹_cohen 𝔹_boolean_algebra))))))
  (@Top.top.{0} 𝔹_cohen
    (@BooleanAlgebra.toTop.{0} 𝔹_cohen
      (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} 𝔹_cohen
        (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} 𝔹_cohen 𝔹_boolean_algebra))))
  (@Compl.compl.{0} 𝔹_cohen
    (@BooleanAlgebra.toCompl.{0} 𝔹_cohen
      (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} 𝔹_cohen
        (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} 𝔹_cohen 𝔹_boolean_algebra)))
    (@bSet.larger_than.{0} 𝔹_cohen 𝔹_boolean_algebra
      (@bSet.check.{0} 𝔹_cohen 𝔹_boolean_algebra
        (PSet.card_ex.{0}
          (@DFunLike.coe.{2, 2, 2}
            (@OrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Ordinal.{0} (fun x => Cardinal.{0})
            (@instFunLikeOrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Cardinal.aleph.{0}
            (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1) (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))))
      (@bSet.check.{0} 𝔹_cohen 𝔹_boolean_algebra
        (PSet.card_ex.{0}
          (@DFunLike.coe.{2, 2, 2}
            (@OrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Ordinal.{0} (fun x => Cardinal.{0})
            (@instFunLikeOrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Cardinal.aleph.{0}
            (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 2)
              (@instOfNatAtLeastTwo.{1} Ordinal.{0} (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{1} Ordinal.{0} Ordinal.addMonoidWithOne.{0})
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))) :=
  @bSet.aleph1_lt_aleph2_bSet_cohenProof02
