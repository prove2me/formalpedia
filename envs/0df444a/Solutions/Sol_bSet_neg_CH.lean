-- Prove2me | solution 1 for bSet.neg_CH
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T02:08:38.887552+00:00
-- url     : https://prove2.me/submissions/869705dd-c8bd-41a9-9576-2a0e12fc9b15

import Definitions.Def_CH_Cohen_Library10
import Theorems.Thm_bSet_aleph0_lt_aleph1_bSet
import Theorems.Thm_bSet_aleph1_lt_aleph2_bSet
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





















/-! ### Subset helpers (src lines 698-704) -/





/-! ### ofNat lemmas (src lines 706-768) -/
-- In mathlib4, Lean 3's `of_nat` is `PSet.ofNat`.
-- Lean 3 omega.type = ℕ-indexed; mathlib4 uses ULift ℕ.

















/-! ### Transitivity and well-orders for omega (src lines 770-800) -/







/-- Injectivity of `ofNat`.
    Port of `of_nat_inj` (src/pSet_ordinal.lean:792). -/
private lemma ofNat_inj {n k : ℕ} (H_neq : n ≠ k) :
    ¬ Equiv (PSet.ofNat n : PSet.{u}) (PSet.ofNat k : PSet.{u}) := by
  intro H
  rcases lt_trichotomy n k with h | rfl | h
  · exact PSet.mem_irrefl (PSet.ofNat n)
      ((PSet.Mem.congr_right H).mpr (ofNat_mem_of_lt h))
  · exact H_neq rfl
  · exact PSet.mem_irrefl (PSet.ofNat k)
      ((PSet.Mem.congr_right H.symm).mpr (ofNat_mem_of_lt h))



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


-- src/bvm.lean:40


-- src/bvm.lean:43


-- src/bvm.lean:46


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








private lemma omega_definite {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega := by
  suffices h : of_nat n ∈ᴮ omega = (⊤ : 𝔹) by
    exact le_trans le_top (by rwa [top_le_iff])
  apply top_unique
  induction n with
  | zero => apply bv_use (ULift.up 0); simp
  | succ k _ => apply bv_use (ULift.up (k + 1)); simp









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


-- src/bvm_extras.lean:1177


-- src/bvm_extras.lean:1191


-- src/bvm_extras.lean:1198


-- src/bvm_extras.lean:1209


-- src/bvm_extras.lean:1220


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
private lemma functionMk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
    (⊤ : 𝔹) ≤ is_func (functionMk F h_congr) := by
  -- is_func g = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ g ⊓ pair w₂ v₂ ∈ g ⊓ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, top_inf_eq]
  -- Goal: pair w₁ v₁ ∈ functionMk ⊓ pair w₂ v₂ ∈ functionMk ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂
  -- Extract i from pair w₁ v₁ ∈ functionMk
  have hmem_left : pair w₁ v₁ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ i : u.type, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  have hmem_right : pair w₂ v₂ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ j : u.type, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  -- Carry context through double iSup
  calc pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)
      ≤ (⨆ i, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)) :=
        le_inf (inf_le_left.trans hmem_left) le_rfl
    _ ≤ ⨆ i, (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)) :=
        (iSup_inf_eq _ _).le
    _ ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂ := by
        apply iSup_le; intro i
        calc (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
              (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))
            ≤ (⨆ j, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) :=
              le_inf (inf_le_right.trans (inf_le_right.trans hmem_right)) le_rfl
          _ ≤ ⨆ j, (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) :=
              (iSup_inf_eq _ _).le
          _ ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂ := by
              apply iSup_le; intro j
              -- Context: (u.bval j ⊓ w₂v₂=pair(Func j)(F j)) ⊓ (u.bval i ⊓ w₁v₁=pair(Func i)(F i)) ⊓ ...
              have hw1 : (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) ≤
                    pair w₁ v₁ =ᴮ pair (u.func i) (F i) :=
                inf_le_right.trans (inf_le_left.trans inf_le_right)
              have hw2 : (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) ≤
                    pair w₂ v₂ =ᴮ pair (u.func j) (F j) :=
                inf_le_left.trans inf_le_right
              rw [← deduction]
              -- Goal: ctx ⊓ w₁ =ᴮ w₂ ≤ v₁ =ᴮ v₂
              -- w₁ =ᴮ u.func i (from hw1: pair_eq_pair_left)
              -- w₂ =ᴮ u.func j (from hw2: pair_eq_pair_left)
              -- v₁ =ᴮ F i (from hw1: pair_eq_pair_right)
              -- v₂ =ᴮ F j (from hw2: pair_eq_pair_right)
              -- F i =ᴮ F j from h_congr (since w₁ =ᴮ w₂ = u.func i =ᴮ u.func j via bv_trans)
              set ctx4 := (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)))
              -- v₁ =ᴮ F i
              have hv1_Fi : ctx4 ⊓ w₁ =ᴮ w₂ ≤ v₁ =ᴮ F i :=
                le_trans inf_le_left (le_trans hw1 eq_of_eq_pair_right)
              -- v₂ =ᴮ F j
              have hv2_Fj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ v₂ =ᴮ F j :=
                le_trans inf_le_left (le_trans hw2 eq_of_eq_pair_right)
              -- w₁ =ᴮ u.func i
              have hw1_ui : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ u.func i :=
                le_trans inf_le_left (le_trans hw1 eq_of_eq_pair_left)
              -- w₂ =ᴮ u.func j
              have hw2_uj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₂ =ᴮ u.func j :=
                le_trans inf_le_left (le_trans hw2 eq_of_eq_pair_left)
              -- w₁ =ᴮ w₂
              have hw12 : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ w₂ := inf_le_right
              -- u.func i =ᴮ u.func j via: u.func i =ᴮ w₁ =ᴮ w₂ =ᴮ u.func j
              have h_ui_uj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ u.func i =ᴮ u.func j :=
                bv_trans (bv_symm hw1_ui) (bv_trans hw12 hw2_uj)
              -- F i =ᴮ F j
              have h_Fi_Fj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ F i =ᴮ F j :=
                le_trans h_ui_uj (h_congr i j)
              -- v₁ =ᴮ v₂ via v₁ =ᴮ F i =ᴮ F j =ᴮ v₂ (symm)
              exact bv_trans hv1_Fi (bv_trans h_Fi_Fj (bv_symm hv2_Fj))

-- src/bvm_extras.lean:2041
private lemma functionMk_inj_of_inj {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    (h_inj : ∀ i j, i ≠ j → F i =ᴮ F j ≤ ⊥)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
    (⊤ : 𝔹) ≤ is_inj (functionMk F h_congr) := by
  -- is_inj f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⊓ v₁ =ᴮ v₂ ⟹ w₁ =ᴮ w₂
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, top_inf_eq]
  -- Goal: pair w₁ v₁ ∈ functionMk ⊓ pair w₂ v₂ ∈ functionMk ⊓ v₁ =ᴮ v₂ ≤ w₁ =ᴮ w₂
  have hmem_left : pair w₁ v₁ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ i : u.type, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  have hmem_right : pair w₂ v₂ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ j : u.type, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  -- Carry context through double iSup
  calc pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂
      ≤ (⨆ i, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂) :=
        le_inf (inf_le_left.trans (inf_le_left.trans hmem_left)) le_rfl
    _ ≤ ⨆ i, (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂) :=
        (iSup_inf_eq _ _).le
    _ ≤ w₁ =ᴮ w₂ := by
        apply iSup_le; intro i
        calc (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
              (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂)
            ≤ (⨆ j, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂)) :=
              le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans hmem_right))) le_rfl
          _ ≤ ⨆ j, (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂)) :=
              (iSup_inf_eq _ _).le
          _ ≤ w₁ =ᴮ w₂ := by
              apply iSup_le; intro j
              set ctx5 := (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂))
              -- w₁ =ᴮ u.func i, v₁ =ᴮ F i
              have hw1_ui : ctx5 ≤ w₁ =ᴮ u.func i :=
                inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left))
              have hv1_Fi : ctx5 ≤ v₁ =ᴮ F i :=
                inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right))
              -- w₂ =ᴮ u.func j, v₂ =ᴮ F j
              have hw2_uj : ctx5 ≤ w₂ =ᴮ u.func j :=
                inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left)
              have hv2_Fj : ctx5 ≤ v₂ =ᴮ F j :=
                inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right)
              -- v₁ =ᴮ v₂
              have hv12 : ctx5 ≤ v₁ =ᴮ v₂ :=
                inf_le_right.trans (inf_le_right.trans inf_le_right)
              by_cases h_ij : i = j
              · -- i = j: w₁ =ᴮ u.func i =ᴮ u.func j =ᴮ w₂
                subst h_ij
                exact bv_trans hw1_ui (bv_symm hw2_uj)
              · -- i ≠ j: derive contradiction via F i =ᴮ F j ≤ ⊥
                -- v₁ =ᴮ F i, v₁ =ᴮ v₂, v₂ =ᴮ F j → F i =ᴮ F j
                have hFiFj : ctx5 ≤ F i =ᴮ F j :=
                  bv_trans (bv_symm hv1_Fi) (bv_trans hv12 hv2_Fj)
                have h_bot : ctx5 ≤ ⊥ :=
                  le_trans hFiFj (h_inj i j h_ij)
                exact le_trans h_bot bot_le

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
private lemma of_nat_inj' {n k : ℕ} (H_neq : n ≠ k) :
    ((of_nat n : bSet 𝔹) =ᴮ of_nat k) = ⊥ :=
  check_bv_eq_bot_of_not_equiv (PSet.ofNat_inj H_neq)

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



@[ext] private theorem ext {x y : RegularOpens α} (h : (x : Set α) = y) : x = y := Subtype.ext h

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































/-- `generateFrom (opensOver a)` is coarser than `τ a` (they are actually equal). -/
private lemma τ_le_opensOver (a : α) : generateFrom (opensOver a) ≤ τ a := by
  rw [TopologicalSpace.le_def]
  intro s hs
  rw [@isOpen_induced_iff] at hs
  obtain ⟨U, hU_open, hU_eq⟩ := hs
  subst hU_eq
  have ha_true : (fun S : Set α => a ∈ S) ⁻¹' {True} = principalOpen a := by
    ext S; simp [principalOpen]
  have ha_false : (fun S : Set α => a ∈ S) ⁻¹' {False} = coPrincipalOpen a := by
    ext S; simp [coPrincipalOpen]
  have hU : U = ∅ ∨ U = {True} ∨ U = {False} ∨ U = Set.univ := by
    rcases Classical.em (True ∈ U) with hT | hT <;> rcases Classical.em (False ∈ U) with hF | hF
    · right; right; right
      ext p; simp only [Set.mem_univ, iff_true]
      rcases Classical.em p with hp | hp
      · rwa [eq_true hp]
      · rwa [eq_false hp]
    · right; left
      ext p; simp only [Set.mem_singleton_iff]
      rcases Classical.em p with hp | hp
      · rw [eq_true hp]; exact ⟨fun _ => rfl, fun _ => hT⟩
      · rw [eq_false hp]; exact ⟨fun h => absurd h hF, fun h => absurd h (by simp)⟩
    · right; right; left
      ext p; simp only [Set.mem_singleton_iff]
      rcases Classical.em p with hp | hp
      · rw [eq_true hp]; exact ⟨fun h => absurd h hT, fun h => absurd h (by simp)⟩
      · rw [eq_false hp]; exact ⟨fun _ => rfl, fun _ => hF⟩
    · left
      ext p; simp only [Set.mem_empty_iff_false, iff_false]
      rcases Classical.em p with hp | hp
      · rwa [eq_true hp]
      · rwa [eq_false hp]
  rcases hU with rfl | rfl | rfl | rfl
  · have : (fun S : Set α => a ∈ S) ⁻¹' (∅ : Set Prop) = ∅ := Set.preimage_empty
    rw [this]; exact @isOpen_empty _ (generateFrom _)
  · rw [ha_true]; exact isOpen_generateFrom_of_mem (by simp [opensOver])
  · rw [ha_false]; exact isOpen_generateFrom_of_mem (by simp [opensOver])
  · have : (fun S : Set α => a ∈ S) ⁻¹' (Set.univ : Set Prop) = Set.univ := Set.preimage_univ
    rw [this]; exact @isOpen_univ _ (generateFrom _)

































private lemma product_topology_generate_from :
    (product_topology : TopologicalSpace (Set α)) = generateFrom (⋃ a : α, opensOver a) := by
  have hτ : ∀ a : α, τ a = generateFrom (opensOver a) := fun a =>
    le_antisymm (opensOver_le_τ a) (τ_le_opensOver a)
  show Pi.topologicalSpace = generateFrom (⋃ a : α, opensOver a)
  have hpi : Pi.topologicalSpace = ⨅ a : α, τ a := rfl
  have hτeq : ⨅ a : α, τ a = ⨅ a : α, generateFrom (opensOver a) :=
    congrArg iInf (funext hτ)
  rw [hpi, hτeq, generateFrom_iUnion]



private lemma ins₁_out₂_disjoint [DecidableEq α] {x : Set α}
    {p_ins₁ p_out₁ p_ins₂ p_out₂ : Finset α}
    (H_mem₁ : x ∈ p_ins₁.inf principalOpen ∩ p_out₁.inf coPrincipalOpen)
    (H_mem₂ : x ∈ p_ins₂.inf principalOpen ∩ p_out₂.inf coPrincipalOpen)
    (H_disjoint₁ : Disjoint p_ins₁ p_out₁)
    (H_disjoint₂ : Disjoint p_ins₂ p_out₂)
    {a : α} (Ha_left : a ∈ p_ins₁) (Ha_right : a ∈ p_out₂) : False := by
  rw [← principalOpenFinset_eq_inter, ← coPrincipalOpenFinset_eq_inter] at H_mem₁ H_mem₂
  have hmem₁ := (Set.mem_inter_iff _ _ _).mp H_mem₁
  have hmem₂ := (Set.mem_inter_iff _ _ _).mp H_mem₂
  exact hmem₂.2 Ha_right (hmem₁.1 Ha_left)





private lemma univ_mem_standardBasis : Set.univ ∈ @standardBasis α := by
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  left
  exact ⟨∅, ∅, by simp [Finset.inf_empty], by simp⟩







private lemma is_topological_basis_standardBasis :
    @IsTopologicalBasis (Set α) _ standardBasis := by
  refine ⟨?_, ?_, ?_⟩
  · -- exists_subset_inter
    intro t₁ ht₁ t₂ ht₂ x hx
    simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at ht₁ ht₂
    rcases ht₁ with ⟨p_ins₁, p_out₁, H_eq₁, H_disj₁⟩ | rfl
    · rcases ht₂ with ⟨p_ins₂, p_out₂, H_eq₂, H_disj₂⟩ | rfl
      · classical
        subst H_eq₁; subst H_eq₂
        obtain ⟨⟨hx_ins₁, hx_out₁⟩, hx_ins₂, hx_out₂⟩ := hx
        refine ⟨(p_ins₁ ∪ p_ins₂).inf principalOpen ∩ (p_out₁ ∪ p_out₂).inf coPrincipalOpen,
               ?_, ?_, ?_⟩
        · simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
          left
          refine ⟨p_ins₁ ∪ p_ins₂, p_out₁ ∪ p_out₂, rfl, ?_⟩
          rw [Finset.disjoint_left]
          intro a ha_ins ha_out
          simp only [Finset.mem_union] at ha_ins ha_out
          rcases ha_ins with ha_ins₁ | ha_ins₂ <;> rcases ha_out with ha_out₁ | ha_out₂
          · exact Finset.disjoint_left.mp H_disj₁ ha_ins₁ ha_out₁
          · exact ins₁_out₂_disjoint ⟨hx_ins₁, hx_out₁⟩ ⟨hx_ins₂, hx_out₂⟩ H_disj₁ H_disj₂ ha_ins₁ ha_out₂
          · exact ins₁_out₂_disjoint ⟨hx_ins₂, hx_out₂⟩ ⟨hx_ins₁, hx_out₁⟩ H_disj₂ H_disj₁ ha_ins₂ ha_out₁
          · exact Finset.disjoint_left.mp H_disj₂ ha_ins₂ ha_out₂
        · simp only [Finset.inf_union, Set.mem_inter_iff]
          exact ⟨⟨hx_ins₁, hx_ins₂⟩, hx_out₁, hx_out₂⟩
        · intro y hy
          simp only [Finset.inf_union, Set.mem_inter_iff] at hy
          obtain ⟨⟨hy_ins₁, hy_ins₂⟩, hy_out₁, hy_out₂⟩ := hy
          exact ⟨⟨hy_ins₁, hy_out₁⟩, hy_ins₂, hy_out₂⟩
      · exact absurd hx.2 (by simp)
    · exact absurd hx.1 (by simp)
  · -- sUnion_eq
    ext x
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    exact ⟨Set.univ, univ_mem_standardBasis, Set.mem_univ _⟩
  · -- eq_generateFrom
    apply le_antisymm
    · rw [le_generateFrom_iff_subset_isOpen]
      intro T hT
      simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hT
      rcases hT with ⟨p_ins, p_out, H_eq, H_disj⟩ | rfl
      · subst H_eq
        classical
        simp only [Set.mem_setOf_eq]
        apply IsOpen.inter
        · rw [← principalOpenFinset_eq_inter]
          exact (isClopen_principalOpenFinset p_ins).2
        · rw [← coPrincipalOpenFinset_eq_inter]
          exact (isClopen_coPrincipalOpenFinset p_out).2
      · simp only [Set.mem_setOf_eq]; exact isOpen_empty
    · rw [product_topology_generate_from]
      apply generateFrom_anti
      intro X hX
      simp only [Set.mem_iUnion] at hX
      obtain ⟨a, ha⟩ := hX
      simp only [opensOver, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      rcases ha with rfl | rfl | rfl | rfl
      · left; exact ⟨{a}, ∅, by simp [Finset.inf_singleton], by simp⟩
      · left; exact ⟨∅, {a}, by simp [Finset.inf_singleton], by simp⟩
      · left; exact ⟨∅, ∅, by simp, by simp⟩
      · right; rfl

open Cardinal



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


-- src/forcing.lean:50-56


-- src/forcing.lean:58-62


-- src/forcing.lean:63-100: not_CCC_of_uncountable_fiber
variable
  (η₁ η₂ : PSet.{u}) (H_infinite : Cardinal.aleph0 ≤ #(η₁.Type))
  (H_lt : #(η₁.Type) < #(η₂.Type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
  (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
  (H : ∀ β : η₂.Type, (⊥ : 𝔹) < is_func f ⊓ pair (check (η₁.Func (g β))) (check (η₂.Func β)) ∈ᴮ f)



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
universe w in
private lemma pi₂_cast₁ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    HEq p.1 q.1 := by
  subst H'; exact heq_of_eq (congr_arg Prod.fst (eq_of_heq H))

universe w in
private lemma pi₂_cast₂ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    p.2 = q.2 := by
  subst H'; exact congr_arg Prod.snd (eq_of_heq H)





private lemma eq₁_cast' (p : PSet.pSet_aleph2.Type × ℕ) :
    cast eq₁.symm p = (cast eq₀.symm p.1, p.2) := by
  have hcast : HEq p (cast eq₁.symm p) := (cast_heq eq₁.symm p).symm
  apply Prod.ext
  · apply eq_of_heq
    exact (pi₂_cast₁ eq₀.symm hcast).symm.trans (cast_heq eq₀.symm p.1).symm
  · exact (pi₂_cast₂ eq₀.symm hcast).symm

-- src/forcing.lean:178-179


local notation "𝒳" => Set (PSet.pSet_aleph2.Type × ℕ)

-- src/forcing.lean:187-191


private lemma is_clopen_principal_open {ν n} : IsClopen (principal_open ν n).val :=
  CantorSpace.isClopen_principalOpen

-- src/forcing.lean:202-203
private lemma perp_eq_compl_of_clopen {β : Type*} [TopologicalSpace β] {S : Set β}
    (H : IsClopen S) : Sᵖ = Sᶜ := by
  unfold Flypitch.perp; rw [IsClosed.closure_eq H.1]

-- src/forcing.lean:205-209
private lemma mem_neg_principal_open_of_not_mem {ν n S} :
    (cast eq₁ (ν, n) ∈ Sᶜ) → S ∈ ((principal_open ν n)ᶜ).val := by
  intro H
  -- (principal_open ν n)ᶜ in 𝔹 = RegularOpens has val = perp of (principal_open ν n).val
  -- Since principal_open is clopen, perp = complement
  -- (principal_open ν n)ᶜ in 𝔹 has val = perp of (principal_open ν n).val (by RegularOpens.compl_val)
  -- and perp = compl since principal_open is clopen
  have hval : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᶜ := by
    have h1 : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᵖ :=
      Flypitch.RegularOpens.compl_val (principal_open ν n)
    rw [h1, perp_eq_compl_of_clopen is_clopen_principal_open]
  rw [hval]
  -- Goal: S ∈ (principal_open ν n).valᶜ  i.e. S ∉ (principal_open ν n).val
  -- (principal_open ν n).val = CantorSpace.principalOpen (cast eq₁ (ν,n)) = {S | cast eq₁ (ν,n) ∈ S}
  simp only [Set.mem_compl_iff, principal_open, CantorSpace.principalOpen, Set.mem_setOf_eq]
  exact H

-- src/forcing.lean:211-214: structure 𝒞


-- src/forcing.lean:216


-- src/forcing.lean:223-245: ι definition


open CantorSpace

-- src/forcing.lean:249-250


-- src/forcing.lean:252-272: 𝒞_dense_basis
private lemma 𝒞_dense_basis : ∀ T ∈ @standardBasis (PSet.pSet_aleph2.Type × ℕ), ∀ _h : T ≠ ∅,
    ∃ p : 𝒞, (ι p).val ⊆ T := by
  intro T hT _h
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hT
  rcases hT with ⟨p_ins, p_out, hTeq, hDisj⟩ | hTe
  · -- T = p_ins.inf principalOpen ∩ p_out.inf coPrincipalOpen
    -- Helpers for casting
    -- General: x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F
    have key_finset_mem : ∀ {A B : Type} (h : A = B) (F : Finset A) (x : B),
        x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F := by
      intro A B h; subst h; intro F x; simp
    -- General: x ∈ cast (congr_arg Set h).symm S ↔ cast h x ∈ S
    have key_set_mem : ∀ {A B : Type} (h : A = B) (S : Set B) (x : A),
        x ∈ cast (congr_arg Set h).symm S ↔ cast h x ∈ S := by
      intro A B h; subst h; intro S x; simp
    -- (1) a ∈ cast eq₃.symm F' ↔ cast eq₁ a ∈ F' (for F' : Finset B, a : A)
    have cast_finset_symm : ∀ (F' : Finset (PSet.pSet_aleph2.Type × ℕ))
        (a : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ),
        a ∈ (cast eq₃.symm F' : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)) ↔ cast eq₁ a ∈ F' := by
      intro F' a
      -- cast eq₃.symm F' = cast (congr_arg Finset eq₁.symm) F' (since eq₃.symm = congr_arg Finset eq₁.symm)
      -- Then by key_finset_mem with h = eq₁.symm: a ∈ cast (congr_arg Finset eq₁.symm) F' ↔ cast eq₁ a ∈ F'
      have heq : eq₃.symm = congr_arg Finset eq₁.symm := rfl
      rw [heq, key_finset_mem eq₁.symm F' a]
    -- (2) a ∈ cast eq₂.symm S ↔ cast eq₁ a ∈ S (for S : Set B, a : A)
    have cast_set_symm : ∀ (S : Set (PSet.pSet_aleph2.Type × ℕ))
        (a : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ),
        a ∈ cast eq₂.symm S ↔ cast eq₁ a ∈ S := by
      intro S a
      have heq : eq₂.symm = (congr_arg Set eq₁).symm := by rfl
      rw [heq, key_set_mem eq₁ S a]
    -- Construct p' with ins = cast eq₃.symm p_ins, out = cast eq₃.symm p_out
    let p' : 𝒞 :=
      { ins := cast eq₃.symm p_ins
        out := cast eq₃.symm p_out
        H := by
          have hd := Finset.disjoint_left.mp hDisj
          ext a
          simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
          intro ⟨ha1, ha2⟩
          exact hd ((cast_finset_symm p_ins a).mp ha1) ((cast_finset_symm p_out a).mp ha2) }
    refine ⟨p', ?_⟩
    -- Show (ι p').val ⊆ T
    -- T = principalOpenFinset p_ins ∩ coPrincipalOpenFinset p_out
    rw [hTeq, ← principalOpenFinset_eq_inter, ← coPrincipalOpenFinset_eq_inter]
    intro S hS
    simp only [ι, Set.mem_setOf_eq] at hS
    obtain ⟨hS_ins, hS_out⟩ := hS
    simp only [Set.mem_inter_iff, mem_principalOpenFinset_iff, coPrincipalOpenFinset,
      Set.mem_setOf_eq]
    -- Helper: cast eq₁ (cast eq₁.symm z) = z for z : B
    have cast_eq₁_symm_eq : ∀ (z : PSet.pSet_aleph2.Type × ℕ),
        cast eq₁ (cast eq₁.symm z) = z := by
      intro z; rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm z
    constructor
    · intro z hz
      -- z ∈ p_ins, need z ∈ S
      -- cast eq₁.symm z ∈ cast eq₃.symm p_ins: by cast_finset_symm
      have ha : cast eq₁.symm z ∈ p'.ins := (cast_finset_symm p_ins (cast eq₁.symm z)).mpr
        (by rw [cast_eq₁_symm_eq]; exact hz)
      have hmem := hS_ins (Finset.mem_coe.mpr ha)
      rw [cast_set_symm] at hmem
      rw [cast_eq₁_symm_eq] at hmem
      exact hmem
    · intro z hz hzS
      -- z ∈ p_out, need z ∉ S
      have ha : cast eq₁.symm z ∈ p'.out := (cast_finset_symm p_out (cast eq₁.symm z)).mpr
        (by rw [cast_eq₁_symm_eq]; exact hz)
      have hmem := hS_out (Finset.mem_coe.mpr ha)
      rw [cast_set_symm] at hmem
      rw [cast_eq₁_symm_eq] at hmem
      exact hmem hzS
  · -- T = ∅, contradicts _h
    exact absurd hTe _h

-- src/forcing.lean:274-284: 𝒞_dense
private lemma 𝒞_dense {b : 𝔹} (H : ⊥ < b) : ∃ p : 𝒞, ι p ≤ b := by
  have hne : b.val ≠ ∅ := by
    intro heq
    exact H.ne (Flypitch.RegularOpens.ext (Flypitch.RegularOpens.bot_val.trans heq.symm))
  obtain ⟨S_wit, H_wit⟩ := Set.nonempty_iff_ne_empty.mpr hne
  change ∃ p, (ι p).val ⊆ b.val
  rcases (is_topological_basis_standardBasis.exists_subset_of_mem_open H_wit
      (isOpen_of_isRegularOpen b.property))
    with ⟨v, Hv₁, Hv₂, Hv₃⟩
  obtain ⟨p, H_p⟩ := 𝒞_dense_basis v Hv₁ (fun hv => by rw [hv] at Hv₂; exact Hv₂)
  exact ⟨p, Set.Subset.trans H_p Hv₃⟩

-- src/forcing.lean:286-288


-- src/forcing.lean:292-299


-- src/forcing.lean:301-303


-- src/forcing.lean:305-319: 𝒞_nonzero
private lemma 𝒞_nonzero (p : 𝒞) : ⊥ ≠ ι p := by
  -- Show ι p ≠ ⊥ by exhibiting an element S ∈ ι p
  -- The witness is S = cast eq₂ p.ins.toSet
  intro H
  -- H : ⊥ = ι p, so (ι p).val = ∅ (since ⊥ in 𝔹 has empty val)
  have hval_empty : (ι p).val = ∅ := by
    rw [← H]; exact Flypitch.RegularOpens.bot_val
  -- But S := cast eq₂ p.ins.toSet ∈ (ι p).val
  let S : 𝒳 := cast eq₂ p.ins.toSet
  have hS_mem : S ∈ (ι p).val := by
    simp only [ι, Set.mem_setOf_eq]
    constructor
    · -- p.ins.toSet ⊆ cast eq₂.symm S = p.ins.toSet
      intro x hx
      -- Need: x ∈ cast eq₂.symm (cast eq₂ p.ins.toSet)
      -- cast eq₂.symm ∘ cast eq₂ = id
      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T1) (x : T1),
          x ∈ cast (congr_arg Set h).symm (cast (congr_arg Set h) T) ↔ x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      exact (key eq₁ p.ins.toSet x).mpr hx
    · -- p.out.toSet ⊆ cast eq₂.symm Sᶜ = (p.ins.toSet)ᶜ
      intro x hx
      -- Need: x ∈ cast eq₂.symm (cast eq₂ p.ins.toSet)ᶜ = (p.ins.toSet)ᶜ
      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T1) (x : T1),
          x ∈ cast (congr_arg Set h).symm (cast (congr_arg Set h) T)ᶜ ↔ x ∉ T := by
        intro T1 T2 h; subst h; intro T x; simp
      rw [key eq₁]
      -- We need x ∉ p.ins.toSet.
      -- p.H : p.ins ∩ p.out = ∅, x ∈ p.out.toSet
      intro h_ins
      have : x ∈ p.ins ∩ p.out := by
        simp only [Finset.mem_inter, Finset.mem_coe] at *
        exact ⟨h_ins, hx⟩
      rw [p.H] at this
      exact absurd this (Finset.notMem_empty _)
  -- But (ι p).val = ∅ so S ∉ (ι p).val
  exact absurd hS_mem (by rw [hval_empty]; simp)

-- src/forcing.lean:323-350: 𝒞_disjoint_row
private lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : PSet.pSet_aleph2.Type,
    (cast eq₁.symm (ξ, n)) ∉ p.ins ∧ (cast eq₁.symm (ξ, n)) ∉ p.out := by
  -- Let Y' = image π₂ (p.ins ∪ p.out)
  let Y' := Finset.image π₂ (p.ins ∪ p.out)
  by_cases h_empty : (p.ins ∪ p.out) = ∅
  · -- Case: p.ins ∪ p.out = ∅, so p.ins = ∅ and p.out = ∅
    use 0; intro ξ
    have h_ins : p.ins = ∅ := Finset.subset_empty.mp (h_empty ▸ Finset.subset_union_left)
    have h_out : p.out = ∅ := Finset.subset_empty.mp (h_empty ▸ Finset.subset_union_right)
    refine ⟨?_, ?_⟩
    all_goals intro h
    · rw [h_ins] at h; exact Finset.notMem_empty _ h
    · rw [h_out] at h; exact Finset.notMem_empty _ h
  · -- Case: Y' is nonempty
    have h_Y'_nonempty : Y'.Nonempty := by
      apply Finset.Nonempty.image
      exact Finset.nonempty_of_ne_empty h_empty
    let N := Y'.max' h_Y'_nonempty
    use N + 1
    intro ξ
    constructor
    · intro H_mem
      rw [eq₁_cast'] at H_mem
      have hNmem : N + 1 ∈ Y' := by
        simp only [Y', Finset.mem_image]
        exact ⟨_, Finset.mem_union_left _ H_mem, rfl⟩
      exact Nat.not_succ_le_self N (Finset.le_max' _ _ hNmem)
    · intro H_mem
      rw [eq₁_cast'] at H_mem
      have hNmem : N + 1 ∈ Y' := by
        simp only [Y', Finset.mem_image]
        exact ⟨_, Finset.mem_union_right _ H_mem, rfl⟩
      exact Nat.not_succ_le_self N (Finset.le_max' _ _ hNmem)

-- src/forcing.lean:352-353
private lemma 𝒞_anti {p₁ p₂ : 𝒞} : p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → ι p₂ ≤ ι p₁ := by
  intro H₁ H₂
  intro S hS
  obtain ⟨hS₁, hS₂⟩ := hS
  exact ⟨fun x hx => hS₁ (H₁ hx), fun x hx => hS₂ (H₂ hx)⟩

-- ============================================================
-- src/forcing.lean:355-441: namespace cohen_real (inside namespace bSet)
-- ============================================================

namespace bSet

namespace cohen_real











/-- bSet 𝔹 believes that each `mk ν` is a subset of omega -/
private lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ omega := by
  rw [subset_unfold]
  apply le_iInf; intro i
  rw [← deduction]
  simp only [mk_bval, mk_func]
  -- Goal: χ ν i.down ⊓ Γ ≤ of_nat i.down ∈ᴮ omega
  exact le_trans inf_le_left (le_trans le_top omega_definite)

/-- bSet 𝔹 believes that each `mk ν` is an element of 𝒫(ω) -/
private lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

-- src/forcing.lean:379-386
private lemma sep {n} {Γ} {ν₁ ν₂} (H₁ : Γ ≤ of_nat n ∈ᴮ mk ν₁)
    (H₂ : Γ ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ) :
    Γ ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ := by
  -- Show: (mk ν₁ =ᴮ mk ν₂) ⊓ Γ ≤ ⊥, which is equivalent
  -- Use le_neg_of_inf_eq_bot: to show Γ ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ, show (mk ν₁ =ᴮ mk ν₂) ⊓ Γ = ⊥
  apply le_neg_of_inf_eq_bot
  rw [le_antisymm_iff]; constructor
  · -- (mk ν₁ =ᴮ mk ν₂) ⊓ Γ ≤ ⊥
    apply le_bot_iff.mpr
    -- Use subst_congr_mem_right: mk ν₁ =ᴮ mk ν₂ ⊓ of_nat n ∈ᴮ mk ν₁ ≤ of_nat n ∈ᴮ mk ν₂
    rw [eq_bot_iff]
    have hmem : mk ν₁ =ᴮ mk ν₂ ⊓ Γ ≤ of_nat n ∈ᴮ mk ν₂ :=
      le_trans (le_inf inf_le_left (le_trans inf_le_right H₁)) subst_congr_mem_right
    exact le_trans (le_inf hmem (le_trans inf_le_right H₂)) inf_compl_eq_bot.le
  · exact bot_le

-- src/forcing.lean:388-398
private lemma not_mem_of_not_mem {p : 𝒞} {ν} {n} (H : (ν, n) ∈ p.out) :
    ι p ≤ (of_nat n ∈ᴮ mk ν)ᶜ := by
  rw [mem_unfold, compl_iSup]
  apply le_iInf; intro k
  rw [compl_inf]
  by_cases hk : n = k.down
  · subst hk
    simp only [mk_bval, mk_func]
    rw [bv_eq_refl, compl_top, sup_bot_eq]
    intro S hS
    apply mem_neg_principal_open_of_not_mem
    have hS₂ := hS.2 (Finset.mem_coe.mpr H)
    have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
        x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
      intro T1 T2 h; subst h; intro T x; simp
    exact (key eq₁ Sᶜ (ν, k.down)).mp hS₂
  · have : of_nat n =ᴮ (of_nat k.down : bSet 𝔹) = ⊥ := of_nat_inj' hk
    simp only [mk_bval, mk_func, this, compl_bot, sup_top_eq]; exact le_top

-- src/forcing.lean:400-406
private lemma inj_cast_lemma (ν' : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n' : ℕ) :
    cast eq₁.symm (cast eq₀ ν', n') = (ν', n') := by
  rw [eq₁_cast']; simp [cast_cast]

/-- Whenever ν₁ ≠ ν₂ < ℵ₂, bSet 𝔹 believes that `mk ν₁` and `mk ν₂` are distinct -/
private lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : mk ν₁ =ᴮ mk ν₂ ≤ (⊥ : 𝔹) := by
  by_contra h
  replace h : ⊥ < mk ν₁ =ᴮ mk ν₂ := lt_of_le_of_ne bot_le (Ne.symm (mt le_bot_iff.mpr h))
  obtain ⟨p, H_p⟩ := 𝒞_dense h
  obtain ⟨n, H_n⟩ := 𝒞_disjoint_row p
  -- p'.ins = insert (ν₁, n) p.ins, p'.out = insert (ν₂, n) p.out
  -- Note: ν₁, ν₂ : (check pSet_aleph2).type, so (ν₁, n), (ν₂, n) are in the right type
  -- H_n gives: cast eq₁.symm (cast eq₀ ν₁, n) = (ν₁, n) ∉ p.ins ∧ ∉ p.out (by inj_cast_lemma)
  have Hν₁_ins : (ν₁, n) ∉ p.ins := by
    have := (H_n (cast eq₀ ν₁)).1
    rwa [inj_cast_lemma] at this
  have Hν₁_out : (ν₁, n) ∉ p.out := by
    have := (H_n (cast eq₀ ν₁)).2
    rwa [inj_cast_lemma] at this
  have Hν₂_ins : (ν₂, n) ∉ p.ins := by
    have := (H_n (cast eq₀ ν₂)).1
    rwa [inj_cast_lemma] at this
  have Hν₂_out : (ν₂, n) ∉ p.out := by
    have := (H_n (cast eq₀ ν₂)).2
    rwa [inj_cast_lemma] at this
  let p' : 𝒞 :=
    { ins := insert (ν₁, n) p.ins
      out := insert (ν₂, n) p.out
      H := by
        ext a
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨ha_ins, ha_out⟩
        simp only [Finset.mem_insert] at ha_ins ha_out
        rcases ha_ins with rfl | ha_ins
        · -- a = (ν₁, n), and ha_out : (ν₁, n) = (ν₂, n) ∨ (ν₁, n) ∈ p.out
          rcases ha_out with h_eq | ha_out
          · -- (ν₁, n) = (ν₂, n), so ν₁ = ν₂
            exact H_neq (Prod.mk.inj h_eq).1
          · exact Hν₁_out ha_out
        · -- a ∈ p.ins
          rcases ha_out with rfl | ha_out
          · -- (ν₂, n) ∈ p.ins, contradicts Hν₂_ins
            exact Hν₂_ins ha_ins
          · -- a ∈ p.ins ∩ p.out = ∅
            have : a ∈ p.ins ∩ p.out := Finset.mem_inter.mpr ⟨ha_ins, ha_out⟩
            rw [p.H] at this
            exact Finset.notMem_empty _ this }
  -- ι p' ≤ ι p (by 𝒞_anti, since p'.ins ⊇ p.ins and p'.out ⊇ p.out)
  have anti : ι p' ≤ ι p :=
    𝒞_anti (fun i hi => Finset.mem_insert_of_mem hi)
           (fun i hi => Finset.mem_insert_of_mem hi)
  -- ι p' ≤ of_nat n ∈ᴮ mk ν₁
  have this₁ : ι p' ≤ of_nat n ∈ᴮ mk ν₁ := by
    rw [mem_unfold]
    apply le_iSup_of_le (ULift.up n)
    simp only [mk_bval, mk_func, χ, bv_refl, le_inf_iff]
    constructor
    · -- ι p' ≤ principal_open ν₁ n
      intro S hS
      simp only [ι, Set.mem_setOf_eq] at hS
      have hins : (ν₁, n) ∈ (p' : 𝒞).ins.toSet :=
        Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
      have hmem := hS.1 hins
      -- hmem : (ν₁, n) ∈ cast eq₂.symm S, i.e., cast eq₁ (ν₁, n) ∈ S
      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
          x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      rw [show (principal_open ν₁ n).val = CantorSpace.principalOpen (cast eq₁ (ν₁, n)) from rfl]
      exact (key eq₁ S (ν₁, n)).mp hmem
    · trivial  -- bv_refl : of_nat n =ᴮ of_nat n = ⊤ simplified to True
  -- ι p' ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ
  have this₂ : ι p' ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ :=
    not_mem_of_not_mem (Finset.mem_insert_self (ν₂, n) p.out)
  -- ι p' ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ (from sep)
  have this₃ : ι p' ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ := sep this₁ this₂
  -- ι p' ≤ mk ν₁ =ᴮ mk ν₂ (via ι p' ≤ ι p ≤ mk ν₁ =ᴮ mk ν₂)
  have this₄ : ι p' ≤ mk ν₁ =ᴮ mk ν₂ := le_trans anti H_p
  -- Contradiction: ι p' = ⊥, but 𝒞_nonzero says ⊥ ≠ ι p'
  have this₅ : ι p' = ⊥ := le_antisymm (le_trans (le_inf this₄ this₃) inf_compl_eq_bot.le) bot_le
  exact (𝒞_nonzero p') this₅.symm

end cohen_real

-- ============================================================
-- src/forcing.lean:443-567: section neg_CH
-- ============================================================

section neg_CH
-- (still inside namespace bSet)

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)

-- src/forcing.lean:450-457


-- src/forcing.lean:459-466


-- src/forcing.lean:468-487


-- src/forcing.lean:489-504


-- src/forcing.lean:507-509




-- src/forcing.lean:513-529: cohen_real.mk_ext


-- src/forcing.lean:531-532


-- src/forcing.lean:534-546
set_option maxHeartbeats 400000 in
private theorem aleph2_le_powerset_omega :
    ⊤ ≤ is_func' (check PSet.pSet_aleph2) 𝔠 neg_CH_func ⊓ is_inj neg_CH_func := by
  apply le_inf
  · -- is_func' (check PSet.pSet_aleph2) 𝔠 neg_CH_func = is_func neg_CH_func ⊓ is_total ...
    apply le_inf
    · -- is_func neg_CH_func
      exact functionMk_is_func _ cohen_real.mk_ext
    · -- is_total (check PSet.pSet_aleph2) 𝔠 neg_CH_func
      apply le_iInf; intro w₁; rw [← deduction, top_inf_eq]
      -- w₁ ∈ check PSet.pSet_aleph2 ≤ ⨆ w₂, w₂ ∈ 𝔠 ⊓ pair w₁ w₂ ∈ neg_CH_func
      -- Unfold the membership w₁ ∈ check PSet.pSet_aleph2 to extract ν
      rw [mem_unfold]
      -- ⨆ ν, (check pSet_aleph2).bval ν ⊓ w₁ =ᴮ (check pSet_aleph2).func ν ≤ ⨆ w₂, ...
      apply iSup_le; intro ν
      -- (check pSet_aleph2).bval ν ⊓ w₁ =ᴮ (check pSet_aleph2).func ν ≤ ⨆ w₂, ...
      rw [check_bval_top, top_inf_eq]
      -- w₁ =ᴮ (check pSet_aleph2).func ν ≤ ⨆ w₂, w₂ ∈ 𝔠 ⊓ pair w₁ w₂ ∈ neg_CH_func
      apply le_iSup_of_le (cohen_real.mk ν)
      -- cohen_real.definite' : Γ ≤ cohen_real.mk ν ∈ 𝔠
      -- functionMk_self : check.bval ν ≤ pair (check.func ν) (mk ν) ∈ neg_CH_func
      -- We need: w₁ =ᴮ check.func ν ≤ mk ν ∈ 𝔠 ⊓ pair w₁ (mk ν) ∈ neg_CH_func
      apply le_inf
      · -- mk ν ∈ 𝔠
        exact le_trans le_top cohen_real.definite'
      · -- pair w₁ (mk ν) ∈ neg_CH_func
        -- w₁ =ᴮ (check pSet_aleph2).func ν; pair (check.func ν) (mk ν) ∈ neg_CH_func by functionMk_self
        -- Use bv_rw' with H := w₁ =ᴮ check.func ν (the current goal), ϕ := fun z => pair z (mk ν) ∈ neg_CH_func
        have h_func_mem : (⊤ : 𝔹) ≤ pair ((check PSet.pSet_aleph2).func ν) (cohen_real.mk ν) ∈ᴮ neg_CH_func := by
          have := @functionMk_self 𝔹 _ (check PSet.pSet_aleph2) (fun x => cohen_real.mk x)
            cohen_real.mk_ext ν
          rwa [check_bval_top] at this
        -- Γ = w₁ =ᴮ check.func ν, use bv_rw' to get pair w₁ (mk ν) ∈ neg_CH_func from pair (check.func ν) (mk ν) ∈ neg_CH_func
        exact bv_rw' (H := le_refl _) (ϕ := fun z => pair z (cohen_real.mk ν) ∈ᴮ neg_CH_func)
          (h_congr := B_ext_pair_mem_left) (H_new := le_trans le_top h_func_mem)
  · -- is_inj neg_CH_func
    exact functionMk_inj_of_inj (fun i j h => cohen_real.inj h) cohen_real.mk_ext

-- src/forcing.lean:548-550
private lemma aleph1_Ord {Γ : 𝔹} : Γ ≤ Ord (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) :=
  Ord_card_ex _



-- src/forcing.lean:552-562
private theorem neg_CH_cohenProof03 : (⊤ : 𝔹) ≤ CHᶜ := by
  simp only [CH, compl_compl]
  exact le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 1)))
    (le_inf aleph1_Ord (le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 2)))
      (le_inf (le_inf aleph0_lt_aleph1_bSet aleph1_lt_aleph2_bSet)
        (le_iSup_of_le neg_CH_func aleph2_le_powerset_omega))))

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
    (@bSet.CH.{0} 𝔹_cohen 𝔹_boolean_algebra)) :=
  @bSet.neg_CH_cohenProof03
