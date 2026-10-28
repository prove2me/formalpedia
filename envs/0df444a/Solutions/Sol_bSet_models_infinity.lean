-- Prove2me | solution 1 for bSet_models_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T02:08:39.763408+00:00
-- url     : https://prove2.me/submissions/d1d36295-7eaa-4d2f-a954-fc417b2195e9

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








-- Aliases without `@[simp]`: mathlib4's `inf_idem`/`sup_idem` already carry `@[simp]`,
-- so adding `@[simp]` here would create duplicate rewrite rules.




-- Note: bot_lt_iff_not_le_bot and lt_top_iff_not_top_le already exist in mathlib4












open scoped Flypitch




























-- Note: Lean 4 already has a `imp_self` in core; use `ba_imp_self` for Boolean algebra version

























-- Aliases without `@[simp]`: mathlib4's `iSup_option`/`iInf_option` already carry `@[simp]`.








































-- Note: le_trans' already exists in Mathlib (as alias for ge_trans)
-- Use le_trans_inf for our version











































private theorem bv_absurd {β} [BooleanAlgebra β] {Γ : β} (b : β) (H₁ : Γ ≤ b) (H₂ : Γ ≤ bᶜ) :
    Γ ≤ ⊥ :=
  le_trans (le_inf H₁ H₂) inf_compl_eq_bot.le



















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






private lemma is_epsilon_well_founded (x : PSet.{u}) :
    ∀ (u : PSet.{u}), u ⊆ x → ¬ Equiv u (∅ : PSet.{u}) →
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  intro u _Hu Hu_ne_empty
  classical
  by_contra h
  push_neg at h
  -- h : ∀ y ∈ u, ∃ z ∈ u, z ∈ y
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty Hu_ne_empty
  obtain ⟨y, Hy₁, Hy₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  -- y is a ZFSet with y ∈ ZFSet.mk u and (ZFSet.mk u) ∩ y = ∅
  -- Get a PSet representative: y.out is a PSet with ZFSet.mk y.out = y
  have Hy₁' : y.out ∈ u := by
    have : ZFSet.mk y.out ∈ ZFSet.mk u := by
      rw [ZFSet.mk_out y]; exact Hy₁
    exact mem_iff.mpr this
  obtain ⟨z, Hz₁, Hz₂⟩ := h y.out Hy₁'
  -- z ∈ u and z ∈ y.out → contradiction since ZFSet.mk u ∩ y = ∅
  apply ZFSet.notMem_empty (ZFSet.mk z)
  rw [← Hy₂]
  apply ZFSet.mem_inter.mpr
  exact ⟨mem_iff.mp Hz₁, by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz₂⟩

















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









private lemma ofNat_of_mem_ofNat {y : PSet.{u}} {k : ℕ}
    (H_mem : y ∈ (PSet.ofNat k : PSet.{u})) :
    ∃ j, Equiv y (PSet.ofNat j : PSet.{u}) := by
  induction k with
  | zero => exact absurd H_mem (PSet.notMem_empty _)
  | succ k ih =>
    rw [ofNat_succ, succ_ord] at H_mem
    rcases PSet.mem_insert_iff.mp H_mem with heq | hin
    · exact ⟨k, heq⟩
    · exact ih hin







/-! ### Transitivity and well-orders for omega (src lines 770-800) -/

private lemma is_transitive_omega : is_transitive (PSet.omega : PSet.{u}) := by
  intro z Hz
  rw [PSet.mem_def] at Hz
  obtain ⟨⟨k⟩, Hk⟩ := Hz
  apply subset_of_all_mem; intro y Hy
  rw [PSet.mem_def]
  -- omega.Type = ULift ℕ; Func ⟨k⟩ = ofNat k
  simp only [PSet.omega]
  -- Hy : y ∈ z, Hk : Equiv z (ofNat k)
  -- So y ∈ ofNat k; find j with y ≡ ofNat j
  obtain ⟨j, hj⟩ := ofNat_of_mem_ofNat ((PSet.Mem.congr_right Hk).mp Hy)
  exact ⟨⟨j⟩, hj⟩

private lemma is_ewo_omega : epsilon_well_orders (PSet.omega : PSet.{u}) := by
  constructor
  · -- trichotomy
    intro y Hy z Hz
    rw [PSet.mem_def] at Hy Hz
    obtain ⟨⟨k₁⟩, Hk₁⟩ := Hy
    obtain ⟨⟨k₂⟩, Hk₂⟩ := Hz
    rcases lt_trichotomy k₁ k₂ with h | rfl | h
    · right; left
      rw [PSet.Mem.congr_left Hk₁, PSet.Mem.congr_right Hk₂]
      exact ofNat_mem_of_lt h
    · left; exact PSet.Equiv.trans Hk₁ Hk₂.symm
    · right; right
      rw [PSet.Mem.congr_left Hk₂, PSet.Mem.congr_right Hk₁]
      exact ofNat_mem_of_lt h
  · exact is_epsilon_well_founded _







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
private lemma bv_or_left {a b₁ b₂ : 𝔹} (h₁ : a ≤ b₁) : a ≤ b₁ ⊔ b₂ :=
  le_trans h₁ le_sup_left

-- src/bvm.lean:126
private lemma bv_or_right {a b₁ b₂ : 𝔹} (h₂ : a ≤ b₂) : a ≤ b₁ ⊔ b₂ :=
  le_trans h₂ le_sup_right

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








private lemma contains_empty_check_omega : (⊤ : 𝔹) ≤ contains_empty (check ω') := by
  simp only [contains_empty]
  -- ∅ = (check ω').func ⟨0⟩ since check_omega_func and PSet.ofNat 0 = ∅
  have h : (∅ : bSet 𝔹) = (check ω').func ⟨0⟩ := by
    simp only [check_omega_func]
    -- PSet.ofNat 0 = ∅, so check (PSet.ofNat 0) = check ∅ = ∅
    norm_cast
    simp [show PSet.ofNat 0 = ∅ from rfl, check_empty_eq_empty]
  rw [h, top_le_iff]
  exact check_mem_top





-- src/bvm.lean:2234








private lemma omega_definite {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega := by
  suffices h : of_nat n ∈ᴮ omega = (⊤ : 𝔹) by
    exact le_trans le_top (by rwa [top_le_iff])
  apply top_unique
  induction n with
  | zero => apply bv_use (ULift.up 0); simp
  | succ k _ => apply bv_use (ULift.up (k + 1)); simp

private lemma of_nat_mem_omega {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega := omega_definite







-- src/bvm.lean:2261
private lemma zero_eq_empty {Γ : 𝔹} : Γ ≤ (0 : bSet 𝔹) =ᴮ ∅ := by
  change Γ ≤ of_nat 0 =ᴮ ∅
  rw [← check_empty_eq_empty]
  exact check_bv_eq (by rfl)

-- Helper: PSet-level membership gives check-level membership




-- src/bvm.lean:2270 (one_eq_singleton_zero) -- TODO: singleton notation for bSet
-- lemma one_eq_singleton_zero : Γ ≤ (1 : bSet 𝔹) =ᴮ {(0 : bSet 𝔹)} := by sorry





-- src/bvm.lean:2291
private theorem bSet_axiom_of_infinity' :
    (⊤ : 𝔹) ≤ (∅ ∈ᴮ omega) ⊓ (⨅ x, x ∈ᴮ omega ⟹ ⨆ y, y ∈ᴮ omega ⊓ x ∈ᴮ y) := by
  apply le_inf
  · exact contains_empty_check_omega
  · -- ⊤ ≤ ⨅ x, x ∈ᴮ omega ⟹ ⨆ y, y ∈ᴮ omega ⊓ x ∈ᴮ y
    -- For each x ∈ᴮ omega, show ⊤ ≤ ⨆ y, y ∈ᴮ omega ⊓ x ∈ᴮ y
    -- omega = check ω' = mk (ULift ℕ) (fun k => of_nat k.down) (fun _ => ⊤)
    -- x ∈ᴮ omega = ⨆ k, ⊤ ⊓ of_nat k.down =ᴮ x = ⨆ k, of_nat k.down =ᴮ x
    apply le_iInf; intro x
    rw [← deduction, top_inf_eq]
    -- x ∈ᴮ omega ≤ ⨆ y, y ∈ᴮ omega ⊓ x ∈ᴮ y
    -- Manually unfold just the LHS x ∈ᴮ omega
    rw [mem_unfold]; simp only [omega_bval, omega_func, top_inf_eq]
    apply iSup_le; intro ⟨k⟩
    -- of_nat k =ᴮ x ≤ ⨆ y, y ∈ᴮ omega ⊓ x ∈ᴮ y
    apply le_iSup_of_le (of_nat (k + 1))
    apply le_inf
    · -- of_nat k =ᴮ x ≤ of_nat (k+1) ∈ᴮ omega
      exact le_trans le_top omega_definite
    · -- x =ᴮ of_nat k ≤ x ∈ᴮ of_nat (k+1)
      -- via subst_congr_mem_left: of_nat k =ᴮ x ⊓ of_nat k ∈ᴮ of_nat(k+1) ≤ x ∈ᴮ of_nat(k+1)
      have h_kmem : (of_nat k : bSet 𝔹) ∈ᴮ of_nat (k + 1) = ⊤ := of_nat_mem_of_nat_succ k
      calc x =ᴮ of_nat k
          = of_nat k =ᴮ x := bv_eq_symm
        _ ≤ of_nat k =ᴮ x ⊓ (of_nat k : bSet 𝔹) ∈ᴮ of_nat (k + 1) :=
            le_inf le_rfl (h_kmem ▸ le_top)
        _ ≤ x ∈ᴮ of_nat (k + 1) := subst_congr_mem_left

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



private lemma mem_comprehend_iff : ∀ {z : bSet 𝔹} {Γ : 𝔹}, Γ ≤ z ∈ᴮ comprehend ϕ x ↔
    Γ ≤ ⨆ (i : x.type), x.bval i ⊓ (z =ᴮ x.func i ⊓ (fun i : x.type => ϕ (x.func i)) i) := by
  intros; exact mem_subset.mk_iff₂

include H_congr in
private lemma mem_comprehend_iff₂ : ∀ {z : bSet 𝔹} {Γ : 𝔹}, Γ ≤ z ∈ᴮ comprehend ϕ x ↔
    Γ ≤ ⨆ w, w ∈ᴮ x ⊓ (z =ᴮ w ⊓ ϕ w) := by
  intro z Γ
  rw [mem_comprehend_iff]
  -- Use bounded_exists: ⨆ i, x.bval i ⊓ ψ (x.func i) = ⨆ w, w ∈ᴮ x ⊓ ψ w
  -- where ψ w = z =ᴮ w ⊓ ϕ w
  have h_cong : ∀ a b : bSet 𝔹, a =ᴮ b ⊓ (z =ᴮ a ⊓ ϕ a) ≤ z =ᴮ b ⊓ ϕ b := by
    intro a b
    apply le_inf
    · -- a =ᴮ b ⊓ z =ᴮ a ≤ z =ᴮ b (by bv_eq_trans: z =ᴮ a ⊓ a =ᴮ b ≤ z =ᴮ b)
      calc a =ᴮ b ⊓ (z =ᴮ a ⊓ ϕ a)
          ≤ a =ᴮ b ⊓ z =ᴮ a := inf_le_inf_left _ inf_le_left
        _ = z =ᴮ a ⊓ a =ᴮ b := by rw [inf_comm]
        _ ≤ z =ᴮ b := bv_eq_trans
    · exact le_trans (inf_le_inf_left _ inf_le_right) (H_congr a b)
  rw [← @bounded_exists _ _ x (fun w => z =ᴮ w ⊓ ϕ w) (h_congr := h_cong)]



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
private lemma mem_binary_inter_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ∈ᴮ (x ∩ᴮ y) ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ z ∈ᴮ y) := by
  -- (x ∩ᴮ y).bval i = x.bval i ⊓ (x.func i ∈ᴮ y)
  -- (x ∩ᴮ y).func i = x.func i
  -- z ∈ᴮ (x ∩ᴮ y) = ⨆ i, (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
  constructor
  · intro H
    constructor
    · -- z ∈ᴮ x: strip the x.func i ∈ᴮ y part
      rw [mem_unfold] at H ⊢
      apply le_trans H; apply iSup_le; intro i
      apply le_iSup_of_le i
      simp only [binary_inter_bval, binary_inter_func]
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · -- z ∈ᴮ y: from x.func i ∈ᴮ y and z =ᴮ x.func i
      -- Use subst_congr_mem_left' with u=x.func i, v=z, w=y
      -- need: Γ_1 ≤ x.func i =ᴮ z and Γ_1 ≤ x.func i ∈ᴮ y
      rw [mem_unfold] at H
      apply le_trans H; apply iSup_le; intro i
      simp only [binary_inter_bval, binary_inter_func]
      -- Γ_1 = (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
      exact subst_congr_mem_left' (bv_symm inf_le_right) (inf_le_left.trans inf_le_right)
  · intro ⟨H₁, H₂⟩
    -- Use H₁ : Γ ≤ z ∈ᴮ x and H₂ : Γ ≤ z ∈ᴮ y
    -- z ∈ᴮ x = ⨆ i, x.bval i ⊓ z =ᴮ x.func i
    -- We need ⨆ i, (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
    -- Augment with H₂: Γ ≤ (⨆ i, x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y
    -- Then: (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y ≤ (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
    rw [mem_unfold] at H₁ ⊢
    calc Γ ≤ (⨆ i : x.type, x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y := le_inf H₁ H₂
      _ ≤ ⨆ i : x.type, (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y := by
              rw [iSup_inf_eq]
      _ ≤ ⨆ i : (x ∩ᴮ y).type, (x ∩ᴮ y).bval i ⊓ z =ᴮ (x ∩ᴮ y).func i := by
              apply iSup_le; intro i; apply le_iSup_of_le i
              simp only [binary_inter_bval, binary_inter_func]
              -- (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y ≤ (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
              refine le_inf (le_inf ?_ ?_) ?_
              · exact inf_le_left.trans inf_le_left
              · -- (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y ≤ x.func i ∈ᴮ y
                -- Use subst_congr_mem_left: z =ᴮ x.func i ⊓ z ∈ᴮ y ≤ x.func i ∈ᴮ y
                exact le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
                               subst_congr_mem_left
              · exact inf_le_left.trans inf_le_right

-- src/bvm_extras.lean:112


-- src/bvm_extras.lean:126


-- src/bvm_extras.lean:132


-- src/bvm_extras.lean:139


-- src/bvm_extras.lean:146
private lemma binary_inter_subset_left {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ x := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
    mem_binary_inter_iff.mp inf_le_right
  exact h.1

-- src/bvm_extras.lean:150
private lemma binary_inter_subset_right {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ y := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
    mem_binary_inter_iff.mp inf_le_right
  exact h.2

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


-- src/bvm_extras.lean:2041


-- ============================================================
-- src/bvm_extras.lean:2080-2136: bot_of_mem_self, bot_of_mem_mem
-- ============================================================

-- src/bvm_extras.lean:2080
private lemma bot_of_mem_self {x : bSet 𝔹} : (⊤ : 𝔹) ≤ (x ∈ᴮ x ⟹ ⊥) := by
  induction x using bSet.rec' with
  | _ x IH =>
    -- IH : ∀ a : x.type, ⊤ ≤ (x.func a ∈ᴮ x.func a ⟹ ⊥)
    rw [← deduction, top_inf_eq]
    -- Goal: x ∈ x ≤ ⊥
    rw [mem_unfold]; apply iSup_le; intro i
    -- LHS: x.bval i ⊓ x =ᴮ x.func i
    -- From x.bval i: x.func i ∈ x (by mem_mk'')
    -- From x =ᴮ x.func i and x.func i ∈ x: x.func i ∈ x.func i (by subst_congr_mem_right)
    have h_mem : x.bval i ⊓ x =ᴮ x.func i ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_left (mem_mk'' le_rfl)
    have h_self_mem : x.bval i ⊓ x =ᴮ x.func i ≤ x.func i ∈ᴮ x.func i :=
      le_trans (le_inf inf_le_right h_mem) subst_congr_mem_right
    have h_bot_iff : (⊤ : 𝔹) ≤ x.func i ∈ᴮ x.func i ⟹ ⊥ := IH i
    rw [← deduction, top_inf_eq] at h_bot_iff
    exact le_trans h_self_mem h_bot_iff

-- src/bvm_extras.lean:2093
private lemma bot_of_mem_self' {x : bSet 𝔹} {Γ} (H : Γ ≤ (x ∈ᴮ x)) : Γ ≤ ⊥ := by
  have h := @bot_of_mem_self 𝔹 _ x
  -- h : ⊤ ≤ x ∈ᴮ x ⟹ ⊥, i.e., ⊤ ⊓ x ∈ᴮ x ≤ ⊥ (by ← deduction)
  calc Γ ≤ ⊤ ⊓ x ∈ᴮ x := le_inf le_top H
    _ ≤ ⊥ := by rwa [← deduction] at h

-- src/bvm_extras.lean:2099


-- src/bvm_extras.lean:2110
private lemma bot_of_mem_mem (x y : bSet 𝔹) : (⊤ : 𝔹) ≤ ((x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥) := by
  induction x using bSet.rec' generalizing y with
  | _ x IHx =>
    induction y using bSet.rec' with
    | _ y IHy =>
      -- IHx : ∀ a' : x.type, ∀ z, ⊤ ≤ (x.func a' ∈ z ⊓ z ∈ x.func a' ⟹ ⊥)
      -- IHy : ∀ a'' : y.type, ⊤ ≤ (x ∈ y.func a'' ⊓ y.func a'' ∈ x ⟹ ⊥)
      rw [← deduction, top_inf_eq]
      -- Goal: x ∈ y ⊓ y ∈ x ≤ ⊥
      -- Unfold x ∈ y and y ∈ x
      rw [mem_unfold (v := y), mem_unfold (v := x)]
      -- x ∈ y = ⨆ a'', y.bval a'' ⊓ x =ᴮ y.func a''
      -- y ∈ x = ⨆ a', x.bval a' ⊓ y =ᴮ x.func a'
      -- (⨆ a'', ...) ⊓ (⨆ a', ...) ≤ ⊥
      calc (⨆ a'' : y.type, y.bval a'' ⊓ x =ᴮ y.func a'') ⊓
            (⨆ a' : x.type, x.bval a' ⊓ y =ᴮ x.func a')
          ≤ ⨆ a'' : y.type, (y.bval a'' ⊓ x =ᴮ y.func a'') ⊓
              (⨆ a' : x.type, x.bval a' ⊓ y =ᴮ x.func a') := (iSup_inf_eq _ _).le
        _ ≤ ⊥ := by
            apply iSup_le; intro a''
            calc (y.bval a'' ⊓ x =ᴮ y.func a'') ⊓
                (⨆ a' : x.type, x.bval a' ⊓ y =ᴮ x.func a')
                ≤ ⨆ a' : x.type, (x.bval a' ⊓ y =ᴮ x.func a') ⊓
                    (y.bval a'' ⊓ x =ᴮ y.func a'') := by
                      rw [inf_comm]; exact (iSup_inf_eq _ _).le
              _ ≤ ⊥ := by
                  apply iSup_le; intro a'
                  -- Context: (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'')
                  -- From x.bval a': x.func a' ∈ x (by mem_mk'')
                  -- From y =ᴮ x.func a' and ... : convert
                  -- We need x.func a' ∈ y.func a'' ⊓ y.func a'' ∈ x.func a'
                  -- Apply IHx a' (y.func a'')
                  have h_IH := IHx a' (y.func a'')
                  rw [← deduction, top_inf_eq] at h_IH
                  apply le_trans _ h_IH
                  -- Need: ctx ≤ x.func a' ∈ y.func a'' ⊓ y.func a'' ∈ x.func a'
                  -- From y =ᴮ x.func a': convert (x ∈ y) to (x ∈ x.func a')
                  -- From x =ᴮ y.func a'': convert (y ∈ x) to (y ∈ y.func a'')
                  -- From x.bval a' ≤ x.func a' ∈ x and y =ᴮ x.func a' → subst
                  refine le_inf ?_ ?_
                  · -- x.func a' ∈ y.func a''
                    -- Have: x =ᴮ y.func a'' (from a''-context, inf_right.trans inf_right)
                    -- Have: x.func a' ∈ x (from a'-context: x.bval a' ≤ x.func a' ∈ x)
                    -- Wait, x.func a' ∈ y.func a'' from... let me think
                    -- We have y.bval a'' ≤ y.func a'' ∈ y (by mem_mk'')
                    -- And x =ᴮ y.func a'' (inf_right.trans inf_right)
                    -- So y.func a'' ∈ y → y.func a'' ∈ x via x =ᴮ y.func a'' (bv_symm + subst)
                    -- Not quite. We need x.func a' ∈ y.func a''.
                    -- From y =ᴮ x.func a' and x.func a' ∈ y... wait
                    -- x.func a' ∈ y by: y.bval a'' ⊓ ... from y and x.func a' ??? No.
                    -- Actually: x.func a' ∈ y iff in context (y =ᴮ x.func a'), (something) ∈ x.func a'
                    -- We have y.bval a'' ≤ y.func a'' ∈ y. And x =ᴮ y.func a''.
                    -- x ∈ y (from original?) but we've unfolded it...
                    -- Let me use: y.bval a'' ⊓ x =ᴮ y.func a'' ≤ x.func a' ∈ y.func a''
                    -- From y =ᴮ x.func a' and y.func a'' ∈ x.func a' (via y.bval a'' ≤ y.func a'' ∈ y and y =ᴮ x.func a')
                    -- Hmm. This approach is getting complicated.
                    -- From IHy a'': ⊤ ≤ x ∈ y.func a'' ⊓ y.func a'' ∈ x ⟹ ⊥
                    -- We need x.func a' ∈ y.func a''.
                    -- Simpler: from y =ᴮ x.func a' and y.func a'' ∈ y → y.func a'' ∈ x.func a'
                    -- And from x =ᴮ y.func a'' and x.func a' ∈ x → x.func a' ∈ y.func a''? No
                    -- Let's be careful:
                    -- ctx = (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'')
                    -- From x.bval a': mem_mk'' → x.func a' ∈ x
                    -- From x =ᴮ y.func a'': subst_congr_mem_right → x.func a' ∈ y.func a''
                    have h1 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        x.func a' ∈ᴮ x :=
                      inf_le_left.trans (inf_le_left.trans (mem_mk'' le_rfl))
                    have h2 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        x =ᴮ y.func a'' := inf_le_right.trans inf_le_right
                    -- x.func a' ∈ x and x =ᴮ y.func a'' → x.func a' ∈ y.func a''
                    exact le_trans (le_inf h2 h1) subst_congr_mem_right
                  · -- y.func a'' ∈ x.func a'
                    -- From y.bval a'': mem_mk'' → y.func a'' ∈ y
                    -- From y =ᴮ x.func a'': subst_congr_mem_right → y.func a'' ∈ x.func a'
                    have h3 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        y.func a'' ∈ᴮ y :=
                      inf_le_right.trans (inf_le_left.trans (mem_mk'' le_rfl))
                    have h4 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        y =ᴮ x.func a' := inf_le_left.trans inf_le_right
                    -- y.func a'' ∈ y and y =ᴮ x.func a' → y.func a'' ∈ x.func a'
                    exact le_trans (le_inf h4 h3) subst_congr_mem_right

-- src/bvm_extras.lean:2131
private lemma bot_of_mem_mem' (x y : bSet 𝔹) {Γ} (H : Γ ≤ x ∈ᴮ y) (H' : Γ ≤ y ∈ᴮ x) : Γ ≤ ⊥ := by
  have h : (⊤ : 𝔹) ≤ (x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥ := bot_of_mem_mem x y
  calc Γ ≤ ⊤ ⊓ (x ∈ᴮ y ⊓ y ∈ᴮ x) := le_inf le_top (le_inf H H')
    _ ≤ ⊥ := by rwa [← deduction] at h

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
private lemma check_succ_eq_succ_check {n : ℕ} {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] :
    (of_nat (n.succ) : bSet 𝔹) = succ (of_nat n) := by
  -- of_nat m = check (PSet.ofNat m), succ = insert1
  simp only [of_nat, succ]
  -- check (PSet.ofNat (n+1)) = check (PSet.succ_ord (PSet.ofNat n)) = check (PSet.insert ... ...)
  -- = insert1 (check (PSet.ofNat n)) (check (PSet.ofNat n))
  have h : PSet.ofNat n.succ = PSet.insert (PSet.ofNat n) (PSet.ofNat n) := by
    rw [Nat.succ_eq_add_one, PSet.ofNat_succ]; rfl
  conv_lhs => rw [h]
  exact check_insert (PSet.ofNat n) (PSet.ofNat n)

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
private lemma epsilon_dichotomy (x y z : bSet 𝔹) :
    epsilon_well_orders x ≤ y ∈ᴮ x ⟹ (z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)) := by
  unfold epsilon_well_orders
  rw [← deduction, ← deduction]
  -- Goal: epsilon_well_orders x ⊓ y ∈ x ⊓ z ∈ x ≤ y =ᴮ z ⊔ y ∈ z ⊔ z ∈ y
  have h1 : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
      y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
    have htri : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        epsilon_trichotomy x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hy_mem : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        y ∈ᴮ x := inf_le_left.trans inf_le_right
    have hz_mem : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        z ∈ᴮ x := inf_le_right
    have h_iinf_y : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        ⨅ z', z' ∈ᴮ x ⟹ (y =ᴮ z' ⊔ y ∈ᴮ z' ⊔ z' ∈ᴮ y) :=
      le_trans (le_inf (htri.trans (iInf_le _ y)) hy_mem) bv_imp_elim
    exact le_trans (le_inf (h_iinf_y.trans (iInf_le _ z)) hz_mem) bv_imp_elim
  exact h1

-- src/bvm_extras.lean:2420


-- src/bvm_extras.lean:2422
private lemma subset_of_mem_transitive {x w : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_transitive x)
    (H₂ : Γ ≤ w ∈ᴮ x) : Γ ≤ w ⊆ᴮ x :=
  le_trans (le_inf (le_trans H₁ (iInf_le _ w)) H₂) bv_imp_elim

-- src/bvm_extras.lean:2425


-- src/bvm_extras.lean:2428


-- src/bvm_extras.lean:2430
private lemma epsilon_trichotomy_of_Ord {x a b : bSet 𝔹} {Γ : 𝔹} (Ha_mem : Γ ≤ a ∈ᴮ x)
    (Hb_mem : Γ ≤ b ∈ᴮ x) (H_Ord : Γ ≤ Ord x) :
    Γ ≤ a =ᴮ b ⊔ a ∈ᴮ b ⊔ b ∈ᴮ a := by
  have h_tri : Γ ≤ epsilon_trichotomy x :=
    le_trans (le_trans H_Ord inf_le_left) inf_le_left
  have h1 : Γ ≤ ⨅ z, z ∈ᴮ x ⟹ (a =ᴮ z ⊔ a ∈ᴮ z ⊔ z ∈ᴮ a) :=
    le_trans (le_inf (le_trans h_tri (iInf_le _ a)) Ha_mem) bv_imp_elim
  exact le_trans (le_inf (le_trans h1 (iInf_le _ b)) Hb_mem) bv_imp_elim

-- src/bvm_extras.lean:2438

-- src/bvm_extras.lean:2475


-- src/bvm_extras.lean:2478


-- src/bvm_extras.lean:2481


-- src/bvm_extras.lean:2484


-- src/bvm_extras.lean:2486
private lemma is_transitive_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ is_transitive y := by
  induction y using bSet.rec' generalizing x with
  | _ y IH =>
    -- IH : ∀ a : y.type, ∀ x', Ord x' ⊓ y.func a ∈ x' ≤ is_transitive (y.func a)
    -- Goal: Ord x ⊓ y ∈ x ≤ is_transitive y = ⨅ w, w ∈ y ⟹ w ⊆ y
    apply le_iInf; intro w; rw [← deduction]
    -- Goal: Ord x ⊓ y ∈ x ⊓ w ∈ y ≤ w ⊆ y = ⨅ z, z ∈ w ⟹ z ∈ y
    rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
    -- Goal: Ord x ⊓ y ∈ x ⊓ w ∈ y ⊓ z ∈ w ≤ z ∈ y
    set ctx := Ord x ⊓ y ∈ᴮ x ⊓ w ∈ᴮ y ⊓ z ∈ᴮ w
    -- Extract relevant information
    have hOrd : ctx ≤ Ord x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hyx : ctx ≤ y ∈ᴮ x := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hwy : ctx ≤ w ∈ᴮ y := inf_le_left.trans inf_le_right
    have hzw : ctx ≤ z ∈ᴮ w := inf_le_right
    -- is_transitive x: y ⊆ x
    have hy_sub_x : ctx ≤ y ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd.trans inf_le_right) hyx
    -- w ∈ x
    have hwx : ctx ≤ w ∈ᴮ x :=
      mem_of_mem_subset hy_sub_x hwy
    -- is_transitive x: w ⊆ x
    have hw_sub_x : ctx ≤ w ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd.trans inf_le_right) hwx
    -- z ∈ x
    have hzx : ctx ≤ z ∈ᴮ x :=
      mem_of_mem_subset hw_sub_x hzw
    -- Apply epsilon_dichotomy x y z with ewo x from Ord x
    have h_tri : ctx ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
      have hewo : ctx ≤ epsilon_well_orders x := hOrd.trans inf_le_left
      have h_step1 : ctx ≤ z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y) :=
        le_trans (le_inf (hewo.trans (epsilon_dichotomy x y z)) hyx) bv_imp_elim
      exact le_trans (le_inf h_step1 hzx) bv_imp_elim
    -- Case analysis on the trichotomy using bv_or_elim_right
    -- h_tri : ctx ≤ y =ᴮ z ⊔ y ∈ z ⊔ z ∈ y
    calc ctx
        ≤ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y) ⊓ ctx := le_inf h_tri le_rfl
      _ ≤ z ∈ᴮ y := by
          apply bv_or_elim_left
          · -- (y =ᴮ z ⊔ y ∈ z) ⊓ ctx ≤ z ∈ y
            apply bv_or_elim_left
            · -- (y =ᴮ z) ⊓ ctx ≤ z ∈ y: get bot
              -- z ∈ w and y =ᴮ z → y ∈ w (rewrite); w ∈ y and y ∈ w → bot
              apply le_trans _ bot_le
              -- Goal: (y =ᴮ z) ⊓ ctx ≤ ⊥
              have h_yw : (y =ᴮ z) ⊓ ctx ≤ y ∈ᴮ w :=
                bv_rw' (H := inf_le_left) (ϕ := fun v => v ∈ᴮ w) (h_congr := B_ext_mem_left)
                  (H_new := le_trans inf_le_right hzw)
              exact bot_of_mem_mem' y w h_yw (inf_le_right.trans hwy)
            · -- (y ∈ z) ⊓ ctx ≤ z ∈ y: get bot
              -- y ∈ z, z ∈ w, w ∈ y → derive bot using induction
              apply le_trans _ bot_le
              -- From w ∈ y: get index i_w
              have hwmem_iSup : (y ∈ᴮ z) ⊓ ctx ≤ ⨆ i : y.type, y.bval i ⊓ w =ᴮ y.func i := by
                calc (y ∈ᴮ z) ⊓ ctx ≤ w ∈ᴮ y := inf_le_right.trans hwy
                  _ = ⨆ i : y.type, y.bval i ⊓ w =ᴮ y.func i := mem_unfold
              calc (y ∈ᴮ z) ⊓ ctx
                  ≤ (⨆ i : y.type, y.bval i ⊓ w =ᴮ y.func i) ⊓ ((y ∈ᴮ z) ⊓ ctx) :=
                    le_inf hwmem_iSup le_rfl
                _ ≤ ⨆ i, (y.bval i ⊓ w =ᴮ y.func i) ⊓ ((y ∈ᴮ z) ⊓ ctx) :=
                    (iSup_inf_eq _ _).le
                _ ≤ ⊥ := by
                    apply iSup_le; intro i_w
                    set ctx2 := (y.bval i_w ⊓ w =ᴮ y.func i_w) ⊓ ((y ∈ᴮ z) ⊓ ctx)
                    have hw_eq : ctx2 ≤ w =ᴮ y.func i_w := inf_le_left.trans inf_le_right
                    have h_hyz : ctx2 ≤ y ∈ᴮ z := inf_le_right.trans inf_le_left
                    -- y.func i_w ∈ x from w ∈ x rewritten
                    have hyf_x : ctx2 ≤ y.func i_w ∈ᴮ x :=
                      bv_rw' (H := bv_symm hw_eq) (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
                        (H_new := le_trans inf_le_right (inf_le_right.trans hwx))
                    -- Apply IH i_w x
                    have h_ihiw : ctx2 ≤ is_transitive (y.func i_w) :=
                      le_trans (le_inf (le_trans inf_le_right (inf_le_right.trans hOrd)) hyf_x) (IH i_w x)
                    -- is_transitive (y.func i_w): z ∈ y.func i_w → z ⊆ y.func i_w
                    have h_z_in_yfi : ctx2 ≤ z ∈ᴮ y.func i_w :=
                      bv_rw' (H := bv_symm hw_eq) (ϕ := fun v => z ∈ᴮ v) (h_congr := B_ext_mem_right)
                        (H_new := le_trans inf_le_right (inf_le_right.trans hzw))
                    have h_ztrans : ctx2 ≤ z ⊆ᴮ y.func i_w :=
                      subset_of_mem_transitive h_ihiw h_z_in_yfi
                    -- y ∈ z and z ⊆ y.func i_w → y ∈ y.func i_w = y ∈ w
                    have h_y_yfi : ctx2 ≤ y ∈ᴮ y.func i_w :=
                      mem_of_mem_subset h_ztrans h_hyz
                    have h_yw : ctx2 ≤ y ∈ᴮ w :=
                      bv_rw' (H := hw_eq) (ϕ := fun v => y ∈ᴮ v) (h_congr := B_ext_mem_right)
                        (H_new := h_y_yfi)
                    -- y ∈ w ∧ w ∈ y → bot
                    exact bot_of_mem_mem' y w h_yw (le_trans inf_le_right (inf_le_right.trans hwy))
          · -- (z ∈ y) ⊓ ctx ≤ z ∈ y
            exact inf_le_left

-- src/bvm_extras.lean:2520
private lemma is_ewo_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ epsilon_well_orders y := by
  -- epsilon_well_orders y = epsilon_trichotomy y ⊓ epsilon_well_founded y
  apply le_inf
  · -- epsilon_trichotomy y = ⨅ w, w ∈ y ⟹ ⨅ z, z ∈ y ⟹ (w =ᴮ z ⊔ w ∈ z ⊔ z ∈ y)
    apply le_iInf; intro w; rw [← deduction]
    apply le_iInf; intro z; rw [← deduction]
    -- Goal: Ord x ⊓ y ∈ x ⊓ w ∈ y ⊓ z ∈ y ≤ w =ᴮ z ⊔ w ∈ z ⊔ z ∈ y
    set ctx := Ord x ⊓ y ∈ᴮ x ⊓ w ∈ᴮ y ⊓ z ∈ᴮ y
    have hOrd : ctx ≤ Ord x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hyx : ctx ≤ y ∈ᴮ x := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hwy : ctx ≤ w ∈ᴮ y := inf_le_left.trans inf_le_right
    have hzy : ctx ≤ z ∈ᴮ y := inf_le_right
    -- y ⊆ x (from Ord x ⊃ is_transitive x and y ∈ x)
    have hy_sub_x : ctx ≤ y ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd.trans inf_le_right) hyx
    -- w ∈ x, z ∈ x
    have hwx : ctx ≤ w ∈ᴮ x := mem_of_mem_subset hy_sub_x hwy
    have hzx : ctx ≤ z ∈ᴮ x := mem_of_mem_subset hy_sub_x hzy
    -- epsilon_trichotomy x applied to w, z in x
    have hewo : ctx ≤ epsilon_well_orders x := hOrd.trans inf_le_left
    have htri : ctx ≤ epsilon_trichotomy x := hewo.trans inf_le_left
    have h_step0 : ctx ≤ ⨅ z', z' ∈ᴮ x ⟹ (w =ᴮ z' ⊔ w ∈ᴮ z' ⊔ z' ∈ᴮ w) :=
      le_trans (le_inf (htri.trans (iInf_le _ w)) hwx) bv_imp_elim
    exact le_trans (le_inf (h_step0.trans (iInf_le _ z)) hzx) bv_imp_elim
  · -- epsilon_well_founded y = ⨅ u, u ⊆ y ⟹ (uᶜ =ᴮ ∅ ⟹ ⨆ v, v ∈ u ⊓ ⨅ z', z' ∈ u ⟹ (z' ∈ v)ᶜ)
    -- Use epsilon_well_founded x applied to u: need u ⊆ x
    -- u ⊆ y ⊆ x → u ⊆ x
    apply le_iInf; intro u
    rw [← deduction, ← deduction]
    -- Goal: Ord x ⊓ y ∈ x ⊓ u ⊆ y ⊓ (u =ᴮ ∅)ᶜ ≤ ⨆ v, v ∈ u ⊓ ⨅ z', z' ∈ u ⟹ (z' ∈ v)ᶜ
    set ctx2 := Ord x ⊓ y ∈ᴮ x ⊓ u ⊆ᴮ y ⊓ (u =ᴮ ∅)ᶜ
    have hOrd2 : ctx2 ≤ Ord x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hyx2 : ctx2 ≤ y ∈ᴮ x := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have huby : ctx2 ≤ u ⊆ᴮ y := inf_le_left.trans inf_le_right
    have hne : ctx2 ≤ (u =ᴮ ∅)ᶜ := inf_le_right
    -- y ⊆ x
    have hy_sub_x2 : ctx2 ≤ y ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd2.trans inf_le_right) hyx2
    -- u ⊆ y ⊆ x → u ⊆ x
    have hubx : ctx2 ≤ u ⊆ᴮ x := subset_trans' huby hy_sub_x2
    -- epsilon_well_founded x: u ⊆ x ∧ u ≠ ∅ → ⨆ v, v ∈ u ⊓ ⨅ z', z' ∈ u ⟹ (z' ∈ v)ᶜ
    have hewo2 : ctx2 ≤ epsilon_well_orders x := hOrd2.trans inf_le_left
    have hwf2 : ctx2 ≤ epsilon_well_founded x := hewo2.trans inf_le_right
    have hwf3 : ctx2 ≤ u ⊆ᴮ x ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ v, v ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ v)ᶜ)) :=
      hwf2.trans (iInf_le _ u)
    have hwf4 : ctx2 ≤ (u =ᴮ ∅)ᶜ ⟹ ⨆ v, v ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ v)ᶜ) :=
      le_trans (le_inf hwf3 hubx) bv_imp_elim
    exact le_trans (le_inf hwf4 hne) bv_imp_elim

-- src/bvm_extras.lean:2551
private theorem Ord_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) :
    Γ ≤ Ord x :=
  le_inf
    (le_trans (le_inf H_Ord H_mem) (is_ewo_of_mem_Ord x y))
    (le_trans (le_inf H_Ord H_mem) (is_transitive_of_mem_Ord x y))

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
private lemma Ord_omega {Γ : 𝔹} : Γ ≤ Ord (omega : bSet 𝔹) :=
  le_inf (check_ewo PSet.is_ewo_omega) (check_is_transitive PSet.is_transitive_omega)

-- src/bvm_extras.lean:2717
private lemma Ord_of_nat {Γ : 𝔹} {n : ℕ} : Γ ≤ Ord (of_nat n) :=
  Ord_of_mem_Ord of_nat_mem_omega Ord_omega

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

/- Source module: Definitions.Flypitch4.BvmExtras2 -/
section CohenSource_BvmExtras2
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/bvm_extras2.lean



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch
open Lattice

universe u

namespace bSet

-- ============================================================
-- src/bvm_extras2.lean:17-35: section lemmas
-- ============================================================

section lemmas
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:20


-- src/bvm_extras2.lean:29


-- src/bvm_extras2.lean:32


end lemmas

-- ============================================================
-- src/bvm_extras2.lean:37-62: section inj_inverse_surj
-- ============================================================

section inj_inverse_surj
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {x y f : bSet 𝔹} {Γ : 𝔹}
  (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)

-- src/bvm_extras2.lean:41


-- src/bvm_extras2.lean:48


-- src/bvm_extras2.lean:55


end inj_inverse_surj

-- ============================================================
-- src/bvm_extras2.lean:64-345: section Ord
-- ============================================================

section Ord
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:67
private lemma subset_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y :=
  subset_of_mem_transitive (H_Ord.trans inf_le_right) H_mem

-- src/bvm_extras2.lean:70
private lemma mem_of_mem_Ord {x y z : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_mem' : Γ ≤ y ∈ᴮ z)
    (H_ord₂ : Γ ≤ Ord z) : Γ ≤ x ∈ᴮ z :=
  mem_of_mem_subset (subset_of_mem_Ord H_mem' H_ord₂) H_mem

-- src/bvm_extras2.lean:78


-- src/bvm_extras2.lean:88
private lemma transitive_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ is_transitive (x ∩ᴮ y) := by
  unfold is_transitive
  apply le_iInf; intro z; rw [← deduction]
  set ctx := Γ ⊓ z ∈ᴮ x ∩ᴮ y
  have hmem : ctx ≤ z ∈ᴮ x ∩ᴮ y := inf_le_right
  have Hz_x : ctx ≤ z ∈ᴮ x := (mem_binary_inter_iff.mp hmem).1
  have Hz_y : ctx ≤ z ∈ᴮ y := (mem_binary_inter_iff.mp hmem).2
  rw [subset_unfold']
  apply le_iInf; intro w; rw [← deduction]
  apply mem_binary_inter_iff.mpr
  constructor
  · have Hx_trans : ctx ≤ is_transitive x := inf_le_left.trans (H₁.trans inf_le_right)
    have hsub : ctx ≤ z ⊆ᴮ x :=
      le_trans (le_inf (Hx_trans.trans (iInf_le _ z)) Hz_x) bv_imp_elim
    rw [subset_unfold'] at hsub
    exact le_trans (le_inf (inf_le_left.trans (hsub.trans (iInf_le _ w))) inf_le_right)
      bv_imp_elim
  · have Hy_trans : ctx ≤ is_transitive y := inf_le_left.trans (H₂.trans inf_le_right)
    have hsub : ctx ≤ z ⊆ᴮ y :=
      le_trans (le_inf (Hy_trans.trans (iInf_le _ z)) Hz_y) bv_imp_elim
    rw [subset_unfold'] at hsub
    exact le_trans (le_inf (inf_le_left.trans (hsub.trans (iInf_le _ w))) inf_le_right)
      bv_imp_elim

-- src/bvm_extras2.lean:96
private lemma epsilon_trichotomy_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) :
    Γ ≤ epsilon_trichotomy (x ∩ᴮ y) := by
  unfold epsilon_trichotomy
  apply le_iInf; intro w; rw [← deduction]
  apply le_iInf; intro z; rw [← deduction]
  set ctx := Γ ⊓ w ∈ᴮ x ∩ᴮ y ⊓ z ∈ᴮ x ∩ᴮ y
  have hw_inter : ctx ≤ w ∈ᴮ x ∩ᴮ y := inf_le_left.trans inf_le_right
  have hz_inter : ctx ≤ z ∈ᴮ x ∩ᴮ y := inf_le_right
  have Hw_x : ctx ≤ w ∈ᴮ x := (mem_binary_inter_iff.mp hw_inter).1
  have Hz_x : ctx ≤ z ∈ᴮ x := (mem_binary_inter_iff.mp hz_inter).1
  exact epsilon_trichotomy_of_Ord Hw_x Hz_x (inf_le_left.trans (inf_le_left.trans H₁))

-- src/bvm_extras2.lean:104
private lemma epsilon_well_founded_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) :
    Γ ≤ epsilon_well_founded (x ∩ᴮ y) := by
  rw [epsilon_well_founded]
  apply le_iInf; intro w; rw [← deduction, ← deduction]
  -- ctx = Γ ⊓ w ⊆ᴮ (x ∩ᴮ y) ⊓ (w =ᴮ ∅)ᶜ
  -- epsilon_well_founded x = ⨅ u, u ⊆ x ⟹ ((u = ∅)ᶜ ⟹ ⨆ v, ...)
  -- Apply at w with w ⊆ x (via w ⊆ x ∩ y ⊆ x) and w ≠ ∅
  set ctx := Γ ⊓ w ⊆ᴮ x ∩ᴮ y ⊓ (w =ᴮ ∅)ᶜ
  have Hw_sub_x : ctx ≤ w ⊆ᴮ x :=
    subset_trans' (inf_le_left.trans inf_le_right) binary_inter_subset_left
  have Hw_ne : ctx ≤ (w =ᴮ ∅)ᶜ := inf_le_right
  -- epsilon_well_founded x at w
  have Hewf : ctx ≤ epsilon_well_founded x :=
    inf_le_left.trans (inf_le_left.trans
      (le_trans H₁ (inf_le_left.trans inf_le_right)))
  -- epsilon_well_founded x = ⨅ u, u ⊆ x ⟹ ((u = ∅)ᶜ ⟹ ⨆ y, ...)
  have Hewf_w : ctx ≤ w ⊆ᴮ x ⟹ ((w =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ w ⊓ (⨅ z', z' ∈ᴮ w ⟹ (z' ∈ᴮ y)ᶜ)) :=
    le_trans Hewf (iInf_le _ w)
  have h1 : ctx ≤ (w =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ w ⊓ (⨅ z', z' ∈ᴮ w ⟹ (z' ∈ᴮ y)ᶜ) :=
    le_trans (le_inf Hewf_w Hw_sub_x) bv_imp_elim
  exact le_trans (le_inf h1 Hw_ne) bv_imp_elim

-- src/bvm_extras2.lean:112
private lemma Ord_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ Ord (binary_inter x y) := by
  unfold Ord epsilon_well_orders
  apply le_inf
  · apply le_inf
    · exact epsilon_trichotomy_binary_inter H₁
    · exact epsilon_well_founded_binary_inter H₁
  · exact transitive_binary_inter H₁ H₂

-- ============================================================
-- src/bvm_extras2.lean:122-158: section compl
-- ============================================================

section compl



-- src/bvm_extras2.lean:126


-- src/bvm_extras2.lean:129
private lemma mem_compl_iff {x y : bSet 𝔹} {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ compl x y ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ (z ∈ᴮ y)ᶜ) := by
  unfold compl
  have H_congr : ∀ a b : bSet 𝔹, a =ᴮ b ⊓ (a ∈ᴮ y)ᶜ ≤ (b ∈ᴮ y)ᶜ := by
    intro a b
    simp only [← imp_bot]; rw [← deduction]
    have h_ba : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ b =ᴮ a := by
      rw [bv_eq_symm]; exact inf_le_left.trans inf_le_left
    have h_by : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ b ∈ᴮ y := inf_le_right
    have h_ay : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ a ∈ᴮ y :=
      bv_rw'' h_ba h_by B_ext_mem_left
    have h_nay : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ a ∈ᴮ y ⟹ ⊥ :=
      inf_le_left.trans inf_le_right
    exact le_trans (le_inf h_nay h_ay) bv_imp_elim
  rw [mem_comprehend_iff₂ _ _ H_congr]
  constructor
  · intro H
    obtain ⟨w, Hw⟩ := exists_convert H (B_ext_inf B_ext_mem_left
      (B_ext_inf B_ext_bv_eq_right (B_ext_neg (h := B_ext_mem_left))))
    have Hw_mem : Γ ≤ w ∈ᴮ x := Hw.trans inf_le_left
    have Hw_eq : Γ ≤ z =ᴮ w := Hw.trans (inf_le_right.trans inf_le_left)
    have Hw_nmem : Γ ≤ (w ∈ᴮ y)ᶜ := Hw.trans (inf_le_right.trans inf_le_right)
    constructor
    · exact bv_rw'' (bv_symm Hw_eq) Hw_mem B_ext_mem_left
    · simp only [← imp_bot] at Hw_nmem ⊢; rw [← deduction] at Hw_nmem ⊢
      have : Γ ⊓ z ∈ᴮ y ≤ w ∈ᴮ y :=
        bv_rw'' (inf_le_left.trans Hw_eq) inf_le_right B_ext_mem_left
      exact le_trans (le_inf inf_le_left this) Hw_nmem
  · intro ⟨H_mem, H_nmem⟩
    apply le_iSup_of_le z
    exact le_inf H_mem (le_inf bv_refl H_nmem)

end compl

-- src/bvm_extras2.lean:141
private lemma compl_empty_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H_sub : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ compl x y =ᴮ ∅ := by
  apply mem_ext
  · apply le_iInf; intro w; rw [← deduction]
    have hmem : Γ ⊓ w ∈ᴮ compl x y ≤ w ∈ᴮ compl x y := inf_le_right
    have ⟨Hw_x, Hw_ny⟩ := mem_compl_iff.mp hmem
    have Hw_y : Γ ⊓ w ∈ᴮ compl x y ≤ w ∈ᴮ y :=
      mem_of_mem_subset (inf_le_left.trans H_sub) Hw_x
    exact bv_exfalso (bv_absurd (w ∈ᴮ y) Hw_y Hw_ny)
  · apply le_iInf; intro w; rw [← deduction]
    exact bv_exfalso (bot_of_mem_empty inf_le_right)

-- src/bvm_extras2.lean:149
private lemma nonempty_compl_of_ne {x y : bSet 𝔹} {Γ : 𝔹} (H_ne : Γ ≤ (x =ᴮ y)ᶜ) :
    Γ ≤ ((compl x y =ᴮ ∅)ᶜ) ⊔ ((compl y x =ᴮ ∅)ᶜ) := by
  -- x ≠ y means (x ⊆ y ⊓ y ⊆ x)ᶜ = (x ⊆ y)ᶜ ⊔ (y ⊆ x)ᶜ
  rw [eq_iff_subset_subset, compl_inf] at H_ne
  -- Helper: compl a b = ∅ and z ∈ a and z ∉ b → ⊥ (contradiction)
  -- Actually: show each disjunct using bv_or_elim_left
  -- For (x ⊆ y)ᶜ case: derive (compl x y = ∅)ᶜ
  -- For (y ⊆ x)ᶜ case: derive (compl y x = ∅)ᶜ
  -- Use: if (compl x y = ∅) then x ⊆ y [the contrapositive of compl_empty_of_subset]
  -- Prove: compl_full_empty : Γ ≤ compl x y =ᴮ ∅ → Γ ≤ x ⊆ y
  -- Proof: for z ∈ x, if z ∉ y then z ∈ compl x y = ∅, contradiction
  -- So the two branches are:
  -- Branch 1: (x ⊆ y)ᶜ ⊓ Γ: if compl x y = ∅ → x ⊆ y, but (x ⊆ y)ᶜ = contradiction
  -- Branch 2: symmetric
  have compl_empty_imp_sub : ∀ (a b : bSet 𝔹) (Γ' : 𝔹),
      Γ' ≤ compl a b =ᴮ ∅ → Γ' ≤ a ⊆ᴮ b := by
    intro a b Γ' H
    rw [subset_unfold']
    apply le_iInf; intro z; rw [← deduction]
    -- z ∈ a → z ∈ b; prove: ctx' ⊓ (z ∈ b)ᶜ = ⊥
    set ctx' := Γ' ⊓ z ∈ᴮ a
    rw [← disjoint_compl_right_iff, disjoint_iff]
    apply le_antisymm _ bot_le
    have h1 : ctx' ⊓ (z ∈ᴮ b)ᶜ ≤ z ∈ᴮ compl a b :=
      mem_compl_iff.mpr ⟨inf_le_left.trans inf_le_right, inf_le_right⟩
    have h2 : ctx' ⊓ (z ∈ᴮ b)ᶜ ≤ compl a b =ᴮ ∅ := inf_le_left.trans (inf_le_left.trans H)
    exact bv_exfalso (bot_of_mem_empty (bv_rw'' h2 h1 B_ext_mem_right))
  -- Now case split on H_ne : (x ⊆ y)ᶜ ⊔ (y ⊆ x)ᶜ
  have h_left : (x ⊆ᴮ y)ᶜ ⊓ Γ ≤ (compl x y =ᴮ ∅)ᶜ ⊔ (compl y x =ᴮ ∅)ᶜ := by
    apply bv_or_left
    -- need: (x ⊆ y)ᶜ ⊓ Γ ≤ (compl x y = ∅)ᶜ
    conv_rhs => rw [← imp_bot]
    rw [← deduction]
    -- goal: (x ⊆ y)ᶜ ⊓ Γ ⊓ compl x y =ᴮ ∅ ≤ ⊥
    have hce : (x ⊆ᴮ y)ᶜ ⊓ Γ ⊓ compl x y =ᴮ ∅ ≤ compl x y =ᴮ ∅ := inf_le_right
    have hsub := compl_empty_imp_sub x y _ hce
    have hn : (x ⊆ᴮ y)ᶜ ⊓ Γ ⊓ compl x y =ᴮ ∅ ≤ (x ⊆ᴮ y)ᶜ := inf_le_left.trans inf_le_left
    exact bv_absurd (x ⊆ᴮ y) hsub hn
  have h_right : (y ⊆ᴮ x)ᶜ ⊓ Γ ≤ (compl x y =ᴮ ∅)ᶜ ⊔ (compl y x =ᴮ ∅)ᶜ := by
    apply bv_or_right
    conv_rhs => rw [← imp_bot]
    rw [← deduction]
    have hce : (y ⊆ᴮ x)ᶜ ⊓ Γ ⊓ compl y x =ᴮ ∅ ≤ compl y x =ᴮ ∅ := inf_le_right
    have hsub := compl_empty_imp_sub y x _ hce
    have hn : (y ⊆ᴮ x)ᶜ ⊓ Γ ⊓ compl y x =ᴮ ∅ ≤ (y ⊆ᴮ x)ᶜ := inf_le_left.trans inf_le_left
    exact bv_absurd (y ⊆ᴮ x) hsub hn
  exact le_trans (le_inf H_ne le_rfl) (bv_or_elim_left h_left h_right)
-- src/bvm_extras2.lean:173
private lemma Ord.lt_of_ne_and_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H_ne : Γ ≤ (x =ᴮ y)ᶜ) (H_le : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ∈ᴮ y := by
  -- Step 1: compl y x ≠ ∅ (since x ≠ y, one of compl x y or compl y x is nonempty;
  --   compl x y = ∅ since x ⊆ y; so compl y x ≠ ∅)
  have H_cxy := compl_empty_of_subset H_le
  have H_compl_ne : Γ ≤ (compl y x =ᴮ ∅)ᶜ := by
    have H_both := nonempty_compl_of_ne H_ne
    have h1 : (compl x y =ᴮ ∅)ᶜ ⊓ Γ ≤ (compl y x =ᴮ ∅)ᶜ :=
      bv_exfalso (bv_absurd _ (inf_le_right.trans H_cxy) inf_le_left)
    have h2 : (compl y x =ᴮ ∅)ᶜ ⊓ Γ ≤ (compl y x =ᴮ ∅)ᶜ := inf_le_left
    exact le_trans (le_inf H_both le_rfl) (bv_or_elim_left h1 h2)
  -- Step 2: get minimal element u of compl y x by regularity
  have H_reg := bSet_axiom_of_regularity (compl y x) H_compl_ne
  -- B_ext for ϕ u = u ∈ compl y x ⊓ ⨅ z', z' ∈ compl y x ⟹ (z' ∈ u)ᶜ
  have H_Bext : B_ext (fun u : bSet 𝔹 =>
      u ∈ᴮ compl y x ⊓ (⨅ z', z' ∈ᴮ compl y x ⟹ (z' ∈ᴮ u)ᶜ)) := by
    apply B_ext_inf B_ext_mem_left
    apply B_ext_iInf; intro z'
    simp only [← imp_bot]
    exact B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))
  obtain ⟨u, Hu⟩ := exists_convert H_reg H_Bext
  -- Hu : Γ ≤ u ∈ compl y x ⊓ ⨅ z', z' ∈ compl y x ⟹ (z' ∈ u)ᶜ
  have Hu_mem : Γ ≤ u ∈ᴮ compl y x := Hu.trans inf_le_left
  have Hu_min : Γ ≤ ⨅ z', z' ∈ᴮ compl y x ⟹ (z' ∈ᴮ u)ᶜ := Hu.trans inf_le_right
  -- From u ∈ compl y x: u ∈ y and u ∉ x
  have ⟨Hu_y, Hu_nx⟩ := mem_compl_iff.mp Hu_mem
  -- Step 3: show x = u (hence x ∈ y via bv_rw)
  -- Prove x ⊆ u
  have Hx_sub_u : Γ ≤ x ⊆ᴮ u := by
    rw [subset_unfold']
    apply le_iInf; intro a; rw [← deduction]
    set ctx := Γ ⊓ a ∈ᴮ x
    have Ha_x : ctx ≤ a ∈ᴮ x := inf_le_right
    have Ha_y : ctx ≤ a ∈ᴮ y := mem_of_mem_subset (inf_le_left.trans H_le) Ha_x
    -- trichotomy on a,u ∈ y under Ord y
    have H_tri := epsilon_trichotomy_of_Ord Ha_y (inf_le_left.trans Hu_y)
                    (inf_le_left.trans H₂)
    -- H_tri : ctx ≤ a = u ⊔ a ∈ u ⊔ u ∈ a
    -- Case a = u: u ∈ x, contradiction with Hu_nx
    have hcase1 : (a =ᴮ u) ⊓ ctx ≤ a ∈ᴮ u := by
      have heq : (a =ᴮ u) ⊓ ctx ≤ a =ᴮ u := inf_le_left
      have ha_x : (a =ᴮ u) ⊓ ctx ≤ a ∈ᴮ x := inf_le_right.trans Ha_x
      -- a = u and a ∈ x → u ∈ x, contradicts Hu_nx
      have hu_x : (a =ᴮ u) ⊓ ctx ≤ u ∈ᴮ x :=
        bv_rw'' heq ha_x B_ext_mem_left
      exact bv_exfalso (bv_absurd (u ∈ᴮ x) hu_x (inf_le_right.trans (inf_le_left.trans Hu_nx)))
    -- Case a ∈ u: done
    have hcase2 : (a ∈ᴮ u) ⊓ ctx ≤ a ∈ᴮ u := inf_le_left
    -- Case u ∈ a: u ∈ a ∈ x → u ∈ x (by Ord x transitivity), contradiction
    have hcase3 : (u ∈ᴮ a) ⊓ ctx ≤ a ∈ᴮ u := by
      have Hua : (u ∈ᴮ a) ⊓ ctx ≤ u ∈ᴮ a := inf_le_left
      have ha_x2 : (u ∈ᴮ a) ⊓ ctx ≤ a ∈ᴮ x := inf_le_right.trans Ha_x
      -- u ∈ a ∈ x → u ∈ x by Ord x transitivity
      have hu_x : (u ∈ᴮ a) ⊓ ctx ≤ u ∈ᴮ x :=
        mem_of_mem_Ord Hua ha_x2 (inf_le_right.trans (inf_le_left.trans H₁))
      exact bv_exfalso (bv_absurd (u ∈ᴮ x) hu_x (inf_le_right.trans (inf_le_left.trans Hu_nx)))
    -- Combine trichotomy: (a=u ⊔ a∈u ⊔ u∈a) ⊓ ctx ≤ a∈u
    have h12 : (a =ᴮ u ⊔ a ∈ᴮ u) ⊓ ctx ≤ a ∈ᴮ u := bv_or_elim_left hcase1 hcase2
    have hfinal := bv_or_elim_left h12 hcase3
    -- hfinal : ((a =ᴮ u ⊔ a ∈ᴮ u) ⊔ u ∈ᴮ a) ⊓ ctx ≤ a ∈ᴮ u
    exact le_trans (le_inf H_tri le_rfl) hfinal
  -- Prove u ⊆ x
  have Hu_sub_x : Γ ≤ u ⊆ᴮ x := by
    rw [subset_unfold']
    apply le_iInf; intro a; rw [← deduction]
    set ctx := Γ ⊓ a ∈ᴮ u
    have Ha_u : ctx ≤ a ∈ᴮ u := inf_le_right
    -- By contradiction: assume a ∉ x
    -- Convert ctx ≤ a ∈ x to: ctx ⊓ (a ∈ x)ᶜ ≤ ⊥
    rw [← disjoint_compl_right_iff, disjoint_iff]
    apply le_antisymm _ bot_le
    -- goal: ctx ⊓ (a ∈ x)ᶜ ≤ ⊥
    -- From a ∈ u ∈ y → a ∈ y; and a ∉ x → a ∈ compl y x
    -- Minimality of u: z' ∈ compl y x → z' ∉ u; contradiction with a ∈ u
    have Ha_y : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ y := by
      have hu_y : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ u ∈ᴮ y := inf_le_left.trans (inf_le_left.trans Hu_y)
      have ha_u : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ u := inf_le_left.trans Ha_u
      exact mem_of_mem_Ord ha_u hu_y (inf_le_left.trans (inf_le_left.trans H₂))
    have Ha_compl : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ compl y x :=
      mem_compl_iff.mpr ⟨Ha_y, inf_le_right⟩
    -- Minimality gives a ∉ u
    have Ha_nu : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ (a ∈ᴮ u)ᶜ := by
      -- ctx ⊓ (a ∈ x)ᶜ ≤ ctx ≤ Γ ≤ Hu_min
      have h1 : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ ctx := inf_le_left
      have h2 : ctx ≤ ⨅ z', z' ∈ᴮ compl y x ⟹ (z' ∈ᴮ u)ᶜ :=
        inf_le_left.trans Hu_min
      have h3 : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ compl y x ⟹ (a ∈ᴮ u)ᶜ :=
        (h1.trans h2).trans (iInf_le _ a)
      exact le_trans (le_inf h3 Ha_compl) bv_imp_elim
    exact bv_absurd (a ∈ᴮ u) (inf_le_left.trans Ha_u) Ha_nu
  -- Step 4: x = u, so x ∈ y (since u ∈ y)
  have H_eq : Γ ≤ x =ᴮ u := by
    rw [eq_iff_subset_subset]
    exact le_inf Hx_sub_u Hu_sub_x
  exact bv_rw'' (bv_symm H_eq) Hu_y B_ext_mem_left

-- src/bvm_extras2.lean:201
private lemma Ord.le_or_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
  -- Let w = x ∩ y. If w ≠ x and w ≠ y, then w ∈ x and w ∈ y → w ∈ w (foundation).
  -- So w = x or w = y, giving x ⊆ y or y ⊆ x.
  set w := x ∩ᴮ y
  have w_Ord : Γ ≤ Ord w := Ord_binary_inter H₁ H₂
  -- Show: w = x ⊔ w = y
  have hdiag : Γ ≤ w =ᴮ x ⊔ w =ᴮ y := by
    -- by contradiction: ¬(w = x ⊔ w = y) leads to w ∈ w
    rw [← disjoint_compl_right_iff, disjoint_iff]
    apply le_antisymm _ bot_le
    -- goal: Γ ⊓ (w =ᴮ x ⊔ w =ᴮ y)ᶜ ≤ ⊥
    set ctx := Γ ⊓ (w =ᴮ x ⊔ w =ᴮ y)ᶜ
    -- ¬(w=x): w=x ≤ w=x ⊔ w=y, so (w=x ⊔ w=y)ᶜ ≤ (w=x)ᶜ
    have hne_x : ctx ≤ (w =ᴮ x)ᶜ := inf_le_right.trans (compl_le_compl le_sup_left)
    -- ¬(w=y): w=y ≤ w=x ⊔ w=y, so (w=x ⊔ w=y)ᶜ ≤ (w=y)ᶜ
    have hne_y : ctx ≤ (w =ᴮ y)ᶜ := inf_le_right.trans (compl_le_compl le_sup_right)
    -- From ¬(w = x) and w ⊆ x: w ∈ x
    have hw_x : ctx ≤ w ∈ᴮ x :=
      Ord.lt_of_ne_and_le (inf_le_left.trans w_Ord) (inf_le_left.trans H₁)
        hne_x (inf_le_left.trans binary_inter_subset_left)
    -- From ¬(w = y) and w ⊆ y: w ∈ y
    have hw_y : ctx ≤ w ∈ᴮ y :=
      Ord.lt_of_ne_and_le (inf_le_left.trans w_Ord) (inf_le_left.trans H₂)
        hne_y (inf_le_left.trans binary_inter_subset_right)
    -- w ∈ x ∩ y = w → w ∈ w, contradiction
    exact bot_of_mem_self' (mem_binary_inter_iff.mpr ⟨hw_x, hw_y⟩)
  -- Case split on hdiag
  have h1 : w =ᴮ x ⊓ Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
    apply bv_or_left
    -- w = x, so w ⊆ y gives x ⊆ y
    have hw_sub : w =ᴮ x ⊓ Γ ≤ w ⊆ᴮ y := inf_le_right.trans binary_inter_subset_right
    exact bv_rw'' (ϕ := fun v => v ⊆ᴮ y) inf_le_left hw_sub B_ext_subset_left
  have h2 : w =ᴮ y ⊓ Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
    apply bv_or_right
    -- w = y, so w ⊆ x gives y ⊆ x
    have hw_sub : w =ᴮ y ⊓ Γ ≤ w ⊆ᴮ x := inf_le_right.trans binary_inter_subset_left
    exact bv_rw'' (ϕ := fun v => v ⊆ᴮ x) inf_le_left hw_sub B_ext_subset_left
  exact le_trans (le_inf hdiag le_rfl) (bv_or_elim_left h1 h2)

-- src/bvm_extras2.lean:220
private lemma Ord.trichotomy {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
  have h_lor := Ord.le_or_le H₁ H₂
  -- helper: case split on (x=y)
  have hL : (x ⊆ᴮ y) ⊓ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
    set ctx := x ⊆ᴮ y ⊓ Γ
    have h_eq : (x =ᴮ y) ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
      le_sup_of_le_left (le_sup_of_le_left inf_le_left)
    have h_ne : (x =ᴮ y)ᶜ ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
      le_sup_of_le_left (le_sup_of_le_right
        (Ord.lt_of_ne_and_le (inf_le_right.trans (inf_le_right.trans H₁))
          (inf_le_right.trans (inf_le_right.trans H₂))
          inf_le_left (inf_le_right.trans inf_le_left)))
    calc ctx = (x =ᴮ y ⊔ (x =ᴮ y)ᶜ) ⊓ ctx := by rw [sup_compl_eq_top, top_inf_eq]
         _ = (x =ᴮ y) ⊓ ctx ⊔ (x =ᴮ y)ᶜ ⊓ ctx := by rw [inf_sup_right]
         _ ≤ _ := sup_le h_eq h_ne
  have hR : (y ⊆ᴮ x) ⊓ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
    set ctx := y ⊆ᴮ x ⊓ Γ
    have h_eq : (x =ᴮ y) ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
      le_sup_of_le_left (le_sup_of_le_left inf_le_left)
    have h_ne : (x =ᴮ y)ᶜ ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
      -- ¬(x=y) ↔ ¬(y=x) (bv_eq_symm), and y ⊆ x with ¬(y=x) gives y ∈ x
      apply le_sup_of_le_right
      have hne_yx : (x =ᴮ y)ᶜ ⊓ ctx ≤ (y =ᴮ x)ᶜ := by
        -- if y = x then x = y (bv_symm), contradicting (x=y)ᶜ
        conv_rhs => rw [← imp_bot]
        rw [← deduction]
        exact bv_absurd (x =ᴮ y) (bv_symm inf_le_right) (inf_le_left.trans inf_le_left)
      exact Ord.lt_of_ne_and_le (inf_le_right.trans (inf_le_right.trans H₂))
        (inf_le_right.trans (inf_le_right.trans H₁))
        hne_yx (inf_le_right.trans inf_le_left)
    calc ctx = (x =ᴮ y ⊔ (x =ᴮ y)ᶜ) ⊓ ctx := by rw [sup_compl_eq_top, top_inf_eq]
         _ = (x =ᴮ y) ⊓ ctx ⊔ (x =ᴮ y)ᶜ ⊓ ctx := by rw [inf_sup_right]
         _ ≤ _ := sup_le h_eq h_ne
  exact le_trans (le_inf h_lor le_rfl) (bv_or_elim_left hL hR)

-- src/bvm_extras2.lean:232


-- src/bvm_extras2.lean:245


-- src/bvm_extras2.lean:160


-- src/bvm_extras2.lean:248
private lemma Ord.le_iff_lt_or_eq {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y ↔ (Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y) := by
  constructor
  · -- x ⊆ y → x ∈ y ∨ x = y: case split on x = y
    intro H
    have h_eq : (x =ᴮ y) ⊓ Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y := le_sup_of_le_right inf_le_left
    have h_ne : (x =ᴮ y)ᶜ ⊓ Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y :=
      le_sup_of_le_left (Ord.lt_of_ne_and_le (inf_le_right.trans H₁) (inf_le_right.trans H₂)
        inf_le_left (inf_le_right.trans H))
    calc Γ = (x =ᴮ y ⊔ (x =ᴮ y)ᶜ) ⊓ Γ := by rw [sup_compl_eq_top, top_inf_eq]
         _ = (x =ᴮ y) ⊓ Γ ⊔ (x =ᴮ y)ᶜ ⊓ Γ := by rw [inf_sup_right]
         _ ≤ _ := sup_le h_eq h_ne
  · -- x ∈ y ∨ x = y → x ⊆ y
    intro H
    have h1 : (x ∈ᴮ y) ⊓ Γ ≤ x ⊆ᴮ y := subset_of_mem_Ord inf_le_left (inf_le_right.trans H₂)
    have h2 : (x =ᴮ y) ⊓ Γ ≤ x ⊆ᴮ y :=
      -- x = y → x ⊆ x → x ⊆ y (rewrite y to x in x ⊆ x)
      bv_rw'' (ϕ := fun v => x ⊆ᴮ v) inf_le_left (inf_le_right.trans subset_self)
        B_ext_subset_right
    exact le_trans (le_inf H le_rfl) (bv_or_elim_left h1 h2)

-- src/bvm_extras2.lean:259


-- src/bvm_extras2.lean:271


-- src/bvm_extras2.lean:280
private lemma epsilon_trichotomy_of_sub_Ord {Γ : 𝔹} (u : bSet 𝔹)
    (H_ord : Γ ≤ ⨅ x, x ∈ᴮ u ⟹ Ord x) :
    Γ ≤ (⨅ y, y ∈ᴮ u ⟹ (⨅ z, z ∈ᴮ u ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) := by
  apply le_iInf; intro y; rw [← deduction]
  apply le_iInf; intro z; rw [← deduction]
  -- ctx = Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u
  -- H_ord : Γ ≤ ⨅ x, x ∈ u ⟹ Ord x
  have H₁ : Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u ≤ Ord y :=
    le_trans (le_inf
      (inf_le_left.trans (inf_le_left.trans (H_ord.trans (iInf_le _ y))))
      (inf_le_left.trans inf_le_right)) bv_imp_elim
  have H₂ : Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u ≤ Ord z :=
    le_trans (le_inf
      (inf_le_left.trans (inf_le_left.trans (H_ord.trans (iInf_le _ z))))
      inf_le_right) bv_imp_elim
  exact Ord.trichotomy H₁ H₂

-- src/bvm_extras2.lean:289


-- src/bvm_extras2.lean:295


-- src/bvm_extras2.lean:297


-- src/bvm_extras2.lean:302


-- src/bvm_extras2.lean:312


end Ord

-- ============================================================
-- src/bvm_extras2.lean:347-537: section eps_iso
-- ============================================================

section eps_iso
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:350


-- src/bvm_extras2.lean:352


-- src/bvm_extras2.lean:365


-- src/bvm_extras2.lean:371


-- src/bvm_extras2.lean:373


-- src/bvm_extras2.lean:376


-- src/bvm_extras2.lean:379


-- src/bvm_extras2.lean:382


-- src/bvm_extras2.lean:385


-- src/bvm_extras2.lean:388


-- src/bvm_extras2.lean:394


-- src/bvm_extras2.lean:400


-- src/bvm_extras2.lean:423


-- src/bvm_extras2.lean:425


-- src/bvm_extras2.lean:428


-- src/bvm_extras2.lean:433


-- src/bvm_extras2.lean:449


-- src/bvm_extras2.lean:453


-- src/bvm_extras2.lean:460


-- src/bvm_extras2.lean:505


-- src/bvm_extras2.lean:526


end eps_iso

-- ============================================================
-- src/bvm_extras2.lean:539-597: remainder
-- ============================================================

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:541


-- src/bvm_extras2.lean:543


-- src/bvm_extras2.lean:546
private lemma Ord_succ {η : bSet 𝔹} {Γ : 𝔹} (H_Ord : Γ ≤ Ord η) : Γ ≤ Ord (succ η) := by
  -- Ord = epsilon_trichotomy ⊓ epsilon_well_founded ⊓ is_transitive
  refine le_inf (le_inf ?_ ?_) ?_
  · -- epsilon_trichotomy (succ η): use epsilon_trichotomy_of_sub_Ord
    -- Need: ⨅ x, x ∈ succ η ⟹ Ord x
    -- x ∈ succ η ↔ x = η ∨ x ∈ η
    have H_all_ord : Γ ≤ ⨅ x, x ∈ᴮ succ η ⟹ Ord x := by
      apply le_iInf; intro x; rw [← deduction]
      -- goal: Γ ⊓ x ∈ succ η ≤ Ord x
      have hx : Γ ⊓ x ∈ᴮ succ η ≤ x =ᴮ η ⊔ x ∈ᴮ η := by
        have h : x ∈ᴮ succ η = x =ᴮ η ⊔ x ∈ᴮ η := by unfold succ; exact mem_insert1
        rw [h]; exact inf_le_right
      -- Case x = η: Ord η
      have hx_eq : (x =ᴮ η) ⊓ (Γ ⊓ x ∈ᴮ succ η) ≤ Ord x :=
        bv_rw'' (ϕ := fun v => Ord v) (bv_symm inf_le_left)
          (inf_le_right.trans (inf_le_left.trans H_Ord)) B_ext_Ord
      -- Case x ∈ η: Ord x (by Ord_of_mem_Ord)
      have hx_mem : (x ∈ᴮ η) ⊓ (Γ ⊓ x ∈ᴮ succ η) ≤ Ord x :=
        Ord_of_mem_Ord inf_le_left (inf_le_right.trans (inf_le_left.trans H_Ord))
      exact le_trans (le_inf hx le_rfl) (bv_or_elim_left hx_eq hx_mem)
    -- Now use epsilon_trichotomy_of_sub_Ord
    have htri := epsilon_trichotomy_of_sub_Ord (succ η) H_all_ord
    -- htri: Γ ≤ ⨅ y, y ∈ succ η ⟹ ⨅ z, z ∈ succ η ⟹ (y=z ⊔ y∈z ⊔ z∈y)
    -- Unfold epsilon_trichotomy to match
    unfold epsilon_trichotomy
    apply le_iInf; intro y; rw [← deduction]
    apply le_iInf; intro z; rw [← deduction]
    -- ctx = Γ ⊓ y ∈ succ η ⊓ z ∈ succ η
    have hy_mem : Γ ⊓ y ∈ᴮ succ η ⊓ z ∈ᴮ succ η ≤ y ∈ᴮ succ η := inf_le_left.trans inf_le_right
    have hz_mem : Γ ⊓ y ∈ᴮ succ η ⊓ z ∈ᴮ succ η ≤ z ∈ᴮ succ η := inf_le_right
    have htri_y := le_trans (le_inf (inf_le_left.trans (inf_le_left.trans (htri.trans (iInf_le _ y)))) hy_mem) bv_imp_elim
    exact le_trans (le_inf (htri_y.trans (iInf_le _ z)) hz_mem) bv_imp_elim
  · -- epsilon_well_founded: directly from regularity
    rw [epsilon_well_founded]
    apply le_iInf; intro x; rw [← deduction, ← deduction]
    exact bSet_axiom_of_regularity x inf_le_right
  · -- is_transitive (succ η): for z ∈ succ η, z ⊆ succ η
    unfold is_transitive
    apply le_iInf; intro z; rw [← deduction]
    have hz : Γ ⊓ z ∈ᴮ succ η ≤ z =ᴮ η ⊔ z ∈ᴮ η := by
      have h : z ∈ᴮ succ η = z =ᴮ η ⊔ z ∈ᴮ η := by unfold succ; exact mem_insert1
      rw [h]; exact inf_le_right
    have h1 : (z =ᴮ η) ⊓ (Γ ⊓ z ∈ᴮ succ η) ≤ z ⊆ᴮ succ η :=
      bv_rw'' (ϕ := fun v => v ⊆ᴮ succ η) (bv_symm inf_le_left)
        (inf_le_right.trans subset_succ) B_ext_subset_left
    have h2 : (z ∈ᴮ η) ⊓ (Γ ⊓ z ∈ᴮ succ η) ≤ z ⊆ᴮ succ η :=
      subset_trans' (subset_of_mem_Ord inf_le_left (inf_le_right.trans (inf_le_left.trans H_Ord)))
                    (inf_le_right.trans subset_succ)
    exact le_trans (le_inf hz le_rfl) (bv_or_elim_left h1 h2)

-- src/bvm_extras2.lean:563
private lemma Ord.succ_le_of_lt {η ρ : bSet 𝔹} {Γ : 𝔹} (H_Ord' : Γ ≤ Ord ρ) (H_lt : Γ ≤ η ∈ᴮ ρ) :
    Γ ≤ succ η ⊆ᴮ ρ := by
  rw [subset_unfold']
  apply le_iInf; intro w; rw [← deduction]
  set ctx := Γ ⊓ w ∈ᴮ succ η
  have hw : ctx ≤ w ∈ᴮ succ η := inf_le_right
  rw [show w ∈ᴮ succ η = w =ᴮ η ⊔ w ∈ᴮ η from mem_insert1] at hw
  have h_eta_mem : ctx ≤ η ∈ᴮ ρ := inf_le_left.trans H_lt
  have h_rho_trans : ctx ≤ is_transitive ρ := inf_le_left.trans (H_Ord'.trans inf_le_right)
  have h_eta_sub : ctx ≤ η ⊆ᴮ ρ :=
    le_trans (le_inf (h_rho_trans.trans (iInf_le _ η)) h_eta_mem) bv_imp_elim
  -- case 1: w = η → w ∈ ρ
  have hcase1 : ctx ⊓ (w =ᴮ η) ≤ w ∈ᴮ ρ := by
    have h1a : ctx ⊓ (w =ᴮ η) ≤ w =ᴮ η := inf_le_right
    have h1b : ctx ⊓ (w =ᴮ η) ≤ η ∈ᴮ ρ := inf_le_left.trans h_eta_mem
    exact bv_rw'' (bv_symm h1a) h1b B_ext_mem_left
  -- case 2: w ∈ η → w ∈ ρ (η ⊆ ρ)
  have hcase2 : ctx ⊓ (w ∈ᴮ η) ≤ w ∈ᴮ ρ := by
    rw [subset_unfold'] at h_eta_sub
    exact le_trans (le_inf (inf_le_left.trans (h_eta_sub.trans (iInf_le _ w))) inf_le_right)
      bv_imp_elim
  -- combine
  calc ctx ≤ (w =ᴮ η ⊔ w ∈ᴮ η) ⊓ ctx := le_inf hw le_rfl
       _ = ctx ⊓ (w =ᴮ η) ⊔ ctx ⊓ (w ∈ᴮ η) := by rw [inf_comm, inf_sup_left]
       _ ≤ w ∈ᴮ ρ := sup_le hcase1 hcase2
-- src/bvm_extras2.lean:572
private lemma omega_least_is_limit {Γ : 𝔹} :
    Γ ≤ ⨅ η, Ord η ⟹ ((is_limit η) ⟹ omega ⊆ᴮ η) := by
  apply le_iInf; intro η; rw [← deduction, ← deduction]
  -- ctx = Γ ⊓ Ord η ⊓ is_limit η
  -- Goal: ctx ≤ omega ⊆ᴮ η
  -- omega ⊆ η unfolds via subset_unfold to ⨅ j : ULift ℕ, ⊤ ⟹ of_nat j.down ∈ η
  rw [subset_unfold]
  apply le_iInf; intro j
  simp only [omega_bval, omega_func, top_imp]
  -- Goal: Γ ⊓ Ord η ⊓ is_limit η ≤ of_nat j.down ∈ᴮ η
  -- Prove by induction on j.down
  set ctx := Γ ⊓ Ord η ⊓ is_limit η
  have H_η : ctx ≤ Ord η := inf_le_left.trans inf_le_right
  have H_limit : ctx ≤ is_limit η := inf_le_right
  have H_zero : ctx ≤ (∅ : bSet 𝔹) ∈ᴮ η := H_limit.trans inf_le_left
  have H_succ : ctx ≤ ⨅ x, x ∈ᴮ η ⟹ ⨆ y, y ∈ᴮ η ⊓ x ∈ᴮ y := H_limit.trans inf_le_right
  -- Induction on j.down
  induction j.down with
  | zero =>
    -- of_nat 0 = 0 = ∅ ∈ η
    apply bv_rw' (H := zero_eq_empty) (H_new := H_zero) (h_congr := B_ext_mem_left)
  | succ n ih =>
    -- of_nat (n+1) = succ (of_nat n) ∈ η
    rw [check_succ_eq_succ_check]
    -- ih : ctx ≤ of_nat n ∈ᴮ η
    -- H_succ applied to of_nat n gives ⨆ y, y ∈ η ⊓ of_nat n ∈ y
    have h_spec : ctx ≤ ⨆ y, y ∈ᴮ η ⊓ (of_nat n) ∈ᴮ y :=
      le_trans (le_inf (H_succ.trans (iInf_le _ (of_nat n))) ih) bv_imp_elim
    -- Get y with y ∈ η ∧ of_nat n ∈ y
    obtain ⟨y, Hy⟩ := exists_convert h_spec
      (B_ext_inf B_ext_mem_left B_ext_mem_right)
    have Hy_η : ctx ≤ y ∈ᴮ η := Hy.trans inf_le_left
    have Hn_y : ctx ≤ (of_nat n) ∈ᴮ y := Hy.trans inf_le_right
    -- y ∈ η means Ord y (by Ord_of_mem_Ord)
    have Hy_ord : ctx ≤ Ord y := Ord_of_mem_Ord Hy_η H_η
    -- We need succ (of_nat n) ∈ η
    -- of_nat n ∈ y and Ord η, Ord y means either succ (of_nat n) ⊆ y or y ∈ succ (of_nat n)
    -- Use Ord.succ_le_of_lt: of_nat n ∈ y → succ (of_nat n) ⊆ y
    have h_sub : ctx ≤ succ (of_nat n) ⊆ᴮ y :=
      Ord.succ_le_of_lt Hy_ord Hn_y
    -- From Ord.le_iff_lt_or_eq: succ (of_nat n) ⊆ y → succ (of_nat n) ∈ y ∨ succ (of_nat n) = y
    have h_lor : ctx ≤ succ (of_nat n) ∈ᴮ y ⊔ succ (of_nat n) =ᴮ y :=
      (Ord.le_iff_lt_or_eq (Ord_succ Ord_of_nat) Hy_ord).mp h_sub
    -- Case succ (of_nat n) ∈ y: then succ (of_nat n) ∈ η by mem_of_mem_Ord
    have hcase1 : (succ (of_nat n) ∈ᴮ y) ⊓ ctx ≤ succ (of_nat n) ∈ᴮ η :=
      mem_of_mem_Ord inf_le_left (inf_le_right.trans Hy_η) (inf_le_right.trans H_η)
    -- Case succ (of_nat n) = y: then succ (of_nat n) ∈ η (since y ∈ η)
    have hcase2 : (succ (of_nat n) =ᴮ y) ⊓ ctx ≤ succ (of_nat n) ∈ᴮ η :=
      bv_rw'' (ϕ := fun v => v ∈ᴮ η) (bv_symm inf_le_left) (inf_le_right.trans Hy_η) B_ext_mem_left
    exact le_trans (le_inf h_lor le_rfl) (bv_or_elim_left hcase1 hcase2)

end bSet


end CohenSource_BvmExtras2

/- Source module: Definitions.Flypitch4.Zfc -/
section CohenSource_Zfc
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/zfc.lean (552 lines) — Task 22 -/





set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Fol bSet

universe u

-- ============================================================
-- The language of ZFC (src/zfc.lean:32-46)
-- ============================================================







-- ============================================================
-- The Boolean-valued V model (src/zfc.lean:48-113)
-- ============================================================

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]





variable (β)










variable {β}

-- ============================================================
-- Bounded terms/formulas for L_ZFC (src/zfc.lean:115-140)
-- ============================================================



















-- ============================================================
-- Simp lemmas for boolean_realize (src/zfc.lean:142-176)
-- ============================================================




















-- ============================================================
-- Ordinal predicates (src/zfc.lean:307-327)
-- ============================================================













-- ============================================================
-- The ZFC axioms as sentences (src/zfc.lean:179-382)
-- ============================================================

-- axiom of emptyset: ∀ x, x ∉ ∅




-- axiom of ordered pairs: ∀ x y z w, pair(x,y) = pair(z,w) ↔ x=z ∧ y=w




-- axiom of extensionality: ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y




-- axiom schema of strong collection (src/zfc.lean:208-211)











-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y



-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z



-- axiom of infinity (src/zfc.lean:332-347)


private lemma bSet_models_infinity_cohenProof05 : ⊤ ⊩[V β] axiom_of_infinity := by
  change ⊤ ≤ _
  simp only [axiom_of_infinity, boolean_realize_sentence_all,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_not,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_formula_subset',
             boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term_omega',
             boolean_realize_bounded_term, DVec.nth, Ord_f_is_Ord,
             V_forall, V_exists, V_eq]
  -- Goal: ⊤ ≤ ((∅ ∈ᴮ ω ⊓ ⨅ x, x ∈ᴮ ω ⟹ ⨆ y, y ∈ᴮ ω ⊓ x ∈ᴮ y) ⊓
  --            (⨆ α, Ord α ⊓ ω =ᴮ α)) ⊓
  --           (⨅ α, Ord α ⟹ ((∅ ∈ᴮ α ⊓ ⨅ x, x ∈ᴮ α ⟹ ⨆ y, y ∈ᴮ α ⊓ x ∈ᴮ y) ⟹ ω ⊆ α))
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · -- ∅ ∈ᴮ ω
    exact le_trans bSet_axiom_of_infinity' inf_le_left
  · -- ⨅ x, x ∈ᴮ ω ⟹ ⨆ y, y ∈ᴮ ω ⊓ x ∈ᴮ y
    exact le_trans bSet_axiom_of_infinity' inf_le_right
  · -- ⨆ α, Ord α ⊓ ω =ᴮ α
    apply le_iSup_of_le bSet.omega
    exact le_inf Ord_omega (bv_eq_refl _).symm.le
  · -- ⨅ α, Ord α ⟹ (is_limit α ⟹ ω ⊆ α)
    -- This is omega_least_is_limit
    -- is_limit α = ∅ ∈ᴮ α ⊓ ⨅ x, x ∈ᴮ α ⟹ ⨆ y, y ∈ᴮ α ⊓ x ∈ᴮ y
    -- The goal matches omega_least_is_limit directly
    exact le_trans le_top omega_least_is_limit
-- axiom of regularity: ∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y



-- Zorn's lemma (src/zfc.lean:363-376)



-- ============================================================
-- The ZFC theory (src/zfc.lean:378-399)
-- ============================================================







-- ============================================================
-- Functional-relation formulas (src/zfc.lean:402-470)
-- ============================================================





































-- ============================================================
-- The CH formula (src/zfc.lean:481-502)
-- ============================================================









-- ============================================================
-- CH is unprovable from ZFC (src/zfc.lean:508-536)
-- ============================================================

open PSet Cardinal

section CH_unprovable

local notation "𝔹" => 𝔹_cohen







end CH_unprovable

open collapse_algebra

section neg_CH_unprovable







end neg_CH_unprovable

-- ============================================================
-- CH as a first-order formula (src/zfc.lean:538-552)
-- ============================================================

section CH_formula_sec










end CH_formula_sec


end CohenSource_Zfc


theorem solution : ∀ {β : Type} [inst : NontrivialCompleteBooleanAlgebra.{0} β],
  @Fol.forced_in.{1, 0} L_ZFC β (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst)
    (@Top.top.{0} β
      (@BooleanAlgebra.toTop.{0} β
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} β
          (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst))))
    (@V β inst) axiom_of_infinity :=
  @bSet_models_infinity_cohenProof05
