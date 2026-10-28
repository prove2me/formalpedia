-- Prove2me | solution 1 for bSet_models_collection
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T02:07:52.14432+00:00
-- url     : https://prove2.me/submissions/bed21151-fd98-4283-a343-6766936fe15a

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



private theorem inf_eq_of_le {α : Type*} [DistribLattice α] {a b : α} (h : a ≤ b) : a ⊓ b = a :=
  le_antisymm inf_le_left (le_inf le_rfl h)



private theorem le_of_sub_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : bᶜ ⊓ a = ⊥) : a ≤ b := by
  rw [inf_comm] at h
  exact disjoint_compl_right_iff.mp (disjoint_iff.mpr h)

private theorem le_neg_of_inf_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : b ⊓ a = ⊥) :
    a ≤ bᶜ := by
  apply le_of_sub_eq_bot; rwa [compl_compl]

private theorem sub_eq_bot_of_le {α : Type*} [BooleanAlgebra α] {a b : α} (h : a ≤ b) : bᶜ ⊓ a = ⊥ := by
  rw [← inf_eq_of_le h, inf_comm, inf_assoc, inf_compl_eq_bot, inf_bot_eq]













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





private lemma collect.func_spec
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) (Γ : 𝔹)
    (H : Γ ≤ ⨅ (j : u.type), u.bval j ⟹ ⨆ (z : bSet 𝔹), ϕ (u.func j) z) :
    Γ ≤ ⨅ (x : u.type), u.bval x ⟹ ϕ (u.func x) (collect.func ϕ h_congr_right u x) := by
  apply le_iInf; intro i
  rw [← deduction]
  have hspec := Classical.choose_spec (Classical.axiomOfChoice
    (AE_convert u.func u.bval ϕ (by intro z; intro xv yv; exact h_congr_right xv yv z)))
  specialize hspec i
  have hΓ_imp : Γ ≤ u.bval i ⟹ ϕ (u.func i) _ := le_trans H hspec
  rwa [← deduction] at hΓ_imp

-- src/bvm.lean:1814
private lemma collect_spec₁
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) {Γ : 𝔹}
    (H_AE : Γ ≤ ⨅ i : u.type, u.bval i ⟹ ⨆ w, ϕ (u.func i) w) :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ u ⟹ ⨆ w, w ∈ᴮ collect ϕ h_congr_right h_congr_left u ⊓ ϕ z w := by
  apply le_iInf; intro z
  rw [← deduction]
  -- goal: Γ ⊓ z ∈ u ≤ ⨆ w, w ∈ collect u ⊓ ϕ z w
  rw [mem_unfold, inf_iSup_eq]
  apply iSup_le; intro i
  -- context: Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i)
  apply le_iSup_of_le (collect.func ϕ h_congr_right u i)
  apply le_inf
  · -- collect.func ϕ ... u i ∈ collect u
    -- collect ϕ ... u = ⟨u.type, collect.func ϕ ... u, u.bval⟩
    -- (collect ϕ ... u).bval i = u.bval i, (collect ...).func i = collect.func ...
    apply @mem_mk'' 𝔹 _ (collect ϕ h_congr_right h_congr_left u) i
    exact inf_le_right.trans inf_le_left
  · -- ϕ z (collect.func ϕ ... u i)
    -- Use h_congr_left with z =ᴮ u.func i: u.func i =ᴮ z ⊓ ϕ (u.func i) w ≤ ϕ z w
    -- From context: z =ᴮ u.func i (via inf_le_right), rw to u.func i =ᴮ z
    -- From collect.func_spec: Γ ⊓ u.bval i ≤ ϕ (u.func i) (collect.func ϕ ... u i)
    have hϕi := poset_yoneda_inv (Γ ⊓ u.bval i) bv_imp_elim
      (le_inf (inf_le_left.trans (collect.func_spec ϕ h_congr_right h_congr_left u Γ H_AE |>.trans
        (iInf_le _ i))) inf_le_right)
    -- hϕi : Γ ⊓ u.bval i ≤ ϕ (u.func i) (collect.func ϕ h_congr_right u i)
    have hΓbval : Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ Γ ⊓ u.bval i :=
      inf_le_inf_left _ inf_le_left
    have hbval : Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ ϕ (u.func i) (collect.func ϕ h_congr_right u i) :=
      hΓbval.trans hϕi
    -- now use h_congr_left to go from ϕ (u.func i) w to ϕ z w
    have heq_sym : Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ u.func i =ᴮ z := by
      calc Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ z =ᴮ u.func i := inf_le_right.trans inf_le_right
        _ ≤ u.func i =ᴮ z := le_of_eq bv_eq_symm
    exact le_trans (le_inf heq_sym hbval) (h_congr_left (u.func i) z _)

-- src/bvm.lean:1825
private lemma collect_spec₂
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) {Γ : 𝔹}
    (H_AE : Γ ≤ ⨅ i : u.type, u.bval i ⟹ ⨆ w, ϕ (u.func i) w) :
    Γ ≤ ⨅ (w : bSet 𝔹), w ∈ᴮ collect ϕ h_congr_right h_congr_left u ⟹ ⨆ z, z ∈ᴮ u ⊓ ϕ z w := by
  apply le_iInf; intro w
  rw [← deduction]
  -- goal: Γ ⊓ w ∈ collect u ≤ ⨆ z, z ∈ u ⊓ ϕ z w
  -- collect = ⟨u.type, collect.func ϕ h_congr_right u, u.bval⟩
  -- w ∈ collect u = ⨆ i, u.bval i ⊓ w =ᴮ collect.func ϕ ... u i
  rw [mem_unfold (v := collect ϕ h_congr_right h_congr_left u), inf_iSup_eq]
  apply iSup_le; intro i
  -- context: Γ ⊓ (u.bval i ⊓ w =ᴮ collect.func ϕ ... u i)
  apply le_iSup_of_le (u.func i)
  apply le_inf
  · -- u.func i ∈ u ≥ u.bval i
    apply @mem_mk'' 𝔹 _ u i
    exact inf_le_right.trans inf_le_left
  · -- ϕ (u.func i) w
    -- From collect.func_spec at i: Γ ⊓ u.bval i ≤ ϕ (u.func i) (collect.func ϕ ... u i)
    have hϕi := poset_yoneda_inv (Γ ⊓ u.bval i) bv_imp_elim
      (le_inf (inf_le_left.trans (collect.func_spec ϕ h_congr_right h_congr_left u Γ H_AE |>.trans
        (iInf_le _ i))) inf_le_right)
    -- hϕi : Γ ⊓ u.bval i ≤ ϕ (u.func i) (collect.func ϕ h_congr_right u i)
    -- From context: w =ᴮ collect.func ϕ ... u i, so ϕ (u.func i) (collect.func ...) → ϕ (u.func i) w
    -- via h_congr_right: collect.func ... u i =ᴮ w ⊓ ϕ (u.func i) (collect.func ...) ≤ ϕ (u.func i) w
    have hbval : Γ ⊓ (u.bval i ⊓ w =ᴮ collect.func ϕ h_congr_right u i) ≤
        ϕ (u.func i) (collect.func ϕ h_congr_right u i) :=
      (inf_le_inf_left _ inf_le_left).trans hϕi
    have heq_sym : Γ ⊓ (u.bval i ⊓ w =ᴮ collect.func ϕ h_congr_right u i) ≤
        collect.func ϕ h_congr_right u i =ᴮ w :=
      (inf_le_right.trans inf_le_right).trans (le_of_eq bv_eq_symm)
    exact le_trans (le_inf heq_sym hbval) (h_congr_right _ _ _)


-- src/bvm.lean:1844
private theorem bSet_axiom_of_collection (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z) :
    ⊤ ≤ ⨅ u, (⨅ x, x ∈ᴮ u ⟹ ⨆ y, ϕ x y) ⟹ ⨆ v, (⨅ w, w ∈ᴮ u ⟹ ⨆ w', w' ∈ᴮ v ⊓ ϕ w w') ⊓
      ⨅ w', w' ∈ᴮ v ⟹ ⨆ w, w ∈ᴮ u ⊓ ϕ w w' := by
  apply le_iInf; intro u
  rw [← deduction, top_inf_eq]
  -- goal: (⨅ x, x ∈ u ⟹ ⨆ y, ϕ x y) ≤ ⨆ v, ...
  apply le_iSup_of_le (collect ϕ h_congr_right h_congr_left u)
  -- Derive H_AE: (⨅ x, x ∈ u ⟹ ⨆ y, ϕ x y) ≤ ⨅ i, u.bval i ⟹ ⨆ w, ϕ (u.func i) w
  have H_AE : (⨅ x, x ∈ᴮ u ⟹ ⨆ y, ϕ x y) ≤
      ⨅ (i : u.type), u.bval i ⟹ ⨆ (w : bSet 𝔹), ϕ (u.func i) w := by
    apply le_iInf; intro i
    rw [← deduction]
    calc (⨅ x, x ∈ᴮ u ⟹ ⨆ y, ϕ x y) ⊓ u.bval i
        ≤ (u.func i ∈ᴮ u ⟹ ⨆ y, ϕ (u.func i) y) ⊓ u.bval i :=
          inf_le_inf_right _ (iInf_le _ (u.func i))
      _ ≤ (u.func i ∈ᴮ u ⟹ ⨆ y, ϕ (u.func i) y) ⊓ (u.func i ∈ᴮ u) :=
          inf_le_inf_left _ (mem_mk'' le_rfl)
      _ ≤ ⨆ w, ϕ (u.func i) w := bv_imp_elim
  apply le_inf
  · exact collect_spec₁ ϕ h_congr_right h_congr_left u H_AE
  · exact collect_spec₂ ϕ h_congr_right h_congr_left u H_AE

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

/- Source module: Definitions.Flypitch4.Fol -/
section CohenSource_Fol
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/fol.lean (lines 23-508): Language, preterm, term-level material. -/



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace Fol

/-! ## Valuation helpers (subst_realize) -/





















/-! ## Language -/





variable (L : Language.{u})

/-! ## preterm and term -/





variable {L}









namespace preterm





end preterm









-- term.rec: custom recursion principle via structural recursion










/-! ## lift_term_at — lifting variables -/





































/-! ## subst_term — substitution -/







































/-! ## preformula and formula -/



-- Switch L back to explicit so that `preformula L l` works in type signatures.
-- (After "variable {L}" at line 103, writing "preformula l" has ambiguous L in type positions.)
variable (L)

-- formula: formula L is the type of first-order formulas over language L.


variable {L}































/-! ## lift_formula_at — lifting variables in formulas -/





















private lemma lift_formula_at2_medium : ∀ {l} (f : @preformula L l) (n n') {m m'}, m ≤ m' → m' ≤ m + n →
    lift_formula_at (lift_formula_at f n m) n' m' = lift_formula_at f (n + n') m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H₁, H₂ => by
      simp [lift_formula_at, lift_term_at2_medium, H₁, H₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at, lift_term_at2_medium t n' H₁ H₂]
      exact congrArg₂ preformula.apprel (lift_formula_at2_medium f n n' H₁ H₂) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg₂ preformula.imp
        (lift_formula_at2_medium f₁ n n' H₁ H₂)
        (lift_formula_at2_medium f₂ n n' H₁ H₂)
  | _, preformula.all f, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg preformula.all
        (lift_formula_at2_medium f n n' (Nat.add_le_add_right H₁ 1)
          (by omega))









/-! ## subst_formula — substitution into formulas -/



































/-! ## count_quantifiers and quantifier_free -/









/-! ## prf — the proof system (src/fol.lean lines 816-824) -/









/-! ## Derived proof rules (src/fol.lean lines 832-1103) -/



















































































































/-! ## Theory and consistency (src/fol.lean lines 1105-) -/





/-! ## Structure — L-structures (src/fol.lean line 1109) -/

variable (L)



variable {L}



/-! ## realize_term — realization of terms in a structure -/









/-! ## realize_formula — satisfaction relation -/











/-! ## Semantic notions — satisfaction and models -/



























/-! ## Soundness (src/fol.lean lines 1247-1261) -/



/-! ## bounded_preterm, bounded_term, closed_preterm (src/fol.lean lines 1265-1660) -/

-- Bring L back to explicit so that bounded_preterm's constructors can refer to the
-- inductive type unambiguously (same pattern as Structure and formula above).
variable (L)



export bounded_preterm (bd_var bd_func bd_app)







variable {L}









namespace bounded_preterm

































end bounded_preterm

namespace closed_preterm







end closed_preterm

/-! ### bounded_term.rec — custom recursion principle -/





/-! ### Lift and substitution — irrel lemmas -/





/-! ### realize_bounded_term -/



















/-! ### lift_bounded_term_at — lifting bounded terms -/













/-! ### subst_bounded_term — substitution in bounded terms -/































/-! ### realize_bounded_term lemmas -/











/-! ## bounded_preformula, bounded_formula, presentence, sentence (src/fol.lean lines 1660-2200) -/

variable (L)



export bounded_preformula (bd_falsum bd_equal bd_rel bd_apprel bd_imp bd_all)





variable {L}



/-! ### bounded_preformula notations -/

-- Note: ≃ and ⟹ and ∀' are already declared for preformula/preterm above (scoped).
-- We overload them here for bounded_preformula. Since these are scoped notations,
-- we extend existing ones in the Fol namespace.

-- bd_falsum notation conflicts with preformula.falsum ⊥'; we use bd_falsum directly.
-- The bounded equality and implication will reuse the same notation symbols.





















/-! ### bd_apps_rel -/





/-! ### namespace bounded_preformula -/

namespace bounded_preformula















































end bounded_preformula

/-! ### namespace presentence -/

namespace presentence





end presentence

/-! ### Irrel lemmas for bounded formulas -/









/-! ### realize_bounded_formula -/







/-! ### realize_bounded_formula lemmas -/

-- Helper for realize_bounded_formula_iff: structural recursion over f












/-! ### bounded_formula_of_relation -/



/-! ### Recursors for bounded_preformula / bounded_formula (src/fol.lean lines 1984-2038) -/







/-! ### substmax_bounded_formula — substitute the max (last) variable -/



















/-! ### realize_sentence lemmas -/







































/-! ### lift_bounded_formula_at — lift bounded formulas -/













/-! ## Sentence theories (src/fol.lean lines 2233-2759) -/














/-! ### All-realize-sentence — a structure models a sentence theory -/



-- Use ⊨ₜ for "structure realizes a sentence theory" (distinct from existing ⊨ₛ)










/-! ### ssatisfied — semantic consequence for sentence theories -/



-- Note: ⊨ₛ is already taken by satisfied_in; use ssatisfied directly.



/-! ### Connection between ssatisfied and satisfied -/









/-! ## Model — bundled structure satisfying a sentence theory -/



namespace Model

variable {T : SentTheory L}







end Model







/-! ### Soundness at sentence level -/





/-! ### Sentence-level is_consistent -/



/-! ### Theory of a structure -/









/-! ### eliminates_quantifiers -/



/-! ### L_empty, T_empty, T_equality -/







/-! ## Section bd_alls (src/fol.lean lines 2706-2757) -/



















end Fol


end CohenSource_Fol

/- Source module: Definitions.Flypitch4.Bfol -/
section CohenSource_Bfol
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bfol.lean lines 1-450:
   Boolean-valued first-order logic — bStructure + early semantics. -/




set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open DVec

namespace Fol

section bfol

/-! ## bStructure — boolean-valued L-structure -/



variable {L : Language.{u}} {β : Type v} [CompleteBooleanAlgebra β]



attribute [simp] bStructure.eq_refl

variable {S : bStructure L β}



private lemma eq_dsymm : ∀ {n} (x y : DVec S n),
    (DVec.map2 S.eq x y).fInf = (DVec.map2 S.eq y x).fInf
  | _, DVec.nil, DVec.nil => rfl
  | _, DVec.cons x xs, DVec.cons y ys => by
      simp [S.eq_symm x y, eq_dsymm xs ys]



private lemma subst_realize_congr1 (v v' : ℕ → S) (x : S) (m : ℕ) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    ⨅ k : ℕ, S.eq (subst_realize v x m k) (subst_realize v' x m k) := by
  rw [le_iInf_iff]
  intro k
  rcases Nat.lt_trichotomy k m with h | h | h
  · simp [subst_realize, h]; exact iInf_le _ k
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h]; exact iInf_le _ (k - 1)



/-! ## boolean_realize_term -/





private lemma boolean_realize_term_subst (v : ℕ → S) :
    ∀ {l} (m : ℕ) (t : @preterm L l) (s : term L) (xs : DVec S l),
    boolean_realize_term
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) t xs =
    boolean_realize_term v (subst_term t s m) xs
  | _, m, preterm.var k, s, _ => by
      simp only [boolean_realize_term, subst_term, subst_realize_lt, subst_realize_gt,
                 subst_realize_var_eq]
      rcases Nat.lt_trichotomy k m with h | h | h
      · simp [h, Nat.lt_asymm h]
      · subst h; simp
      · simp [h, Nat.lt_asymm h]
  | _, _, preterm.func _, _, _ => rfl
  | _, m, preterm.app t₁ t₂, s, xs => by
      simp only [boolean_realize_term, subst_term]
      rw [boolean_realize_term_subst v m t₂ s DVec.nil,
          boolean_realize_term_subst v m t₁ s]



private lemma boolean_realize_term_congr_gen (v v' : ℕ → S) :
    ∀ {l} (t : @preterm L l) (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ≤
      S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs')
  | _, preterm.var k, _, _ => le_trans inf_le_left (iInf_le _ k)
  | _, preterm.func f, xs, xs' => le_trans inf_le_right (S.fun_congr f xs xs')
  | _, preterm.app t₁ t₂, xs, xs' => by
      simp only [boolean_realize_term]
      refine le_trans ?_ (boolean_realize_term_congr_gen v v' t₁
        (DVec.cons (boolean_realize_term v t₂ DVec.nil) xs)
        (DVec.cons (boolean_realize_term v' t₂ DVec.nil) xs'))
      simp only [DVec.map2, DVec.fInf_cons]
      apply le_inf
      · exact inf_le_left
      · apply le_inf
        · have h2 := boolean_realize_term_congr_gen v v' t₂ DVec.nil DVec.nil
          simp only [DVec.map2, DVec.fInf_nil, inf_top_eq] at h2
          exact le_trans inf_le_left h2
        · exact inf_le_right

private lemma boolean_realize_term_congr_iInf (v v' : ℕ → S) {l} (t : @preterm L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs) := by
  have h := boolean_realize_term_congr_gen v v' t xs xs
  simp only [eq_drefl, inf_top_eq] at h
  exact h



/-! ## boolean_realize_formula -/





private lemma boolean_realize_formula_subst : ∀ {l} (v : ℕ → S) (m : ℕ) (f : @preformula L l)
    (s : term L) (xs : DVec S l),
    boolean_realize_formula
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) f xs =
    boolean_realize_formula v (subst_formula f s m) xs
  | _, v, m, preformula.falsum, s, xs => rfl
  | _, v, m, preformula.equal t₁ t₂, s, xs => by
      simp [boolean_realize_term_subst]
  | _, v, m, preformula.rel R, s, xs => rfl
  | _, v, m, preformula.apprel f t, s, xs => by
      simp only [boolean_realize_formula, subst_formula, boolean_realize_term_subst]
      rw [boolean_realize_formula_subst v m f s]
  | _, v, m, preformula.imp f₁ f₂, s, xs => by
      simp only [boolean_realize_formula, subst_formula]
      congr 1
      · rw [boolean_realize_formula_subst v m f₁ s xs]
      · rw [boolean_realize_formula_subst v m f₂ s xs]
  | _, v, m, preformula.all f, s, xs => by
      simp only [boolean_realize_formula, subst_formula]
      congr 1; funext x
      rw [← boolean_realize_formula_subst (subst_realize v x 0) (m + 1) f s xs]
      apply boolean_realize_formula_congr'
      intro k
      rw [subst_realize2_0, ← boolean_realize_term_subst_lift v x 0, lift_term_def, lift_term2]

private lemma boolean_realize_formula_subst0 {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    boolean_realize_formula (subst_realize v (boolean_realize_term v s DVec.nil) 0) f xs =
    boolean_realize_formula v (subst_formula f s 0) xs := by
  have h := boolean_realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs



private lemma boolean_realize_formula_congr_gen : ∀ (v v' : ℕ → S) {l} (f : @preformula L l)
    (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
    boolean_realize_formula v f xs ≤ boolean_realize_formula v' f xs'
  | v, v', _, preformula.falsum, _, _ => inf_le_right
  | v, v', _, preformula.equal t₁ t₂, DVec.nil, DVec.nil => by
      simp only [boolean_realize_formula, DVec.map2, DVec.fInf_nil, inf_top_eq]
      -- Goal: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v' t₁)(brt v' t₂)
      refine le_trans ?_ (S.eq_trans (boolean_realize_term v t₂ DVec.nil))
      apply le_inf
      · -- Need: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v' t₁)(brt v t₂)
        refine le_trans ?_ (S.eq_trans (boolean_realize_term v t₁ DVec.nil))
        apply le_inf
        · -- Need: I ⊓ ... ≤ S.eq(brt v' t₁)(brt v t₁)
          -- = S.eq(brt v t₁)(brt v' t₁) by symm, and I ≤ that by congr_iInf
          rw [S.eq_symm (boolean_realize_term v' t₁ DVec.nil) (boolean_realize_term v t₁ DVec.nil)]
          exact le_trans inf_le_left (boolean_realize_term_congr_iInf v v' t₁ DVec.nil)
        · exact inf_le_right  -- I ⊓ S.eq... ≤ S.eq(brt v t₁)(brt v t₂)
      · -- Need: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v t₂)(brt v' t₂)
        exact le_trans inf_le_left (boolean_realize_term_congr_iInf v v' t₂ DVec.nil)
  | v, v', _, preformula.rel R, xs, xs' => by
      simp only [boolean_realize_formula]
      exact le_trans (inf_le_inf inf_le_right le_rfl) (S.rel_congr R xs xs')
  | v, v', _, preformula.apprel f t, xs, xs' => by
      simp only [boolean_realize_formula]
      refine le_trans ?_ (boolean_realize_formula_congr_gen v v' f
        (DVec.cons (boolean_realize_term v t DVec.nil) xs)
        (DVec.cons (boolean_realize_term v' t DVec.nil) xs'))
      simp only [DVec.map2, DVec.fInf_cons]
      -- Need: I ⊓ xs_eq ⊓ brf v f (brt v t :: xs) ≤
      --         I ⊓ (S.eq(brt v t)(brt v' t) ⊓ xs_eq) ⊓ brf v f (brt v t :: xs)
      -- brf does not change; so need to weaken I ⊓ xs_eq to I ⊓ (S.eq ⊓ xs_eq)
      apply le_inf
      · -- I ⊓ xs_eq ⊓ brf ≤ I ⊓ (S.eq ⊓ xs_eq)
        apply le_inf
        · exact le_trans inf_le_left inf_le_left  -- ≤ I
        · apply le_inf
          · -- ≤ S.eq(brt v t)(brt v' t)
            exact le_trans (le_trans inf_le_left inf_le_left)
              (boolean_realize_term_congr_iInf v v' t DVec.nil)
          · exact le_trans inf_le_left inf_le_right  -- ≤ xs_eq
      · exact inf_le_right  -- ≤ brf v f (brt v t :: xs)
  | v, v', _, preformula.imp f₁ f₂, xs, xs' => by
      simp only [boolean_realize_formula, imp, inf_sup_left]
      apply sup_le_sup
      · -- Need: I ⊓ xs_eq ⊓ b_f₁ᶜ ≤ b_f₁'ᶜ
        apply le_neg_of_inf_eq_bot
        -- From IH with v↔v', xs↔xs': I' ⊓ xs_eq' ⊓ b_f₁' ≤ b_f₁
        -- I' = (⨅ k, S.eq (v' k) (v k)) = I  (by eq_symm)
        -- xs_eq' = (xs'.map2 S.eq xs).fInf = xs_eq  (by eq_dsymm)
        have key := boolean_realize_formula_congr_gen v' v f₁ xs' xs
        rw [show (⨅ k : ℕ, S.eq (v' k) (v k)) = (⨅ k : ℕ, S.eq (v k) (v' k)) from
              iInf_congr fun k => S.eq_symm _ _,
            ← eq_dsymm xs xs'] at key
        have bot := sub_eq_bot_of_le key
        -- bot: b_f₁ᶜ ⊓ (I ⊓ xs_eq ⊓ b_f₁') = ⊥
        -- Need: b_f₁' ⊓ (I ⊓ xs_eq ⊓ b_f₁ᶜ) = ⊥
        -- These are equal by commutativity and associativity of ⊓
        have : boolean_realize_formula v' f₁ xs' ⊓
               ((⨅ k, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
               (boolean_realize_formula v f₁ xs)ᶜ) =
               (boolean_realize_formula v f₁ xs)ᶜ ⊓
               ((⨅ k, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
               boolean_realize_formula v' f₁ xs') := by ac_rfl
        rw [this]; exact bot
      · exact boolean_realize_formula_congr_gen v v' f₂ xs xs'
  | v, v', _, preformula.all f, DVec.nil, DVec.nil => by
      simp only [boolean_realize_formula, DVec.map2, DVec.fInf_nil, inf_top_eq]
      rw [le_iInf_iff]
      intro x
      refine le_trans ?_ (boolean_realize_formula_congr_gen (subst_realize v x 0)
        (subst_realize v' x 0) f DVec.nil DVec.nil)
      simp only [DVec.map2, DVec.fInf_nil, inf_top_eq]
      apply le_inf
      · exact le_trans inf_le_left (subst_realize_congr1 v v' x 0)
      · exact le_trans inf_le_right (iInf_le _ x)

private lemma boolean_realize_formula_congr (v v' : ℕ → S) {l} (f : @preformula L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ boolean_realize_formula v f xs ≤
    boolean_realize_formula v' f xs := by
  have key := boolean_realize_formula_congr_gen v v' f xs xs
  have hd : (DVec.map2 S.eq xs xs).fInf = ⊤ := eq_drefl xs
  rw [hd, inf_top_eq] at key
  exact le_trans (le_inf le_rfl le_top) (by rw [inf_top_eq]; exact key)







/-! ## Satisfiability — boolean_realize_formula_glb, bstatisfied -/













/-! ## boolean_formula_soundness -/



/-! ## boolean_realize_bounded_term -/





























/-! ## boolean_realize_bounded_formula -/



/-! ## boolean_realize_sentence — src/bfol.lean:456-459 -/





/-! ## boolean_realize_bounded_formula_eq — src/bfol.lean:461-475 -/





private lemma boolean_realize_bounded_term_eq' {n} {v₁ : DVec S n} (x : S)
    {l} (t : bounded_preterm L n l) (xs : DVec S l) :
    boolean_realize_bounded_term v₁ t xs =
    boolean_realize_term (fun k => if h : k < n then v₁.nth k h else x) t.fst xs := by
  symm
  apply boolean_realize_bounded_term_eq
  intro k hk
  rw [dif_pos hk]

/-! ## boolean_realize_bounded_formula_congr — src/bfol.lean:489-503 -/

private lemma boolean_realize_bounded_formula_congr {n l} (H_nonempty : Nonempty S)
    (v₁ v₂ : DVec S n) (f : bounded_preformula L n l) (xs : DVec S l) :
    ((⨅ m : Fin n, S.eq (v₁.nth m.1 m.2) (v₂.nth m.1 m.2)) ⊓
     boolean_realize_bounded_formula v₁ f xs : β) ≤
    boolean_realize_bounded_formula v₂ f xs := by
  obtain ⟨x⟩ := H_nonempty
  rw [boolean_realize_bounded_formula_eq' (v₁ := v₁) x f xs,
      boolean_realize_bounded_formula_eq' (v₁ := v₂) x f xs]
  let φ₁ := fun k => if h : k < n then v₁.nth k h else x
  let φ₂ := fun k => if h : k < n then v₂.nth k h else x
  have key := boolean_realize_formula_congr φ₁ φ₂ f.fst xs
  refine le_trans ?_ key
  apply inf_le_inf_right
  rw [le_iInf_iff]
  intro k
  by_cases hk : k < n
  · simp only [φ₁, φ₂, dif_pos hk]
    exact iInf_le _ (⟨k, hk⟩ : Fin n)
  · simp only [φ₁, φ₂, dif_neg hk, S.eq_refl]
    exact le_top

/-! ## boolean_realize_bounded_formula_irrel' — src/bfol.lean:513-528 -/





/-! ## boolean_realize_bounded_formula_cast_eq_irrel — src/bfol.lean:536-538 -/



/-! ## basic simp lemmas for boolean_realize_sentence — src/bfol.lean:543-559 -/























/-! ## boolean_realize_bounded_formula_bd_apps_rel — src/bfol.lean:596-602 -/



/-! ## boolean_realize_cast_bounded_formula — src/bfol.lean:604-619 -/





/-! ## boolean_realize_sentence_bd_apps_rel — src/bfol.lean:621-634 -/











/-! ## forced_in, all_forced_in — src/bfol.lean:647-658 -/











/-! ## forced — src/bfol.lean:674-677 -/





/-! ## bsatisfied_of_forced, forced_of_bsatisfied — src/bfol.lean:680-698 -/









/-! ## bModel — src/bfol.lean:720-721 -/



/-! ## boolean_soundness, unprovable_of_model_neg — src/bfol.lean:730-739 -/





/-! ## boolean_realize_subst_preterm — src/bfol.lean:741-761 -/





/-! ## boolean_realize_sentence_bd_alls — src/bfol.lean:763-778 -/

private lemma boolean_realize_sentence_bd_alls {n} {f : bounded_formula L n} :
    boolean_realize_sentence S (bd_alls n f) =
    ⨅ xs : DVec S n, boolean_realize_bounded_formula xs f DVec.nil := by
  induction n with
  | zero =>
    simp only [bd_alls, boolean_realize_sentence]
    apply le_antisymm
    · rw [le_iInf_iff]
      intro xs
      cases xs
      rfl
    · exact iInf_le _ DVec.nil
  | succ n ih =>
    rw [bd_alls, ih]
    apply le_antisymm
    · rw [le_iInf_iff]
      intro xs
      cases xs with
      | cons x xs =>
        refine le_trans (iInf_le _ xs) ?_
        exact iInf_le _ x
    · rw [le_iInf_iff]
      intro xs
      simp only [boolean_realize_bounded_formula, le_iInf_iff]
      intro x
      exact iInf_le _ (DVec.cons x xs)

/-! ## consis_of_exists_bmodel — src/bfol.lean:785-793 -/



/-! ## subst0_bounded_formula_not — src/bfol.lean:799-801 -/



/-! ## subst0_bounded_formula_and — src/bfol.lean:803-805 -/



/-! ## boolean_realize_bounded_formula_insert_lift — src/bfol.lean:854-872 -/



/-! ## boolean_realize_formula_insert_lift2 — src/bfol.lean:874-879 -/



/-! ## boolean_realize_subst_formula0 — src/bfol.lean:881-897 -/

private lemma boolean_realize_subst_formula0 {n} (S : bStructure L β) [Nonempty S]
    (f : bounded_formula L (n + 1)) (t : bounded_term L n) (v : DVec S n) :
    boolean_realize_bounded_formula v (subst0_bounded_formula f t) DVec.nil =
    boolean_realize_bounded_formula
      (DVec.cons (boolean_realize_bounded_term v t DVec.nil) v) f DVec.nil := by
  obtain ⟨y⟩ := ‹Nonempty S›
  -- Reduce both sides to formula semantics via bounded_formula_eq'
  rw [boolean_realize_bounded_formula_eq' (v₁ := v) y,
      boolean_realize_bounded_formula_eq' (v₁ := DVec.cons _ v) y]
  simp only [subst0_bounded_formula_fst]
  -- LHS: boolean_realize_formula (fun k => if h : k < n then v.nth k h else y) (f.fst[t.fst//0]) []
  -- RHS: boolean_realize_formula (fun k => if h : k < n+1 then (brt_v_t :: v).nth k h else y) f.fst []
  -- Use ← boolean_realize_formula_subst0 on LHS:
  -- = boolean_realize_formula (subst_realize φ (brt_v φ t.fst []) 0) f.fst []
  -- where φ = (fun k => if h : k < n then v.nth k h else y)
  -- and brt_v φ t.fst [] = boolean_realize_bounded_term_eq' ... = brt v t []
  rw [← boolean_realize_formula_subst0]
  -- Now LHS = boolean_realize_formula (subst_realize φ (brt φ t.fst []) 0) f.fst []
  -- RHS = boolean_realize_formula (fun k => if h : k < n+1 then (brt_v_t :: v).nth k h else y) f.fst []
  apply boolean_realize_formula_congr'
  intro k
  simp only [subst_realize, boolean_realize_term, DVec.nth]
  -- The bounded term realization
  rw [← boolean_realize_bounded_term_eq' y]
  by_cases hk : k < n + 1
  · simp only [dif_pos hk, DVec.nth]
    cases k with
    | zero => simp [subst_realize, boolean_realize_bounded_term]
    | succ k =>
      have h2k : k < n := Nat.lt_of_succ_lt_succ hk
      simp only [subst_realize, Nat.zero_lt_succ, if_false, Nat.lt_irrefl, if_false]
      simp [dif_pos h2k, DVec.nth]
  · simp only [dif_neg hk, subst_realize]
    have h2k : 0 < k := Nat.pos_of_ne_zero (by omega)
    have h3k : ¬(k - 1 < n) := by omega
    simp [Nat.not_lt.mp hk, h2k, h3k, dif_neg h3k]

end bfol

end Fol


end CohenSource_Bfol

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


private lemma lift2_helper {n l} (f : bounded_preformula L_ZFC n l) {k} (m : ℕ) :
    (f ↑ᶠᵇ' (k + 2) # m).fst = ((f ↑ᶠᵇ' (k + 1) # m) ↑ᶠᵇ' 1 # m).fst := by
  simp only [lift_bounded_formula_fst]
  rw [lift_formula_at2_medium] <;> omega

private lemma B_ext_left_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 1))
    (xs : DVec (V β) n) (x y : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons x xs) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons y xs) ϕ DVec.nil := by
  -- Key: x =ᴮ y = ⨅ m : Fin (n+1), (V β).eq ((x::xs)[m]) ((y::xs)[m])
  -- At m=0: eq(x,y) = x =ᴮ y; at m=succ k: eq(xs[k], xs[k]) = ⊤
  have hkey : x =ᴮ y = ⨅ (m : Fin (n + 1)),
      (V β).eq ((DVec.cons x xs).nth m.1 m.2) ((DVec.cons y xs).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf; intro ⟨m, hm⟩
      simp only [V_eq]
      cases m with
      | zero => simp [DVec.nth]
      | succ k =>
        show x =ᴮ y ≤ xs.nth k (Nat.lt_of_succ_lt_succ hm) =ᴮ xs.nth k (Nat.lt_of_succ_lt_succ hm)
        rw [bv_eq_refl]; exact le_top
    · exact iInf_le _ (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  rw [hkey]
  exact boolean_realize_bounded_formula_congr (inferInstance : Nonempty (V β)) _ _ ϕ DVec.nil
private lemma B_ext_right_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 2))
    (xs : DVec (V β) n) (x y z : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons z (DVec.cons x xs)) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons z (DVec.cons y xs)) ϕ DVec.nil := by
  -- Key: x =ᴮ y = ⨅ m : Fin (n+2), eq((z::x::xs)[m], (z::y::xs)[m])
  -- At m=0: eq(z,z)=⊤; at m=1: eq(x,y)=x=ᴮy; at m=succ(succ k): eq(xs[k],xs[k])=⊤
  have hkey : x =ᴮ y = ⨅ (m : Fin (n + 2)),
      (V β).eq ((DVec.cons z (DVec.cons x xs)).nth m.1 m.2)
               ((DVec.cons z (DVec.cons y xs)).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf; intro ⟨m, hm⟩
      simp only [V_eq]
      cases m with
      | zero =>
        show x =ᴮ y ≤ z =ᴮ z
        rw [bv_eq_refl]; exact le_top
      | succ k =>
        cases k with
        | zero => simp [DVec.nth]
        | succ k' =>
          show x =ᴮ y ≤ xs.nth k' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm)) =ᴮ
               xs.nth k' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm))
          rw [bv_eq_refl]; exact le_top
    · exact iInf_le _ (⟨1, by omega⟩ : Fin (n + 2))
  rw [hkey]
  exact boolean_realize_bounded_formula_congr (inferInstance : Nonempty (V β)) _ _ ϕ DVec.nil
private lemma realize_lift2_at2 {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec (V β) n) (x y z₁ z₂ : V β) :
    boolean_realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ v)))) (ϕ ↑ᶠᵇ' 2 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper ϕ (k := 0) 2)]
  rw [boolean_realize_formula_insert_lift2 (DVec.cons z₂ v) x y z₁ (ϕ ↑ᶠᵇ' 1 # 2)]
  exact boolean_realize_formula_insert_lift2 v x y z₂ ϕ

private lemma realize_lift3_at2 {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec (V β) n) (x y z₁ z₂ z₃ : V β) :
    boolean_realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ (DVec.cons z₃ v))))) (ϕ ↑ᶠᵇ' 3 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper ϕ (k := 1) 2)]
  rw [boolean_realize_formula_insert_lift2 (DVec.cons z₂ (DVec.cons z₃ v)) x y z₁ (ϕ ↑ᶠᵇ' 2 # 2)]
  exact realize_lift2_at2 ϕ v x y z₂ z₃

private lemma bSet_models_collection_cohenProof04 {n} (ϕ : bounded_formula L_ZFC (n + 2)) :
    ⊤ ⊩[V β] axiom_of_collection ϕ := by
  change ⊤ ≤ _
  simp only [axiom_of_collection, boolean_realize_sentence_bd_alls]
  apply le_iInf
  intro xs
  match xs with
  | DVec.cons u xs' =>
    simp only [boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
               boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_mem',
               boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq,
               boolean_realize_formula_insert_lift2, realize_lift2_at2, realize_lift3_at2,
               boolean_realize_subst_formula0]
    -- After simp, goal should be `⊤ ≤ realize (cons u xs') (imp ... (∃ ...))`
    -- with the formula bodies being  ϕ.eval at appropriate env
    -- ψ a b := boolean_realize (b :: a :: xs') ϕ  matches the role of ϕ in bSet_axiom_of_collection
    have hcoll := bSet_axiom_of_collection
        (fun a b : bSet β =>
          boolean_realize_bounded_formula (DVec.cons b (DVec.cons a xs')) ϕ DVec.nil)
        (fun x y z => by
          -- need: x =ᴮ y ⊓ realize (x :: z :: xs') ϕ ≤ realize (y :: z :: xs') ϕ
          -- (ψ z x → ψ z y means varying position 0 of cons-cons)
          exact B_ext_left_realize_bounded_formula ϕ (DVec.cons z xs') x y)
        (fun x y z => by
          -- need: x =ᴮ y ⊓ realize (z :: x :: xs') ϕ ≤ realize (z :: y :: xs') ϕ
          exact B_ext_right_realize_bounded_formula ϕ xs' x y z)
    have hu := hcoll.trans (iInf_le _ u)
    -- Try to match goal
    convert hu using 0
-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y



-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z



-- axiom of infinity (src/zfc.lean:332-347)



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


theorem solution : ∀ {β : Type} [inst : NontrivialCompleteBooleanAlgebra.{0} β] {n : Nat}
  (ϕ :
    Fol.bounded_formula.{1} L_ZFC
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))),
  @Fol.forced_in.{1, 0} L_ZFC β (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst)
    (@Top.top.{0} β
      (@BooleanAlgebra.toTop.{0} β
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} β
          (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst))))
    (@V β inst) (@axiom_of_collection n ϕ) :=
  @bSet_models_collection_cohenProof04
