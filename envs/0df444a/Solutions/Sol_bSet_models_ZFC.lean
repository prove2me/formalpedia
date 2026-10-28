-- Prove2me | solution 1 for bSet_models_ZFC
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T02:09:36.681572+00:00
-- url     : https://prove2.me/submissions/726a4642-bf0e-4b0e-a384-be20144cfa01

import Definitions.Def_CH_Cohen_Library10
import Theorems.Thm_bSet_models_collection
import Theorems.Thm_bSet_models_infinity
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







-- Aliases without `@[simp]`: mathlib4's `inf_idem`/`sup_idem` already carry `@[simp]`,
-- so adding `@[simp]` here would create duplicate rewrite rules.




-- Note: bot_lt_iff_not_le_bot and lt_top_iff_not_top_le already exist in mathlib4












open scoped Flypitch




























-- Note: Lean 4 already has a `imp_self` in core; use `ba_imp_self` for Boolean algebra version

























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
private lemma bv_or_elim {b₁ b₂ c : 𝔹} (h : b₁ ≤ c) (h' : b₂ ≤ c) : b₁ ⊔ b₂ ≤ c :=
  sup_le h h'

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
private lemma bv_imp_intro_lemma {a b c : 𝔹} (h : a ⊓ b ≤ c) : a ≤ b ⟹ c := by
  rwa [deduction] at h

-- src/bvm.lean:140


-- src/bvm.lean:143


-- src/bvm.lean:146


-- src/bvm.lean:149
private lemma bv_context_apply {β : Type*} [CompleteBooleanAlgebra β] {Γ a₁ a₂ : β}
    (h₁ : Γ ≤ a₁ ⟹ a₂) (h₂ : Γ ≤ a₁) : Γ ≤ a₂ :=
  context_imp_elim h₁ h₂

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
private theorem bSet_axiom_of_extensionality (x y : bSet 𝔹) :
    (⨅ (z : bSet 𝔹), (z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (z ∈ᴮ y ⟹ z ∈ᴮ x)) ≤ x =ᴮ y := by
  rw [bv_eq_unfold]
  apply le_inf <;> apply le_iInf <;> intro i
  · apply iInf_le_of_le (x.func i)
    apply inf_le_left.trans
    apply imp_le_of_left_le
    cases x with | mk xα xA xB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i (le_inf le_rfl (by simp))
  · apply iInf_le_of_le (y.func i)
    apply inf_le_right.trans
    apply imp_le_of_left_le
    cases y with | mk yα yA yB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i (le_inf le_rfl (by simp))

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
private lemma bv_rw {x y : bSet 𝔹} (H : x =ᴮ y = ⊤) (ϕ : bSet 𝔹 → 𝔹)
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} : ϕ y = ϕ x := by
  apply le_antisymm
  · -- ϕ y ≤ ϕ x: use h_congr y x with y =ᴮ x = ⊤
    have : y =ᴮ x = ⊤ := by rw [bv_eq_symm]; exact H
    calc ϕ y ≤ ⊤ ⊓ ϕ y := by simp
      _ = (y =ᴮ x) ⊓ ϕ y := by rw [this]
      _ ≤ ϕ x := h_congr y x
  · -- ϕ x ≤ ϕ y: use h_congr x y with x =ᴮ y = ⊤
    calc ϕ x ≤ ⊤ ⊓ ϕ x := by simp
      _ = (x =ᴮ y) ⊓ ϕ x := by rw [H]
      _ ≤ ϕ y := h_congr x y

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
private lemma empty_spec {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ (x ∈ᴮ ∅)ᶜ := by
  have : x ∈ᴮ ∅ = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
  rw [this, compl_bot]; exact le_top

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
private lemma two_term_mixture_h_star (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
    ∀ i j : ULift Bool, (bool_map a₁ a₂) i ⊓ (bool_map a₁ a₂) j ≤
      (bool_map u₁ u₂) i =ᴮ (bool_map u₁ u₂) j := by
  intro ⟨bi⟩ ⟨bj⟩
  cases bi <;> cases bj <;> simp only [bool_map, bv_eq_refl, le_top, h_anti, inf_comm, bot_le]

-- src/bvm.lean:937 — Mixing Lemma


-- src/bvm.lean:954


-- src/bvm.lean:957
private lemma mixing_lemma_two_term (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
    a₁ ≤ (two_term_mixture a₁ a₂ h_anti u₁ u₂ =ᴮ u₁) ∧
    a₂ ≤ (two_term_mixture a₁ a₂ h_anti u₁ u₂ =ᴮ u₂) := by
  have h := mixing_lemma' (bool_map a₁ a₂) (bool_map u₁ u₂)
    (two_term_mixture_h_star a₁ a₂ h_anti u₁ u₂)
  exact ⟨h ⟨false⟩, h ⟨true⟩⟩

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
include h_partition in
private lemma two_term_mixture_mem_top (h₁ : u₁ ∈ᴮ X = ⊤) (h₂ : u₂ ∈ᴮ X = ⊤) :
    two_term_mixture a₁ a₂ h_anti u₁ u₂ ∈ᴮ X = ⊤ := by
  apply top_unique
  set U := two_term_mixture a₁ a₂ h_anti u₁ u₂
  have mixing := mixing_lemma_two_term a₁ a₂ h_anti u₁ u₂
  -- ⊤ = a₁ ⊔ a₂ ≤ (U =ᴮ u₁) ⊔ (U =ᴮ u₂) ≤ U ∈ᴮ X
  calc ⊤ = a₁ ⊔ a₂ := by rw [h_partition]
    _ ≤ (U =ᴮ u₁) ⊔ (U =ᴮ u₂) := sup_le_sup mixing.1 mixing.2
    _ ≤ U ∈ᴮ X := bv_or_elim
        (by calc U =ᴮ u₁ = u₁ =ᴮ U := bv_eq_symm
              _ ≤ u₁ =ᴮ U ⊓ u₁ ∈ᴮ X := le_inf le_rfl (h₁ ▸ le_top)
              _ ≤ U ∈ᴮ X := subst_congr_mem_left)
        (by calc U =ᴮ u₂ = u₂ =ᴮ U := bv_eq_symm
              _ ≤ u₂ =ᴮ U ⊓ u₂ ∈ᴮ X := le_inf le_rfl (h₂ ▸ le_top)
              _ ≤ U ∈ᴮ X := subst_congr_mem_left)

-- src/bvm.lean:1192
include h_partition in
private lemma two_term_mixture_subset_top (H : a₁ = u₂ ⊆ᴮ u₁) :
    ⊤ ≤ u₂ ⊆ᴮ (two_term_mixture a₁ a₂ h_anti u₁ u₂) := by
  set U := two_term_mixture a₁ a₂ h_anti u₁ u₂
  have mixing := mixing_lemma_two_term a₁ a₂ h_anti u₁ u₂
  have h_eq₁ : a₁ ≤ u₁ =ᴮ U := mixing.1.trans (le_of_eq bv_eq_symm)
  have h_eq₂ : a₂ ≤ u₂ =ᴮ U := mixing.2.trans (le_of_eq bv_eq_symm)
  rw [subset_unfold', le_iInf_iff]
  intro w
  rw [← deduction, top_inf_eq]
  -- Goal: w ∈ᴮ u₂ ≤ w ∈ᴮ U
  -- From H: a₁ ⊓ w ∈ᴮ u₂ ≤ w ∈ᴮ u₁ (subset definition)
  have h_mem_u₂_le_u₁ : a₁ ⊓ w ∈ᴮ u₂ ≤ w ∈ᴮ u₁ := by
    have hsub : (u₂ ⊆ᴮ u₁) ⊓ w ∈ᴮ u₂ ≤ w ∈ᴮ u₁ := by
      rw [subset_unfold']
      exact le_trans (le_inf (inf_le_left.trans (iInf_le _ w)) inf_le_right) bv_imp_elim
    rw [H]; exact hsub
  -- Decompose: w ∈ᴮ u₂ = (a₁ ⊔ a₂) ⊓ w ∈ᴮ u₂ = (a₁ ⊓ w ∈ᴮ u₂) ⊔ (a₂ ⊓ w ∈ᴮ u₂)
  calc w ∈ᴮ u₂
      = (a₁ ⊔ a₂) ⊓ w ∈ᴮ u₂ := by rw [h_partition, top_inf_eq]
    _ = a₁ ⊓ w ∈ᴮ u₂ ⊔ a₂ ⊓ w ∈ᴮ u₂ := inf_sup_right a₁ a₂ _
    _ ≤ w ∈ᴮ U :=
        sup_le
          -- a₁ case: a₁ ⊓ w ∈ᴮ u₂ ≤ w ∈ᴮ u₁, then (u₁ =ᴮ U) ⊓ w ∈ᴮ u₁ ≤ w ∈ᴮ U
          (le_trans (le_inf (inf_le_left.trans h_eq₁) h_mem_u₂_le_u₁) subst_congr_mem_right)
          -- a₂ case: a₂ ⊓ w ∈ᴮ u₂ ≤ (u₂ =ᴮ U) ⊓ w ∈ᴮ u₂ ≤ w ∈ᴮ U
          (le_trans (le_inf (inf_le_left.trans h_eq₂) inf_le_right) subst_congr_mem_right)

end mixing_corollaries

/-! ### core_aux_lemma -/

-- src/bvm.lean:1210
private lemma core_aux_lemma (ϕ : bSet 𝔹 → 𝔹) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y)
    (h_definite : (⨆ (w : bSet 𝔹), ϕ w) = ⊤) (v : bSet 𝔹) :
    ∃ u : bSet 𝔹, ϕ u = ⊤ ∧ ϕ v = u =ᴮ v := by
  obtain ⟨w, H_w⟩ := maximum_principle ϕ h_congr
  have H_w_eq : ϕ w = ⊤ := by rw [← H_w, h_definite]
  set b := ϕ v with hb
  have h_inf : b ⊓ bᶜ = ⊥ := inf_compl_eq_bot
  set U := two_term_mixture b bᶜ h_inf v w with hU
  have mixing := mixing_lemma_two_term b bᶜ h_inf v w
  -- mixing.1 : b ≤ U =ᴮ v, mixing.2 : bᶜ ≤ U =ᴮ w
  have hm1 : b ≤ U =ᴮ v := mixing.1
  have hm2 : bᶜ ≤ U =ᴮ w := mixing.2
  have h_U_eq_v : U =ᴮ v = v =ᴮ U := bv_eq_symm
  have h_U_eq_w : U =ᴮ w = w =ᴮ U := bv_eq_symm
  have h_phi_U : ϕ U = ⊤ := by
    apply top_unique; rw [← sup_compl_eq_top]; apply sup_le
    · exact (le_inf (hm1.trans (le_of_eq h_U_eq_v)) le_rfl).trans (h_congr v U)
    · exact (le_inf (hm2.trans (le_of_eq h_U_eq_w)) (H_w_eq ▸ le_top)).trans (h_congr w U)
  refine ⟨U, h_phi_U, ?_⟩
  apply le_antisymm
  · -- ϕ v = b ≤ U =ᴮ v
    exact hm1
  · -- U =ᴮ v ≤ ϕ v: from h_congr U v: U =ᴮ v ⊓ ϕ U ≤ ϕ v, ϕ U = ⊤
    have := h_congr U v; rw [h_phi_U, inf_top_eq] at this; exact this

-- src/bvm.lean:1229
private lemma core_aux_lemma2 (ϕ ψ : bSet 𝔹 → 𝔹) (h_congrϕ : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y)
    (h_congrψ : ∀ x y, x =ᴮ y ⊓ ψ x ≤ ψ y) (h_sub : ∀ u, ϕ u = ⊤ → ψ u = ⊤)
    (h_definite : (⨆ (w : bSet 𝔹), ϕ w) = ⊤) :
    (⨅ (x : bSet 𝔹), ϕ x ⟹ ψ x) = ⊤ := by
  apply top_unique; apply le_iInf; intro x
  rw [← deduction, top_inf_eq]
  obtain ⟨u, h₁, h₂⟩ := core_aux_lemma ϕ h_congrϕ h_definite x
  have hψu : ψ u = ⊤ := h_sub u h₁
  -- ϕ x = u =ᴮ x, so need u =ᴮ x ≤ ψ x
  rw [h₂]
  calc u =ᴮ x
      = u =ᴮ x ⊓ ψ u := by rw [hψu, inf_top_eq]
    _ ≤ ψ x := h_congrψ u x

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
private lemma core.mk_ϕ_inj (u : bSet 𝔹) (x y : bSet 𝔹)
    (h₁ : x ∈ᴮ u = ⊤) (h₂ : y ∈ᴮ u = ⊤) (H : core.mk_ϕ u x = core.mk_ϕ u y) :
    x =ᴮ y = ⊤ := by
  -- H : ∀ a, u.bval a ⊓ x =ᴮ u.func a = u.bval a ⊓ y =ᴮ u.func a
  have H' := congr_fun H  -- H' : ∀ a, core.mk_ϕ u x a = core.mk_ϕ u y a
  simp only [core.mk_ϕ] at H'
  -- H' a : u.bval a ⊓ x =ᴮ u.func a = u.bval a ⊓ y =ᴮ u.func a
  apply top_unique
  -- ⊤ ≤ x =ᴮ y
  -- From h₁: ⊤ ≤ x ∈ u = ⨆ a, u.bval a ⊓ x =ᴮ u.func a
  rw [← h₁, mem_unfold]
  apply iSup_le; intro a
  -- u.bval a ⊓ x =ᴮ u.func a ≤ x =ᴮ y
  -- Chain: ≤ x =ᴮ u.func a ⊓ u.func a =ᴮ y ≤ x =ᴮ y
  calc u.bval a ⊓ x =ᴮ u.func a
      ≤ x =ᴮ u.func a ⊓ u.func a =ᴮ y := by
          apply le_inf inf_le_right
          -- u.bval a ⊓ x =ᴮ u.func a ≤ u.func a =ᴮ y
          calc u.bval a ⊓ x =ᴮ u.func a
              = u.bval a ⊓ y =ᴮ u.func a := H' a
            _ ≤ y =ᴮ u.func a := inf_le_right
            _ = u.func a =ᴮ y := bv_eq_symm
    _ ≤ x =ᴮ y := bv_eq_trans

-- src/bvm.lean:1296


-- src/bvm.lean:1299


-- src/bvm.lean:1301


-- src/bvm.lean:1303
private lemma core.S'_spec (u : bSet 𝔹) (x : core.mk_ϕ u '' Set.univ) :
    core.mk_ϕ u (core.S' u x) = x.val :=
  (fiber_lift' (core.mk_ϕ u) x).2

-- src/bvm.lean:1306


-- src/bvm.lean:1309


-- src/bvm.lean:1320


-- src/bvm.lean:1331


-- src/bvm.lean:1334


-- src/bvm.lean:1337
private lemma core.mk (u : bSet 𝔹) : ∃ α : Type u, ∃ S : α → bSet 𝔹, core u S := by
  -- α = Quotient (core.S''_setoid u), S = core.mk_aux u
  refine ⟨Quotient (@core.S''_setoid 𝔹 _ u), core.mk_aux u, ?_, ?_⟩
  · -- Part 1: ∀ x, core.mk_aux u x ∈ u = ⊤
    intro x
    -- core.mk_aux u x = core.S'' u (Quotient.out x)
    -- Quotient.out x : core.α_S'' u, and core.α_S'' u is {i // core.S' u i ∈ u = ⊤}
    exact (Quotient.out x).property
  · -- Part 2: ∀ y, y ∈ u = ⊤ → ∃! x, y =ᴮ core.mk_aux u x = ⊤
    intro y H_y
    -- y' = core.S' u (image_mk y), which is a bSet with the same mk_ϕ as y
    let y' := core.S' u (image_mk y)
    -- core.mk_ϕ u y = core.mk_ϕ u y'  (by core.S'_spec)
    have H_y' : core.mk_ϕ u y = core.mk_ϕ u y' := (core.S'_spec u (image_mk y)).symm
    -- y' ∈ u = ⊤: since mk_ϕ u y = mk_ϕ u y', y ∈ u ⟺ y' ∈ u
    have H_y'2 : y' ∈ᴮ u = ⊤ := by
      simp only [mem_unfold]
      apply top_unique
      rw [← H_y, mem_unfold]
      apply iSup_le; intro a
      -- u.bval a ⊓ y =ᴮ u.func a = u.bval a ⊓ y' =ᴮ u.func a (from H_y')
      have := congr_fun H_y' a
      simp only [core.mk_ϕ] at this
      rw [this]; exact le_iSup (fun i => u.bval i ⊓ y' =ᴮ u.func i) a
    -- Package y' as an element of core.α_S''
    let y_q : core.α_S'' u := ⟨image_mk y, H_y'2⟩
    -- y'' = core.mk_aux u ⟦y_q⟧
    let y'' := core.mk_aux u ⟦y_q⟧
    -- y'' =ᴮ y' = ⊤: from Quotient.mk_out applied to y_q
    have H_y'' : y'' =ᴮ y' = ⊤ := by
      -- Quotient.mk_out y_q : (core.S''_setoid u).r (⟦y_q⟧.out) y_q
      -- i.e., pullback_eq_rel (core.S'' u) core.bv_eq_top (⟦y_q⟧.out) y_q
      -- i.e., core.S'' u (⟦y_q⟧.out) =ᴮ core.S'' u y_q = ⊤
      -- i.e., core.mk_aux u ⟦y_q⟧ =ᴮ y' = ⊤
      exact Quotient.mk_out y_q
    -- y =ᴮ y' = ⊤: from core.mk_ϕ_inj using H_y'
    have H₃ : y =ᴮ y' = ⊤ := core.mk_ϕ_inj u y y' H_y H_y'2 H_y'
    -- y =ᴮ y'' = ⊤: chain through y'
    have H₁ : y =ᴮ y'' = ⊤ := by
      apply top_unique
      calc (⊤ : 𝔹) ≤ y =ᴮ y' ⊓ y' =ᴮ y'' := by
              rw [H₃, show y' =ᴮ y'' = ⊤ from by rw [bv_eq_symm]; exact H_y'']; simp
        _ ≤ y =ᴮ y'' := bv_eq_trans
    -- Existence: use ⟦y_q⟧ as the witness
    refine ⟨⟦y_q⟧, H₁, ?_⟩
    -- Uniqueness: if y =ᴮ core.mk_aux u i = ⊤, then i = ⟦y_q⟧
    intro i H_y'''
    -- Show core.mk_aux u i =ᴮ y' = ⊤
    suffices h : core.mk_aux u i =ᴮ y' = ⊤ by
      -- Then core.mk_aux u i =ᴮ y'' = ⊤ (chain through y')
      have hiy'' : core.mk_aux u i =ᴮ y'' = ⊤ := by
        apply top_unique
        calc (⊤ : 𝔹) ≤ core.mk_aux u i =ᴮ y' ⊓ y' =ᴮ y'' := by
                rw [h, show y' =ᴮ y'' = ⊤ from by rw [bv_eq_symm]; exact H_y'']; simp
          _ ≤ core.mk_aux u i =ᴮ y'' := bv_eq_trans
      -- Now: core.S'' u (Quotient.out i) =ᴮ core.S'' u (Quotient.out ⟦y_q⟧) = ⊤
      -- This means (core.S''_setoid u).r (Quotient.out i) (Quotient.out ⟦y_q⟧)
      -- So ⟦Quotient.out i⟧ = ⟦Quotient.out ⟦y_q⟧⟧ (by Quotient.sound)
      -- And i = ⟦Quotient.out ⟦y_q⟧⟧ = ⟦y_q⟧ (by Quotient.out_eq)
      have hrel : (core.S''_setoid u).r
          (@Quotient.out _ (core.S''_setoid u) i)
          (@Quotient.out _ (core.S''_setoid u) ⟦y_q⟧) := by
        -- goal unfolds to: core.S'' u (Quotient.out i) =ᴮ core.S'' u (Quotient.out ⟦y_q⟧) = ⊤
        -- i.e., core.mk_aux u i =ᴮ y'' = ⊤, which is hiy''
        show core.bv_eq_top (core.S'' u _) (core.S'' u _)
        simp only [core.bv_eq_top, core.S'', core.mk_aux] at hiy'' ⊢
        exact hiy''
      have heq : ⟦(@Quotient.out _ (core.S''_setoid u) i)⟧ =
                 ⟦(@Quotient.out _ (core.S''_setoid u) ⟦y_q⟧)⟧ :=
        Quotient.sound hrel
      rw [Quotient.out_eq, Quotient.out_eq] at heq
      exact heq
    -- Prove core.mk_aux u i =ᴮ y' = ⊤
    apply top_unique
    rw [show (⊤ : 𝔹) = core.mk_aux u i =ᴮ y ⊓ y =ᴮ y' by
      rw [show core.mk_aux u i =ᴮ y = ⊤ by rw [bv_eq_symm]; exact H_y''', H₃]; simp]
    exact bv_eq_trans

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
private lemma subset'_unfold {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} {a₁ a₂ : α} :
    subset' h a₁ a₂ ↔ S a₁ ⊆ᴮ S a₂ = ⊤ := Iff.rfl

-- src/bvm.lean:1430


-- src/bvm.lean:1432


-- src/bvm.lean:1435


-- src/bvm.lean:1438


-- src/bvm.lean:1443


-- src/bvm.lean:1450


-- src/bvm.lean:1459
private lemma core_aux_lemma3 (u : bSet 𝔹) (h_nonempty : (u =ᴮ ∅)ᶜ = ⊤) {α : Type u} (S : α → bSet 𝔹)
    (h_core : core u S) : ∀ x, ∃ y ∈ S '' Set.univ, x =ᴮ y = x ∈ᴮ u := by
  intro x
  -- Apply core_aux_lemma with ϕ = (· ∈ u)
  have h_congr : ∀ a b : bSet 𝔹, a =ᴮ b ⊓ a ∈ᴮ u ≤ b ∈ᴮ u :=
    fun a b => subst_congr_mem_left
  have h_definite : (⨆ (w : bSet 𝔹), w ∈ᴮ u) = ⊤ :=
    top_unique (le_trans (h_nonempty ▸ le_rfl) (exists_mem_of_nonempty u le_rfl))
  obtain ⟨y, h₁, h₂⟩ := core_aux_lemma (fun z => z ∈ᴮ u) h_congr h_definite x
  -- y ∈ u = ⊤, x ∈ u = y =ᴮ x
  -- Use h_core to find y' : α with y =ᴮ S y' = ⊤
  obtain ⟨y', H_y'_eq, -⟩ := h_core.2 y h₁
  -- Return S y'
  refine ⟨S y', Set.mem_image_of_mem _ (Set.mem_univ _), ?_⟩
  -- Show x =ᴮ S y' = x ∈ u
  -- From h₂: x ∈ u = y =ᴮ x
  -- From H_y'_eq: y =ᴮ S y' = ⊤, so bv_rw gives x =ᴮ S y' = x =ᴮ y
  -- And bv_eq_symm gives x =ᴮ y = y =ᴮ x
  -- So x =ᴮ S y' = y =ᴮ x = x ∈ u
  have h_rw : x =ᴮ S y' = x =ᴮ y := by
    apply bv_rw H_y'_eq (fun z => x =ᴮ z)
    intro a b
    rw [inf_comm]; exact bv_eq_trans
  rw [h_rw, bv_eq_symm, h₂]

-- src/bvm.lean:1470
private lemma core_mem_of_mem_image {u y : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h_core : core u S) :
    y ∈ S '' Set.univ → y ∈ᴮ u = ⊤ := by
  rintro ⟨a, -, rfl⟩
  exact h_core.1 a

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






/-- For every x ∈ u, x ⊆ᴮ ⋃ u. -/
-- src/bvm.lean:1915
private lemma bv_union_spec'' (u : bSet 𝔹) : ⊤ ≤ ⨅ (x : bSet 𝔹), (x ∈ᴮ u) ⟹ (x ⊆ᴮ bv_union u) := by
  apply le_iInf; intro x
  rw [← deduction, top_inf_eq, subset_unfold']
  apply le_iInf; intro v
  rw [← deduction]
  -- goal: x ∈ u ⊓ v ∈ x ≤ v ∈ bv_union u
  rw [bv_union_spec_split]
  -- goal: x ∈ u ⊓ v ∈ x ≤ ⨆ y, y ∈ u ⊓ v ∈ y
  exact le_iSup_of_le x (le_inf inf_le_left inf_le_right)





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

private lemma B_ext_subset_or_subset_left (y : bSet 𝔹) : B_ext (fun x => x ⊆ᴮ y ⊔ y ⊆ᴮ x) :=
  B_ext_sup (h₁ := B_ext_subset_left) (h₂ := B_ext_subset_right (x := y))
private lemma B_ext_subset_or_subset_right (x : bSet 𝔹) : B_ext (fun y => x ⊆ᴮ y ⊔ y ⊆ᴮ x) :=
  B_ext_sup (h₁ := B_ext_subset_right (x := x)) (h₂ := B_ext_subset_left (y := x))

private lemma forall_forall_reindex (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h₁ : ∀ x, B_ext (fun y => ϕ x y))
    (h₂ : ∀ y, B_ext (fun x => ϕ x y)) (C : bSet 𝔹) :
    (⨅ (i₁ : C.type), (C.bval i₁ ⟹ ⨅ (i₂ : C.type), (C.bval i₂ ⟹ ϕ (C.func i₁) (C.func i₂)))) =
    ⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹), w₁ ∈ᴮ C ⊓ w₂ ∈ᴮ C ⟹ ϕ w₁ w₂ := by
  -- Helper: imp distributes over iInf
  have imp_iInf : ∀ (a : 𝔹) (f : bSet 𝔹 → 𝔹), (a ⟹ ⨅ w, f w) = ⨅ w, a ⟹ f w := by
    intro a f; simp only [imp, sup_iInf_eq]
  -- Step 1: inner bounded_forall (C.func i₁ is fixed)
  simp_rw [fun w₁ => @bounded_forall _ _ C (fun w₂ => ϕ w₁ w₂) (h_congr := fun a b => h₁ w₁ a b)]
  -- LHS = ⨅ i₁, C.bval i₁ ⟹ ⨅ w₂, w₂ ∈ C ⟹ ϕ (C.func i₁) w₂
  -- Step 2: outer bounded_forall
  have h_cong_outer : ∀ (a b : bSet 𝔹), a =ᴮ b ⊓ (⨅ w₂, w₂ ∈ᴮ C ⟹ ϕ a w₂) ≤
      ⨅ w₂, w₂ ∈ᴮ C ⟹ ϕ b w₂ := by
    intro a b; apply le_iInf; intro w₂
    apply le_trans (inf_le_inf_left _ (iInf_le _ w₂))
    rw [← deduction]
    calc (a =ᴮ b ⊓ (w₂ ∈ᴮ C ⟹ ϕ a w₂)) ⊓ w₂ ∈ᴮ C
        ≤ a =ᴮ b ⊓ ((w₂ ∈ᴮ C ⟹ ϕ a w₂) ⊓ w₂ ∈ᴮ C) :=
          le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      _ ≤ a =ᴮ b ⊓ ϕ a w₂ := inf_le_inf_left _ bv_imp_elim
      _ ≤ ϕ b w₂ := h₂ w₂ a b
  rw [@bounded_forall _ _ C (fun w₁ => ⨅ w₂, w₂ ∈ᴮ C ⟹ ϕ w₁ w₂) (h_congr := h_cong_outer)]
  -- LHS = ⨅ w₁, w₁ ∈ C ⟹ ⨅ w₂, w₂ ∈ C ⟹ ϕ w₁ w₂
  -- Step 3: distribute imp and curry
  simp_rw [imp_iInf, curry_uncurry]



private lemma subset'_inductive (X : bSet 𝔹)
    (H : ⊤ ≤ zorn_chain_hyp X)
    {α : Type u} {S : α → bSet 𝔹} (h_core : core X S) :
    haveI := subset'_partial_order h_core
    ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c := by
  haveI hPO := subset'_partial_order h_core
  intro C C_chain
  -- Let C' be the bSet indexed by C with func = S ∘ (coe : C → α), bval = ⊤
  -- Abbreviation for C' = bSet_of_core_set h_core C
  -- C'.type = C, C'.func ⟨i, _⟩ = S i, C'.bval _ = ⊤
  set C' := bSet_of_core_set h_core C with hC'_def
  -- Step 1: C' is internally a chain
  have H_internal_chain : (⊤ : 𝔹) ≤
      ⨅ (i₁ : C'.type), (C'.bval i₁ ⟹
      ⨅ (i₂ : C'.type), (C'.bval i₂ ⟹
        (C'.func i₁ ⊆ᴮ C'.func i₂ ⊔ C'.func i₂ ⊆ᴮ C'.func i₁))) := by
    apply le_iInf; intro ⟨i₁, H₁⟩
    rw [show C'.bval ⟨i₁, H₁⟩ = ⊤ from rfl, top_imp]
    apply le_iInf; intro ⟨i₂, H₂⟩
    rw [show C'.bval ⟨i₂, H₂⟩ = ⊤ from rfl, top_imp]
    show (⊤ : 𝔹) ≤ S i₁ ⊆ᴮ S i₂ ⊔ S i₂ ⊆ᴮ S i₁
    -- From C_chain: either i₁ = i₂, or subset' h_core i₁ i₂ or subset' h_core i₂ i₁
    by_cases heq : i₁ = i₂
    · -- i₁ = i₂: S i₁ ⊆ S i₁ = ⊤ (reflexivity)
      subst heq
      apply le_sup_of_le_left
      exact le_of_eq (subset_self_eq_top (x := S i₁)).symm
    · -- i₁ ≠ i₂: use C_chain
      have hchain := C_chain H₁ H₂ heq
      cases hchain with
      | inl h =>
        apply le_sup_of_le_left
        exact le_of_eq (subset'_unfold.mp h).symm
      | inr h =>
        apply le_sup_of_le_right
        exact le_of_eq (subset'_unfold.mp h).symm
  -- Step 2: C' ⊆ X (as a bSet)
  have H_C'_sub_X : (⊤ : 𝔹) ≤ C' ⊆ᴮ X := by
    rw [hC'_def, subset_unfold]
    apply le_iInf; intro ⟨i, hi⟩
    rw [show (bSet_of_core_set h_core C).bval ⟨i, hi⟩ = ⊤ from rfl, top_imp]
    exact top_le_iff.mpr (h_core.1 i)
  -- Step 3: chain condition in the quantified form
  -- We need the chain condition expressed as:
  -- ⊤ ≤ ⨅ w₁ w₂, w₁ ∈ C' ⊓ w₂ ∈ C' ⟹ (w₁ ⊆ w₂ ⊔ w₂ ⊆ w₁)
  -- Use forall_forall_reindex with the internal chain form
  have H_chain_quant : (⊤ : 𝔹) ≤ ⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
      w₁ ∈ᴮ C' ⊓ w₂ ∈ᴮ C' ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁) := by
    rw [← forall_forall_reindex (fun x y => x ⊆ᴮ y ⊔ y ⊆ᴮ x)
        (h₁ := fun x => B_ext_subset_or_subset_right x)
        (h₂ := fun y => B_ext_subset_or_subset_left y)]
    exact H_internal_chain
  -- Step 4: bv_union C' ∈ X
  have H_internal_ub_mem : (⊤ : 𝔹) ≤ bv_union C' ∈ᴮ X := by
    apply bv_context_apply (le_trans H (iInf_le _ C'))
    exact le_inf H_C'_sub_X H_chain_quant
  -- Step 5: bv_union C' is an upper bound on each element of C'
  have H_internal_ub_spec : ∀ i_w : C,
      (⊤ : 𝔹) ≤ S i_w.val ⊆ᴮ bv_union C' := by
    intro ⟨i_w, H_i_w⟩
    -- S i_w = C'.func ⟨i_w, H_i_w⟩ ∈ C', so it ⊆ bv_union C'
    have hmem : (⊤ : 𝔹) ≤ C'.func ⟨i_w, H_i_w⟩ ∈ᴮ C' :=
      le_trans (le_of_eq (of_core_bval (i := ⟨i_w, H_i_w⟩)).symm)
               (mem_mk' C' ⟨i_w, H_i_w⟩)
    -- Use bv_union_spec'' C' : ⊤ ≤ ⨅ x, x ∈ C' ⟹ x ⊆ bv_union C'
    have hspec : (⊤ : 𝔹) ≤ C'.func ⟨i_w, H_i_w⟩ ∈ᴮ C' ⟹ C'.func ⟨i_w, H_i_w⟩ ⊆ᴮ bv_union C' :=
      (bv_union_spec'' C').trans (iInf_le _ (C'.func ⟨i_w, H_i_w⟩))
    exact le_trans (le_inf hspec hmem) bv_imp_elim
  -- Step 6: get w with bv_union C' =ᴮ S w = ⊤
  have H_ub_mem : bv_union C' ∈ᴮ X = ⊤ := top_unique H_internal_ub_mem
  obtain ⟨w, H_w⟩ := core_witness h_core (bv_union C') H_ub_mem
  -- w is the upper bound
  refine ⟨w, fun x_w' H_x_w' => ?_⟩
  -- Need: subset' h_core x_w' w, i.e., S x_w' ⊆ S w = ⊤
  -- Under hPO, the goal is x_w' ≤ w (i.e., subset' h_core x_w' w)
  show subset' h_core x_w' w
  rw [subset'_unfold]
  apply top_unique
  -- S x_w' ⊆ bv_union C' (from H_internal_ub_spec)
  have h_ub_spec : (⊤ : 𝔹) ≤ S x_w' ⊆ᴮ bv_union C' :=
    H_internal_ub_spec ⟨x_w', H_x_w'⟩
  -- And bv_union C' =ᴮ S w = ⊤, so S x_w' ⊆ S w by subst_congr_subset_right
  calc (⊤ : 𝔹) ≤ S x_w' ⊆ᴮ bv_union C' ⊓ bv_union C' =ᴮ S w :=
          le_inf h_ub_spec (le_of_eq H_w.symm)
    _ ≤ S x_w' ⊆ᴮ S w := subst_congr_subset_right

/-- ∀ x, x ≠ ∅ ∧ ((∀ y, y ⊆ x ∧ ∀ w₁ w₂ ∈ y, w₁ ⊆ w₂ ∨ w₂ ⊆ w₁) → (⋃y) ∈ x)
    → ∃ c ∈ x, ∀ z ∈ x, c ⊆ z → c = z -/
-- src/bvm.lean:2447
private theorem bSet_zorns_lemma (X : bSet 𝔹) (H_nonempty : (X =ᴮ ∅)ᶜ = ⊤)
    (H : ⊤ ≤ zorn_chain_hyp X) :
    ⊤ ≤ ⨆ c, c ∈ᴮ X ⊓ ⨅ z, z ∈ᴮ X ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z) := by
  -- Step 1: Get a core for X
  obtain ⟨α, S, h_core⟩ := core.mk X
  -- Step 2: Apply Zorn's lemma to get a maximal element c
  letI hPO := subset'_partial_order h_core
  have H_zorn := @zorn_le α hPO.toPreorder (subset'_inductive X H h_core)
  obtain ⟨c, H_c⟩ := H_zorn
  -- H_c : IsMax c, i.e., ∀ a, c ≤ a → a ≤ c
  -- Step 3: S c is in X
  have H_c_in_X : S c ∈ᴮ X = ⊤ := h_core.1 c
  -- Auxiliary: for any a with S a ∈ X = ⊤, S c ⊆ S a ≤ S a = S c
  -- This uses the maximality of c to show a ≤ c, then eq_iff_subset_subset
  have aux : ∀ (a : α), S a ∈ᴮ X = ⊤ → S c ⊆ᴮ S a ≤ S a =ᴮ S c := by
    intro a H_a
    -- Let p = S c ⊆ S a, define v = two_term_mixture p pᶜ (...) (S a) (S c)
    set p := S c ⊆ᴮ S a with hp_def
    have h_anti : p ⊓ pᶜ = ⊥ := inf_compl_eq_bot
    have h_partition : p ⊔ pᶜ = ⊤ := sup_compl_eq_top
    set v := two_term_mixture p pᶜ h_anti (S a) (S c) with hv_def
    -- claim_1: v ∈ X = ⊤
    have claim_1 : v ∈ᴮ X = ⊤ :=
      two_term_mixture_mem_top X (S a) (S c) p pᶜ h_anti h_partition H_a H_c_in_X
    -- claim_2: ∃ z : α, v =ᴮ S z = ⊤
    obtain ⟨z, H_z⟩ := core_witness h_core v claim_1
    -- claim_3: ⊤ ≤ S c ⊆ v
    have claim_3 : (⊤ : 𝔹) ≤ S c ⊆ᴮ v :=
      two_term_mixture_subset_top (S a) (S c) p pᶜ h_anti h_partition hp_def
    -- claim_4: c ≤ z (i.e., S c ⊆ S z = ⊤)
    have claim_4 : c ≤ z := by
      show subset' h_core c z
      rw [subset'_unfold]
      apply top_unique
      calc (⊤ : 𝔹) ≤ S c ⊆ᴮ v ⊓ v =ᴮ S z :=
              le_inf claim_3 (le_of_eq H_z.symm)
        _ ≤ S c ⊆ᴮ S z := subst_congr_subset_right
    -- claim_5: S c =ᴮ S z = ⊤ (from maximality: z ≤ c and c ≤ z)
    have claim_5 : S c =ᴮ S z = ⊤ := by
      have hz_le_c : z ≤ c := H_c claim_4
      apply top_unique
      rw [eq_iff_subset_subset]
      apply le_inf
      · -- S c ⊆ S z = ⊤: from claim_4
        exact le_of_eq (subset'_unfold.mp claim_4).symm
      · -- S z ⊆ S c = ⊤: from hz_le_c
        exact le_of_eq (subset'_unfold.mp hz_le_c).symm
    -- claim_6: ⊤ ≤ v =ᴮ S c (from H_z and claim_5)
    have hSz_eq_Sc : S z =ᴮ S c = ⊤ := by rw [bv_eq_symm]; exact claim_5
    have claim_6 : (⊤ : 𝔹) ≤ v =ᴮ S c := by
      calc (⊤ : 𝔹) ≤ v =ᴮ S z ⊓ S z =ᴮ S c :=
              le_inf (le_of_eq H_z.symm) (le_of_eq hSz_eq_Sc.symm)
        _ ≤ v =ᴮ S c := bv_eq_trans
    -- Now: p = S c ⊆ S a ≤ S a = S c
    -- mixing gives: p ≤ v =ᴮ S a
    have mixing := mixing_lemma_two_term p pᶜ h_anti (S a) (S c)
    -- p ≤ v =ᴮ S a ≤ S a =ᴮ v ≤ S a =ᴮ S c
    calc p ≤ v =ᴮ S a := mixing.1
      _ = S a =ᴮ v := bv_eq_symm
      _ ≤ S a =ᴮ S c := by
          calc S a =ᴮ v ≤ S a =ᴮ v ⊓ v =ᴮ S c :=
                  le_inf le_rfl (le_top.trans claim_6)
            _ ≤ S a =ᴮ S c := bv_eq_trans
  -- Step 4: provide S c as the witness for the iSup
  apply bv_use (S c)
  rw [H_c_in_X, top_inf_eq]
  -- Step 5: prove ⨅ z, z ∈ X ⟹ (S c ⊆ z ⟹ S c = z)
  apply le_iInf; intro x
  rw [← deduction, top_inf_eq, ← deduction]
  -- Goal: x ∈ X ⊓ S c ⊆ x ≤ S c = x
  -- Use core_aux_lemma3 to get S a with x = S a = x ∈ X
  obtain ⟨y, H₁_y, H₂_y⟩ := core_aux_lemma3 X H_nonempty S h_core x
  obtain ⟨a, -, rfl⟩ := H₁_y  -- y = S a
  -- H₂_y : x = S a = x ∈ X (so x ∈ X ≤ x = S a and x = S a ≤ x ∈ X)
  -- Key: we need x ∈ X ⊓ S c ⊆ x ≤ S c = x
  -- Strategy:
  -- (1) x ∈ X ⊓ S c ⊆ x ≤ (x = S a) ⊓ (S a = S c)
  --     Left: x ∈ X ≤ x = S a (from H₂_y.symm)
  --     Right: S c ⊆ x ⊓ x = S a ≤ S c ⊆ S a (subst_congr_subset_right) ≤ S a = S c (aux)
  -- (2) (x = S a) ⊓ (S a = S c) ≤ x = S c ≤ S c = x
  have H₂_y_le : x ∈ᴮ X ≤ x =ᴮ S a := le_of_eq H₂_y.symm
  have h_Sc_sub_Sa : x ∈ᴮ X ⊓ S c ⊆ᴮ x ≤ S c ⊆ᴮ S a :=
    calc x ∈ᴮ X ⊓ S c ⊆ᴮ x
        ≤ x =ᴮ S a ⊓ S c ⊆ᴮ x :=
            le_inf (inf_le_left.trans H₂_y_le) inf_le_right
      _ ≤ S c ⊆ᴮ S a := by
            rw [inf_comm]; exact subst_congr_subset_right
  have h_Sa_eq_Sc : S c ⊆ᴮ S a ≤ S a =ᴮ S c :=
    aux a (core_mem_of_mem_image h_core ⟨a, Set.mem_univ _, rfl⟩)
  calc x ∈ᴮ X ⊓ S c ⊆ᴮ x
      ≤ x =ᴮ S a ⊓ S a =ᴮ S c := by
          apply le_inf
          · exact inf_le_left.trans H₂_y_le
          · exact h_Sc_sub_Sa.trans h_Sa_eq_Sc
    _ ≤ x =ᴮ S c := bv_eq_trans
    _ = S c =ᴮ x := bv_eq_symm

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
private theorem bSet_zorns_lemma' {Γ : 𝔹} :
    Γ ≤ ⨅ (X : bSet 𝔹), (X =ᴮ ∅)ᶜ ⟹
      ((⨅ y, (y ⊆ᴮ X ⊓ (⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
          w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ bv_union y ∈ᴮ X) ⟹
        (⨆ c, c ∈ᴮ X ⊓ (⨅ z, z ∈ᴮ X ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z)))) := by
  apply le_iInf; intro X
  rw [← curry_uncurry]
  suffices h : (⨅ (Y : bSet 𝔹), ((Y =ᴮ ∅)ᶜ ⊓ ⨅ y, (y ⊆ᴮ Y ⊓
      (⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
        w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ bv_union y ∈ᴮ Y) ⟹
    (⨆ c, c ∈ᴮ Y ⊓ (⨅ z, z ∈ᴮ Y ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z)))) = ⊤ by
    exact le_top.trans (h ▸ iInf_le _ X)
  apply core_aux_lemma2
  · exact B_ext_inf (h₁ := B_ext_neg (h := B_ext_bv_eq_left))
      (h₂ := B_ext_iInf (h := fun y => B_ext_imp
        (h₁ := B_ext_inf B_ext_subset_right B_ext_const)
        (h₂ := B_ext_mem_right)))
  · exact B_ext_iSup (h := fun c => B_ext_inf (h₁ := B_ext_mem_right)
      (h₂ := B_ext_iInf (h := fun z => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
  · intro u hu
    have h_nonempty : (u =ᴮ ∅)ᶜ = ⊤ := top_unique (hu ▸ inf_le_left)
    have h_chain : (⊤ : 𝔹) ≤ ⨅ y, (y ⊆ᴮ u ⊓
        (⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
          w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ bv_union y ∈ᴮ u :=
      hu ▸ inf_le_right
    exact top_unique (bSet_zorns_lemma u h_nonempty h_chain)
  · apply top_unique; apply le_iSup_of_le ({∅} : bSet 𝔹)
    apply le_inf
    · apply nonempty_of_exists_mem; apply le_iSup_of_le (∅ : bSet 𝔹)
      have hmem : (∅ : bSet 𝔹) ∈ᴮ ({∅} : bSet 𝔹) = ⊤ := by
        simp [mem_singleton_bSet, bv_eq_refl]
      exact le_of_eq hmem.symm
    · apply le_iInf; intro y; apply bv_imp_intro_lemma; rw [top_inf_eq]
      simp only [mem_singleton_bSet]
      apply le_sup_of_le_left
      rw [eq_iff_subset_subset]
      apply le_inf
      · -- Goal: ctx ≤ bv_union y ⊆ᴮ ∅
        -- Rewrite via the propositional equality from subset_unfold'
        rw [show bv_union y ⊆ᴮ (∅ : bSet 𝔹) = ⨅ w : bSet 𝔹, w ∈ᴮ bv_union y ⟹ w ∈ᴮ ∅
              from subset_unfold']
        apply le_iInf; intro w; apply bv_imp_intro_lemma
        -- goal: ctx ⊓ w ∈ bv_union y ≤ w ∈ ∅, w : bSet 𝔹
        -- Step 1: from bv_union_spec_split, w ∈ bv_union y ↔ ⨆ z, z ∈ y ⊓ w ∈ z
        -- Then use y ⊆ {∅} to show z = ∅, then w ∈ z = w ∈ ∅ = ⊥
        apply le_trans (b := y ⊆ᴮ ({∅} : bSet 𝔹) ⊓ ⨆ z, z ∈ᴮ y ⊓ w ∈ᴮ z)
        · exact le_inf (inf_le_left.trans inf_le_left) ((bv_union_spec_split y w).mp inf_le_right)
        · rw [inf_iSup_eq']; apply iSup_le; intro z
          -- goal: y ⊆ {∅} ⊓ (z ∈ y ⊓ w ∈ z) ≤ w ∈ ∅
          -- First: z ∈ y ⊓ y ⊆ {∅} ≤ z ∈ {∅} = z =ᴮ ∅ ⊔ z ∈ ∅
          have hz_sing : y ⊆ᴮ ({∅} : bSet 𝔹) ⊓ (z ∈ᴮ y ⊓ w ∈ᴮ z) ≤ z ∈ᴮ ({∅} : bSet 𝔹) :=
            mem_of_mem_subset inf_le_left (inf_le_right.trans inf_le_left)
          -- Second: z ∈ {∅} simplifies to z =ᴮ ∅ ⊔ z ∈ ∅
          have hz_eq : y ⊆ᴮ ({∅} : bSet 𝔹) ⊓ (z ∈ᴮ y ⊓ w ∈ᴮ z) ≤ z =ᴮ (∅ : bSet 𝔹) := by
            have hh := hz_sing; simp only [mem_singleton_bSet] at hh
            have hbot_z : z ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by
              rw [mem_unfold]; exact exists_over_empty _
            simpa only [hbot_z, sup_bot_eq] using hh
          -- Third: use bv_rw' to substitute z =ᴮ ∅ into w ∈ z giving w ∈ ∅
          exact bv_rw' (H := bv_symm hz_eq)
            (h_congr := B_ext_mem_right) (H_new := inf_le_right.trans inf_le_right)
      · exact le_trans le_top empty_subset

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


private lemma bSet_models_emptyset : ⊤ ⊩[V β] axiom_of_emptyset := by
  change ⊤ ≤ _
  simp only [axiom_of_emptyset, boolean_realize_sentence_all,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula,
             V_eq, boolean_realize_bounded_term_emptyset']
  exact le_iInf (fun x => empty_spec)

-- axiom of ordered pairs: ∀ x y z w, pair(x,y) = pair(z,w) ↔ x=z ∧ y=w


private lemma bSet_models_ordered_pairs : ⊤ ⊩[V β] axiom_of_ordered_pairs := by
  change ⊤ ≤ _
  simp only [axiom_of_ordered_pairs, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term, DVec.nth, V_eq, V_forall]
  apply le_iInf; intro a; apply le_iInf; intro b; apply le_iInf; intro x; apply le_iInf; intro y
  -- goal: ⊤ ≤ bihimp (pair a b =ᴮ pair x y) (a =ᴮ x ⊓ b =ᴮ y)
  have heq : pair a b =ᴮ pair x y = a =ᴮ x ⊓ b =ᴮ y :=
    le_antisymm (le_inf eq_of_eq_pair_left eq_of_eq_pair_right)
                (pair_congr inf_le_left inf_le_right)
  rw [heq]
  -- Need: ⊤ ≤ bihimp (a =ᴮ x ⊓ b =ᴮ y) (a =ᴮ x ⊓ b =ᴮ y)
  rw [bihimp_self]

-- axiom of extensionality: ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y


private lemma bSet_models_extensionality : ⊤ ⊩[V β] axiom_of_extensionality := by
  change ⊤ ≤ _
  simp only [axiom_of_extensionality, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_eq]
  apply le_iInf; intro x; apply le_iInf; intro y
  -- goal: ⊤ ≤ (⨅ z, bihimp (z ∈ x) (z ∈ y)) ⟹ (x =ᴮ y)
  rw [← _root_.deduction]
  -- goal: ⊤ ⊓ (⨅ z, bihimp (z ∈ x) (z ∈ y)) ≤ x =ᴮ y
  rw [top_inf_eq]
  -- goal: ⨅ z, bihimp (z ∈ x) (z ∈ y) ≤ x =ᴮ y
  apply le_trans ?_ (bSet_axiom_of_extensionality x y)
  apply le_iInf; intro z
  apply le_trans (iInf_le _ z)
  -- bihimp A B = (B ⇨ A) ⊓ (A ⇨ B); imp A B = Aᶜ ⊔ B; himp_eq: A ⇨ B = B ⊔ Aᶜ
  apply le_inf
  · exact le_trans inf_le_right (by simp [himp_eq, imp, sup_comm])
  · exact le_trans inf_le_left (by simp [himp_eq, imp, sup_comm])

-- axiom schema of strong collection (src/zfc.lean:208-211)











-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y


private lemma bSet_models_union : ⊤ ⊩[V β] axiom_of_union := by
  change ⊤ ≤ _
  simp only [axiom_of_union, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_Union', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]
  apply le_iInf; intro u; apply le_iInf; intro x
  -- goal: ⊤ ≤ bihimp (x ∈ bv_union u) (⨆ y, y ∈ u ⊓ x ∈ y)
  have heq : x ∈ᴮ bv_union u = ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y :=
    le_antisymm ((bv_union_spec_split u (Γ := x ∈ᴮ bv_union u) x).mp le_rfl)
                ((bv_union_spec_split u (Γ := ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) x).mpr le_rfl)
  rw [heq, bihimp_self]
-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z


private lemma bSet_models_powerset : ⊤ ⊩[V β] axiom_of_powerset := by
  change ⊤ ≤ _
  simp only [axiom_of_powerset, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_Powerset', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_eq]
  apply le_iInf; intro z; apply le_iInf; intro y
  -- goal: ⊤ ≤ bihimp (y ∈ bv_powerset z) (⨅ x, x ∈ y ⟹ x ∈ z)
  rw [← subset_unfold']
  -- goal: ⊤ ≤ bihimp (y ∈ bv_powerset z) (y ⊆ z)
  have heq : y ∈ᴮ bv_powerset z = y ⊆ᴮ z :=
    le_antisymm (bv_powerset_spec.mpr le_rfl) (bv_powerset_spec.mp le_rfl)
  rw [heq, bihimp_self]
-- axiom of infinity (src/zfc.lean:332-347)



-- axiom of regularity: ∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y


private lemma bSet_models_regularity : ⊤ ⊩[V β] axiom_of_regularity := by
  change ⊤ ≤ _
  simp only [axiom_of_regularity, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_term_emptyset',
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_formula_and, boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]
  apply le_iInf; intro x
  rw [← _root_.deduction]
  -- goal: ⊤ ⊓ (x =ᴮ ∅)ᶜ ≤ ⨆ y, y ∈ x ⊓ (⨅ z, z ∈ x ⟹ (z ∈ y)ᶜ)
  rw [top_inf_eq]
  -- goal: (x =ᴮ ∅)ᶜ ≤ ⨆ y, y ∈ x ⊓ (⨅ z, z ∈ x ⟹ (z ∈ y)ᶜ)
  exact bSet_axiom_of_regularity x le_rfl
-- Zorn's lemma (src/zfc.lean:363-376)


private lemma bSet_models_Zorn : ⊤ ⊩[V β] zorns_lemma := by
  change ⊤ ≤ _
  simp only [zorns_lemma, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_or,
             boolean_realize_bounded_formula_subset', boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term_Union',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq]
  -- After simp, goal should match bSet_zorns_lemma' exactly
  exact bSet_zorns_lemma'
-- ============================================================
-- The ZFC theory (src/zfc.lean:378-399)
-- ============================================================



/-- The fundamental theorem of forcing: bSet β models all of ZFC. -/
private theorem bSet_models_ZFC_cohenProof06 : ⊤ ⊩ₜ[V β] ZFC := by
  simp only [all_forced_in]
  apply le_iInf; intro f; apply le_iInf; intro hf
  simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
             Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and] at hf
  rcases hf with (hf | ⟨n, ϕ, rfl⟩)
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bSet_models_emptyset
    · exact bSet_models_ordered_pairs
    · exact bSet_models_extensionality
    · exact bSet_models_union
    · exact bSet_models_powerset
    · exact bSet_models_infinity
    · exact bSet_models_regularity
    · exact bSet_models_Zorn
  · exact bSet_models_collection _



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
  @Fol.all_forced_in.{1, 0} L_ZFC β (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst)
    (@Top.top.{0} β
      (@BooleanAlgebra.toTop.{0} β
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} β
          (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst))))
    (@V β inst) ZFC :=
  @bSet_models_ZFC_cohenProof06
