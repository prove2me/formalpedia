-- Prove2me | solution 1 for UlmsTheorem.iso_of_ulmInvariant_eq_of_backAndForth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:38.91171+00:00
-- url     : https://prove2.me/submissions/50a53d36-cb84-427c-9537-3634a395ca93

module
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
public import Theorems.Thm_UlmsTheorem_IsHeightPresOn_injective
public import Theorems.Thm_UlmsTheorem_IsHeightPreserving_injective
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


section
@[expose] public section
namespace UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
omit hp in
/-- The partial isomorphisms are compatible across chain stages. -/
private lemma bf_chain_compat
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n)
    (a : (bf_chain p hforth hback enumG enumH m).A) :
    ((bf_chain p hforth hback enumG enumH n).e
      ⟨a.val, bf_chain_A_le p hforth hback enumG enumH hmn a.prop⟩ : H) =
    (bf_chain p hforth hback enumG enumH m).e a := by
  induction hmn with
  | refl => rfl
  | @step n hmn ih =>
    obtain ⟨hle, _, _, _, h⟩ := bf_chain_step_props p hforth hback enumG enumH n
    exact h ⟨a, bf_chain_A_le p hforth hback enumG enumH hmn a.2⟩ ▸ ih
omit hp in
/-- The limit map evaluates consistently at any stage that already covers g. -/
private lemma bf_limit_map_eq_at
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H)
    (g : G) (n : ℕ) (hg : g ∈ (bf_chain p hforth hback enumG enumH n).A) :
    bf_limit_map p hforth hback enumG hG_surj enumH g =
      ((bf_chain p hforth hback enumG enumH n).e ⟨g, hg⟩ : H) := by
  by_cases h : n ≤ (hG_surj g).choose + 1
  · have := bf_chain_compat p hforth hback enumG enumH h ⟨g, hg⟩; aesop
  · have hle : (hG_surj g).choose + 1 ≤ n := by omega
    have hgbase := (bf_chain_step_props (G := G) (H := H) p hforth hback enumG enumH
      (hG_surj g).choose).choose_spec.2.1
    rw [(hG_surj g).choose_spec] at hgbase
    have hcompat := bf_chain_compat p hforth hback enumG enumH hle ⟨g, hgbase⟩
    unfold bf_limit_map
    exact hcompat.symm
omit hp in
/-- The limit map is additive. -/
private lemma bf_limit_map_add
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H)
    (g₁ g₂ : G) :
    bf_limit_map p hforth hback enumG hG_surj enumH (g₁ + g₂) =
    bf_limit_map p hforth hback enumG hG_surj enumH g₁ +
    bf_limit_map p hforth hback enumG hG_surj enumH g₂ := by
  obtain ⟨n₁, hn₁⟩ := hG_surj g₁
  obtain ⟨n₂, hn₂⟩ := hG_surj g₂
  set N := Nat.max (n₁ + 1) (n₂ + 1)
  have hg₁ : g₁ ∈ (bf_chain p hforth hback enumG enumH N).A := by
    have hg₁' : g₁ ∈ (bf_chain p hforth hback enumG enumH (n₁ + 1)).A := by
      have := bf_chain_step_props p hforth hback enumG enumH n₁; grind +ring
    exact bf_chain_A_le p hforth hback enumG enumH (Nat.le_max_left _ _) hg₁'
  have hg₂ : g₂ ∈ (bf_chain p hforth hback enumG enumH N).A := by
    have := bf_chain_step_props p hforth hback enumG enumH n₂
    have henum := this.2.2.1
    rw [hn₂] at henum
    exact bf_chain_A_le p hforth hback enumG enumH
      (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)))
      henum
  have hg₁g₂ : g₁ + g₂ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    AddSubgroup.add_mem _ hg₁ hg₂
  set eN := (bf_chain p hforth hback enumG enumH N).e
  rw [bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₁ N hg₁,
      bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₂ N hg₂,
      bf_limit_map_eq_at p hforth hback enumG hG_surj enumH (g₁ + g₂) N hg₁g₂]
  exact eN.map_add ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ ▸ rfl
omit hp in
/-- The limit map is injective. -/
private lemma bf_limit_map_injective
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H) :
    Function.Injective (bf_limit_map p hforth hback enumG hG_surj enumH) := by
  intro g₁ g₂ h_eq
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, g₁ ∈ (bf_chain p hforth hback enumG enumH (n₁ + 1)).A := by
    obtain ⟨n₁, hn₁⟩ := hG_surj g₁
    exact ⟨n₁, by have := bf_chain_step_props p hforth hback enumG enumH n₁; aesop⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n₂, g₂ ∈ (bf_chain p hforth hback enumG enumH (n₂ + 1)).A := by
    obtain ⟨n₂, rfl⟩ := hG_surj g₂
    exact ⟨n₂, (bf_chain_step_props p hforth hback enumG enumH n₂).choose_spec.2.1⟩
  set N := max n₁ n₂ + 1
  have hN₁ : g₁ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    bf_chain_A_le p hforth hback enumG enumH (by omega) hn₁
  have hN₂ : g₂ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    bf_chain_A_le p hforth hback enumG enumH (Nat.succ_le_succ (le_max_right _ _)) hn₂
  have h_eq_N :
      ((bf_chain p hforth hback enumG enumH N).e ⟨g₁, hN₁⟩ : H) =
      ((bf_chain p hforth hback enumG enumH N).e ⟨g₂, hN₂⟩ : H) := by
    rw [← bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₁ N hN₁,
        ← bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₂ N hN₂, h_eq]
  exact congrArg Subtype.val
    ((bf_chain p hforth hback enumG enumH N).e.injective (Subtype.ext h_eq_N))
omit hp in
/-- The limit map is surjective. -/
private lemma bf_limit_map_surjective
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG)
    (enumH : ℕ → H) (hH_surj : Function.Surjective enumH) :
    Function.Surjective (bf_limit_map p hforth hback enumG hG_surj enumH) := by
  intro h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, h ∈ (bf_chain p hforth hback enumG enumH n).B := by
    obtain ⟨n, rfl⟩ := hH_surj h
    exact ⟨n + 1, by
      simpa using (bf_chain_step_props p hforth hback enumG enumH n).choose_spec.2.2.1⟩
  let a := (bf_chain p hforth hback enumG enumH n).e.symm ⟨h, hn⟩
  use a.val
  have ha : (bf_chain p hforth hback enumG enumH n).e a = ⟨h, hn⟩ := by simp [a]
  rw [bf_limit_map_eq_at p hforth hback enumG hG_surj enumH a.val n a.prop]
  exact congrArg Subtype.val ha
end UlmsTheorem
end
end

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
omit hp
namespace UlmsTheorem
theorem _root_.solution
    [Countable G] [Countable H]
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H)) :
    Nonempty (G ≃+ H) := by
  obtain ⟨enumG, hG_surj⟩ := exists_surjective_nat G
  obtain ⟨enumH, hH_surj⟩ := exists_surjective_nat H
  have h_bij : Function.Bijective (bf_limit_map p hforth hback enumG hG_surj enumH) :=
    ⟨bf_limit_map_injective p hforth hback enumG hG_surj enumH,
     bf_limit_map_surjective p hforth hback enumG hG_surj enumH hH_surj⟩
  exact ⟨{ Equiv.ofBijective _ h_bij with
             map_add' := fun x y ↦ by
               simpa using bf_limit_map_add p hforth hback enumG hG_surj enumH x y }⟩
end UlmsTheorem
