-- Prove2me | solution 1 for TwoBQO.lexSigmaQO_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:50.923347+00:00
-- url     : https://prove2.me/submissions/8c0fdac7-d1de-40f6-8be9-9055de0c7bf0

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
public import Theorems.Thm_PairSeq_perfect_or_bad

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
namespace TwoBQO
theorem _root_.solution {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) (f : PairSeq (Σ i, s i))
    (hf_bad : PairSeq.IsBad (TwoBQO.LexSumRelQO r s t) f) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      PairSeq.IsBad r (fun m n hmn => (f (e m) (e n) (he_mono hmn)).1) ∨
      ∃ (i : ι) (hmem : ∀ m n (hmn : m < n), (f (e m) (e n) (he_mono hmn)).1 = i),
        PairSeq.IsBad (t i) fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he_mono hmn)).2 := by
  let f₁ : PairSeq ι := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad₁⟩ := PairSeq.perfect_or_bad r f₁
  · by_cases hconst : ∀ m n l : ℕ, (hmn : m < n) → (hnl : n < l) →
        (f (e m) (e n) (he hmn)).1 = (f (e n) (e l) (he hnl)).1
    · set c := (f (e 0) (e 1) (he (by norm_num : (0 : ℕ) < 1))).1
      have hmem : ∀ m n : ℕ, (hmn : m < n) → (f (e m) (e n) (he hmn)).1 = c := by
        have hsucc : ∀ n : ℕ, (f (e n) (e (n + 1)) (he (Nat.lt_succ_self n))).1 = c := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            exact (hconst n (n + 1) (n + 2) (Nat.lt_succ_self n)
              (Nat.lt_succ_self (n + 1))).symm.trans ih
        intro m n hmn
        exact (hconst m n (n + 1) hmn (Nat.lt_succ_self n)).trans (hsucc n)
      let g : PairSeq (s c) := fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he hmn)).2
      have hg_bad : PairSeq.IsBad (t c) g := by
        intro m n l hmn hnl htrel
        apply hf_bad (e m) (e n) (e l) (he hmn) (he hnl)
        set σ_mn := f (e m) (e n) (he hmn) with hσ_mn
        set σ_nl := f (e n) (e l) (he hnl) with hσ_nl
        have h_mn : σ_mn.1 = c := hmem m n hmn
        have h_nl : σ_nl.1 = c := hmem n l hnl
        rw [show σ_mn = ⟨c, h_mn ▸ σ_mn.2⟩ from by ext <;> simp [h_mn]]
        rw [show σ_nl = ⟨c, h_nl ▸ σ_nl.2⟩ from by ext <;> simp [h_nl]]
        exact Or.inr ⟨rfl, htrel⟩
      exact ⟨e, he, Or.inr ⟨c, hmem, hg_bad⟩⟩
    · exfalso
      push Not at hconst
      obtain ⟨m, n, l, hmn, hnl, hne⟩ := hconst
      exact hf_bad (e m) (e n) (e l) (he hmn) (he hnl) (Or.inl ⟨hperf m n l hmn hnl, hne⟩)
  · exact ⟨e, he, Or.inl hbad₁⟩
end TwoBQO
