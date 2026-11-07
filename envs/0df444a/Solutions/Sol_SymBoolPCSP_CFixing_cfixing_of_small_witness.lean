-- Prove2me | solution 1 for SymBoolPCSP.CFixing.cfixing_of_small_witness
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:08:38.098177+00:00
-- url     : https://prove2.me/submissions/946555cf-67ae-4d22-a3a3-b09139c8cf4d

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_cfixing_of_small_witness

theorem indicator_filter {L : ℕ} (x : Fin L → Bool) :
    x = indicator (Finset.univ.filter (fun i => x i = true)) := by
  funext i; simp [indicator]

end Aux_cfixing_of_small_witness

open Aux_cfixing_of_small_witness in
/-- A generic `C`-fixing criterion (BG, proof of Lemma 4.12, Case 2): suppose `f(0) = 0`,
every `X` with `f(e_X) = 1` contains some `T` with `f(e_T) = 1` and `|T| ≤ B`, and at most `c`
pairwise disjoint sets `S_i` can have `f(e_{S_i}) = 1`. Then `f` is `(c + 1) B`-fixing. -/
theorem cfixing_of_small_witness {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (B c : ℕ)
    (hsmall : ∀ X : Finset (Fin L), f (indicator X) = true →
      ∃ T ⊆ X, f (indicator T) = true ∧ T.card ≤ B)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    IsCFixing ((c + 1) * B) f := by
  classical
  have key : ∀ n : ℕ, (∃ U : Finset (Fin L), U.card ≤ n * B ∧
      ∀ X : Finset (Fin L), Disjoint X U → f (indicator X) = false) ∨
      (∃ S : Fin n → Finset (Fin L), (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
        (∀ i, f (indicator (S i)) = true) ∧ ∀ i, (S i).card ≤ B) := by
    intro n
    induction n with
    | zero => exact Or.inr ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩
    | succ n ih =>
      rcases ih with ⟨U, hU, hX⟩ | ⟨S, hdis, htrue, hcard⟩
      · exact Or.inl ⟨U, le_trans hU (Nat.mul_le_mul_right _ (Nat.le_succ n)), hX⟩
      · by_cases hall : ∀ X : Finset (Fin L), Disjoint X (Finset.univ.biUnion S) →
            f (indicator X) = false
        · refine Or.inl ⟨Finset.univ.biUnion S, ?_, hall⟩
          calc (Finset.univ.biUnion S).card ≤ ∑ i, (S i).card := Finset.card_biUnion_le
            _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hcard i)
            _ = n * B := by simp
            _ ≤ (n + 1) * B := Nat.mul_le_mul_right _ (Nat.le_succ n)
        · push_neg at hall
          obtain ⟨X, hXd, hXt⟩ := hall
          obtain ⟨T, hTX, hTt, hTc⟩ := hsmall X (by simpa using hXt)
          have hTd : ∀ i, Disjoint T (S i) := fun i =>
            Finset.disjoint_of_subset_left hTX (Finset.disjoint_of_subset_right
              (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)) hXd)
          refine Or.inr ⟨Fin.cons T S, ?_, ?_, ?_⟩
          · intro i j hij
            induction i using Fin.cases with
            | zero =>
              induction j using Fin.cases with
              | zero => exact absurd rfl hij
              | succ j => simpa using hTd j
            | succ i =>
              induction j using Fin.cases with
              | zero => simpa using (hTd i).symm
              | succ j =>
                simpa using hdis i j (fun h' => hij (by rw [h']))
          · intro i
            induction i using Fin.cases with
            | zero => simpa using hTt
            | succ i => simpa using htrue i
          · intro i
            induction i using Fin.cases with
            | zero => simpa using hTc
            | succ i => simpa using hcard i
  rcases key (c + 1) with ⟨U, hU, hX⟩ | ⟨S, hdis, htrue, _⟩
  · refine ⟨U, hU, fun x hx => ?_⟩
    rw [h0, indicator_filter x]
    apply hX
    exact Finset.disjoint_left.mpr fun i hi hiU => by
      have := hx i hiU
      simp [this] at hi
  · have := hdisj (c + 1) S hdis htrue
    omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (B c : ℕ)
    (hsmall : ∀ X : Finset (Fin L), f (indicator X) = true →
      ∃ T ⊆ X, f (indicator T) = true ∧ T.card ≤ B)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    IsCFixing ((c + 1) * B) f :=
  SymBoolPCSP.CFixing.cfixing_of_small_witness f h0 B c hsmall hdisj
