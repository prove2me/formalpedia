-- Prove2me | solution 1 for Puder.limsup_sum_ncard_crit_rpow_le_rhoStair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T10:18:05.519236+00:00
-- url     : https://prove2.me/submissions/f1c00497-a890-4e4f-b8cb-d82cc76c8293
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_Puder_limsup_sum_rpow_le_cogrowth
import Theorems.Thm_Puder_limsup_sum_ncard_crit_reduced_rpow_le

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
/-! q218 Blueprint: Puder's extended cogrowth formula (Theorem 4.4) for the Cayley graph of `F_k`,
and the bridge between non-backtracking letter sequences and reduced words. -/
/-- The generator a letter stands for: `inl x ↦ x`, `inr x ↦ x⁻¹`. -/
def gen : Fin k ⊕ Fin k → FreeGroup (Fin k)
  | Sum.inl x => FreeGroup.of x
  | Sum.inr x => (FreeGroup.of x)⁻¹

/-- The endpoint in `F_k` of the walk spelled by a letter sequence. -/
noncomputable def word {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : FreeGroup (Fin k) :=
  StrongConv.wordFree (List.ofFn fun j => some (i j))

/-- Non-backtracking: no letter is followed by its inverse. -/
def NB {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : Prop :=
  ∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap

instance {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : Decidable (NB i) := by
  unfold NB; infer_instance

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog
/-! q218 Part A: the combinatorial lemmas of the Blueprint `Puder.Cog`, proved. -/
/-! ### Helpers -/
theorem word_eq {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    word i = (List.ofFn fun j => gen (i j)).prod := by
  unfold word StrongConv.wordFree
  rw [List.map_ofFn]
  congr 2
  funext j
  simp only [Function.comp]
  rcases i j with x | x <;> rfl

/-! ### The five Blueprint lemmas -/

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
/-! ## Part A: combinatorics (stubs) -/

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog
/-- The letter as a generator-with-sign pair. -/
def toP {k : ℕ} : Fin k ⊕ Fin k → Fin k × Bool
  | Sum.inl x => (x, true)
  | Sum.inr x => (x, false)

theorem gen_eq_mk {k : ℕ} (a : Fin k ⊕ Fin k) : gen a = FreeGroup.mk [toP a] := by
  rcases a with x | x
  · rfl
  · simp [gen, toP, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

theorem prod_map_gen {k : ℕ} (l : List (Fin k ⊕ Fin k)) :
    (l.map gen).prod = FreeGroup.mk (l.map toP) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, gen_eq_mk, FreeGroup.mul_mk]
    rfl

theorem word_eq_mk {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    word i = FreeGroup.mk (List.ofFn fun j => toP (i j)) := by
  rw [word_eq]
  have h1 : (List.ofFn fun j => gen (i j)) = (List.ofFn i).map gen := by
    rw [List.map_ofFn]; rfl
  have h2 : (List.ofFn fun j => toP (i j)) = (List.ofFn i).map toP := by
    rw [List.map_ofFn]; rfl
  rw [h1, h2, prod_map_gen]

theorem toP_rel {k : ℕ} (a b : Fin k ⊕ Fin k) :
    ((toP a).1 = (toP b).1 → (toP a).2 = (toP b).2) ↔ b ≠ a.swap := by
  rcases a with x | x <;> rcases b with y | y <;> simp [toP, eq_comm]

theorem NB_iff_isReduced {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    NB i ↔ FreeGroup.IsReduced (List.ofFn fun j => toP (i j)) := by
  rw [FreeGroup.IsReduced, List.isChain_ofFn]
  simp only [toP_rel, NB]
  constructor
  · intro H j hj
    exact H ⟨j, by omega⟩ hj
  · intro H j hj
    exact H j hj

theorem NB_iff_length {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    NB i ↔ (word i).toWord.length = t := by
  rw [NB_iff_isReduced, word_eq_mk, FreeGroup.toWord_mk]
  set M := List.ofFn fun j => toP (i j)
  have hM : M.length = t := by simp [M]
  constructor
  · intro hr
    rw [hr.reduce_eq, hM]
  · intro hl
    by_contra hr
    rw [FreeGroup.isReduced_iff_not_step] at hr
    push Not at hr
    obtain ⟨L₂, hs⟩ := hr
    have e := FreeGroup.reduce.Step.eq hs
    have hle := FreeGroup.Red.length_le (FreeGroup.reduce.red (L := L₂))
    have hst := hs.length
    rw [e] at hl
    omega

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
alias NB_iff_length := Puder.Cog.PartA.NB_iff_length

/-! ## Part B: the potential bound and the theorem (target) -/

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartC
theorem cor45_dev (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) atTop ≤ StrongConv.rhoStair k m := by
  set q : ℝ := 2 * k - 1 with hq
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 < q := by rw [hq]; linarith
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set ρ : ℝ := if (2 * m - 1 : ℝ) ≤ Real.sqrt q then Real.sqrt q else 2 * m - 1 with hρ
  have hρs : Real.sqrt q ≤ ρ := by
    rw [hρ]; split_ifs with h
    · exact le_rfl
    · linarith
  have hρ0 : 0 < ρ := lt_of_lt_of_le hsq hρs
  have hrho : StrongConv.rhoStair k m = ρ + q / ρ := by
    unfold StrongConv.rhoStair
    rw [← hq, hρ]
    split_ifs with h
    · have : q / Real.sqrt q = Real.sqrt q := by
        rw [div_eq_iff hsq.ne', ← sq, hsq2]
      rw [this]; ring
    · rfl
  let f : FreeGroup (Fin k) → ℝ := fun g =>
    if primitivityRank g = m then ((Crit g).ncard : ℝ) else 0
  have hf : ∀ g, 0 ≤ f g := fun g => by
    simp only [f]; split_ifs <;> positivity
  obtain ⟨hB43, hL43⟩ := Puder.limsup_sum_ncard_crit_reduced_rpow_le k m hk hm1 hm
  set ν : ℕ → ℝ := fun t => ∑ i : Fin t → Fin k ⊕ Fin k with
      (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
        primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
      ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ) with hν_def
  have hν0 : ∀ t, 0 ≤ ν t := fun t => Finset.sum_nonneg fun i _ => by positivity
  have hsum : ∀ t, (∑ i : Fin t → Fin k ⊕ Fin k with
      (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
      f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) = ν t := by
    intro t
    simp only [hν_def]
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := Puder.Cog.NB_iff_length i
    simp only [Puder.Cog.NB, Puder.Cog.word] at h
    simp only [f]
    by_cases h1 : ∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap <;>
      by_cases h2 : primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m <;>
      simp_all
  have htarget : (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) = (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) := by
    funext t
    rw [Finset.sum_filter]
  have key : ∀ ε > 0, IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) atTop ≤ ρ + q / ρ + ε := by
    intro ε hε
    set α := ρ + ε with hα
    have hα0 : 0 < α := by linarith
    have hev : ∀ᶠ t in atTop, ν t ^ (1 / (t : ℝ)) < α :=
      eventually_lt_of_limsup_lt (by linarith) hB43
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    set c : ℝ := 1 + ∑ t ∈ Finset.range (max N 1), ν t / α ^ t with hc
    have hν' : ∀ t, ν t ≤ c * α ^ t := by
      intro t
      have hαt : 0 < α ^ t := by positivity
      by_cases ht : t < max N 1
      · have h1 : ν t / α ^ t ≤ ∑ t ∈ Finset.range (max N 1), ν t / α ^ t :=
          Finset.single_le_sum (f := fun t => ν t / α ^ t)
            (fun s _ => div_nonneg (hν0 s) (pow_pos hα0 s).le) (Finset.mem_range.mpr ht)
        have h2 : ν t / α ^ t ≤ c := by rw [hc]; linarith
        rwa [div_le_iff₀ hαt] at h2
      · have htN : N ≤ t := by omega
        have ht0 : t ≠ 0 := by omega
        have h1 := hN t htN
        have h2 : ν t ≤ α ^ t := by
          have e := Real.rpow_inv_natCast_pow (hν0 t) ht0
          rw [one_div] at h1
          rw [← e]
          exact pow_le_pow_left₀ (Real.rpow_nonneg (hν0 t) _) h1.le t
        have hc1 : 1 ≤ c := by
          rw [hc]
          have := Finset.sum_nonneg (s := Finset.range (max N 1))
            (fun s _ => div_nonneg (hν0 s) (pow_pos hα0 s).le)
          linarith
        nlinarith
    obtain ⟨hb, hl⟩ := Puder.limsup_sum_rpow_le_cogrowth k hk f hf α c hα0.le
      (fun t => by rw [hsum]; exact hν' t)
    refine ⟨hb, hl.trans ?_⟩
    rw [if_neg (by linarith : ¬ α ≤ Real.sqrt q)]
    have : q / α ≤ q / ρ := div_le_div_of_nonneg_left hq0.le hρ0 (by linarith)
    linarith
  rw [htarget, hrho]
  exact ⟨(key 1 one_pos).1, le_of_forall_pos_le_add fun ε hε => (key ε hε).2⟩

end Puder.Cog.PartC
end

open Filter Puder in
theorem solution (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) atTop ≤ StrongConv.rhoStair k m :=
  Puder.Cog.PartC.cor45_dev k m hk hm1 hm
