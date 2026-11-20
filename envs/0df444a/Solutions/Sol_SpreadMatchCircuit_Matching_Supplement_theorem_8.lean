-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:44:24.945866+00:00
-- url     : https://prove2.me/submissions/fd08a3fd-c963-461e-81cb-56c7be943cb7

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_Cliques
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_SetSpread
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
import Definitions.Def_SpreadMatchCircuit_Matching_Promise
import Theorems.Thm_SpreadMatchCircuit_Matching_Supplement_lemma_4

section
/-!
# Lemma 4 (Spread Clique Lemma) from the Spread Set Lemma (Lemma 3)

The paper's hybrid inequality (9) is false as literally stated (edges from vertex `i+1` back to
`[i] \ W_i` are present in `X'_{i+1}` but never in `X'_i`), so we use a corrected hybrid:
for a set `D` of processed vertices (disjoint from `S`), the event is
`∃ z ∈ 𝒵, z ∩ D ⊆ W ∧ R_D(z) ⊆ X`, where `R_D(z)` are the edges of `C_{z ∪ S}` outside `C_S`
avoiding `D`. Processing one more vertex `v` can only decrease the probability.
-/

namespace SpreadMatchCircuit.Matching.Dev.Lemma4

open Finset SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Supplement

section Wt
variable {β : Type} [DecidableEq β]

/-- Binomial weight of `y ⊆ s` when each element of `s` is kept with probability `q`. -/
def wt (q : ℝ) (s y : Finset β) : ℝ := q ^ y.card * (1 - q) ^ (s.card - y.card)

lemma sum_wt (q : ℝ) (s : Finset β) : ∑ y ∈ s.powerset, wt q s y = 1 := by
  unfold wt; rw [Finset.sum_pow_mul_eq_add_pow]; simp

lemma wt_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s y : Finset β) : 0 ≤ wt q s y :=
  mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (by linarith) _)

lemma split (q : ℝ) (s B : Finset β) (f : Finset β → ℝ) :
    ∑ x ∈ s.powerset, wt q s x * f x =
      ∑ a ∈ (s \ B).powerset, ∑ y ∈ (s ∩ B).powerset,
        wt q (s \ B) a * wt q (s ∩ B) y * f (a ∪ y) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun x => (x \ B, x ∩ B))
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    simp only [mem_powerset]
    exact union_subset (hp.1.trans sdiff_subset) (hp.2.trans inter_subset_left)
  · intro x hx
    simp only [mem_powerset] at hx
    simp only [mem_product, mem_powerset]
    exact ⟨sdiff_subset_sdiff hx le_rfl, inter_subset_inter hx le_rfl⟩
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    have h1 : ∀ v ∈ p.1, v ∉ B := fun v hv => (mem_sdiff.1 (hp.1 hv)).2
    have h2 : ∀ v ∈ p.2, v ∈ B := fun v hv => (mem_inter.1 (hp.2 hv)).2
    ext v
    · simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hB⟩
        · exact h
        · exact absurd (h2 v h) hB
      · intro h; exact ⟨Or.inl h, h1 v h⟩
    · simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨h | h, hB⟩
        · exact absurd hB (h1 v h)
        · exact h
      · intro h; exact ⟨Or.inr h, h2 v h⟩
  · intro x _
    exact sdiff_union_inter x B
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    have hd : Disjoint p.1 p.2 := by
      rw [disjoint_left]
      intro v h1 h2
      exact (mem_sdiff.1 (hp.1 h1)).2 (mem_inter.1 (hp.2 h2)).2
    have hc1 := card_le_card hp.1
    have hc2 := card_le_card hp.2
    have hs := card_sdiff_add_card_inter s B
    unfold wt
    rw [card_union_of_disjoint hd]
    have : s.card - (p.1.card + p.2.card) =
        ((s \ B).card - p.1.card) + ((s ∩ B).card - p.2.card) := by omega
    rw [this, pow_add, pow_add]
    ring

lemma sum_sup (q : ℝ) (B y0 : Finset β) (h : y0 ⊆ B) :
    ∑ y ∈ B.powerset, wt q B y * (if y0 ⊆ y then (1 : ℝ) else 0) = q ^ y0.card := by
  rw [split q B y0]
  rw [inter_eq_right.2 h]
  have : ∀ a ∈ (B \ y0).powerset,
      ∑ y ∈ y0.powerset, wt q (B \ y0) a * wt q y0 y * (if y0 ⊆ a ∪ y then (1 : ℝ) else 0) =
        wt q (B \ y0) a * q ^ y0.card := by
    intro a ha
    rw [mem_powerset] at ha
    rw [sum_eq_single y0]
    · simp [wt]
    · intro y hy hne
      rw [mem_powerset] at hy
      have : ¬ y0 ⊆ a ∪ y := by
        intro hs
        apply hne
        apply Subset.antisymm hy
        intro w hw
        rcases mem_union.1 (hs hw) with h' | h'
        · exact absurd hw (mem_sdiff.1 (ha h')).2
        · exact h'
      simp [this]
    · intro h'; exact absurd (mem_powerset.2 (Subset.refl _)) h'
  rw [sum_congr rfl this, ← sum_mul, sum_wt, one_mul]

end Wt

section Main

variable {n : ℕ}

open scoped Classical

/-- Indicator. -/
noncomputable def ind (P : Prop) : ℝ := if P then 1 else 0

lemma ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  unfold ind
  by_cases hP : P
  · rw [if_pos hP, if_pos (h hP)]
  · rw [if_neg hP]; split_ifs <;> norm_num

lemma mem_cliqueEdges {T : Finset (Fin n)} {e : Edge n} : e ∈ cliqueEdges T ↔ endpoints e ⊆ T := by
  simp [cliqueEdges]

lemma sum_wt_univ {β : Type} [Fintype β] [DecidableEq β] (q : ℝ) :
    ∑ x : Finset β, wt q univ x = 1 := by
  have := sum_wt q (univ : Finset β); rwa [powerset_univ] at this

end Main

end SpreadMatchCircuit.Matching.Dev.Lemma4

namespace SpreadMatchCircuit.Matching.Supplement

open Finset SpreadMatchCircuit.Matching.Dev.Lemma4

end SpreadMatchCircuit.Matching.Supplement
end

section
/-!
# Theorem 8 from Lemma 4 and the approximation step (Eq. (10): Algorithm 2, Lemmas 13, 14)
-/

namespace SpreadMatchCircuit.Matching.Dev.Thm8

open Finset SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Supplement

variable {n : ℕ}

/-- `f_A(x) = 1` iff some `S ∈ A` lies in a clique `C_T ⊆ x` with `|T| ≥ 2`. -/
def fA (A : Finset (Finset (Fin n))) (x : Finset (Edge n)) : Prop :=
  ∃ S ∈ A, ∃ T : Finset (Fin n), S ⊆ T ∧ 2 ≤ T.card ∧ cliqueEdges T ⊆ x

/-- The approximation step of Section 4.1 (gate-by-gate construction with Algorithm 2, Lemma 13,
Lemma 14 and the union bound over gates): for every monotone circuit there is a family `A` of
vertex sets of size `≤ t` whose function `f_A` errs on `X₁ = C_{W₁}` (`W₁` a uniform `k`-set) with
probability `≤ size · (kr/n)^{t+1}` and on the Erdős–Rényi graph `X₀ ∼ G(n,p)` with probability
`≤ size · (2n)^{t+2} · ε`. -/
def ApproxStatement : Prop :=
  ∃ β : ℝ, 0 < β ∧
    ∀ (n k : ℕ) (C : MonotoneCircuit (Edge n)) (t : ℕ) (ε p r : ℝ),
      2 ≤ t → 2 ≤ k → k ≤ n → 0 < ε → ε ≤ 1 / 2 → 0 < p → p ≤ 1 →
      r = β * Real.log ((2 * t + 1) / ε) / p ^ (3 * t + 2) → (k : ℝ) * r ≤ n →
      ∃ A : Finset (Finset (Fin n)), (∀ S ∈ A, S.card ≤ t) ∧
        uniformProb (univ.powersetCard k)
            (fun W => ¬ fA A (cliqueEdges W) ∧ C.eval (graphInput (cliqueEdges W)) = true) ≤
          (C.size : ℝ) * ((k : ℝ) * r / n) ^ (t + 1) ∧
        randomGraphProb n p (fun X => fA A X ∧ C.eval (graphInput X) = false) ≤
          (C.size : ℝ) * (2 * (n : ℝ)) ^ (t + 2) * ε

/-! ### Probability helpers -/

open scoped Classical

lemma rgp_eq (p : ℝ) (P : Finset (Edge n) → Prop) :
    randomGraphProb n p P = ∑ X : Finset (Edge n), Dev.Lemma4.wt p univ X * Dev.Lemma4.ind (P X) := by
  unfold randomGraphProb Dev.Lemma4.ind Dev.Lemma4.wt
  rw [sum_filter, card_univ]
  apply sum_congr rfl; intro X _; split_ifs <;> simp

lemma rgp_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {P Q R : Finset (Edge n) → Prop}
    (h : ∀ X, P X → Q X ∨ R X) :
    randomGraphProb n p P ≤ randomGraphProb n p Q + randomGraphProb n p R := by
  rw [rgp_eq, rgp_eq, rgp_eq, ← sum_add_distrib]
  apply sum_le_sum; intro X _
  have hw := Dev.Lemma4.wt_nonneg hp0 hp1 (univ : Finset (Edge n)) X
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ hw
  unfold Dev.Lemma4.ind
  by_cases hP : P X
  · rcases h X hP with hQ | hR
    · rw [if_pos hP, if_pos hQ]; split_ifs <;> norm_num
    · rw [if_pos hP, if_pos hR]; split_ifs <;> norm_num
  · rw [if_neg hP]; split_ifs <;> norm_num

lemma rgp_union {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ι : Type} (s : Finset ι)
    (P : ι → Finset (Edge n) → Prop) :
    randomGraphProb n p (fun X => ∃ i ∈ s, P i X) ≤ ∑ i ∈ s, randomGraphProb n p (P i) := by
  simp_rw [rgp_eq]
  rw [sum_comm]
  apply sum_le_sum; intro X _
  have hw := Dev.Lemma4.wt_nonneg hp0 hp1 (univ : Finset (Edge n)) X
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ hw
  unfold Dev.Lemma4.ind
  split_ifs with h
  · obtain ⟨i, hi, hP⟩ := h
    calc (1 : ℝ) = if P i X then 1 else 0 := by rw [if_pos hP]
      _ ≤ _ := single_le_sum (f := fun i => if P i X then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
  · exact sum_nonneg fun j _ => by split_ifs <;> norm_num

lemma rgp_subset (p : ℝ) (y0 : Finset (Edge n)) :
    randomGraphProb n p (fun X => y0 ⊆ X) = p ^ y0.card := by
  rw [rgp_eq]
  have := Dev.Lemma4.sum_sup p (univ : Finset (Edge n)) y0 (subset_univ _)
  rw [powerset_univ] at this
  rw [← this]
  apply sum_congr rfl; intro y _
  unfold Dev.Lemma4.ind
  by_cases h : y0 ⊆ y <;> simp [h]

lemma card_cliqueEdges_ge (T : Finset (Fin n)) : T.card.choose 2 ≤ (cliqueEdges T).card := by
  rw [← card_powersetCard]
  apply card_le_card_of_surjOn endpoints
  intro P hP
  rw [mem_coe, mem_powersetCard] at hP
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hP.2
  refine ⟨⟨s(a, b), by simp [hab]⟩, ?_, ?_⟩
  · rw [mem_coe, Dev.Lemma4.mem_cliqueEdges]
    intro v hv
    apply hP.1
    simpa [endpoints, Sym2.mem_toFinset] using hv
  · ext v; simp [endpoints, Sym2.mem_toFinset]

lemma clique_prob_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    randomGraphProb n p (fun X => HasCliqueOfSize X q) ≤ (n.choose q : ℝ) * p ^ (q.choose 2) := by
  have h1 : randomGraphProb n p (fun X => HasCliqueOfSize X q) ≤
      randomGraphProb n p (fun X => ∃ T ∈ (univ : Finset (Fin n)).powersetCard q,
        cliqueEdges T ⊆ X) := by
    have := rgp_le (n := n) hp0 hp1 (P := fun X => HasCliqueOfSize X q)
      (Q := fun X => ∃ T ∈ (univ : Finset (Fin n)).powersetCard q, cliqueEdges T ⊆ X)
      (R := fun _ => False) (fun X ⟨T, hT, hTX⟩ => Or.inl ⟨T, by simp [hT], hTX⟩)
    have h0 : randomGraphProb n p (fun _ => False) = 0 := by
      unfold randomGraphProb; simp
    linarith
  refine h1.trans ((rgp_union hp0 hp1 _ _).trans ?_)
  rw [show (n.choose q : ℝ) * p ^ (q.choose 2) =
      ∑ T ∈ (univ : Finset (Fin n)).powersetCard q, p ^ (q.choose 2) by
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]]
  apply sum_le_sum; intro T hT
  rw [rgp_subset]
  rw [mem_powersetCard] at hT
  apply pow_le_pow_of_le_one hp0 hp1
  rw [← hT.2]; exact card_cliqueEdges_ge T

lemma subset_of_cliqueEdges_subset {T W : Finset (Fin n)} (hT : 2 ≤ T.card)
    (h : cliqueEdges T ⊆ cliqueEdges W) : T ⊆ W := by
  intro v hv
  obtain ⟨u, hu, huv⟩ : ∃ u ∈ T, u ≠ v := by
    by_contra hne
    push Not at hne
    have : T ⊆ {v} := fun w hw => mem_singleton.2 (hne w hw)
    have := card_le_card this
    simp at this; omega
  have he : (⟨s(u, v), by simp [huv]⟩ : Edge n) ∈ cliqueEdges T := by
    rw [Dev.Lemma4.mem_cliqueEdges]
    intro w hw
    simp [endpoints, Sym2.mem_toFinset] at hw
    rcases hw with rfl | rfl <;> assumption
  have := Dev.Lemma4.mem_cliqueEdges.1 (h he)
  exact this (by simp [endpoints, Sym2.mem_toFinset])

lemma uP_mono {β : Type} (F : Finset β) (A B : β → Prop) (h : ∀ x ∈ F, A x → B x) :
    uniformProb F A ≤ uniformProb F B := by
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, h _ hx.1 hx.2⟩)

lemma lawProb_map_uniform {α β : Type} [Fintype β] (S : Finset α) (hS : S.Nonempty) (Z : α → β)
    (A : β → Prop) [DecidablePred (fun x => A (Z x))] :
    lawProb (PMF.map Z (PMF.uniformOfFinset S hS)) A =
      ((S.filter (fun x => A (Z x))).card : ℝ) / S.card := by
  unfold lawProb
  rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _), ← PMF.toOuterMeasure_apply_finset,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  congr 3
  ext x
  simp

lemma descFactorial_mul_pow_le {k n : ℕ} (hkn : k ≤ n) :
    ∀ a : ℕ, k.descFactorial a * n ^ a ≤ n.descFactorial a * k ^ a
  | 0 => by simp
  | a + 1 => by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have ih := descFactorial_mul_pow_le hkn a
    have h2 : (k - a) * n ≤ (n - a) * k := by
      rcases le_or_gt a k with h | h
      · have : (k - a) * n + a * n = (n - a) * k + a * k := by
          rw [← add_mul, ← add_mul, Nat.sub_add_cancel h, Nat.sub_add_cancel (h.trans hkn),
            mul_comm]
        have : a * k ≤ a * n := Nat.mul_le_mul_left a hkn
        omega
      · rw [Nat.sub_eq_zero_of_le h.le]; simp
    calc (k - a) * k.descFactorial a * (n ^ a * n)
        = (k.descFactorial a * n ^ a) * ((k - a) * n) := by ring
      _ ≤ (n.descFactorial a * k ^ a) * ((n - a) * k) := Nat.mul_le_mul ih h2
      _ = (n - a) * n.descFactorial a * (k ^ a * k) := by ring

/-- `P(A' ⊆ W₁) ≤ (k/n)^{|A'|}` for a uniform `k`-subset `W₁` of `[n]`. -/
lemma subset_prob_le {k : ℕ} (hk : k ≤ n) (hn : 0 < n) (A' : Finset (Fin n)) :
    (((univ.powersetCard k).filter (fun W : Finset (Fin n) => A' ⊆ W)).card : ℝ) ≤
      ((k : ℝ) / n) ^ A'.card * (n.choose k : ℝ) := by
  set a := A'.card
  by_cases hak : a ≤ k
  · have hsub : (univ.powersetCard k).filter (fun W : Finset (Fin n) => A' ⊆ W) ⊆
        ((univ \ A').powersetCard (k - a)).image (fun U => U ∪ A') := by
      intro W hW
      rw [mem_filter, mem_powersetCard] at hW
      rw [mem_image]
      refine ⟨W \ A', ?_, sdiff_union_of_subset hW.2⟩
      rw [mem_powersetCard]
      refine ⟨sdiff_subset_sdiff (subset_univ _) le_rfl, ?_⟩
      rw [card_sdiff_of_subset hW.2, hW.1.2]
    have h1 := (card_le_card hsub).trans card_image_le
    rw [card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at h1
    -- `C(n,k) C(k,a) = C(n,a) C(n-a,k-a)`
    have hcm := Nat.choose_mul (n := n) (k := k) (s := a) hak
    have hd := descFactorial_mul_pow_le hk a
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hd
    have hfac : 0 < a.factorial := Nat.factorial_pos a
    have hd' : k.choose a * n ^ a ≤ n.choose a * k ^ a := by
      have : a.factorial * (k.choose a * n ^ a) ≤ a.factorial * (n.choose a * k ^ a) := by
        calc a.factorial * (k.choose a * n ^ a) = a.factorial * k.choose a * n ^ a := by ring
          _ ≤ a.factorial * n.choose a * k ^ a := hd
          _ = _ := by ring
      exact Nat.le_of_mul_le_mul_left this hfac
    have hna : 0 < n.choose a := Nat.choose_pos (hak.trans hk)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hnaR : (0 : ℝ) < n.choose a := by exact_mod_cast hna
    have h1R : (((univ.powersetCard k).filter (fun W : Finset (Fin n) => A' ⊆ W)).card : ℝ) ≤
        ((n - a).choose (k - a) : ℝ) := by exact_mod_cast h1
    have hcmR : (n.choose k : ℝ) * k.choose a = n.choose a * (n - a).choose (k - a) := by
      exact_mod_cast hcm
    have hdR : (k.choose a : ℝ) * (n : ℝ) ^ a ≤ n.choose a * (k : ℝ) ^ a := by exact_mod_cast hd'
    refine h1R.trans ?_
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    -- `(n-a).choose (k-a) * n^a ≤ k^a * C(n,k)`
    have : ((n - a).choose (k - a) : ℝ) * n.choose a * (n : ℝ) ^ a ≤
        (k : ℝ) ^ a * n.choose k * n.choose a := by
      calc ((n - a).choose (k - a) : ℝ) * n.choose a * (n : ℝ) ^ a
          = (n.choose k : ℝ) * (k.choose a * (n : ℝ) ^ a) := by
            linear_combination (-((n : ℝ) ^ a)) * hcmR
        _ ≤ (n.choose k : ℝ) * (n.choose a * (k : ℝ) ^ a) :=
            mul_le_mul_of_nonneg_left hdR (by positivity)
        _ = _ := by ring
    nlinarith
  · have : (univ.powersetCard k).filter (fun W : Finset (Fin n) => A' ⊆ W) = ∅ := by
      apply filter_false_of_mem
      intro W hW hAW
      rw [mem_powersetCard] at hW
      have := card_le_card hAW
      omega
    rw [this, card_empty, Nat.cast_zero]
    positivity

/-- The spread law of the sets caught by `f_A` on `X₁ = C_{W₁}`. -/
lemma exists_law {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) (t : ℕ) (A : Finset (Finset (Fin n)))
    (hA : ∀ S ∈ A, S.card ≤ t)
    (hbad : uniformProb (univ.powersetCard k) (fun W => ¬ fA A (cliqueEdges W)) ≤ 1 / 3) :
    ∃ μ : PMF (Finset (Fin n)), IsSetSpread μ ((n : ℝ) / (2 * k)) ∧
      IsBoundedSetLaw μ ((t : ℝ) + 2) ∧
      ∀ z ∈ lawSupport μ, 2 ≤ z.card ∧ ∃ S ∈ A, S ⊆ z := by
  set all := (univ : Finset (Fin n)).powersetCard k with hall
  set G := all.filter (fun W => fA A (cliqueEdges W)) with hG
  have hn : 0 < n := by omega
  have hallpos : 0 < all.card := by
    rw [hall, card_powersetCard, card_univ, Fintype.card_fin]; exact Nat.choose_pos hkn
  have hallR : (0 : ℝ) < all.card := by exact_mod_cast hallpos
  have hGcard : (all.card : ℝ) ≤ 3 / 2 * G.card := by
    unfold uniformProb at hbad
    rw [div_le_iff₀ hallR] at hbad
    have := card_filter_add_card_filter_not (s := all) (fun W => fA A (cliqueEdges W))
    have h' : ((all.filter fun W => fA A (cliqueEdges W)).card : ℝ) +
        (all.filter fun W => ¬ fA A (cliqueEdges W)).card = all.card := by exact_mod_cast this
    rw [← hG] at h'
    have hbad' : ((all.filter fun W => ¬ fA A (cliqueEdges W)).card : ℝ) ≤ 1 / 3 * all.card := by
      convert hbad using 4
      all_goals rfl
    linarith
  have hGne : G.Nonempty := by
    rw [← card_pos]; by_contra h; push Not at h
    have : (G.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.1 h
    linarith
  -- the selector
  have hsel : ∀ W ∈ G, ∃ z, (∃ S ∈ A, S ⊆ z) ∧ z ⊆ W ∧ 2 ≤ z.card ∧ z.card ≤ t + 2 := by
    intro W hW
    rw [hG, mem_filter, hall, mem_powersetCard] at hW
    obtain ⟨⟨_, hWk⟩, S, hS, T, hST, hT2, hTW⟩ := hW
    have hSW : S ⊆ W := hST.trans (subset_of_cliqueEdges_subset hT2 (fun e he => by
      exact Dev.Lemma4.mem_cliqueEdges.2 (Dev.Lemma4.mem_cliqueEdges.1 (hTW he))))
    obtain ⟨P, hPW, hP2⟩ := exists_subset_card_eq (show 2 ≤ W.card by omega)
    refine ⟨S ∪ P, ⟨S, hS, subset_union_left⟩, union_subset hSW hPW, ?_, ?_⟩
    · rw [← hP2]; exact card_le_card subset_union_right
    · have := card_union_le S P; have := hA S hS; omega
  let Z : Finset (Fin n) → Finset (Fin n) := fun W =>
    if h : W ∈ G then Classical.choose (hsel W h) else ∅
  have hZ : ∀ W ∈ G, (∃ S ∈ A, S ⊆ Z W) ∧ Z W ⊆ W ∧ 2 ≤ (Z W).card ∧ (Z W).card ≤ t + 2 := by
    intro W hW
    simp only [Z, dif_pos hW]
    exact Classical.choose_spec (hsel W hW)
  set μ := PMF.map Z (PMF.uniformOfFinset G hGne) with hμ
  have hsupp : ∀ z ∈ lawSupport μ, ∃ W ∈ G, Z W = z := by
    intro z hz
    simp only [lawSupport, Finset.mem_filter, Finset.mem_univ, true_and, μ, PMF.support_map,
      PMF.support_uniformOfFinset, Set.mem_image, Finset.mem_coe] at hz
    exact hz
  refine ⟨μ, ?_, ?_, ?_⟩
  · intro A'
    rw [hμ, lawProb_map_uniform]
    have hGpos : (0 : ℝ) < G.card := by exact_mod_cast card_pos.mpr hGne
    have hle1 : ((G.filter (fun W => A' ⊆ Z W)).card : ℝ) / G.card ≤ 1 := by
      rw [div_le_one hGpos]; exact_mod_cast card_filter_le _ _
    rcases Nat.eq_zero_or_pos A'.card with h0 | hpos
    · rw [h0]; simpa using hle1
    have hsub : ((G.filter (fun W => A' ⊆ Z W)).card : ℝ) ≤
        ((all.filter (fun W => A' ⊆ W)).card : ℝ) := by
      exact_mod_cast card_le_card (fun W hW => by
        rw [mem_filter] at hW ⊢
        exact ⟨(mem_filter.1 hW.1).1, hW.2.trans (hZ W hW.1).2.1⟩)
    have hsp := subset_prob_le hkn hn A'
    rw [← hall] at hsp
    have hallc : (all.card : ℝ) = n.choose k := by
      rw [hall, card_powersetCard, card_univ, Fintype.card_fin]
    rw [← hallc] at hsp
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hX0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    calc ((G.filter (fun W => A' ⊆ Z W)).card : ℝ) / G.card
        ≤ (((k : ℝ) / n) ^ A'.card * all.card) / G.card :=
          div_le_div_of_nonneg_right (hsub.trans hsp) hGpos.le
      _ ≤ 3 / 2 * ((k : ℝ) / n) ^ A'.card := by
          rw [div_le_iff₀ hGpos]
          have := pow_nonneg hX0 A'.card
          nlinarith
      _ ≤ 2 ^ A'.card * ((k : ℝ) / n) ^ A'.card := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hX0 _)
          calc (3 / 2 : ℝ) ≤ 2 ^ 1 := by norm_num
            _ ≤ 2 ^ A'.card := pow_le_pow_right₀ (by norm_num) hpos
      _ = (((n : ℝ) / (2 * k)) ^ A'.card)⁻¹ := by
          rw [← mul_pow, ← inv_pow]; congr 1; field_simp
  · intro z hz
    obtain ⟨W, hW, rfl⟩ := hsupp z hz
    exact_mod_cast (hZ W hW).2.2.2
  · intro z hz
    obtain ⟨W, hW, rfl⟩ := hsupp z hz
    exact ⟨(hZ W hW).2.2.1, (hZ W hW).1⟩


/-! ### Arithmetic -/

lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

lemma p_pow_ge {N : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (q t : ℕ) (K : ℝ) (hq : 2 ≤ q)
    (ht : 2 ≤ t) (hK : 8 ≤ K) (htq : (t : ℝ) * Real.log N * K ≤ q) :
    1 / 8 ≤ (N ^ (-(2 / ((q : ℝ) - 1)))) ^ (3 * t + 2) := by
  have hN0 : 0 < N := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.rpow_def_of_pos hN0]
  have hy : Real.log N * (2 / ((q : ℝ) - 1) * ((3 * t + 2 : ℕ) : ℝ)) ≤ 2 := by
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    have h1 : 8 * ((t : ℝ) * Real.log N) ≤ q := by
      have : 8 * ((t : ℝ) * Real.log N) ≤ (t : ℝ) * Real.log N * K := by
        have : 0 ≤ (t : ℝ) * Real.log N := by positivity
        nlinarith
      linarith
    rw [show Real.log N * (2 / ((q : ℝ) - 1) * (3 * (t : ℝ) + 2)) =
      (2 * Real.log N * (3 * t + 2)) / ((q : ℝ) - 1) by ring]
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.log N := by linarith
    nlinarith
  have : Real.exp (-2) ≤ Real.exp (Real.log N * (-(2 / ((q : ℝ) - 1)) * ((3 * t + 2 : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.2
    have : Real.log N * (-(2 / ((q : ℝ) - 1)) * ((3 * t + 2 : ℕ) : ℝ)) =
      -(Real.log N * (2 / ((q : ℝ) - 1) * ((3 * t + 2 : ℕ) : ℝ))) := by ring
    rw [this]; linarith
  have h8 : 1 / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 2) exp_two_lt_eight.le
  linarith

lemma clique_bound {N : ℕ} (hN : 1 ≤ N) (q : ℕ) (hq : 2 ≤ q) :
    (N.choose q : ℝ) * (((N : ℝ) ^ (-(2 / ((q : ℝ) - 1)))) ^ (q.choose 2)) ≤ 1 / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Nat.cast_choose_two]
  have : -(2 / ((q : ℝ) - 1)) * ((q : ℝ) * ((q : ℝ) - 1) / 2) = -(q : ℝ) := by
    field_simp
  rw [this, Real.rpow_neg hN0.le, Real.rpow_natCast]
  have hc := Nat.choose_le_pow_div (α := ℝ) q N
  have hfac : (2 : ℝ) ≤ (q.factorial : ℝ) := by
    exact_mod_cast hq.trans (Nat.self_le_factorial q)
  have hpow : (0 : ℝ) < (N : ℝ) ^ q := by positivity
  calc (N.choose q : ℝ) * ((N : ℝ) ^ q)⁻¹ ≤ ((N : ℝ) ^ q / q.factorial) * ((N : ℝ) ^ q)⁻¹ :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 1 / q.factorial := by field_simp
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hfac

lemma log_bound {N L : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hL : 1 ≤ L) (t : ℕ) (ht : 2 ≤ t) :
    Real.log ((2 * (t : ℝ) + 1) / (1 / (8 * L * (2 * N) ^ (t + 2)))) ≤
      10 * ((t : ℝ) * Real.log N) + Real.log L := by
  have hN0 : 0 < N := by linarith
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  rw [div_div_eq_mul_div, div_one, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_mul (by norm_num) hN0.ne']
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * t + 1 by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
  have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  push_cast
  have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-! ### Steps of the main computation -/

lemma part1 {K α4 η : ℝ} (hK8 : 8 ≤ K) (hα4 : 0 < α4) (hη : η = 1 / (3 * K + 192 * α4 + 3))
    {n k q : ℕ} (h1 : Real.log (n : ℝ) < η * (q : ℝ)) (h2 : η * (q : ℝ) < (k : ℝ))
    (h3 : (k : ℝ) * (q : ℝ) ≤ η * (n : ℝ)) :
    1 ≤ Real.log (n : ℝ) ∧ (1 : ℝ) ≤ q ∧ (1 : ℝ) ≤ k ∧
      3 * K + 192 * α4 + 3 ≤ (q : ℝ) / Real.log n ∧ k ≤ n ∧
      (3 : ℝ) ≤ (n : ℝ) / ((k : ℝ) * (q : ℝ)) ∧ η * (3 * K + 192 * α4 + 3) = 1 ∧ η ≤ 1 := by
  have hKpos : 0 < K := by linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hqpos : (0 : ℝ) < q := by
    by_contra h; push Not at h; nlinarith
  have hkpos : (0 : ℝ) < k := by nlinarith
  have hq1 : (1 : ℝ) ≤ q := by
    have : 0 < q := by exact_mod_cast hqpos
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ k := by
    have : 0 < k := by exact_mod_cast hkpos
    exact_mod_cast this
  have hηinv : η * (3 * K + 192 * α4 + 3) = 1 := by rw [hη]; field_simp
  have hn_big : 3 * K + 192 * α4 + 3 ≤ (n : ℝ) := by
    have : 1 ≤ η * n := le_trans (by nlinarith) h3
    nlinarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hxη : 3 * K + 192 * α4 + 3 ≤ (q : ℝ) / Real.log n := by
    rw [le_div_iff₀ hlogpos]
    nlinarith
  have hη1 : η * 3 ≤ 1 := by
    have : η * 3 ≤ η * (3 * K + 192 * α4 + 3) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hηpos.le
    linarith
  have hkq1 : (k : ℝ) ≤ k * q := le_mul_of_one_le_right hkpos.le hq1
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := by
      have : η * n ≤ n := by nlinarith
      linarith
    exact_mod_cast this
  have hkq : (0 : ℝ) < k * q := by positivity
  have hB3 : (3 : ℝ) ≤ (n : ℝ) / ((k : ℝ) * (q : ℝ)) := by
    rw [le_div_iff₀ hkq]
    have : 3 * (η * n) ≤ n := by nlinarith
    linarith
  exact ⟨hlog1, hq1, hk1, hxη, hkn, hB3, hηinv, by linarith⟩

lemma part2 {K α4 x ℓ q : ℝ} (hK8 : 8 ≤ K) (hα4 : 0 < α4) (hxη : 3 * K + 192 * α4 + 3 ≤ x)
    (hlog1 : 1 ≤ ℓ) (hx : x = q / ℓ) {t : ℕ} (ht_le : (t : ℝ) ≤ x / K) (ht : t = ⌊x / K⌋₊) :
    2 ≤ t ∧ (t : ℝ) * ℓ * K ≤ q ∧ (2 : ℝ) ≤ q := by
  have hKpos : 0 < K := by linarith
  have hlogpos : 0 < ℓ := by linarith
  have ht2 : 2 ≤ t := by
    rw [ht]
    apply Nat.le_floor
    rw [le_div_iff₀ hKpos]; push_cast; nlinarith
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have htlog : (t : ℝ) * ℓ * K ≤ q := by
    have : (t : ℝ) * K ≤ x := by rwa [le_div_iff₀ hKpos] at ht_le
    have : (t : ℝ) * K * ℓ ≤ x * ℓ := mul_le_mul_of_nonneg_right this hlogpos.le
    rw [hx, div_mul_cancel₀ _ hlogpos.ne'] at this
    linarith
  refine ⟨ht2, htlog, ?_⟩
  have : (t : ℝ) * ℓ * K ≥ 2 * 1 * 8 := by
    have := mul_le_mul htR hlog1 (by norm_num) (by positivity)
    nlinarith
  linarith

lemma r_le_q {β K c ℓ q ε L p r : ℝ} {t : ℕ} (hβ : 0 < β) (hK : K = 96 * β + 8)
    (hc : c = 1 / (16 * (β + 1) * K)) (hp0 : 0 < p)
    (hr : r = β * Real.log ((2 * t + 1) / ε) / p ^ (3 * t + 2))
    (hlogr : Real.log ((2 * t + 1) / ε) ≤ 10 * ((t : ℝ) * ℓ) + Real.log L)
    (hlogL : Real.log L ≤ c * q) (htlog : (t : ℝ) * ℓ * K ≤ q) (hp3 : 1 / 8 ≤ p ^ (3 * t + 2))
    (hlogr0 : 0 ≤ Real.log ((2 * t + 1) / ε)) (hq : 0 ≤ q) :
    r ≤ q := by
  have hKpos : 0 < K := by rw [hK]; linarith
  have hb : r ≤ β * Real.log ((2 * t + 1) / ε) * 8 := by
    rw [hr, div_le_iff₀ (by positivity)]
    have : 0 ≤ β * Real.log ((2 * t + 1) / ε) := by positivity
    nlinarith
  have h10 : 10 * ((t : ℝ) * ℓ) ≤ 10 * (q / K) := by
    have : (t : ℝ) * ℓ ≤ q / K := by rw [le_div_iff₀ hKpos]; linarith
    linarith
  have hcK : c * (16 * (β + 1) * K) = 1 := by rw [hc]; field_simp
  have hβK : 80 * β ≤ 5 / 6 * K := by rw [hK]; linarith
  have hqK : 10 * (q / K) * (8 * β) ≤ 5 / 6 * q := by
    rw [show 10 * (q / K) * (8 * β) = (80 * β) * q / K by ring, div_le_iff₀ hKpos]
    nlinarith
  have hcβ : 8 * β * c ≤ 1 / 16 := by
    have : 8 * β * c * (16 * (β + 1) * K) ≤ 1 / 16 * (16 * (β + 1) * K) := by
      rw [show 8 * β * c * (16 * (β + 1) * K) = 8 * β * (c * (16 * (β + 1) * K)) by ring, hcK]
      nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  have : β * Real.log ((2 * t + 1) / ε) * 8 ≤ (10 * (q / K) + c * q) * (8 * β) := by
    have := add_le_add h10 hlogL
    nlinarith
  nlinarith

lemma err1_bound {S L B c x K r k n q : ℝ} {t : ℕ} (ht : 1 ≤ t) (hS : S ≤ L) (hk : 0 < k) (hn : 0 < n)
    (hB : B = n / (k * q)) (hB3 : 3 ≤ B) (hL : L = B ^ (c * x)) (hc : 0 ≤ c)
    (hcK : c * K ≤ 1 / 2) (hxK : x < K * (t + 1)) (hr0 : 0 ≤ r) (hrq : r ≤ q) :
    S * (k * r / n) ^ (t + 1) ≤ 1 / 3 := by
  have hkrn : k * r / n ≤ 1 / B := by
    rw [hB, one_div_div, div_le_div_iff_of_pos_right hn]
    exact mul_le_mul_of_nonneg_left hrq hk.le
  have hkrn0 : 0 ≤ k * r / n := by positivity
  set y := B ^ (((t : ℝ) + 1) / 2) with hy
  have hy3 : 3 ≤ y := by
    calc (3 : ℝ) ≤ B := hB3
      _ = B ^ (1 : ℝ) := (Real.rpow_one B).symm
      _ ≤ y := Real.rpow_le_rpow_of_exponent_le (by linarith) (by
          have : (1 : ℝ) ≤ t := by exact_mod_cast ht
          linarith)
  have hLy : L ≤ y := by
    rw [hL]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have : c * x ≤ c * (K * (t + 1)) := mul_le_mul_of_nonneg_left hxK.le hc
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith
  have hBy : B ^ (t + 1) = y * y := by
    rw [hy, ← Real.rpow_add (by linarith), ← Real.rpow_natCast]; push_cast; ring_nf
  calc S * (k * r / n) ^ (t + 1) ≤ L * (1 / B) ^ (t + 1) :=
        mul_le_mul hS (pow_le_pow_left₀ hkrn0 hkrn _) (pow_nonneg hkrn0 _)
          (by rw [hL]; exact Real.rpow_nonneg (by linarith) _)
    _ ≤ y * (1 / B) ^ (t + 1) := mul_le_mul_of_nonneg_right hLy (by positivity)
    _ = 1 / y := by rw [div_pow, one_pow, hBy]; field_simp
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hy3

lemma r4_le {α4 K η q n k ℓ p : ℝ} {t : ℕ} (hα4 : 0 < α4) (hK8 : 8 ≤ K)
    (hηinv : η * (3 * K + 192 * α4 + 3) = 1) (h3 : k * q ≤ η * n) (hk : 0 < k) (hq2 : 2 ≤ q)
    (hlog1 : 1 ≤ ℓ) (htlog : (t : ℝ) * ℓ * K ≤ q) (hp3' : 1 / 8 ≤ p ^ (t + 2)) (hp0 : 0 < p) :
    α4 * Real.log (((t : ℝ) + 2) / (1 / 6)) / p ^ (t + 2) ≤ n / (2 * k) := by
  rw [div_le_iff₀ (by positivity)]
  have hl6 : Real.log (((t : ℝ) + 2) / (1 / 6)) ≤ 12 * q := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((t : ℝ) + 2) / (1 / 6) by positivity)
    have htq : (t : ℝ) ≤ q := by
      have : (t : ℝ) * ℓ * K ≥ t := by
        have : (t : ℝ) * 1 * 1 ≤ t * ℓ * K := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hlog1 (by positivity)) (by linarith)
            (by norm_num) (by positivity)
        linarith
      linarith
    rw [div_div_eq_mul_div, div_one] at this ⊢
    linarith
  have hnk : q * (3 * K + 192 * α4 + 3) ≤ n / k := by
    rw [le_div_iff₀ hk]
    have : k * q * (3 * K + 192 * α4 + 3) ≤ η * n * (3 * K + 192 * α4 + 3) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    rw [show η * n * (3 * K + 192 * α4 + 3) = n * (η * (3 * K + 192 * α4 + 3)) by ring,
      hηinv, mul_one] at this
    linarith
  have : n / (2 * k) = (n / k) / 2 := by field_simp
  rw [this]
  have : α4 * Real.log (((t : ℝ) + 2) / (1 / 6)) ≤ α4 * (12 * q) :=
    mul_le_mul_of_nonneg_left hl6 hα4.le
  have hA8 : q * (3 * K + 192 * α4 + 3) / 2 * (1 / 8) ≤ (n / k) / 2 * p ^ (t + 2) :=
    mul_le_mul (by linarith) hp3' (by norm_num) (by
      have : 0 ≤ q * (3 * K + 192 * α4 + 3) := by nlinarith
      linarith)
  have : 0 ≤ q * (3 * K + 3) := by nlinarith
  have : α4 * (12 * q) ≤ q * (3 * K + 192 * α4 + 3) / 2 * (1 / 8) := by nlinarith
  linarith

lemma err0_bound {S L N : ℝ} {t : ℕ} (hS : S ≤ L) (hL1 : 1 ≤ L) (hN : 0 < N) :
    S * (2 * N) ^ (t + 2) * (1 / (8 * L * (2 * N) ^ (t + 2))) ≤ 1 / 8 := by
  have : 0 < (2 * N) ^ (t + 2) := by positivity
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  nlinarith

lemma eps_le {L N : ℝ} (t : ℕ) (hL1 : 1 ≤ L) (hN : 1 ≤ N) :
    1 / (8 * L * (2 * N) ^ (t + 2)) ≤ 1 / 2 := by
  apply one_div_le_one_div_of_le (by norm_num)
  have : 1 ≤ (2 * N) ^ (t + 2) := one_le_pow₀ (by linarith)
  nlinarith

/-- The event of Lemma 4 forces `f_A`, hence an error of `f_A` or a `q`-clique. -/
lemma lemma4_event_split {n k q : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : MonotoneCircuit (Edge n)) (hC : DistinguishesCliques C k q)
    (A : Finset (Finset (Fin n))) (μ : PMF (Finset (Fin n)))
    (hsupp : ∀ z ∈ lawSupport μ, 2 ≤ z.card ∧ ∃ S ∈ A, S ⊆ z) :
    randomGraphProb n p
      (fun X => ∃ z ∈ lawSupport μ, cliqueEdges (z ∪ ∅) ⊆ X ∪ cliqueEdges ∅) ≤
    randomGraphProb n p (fun X => fA A X ∧ C.eval (graphInput X) = false) +
      randomGraphProb n p (fun X => HasCliqueOfSize X q) := by
  apply rgp_le hp0 hp1
  rintro X ⟨z, hz, hzX⟩
  have hzX' : cliqueEdges z ⊆ X := by
    intro e he
    have := hzX (by rwa [union_empty])
    rcases mem_union.1 this with h | h
    · exact h
    · exfalso
      have h' := Dev.Lemma4.mem_cliqueEdges.1 h
      have := Finset.subset_empty.1 h'
      have h2 : (endpoints e).card = 2 := Sym2.card_toFinset_of_not_isDiag _ e.2
      rw [this, card_empty] at h2; omega
  obtain ⟨hz2, S, hS, hSz⟩ := hsupp z hz
  have hf : fA A X := ⟨S, hS, z, hSz, hz2, hzX'⟩
  by_cases hev : C.eval (graphInput X) = false
  · exact Or.inl ⟨hf, hev⟩
  · right
    by_contra hnc
    exact hev ((hC X).2 hnc)

end SpreadMatchCircuit.Matching.Dev.Thm8

namespace SpreadMatchCircuit.Matching.Supplement

open Finset SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Dev.Thm8

theorem chk_theorem_8_of_approx (happ : ApproxStatement) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (n k q : ℕ), Real.log (n : ℝ) < η * (q : ℝ) → η * (q : ℝ) < (k : ℝ) →
        (k : ℝ) * (q : ℝ) ≤ η * (n : ℝ) →
        ∀ C : MonotoneCircuit (Edge n), DistinguishesCliques C k q →
          ((n : ℝ) / ((k : ℝ) * (q : ℝ))) ^ (c * (q : ℝ) / Real.log (n : ℝ)) ≤
            (C.size : ℝ) := by
  classical
  obtain ⟨β, hβ, happ⟩ := happ
  obtain ⟨α4, hα4, hl4⟩ := lemma_4
  set K : ℝ := 96 * β + 8 with hK
  set c : ℝ := 1 / (16 * (β + 1) * K) with hc
  set η : ℝ := 1 / (3 * K + 192 * α4 + 3) with hη
  have hK8 : 8 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hcpos : 0 < c := by positivity
  have hηpos : 0 < η := by positivity
  have hcK : c * K ≤ 1 / 2 := by
    rw [hc, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; nlinarith
  refine ⟨η, c, hηpos, hcpos, ?_⟩
  intro n k q h1 h2 h3 C hC
  by_contra hlt
  push Not at hlt
  obtain ⟨hlog1, hq1, hk1, hxη, hkn, hB3, hηinv, hη1⟩ := part1 hK8 hα4 hη h1 h2 h3
  have hn1 : (1 : ℝ) ≤ n := hk1.trans (by exact_mod_cast hkn)
  have hnpos : (0 : ℝ) < n := by linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  set x := (q : ℝ) / Real.log n with hx
  set t := ⌊x / K⌋₊ with ht
  have ht_le : (t : ℝ) ≤ x / K := Nat.floor_le (by positivity)
  have ht_lt : x / K < t + 1 := Nat.lt_floor_add_one _
  obtain ⟨ht2, htlog, hq2R⟩ := part2 hK8 hα4 hxη hlog1 hx ht_le ht
  have hq2 : 2 ≤ q := by exact_mod_cast hq2R
  have hk2 : 2 ≤ k := by
    have : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast this
    omega
  -- B and L
  set B := (n : ℝ) / ((k : ℝ) * (q : ℝ)) with hB
  have hBn : B ≤ n := by
    rw [hB, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ k * q := one_le_mul_of_one_le_of_one_le hk1 hq1
    have := mul_le_mul_of_nonneg_left this hnpos.le
    linarith
  set L := B ^ (c * (q : ℝ) / Real.log (n : ℝ)) with hL
  have hcx : c * (q : ℝ) / Real.log n = c * x := by rw [hx]; ring
  have hL1 : 1 ≤ L := Real.one_le_rpow (by linarith) (by positivity)
  have hlogL : Real.log L ≤ c * q := by
    rw [hL, Real.log_rpow (by linarith), hcx]
    have : Real.log B ≤ Real.log n := Real.log_le_log (by linarith) hBn
    calc c * x * Real.log B ≤ c * x * Real.log n :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = c * q := by rw [hx]; field_simp
  -- p
  set p := (n : ℝ) ^ (-(2 / ((q : ℝ) - 1))) with hp
  have hp0 : 0 < p := Real.rpow_pos_of_pos hnpos _
  have hp1 : p ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hn1
    have : 0 ≤ 2 / ((q : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
    linarith
  have hp3 : 1 / 8 ≤ p ^ (3 * t + 2) := p_pow_ge hn1 hlog1 q t K hq2 ht2 hK8 htlog
  have hp3' : 1 / 8 ≤ p ^ (t + 2) :=
    hp3.trans (pow_le_pow_of_le_one hp0.le hp1 (by omega))
  -- ε and r
  set ε := 1 / (8 * L * (2 * (n : ℝ)) ^ (t + 2)) with hε
  have hεpos : 0 < ε := by positivity
  have hε2 : ε ≤ 1 / 2 := eps_le t hL1 hn1
  set r := β * Real.log ((2 * t + 1) / ε) / p ^ (3 * t + 2) with hr
  have hlogr := log_bound hn1 hlog1 hL1 t ht2
  rw [← hε] at hlogr
  have hlogr0 : 0 ≤ Real.log ((2 * t + 1) / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hεpos]
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith
  have hrq : r ≤ q := r_le_q hβ hK hc hp0 hr hlogr hlogL htlog hp3 hlogr0 (by positivity)
  have hkr : (k : ℝ) * r ≤ n := by
    have : (k : ℝ) * r ≤ k * q := mul_le_mul_of_nonneg_left hrq hkpos.le
    have : η * n ≤ 1 * n := mul_le_mul_of_nonneg_right hη1 hnpos.le
    linarith
  obtain ⟨A, hAt, he1, he0⟩ := happ n k C t ε p r ht2 hk2 hkn hεpos hε2 hp0 hp1
    hr hkr
  -- error on `X₁`
  have hsize : (C.size : ℝ) ≤ L := hlt.le
  have hxK : x < K * (t + 1) := by rwa [div_lt_iff₀ hKpos, mul_comm] at ht_lt
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have he1' : uniformProb (univ.powersetCard k) (fun W => ¬ fA A (cliqueEdges W)) ≤ 1 / 3 := by
    have hmono : uniformProb (univ.powersetCard k) (fun W => ¬ fA A (cliqueEdges W)) ≤
        uniformProb (univ.powersetCard k)
          (fun W => ¬ fA A (cliqueEdges W) ∧ C.eval (graphInput (cliqueEdges W)) = true) := by
      apply uP_mono
      intro W hW hb
      exact ⟨hb, (hC _).1 ⟨W, (mem_powersetCard.1 hW).2, subset_refl _⟩⟩
    refine hmono.trans (he1.trans ?_)
    exact err1_bound (by omega) hsize hkpos hnpos hB hB3 (by rw [hL, hcx]) hcpos.le hcK hxK hr0 hrq
  -- the spread law
  obtain ⟨μ, hsp, hbd, hsupp⟩ := exists_law hk2 hkn t A hAt he1'
  -- Lemma 4 with `S = ∅`
  set r4 := α4 * Real.log (((t : ℝ) + 2) / (1 / 6)) /
    p ^ (((t : ℝ) + 2) + ((∅ : Finset (Fin n)).card : ℝ)) with hr4
  have hpp : p ^ (((t : ℝ) + 2) + ((∅ : Finset (Fin n)).card : ℝ)) = p ^ (t + 2) := by
    rw [card_empty, Nat.cast_zero, add_zero, ← Real.rpow_natCast]; push_cast; ring_nf
  have hlog6 : 0 < Real.log (((t : ℝ) + 2) / (1 / 6)) := Real.log_pos (by
    rw [div_div_eq_mul_div, div_one]
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith)
  have hr4pos : 0 < r4 := by rw [hr4, hpp]; positivity
  have hr4le : r4 ≤ (n : ℝ) / (2 * k) := by
    rw [hr4, hpp]
    exact r4_le hα4 hK8 hηinv h3 hkpos hq2R hlog1 htlog hp3' hp0
  have hsp4 : IsSetSpread μ r4 := by
    intro A'
    refine (hsp A').trans ?_
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ hr4pos.le hr4le _
  have hmain := hl4 n μ (1 / 6) ((t : ℝ) + 2) p r4 ∅ (by norm_num) (by norm_num) (by positivity)
    hp0 hp1 rfl hsp4 hbd
  have hincl := lemma4_event_split hp0.le hp1 C hC A μ hsupp
  have hcl := clique_prob_le (n := n) hp0.le hp1 q
  have hcb := clique_bound (show 1 ≤ n by exact_mod_cast hn1) q hq2
  have he0' : (C.size : ℝ) * (2 * (n : ℝ)) ^ (t + 2) * ε ≤ 1 / 8 := err0_bound hsize hL1 hnpos
  linarith

end SpreadMatchCircuit.Matching.Supplement
end

section
/-!
# Eq. (10) for Theorem 8: the approximation step (Section 4.1, Algorithm 2, Lemmas 13, 14)

We prove `Dev.Thm8.ApproxStatement` from the (published) Lemma 4, with `β = α` (Lemma 4's
constant). For each AND gate `g = h₁ ∧ h₂` we run Algorithm 2 on the new positive errors
`N¹_g = {W : g(C_W) = 1, f_{A_g}(C_W) = 0, h₁, h₂ correct on C_W}`; the selector `Z(W)` is a
(classically chosen) member `S₁ ∪ S₂` of `A'_g` contained in `W`.
Lemma 13: `p(N¹_g) ≤ (kr/n)^{t+1}`. Lemma 14: `p(N⁰_g) ≤ (2n)^{t+2} ε`, by a union bound over the
pairs `(S*, T*)` (`S* ∈ A_g`, `S* ⊆ T*`, `2 ≤ |T*| ≤ t+2`), encoded by maps `Fin (t+2) → Fin n` and
subsets of `Fin (t+2)`, and Lemma 4 applied with `S = T*` to the conditioned selector `Z \ S*`.
-/

namespace SpreadMatchCircuit.Matching.Dev.Thm8A

open Finset SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Supplement
open SpreadMatchCircuit.Matching.Dev.Thm8

open scoped Classical

variable {n : ℕ}

/-! ### Generic helpers -/

lemma uniformProb_eq {β : Type} (F : Finset β) (A : β → Prop) [DecidablePred A] :
    uniformProb F A = ((F.filter A).card : ℝ) / F.card := by
  unfold uniformProb
  congr

lemma exists_of_uniformProb_pos {β : Type} (F : Finset β) (A : β → Prop)
    (h : 0 < uniformProb F A) : ∃ x ∈ F, A x := by
  by_contra hc
  push Not at hc
  unfold uniformProb at h
  rw [filter_false_of_mem hc] at h
  simp at h

/-- The push-forward of the uniform law on a nonempty finite set. -/
lemma exists_pushforward {α β : Type} [Fintype α] (S : Finset β) (hS : S.Nonempty)
    (f : β → α) :
    ∃ μ : PMF α, (∀ (A : α → Prop) [DecidablePred A], lawProb μ A =
      ((S.filter fun x => A (f x)).card : ℝ) / S.card) ∧
      ∀ z ∈ lawSupport μ, ∃ x ∈ S, f x = z := by
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  set q : α → ℝ := fun z => ((S.filter fun x => f x = z).card : ℝ) / S.card with hq
  have hq0 : ∀ z, 0 ≤ q z := fun z => by positivity
  have hsum : ∑ z, q z = 1 := by
    simp only [q, ← Finset.sum_div]
    have := card_eq_sum_card_fiberwise (s := S) (t := (univ : Finset α)) (f := f)
      (fun _ _ => mem_coe.mpr (mem_univ _))
    rw [div_eq_one_iff_eq hSpos.ne']
    exact_mod_cast this.symm
  let μ : PMF α := PMF.ofFintype (fun z => ENNReal.ofReal (q z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hq0 z), hsum, ENNReal.ofReal_one])
  refine ⟨μ, ?_, ?_⟩
  · intro A _
    unfold lawProb
    simp only [μ, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hq0 _)]
    simp only [q, ← Finset.sum_div]
    congr 1
    have := card_eq_sum_card_fiberwise (s := S.filter fun x => A (f x)) (t := univ.filter A)
      (f := f) (by intro x hx; simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢; simp [hx.2])
    rw [this]; push_cast
    refine sum_congr (by ext; simp) ?_
    intro z hz
    rw [filter_filter]
    congr 2
    apply filter_congr
    intro x _
    simp only [mem_filter, mem_univ, true_and] at hz
    constructor <;> intro h <;> aesop
  · intro z hz
    simp only [lawSupport, mem_filter, PMF.mem_support_iff] at hz
    have hqz : 0 < q z := by
      by_contra h
      push Not at h
      apply hz.2
      simp [μ, PMF.ofFintype_apply, ENNReal.ofReal_eq_zero.mpr h]
    have hc : 0 < (S.filter fun x => f x = z).card := by
      by_contra h
      push Not at h
      have : (S.filter fun x => f x = z).card = 0 := Nat.le_zero.mp h
      simp [q, this] at hqz
    obtain ⟨x, hx⟩ := card_pos.mp hc
    exact ⟨x, (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩

lemma prob_union {β : Type} (F : Finset β) (A : β → Prop) {s : ℕ} (B : Fin s → β → Prop) (c : ℝ)
    (hsub : ∀ x ∈ F, A x → ∃ h, B h x) (hB : ∀ h, uniformProb F (B h) ≤ c) :
    uniformProb F A ≤ (s : ℝ) * c := by
  unfold uniformProb at hB ⊢
  have hsub' : F.filter A ⊆ Finset.univ.biUnion (fun h => F.filter (B h)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨h, hh⟩ := hsub x hx.1 hx.2
    exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx.1, hh⟩⟩
  have hcard : ((F.filter A).card : ℝ) ≤ ∑ h, ((F.filter (B h)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub').trans Finset.card_biUnion_le
  calc ((F.filter A).card : ℝ) / F.card
      ≤ (∑ h, ((F.filter (B h)).card : ℝ)) / F.card :=
        div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = ∑ h, ((F.filter (B h)).card : ℝ) / F.card := Finset.sum_div _ _ _
    _ ≤ ∑ _h : Fin s, c := Finset.sum_le_sum (fun h _ => hB h)
    _ = (s : ℝ) * c := by simp

lemma rgp_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {P Q : Finset (Edge n) → Prop}
    (h : ∀ X, P X → Q X) : randomGraphProb n p P ≤ randomGraphProb n p Q := by
  rw [rgp_eq, rgp_eq]
  apply sum_le_sum; intro X _
  exact mul_le_mul_of_nonneg_left (Dev.Lemma4.ind_mono (h X))
    (Dev.Lemma4.wt_nonneg hp0 hp1 _ _)

lemma rgp_compl (p : ℝ) (P : Finset (Edge n) → Prop) :
    randomGraphProb n p P + randomGraphProb n p (fun X => ¬ P X) = 1 := by
  rw [rgp_eq, rgp_eq, ← sum_add_distrib, ← Dev.Lemma4.sum_wt_univ (β := Edge n) p]
  apply sum_congr rfl; intro X _
  unfold Dev.Lemma4.ind
  by_cases h : P X <;> simp [h]

lemma rgp_false (p : ℝ) : randomGraphProb n p (fun _ => False) = 0 := by
  unfold randomGraphProb; simp

/-! ### Cliques and `f_A` -/

lemma cliqueEdges_mono {S T : Finset (Fin n)} (h : S ⊆ T) : cliqueEdges S ⊆ cliqueEdges T := by
  intro e he
  rw [Dev.Lemma4.mem_cliqueEdges] at he ⊢
  exact he.trans h

lemma fA_clique {A : Finset (Finset (Fin n))} {W S : Finset (Fin n)} (hW : 2 ≤ W.card)
    (hS : S ∈ A) (hSW : S ⊆ W) : fA A (cliqueEdges W) :=
  ⟨S, hS, W, hSW, hW, subset_refl _⟩

lemma exists_of_fA_clique {A : Finset (Finset (Fin n))} {W : Finset (Fin n)}
    (h : fA A (cliqueEdges W)) : ∃ S ∈ A, S ⊆ W := by
  obtain ⟨S, hS, T, hST, hT2, hTW⟩ := h
  exact ⟨S, hS, hST.trans (subset_of_cliqueEdges_subset hT2 hTW)⟩

lemma endpoints_card (e : Edge n) : (endpoints e).card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _ e.2

/-! ### AND gates and Algorithm 2 -/

/-- The data of an AND gate `g = h₁ ∧ h₂`: predecessor functions and families. -/
structure AG (n : ℕ) where
  h₁ : Finset (Edge n) → Bool
  h₂ : Finset (Edge n) → Bool
  A₁ : Finset (Finset (Fin n))
  A₂ : Finset (Finset (Fin n))

namespace AG

variable (G : AG n)

/-- The function computed at `g`. -/
def g (x : Finset (Edge n)) : Bool := G.h₁ x && G.h₂ x

/-- `X₁ = C_W ∈ E¹` for the function `h` with family `A`. -/
def errPos (h : Finset (Edge n) → Bool) (A : Finset (Finset (Fin n))) (W : Finset (Fin n)) :
    Prop :=
  h (cliqueEdges W) = true ∧ ¬ fA A (cliqueEdges W)

/-- `X ∈ E⁰` for the function `h` with family `A`. -/
def errNeg (h : Finset (Edge n) → Bool) (A : Finset (Finset (Fin n))) (X : Finset (Edge n)) :
    Prop :=
  h X = false ∧ fA A X

/-- `N¹_g` for the current family `A`. -/
def newPos (A : Finset (Finset (Fin n))) (W : Finset (Fin n)) : Prop :=
  errPos G.g A W ∧ ¬ errPos G.h₁ G.A₁ W ∧ ¬ errPos G.h₂ G.A₂ W

/-- `N⁰_g` for the current family `A`. -/
def newNeg (A : Finset (Finset (Fin n))) (X : Finset (Edge n)) : Prop :=
  errNeg G.g A X ∧ ¬ errNeg G.h₁ G.A₁ X ∧ ¬ errNeg G.h₂ G.A₂ X

/-- `A'_g = {S₁ ∪ S₂}`. -/
noncomputable def cands : Finset (Finset (Fin n)) := image₂ (· ∪ ·) G.A₁ G.A₂

/-- The selector `Z(W)`: a member of `A'_g` inside `W` (or `∅`). -/
noncomputable def sel (W : Finset (Fin n)) : Finset (Fin n) :=
  if h : ∃ c ∈ G.cands, c ⊆ W then Classical.choose h else ∅

/-- `p(X₁ ∈ N¹_g)`. -/
noncomputable def P (k : ℕ) (A : Finset (Finset (Fin n))) : ℝ :=
  uniformProb (univ.powersetCard k) (G.newPos A)

/-- `p(S ⊆ Z(X₁) | X₁ ∈ N¹_g)`. -/
noncomputable def core (k : ℕ) (A : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℝ :=
  uniformProb (univ.powersetCard k) (fun W => S ⊆ G.sel W ∧ G.newPos A W) / G.P k A

/-- The sets meeting the threshold of Algorithm 2. -/
noncomputable def qual (k : ℕ) (r : ℝ) (A : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter fun S => (r ^ S.card)⁻¹ ≤ G.core k A S

/-- A largest set meeting the threshold. -/
noncomputable def lc (k : ℕ) (r : ℝ) (A : Finset (Finset (Fin n))) : Finset (Fin n) :=
  if h : (G.qual k r A).Nonempty then Classical.choose (exists_max_image (G.qual k r A) card h)
  else ∅

/-- The loop of Algorithm 2 with a step allowance. -/
noncomputable def loop (k : ℕ) (r : ℝ) (t : ℕ) :
    ℕ → Finset (Finset (Fin n)) → Finset (Finset (Fin n))
  | 0, A => A
  | s + 1, A =>
      if 0 < G.P k A then
        if (G.lc k r A).card ≤ t then loop k r t s (insert (G.lc k r A) A) else A
      else A

/-- Algorithm 2 started from `A_g = ∅`. -/
noncomputable def alg (k : ℕ) (r : ℝ) (t : ℕ) : Finset (Finset (Fin n)) :=
  G.loop k r t (Fintype.card (Finset (Fin n)) + 1) ∅

/-- Both predecessor families have sets of size `≤ t`. -/
def SB (t : ℕ) : Prop := (∀ S ∈ G.A₁, S.card ≤ t) ∧ (∀ S ∈ G.A₂, S.card ≤ t)

variable {G}

lemma newPos_fires {A : Finset (Finset (Fin n))} {W : Finset (Fin n)} (h : G.newPos A W) :
    fA G.A₁ (cliqueEdges W) ∧ fA G.A₂ (cliqueEdges W) := by
  obtain ⟨⟨hg, -⟩, h1, h2⟩ := h
  unfold g at hg
  rw [Bool.and_eq_true] at hg
  exact ⟨by by_contra h; exact h1 ⟨hg.1, h⟩, by by_contra h; exact h2 ⟨hg.2, h⟩⟩

lemma newPos_not {A : Finset (Finset (Fin n))} {W : Finset (Fin n)} (h : G.newPos A W) :
    ¬ fA A (cliqueEdges W) := h.1.2

lemma newNeg_not {A : Finset (Finset (Fin n))} {X : Finset (Edge n)} (h : G.newNeg A X) :
    ¬ (fA G.A₁ X ∧ fA G.A₂ X) := by
  obtain ⟨⟨hg, -⟩, h1, h2⟩ := h
  rintro ⟨f1, f2⟩
  unfold g at hg
  rcases Bool.and_eq_false_iff.mp hg with h | h
  · exact h1 ⟨h, f1⟩
  · exact h2 ⟨h, f2⟩

lemma newNeg_fA {A : Finset (Finset (Fin n))} {X : Finset (Edge n)} (h : G.newNeg A X) :
    fA A X := h.1.2

lemma sel_subset (W : Finset (Fin n)) : G.sel W ⊆ W := by
  unfold sel
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · exact empty_subset _

lemma sel_mem {A : Finset (Finset (Fin n))} {W : Finset (Fin n)} (h : G.newPos A W) :
    G.sel W ∈ G.cands := by
  obtain ⟨f1, f2⟩ := newPos_fires h
  obtain ⟨S1, h1, hS1⟩ := exists_of_fA_clique f1
  obtain ⟨S2, h2, hS2⟩ := exists_of_fA_clique f2
  have hex : ∃ c ∈ G.cands, c ⊆ W := ⟨S1 ∪ S2, mem_image₂_of_mem h1 h2, union_subset hS1 hS2⟩
  unfold sel
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1

lemma cands_card {t : ℕ} (hG : G.SB t) {c : Finset (Fin n)} (hc : c ∈ G.cands) :
    c.card ≤ 2 * t := by
  unfold cands at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_image₂.mp hc
  have := card_union_le a b
  have := hG.1 a ha
  have := hG.2 b hb
  omega

lemma core_empty (k : ℕ) (A : Finset (Finset (Fin n))) (hP : 0 < G.P k A) : G.core k A ∅ = 1 := by
  unfold core
  simp only [empty_subset, true_and]
  exact div_self hP.ne'

lemma qual_nonempty (k : ℕ) (r : ℝ) (A : Finset (Finset (Fin n))) (hP : 0 < G.P k A) :
    (G.qual k r A).Nonempty :=
  ⟨∅, by unfold qual; rw [mem_filter]; refine ⟨mem_univ _, ?_⟩; rw [core_empty k A hP]; simp⟩

lemma lc_spec (k : ℕ) (r : ℝ) (A : Finset (Finset (Fin n))) (hP : 0 < G.P k A) :
    (r ^ (G.lc k r A).card)⁻¹ ≤ G.core k A (G.lc k r A) := by
  have hne := qual_nonempty k r A hP
  unfold lc
  rw [dif_pos hne]
  have := (Classical.choose_spec (exists_max_image (G.qual k r A) card hne)).1
  unfold qual at this
  exact (mem_filter.mp this).2

lemma lc_max (k : ℕ) (r : ℝ) (A : Finset (Finset (Fin n))) (hP : 0 < G.P k A)
    (S : Finset (Fin n)) (hS : (r ^ S.card)⁻¹ ≤ G.core k A S) : S.card ≤ (G.lc k r A).card := by
  have hne := qual_nonempty k r A hP
  unfold lc
  rw [dif_pos hne]
  apply (Classical.choose_spec (exists_max_image (G.qual k r A) card hne)).2
  unfold qual
  exact mem_filter.mpr ⟨mem_univ _, hS⟩

lemma lc_witness (k : ℕ) {r : ℝ} (hr : 0 < r) (A : Finset (Finset (Fin n))) (hP : 0 < G.P k A) :
    ∃ W ∈ (univ : Finset (Fin n)).powersetCard k, G.lc k r A ⊆ G.sel W ∧ G.newPos A W := by
  have hcore := lc_spec k r A hP
  have hpos : 0 < G.core k A (G.lc k r A) := lt_of_lt_of_le (by positivity) hcore
  unfold core at hpos
  have hU := (div_pos_iff_of_pos_right hP).mp hpos
  exact exists_of_uniformProb_pos _ _ hU

lemma lc_not_mem {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : 0 < r) (A : Finset (Finset (Fin n)))
    (hP : 0 < G.P k A) : G.lc k r A ∉ A := by
  intro hmem
  obtain ⟨W, hW, hsub, hx⟩ := lc_witness k hr A hP
  rw [mem_powersetCard] at hW
  exact newPos_not hx (fA_clique (by omega) hmem (hsub.trans (sel_subset W)))

lemma loop_spec {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : 0 < r) (t : ℕ) :
    ∀ (steps : ℕ) (A : Finset (Finset (Fin n))),
      Fintype.card (Finset (Fin n)) < A.card + steps →
      (¬ 0 < G.P k (G.loop k r t steps A)) ∨
      (0 < G.P k (G.loop k r t steps A) ∧ t < (G.lc k r (G.loop k r t steps A)).card) := by
  intro steps
  induction steps with
  | zero =>
    intro A hA
    exfalso
    have := card_le_univ A
    omega
  | succ s ih =>
    intro A hA
    rw [loop]
    by_cases hP : 0 < G.P k A
    · rw [if_pos hP]
      by_cases ht : (G.lc k r A).card ≤ t
      · rw [if_pos ht]
        apply ih
        rw [card_insert_of_notMem (lc_not_mem hk hr A hP)]
        omega
      · rw [if_neg ht]
        exact Or.inr ⟨hP, lt_of_not_ge ht⟩
    · rw [if_neg hP]
      exact Or.inl hP

/-- Members of `A_g` are largest threshold sets of size `≤ t` at an earlier stage. -/
def IsCore (G : AG n) (k : ℕ) (r : ℝ) (t : ℕ) (S : Finset (Fin n)) : Prop :=
  S.card ≤ t ∧ ∃ A', 0 < G.P k A' ∧ S = G.lc k r A'

lemma loop_core (k : ℕ) (r : ℝ) (t : ℕ) :
    ∀ (steps : ℕ) (A : Finset (Finset (Fin n))), (∀ S ∈ A, IsCore G k r t S) →
      ∀ S ∈ G.loop k r t steps A, IsCore G k r t S := by
  intro steps
  induction steps with
  | zero => intro A hA; rw [loop]; exact hA
  | succ s ih =>
    intro A hA
    rw [loop]
    split_ifs with hP ht
    · apply ih
      intro S hS
      rcases mem_insert.mp hS with rfl | hS
      · exact ⟨ht, A, hP, rfl⟩
      · exact hA S hS
    · exact hA
    · exact hA

lemma alg_core (k : ℕ) (r : ℝ) (t : ℕ) (S : Finset (Fin n)) (hS : S ∈ G.alg k r t) :
    IsCore G k r t S :=
  loop_core k r t _ ∅ (by simp) S hS

/-! ### Lemma 13 -/

lemma subset_uprob {k : ℕ} (hk : k ≤ n) (hn : 0 < n) (c : Finset (Fin n)) :
    uniformProb ((univ : Finset (Fin n)).powersetCard k) (fun W => c ⊆ W) ≤
      ((k : ℝ) / n) ^ c.card := by
  rw [uniformProb_eq]
  have h := subset_prob_le hk hn c
  have hC : (((univ : Finset (Fin n)).powersetCard k).card : ℝ) = n.choose k := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [hC]
  have hpos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  rw [div_le_iff₀ hpos]
  exact h

lemma lemma13 (G : AG n) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) {r : ℝ} (hr : 0 < r)
    (hkr : (k : ℝ) * r ≤ n) (t : ℕ) :
    G.P k (G.alg k r t) ≤ ((k : ℝ) * r / n) ^ (t + 1) := by
  have hspec := loop_spec (G := G) hk2 hr t (Fintype.card (Finset (Fin n)) + 1) ∅ (by simp)
  unfold alg
  generalize G.loop k r t (Fintype.card (Finset (Fin n)) + 1) ∅ = A at hspec ⊢
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ (k : ℝ) * r / n := by positivity
  have hx1 : (k : ℝ) * r / n ≤ 1 := by rw [div_le_one hnR]; exact hkr
  rcases hspec with hP | ⟨hP, hct⟩
  · exact (le_of_not_gt hP).trans (pow_nonneg hx0 _)
  set c := G.lc k r A with hc
  have hcore := lc_spec k r A hP
  rw [← hc] at hcore
  unfold core at hcore
  rw [le_div_iff₀ hP] at hcore
  have hU : uniformProb ((univ : Finset (Fin n)).powersetCard k)
      (fun W => c ⊆ G.sel W ∧ G.newPos A W) ≤ ((k : ℝ) / n) ^ c.card :=
    (uP_mono _ _ _ (fun W _ h => h.1.trans (sel_subset W))).trans (subset_uprob hkn hn c)
  have hrj : 0 < r ^ c.card := pow_pos hr _
  have hP1 : G.P k A ≤ r ^ c.card * ((k : ℝ) / n) ^ c.card := by
    have := mul_le_mul_of_nonneg_left (hcore.trans hU) hrj.le
    rwa [← mul_assoc, mul_inv_cancel₀ hrj.ne', one_mul] at this
  calc G.P k A ≤ r ^ c.card * ((k : ℝ) / n) ^ c.card := hP1
    _ = ((k : ℝ) * r / n) ^ c.card := by rw [← mul_pow]; congr 1; ring
    _ ≤ ((k : ℝ) * r / n) ^ (t + 1) := pow_le_pow_of_le_one hx0 hx1 hct

/-! ### Lemma 14 -/

/-- The hypothesis shape of Lemma 4 for the constant `α`. -/
def L4 (α : ℝ) : Prop :=
  ∀ (n : ℕ) (μ : PMF (Finset (Fin n))) (ε t p r : ℝ) (S : Finset (Fin n)),
    0 < ε → ε ≤ 1 / 2 → 0 < t → 0 < p → p ≤ 1 →
    r = α * Real.log (t / ε) / p ^ (t + (S.card : ℝ)) →
    IsSetSpread μ r → IsBoundedSetLaw μ t →
    1 - ε < randomGraphProb n p
      (fun X => ∃ z ∈ lawSupport μ, cliqueEdges (z ∪ S) ⊆ X ∪ cliqueEdges S)

/-- The conditioned selector `Z \ S*` is `r`-spread. -/
lemma spread_part (G : AG n) (k : ℕ) {r : ℝ} (hr : 0 < r) (A' : Finset (Finset (Fin n)))
    (hP : 0 < G.P k A')
    (Sset : Finset (Finset (Fin n)))
    (hSset : Sset = ((univ : Finset (Fin n)).powersetCard k).filter
      (fun W => G.lc k r A' ⊆ G.sel W ∧ G.newPos A' W))
    (hSne : Sset.Nonempty) (B : Finset (Fin n)) :
    ((Sset.filter fun W => B ⊆ G.sel W \ G.lc k r A').card : ℝ) / Sset.card ≤ (r ^ B.card)⁻¹ := by
  set c := G.lc k r A' with hc
  have hSpos : (0 : ℝ) < Sset.card := by exact_mod_cast hSne.card_pos
  by_cases hB0 : B = ∅
  · subst hB0
    simp only [card_empty, pow_zero, inv_one]
    exact div_le_one_of_le₀ (by exact_mod_cast card_filter_le _ _) hSpos.le
  by_cases hdisj : Disjoint B c
  swap
  · have : Sset.filter (fun W => B ⊆ G.sel W \ c) = ∅ := by
      apply filter_false_of_mem
      intro W _ hBW
      apply hdisj
      rw [disjoint_left]
      intro v hv hvc
      exact (mem_sdiff.mp (hBW hv)).2 hvc
    rw [this, card_empty, Nat.cast_zero, zero_div]
    positivity
  set D := B ∪ c with hD
  have hDcard : D.card = B.card + c.card := card_union_of_disjoint hdisj
  have hBpos : 0 < B.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hB0)
  have hfilt : Sset.filter (fun W => B ⊆ G.sel W \ c) =
      ((univ : Finset (Fin n)).powersetCard k).filter (fun W => D ⊆ G.sel W ∧ G.newPos A' W) := by
    rw [hSset, filter_filter]
    apply filter_congr
    intro W _
    rw [hD, union_subset_iff, subset_sdiff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, -⟩; exact ⟨⟨h3, h1⟩, h2⟩
    · rintro ⟨⟨h3, h1⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3, hdisj⟩
  have hnot : G.core k A' D < (r ^ D.card)⁻¹ := by
    by_contra h
    push Not at h
    have := lc_max k r A' hP D h
    rw [← hc] at this
    omega
  have hcore := lc_spec k r A' hP
  rw [← hc] at hcore
  unfold core at hnot hcore
  rw [uniformProb_eq] at hnot hcore
  rw [← hfilt] at hnot
  rw [← hSset] at hcore
  set a := ((Sset.filter fun W => B ⊆ G.sel W \ c).card : ℝ)
  set Dn := ((((univ : Finset (Fin n)).powersetCard k)).card : ℝ)
  set P := G.P k A'
  have hDn : 0 < Dn := by
    obtain ⟨W, hW⟩ := hSne
    rw [hSset] at hW
    have : 0 < ((univ : Finset (Fin n)).powersetCard k).card :=
      card_pos.mpr ⟨_, (mem_filter.mp hW).1⟩
    simp only [Dn]
    exact_mod_cast this
  rw [hDcard, pow_add, mul_inv] at hnot
  have hrm : 0 < (r ^ B.card)⁻¹ := inv_pos.mpr (pow_pos hr _)
  have h3 : a / Dn / P < (r ^ B.card)⁻¹ * (Sset.card / Dn / P) :=
    lt_of_lt_of_le hnot (mul_le_mul_of_nonneg_left hcore hrm.le)
  rw [div_le_iff₀ hSpos]
  rw [div_div, div_div, div_lt_iff₀ (mul_pos hDn hP)] at h3
  have : (r ^ B.card)⁻¹ * (Sset.card / (Dn * P)) * (Dn * P) = (r ^ B.card)⁻¹ * Sset.card := by
    rw [mul_assoc, div_mul_cancel₀ _ (mul_pos hDn hP).ne']
  linarith

lemma partB {α : ℝ} (hα : 0 < α) (hl4 : L4 α) (G : AG n) (k t : ℕ) (ht : 1 ≤ t) {ε p r : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hr : r = α * Real.log ((2 * t + 1) / ε) / p ^ (3 * t + 2))
    (hG : G.SB t) (A' : Finset (Finset (Fin n))) (hP : 0 < G.P k A')
    (T : Finset (Fin n)) (hcT : G.lc k r A' ⊆ T) (hT2 : 2 ≤ T.card) (hTt : T.card ≤ t + 2)
    (M : Finset (Finset (Fin n))) :
    randomGraphProb n p (fun X => G.newNeg M X ∧ cliqueEdges T ⊆ X) ≤ ε := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog : 0 < Real.log ((2 * t + 1) / ε) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hε]; linarith
  have hrpos : 0 < r := by rw [hr]; positivity
  set c := G.lc k r A' with hc
  set Sset := ((univ : Finset (Fin n)).powersetCard k).filter
      (fun W => c ⊆ G.sel W ∧ G.newPos A' W) with hSset
  have hSne : Sset.Nonempty := by
    obtain ⟨W, hW, h1, h2⟩ := lc_witness k hrpos A' hP
    exact ⟨W, mem_filter.mpr ⟨hW, h1, h2⟩⟩
  obtain ⟨μ, hμP, hμS⟩ := exists_pushforward Sset hSne (fun W => G.sel W \ c)
  -- Lemma 4's radius
  set r4 := α * Real.log ((2 * (t : ℝ)) / ε) / p ^ ((2 * (t : ℝ)) + (T.card : ℝ)) with hr4
  have hpow : p ^ ((2 * (t : ℝ)) + (T.card : ℝ)) = p ^ (2 * t + T.card) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  have hlog4 : 0 < Real.log ((2 * (t : ℝ)) / ε) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hε]; linarith
  have hr4pos : 0 < r4 := by rw [hr4, hpow]; positivity
  have hr4le : r4 ≤ r := by
    rw [hr4, hpow, hr]
    apply div_le_div₀ (by positivity)
    · apply mul_le_mul_of_nonneg_left _ hα.le
      apply Real.log_le_log (by positivity)
      apply div_le_div_of_nonneg_right (by linarith) hε.le
    · positivity
    · exact pow_le_pow_of_le_one hp0.le hp1 (by omega)
  have hbounded : IsBoundedSetLaw μ (2 * (t : ℝ)) := by
    intro z hz
    obtain ⟨W, hW, rfl⟩ := hμS z hz
    have hcand := sel_mem (mem_filter.mp hW).2.2
    have h1 := card_le_card (sdiff_subset (s := G.sel W) (t := c))
    have h2 := cands_card hG hcand
    have : (G.sel W \ c).card ≤ 2 * t := by omega
    exact_mod_cast this
  have hspread : IsSetSpread μ r4 := by
    intro B
    rw [hμP]
    refine (spread_part G k hrpos A' hP Sset hSset hSne B).trans ?_
    apply inv_anti₀ (pow_pos hr4pos _)
    exact pow_le_pow_left₀ hr4pos.le hr4le _
  have key := hl4 n μ ε (2 * t) p r4 T hε hε2 (by positivity) hp0 hp1 rfl hspread hbounded
  have hc1 := rgp_compl (n := n) p
    (fun X => ∃ z ∈ lawSupport μ, cliqueEdges (z ∪ T) ⊆ X ∪ cliqueEdges T)
  have hmono : randomGraphProb n p (fun X => G.newNeg M X ∧ cliqueEdges T ⊆ X) ≤
      randomGraphProb n p
        (fun X => ¬ ∃ z ∈ lawSupport μ, cliqueEdges (z ∪ T) ⊆ X ∪ cliqueEdges T) := by
    apply rgp_mono hp0.le hp1
    rintro X ⟨hneg, hTX⟩ ⟨z, hz, hzX⟩
    rw [union_eq_left.mpr hTX] at hzX
    obtain ⟨W, hW, rfl⟩ := hμS z hz
    have hcand := sel_mem (mem_filter.mp hW).2.2
    unfold cands at hcand
    obtain ⟨S1, h1, S2, h2, hS⟩ := mem_image₂.mp hcand
    have hsub : G.sel W ⊆ (G.sel W \ c) ∪ T := by
      intro v hv
      by_cases hvc : v ∈ c
      · exact mem_union_right _ (hcT hvc)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hv, hvc⟩)
    have hcard : 2 ≤ ((G.sel W \ c) ∪ T).card := hT2.trans (card_le_card subset_union_right)
    apply newNeg_not hneg
    have hS1 : S1 ⊆ G.sel W := by rw [← hS]; exact subset_union_left
    have hS2 : S2 ⊆ G.sel W := by rw [← hS]; exact subset_union_right
    exact ⟨⟨S1, h1, _, hS1.trans hsub, hcard, hzX⟩,
      ⟨S2, h2, _, hS2.trans hsub, hcard, hzX⟩⟩
  linarith

/-- Every nonempty set of at most `m` vertices is the range of a map `Fin m → Fin n`. -/
lemma exists_range {m : ℕ} (T : Finset (Fin n)) (hT : T.Nonempty) (hm : T.card ≤ m) :
    ∃ u : Fin m → Fin n, univ.image u = T := by
  obtain ⟨a, ha⟩ := hT
  refine ⟨fun i => if h : i.val < T.card then T.orderEmbOfFin rfl ⟨i.val, h⟩ else a, ?_⟩
  ext v
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    split_ifs with h
    · exact T.orderEmbOfFin_mem rfl _
    · exact ha
  · intro hv
    have : v ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hv
    obtain ⟨j, rfl⟩ := this
    refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hm⟩, ?_⟩
    simp only [j.isLt, dif_pos]

lemma lemma14 {α : ℝ} (hα : 0 < α) (hl4 : L4 α) (G : AG n) (k t : ℕ) (ht : 2 ≤ t) {ε p r : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hr : r = α * Real.log ((2 * t + 1) / ε) / p ^ (3 * t + 2)) (hG : G.SB t) :
    randomGraphProb n p (G.newNeg (G.alg k r t)) ≤ (2 * (n : ℝ)) ^ (t + 2) * ε := by
  set M := G.alg k r t with hM
  let Tf : (Fin (t + 2) → Fin n) × Finset (Fin (t + 2)) → Finset (Fin n) :=
    fun i => univ.image i.1
  let Sf : (Fin (t + 2) → Fin n) × Finset (Fin (t + 2)) → Finset (Fin n) :=
    fun i => i.2.image i.1
  let Ev : (Fin (t + 2) → Fin n) × Finset (Fin (t + 2)) → Finset (Edge n) → Prop :=
    fun i X => (G.newNeg M X ∧ cliqueEdges (Tf i) ⊆ X) ∧
      (Sf i ∈ M ∧ Sf i ⊆ Tf i ∧ 2 ≤ (Tf i).card)
  have hcover : randomGraphProb n p (G.newNeg M) ≤
      randomGraphProb n p (fun X => ∃ i ∈ (univ : Finset ((Fin (t + 2) → Fin n) ×
        Finset (Fin (t + 2)))), Ev i X) := by
    apply rgp_mono hp0.le hp1
    intro X hX
    obtain ⟨S, hS, T, hST, hT2, hTX⟩ := newNeg_fA hX
    obtain ⟨T', hT'T, hT'2⟩ := exists_subset_card_eq hT2
    have hSt := (alg_core k r t S hS).1
    have hT2c : (S ∪ T').card ≤ t + 2 := by
      have := card_union_le S T'; omega
    have hT22 : 2 ≤ (S ∪ T').card := by rw [← hT'2]; exact card_le_card subset_union_right
    set T2 := S ∪ T' with hT2def
    have hT2ne : T2.Nonempty := card_pos.mp (by omega)
    obtain ⟨u, hu⟩ := exists_range T2 hT2ne hT2c
    refine ⟨(u, univ.filter (fun i => u i ∈ S)), mem_univ _, ⟨hX, ?_⟩, ?_, ?_, ?_⟩
    · show cliqueEdges (univ.image u) ⊆ X
      rw [hu]
      exact (cliqueEdges_mono (union_subset hST hT'T)).trans hTX
    · show (univ.filter (fun i => u i ∈ S)).image u ∈ M
      convert hS using 1
      ext v
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hv
        have : v ∈ univ.image u := by rw [hu]; exact mem_union_left _ hv
        obtain ⟨i, -, rfl⟩ := mem_image.mp this
        exact ⟨i, hv, rfl⟩
    · show (univ.filter (fun i => u i ∈ S)).image u ⊆ univ.image u
      exact image_subset_image (filter_subset _ _)
    · show 2 ≤ (univ.image u).card
      rw [hu]; exact hT22
  have hunion := rgp_union hp0.le hp1 (univ : Finset ((Fin (t + 2) → Fin n) ×
        Finset (Fin (t + 2)))) Ev
  have heach : ∀ i, randomGraphProb n p (Ev i) ≤ ε := by
    intro i
    by_cases hc : Sf i ∈ M ∧ Sf i ⊆ Tf i ∧ 2 ≤ (Tf i).card
    · obtain ⟨hSM, hST, hT2⟩ := hc
      obtain ⟨-, A', hP, hA'⟩ := alg_core k r t _ hSM
      have hTt : (Tf i).card ≤ t + 2 := by
        have := card_image_le (s := (univ : Finset (Fin (t + 2)))) (f := i.1)
        rw [card_univ, Fintype.card_fin] at this
        exact this
      refine le_trans (rgp_mono hp0.le hp1 (fun X h => h.1)) ?_
      exact partB hα hl4 G k t (by omega) hε hε2 hp0 hp1 hr hG A' hP (Tf i) (hA' ▸ hST) hT2 hTt M
    · have : randomGraphProb n p (Ev i) ≤ randomGraphProb n p (fun _ => False) :=
        rgp_mono hp0.le hp1 (fun X h => hc h.2)
      rw [rgp_false] at this
      linarith
  have hsum : ∑ i ∈ (univ : Finset ((Fin (t + 2) → Fin n) × Finset (Fin (t + 2)))),
      randomGraphProb n p (Ev i) ≤ (2 * (n : ℝ)) ^ (t + 2) * ε := by
    refine (sum_le_sum (fun i _ => heach i)).trans ?_
    rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_finset,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_pow]; nlinarith [le_refl ε]
  exact hcover.trans (hunion.trans hsum)

end AG

/-! ### The circuit -/

section Circ

variable (C : MonotoneCircuit (Edge n)) (k : ℕ) (r : ℝ) (t : ℕ)

/-- The value of node `g` on the graph `x`. -/
def val (g : Fin C.size) (x : Finset (Edge n)) : Bool := C.nodeValue (graphInput x) g

/-- The approximating family `A_g`. -/
noncomputable def fam (g : Fin C.size) : Finset (Finset (Fin n)) :=
  match C.gate g with
  | .input e => {endpoints e}
  | .and a b =>
      (AG.mk (val C ⟨a.val, a.isLt.trans g.isLt⟩) (val C ⟨b.val, b.isLt.trans g.isLt⟩)
        (fam ⟨a.val, a.isLt.trans g.isLt⟩) (fam ⟨b.val, b.isLt.trans g.isLt⟩)).alg k r t
  | .or a b => fam ⟨a.val, a.isLt.trans g.isLt⟩ ∪ fam ⟨b.val, b.isLt.trans g.isLt⟩
termination_by g.val
decreasing_by
  all_goals first | exact a.isLt | exact b.isLt

/-- The AND gate data at node `g` (a dummy gate at non-AND nodes). -/
noncomputable def gateOf (g : Fin C.size) : AG n :=
  match C.gate g with
  | .and a b =>
      AG.mk (val C ⟨a.val, a.isLt.trans g.isLt⟩) (val C ⟨b.val, b.isLt.trans g.isLt⟩)
        (fam C k r t ⟨a.val, a.isLt.trans g.isLt⟩) (fam C k r t ⟨b.val, b.isLt.trans g.isLt⟩)
  | _ => AG.mk (fun _ => false) (fun _ => false) ∅ ∅

end Circ

variable (C : MonotoneCircuit (Edge n)) (k : ℕ) (r : ℝ) (t : ℕ)

lemma val_input {g : Fin C.size} {e : Edge n} (hg : C.gate g = .input e) (x : Finset (Edge n)) :
    val C g x = decide (e ∈ x) := by
  unfold val
  rw [MonotoneCircuit.nodeValue]
  split <;> simp_all [graphInput]

lemma val_and {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .and a b) (x : Finset (Edge n)) :
    val C g x = (val C ⟨a.val, a.isLt.trans g.isLt⟩ x && val C ⟨b.val, b.isLt.trans g.isLt⟩ x) := by
  unfold val
  rw [MonotoneCircuit.nodeValue]
  split <;> simp_all

lemma val_or {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .or a b) (x : Finset (Edge n)) :
    val C g x = (val C ⟨a.val, a.isLt.trans g.isLt⟩ x || val C ⟨b.val, b.isLt.trans g.isLt⟩ x) := by
  unfold val
  rw [MonotoneCircuit.nodeValue]
  split <;> simp_all

lemma fam_input {g : Fin C.size} {e : Edge n} (hg : C.gate g = .input e) :
    fam C k r t g = {endpoints e} := by
  rw [fam]
  split <;> simp_all

lemma fam_or {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .or a b) :
    fam C k r t g = fam C k r t ⟨a.val, a.isLt.trans g.isLt⟩ ∪
      fam C k r t ⟨b.val, b.isLt.trans g.isLt⟩ := by
  rw [fam]
  split <;> simp_all

lemma gateOf_and {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .and a b) :
    gateOf C k r t g =
      AG.mk (val C ⟨a.val, a.isLt.trans g.isLt⟩) (val C ⟨b.val, b.isLt.trans g.isLt⟩)
        (fam C k r t ⟨a.val, a.isLt.trans g.isLt⟩) (fam C k r t ⟨b.val, b.isLt.trans g.isLt⟩) := by
  rw [gateOf]
  split <;> simp_all

lemma fam_and {g : Fin C.size} {a b : Fin g.val} (hg : C.gate g = .and a b) :
    fam C k r t g = (gateOf C k r t g).alg k r t := by
  rw [gateOf_and C k r t hg, fam]
  split <;> simp_all

lemma fam_good (ht : 2 ≤ t) : ∀ g : Fin C.size, ∀ S ∈ fam C k r t g, S.card ≤ t := by
  intro g
  induction g using WellFoundedLT.induction with
  | _ g ih =>
  rcases hg : C.gate g with e | ⟨a, b⟩ | ⟨a, b⟩
  · rw [fam_input C k r t hg]
    intro S hS
    rw [mem_singleton] at hS
    subst hS
    rw [endpoints_card]; exact ht
  · rw [fam_and C k r t hg]
    intro S hS
    exact (AG.alg_core k r t S hS).1
  · rw [fam_or C k r t hg]
    intro S hS
    rcases mem_union.mp hS with hS | hS
    · exact ih _ a.isLt S hS
    · exact ih _ b.isLt S hS

lemma gateOf_SB (ht : 2 ≤ t) (g : Fin C.size) : (gateOf C k r t g).SB t := by
  rcases hg : C.gate g with e | ⟨a, b⟩ | ⟨a, b⟩
  · rw [gateOf]; split <;> simp_all [AG.SB]
  · rw [gateOf_and C k r t hg]
    exact ⟨fun S hS => fam_good C k r t ht _ S hS, fun S hS => fam_good C k r t ht _ S hS⟩
  · rw [gateOf]; split <;> simp_all [AG.SB]

lemma pos_cover : ∀ g : Fin C.size, ∀ W ∈ (univ : Finset (Fin n)).powersetCard k,
    val C g (cliqueEdges W) = true → ¬ fA (fam C k r t g) (cliqueEdges W) →
    ∃ h : Fin C.size, (gateOf C k r t h).newPos ((gateOf C k r t h).alg k r t) W := by
  intro g
  induction g using WellFoundedLT.induction with
  | _ g ih =>
  intro W hW hv hf
  rcases hg : C.gate g with e | ⟨a, b⟩ | ⟨a, b⟩
  · rw [val_input C hg] at hv
    rw [fam_input C k r t hg] at hf
    simp only [decide_eq_true_eq, Dev.Lemma4.mem_cliqueEdges] at hv
    exact absurd ⟨endpoints e, mem_singleton_self _, endpoints e, subset_refl _,
      (endpoints_card e).ge, cliqueEdges_mono hv⟩ hf
  · have hG := gateOf_and C k r t hg
    have hF := fam_and C k r t hg
    by_cases hn : (gateOf C k r t g).newPos ((gateOf C k r t g).alg k r t) W
    · exact ⟨g, hn⟩
    have h1 : AG.errPos (gateOf C k r t g).g ((gateOf C k r t g).alg k r t) W := by
      refine ⟨?_, ?_⟩
      · rw [hG]; simpa [AG.g, val_and C hg] using hv
      · rwa [← hF]
    have h2 : AG.errPos (gateOf C k r t g).h₁ (gateOf C k r t g).A₁ W ∨
        AG.errPos (gateOf C k r t g).h₂ (gateOf C k r t g).A₂ W := by
      by_contra hc
      push Not at hc
      exact hn ⟨h1, hc.1, hc.2⟩
    rw [hG] at h2
    rcases h2 with h3 | h3
    · exact ih _ a.isLt W hW h3.1 h3.2
    · exact ih _ b.isLt W hW h3.1 h3.2
  · rw [val_or C hg] at hv
    rw [fam_or C k r t hg] at hf
    have hfa : ¬ fA (fam C k r t ⟨a.val, a.isLt.trans g.isLt⟩) (cliqueEdges W) :=
      fun ⟨S, hS, h⟩ => hf ⟨S, mem_union_left _ hS, h⟩
    have hfb : ¬ fA (fam C k r t ⟨b.val, b.isLt.trans g.isLt⟩) (cliqueEdges W) :=
      fun ⟨S, hS, h⟩ => hf ⟨S, mem_union_right _ hS, h⟩
    rcases Bool.or_eq_true_iff.mp hv with hv | hv
    · exact ih _ a.isLt W hW hv hfa
    · exact ih _ b.isLt W hW hv hfb

lemma neg_cover : ∀ g : Fin C.size, ∀ X : Finset (Edge n),
    val C g X = false → fA (fam C k r t g) X →
    ∃ h : Fin C.size, (gateOf C k r t h).newNeg ((gateOf C k r t h).alg k r t) X := by
  intro g
  induction g using WellFoundedLT.induction with
  | _ g ih =>
  intro X hv hf
  rcases hg : C.gate g with e | ⟨a, b⟩ | ⟨a, b⟩
  · rw [val_input C hg] at hv
    rw [fam_input C k r t hg] at hf
    simp only [decide_eq_false_iff_not] at hv
    obtain ⟨S, hS, T, hST, -, hTX⟩ := hf
    rw [mem_singleton] at hS
    subst hS
    exact (hv (hTX (Dev.Lemma4.mem_cliqueEdges.mpr hST))).elim
  · have hG := gateOf_and C k r t hg
    have hF := fam_and C k r t hg
    by_cases hn : (gateOf C k r t g).newNeg ((gateOf C k r t g).alg k r t) X
    · exact ⟨g, hn⟩
    have h1 : AG.errNeg (gateOf C k r t g).g ((gateOf C k r t g).alg k r t) X := by
      refine ⟨?_, ?_⟩
      · rw [hG]; simpa [AG.g, val_and C hg] using hv
      · rwa [← hF]
    have h2 : AG.errNeg (gateOf C k r t g).h₁ (gateOf C k r t g).A₁ X ∨
        AG.errNeg (gateOf C k r t g).h₂ (gateOf C k r t g).A₂ X := by
      by_contra hc
      push Not at hc
      exact hn ⟨h1, hc.1, hc.2⟩
    rw [hG] at h2
    rcases h2 with h3 | h3
    · exact ih _ a.isLt X h3.1 h3.2
    · exact ih _ b.isLt X h3.1 h3.2
  · rw [val_or C hg] at hv
    rw [fam_or C k r t hg] at hf
    simp only [Bool.or_eq_false_iff] at hv
    obtain ⟨S, hS, h⟩ := hf
    rcases mem_union.mp hS with hS | hS
    · exact ih _ a.isLt X hv.1 ⟨S, hS, h⟩
    · exact ih _ b.isLt X hv.2 ⟨S, hS, h⟩

end SpreadMatchCircuit.Matching.Dev.Thm8A

namespace SpreadMatchCircuit.Matching.Dev.Thm8

open Finset SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Supplement
open SpreadMatchCircuit.Matching.Dev.Thm8A

/-- Eq. (10): the approximation step, from Lemma 4 (with `β = α`). -/
theorem approxStatement_holds : ApproxStatement := by
  obtain ⟨α, hα, hl4⟩ := lemma_4
  refine ⟨α, hα, ?_⟩
  intro n k C t ε p r ht hk2 hkn hε hε2 hp0 hp1 hr hkr
  have hlog : 0 < Real.log ((2 * t + 1) / ε) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hε]
    have : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hrpos : 0 < r := by rw [hr]; positivity
  have hr' : r = α * Real.log ((2 * (t : ℝ) + 1) / ε) / p ^ (3 * t + 2) := hr
  refine ⟨fam C k r t C.output, fam_good C k r t ht _, ?_, ?_⟩
  · apply prob_union _ _
      (fun h W => (gateOf C k r t h).newPos ((gateOf C k r t h).alg k r t) W)
    · intro W hW hA
      exact pos_cover C k r t C.output W hW hA.2 hA.1
    · intro h
      exact AG.lemma13 _ hk2 hkn hrpos hkr t
  · have h1 : randomGraphProb n p (fun X => fA (fam C k r t C.output) X ∧
        C.eval (graphInput X) = false) ≤
        randomGraphProb n p (fun X => ∃ h ∈ (univ : Finset (Fin C.size)),
          (gateOf C k r t h).newNeg ((gateOf C k r t h).alg k r t) X) := by
      apply rgp_mono hp0.le hp1
      intro X hX
      obtain ⟨h, hh⟩ := neg_cover C k r t C.output X hX.2 hX.1
      exact ⟨h, mem_univ _, hh⟩
    refine h1.trans ((rgp_union hp0.le hp1 _ _).trans ?_)
    calc ∑ h ∈ (univ : Finset (Fin C.size)),
          randomGraphProb n p ((gateOf C k r t h).newNeg ((gateOf C k r t h).alg k r t))
        ≤ ∑ _h ∈ (univ : Finset (Fin C.size)), (2 * (n : ℝ)) ^ (t + 2) * ε :=
          sum_le_sum (fun h _ => AG.lemma14 hα hl4 _ k t ht hε hε2 hp0 hp1 hr'
            (gateOf_SB C k r t ht h))
      _ = (C.size : ℝ) * (2 * (n : ℝ)) ^ (t + 2) * ε := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end SpreadMatchCircuit.Matching.Dev.Thm8
end

section
/-!
# Theorem 8 (exponential lower bound for clique), from the published Lemma 4

`chk_theorem_8_of_approx` (Thm8.lean) reduces Theorem 8 to Eq. (10), `ApproxStatement`, which is
proved in Thm8Approx.lean from Lemma 4. The only `sorry`-carrying dependency is the published
Lemma 4 stub `Theorems.Thm_SpreadMatchCircuit_Matching_Supplement_lemma_4`.
-/

namespace SpreadMatchCircuit.Matching.Supplement

open SpreadMatchCircuit.Matching

theorem chk_theorem_8 :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (n k q : ℕ), Real.log (n : ℝ) < η * (q : ℝ) → η * (q : ℝ) < (k : ℝ) →
        (k : ℝ) * (q : ℝ) ≤ η * (n : ℝ) →
        ∀ C : MonotoneCircuit (Edge n), DistinguishesCliques C k q →
          ((n : ℝ) / ((k : ℝ) * (q : ℝ))) ^ (c * (q : ℝ) / Real.log (n : ℝ)) ≤
            (C.size : ℝ) :=
  chk_theorem_8_of_approx Dev.Thm8.approxStatement_holds

end SpreadMatchCircuit.Matching.Supplement
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.Supplement.chk_theorem_8 := @SpreadMatchCircuit.Matching.Supplement.chk_theorem_8
