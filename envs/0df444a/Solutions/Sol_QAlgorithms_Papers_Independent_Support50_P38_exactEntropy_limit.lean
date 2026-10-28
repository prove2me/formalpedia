-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P38.exactEntropy_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:01:59.186512+00:00
-- url     : https://prove2.me/submissions/b8526cc7-a417-45f6-be6a-5d1f8d8c08cd

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

-- ===== P38E =====

noncomputable section

namespace X4P38E

open QAlgorithms.Papers.Independent.Support50.P38 Finset Filter
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

variable {A B : Type} [Fintype A] [Fintype B]

lemma sum_prod_word {n : ℕ} (f : Fin n → A → ℝ) :
    ∑ x : Fin n → A, ∏ i, f i (x i) = ∏ i, ∑ a, f i a := by
  rw [Finset.prod_univ_sum]; simp

lemma wordMass_law {n : ℕ} (p : A → ℝ) (hp : IsLaw p) : IsLaw (wordMass (n := n) p) := by
  refine ⟨fun x => prod_nonneg fun i _ => hp.1 _, ?_⟩
  unfold wordMass
  rw [sum_prod_word (fun _ a => p a)]; simp [hp.2]

lemma wordChannel_law {n : ℕ} (w : A → B → ℝ) (hw : IsStochastic w) (x : Fin n → A) :
    IsLaw (wordChannel w x) := by
  refine ⟨fun y => prod_nonneg fun i _ => (hw (x i)).1 _, ?_⟩
  unfold wordChannel
  rw [sum_prod_word (fun i b => w (x i) b)]; simp [(hw _).2]

lemma shannon_nonneg {K : Type} [Fintype K] (q : K → ℝ) (hq : IsLaw q) : 0 ≤ shannon q := by
  unfold shannon
  rw [neg_nonneg]
  refine sum_nonpos fun k _ => ?_
  have h0 := hq.1 k
  have h1 : q k ≤ 1 := by
    rw [← hq.2]; exact single_le_sum (fun j _ => hq.1 j) (mem_univ k)
  exact mul_nonpos_of_nonneg_of_nonpos h0 (Real.logb_nonpos one_lt_two h0 h1)

lemma shannon_equiv {K L : Type} [Fintype K] [Fintype L] (e : K ≃ L) (q : L → ℝ) :
    shannon (fun k => q (e k)) = shannon q := by
  unfold shannon; congr 1; exact e.sum_comp (fun l => q l * Real.logb 2 (q l))

lemma shannon_prod {K L : Type} [Fintype K] [Fintype L] (q : K → ℝ) (r : L → ℝ)
    (hq : IsLaw q) (hr : IsLaw r) :
    shannon (fun z : K × L => q z.1 * r z.2) = shannon q + shannon r := by
  unfold shannon
  have key : ∀ k l, q k * r l * Real.logb 2 (q k * r l) =
      (q k * Real.logb 2 (q k)) * r l + q k * (r l * Real.logb 2 (r l)) := by
    intro k l
    by_cases hk : q k = 0
    · simp [hk]
    by_cases hl : r l = 0
    · simp [hl]
    rw [Real.logb_mul hk hl]; ring
  rw [Fintype.sum_prod_type]
  simp_rw [key]
  have h2 : ∀ k, ∑ l, ((q k * Real.logb 2 (q k)) * r l + q k * (r l * Real.logb 2 (r l))) =
      q k * Real.logb 2 (q k) + q k * ∑ l, r l * Real.logb 2 (r l) := by
    intro k; rw [sum_add_distrib, ← mul_sum, ← mul_sum, hr.2, mul_one]
  simp_rw [h2]; rw [sum_add_distrib, ← sum_mul, hq.2, one_mul]; ring

/-- splitting a word of length n+m -/
def splitE (n m : ℕ) (X : Type) : (Fin (n + m) → X) ≃ (Fin n → X) × (Fin m → X) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl X)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

lemma splitE_fst {n m : ℕ} {X : Type} (x : Fin (n + m) → X) (i : Fin n) :
    (splitE n m X x).1 i = x (Fin.castAdd m i) := by
  simp [splitE, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]

lemma splitE_snd {n m : ℕ} {X : Type} (x : Fin (n + m) → X) (i : Fin m) :
    (splitE n m X x).2 i = x (Fin.natAdd n i) := by
  simp [splitE, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]

lemma prod_split {n m : ℕ} {X : Type} (f : X → ℝ) (x : Fin (n + m) → X) :
    ∏ i, f (x i) = (∏ i, f ((splitE n m X x).1 i)) * ∏ i, f ((splitE n m X x).2 i) := by
  rw [Fin.prod_univ_add]; simp [splitE_fst, splitE_snd]

lemma prod_split2 {n m : ℕ} (f : A → B → ℝ) (x : Fin (n + m) → A) (y : Fin (n + m) → B) :
    ∏ i, f (x i) (y i) = (∏ i, f ((splitE n m A x).1 i) ((splitE n m B y).1 i)) *
      ∏ i, f ((splitE n m A x).2 i) ((splitE n m B y).2 i) := by
  rw [Fin.prod_univ_add]; simp [splitE_fst, splitE_snd]

lemma sum_split {n m : ℕ} {X : Type} [Fintype X] (g : (Fin (n + m) → X) → ℝ) :
    ∑ x, g x = ∑ x1, ∑ x2, g ((splitE n m X).symm (x1, x2)) := by
  rw [← Fintype.sum_prod_type', ← (splitE n m X).symm.sum_comp]

/-- the product code -/
def prodCode {n m : ℕ} (c1 : DistributionCompressionCode A B n)
    (c2 : DistributionCompressionCode A B m) : DistributionCompressionCode A B (n + m) where
  size := c1.size * c2.size
  size_pos := Nat.mul_pos c1.size_pos c2.size_pos
  enc x k := c1.enc (splitE n m A x).1 (finProdFinEquiv.symm k).1 *
    c2.enc (splitE n m A x).2 (finProdFinEquiv.symm k).2
  enc_law := by
    intro x
    refine ⟨fun k => mul_nonneg ((c1.enc_law _).1 _) ((c2.enc_law _).1 _), ?_⟩
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, (c2.enc_law _).2, mul_one, (c1.enc_law _).2]
  dec k y := c1.dec (finProdFinEquiv.symm k).1 (splitE n m B y).1 *
    c2.dec (finProdFinEquiv.symm k).2 (splitE n m B y).2
  dec_law := by
    intro k
    refine ⟨fun y => mul_nonneg ((c1.dec_law _).1 _) ((c2.dec_law _).1 _), ?_⟩
    rw [sum_split]
    simp only [Equiv.apply_symm_apply]
    simp_rw [← mul_sum, (c2.dec_law _).2, mul_one, (c1.dec_law _).2]

lemma sum_pc {n m : ℕ} (c1 : DistributionCompressionCode A B n)
    (c2 : DistributionCompressionCode A B m) (g : Fin (c1.size * c2.size) → ℝ) :
    (∑ k : Fin (prodCode c1 c2).size, g k) = ∑ k1, ∑ k2, g (finProdFinEquiv (k1, k2)) := by
  rw [← Fintype.sum_prod_type']; exact (finProdFinEquiv.sum_comp g).symm

lemma prodCode_output {n m : ℕ} (c1 : DistributionCompressionCode A B n)
    (c2 : DistributionCompressionCode A B m) (x : Fin (n + m) → A) (y : Fin (n + m) → B) :
    (prodCode c1 c2).output x y =
      c1.output (splitE n m A x).1 (splitE n m B y).1 *
        c2.output (splitE n m A x).2 (splitE n m B y).2 := by
  unfold DistributionCompressionCode.output
  refine (sum_pc c1 c2 (fun k => (prodCode c1 c2).enc x k * (prodCode c1 c2).dec k y)).trans ?_
  rw [sum_mul_sum]
  refine sum_congr rfl fun k1 _ => sum_congr rfl fun k2 _ => ?_
  simp only [prodCode, Equiv.symm_apply_apply]
  ring

lemma prodCode_exact {n m : ℕ} (w : A → B → ℝ) (c1 : DistributionCompressionCode A B n)
    (c2 : DistributionCompressionCode A B m) (h1 : c1.Exact w) (h2 : c2.Exact w) :
    (prodCode c1 c2).Exact w := by
  intro x y
  rw [prodCode_output, h1, h2]
  unfold wordChannel; rw [prod_split2 w x y]

lemma prodCode_msg {n m : ℕ} (p : A → ℝ) (c1 : DistributionCompressionCode A B n)
    (c2 : DistributionCompressionCode A B m) (k : Fin (prodCode c1 c2).size) :
    (prodCode c1 c2).messageLaw p k =
      c1.messageLaw p (finProdFinEquiv.symm k).1 * c2.messageLaw p (finProdFinEquiv.symm k).2 := by
  unfold DistributionCompressionCode.messageLaw
  simp only [prodCode]
  rw [sum_split, sum_mul_sum]
  refine sum_congr rfl fun x1 _ => sum_congr rfl fun x2 _ => ?_
  simp only [Equiv.apply_symm_apply]
  unfold wordMass
  rw [prod_split p ((splitE n m A).symm (x1, x2))]
  simp only [Equiv.apply_symm_apply]
  ring

lemma msg_law {n : ℕ} (p : A → ℝ) (hp : IsLaw p) (c : DistributionCompressionCode A B n) :
    IsLaw (c.messageLaw p) := by
  refine ⟨fun k => sum_nonneg fun x _ =>
    mul_nonneg ((wordMass_law p hp).1 x) ((c.enc_law x).1 k), ?_⟩
  unfold DistributionCompressionCode.messageLaw
  rw [sum_comm]
  simp_rw [← mul_sum, (c.enc_law _).2, mul_one]
  exact (wordMass_law p hp).2

/-- the label code -/
def labelCode [Nonempty A] (n : ℕ) (w : A → B → ℝ) (hw : IsStochastic w) :
    DistributionCompressionCode A B n where
  size := Fintype.card (Fin n → A)
  size_pos := Fintype.card_pos
  enc x k := if k = Fintype.equivFin _ x then 1 else 0
  enc_law := by
    intro x
    refine ⟨fun k => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp
  dec k y := wordChannel w ((Fintype.equivFin _).symm k) y
  dec_law := fun k => wordChannel_law w hw _

lemma labelCode_exact [Nonempty A] (n : ℕ) (w : A → B → ℝ) (hw : IsStochastic w) :
    (labelCode n w hw).Exact w := by
  intro x y
  unfold DistributionCompressionCode.output labelCode
  simp

def Sset (p : A → ℝ) (w : A → B → ℝ) (n : ℕ) : Set ℝ :=
  {r | ∃ c : DistributionCompressionCode A B n, c.Exact w ∧ shannon (c.messageLaw p) = r}

lemma Sset_nonempty [Nonempty A] (p : A → ℝ) (w : A → B → ℝ) (hw : IsStochastic w) (n : ℕ) :
    (Sset p w n).Nonempty := ⟨_, labelCode n w hw, labelCode_exact n w hw, rfl⟩

lemma Sset_nonneg (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (n : ℕ) :
    ∀ r ∈ Sset p w n, 0 ≤ r := by
  rintro r ⟨c, -, rfl⟩; exact shannon_nonneg _ (msg_law p hp c)

lemma Sset_bdd (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (n : ℕ) :
    BddBelow (Sset p w n) := ⟨0, Sset_nonneg p w hp n⟩

lemma S_eq (p : A → ℝ) (w : A → B → ℝ) (n : ℕ) : exactEntropy p w n = sInf (Sset p w n) := rfl

lemma S_nonneg (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (n : ℕ) :
    0 ≤ exactEntropy p w n := Real.sInf_nonneg (Sset_nonneg p w hp n)

theorem subadd [Nonempty A] (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (n m : ℕ) : exactEntropy p w (n + m) ≤ exactEntropy p w n + exactEntropy p w m := by
  have key : ∀ r1 ∈ Sset p w n, ∀ r2 ∈ Sset p w m, exactEntropy p w (n + m) ≤ r1 + r2 := by
    rintro r1 ⟨c1, h1, rfl⟩ r2 ⟨c2, h2, rfl⟩
    refine csInf_le (Sset_bdd p w hp _) ⟨prodCode c1 c2, prodCode_exact w c1 c2 h1 h2, ?_⟩
    have h := shannon_prod _ _ (msg_law p hp c1) (msg_law p hp c2)
    rw [← h]
    unfold shannon
    congr 1
    refine (sum_pc c1 c2 (fun k => (prodCode c1 c2).messageLaw p k *
      Real.logb 2 ((prodCode c1 c2).messageLaw p k))).trans ?_
    rw [Fintype.sum_prod_type]
    have hm : ∀ k1 k2, (prodCode c1 c2).messageLaw p (finProdFinEquiv (k1, k2)) =
        c1.messageLaw p k1 * c2.messageLaw p k2 := fun k1 k2 => by
      exact (prodCode_msg p c1 c2 _).trans (by simp)
    simp only [hm]
  have h1 : ∀ r2 ∈ Sset p w m, exactEntropy p w (n + m) - r2 ≤ exactEntropy p w n := by
    intro r2 hr2
    exact le_csInf (Sset_nonempty p w hw n) fun r1 hr1 => by linarith [key r1 hr1 r2 hr2]
  have h2 : exactEntropy p w (n + m) - exactEntropy p w n ≤ exactEntropy p w m :=
    le_csInf (Sset_nonempty p w hw m) fun r2 hr2 => by linarith [h1 r2 hr2]
  linarith

theorem main [Nonempty A] (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w) :
    (∀ n m, exactEntropy p w (n + m) ≤ exactEntropy p w n + exactEntropy p w m) ∧
    Tendsto (fun n : ℕ => exactEntropy p w (n + 1) / (n + 1 : ℝ))
      atTop (nhds (exactEntropyRate p w)) := by
  refine ⟨subadd p w hp hw, ?_⟩
  have hs : Subadditive (fun n => exactEntropy p w n) := fun n m => subadd p w hp hw n m
  have hbdd : BddBelow (Set.range fun n => exactEntropy p w n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (S_nonneg p w hp n) (Nat.cast_nonneg n)⟩
  have hT := hs.tendsto_lim hbdd
  have hlim : hs.lim = exactEntropyRate p w := by
    rw [Subadditive.lim]; unfold exactEntropyRate
    congr 1
  rw [hlim] at hT
  have := hT.comp (tendsto_add_atTop_nat 1)
  refine this.congr fun n => ?_
  simp [Function.comp]

end X4P38E

-- ===== P38ESol =====

noncomputable section

open QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

theorem solution {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A → ℝ) (w : A → B → ℝ)
    (hp : IsLaw p) (hw : IsStochastic w) :
    (∀ n m, exactEntropy p w (n + m) ≤ exactEntropy p w n + exactEntropy p w m) ∧
    Tendsto (fun n : ℕ => exactEntropy p w (n + 1) / (n + 1 : ℝ))
      atTop (nhds (exactEntropyRate p w)) :=
  X4P38E.main p w hp hw
