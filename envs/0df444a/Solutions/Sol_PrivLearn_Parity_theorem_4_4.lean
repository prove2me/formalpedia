-- Prove2me | solution 1 for PrivLearn.Parity.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T05:17:00.203287+00:00
-- url     : https://prove2.me/submissions/c1a914bb-cd1f-445e-8955-1f686de4b9ac

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Parity_Learner
import Definitions.Def_PrivLearn_Parity_Amplified

-- ParityProof.IIDMarginal
namespace ParityProof
open scoped BigOperators Classical
lemma weighted_reindex {ι κ α R : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [CommSemiring R] (e : ι ≃ κ) (w : α → R) (F : (ι → α) → R) :
    (∑ x : κ → α, (∏ j, w (x j))*F (fun i => x (e i))) =
      ∑ y : ι → α, (∏ i, w (y i))*F y := by
  let E : (κ → α) ≃ (ι → α) := Equiv.arrowCongr e.symm (Equiv.refl α)
  apply Fintype.sum_equiv E
  intro x
  have hp := e.prod_comp (fun j => w (x j))
  change (∏ j, w (x j))*F (fun i => x (e i)) =
    (∏ i, w (x (e i)))*F (fun i => x (e i))
  rw [hp]
lemma weighted_sum_left {ι κ α R : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [CommSemiring R] (w : α → R) (hw : ∑ a, w a = 1) (F : (ι → α) → R) :
    (∑ x : ι ⊕ κ → α, (∏ j, w (x j))*F (fun i => x (Sum.inl i))) =
      ∑ y : ι → α, (∏ i, w (y i))*F y := by
  have he : (∑ x : ι ⊕ κ → α, (∏ j, w (x j))*F (fun i => x (Sum.inl i))) =
      ∑ y : (ι → α) × (κ → α), ((∏ i, w (y.1 i))*F y.1)*(∏ j, w (y.2 j)) := by
    apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ α)
    intro x
    change (∏ j, w (x j))*F (fun i => x (Sum.inl i)) =
      ((∏ i, w (x (Sum.inl i)))*F (fun i => x (Sum.inl i)))*(∏ j, w (x (Sum.inr j)))
    rw [Fintype.prod_sum_type]
    ring
  rw [he, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  have hz : (∑ z : κ → α, ∏ j, w (z j)) = 1 := by
    have h := Fintype.prod_sum (fun (_ : κ) (a : α) => w a)
    simpa [hw] using h.symm
  simp [hz]
lemma weighted_injective_marginal {ι κ α R : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [CommSemiring R] (e : ι ↪ κ) (w : α → R) (hw : ∑ a, w a = 1)
    (F : (ι → α) → R) :
    (∑ x : κ → α, (∏ j, w (x j))*F (fun i => x (e i))) =
      ∑ y : ι → α, (∏ i, w (y i))*F y := by
  let J := {j : κ // j ∉ Set.range e}
  let E : ι ⊕ J ≃ κ :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl J)).trans
      (Equiv.Set.sumCompl (Set.range e))
  have h := weighted_reindex E w (fun x : ι ⊕ J → α => F (fun i => x (Sum.inl i)))
  apply h.trans
  convert weighted_sum_left (κ := J) w hw F using 1
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
end ParityProof

-- ParityProof.BlockIndices
open PrivLearn.Parity
namespace ParityProof
abbrev BlockIndex (k b s : ℕ) := (Fin k × Fin b) ⊕ Fin s
def blockEmbedding {k b s n : ℕ} (hn : k*b+s ≤ n) : BlockIndex k b s ↪ Fin n :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin s))).trans finSumFinEquiv).toEmbedding.trans
    (Fin.castLEEmb hn)
lemma blockEmbedding_train_val {k b s n : ℕ} (hn : k*b+s ≤ n) (j : Fin k) (t : Fin b) :
    (blockEmbedding hn (Sum.inl (j,t))).val = j.val*b+t.val := by
  simp [blockEmbedding, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
lemma blockEmbedding_test_val {k b s n : ℕ} (hn : k*b+s ≤ n) (t : Fin s) :
    (blockEmbedding hn (Sum.inr t)).val = k*b+t.val := by rfl
lemma trainBlock_eq_project {d k b s n : ℕ} (hn : k*b+s ≤ n)
    (z : Fin n → Example d) (j : Fin k) :
    trainBlock z b j.val = fun t => z (blockEmbedding hn (Sum.inl (j,t))) := by
  funext t
  have ht : j.val*b+t.val < n := by
    rw [← blockEmbedding_train_val hn j t]
    exact (blockEmbedding hn (Sum.inl (j,t))).isLt
  simp only [trainBlock, entry, dif_pos ht]
  congr 1
  apply Fin.ext
  exact (blockEmbedding_train_val hn j t).symm
lemma testSet_eq_project {d k b s n : ℕ} (hn : k*b+s ≤ n) (z : Fin n → Example d) :
    testSet z k b s = fun t => z (blockEmbedding hn (Sum.inr t)) := by
  funext t
  have ht : k*b+t.val < n := (blockEmbedding hn (Sum.inr t)).isLt
  simp only [testSet, entry, dif_pos ht]
  rfl
lemma trainBlock_labeled {d k b s n : ℕ} (hn : k*b+s ≤ n)
    (r : Fin d → ZMod 2) (x : Fin n → (Fin d → ZMod 2)) (j : Fin k) :
    trainBlock (labeled r x) b j.val = labeled r (fun t => x (blockEmbedding hn (Sum.inl (j,t)))) := by
  rw [trainBlock_eq_project hn]
  rfl
lemma testSet_labeled {d k b s n : ℕ} (hn : k*b+s ≤ n)
    (r : Fin d → ZMod 2) (x : Fin n → (Fin d → ZMod 2)) :
    testSet (labeled r x) k b s = labeled r (fun t => x (blockEmbedding hn (Sum.inr t))) := by
  rw [testSet_eq_project hn]
  rfl
end ParityProof

-- ParityProof.BlockFactorization
namespace ParityProof
open scoped BigOperators Classical
lemma weighted_sum_both {ι κ α R : Type*} [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq ι] [DecidableEq κ]
    [CommSemiring R] (w : α → R) (F : (ι → α) → R) (G : (κ → α) → R) :
    (∑ x : ι ⊕ κ → α, (∏ j, w (x j))*F (fun i => x (Sum.inl i))*G (fun j => x (Sum.inr j))) =
      (∑ y : ι → α, (∏ i, w (y i))*F y)*(∑ z : κ → α, (∏ j, w (z j))*G z) := by
  have he : (∑ x : ι ⊕ κ → α, (∏ j, w (x j))*F (fun i => x (Sum.inl i))*G (fun j => x (Sum.inr j))) =
      ∑ y : (ι → α) × (κ → α), ((∏ i, w (y.1 i))*F y.1)*((∏ j, w (y.2 j))*G y.2) := by
    apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ α)
    intro x
    change (∏ j, w (x j))*F (fun i => x (Sum.inl i))*G (fun j => x (Sum.inr j)) =
      ((∏ i, w (x (Sum.inl i)))*F (fun i => x (Sum.inl i)))*
      ((∏ j, w (x (Sum.inr j)))*G (fun j => x (Sum.inr j)))
    rw [Fintype.prod_sum_type]
    ring
  rw [he, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
lemma weighted_matrix_product {ι κ α R : Type*} [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq ι] [DecidableEq κ]
    [CommSemiring R] (w : α → R) (A : ι → (κ → α) → R) :
    (∑ x : ι × κ → α, (∏ j, w (x j))*(∏ i,A i (fun t => x (i,t)))) =
      ∏ i, ∑ y : κ → α, (∏ t,w (y t))*A i y := by
  have he : (∑ x : ι × κ → α, (∏ j, w (x j))*(∏ i,A i (fun t => x (i,t)))) =
      ∑ y : ι → κ → α, ∏ i, (∏ t,w (y i t))*A i (y i) := by
    apply Fintype.sum_equiv (Equiv.curry ι κ α)
    intro x
    change (∏ j, w (x j))*(∏ i,A i (fun t => x (i,t))) =
      ∏ i,(∏ t,w (x (i,t)))*A i (fun t => x (i,t))
    rw [Fintype.prod_prod_type, Finset.prod_mul_distrib]
  rw [he, Fintype.prod_sum]
lemma weighted_block_factorization {k b s : ℕ} {α O R : Type*} [Fintype α] [Fintype O]
    [CommSemiring R] (w : α → R) (A : (Fin b → α) → O → R)
    (B : (Fin k → O) → (Fin s → α) → R) :
    (∑ Z : BlockIndex k b s → α, (∏ i,w (Z i)) *
      ∑ H : Fin k → O, (∏ j,A (fun t=>Z (Sum.inl (j,t))) (H j))*B H (fun t=>Z (Sum.inr t))) =
    ∑ H : Fin k → O, (∏ j,∑ x : Fin b → α,(∏ t,w (x t))*A x (H j))*
      (∑ T : Fin s → α,(∏ t,w (T t))*B H T) := by
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H _
  conv_lhs => simp only [← mul_assoc]
  rw [weighted_sum_both w (fun X : Fin k × Fin b → α => ∏ j,A (fun t => X (j,t)) (H j)) (B H)]
  rw [weighted_matrix_product w (fun j x => A x (H j))]
end ParityProof

-- ParityProof.FiniteBasics
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators
lemma output_measurable {d : ℕ} (E : Set (Option (Fin d → ZMod 2))) : MeasurableSet E := by
  trivial
lemma selWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (S : Finset (Fin n)) :
    0 ≤ selWeight p n S := mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)
lemma selWeight_sum (p : ℝ) (n : ℕ) : ∑ S : Finset (Fin n), selWeight p n S = 1 := by
  classical
  have h := Fintype.prod_add (fun _ : Fin n => p) (fun _ => 1 - p)
  simpa [selWeight, Finset.prod_const, Finset.card_compl] using h.symm
noncomputable def solutionLaw {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) :
    Measure (Option (Fin d → ZMod 2)) :=
  if (solSpace z S).Nonempty then
    ∑ r ∈ solSpace z S, ((solSpace z S).card : ENNReal)⁻¹ • Measure.dirac (some r)
  else Measure.dirac none
lemma solutionLaw_univ {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) :
    solutionLaw z S Set.univ = 1 := by
  classical
  unfold solutionLaw
  split_ifs with h
  · have hc : (solSpace z S).card ≠ 0 := Finset.card_ne_zero.mpr h
    simp [hc, ENNReal.mul_inv_cancel]
  · simp
instance solutionLaw_probability {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) :
    IsProbabilityMeasure (solutionLaw z S) := ⟨solutionLaw_univ z S⟩
lemma algA_eq {d n : ℕ} (ε : ℝ) (z : Fin n → Example d) :
    algA ε z = (1 / 2 : ENNReal) • Measure.dirac none +
      (1 / 2 : ENNReal) • ∑ S : Finset (Fin n),
        ENNReal.ofReal (selWeight (ε / 4) n S) • solutionLaw z S := rfl
lemma algA_univ {d n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hε4 : ε ≤ 4)
    (z : Fin n → Example d) : algA ε z Set.univ = 1 := by
  classical
  have hp : 0 ≤ ε / 4 := by positivity
  have hp1 : ε / 4 ≤ 1 := by linarith
  have hs : ∑ S : Finset (Fin n), ENNReal.ofReal (selWeight (ε / 4) n S) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => selWeight_nonneg hp hp1 n S), selWeight_sum]
    simp
  rw [algA_eq]
  simpa [hs] using ENNReal.inv_two_add_inv_two
lemma parity_comm {d : ℕ} (r x : Fin d → ZMod 2) : parity r x = parity x r :=
  dotProduct_comm r x
lemma true_mem_solSpace {d n : ℕ} (r : Fin d → ZMod 2)
    (x : Fin n → (Fin d → ZMod 2)) (S : Finset (Fin n)) :
    r ∈ solSpace (labeled r x) S := by
  classical
  simp [solSpace, labeled, parity_comm]
lemma algA_probability {d n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hε4 : ε ≤ 4)
    (z : Fin n → Example d) : IsProbabilityMeasure (algA ε z) := ⟨algA_univ hε hε4 z⟩
end ParityProof

-- ParityProof.AffineFibers
open PrivLearn.Parity
namespace ParityProof
lemma zmod2_eq_of_ne {a b c : ZMod 2} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  have h : ∀ a b c : ZMod 2, a ≠ c → b ≠ c → a = b := by decide
  exact h a b c ha hb
lemma sol_insert_subset {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n) :
    solSpace z (insert i T) ⊆ solSpace z T := by
  classical
  intro r hr
  simp only [solSpace, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact fun j hj => hr j (Finset.mem_insert_of_mem hj)
lemma solSpace_insert_filter {d n : ℕ} (z : Fin n → Example d)
    (T : Finset (Fin n)) (i : Fin n) :
    solSpace z (insert i T) = (solSpace z T).filter (fun r => parity (z i).1 r = (z i).2) := by
  classical
  ext r
  simp [solSpace, and_comm]
lemma affine_halving {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n)
    (h : (solSpace z (insert i T)).Nonempty) :
    (solSpace z T).card ≤ 2 * (solSpace z (insert i T)).card := by
  classical
  let A := solSpace z T
  let B := solSpace z (insert i T)
  have hBA : B ⊆ A := sol_insert_subset z T i
  have hc := Finset.card_sdiff_add_card_eq_card hBA
  obtain ⟨u,hu⟩ := h
  have hu' : ∀ j ∈ insert i T, parity (z j).1 u = (z j).2 := by
    simpa [solSpace] using hu
  by_cases he : (A \ B).Nonempty
  · obtain ⟨v,hv⟩ := he
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    have hvB : v ∉ B := (Finset.mem_sdiff.mp hv).2
    have hv' : ∀ j ∈ T, parity (z j).1 v = (z j).2 := by
      simpa [A,solSpace] using hvA
    have hvbad : parity (z i).1 v ≠ (z i).2 := by
      intro heq
      apply hvB
      simp [B, solSpace_insert_filter, hvA, A, heq]
    have hcard : (A \ B).card ≤ B.card := by
      apply Finset.card_le_card_of_injOn (fun r => r + v + u)
      · intro r hr
        obtain ⟨hrA,hrB⟩ := Finset.mem_sdiff.mp hr
        have hr' : ∀ j ∈ T, parity (z j).1 r = (z j).2 := by
          simpa [A,solSpace] using hrA
        have hrbad : parity (z i).1 r ≠ (z i).2 := by
          intro heq
          apply hrB
          simp [B, solSpace_insert_filter, hrA, A, heq]
        have heq := zmod2_eq_of_ne hrbad hvbad
        change r + v + u ∈ solSpace z (insert i T)
        simp only [solSpace, Finset.mem_filter, Finset.mem_univ, true_and]
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simp only [parity, dotProduct_add]
          change (parity (z i).1 r + parity (z i).1 v) + parity (z i).1 u = (z i).2
          rw [heq, ZModModule.add_self, zero_add, hu' i (Finset.mem_insert_self _ _)]
        · simp only [parity, dotProduct_add]
          change (parity (z j).1 r + parity (z j).1 v) + parity (z j).1 u = (z j).2
          rw [hr' j hj, hv' j hj, ZModModule.add_self, zero_add,
            hu' j (Finset.mem_insert_of_mem hj)]
      · intro x hx y hy hxy
        exact add_right_cancel (add_right_cancel hxy)
    dsimp [A,B] at hc hcard
    omega
  · have hz : (A \ B).card = 0 := by simpa using Finset.not_nonempty_iff_eq_empty.mp he
    dsimp [A,B] at hc hz
    omega
end ParityProof

-- ParityProof.SolutionScore
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators
noncomputable def solutionScore {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n))
    (E : Set (Option (Fin d → ZMod 2))) : ℝ := by
  classical
  exact if (solSpace z S).Nonempty then
    ((solSpace z S).filter (fun r => some r ∈ E)).card / ((solSpace z S).card : ℝ)
    else if none ∈ E then 1 else 0
lemma solutionScore_nonneg {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n))
    (E : Set (Option (Fin d → ZMod 2))) : 0 ≤ solutionScore z S E := by
  classical
  unfold solutionScore
  split_ifs <;> positivity
lemma solutionScore_le_one {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n))
    (E : Set (Option (Fin d → ZMod 2))) : solutionScore z S E ≤ 1 := by
  classical
  unfold solutionScore
  split_ifs with h
  · have hc : (0 : ℝ) < (solSpace z S).card := by exact_mod_cast Finset.card_pos.mpr h
    apply (div_le_one hc).mpr
    exact_mod_cast Finset.card_filter_le (solSpace z S) (fun r => some r ∈ E)
  · norm_num
  · norm_num
lemma solutionLaw_apply {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n))
    (E : Set (Option (Fin d → ZMod 2))) :
    solutionLaw z S E = ENNReal.ofReal (solutionScore z S E) := by
  classical
  unfold solutionLaw solutionScore
  split_ifs with h hn
  · rw [Measure.finsetSum_apply _ _ E]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (output_measurable E)]
    simp only [Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp [Finset.card_pos.mpr h, div_eq_mul_inv]
  · simp_all [Measure.dirac_apply' _ (output_measurable E)]
  · simp_all [Measure.dirac_apply' _ (output_measurable E)]
lemma score_insert_le {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n))
    (i : Fin n) (E : Set (Option (Fin d → ZMod 2))) (hn : none ∉ E) :
    solutionScore z (insert i T) E ≤ 2 * solutionScore z T E := by
  classical
  by_cases hB : (solSpace z (insert i T)).Nonempty
  · have hA := hB.mono (sol_insert_subset z T i)
    have hcard := affine_halving z T i hB
    have hfilter : ((solSpace z (insert i T)).filter (fun r => some r ∈ E)).card ≤
        ((solSpace z T).filter (fun r => some r ∈ E)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (sol_insert_subset z T i))
    have ha : (0 : ℝ) < (solSpace z T).card := by exact_mod_cast Finset.card_pos.mpr hA
    have hb : (0 : ℝ) < (solSpace z (insert i T)).card := by exact_mod_cast Finset.card_pos.mpr hB
    have hc : ((solSpace z T).card : ℝ) ≤ 2 * (solSpace z (insert i T)).card := by exact_mod_cast hcard
    have hf : (((solSpace z (insert i T)).filter (fun r => some r ∈ E)).card : ℝ) ≤
        ((solSpace z T).filter (fun r => some r ∈ E)).card := by exact_mod_cast hfilter
    simp only [solutionScore, if_pos hB, if_pos hA]
    apply (div_le_iff₀ hb).mpr
    rw [mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc]
    apply (le_div_iff₀ ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (((solSpace z (insert i T)).filter (fun r => some r ∈ E)).card))]
  · have hz : solutionScore z (insert i T) E = 0 := by simp [solutionScore, hB, hn]
    rw [hz]
    exact mul_nonneg (by norm_num) (solutionScore_nonneg z T E)
end ParityProof

-- ParityProof.SubsetSplit
open PrivLearn.Parity
namespace ParityProof
open scoped BigOperators
noncomputable def subWeight {ι : Type*} (p : ℝ) (U S : Finset ι) : ℝ :=
  p ^ S.card * (1-p) ^ (U.card-S.card)
lemma subWeight_nonneg {ι : Type*} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (U S : Finset ι) :
    0 ≤ subWeight p U S := mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)
lemma subWeight_insert {ι : Type*} [DecidableEq ι] (p : ℝ) (U S : Finset ι) (i : ι)
    (hi : i ∉ U) (hS : S ⊆ U) :
    subWeight p (insert i U) S = (1-p)*subWeight p U S ∧
    subWeight p (insert i U) (insert i S) = p*subWeight p U S := by
  have hiS : i ∉ S := fun h => hi (hS h)
  have hc := Finset.card_le_card hS
  have he : U.card + 1 - S.card = (U.card-S.card)+1 := by omega
  simp only [subWeight, Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hiS]
  rw [he, Nat.add_sub_add_right, pow_succ, pow_succ]
  constructor <;> ring
lemma subWeight_sum {ι : Type*} [DecidableEq ι] (p : ℝ) (U : Finset ι) :
    ∑ S ∈ U.powerset, subWeight p U S = 1 := by
  induction U using Finset.induction_on with
  | empty => simp [subWeight]
  | @insert i U hi ih =>
    rw [Finset.sum_powerset_insert hi]
    have h1 : (∑ S ∈ U.powerset, subWeight p (insert i U) S) =
        (1-p)*∑ S ∈ U.powerset, subWeight p U S := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun S hS => (subWeight_insert p U S i hi (Finset.mem_powerset.mp hS)).1)
    have h2 : (∑ S ∈ U.powerset, subWeight p (insert i U) (insert i S)) =
        p*∑ S ∈ U.powerset, subWeight p U S := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun S hS => (subWeight_insert p U S i hi (Finset.mem_powerset.mp hS)).2)
    rw [h1,h2,ih]
    ring
lemma weighted_subset_split {n : ℕ} (p : ℝ) (i : Fin n) (f : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), selWeight p n S * f S) =
    ∑ T ∈ (Finset.univ.erase i).powerset,
      subWeight p (Finset.univ.erase i) T * ((1-p)*f T+p*f (insert i T)) := by
  classical
  have he : insert i (Finset.univ.erase i) = (Finset.univ : Finset (Fin n)) :=
    Finset.insert_erase (Finset.mem_univ i)
  calc
    _ = ∑ S ∈ (insert i (Finset.univ.erase i)).powerset,
        subWeight p (insert i (Finset.univ.erase i)) S * f S := by
      simp [he, subWeight, selWeight]
    _ = _ := by
      rw [Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ), ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨h1,h2⟩ := subWeight_insert p (Finset.univ.erase i) T i
        (Finset.notMem_erase i Finset.univ) (Finset.mem_powerset.mp hT)
      rw [h1,h2]
      ring
end ParityProof

-- ParityProof.BaseScore
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators
noncomputable def baseScore {d n : ℕ} (p : ℝ) (z : Fin n → Example d)
    (E : Set (Option (Fin d → ZMod 2))) : ℝ := by
  classical
  exact (if none ∈ E then 1/2 else 0) + (1/2)*∑ S : Finset (Fin n),
    selWeight p n S * solutionScore z S E
lemma baseScore_nonneg {d n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (z : Fin n → Example d) (E : Set (Option (Fin d → ZMod 2))) : 0 ≤ baseScore p z E := by
  classical
  unfold baseScore
  apply add_nonneg
  · split_ifs <;> norm_num
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun S _ => mul_nonneg (selWeight_nonneg hp hp1 n S) (solutionScore_nonneg z S E))
lemma algA_apply_score {d n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hε4 : ε ≤ 4)
    (z : Fin n → Example d) (E : Set (Option (Fin d → ZMod 2))) :
    algA ε z E = ENNReal.ofReal (baseScore (ε/4) z E) := by
  classical
  have hp : 0 ≤ ε/4 := by positivity
  have hp1 : ε/4 ≤ 1 := by linarith
  have hn (S : Finset (Fin n)) : 0 ≤ selWeight (ε/4) n S * solutionScore z S E :=
    mul_nonneg (selWeight_nonneg hp hp1 n S) (solutionScore_nonneg z S E)
  rw [algA_eq]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    solutionLaw_apply, Measure.dirac_apply' _ (output_measurable E)]
  simp only [← ENNReal.ofReal_mul (selWeight_nonneg hp hp1 n _), ← ENNReal.ofReal_sum_of_nonneg (fun S _ => hn S)]
  unfold baseScore
  split_ifs with he
  · simp [he, ENNReal.ofReal_add, ENNReal.ofReal_mul, Finset.sum_nonneg (fun S _ => hn S)]
  · simp [he, ENNReal.ofReal_mul]
lemma score_eq_away {d n : ℕ} (z z' : Fin n → Example d) (i : Fin n)
    (hz : ∀ j, j ≠ i → z j = z' j) (T : Finset (Fin n)) (hi : i ∉ T)
    (E : Set (Option (Fin d → ZMod 2))) : solutionScore z T E = solutionScore z' T E := by
  classical
  have he : solSpace z T = solSpace z' T := by
    ext r
    simp only [solSpace, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [hz j (fun h => hi (h ▸ hj))]
  simp only [solutionScore, he]
end ParityProof

-- ParityProof.BasePrivacy
open MeasureTheory PrivLearn.Parity PrivLearn.Generic
namespace ParityProof
open scoped BigOperators Classical
lemma baseScore_split {d n : ℕ} (p : ℝ) (z : Fin n → Example d) (i : Fin n)
    (E : Set (Option (Fin d → ZMod 2))) :
    baseScore p z E = (1/2)*∑ T ∈ (Finset.univ.erase i).powerset,
      subWeight p (Finset.univ.erase i) T *
      ((if none ∈ E then 1 else 0) + (1-p)*solutionScore z T E + p*solutionScore z (insert i T) E) := by
  classical
  unfold baseScore
  rw [weighted_subset_split p i]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, subWeight_sum]
  split_ifs <;> ring
lemma baseScore_neighbor {d n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (z z' : Fin n → Example d) (i : Fin n) (hz : ∀ j, j ≠ i → z j = z' j)
    (E : Set (Option (Fin d → ZMod 2))) : baseScore (ε/4) z E ≤ (1+ε)*baseScore (ε/4) z' E := by
  classical
  have hp : 0 ≤ ε/4 := by positivity
  have hp1 : ε/4 ≤ 1 := by linarith
  rw [baseScore_split (ε/4) z i E, baseScore_split (ε/4) z' i E]
  rw [← mul_assoc, mul_comm (1+ε) (1/2:ℝ), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hi : i ∉ T := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hT h)).1 rfl
  have he := score_eq_away z z' i hz T hi E
  rw [← he]
  rw [← mul_assoc, mul_comm (1+ε) (subWeight _ _ T), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (subWeight_nonneg hp hp1 _ _)
  have hx := solutionScore_nonneg z T E
  have hy := solutionScore_nonneg z (insert i T) E
  have hy1 := solutionScore_le_one z (insert i T) E
  have hz0 := solutionScore_nonneg z' (insert i T) E
  have hrem : 0 ≤ 1-ε/4 := by linarith
  by_cases hn : none ∈ E
  · simp only [if_pos hn]
    have hprod := mul_nonneg hε (add_nonneg
      (mul_nonneg hrem hx) (mul_nonneg hp hz0))
    have hdiff := mul_le_mul_of_nonneg_left hy1 hp
    nlinarith [mul_nonneg hp hz0]
  · simp only [if_neg hn, zero_add]
    have htwo := score_insert_le z T i E hn
    have hleft := mul_le_mul_of_nonneg_left htwo hp
    have hfactor : 2*(ε/4) ≤ ε*(1-ε/4) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hfactor hx
    have hright := mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1+ε) hp) hz0
    nlinarith
lemma algA_dp {d n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    IsDP (fun z : Fin n → Example d => algA ε z) ε := by
  intro z z' hn E _
  obtain ⟨i, _, hz⟩ := hn
  have hb := baseScore_neighbor hε.le (by linarith) z z' i hz E
  have hn0 := baseScore_nonneg (by positivity : 0 ≤ ε/4) (by linarith : ε/4 ≤ 1) z' E
  have he : 1+ε ≤ Real.exp ε := by linarith [Real.add_one_le_exp ε]
  rw [algA_apply_score hε.le (by linarith), algA_apply_score hε.le (by linarith),
    ← ENNReal.ofReal_mul (Real.exp_nonneg ε)]
  exact ENNReal.ofReal_le_ofReal (hb.trans (mul_le_mul_of_nonneg_right he hn0))
end ParityProof

-- ParityProof.LaplaceBasics
open MeasureTheory Set
namespace ParityProof
noncomputable def laplaceDensity (s x:ℝ) : ℝ := Real.exp (-|x|/s)/(2*s)
lemma laplaceDensity_nonneg {s:ℝ} (hs:0<s) (x:ℝ) : 0≤laplaceDensity s x := by
  unfold laplaceDensity; positivity
lemma laplaceDensity_continuous (s:ℝ) : Continuous (laplaceDensity s) := by
  unfold laplaceDensity; fun_prop
lemma laplaceDensity_left {s x:ℝ} (hx:x≤0) :
    laplaceDensity s x=Real.exp ((1/s)*x)/(2*s) := by
  unfold laplaceDensity
  rw [abs_of_nonpos hx]
  congr 2; ring
lemma laplaceDensity_right {s x:ℝ} (hx:0≤x) :
    laplaceDensity s x=Real.exp ((-(1/s))*x)/(2*s) := by
  unfold laplaceDensity
  rw [abs_of_nonneg hx]
  congr 2; ring
lemma laplaceDensity_integrable_left {s:ℝ} (hs:0<s) :
    IntegrableOn (laplaceDensity s) (Iic 0) := by
  apply IntegrableOn.congr_fun ((integrableOn_exp_mul_Iic (by positivity : 0<(1:ℝ)/s) 0).div_const (2*s))
  · intro x hx
    exact (laplaceDensity_left hx).symm
  · exact measurableSet_Iic
lemma laplaceDensity_integrable_right {s:ℝ} (hs:0<s) :
    IntegrableOn (laplaceDensity s) (Ioi 0) := by
  apply IntegrableOn.congr_fun ((integrableOn_exp_mul_Ioi (by exact div_neg_of_neg_of_pos (by norm_num) hs : -(1:ℝ)/s<0) 0).div_const (2*s))
  · intro x hx
    simpa only [neg_div] using (laplaceDensity_right (le_of_lt hx)).symm
  · exact measurableSet_Ioi
lemma laplaceDensity_integrable {s:ℝ} (hs:0<s) : Integrable (laplaceDensity s) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a:=(0:ℝ)), integrableOn_union]
  exact ⟨laplaceDensity_integrable_left hs,laplaceDensity_integrable_right hs⟩
lemma laplaceDensity_integral {s:ℝ} (hs:0<s) : ∫x,laplaceDensity s x=1 := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (laplaceDensity_integrable_left hs) (laplaceDensity_integrable_right hs)]
  have hl : (∫x in Iic (0:ℝ),laplaceDensity s x)=(1/2:ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun x hx=>laplaceDensity_left hx),integral_div,
      integral_exp_mul_Iic (by positivity : 0<(1:ℝ)/s)]
    simp only [mul_zero,Real.exp_zero]
    field_simp
  have hr : (∫x in Ioi (0:ℝ),laplaceDensity s x)=(1/2:ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx=>laplaceDensity_right (le_of_lt hx)),integral_div,
      integral_exp_mul_Ioi (by exact neg_neg_of_pos (by positivity) : -((1:ℝ)/s)<0)]
    simp only [mul_zero,Real.exp_zero]
    field_simp
  rw [hl,hr]; norm_num
lemma laplace_probability {s:ℝ} (hs:0<s) : IsProbabilityMeasure (PrivLearn.Generic.laplace s) := by
  constructor
  rw [PrivLearn.Generic.laplace,withDensity_apply _ MeasurableSet.univ]
  change (∫⁻x, ENNReal.ofReal (laplaceDensity s x) ∂volume.restrict univ)=1
  rw [Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (laplaceDensity_integrable hs)
    (Filter.Eventually.of_forall (laplaceDensity_nonneg hs)),laplaceDensity_integral hs]
  norm_num
end ParityProof

-- ParityProof.LaplaceTails
open MeasureTheory Set PrivLearn.Generic
namespace ParityProof
lemma laplace_apply_integral {s:ℝ} (hs:0<s) (E:Set ℝ) (hE:MeasurableSet E) :
    laplace s E=ENNReal.ofReal (∫x in E,laplaceDensity s x) := by
  rw [laplace,withDensity_apply _ hE]
  exact (ofReal_integral_eq_lintegral_ofReal ((laplaceDensity_integrable hs).integrableOn)
    (Filter.Eventually.of_forall (laplaceDensity_nonneg hs))).symm
lemma laplace_right_tail {s a:ℝ} (hs:0<s) (ha:0≤a) :
    laplace s (Ioi a)=ENNReal.ofReal (Real.exp (-a/s)/2) := by
  rw [laplace_apply_integral hs _ measurableSet_Ioi]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx=>laplaceDensity_right (le_trans ha (le_of_lt hx))),
    integral_div,integral_exp_mul_Ioi (by exact neg_neg_of_pos (by positivity) : -((1:ℝ)/s)<0)]
  have he : -((1:ℝ)/s)*a= -a/s := by ring
  rw [he]
  field_simp
lemma laplace_left_tail {s a:ℝ} (hs:0<s) (ha:0≤a) :
    laplace s (Iic (-a))=ENNReal.ofReal (Real.exp (-a/s)/2) := by
  rw [laplace_apply_integral hs _ measurableSet_Iic]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Iic (fun x hx=>laplaceDensity_left (show x≤0 by have := (show x≤ -a from hx); linarith)),
    integral_div,integral_exp_mul_Iic (by positivity : 0<(1:ℝ)/s)]
  have he : ((1:ℝ)/s)*(-a)= -a/s := by ring
  rw [he]
  field_simp
lemma laplace_abs_tail {s a:ℝ} (hs:0<s) (ha:0≤a) :
    laplace s {x : ℝ | a < |x|}≤ENNReal.ofReal (Real.exp (-a/s)) := by
  calc
    laplace s {x : ℝ | a < |x|} ≤ laplace s (Iic (-a)∪Ioi a) := by
      apply measure_mono
      intro x hx
      rcases lt_abs.mp (show a < |x| from hx) with h|h
      · exact Or.inr h
      · exact Or.inl (by change x≤ -a; linarith)
    _ ≤ laplace s (Iic (-a))+laplace s (Ioi a) := measure_union_le _ _
    _ = ENNReal.ofReal (Real.exp (-a/s)) := by
      rw [laplace_left_tail hs ha,laplace_right_tail hs ha,← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
end ParityProof

-- ParityProof.LaplaceProduct
open MeasureTheory Set PrivLearn.Generic
namespace ParityProof
noncomputable def laplaceProductDensity (k:ℕ) (s:ℝ) (x:Fin k→ℝ) : ℝ := ∏i,laplaceDensity s (x i)
lemma laplaceProductDensity_nonneg {k:ℕ} {s:ℝ} (hs:0<s) (x:Fin k→ℝ) :
    0≤laplaceProductDensity k s x := Finset.prod_nonneg (fun i _=>laplaceDensity_nonneg hs (x i))
lemma laplaceProductDensity_continuous (k:ℕ) (s:ℝ) : Continuous (laplaceProductDensity k s) := by
  unfold laplaceProductDensity
  exact continuous_finsetProd _ (fun i _=>(laplaceDensity_continuous s).comp (continuous_apply i))
lemma laplaceProductDensity_integrable (k:ℕ) {s:ℝ} (hs:0<s) :
    Integrable (laplaceProductDensity k s) := by
  change Integrable (fun x:Fin k→ℝ=>∏i,laplaceDensity s (x i)) (Measure.pi fun _=>volume)
  exact Integrable.fintype_prod_dep (fun _=>laplaceDensity_integrable hs)
lemma pi_laplace_density (k:ℕ) {s:ℝ} (hs:0<s) :
    Measure.pi (fun _:Fin k=>laplace s)=volume.withDensity (fun x=>ENNReal.ofReal (laplaceProductDensity k s x)) := by
  let := laplace_probability hs
  apply Measure.pi_eq
  intro E hE
  rw [withDensity_apply _ (MeasurableSet.univ_pi hE),
    ← ofReal_integral_eq_lintegral_ofReal ((laplaceProductDensity_integrable k hs).integrableOn)
      (Filter.Eventually.of_forall (laplaceProductDensity_nonneg hs))]
  change ENNReal.ofReal (∫x,laplaceProductDensity k s x ∂(Measure.pi fun _:Fin k=>volume).restrict (univ.pi E))=_
  rw [Measure.restrict_pi_pi]
  unfold laplaceProductDensity
  rw [integral_fintype_prod_eq_prod,ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    exact (laplace_apply_integral hs (E i) (hE i)).symm
  · intro i _
    exact integral_nonneg (laplaceDensity_nonneg hs)
lemma laplaceDensity_shift {s:ℝ} (hs:0<s) (x t:ℝ) :
    laplaceDensity s x ≤ Real.exp (|t|/s)*laplaceDensity s (x+t) := by
  have hab := abs_add_le x t
  have hex : -|x|/s ≤ |t|/s + (-|x+t|/s) := by
    apply (div_le_div_iff_of_pos_right hs).2 at hab
    rw [add_div] at hab
    simp only [neg_div] at *
    linarith
  have he := Real.exp_le_exp.mpr hex
  unfold laplaceDensity
  rw [Real.exp_add] at he
  have hd := div_le_div_of_nonneg_right he (show 0≤2*s by positivity)
  simpa only [mul_div_assoc] using hd
lemma laplaceProductDensity_shift {k:ℕ} {s:ℝ} (hs:0<s) (x t:Fin k→ℝ) :
    laplaceProductDensity k s x ≤ Real.exp ((∑i,|t i|)/s)*laplaceProductDensity k s (x+t) := by
  have h := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>laplaceDensity_nonneg hs (x i))
    (fun i _=>laplaceDensity_shift hs (x i) (t i))
  change (∏i:Fin k,laplaceDensity s (x i))≤_ at h
  rw [Finset.prod_mul_distrib,← Real.exp_sum] at h
  simpa [laplaceProductDensity,Finset.sum_div,Pi.add_apply] using h
end ParityProof

-- ParityProof.LaplaceShift
open MeasureTheory Set PrivLearn.Generic
namespace ParityProof
lemma pi_laplace_shift_integral {k:ℕ} {s:ℝ} (hs:0<s) (t:Fin k→ℝ)
    (F:(Fin k→ℝ)→ENNReal) (hF:Measurable F) :
    (∫⁻x,F x ∂(Measure.pi (fun _:Fin k=>laplace s))) ≤
      ENNReal.ofReal (Real.exp ((∑i,|t i|)/s)) *
      ∫⁻x,F (x-t) ∂(Measure.pi (fun _:Fin k=>laplace s)) := by
  have hd : Measurable (fun x:Fin k→ℝ=>ENNReal.ofReal (laplaceProductDensity k s x)) :=
    (laplaceProductDensity_continuous k s).measurable.ennreal_ofReal
  have hG : Measurable (fun x:Fin k→ℝ=>F (x-t)) := hF.comp (by fun_prop)
  rw [pi_laplace_density k hs,lintegral_withDensity_eq_lintegral_mul _ hd hF,
    lintegral_withDensity_eq_lintegral_mul _ hd hG]
  have hpoint (x:Fin k→ℝ) : ENNReal.ofReal (laplaceProductDensity k s x)*F x ≤
      ENNReal.ofReal (Real.exp ((∑i,|t i|)/s))*(ENNReal.ofReal (laplaceProductDensity k s (x+t))*F x) := by
    have h:=ENNReal.ofReal_le_ofReal (laplaceProductDensity_shift hs x t)
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
    simpa [mul_assoc] using mul_le_mul h (le_refl (F x))
  calc
    (∫⁻x,ENNReal.ofReal (laplaceProductDensity k s x)*F x) ≤
        ∫⁻x,ENNReal.ofReal (Real.exp ((∑i,|t i|)/s))*(ENNReal.ofReal (laplaceProductDensity k s (x+t))*F x) := lintegral_mono hpoint
    _ = ENNReal.ofReal (Real.exp ((∑i,|t i|)/s)) *
        ∫⁻x,ENNReal.ofReal (laplaceProductDensity k s (x+t))*F x := by
      exact lintegral_const_mul _ (show Measurable (fun x:Fin k→ℝ=>ENNReal.ofReal (laplaceProductDensity k s (x+t))*F x) from (hd.comp (by fun_prop)).mul hF)
    _ = _ := by
      congr 1
      have hh:=lintegral_add_right_eq_self (μ:=volume)
        (fun x:Fin k→ℝ=>ENNReal.ofReal (laplaceProductDensity k s x)*F (x-t)) t
      simpa only [add_sub_cancel_right,Pi.mul_apply] using hh
end ParityProof

-- ParityProof.NoisySelection
open MeasureTheory Set PrivLearn.Parity PrivLearn.Generic
namespace ParityProof
local instance optionFinMeasurable (k:ℕ) : MeasurableSpace (Option (Fin k)) := ⊤
local instance optionFinSingleton (k:ℕ) : MeasurableSingletonClass (Option (Fin k)) := ⟨fun _=>trivial⟩
lemma argmin_measurable {k:ℕ} (L:List (Fin k)) :
    Measurable (fun e:Fin k→ℝ=>L.argmin e) := by
  classical
  apply measurable_to_countable
  intro e
  change MeasurableSet {e' : Fin k→ℝ | L.argmin e'=L.argmin e}
  cases h:L.argmin e with
  | none =>
    simp only [List.argmin_eq_none]
    by_cases hL:L=[] <;> simp [hL]
  | some j =>
    simp only [List.argmin_eq_some_iff]
    measurability
lemma select_measurable {d k:ℕ} (H:Fin k→Option (Fin d→ZMod 2)) :
    Measurable (select H) := by
  classical
  let f : Option (Fin k)→AstarOut d := fun j=>match j with
    | none=>AstarOut.fail
    | some j=>match H j with | none=>AstarOut.fail | some r=>AstarOut.hyp r
  exact (measurable_of_finite f).comp (argmin_measurable _)
noncomputable def testMechanism {d k s:ℕ} (H:Fin k→Option (Fin d→ZMod 2))
    (T:Fin s→Example d) (ε:ℝ) : Measure (AstarOut d) :=
  (Measure.pi (fun _:Fin k=>laplace ((k:ℝ)/(s*ε)))).map
    (fun η=>select H (fun j=>testErr T (H j)+η j))
lemma noisy_select_measurable {d k:ℕ} (H:Fin k→Option (Fin d→ZMod 2)) (v:Fin k→ℝ) :
    Measurable (fun η:Fin k→ℝ=>select H (fun j=>v j+η j)) :=
  (select_measurable H).comp (by fun_prop)
lemma testMechanism_probability {d k s:ℕ} (hk:0<k) (hs:0<s) {ε:ℝ} (he:0<ε)
    (H:Fin k→Option (Fin d→ZMod 2)) (T:Fin s→Example d) :
    IsProbabilityMeasure (testMechanism H T ε) := by
  let := laplace_probability (show 0<(k:ℝ)/(s*ε) by positivity)
  exact Measure.isProbabilityMeasure_map (noisy_select_measurable H _).aemeasurable
lemma select_good_of_gap {d k:ℕ} (H:Fin k→Option (Fin d→ZMod 2)) (e:Fin k→ℝ)
    (good:(Fin d→ZMod 2)→Prop) (j:Fin k) (r:Fin d→ZMod 2)
    (hj:H j=some r) (hbad:∀i r',H i=some r'→¬good r'→e j<e i) :
    ∃r',select H e=AstarOut.hyp r'∧good r' := by
  classical
  let L := (List.finRange k).filter (fun i=>(H i).isSome)
  have hjL : j∈L := by simp [L,hj]
  have hn : L.argmin e≠none := by
    intro h
    have hh := List.argmin_eq_none.mp h
    simp [hh] at hjL
  obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp hn
  have hiL := List.argmin_mem (show i∈L.argmin e from hi)
  have hle := List.le_of_mem_argmin hjL (show i∈L.argmin e from hi)
  have hsome : (H i).isSome := (List.mem_filter.mp hiL).2
  obtain ⟨r',hr'⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨r',?_,?_⟩
  · simp only [select,show ((List.finRange k).filter fun j=>(H j).isSome)=L from rfl,hi,hr']
  · by_contra hg
    exact (not_lt_of_ge hle) (hbad i r' hr' hg)
end ParityProof

-- ParityProof.TestPrivacy
open MeasureTheory Set PrivLearn.Generic PrivLearn.Parity
namespace ParityProof
open scoped Classical
lemma testErr_sensitivity {d s:ℕ} (hs:0<s) (T T':Fin s→Example d)
    (hn:Neighbors T T') (r:Option (Fin d→ZMod 2)) : |testErr T r-testErr T' r|≤1/(s:ℝ) := by
  rcases hn with ⟨i,_,hi⟩
  cases r with
  | none => simp [testErr]
  | some r =>
    let a : Fin s→ℝ := fun j=>if parity r (T j).1≠(T j).2 then 1 else 0
    let b : Fin s→ℝ := fun j=>if parity r (T' j).1≠(T' j).2 then 1 else 0
    have hdiff : (∑j,a j)-(∑j,b j)=a i-b i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [a,b,hi j hji]
      · simp
    have ha : 0≤a i ∧ a i≤1 := by dsimp [a]; split_ifs <;> norm_num
    have hb : 0≤b i ∧ b i≤1 := by dsimp [b]; split_ifs <;> norm_num
    have herr : testErr T (some r)=(∑j,a j)/(s:ℝ) := by
      simp [testErr,a,Finset.card_filter]
    have herr' : testErr T' (some r)=(∑j,b j)/(s:ℝ) := by
      simp [testErr,b,Finset.card_filter]
    rw [herr,herr',← sub_div,hdiff,abs_div,abs_of_pos (show (0:ℝ)<s by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma testMechanism_dp {d k s:ℕ} (hk:0<k) (hs:0<s) {ε:ℝ} (he:0<ε)
    (H:Fin k→Option (Fin d→ZMod 2)) : IsDP (fun T:Fin s→Example d=>testMechanism H T ε) ε := by
  intro T T' hn E hE
  let v : Fin k→ℝ := fun j=>testErr T (H j)
  let v' : Fin k→ℝ := fun j=>testErr T' (H j)
  let t : Fin k→ℝ := v-v'
  let L := Measure.pi (fun _:Fin k=>laplace ((k:ℝ)/(s*ε)))
  let A := (fun η:Fin k→ℝ=>select H (v+η)) ⁻¹' E
  let B := (fun η:Fin k→ℝ=>select H (v'+η)) ⁻¹' E
  have hA : MeasurableSet A := (noisy_select_measurable H v) hE
  have hB : MeasurableSet B := (noisy_select_measurable H v') hE
  have hscale : 0<(k:ℝ)/(s*ε) := by positivity
  have hshift := pi_laplace_shift_integral hscale t (A.indicator (fun _=>(1:ENNReal)))
    (measurable_const.indicator hA)
  have hfun : (fun x:Fin k→ℝ=>A.indicator (fun _=>(1:ENNReal)) (x-t))=B.indicator (fun _=>(1:ENNReal)) := by
    funext x
    have heq : v+(x-t)=v'+x := by dsimp [t]; abel
    simp only [A,B,Set.indicator,Set.mem_preimage,heq]
  rw [hfun] at hshift
  have hIA : (∫⁻x,A.indicator (fun _=>(1:ENNReal)) x ∂L)=L A := by simpa only [Pi.one_def] using lintegral_indicator_one (μ:=L) hA
  have hIB : (∫⁻x,B.indicator (fun _=>(1:ENNReal)) x ∂L)=L B := by simpa only [Pi.one_def] using lintegral_indicator_one (μ:=L) hB
  rw [hIA,hIB] at hshift
  have hsum : (∑j,|t j|)≤(k:ℝ)/(s:ℝ) := by
    calc
      (∑j,|t j|) ≤ ∑j:Fin k,1/(s:ℝ) := Finset.sum_le_sum (fun j _=>testErr_sensitivity hs T T' hn (H j))
      _ = _ := by simp; ring
  have hbudget : (∑j,|t j|)/((k:ℝ)/(s*ε))≤ε := by
    apply (div_le_iff₀ hscale).2
    have hid : ε*((k:ℝ)/(s*ε))=(k:ℝ)/(s:ℝ) := by field_simp
    rw [hid]
    exact hsum
  have hfac := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hbudget)
  have hfinal := hshift.trans (mul_le_mul hfac (le_refl (L B)) (by positivity) (by positivity))
  have heq1 : (fun η:Fin k→ℝ=>select H (v+η))=(fun η=>select H (fun j=>testErr T (H j)+η j)) := by
    funext η
    congr 1
  have heq2 : (fun η:Fin k→ℝ=>select H (v'+η))=(fun η=>select H (fun j=>testErr T' (H j)+η j)) := by
    funext η
    congr 1
  dsimp only [A,B] at hfinal
  rw [heq1,heq2] at hfinal
  simpa only [testMechanism,Measure.map_apply (noisy_select_measurable H _) hE,L] using hfinal
end ParityProof

-- ParityProof.PrivacyComposition
open MeasureTheory PrivLearn.Parity PrivLearn.Generic
namespace ParityProof
open scoped BigOperators Classical
lemma dp_compare_equal_or_one {D O : Type*} [MeasurableSpace O] {n : ℕ}
    {A : (Fin n → D) → Measure O} {ε : ℝ} (hε : 0 ≤ ε) (hA : IsDP A ε)
    (z z' : Fin n → D) (i : Fin n) (hz : ∀ j, j ≠ i → z j = z' j)
    (E : Set O) (hE : MeasurableSet E) : A z E ≤ ENNReal.ofReal (Real.exp ε)*A z' E := by
  by_cases hi : z i = z' i
  · have he : z=z' := by
      ext j
      by_cases hj : j=i
      · simpa [hj] using hi
      · exact hz j hj
    rw [he]
    have hc : (1:ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := by
      simpa using ENNReal.ofReal_le_ofReal (Real.one_le_exp hε)
    simpa using mul_le_mul' hc (le_refl (A z' E))
  · exact hA z z' ⟨i,hi,hz⟩ E hE
lemma prod_change_bound {ι : Type*} [Fintype ι] (a b : ι → ENNReal) (c : ENNReal)
    (i : ι) (hi : a i ≤ c*b i) (hother : ∀ j,j≠i→a j=b j) :
    ∏ j,a j ≤ c*∏ j,b j := by
  classical
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i,a j) = ∏ j ∈ Finset.univ.erase i,b j :=
    Finset.prod_congr rfl (fun j hj => hother j (Finset.mem_erase.mp hj).1)
  rw [he]
  calc
    _ ≤ (∏ j ∈ Finset.univ.erase i,b j)*(c*b i) := mul_le_mul' le_rfl hi
    _ = _ := by ac_rfl
noncomputable def blockLaw {d k b s : ℕ} (ε : ℝ) (z : BlockIndex k b s → Example d) :
    Measure (AstarOut d) :=
  ∑ H : Fin k → Option (Fin d → ZMod 2),
    (∏ j, algA ε (fun t : Fin b => z (Sum.inl (j,t))) {H j}) •
      testMechanism H (fun t : Fin s => z (Sum.inr t)) ε
lemma blockLaw_compare {d k b s : ℕ} (hk : 0<k) (hs : 0<s) {ε : ℝ}
    (hε : 0<ε) (hε1 : ε≤1/2) (z z' : BlockIndex k b s → Example d)
    (i : BlockIndex k b s) (hz : ∀ j,j≠i→z j=z' j)
    (E : Set (AstarOut d)) : blockLaw ε z E ≤ ENNReal.ofReal (Real.exp ε)*blockLaw ε z' E := by
  have hE : MeasurableSet E := by trivial
  simp only [blockLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro H _
  cases i with
  | inl jt =>
    rcases jt with ⟨j,t⟩
    have ht : (fun u : Fin s => z (Sum.inr u)) = (fun u => z' (Sum.inr u)) := by
      funext u
      exact hz _ (by simp)
    rw [ht]
    have hc : algA ε (fun u : Fin b => z (Sum.inl (j,u))) {H j} ≤
        ENNReal.ofReal (Real.exp ε)*algA ε (fun u : Fin b => z' (Sum.inl (j,u))) {H j} := by
      apply dp_compare_equal_or_one hε.le (algA_dp hε hε1) _ _ t
      · intro u hu
        exact hz _ (by simpa using hu)
      · trivial
    have hp := prod_change_bound
      (fun l : Fin k => algA ε (fun u : Fin b => z (Sum.inl (l,u))) {H l})
      (fun l : Fin k => algA ε (fun u : Fin b => z' (Sum.inl (l,u))) {H l})
      (ENNReal.ofReal (Real.exp ε)) j hc (by
        intro l hl
        congr 2
        funext u
        exact hz _ (by simp [hl]))
    simpa [mul_assoc] using mul_le_mul' hp (le_refl (testMechanism H (fun u => z' (Sum.inr u)) ε E))
  | inr t =>
    have ht : ∀j:Fin k,(fun u : Fin b => z (Sum.inl (j,u))) = (fun u => z' (Sum.inl (j,u))) := by
      intro j
      funext u
      exact hz _ (by simp)
    simp_rw [ht]
    have hc := dp_compare_equal_or_one hε.le (testMechanism_dp hk hs hε H)
      (fun u : Fin s => z (Sum.inr u)) (fun u => z' (Sum.inr u)) t
      (fun u hu => hz _ (by simpa using hu)) E hE
    have hh := mul_le_mul' (le_refl (∏ j : Fin k, algA ε (fun u : Fin b => z' (Sum.inl (j,u))) {H j})) hc
    simpa [mul_left_comm] using hh
end ParityProof

-- ParityProof.ParameterBasics
open MeasureTheory PrivLearn.Parity
namespace ParityProof
lemma log_two_bounds : (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1/2)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
lemma log_four_thirds_bounds : (1/4:ℝ) ≤ Real.log (4/3) ∧ Real.log (4/3) ≤ 1/3 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/4)
    have he : Real.log (3/4) = -Real.log (4/3) := by
      rw [show (3/4:ℝ) = (4/3)⁻¹ by norm_num, Real.log_inv]
    rw [he] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4/3)
    linarith
lemma beta_log_bounds {β:ℝ} (hb:0<β) (hb1:β<1/2) :
    1 < Real.logb 2 (1/β) ∧
    Real.log (1/(β/2)) = Real.log 2 + Real.logb 2 (1/β)*Real.log 2 := by
  have ht : (2:ℝ)<1/β := (lt_div_iff₀ hb).2 (by linarith)
  constructor
  · have h := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<2) ht
    simpa using h
  · rw [show 1/(β/2)=2*(1/β) by field_simp]
    rw [Real.log_mul (by norm_num) (ne_of_gt (one_div_pos.mpr hb))]
    rw [Real.logb, div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]
lemma paramK_bounds {β:ℝ} (hb:0<β) (hb1:β<1/2) :
    3 ≤ paramK β ∧ (paramK β:ℝ) ≤ 9*Real.logb 2 (1/β) := by
  obtain ⟨hl,he⟩ := beta_log_bounds hb hb1
  obtain ⟨h2lo,h2hi⟩ := log_two_bounds
  obtain ⟨hblo,hbhi⟩ := log_four_thirds_bounds
  have hbpos : 0<Real.log (4/3:ℝ) := by linarith
  have hnum : 0<Real.log (1/(β/2)) := by rw [he]; positivity
  have hqpos : 0≤Real.logb (4/3) (1/(β/2)) := le_of_lt (div_pos hnum hbpos)
  have hceil := Nat.le_ceil (Real.logb (4/3) (1/(β/2)))
  have hceilhi := Nat.ceil_lt_add_one hqpos
  have hlow : (3:ℝ) ≤ Real.logb (4/3) (1/(β/2)) := by
    rw [Real.logb, le_div_iff₀ hbpos,he]
    nlinarith
  have hupp : Real.logb (4/3) (1/(β/2)) ≤ 8*Real.logb 2 (1/β) := by
    rw [Real.logb, div_le_iff₀ hbpos,he]
    nlinarith
  constructor
  · unfold paramK
    exact_mod_cast hlow.trans hceil
  · unfold paramK
    linarith
lemma paramK_pos {β:ℝ} (hb:0<β) (hb1:β<1/2) : 0<paramK β := by
  have := (paramK_bounds hb hb1).1
  omega
lemma paramN_pos {d:ℕ} (hd:1≤d) {ε α:ℝ} (he:0<ε) (ha:0<α) :
    0<paramN 64 d ε α := by
  have hd' : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have h := Nat.le_ceil (64*(d:ℝ)/(ε*(α/5)))
  have hp : 0<(64:ℝ)*d/(ε*(α/5)) := by positivity
  unfold paramN
  exact_mod_cast hp.trans_le h
lemma paramS_pos {ε α β:ℝ} (he:0<ε) (ha:0<α) (hb:0<β) (hb1:β<1/2) :
    0<paramS 64 ε α β := by
  have hk := paramK_pos hb hb1
  have hk' : (1:ℝ)≤paramK β := by exact_mod_cast hk
  have hq : 1 < (paramK β:ℝ)/(β/2) := (lt_div_iff₀ (by positivity)).2 (by linarith)
  have hl := Real.logb_pos (by norm_num : (1:ℝ)<2) hq
  have hp : 0<(64:ℝ)*paramK β/((α/5)*ε)*Real.logb 2 (paramK β/(β/2)) := by positivity
  have hc := Nat.le_ceil (64*(paramK β:ℝ)/((α/5)*ε)*Real.logb 2 (paramK β/(β/2)))
  unfold paramS
  exact_mod_cast hp.trans_le hc
end ParityProof

-- ParityProof.AmplifiedPrivacy
open MeasureTheory PrivLearn.Parity PrivLearn.Generic
namespace ParityProof
open scoped BigOperators Classical
lemma algAstar_eq_blockLaw {d n : ℕ} {ε α β : ℝ}
    (hn : paramK β*paramN 64 d ε α+paramS 64 ε α β < n) (z : Fin n → Example d) :
    algAstar 64 64 d ε α β z = blockLaw ε (fun i => z (blockEmbedding hn.le i)) := by
  unfold algAstar blockLaw testMechanism
  rw [if_neg (not_le.mpr hn)]
  simp_rw [trainBlock_eq_project hn.le, testSet_eq_project hn.le]
lemma projected_blockLaw_compare {d k b s n : ℕ} (hk : 0<k) (hs : 0<s) {ε : ℝ}
    (hε : 0<ε) (hε1 : ε≤1/2) (hn : k*b+s≤n) (z z' : Fin n → Example d)
    (i : Fin n) (hz : ∀ j,j≠i→z j=z' j) (E : Set (AstarOut d)) :
    blockLaw ε (fun j => z (blockEmbedding hn j)) E ≤ ENNReal.ofReal (Real.exp ε)*
      blockLaw ε (fun j => z' (blockEmbedding hn j)) E := by
  by_cases hi : ∃ u, blockEmbedding hn u = i
  · obtain ⟨u,hu⟩ := hi
    apply blockLaw_compare hk hs hε hε1 _ _ u
    intro v hv
    apply hz
    intro he
    apply hv
    apply (blockEmbedding hn).injective
    exact he.trans hu.symm
  · have he : (fun j => z (blockEmbedding hn j)) = (fun j => z' (blockEmbedding hn j)) := by
      funext j
      apply hz
      exact fun h => hi ⟨j,h⟩
    rw [he]
    have hc : (1:ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := by
      simpa using ENNReal.ofReal_le_ofReal (Real.one_le_exp hε.le)
    simpa using mul_le_mul' hc (le_refl (blockLaw ε (fun j => z' (blockEmbedding hn j)) E))
lemma algAstar_dp {d n : ℕ} {ε α β : ℝ} (hε : 0<ε) (hε1 : ε≤1/2)
    (hα : 0<α) (hβ : 0<β) (hβ1 : β<1/2) :
    IsDP (fun z : Fin n → Example d => algAstar 64 64 d ε α β z) ε := by
  intro z z' hzz E _
  dsimp only
  by_cases hn : n ≤ paramK β*paramN 64 d ε α+paramS 64 ε α β
  · simp only [algAstar, if_pos hn]
    have hc : (1:ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := by
      simpa using ENNReal.ofReal_le_ofReal (Real.one_le_exp hε.le)
    simpa using mul_le_mul' hc (le_refl (Measure.dirac (AstarOut.insufficient : AstarOut d) E))
  · have hlt := lt_of_not_ge hn
    rw [algAstar_eq_blockLaw hlt, algAstar_eq_blockLaw hlt]
    obtain ⟨i,_,hi⟩ := hzz
    exact projected_blockLaw_compare (paramK_pos hβ hβ1) (paramS_pos hε hα hβ hβ1)
      hε hε1 hlt.le z z' i hi E
end ParityProof

-- ParityProof.AmplifiedFactorization
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators Classical
lemma amplified_sample_factorization {d n : ℕ} {ε α β : ℝ}
    (hn : paramK β*paramN 64 d ε α+paramS 64 ε α β < n)
    (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) (E : Set (AstarOut d)) :
    samplePr μ r (fun z : Fin n → Example d => algAstar 64 64 d ε α β z) E =
      ∑ H : Fin (paramK β) → Option (Fin d → ZMod 2),
        (∏ j, samplePr μ r (fun z : Fin (paramN 64 d ε α) → Example d => algA ε z) {H j}) *
          samplePr μ r (fun T : Fin (paramS 64 ε α β) → Example d => testMechanism H T ε) E := by
  let k := paramK β
  let b := paramN 64 d ε α
  let s := paramS 64 ε α β
  let A := fun (x : Fin b → (Fin d → ZMod 2)) (h : Option (Fin d → ZMod 2)) =>
    algA ε (labeled r x) {h}
  let B := fun (H : Fin k → Option (Fin d → ZMod 2)) (T : Fin s → (Fin d → ZMod 2)) =>
    testMechanism H (labeled r T) ε E
  let F := fun Z : BlockIndex k b s → (Fin d → ZMod 2) =>
    ∑ H : Fin k → Option (Fin d → ZMod 2),
      (∏ j,A (fun t => Z (Sum.inl (j,t))) (H j))*B H (fun t => Z (Sum.inr t))
  have hw : ∑ x, μ x = 1 := by simpa [tsum_fintype] using μ.tsum_coe
  have hm := weighted_injective_marginal (blockEmbedding hn.le) (fun x => μ x) hw F
  simp only [samplePr]
  simp_rw [algAstar_eq_blockLaw hn, blockLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  change (∑ x : Fin n → (Fin d → ZMod 2), (∏ i,μ (x i))*F (fun j=>x (blockEmbedding hn.le j))) = _
  have hm' : (∑ x : Fin n → (Fin d → ZMod 2), (∏ i,μ (x i))*F (fun j=>x (blockEmbedding hn.le j))) =
      ∑ Z : BlockIndex k b s → (Fin d → ZMod 2),(∏ i,μ (Z i))*F Z := by
    convert hm using 1 <;> exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
  rw [hm']
  exact weighted_block_factorization (fun x => μ x) A B
end ParityProof

-- ParityProof.GoodScore
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators Classical
lemma good_score_lower {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n))
    (P : (Fin d → ZMod 2) → Prop) (hne : (solSpace z S).Nonempty) :
    1 - (∑ h : Fin d → ZMod 2, if h ∈ solSpace z S ∧ ¬P h then (1:ℝ) else 0) ≤
    solutionScore z S {o | ∃ h, o = some h ∧ P h} := by
  classical
  by_cases hb : ∃ h ∈ solSpace z S, ¬P h
  · obtain ⟨h,hh,hP⟩ := hb
    have hs : (1:ℝ) ≤ ∑ h : Fin d → ZMod 2, if h ∈ solSpace z S ∧ ¬P h then (1:ℝ) else 0 := by
      calc
        1 = (if h ∈ solSpace z S ∧ ¬P h then (1:ℝ) else 0) := by simp [hh,hP]
        _ ≤ _ := Finset.single_le_sum (f := fun j : Fin d → ZMod 2 => if j ∈ solSpace z S ∧ ¬P j then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ h)
    linarith [solutionScore_nonneg z S {o | ∃ h, o = some h ∧ P h}]
  · have hgood : ∀ h ∈ solSpace z S, P h := by simpa using hb
    have hc : ((solSpace z S).card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hne
    simp only [solutionScore, if_pos hne, Set.mem_ofPred_eq, Option.some.injEq]
    rw [Finset.filter_eq_self.mpr (fun x hx => ⟨x, rfl, hgood x hx⟩), div_self hc]
    have hs : 0 ≤ ∑ h : Fin d → ZMod 2, if h ∈ solSpace z S ∧ ¬P h then (1:ℝ) else 0 :=
      Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
    linarith
lemma realizable_score_lower {d n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (r : Fin d → ZMod 2) (x : Fin n → (Fin d → ZMod 2)) (P : (Fin d → ZMod 2) → Prop) :
    (1/2)*(1-∑ h : Fin d → ZMod 2, if ¬P h then
      ∑ S : Finset (Fin n), selWeight p n S*(if h ∈ solSpace (labeled r x) S then (1:ℝ) else 0) else 0) ≤
    baseScore p (labeled r x) {o | ∃ h, o = some h ∧ P h} := by
  classical
  have hbound : ∑ S : Finset (Fin n), selWeight p n S *
      (1 - ∑ h : Fin d → ZMod 2, if h ∈ solSpace (labeled r x) S ∧ ¬P h then (1:ℝ) else 0) ≤
      ∑ S : Finset (Fin n), selWeight p n S * solutionScore (labeled r x) S {o | ∃ h, o = some h ∧ P h} := by
    apply Finset.sum_le_sum
    intro S _
    exact mul_le_mul_of_nonneg_left
      (good_score_lower _ S P ⟨r,true_mem_solSpace r x S⟩) (selWeight_nonneg hp hp1 n S)
  have he : (∑ S : Finset (Fin n), selWeight p n S *
      (1 - ∑ h : Fin d → ZMod 2, if h ∈ solSpace (labeled r x) S ∧ ¬P h then (1:ℝ) else 0)) =
      1-∑ h : Fin d → ZMod 2, if ¬P h then
      ∑ S : Finset (Fin n), selWeight p n S*(if h ∈ solSpace (labeled r x) S then (1:ℝ) else 0) else 0 := by
    simp_rw [mul_sub, mul_one, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, selWeight_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    by_cases hP : P h <;> simp [hP]
  rw [he] at hbound
  simpa [baseScore] using mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ)≤1/2)
end ParityProof

-- ParityProof.PMFBasics
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators
lemma pmf_real_sum {α : Type*} [Fintype α] (μ : PMF α) : ∑ x, (μ x).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun x _ => μ.apply_ne_top x)]
  have h : ∑ x, μ x = 1 := by simpa [tsum_fintype] using μ.tsum_coe
  rw [h, ENNReal.toReal_one]
lemma iid_real_sum {α : Type*} [Fintype α] (μ : PMF α) (n : ℕ) :
    ∑ x : Fin n → α, ∏ i, (μ (x i)).toReal = 1 := by
  have h := Fintype.prod_sum (fun (_ : Fin n) (x : α) => (μ x).toReal)
  simpa [pmf_real_sum] using h.symm
lemma err_sum {d : ℕ} (μ : PMF (Fin d → ZMod 2)) (r h : Fin d → ZMod 2) :
    err μ r (some h) = ∑ x, if parity h x ≠ parity r x then (μ x).toReal else 0 := by
  classical
  simp only [err]
  rw [PMF.toOuterMeasure_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  · intro x _
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp [μ.apply_ne_top]
lemma err_nonneg {d : ℕ} (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2)
    (o : Option (Fin d → ZMod 2)) : 0 ≤ err μ r o := by
  cases o <;> simp [err, ENNReal.toReal_nonneg]
lemma err_le_one {d : ℕ} (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2)
    (o : Option (Fin d → ZMod 2)) : err μ r o ≤ 1 := by
  classical
  cases o with
  | none => simp [err]
  | some h =>
    rw [err_sum, ← pmf_real_sum μ]
    apply Finset.sum_le_sum
    intro x _
    split_ifs <;> simp [ENNReal.toReal_nonneg]
end ParityProof

-- ParityProof.Survival
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators Classical
lemma survival_powerset {ι : Type*} [DecidableEq ι] (p : ℝ) (U : Finset ι)
    (Q : ι → Prop) [DecidablePred Q] :
    (∑ S ∈ U.powerset, subWeight p U S * (if ∀ i ∈ S, Q i then 1 else 0)) =
      ∏ i ∈ U, if Q i then 1 else 1-p := by
  induction U using Finset.induction_on with
  | empty => simp [subWeight]
  | @insert i U hi ih =>
    rw [Finset.sum_powerset_insert hi, Finset.prod_insert hi]
    have h1 : (∑ S ∈ U.powerset, subWeight p (insert i U) S * (if ∀ j ∈ S, Q j then 1 else 0)) =
        (1-p) * ∑ S ∈ U.powerset, subWeight p U S * (if ∀ j ∈ S, Q j then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [(subWeight_insert p U S i hi (Finset.mem_powerset.mp hS)).1]
      ring
    rw [h1, ih]
    by_cases hQi : Q i
    · simp only [hQi, if_true, one_mul, Finset.forall_mem_insert, true_and]
      have h2 : (∑ S ∈ U.powerset, subWeight p (insert i U) (insert i S) * (if ∀ j ∈ S, Q j then 1 else 0)) =
          p * ∑ S ∈ U.powerset, subWeight p U S * (if ∀ j ∈ S, Q j then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [(subWeight_insert p U S i hi (Finset.mem_powerset.mp hS)).2]
        ring
      rw [h2, ih]
      ring
    · simp [hQi]
lemma survival_sum {d n : ℕ} (p : ℝ) (r h : Fin d → ZMod 2)
    (x : Fin n → (Fin d → ZMod 2)) :
    (∑ S : Finset (Fin n), selWeight p n S * (if h ∈ solSpace (labeled r x) S then 1 else 0)) =
    ∏ i, if parity h (x i) = parity r (x i) then 1 else 1-p := by
  classical
  simpa [subWeight, selWeight, solSpace, labeled, parity_comm] using
    survival_powerset p (Finset.univ : Finset (Fin n)) (fun i => parity h (x i) = parity r (x i))
lemma sample_survival {d n : ℕ} (p : ℝ) (μ : PMF (Fin d → ZMod 2)) (r h : Fin d → ZMod 2) :
    (∑ x : Fin n → (Fin d → ZMod 2), (∏ i, (μ (x i)).toReal) *
      ∑ S : Finset (Fin n), selWeight p n S * (if h ∈ solSpace (labeled r x) S then 1 else 0)) =
      (1-p*err μ r (some h))^n := by
  classical
  simp_rw [survival_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Fin d → ZMod 2) =>
    (μ x).toReal * (if parity h x = parity r x then (1:ℝ) else 1-p))]
  have he : (∑ x, (μ x).toReal * (if parity h x = parity r x then (1:ℝ) else 1-p)) =
      1-p*err μ r (some h) := by
    rw [err_sum, Finset.mul_sum, ← pmf_real_sum μ, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : parity h x = parity r x
    · simp [hx, pmf_real_sum]
    · rw [if_neg hx, if_pos hx, pmf_real_sum]
      ring
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end ParityProof

-- ParityProof.SampleReal
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators Classical
lemma samplePr_ofReal {d n : ℕ} {O : Type*} [MeasurableSpace O]
    (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2)
    (A : (Fin n → Example d) → Measure O) (E : Set O)
    (f : (Fin n → (Fin d → ZMod 2)) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hA : ∀ x, A (labeled r x) E = ENNReal.ofReal (f x)) :
    samplePr μ r A E = ENNReal.ofReal (∑ x, (∏ i, (μ (x i)).toReal)*f x) := by
  unfold samplePr
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (Finset.prod_nonneg (fun i _ => ENNReal.toReal_nonneg)) (hf x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [hA, ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => ENNReal.toReal_nonneg)), ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (ENNReal.ofReal_toReal (μ.apply_ne_top _)).symm
  · intro i _
    exact ENNReal.toReal_nonneg
lemma samplePr_algA_score {d n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hε4 : ε ≤ 4)
    (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2)
    (E : Set (Option (Fin d → ZMod 2))) :
    samplePr μ r (fun z : Fin n → Example d => algA ε z) E =
      ENNReal.ofReal (∑ x : Fin n → (Fin d → ZMod 2),
        (∏ i, (μ (x i)).toReal)*baseScore (ε/4) (labeled r x) E) := by
  apply samplePr_ofReal
  · intro x
    exact baseScore_nonneg (by positivity) (by linarith) _ _
  · intro x
    exact algA_apply_score hε hε4 _ _
end ParityProof

-- ParityProof.BaseUtilityEstimate
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators Classical
lemma averaged_score_lower {d n : ℕ} {p a : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) :
    (1/2)*(1-∑ h : Fin d → ZMod 2, if a < err μ r (some h) then
      (1-p*err μ r (some h))^n else 0) ≤
    ∑ x : Fin n → (Fin d → ZMod 2), (∏ i, (μ (x i)).toReal) *
      baseScore p (labeled r x) {o | ∃ h, o = some h ∧ err μ r (some h) ≤ a} := by
  let w := fun x : Fin n → (Fin d → ZMod 2) => ∏ i, (μ (x i)).toReal
  let B := fun x : Fin n → (Fin d → ZMod 2) => ∑ h : Fin d → ZMod 2,
    if a < err μ r (some h) then
      ∑ S : Finset (Fin n), selWeight p n S*(if h ∈ solSpace (labeled r x) S then (1:ℝ) else 0) else 0
  have he : (∑ x, w x * (1-B x)) = 1-∑ h : Fin d → ZMod 2,
      if a < err μ r (some h) then (1-p*err μ r (some h))^n else 0 := by
    simp only [B, mul_sub, mul_one, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, iid_real_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : a < err μ r (some h)
    · simp only [if_pos hh]
      exact sample_survival p μ r h
    · simp [hh]
  rw [← he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hw : 0 ≤ w x := Finset.prod_nonneg (fun i _ => ENNReal.toReal_nonneg)
  have hb := mul_le_mul_of_nonneg_left
    (realizable_score_lower hp hp1 r x (fun h => err μ r (some h) ≤ a)) hw
  simp only [not_le] at hb
  change w x * ((1/2)*(1-B x)) ≤ _ at hb
  change (1/2)*(w x*(1-B x)) ≤ _
  nlinarith only [hb]
lemma survival_exp_bound {n : ℕ} {p a e : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (he1 : e ≤ 1) (hae : a ≤ e) :
    (1-p*e)^n ≤ Real.exp (-(p*(n:ℝ)*a)) := by
  have hnonneg : 0 ≤ 1-p*e := by nlinarith
  have hbase : 1-p*e ≤ Real.exp (-p*e) := by
    simpa [neg_mul] using Real.one_sub_le_exp_neg (p*e)
  have hpow := pow_le_pow_left₀ hnonneg hbase n
  rw [← Real.exp_nat_mul] at hpow
  apply hpow.trans
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left hae (mul_nonneg hp (Nat.cast_nonneg n))
  nlinarith
lemma finite_class_bad_bound {d n : ℕ} {p a : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) :
    (∑ h : Fin d → ZMod 2, if a < err μ r (some h) then
      (1-p*err μ r (some h))^n else 0) ≤
      (2:ℝ)^d * Real.exp (-(p*(n:ℝ)*a)) := by
  calc
    _ ≤ ∑ _h : Fin d → ZMod 2, Real.exp (-(p*(n:ℝ)*a)) := by
      apply Finset.sum_le_sum
      intro h _
      split_ifs with hh
      · exact survival_exp_bound hp hp1 (err_le_one μ r _) hh.le
      · exact Real.exp_nonneg _
    _ = _ := by simp
end ParityProof

-- ParityProof.BaseUtilityConstant
namespace ParityProof
open PrivLearn.Parity
lemma base_sample_exponent {d : ℕ} {ε α : ℝ} (hε : 0 < ε) (hα : 0 < α) :
    16*(d:ℝ) ≤ (ε/4)*(paramN 64 d ε α:ℝ)*(α/5) := by
  have h := Nat.le_ceil (64*(d:ℝ)/(ε*(α/5)))
  have he := (div_le_iff₀ (mul_pos hε (by positivity : 0<α/5))).mp h
  change 16*(d:ℝ) ≤ (ε/4)*(⌈64*(d:ℝ)/(ε*(α/5))⌉₊:ℝ)*(α/5)
  nlinarith
lemma exponential_class_small {d : ℕ} (hd : 1 ≤ d) :
    (2:ℝ)^d * Real.exp (-(16*(d:ℝ))) ≤ 1/4 := by
  have hex : Real.exp (-16) ≤ (1:ℝ)/8 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<8)
      (by linarith [Real.add_one_le_exp (16:ℝ)] : (8:ℝ)≤Real.exp 16)
  have he : Real.exp (-(16*(d:ℝ))) = (Real.exp (-16))^d := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, ← mul_pow]
  have hbase : 2*Real.exp (-16) ≤ (1:ℝ)/4 := by linarith
  calc
    _ ≤ ((1:ℝ)/4)^d := pow_le_pow_left₀ (by positivity) hbase d
    _ ≤ ((1:ℝ)/4)^1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
    _ = _ := by norm_num
end ParityProof

-- ParityProof.BaseUtility
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators Classical
lemma algA_base_utility {d : ℕ} (hd : 1 ≤ d) {ε α : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hα : 0 < α)
    (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) :
    (3/8 : ENNReal) ≤ samplePr μ r
      (fun z : Fin (paramN 64 d ε α) → Example d => algA ε z)
      {o | ∃ h, o = some h ∧ err μ r (some h) ≤ α/5} := by
  have hp : 0 ≤ ε/4 := by positivity
  have hp1 : ε/4 ≤ 1 := by linarith
  have hb := finite_class_bad_bound (n := paramN 64 d ε α) (a := α/5) hp hp1 μ r
  have he := base_sample_exponent (d := d) hε hα
  have hex : Real.exp (-((ε/4)*(paramN 64 d ε α:ℝ)*(α/5))) ≤ Real.exp (-(16*(d:ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbad : (∑ h : Fin d → ZMod 2, if α/5 < err μ r (some h) then
      (1-(ε/4)*err μ r (some h))^(paramN 64 d ε α) else 0) ≤ (1:ℝ)/4 :=
    hb.trans ((mul_le_mul_of_nonneg_left hex (by positivity)).trans (exponential_class_small hd))
  have hl := averaged_score_lower (n := paramN 64 d ε α) (a := α/5) hp hp1 μ r
  have hg : (3:ℝ)/8 ≤ ∑ x : Fin (paramN 64 d ε α) → (Fin d → ZMod 2),
      (∏ i, (μ (x i)).toReal) * baseScore (ε/4) (labeled r x)
        {o | ∃ h, o = some h ∧ err μ r (some h) ≤ α/5} := by linarith
  rw [samplePr_algA_score hε.le (by linarith)]
  have hcast : ENNReal.ofReal ((3:ℝ)/8) = (3/8:ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [← hcast]
  exact ENNReal.ofReal_le_ofReal hg
end ParityProof

-- ParityProof.CandidateLaw
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped Classical
noncomputable def candidateLaw {d:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2)
    (ε:ℝ) (b:ℕ) (h:Option (Fin d→ZMod 2)) : ENNReal :=
  samplePr μ r (fun z:Fin b→Example d=>algA ε z) {h}
lemma candidateLaw_event {d b:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) (ε:ℝ)
    (E:Set (Option (Fin d→ZMod 2))) :
    (∑h,if h∈E then candidateLaw μ r ε b h else 0)=
      samplePr μ r (fun z:Fin b→Example d=>algA ε z) E := by
  simp only [candidateLaw,samplePr]
  have hstep (h:Option (Fin d→ZMod 2)) :
      (if h∈E then ∑x:Fin b→(Fin d→ZMod 2),(∏i,μ (x i))*algA ε (labeled r x) {h} else 0)=
      ∑x:Fin b→(Fin d→ZMod 2),(∏i,μ (x i))*(if h∈E then algA ε (labeled r x) {h} else 0) := by
    split_ifs <;> simp
  simp_rw [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum,← Finset.sum_filter,sum_measure_singleton]
  congr 2
  ext h
  simp
lemma candidateLaw_sum {d:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) {ε:ℝ}
    (he:0<ε) (he1:ε≤1/2) (b:ℕ) : ∑h,candidateLaw μ r ε b h=1 := by
  have h:=candidateLaw_event (b:=b) μ r ε Set.univ
  simp only [Set.mem_univ,ite_true] at h
  rw [h]
  unfold samplePr
  simp only [algA_univ he.le (by linarith),mul_one]
  have hm : ∑x,μ x=1 := by simpa [tsum_fintype] using μ.tsum_coe
  simpa [hm] using (Fintype.prod_sum (fun (_:Fin b) (x:Fin d→ZMod 2)=>μ x)).symm
lemma candidateLaw_le_one {d:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) {ε:ℝ}
    (he:0<ε) (he1:ε≤1/2) (b:ℕ) (h:Option (Fin d→ZMod 2)) : candidateLaw μ r ε b h≤1 := by
  rw [← candidateLaw_sum μ r he he1 b]
  exact Finset.single_le_sum (fun _ _=>zero_le) (Finset.mem_univ h)
lemma candidateLaw_ne_top {d:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) {ε:ℝ}
    (he:0<ε) (he1:ε≤1/2) (b:ℕ) (h:Option (Fin d→ZMod 2)) : candidateLaw μ r ε b h≠⊤ :=
  ne_of_lt ((candidateLaw_le_one μ r he he1 b h).trans_lt (by simp))
lemma candidateLaw_real_sum {d:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) {ε:ℝ}
    (he:0<ε) (he1:ε≤1/2) (b:ℕ) : ∑h,(candidateLaw μ r ε b h).toReal=1 := by
  rw [← ENNReal.toReal_sum (fun h _=>candidateLaw_ne_top μ r he he1 b h),candidateLaw_sum μ r he he1 b]
  simp
lemma candidateLaw_real_good {d:ℕ} (hd:1≤d) {ε α:ℝ} (he:0<ε) (he1:ε≤1/2) (ha:0<α)
    (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) :
    (3/8:ℝ)≤∑o,if ∃h,o=some h ∧ err μ r (some h)≤α/5 then
      (candidateLaw μ r ε (paramN 64 d ε α) o).toReal else 0 := by
  let E : Set (Option (Fin d→ZMod 2)) := {o|∃h,o=some h ∧ err μ r (some h)≤α/5}
  have h:=algA_base_utility hd he he1 ha μ r
  rw [← candidateLaw_event μ r ε E] at h
  have hfin : (∑o,if o∈E then candidateLaw μ r ε (paramN 64 d ε α) o else 0)≠⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt _ (by simp : (1:ENNReal)<⊤)
    rw [← candidateLaw_sum μ r he he1 (paramN 64 d ε α)]
    apply Finset.sum_le_sum
    intro o _
    split_ifs <;> simp
  have h' : (3/8:ENNReal)≤∑o,if o∈E then candidateLaw μ r ε (paramN 64 d ε α) o else 0 := by
    convert h using 1
    apply Finset.sum_congr rfl
    intro o _
    split_ifs <;> simp_all
  have hr := ENNReal.toReal_mono hfin h'
  rw [ENNReal.toReal_sum] at hr
  · simpa [E,apply_ite] using hr
  · intro o _
    split_ifs <;> simp [candidateLaw_ne_top μ r he he1]
end ParityProof

-- ParityProof.FiniteAmplification
namespace ParityProof
open scoped Classical
lemma finite_amplification {A:Type*} [Fintype A] (w:A→ℝ) (hw:∀x,0≤w x)
    (hsum:∑x,w x=1) (G:A→Prop) (hgood:(3/8:ℝ)≤∑x,if G x then w x else 0) (k:ℕ) :
    1-(5/8:ℝ)^k ≤ ∑H:Fin k→A,(∏j,w (H j))*(if ∃j,G (H j) then 1 else 0) := by
  have hsplit : (∑x,if G x then w x else 0)+(∑x,if ¬G x then w x else 0)=1 := by
    rw [← Finset.sum_add_distrib,← hsum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  have hb0 : 0≤∑x,if ¬G x then w x else 0 := Finset.sum_nonneg (fun x _=>by split_ifs <;> simp [hw x])
  have hb : (∑x,if ¬G x then w x else 0)≤5/8 := by linarith
  have hbpow := pow_le_pow_left₀ hb0 hb k
  have htotal : (∑H:Fin k→A,∏j,w (H j))=1 := by
    simpa [hsum] using (Fintype.prod_sum (fun (_:Fin k) (x:A)=>w x)).symm
  have hterm (H:Fin k→A) : (∏j,w (H j))*(if ¬∃j,G (H j) then 1 else 0)=
      ∏j,if ¬G (H j) then w (H j) else 0 := by
    by_cases hx:∃j,G (H j)
    · obtain ⟨j,hj⟩:=hx
      have hh : ¬(¬∃i,G (H i)) := by simpa using (show ∃i,G (H i) from ⟨j,hj⟩)
      rw [if_neg hh,mul_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
    · have hall : ∀j,¬G (H j) := by simpa using hx
      simp [hall]
  have hbad : (∑H:Fin k→A,(∏j,w (H j))*(if ¬∃j,G (H j) then 1 else 0))=
      (∑x,if ¬G x then w x else 0)^k := by
    simp_rw [hterm]
    rw [← Fintype.prod_sum (fun (_:Fin k) (x:A)=>if ¬G x then w x else 0)]
    simp
  have hboth : (∑H:Fin k→A,(∏j,w (H j))*(if ∃j,G (H j) then 1 else 0))+
      (∑H:Fin k→A,(∏j,w (H j))*(if ¬∃j,G (H j) then 1 else 0))=1 := by
    rw [← Finset.sum_add_distrib,← htotal]
    apply Finset.sum_congr rfl
    intro H _
    split_ifs <;> simp_all
  rw [hbad] at hboth
  linarith
end ParityProof

-- ParityProof.ParameterBounds
open MeasureTheory PrivLearn.Parity
namespace ParityProof
lemma candidate_failure_bound {β:ℝ} (hb:0<β) (hb1:β<1/2) :
    (5/8:ℝ)^paramK β ≤ β/3 := by
  have hc := Nat.le_ceil (Real.logb (4/3) (1/(β/2)))
  have hx := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<4/3)
    (by positivity : 0<(1:ℝ)/(β/2))).mp hc
  rw [Real.rpow_natCast] at hx
  change 1/(β/2) ≤ (4/3:ℝ)^paramK β at hx
  have hp : (0:ℝ)<(3/4:ℝ)^paramK β := by positivity
  have hi : (3/4:ℝ)^paramK β * (4/3:ℝ)^paramK β = 1 := by
    rw [← mul_pow]; norm_num
  have hmul := mul_le_mul_of_nonneg_left hx (le_of_lt hp)
  rw [hi] at hmul
  have hsmall : (3/4:ℝ)^paramK β ≤ β/2 := by
    have hden : 0<β/2 := by positivity
    have : (3/4:ℝ)^paramK β/(β/2) ≤ 1 := by simpa [div_eq_mul_inv] using hmul
    exact (div_le_iff₀ hden).mp this |>.trans_eq (one_mul _)
  have hpow := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤5/6)
    (by norm_num : (5/6:ℝ)≤1) (paramK_bounds hb hb1).1
  calc
    (5/8:ℝ)^paramK β = (3/4:ℝ)^paramK β * (5/6:ℝ)^paramK β := by rw [← mul_pow]; norm_num
    _ ≤ (β/2)*(5/6:ℝ)^3 := mul_le_mul hsmall hpow (by positivity) (by positivity)
    _ ≤ β/3 := by nlinarith
lemma validation_log_bound {β:ℝ} (hb:0<β) (hb1:β<1/2) :
    Real.logb 2 (paramK β/(β/2)) ≤ 20*Real.logb 2 (1/β) := by
  obtain ⟨hl,he⟩ := beta_log_bounds hb hb1
  have hk := paramK_pos hb hb1
  have hk0 : (0:ℝ)<paramK β := by exact_mod_cast hk
  have hkhi := (paramK_bounds hb hb1).2
  obtain ⟨hlo,hhi⟩ := log_two_bounds
  have hp : 0<Real.log 2 := by linarith
  have hklog : Real.log (paramK β) ≤ (paramK β:ℝ) := Real.log_le_self (by positivity)
  have hid : Real.log (paramK β/(β/2)) = Real.log (paramK β) + Real.log (1/(β/2)) := by
    rw [div_eq_mul_inv, Real.log_mul (ne_of_gt hk0) (by positivity), one_div]
  rw [Real.logb, div_le_iff₀ hp,hid,he]
  have hm : (paramK β:ℝ) ≤ 2*(paramK β:ℝ)*Real.log 2 := by nlinarith
  nlinarith
lemma paramN_upper {d:ℕ} {ε α:ℝ} (he:0<ε) (ha:0<α) :
    (paramN 64 d ε α:ℝ) ≤ 320*d/(ε*α)+1 := by
  unfold paramN
  have h := Nat.ceil_lt_add_one (show 0≤(64:ℝ)*d/(ε*(α/5)) by positivity)
  have hid : (64:ℝ)*d/(ε*(α/5))=320*d/(ε*α) := by field_simp; ring
  rw [hid] at h ⊢
  exact le_of_lt h
lemma paramS_upper {ε α β:ℝ} (he:0<ε) (ha:0<α) (hb:0<β) (hb1:β<1/2) :
    (paramS 64 ε α β:ℝ) ≤ 57600*(Real.logb 2 (1/β))^2/(ε*α)+1 := by
  have hk := paramK_pos hb hb1
  have hk' : (1:ℝ)≤paramK β := by exact_mod_cast hk
  have hq : 1 < (paramK β:ℝ)/(β/2) := (lt_div_iff₀ (by positivity)).2 (by linarith)
  have hl := Real.logb_pos (by norm_num : (1:ℝ)<2) hq
  have hceil := Nat.ceil_lt_add_one (show 0≤(64:ℝ)*paramK β/((α/5)*ε)*Real.logb 2 (paramK β/(β/2)) by positivity)
  have hlog := validation_log_bound hb hb1
  have hkhi := (paramK_bounds hb hb1).2
  have hell := (beta_log_bounds hb hb1).1
  have hid : (64:ℝ)*paramK β/((α/5)*ε)=320*paramK β/(ε*α) := by field_simp; ring
  rw [hid] at hceil
  have hprod : (320*(paramK β:ℝ)/(ε*α))*Real.logb 2 (paramK β/(β/2)) ≤
      (320*(9*Real.logb 2 (1/β))/(ε*α))*(20*Real.logb 2 (1/β)) := by gcongr
  have hid2 : (320*(9*Real.logb 2 (1/β))/(ε*α))*(20*Real.logb 2 (1/β)) =
      57600*(Real.logb 2 (1/β))^2/(ε*α) := by ring
  rw [hid2] at hprod
  unfold paramS
  rw [hid]
  linarith
lemma sample_threshold {d:ℕ} (hd:1≤d) {ε α β:ℝ}
    (he:0<ε) (he1:ε≤1/2) (ha:0<α) (ha1:α<1/2) (hb:0<β) (hb1:β<1/2)
    (n:ℕ) (hn:1000000*((d:ℝ)+Real.logb 2 (1/β))*Real.logb 2 (1/β)/(ε*α)≤n) :
    paramK β*paramN 64 d ε α+paramS 64 ε α β<n := by
  have hl := (beta_log_bounds hb hb1).1
  have hk := (paramK_bounds hb hb1).2
  have hN := paramN_upper (d:=d) he ha
  have hS := paramS_upper he ha hb hb1
  have hD : 0<ε*α := mul_pos he ha
  have hD1 : ε*α≤1 := by nlinarith
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  have hu : (paramK β:ℝ)*(paramN 64 d ε α:ℝ)+(paramS 64 ε α β:ℝ) ≤
      (9*Real.logb 2 (1/β))*(320*d/(ε*α)+1)+57600*(Real.logb 2 (1/β))^2/(ε*α)+1 := by
    have hp := mul_le_mul hk hN (by positivity) (by positivity)
    linarith
  have hstrict : (9*Real.logb 2 (1/β))*(320*d/(ε*α)+1)+57600*(Real.logb 2 (1/β))^2/(ε*α)+1 <
      1000000*((d:ℝ)+Real.logb 2 (1/β))*Real.logb 2 (1/β)/(ε*α) := by
    apply (mul_lt_mul_iff_left₀ hD).mp
    field_simp
    have hprod : 0≤(d:ℝ)*Real.logb 2 (1/β) := by positivity
    have hm := mul_le_mul_of_nonneg_right hD1 (show 0≤Real.logb 2 (1/β) by linarith)
    nlinarith [sq_nonneg (Real.logb 2 (1/β)-1)]
  have := lt_of_le_of_lt hu (lt_of_lt_of_le hstrict hn)
  exact_mod_cast this
end ParityProof

-- ParityProof.CandidateAmplification
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped Classical
lemma candidate_tuple_sum {d:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) {ε:ℝ}
    (he:0<ε) (he1:ε≤1/2) (b k:ℕ) :
    (∑H:Fin k→Option (Fin d→ZMod 2),∏j,candidateLaw μ r ε b (H j))=1 := by
  simpa [candidateLaw_sum μ r he he1] using
    (Fintype.prod_sum (fun (_:Fin k) (h:Option (Fin d→ZMod 2))=>candidateLaw μ r ε b h)).symm
lemma candidate_amplification {d:ℕ} (hd:1≤d) {ε α β:ℝ} (he:0<ε) (he1:ε≤1/2)
    (ha:0<α) (hb:0<β) (hb1:β<1/2) (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) :
    ENNReal.ofReal (1-β/3)≤
      ∑H:Fin (paramK β)→Option (Fin d→ZMod 2),
        (∏j,candidateLaw μ r ε (paramN 64 d ε α) (H j))*
          (if ∃j h,H j=some h ∧ err μ r (some h)≤α/5 then 1 else 0) := by
  let b := paramN 64 d ε α
  let k := paramK β
  let w : Option (Fin d→ZMod 2)→ℝ := fun h=>(candidateLaw μ r ε b h).toReal
  let G : Option (Fin d→ZMod 2)→Prop := fun o=>∃h,o=some h ∧ err μ r (some h)≤α/5
  have hgood' : (3/8:ℝ)≤∑x,@ite ℝ (G x) (Classical.propDecidable (G x)) (w x) 0 := by
    convert candidateLaw_real_good hd he he1 ha μ r using 1
    apply Finset.sum_congr rfl
    intro o _
    by_cases ho:G o <;> simp_all only [G,w,b,ite_true,ite_false]
  have hreal0 := finite_amplification w (fun _=>ENNReal.toReal_nonneg)
    (candidateLaw_real_sum μ r he he1 b) G hgood' k
  have hreal : 1-(5/8:ℝ)^k≤∑H:Fin k→Option (Fin d→ZMod 2),(∏j,w (H j))*(if ∃j,G (H j) then 1 else 0) := by
    convert hreal0 using 1
    apply Finset.sum_congr rfl
    intro H _
    split_ifs <;> simp_all
  have hbound : 1-β/3≤∑H:Fin k→Option (Fin d→ZMod 2),(∏j,w (H j))*(if ∃j,G (H j) then 1 else 0) := by
    have hc:=candidate_failure_bound hb hb1
    change (5/8:ℝ)^k≤β/3 at hc
    linarith
  have hconvert : ENNReal.ofReal (∑H:Fin k→Option (Fin d→ZMod 2),(∏j,w (H j))*(if ∃j,G (H j) then 1 else 0))=
      ∑H:Fin k→Option (Fin d→ZMod 2),(∏j,candidateLaw μ r ε b (H j))*(if ∃j,G (H j) then 1 else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun H _=>by dsimp [w]; positivity)]
    apply Finset.sum_congr rfl
    intro H _
    by_cases hG:∃j,G (H j)
    · simp only [hG,ite_true,mul_one]
      rw [ENNReal.ofReal_prod_of_nonneg (fun j _=>ENNReal.toReal_nonneg)]
      apply Finset.prod_congr rfl
      intro j _
      exact ENNReal.ofReal_toReal (candidateLaw_ne_top μ r he he1 b (H j))
    · simp [hG]
  rw [← hconvert]
  exact ENNReal.ofReal_le_ofReal hbound
end ParityProof

-- ParityProof.BernoulliMGF
open MeasureTheory
namespace ParityProof
open scoped Classical
noncomputable def validationWeight {A:Type*} [Fintype A] (μ:PMF A) {n:ℕ} (x:Fin n→A) : ℝ := ∏i,(μ (x i)).toReal
noncomputable def bernoulliMean {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) : ℝ := by
  classical
  exact ∑x,if B x then (μ x).toReal else 0
noncomputable def bernoulliCount {A:Type*} {n:ℕ} (B:A→Prop) (x:Fin n→A) : ℝ := by
  classical
  exact ∑i,if B (x i) then 1 else 0
lemma bernoulliMean_nonneg {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) : 0≤bernoulliMean μ B := by
  classical
  exact Finset.sum_nonneg (fun x _=>by positivity)
lemma bernoulliMean_le_one {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) : bernoulliMean μ B≤1 := by
  classical
  rw [← pmf_real_sum μ]
  exact Finset.sum_le_sum (fun x _=>by split_ifs <;> simp [ENNReal.toReal_nonneg])
lemma bernoulli_single_mgf {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) (t:ℝ) :
    (∑x,(μ x).toReal*Real.exp (t*(if B x then 1 else 0)))=1+bernoulliMean μ B*(Real.exp t-1) := by
  classical
  have h (x:A) : (μ x).toReal*Real.exp (t*(if B x then 1 else 0))=
      (μ x).toReal+(if B x then (μ x).toReal else 0)*(Real.exp t-1) := by
    split_ifs <;> simp; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,pmf_real_sum]
  rfl
lemma bernoulli_mgf {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) (t:ℝ) (n:ℕ) :
    (∑x:Fin n→A,validationWeight μ x*Real.exp (t*bernoulliCount B x))=
      (1+bernoulliMean μ B*(Real.exp t-1))^n := by
  classical
  simp only [validationWeight,bernoulliCount,Finset.mul_sum,Real.exp_sum,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_:Fin n) (x:A)=>(μ x).toReal*Real.exp (t*(if B x then 1 else 0)))]
  simp only [bernoulli_single_mgf,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
lemma bernoulli_mgf_le {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) (t:ℝ) (n:ℕ) :
    (∑x:Fin n→A,validationWeight μ x*Real.exp (t*bernoulliCount B x))≤
      Real.exp ((n:ℝ)*bernoulliMean μ B*(Real.exp t-1)) := by
  classical
  rw [bernoulli_mgf]
  have h0 : 0≤1+bernoulliMean μ B*(Real.exp t-1) := by
    rw [← bernoulli_single_mgf]
    exact Finset.sum_nonneg (fun _ _=>by positivity)
  have h := pow_le_pow_left₀ h0 (show 1+bernoulliMean μ B*(Real.exp t-1)≤Real.exp (bernoulliMean μ B*(Real.exp t-1)) by
    simpa [add_comm] using Real.add_one_le_exp (bernoulliMean μ B*(Real.exp t-1))) n
  rw [← Real.exp_nat_mul] at h
  simpa only [mul_assoc] using h
lemma bernoulli_chernoff {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) (t z:ℝ) (n:ℕ) :
    (∑x:Fin n→A,if t*z≤t*bernoulliCount B x then validationWeight μ x else 0)≤
      Real.exp ((n:ℝ)*bernoulliMean μ B*(Real.exp t-1)-t*z) := by
  classical
  have hm : (∑x:Fin n→A,if t*z≤t*bernoulliCount B x then validationWeight μ x else 0)*Real.exp (t*z)≤
      ∑x:Fin n→A,validationWeight μ x*Real.exp (t*bernoulliCount B x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) (by unfold validationWeight; positivity)
    · simp only [zero_mul]
      unfold validationWeight
      positivity
  have h := hm.trans (bernoulli_mgf_le μ B t n)
  apply (le_div_iff₀ (Real.exp_pos (t*z))).mpr at h
  simpa [Real.exp_sub] using h
end ParityProof

-- ParityProof.BernoulliTails
namespace ParityProof
open scoped Classical
lemma log_five_fourths_bounds : 0<Real.log (5/4:ℝ) ∧ Real.log (5/4:ℝ)≤9/40 := by
  refine ⟨Real.log_pos (by norm_num),?_⟩
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<5/4)).2
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤9/40) 4
  norm_num [Finset.sum_range_succ] at h
  linarith
lemma bernoulli_upper_tail {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) {a:ℝ}
    (ha:0≤a) (hp:bernoulliMean μ B≤a) (n:ℕ) :
    (∑x:Fin n→A,if 2*a*n≤bernoulliCount B x then validationWeight μ x else 0)≤Real.exp (-(n:ℝ)*a/3) := by
  have ht : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h := bernoulli_chernoff μ B (Real.log 2) (2*a*n) n
  simp only [mul_le_mul_iff_right₀ ht,Real.exp_log (by norm_num : (0:ℝ)<2)] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog : (2/3:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnp := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤n by positivity)
  have hna : 0≤(n:ℝ)*a := by positivity
  have hh := mul_le_mul_of_nonneg_left hlog hna
  nlinarith
lemma bernoulli_lower_tail {A:Type*} [Fintype A] (μ:PMF A) (B:A→Prop) {a:ℝ}
    (ha:0≤a) (hp:5*a≤bernoulliMean μ B) (n:ℕ) :
    (∑x:Fin n→A,if bernoulliCount B x≤4*a*n then validationWeight μ x else 0)≤Real.exp (-(n:ℝ)*a/10) := by
  have ht := log_five_fourths_bounds.1
  have h := bernoulli_chernoff μ B (-Real.log (5/4)) (4*a*n) n
  have hex : Real.exp (-Real.log (5/4:ℝ))=4/5 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  have hcond (x:Fin n→A) : (-Real.log (5/4))* (4*a*n)≤(-Real.log (5/4))*bernoulliCount B x ↔
      bernoulliCount B x≤4*a*n := mul_le_mul_left_of_neg (neg_neg_of_pos ht)
  simp only [hcond,hex] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hnp := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤n by positivity)
  have hna : 0≤(n:ℝ)*a := by positivity
  have hh := mul_le_mul_of_nonneg_left log_five_fourths_bounds.2 hna
  nlinarith
end ParityProof

-- ParityProof.TestValidation
open PrivLearn.Parity
namespace ParityProof
open scoped Classical
lemma testErr_count {d s:ℕ} (r h:Fin d→ZMod 2) (x:Fin s→(Fin d→ZMod 2)) :
    testErr (labeled r x) (some h)=bernoulliCount (fun u=>parity h u≠parity r u) x/(s:ℝ) := by
  dsimp only [testErr]
  congr 1
  rw [Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,bernoulliCount]
  apply Finset.sum_congr rfl
  intro j _
  simp only [labeled]
  split_ifs <;> simp_all
lemma err_bernoulli {d:ℕ} (μ:PMF (Fin d→ZMod 2)) (r h:Fin d→ZMod 2) :
    err μ r (some h)=bernoulliMean μ (fun u=>parity h u≠parity r u) := by
  rw [err_sum]
  unfold bernoulliMean
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all
noncomputable def badCandidate {d s:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2)
    (a:ℝ) (o:Option (Fin d→ZMod 2)) (x:Fin s→(Fin d→ZMod 2)) : Prop :=
  match o with
  | none=>False
  | some h=>(err μ r (some h)≤a ∧ 2*a≤testErr (labeled r x) (some h)) ∨
      (5*a<err μ r (some h) ∧ testErr (labeled r x) (some h)≤4*a)
lemma badCandidate_bound {d s:ℕ} (hs:0<s) (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2)
    {a:ℝ} (ha:0≤a) (o:Option (Fin d→ZMod 2)) :
    (∑x:Fin s→(Fin d→ZMod 2),if badCandidate μ r a o x then validationWeight μ x else 0)≤
      Real.exp (-(s:ℝ)*a/10) := by
  cases o with
  | none=>simp [badCandidate,Real.exp_nonneg]
  | some h=>
    let B := fun u:Fin d→ZMod 2=>parity h u≠parity r u
    have hs' : (0:ℝ)<s := by positivity
    by_cases hp:err μ r (some h)≤a
    · have hnp : ¬5*a<err μ r (some h) := by linarith
      simp only [badCandidate,hp,hnp,true_and,false_and,or_false,testErr_count,le_div_iff₀ hs']
      have hu:=bernoulli_upper_tail μ B ha (by simpa [B,← err_bernoulli] using hp) s
      apply hu.trans
      apply Real.exp_le_exp.mpr
      have : 0≤(s:ℝ)*a := by positivity
      linarith
    · by_cases hp':5*a<err μ r (some h)
      · simp only [badCandidate,hp,hp',false_and,true_and,false_or,testErr_count,div_le_iff₀ hs']
        exact bernoulli_lower_tail μ B ha (by simpa [B,← err_bernoulli] using le_of_lt hp') s
      · simp [badCandidate,hp,hp',Real.exp_nonneg]
lemma weighted_exists_le {A I:Type*} [Fintype A] [Fintype I] (w:A→ℝ) (hw:∀x,0≤w x) (B:I→A→Prop) :
    (∑x,if ∃i,B i x then w x else 0)≤∑i,∑x,if B i x then w x else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with h
  · obtain ⟨i,hi⟩:=h
    have hh := Finset.single_le_sum (f:=fun j=>if B j x then w x else 0)
      (fun j _=>by split_ifs <;> simp [hw x]) (Finset.mem_univ i)
    simpa [hi] using hh
  · exact Finset.sum_nonneg (fun i _=>by split_ifs <;> simp [hw x])
lemma validation_bad_bound {d k s:ℕ} (hs:0<s) (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2)
    {a:ℝ} (ha:0≤a) (H:Fin k→Option (Fin d→ZMod 2)) :
    (∑x:Fin s→(Fin d→ZMod 2),if ∃j,badCandidate μ r a (H j) x then validationWeight μ x else 0)≤
      (k:ℝ)*Real.exp (-(s:ℝ)*a/10) := by
  have hh := weighted_exists_le (A:=Fin s→(Fin d→ZMod 2)) (validationWeight μ) (fun x=>by unfold validationWeight; positivity) (fun j:Fin k=>badCandidate μ r a (H j))
  have hh' : (∑x:Fin s→(Fin d→ZMod 2),if ∃j,badCandidate μ r a (H j) x then validationWeight μ x else 0)≤
      ∑j:Fin k,∑x:Fin s→(Fin d→ZMod 2),if badCandidate μ r a (H j) x then validationWeight μ x else 0 := by
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  apply hh'.trans
  calc
    _ ≤ ∑_:Fin k,Real.exp (-(s:ℝ)*a/10) := Finset.sum_le_sum (fun j _=>badCandidate_bound hs μ r ha (H j))
    _ = _ := by simp
end ParityProof

-- ParityProof.NoiseEvent
open MeasureTheory Set PrivLearn.Generic
namespace ParityProof
lemma noise_bad_measure {k:ℕ} {s a:ℝ} (hs:0<s) (ha:0≤a) :
    (Measure.pi (fun _:Fin k=>laplace s)) {η:Fin k→ℝ | ∃j,a < |η j|}≤
      ENNReal.ofReal ((k:ℝ)*Real.exp (-a/s)) := by
  let := laplace_probability hs
  have hsingle (j:Fin k) : (Measure.pi (fun _:Fin k=>laplace s)) {η:Fin k→ℝ | a < |η j|}≤
      ENNReal.ofReal (Real.exp (-a/s)) := by
    have hm := measurePreserving_eval (μ:=fun _:Fin k=>laplace s) j
    have he := hm.measure_preimage (show MeasurableSet {x:ℝ | a < |x|} by measurability).nullMeasurableSet
    change (Measure.pi (fun _:Fin k=>laplace s)) (Function.eval j ⁻¹' {x:ℝ | a < |x|})≤_
    rw [he]
    exact laplace_abs_tail hs ha
  calc
    (Measure.pi (fun _:Fin k=>laplace s)) {η:Fin k→ℝ | ∃j,a < |η j|} =
        (Measure.pi (fun _:Fin k=>laplace s)) (⋃j:Fin k,{η:Fin k→ℝ | a < |η j|}) := by congr 1; ext η; simp
    _ ≤ ∑j:Fin k,(Measure.pi (fun _:Fin k=>laplace s)) {η:Fin k→ℝ | a < |η j|} := by
      simpa only [tsum_fintype] using measure_iUnion_le (fun j:Fin k=>{η:Fin k→ℝ | a < |η j|})
    _ ≤ ∑_:Fin k,ENNReal.ofReal (Real.exp (-a/s)) := Finset.sum_le_sum (fun j _=>hsingle j)
    _ = ENNReal.ofReal ((k:ℝ)*Real.exp (-a/s)) := by simp [ENNReal.ofReal_mul]
end ParityProof

-- ParityProof.SelectionUtility
open MeasureTheory Set PrivLearn.Parity PrivLearn.Generic
namespace ParityProof
open scoped Classical
lemma select_good_validation {d k s:ℕ} (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2)
    (a:ℝ) (H:Fin k→Option (Fin d→ZMod 2)) (x:Fin s→(Fin d→ZMod 2)) (η:Fin k→ℝ)
    (hgood:∃j h,H j=some h ∧ err μ r (some h)≤a)
    (hvalid:¬∃j,badCandidate μ r a (H j) x) (hnoise:∀j,|η j|≤a) :
    ∃h,select H (fun j=>testErr (labeled r x) (H j)+η j)=AstarOut.hyp h ∧ err μ r (some h)≤5*a := by
  obtain ⟨j,h,hj,herr⟩:=hgood
  have hjemp : testErr (labeled r x) (H j)<2*a := by
    by_contra hh
    apply hvalid
    exact ⟨j,by simp only [hj,badCandidate]; exact Or.inl ⟨herr,by simpa only [hj] using le_of_not_gt hh⟩⟩
  apply select_good_of_gap H _ (fun h=>err μ r (some h)≤5*a) j h hj
  intro i h' hi hbad
  have hiemp : 4*a<testErr (labeled r x) (H i) := by
    by_contra hh
    apply hvalid
    exact ⟨i,by simp only [hi,badCandidate]; exact Or.inr ⟨lt_of_not_ge hbad,by simpa only [hi] using le_of_not_gt hh⟩⟩
  have hjnoise := (abs_le.mp (hnoise j)).2
  have hinoise := (abs_le.mp (hnoise i)).1
  linarith
lemma test_success_real {d k s:ℕ} (hk:0<k) (hs:0<s) {ε:ℝ} (he:0<ε)
    (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2) {a:ℝ} (ha:0≤a)
    (H:Fin k→Option (Fin d→ZMod 2)) (x:Fin s→(Fin d→ZMod 2))
    (hgood:∃j h,H j=some h ∧ err μ r (some h)≤a)
    (hvalid:¬∃j,badCandidate μ r a (H j) x) :
    1-(k:ℝ)*Real.exp (-a/((k:ℝ)/(s*ε))) ≤
      (testMechanism H (labeled r x) ε {o|∃h,o=AstarOut.hyp h ∧ err μ r (some h)≤5*a}).toReal := by
  let L := Measure.pi (fun _:Fin k=>laplace ((k:ℝ)/(s*ε)))
  let bad : Set (Fin k→ℝ) := {η|∃j,a < |η j|}
  let E : Set (AstarOut d) := {o|∃h,o=AstarOut.hyp h ∧ err μ r (some h)≤5*a}
  have hscale : 0<(k:ℝ)/(s*ε) := by positivity
  let := laplace_probability hscale
  have hbad : MeasurableSet bad := by dsimp [bad]; measurability
  have hE : MeasurableSet E := by trivial
  have hsub : badᶜ ⊆ (fun η:Fin k→ℝ=>select H (fun j=>testErr (labeled r x) (H j)+η j)) ⁻¹' E := by
    intro η hη
    apply select_good_validation μ r a H x η hgood hvalid
    intro j
    exact le_of_not_gt (fun hj=>hη ⟨j,hj⟩)
  have hm := measureReal_mono (μ:=L) hsub
  rw [measureReal_compl hbad] at hm
  have hu : L.real univ=1 := by simp [L]
  rw [hu] at hm
  have hb := ENNReal.toReal_mono (by finiteness) (noise_bad_measure (k:=k) hscale ha)
  rw [ENNReal.toReal_ofReal (by positivity)] at hb
  change (L bad).toReal≤_ at hb
  have hmap : (testMechanism H (labeled r x) ε E).toReal=
      L.real ((fun η:Fin k→ℝ=>select H (fun j=>testErr (labeled r x) (H j)+η j)) ⁻¹' E) := by
    rw [testMechanism,Measure.map_apply (noisy_select_measurable H _) hE]
    rfl
  rw [hmap]
  change 1-(L bad).toReal≤_ at hm
  linarith
end ParityProof

-- ParityProof.ParameterBudgets
open PrivLearn.Parity
namespace ParityProof
lemma paramS_lower {ε α β:ℝ} (he:0<ε) (ha:0<α) :
    64*(paramK β:ℝ)*Real.logb 2 (paramK β/(β/2)) ≤ (paramS 64 ε α β:ℝ)*(α/5)*ε := by
  have h := Nat.le_ceil ((64:ℝ)*paramK β/((α/5)*ε)*Real.logb 2 (paramK β/(β/2)))
  change _ ≤ (paramS 64 ε α β:ℝ) at h
  have hid : (64:ℝ)*paramK β/((α/5)*ε)*Real.logb 2 (paramK β/(β/2)) =
      (64*paramK β*Real.logb 2 (paramK β/(β/2)))/((α/5)*ε) := by ring
  rw [hid,div_le_iff₀ (by positivity)] at h
  nlinarith
lemma validation_exponents {ε α β:ℝ} (he:0<ε) (he1:ε≤1/2) (ha:0<α)
    (hb:0<β) (hb1:β<1/2) :
    2*Real.log (paramK β/(β/2)) ≤ (paramS 64 ε α β:ℝ)*(α/5)/10 ∧
    2*Real.log (paramK β/(β/2)) ≤ (paramS 64 ε α β:ℝ)*ε*(α/5)/paramK β := by
  have hk : (1:ℝ)≤paramK β := by exact_mod_cast paramK_pos hb hb1
  have hq : 1<(paramK β:ℝ)/(β/2) := (lt_div_iff₀ (by positivity)).2 (by linarith)
  have hl : 0<Real.log ((paramK β:ℝ)/(β/2)) := Real.log_pos hq
  have hlb := Real.logb_pos (by norm_num : (1:ℝ)<2) hq
  have hlog : Real.log ((paramK β:ℝ)/(β/2)) ≤ Real.logb 2 (paramK β/(β/2)) := by
    rw [Real.logb,le_div_iff₀ (by have := log_two_bounds; linarith : 0<Real.log 2)]
    have := mul_le_mul_of_nonneg_left log_two_bounds.2 (le_of_lt hl)
    simpa using this
  have hlow := paramS_lower he ha (β:=β)
  have hprod := mul_le_mul_of_nonneg_left hlog (show 0≤64*(paramK β:ℝ) by positivity)
  have hS : 0≤(paramS 64 ε α β:ℝ)*(α/5) := by positivity
  have hcap := mul_le_mul_of_nonneg_left he1 hS
  have hklog := mul_le_mul_of_nonneg_right hk (le_of_lt hl)
  constructor
  · nlinarith
  · apply (le_div_iff₀ (by positivity : (0:ℝ)<paramK β)).2
    nlinarith
lemma exponential_budget {β:ℝ} (hb:0<β) (hb1:β<1/2) {z:ℝ}
    (hz:2*Real.log (paramK β/(β/2))≤z) :
    (paramK β:ℝ)*Real.exp (-z)≤β/3 := by
  have hk : (1:ℝ)≤paramK β := by exact_mod_cast paramK_pos hb hb1
  have hk0 : (0:ℝ)<paramK β := by linarith
  have hq : 0<(paramK β:ℝ)/(β/2) := by positivity
  have hpow : Real.exp (-2*Real.log (paramK β/(β/2))) = (β/(2*paramK β))^2 := by
    rw [show -2*Real.log ((paramK β:ℝ)/(β/2)) = -(Real.log ((paramK β:ℝ)/(β/2))+Real.log ((paramK β:ℝ)/(β/2))) by ring,
      Real.exp_neg,Real.exp_add,Real.exp_log hq]
    field_simp
  have hexp := Real.exp_le_exp.mpr (show -z≤ -2*Real.log ((paramK β:ℝ)/(β/2)) by linarith)
  rw [hpow] at hexp
  have hmul := mul_le_mul_of_nonneg_left hexp (le_of_lt hk0)
  have hid : (paramK β:ℝ)*(β/(2*paramK β))^2=β^2/(4*paramK β) := by field_simp; ring
  rw [hid] at hmul
  apply hmul.trans
  apply (div_le_iff₀ (by positivity)).2
  nlinarith
lemma validation_budget {ε α β:ℝ} (he:0<ε) (he1:ε≤1/2) (ha:0<α)
    (hb:0<β) (hb1:β<1/2) :
    (paramK β:ℝ)*Real.exp (-(paramS 64 ε α β:ℝ)*(α/5)/10)≤β/3 := by
  simpa only [neg_div,neg_mul] using exponential_budget hb hb1 (validation_exponents he he1 ha hb hb1).1
lemma noise_budget {ε α β:ℝ} (he:0<ε) (he1:ε≤1/2) (ha:0<α)
    (hb:0<β) (hb1:β<1/2) :
    (paramK β:ℝ)*Real.exp (-(paramS 64 ε α β:ℝ)*ε*(α/5)/paramK β)≤β/3 := by
  simpa only [neg_div,neg_mul] using exponential_budget hb hb1 (validation_exponents he he1 ha hb hb1).2
end ParityProof

-- ParityProof.ConditionalValidation
open MeasureTheory Set PrivLearn.Parity
namespace ParityProof
open scoped Classical
lemma conditional_validation {d:ℕ} {ε α β:ℝ} (he:0<ε) (he1:ε≤1/2) (ha:0<α)
    (hb:0<β) (hb1:β<1/2) (μ:PMF (Fin d→ZMod 2)) (r:Fin d→ZMod 2)
    (H:Fin (paramK β)→Option (Fin d→ZMod 2))
    (hgood:∃j h,H j=some h ∧ err μ r (some h)≤α/5) :
    ENNReal.ofReal (1-2*β/3) ≤ samplePr μ r
      (fun T:Fin (paramS 64 ε α β)→Example d=>testMechanism H T ε)
      {o|∃h,o=AstarOut.hyp h ∧ err μ r (some h)≤α} := by
  let k := paramK β
  let s := paramS 64 ε α β
  let a := α/5
  let E : Set (AstarOut d) := {o|∃h,o=AstarOut.hyp h ∧ err μ r (some h)≤α}
  let f : (Fin s→(Fin d→ZMod 2))→ℝ := fun x=>(testMechanism H (labeled r x) ε E).toReal
  let bad : (Fin s→(Fin d→ZMod 2))→Prop := fun x=>∃j,badCandidate μ r a (H j) x
  have hk : 0<k := paramK_pos hb hb1
  have hs : 0<s := paramS_pos he ha hb hb1
  have ha' : 0≤a := by dsimp [a]; positivity
  have hnoise : (k:ℝ)*Real.exp (-a/((k:ℝ)/(s*ε)))≤β/3 := by
    have h := noise_budget he he1 ha hb hb1
    have heq : -a/((k:ℝ)/(s*ε))= -(s:ℝ)*ε*(α/5)/k := by dsimp [a]; field_simp
    rw [heq]
    exact h
  have hf : ∀x,0≤f x := fun _=>ENNReal.toReal_nonneg
  have hpoint (x:Fin s→(Fin d→ZMod 2)) : 1-β/3-(if bad x then 1 else 0)≤f x := by
    by_cases hx:bad x
    · simp only [hx,ite_true]
      have := hf x
      linarith
    · simp only [hx,ite_false,sub_zero]
      have h := test_success_real hk hs he μ r ha' H x hgood hx
      have heq : 5*a=α := by dsimp [a]; ring
      rw [heq] at h
      change 1-(k:ℝ)*Real.exp (-a/((k:ℝ)/(s*ε)))≤f x at h
      linarith
  have hbad : (∑x:Fin s→(Fin d→ZMod 2),if bad x then validationWeight μ x else 0)≤β/3 :=
    (validation_bad_bound hs μ r ha' H).trans (validation_budget he he1 ha hb hb1)
  have havg := Finset.sum_le_sum (fun (x:Fin s→(Fin d→ZMod 2)) (_:x∈Finset.univ)=>
    mul_le_mul_of_nonneg_left (hpoint x) (show 0≤validationWeight μ x by unfold validationWeight; positivity))
  have hid : (∑x:Fin s→(Fin d→ZMod 2),validationWeight μ x*(1-β/3-(if bad x then 1 else 0)))=
      1-β/3-(∑x:Fin s→(Fin d→ZMod 2),if bad x then validationWeight μ x else 0) := by
    have hterm (x:Fin s→(Fin d→ZMod 2)) : validationWeight μ x*(1-β/3-(if bad x then 1 else 0))=
        validationWeight μ x*(1-β/3)-(if bad x then validationWeight μ x else 0) := by
      split_ifs <;> ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul]
    have hw : (∑x:Fin s→(Fin d→ZMod 2),validationWeight μ x)=1 := iid_real_sum μ s
    rw [hw,one_mul]
  rw [hid] at havg
  have hfinal : 1-2*β/3≤∑x:Fin s→(Fin d→ZMod 2),validationWeight μ x*f x := by linarith
  have heval : samplePr μ r (fun T:Fin s→Example d=>testMechanism H T ε) E=
      ENNReal.ofReal (∑x:Fin s→(Fin d→ZMod 2),validationWeight μ x*f x) := by
    apply samplePr_ofReal μ r _ E f hf
    intro x
    let := testMechanism_probability hk hs he H (labeled r x)
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [heval]
  exact ENNReal.ofReal_le_ofReal hfinal
end ParityProof

-- ParityProof.AmplifiedUtility
open MeasureTheory PrivLearn.Parity
namespace ParityProof
open scoped BigOperators Classical
lemma weighted_good_lower {I : Type*} [Fintype I] (w f : I → ENNReal) (G : I → Prop)
    (v : ENNReal) (hf : ∀ i,G i→v≤f i) :
    v*(∑ i,w i*(if G i then 1 else 0)) ≤ ∑ i,w i*f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : G i
  · simp only [if_pos hi,mul_one]
    simpa only [mul_comm] using mul_le_mul' (le_refl (w i)) (hf i hi)
  · simp [hi]
lemma algAstar_utility {d n : ℕ} (hd : 1≤d) {ε α β : ℝ}
    (he : 0<ε) (he1 : ε≤1/2) (ha : 0<α) (hb : 0<β) (hb1 : β<1/2)
    (hn : paramK β*paramN 64 d ε α+paramS 64 ε α β < n)
    (μ : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) :
    ENNReal.ofReal (1-β) ≤ samplePr μ r
      (fun z : Fin n → Example d => algAstar 64 64 d ε α β z)
      {o | ∃ h,o=AstarOut.hyp h ∧ err μ r (some h)≤α} := by
  let w := fun H : Fin (paramK β) → Option (Fin d → ZMod 2) =>
    ∏ j,candidateLaw μ r ε (paramN 64 d ε α) (H j)
  let G := fun H : Fin (paramK β) → Option (Fin d → ZMod 2) =>
    ∃ j h,H j=some h ∧ err μ r (some h)≤α/5
  let f := fun H : Fin (paramK β) → Option (Fin d → ZMod 2) =>
    samplePr μ r (fun T : Fin (paramS 64 ε α β) → Example d => testMechanism H T ε)
      {o | ∃ h,o=AstarOut.hyp h ∧ err μ r (some h)≤α}
  have hc : ENNReal.ofReal (1-β/3) ≤ ∑ H,w H*(@ite ENNReal (G H) (Classical.propDecidable (G H)) 1 0) := by
    convert candidate_amplification hd he he1 ha hb hb1 μ r using 1
    apply Finset.sum_congr rfl
    intro H _
    by_cases hG : G H <;> simp_all only [G,w,if_pos]
  have hv : ∀ H,G H→ENNReal.ofReal (1-2*β/3)≤f H := by
    intro H hH
    exact conditional_validation he he1 ha hb hb1 μ r H hH
  have hmix := weighted_good_lower w f G (ENNReal.ofReal (1-2*β/3)) hv
  have hprod := mul_le_mul' (le_refl (ENNReal.ofReal (1-2*β/3))) hc
  have hlow : ENNReal.ofReal (1-β) ≤ ENNReal.ofReal (1-2*β/3)*ENNReal.ofReal (1-β/3) := by
    rw [← ENNReal.ofReal_mul (by linarith : 0≤1-2*β/3)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg β]
  rw [amplified_sample_factorization hn]
  exact hlow.trans (hprod.trans hmix)
end ParityProof

-- ParityProof.Root
open MeasureTheory ProbabilityTheory PrivLearn.Parity
namespace ParityProof
theorem full_solution :
∃ c c' C : ℝ, 0 < c ∧ 0 < c' ∧ 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ ε α β : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algAstar c c' d ε α β z) ε) ∧
        (∀ (𝒳 : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) (n : ℕ),
          C * (d + Real.logb 2 (1 / β)) * Real.logb 2 (1 / β) / (ε * α) ≤ n →
          ENNReal.ofReal (1 - β) ≤
            samplePr 𝒳 r (fun z : Fin n → Example d => algAstar c c' d ε α β z)
              {o | ∃ r' : Fin d → ZMod 2, o = AstarOut.hyp r' ∧ err 𝒳 r (some r') ≤ α}) := by
  refine ⟨64,64,1000000,by norm_num,by norm_num,by norm_num,?_⟩
  intro d hd ε α β he he1 ha ha1 hb hb1
  constructor
  · intro n
    exact algAstar_dp he he1 ha hb hb1
  · intro μ r n hn
    exact algAstar_utility hd he he1 ha hb hb1
      (sample_threshold hd he he1 ha ha1 hb hb1 n hn) μ r
end ParityProof

open MeasureTheory ProbabilityTheory PrivLearn.Parity
theorem solution :
∃ c c' C : ℝ, 0 < c ∧ 0 < c' ∧ 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ ε α β : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algAstar c c' d ε α β z) ε) ∧
        (∀ (𝒳 : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) (n : ℕ),
          C * (d + Real.logb 2 (1 / β)) * Real.logb 2 (1 / β) / (ε * α) ≤ n →
          ENNReal.ofReal (1 - β) ≤
            samplePr 𝒳 r (fun z : Fin n → Example d => algAstar c c' d ε α β z)
              {o | ∃ r' : Fin d → ZMod 2, o = AstarOut.hyp r' ∧ err 𝒳 r (some r') ≤ α}) := ParityProof.full_solution
theorem PrivLearn.Parity.theorem_4_4 :
∃ c c' C : ℝ, 0 < c ∧ 0 < c' ∧ 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ ε α β : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algAstar c c' d ε α β z) ε) ∧
        (∀ (𝒳 : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) (n : ℕ),
          C * (d + Real.logb 2 (1 / β)) * Real.logb 2 (1 / β) / (ε * α) ≤ n →
          ENNReal.ofReal (1 - β) ≤
            samplePr 𝒳 r (fun z : Fin n → Example d => algAstar c c' d ε α β z)
              {o | ∃ r' : Fin d → ZMod 2, o = AstarOut.hyp r' ∧ err 𝒳 r (some r') ≤ α}) := ParityProof.full_solution
