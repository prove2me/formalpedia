-- Prove2me | solution 1 for UnderstandingML.vc_uniform_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T19:50:15.041324+00:00
-- url     : https://prove2.me/submissions/9096120f-8930-41a9-b000-3e689d296089

import Definitions.Def_UnderstandingML_FundamentalProof
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# §28.1: uniform deviation bound for classes of finite VC dimension

Proof by the classical VC route (not via Rademacher complexity): reduction to the error
indicators of a countable subclass, a ghost sample with Chebyshev's inequality, symmetrization
by random swaps with a Hoeffding bound (`cosh x ≤ exp (x²/2)`), Sauer's lemma, and the final
numerical inequality.
-/

open MeasureTheory Finset

namespace UnderstandingML.EpsNetAux

variable {X : Type*}

/-- Number of sample points hit by `h`. -/
def hits (h : X → Bool) {m : ℕ} (T : Fin m → X) : ℕ :=
  (univ.filter fun i ↦ h (T i) = true).card

/-- Swap the coordinates `i` with `σ i = true` between two samples. -/
def swapS {m : ℕ} (σ : Fin m → Bool) (S T : Fin m → X) : Fin m → X :=
  fun i ↦ if σ i then T i else S i

/-- The pattern of `h` on a double sample. -/
def pattern {m : ℕ} (S T : Fin m → X) (h : X → Bool) : Fin m → Bool × Bool :=
  fun i ↦ (h (S i), h (T i))

open Classical in
/-- A family of subsets of a finite set `C` that is shattered gives a set shattered by `H`. -/
lemma vcDim_family_le (H : Set (X → Bool)) (d : ℕ) (hd : vcDim H = d) (C : Finset X) :
    (univ.filter (fun s : Finset C ↦ ∃ h ∈ H, ∀ c : C, c ∈ s ↔ h c = true)).vcDim ≤ d := by
  classical
  unfold Finset.vcDim
  apply Finset.sup_le
  intro s hs
  rw [Finset.mem_shatterer] at hs
  -- `H` shatters the image of `s` in `X`
  have hshat : Shatters H (s.map (Function.Embedding.subtype _)) := by
    intro g
    set g' : C → Bool := fun c ↦
      if hc : c ∈ s then g ⟨c.val, Finset.mem_map_of_mem _ hc⟩ else false with hg'
    set t : Finset C := s.filter (fun c ↦ g' c = true) with ht
    obtain ⟨u, hu, hsu⟩ := hs (show t ⊆ s from Finset.filter_subset _ _)
    rw [Finset.mem_filter] at hu
    obtain ⟨h, hH, hhu⟩ := hu.2
    refine ⟨h, hH, fun c' ↦ ?_⟩
    obtain ⟨c'', hc''⟩ := c'
    have hc2 := hc''
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hc2
    obtain ⟨c, hcs, rfl⟩ := hc2
    have key : c ∈ s ∩ u ↔ c ∈ t := by rw [hsu]
    simp only [Finset.mem_inter, hcs, true_and, ht, Finset.mem_filter] at key
    rw [hhu c] at key
    have hgc : g' c = g ⟨c.val, hc''⟩ := by simp [hg', hcs]
    rw [hgc] at key
    show h c = g ⟨c.val, hc''⟩
    cases hc : h c <;> cases hg : g ⟨c.val, hc''⟩ <;> simp_all
  have hle : ((s.map (Function.Embedding.subtype _)).card : ℕ∞) ≤ vcDim H := by
    unfold vcDim
    exact le_iSup₂ (f := fun (C : Finset X) (_ : Shatters H C) ↦ (C.card : ℕ∞)) _ hshat
  rw [hd, Finset.card_map] at hle
  exact_mod_cast hle

/-- Sauer's lemma for the patterns on a double sample. -/
lemma sauer_patterns (H : Set (X → Bool)) (d : ℕ) (hd : vcDim H = d) {m : ℕ}
    (S T : Fin m → X) :
    (pattern S T '' H).ncard ≤ ∑ k ∈ range (d + 1), (2 * m).choose k := by
  classical
  set C : Finset X := Finset.image S univ ∪ Finset.image T univ with hC
  have hSC : ∀ i, S i ∈ C := fun i ↦ by simp [hC]
  have hTC : ∀ i, T i ∈ C := fun i ↦ by simp [hC]
  set 𝒜 : Finset (Finset C) :=
    univ.filter (fun s : Finset C ↦ ∃ h ∈ H, ∀ c : C, c ∈ s ↔ h c = true) with h𝒜
  set φ : Finset C → (Fin m → Bool × Bool) :=
    fun s i ↦ (decide (⟨S i, hSC i⟩ ∈ s), decide (⟨T i, hTC i⟩ ∈ s)) with hφ
  have hsub : pattern S T '' H ⊆ φ '' (𝒜 : Set (Finset C)) := by
    rintro _ ⟨h, hH, rfl⟩
    refine ⟨univ.filter (fun c : C ↦ h c = true), ?_, ?_⟩
    · simp only [h𝒜, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨h, hH, fun c ↦ by simp⟩
    · funext i
      simp [hφ, pattern]
  have hCcard : C.card ≤ 2 * m := by
    calc C.card ≤ (Finset.image S univ).card + (Finset.image T univ).card :=
          Finset.card_union_le _ _
      _ ≤ m + m := by
          gcongr
          · exact (Finset.card_image_le).trans (by simp)
          · exact (Finset.card_image_le).trans (by simp)
      _ = 2 * m := by ring
  calc (pattern S T '' H).ncard ≤ (φ '' (𝒜 : Set (Finset C))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (𝒜 : Set (Finset C)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 𝒜.card := Set.ncard_coe_finset _
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Iic 𝒜.vcDim, (Fintype.card C).choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ range (d + 1), (Fintype.card C).choose k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          have := vcDim_family_le H d hd C
          simp only [Finset.mem_Iic] at hk
          simp only [Finset.mem_range]
          rw [← h𝒜] at this
          omega
        · intros; exact Nat.zero_le _
    _ ≤ ∑ k ∈ range (d + 1), (2 * m).choose k := by
        apply Finset.sum_le_sum
        intro k _
        apply Nat.choose_le_choose
        rw [Fintype.card_coe]
        exact hCcard

lemma hits_le (h : X → Bool) {m : ℕ} (T : Fin m → X) : hits h T ≤ m := by
  unfold hits
  exact (Finset.card_filter_le _ _).trans (by simp)

variable [MeasurableSpace X]

lemma measurable_hits {m : ℕ} (h : X → Bool) (hh : Measurable h) :
    Measurable (fun T : Fin m → X ↦ hits h T) := by
  have h1 : Measurable (fun T : Fin m → X ↦ fun i ↦ h (T i)) := by
    rw [measurable_pi_iff]; intro i; exact hh.comp (measurable_pi_apply i)
  have h2 : Measurable (fun b : Fin m → Bool ↦ (univ.filter fun i ↦ b i = true).card) :=
    measurable_of_countable _
  exact h2.comp h1

lemma measurable_pattern {m : ℕ} (h : X → Bool) (hh : Measurable h) :
    Measurable (fun p : (Fin m → X) × (Fin m → X) ↦ pattern p.1 p.2 h) := by
  unfold pattern
  rw [measurable_pi_iff]
  intro i
  exact (hh.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
    (hh.comp ((measurable_pi_apply i).comp measurable_snd))

lemma measurableSet_bad (H₀ : Set (X → Bool)) (hH₀c : H₀.Countable)
    (hH₀m : ∀ h ∈ H₀, Measurable h) {m : ℕ} (k : ℕ) :
    MeasurableSet {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ H₀, (∀ i, h (p.1 i) = false) ∧
      k ≤ hits h p.2} := by
  have : {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ H₀, (∀ i, h (p.1 i) = false) ∧
      k ≤ hits h p.2} = ⋃ h ∈ H₀, (fun p : (Fin m → X) × (Fin m → X) ↦ pattern p.1 p.2 h) ⁻¹'
        {q | (∀ i, (q i).1 = false) ∧ k ≤ (univ.filter fun i ↦ (q i).2 = true).card} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, exists_prop]
    rfl
  rw [this]
  exact MeasurableSet.biUnion hH₀c fun h hh ↦
    measurable_pattern h (hH₀m h hh) MeasurableSet.of_discrete

lemma swap_measurePreserving (D : Measure X) [IsProbabilityMeasure D] {m : ℕ}
    (σ : Fin m → Bool) :
    MeasurePreserving (fun p : (Fin m → X) × (Fin m → X) ↦ (swapS σ p.1 p.2, swapS σ p.2 p.1))
      ((iidLaw D m).prod (iidLaw D m)) ((iidLaw D m).prod (iidLaw D m)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m) with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : Fin m ↦ D.prod D)
      ((iidLaw D m).prod (iidLaw D m)) :=
    measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ ↦ D) (fun _ ↦ D)
  have hΦ : MeasurePreserving
      (fun (f : Fin m → X × X) i ↦ (if σ i then Prod.swap else id) (f i))
      (Measure.pi fun _ : Fin m ↦ D.prod D) (Measure.pi fun _ : Fin m ↦ D.prod D) := by
    apply measurePreserving_pi
    intro i
    by_cases hσ : σ i = true
    · simp only [hσ, if_true]
      exact Measure.measurePreserving_swap
    · simp only [hσ, Bool.false_eq_true, if_false]
      exact MeasurePreserving.id _
  have hcomp := he_mp.comp (hΦ.comp (MeasurePreserving.symm e he_mp))
  convert hcomp using 1
  funext p
  simp only [Function.comp_apply, he]
  ext i <;> by_cases hσ : σ i = true <;>
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow, swapS, hσ]

end UnderstandingML.EpsNetAux

namespace UnderstandingML.EpsNetArith

lemma sum_choose_le (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) :
    ((∑ k ∈ Finset.range (d + 1), n.choose k : ℕ) : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
  have hn : 0 < n := lt_of_lt_of_le hd hdn
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := (d : ℝ) / n with hx
  have hx0 : 0 < x := div_pos hdpos hnpos
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hnpos]; exact_mod_cast hdn
  have key : ((∑ k ∈ Finset.range (d + 1), n.choose k : ℕ) : ℝ) * x ^ d ≤ Real.exp d := by
    push_cast
    rw [Finset.sum_mul]
    calc ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * x ^ d
        ≤ ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * x ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0.le hx1 hk') (by positivity)
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_subset_range.mpr (by omega)
          · intro k _ _; positivity
      _ = (x + 1) ^ n := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro k _
          simp [mul_comm]
      _ ≤ (Real.exp x) ^ n := by
          gcongr
          linarith [Real.add_one_le_exp x]
      _ = Real.exp d := by
          rw [← Real.exp_nat_mul, hx]
          congr 1
          field_simp
  have hxd : 0 < x ^ d := pow_pos hx0 d
  have : ((∑ k ∈ Finset.range (d + 1), n.choose k : ℕ) : ℝ) ≤ Real.exp d / x ^ d := by
    rw [le_div_iff₀ hxd]; exact key
  refine this.trans (le_of_eq ?_)
  rw [show (Real.exp 1 * n / d) ^ d = Real.exp d * n ^ d / d ^ d by
    rw [div_pow, mul_pow, ← Real.exp_nat_mul, mul_one], hx, div_pow]
  field_simp

end UnderstandingML.EpsNetArith

namespace UnderstandingML.VCAux

open UnderstandingML UnderstandingML.EpsNetAux

variable {Z : Type*}

/-- The signed sum `∑ᵢ ±cᵢ` given by a swap pattern. -/
noncomputable def sgnSum {m : ℕ} (σ : Fin m → Bool) (c : Fin m → ℝ) : ℝ :=
  ∑ i, if σ i then -c i else c i

lemma exp_moment {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, |c i| ≤ 1) (l : ℝ) :
    ∑ σ : Fin m → Bool, Real.exp (l * sgnSum σ c) ≤ 2 ^ m * Real.exp (l ^ 2 * m / 2) := by
  classical
  have e1 : ∀ σ : Fin m → Bool, Real.exp (l * sgnSum σ c) =
      ∏ i, Real.exp (if σ i then -(l * c i) else l * c i) := by
    intro σ
    rw [sgnSum, mul_sum, Real.exp_sum]
    refine prod_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring_nf
  simp_rw [e1]
  rw [show (∑ x : Fin m → Bool, ∏ i, Real.exp (if x i = true then -(l * c i) else l * c i)) =
      ∏ i, ∑ b : Bool, Real.exp (if b = true then -(l * c i) else l * c i) from
    (Fintype.prod_sum (fun i (b : Bool) ↦ Real.exp (if b = true then -(l * c i) else l * c i))).symm]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  calc ∏ i, (Real.exp (-(l * c i)) + Real.exp (l * c i))
      = ∏ i, (2 * Real.cosh (l * c i)) := by
        refine prod_congr rfl fun i _ ↦ ?_
        rw [Real.cosh_eq]; ring
    _ ≤ ∏ _i : Fin m, (2 * Real.exp (l ^ 2 / 2)) := by
        apply Finset.prod_le_prod (fun i _ ↦ by positivity)
        intro i _
        have h1 := Real.cosh_le_exp_half_sq (l * c i)
        have hc2 : c i ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (hc i)
        have h2 : (l * c i) ^ 2 / 2 ≤ l ^ 2 / 2 := by
          rw [mul_pow]; nlinarith [sq_nonneg l]
        have h3 := Real.exp_le_exp.mpr h2
        linarith
    _ = 2 ^ m * Real.exp (l ^ 2 * m / 2) := by
        rw [prod_const, card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
        ring_nf

lemma tail_one {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, |c i| ≤ 1) (t : ℝ)
    (ht : 0 < t) :
    ((univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ c)).card : ℝ) ≤
      2 ^ m * Real.exp (-(t ^ 2 / (2 * m))) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set l := t / m with hl
  have hl0 : 0 ≤ l := by positivity
  calc ((univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ c)).card : ℝ)
      = ∑ σ ∈ univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ c), (1 : ℝ) := by simp
    _ ≤ ∑ σ ∈ univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ c),
          Real.exp (l * sgnSum σ c - l * t) := by
        refine sum_le_sum fun σ hσ ↦ ?_
        simp only [mem_filter, mem_univ, true_and] at hσ
        apply Real.one_le_exp
        nlinarith
    _ ≤ ∑ σ : Fin m → Bool, Real.exp (l * sgnSum σ c - l * t) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ (Real.exp_pos _).le)
    _ = Real.exp (-(l * t)) * ∑ σ : Fin m → Bool, Real.exp (l * sgnSum σ c) := by
        rw [mul_sum]
        refine sum_congr rfl fun σ _ ↦ ?_
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(l * t)) * (2 ^ m * Real.exp (l ^ 2 * m / 2)) :=
        mul_le_mul_of_nonneg_left (exp_moment c hc l) (Real.exp_pos _).le
    _ = 2 ^ m * Real.exp (-(t ^ 2 / (2 * m))) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        rw [hl]; field_simp; ring

lemma tail_two {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, |c i| ≤ 1) (t : ℝ)
    (ht : 0 < t) :
    ((univ.filter (fun σ : Fin m → Bool ↦ t < |sgnSum σ c|)).card : ℝ) ≤
      2 * (2 ^ m * Real.exp (-(t ^ 2 / (2 * m)))) := by
  classical
  have hneg : ∀ σ, sgnSum σ (fun i ↦ -c i) = -sgnSum σ c := by
    intro σ; unfold sgnSum; rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_; split_ifs <;> ring
  have hsub : univ.filter (fun σ : Fin m → Bool ↦ t < |sgnSum σ c|) ⊆
      univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ c) ∪
        univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ (fun i ↦ -c i)) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and, mem_union, hneg] at hσ ⊢
    rcases lt_abs.mp hσ with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h1 := tail_one hm c hc t ht
  have h2 := tail_one hm (fun i ↦ -c i) (fun i ↦ by rw [abs_neg]; exact hc i) t ht
  calc ((univ.filter (fun σ : Fin m → Bool ↦ t < |sgnSum σ c|)).card : ℝ)
      ≤ ((univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ c) ∪
          univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ (fun i ↦ -c i))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ((univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ c)).card : ℝ) +
        ((univ.filter (fun σ : Fin m → Bool ↦ t < sgnSum σ (fun i ↦ -c i))).card : ℝ) := by
        exact_mod_cast card_union_le _ _
    _ ≤ _ := by linarith

/-- The difference vector of a pattern on a double sample. -/
noncomputable def cvec {m : ℕ} (p : Fin m → Bool × Bool) : Fin m → ℝ :=
  fun i ↦ (if (p i).1 then 1 else 0) - (if (p i).2 then 1 else 0)

lemma abs_cvec_le {m : ℕ} (p : Fin m → Bool × Bool) (i : Fin m) : |cvec p i| ≤ 1 := by
  unfold cvec; cases (p i).1 <;> cases (p i).2 <;> norm_num

lemma hits_diff (g : Z → Bool) {m : ℕ} (σ : Fin m → Bool) (S T : Fin m → Z) :
    (hits g (swapS σ S T) : ℝ) - hits g (swapS σ T S) = sgnSum σ (cvec (pattern S T g)) := by
  classical
  unfold hits sgnSum
  rw [natCast_card_filter, natCast_card_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [swapS, cvec, pattern]
  by_cases hσ : σ i = true <;> by_cases h1 : g (S i) = true <;> by_cases h2 : g (T i) = true <;>
    simp [hσ, h1, h2]

open Classical in
lemma count_swaps_dev (G : Set (Z → Bool)) {m : ℕ} (hm : 0 < m) (S T : Fin m → Z) (t : ℝ)
    (ht : 0 < t) :
    ((univ.filter fun σ : Fin m → Bool ↦ ∃ g ∈ G,
        t < |(hits g (swapS σ S T) : ℝ) - hits g (swapS σ T S)|).card : ℝ) ≤
      (pattern S T '' G).ncard * (2 * (2 ^ m * Real.exp (-(t ^ 2 / (2 * m))))) := by
  set P := (Set.toFinite (pattern S T '' G)).toFinset with hP
  have hPcard : P.card = (pattern S T '' G).ncard := (Set.ncard_eq_toFinset_card _ _).symm
  rw [← hPcard]
  have hsub : (univ.filter fun σ : Fin m → Bool ↦ ∃ g ∈ G,
        t < |(hits g (swapS σ S T) : ℝ) - hits g (swapS σ T S)|) ⊆
      P.biUnion fun p ↦ univ.filter fun σ : Fin m → Bool ↦ t < |sgnSum σ (cvec p)| := by
    intro σ hσ
    rw [mem_filter] at hσ
    obtain ⟨g, hg, hlt⟩ := hσ.2
    rw [mem_biUnion]
    refine ⟨pattern S T g, ?_, ?_⟩
    · rw [hP, Set.Finite.mem_toFinset]; exact ⟨g, hg, rfl⟩
    · rw [mem_filter, ← hits_diff]; exact ⟨mem_univ _, hlt⟩
  calc _ ≤ (((P.biUnion fun p ↦ univ.filter fun σ : Fin m → Bool ↦
          t < |sgnSum σ (cvec p)|).card : ℕ) : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ((∑ p ∈ P, (univ.filter fun σ : Fin m → Bool ↦ t < |sgnSum σ (cvec p)|).card : ℕ) : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ = ∑ p ∈ P, ((univ.filter fun σ : Fin m → Bool ↦ t < |sgnSum σ (cvec p)|).card : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ _p ∈ P, 2 * (2 ^ m * Real.exp (-(t ^ 2 / (2 * m)))) :=
        sum_le_sum fun p _ ↦ tail_two hm (cvec p) (abs_cvec_le p) t ht
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end UnderstandingML.VCAux

namespace UnderstandingML.VCAux

open UnderstandingML UnderstandingML.EpsNetAux

variable {Z : Type*} [MeasurableSpace Z]

lemma measurable_hits_real {m : ℕ} (g : Z → Bool) (hg : Measurable g) :
    Measurable (fun T : Fin m → Z ↦ (hits g T : ℝ)) :=
  (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_hits g hg)

lemma measurableSet_dev (G : Set (Z → Bool)) (hGc : G.Countable)
    (hGm : ∀ g ∈ G, Measurable g) {m : ℕ} (t : ℝ) :
    MeasurableSet {p : (Fin m → Z) × (Fin m → Z) | ∃ g ∈ G,
      t < |(hits g p.1 : ℝ) - hits g p.2|} := by
  have : {p : (Fin m → Z) × (Fin m → Z) | ∃ g ∈ G, t < |(hits g p.1 : ℝ) - hits g p.2|} =
      ⋃ g ∈ G, {p : (Fin m → Z) × (Fin m → Z) | t < |(hits g p.1 : ℝ) - hits g p.2|} := by
    ext p; simp
  rw [this]
  refine MeasurableSet.biUnion hGc fun g hg ↦ ?_
  exact measurableSet_lt measurable_const (continuous_abs.measurable.comp
    (((measurable_hits_real g (hGm g hg)).comp measurable_fst).sub
      ((measurable_hits_real g (hGm g hg)).comp measurable_snd)))

/-- Symmetrization by random swaps, with Hoeffding's bound for each pattern. -/
lemma symm_swap (D : Measure Z) [IsProbabilityMeasure D] (G : Set (Z → Bool))
    (hGc : G.Countable) (hGm : ∀ g ∈ G, Measurable g) {m : ℕ} (hm : 0 < m) (t : ℝ)
    (ht : 0 < t) (N : ℕ) (hN : ∀ S T : Fin m → Z, (pattern S T '' G).ncard ≤ N) :
    ((iidLaw D m).prod (iidLaw D m))
        {p | ∃ g ∈ G, t < |(hits g p.1 : ℝ) - hits g p.2|} ≤
      ENNReal.ofReal (N * (2 * Real.exp (-(t ^ 2 / (2 * m))))) := by
  classical
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  set PP := (iidLaw D m).prod (iidLaw D m) with hPP
  have : IsProbabilityMeasure PP := by rw [hPP]; infer_instance
  set B := {p : (Fin m → Z) × (Fin m → Z) | ∃ g ∈ G, t < |(hits g p.1 : ℝ) - hits g p.2|}
    with hB
  have hBmeas : MeasurableSet B := measurableSet_dev G hGc hGm t
  set τ : (Fin m → Bool) → (Fin m → Z) × (Fin m → Z) → (Fin m → Z) × (Fin m → Z) :=
    fun σ p ↦ (swapS σ p.1 p.2, swapS σ p.2 p.1) with hτ
  have hτmeas : ∀ σ, MeasurableSet (τ σ ⁻¹' B) := fun σ ↦
    (swap_measurePreserving D σ).measurable hBmeas
  have hsum : (2 ^ m : ENNReal) * PP B = ∫⁻ p, ∑ σ : Fin m → Bool,
      (τ σ ⁻¹' B).indicator (1 : (Fin m → Z) × (Fin m → Z) → ENNReal) p ∂PP := by
    rw [lintegral_finset_sum _ (fun σ _ ↦ (measurable_one.indicator (hτmeas σ)))]
    simp_rw [lintegral_indicator_one (hτmeas _)]
    have : ∀ σ, PP (τ σ ⁻¹' B) = PP B := fun σ ↦
      (swap_measurePreserving D σ).measure_preimage hBmeas.nullMeasurableSet
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul]
    norm_cast
  set bnd : ℝ := N * (2 * Real.exp (-(t ^ 2 / (2 * m)))) with hbnd
  have hbnd0 : 0 ≤ bnd := by positivity
  have hpt : ∀ p, ∑ σ : Fin m → Bool,
      (τ σ ⁻¹' B).indicator (1 : (Fin m → Z) × (Fin m → Z) → ENNReal) p ≤
        (2 ^ m : ENNReal) * ENNReal.ofReal bnd := by
    intro p
    have e : ∑ σ : Fin m → Bool,
        (τ σ ⁻¹' B).indicator (1 : (Fin m → Z) × (Fin m → Z) → ENNReal) p =
        ((univ.filter fun σ : Fin m → Bool ↦ ∃ g ∈ G,
          t < |(hits g (swapS σ p.1 p.2) : ℝ) - hits g (swapS σ p.2 p.1)|).card : ENNReal) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro σ _
      simp [Set.indicator, hτ, hB]
    rw [e]
    have hc := count_swaps_dev G hm p.1 p.2 t ht
    have hc2 : ((univ.filter fun σ : Fin m → Bool ↦ ∃ g ∈ G,
          t < |(hits g (swapS σ p.1 p.2) : ℝ) - hits g (swapS σ p.2 p.1)|).card : ℝ) ≤
        2 ^ m * bnd := by
      refine hc.trans ?_
      have hNp : ((pattern p.1 p.2 '' G).ncard : ℝ) ≤ N := by exact_mod_cast hN p.1 p.2
      rw [hbnd]
      have : 0 ≤ 2 * (2 ^ m * Real.exp (-(t ^ 2 / (2 * m)))) := by positivity
      nlinarith
    rw [← ENNReal.ofReal_natCast]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal (2 ^ m * bnd) := ENNReal.ofReal_le_ofReal hc2
      _ = (2 ^ m : ENNReal) * ENNReal.ofReal bnd := by
          rw [ENNReal.ofReal_mul (by positivity)]; simp [ENNReal.ofReal_pow]
  have hle : (2 ^ m : ENNReal) * PP B ≤ (2 ^ m : ENNReal) * ENNReal.ofReal bnd := by
    rw [hsum]
    calc ∫⁻ p, ∑ σ : Fin m → Bool,
          (τ σ ⁻¹' B).indicator (1 : (Fin m → Z) × (Fin m → Z) → ENNReal) p ∂PP
        ≤ ∫⁻ _p, (2 ^ m : ENNReal) * ENNReal.ofReal bnd ∂PP := lintegral_mono hpt
      _ = (2 ^ m : ENNReal) * ENNReal.ofReal bnd := by
          rw [lintegral_const, measure_univ, mul_one]
  exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).mp hle

/-- Integral of a function of a Boolean feature. -/
lemma integral_ite_bool (D : Measure Z) [IsProbabilityMeasure D] (g : Z → Bool)
    (hg : Measurable g) (a b : ℝ) :
    ∫ z, (if g z = true then a else b) ∂D =
      a * D.real {z | g z = true} + b * (1 - D.real {z | g z = true}) := by
  have hs : MeasurableSet {z | g z = true} := hg (measurableSet_singleton true)
  have : (fun z ↦ if g z = true then a else b) =
      fun z ↦ b + (a - b) * ({z | g z = true}.indicator 1 z) := by
    funext z
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> ring
  rw [this, integral_add (integrable_const _) ((integrable_const _).indicator hs |>.const_mul _),
    integral_const_mul, integral_indicator_one hs]
  simp
  ring

/-- Second moment of the number of hits. -/
lemma second_moment (D : Measure Z) [IsProbabilityMeasure D] (g : Z → Bool) (hg : Measurable g)
    (m : ℕ) :
    ∫ T, ((hits g T : ℝ) - m * D.real {z | g z = true}) ^ 2 ∂(iidLaw D m) ≤ m / 4 := by
  classical
  set q := D.real {z | g z = true} with hq
  set u : Z → ℝ := fun z ↦ if g z = true then 1 - q else -q with hu
  have hum : Measurable u := by
    apply Measurable.ite (hg (measurableSet_singleton true)) measurable_const measurable_const
  have hub : ∀ z, |u z| ≤ 1 := by
    have hq0 : 0 ≤ q := measureReal_nonneg
    have hq1 : q ≤ 1 := measureReal_le_one
    intro z; simp only [hu]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hsum : ∀ T : Fin m → Z, (hits g T : ℝ) - m * q = ∑ i, u (T i) := by
    intro T
    unfold hits
    rw [natCast_card_filter]
    have : ∀ i, u (T i) = (if g (T i) = true then (1 : ℝ) else 0) - q := by
      intro i; simp only [hu]; split_ifs <;> ring
    simp_rw [this, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hint : ∀ i j : Fin m, ∫ T, u (T i) * u (T j) ∂(iidLaw D m) =
      if i = j then ∫ z, u z * u z ∂D else 0 := by
    intro i j
    have e : ∀ T : Fin m → Z, u (T i) * u (T j) =
        ∏ k, ((if k = i then u (T k) else 1) * (if k = j then u (T k) else 1)) := by
      intro T
      rw [prod_mul_distrib, prod_ite_eq', prod_ite_eq']
      simp
    simp_rw [e]
    rw [iidLaw, integral_fintype_prod_eq_prod (𝕜 := ℝ)
      (fun k z ↦ (if k = i then u z else 1) * (if k = j then u z else 1))]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, prod_eq_single i]
      · simp
      · intro k _ hk; simp [hk]
      · simp
    · rw [if_neg hij]
      apply prod_eq_zero (mem_univ i)
      show ∫ z, (if i = i then u z else 1) * (if i = j then u z else 1) ∂D = 0
      simp only [if_true, if_neg hij, mul_one, hu]
      rw [integral_ite_bool D g hg]; ring
  have huu : ∫ z, u z * u z ∂D ≤ 1 / 4 := by
    have : (fun z ↦ u z * u z) = fun z ↦ if g z = true then (1 - q) * (1 - q) else q * q := by
      funext z; simp only [hu]; split_ifs <;> ring
    rw [this, integral_ite_bool D g hg]
    nlinarith [sq_nonneg (q - 1 / 2)]
  have hInt : ∀ i j : Fin m, Integrable (fun T : Fin m → Z ↦ u (T i) * u (T j)) (iidLaw D m) := by
    intro i j
    have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
    refine Integrable.of_bound ((hum.comp (measurable_pi_apply i)).mul
      (hum.comp (measurable_pi_apply j))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun T ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hub (T i), hub (T j), abs_nonneg (u (T i)), abs_nonneg (u (T j))]
  simp_rw [hsum, sq, sum_mul_sum]
  rw [integral_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦ hInt i j))]
  simp_rw [integral_finset_sum _ (fun j _ ↦ hInt _ j), hint]
  simp only [sum_ite_eq, mem_univ, if_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- Chebyshev's inequality for the number of hits. -/
lemma cheb (D : Measure Z) [IsProbabilityMeasure D] (g : Z → Bool) (hg : Measurable g)
    (m : ℕ) (t : ℝ) (ht : 0 < t) :
    iidLaw D m {T | t ≤ |(hits g T : ℝ) - m * D.real {z | g z = true}|} ≤
      ENNReal.ofReal (m / (4 * t ^ 2)) := by
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  set f : (Fin m → Z) → ℝ := fun T ↦ ((hits g T : ℝ) - m * D.real {z | g z = true}) ^ 2 with hf
  have hfm : Measurable f :=
    ((measurable_hits_real g hg).sub measurable_const).pow_const 2
  have hfb : ∀ T, |f T| ≤ (m + m) ^ 2 := by
    intro T
    have h1 : (hits g T : ℝ) ≤ m := by exact_mod_cast hits_le g T
    have h2 : (0 : ℝ) ≤ hits g T := Nat.cast_nonneg _
    have hq0 : 0 ≤ D.real {z | g z = true} := measureReal_nonneg
    have hq1 : D.real {z | g z = true} ≤ 1 := measureReal_le_one
    rw [abs_of_nonneg (sq_nonneg _)]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : |(hits g T : ℝ) - m * D.real {z | g z = true}| ≤ m + m := by
      rw [abs_le]; constructor <;> nlinarith
    calc f T = |(hits g T : ℝ) - m * D.real {z | g z = true}| ^ 2 := by rw [hf, sq_abs]
      _ ≤ (m + m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hfi : Integrable f (iidLaw D m) :=
    Integrable.of_bound hfm.aestronglyMeasurable ((m + m) ^ 2)
      (Filter.Eventually.of_forall fun T ↦ by rw [Real.norm_eq_abs]; exact hfb T)
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun T ↦ sq_nonneg _) hfi (t ^ 2)
  have hsm := second_moment D g hg m
  have hset : {T | t ≤ |(hits g T : ℝ) - m * D.real {z | g z = true}|} = {T | t ^ 2 ≤ f T} := by
    ext T
    simp only [Set.mem_setOf_eq, hf]
    rw [← sq_abs ((hits g T : ℝ) - _), sq_le_sq₀ ht.le (abs_nonneg _)]
  rw [hset]
  have hreal : (iidLaw D m).real {T | t ^ 2 ≤ f T} ≤ m / (4 * t ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc iidLaw D m {T | t ^ 2 ≤ f T} = ENNReal.ofReal ((iidLaw D m).real {T | t ^ 2 ≤ f T}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The ghost-sample step. -/
lemma symm_ghost (D : Measure Z) [IsProbabilityMeasure D] (G : Set (Z → Bool))
    (hGc : G.Countable) (hGm : ∀ g ∈ G, Measurable g) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hmε : 2 ≤ m * ε ^ 2) :
    iidLaw D m {S | ∃ g ∈ G, ε * m < |(m : ℝ) * D.real {z | g z = true} - hits g S|} ≤
      2 * ((iidLaw D m).prod (iidLaw D m))
        {p | ∃ g ∈ G, ε * m / 2 < |(hits g p.1 : ℝ) - hits g p.2|} := by
  have hP : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  set P := iidLaw D m with hPdef
  have hm : (0 : ℝ) < m := by
    by_contra h; push_neg at h
    have : (m : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg m)
    rw [this] at hmε; linarith
  set A := {S : Fin m → Z | ∃ g ∈ G, ε * m < |(m : ℝ) * D.real {z | g z = true} - hits g S|}
    with hA
  set B := {p : (Fin m → Z) × (Fin m → Z) | ∃ g ∈ G, ε * m / 2 < |(hits g p.1 : ℝ) - hits g p.2|}
    with hB
  have hBmeas : MeasurableSet B := measurableSet_dev G hGc hGm _
  have hAmeas : MeasurableSet A := by
    have : A = ⋃ g ∈ G, {S : Fin m → Z | ε * m < |(m : ℝ) * D.real {z | g z = true} - hits g S|} := by
      ext S; simp [hA]
    rw [this]
    exact MeasurableSet.biUnion hGc fun g hg ↦ measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (measurable_const.sub (measurable_hits_real g (hGm g hg))))
  have hsec : ∀ S ∈ A, (1 / 2 : ENNReal) ≤ P (Prod.mk S ⁻¹' B) := by
    intro S hS
    obtain ⟨g, hg, hgS⟩ := hS
    set E := {T : Fin m → Z | ε * m / 2 ≤ |(hits g T : ℝ) - m * D.real {z | g z = true}|} with hE
    have hEmeas : MeasurableSet E := measurableSet_le measurable_const
      (continuous_abs.measurable.comp ((measurable_hits_real g (hGm g hg)).sub measurable_const))
    have hEle : P E ≤ 1 / 2 := by
      refine (cheb D g (hGm g hg) m (ε * m / 2) (by positivity)).trans ?_
      have : (m : ℝ) / (4 * (ε * m / 2) ^ 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : (m : ℝ) * (m * ε ^ 2) ≥ m * 2 := by nlinarith
        nlinarith
      refine (ENNReal.ofReal_le_ofReal this).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    have hsub : Eᶜ ⊆ Prod.mk S ⁻¹' B := by
      intro T hT
      simp only [hE, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hT
      simp only [Set.mem_preimage, hB, Set.mem_setOf_eq]
      refine ⟨g, hg, ?_⟩
      set a := (m : ℝ) * D.real {z | g z = true} - hits g S with ha
      set b := (hits g T : ℝ) - m * D.real {z | g z = true} with hb
      have h4 : |(hits g S : ℝ) - hits g T| = |a + b| := by
        rw [← abs_neg]; congr 1; rw [ha, hb]; ring
      have h6 : |a| ≤ |a + b| + |b| := by
        have := abs_add_le (a + b) (-b)
        rwa [abs_neg, add_neg_cancel_right] at this
      rw [h4]
      linarith
    calc (1 / 2 : ENNReal) ≤ P Eᶜ := by
          rw [prob_compl_eq_one_sub hEmeas]
          calc (1 / 2 : ENNReal) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
            _ ≤ 1 - P E := tsub_le_tsub_left hEle 1
      _ ≤ P (Prod.mk S ⁻¹' B) := measure_mono hsub
  rw [Measure.prod_apply hBmeas]
  have : (1 / 2 : ENNReal) * P A ≤ ∫⁻ S, P (Prod.mk S ⁻¹' B) ∂P := by
    rw [← lintegral_indicator_const hAmeas]
    apply lintegral_mono
    intro S
    by_cases hS : S ∈ A
    · rw [Set.indicator_of_mem hS]; exact hsec S hS
    · rw [Set.indicator_of_notMem hS]; exact bot_le
  calc P A = 2 * ((1 / 2 : ENNReal) * P A) := by
        rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * ∫⁻ S, P (Prod.mk S ⁻¹' B) ∂P := by gcongr

end UnderstandingML.VCAux

namespace UnderstandingML.VCAux

open UnderstandingML UnderstandingML.EpsNetAux UnderstandingML.EpsNetArith Filter

variable {X : Type*}

/-- The error indicator of `h`: `true` iff `h` misclassifies `(x, y)`. -/
def errFn (h : X → Bool) : X × Bool → Bool := fun z ↦ h z.1 != z.2

lemma loss01_eq (h : X → Bool) (z : X × Bool) :
    loss01 h z = if errFn h z = true then 1 else 0 := by
  unfold loss01 errFn
  cases h z.1 <;> cases z.2 <;> simp

lemma empRisk_eq (h : X → Bool) {m : ℕ} (S : Fin m → X × Bool) :
    empRisk loss01 S h = hits (errFn h) S / m := by
  classical
  unfold empRisk hits
  rw [natCast_card_filter]
  congr 1
  exact sum_congr rfl fun i _ ↦ loss01_eq h (S i)

variable [MeasurableSpace X]

lemma measurable_errFn {h : X → Bool} (hh : Measurable h) : Measurable (errFn h) := by
  have h1 : Measurable (fun p : Bool × Bool ↦ p.1 != p.2) := measurable_of_countable _
  exact h1.comp ((hh.comp measurable_fst).prodMk measurable_snd)

lemma measurable_loss01 {h : X → Bool} (hh : Measurable h) :
    Measurable (fun z : X × Bool ↦ loss01 h z) := by
  have : (fun z : X × Bool ↦ loss01 h z) = fun z ↦ if errFn h z = true then (1 : ℝ) else 0 := by
    funext z; exact loss01_eq h z
  rw [this]
  exact Measurable.ite ((measurable_errFn hh) (measurableSet_singleton true)) measurable_const
    measurable_const

lemma risk_eq_real (D : Measure (X × Bool)) [IsProbabilityMeasure D] {h : X → Bool}
    (hh : Measurable h) : risk loss01 D h = D.real {z | errFn h z = true} := by
  unfold risk
  simp_rw [loss01_eq]
  rw [integral_ite_bool D (errFn h) (measurable_errFn hh)]
  ring

/-- Reduction from `H` to the error indicators of the countable subclass `H₀`. -/
lemma reduce (D : Measure (X × Bool)) [IsProbabilityMeasure D] (H H₀ : Set (X → Bool))
    (hH₀m : ∀ h ∈ H₀, Measurable h)
    (happrox : ∀ h ∈ H, ∃ u : ℕ → (X → Bool), (∀ n, u n ∈ H₀) ∧
      ∀ x, ∃ N, ∀ n, N ≤ n → u n x = h x)
    (ε : ℝ) {m : ℕ} (hm : 0 < m) :
    {S : Fin m → X × Bool | ∃ h ∈ H, ε < |risk loss01 D h - empRisk loss01 S h|} ⊆
      {S | ∃ g ∈ errFn '' H₀, ε * m < |(m : ℝ) * D.real {z | g z = true} - hits g S|} := by
  intro S hS
  obtain ⟨h, hH, hlt⟩ := hS
  obtain ⟨u, huH₀, hconv⟩ := happrox h hH
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrisk : Tendsto (fun n ↦ risk loss01 D (u n)) atTop (nhds (risk loss01 D h)) := by
    unfold risk
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro n; exact (measurable_loss01 (hH₀m _ (huH₀ n))).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall fun z ↦ by unfold loss01; split_ifs <;> simp
    · refine Eventually.of_forall fun z ↦ ?_
      obtain ⟨N, hN⟩ := hconv z.1
      apply tendsto_const_nhds.congr'
      rw [EventuallyEq, eventually_atTop]
      exact ⟨N, fun n hn ↦ by unfold loss01; rw [hN n hn]⟩
  have hsample : ∀ i, ∃ N, ∀ n, N ≤ n → u n (S i).1 = h (S i).1 := fun i ↦ hconv (S i).1
  choose Ni hNi using hsample
  set N0 := univ.sup Ni with hN0
  have hemp : ∀ n, N0 ≤ n → empRisk loss01 S (u n) = empRisk loss01 S h := by
    intro n hn
    unfold empRisk
    congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    unfold loss01
    rw [hNi i n ((le_sup (mem_univ i)).trans hn)]
  have hev : ∀ᶠ n in atTop, ε < |risk loss01 D (u n) - empRisk loss01 S h| :=
    ((continuous_abs.tendsto _).comp (hrisk.sub_const _)).eventually (lt_mem_nhds hlt)
  obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_ge_atTop N0)).exists
  refine ⟨errFn (u n), ⟨u n, huH₀ n, rfl⟩, ?_⟩
  rw [← hemp n hn2, risk_eq_real D (hH₀m _ (huH₀ n)), empRisk_eq] at hn1
  have e : (m : ℝ) * D.real {z | errFn (u n) z = true} - hits (errFn (u n)) S =
      m * (D.real {z | errFn (u n) z = true} - hits (errFn (u n)) S / m) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hmR, mul_comm ε]
  exact mul_lt_mul_of_pos_left hn1 hmR

omit [MeasurableSpace X] in
/-- Sauer's lemma for the error indicators. -/
lemma patterns_err (H H₀ : Set (X → Bool)) (hH₀ : H₀ ⊆ H) (d : ℕ) (hd : vcDim H = d) {m : ℕ}
    (S T : Fin m → X × Bool) :
    (pattern S T '' (errFn '' H₀)).ncard ≤ ∑ k ∈ range (d + 1), (2 * m).choose k := by
  set F : (Fin m → Bool × Bool) → (Fin m → Bool × Bool) :=
    fun q i ↦ ((q i).1 != (S i).2, (q i).2 != (T i).2) with hF
  have e : pattern S T '' (errFn '' H₀) =
      F '' (pattern (fun i ↦ (S i).1) (fun i ↦ (T i).1) '' H₀) := by
    rw [Set.image_image, Set.image_image]; rfl
  rw [e]
  exact (Set.ncard_image_le (Set.toFinite _)).trans
    ((Set.ncard_le_ncard (Set.image_mono hH₀) (Set.toFinite _)).trans
      (sauer_patterns H d hd _ _))

/-- The numerical part. -/
lemma final_arith_vc (d m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hm : d + 1 < m) :
    0 < 2 * Real.sqrt ((8 * d * Real.log (Real.exp 1 * m / d) + 2 * Real.log (4 / δ)) / m) ∧
    2 ≤ m * (2 * Real.sqrt ((8 * d * Real.log (Real.exp 1 * m / d) +
      2 * Real.log (4 / δ)) / m)) ^ 2 ∧
    2 * (((∑ k ∈ range (d + 1), (2 * m).choose k : ℕ) : ℝ) *
      (2 * Real.exp (-((2 * Real.sqrt ((8 * d * Real.log (Real.exp 1 * m / d) +
        2 * Real.log (4 / δ)) / m) * m / 2) ^ 2 / (2 * m))))) ≤ δ := by
  set L := Real.log (Real.exp 1 * m / d) with hL
  set K := 8 * d * L + 2 * Real.log (4 / δ) with hK
  set N := ((∑ k ∈ range (d + 1), (2 * m).choose k : ℕ) : ℝ) with hN
  have hmR : (0 : ℝ) < m := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast this
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast (show d ≤ m by omega)
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hlog4 : 1 < Real.log (4 / δ) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    have : 4 < 4 / δ := by rw [lt_div_iff₀ hδ]; linarith
    linarith
  have hdL : 0 ≤ d * L := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · simp [h0]
    · have hdpos : (0 : ℝ) < d := by exact_mod_cast hpos
      apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      rw [le_div_iff₀ hdpos]
      nlinarith
  have hK2 : 2 < K := by rw [hK]; nlinarith
  have hK0 : 0 ≤ K / m := by positivity
  have hsq : (2 * Real.sqrt (K / m)) ^ 2 = 4 * (K / m) := by
    rw [mul_pow, Real.sq_sqrt hK0]; ring
  refine ⟨by have := Real.sqrt_pos.mpr (div_pos (by linarith : (0:ℝ) < K) hmR); positivity,
    ?_, ?_⟩
  · rw [hsq]; field_simp; linarith
  · have hexp : (2 * Real.sqrt (K / m) * m / 2) ^ 2 / (2 * m) = 4 * (d * L) + Real.log (4 / δ) := by
      rw [show (2 * Real.sqrt (K / m) * m / 2) ^ 2 = (2 * Real.sqrt (K / m)) ^ 2 * m ^ 2 / 4 by
        ring, hsq, hK]
      field_simp; ring
    rw [hexp, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity),
      inv_div]
    have hN0 : 0 ≤ N := by positivity
    suffices hNb : N * Real.exp (-(4 * (d * L))) ≤ 1 by
      have := Real.exp_pos (-(4 * (d * L)))
      nlinarith
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [hN]; subst h0; simp
    · have hdpos : (0 : ℝ) < d := by exact_mod_cast hpos
      have hd2m : d ≤ 2 * m := by omega
      have h1 := sum_choose_le (2 * m) d hpos hd2m
      have hb : Real.exp 1 * ((2 * m : ℕ) : ℝ) / d = 2 * (Real.exp 1 * m / d) := by
        push_cast; ring
      rw [hb] at h1
      have hpos' : 0 < Real.exp 1 * m / d := by positivity
      have hL1 : 1 ≤ L := by
        rw [hL, Real.le_log_iff_exp_le hpos', le_div_iff₀ hdpos]
        nlinarith [Real.exp_pos 1]
      have h2 : (2 * (Real.exp 1 * m / d)) ^ d = Real.exp (d * (Real.log 2 + L)) := by
        rw [← Real.exp_log (pow_pos (by positivity : (0:ℝ) < 2 * (Real.exp 1 * m / d)) d),
          Real.log_pow, Real.log_mul (by norm_num) hpos'.ne']
      calc N * Real.exp (-(4 * (d * L)))
          ≤ Real.exp (d * (Real.log 2 + L)) * Real.exp (-(4 * (d * L))) :=
            mul_le_mul_of_nonneg_right (h1.trans h2.le) (Real.exp_pos _).le
        _ = Real.exp (d * Real.log 2 - 3 * (d * L)) := by rw [← Real.exp_add]; ring_nf
        _ ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have := Real.log_two_lt_d9
            nlinarith

end UnderstandingML.VCAux

open UnderstandingML UnderstandingML.EpsNetAux UnderstandingML.EpsNetArith UnderstandingML.VCAux

theorem solution {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hsep : PointwiseSeparable H) (d : ℕ) (hd : vcDim H = d)
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : d + 1 < m) :
    iidLaw D m {S | ∃ h ∈ H,
      2 * Real.sqrt ((8 * d * Real.log (Real.exp 1 * m / d) + 2 * Real.log (4 / δ)) / m) <
        |risk loss01 D h - empRisk loss01 S h|} ≤ ENNReal.ofReal δ := by
  obtain ⟨H₀, hH₀H, hH₀c, happrox⟩ := hsep
  have hH₀m : ∀ h ∈ H₀, Measurable h := fun h hh ↦ hH h (hH₀H hh)
  set G := errFn '' H₀ with hG
  have hGc : G.Countable := hH₀c.image _
  have hGm : ∀ g ∈ G, Measurable g := by
    rintro _ ⟨h, hh, rfl⟩; exact measurable_errFn (hH₀m h hh)
  obtain ⟨hε0, hmε, harith⟩ := final_arith_vc d m δ hδ hδ1 hm
  set ε := 2 * Real.sqrt ((8 * d * Real.log (Real.exp 1 * m / d) + 2 * Real.log (4 / δ)) / m)
    with hε
  have hm0 : 0 < m := by omega
  set N := ∑ k ∈ range (d + 1), (2 * m).choose k with hNdef
  have hN : ∀ S T : Fin m → X × Bool, (pattern S T '' G).ncard ≤ N :=
    fun S T ↦ patterns_err H H₀ hH₀H d hd S T
  calc iidLaw D m {S | ∃ h ∈ H, ε < |risk loss01 D h - empRisk loss01 S h|}
      ≤ iidLaw D m {S | ∃ g ∈ G, ε * m < |(m : ℝ) * D.real {z | g z = true} - hits g S|} :=
        measure_mono (reduce D H H₀ hH₀m happrox ε hm0)
    _ ≤ 2 * ((iidLaw D m).prod (iidLaw D m))
          {p | ∃ g ∈ G, ε * m / 2 < |(hits g p.1 : ℝ) - hits g p.2|} :=
        symm_ghost D G hGc hGm m ε hε0 hmε
    _ ≤ 2 * ENNReal.ofReal (N * (2 * Real.exp (-((ε * m / 2) ^ 2 / (2 * m))))) := by
        gcongr
        exact symm_swap D G hGc hGm hm0 (ε * m / 2) (by positivity) N hN
    _ ≤ ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal harith
