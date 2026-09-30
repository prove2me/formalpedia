-- Prove2me | solution 1 for UnderstandingML.eps_net_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T19:09:14.21644+00:00
-- url     : https://prove2.me/submissions/c5920d1f-a739-4023-8f23-74883079fdad

import Definitions.Def_UnderstandingML_FundamentalProof
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum

/-!
# Theorem 28.3 (the ε-net theorem)

Proof by the double-sample argument: reduction to a countable subclass (Remark 3.1),
Claim 1 (a Chernoff bound), Claim 2 (symmetrization by random swaps), Sauer's lemma,
and the final numerical inequality.
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

open Classical in
/-- For a fixed pattern, few swaps make it bad. -/
lemma count_one_pattern {m : ℕ} (p : Fin m → Bool × Bool) (k : ℕ) :
    (univ.filter fun σ : Fin m → Bool ↦ (∀ i, (if σ i then (p i).2 else (p i).1) = false) ∧
      k ≤ (univ.filter fun i ↦ (if σ i then (p i).1 else (p i).2) = true).card).card ≤
      2 ^ (m - k) := by
  set J : Finset (Fin m) := univ.filter (fun i ↦ (p i).1 = true ∨ (p i).2 = true) with hJ
  set A := (univ.filter fun σ : Fin m → Bool ↦ (∀ i, (if σ i then (p i).2 else (p i).1) = false) ∧
      k ≤ (univ.filter fun i ↦ (if σ i then (p i).1 else (p i).2) = true).card) with hA
  rcases A.eq_empty_or_nonempty with hAe | ⟨σ₀, hσ₀⟩
  · rw [hAe]; simp
  -- forced values on `J`
  have hforced : ∀ σ ∈ A, ∀ i ∈ J, σ i = (p i).1 := by
    intro σ hσ i hi
    rw [hA, Finset.mem_filter] at hσ
    have h1 := hσ.2.1 i
    rw [hJ, Finset.mem_filter] at hi
    obtain ⟨_, hi⟩ := hi
    cases hs : σ i
    · simp only [hs, Bool.false_eq_true, if_false] at h1; exact h1.symm
    · simp only [hs, if_true] at h1
      rcases hi with h | h
      · exact h.symm
      · rw [h1] at h; exact absurd h (by simp)
  have hkJ : k ≤ J.card := by
    rw [hA, Finset.mem_filter] at hσ₀
    refine hσ₀.2.2.trans (Finset.card_le_card ?_)
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [hJ, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨_, hi⟩ := hi
    cases hs : σ₀ i
    · simp only [hs, Bool.false_eq_true, if_false] at hi; exact Or.inr hi
    · simp only [hs, if_true] at hi; exact Or.inl hi
  calc A.card ≤ (Finset.univ : Finset ((univ \ J : Finset (Fin m)) → Bool)).card := by
        apply Finset.card_le_card_of_injOn (fun σ (i : (univ \ J : Finset (Fin m))) ↦ σ i.1)
        · intro σ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
        · intro σ₁ hσ₁ σ₂ hσ₂ heq
          funext i
          by_cases hi : i ∈ J
          · rw [hforced σ₁ hσ₁ i hi, hforced σ₂ hσ₂ i hi]
          · have hi' : i ∈ univ \ J := by simp [hi]
            exact congrFun heq ⟨i, hi'⟩
    _ = 2 ^ (m - J.card) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
          Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    _ ≤ 2 ^ (m - k) := Nat.pow_le_pow_right (by norm_num) (by omega)

open Classical in
/-- Counting the swaps that make a pattern bad. -/
lemma count_swaps (H : Set (X → Bool)) {m : ℕ} (S T : Fin m → X) (k : ℕ) :
    (univ.filter fun σ : Fin m → Bool ↦ ∃ h ∈ H, (∀ i, h (swapS σ S T i) = false) ∧
      k ≤ hits h (swapS σ T S)).card ≤ (pattern S T '' H).ncard * 2 ^ (m - k) := by
  set P := (Set.toFinite (pattern S T '' H)).toFinset with hP
  have hPcard : P.card = (pattern S T '' H).ncard := (Set.ncard_eq_toFinset_card _ _).symm
  rw [← hPcard]
  calc _ ≤ (P.biUnion fun p ↦ univ.filter fun σ : Fin m → Bool ↦
          (∀ i, (if σ i then (p i).2 else (p i).1) = false) ∧
          k ≤ (univ.filter fun i ↦ (if σ i then (p i).1 else (p i).2) = true).card).card := by
        apply Finset.card_le_card
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        obtain ⟨h, hH, h1, h2⟩ := hσ.2
        rw [Finset.mem_biUnion]
        refine ⟨pattern S T h, ?_, ?_⟩
        · rw [hP, Set.Finite.mem_toFinset]; exact ⟨h, hH, rfl⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun i ↦ ?_, ?_⟩
          · have := h1 i
            unfold swapS at this
            unfold pattern
            cases hs : σ i <;> simp only [hs, Bool.false_eq_true, if_false, if_true] at this ⊢ <;>
              exact this
          · refine h2.trans (le_of_eq ?_)
            unfold hits swapS pattern
            congr 1
            apply Finset.filter_congr
            intro i _
            cases σ i <;> simp
    _ ≤ ∑ p ∈ P, (univ.filter fun σ : Fin m → Bool ↦
          (∀ i, (if σ i then (p i).2 else (p i).1) = false) ∧
          k ≤ (univ.filter fun i ↦ (if σ i then (p i).1 else (p i).2) = true).card).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, 2 ^ (m - k) := Finset.sum_le_sum fun p _ ↦ count_one_pattern p k
    _ = P.card * 2 ^ (m - k) := by rw [Finset.sum_const, smul_eq_mul]

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

/-- Symmetrization (Claim 2). -/
lemma symmetrization (D : Measure X) [IsProbabilityMeasure D] (H₀ : Set (X → Bool))
    (hH₀c : H₀.Countable) (hH₀m : ∀ h ∈ H₀, Measurable h) {m : ℕ} (k N : ℕ)
    (hN : ∀ S T : Fin m → X, (pattern S T '' H₀).ncard ≤ N) :
    ((iidLaw D m).prod (iidLaw D m))
        {p | ∃ h ∈ H₀, (∀ i, h (p.1 i) = false) ∧ k ≤ hits h p.2} ≤
      (N : ENNReal) / 2 ^ k := by
  classical
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  set PP := (iidLaw D m).prod (iidLaw D m) with hPP
  have : IsProbabilityMeasure PP := by rw [hPP]; infer_instance
  set B := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ H₀, (∀ i, h (p.1 i) = false) ∧
    k ≤ hits h p.2} with hB
  rcases Nat.lt_or_ge m k with hkm | hkm
  · -- the event is empty
    have : B = ∅ := by
      ext p
      simp only [hB, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro h _ _ hk
      have := hits_le h p.2
      omega
    rw [this, measure_empty]
    exact bot_le
  have hBmeas : MeasurableSet B := measurableSet_bad H₀ hH₀c hH₀m k
  set τ : (Fin m → Bool) → (Fin m → X) × (Fin m → X) → (Fin m → X) × (Fin m → X) :=
    fun σ p ↦ (swapS σ p.1 p.2, swapS σ p.2 p.1) with hτ
  have hτmeas : ∀ σ, MeasurableSet (τ σ ⁻¹' B) := fun σ ↦
    (swap_measurePreserving D σ).measurable hBmeas
  have hsum : (2 ^ m : ENNReal) * PP B = ∫⁻ p, ∑ σ : Fin m → Bool, (τ σ ⁻¹' B).indicator (1 : (Fin m → X) × (Fin m → X) → ENNReal) p ∂PP := by
    rw [lintegral_finset_sum _ (fun σ _ ↦ (measurable_one.indicator (hτmeas σ)))]
    simp_rw [lintegral_indicator_one (hτmeas _)]
    have : ∀ σ, PP (τ σ ⁻¹' B) = PP B := fun σ ↦
      (swap_measurePreserving D σ).measure_preimage hBmeas.nullMeasurableSet
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul]
    norm_cast
  have hpt : ∀ p, ∑ σ : Fin m → Bool, (τ σ ⁻¹' B).indicator (1 : (Fin m → X) × (Fin m → X) → ENNReal) p ≤ ((N * 2 ^ (m - k) : ℕ) : ENNReal) := by
    intro p
    have : ∑ σ : Fin m → Bool, (τ σ ⁻¹' B).indicator (1 : (Fin m → X) × (Fin m → X) → ENNReal) p =
        ((univ.filter fun σ : Fin m → Bool ↦ ∃ h ∈ H₀, (∀ i, h (swapS σ p.1 p.2 i) = false) ∧
          k ≤ hits h (swapS σ p.2 p.1)).card : ENNReal) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro σ _
      simp [Set.indicator, hτ, hB]
    rw [this]
    norm_cast
    exact (count_swaps H₀ p.1 p.2 k).trans (Nat.mul_le_mul_right _ (hN p.1 p.2))
  have hle : (2 ^ m : ENNReal) * PP B ≤ ((N * 2 ^ (m - k) : ℕ) : ENNReal) := by
    rw [hsum]
    calc ∫⁻ p, ∑ σ : Fin m → Bool, (τ σ ⁻¹' B).indicator (1 : (Fin m → X) × (Fin m → X) → ENNReal) p ∂PP
        ≤ ∫⁻ _p, ((N * 2 ^ (m - k) : ℕ) : ENNReal) ∂PP := lintegral_mono hpt
      _ = ((N * 2 ^ (m - k) : ℕ) : ENNReal) := by
          rw [lintegral_const, measure_univ, mul_one]
  have h2m : (2 ^ m : ENNReal) = 2 ^ k * 2 ^ (m - k) := by
    rw [← pow_add]; congr 1; omega
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  rw [h2m] at hle
  push_cast at hle
  have hpos : (2 ^ (m - k) : ENNReal) ≠ 0 := by simp
  have hfin : (2 ^ (m - k) : ENNReal) ≠ ⊤ := by simp
  calc PP B * 2 ^ k = (2 ^ k * 2 ^ (m - k) * PP B) / 2 ^ (m - k) := by
        rw [ENNReal.eq_div_iff hpos hfin]; ring
    _ ≤ (N * 2 ^ (m - k)) / 2 ^ (m - k) := by gcongr
    _ = N := ENNReal.mul_div_cancel_right hpos hfin

/-- A Chernoff bound: a set of mass at least `ε'` is hit at least `ε' m / 2` times with
probability at least `1/2`. -/
lemma chernoff_half (D : Measure X) [IsProbabilityMeasure D] (h : X → Bool) (hh : Measurable h)
    (ε' : ℝ) (hε' : 0 < ε') (hD : ENNReal.ofReal ε' ≤ D {x | h x = true}) (m : ℕ)
    (hm : 8 ≤ ε' * m) :
    (1 / 2 : ENNReal) ≤ iidLaw D m {T | ε' * m / 2 ≤ hits h T} := by
  have hP : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  set P := iidLaw D m with hPdef
  set E := {T : Fin m → X | ε' * m / 2 ≤ (hits h T : ℝ)} with hE
  have hEmeas : MeasurableSet E :=
    measurableSet_le measurable_const ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_hits h hh))
  -- the probability of the set hit by `h`
  set q := (D {x | h x = true}).toReal with hq
  have hSmeas : MeasurableSet {x | h x = true} := hh (measurableSet_singleton true)
  have hqε : ε' ≤ q := by
    rw [hq]
    have := ENNReal.toReal_mono (measure_ne_top D _) hD
    rwa [ENNReal.toReal_ofReal hε'.le] at this
  -- the exponential moment
  set f : X → ℝ := fun x ↦ if h x = true then (1 / 2 : ℝ) else 1 with hf
  set Y : (Fin m → X) → ℝ := fun T ↦ ∏ i, f (T i) with hY
  have hYpow : ∀ T, Y T = (1 / 2 : ℝ) ^ hits h T := by
    intro T
    simp only [hY, hf, hits]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hYmeas : Measurable Y := by
    have h1 : Measurable (fun T : Fin m → X ↦ fun i ↦ h (T i)) := by
      rw [measurable_pi_iff]; intro i; exact hh.comp (measurable_pi_apply i)
    have h2 : Measurable (fun b : Fin m → Bool ↦ ∏ i, (if b i = true then (1 / 2 : ℝ) else 1)) :=
      measurable_of_countable _
    exact h2.comp h1
  have hY0 : ∀ T, 0 ≤ Y T := fun T ↦ by rw [hYpow]; positivity
  have hY1 : ∀ T, Y T ≤ 1 := fun T ↦ by
    rw [hYpow]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hYint : Integrable Y P :=
    Integrable.of_bound hYmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun T ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hY0 T)]; exact hY1 T)
  have hfint : ∫ x, f x ∂D = 1 - q / 2 := by
    have : f = fun x ↦ 1 - (1 / 2 : ℝ) * ({x | h x = true}.indicator 1 x) := by
      funext x
      simp only [hf, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
      split_ifs <;> norm_num
    rw [this, integral_sub (integrable_const _) ((integrable_const _).indicator hSmeas |>.const_mul _)]
    rw [integral_const_mul, integral_indicator_one hSmeas]
    simp [hq, measureReal_def]
    ring
  have hEY : ∫ T, Y T ∂P = (1 - q / 2) ^ m := by
    rw [hPdef, iidLaw, hY]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ x ↦ f x)]
    simp [hfint]
  -- Markov
  set c : ℝ := (1 / 2 : ℝ) ^ (ε' * m / 2) with hc
  have hcpos : 0 < c := by positivity
  have hsub : Eᶜ ⊆ {T | c ≤ Y T} := by
    intro T hT
    simp only [hE, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hT
    simp only [Set.mem_setOf_eq]
    rw [hYpow, hc, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hT.le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hY0) hYint c
  rw [hEY] at hmarkov
  have hbound : (1 - q / 2) ^ m / c ≤ 1 / 2 := by
    have hq1 : q ≤ 1 := by
      rw [hq]; exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simp [prob_le_one])
    have h1 : (1 - q / 2) ^ m ≤ Real.exp (-(ε' * m / 2)) := by
      calc (1 - q / 2) ^ m ≤ (Real.exp (-(q / 2))) ^ m := by
            gcongr
            · linarith
            · linarith [Real.add_one_le_exp (-(q / 2))]
        _ = Real.exp (-(q * m / 2)) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (-(ε' * m / 2)) := by
            apply Real.exp_le_exp.mpr
            have : ε' * m ≤ q * m := by gcongr
            linarith
    have h2 : 1 / c = Real.exp (Real.log 2 * (ε' * m / 2)) := by
      have hc' : c = Real.exp (-(Real.log 2 * (ε' * m / 2))) := by
        rw [hc, Real.rpow_def_of_pos (by norm_num)]
        congr 1
        rw [one_div, Real.log_inv]
        ring
      rw [hc', one_div, ← Real.exp_neg, neg_neg]
    rw [div_eq_mul_one_div, h2]
    calc (1 - q / 2) ^ m * Real.exp (Real.log 2 * (ε' * m / 2))
        ≤ Real.exp (-(ε' * m / 2)) * Real.exp (Real.log 2 * (ε' * m / 2)) := by gcongr
      _ = Real.exp (-((1 - Real.log 2) * (ε' * m / 2))) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have := Real.log_two_lt_d9
          nlinarith
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
  have hreal : P.real {T | c ≤ Y T} ≤ 1 / 2 := by
    have := (le_div_iff₀' hcpos).mpr hmarkov
    linarith
  have hcompl : P Eᶜ ≤ 1 / 2 := by
    calc P Eᶜ ≤ P {T | c ≤ Y T} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {T | c ≤ Y T}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hreal
      _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [prob_compl_eq_one_sub hEmeas] at hcompl
  have hPE : P E ≤ 1 := prob_le_one
  have : (1 : ENNReal) - 1 / 2 ≤ P E := by
    rw [tsub_le_iff_right]
    calc (1 : ENNReal) ≤ (1 - P E) + P E := le_tsub_add
      _ ≤ 1 / 2 + P E := by gcongr
      _ = P E + 1 / 2 := add_comm _ _
  calc (1 / 2 : ENNReal) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
    _ ≤ P E := this

/-- The double-sample trick (Claim 1). -/
lemma double_sample (D : Measure X) [IsProbabilityMeasure D] (H₀ : Set (X → Bool))
    (hH₀c : H₀.Countable) (hH₀m : ∀ h ∈ H₀, Measurable h) (ε' : ℝ) (hε' : 0 < ε') (m : ℕ)
    (hm : 8 ≤ ε' * m) :
    iidLaw D m {S | ∃ h ∈ H₀, ENNReal.ofReal ε' ≤ D {x | h x = true} ∧ ∀ i, h (S i) = false} ≤
      2 * ((iidLaw D m).prod (iidLaw D m))
        {p | ∃ h ∈ H₀, (∀ i, h (p.1 i) = false) ∧ ⌈ε' * m / 2⌉₊ ≤ hits h p.2} := by
  have hP : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  set P := iidLaw D m with hPdef
  set A := {S : Fin m → X | ∃ h ∈ H₀, ENNReal.ofReal ε' ≤ D {x | h x = true} ∧
    ∀ i, h (S i) = false} with hA
  set B := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ H₀, (∀ i, h (p.1 i) = false) ∧
    ⌈ε' * m / 2⌉₊ ≤ hits h p.2} with hB
  have hBmeas : MeasurableSet B := measurableSet_bad H₀ hH₀c hH₀m _
  have hAmeas : MeasurableSet A := by
    have : A = ⋃ h ∈ H₀, {_S : Fin m → X | ENNReal.ofReal ε' ≤ D {x | h x = true}} ∩
        ⋂ i, {S : Fin m → X | h (S i) = false} := by
      ext S
      simp only [hA, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
        exists_prop]
    rw [this]
    refine MeasurableSet.biUnion hH₀c fun h hh ↦ (MeasurableSet.const _).inter ?_
    exact MeasurableSet.iInter fun i ↦
      (hH₀m h hh).comp (measurable_pi_apply i) (measurableSet_singleton false)
  have hsec : ∀ S ∈ A, (1 / 2 : ENNReal) ≤ P (Prod.mk S ⁻¹' B) := by
    intro S hS
    obtain ⟨h, hh, hD, hS0⟩ := hS
    refine (chernoff_half D h (hH₀m h hh) ε' hε' hD m hm).trans (measure_mono ?_)
    intro T hT
    simp only [Set.mem_setOf_eq] at hT
    simp only [Set.mem_preimage, hB, Set.mem_setOf_eq]
    exact ⟨h, hh, hS0, Nat.ceil_le.mpr hT⟩
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

/-- Reduction from `H` to its countable approximating subclass. -/
lemma not_net_subset (D : Measure X) (H H₀ : Set (X → Bool))
    (happrox : ∀ h ∈ H, ∃ u : ℕ → (X → Bool), (∀ n, u n ∈ H₀) ∧
      ∀ x, ∃ N, ∀ n, N ≤ n → u n x = h x)
    (ε ε' : ℝ) (hε' : 0 < ε') (hεε' : ε' < ε) (m : ℕ) :
    {S : Fin m → X | ¬ IsEpsNet H D ε S} ⊆
      {S | ∃ h ∈ H₀, ENNReal.ofReal ε' ≤ D {x | h x = true} ∧ ∀ i, h (S i) = false} := by
  intro S hS
  simp only [Set.mem_setOf_eq, IsEpsNet, not_forall, not_exists] at hS
  obtain ⟨h, hH, hDh, hmiss⟩ := hS
  obtain ⟨u, huH₀, hconv⟩ := happrox h hH
  -- the sets where the approximants are eventually `true`
  set E : ℕ → Set X := fun N ↦ ⋂ n, ⋂ (_ : N ≤ n), {x | u n x = true} with hE
  have hEmono : Monotone E := by
    intro N₁ N₂ hN x hx
    simp only [hE, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
    exact fun n hn ↦ hx n (hN.trans hn)
  have hcover : {x | h x = true} ⊆ ⋃ N, E N := by
    intro x hx
    obtain ⟨N, hN⟩ := hconv x
    simp only [Set.mem_iUnion, hE, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨N, fun n hn ↦ (hN n hn).trans hx⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := D) hEmono
  have hlt : ENNReal.ofReal ε' < D (⋃ N, E N) := by
    calc ENNReal.ofReal ε' < ENNReal.ofReal ε :=
          (ENNReal.ofReal_lt_ofReal_iff (hε'.trans hεε')).mpr hεε'
      _ ≤ D {x | h x = true} := hDh
      _ ≤ D (⋃ N, E N) := measure_mono hcover
  obtain ⟨N₀, hN₀⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
  -- convergence on the sample
  have hsample : ∀ i, ∃ N, ∀ n, N ≤ n → u n (S i) = false := by
    intro i
    obtain ⟨N, hN⟩ := hconv (S i)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [hN n hn]
    simpa using hmiss i
  choose Ni hNi using hsample
  set n := max N₀ (univ.sup Ni) with hn
  refine ⟨u n, huH₀ n, ?_, fun i ↦ hNi i n ?_⟩
  · refine hN₀.le.trans (measure_mono ?_)
    intro x hx
    simp only [hE, Set.mem_iInter, Set.mem_setOf_eq] at hx
    exact hx n (le_max_left _ _)
  · exact (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)

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

lemma log_le_half (y : ℝ) (hy : 0 < y) : Real.log y ≤ y / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (half_pos hy)
  rw [Real.log_div hy.ne' (by norm_num)] at h1
  linarith [Real.log_two_lt_d9]

/-- The final numerical inequality. -/
lemma final_arith (d m : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 4)
    (hm : 8 / ε * (2 * d * Real.log (16 * Real.exp 1 / ε) + Real.log (2 / δ)) ≤ m) :
    2 * ((∑ k ∈ Finset.range (d + 1), (2 * m).choose k : ℕ) : ℝ) *
      (2 : ℝ) ^ (-(3 * ε * m / 8)) ≤ δ ∧ 8 ≤ (3 * ε / 4) * m := by
  set L := Real.log (16 * Real.exp 1 / ε) with hL
  set B := Real.log (2 / δ) with hB
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    rw [le_div_iff₀ hε]
    nlinarith
  have hB2 : 2 ≤ B := by
    rw [hB, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hδ]
    have : Real.exp 2 < 8 := by
      have h := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_pos 1]
    nlinarith
  have hεm : 8 * (2 * d * L + B) ≤ ε * m := by
    have := mul_le_mul_of_nonneg_left hm hε.le
    rw [← mul_assoc, mul_div_cancel₀ _ hε.ne'] at this
    linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdL : 0 ≤ d * L := by positivity
  refine ⟨?_, by nlinarith⟩
  -- exponential form of the rpow
  have hpow : (2 : ℝ) ^ (-(3 * ε * m / 8)) ≤ Real.exp (-(ε * m / 4)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have := Real.log_two_gt_d9
    have hεm0 : 0 ≤ ε * m := by positivity
    nlinarith
  set N : ℝ := ((∑ k ∈ Finset.range (d + 1), (2 * m).choose k : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  -- bound on N
  have hNexp : N ≤ Real.exp (d * L + ε * m / 8) := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [hN]; simp
      positivity
    · have hmpos : (0 : ℝ) < m := by
        have : 0 < ε * m := by nlinarith
        by_contra h; push Not at h; nlinarith
      have hd2m : d ≤ 2 * m := by
        have : (16 : ℝ) * d ≤ m := by
          have h1 : 16 * d ≤ ε * m := by nlinarith
          nlinarith
        have : (d : ℝ) ≤ 2 * m := by linarith
        exact_mod_cast this
      have h1 := sum_choose_le (2 * m) d hd hd2m
      refine h1.trans ?_
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      have hbase : 0 < Real.exp 1 * ((2 * m : ℕ) : ℝ) / d := by push_cast; positivity
      rw [← Real.exp_log (pow_pos hbase d), Real.log_pow]
      apply Real.exp_le_exp.mpr
      have hsplit : Real.exp 1 * ((2 * m : ℕ) : ℝ) / d =
          (8 * Real.exp 1 / ε) * (ε * m / (4 * d)) := by
        push_cast; field_simp; ring
      rw [hsplit, Real.log_mul (by positivity) (by positivity)]
      have h8 : Real.log (8 * Real.exp 1 / ε) ≤ L := by
        rw [hL]; apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_right _ hε.le; nlinarith
      have h9 := log_le_half (ε * m / (4 * d)) (by positivity)
      have h10 : (d : ℝ) * (ε * m / (4 * d) / 2) = ε * m / 8 := by field_simp; ring
      nlinarith
  calc 2 * N * (2 : ℝ) ^ (-(3 * ε * m / 8))
      ≤ 2 * Real.exp (d * L + ε * m / 8) * Real.exp (-(ε * m / 4)) := by gcongr
    _ = 2 * Real.exp (d * L - ε * m / 8) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ 2 * Real.exp (-B) := by gcongr; linarith
    _ = δ := by
        rw [hB, Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

end UnderstandingML.EpsNetArith

open UnderstandingML UnderstandingML.EpsNetAux UnderstandingML.EpsNetArith

theorem solution {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hsep : PointwiseSeparable H) (d : ℕ) (hd : vcDim H = d)
    (D : Measure X) [IsProbabilityMeasure D] (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 4) (m : ℕ)
    (hm : 8 / ε * (2 * d * Real.log (16 * Real.exp 1 / ε) + Real.log (2 / δ)) ≤ m) :
    iidLaw D m {S | ¬ IsEpsNet H D ε S} ≤ ENNReal.ofReal δ := by
  obtain ⟨H₀, hH₀H, hH₀c, happrox⟩ := hsep
  have hH₀m : ∀ h ∈ H₀, Measurable h := fun h hh ↦ hH h (hH₀H hh)
  obtain ⟨harith, hm8⟩ := final_arith d m ε δ hε hε1 hδ hδ1 hm
  set N := ∑ k ∈ Finset.range (d + 1), (2 * m).choose k with hNdef
  have hN : ∀ S T : Fin m → X, (pattern S T '' H₀).ncard ≤ N := fun S T ↦
    (Set.ncard_le_ncard (Set.image_mono hH₀H) (Set.toFinite _)).trans
      (sauer_patterns H d hd S T)
  set k := ⌈3 * ε / 4 * m / 2⌉₊ with hk
  have hε' : 0 < 3 * ε / 4 := by positivity
  calc iidLaw D m {S | ¬ IsEpsNet H D ε S}
      ≤ iidLaw D m {S | ∃ h ∈ H₀, ENNReal.ofReal (3 * ε / 4) ≤ D {x | h x = true} ∧
          ∀ i, h (S i) = false} :=
        measure_mono (not_net_subset D H H₀ happrox ε (3 * ε / 4) hε' (by linarith) m)
    _ ≤ 2 * ((iidLaw D m).prod (iidLaw D m))
          {p | ∃ h ∈ H₀, (∀ i, h (p.1 i) = false) ∧ k ≤ hits h p.2} :=
        double_sample D H₀ hH₀c hH₀m (3 * ε / 4) hε' m hm8
    _ ≤ 2 * ((N : ENNReal) / 2 ^ k) := by
        gcongr
        exact symmetrization D H₀ hH₀c hH₀m k N hN
    _ ≤ ENNReal.ofReal δ := by
        have h1 : (2 : ENNReal) * ((N : ENNReal) / 2 ^ k) =
            ENNReal.ofReal (2 * ((N : ℝ) / 2 ^ k)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by positivity)]
          simp [ENNReal.ofReal_pow]
        rw [h1]
        apply ENNReal.ofReal_le_ofReal
        refine le_trans ?_ harith
        have hkge : 3 * ε * m / 8 ≤ (k : ℝ) := by
          have := Nat.le_ceil (3 * ε / 4 * m / 2)
          rw [← hk] at this
          linarith
        have h2 : ((N : ℝ) / 2 ^ k) = N * (2 : ℝ) ^ (-(k : ℝ)) := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_eq_mul_inv]
        rw [h2]
        have h3 : (2 : ℝ) ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (-(3 * ε * m / 8)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        push_cast [hNdef] at hN0 ⊢
        nlinarith
