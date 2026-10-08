-- Prove2me | solution 1 for PalmQueueing.Recurrence.monotone_propp_wilson
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:43:39.635981+00:00
-- url     : https://prove2.me/submissions/7b34db7b-3470-4d44-a9bc-7307f685f114

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_ExactSampling



namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

section MPW

variable {r : ℕ}

/-- pure iteration of the updating function along a finite word -/
def iterH (h : Fin r → ℝ → Fin r) : (n : ℕ) → Fin r → (Fin n → ℝ) → Fin r
  | 0, i, _ => i
  | n + 1, i, v => h (iterH h n i (fun l => v l.castSucc)) (v (Fin.last n))

lemma measurable_iterH (h : Fin r → ℝ → Fin r) (hh : ∀ i, Measurable (h i)) (n : ℕ) (i : Fin r) :
    Measurable (iterH h n i) := by
  induction n generalizing i with
  | zero => exact measurable_const
  | succ n ih =>
    have hh' : Measurable (fun p : Fin r × ℝ => h p.1 p.2) :=
      measurable_from_prod_countable_right (fun i => hh i)
    exact hh'.comp (((ih i).comp (measurable_pi_lambda _ fun l => measurable_pi_apply _)).prodMk
      (measurable_pi_apply _))

variable (C : CFTPMono Ω r)

lemma X_eq_iterH (k : ℤ) (n : ℕ) (i : Fin r) (ω : Ω) :
    C.X k n i ω = iterH C.h n i (fun l : Fin n => C.xi (k + ((l : ℕ) : ℤ)) ω) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [CFTPMono.X, iterH]
    rw [ih]
    simp [Fin.coe_castSucc, Fin.val_last]

lemma X_succ (k : ℤ) (n : ℕ) (i : Fin r) (ω : Ω) :
    C.X k (n + 1) i ω = C.h (C.X k n i ω) (C.xi (k + n) ω) := rfl

/-- the joint law of a block of `n` consecutive driving variables is the product law -/
lemma law_block (k : ℤ) (n : ℕ) :
    Measure.map (fun ω (l : Fin n) => C.xi (k + ((l : ℕ) : ℤ)) ω) C.P
      = Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
  haveI := C.isProb
  have hind : iIndepFun (fun l : Fin n => C.xi (k + ((l : ℕ) : ℤ))) C.P := by
    have hinj : Function.Injective (fun l : Fin n => k + ((l : ℕ) : ℤ)) := by
      intro a b hab
      have := add_left_cancel hab
      exact Fin.ext (by exact_mod_cast this)
    exact C.indep_xi.precomp hinj
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun l => (C.measurable_xi _).aemeasurable)] at hind
  rw [hind]
  congr 1
  funext l
  exact C.unif_xi _

lemma measurable_block (k : ℤ) (n : ℕ) :
    Measurable (fun ω (l : Fin n) => C.xi (k + ((l : ℕ) : ℤ)) ω) :=
  measurable_pi_lambda _ fun l => C.measurable_xi _

lemma prob_block_invariant (k k' : ℤ) (n : ℕ) {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    C.P ((fun ω (l : Fin n) => C.xi (k + ((l : ℕ) : ℤ)) ω) ⁻¹' S)
      = C.P ((fun ω (l : Fin n) => C.xi (k' + ((l : ℕ) : ℤ)) ω) ⁻¹' S) := by
  rw [← Measure.map_apply (measurable_block C k n) hS,
    ← Measure.map_apply (measurable_block C k' n) hS, law_block C, law_block C]

lemma set_X_eq (k : ℤ) (n : ℕ) (i j : Fin r) :
    {ω | C.X k n i ω = j} =
      (fun ω (l : Fin n) => C.xi (k + ((l : ℕ) : ℤ)) ω) ⁻¹' (iterH C.h n i ⁻¹' {j}) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, X_eq_iterH]

lemma measurableSet_X_eq (k : ℤ) (n : ℕ) (i j : Fin r) :
    MeasurableSet {ω | C.X k n i ω = j} := by
  rw [set_X_eq]
  exact measurable_block C k n
    ((measurable_iterH C.h C.measurable_h n i) (measurableSet_singleton j))

lemma prob_X_eq_invariant (k k' : ℤ) (n : ℕ) (i j : Fin r) :
    C.P {ω | C.X k n i ω = j} = C.P {ω | C.X k' n i ω = j} := by
  rw [set_X_eq, set_X_eq]
  exact prob_block_invariant C k k' n
    ((measurable_iterH C.h C.measurable_h n i) (measurableSet_singleton j))

lemma set_X_coal (k : ℤ) (n : ℕ) (a b : Fin r) :
    {ω | C.X k n a ω = C.X k n b ω} =
      (fun ω (l : Fin n) => C.xi (k + ((l : ℕ) : ℤ)) ω) ⁻¹'
        (⋃ x : Fin r, iterH C.h n a ⁻¹' {x} ∩ iterH C.h n b ⁻¹' {x}) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_singleton_iff, X_eq_iterH]
  constructor
  · intro h; exact ⟨_, rfl, h.symm⟩
  · rintro ⟨x, h1, h2⟩; rw [h1, h2]

lemma measurableSet_coal_word (n : ℕ) (a b : Fin r) :
    MeasurableSet (⋃ x : Fin r, iterH C.h n a ⁻¹' {x} ∩ iterH C.h n b ⁻¹' {x}) :=
  MeasurableSet.iUnion fun x =>
    ((measurable_iterH C.h C.measurable_h n a) (measurableSet_singleton x)).inter
      ((measurable_iterH C.h C.measurable_h n b) (measurableSet_singleton x))

lemma measurableSet_X_coal (k : ℤ) (n : ℕ) (a b : Fin r) :
    MeasurableSet {ω | C.X k n a ω = C.X k n b ω} := by
  rw [set_X_coal]
  exact measurable_block C k n (measurableSet_coal_word C n a b)

lemma prob_X_coal_invariant (k k' : ℤ) (n : ℕ) (a b : Fin r) :
    C.P {ω | C.X k n a ω = C.X k n b ω} = C.P {ω | C.X k' n a ω = C.X k' n b ω} := by
  rw [set_X_coal, set_X_coal]
  exact prob_block_invariant C k k' n (measurableSet_coal_word C n a b)

end MPW

section Markov

variable {r : ℕ} (C : CFTPMono Ω r)

lemma row_sum_one (i : Fin r) : ∑ j, ENNReal.ofReal (C.IP i j) = 1 := by
  haveI := C.isProb
  have huniv : (⋃ j : Fin r, {ω | C.h i (C.xi 0 ω) = j}) = Set.univ := by
    ext ω; simp
  have hmeas : ∀ j, MeasurableSet {ω | C.h i (C.xi 0 ω) = j} := fun j =>
    ((C.measurable_h i).comp (C.measurable_xi 0)) (measurableSet_singleton j)
  have hdisj : Pairwise (Function.onFun Disjoint fun j : Fin r => {ω | C.h i (C.xi 0 ω) = j}) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have := measure_iUnion (μ := C.P) hdisj hmeas
  rw [huniv, measure_univ, tsum_fintype] at this
  simp_rw [C.implements] at this
  exact this.symm

lemma ofReal_eq_ofReal_max (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_or_gt 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_zero]

lemma row_max_sum_one (i : Fin r) : ∑ j, max (C.IP i j) 0 = 1 := by
  have h := row_sum_one C i
  have : ∑ j, ENNReal.ofReal (C.IP i j) = ENNReal.ofReal (∑ j, max (C.IP i j) 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => le_max_right _ _)]
    congr 1
    funext j
    exact ofReal_eq_ofReal_max _
  rw [this] at h
  have h1 : (0:ℝ) ≤ ∑ j, max (C.IP i j) 0 := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff h1 zero_le_one] at h
  exact h

lemma IP_nonneg (i j : Fin r) : 0 ≤ C.IP i j := by
  classical
  -- row sums are at most one
  have hsum_le : ∀ i, ∑ j, C.IP i j ≤ 1 := by
    intro i
    rw [← row_max_sum_one C i]
    exact Finset.sum_le_sum fun j _ => le_max_left _ _
  -- rows with positive pi are nonnegative
  have hπsum : ∑ i, C.pi i * ∑ j, C.IP i j = 1 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [C.pi_stationary]
    exact C.pi_sum
  have hterms : ∀ i, C.pi i * (1 - ∑ j, C.IP i j) = 0 := by
    have hz : ∑ i, C.pi i * (1 - ∑ j, C.IP i j) = 0 := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hπsum, C.pi_sum, sub_self]
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ C.pi i * (1 - ∑ j, C.IP i j) :=
      fun i _ => mul_nonneg (C.pi_nonneg i) (sub_nonneg.mpr (hsum_le i))
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i (Finset.mem_univ i)
  have hrow_nonneg : ∀ i, 0 < C.pi i → ∀ j, 0 ≤ C.IP i j := by
    intro i hi j
    have h1 : 1 - ∑ j, C.IP i j = 0 := by
      rcases mul_eq_zero.mp (hterms i) with h | h
      · exact absurd h hi.ne'
      · exact h
    have h2 : ∑ j, (max (C.IP i j) 0 - C.IP i j) = 0 := by
      rw [Finset.sum_sub_distrib, row_max_sum_one C i]
      linarith
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin r)), 0 ≤ max (C.IP i j) 0 - C.IP i j :=
      fun j _ => sub_nonneg.mpr (le_max_left _ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h2 j (Finset.mem_univ j)
    have hmax : max (C.IP i j) 0 = C.IP i j := by linarith
    rw [max_eq_left_iff] at hmax
    exact hmax
  -- transitions from positive-pi states to zero-pi states vanish
  have hzero : ∀ i, 0 < C.pi i → ∀ j, C.pi j = 0 → C.IP i j = 0 := by
    intro i hi j hj
    have hs : ∑ x, C.pi x * C.IP x j = 0 := by rw [C.pi_stationary, hj]
    have hnn : ∀ x ∈ (Finset.univ : Finset (Fin r)), 0 ≤ C.pi x * C.IP x j := by
      intro x _
      rcases (C.pi_nonneg x).lt_or_eq with hx | hx
      · exact mul_nonneg hx.le (hrow_nonneg x hx j)
      · rw [← hx, zero_mul]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi.ne'
    · exact h
  have hpow : ∀ n : ℕ, ∀ i, 0 < C.pi i → ∀ j, C.pi j = 0 → (C.IP ^ n) i j = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi j hj
      rw [pow_zero, Matrix.one_apply_ne]
      rintro rfl
      exact hi.ne' hj
    | succ n ih =>
      intro i hi j hj
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x _
      rcases (C.pi_nonneg x).lt_or_eq with hx | hx
      · rw [hzero x hx j hj, mul_zero]
      · rw [ih i hi x hx.symm, zero_mul]
  -- all pi positive
  have hpos : ∀ j, 0 < C.pi j := by
    intro j
    by_contra hj
    have hj0 : C.pi j = 0 := le_antisymm (not_lt.mp hj) (C.pi_nonneg j)
    obtain ⟨i, hi⟩ : ∃ i, 0 < C.pi i := by
      by_contra hall
      push Not at hall
      have : ∑ i, C.pi i = 0 :=
        Finset.sum_eq_zero fun i _ => le_antisymm (hall i) (C.pi_nonneg i)
      rw [C.pi_sum] at this
      exact one_ne_zero this
    obtain ⟨n, hn⟩ := C.irreducible i j
    rw [hpow n i hi j hj0] at hn
    exact lt_irrefl _ hn
  exact hrow_nonneg i (hpos i) j

lemma IPpow_nonneg (n : ℕ) (i j : Fin r) : 0 ≤ (C.IP ^ n) i j := by
  induction n generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ih i x) (IP_nonneg C x j)

/-- the index block `{0, …, n-1}` as a finset of `ℤ` -/
noncomputable def blk (n : ℕ) : Finset ℤ := Finset.Ico 0 (n : ℤ)

lemma mem_blk (n : ℕ) (l : Fin n) : ((l : ℕ) : ℤ) ∈ blk n := by
  simp only [blk, Finset.mem_Ico]
  omega

/-- restriction from the block coordinates to `Fin n` -/
noncomputable def restr (n : ℕ) (w : ↥(blk n) → ℝ) : Fin n → ℝ := fun l => w ⟨((l : ℕ) : ℤ), mem_blk n l⟩

lemma measurable_restr (n : ℕ) : Measurable (restr n) :=
  measurable_pi_lambda _ fun l => measurable_pi_apply _

lemma X_zero_eq (n : ℕ) (i : Fin r) (ω : Ω) :
    C.X 0 n i ω = iterH C.h n i (restr n (fun l : ↥(blk n) => C.xi l ω)) := by
  rw [X_eq_iterH]
  simp only [zero_add]
  rfl

lemma blk_disjoint (n : ℕ) : Disjoint (blk n) {(n : ℤ)} := by
  rw [Finset.disjoint_singleton_right]
  simp [blk]

lemma markov (n : ℕ) (i j : Fin r) :
    C.P {ω | C.X 0 n i ω = j} = ENNReal.ofReal ((C.IP ^ n) i j) := by
  classical
  haveI := C.isProb
  induction n generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [CFTPMono.X]
    · simp [CFTPMono.X, hij, Ne.symm hij]
  | succ n ih =>
    have hunion : {ω | C.X 0 (n + 1) i ω = j} =
        ⋃ x : Fin r, {ω | C.X 0 n i ω = x} ∩ {ω | C.h x (C.xi n ω) = j} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, X_succ, zero_add]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨x, h1, h2⟩; rw [h1]; exact h2
    have hmeasB : ∀ x : Fin r, MeasurableSet {ω | C.h x (C.xi n ω) = j} := fun x =>
      ((C.measurable_h x).comp (C.measurable_xi n)) (measurableSet_singleton j)
    have hdisj : Pairwise (Function.onFun Disjoint fun x : Fin r =>
        {ω | C.X 0 n i ω = x} ∩ {ω | C.h x (C.xi n ω) = j}) := by
      intro a b hab
      rw [Function.onFun, Set.disjoint_left]
      intro ω ha hb
      exact hab (ha.1.symm.trans hb.1)
    rw [hunion, measure_iUnion hdisj (fun x => (measurableSet_X_eq C 0 n i x).inter (hmeasB x)),
      tsum_fintype]
    -- independence
    have hind := C.indep_xi.indepFun_finset (blk n) {(n : ℤ)} (blk_disjoint n) C.measurable_xi
    have hterm : ∀ x : Fin r,
        C.P ({ω | C.X 0 n i ω = x} ∩ {ω | C.h x (C.xi n ω) = j})
          = C.P {ω | C.X 0 n i ω = x} * C.P {ω | C.h x (C.xi n ω) = j} := by
      intro x
      have hA : {ω | C.X 0 n i ω = x} =
          (fun ω (l : ↥(blk n)) => C.xi l ω) ⁻¹' ((iterH C.h n i ∘ restr n) ⁻¹' {x}) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.comp, Set.mem_singleton_iff,
          X_zero_eq]
      have hB : {ω | C.h x (C.xi n ω) = j} =
          (fun ω (l : ↥({(n : ℤ)} : Finset ℤ)) => C.xi l ω) ⁻¹'
            ((fun w : ↥({(n : ℤ)} : Finset ℤ) → ℝ => C.h x (w ⟨n, Finset.mem_singleton_self _⟩))
              ⁻¹' {j}) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      rw [hA, hB]
      apply hind.measure_inter_preimage_eq_mul
      · exact ((measurable_iterH C.h C.measurable_h n i).comp (measurable_restr n))
          (measurableSet_singleton x)
      · exact ((C.measurable_h x).comp (measurable_pi_apply _)) (measurableSet_singleton j)
    simp_rw [hterm, ih, C.implements]
    rw [pow_succ, Matrix.mul_apply,
      ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (IPpow_nonneg C n i x) (IP_nonneg C x j))]
    congr 1
    funext x
    rw [ENNReal.ofReal_mul (IPpow_nonneg C n i x)]

end Markov

section Main

variable {r : ℕ} (C : CFTPMono Ω r)

/-- measure lemma: measurable sets of probability tending to one inside the target set. -/
theorem ae_of_tendsto_one' (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (T : Set Ω) (Cs : ℕ → Set Ω) (hC : ∀ n, MeasurableSet (Cs n))
    (hsub : ∀ n, Cs n ⊆ T) (hlim : Tendsto (fun n => P0 (Cs n)) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P0, ω ∈ T := by
  rw [ae_iff]
  have hle : ∀ n, P0 {ω | ¬ ω ∈ T} + P0 (Cs n) ≤ 1 := by
    intro n
    have h1 : P0 {ω | ¬ ω ∈ T} ≤ P0 (Cs n)ᶜ := by
      apply measure_mono
      intro ω hω hc
      exact hω (hsub n hc)
    calc P0 {ω | ¬ ω ∈ T} + P0 (Cs n) ≤ P0 (Cs n)ᶜ + P0 (Cs n) := add_le_add h1 le_rfl
      _ = 1 := by rw [add_comm, measure_add_measure_compl (hC n), measure_univ]
  have hlim2 : Tendsto (fun n => P0 {ω | ¬ ω ∈ T} + P0 (Cs n)) atTop
      (𝓝 (P0 {ω | ¬ ω ∈ T} + 1)) := hlim.const_add _
  have := le_of_tendsto' hlim2 hle
  have h2 : P0 {ω | ¬ ω ∈ T} + 1 ≤ 0 + 1 := by simpa using this
  exact le_antisymm ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h2) zero_le'

lemma X_mono (le : Fin r → Fin r → Prop)
    (hpreserve : ∀ i j : Fin r, le i j → ∀ x : ℝ, le (C.h i x) (C.h j x))
    (k : ℤ) (n : ℕ) (ω : Ω) : ∀ i j, le i j → le (C.X k n i ω) (C.X k n j ω) := by
  induction n with
  | zero => intro i j h; exact h
  | succ n ih => intro i j h; exact hpreserve _ _ (ih i j h) _

lemma F_mono (n : ℕ) (a b : Fin r) :
    {ω | C.X 0 n a ω = C.X 0 n b ω} ⊆ {ω | C.X 0 (n + 1) a ω = C.X 0 (n + 1) b ω} := by
  intro ω h
  simp only [Set.mem_ofPred_eq] at h ⊢
  rw [X_succ, X_succ, h]

theorem monotone_propp_wilson_core (le : Fin r → Fin r → Prop)
    (hrefl : ∀ i, le i i) (htrans : ∀ i j k, le i j → le j k → le i k)
    (hantisymm : ∀ i j, le i j → le j i → i = j)
    (bot top : Fin r)
    (hbot : ∀ i, le bot i) (htop : ∀ i, le i top)
    (hpreserve : ∀ i j : Fin r, le i j → ∀ x : ℝ, le (C.h i x) (C.h j x))
    (hrec : ∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.X 0 n top ω = bot) :
    (∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.CoalescedExtremal bot top n ω) ∧
    ∀ Z : Ω → Fin r, Measurable Z →
      (∀ᵐ ω ∂C.P, ∀ n : ℕ, 1 ≤ n → C.CoalescedExtremal bot top n ω →
        Z ω = C.X (-(n : ℤ)) n bot ω) →
      ∀ j : Fin r, (C.P {ω | Z ω = j}).toReal = C.pi j := by
  haveI := C.isProb
  set F : ℕ → Set Ω := fun n => {ω | C.X 0 (n + 1) bot ω = C.X 0 (n + 1) top ω} with hF
  set E : ℕ → Set Ω := fun n =>
    {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) top ω}
    with hE
  have hFm : ∀ n, MeasurableSet (F n) := fun n => measurableSet_X_coal C 0 (n + 1) bot top
  have hEm : ∀ n, MeasurableSet (E n) := fun n => measurableSet_X_coal C _ (n + 1) bot top
  have hEF : ∀ n, C.P (E n) = C.P (F n) := fun n =>
    prob_X_coal_invariant C _ 0 (n + 1) bot top
  have hFmono : Monotone F := monotone_nat_of_le_succ fun n => F_mono C (n + 1) bot top
  have hFU : C.P (⋃ n, F n) = 1 := by
    have hae : ∀ᵐ ω ∂C.P, ω ∈ ⋃ n, F n := by
      filter_upwards [hrec] with ω hω
      obtain ⟨n, hn1, hn⟩ := hω
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Set.mem_iUnion]
      refine ⟨m, ?_⟩
      show C.X 0 (m + 1) bot ω = C.X 0 (m + 1) top ω
      rw [hn]
      apply hantisymm
      · have := X_mono C le hpreserve 0 (m + 1) ω bot top (hbot top)
        rw [hn] at this
        exact this
      · exact hbot _
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hFm)]
    exact ae_iff.mp hae
  have hFlim : Tendsto (fun n => C.P (F n)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := C.P) hFmono
    rw [hFU] at this
    exact this
  have hElim : Tendsto (fun n => C.P (E n)) atTop (𝓝 1) := by
    simp only [hEF]; exact hFlim
  have hEc : Tendsto (fun n => C.P (E n)ᶜ) atTop (𝓝 0) := by
    have hc : ∀ n, C.P (E n)ᶜ = 1 - C.P (E n) := fun n => prob_compl_eq_one_sub (hEm n)
    simp only [hc]
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) hElim
      (Or.inl ENNReal.one_ne_top)
    simpa using this
  refine ⟨?_, ?_⟩
  · apply ae_of_tendsto_one' C.P _ E hEm _ hElim
    intro n ω hω
    exact ⟨n + 1, by omega, hω⟩
  · intro Z hZ hZcoal j
    set G : Set Ω := {ω | ∀ n : ℕ, 1 ≤ n → C.CoalescedExtremal bot top n ω →
      Z ω = C.X (-(n : ℤ)) n bot ω} with hG
    have hGc : C.P Gᶜ = 0 := ae_iff.mp hZcoal
    have hup : ∀ n, C.P {ω | Z ω = j} ≤
        C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j} + C.P (E n)ᶜ := by
      intro n
      calc C.P {ω | Z ω = j}
          ≤ C.P ({ω | Z ω = j} ∩ E n) + C.P ({ω | Z ω = j} \ E n) :=
            measure_le_inter_add_sdiff _ _ _
        _ ≤ (C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j} + C.P Gᶜ) + C.P (E n)ᶜ := by
            gcongr
            · calc C.P ({ω | Z ω = j} ∩ E n)
                  ≤ C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j} ∪ Gᶜ) := by
                    apply measure_mono
                    rintro ω ⟨h1, h2⟩
                    by_cases hg : ω ∈ G
                    · left
                      have := hg (n + 1) (by omega) h2
                      simp only [Set.mem_ofPred_eq] at h1 ⊢
                      rw [← this]; exact h1
                    · right; exact hg
                _ ≤ _ := measure_union_le _ _
            · exact Set.sdiff_subset_compl _ _
        _ = _ := by rw [hGc, add_zero]
    have hlow : ∀ n, C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j} ≤
        C.P {ω | Z ω = j} + C.P (E n)ᶜ := by
      intro n
      calc C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j}
          ≤ C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j} ∩ E n)
            + C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j} \ E n) :=
            measure_le_inter_add_sdiff _ _ _
        _ ≤ (C.P {ω | Z ω = j} + C.P Gᶜ) + C.P (E n)ᶜ := by
            gcongr
            · calc C.P ({ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j} ∩ E n)
                  ≤ C.P ({ω | Z ω = j} ∪ Gᶜ) := by
                    apply measure_mono
                    rintro ω ⟨h1, h2⟩
                    by_cases hg : ω ∈ G
                    · left
                      have := hg (n + 1) (by omega) h2
                      simp only [Set.mem_ofPred_eq] at h1 ⊢
                      rw [this]; exact h1
                    · right; exact hg
                _ ≤ _ := measure_union_le _ _
            · exact Set.sdiff_subset_compl _ _
        _ = _ := by rw [hGc, add_zero]
    have hXlim : Tendsto (fun n => C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j}) atTop
        (𝓝 (ENNReal.ofReal (C.pi j))) := by
      have h1 : ∀ n, C.P {ω | C.X (-((n + 1 : ℕ) : ℤ)) (n + 1) bot ω = j}
          = ENNReal.ofReal ((C.IP ^ (n + 1)) bot j) := fun n => by
        rw [prob_X_eq_invariant C _ 0, markov]
      simp only [h1]
      apply ENNReal.tendsto_ofReal
      exact (C.ergodic bot j).comp (tendsto_add_atTop_nat 1)
    have hle : C.P {ω | Z ω = j} ≤ ENNReal.ofReal (C.pi j) := by
      have := ge_of_tendsto' (hXlim.add hEc) hup
      simpa using this
    have hge : ENNReal.ofReal (C.pi j) ≤ C.P {ω | Z ω = j} := by
      have := le_of_tendsto_of_tendsto' hXlim (tendsto_const_nhds.add hEc) hlow
      simpa using this
    rw [le_antisymm hle hge, ENNReal.toReal_ofReal (C.pi_nonneg j)]

end Main

end PalmQueueing.Recurrence

open PalmQueueing.Recurrence
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution {r : ℕ} (C : CFTPMono Ω r) (le : Fin r → Fin r → Prop)
    (hrefl : ∀ i, le i i) (htrans : ∀ i j k, le i j → le j k → le i k)
    (hantisymm : ∀ i j, le i j → le j i → i = j)
    (bot top : Fin r)
    (hbot : ∀ i, le bot i) (htop : ∀ i, le i top)
    (hpreserve : ∀ i j : Fin r, le i j → ∀ x : ℝ, le (C.h i x) (C.h j x))
    (hrec : ∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.X 0 n top ω = bot) :
    (∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.CoalescedExtremal bot top n ω) ∧
    ∀ Z : Ω → Fin r, Measurable Z →
      (∀ᵐ ω ∂C.P, ∀ n : ℕ, 1 ≤ n → C.CoalescedExtremal bot top n ω →
        Z ω = C.X (-(n : ℤ)) n bot ω) →
      ∀ j : Fin r, (C.P {ω | Z ω = j}).toReal = C.pi j := by
  exact monotone_propp_wilson_core C le hrefl htrans hantisymm bot top hbot htop hpreserve hrec
