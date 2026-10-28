-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.circle_walk_return
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:11:32.173426+00:00
-- url     : https://prove2.me/submissions/4670cedc-5358-4716-958e-399f6552d819

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section
open MeasureTheory ProbabilityTheory Finset

namespace X4CW

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}

def shift (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℕ → ℝ := fun k => X (t + k) ω

lemma measurable_shift (hX : ∀ i, Measurable (X i)) (t : ℕ) : Measurable (shift X t) :=
  measurable_pi_lambda _ fun k => hX (t + k)

lemma law (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (t : ℕ) :
    μ.map (shift X t) = Measure.infinitePi (fun _ : ℕ => μ.map (X 0)) := by
  have h := (hind.precomp (g := fun k => t + k) (add_right_injective t)).map_fun_eq_infinitePi_map
    (fun k => hX (t + k))
  simp only [hlaw] at h
  exact h

lemma shift_eq (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (t : ℕ) {G : Set (ℕ → ℝ)} (hG : MeasurableSet G) :
    μ (shift X t ⁻¹' G) = μ (shift X 0 ⁻¹' G) := by
  rw [← Measure.map_apply (measurable_shift hX t) hG, ← Measure.map_apply (measurable_shift hX 0) hG,
    law hX hind hlaw, law hX hind hlaw]

/-- σ-algebra of the coordinates `< T`. -/
abbrev past (X : ℕ → Ω → ℝ) (T : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Iio T, MeasurableSpace.comap (X i) inferInstance

abbrev fut (X : ℕ → Ω → ℝ) (T : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Ici T, MeasurableSpace.comap (X i) inferInstance

lemma shift_fut (T : ℕ) {G : Set (ℕ → ℝ)} (hG : MeasurableSet G) :
    MeasurableSet[fut X T] (shift X T ⁻¹' G) := by
  have : Measurable[fut X T] (shift X T) := by
    refine @measurable_pi_lambda _ _ _ (fut X T) _ _ fun k => ?_
    exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Set.Ici T) =>
      MeasurableSpace.comap (X i) inferInstance) (T + k) (by simp))
  exact this hG

lemma split (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (T : ℕ) {A : Set Ω} (hA : MeasurableSet[past X T] A)
    {G : Set (ℕ → ℝ)} (hG : MeasurableSet G) :
    μ (A ∩ shift X T ⁻¹' G) = μ A * μ (shift X 0 ⁻¹' G) := by
  have hi := (iIndepFun_iff_iIndep _ X μ).1 hind
  have hind2 := indep_iSup_of_disjoint (fun i => (hX i).comap_le) hi (S := Set.Iio T)
    (T := Set.Ici T) (by
      rw [Set.disjoint_iff]; rintro x ⟨h1, h2⟩; simp at h1 h2; omega)
  rw [(Indep_iff _ _ _).1 hind2 _ _ hA (shift_fut T hG), shift_eq hX hind hlaw T hG]

lemma msum {T a m : ℕ} (h : a + m ≤ T) :
    Measurable[past X T] (fun ω => ∑ k ∈ range m, X (a + k) ω) := by
  refine Finset.measurable_sum (range m) fun k hk => ?_
  exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Set.Iio T) =>
      MeasurableSpace.comap (X i) inferInstance) (a + k) (by simp at hk ⊢; omega))

lemma fract_sub_cases (a b : ℝ) : Int.fract (a - b) = Int.fract a - Int.fract b ∨
    Int.fract (a - b) = Int.fract a - Int.fract b + 1 := by
  have e : a - b = (Int.fract a - Int.fract b) + ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) := by
    push_cast; rw [Int.fract, Int.fract]; ring
  rw [e, Int.fract_add_intCast]
  have h1 := Int.fract_nonneg a; have h2 := Int.fract_lt_one a
  have h3 := Int.fract_nonneg b; have h4 := Int.fract_lt_one b
  rcases le_or_gt 0 (Int.fract a - Int.fract b) with h | h
  · left; exact Int.fract_eq_self.2 ⟨h, by linarith⟩
  · right; rw [← Int.fract_add_one, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]

lemma sum_shift (t j : ℕ) (ω : Ω) :
    ∑ k ∈ range j, shift X t ω k = ∑ k ∈ range (t + j), X k ω - ∑ k ∈ range t, X k ω := by
  rw [Finset.sum_range_add]; simp [shift]

/-! Step 1: two-sided recurrence. -/

def A2 (η : ℝ) : Set (ℕ → ℝ) :=
  {y | ∀ j, 0 < j → Int.fract (∑ k ∈ range j, y k) ∈ Set.Icc η (1 - η)}

lemma A2_meas (η : ℝ) : MeasurableSet (A2 η) := by
  have : A2 η = ⋂ j : ℕ, ⋂ (_ : 0 < j),
      (fun y : ℕ → ℝ => Int.fract (∑ k ∈ range j, y k)) ⁻¹' Set.Icc η (1 - η) := by
    ext y; simp [A2]
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_preimage (measurable_fract.comp
    (Finset.measurable_sum _ fun k _ => measurable_pi_apply k)) measurableSet_Icc

lemma count (η : ℝ) (hη : 0 < η) (N : ℕ) (ω : Ω) :
    ((range N).filter (fun i => shift X i ω ∈ A2 η)).card ≤ ⌈1 / η⌉₊ := by
  set K := ⌈1 / η⌉₊
  have hK : (1 : ℝ) / η ≤ K := Nat.le_ceil _
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK
  have hKη : 1 / (K : ℝ) ≤ η := by
    rw [div_le_iff₀ hKpos]; rw [div_le_iff₀ hη] at hK; linarith
  set S : ℕ → ℝ := fun i => ∑ k ∈ range i, X k ω
  let φ : ℕ → ℕ := fun i => ⌊Int.fract (S i) * K⌋₊
  have key : ∀ i i', i < i' → shift X i ω ∈ A2 η → φ i ≠ φ i' := by
    intro i i' hii' hA heq
    have h := hA (i' - i) (by omega)
    rw [sum_shift, Nat.add_sub_cancel' hii'.le] at h
    have hu := Int.fract_nonneg (S i); have hv := Int.fract_nonneg (S i')
    have f1 := Nat.floor_le (mul_nonneg hu hKpos.le)
    have f2 := Nat.lt_floor_add_one (Int.fract (S i) * K)
    have f3 := Nat.floor_le (mul_nonneg hv hKpos.le)
    have f4 := Nat.lt_floor_add_one (Int.fract (S i') * K)
    simp only [φ] at heq
    rw [heq] at f1 f2
    have hd : |Int.fract (S i') - Int.fract (S i)| < 1 / K := by
      rw [abs_lt, lt_div_iff₀ hKpos, ← neg_div, div_lt_iff₀ hKpos]; constructor <;> nlinarith
    rw [abs_lt] at hd
    rcases fract_sub_cases (S i') (S i) with e | e <;> simp only [S] at e <;>
      rw [e] at h <;> obtain ⟨h1, h2⟩ := h <;> linarith
  calc ((range N).filter (fun i => shift X i ω ∈ A2 η)).card ≤ (range K).card := by
        refine Finset.card_le_card_of_injOn φ (fun i _ => ?_) (fun i hi i' hi' heq => ?_)
        · simp only [coe_range, Set.mem_Iio, φ]
          rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hKpos.le)]
          nlinarith [Int.fract_lt_one (S i)]
        · simp only [coe_filter, Set.mem_setOf_eq] at hi hi'
          rcases lt_trichotomy i i' with h | h | h
          · exact absurd heq (key i i' h hi.2)
          · exact h
          · exact absurd heq.symm (key i' i h hi'.2)
    _ = K := card_range K

lemma recur (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (η : ℝ) (hη : 0 < η) :
    μ (shift X 0 ⁻¹' A2 η) = 0 := by
  set q := μ (shift X 0 ⁻¹' A2 η)
  have hE : ∀ i, MeasurableSet (shift X i ⁻¹' A2 η) := fun i => measurable_shift hX i (A2_meas η)
  have hb : ∀ N : ℕ, (N : ENNReal) * q ≤ (⌈1 / η⌉₊ : ENNReal) := by
    intro N
    calc (N : ENNReal) * q = ∑ i ∈ range N, μ (shift X i ⁻¹' A2 η) := by
          rw [Finset.sum_congr rfl fun i _ => shift_eq hX hind hlaw i (A2_meas η)]; simp [q]
      _ = ∫⁻ ω, ∑ i ∈ range N, (shift X i ⁻¹' A2 η).indicator 1 ω ∂μ := by
          rw [lintegral_finsetSum]
          · exact Finset.sum_congr rfl fun i _ => (lintegral_indicator_one (hE i)).symm
          · intro i _; exact measurable_one.indicator (hE i)
      _ ≤ ∫⁻ _, (⌈1 / η⌉₊ : ENNReal) ∂μ := by
          refine lintegral_mono fun ω => ?_
          simp only [Set.indicator, Pi.one_apply, Set.mem_preimage]
          rw [Finset.sum_boole]
          exact_mod_cast count η hη N ω
      _ = _ := by simp
  by_contra hq
  have hqt : q ≠ ⊤ := measure_ne_top _ _
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top (ENNReal.natCast_ne_top ⌈1 / η⌉₊) hq)
  rw [ENNReal.div_lt_iff (Or.inl hq) (Or.inl hqt)] at hN
  exact absurd (hb N) (not_le.2 hN)


/-! Step 2: descending blocks sweep the circle. -/

def Sup (m n : ℕ) (I : Set ℝ) : Set (ℕ → ℝ) :=
  {y | ∀ j < n, Int.fract (∑ k ∈ range m, y (j * m + k)) ∈ I}

lemma Sup_meas (m n : ℕ) {I : Set ℝ} (hI : MeasurableSet I) : MeasurableSet (Sup m n I) := by
  have : Sup m n I = ⋂ j ∈ range n,
      (fun y : ℕ → ℝ => Int.fract (∑ k ∈ range m, y (j * m + k))) ⁻¹' I := by
    ext y; simp [Sup]
  rw [this]
  refine Finset.measurableSet_biInter _ fun j _ => ?_
  exact measurableSet_preimage (measurable_fract.comp
    (Finset.measurable_sum _ fun k _ => measurable_pi_apply _)) hI

lemma past_sup {t T m n : ℕ} (h : t + n * m ≤ T) {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet[past X T] (shift X t ⁻¹' Sup m n I) := by
  have : shift X t ⁻¹' Sup m n I = ⋂ j ∈ range n,
      (fun ω => Int.fract (∑ k ∈ range m, X ((t + j * m) + k) ω)) ⁻¹' I := by
    ext ω; simp [Sup, shift, add_assoc]
  rw [this]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hj' : j + 1 ≤ n := by simp at hj; omega
  have : t + j * m + m ≤ T := by nlinarith
  exact (measurable_fract.comp (msum this)) hI

lemma sup_succ (t m n : ℕ) (I : Set ℝ) :
    shift X t ⁻¹' Sup m (n + 1) I = shift X t ⁻¹' Sup m n I ∩ shift X (t + n * m) ⁻¹' Sup m 1 I := by
  ext ω
  simp only [Sup, shift, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]
  simp only [Nat.lt_one_iff, forall_eq, zero_mul, zero_add, add_assoc]
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact h1 j h
    · subst h; exact h2

lemma prob_sup (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (m : ℕ) {I : Set ℝ} (hI : MeasurableSet I) (n : ℕ) :
    μ (shift X 0 ⁻¹' Sup m n I) = μ (shift X 0 ⁻¹' Sup m 1 I) ^ n := by
  induction n with
  | zero =>
    have : Sup m 0 I = Set.univ := by ext y; simp [Sup]
    simp [this]
  | succ n ih =>
    rw [sup_succ, zero_add, split hX hind hlaw _ (past_sup (by simp) hI) (Sup_meas m 1 hI), ih,
      pow_succ]

lemma desc_hit (s : ℕ → ℝ) (δ δ1 : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1) (n : ℕ) (hn : 2 ≤ n * δ1)
    (hs : ∀ j < n, Int.fract (s (j + 1) - s j) ∈ Set.Ioc (1 - δ) (1 - δ1)) :
    ∃ j, 0 < j ∧ j ≤ n ∧ Int.fract (s j) ∈ Set.Icc 0 δ := by
  set e : ℕ → ℝ := fun l => 1 - Int.fract (s (l + 1) - s l)
  set R : ℕ → ℝ := fun j => Int.fract (s 0) - ∑ l ∈ range j, e l
  have hint : ∀ j, ∃ z : ℤ, s j - R j = z := by
    intro j
    induction j with
    | zero => exact ⟨⌊s 0⌋, by simp [R, Int.self_sub_fract]⟩
    | succ j ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z + ⌊s (j + 1) - s j⌋ + 1, ?_⟩
      have := Int.self_sub_fract (s (j + 1) - s j)
      simp only [R, e, Finset.sum_range_succ] at hz ⊢
      push_cast; linarith
  have hfr : ∀ j, Int.fract (s j) = Int.fract (R j) := fun j => by
    obtain ⟨z, hz⟩ := hint j; exact Int.fract_eq_fract.2 ⟨z, hz⟩
  have hR0 : 0 ≤ R 0 := by simp [R, Int.fract_nonneg]
  have hRn : R n ≤ -1 + δ := by
    have h1 : (n : ℝ) * δ1 ≤ ∑ l ∈ range n, e l := by
      have := Finset.card_nsmul_le_sum (range n) e δ1 (fun l hl => by
        simp only [mem_range] at hl; have := (hs l hl).2; simp only [e]; linarith)
      simpa using this
    have := Int.fract_lt_one (s 0); simp only [R]; linarith
  have hex : ∃ j, R j ≤ -1 + δ := ⟨n, hRn⟩
  have hj : R (Nat.find hex) ≤ -1 + δ := Nat.find_spec hex
  have hjn : Nat.find hex ≤ n := Nat.find_min' hex hRn
  have hj0 : Nat.find hex ≠ 0 := by intro h; rw [h] at hj; linarith
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := Nat.exists_eq_succ_of_ne_zero hj0
  have hprev : ¬ R i ≤ -1 + δ := Nat.find_min hex (by omega)
  have hstep : R (Nat.find hex) = R i - e i := by rw [hi]; simp [R, Finset.sum_range_succ]; ring
  have hei : e i < δ := by have := (hs i (by omega)).1; simp only [e]; linarith
  refine ⟨Nat.find hex, by omega, hjn, ?_⟩
  rw [hfr, ← Int.fract_add_one, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
  constructor <;> linarith

lemma sweep (δ δ1 : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1) {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n * δ1) (t : ℕ) (ω : Ω)
    (h : shift X t ω ∈ Sup m n (Set.Ioc (1 - δ) (1 - δ1))) :
    ∃ M, 0 < M ∧ Int.fract (∑ k ∈ range M, X k ω) ∈ Set.Icc 0 δ := by
  set s : ℕ → ℝ := fun j => ∑ k ∈ range (t + j * m), X k ω
  have hs : ∀ j < n, Int.fract (s (j + 1) - s j) ∈ Set.Ioc (1 - δ) (1 - δ1) := by
    intro j hj
    have e : s (j + 1) - s j = ∑ k ∈ range m, shift X t ω (j * m + k) := by
      simp only [s, shift]
      rw [show t + (j + 1) * m = (t + j * m) + m by ring, Finset.sum_range_add]
      simp [add_assoc]
    rw [e]; exact h j hj
  obtain ⟨j, hj0, -, hj⟩ := desc_hit s δ δ1 hδ0 hδ n hn hs
  exact ⟨t + j * m, by positivity, hj⟩

theorem main (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ {ω | ¬ ∃ M, 0 < M ∧ Int.fract (∑ k ∈ range M, X k ω) ∈ Set.Icc 0 δ} = 0 := by
  set Bad := {ω | ¬ ∃ M, 0 < M ∧ Int.fract (∑ k ∈ range M, X k ω) ∈ Set.Icc 0 δ}
  set N2 := {ω | ∃ j, 0 < j ∧ Int.fract (∑ k ∈ range j, X k ω) ∈ Set.Ioo (1 - δ) 1}
  by_cases h2 : μ N2 = 0
  · refine measure_mono_null (t := shift X 0 ⁻¹' A2 δ ∪ N2) ?_
      (measure_union_null (recur hX hind hlaw δ hδ) h2)
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or, Set.mem_preimage, A2, Set.mem_setOf_eq, not_forall] at hc
    obtain ⟨⟨j, hj, hjI⟩, hN2⟩ := hc
    simp only [shift, zero_add] at hjI
    apply hω
    refine ⟨j, hj, ?_⟩
    have h0 := Int.fract_nonneg (∑ k ∈ range j, X k ω)
    have h1 := Int.fract_lt_one (∑ k ∈ range j, X k ω)
    rcases lt_or_ge (Int.fract (∑ k ∈ range j, X k ω)) δ with h | h
    · exact ⟨h0, h.le⟩
    · exfalso; apply hN2; refine ⟨j, hj, ?_, h1⟩
      by_contra h'; exact hjI ⟨h, not_lt.1 h'⟩
  · have hcov : N2 ⊆ ⋃ j : ℕ, ⋃ n0 : ℕ, {ω | 0 < j ∧
        Int.fract (∑ k ∈ range j, X k ω) ∈ Set.Ioc (1 - δ) (1 - 1 / ((n0 : ℝ) + 1))} := by
      rintro ω ⟨j, hj, h1, h2⟩
      obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨j, n0, hj, h1, by linarith⟩
    have hex : ∃ j n0 : ℕ, μ {ω | 0 < j ∧
        Int.fract (∑ k ∈ range j, X k ω) ∈ Set.Ioc (1 - δ) (1 - 1 / ((n0 : ℝ) + 1))} ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact h2 (measure_mono_null hcov (measure_iUnion_null fun j => measure_iUnion_null
        fun n0 => hne j n0))
    obtain ⟨m, n0, hp⟩ := hex
    have hm : 0 < m := by
      by_contra hm0
      apply hp
      have : {ω | 0 < m ∧ Int.fract (∑ k ∈ range m, X k ω) ∈
          Set.Ioc (1 - δ) (1 - 1 / ((n0 : ℝ) + 1))} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h; exact absurd h hm0
      rw [this, measure_empty]
    set δ1 : ℝ := 1 / ((n0 : ℝ) + 1)
    set I := Set.Ioc (1 - δ) (1 - δ1)
    have hI : MeasurableSet I := measurableSet_Ioc
    set n := 2 * (n0 + 1)
    have hn : 2 ≤ (n : ℝ) * δ1 := by
      simp only [n, δ1]; push_cast; rw [mul_one_div, mul_div_assoc, div_self (by positivity)]; simp
    have hp' : μ (shift X 0 ⁻¹' Sup m 1 I) ≠ 0 := by
      refine fun h0 => hp (measure_mono_null ?_ h0)
      intro ω hω
      simp only [Sup, shift, Set.mem_preimage, Set.mem_setOf_eq, Nat.lt_one_iff, forall_eq,
        zero_mul, zero_add]
      exact hω.2
    set r := μ (shift X 0 ⁻¹' Sup m n I)
    have hr : r ≠ 0 := by
      simp only [r]; rw [prob_sup hX hind hlaw m hI]; exact pow_ne_zero _ hp'
    set W := n * m
    set F : ℕ → Set Ω := fun L => ⋂ s ∈ range L, (shift X (s * W) ⁻¹' Sup m n I)ᶜ
    have hF : ∀ L, μ (F L) = (1 - r) ^ L := by
      intro L
      induction L with
      | zero => simp [F]
      | succ L ih =>
        have e : F (L + 1) = F L ∩ shift X (L * W) ⁻¹' (Sup m n I)ᶜ := by
          ext ω; simp only [F, Finset.range_add_one, Finset.set_biInter_insert, Set.mem_inter_iff,
            Set.preimage_compl]; tauto
        have hFm : MeasurableSet[past X (L * W)] (F L) := by
          refine Finset.measurableSet_biInter _ fun s hs => ?_
          have hsL : s + 1 ≤ L := by simp at hs; omega
          have : s * W + n * m ≤ L * W := by
            calc s * W + n * m = (s + 1) * W := by simp only [W]; ring
              _ ≤ L * W := Nat.mul_le_mul_right _ hsL
          exact (past_sup this hI).compl
        rw [e, split hX hind hlaw _ hFm (Sup_meas m n hI).compl, ih, pow_succ, Set.preimage_compl,
          prob_compl_eq_one_sub (measurable_shift hX 0 (Sup_meas m n hI))]
    have hBad : ∀ L, Bad ⊆ F L := by
      intro L ω hω
      simp only [F, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
      intro s _ hs
      exact hω (sweep δ δ1 hδ hδ1 hm hn (s * W) ω hs)
    have hlt : 1 - r < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hr
    have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
    exact le_antisymm (ge_of_tendsto' ht fun L => (measure_mono (hBad L)).trans (hF L).le)
      (zero_le)

end X4CW

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.8: positive-time circular return for any IID step law. Real
representatives cover all Borel laws on R/Z. Neither finite support nor a
density is assumed. Time zero cannot witness the conclusion. -/
theorem _root_.solution {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (X : ℕ → Omega → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X mu)
    (hlaw : ∀ i, Measure.map (X i) mu=Measure.map (X 0) mu)
    (epsilon : ℝ) (he : 0<epsilon) :
    mu {w | ∃ m : ℕ, 0 < m ∧ circlePosition X m w∈Set.Icc 0 (Real.logb 2 (1+epsilon))}=1 := by
  set δ := Real.logb 2 (1 + epsilon)
  have hδ : 0 < δ := Real.logb_pos (by norm_num) (by linarith)
  set δ' := min δ (1 / 2)
  have h0 : 0 < δ' := lt_min hδ (by norm_num)
  have h1 : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hm := X4CW.main hX hind hlaw δ' h0 h1
  set T := {w | ∃ m : ℕ, 0 < m ∧ circlePosition X m w ∈ Set.Icc 0 (Real.logb 2 (1 + epsilon))}
  have hc : mu Tᶜ = 0 := by
    refine measure_mono_null (fun w hw => ?_) hm
    simp only [Set.mem_setOf_eq]
    rintro ⟨M, hM, h⟩
    exact hw ⟨M, hM, h.1, h.2.trans (min_le_left _ _)⟩
  refine le_antisymm prob_le_one ?_
  calc (1 : ENNReal) = mu Set.univ := measure_univ.symm
    _ ≤ mu T + mu Tᶜ := by rw [← Set.union_compl_self T]; exact measure_union_le _ _
    _ = mu T := by rw [hc, add_zero]

end QAlgorithms.Papers.Independent.Support50.P42

end
