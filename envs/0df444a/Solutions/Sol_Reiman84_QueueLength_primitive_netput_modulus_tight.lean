-- Prove2me | solution 1 for Reiman84.QueueLength.primitive_netput_modulus_tight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T13:25:02.454933+00:00
-- url     : https://prove2.me/submissions/f0145e0a-4caa-4d43-b816-595063d6b242

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

set_option autoImplicit false


/-! Random-walk tools for TightPrim (755ffe80): fourth moments of sums of independent centred
bounded variables, and Etemadi's maximal inequality. -/

namespace RW

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma int_of_bdd {f : Ω → ℝ} (B : ℝ) (hf : Measurable f) (hB : ∀ ω, |f ω| ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)

/-- second and fourth moments of a sum of independent centred bounded variables. -/
lemma moments (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (C : ℝ) (hb : ∀ i ω, |Y i ω| ≤ C) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (σ2 M4 : ℝ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2) (h4 : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ M4)
    (j : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range j, Y i ω) ^ 2 ∂μ ≤ j * σ2 ∧
    ∫ ω, (∑ i ∈ Finset.range j, Y i ω) ^ 4 ∂μ ≤ 3 * j ^ 2 * σ2 ^ 2 + j * M4 := by
  have hσ : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (Y 0 ω)).trans (h2 0)
  induction j with
  | zero => simp [hσ]
  | succ j ih =>
    set T : Ω → ℝ := fun ω => ∑ i ∈ Finset.range j, Y i ω with hTdef
    have hT : Measurable T := Finset.measurable_sum _ fun i _ => hmeas i
    have hTb : ∀ ω, |T ω| ≤ j * C := by
      intro ω
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hb i ω).trans ?_
      simp
    have hind' : IndepFun T (Y j) μ := by
      have := hind.indepFun_finsetSum_of_notMem hmeas (s := Finset.range j) (i := j) (by simp)
      convert this using 1
      funext ω; simp [hTdef, Finset.sum_apply]
    have hI : ∀ a b : ℕ, Integrable (fun ω => T ω ^ a * Y j ω ^ b) μ := fun a b =>
      int_of_bdd ((j * C) ^ a * C ^ b) ((hT.pow_const a).mul ((hmeas j).pow_const b))
        fun ω => by
          rw [abs_mul, abs_pow, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hTb ω) a)
            (pow_le_pow_left₀ (abs_nonneg _) (hb j ω) b) (by positivity)
            (pow_nonneg ((abs_nonneg _).trans (hTb ω)) a)
    have hE : ∀ a b : ℕ, ∫ ω, T ω ^ a * Y j ω ^ b ∂μ =
        (∫ ω, T ω ^ a ∂μ) * ∫ ω, Y j ω ^ b ∂μ := fun a b =>
      (hind'.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integral_mul_eq_mul_integral
        (hT.pow_const a).aestronglyMeasurable ((hmeas j).pow_const b).aestronglyMeasurable
    have hexp : ∀ n : ℕ, ∫ ω, (T ω + Y j ω) ^ n ∂μ = ∑ m ∈ Finset.range (n + 1),
        (∫ ω, T ω ^ m ∂μ) * (∫ ω, Y j ω ^ (n - m) ∂μ) * n.choose m := by
      intro n
      simp_rw [add_pow]
      rw [integral_finsetSum _ fun m _ => (hI m (n - m)).mul_const _]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [integral_mul_const, hE]
    have i1 : ∫ ω, T ω ∂μ = 0 := by
      rw [hTdef, integral_finsetSum _ fun i _ => int_of_bdd C (hmeas i) (hb i)]
      simp [h0]
    have hsum : ∀ ω, ∑ i ∈ Finset.range (j + 1), Y i ω = T ω + Y j ω :=
      fun ω => Finset.sum_range_succ _ _
    simp only [hsum, hexp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, zero_add]
    norm_num only [pow_zero, pow_one, integral_const, probReal_univ, smul_eq_mul, mul_one,
      one_mul, zero_mul, i1, h0]
    have hT2 : 0 ≤ ∫ ω, T ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hY2 : 0 ≤ ∫ ω, Y j ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    obtain ⟨ih1, ih2⟩ := ih
    change ∫ ω, T ω ^ 2 ∂μ ≤ _ at ih1
    have hm := mul_le_mul ih1 (h2 j) hY2 (by positivity)
    change ∫ ω, T ω ^ 4 ∂μ ≤ _ at ih2
    have h4j := h4 j
    have h2j := h2 j
    push_cast
    constructor <;> nlinarith

/-- partial sums `S_j = ∑_{i<j} Y_i`. -/
noncomputable def psum (Y : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range j, Y i ω

/-- Etemadi's maximal inequality. -/
lemma etemadi (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (L : ℕ) (x : ℝ) (q : ENNReal)
    (hq : ∀ j ≤ L, μ {ω | x ≤ |psum Y j ω|} ≤ q) :
    μ {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|} ≤ 3 * q := by
  classical
  let F : ∀ j : ℕ, (Finset.range j → ℝ) → (ℕ → ℝ) :=
    fun j v i => if h : i ∈ Finset.range j then v ⟨i, h⟩ else 0
  have hF : ∀ j, Measurable (F j) := fun j => measurable_pi_lambda _ fun i => by
    by_cases h : i ∈ Finset.range j
    · simp only [F, dif_pos h]; exact measurable_pi_apply _
    · simp only [F, dif_neg h]; exact measurable_const
  let V1 : ∀ j, Ω → (Finset.range j → ℝ) := fun j ω i => Y i ω
  have hV1 : ∀ j, Measurable (V1 j) := fun j => measurable_pi_lambda _ fun i => hmeas i
  have hFV : ∀ j ω, ∀ i' ≤ j, ∑ i ∈ Finset.range i', F j (V1 j ω) i = psum Y i' ω := by
    intro j ω i' hi'
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ∈ Finset.range j := Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hi')
    simp only [F, V1, dif_pos this]
  have hV2 : ∀ j ≤ L, ∀ ω, (∑ i : Finset.Ico j L, Y i ω) = psum Y L ω - psum Y j ω := by
    intro j hj ω
    rw [Finset.sum_coe_sort (Finset.Ico j L) (fun i => Y i ω), psum, psum,
      ← Finset.sum_range_add_sum_Ico _ hj]
    ring
  have hg : ∀ m, Measurable fun y : ℕ → ℝ => |∑ i ∈ Finset.range m, y i| := fun m =>
    continuous_abs.measurable.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  let s : ℕ → Set (ℕ → ℝ) := fun j => {y | 3 * x ≤ |∑ i ∈ Finset.range j, y i| ∧
    ∀ i' ∈ Finset.range j, |∑ i ∈ Finset.range i', y i| < 3 * x}
  have hsm : ∀ j, MeasurableSet (s j) := by
    intro j
    have : s j = {y | 3 * x ≤ |∑ i ∈ Finset.range j, y i|} ∩
        ⋂ i' ∈ Finset.range j, {y | |∑ i ∈ Finset.range i', y i| < 3 * x} := by
      ext y; simp [s]
    rw [this]
    exact (measurableSet_le measurable_const (hg j)).inter
      (Finset.measurableSet_biInter _ fun i' _ => measurableSet_lt (hg i') measurable_const)
  let E : ℕ → Set Ω := fun j => (F j ∘ V1 j) ⁻¹' (s j)
  have hEm : ∀ j, MeasurableSet (E j) := fun j => ((hF j).comp (hV1 j)) (hsm j)
  let D : ℕ → Set Ω := fun j =>
    ((fun v : Finset.Ico j L → ℝ => ∑ i, v i) ∘ (fun ω (i : Finset.Ico j L) => Y i ω)) ⁻¹'
      {r | 2 * x ≤ |r|}
  have hind2 : ∀ j, μ (E j ∩ D j) = μ (E j) * μ (D j) := by
    intro j
    have h1 := hind.indepFun_finset (Finset.range j) (Finset.Ico j L)
      (Finset.disjoint_left.2 fun i hi hi' => by
        simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'; omega) hmeas
    have h2 := h1.comp (hF j) (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
    exact h2.measure_inter_preimage_eq_mul _ _ (hsm j)
      (measurableSet_le measurable_const continuous_abs.measurable)
  have hD : ∀ j ≤ L, μ (D j) ≤ 2 * q := by
    intro j hj
    have hsub : D j ⊆ {ω | x ≤ |psum Y L ω|} ∪ {ω | x ≤ |psum Y j ω|} := by
      intro ω hω
      have hω' : 2 * x ≤ |∑ i : Finset.Ico j L, Y i ω| := hω
      rw [hV2 j hj ω] at hω'
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      have := abs_sub (psum Y L ω) (psum Y j ω)
      linarith [hcon.1, hcon.2]
    calc μ (D j) ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ q + q := add_le_add (hq L le_rfl) (hq j hj)
      _ = 2 * q := by ring
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (L + 1))) E := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω ha hb
    have ha' : F a (V1 a ω) ∈ s a := ha
    have hb' : F b (V1 b ω) ∈ s b := hb
    simp only [s, Set.mem_setOf_eq] at ha' hb'
    rcases lt_or_gt_of_ne hab with h | h
    · have h1 := ha'.1
      have h2 := hb'.2 a (Finset.mem_range.2 h)
      rw [hFV a ω a le_rfl] at h1; rw [hFV b ω a h.le] at h2; linarith
    · have h1 := hb'.1
      have h2 := ha'.2 b (Finset.mem_range.2 h)
      rw [hFV b ω b le_rfl] at h1; rw [hFV a ω b h.le] at h2; linarith
  have hsub : {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|} ⊆
      {ω | x ≤ |psum Y L ω|} ∪ ⋃ j ∈ Finset.range (L + 1), (E j ∩ D j) := by
    rintro ω ⟨j, hjL, hj⟩
    by_cases hL : x ≤ |psum Y L ω|
    · left; exact hL
    · right
      have hex : ∃ j, j ≤ L ∧ 3 * x ≤ |psum Y j ω| := ⟨j, hjL, hj⟩
      have hj0 := Nat.find_spec hex
      have hmin : ∀ i < Nat.find hex, ¬ (i ≤ L ∧ 3 * x ≤ |psum Y i ω|) :=
        fun i hi => Nat.find_min hex hi
      refine Set.mem_biUnion (x := Nat.find hex)
        (Finset.mem_coe.2 (Finset.mem_range.2 (by omega))) ⟨?_, ?_⟩
      · show F (Nat.find hex) (V1 (Nat.find hex) ω) ∈ s (Nat.find hex)
        refine ⟨by rw [hFV _ ω _ le_rfl]; exact hj0.2, fun i' hi' => ?_⟩
        rw [hFV _ ω i' (Finset.mem_range.1 hi').le]
        have := hmin i' (Finset.mem_range.1 hi')
        push_neg at this
        exact this (by have := Finset.mem_range.1 hi'; omega)
      · show 2 * x ≤ |∑ i : Finset.Ico (Nat.find hex) L, Y i ω|
        rw [hV2 _ hj0.1 ω]
        push_neg at hL
        have := abs_sub_abs_le_abs_sub (psum Y (Nat.find hex) ω) (psum Y L ω)
        rw [abs_sub_comm] at this
        linarith [hj0.2]
  calc μ {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|}
      ≤ μ ({ω | x ≤ |psum Y L ω|} ∪ ⋃ j ∈ Finset.range (L + 1), (E j ∩ D j)) := measure_mono hsub
    _ ≤ μ {ω | x ≤ |psum Y L ω|} + ∑ j ∈ Finset.range (L + 1), μ (E j ∩ D j) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ q + ∑ j ∈ Finset.range (L + 1), μ (E j) * (2 * q) := by
        refine add_le_add (hq L le_rfl) (Finset.sum_le_sum fun j hj => ?_)
        rw [hind2 j]
        gcongr
        exact hD j (by have := Finset.mem_range.1 hj; omega)
    _ = q + μ (⋃ j ∈ Finset.range (L + 1), E j) * (2 * q) := by
        rw [← Finset.sum_mul, measure_biUnion_finset hdisj fun j _ => hEm j]
    _ ≤ q + 1 * (2 * q) := by gcongr; exact prob_le_one
    _ = 3 * q := by ring

lemma markov4 (Z : Ω → ℝ) (hint : Integrable (fun ω => Z ω ^ 4) μ) {x : ℝ} (hx : 0 < x) :
    μ {ω | x ≤ |Z ω|} ≤ ENNReal.ofReal ((∫ ω, Z ω ^ 4 ∂μ) / x ^ 4) := by
  have hx4 : 0 < x ^ 4 := by positivity
  have h := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => by positivity : 0 ≤ᵐ[μ] fun ω => Z ω ^ 4) hint (x ^ 4)
  have hsub : {ω | x ≤ |Z ω|} ⊆ {ω | x ^ 4 ≤ Z ω ^ 4} := by
    intro ω hω
    have h1 : x ^ 4 ≤ |Z ω| ^ 4 := pow_le_pow_left₀ hx.le hω 4
    rwa [Even.pow_abs (⟨2, rfl⟩ : Even 4)] at h1
  calc μ {ω | x ≤ |Z ω|} ≤ μ {ω | x ^ 4 ≤ Z ω ^ 4} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | x ^ 4 ≤ Z ω ^ 4}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((∫ ω, Z ω ^ 4 ∂μ) / x ^ 4) :=
        ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hx4]; linarith [h])

/-- maximal inequality for one block of a centred bounded independent sequence. -/
lemma block_bound (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (B : ℝ) (hb : ∀ i ω, |Y i ω| ≤ B) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (σ2 : ℝ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2) (a L : ℕ) {x : ℝ} (hx : 0 < x) :
    μ {ω | ∃ l ≤ L, 3 * x ≤ |psum (Y ∘ (fun i => a + i)) l ω|} ≤
      3 * ENNReal.ofReal ((3 * L ^ 2 * σ2 ^ 2 + L * (B ^ 2 * σ2)) / x ^ 4) := by
  have hσ : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (Y 0 ω)).trans (h2 0)
  have hind' : iIndepFun (Y ∘ (fun i => a + i)) μ := iIndepFun.precomp (g := fun i : ℕ => a + i) (add_right_injective a) hind
  have hmeas' : ∀ i, Measurable ((Y ∘ (fun i => a + i)) i) := fun i => hmeas _
  have hb' : ∀ i ω, |(Y ∘ (fun i => a + i)) i ω| ≤ B := fun i ω => hb _ ω
  have h4 : ∀ i, ∫ ω, (Y ∘ (fun i => a + i)) i ω ^ 4 ∂μ ≤ B ^ 2 * σ2 := by
    intro i
    have hY := hmeas (a + i)
    have hi2 : Integrable (fun ω => Y (a + i) ω ^ 2) μ :=
      int_of_bdd (B ^ 2) (hY.pow_const 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 2
    have hi4 : Integrable (fun ω => Y (a + i) ω ^ 4) μ :=
      int_of_bdd (B ^ 4) (hY.pow_const 4) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 4
    calc ∫ ω, Y (a + i) ω ^ 4 ∂μ ≤ ∫ ω, B ^ 2 * Y (a + i) ω ^ 2 ∂μ := by
          refine integral_mono hi4 (hi2.const_mul _) fun ω => ?_
          have h1 : Y (a + i) ω ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 2
          have h2' : 0 ≤ Y (a + i) ω ^ 2 := sq_nonneg _
          show Y (a + i) ω ^ 4 ≤ B ^ 2 * Y (a + i) ω ^ 2
          nlinarith
      _ = B ^ 2 * ∫ ω, Y (a + i) ω ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ B ^ 2 * σ2 := mul_le_mul_of_nonneg_left (h2 _) (sq_nonneg _)
  refine etemadi _ hind' hmeas' L x _ fun j hj => ?_
  have hmom := (moments _ hind' hmeas' B hb' (fun i => h0 _) σ2 (B ^ 2 * σ2)
    (fun i => h2 _) h4 j).2
  have hpm : Measurable (psum (Y ∘ (fun i => a + i)) j) :=
    Finset.measurable_sum _ fun i _ => hmeas' i
  have hint : Integrable (fun ω => psum (Y ∘ (fun i => a + i)) j ω ^ 4) μ := by
    refine int_of_bdd ((j * B) ^ 4) (hpm.pow_const 4) fun ω => ?_
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hb' i ω).trans ?_
    simp
  refine (markov4 _ hint hx).trans (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hjL : (j:ℝ) ≤ L := by exact_mod_cast hj
  have hB2 : 0 ≤ B ^ 2 * σ2 := mul_nonneg (sq_nonneg _) hσ
  refine hmom.trans ?_
  have : (j:ℝ) ^ 2 ≤ (L:ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hjL 2
  nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg σ2),
    mul_le_mul_of_nonneg_right hjL hB2]

/-- truncation at level `τ`. -/
noncomputable def trunc (τ : ℝ) (x : ℝ) : ℝ := if |x| ≤ τ then x else 0

lemma trunc_meas (τ : ℝ) : Measurable (trunc τ) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
    measurable_const

lemma trunc_abs {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) : |trunc τ x| ≤ τ := by
  unfold trunc; split_ifs with h
  · exact h
  · simpa using hτ

lemma trunc_sq (τ x : ℝ) : trunc τ x ^ 2 ≤ x ^ 2 := by
  unfold trunc; split_ifs
  · exact le_rfl
  · simpa using sq_nonneg x

lemma trunc_tail {τ : ℝ} (hτ : 0 < τ) (x : ℝ) : |x - trunc τ x| ≤ x ^ 2 / τ := by
  unfold trunc; split_ifs with h
  · simp only [sub_self, abs_zero]; positivity
  · push_neg at h
    rw [sub_zero, le_div_iff₀ hτ, ← sq_abs]
    nlinarith [abs_nonneg x]

/-- one-space modulus bound for a centred i.i.d. square-integrable sequence, by truncation at
`τ`, block decomposition and Etemadi's inequality. -/
lemma mod_bound (ξ : ℕ → Ω → ℝ) (hind : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) (hL2 : MemLp (ξ 0) 2 μ)
    (h0 : ∫ ω, ξ 0 ω ∂μ = 0) (σ2 : ℝ) (hσ : ∫ ω, ξ 0 ω ^ 2 ∂μ ≤ σ2)
    {τ : ℝ} (hτ : 0 < τ) (Nmax L : ℕ) (hL : 1 ≤ L) {x : ℝ} (hx : 0 < x)
    (hdrift : (L:ℝ) * (σ2 / τ) ≤ x / 2) :
    μ {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|} ≤
      Nmax * μ {ω | τ < |ξ 0 ω|} + ((Nmax / L + 1 : ℕ) : ENNReal) *
        (3 * ENNReal.ofReal ((3 * ((2 * L : ℕ) : ℝ) ^ 2 * σ2 ^ 2 +
          ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * σ2)) / (x / 12) ^ 4)) := by
  classical
  set c := ∫ ω, trunc τ (ξ 0 ω) ∂μ with hc
  set Y : ℕ → Ω → ℝ := fun i => (fun r => trunc τ r - c) ∘ ξ i with hY
  have hYind : iIndepFun Y μ := hind.comp (fun _ r => trunc τ r - c)
    (fun _ => (trunc_meas τ).sub_const c)
  have hYm : ∀ i, Measurable (Y i) := fun i => ((trunc_meas τ).sub_const c).comp (hmeas i)
  have htr_int : ∀ i, Integrable (fun ω => trunc τ (ξ i ω)) μ := fun i =>
    int_of_bdd τ ((trunc_meas τ).comp (hmeas i)) fun ω => trunc_abs hτ.le _
  have hcabs : |c| ≤ τ := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => trunc τ (ξ 0 ω)) (C := τ)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact trunc_abs hτ.le _)
    simpa [Real.norm_eq_abs] using this
  have hYb : ∀ i ω, |Y i ω| ≤ 2 * τ := by
    intro i ω
    simp only [hY, Function.comp]
    have := abs_sub (trunc τ (ξ i ω)) c
    linarith [trunc_abs hτ.le (ξ i ω)]
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [hY, Function.comp]
    rw [integral_sub (htr_int i) (integrable_const c), integral_const, probReal_univ, one_smul]
    have := ((hid i).comp (trunc_meas τ)).integral_eq
    simp only [Function.comp] at this
    rw [this, hc, sub_self]
  have hY2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2 := by
    intro i
    have e : ∫ ω, Y i ω ^ 2 ∂μ = ∫ ω, (trunc τ (ξ 0 ω) - c) ^ 2 ∂μ := by
      have := ((hid i).comp (((trunc_meas τ).sub_const c).pow_const 2)).integral_eq
      simpa [hY, Function.comp] using this
    rw [e]
    have hsq : Integrable (fun ω => trunc τ (ξ 0 ω) ^ 2) μ :=
      int_of_bdd (τ ^ 2) (((trunc_meas τ).comp (hmeas 0)).pow_const 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (trunc_abs hτ.le _) 2
    have e2 : ∫ ω, (trunc τ (ξ 0 ω) - c) ^ 2 ∂μ = ∫ ω, trunc τ (ξ 0 ω) ^ 2 ∂μ - c ^ 2 := by
      have hp : ∀ ω, (trunc τ (ξ 0 ω) - c) ^ 2 =
          trunc τ (ξ 0 ω) ^ 2 + ((-2 * c) * trunc τ (ξ 0 ω) + c ^ 2) := fun ω => by ring
      simp only [hp]
      have hg1 : Integrable (fun ω => -2 * c * trunc τ (ξ 0 ω)) μ := (htr_int 0).const_mul _
      have hg : Integrable (fun ω => -2 * c * trunc τ (ξ 0 ω) + c ^ 2) μ :=
        hg1.add (integrable_const _)
      rw [integral_add hsq hg, integral_add hg1 (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul, ← hc]
      ring
    rw [e2]
    have h1 : ∫ ω, trunc τ (ξ 0 ω) ^ 2 ∂μ ≤ ∫ ω, ξ 0 ω ^ 2 ∂μ :=
      integral_mono hsq hL2.integrable_sq fun ω => trunc_sq τ _
    nlinarith [sq_nonneg c]
  have hcσ : |c| ≤ σ2 / τ := by
    have hξi : Integrable (ξ 0) μ := hL2.integrable one_le_two
    have e : c = -∫ ω, (ξ 0 ω - trunc τ (ξ 0 ω)) ∂μ := by
      rw [integral_sub hξi (htr_int 0), h0, hc]; ring
    rw [e, abs_neg]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |ξ 0 ω - trunc τ (ξ 0 ω)| ∂μ ≤ ∫ ω, ξ 0 ω ^ 2 / τ ∂μ :=
          integral_mono (hξi.sub (htr_int 0)).abs (hL2.integrable_sq.div_const τ)
            fun ω => trunc_tail hτ _
      _ = (∫ ω, ξ 0 ω ^ 2 ∂μ) / τ := integral_div _ _
      _ ≤ σ2 / τ := div_le_div_of_nonneg_right hσ hτ.le
  -- the event inclusion
  set Blk : ℕ → Set Ω := fun b =>
    {ω | ∃ l ≤ 2 * L, 3 * (x / 12) ≤ |psum (Y ∘ (fun i => b * L + i)) l ω|} with hBlk
  have hsub : {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|} ⊆
      (⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) ∪ ⋃ b ∈ Finset.range (Nmax / L + 1), Blk b := by
    rintro ω ⟨i, j, hij, hjL, hjN, hxij⟩
    by_cases hbad : ∃ i' < Nmax, τ < |ξ i' ω|
    · obtain ⟨i', hi', h'⟩ := hbad
      left; exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi')) h'
    · right
      push_neg at hbad
      have hpsum : ∀ k ≤ Nmax, psum ξ k ω = psum Y k ω + k * c := by
        intro k hk
        have e : ∀ i ∈ Finset.range k, ξ i ω = Y i ω + c := fun i hi => by
          simp only [hY, Function.comp, trunc,
            if_pos (hbad i (by have := Finset.mem_range.1 hi; omega))]
          ring
        rw [psum, psum, Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      have hdiff : x / 2 ≤ |psum Y j ω - psum Y i ω| := by
        rw [hpsum j hjN, hpsum i (hij.trans hjN)] at hxij
        have hji : ((j:ℝ) - i) ≤ L := by
          have : (j:ℝ) ≤ i + L := by exact_mod_cast hjL
          linarith
        have hji0 : 0 ≤ (j:ℝ) - i := by
          have : (i:ℝ) ≤ j := by exact_mod_cast hij
          linarith
        have hcd : |((j:ℝ) - i) * c| ≤ L * (σ2 / τ) := by
          rw [abs_mul, abs_of_nonneg hji0]
          exact mul_le_mul hji hcσ (abs_nonneg _) (Nat.cast_nonneg _)
        have e : psum Y j ω + j * c - (psum Y i ω + i * c) =
            (psum Y j ω - psum Y i ω) + ((j:ℝ) - i) * c := by ring
        rw [e] at hxij
        have := abs_add_le (psum Y j ω - psum Y i ω) (((j:ℝ) - i) * c)
        linarith
      set b := i / L with hb
      have ha : b * L ≤ i := Nat.div_mul_le_self i L
      have ha2 : i < b * L + L := Nat.lt_div_mul_add hL
      have hshift : ∀ k, b * L ≤ k →
          psum (Y ∘ (fun i => b * L + i)) (k - b * L) ω = psum Y k ω - psum Y (b * L) ω := by
        intro k hk
        have : psum Y k ω = psum Y (b * L) ω + psum (Y ∘ (fun i => b * L + i)) (k - b * L) ω := by
          simp only [psum, Function.comp]
          rw [← Finset.sum_range_add (fun i => Y i ω) (b * L) (k - b * L), Nat.add_sub_cancel' hk]
        linarith
      refine Set.mem_biUnion (x := b) (Finset.mem_coe.2 (Finset.mem_range.2 ?_)) ?_
      · have : b ≤ Nmax / L := Nat.div_le_div_right (hij.trans hjN)
        omega
      · by_contra hno
        simp only [hBlk, Set.mem_setOf_eq, not_exists, not_and, not_le] at hno
        have h1 := hno (j - b * L) (by omega)
        have h2 := hno (i - b * L) (by omega)
        rw [hshift j (by omega)] at h1
        rw [hshift i ha] at h2
        have := abs_sub_le (psum Y j ω) (psum Y (b * L) ω) (psum Y i ω)
        rw [abs_sub_comm (psum Y (b * L) ω)] at this
        linarith
  calc μ {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|}
      ≤ μ ((⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) ∪
          ⋃ b ∈ Finset.range (Nmax / L + 1), Blk b) := measure_mono hsub
    _ ≤ μ (⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) +
          μ (⋃ b ∈ Finset.range (Nmax / L + 1), Blk b) := measure_union_le _ _
    _ ≤ ∑ i ∈ Finset.range Nmax, μ {ω | τ < |ξ i ω|} +
          ∑ b ∈ Finset.range (Nmax / L + 1), μ (Blk b) :=
        add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ ∑ i ∈ Finset.range Nmax, μ {ω | τ < |ξ 0 ω|} +
          ∑ b ∈ Finset.range (Nmax / L + 1), (3 * ENNReal.ofReal ((3 * ((2 * L : ℕ) : ℝ) ^ 2 *
            σ2 ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * σ2)) / (x / 12) ^ 4)) := by
        refine add_le_add (le_of_eq (Finset.sum_congr rfl fun i _ =>
          (hid i).measure_mem_eq (measurableSet_lt measurable_const continuous_abs.measurable)))
          (Finset.sum_le_sum fun b _ => ?_)
        exact block_bound Y hYind hYm (2 * τ) hYb hY0 σ2 hY2 (b * L) (2 * L) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
          nsmul_eq_mul, nsmul_eq_mul]

section Tri

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)]

/-- lattice modulus tightness of the scaled partial-sum process of a triangular array of centred
i.i.d. rows with bounded variances and a Lindeberg-type jump condition. -/
lemma rw_tight (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (ξ : ∀ n, ℕ → Ωs n → ℝ) (hind : ∀ n, iIndepFun (ξ n) (P n))
    (hmeas : ∀ n i, Measurable (ξ n i)) (hid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n))
    (hL2 : ∀ n, MemLp (ξ n 0) 2 (P n)) (h0 : ∀ n, ∫ ω, ξ n 0 ω ∂(P n) = 0)
    (σ2 : ℝ) (hσ : ∀ᶠ n in atTop, ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ σ2)
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0))
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
      (j:ℝ) ≤ T * n ∧ ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤
        ENNReal.ofReal η := by
  set s' := max σ2 1 with hs'
  have hs'1 : 1 ≤ s' := le_max_right _ _
  have hs'0 : 0 < s' := by linarith
  set K := 6 * 12 ^ 4 * T / ε ^ 4 with hK
  have hK0 : 0 < K := by positivity
  set θ := Real.sqrt (η / (64 * K * s')) with hθ
  have hθ0 : 0 < θ := Real.sqrt_pos.2 (by positivity)
  have hθ2 : θ ^ 2 = η / (64 * K * s') := Real.sq_sqrt (by positivity)
  set δ := min T (min (η / (192 * K * s' ^ 2)) (θ * ε / (4 * s'))) with hδ
  have hδ0 : 0 < δ := lt_min hT (lt_min (by positivity) (by positivity))
  have hδT : δ ≤ T := min_le_left _ _
  have hδ1 : δ ≤ η / (192 * K * s' ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ θ * ε / (4 * s') := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ0, ?_⟩
  have hJ : ∀ᶠ n : ℕ in atTop, ((⌈T⌉₊ : ℕ) : ENNReal) *
      ((n : ENNReal) * P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) < ENNReal.ofReal (η / 2) := by
    have := ENNReal.Tendsto.const_mul (a := ((⌈T⌉₊ : ℕ) : ENNReal)) (hUI θ hθ0)
      (Or.inr (ENNReal.natCast_ne_top _))
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 _ (ENNReal.ofReal_pos.2 (by linarith))
  filter_upwards [hJ, hσ, eventually_ge_atTop ⌈1 / δ⌉₊, eventually_ge_atTop 1]
    with n hJn hσn hnδ hn1
  have := hP n
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hδn : 1 ≤ δ * n := by
    have h1 : 1 / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
    rw [div_le_iff₀ hδ0] at h1; linarith
  set Nmax := ⌊T * n⌋₊ with hNmax
  set L := ⌈δ * n⌉₊ with hLdef
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hLr : (L:ℝ) ≤ 2 * δ * n := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ δ * n); linarith
  have hLr' : δ * n ≤ L := Nat.le_ceil _
  have hNr : (Nmax:ℝ) ≤ T * n := Nat.floor_le (by positivity)
  set τ := θ * Real.sqrt n with hτdef
  have hτ : 0 < τ := by positivity
  set x := ε * Real.sqrt n with hxdef
  have hx : 0 < x := by positivity
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hdrift : (L:ℝ) * (s' / τ) ≤ x / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hτ]
    have hxτ : x / 2 * τ = ε * θ * n / 2 := by
      rw [hxdef, hτdef, show ε * Real.sqrt n / 2 * (θ * Real.sqrt n) =
        ε * θ * (Real.sqrt n * Real.sqrt n) / 2 by ring, hsn]
    rw [hxτ]
    calc (L:ℝ) * s' ≤ 2 * δ * n * s' := mul_le_mul_of_nonneg_right hLr hs'0.le
      _ ≤ 2 * (θ * ε / (4 * s')) * n * s' := by gcongr
      _ = ε * θ * n / 2 := by field_simp; ring
  have hmb := mod_bound (ξ n) (hind n) (hmeas n) (hid n) (hL2 n) (h0 n) s'
    (hσn.trans (le_max_left _ _)) hτ Nmax L hL1 hx hdrift
  have hsub : {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
      (j:ℝ) ≤ T * n ∧ ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ⊆
      {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} := by
    rintro ω ⟨i, j, hij, hj1, hj2, hjx⟩
    refine ⟨i, j, hij, ?_, Nat.le_floor hj2, hjx⟩
    have : (j:ℝ) ≤ i + L := hj1.trans (by linarith [hLr'])
    exact_mod_cast this
  refine (measure_mono hsub).trans (hmb.trans ?_)
  have hjump : (Nmax : ENNReal) * P n {ω | τ < |ξ n 0 ω|} ≤ ENNReal.ofReal (η / 2) := by
    refine le_trans ?_ hJn.le
    rw [← mul_assoc]
    gcongr
    have : Nmax ≤ ⌈T⌉₊ * n := by
      have h1 : (Nmax:ℝ) ≤ ⌈T⌉₊ * n :=
        hNr.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hnpos.le)
      exact_mod_cast h1
    exact_mod_cast this
  set Z := 48 * δ * s' ^ 2 + 16 * θ ^ 2 * s' with hZ
  have hZ0 : 0 < Z := by positivity
  set r := (3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s')) /
    (x / 12) ^ 4 with hr
  have hr0 : 0 ≤ r := by positivity
  have hx4 : (x / 12) ^ 4 = ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4 := by
    rw [hxdef, div_pow, mul_pow, show Real.sqrt n ^ 4 = (Real.sqrt n * Real.sqrt n) ^ 2 by ring, hsn]
  have h2L : ((2 * L : ℕ) : ℝ) ≤ 4 * δ * n := by push_cast; linarith
  have hτ2 : (2 * τ) ^ 2 = 4 * θ ^ 2 * n := by
    rw [hτdef, show (2 * (θ * Real.sqrt n)) ^ 2 = 4 * θ ^ 2 * (Real.sqrt n * Real.sqrt n) by ring,
      hsn]
  have hnum : 3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s') ≤
      (n:ℝ) ^ 2 * δ * Z := by
    rw [hτ2]
    have h0' : 0 ≤ ((2 * L : ℕ) : ℝ) := Nat.cast_nonneg _
    calc 3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * (4 * θ ^ 2 * n * s')
        ≤ 3 * (4 * δ * n) ^ 2 * s' ^ 2 + (4 * δ * n) * (4 * θ ^ 2 * n * s') := by
          gcongr
      _ = (n:ℝ) ^ 2 * δ * Z := by rw [hZ]; ring
  have hrb : r ≤ 12 ^ 4 * δ * Z / ε ^ 4 := by
    calc r = (3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s')) /
          (ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4) := by rw [hr, hx4]
      _ ≤ ((n:ℝ) ^ 2 * δ * Z) / (ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 12 ^ 4 * δ * Z / ε ^ 4 := by field_simp
  have hk : (((Nmax / L + 1 : ℕ)) : ℝ) ≤ 2 * T / δ := by
    push_cast
    have h1 : ((Nmax / L : ℕ) : ℝ) ≤ (Nmax : ℝ) / L := Nat.cast_div_le
    have h2 : (Nmax : ℝ) / L ≤ T / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ0]
      calc (Nmax:ℝ) * δ ≤ T * n * δ := mul_le_mul_of_nonneg_right hNr hδ0.le
        _ = T * (δ * n) := by ring
        _ ≤ T * L := mul_le_mul_of_nonneg_left hLr' hT.le
    have h3 : 1 ≤ T / δ := by rw [le_div_iff₀ hδ0]; linarith
    have : 2 * T / δ = T / δ + T / δ := by ring
    linarith
  have hblock : (((Nmax / L + 1 : ℕ)) : ENNReal) * (3 * ENNReal.ofReal r) ≤
      ENNReal.ofReal (η / 2) := by
    rw [← ENNReal.ofReal_natCast, show (3 : ENNReal) = ENNReal.ofReal 3 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk0 : (0:ℝ) ≤ ((Nmax / L + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (((Nmax / L + 1 : ℕ)) : ℝ) * (3 * r) ≤ (2 * T / δ) * (3 * (12 ^ 4 * δ * Z / ε ^ 4)) :=
          mul_le_mul hk (by linarith) (by positivity) (by positivity)
      _ = K * (48 * δ * s' ^ 2) + K * (16 * θ ^ 2 * s') := by rw [hK, hZ]; field_simp; ring
      _ ≤ K * (48 * (η / (192 * K * s' ^ 2)) * s' ^ 2) + K * (16 * θ ^ 2 * s') := by gcongr
      _ = η / 2 := by rw [hθ2]; field_simp; ring
  calc (Nmax : ENNReal) * P n {ω | τ < |ξ n 0 ω|} +
        (((Nmax / L + 1 : ℕ)) : ENNReal) * (3 * ENNReal.ofReal r)
      ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hjump hblock
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

/-- boundedness in probability of the scaled partial sums up to time `T n`, by chaining the
modulus bound of `rw_tight`. -/
lemma rw_bdd (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (ξ : ∀ n, ℕ → Ωs n → ℝ) (T : ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤ ENNReal.ofReal η)
    (hT : 0 < T) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧
      M * Real.sqrt n ≤ |psum (ξ n) l ω|} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, hev⟩ := hmod 1 one_pos η hη
  set k0 : ℕ := ⌈2 * T / δ⌉₊ with hk0
  refine ⟨k0 + 1, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop ⌈2 / δ⌉₊, eventually_ge_atTop 1] with n hn hn2 hn1
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨l, hlT, hlM⟩
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hδn : 2 ≤ δ * n := by
    have h1 : 2 / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
    rw [div_le_iff₀ hδ] at h1; linarith
  set d : ℕ := ⌊δ * n⌋₊ with hd
  have hd1 : δ * n / 2 ≤ d := by
    have := Nat.lt_floor_add_one (δ * n); linarith
  have hdle : (d:ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hd0 : 0 < d := by
    have : (0:ℝ) < d := by linarith
    exact_mod_cast this
  have chain : ∀ k : ℕ, ∀ l' : ℕ, l' ≤ k * d → (l':ℝ) ≤ T * n →
      |psum (ξ n) l' ω| < (k + 1) * Real.sqrt n := by
    intro k
    induction k with
    | zero =>
      intro l' hl' _
      have : l' = 0 := by simpa using hl'
      subst this
      simp [psum, hsq]
    | succ k ih =>
      intro l' hl' hlT'
      by_cases hle : l' ≤ k * d
      · have := ih l' hle hlT'
        push_cast; linarith
      · push_neg at hle
        have hi := ih (k * d) le_rfl (by
          have : ((k * d : ℕ) : ℝ) ≤ l' := by exact_mod_cast hle.le
          linarith)
        have hstep := hcon (k * d) l' hle.le (by
          have : (l':ℝ) ≤ ((k * d : ℕ) : ℝ) + d := by
            have : l' ≤ k * d + d := by rw [Nat.succ_mul] at hl'; exact hl'
            exact_mod_cast this
          linarith) hlT'
        have := abs_sub_abs_le_abs_sub (psum (ξ n) l' ω) (psum (ξ n) (k * d) ω)
        push_cast
        linarith
  have hlk : l ≤ k0 * d := by
    have h1 : (l:ℝ) ≤ k0 * d := by
      calc (l:ℝ) ≤ T * n := hlT
        _ = (2 * T / δ) * (δ * n / 2) := by field_simp
        _ ≤ k0 * d := mul_le_mul (Nat.le_ceil _) hd1 (by positivity) (by positivity)
    exact_mod_cast h1
  have := chain k0 l hlk hlT
  push_cast at hlM
  linarith

/-- no jump of size `θ √n` before time `T n`, with high probability. -/
lemma jump_small (P : ∀ n, Measure (Ωs n)) (ξ : ∀ n, ℕ → Ωs n → ℝ)
    (hmeas : ∀ n i, Measurable (ξ n i))
    (hid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n))
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0))
    (T : ℝ) (hT : 0 < T) (θ : ℝ) (hθ : 0 < θ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|} ≤
      ENNReal.ofReal η := by
  have h := ENNReal.Tendsto.const_mul (a := ((⌈T⌉₊ + 1 : ℕ) : ENNReal)) (hUI θ hθ)
    (Or.inr (ENNReal.natCast_ne_top _))
  rw [mul_zero] at h
  filter_upwards [(tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.2 hη), eventually_ge_atTop 1]
    with n hn hn1
  refine le_trans ?_ hn.le
  have hsub : {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|} ⊆
      ⋃ l ∈ Finset.range (⌊T * n⌋₊ + 1), {ω | θ * Real.sqrt n < |ξ n l ω|} := by
    rintro ω ⟨l, hl, h'⟩
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.le_floor hl)))) h'
  calc P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|}
      ≤ ∑ l ∈ Finset.range (⌊T * n⌋₊ + 1), P n {ω | θ * Real.sqrt n < |ξ n l ω|} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ l ∈ Finset.range (⌊T * n⌋₊ + 1), P n {ω | θ * Real.sqrt n < |ξ n 0 ω|} :=
        Finset.sum_congr rfl fun l _ =>
          (hid n l).measure_mem_eq (measurableSet_lt measurable_const continuous_abs.measurable)
    _ = ((⌊T * n⌋₊ + 1 : ℕ) : ENNReal) * P n {ω | θ * Real.sqrt n < |ξ n 0 ω|} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((⌈T⌉₊ + 1 : ℕ) : ENNReal) * ((n : ENNReal) * P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) := by
        rw [← mul_assoc]
        gcongr
        have hnpos : (1:ℝ) ≤ n := by exact_mod_cast hn1
        have h1 : ((⌊T * n⌋₊ + 1 : ℕ) : ℝ) ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ) * n := by
          push_cast
          have := Nat.floor_le (by positivity : 0 ≤ T * n)
          have h2 : T * n ≤ ⌈T⌉₊ * n := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by linarith)
          nlinarith
        exact_mod_cast h1

/-- renewal counting function `max {l | F l ≤ b}`. -/
noncomputable def cnt (F : ℕ → ℝ) (b : ℝ) : ℕ := sSup {l | F l ≤ b}

lemma cnt_spec {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b : ℝ} (hb : 0 ≤ b) :
    F (cnt F b) ≤ b ∧ b < F (cnt F b + 1) := by
  obtain ⟨L, hL⟩ := (hFt.eventually (eventually_gt_atTop b)).exists
  have hbdd : BddAbove {l | F l ≤ b} := ⟨L, fun l (hl : F l ≤ b) => by
    by_contra h; push_neg at h; linarith [hFm h]⟩
  have hne : ({l | F l ≤ b} : Set ℕ).Nonempty := ⟨0, by show F 0 ≤ b; rw [hF0]; exact hb⟩
  refine ⟨Nat.sSup_mem hne hbdd, ?_⟩
  by_contra h; push_neg at h
  have := le_csSup hbdd (show F (sSup {l | F l ≤ b} + 1) ≤ b from h)
  unfold cnt at *
  omega

lemma cnt_mono {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    cnt F b ≤ cnt F b' := by
  have h1 := cnt_spec hF0 hFm hFt hb
  have h2 := cnt_spec hF0 hFm hFt (hb.trans hbb)
  have := hFm.lt_iff_lt.1 (lt_of_le_of_lt (h1.1.trans hbb) h2.2)
  omega

/-- scalar modulus tightness on `[0,1]`. -/
def MT (P : ∀ n, Measure (Ωs n)) (X : ∀ n, Ωs n → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε ≤ |X n ω s - X n ω t|} ≤ ENNReal.ofReal η

/-- deterministic renewal inversion: on the good event, the scaled centred counting process has
small oscillation. -/
lemma renewal_core (F W ξv : ℕ → ℝ) (m : ℝ) (hm : 0 < m) (hF : ∀ l, F l = l * m + W l)
    (hξv : ∀ l, F (l + 1) - F l = m + ξv l) (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) (n : ℕ) (hn : 1 ≤ n)
    (μb T M θ εr δr ε : ℝ) (hmμ : m⁻¹ ≤ μb) (hT : T = 2 * μb + 2) (hM0 : 0 < M)
    (hθ0 : 0 ≤ θ) (hδr : 0 < δr)
    (hMω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |W l| < M * Real.sqrt n)
    (hJω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |ξv l| ≤ θ * Real.sqrt n)
    (hRω : ∀ i j : ℕ, i ≤ j → (j:ℝ) ≤ i + δr * n → (j:ℝ) ≤ T * n →
      |W j - W i| < εr * Real.sqrt n)
    (hMn : M ^ 2 < n) (hl3 : 1 + μb * (θ + 2 * M) * Real.sqrt n ≤ δr * n / 2)
    (hsmall : (Real.sqrt n)⁻¹ + μb * εr + μb * θ < ε)
    {s t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) (hts : t ≤ s)
    (hst : s - t ≤ δr / (2 * μb)) :
    |(Real.sqrt n)⁻¹ * ((cnt F (n * s) : ℝ) - m⁻¹ * (n * s)) -
      (Real.sqrt n)⁻¹ * ((cnt F (n * t) : ℝ) - m⁻¹ * (n * t))| < ε := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hμb : 0 < μb := lt_of_lt_of_le (inv_pos.2 hm) hmμ
  have hμm : 1 ≤ μb * m := by
    have := mul_le_mul_of_nonneg_right hmμ hm.le
    rwa [inv_mul_cancel₀ hm.ne'] at this
  have hMlt : M * Real.sqrt n < n := by
    have hM : M < Real.sqrt n := by
      rw [show M = Real.sqrt (M ^ 2) from (Real.sqrt_sq hM0.le).symm]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hMn
    nlinarith
  have hnt : 0 ≤ (n:ℝ) * t := mul_nonneg hnpos.le ht.1
  have hns : 0 ≤ (n:ℝ) * s := mul_nonneg hnpos.le hs.1
  set i := cnt F (n * t) with hi
  set j := cnt F (n * s) with hj
  have hspi := cnt_spec hF0 hFm hFt hnt
  have hspj := cnt_spec hF0 hFm hFt hns
  have hij : i ≤ j := cnt_mono hF0 hFm hFt hnt (mul_le_mul_of_nonneg_left hts hnpos.le)
  -- step A: `j + 1 ≤ T n`
  have hjT : ((j + 1 : ℕ) : ℝ) ≤ T * n := by
    set l0 := ⌈2 * μb * n⌉₊ with hl0
    have hl0r : (l0:ℝ) ≤ 2 * μb * n + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hl0T : (l0:ℝ) ≤ T * n := by rw [hT]; nlinarith
    have hFl0 : (n:ℝ) < F l0 := by
      rw [hF l0]
      have h1 : 2 * μb * n ≤ l0 := Nat.le_ceil _
      have h2 : 2 * (n:ℝ) ≤ l0 * m := by
        calc 2 * (n:ℝ) ≤ 2 * n * (μb * m) := by nlinarith
          _ = (2 * μb * n) * m := by ring
          _ ≤ l0 * m := mul_le_mul_of_nonneg_right h1 hm.le
      have h3 := (abs_lt.1 (hMω l0 hl0T)).1
      linarith
    have hcn := cnt_spec hF0 hFm hFt hnpos.le
    have hjn : j ≤ cnt F n := by
      have := cnt_mono hF0 hFm hFt hns (b' := n) (by nlinarith [hs.2])
      simpa using this
    have hlt : cnt F n < l0 := hFm.lt_iff_lt.1 (lt_of_le_of_lt hcn.1 hFl0)
    have : j + 1 ≤ l0 := by omega
    calc ((j + 1 : ℕ) : ℝ) ≤ l0 := by exact_mod_cast this
      _ ≤ T * n := hl0T
  have hjT' : (j:ℝ) ≤ T * n := by push_cast at hjT; linarith
  have hiT' : (i:ℝ) ≤ T * n := (by exact_mod_cast hij : (i:ℝ) ≤ j).trans hjT'
  -- residuals
  set Rt := (n:ℝ) * t - F i with hRt
  set Rs := (n:ℝ) * s - F j with hRs
  have hRt0 : 0 ≤ Rt := by linarith [hspi.1]
  have hRs0 : 0 ≤ Rs := by linarith [hspj.1]
  have hRt1 : Rt ≤ m + θ * Real.sqrt n := by
    have := hξv i
    have := hJω i hiT'
    linarith [hspi.2, le_abs_self (ξv i)]
  have hRs1 : Rs ≤ m + θ * Real.sqrt n := by
    have := hξv j
    have := hJω j hjT'
    linarith [hspj.2, le_abs_self (ξv j)]
  have hFi := hF i
  have hFj := hF j
  -- the gap `j - i`
  have hWi := hMω i hiT'
  have hWj := hMω j hjT'
  have hgap : (j:ℝ) ≤ i + δr * n := by
    have h1 : ((j:ℝ) - i) * m = (n:ℝ) * (s - t) - (Rs - Rt) - (W j - W i) := by
      rw [hRs, hRt, hFi, hFj]; ring
    have h2 : (n:ℝ) * (s - t) - (Rs - Rt) - (W j - W i) ≤
        (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + m := by
      have := mul_le_mul_of_nonneg_left hst hnpos.le
      have h3 := abs_lt.1 hWi
      have h4 := abs_lt.1 hWj
      have e5 : (θ + 2 * M) * Real.sqrt n = θ * Real.sqrt n + 2 * (M * Real.sqrt n) := by ring
      rw [e5]
      linarith [h3.1, h3.2, h4.1, h4.2]
    have hA0 : 0 ≤ n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n := by positivity
    have h3 : (j:ℝ) - i ≤ μb * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + 1 := by
      have e1 : (j:ℝ) - i = m⁻¹ * (((j:ℝ) - i) * m) := by field_simp
      rw [e1, h1]
      calc m⁻¹ * ((n:ℝ) * (s - t) - (Rs - Rt) - (W j - W i))
          ≤ m⁻¹ * ((n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + m) :=
            mul_le_mul_of_nonneg_left h2 (inv_pos.2 hm).le
        _ = m⁻¹ * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + 1 := by
            rw [mul_add, inv_mul_cancel₀ hm.ne']
        _ ≤ μb * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + 1 := by
            gcongr
    have h4 : μb * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) =
        δr * n / 2 + μb * (θ + 2 * M) * Real.sqrt n := by field_simp
    linarith
  have hW := hRω i j hij hgap hjT'
  have hεr : 0 ≤ εr := by
    by_contra hneg
    push_neg at hneg
    have h1 := (abs_nonneg _).trans_lt hW
    have h2 := mul_neg_of_neg_of_pos hneg hsq
    linarith
  have es : (n:ℝ) * s = j * m + W j + Rs := by rw [hRs, hFj]; ring
  have et : (n:ℝ) * t = i * m + W i + Rt := by rw [hRt, hFi]; ring
  have e : (Real.sqrt n)⁻¹ * ((j:ℝ) - m⁻¹ * (n * s)) - (Real.sqrt n)⁻¹ * ((i:ℝ) - m⁻¹ * (n * t)) =
      -((Real.sqrt n)⁻¹ * m⁻¹) * ((W j - W i) + (Rs - Rt)) := by
    rw [es, et]; field_simp; ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hRd : |Rs - Rt| ≤ m + θ * Real.sqrt n := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hsum : |(W j - W i) + (Rs - Rt)| ≤ εr * Real.sqrt n + (m + θ * Real.sqrt n) :=
    (abs_add_le _ _).trans (add_le_add hW.le hRd)
  calc (Real.sqrt n)⁻¹ * m⁻¹ * |(W j - W i) + (Rs - Rt)|
      ≤ (Real.sqrt n)⁻¹ * m⁻¹ * (εr * Real.sqrt n + (m + θ * Real.sqrt n)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = m⁻¹ * εr + (Real.sqrt n)⁻¹ + m⁻¹ * θ := by field_simp; ring
    _ ≤ μb * εr + (Real.sqrt n)⁻¹ + μb * θ := by
        have h1 := mul_le_mul_of_nonneg_right hmμ hεr
        have h2 := mul_le_mul_of_nonneg_right hmμ hθ0
        linarith
    _ < ε := by linarith

/-- tightness of the scaled centred renewal counting process of a triangular array. -/
lemma renewal_tight (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (v : ∀ n, ℕ → Ωs n → ℝ) (hind : ∀ n, iIndepFun (v n) (P n))
    (hmeas : ∀ n i, Measurable (v n i)) (hid : ∀ n i, IdentDistrib (v n i) (v n 0) (P n) (P n))
    (hL2 : ∀ n, MemLp (v n 0) 2 (P n)) (hpos : ∀ n i ω, 0 < v n i ω)
    (hdiv : ∀ n, ∀ᵐ ω ∂(P n), Tendsto (fun l => psum (v n) l ω) atTop atTop)
    (a : ℝ) (ha : 0 < a) (hm : ∀ᶠ n in atTop, a ≤ ∫ ω, v n 0 ω ∂(P n))
    (σ2 : ℝ) (hσ : ∀ᶠ n in atTop,
      ∫ ω, (v n 0 ω - ∫ ω', v n 0 ω' ∂(P n)) ^ 2 ∂(P n) ≤ σ2)
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |v n 0 ω - ∫ ω', v n 0 ω' ∂(P n)|}) atTop (𝓝 0)) :
    MT P (fun n ω t => (Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
      (∫ ω', v n 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  intro ε hε η hη
  set m : ℕ → ℝ := fun n => ∫ ω', v n 0 ω' ∂(P n) with hmdef
  set ξ : ∀ n, ℕ → Ωs n → ℝ := fun n i => (fun x => x - m n) ∘ v n i with hξdef
  have hξind : ∀ n, iIndepFun (ξ n) (P n) := fun n =>
    (hind n).comp (fun _ x => x - m n) (fun _ => measurable_id.sub_const _)
  have hξm : ∀ n i, Measurable (ξ n i) := fun n i => (measurable_id.sub_const _).comp (hmeas n i)
  have hξid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n) := fun n i =>
    (hid n i).comp (measurable_id.sub_const _)
  have hξL2 : ∀ n, MemLp (ξ n 0) 2 (P n) := fun n => (hL2 n).sub (memLp_const (m n))
  have hξ0 : ∀ n, ∫ ω, ξ n 0 ω ∂(P n) = 0 := by
    intro n
    have := hP n
    show ∫ ω, (v n 0 ω - m n) ∂(P n) = 0
    rw [integral_sub ((hL2 n).integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul]
    exact sub_self _
  have hξσ : ∀ᶠ n in atTop, ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ σ2 := hσ
  have hξUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0) := hUI
  set μb := a⁻¹ with hμbdef
  have hμb : 0 < μb := inv_pos.2 ha
  set T := 2 * μb + 2 with hTdef
  have hT : 0 < T := by positivity
  have hmod := fun ε hε η hη =>
    rw_tight P hP ξ hξind hξm hξid hξL2 hξ0 σ2 hξσ hξUI T hT ε hε η hη
  obtain ⟨M, hM0, hMev⟩ := rw_bdd P hP ξ T hmod hT (η / 4) (by linarith)
  set θ := ε / (8 * μb) with hθdef
  have hθ : 0 < θ := by positivity
  have hJ := jump_small P ξ hξm hξid hξUI T hT θ hθ (η / 4) (by linarith)
  set εr := ε / (4 * μb) with hεrdef
  obtain ⟨δr, hδr, hrw⟩ := hmod εr (by positivity) (η / 4) (by linarith)
  refine ⟨δr / (2 * μb), by positivity, ?_⟩
  set c := μb * (θ + 2 * M) with hc
  have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hl3 : ∀ᶠ n : ℕ in atTop, 1 + c * Real.sqrt n ≤ δr * n / 2 := by
    filter_upwards [hsqt.eventually_ge_atTop (max 1 (2 * (1 + c) / δr)),
      eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    simp only [Function.comp] at hn
    have h1 : 1 ≤ Real.sqrt n := (le_max_left _ _).trans hn
    have h2 : 2 * (1 + c) / δr ≤ Real.sqrt n := (le_max_right _ _).trans hn
    have hc0 : 0 ≤ c := by positivity
    rw [div_le_iff₀ hδr] at h2
    nlinarith
  have hl1 : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ ≤ ε / 4 := by
    filter_upwards [hsqt.eventually_ge_atTop (4 / ε)] with n hn
    simp only [Function.comp] at hn
    rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) hn) (by positivity), inv_div]
    exact hn
  have hl2 : ∀ᶠ n : ℕ in atTop, M ^ 2 < n :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hMev.and (hJ.and (hrw.and (hm.and (hl1.and
    (hl2.and (hl3.and (eventually_ge_atTop 1))))))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hMn, hJn, hrwn, hmn, hl1n, hl2n, hl3n, hn1⟩ := hN n hn
  have := hP n
  have hmpos : 0 < m n := lt_of_lt_of_le ha hmn
  have hmμ : (m n)⁻¹ ≤ μb := inv_anti₀ ha hmn
  set BadM := {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ M * Real.sqrt n ≤ |psum (ξ n) l ω|}
  set BadJ := {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|}
  set BadR := {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δr * n ∧ (j:ℝ) ≤ T * n ∧
    εr * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|}
  set BadD := {ω | ¬ Tendsto (fun l => psum (v n) l ω) atTop atTop}
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δr / (2 * μb) ∧
      ε ≤ |(Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * s) : ℝ) - (m n)⁻¹ * (n * s)) -
        (Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
          (m n)⁻¹ * (n * t))|} ⊆ BadD ∪ (BadM ∪ (BadJ ∪ BadR)) := by
    rintro ω ⟨s, hs, t, ht, hst, hX⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hD, hM', hJ', hR'⟩ := hcon
    have hdivω : Tendsto (fun l => psum (v n) l ω) atTop atTop := by
      by_contra h; exact hD h
    have hMω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |psum (ξ n) l ω| < M * Real.sqrt n := by
      intro l hl; by_contra h; push_neg at h; exact hM' ⟨l, hl, h⟩
    have hJω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |ξ n l ω| ≤ θ * Real.sqrt n := by
      intro l hl; by_contra h; push_neg at h; exact hJ' ⟨l, hl, h⟩
    have hRω : ∀ i j : ℕ, i ≤ j → (j:ℝ) ≤ i + δr * n → (j:ℝ) ≤ T * n →
        |psum (ξ n) j ω - psum (ξ n) i ω| < εr * Real.sqrt n := by
      intro i j h1 h2 h3; by_contra h; push_neg at h; exact hR' ⟨i, j, h1, h2, h3, h⟩
    have hF : ∀ l, psum (v n) l ω = l * m n + psum (ξ n) l ω := by
      intro l
      simp only [psum, hξdef, Function.comp, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    have hξv : ∀ l, psum (v n) (l + 1) ω - psum (v n) l ω = m n + ξ n l ω := by
      intro l
      simp only [psum, Finset.sum_range_succ, hξdef, Function.comp]
      ring
    have hF0 : psum (v n) 0 ω = 0 := by simp [psum]
    have hFm : StrictMono fun l => psum (v n) l ω :=
      strictMono_nat_of_lt_succ fun l => by
        simp only [psum, Finset.sum_range_succ]; linarith [hpos n l ω]
    have hsmall : (Real.sqrt n)⁻¹ + μb * εr + μb * θ < ε := by
      have e1 : μb * εr = ε / 4 := by rw [hεrdef]; field_simp
      have e2 : μb * θ = ε / 8 := by rw [hθdef]; field_simp
      linarith
    rcases le_total t s with hts | hst'
    · have := renewal_core (fun l => psum (v n) l ω) (fun l => psum (ξ n) l ω)
        (fun l => ξ n l ω) (m n) hmpos hF hξv hF0 hFm hdivω n hn1 μb T M θ εr δr ε hmμ rfl hM0
        hθ.le hδr hMω hJω hRω hl2n hl3n hsmall ht hs hts (by rw [abs_le] at hst; linarith)
      linarith
    · have := renewal_core (fun l => psum (v n) l ω) (fun l => psum (ξ n) l ω)
        (fun l => ξ n l ω) (m n) hmpos hF hξv hF0 hFm hdivω n hn1 μb T M θ εr δr ε hmμ rfl hM0
        hθ.le hδr hMω hJω hRω hl2n hl3n hsmall hs ht hst' (by rw [abs_le] at hst; linarith)
      rw [abs_sub_comm] at this
      linarith
  calc _ ≤ P n (BadD ∪ (BadM ∪ (BadJ ∪ BadR))) := measure_mono hsub
    _ ≤ P n BadD + (P n BadM + (P n BadJ + P n BadR)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _))))
    _ ≤ 0 + (ENNReal.ofReal (η / 4) + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4))) :=
        add_le_add (le_of_eq (ae_iff.1 (hdiv n))) (add_le_add hMn (add_le_add hJn hrwn))
    _ ≤ ENNReal.ofReal η := by
        rw [zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        exact ENNReal.ofReal_le_ofReal (by linarith)

lemma MT.add {P : ∀ n, Measure (Ωs n)} {X Y : ∀ n, Ωs n → ℝ → ℝ} (hX : MT P X) (hY : MT P Y) :
    MT P (fun n ω t => X n ω t + Y n ω t) := by
  intro ε hε η hη
  obtain ⟨δ1, hδ1, N1, hN1⟩ := hX (ε / 2) (by linarith) (η / 2) (by linarith)
  obtain ⟨δ2, hδ2, N2, hN2⟩ := hY (ε / 2) (by linarith) (η / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, max N1 N2, fun n hn => ?_⟩
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ min δ1 δ2 ∧
      ε ≤ |(X n ω s + Y n ω s) - (X n ω t + Y n ω t)|} ⊆
      {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ1 ∧
        ε / 2 ≤ |X n ω s - X n ω t|} ∪
      {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ2 ∧
        ε / 2 ≤ |Y n ω s - Y n ω t|} := by
    rintro ω ⟨s, hs, t, ht, hst, hle⟩
    have htri : |(X n ω s + Y n ω s) - (X n ω t + Y n ω t)| ≤
        |X n ω s - X n ω t| + |Y n ω s - Y n ω t| := by
      rw [add_sub_add_comm]; exact abs_add_le _ _
    by_cases h1 : ε / 2 ≤ |X n ω s - X n ω t|
    · left; exact ⟨s, hs, t, ht, hst.trans (min_le_left _ _), h1⟩
    · right
      refine ⟨s, hs, t, ht, hst.trans (min_le_right _ _), ?_⟩
      push_neg at h1; linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add (hN1 n (le_of_max_le_left hn)) (hN2 n (le_of_max_le_right hn))
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

lemma MT.const_mul {P : ∀ n, Measure (Ωs n)} {X : ∀ n, Ωs n → ℝ → ℝ} (hX : MT P X) (c : ℝ) :
    MT P (fun n ω t => c * X n ω t) := by
  intro ε hε η hη
  obtain ⟨δ, hδ, N, hN⟩ := hX (ε / (|c| + 1)) (by positivity) η hη
  refine ⟨δ, hδ, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  rintro ω ⟨s, hs, t, ht, hst, hle⟩
  refine ⟨s, hs, t, ht, hst, ?_⟩
  rw [← mul_sub, abs_mul] at hle
  rw [div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg c, abs_nonneg (X n ω s - X n ω t)]

lemma MT.zero {P : ∀ n, Measure (Ωs n)} : MT P (fun _ _ _ => (0:ℝ)) := by
  intro ε hε η hη
  refine ⟨1, one_pos, 0, fun n _ => ?_⟩
  refine le_trans (measure_mono (show _ ⊆ (∅ : Set (Ωs n)) from ?_)) (by simp)
  rintro ω ⟨s, -, t, -, -, hle⟩
  simp only [sub_self, abs_zero] at hle
  linarith

lemma MT.congr {P : ∀ n, Measure (Ωs n)} {X Y : ∀ n, Ωs n → ℝ → ℝ} (hX : MT P X)
    (h : ∀ n ω, ∀ t ∈ Set.Icc (0:ℝ) 1, X n ω t = Y n ω t) : MT P Y := by
  intro ε hε η hη
  obtain ⟨δ, hδ, N, hN⟩ := hX ε hε η hη
  refine ⟨δ, hδ, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  rintro ω ⟨s, hs, t, ht, hst, hle⟩
  exact ⟨s, hs, t, ht, hst, by rw [h n ω s hs, h n ω t ht]; exact hle⟩

/-- modulus tightness with value `0` at `0` gives boundedness in probability on `[0,1]`. -/
lemma MT_bdd {P : ∀ n, Measure (Ωs n)} {X : ∀ n, Ωs n → ℝ → ℝ} (hT : MT P X)
    (h0 : ∀ n ω, X n ω 0 = 0) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, M < |X n ω s|} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, N, hN⟩ := hT 1 one_pos η hη
  set m : ℕ := ⌈1 / δ⌉₊ + 1 with hm
  have hm0 : (0:ℝ) < m := by positivity
  have hmδ : 1 / (m:ℝ) ≤ δ := by
    rw [div_le_iff₀ hm0]
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m:ℝ) = ⌈1 / δ⌉₊ + 1 := by rw [hm]; push_cast; ring
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  refine ⟨m, hm0, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  intro ω hω
  obtain ⟨s, hs, hlt⟩ := hω
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
  have step : ∀ j : ℕ, j ≤ m → |X n ω (s * j / m)| ≤ j := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hmem : ∀ i : ℕ, i ≤ m → s * i / m ∈ Set.Icc (0:ℝ) 1 := by
        intro i hi
        have hi' : (i:ℝ) ≤ m := by exact_mod_cast hi
        refine ⟨by have := hs.1; positivity, ?_⟩
        rw [div_le_one hm0]
        nlinarith [hs.1, hs.2]
      have hd : |s * ((j + 1 : ℕ) : ℝ) / m - s * j / m| ≤ δ := by
        have e : s * ((j + 1 : ℕ) : ℝ) / m - s * j / m = s * (1 / m) := by
          push_cast; field_simp; ring
        rw [e, abs_of_nonneg (by have := hs.1; positivity)]
        calc s * (1 / (m:ℝ)) ≤ 1 * (1 / m) :=
              mul_le_mul_of_nonneg_right hs.2 (by positivity)
          _ ≤ δ := by rw [one_mul]; exact hmδ
      have hlt1 := hcon _ (hmem (j+1) hj) _ (hmem j (by omega)) hd
      have := abs_sub_abs_le_abs_sub (X n ω (s * ((j + 1 : ℕ) : ℝ) / m)) (X n ω (s * j / m))
      push_cast at this hlt1 ⊢
      linarith
  have := step m le_rfl
  have e : s * (m:ℝ) / m = s := by field_simp
  rw [e] at this
  linarith

/-- the partial-sum walk evaluated at a random time that is bounded and fluid. -/
lemma randtime_tight (P : ∀ n, Measure (Ωs n)) (ξ : ∀ n, ℕ → Ωs n → ℝ)
    (hmod : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤ ENNReal.ofReal η)
    (Nc : ∀ n, Ωs n → ℝ → ℕ)
    (hbd : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, T * n < Nc n ω t} ≤ ENNReal.ofReal η)
    (hfl : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε * n < |(Nc n ω s : ℝ) - Nc n ω t|} ≤ ENNReal.ofReal η) :
    MT P (fun n ω t => (Real.sqrt n)⁻¹ * psum (ξ n) (Nc n ω t) ω) := by
  intro ε hε η hη
  obtain ⟨T, hT, hTev⟩ := hbd (η / 3) (by linarith)
  obtain ⟨δr, hδr, hrw⟩ := hmod T hT ε hε (η / 3) (by linarith)
  obtain ⟨δ, hδ, hfev⟩ := hfl δr hδr (η / 3) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hTev.and (hrw.and (hfev.and (eventually_ge_atTop 1))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3, hn1⟩ := hN n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε ≤ |(Real.sqrt n)⁻¹ * psum (ξ n) (Nc n ω s) ω - (Real.sqrt n)⁻¹ * psum (ξ n) (Nc n ω t) ω|}
      ⊆ {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, T * n < Nc n ω t} ∪
        ({ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δr * n ∧ (j:ℝ) ≤ T * n ∧
          ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ∪
        {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
          δr * n < |(Nc n ω s : ℝ) - Nc n ω t|}) := by
    rintro ω ⟨s, hs, t, ht, hst, hle⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_lt,
      not_le] at hcon
    obtain ⟨hA, hB, hC⟩ := hcon
    have hgap := hC s hs t ht hst
    have hle' : ε * Real.sqrt n ≤ |psum (ξ n) (Nc n ω s) ω - psum (ξ n) (Nc n ω t) ω| := by
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hsq)] at hle
      rwa [le_inv_mul_iff₀ hsq, mul_comm] at hle
    rcases le_total (Nc n ω t) (Nc n ω s) with hts | hts
    · have := hB (Nc n ω t) (Nc n ω s) hts (by
        have := (abs_le.1 hgap).1; have := (abs_le.1 hgap).2; linarith) (hA s hs)
      linarith
    · have := hB (Nc n ω s) (Nc n ω t) hts (by
        have := (abs_le.1 hgap).1; have := (abs_le.1 hgap).2; linarith) (hA t ht)
      rw [abs_sub_comm] at this
      linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (η / 3) + (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) :=
        add_le_add h1 (add_le_add h2 h3)
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring

/-- a counting process whose scaled centred version is modulus-tight is bounded by `T n` and
fluid. -/
lemma bd_fl_of_MT (P : ∀ n, Measure (Ωs n)) (Nc : ∀ n, Ωs n → ℝ → ℕ) (μ : ℕ → ℝ) (μb : ℝ)
    (hμ0 : ∀ n, 0 ≤ μ n) (hμb : ∀ᶠ n in atTop, μ n ≤ μb)
    (hX : MT P (fun n ω t => (Real.sqrt n)⁻¹ * ((Nc n ω t : ℝ) - μ n * (n * t))))
    (h0 : ∀ n ω, Nc n ω 0 = 0) :
    (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, T * n < Nc n ω t} ≤ ENNReal.ofReal η) ∧
    (∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε * n < |(Nc n ω s : ℝ) - Nc n ω t|} ≤ ENNReal.ofReal η) := by
  have hμb0 : ∀ᶠ n in atTop, 0 ≤ μb := hμb.mono fun n h => (hμ0 n).trans h
  constructor
  · intro η hη
    obtain ⟨M, hM, N, hN⟩ := MT_bdd hX (fun n ω => by simp [h0]) η hη
    refine ⟨max μb 0 + M + 1, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1, hμb] with n hn hn1 hμn
    refine le_trans (measure_mono ?_) (hN n hn)
    rintro ω ⟨t, ht, hlt⟩
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hcon
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hsqn : Real.sqrt n ≤ n := by
      have hs1 : 1 ≤ Real.sqrt n := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn1'
      have h1 : Real.sqrt n * 1 ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hs1 hsq.le
      linarith [Real.mul_self_sqrt hnpos.le]
    have h1 := hcon t ht
    have h2 : (Nc n ω t : ℝ) - μ n * (n * t) ≤ M * Real.sqrt n := by
      have := (abs_le.1 h1).2
      rw [inv_mul_le_iff₀ hsq] at this
      linarith
    have h3 : μ n * (n * t) ≤ max μb 0 * n := by
      have : n * t ≤ n := by nlinarith [ht.2]
      calc μ n * (n * t) ≤ μb * (n * t) := mul_le_mul_of_nonneg_right hμn (by nlinarith [ht.1])
        _ ≤ max μb 0 * (n * t) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by nlinarith [ht.1])
        _ ≤ max μb 0 * n := mul_le_mul_of_nonneg_left this (le_max_right _ _)
    nlinarith
  · intro ε hε η hη
    obtain ⟨δ0, hδ0, N, hN⟩ := hX 1 one_pos η hη
    refine ⟨min δ0 (ε / (2 * (max μb 0 + 1))), lt_min hδ0 (by positivity), ?_⟩
    have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1, hμb,
      hsqt.eventually_ge_atTop (4 / ε)] with n hn hn1 hμn hsqn
    refine le_trans (measure_mono ?_) (hN n hn)
    rintro ω ⟨s, hs, t, ht, hst, hlt⟩
    refine ⟨s, hs, t, ht, hst.trans (min_le_left _ _), ?_⟩
    by_contra hcon
    push_neg at hcon
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    simp only [Function.comp] at hsqn
    have e : (Real.sqrt n)⁻¹ * ((Nc n ω s : ℝ) - μ n * (n * s)) -
        (Real.sqrt n)⁻¹ * ((Nc n ω t : ℝ) - μ n * (n * t)) =
        (Real.sqrt n)⁻¹ * (((Nc n ω s : ℝ) - Nc n ω t) - μ n * n * (s - t)) := by ring
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hsq), inv_mul_lt_iff₀ hsq, mul_one] at hcon
    have hst' : |s - t| ≤ ε / (2 * (max μb 0 + 1)) := hst.trans (min_le_right _ _)
    have hdr : |μ n * n * (s - t)| ≤ ε * n / 2 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hμ0 n) hnpos.le)]
      calc μ n * n * |s - t| ≤ (max μb 0 + 1) * n * (ε / (2 * (max μb 0 + 1))) := by
            gcongr
            exact (hμn.trans (le_max_left _ _)).trans (by linarith)
        _ = ε * n / 2 := by field_simp
    have hsq2 : Real.sqrt n ≤ ε * n / 4 := by
      rw [div_le_iff₀ hε] at hsqn
      nlinarith
    have := abs_sub_abs_le_abs_sub ((Nc n ω s : ℝ) - Nc n ω t) (μ n * n * (s - t))
    linarith

/-- the jump condition from a uniform `p`-th moment bound, `p > 2`, for positive variables
with bounded means. -/
lemma hUI_of_moment (P : ∀ n, Measure (Ωs n)) (w : ∀ n, Ωs n → ℝ)
    (hmeas : ∀ n, Measurable (w n)) (hpos : ∀ n ω, 0 < w n ω) (m : ℕ → ℝ)
    (hm0 : ∀ n, 0 ≤ m n) (Bm : ℝ) (hm : ∀ᶠ n in atTop, m n ≤ Bm) (p : ℝ) (hp : 2 < p)
    (C : ℝ) (hC : ∀ᶠ n in atTop, ∫⁻ ω, ENNReal.ofReal (w n ω ^ p) ∂(P n) ≤ ENNReal.ofReal C) :
    ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |w n ω - m n|}) atTop (𝓝 0) := by
  intro θ hθ
  set C' := max C 0 * (2 / θ) ^ p with hC'
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C' * (n:ℝ) ^ (-(p / 2 - 1)))) atTop
      (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop (by linarith : 0 < p / 2 - 1)).comp
      tendsto_natCast_atTop_atTop
    have h2 := (h1.const_mul C')
    rw [mul_zero] at h2
    have := ENNReal.tendsto_ofReal h2
    rwa [ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le) ?_
  have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hm, hC, eventually_ge_atTop 1, hsqt.eventually_ge_atTop (2 * max Bm 0 / θ)]
    with n hmn hCn hn1 hsqn
  simp only [Function.comp] at hsqn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set a := θ * Real.sqrt n / 2 with ha
  have ha0 : 0 < a := by positivity
  have hsub : {ω | θ * Real.sqrt n < |w n ω - m n|} ⊆
      {ω | ENNReal.ofReal (a ^ p) ≤ ENNReal.ofReal (w n ω ^ p)} := by
    intro ω hω
    have hw := hpos n ω
    have h1 : |w n ω - m n| ≤ w n ω + m n := by
      rw [abs_le]; constructor <;> linarith [hm0 n]
    have h2 : m n ≤ a := by
      have : 2 * max Bm 0 ≤ θ * Real.sqrt n := by
        have h := hsqn
        rw [div_le_iff₀ hθ] at h
        linarith
      rw [ha]; linarith [le_max_left Bm 0]
    have h3 : a ≤ w n ω := by
      have : θ * Real.sqrt n = 2 * a := by rw [ha]; ring
      have h4 : θ * Real.sqrt n < |w n ω - m n| := hω
      linarith
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha0.le h3 (by linarith))
  have hmark := meas_ge_le_lintegral_div
    ((ENNReal.measurable_ofReal.comp ((hmeas n).pow_const p)).aemeasurable)
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ha0 p)).ne' ENNReal.ofReal_ne_top
    (μ := P n)
  have hap : a ^ p = (θ / 2) ^ p * (n:ℝ) ^ (p / 2) := by
    rw [ha, show θ * Real.sqrt n / 2 = (θ / 2) * Real.sqrt n by ring,
      Real.mul_rpow (by positivity) hsq.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
    ring_nf
  calc (n : ENNReal) * P n {ω | θ * Real.sqrt n < |w n ω - m n|}
      ≤ (n : ENNReal) * ((∫⁻ ω, ENNReal.ofReal (w n ω ^ p) ∂(P n)) / ENNReal.ofReal (a ^ p)) :=
        by gcongr; exact (measure_mono hsub).trans hmark
    _ ≤ (n : ENNReal) * (ENNReal.ofReal (max C 0) / ENNReal.ofReal (a ^ p)) := by
        gcongr
        exact hCn.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (n * (max C 0 / a ^ p)) := by
        rw [ENNReal.ofReal_mul hnpos.le, ENNReal.ofReal_natCast,
          ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ha0 p)]
    _ = ENNReal.ofReal (C' * (n:ℝ) ^ (-(p / 2 - 1))) := by
        congr 1
        have h1 : (0:ℝ) < (n:ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnpos _
        have h2 : (0:ℝ) < θ ^ p := Real.rpow_pos_of_pos hθ _
        have h3 : (0:ℝ) < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
        rw [hap, hC', show -(p / 2 - 1) = 1 - p / 2 by ring, Real.rpow_sub hnpos, Real.rpow_one,
          Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) hθ.le, Real.div_rpow hθ.le (by norm_num : (0:ℝ) ≤ 2)]
        field_simp

end Tri

end RW

/-! ### Network hookups for `TightPrim` -/

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)} {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω}

lemma indep_v (N : Network K J μP) (k : Fin K) : iIndepFun (fun i => N.v k i) μP := by
  rw [iIndepFun_iff_iIndep]
  exact N.indep.precomp (g := fun i : ℕ => (Sum.inr (Sum.inl (k, i)) : PrimIndex K J))
    (fun a b h => by simpa using h)

lemma indep_u (N : Network K J μP) {k : Fin K} (hk : k ∈ J) :
    iIndepFun (fun i => N.u k i) μP := by
  rw [iIndepFun_iff_iIndep]
  exact N.indep.precomp (g := fun i : ℕ => (Sum.inl (⟨k, hk⟩, i) : PrimIndex K J))
    (fun a b h => by simpa using h)

lemma indep_φ (N : Network K J μP) (k : Fin K) : iIndepFun (fun i => N.φ k i) μP := by
  rw [iIndepFun_iff_iIndep]
  exact N.indep.precomp (g := fun i : ℕ => (Sum.inr (Sum.inr (k, i)) : PrimIndex K J))
    (fun a b h => by simpa using h)

lemma integral_pos_of_pos [IsProbabilityMeasure μP] {f : Ω → ℝ} (hf : ∀ ω, 0 < f ω)
    (hint : Integrable f μP) : 0 < ∫ ω, f ω ∂μP := by
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hf ω).le) hint]
  have : Function.support f = Set.univ := Set.eq_univ_of_forall fun ω => (hf ω).ne'
  rw [this, measure_univ]; exact one_pos

/-- a uniform `p`-th moment bound (`p ≥ 1`) bounds the mean. -/
lemma mean_le_of_moment [IsProbabilityMeasure μP] {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω)
    (hint : Integrable w μP) {p C : ℝ} (hp : 1 ≤ p)
    (hC : ∫⁻ ω, ENNReal.ofReal (w ω ^ p) ∂μP ≤ ENNReal.ofReal C) :
    ∫ ω, w ω ∂μP ≤ 1 + max C 0 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (hw ω).le)
    hint.aestronglyMeasurable]
  have h1 : ∫⁻ ω, ENNReal.ofReal (w ω) ∂μP ≤ ∫⁻ ω, (1 + ENNReal.ofReal (w ω ^ p)) ∂μP := by
    refine lintegral_mono fun ω => ?_
    have hv := hw ω
    have hpp : 0 ≤ w ω ^ p := by positivity
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hpp]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt (w ω) 1 with h | h
    · linarith
    · have : w ω ≤ w ω ^ p := by
        calc _ = w ω ^ (1:ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h.le hp
      linarith
  have h2 : ∫⁻ ω, (1 + ENNReal.ofReal (w ω ^ p)) ∂μP = 1 + ∫⁻ ω, ENNReal.ofReal (w ω ^ p) ∂μP := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have h4 : (1 : ENNReal) + ENNReal.ofReal C ≤ ENNReal.ofReal (1 + max C 0) := by
    rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one]
    exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((h1.trans (h2.le.trans (add_le_add le_rfl hC))).trans h4)

lemma ae_V (N : Network K J μP) (k : Fin K) :
    ∀ᵐ ω ∂μP, Tendsto (fun l => RW.psum (fun i => N.v k i) l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.v k 0) μP := (N.memLp_v k).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.v k i) (N.v k i') μP) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inr (Sum.inl (k, i))) (j := Sum.inr (Sum.inl (k, i')))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.v k 0 ω ∂μP := integral_pos_of_pos (N.pos_v k 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.v k i) hint hind
    (N.ident_v k)] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop, (∫ ω, N.v k 0 ω ∂μP) / 2 <
      (∑ i ∈ Finset.range n, N.v k i ω) / n := hω.eventually (lt_mem_nhds (by linarith))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < (∫ ω, N.v k 0 ω ∂μP) / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have : (0:ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ this] at hn
  simp only [RW.psum]
  linarith

lemma ae_U (N : Network K J μP) {k : Fin K} (hk : k ∈ J) :
    ∀ᵐ ω ∂μP, Tendsto (fun l => RW.psum (fun i => N.u k i) l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.u k 0) μP := (N.memLp_u k hk).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.u k i) (N.u k i') μP) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inl (⟨k, hk⟩, i)) (j := Sum.inl (⟨k, hk⟩, i'))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.u k 0 ω ∂μP := integral_pos_of_pos (N.pos_u k hk 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.u k i) hint hind
    (N.ident_u k hk)] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop, (∫ ω, N.u k 0 ω ∂μP) / 2 <
      (∑ i ∈ Finset.range n, N.u k i ω) / n := hω.eventually (lt_mem_nhds (by linarith))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < (∫ ω, N.u k 0 ω ∂μP) / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have : (0:ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ this] at hn
  simp only [RW.psum]
  linarith

lemma cnt_zero {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F) : RW.cnt F 0 = 0 := by
  have : {l : ℕ | F l ≤ 0} = {0} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hl
      by_contra h0
      have := hFm (Nat.pos_of_ne_zero h0)
      linarith
    · rintro rfl; rw [hF0]
  unfold RW.cnt; rw [this, csSup_singleton]

end NetT

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}

lemma mu_pos' {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (k : Fin K) : 0 < N.mu k := by
  have := N.isProb
  exact inv_pos.2 (integral_pos_of_pos (N.pos_v k 0) ((N.memLp_v k).integrable one_le_two))

lemma lam_pos' {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    {k : Fin K} (hk : k ∈ J) : 0 < N.lam k := by
  have := N.isProb
  simp only [Network.lam, if_pos hk]
  exact inv_pos.2 (integral_pos_of_pos (N.pos_u k hk 0) ((N.memLp_u k hk).integrable one_le_two))

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

/-- the scaled centred service renewal process of station `k` is modulus tight. -/
lemma ren_S (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k : Fin K) :
    RW.MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      ((RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  obtain ⟨ε0, hε0, C, hC⟩ := hA.2.2.2.2.2.2.1
  have hP := fun n => (net n).isProb
  have hmu0 : 0 ≤ mu k :=
    ge_of_tendsto (hA.2.1 k) (Eventually.of_forall fun n => (mu_pos' (net n) k).le)
  have hmeas : ∀ n, Measurable ((net n).v k 0) := fun n => (net n).meas_v k 0
  refine RW.renewal_tight P hP (fun n i => (net n).v k i) (fun n => indep_v (net n) k)
    (fun n i => (net n).meas_v k i) (fun n i => (net n).ident_v k i) (fun n => (net n).memLp_v k)
    (fun n i ω => (net n).pos_v k i ω) (fun n => ae_V (net n) k) (mu k + 1)⁻¹ (by positivity)
    ?_ (s k + 1) ?_ ?_
  · filter_upwards [(hA.2.1 k).eventually (Iio_mem_nhds (by linarith : mu k < mu k + 1))]
      with n hn
    have h1 : ∫ ω', (net n).v k 0 ω' ∂(P n) = ((net n).mu k)⁻¹ := by
      simp only [Network.mu, inv_inv]
    rw [h1]
    exact inv_anti₀ (mu_pos' (net n) k) hn.le
  · filter_upwards [(hA.2.2.2.2.1 k).eventually (Iio_mem_nhds (by linarith : s k < s k + 1))]
      with n hn
    have := (net n).isProb
    have h1 : (net n).sVar k = ∫ ω, ((net n).v k 0 ω - ∫ ω', (net n).v k 0 ω' ∂(P n)) ^ 2 ∂(P n) :=
      variance_eq_integral (hmeas n).aemeasurable
    rw [← h1]; exact hn.le
  · refine RW.hUI_of_moment P (fun n => (net n).v k 0) hmeas (fun n ω => (net n).pos_v k 0 ω)
      (fun n => ∫ ω', (net n).v k 0 ω' ∂(P n))
      (fun n => by
        have := hP n
        exact (integral_pos_of_pos ((net n).pos_v k 0) (((net n).memLp_v k).integrable
          one_le_two)).le) (1 + max C 0) ?_ (2 + ε0) (by linarith) C ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have := hP n
      exact mean_le_of_moment ((net n).pos_v k 0) (((net n).memLp_v k).integrable one_le_two)
        (by linarith) (hC n hn k)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact hC n hn k

end NetT

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

/-- the scaled centred arrival renewal process of station `k ∈ 𝒥` is modulus tight. -/
lemma ren_A (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) {k : Fin K}
    (hk : k ∈ J) :
    RW.MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      ((RW.cnt (fun l => RW.psum (fun i => (net n).u k i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).u k 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  obtain ⟨ε0, hε0, C, hC⟩ := hA.2.2.2.2.2.2.2
  have hP := fun n => (net n).isProb
  have hlam0 : 0 ≤ lam k :=
    ge_of_tendsto (hA.2.2.1 k) (Eventually.of_forall fun n => (lam_pos' (net n) hk).le)
  have hmeas : ∀ n, Measurable ((net n).u k 0) := fun n => (net n).meas_u k hk 0
  refine RW.renewal_tight P hP (fun n i => (net n).u k i) (fun n => indep_u (net n) hk)
    (fun n i => (net n).meas_u k hk i) (fun n i => (net n).ident_u k hk i)
    (fun n => (net n).memLp_u k hk)
    (fun n i ω => (net n).pos_u k hk i ω) (fun n => ae_U (net n) hk) (lam k + 1)⁻¹ (by positivity)
    ?_ (a k + 1) ?_ ?_
  · filter_upwards [(hA.2.2.1 k).eventually (Iio_mem_nhds (by linarith : lam k < lam k + 1))]
      with n hn
    have h1 : ∫ ω', (net n).u k 0 ω' ∂(P n) = ((net n).lam k)⁻¹ := by
      simp only [Network.lam, if_pos hk, inv_inv]
    rw [h1]
    exact inv_anti₀ (lam_pos' (net n) hk) hn.le
  · filter_upwards [(hA.2.2.2.1 k hk).eventually (Iio_mem_nhds (by linarith : a k < a k + 1))]
      with n hn
    have := (net n).isProb
    have h1 : (net n).aVar k = ∫ ω, ((net n).u k 0 ω - ∫ ω', (net n).u k 0 ω' ∂(P n)) ^ 2 ∂(P n) :=
      variance_eq_integral (hmeas n).aemeasurable
    rw [← h1]; exact hn.le
  · refine RW.hUI_of_moment P (fun n => (net n).u k 0) hmeas (fun n ω => (net n).pos_u k hk 0 ω)
      (fun n => ∫ ω', (net n).u k 0 ω' ∂(P n))
      (fun n => by
        have := hP n
        exact (integral_pos_of_pos ((net n).pos_u k hk 0) (((net n).memLp_u k hk).integrable
          one_le_two)).le) (1 + max C 0) ?_ (2 + ε0) (by linarith) C ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have := hP n
      exact mean_le_of_moment ((net n).pos_u k hk 0)
        (((net n).memLp_u k hk).integrable one_le_two) (by linarith) (hC n hn k hk)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact hC n hn k hk

lemma routeVec_mem (r : Fin (K + 1)) (j : Fin K) : 0 ≤ routeVec r j ∧ routeVec r j ≤ 1 := by
  unfold routeVec; split_ifs <;> norm_num

lemma routing_mem {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (k j : Fin K) : 0 ≤ N.routing k j ∧ N.routing k j ≤ 1 := by
  have := N.isProb
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

lemma routeVec_integral {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (k j : Fin K) : ∫ ω, routeVec (N.φ k 0 ω) j ∂μP = N.routing k j := by
  have hs : MeasurableSet {ω | N.φ k 0 ω = j.succ} :=
    (N.meas_φ k 0) (measurableSet_singleton _)
  have e : (fun ω => routeVec (N.φ k 0 ω) j) = Set.indicator {ω | N.φ k 0 ω = j.succ} 1 := by
    funext ω
    simp only [routeVec, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [e, integral_indicator_one hs]
  rfl

/-- the scaled centred routing walk of station `k`, coordinate `j`, run at the service count, is
modulus tight. -/
lemma route_walk (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k j : Fin K) :
    RW.MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      RW.psum (fun i ω => routeVec ((net n).φ k i ω) j - R k j)
        (RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t)) ω) := by
  have hP := fun n => (net n).isProb
  have hRm : ∀ n, R k j = (net n).routing k j := fun n => by rw [hA.1 n]
  have hg : Measurable fun r : Fin (K + 1) => routeVec r j - R k j := measurable_of_finite _
  set ξ : ∀ n, ℕ → Ωs n → ℝ := fun n i => (fun r => routeVec r j - R k j) ∘ (net n).φ k i
    with hξ
  have hξind : ∀ n, iIndepFun (ξ n) (P n) := fun n =>
    (indep_φ (net n) k).comp (fun _ r => routeVec r j - R k j) (fun _ => hg)
  have hξm : ∀ n i, Measurable (ξ n i) := fun n i => hg.comp ((net n).meas_φ k i)
  have hξid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n) := fun n i =>
    ((net n).ident_φ k i).comp hg
  have hξb : ∀ n i ω, |ξ n i ω| ≤ 1 := by
    intro n i ω
    have h1 := routeVec_mem ((net n).φ k i ω) j
    have h2 := routing_mem (net n) k j
    rw [← hRm n] at h2
    simp only [hξ, Function.comp]
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hξL2 : ∀ n, MemLp (ξ n 0) 2 (P n) := fun n =>
    MemLp.of_bound (hξm n 0).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hξb n 0 ω)
  have hξ0 : ∀ n, ∫ ω, ξ n 0 ω ∂(P n) = 0 := by
    intro n
    have := hP n
    have hi : Integrable (fun ω => routeVec ((net n).φ k 0 ω) j) (P n) :=
      Integrable.of_bound (measurable_of_finite (fun r : Fin (K + 1) => routeVec r j) |>.comp
        ((net n).meas_φ k 0)).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          have := routeVec_mem ((net n).φ k 0 ω) j
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    show ∫ ω, (routeVec ((net n).φ k 0 ω) j - R k j) ∂(P n) = 0
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul,
      routeVec_integral, hRm n, sub_self]
  have hξσ : ∀ᶠ n in atTop, ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ 1 := Eventually.of_forall fun n => by
    have := hP n
    calc ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ ∫ ω, (1:ℝ) ∂(P n) := by
          refine integral_mono (hξL2 n).integrable_sq (integrable_const _) fun ω => ?_
          have := hξb n 0 ω
          show ξ n 0 ω ^ 2 ≤ 1
          rw [← sq_abs]; nlinarith [abs_nonneg (ξ n 0 ω)]
      _ = 1 := by simp
  have hξUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0) := by
    intro θ hθ
    refine tendsto_const_nhds.congr' ?_
    have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsqt.eventually_ge_atTop (1 / θ)] with n hn
    simp only [Function.comp] at hn
    have h1 : 1 ≤ θ * Real.sqrt n := by rwa [div_le_iff₀ hθ, mul_comm] at hn
    have : {ω | θ * Real.sqrt n < |ξ n 0 ω|} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      linarith [hξb n 0 ω]
    rw [this, measure_empty, mul_zero]
  have hmod : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |RW.psum (ξ n) j ω - RW.psum (ξ n) i ω|} ≤ ENNReal.ofReal η :=
    fun T hT ε hε η hη => RW.rw_tight P hP ξ hξind hξm hξid hξL2 hξ0 1 hξσ hξUI T hT ε hε η hη
  have hmu0 : 0 ≤ mu k :=
    ge_of_tendsto (hA.2.1 k) (Eventually.of_forall fun n => (mu_pos' (net n) k).le)
  have hX := ren_S net hA k
  have hbf := RW.bd_fl_of_MT P
    (fun n ω t => RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t))
    (fun n => (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹) (mu k + 1)
    (fun n => (mu_pos' (net n) k).le)
    ((hA.2.1 k).eventually (Iic_mem_nhds (by linarith : mu k < mu k + 1))) hX
    (fun n ω => by
      simp only [mul_zero]
      exact cnt_zero (by simp [RW.psum])
        (strictMono_nat_of_lt_succ fun l => by
          simp only [RW.psum, Finset.sum_range_succ]; linarith [(net n).pos_v k l ω]))
  exact RW.randtime_tight P ξ hmod _ hbf.1 hbf.2

end NetT

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

/-- vector modulus tightness (the body of `P5.ModTight`) from coordinatewise tightness. -/
lemma vec_of_coords {X : ∀ n, Ωs n → ℝ → Fin K → ℝ}
    (h : ∀ j, RW.MT P (fun n ω t => X n ω t j)) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖X n ω s - X n ω t‖} ≤ ENNReal.ofReal η := by
  intro ε hε η hη
  rcases (Finset.univ (α := Fin K)).eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, 0, fun n _ => ?_⟩
    have hE : IsEmpty (Fin K) := ⟨fun i => by simpa [hK] using Finset.mem_univ i⟩
    have : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ 1 ∧
        ε ≤ ‖X n ω s - X n ω t‖} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro s _ t _ _
      rw [Subsingleton.elim (X n ω s - X n ω t) 0, norm_zero]; exact hε
    rw [this, measure_empty]; exact bot_le
  have hK0 : (0:ℝ) < K := by
    have : 0 < K := Fin.pos_iff_nonempty.2 (Finset.univ_nonempty_iff.1 hK)
    exact_mod_cast this
  choose δj hδj Nj hNj using fun j => h j ε hε (η / K) (by positivity)
  refine ⟨Finset.univ.inf' hK δj, (Finset.lt_inf'_iff hK).2 fun j _ => hδj j,
    Finset.univ.sup Nj, fun n hn => ?_⟩
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1,
      |s - t| ≤ Finset.univ.inf' hK δj ∧ ε ≤ ‖X n ω s - X n ω t‖} ⊆
      ⋃ j, {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δj j ∧
        ε ≤ |X n ω s j - X n ω t j|} := by
    rintro ω ⟨s, hs, t, ht, hst, hle⟩
    obtain ⟨j, hj⟩ : ∃ j, ε ≤ |X n ω s j - X n ω t j| := by
      by_contra hcon
      push_neg at hcon
      have : ‖X n ω s - X n ω t‖ < ε := (pi_norm_lt_iff hε).2 fun j => by
        rw [Pi.sub_apply, Real.norm_eq_abs]; exact hcon j
      linarith
    exact Set.mem_iUnion.2 ⟨j, s, hs, t, ht,
      hst.trans (Finset.inf'_le _ (Finset.mem_univ j)), hj⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ j, P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δj j ∧
        ε ≤ |X n ω s j - X n ω t j|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin K, ENNReal.ofReal (η / K) :=
        Finset.sum_le_sum fun j _ => hNj j n ((Finset.le_sup (Finset.mem_univ j)).trans hn)
    _ = ENNReal.ofReal η := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        field_simp

lemma Stilde_coord (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    (hR : ∀ n, (net n).routing = R) (k j : Fin K) (n : ℕ) (ω : Ωs n) (t : ℝ) :
    diffScale n (fun t => (net n).Stilde k t ω) t j =
      (Real.sqrt n)⁻¹ * RW.psum (fun i ω => routeVec ((net n).φ k i ω) j - R k j)
        (RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t)) ω +
      (R k j - if k = j then 1 else 0) * ((Real.sqrt n)⁻¹ *
        ((RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t) : ℝ) -
          (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  have hS : (net n).S k (n * t) ω =
      RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t) := rfl
  have hmu : (net n).mu k = (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ := rfl
  simp only [diffScale, Network.Stilde, Network.Shat, Pi.smul_apply, Pi.sub_apply,
    Finset.sum_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply, hR n,
    hS, ← hmu]
  simp only [RW.psum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  by_cases hkj : k = j
  · subst hkj; simp; ring
  · simp [hkj, Ne.symm hkj]; ring

lemma Atilde_coord (net : ∀ n, Network K J (P n)) (j : Fin K) (hj : j ∈ J) (n : ℕ)
    (ω : Ωs n) (t : ℝ) :
    diffScale n (fun t => (net n).Atilde t ω) t j = (Real.sqrt n)⁻¹ *
      ((RW.cnt (fun l => RW.psum (fun i => (net n).u j i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).u j 0 ω' ∂(P n))⁻¹ * (n * t)) := by
  simp only [diffScale, Network.Atilde, Network.Avec, Network.A, Network.lam, if_pos hj,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  show (Real.sqrt n)⁻¹ * ((RW.cnt (fun l => RW.psum (fun i => (net n).u j i) l ω) (n * t) : ℝ) -
    (n * t) * (∫ ω', (net n).u j 0 ω' ∂(P n))⁻¹) = _
  ring

lemma Atilde_coord0 (net : ∀ n, Network K J (P n)) (j : Fin K) (hj : j ∉ J) (n : ℕ)
    (ω : Ωs n) (t : ℝ) : diffScale n (fun t => (net n).Atilde t ω) t j = 0 := by
  simp [diffScale, Network.Atilde, Network.Avec, Network.A, Network.lam, hj]

lemma tight_A (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun t => (net n).Atilde t ω) s -
          diffScale n (fun t => (net n).Atilde t ω) t‖} ≤ ENNReal.ofReal η := by
  refine vec_of_coords (X := fun n ω => diffScale n (fun t => (net n).Atilde t ω)) fun j => ?_
  by_cases hj : j ∈ J
  · exact (ren_A net hA hj).congr fun n ω t _ => (Atilde_coord net j hj n ω t).symm
  · exact RW.MT.zero.congr fun n ω t _ => (Atilde_coord0 net j hj n ω t).symm

lemma tight_S (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k : Fin K) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun t => (net n).Stilde k t ω) s -
          diffScale n (fun t => (net n).Stilde k t ω) t‖} ≤ ENNReal.ofReal η := by
  refine vec_of_coords (X := fun n ω => diffScale n (fun t => (net n).Stilde k t ω)) fun j => ?_
  exact ((route_walk net hA k j).add ((ren_S net hA k).const_mul
    (R k j - if k = j then 1 else 0))).congr
    fun n ω t _ => (Stilde_coord net hA.1 k j n ω t).symm

end NetT

open MeasureTheory Reiman84.QueueLength in
theorem solution {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c) :
    (∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |u - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun r => (net n).Atilde r ω) u -
          diffScale n (fun r => (net n).Atilde r ω) t‖} ≤ ENNReal.ofReal η) ∧
    ∀ k : Fin K, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |u - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun r => (net n).Stilde k r ω) u -
          diffScale n (fun r => (net n).Stilde k r ω) t‖} ≤ ENNReal.ofReal η := by
  exact ⟨NetT.tight_A net hA, fun k => NetT.tight_S net hA k⟩
