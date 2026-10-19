-- Prove2me | solution 1 for Reiman84.QueueLength.scaled_netput_fdd_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T13:25:02.239317+00:00
-- url     : https://prove2.me/submissions/5b5d412d-a08d-442b-a623-0081a81de668

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
          linarith
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
    have := mul_lt_mul_of_pos_right hM hsq
    linarith [hsn]
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
    have hl0T : (l0:ℝ) ≤ T * n := by rw [hT]; linarith
    have hFl0 : (n:ℝ) < F l0 := by
      rw [hF l0]
      have h1 : 2 * μb * n ≤ l0 := Nat.le_ceil _
      have h2 : 2 * (n:ℝ) ≤ l0 * m := by
        calc 2 * (n:ℝ) ≤ 2 * n * (μb * m) := by
              have := mul_le_mul_of_nonneg_left hμm (by positivity : (0:ℝ) ≤ 2 * n)
              linarith
          _ = (2 * μb * n) * m := by ring
          _ ≤ l0 * m := mul_le_mul_of_nonneg_right h1 hm.le
      have h3 := (abs_lt.1 (hMω l0 hl0T)).1
      linarith
    have hcn := cnt_spec hF0 hFm hFt hnpos.le
    have hjn : j ≤ cnt F n := by
      have := cnt_mono hF0 hFm hFt hns (b' := n) (mul_le_of_le_one_right hnpos.le hs.2)
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
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (n:ℝ))
    have e : Real.sqrt n * δr * Real.sqrt n = δr * n := by rw [mul_right_comm, hsn, mul_comm]
    have h4 : c * 1 ≤ c * Real.sqrt n := mul_le_mul_of_nonneg_left h1 hc0
    linarith
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

end NetT

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

end NetT

/-! measurability of the netput at fixed times (copied from 755ffe80_meas.lean). -/

namespace MeasQ

open Filter Topology MeasureTheory Set

variable {K : ℕ}


/-! ### counting functions -/

/-- `max {l | F l ≤ b}` (junk `0` when unbounded), as in `Network.A`, `Network.S`. -/
noncomputable def cnt (F : ℕ → ℝ) (b : ℝ) : ℕ := sSup {l | F l ≤ b}

lemma nat_sSup_eq_iff (S : Set ℕ) (j : ℕ) :
    sSup S = j ↔ ((∀ a ∈ S, a ≤ j) ∧ (j = 0 ∨ j ∈ S)) ∨ (j = 0 ∧ ∀ n : ℕ, ∃ a ∈ S, n < a) := by
  by_cases hb : BddAbove S
  · have hnot : ¬ ∀ n : ℕ, ∃ a ∈ S, n < a := by
      intro h
      obtain ⟨M, hM⟩ := hb
      obtain ⟨a, ha, hMa⟩ := h M
      exact absurd (hM ha) (not_le.2 hMa)
    simp only [hnot, and_false, or_false]
    rcases S.eq_empty_or_nonempty with he | hne
    · subst he; simp [eq_comm]
    · constructor
      · rintro rfl; exact ⟨fun a ha => le_csSup hb ha, Or.inr (Nat.sSup_mem hne hb)⟩
      · rintro ⟨hub, h0 | hj⟩
        · subst h0; exact Nat.le_zero.1 (csSup_le hne hub)
        · exact le_antisymm (csSup_le hne hub) (le_csSup hb hj)
  · rw [Nat.sSup_of_not_bddAbove hb]
    have hall : ∀ n : ℕ, ∃ a ∈ S, n < a := by
      intro n; by_contra h; push_neg at h; exact hb ⟨n, fun a ha => h a ha⟩
    have hnub : ¬ ∀ a ∈ S, a ≤ j := fun h => hb ⟨j, h⟩
    simp only [hnub, false_and, false_or, hall, implies_true, and_true]
    exact eq_comm

lemma meas_cnt {Ω' : Type*} [MeasurableSpace Ω'] (F : ℕ → Ω' → ℝ) (hF : ∀ l, Measurable (F l)) :
    Measurable (fun p : ℝ × Ω' => cnt (fun l => F l p.2) p.1) := by
  have hle : ∀ a, Measurable fun p : ℝ × Ω' => F a p.2 ≤ p.1 := fun a =>
    measurableSet_setOfPred.1 (measurableSet_le ((hF a).comp measurable_snd) measurable_fst)
  refine measurable_to_countable' fun j => ?_
  have hset : (fun p : ℝ × Ω' => cnt (fun l => F l p.2) p.1) ⁻¹' {j} =
      {p | ((∀ a, F a p.2 ≤ p.1 → a ≤ j) ∧ (j = 0 ∨ F j p.2 ≤ p.1)) ∨
        (j = 0 ∧ ∀ n : ℕ, ∃ a, F a p.2 ≤ p.1 ∧ n < a)} := by
    ext p; exact nat_sSup_eq_iff _ j
  rw [hset]
  exact measurableSet_setOfPred.2
    (((Measurable.forall fun a => (hle a).imp measurable_const).and
      (measurable_const.or (hle j))).or
      (measurable_const.and (Measurable.forall fun n =>
        Measurable.exists fun a => (hle a).and measurable_const)))


section Net

open Reiman84.QueueLength ProbabilityTheory

variable {J : Finset (Fin K)} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (N : Network K J P)

lemma U_meas {k : Fin K} (hk : k ∈ J) (l : ℕ) : Measurable (N.U k l) := by
  show Measurable fun ω => ∑ i ∈ Finset.range l, N.u k i ω
  exact Finset.measurable_sum _ fun i _ => N.meas_u k hk i

lemma V_meas (k : Fin K) (l : ℕ) : Measurable (N.V k l) := by
  show Measurable fun ω => ∑ i ∈ Finset.range l, N.v k i ω
  exact Finset.measurable_sum _ fun i _ => N.meas_v k i

lemma U_props {k : Fin K} (hk : k ∈ J) (ω : Ω) :
    N.U k 0 ω = 0 ∧ StrictMono (fun l => N.U k l ω) := by
  refine ⟨by simp [Network.U], strictMono_nat_of_lt_succ fun l => ?_⟩
  simp only [Network.U, Finset.sum_range_succ]
  linarith [N.pos_u k hk l ω]

lemma V_props (k : Fin K) (ω : Ω) : N.V k 0 ω = 0 ∧ StrictMono (fun l => N.V k l ω) := by
  refine ⟨by simp [Network.V], strictMono_nat_of_lt_succ fun l => ?_⟩
  simp only [Network.V, Finset.sum_range_succ]
  linarith [N.pos_v k l ω]

lemma A_eq {k : Fin K} (hk : k ∈ J) (t : ℝ) (ω : Ω) :
    N.A k t ω = cnt (fun l => N.U k l ω) t := by
  simp only [Network.A, if_pos hk, cnt]

lemma Avec_jm : Measurable (fun p : ℝ × Ω => N.Avec p.1 p.2) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k ∈ J
  · simp only [Network.Avec, A_eq N hk]
    exact measurable_from_nat.comp (meas_cnt (fun l ω => N.U k l ω) (U_meas N hk))
  · simp only [Network.Avec, Network.A, if_neg hk, Nat.cast_zero]
    exact measurable_const

/-- `Ŝ_k` as a function of the number of completed services. -/
noncomputable def shG (k : Fin K) (q : Ω × ℕ) : Fin K → ℝ :=
  (∑ i ∈ Finset.range q.2, routeVec (N.φ k i q.1)) - (q.2 : ℝ) • Pi.single k 1

lemma shG_meas (k : Fin K) : Measurable (shG N k) := by
  refine measurable_from_prod_countable_left fun j => ?_
  simp only [shG]
  exact (Finset.measurable_sum _ fun i _ =>
    (Measurable.of_discrete (f := (routeVec : Fin (K + 1) → Fin K → ℝ))).comp
      (N.meas_φ k i)).sub measurable_const

lemma Shat_eq (k : Fin K) (y : ℝ) (ω : Ω) :
    N.Shat k y ω = shG N k (ω, cnt (fun l => N.V k l ω) y) := rfl

lemma Shat_jm (k : Fin K) : Measurable (fun p : ℝ × Ω => N.Shat k p.1 p.2) := by
  simp only [Shat_eq]
  exact (shG_meas N k).comp
    (measurable_snd.prodMk (meas_cnt (fun l ω => N.V k l ω) (V_meas N k)))

/-- the arrival path and the service vectors at the sample point `ω`. -/
noncomputable def aω (ω : Ω) : ℝ → Fin K → ℝ := fun t => N.Avec t ω
noncomputable def shω (ω : Ω) : Fin K → ℝ → Fin K → ℝ := fun k y => N.Shat k y ω

lemma aω_meas (ω : Ω) : Measurable (aω N ω) := by
  have h : Measurable ((fun p : ℝ × Ω => N.Avec p.1 p.2) ∘ fun t : ℝ => (t, ω)) :=
    (Avec_jm N).comp measurable_prodMk_right
  exact h

lemma shω_meas (ω : Ω) (k : Fin K) : Measurable (shω N ω k) := by
  have h : Measurable ((fun p : ℝ × Ω => N.Shat k p.1 p.2) ∘ fun t : ℝ => (t, ω)) :=
    (Shat_jm N k).comp measurable_prodMk_right
  exact h

lemma Avec_sec (t : ℝ) : Measurable fun ω => N.Avec t ω := by
  have h : Measurable ((fun p : ℝ × Ω => N.Avec p.1 p.2) ∘ fun ω : Ω => (t, ω)) :=
    (Avec_jm N).comp measurable_prodMk_left
  exact h

lemma Shat_sec (k : Fin K) (t : ℝ) : Measurable fun ω => N.Shat k t ω := by
  have h : Measurable ((fun p : ℝ × Ω => N.Shat k p.1 p.2) ∘ fun ω : Ω => (t, ω)) :=
    (Shat_jm N k).comp measurable_prodMk_left
  exact h


lemma X_meas (t : ℝ) : Measurable fun ω => N.X t ω := by
  simp only [Network.X]
  exact (Avec_sec N t).add (Finset.measurable_sum _ fun k _ => Shat_sec N k t)

end Net

end MeasQ

/-! ## F1: triangular-array fdd CLT (from 755ffe80_fdd1.lean) -/

namespace FddA

open Filter Topology MeasureTheory ProbabilityTheory Matrix Reiman84.QueueLength

lemma norm_pow_sub_pow_le' {a c : ℂ} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) (b : ℕ) :
    ‖a ^ b - c ^ b‖ ≤ b * ‖a - c‖ := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h : a ^ (b + 1) - c ^ (b + 1) = a * (a ^ b - c ^ b) + (a - c) * c ^ b := by ring
    rw [h]
    have hcb : ‖c‖ ^ b ≤ 1 := pow_le_one₀ (norm_nonneg _) hc
    calc ‖a * (a ^ b - c ^ b) + (a - c) * c ^ b‖
        ≤ ‖a * (a ^ b - c ^ b)‖ + ‖(a - c) * c ^ b‖ := norm_add_le _ _
      _ = ‖a‖ * ‖a ^ b - c ^ b‖ + ‖a - c‖ * ‖c‖ ^ b := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ 1 * (b * ‖a - c‖) + ‖a - c‖ * 1 := by
          gcongr
      _ = ((b + 1 : ℕ) : ℝ) * ‖a - c‖ := by push_cast; ring

lemma pow_exp_close {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : ‖z - 1‖ ≤ 1) (b : ℕ) :
    ‖z ^ b - Complex.exp (b * (z - 1))‖ ≤ b * ‖z - 1‖ ^ 2 := by
  have he : ‖Complex.exp (z - 1)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.2
    have : (z - 1).re = z.re - 1 := by simp
    rw [this]
    linarith [Complex.re_le_norm z]
  rw [Complex.exp_nat_mul]
  calc ‖z ^ b - Complex.exp (z - 1) ^ b‖ ≤ b * ‖z - Complex.exp (z - 1)‖ :=
        norm_pow_sub_pow_le' hz he b
    _ ≤ b * ‖z - 1‖ ^ 2 := by
        gcongr
        have := Complex.norm_exp_sub_one_sub_id_le hz1
        have h2 : z - Complex.exp (z - 1) = -(Complex.exp (z - 1) - 1 - (z - 1)) := by ring
        rw [h2, norm_neg]; exact this

/-- `zₙ^{bₙ} → exp w` when `bₙ (zₙ - 1) → w`, `zₙ → 1`, `‖zₙ‖ ≤ 1`. -/
lemma tendsto_pow_of_mul {z : ℕ → ℂ} {b : ℕ → ℕ} {w : ℂ} (hz : ∀ n, ‖z n‖ ≤ 1)
    (h1 : Tendsto z atTop (𝓝 1))
    (hw : Tendsto (fun n => (b n : ℂ) * (z n - 1)) atTop (𝓝 w)) :
    Tendsto (fun n => z n ^ b n) atTop (𝓝 (Complex.exp w)) := by
  have hexp : Tendsto (fun n => Complex.exp ((b n : ℂ) * (z n - 1))) atTop
      (𝓝 (Complex.exp w)) :=
    (Complex.continuous_exp.tendsto w).comp hw
  have hsmall : Tendsto (fun n => ‖z n - 1‖) atTop (𝓝 0) := by
    have := (h1.sub_const 1).norm
    simpa using this
  have hbound : Tendsto (fun n => ‖(b n : ℂ) * (z n - 1)‖ * ‖z n - 1‖) atTop (𝓝 0) := by
    have := hw.norm.mul hsmall
    simpa using this
  have hdiff : Tendsto (fun n => z n ^ b n - Complex.exp ((b n : ℂ) * (z n - 1))) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hsmall.eventually (ge_mem_nhds zero_lt_one)] with n hn
    calc ‖z n ^ b n - Complex.exp (↑(b n) * (z n - 1))‖ ≤ b n * ‖z n - 1‖ ^ 2 :=
          pow_exp_close (hz n) hn _
      _ = ‖(b n : ℂ) * (z n - 1)‖ * ‖z n - 1‖ := by
          rw [norm_mul, Complex.norm_natCast]; ring
  have h3 : (fun n => z n ^ b n) = fun n => (z n ^ b n - Complex.exp ((b n : ℂ) * (z n - 1)))
      + Complex.exp ((b n : ℂ) * (z n - 1)) := by
    funext n; ring
  rw [h3, ← zero_add (Complex.exp w)]
  exact hdiff.add hexp

/-- pointwise third-order bound for `exp (i x)`. -/
lemma exp_I_taylor (x : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖Complex.exp (Complex.I * x) - (1 + Complex.I * x - (x ^ 2 / 2 : ℝ))‖ ≤
      4 * |x| ^ (2 + ε) := by
  rcases le_or_gt |x| 1 with hx | hx
  · have hnx : ‖Complex.I * (x : ℂ)‖ = |x| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := Complex.exp_bound (x := Complex.I * x) (by rw [hnx]; exact hx)
      (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, (Complex.I * (x : ℂ)) ^ m / (m.factorial : ℂ) =
        1 + Complex.I * x - ((x ^ 2 / 2 : ℝ) : ℂ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero,
        pow_one, Nat.cast_one, div_one, zero_add, mul_pow, Complex.I_sq]
      push_cast
      ring
    rw [hsum, hnx] at hb
    have h3 : |x| ^ 3 ≤ |x| ^ (2 + ε) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg x) hx (by linarith) (by push_cast; linarith)
    have hc : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      norm_num [Nat.factorial]
    calc _ ≤ |x| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹) := hb
      _ ≤ |x| ^ 3 * 1 := by gcongr
      _ ≤ 4 * |x| ^ (2 + ε) := by
          have := Real.rpow_nonneg (abs_nonneg x) (2 + ε)
          linarith
  · have h2 : x ^ 2 ≤ |x| ^ (2 + ε) := by
      rw [← sq_abs, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by push_cast; linarith)
    have hx2 : |x| ≤ x ^ 2 := by
      rw [← sq_abs]; nlinarith
    have hn1 : ‖Complex.exp (Complex.I * x)‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
    calc _ ≤ ‖Complex.exp (Complex.I * x)‖ + ‖(1 : ℂ)‖ + ‖Complex.I * (x : ℂ)‖ +
          ‖((x ^ 2 / 2 : ℝ) : ℂ)‖ := by
          have e : Complex.exp (Complex.I * x) - (1 + Complex.I * x - ((x ^ 2 / 2 : ℝ) : ℂ)) =
              Complex.exp (Complex.I * x) - 1 - Complex.I * x + ((x ^ 2 / 2 : ℝ) : ℂ) := by ring
          rw [e]
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 1 + 1 + |x| + x ^ 2 / 2 := by
          rw [hn1, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2 / 2)]
      _ ≤ 4 * |x| ^ (2 + ε) := by nlinarith

/-- quantitative second-order expansion of a characteristic function. -/
lemma charfun_expand {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hX1 : Integrable X μ) (hX0 : ∫ ω, X ω ∂μ = 0)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hXe : Integrable (fun ω => |X ω| ^ (2 + ε)) μ) (t : ℝ) :
    ‖(∫ ω, Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ)) ∂μ) -
        (1 - ((t ^ 2 / 2 * ∫ ω, X ω ^ 2 ∂μ : ℝ) : ℂ))‖ ≤
      4 * |t| ^ (2 + ε) * ∫ ω, |X ω| ^ (2 + ε) ∂μ := by
  set p : Ω → ℂ := fun ω => 1 + Complex.I * ((t * X ω : ℝ) : ℂ) - (((t * X ω) ^ 2 / 2 : ℝ) : ℂ)
    with hp
  have hm1 : Measurable fun ω => ((t * X ω : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_const.mul hX)
  have hI1 : Integrable (fun ω => ((t * X ω : ℝ) : ℂ)) μ := (hX1.const_mul t).ofReal
  have hI2 : Integrable (fun ω => (((t * X ω) ^ 2 / 2 : ℝ) : ℂ)) μ := by
    have : Integrable (fun ω => (t * X ω) ^ 2 / 2) μ := by
      have h := (hX2.const_mul (t ^ 2 / 2))
      refine h.congr (Eventually.of_forall fun ω => ?_)
      simp only; ring
    exact this.ofReal
  have hA : Integrable (fun ω => (1:ℂ) + Complex.I * ((t * X ω : ℝ) : ℂ)) μ :=
    (integrable_const 1).add (hI1.const_mul Complex.I)
  have hpI : Integrable p μ := hA.sub hI2
  have hexpI : Integrable (fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ))) μ := by
    refine Integrable.of_bound (C := 1)
      ((Complex.continuous_exp.measurable.comp (measurable_const.mul hm1)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le
  have hint_p : ∫ ω, p ω ∂μ = 1 - ((t ^ 2 / 2 * ∫ ω, X ω ^ 2 ∂μ : ℝ) : ℂ) := by
    simp only [hp]
    rw [integral_sub hA hI2,
      integral_add (integrable_const 1) (hI1.const_mul Complex.I), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal, integral_const_mul, hX0]
    have : ∫ ω, (t * X ω) ^ 2 / 2 ∂μ = t ^ 2 / 2 * ∫ ω, X ω ^ 2 ∂μ := by
      rw [← integral_const_mul]; congr 1; funext ω; ring
    rw [this]
    simp
  rw [← hint_p, ← integral_sub hexpI hpI]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hb : ∀ ω, ‖Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ)) - p ω‖ ≤
      4 * |t| ^ (2 + ε) * |X ω| ^ (2 + ε) := by
    intro ω
    have h := exp_I_taylor (t * X ω) hε0 hε1
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc] at h
    exact h
  calc ∫ ω, ‖Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ)) - p ω‖ ∂μ
      ≤ ∫ ω, 4 * |t| ^ (2 + ε) * |X ω| ^ (2 + ε) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hXe.const_mul _) (Eventually.of_forall hb)
    _ = 4 * |t| ^ (2 + ε) * ∫ ω, |X ω| ^ (2 + ε) ∂μ := integral_const_mul _ _

lemma sqrt_inv_sq (n : ℕ) : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

lemma tendsto_sqrt_inv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- one block of a triangular array: `φₙ(1/√n)^{bₙ} → exp(-β q / 2)`. -/
lemma block_limit {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (X : ∀ n, Ω n → ℝ) (hXm : ∀ n, Measurable (X n))
    (hX1 : ∀ n, Integrable (X n) (P n)) (hX0 : ∀ n, ∫ ω, X n ω ∂(P n) = 0)
    (hX2 : ∀ n, Integrable (fun ω => X n ω ^ 2) (P n)) {q : ℝ}
    (hq : Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂(P n)) atTop (𝓝 q))
    {ε M : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hXe : ∀ n, Integrable (fun ω => |X n ω| ^ (2 + ε)) (P n))
    (hM : ∀ n, ∫ ω, |X n ω| ^ (2 + ε) ∂(P n) ≤ M)
    (b : ℕ → ℕ) {β : ℝ} (hb : Tendsto (fun n => (b n : ℝ) / n) atTop (𝓝 β)) :
    Tendsto (fun n => (∫ ω, Complex.exp (Complex.I * (((Real.sqrt n)⁻¹ * X n ω : ℝ) : ℂ))
      ∂(P n)) ^ b n) atTop (𝓝 (Complex.exp (-((β * q / 2 : ℝ) : ℂ)))) := by
  set t : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with ht
  set z : ℕ → ℂ := fun n =>
    ∫ ω, Complex.exp (Complex.I * ((t n * X n ω : ℝ) : ℂ)) ∂(P n) with hz
  set qn : ℕ → ℝ := fun n => ∫ ω, X n ω ^ 2 ∂(P n) with hqn
  have ht0 : ∀ n, 0 ≤ t n := fun n => inv_nonneg.2 (Real.sqrt_nonneg _)
  have hzn : ∀ n, ‖z n‖ ≤ 1 := by
    intro n
    have : ∀ ω, ‖Complex.exp (Complex.I * ((t n * X n ω : ℝ) : ℂ))‖ = 1 := fun ω => by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [integral_congr_ae (Eventually.of_forall this :
      (fun ω => ‖Complex.exp (Complex.I * ((t n * X n ω : ℝ) : ℂ))‖) =ᵐ[P n] fun _ => (1:ℝ))]
    simp
  have hexp := fun n => charfun_expand (μ := P n) (hXm n) (hX1 n) (hX0 n) (hX2 n) hε0 hε1
    (hXe n) (t n)
  -- the error term
  set E : ℕ → ℂ := fun n => z n - (1 - ((t n ^ 2 / 2 * qn n : ℝ) : ℂ)) with hE
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _).trans (hM 0)
  have hEb : ∀ n, ‖E n‖ ≤ 4 * M * ((n : ℝ)⁻¹ * t n ^ ε) := by
    intro n
    refine (hexp n).trans ?_
    rw [abs_of_nonneg (ht0 n), Real.rpow_add' (ht0 n) (by linarith), Real.rpow_two,
      sqrt_inv_sq]
    have := hM n
    have h1 : 0 ≤ (n : ℝ)⁻¹ * t n ^ ε := by positivity
    nlinarith
  have htε : Tendsto (fun n => t n ^ ε) atTop (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 ε (Or.inr hε0.le)).tendsto).comp tendsto_sqrt_inv
    rw [Real.zero_rpow hε0.ne'] at h
    exact h
  have hninv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hz1 : Tendsto z atTop (𝓝 1) := by
    have hdec : z = fun n => (1 - ((t n ^ 2 / 2 * qn n : ℝ) : ℂ)) + E n := by
      funext n; simp only [hE]; ring
    rw [hdec]
    have hA : Tendsto (fun n => (1 - ((t n ^ 2 / 2 * qn n : ℝ) : ℂ))) atTop (𝓝 (1 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      have : Tendsto (fun n => t n ^ 2 / 2 * qn n) atTop (𝓝 (0 / 2 * q)) := by
        have h2 : Tendsto (fun n => t n ^ 2) atTop (𝓝 0) := by
          simp only [ht, sqrt_inv_sq]; exact hninv
        exact (h2.div_const 2).mul hq
      rw [zero_div, zero_mul] at this
      have h3 := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at h3
      exact h3
    have hB : Tendsto E atTop (𝓝 0) := by
      refine squeeze_zero_norm hEb ?_
      have := (hninv.mul htε).const_mul (4 * M)
      simpa using this
    rw [sub_zero] at hA
    have := hA.add hB
    rw [add_zero] at this
    exact this
  have hw : Tendsto (fun n => (b n : ℂ) * (z n - 1)) atTop (𝓝 (-((β * q / 2 : ℝ) : ℂ))) := by
    have hdec : (fun n => (b n : ℂ) * (z n - 1)) = fun n =>
        ((-((b n : ℝ) / n * qn n / 2) : ℝ) : ℂ) + (b n : ℂ) * E n := by
      funext n
      simp only [hE]
      have h2 : t n ^ 2 = (n : ℝ)⁻¹ := sqrt_inv_sq n
      rw [h2]
      push_cast
      ring
    rw [hdec]
    have hA : Tendsto (fun n => ((-((b n : ℝ) / n * qn n / 2) : ℝ) : ℂ)) atTop
        (𝓝 (((-(β * q / 2)) : ℝ) : ℂ)) := by
      refine (Complex.continuous_ofReal.tendsto _).comp ?_
      have := (hb.mul hq).div_const 2
      have := this.neg
      convert this using 2
    have hB : Tendsto (fun n => (b n : ℂ) * E n) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n => 4 * M * ((b n : ℝ) / n * t n ^ ε)) (fun n => ?_) ?_
      · rw [norm_mul, Complex.norm_natCast]
        have := hEb n
        calc (b n : ℝ) * ‖E n‖ ≤ (b n : ℝ) * (4 * M * ((n : ℝ)⁻¹ * t n ^ ε)) :=
              mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
          _ = 4 * M * ((b n : ℝ) / n * t n ^ ε) := by ring
      · have := (hb.mul htε).const_mul (4 * M)
        simpa using this
    have := hA.add hB
    rw [add_zero] at this
    convert this using 2
    push_cast; ring
  exact tendsto_pow_of_mul hzn hz1 hw

/-! ### combinatorial and measure-theoretic pieces -/

lemma floor_ratio {a : ℕ → ℝ} {a₀ t : ℝ} (ha : Tendsto a atTop (𝓝 a₀)) (ha0 : ∀ n, 0 ≤ a n)
    (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊a n * n * t⌋₊ : ℝ) / n) atTop (𝓝 (a₀ * t)) := by
  have hninv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun n => a n * t) atTop (𝓝 (a₀ * t)) := ha.mul_const t
  have hlo : Tendsto (fun n : ℕ => a n * t - (n : ℝ)⁻¹) atTop (𝓝 (a₀ * t)) := by
    simpa using hup.sub hninv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnp : (0:ℝ) < n := by exact_mod_cast hn
    have h1 := Nat.lt_floor_add_one (a n * n * t)
    rw [le_div_iff₀ hnp]
    have : (a n * t - (n:ℝ)⁻¹) * n = a n * n * t - 1 := by
      rw [sub_mul, inv_mul_cancel₀ hnp.ne']; ring
    rw [this]; linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnp : (0:ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hnp]
    have := Nat.floor_le (show 0 ≤ a n * n * t by have := ha0 n; positivity)
    linarith [show a n * t * n = a n * n * t by ring]

/-- summation by parts for the increments of a path started at `0`. -/
lemma abel_sum {K : ℕ} (m : ℕ) (θ x : ℕ → Fin K → ℝ) (hx0 : x 0 = 0) :
    ∑ l ∈ Finset.range m, θ l ⬝ᵥ x (l + 1) =
      ∑ l ∈ Finset.range m, (∑ l' ∈ Finset.Ico l m, θ l') ⬝ᵥ (x (l + 1) - x l) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ∀ l ∈ Finset.range (m + 1), (∑ l' ∈ Finset.Ico l (m + 1), θ l') ⬝ᵥ
        (x (l + 1) - x l) = (∑ l' ∈ Finset.Ico l m, θ l') ⬝ᵥ (x (l + 1) - x l) +
          θ m ⬝ᵥ (x (l + 1) - x l) := fun l hl => by
      rw [Finset.sum_Ico_succ_top (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)), add_dotProduct]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
      Finset.sum_range_succ (fun l => (∑ l' ∈ Finset.Ico l m, θ l') ⬝ᵥ (x (l + 1) - x l)),
      Finset.Ico_self, Finset.sum_empty, zero_dotProduct, add_zero, ← ih, ← dotProduct_sum,
      Finset.sum_range_sub, hx0, sub_zero, Finset.sum_range_succ]

/-- Lévy continuity, finite-dimensional-distribution form. -/
lemma levy_fdd {m K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (U : ∀ n, Ω n → Fin m → Fin K → ℝ)
    (hU : ∀ n, Measurable (U n)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (U' : Ω' → Fin m → Fin K → ℝ) (hU' : Measurable U')
    (hch : ∀ θ : Fin m → Fin K → ℝ, Tendsto (fun n => ∫ ω, Complex.exp (Complex.I *
      ((∑ l, θ l ⬝ᵥ U n ω l : ℝ) : ℂ)) ∂(P n)) atTop
      (𝓝 (∫ ω, Complex.exp (Complex.I * ((∑ l, θ l ⬝ᵥ U' ω l : ℝ) : ℂ)) ∂P')))
    (f : (Fin m → Fin K → ℝ) → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => ∫ ω, f (U n ω) ∂(P n)) atTop (𝓝 (∫ ω, f (U' ω) ∂P')) := by
  let eqv := EuclideanSpace.equiv (Fin m × Fin K) ℝ
  let e : (Fin m → Fin K → ℝ) → EuclideanSpace ℝ (Fin m × Fin K) :=
    fun x => eqv.symm (fun p => x p.1 p.2)
  let d : EuclideanSpace ℝ (Fin m × Fin K) → (Fin m → Fin K → ℝ) := fun y l k => eqv y (l, k)
  have he : Continuous e := eqv.symm.continuous.comp
    (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1))
  have hd : Continuous d := continuous_pi fun l => continuous_pi fun k =>
    (continuous_apply (l, k)).comp eqv.continuous
  have hde : ∀ x, d (e x) = x := fun x => by funext l k; simp [d, e, eqv]
  have hinner : ∀ x (y : EuclideanSpace ℝ (Fin m × Fin K)),
      inner ℝ (e x) y = ∑ l, d y l ⬝ᵥ x l := by
    intro x y
    simp [e, d, eqv, PiLp.inner_apply, dotProduct, Fintype.sum_prod_type, mul_comm]
  have hconv : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (Q : Measure Ω₁)
      (V : Ω₁ → Fin m → Fin K → ℝ), Measurable V → ∀ t,
      charFun (Q.map (fun ω => e (V ω))) t =
        ∫ ω, Complex.exp (Complex.I * ((∑ l, d t l ⬝ᵥ V ω l : ℝ) : ℂ)) ∂Q := by
    intro Ω₁ _ Q V hV t
    rw [charFun_apply, integral_map
      (show Measurable (fun ω => e (V ω)) from he.measurable.comp hV).aemeasurable]
    · congr 1; funext ω
      rw [hinner, mul_comm]
    · exact Continuous.aestronglyMeasurable (by fun_prop)
  have hmU : ∀ n, Measurable (fun ω => e (U n ω)) := fun n => he.measurable.comp (hU n)
  have hmU' : Measurable (fun ω => e (U' ω)) := he.measurable.comp hU'
  let μn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin m × Fin K)) := fun n =>
    ⟨(P n).map (fun ω => e (U n ω)), Measure.isProbabilityMeasure_map (hmU n).aemeasurable⟩
  let μ0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin m × Fin K)) :=
    ⟨P'.map (fun ω => e (U' ω)), Measure.isProbabilityMeasure_map hmU'.aemeasurable⟩
  have hlim : Tendsto μn atTop (𝓝 μ0) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    show Tendsto (fun n => charFun ((P n).map (fun ω => e (U n ω))) t) atTop
      (𝓝 (charFun (P'.map (fun ω => e (U' ω))) t))
    simp only [hconv _ _ (hU _), hconv _ _ hU']
    exact hch (d t)
  have hb : ∀ x y : EuclideanSpace ℝ (Fin m × Fin K),
      dist (f (d x)) (f (d y)) ≤ 2 * C := fun x y => by
    rw [Real.dist_eq]
    have h1 := hC (d x); have h2 := hC (d y)
    calc |f (d x) - f (d y)| ≤ |f (d x)| + |f (d y)| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  set g := BoundedContinuousFunction.mkOfBound ⟨fun y => f (d y), hf.comp hd⟩ (2 * C) hb
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) g
  have hrw : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (Q : Measure Ω₁) (V : Ω₁ → Fin m → Fin K → ℝ),
      Measurable V → ∫ y, g y ∂(Q.map (fun ω => e (V ω))) = ∫ ω, f (V ω) ∂Q := by
    intro Ω₁ _ Q V hV
    rw [integral_map (show Measurable (fun ω => e (V ω)) from he.measurable.comp hV).aemeasurable
      g.continuous.aestronglyMeasurable]
    congr 1
  have h2 : ∀ n, ∫ y, g y ∂(μn n : Measure _) = ∫ ω, f (U n ω) ∂(P n) := fun n =>
    hrw _ _ (hU n)
  have h0 : ∫ y, g y ∂(μ0 : Measure _) = ∫ ω, f (U' ω) ∂P' := hrw _ _ hU'
  have := hint.congr h2
  rwa [h0] at this

/-- characteristic function of independent blocks of a triangular array. -/
lemma wside_prod {K : ℕ} {S : Type} [Fintype S] {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Y : S → ℕ → Ω → Fin K → ℝ) (hYm : ∀ s i, Measurable (Y s i))
    (hind : iIndepFun (fun p : S × ℕ => Y p.1 p.2) μ)
    (hid : ∀ s i, IdentDistrib (Y s i) (Y s 0) μ μ)
    (m : ℕ) (B : S → ℕ → ℕ) (hB : ∀ s l l', l ≤ l' → l' ≤ m → B s l ≤ B s l')
    (Θ : ℕ → Fin K → ℝ) (c : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((∑ s, ∑ l ∈ Finset.range m,
        ∑ i ∈ Finset.Ico (B s l) (B s (l + 1)), c * (Θ l ⬝ᵥ Y s i ω) : ℝ) : ℂ)) ∂μ =
      ∏ s, ∏ l ∈ Finset.range m, (∫ ω, Complex.exp (Complex.I *
        ((c * (Θ l ⬝ᵥ Y s 0 ω) : ℝ) : ℂ)) ∂μ) ^ (B s (l + 1) - B s l) := by
  classical
  set T : Finset (Σ _ : S × ℕ, ℕ) := (Finset.univ ×ˢ Finset.range m).sigma
    fun sl => Finset.Ico (B sl.1 sl.2) (B sl.1 (sl.2 + 1)) with hT
  set F : (Σ _ : S × ℕ, ℕ) → Ω → ℂ := fun x ω =>
    Complex.exp (Complex.I * ((c * (Θ x.1.2 ⬝ᵥ Y x.1.1 x.2 ω) : ℝ) : ℂ)) with hF
  have h1 : ∀ ω, Complex.exp (Complex.I * ((∑ s, ∑ l ∈ Finset.range m,
      ∑ i ∈ Finset.Ico (B s l) (B s (l + 1)), c * (Θ l ⬝ᵥ Y s i ω) : ℝ) : ℂ)) =
      ∏ x ∈ T, F x ω := by
    intro ω
    rw [hT, Finset.prod_sigma, Finset.prod_product]
    simp only [hF]
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  have hinj : Function.Injective (fun x : T => (x.1.1.1, x.1.2)) := by
    rintro ⟨⟨⟨s, l⟩, i⟩, hx⟩ ⟨⟨⟨s', l'⟩, i'⟩, hy⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [hT, Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range, Finset.mem_Ico] at hx hy
    have hll : l = l' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hB s (l + 1) l' (by omega) (by omega); omega
      · have := hB s (l' + 1) l (by omega) (by omega); omega
    subst hll; rfl
  have hind' : iIndepFun (fun x : T => Y x.1.1.1 x.1.2) μ := hind.precomp hinj
  have h2 : ∫ ω, ∏ x : T, F x.1 ω ∂μ = ∏ x : T, ∫ ω, F x.1 ω ∂μ :=
    hind'.integral_fun_prod_comp (f := fun (x : T) (y : Fin K → ℝ) =>
      Complex.exp (Complex.I * ((c * (Θ x.1.1.2 ⬝ᵥ y) : ℝ) : ℂ)))
      (fun x => (hYm _ _).aemeasurable) (fun x => Continuous.aestronglyMeasurable (by fun_prop))
  have hc : ∀ ω, ∏ x : T, F x.1 ω = ∏ x ∈ T, F x ω := fun ω =>
    Finset.prod_coe_sort T (fun x => F x ω)
  have hc' : ∏ x : T, ∫ ω, F x.1 ω ∂μ = ∏ x ∈ T, ∫ ω, F x ω ∂μ :=
    Finset.prod_coe_sort T (fun x => ∫ ω, F x ω ∂μ)
  rw [integral_congr_ae (Eventually.of_forall hc), hc'] at h2
  have h3 : ∀ x ∈ T, ∫ ω, F x ω ∂μ = ∫ ω, Complex.exp (Complex.I *
      ((c * (Θ x.1.2 ⬝ᵥ Y x.1.1 0 ω) : ℝ) : ℂ)) ∂μ := by
    intro x _
    exact ((hid x.1.1 x.2).comp (u := fun y : Fin K → ℝ =>
      Complex.exp (Complex.I * ((c * (Θ x.1.2 ⬝ᵥ y) : ℝ) : ℂ)))
      (Continuous.measurable (by fun_prop))).integral_eq
  rw [integral_congr_ae (Eventually.of_forall h1), h2, Finset.prod_congr rfl h3, hT,
    Finset.prod_sigma, Finset.prod_product]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun l _ => ?_
  dsimp only
  rw [Finset.prod_const, Nat.card_Ico]

/-- characteristic function of the increments of a drifted Brownian motion. -/
lemma bm_prod {K : ℕ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {c : Fin K → ℝ}
    {A : Matrix (Fin K) (Fin K) ℝ} {ζ : Ω' → ℝ → Fin K → ℝ} (hζ : IsDriftedBM c A P' ζ)
    (m : ℕ) (τ : Fin (m + 1) → ℝ) (h0 : 0 ≤ τ 0) (hτ : Monotone τ) (Θ : Fin m → Fin K → ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((∑ l : Fin m,
        Θ l ⬝ᵥ (ζ ω (τ l.succ) - ζ ω (τ l.castSucc)) : ℝ) : ℂ)) ∂P' =
      ∏ l : Fin m, Complex.exp (Complex.I * (((τ l.succ - τ l.castSucc) * (Θ l ⬝ᵥ c) : ℝ) : ℂ)
        - (((τ l.succ - τ l.castSucc) / 2 * (Θ l ⬝ᵥ (A *ᵥ Θ l)) : ℝ) : ℂ)) := by
  obtain ⟨hP, hmeas, _, _, hind, hcf⟩ := hζ
  have h1 : ∀ ω, Complex.exp (Complex.I * ((∑ l : Fin m,
      Θ l ⬝ᵥ (ζ ω (τ l.succ) - ζ ω (τ l.castSucc)) : ℝ) : ℂ)) =
      ∏ l : Fin m, Complex.exp (Complex.I *
        ((Θ l ⬝ᵥ (ζ ω (τ l.succ) - ζ ω (τ l.castSucc)) : ℝ) : ℂ)) := by
    intro ω; rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  rw [integral_congr_ae (Eventually.of_forall h1)]
  rw [(hind m τ h0 hτ).integral_fun_prod_comp (f := fun (l : Fin m) (y : Fin K → ℝ) =>
    Complex.exp (Complex.I * ((Θ l ⬝ᵥ y : ℝ) : ℂ)))
    (fun l => ((hmeas _).sub (hmeas _)).aemeasurable)
    (fun l => Continuous.aestronglyMeasurable (by fun_prop))]
  refine Finset.prod_congr rfl fun l _ => ?_
  exact hcf _ _ (h0.trans (hτ (Fin.zero_le _))) (hτ (Fin.castSucc_le_succ l)) (Θ l)

/-! ### the triangular-array process and its fdd characteristic functions -/

/-- `Wₙ(t) = n^{-1/2} Σ_s Σ_{i < ⌊αₙₛ n t⌋} Yₙₛᵢ + t c`. -/
noncomputable def Wp {K : ℕ} {S : Type} [Fintype S] {Ω : ℕ → Type}
    (Y : ∀ n, S → ℕ → Ω n → Fin K → ℝ) (α : ℕ → S → ℝ) (c : Fin K → ℝ) :
    ∀ n, Ω n → ℝ → Fin K → ℝ :=
  fun n ω t => (Real.sqrt n)⁻¹ • ∑ s, ∑ i ∈ Finset.range ⌊α n s * n * t⌋₊, Y n s i ω + t • c

/-- scalar projections of a centred vector with `2 + ε` moments. -/
lemma proj_facts {K : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → Fin K → ℝ} (hZm : Measurable Z) (hZ1 : ∀ k, Integrable (fun ω => Z ω k) μ)
    (hZ0 : ∀ k, ∫ ω, Z ω k ∂μ = 0)
    (hZ2 : ∀ k k', Integrable (fun ω => Z ω k * Z ω k') μ) {ε M : ℝ} (hε0 : 0 < ε)
    (hmI : Integrable (fun ω => ‖Z ω‖ ^ (2 + ε)) μ) (hmM : ∫ ω, ‖Z ω‖ ^ (2 + ε) ∂μ ≤ M)
    (Θ : Fin K → ℝ) :
    Measurable (fun ω => Θ ⬝ᵥ Z ω) ∧ Integrable (fun ω => Θ ⬝ᵥ Z ω) μ ∧
    ∫ ω, Θ ⬝ᵥ Z ω ∂μ = 0 ∧ Integrable (fun ω => (Θ ⬝ᵥ Z ω) ^ 2) μ ∧
    ∫ ω, (Θ ⬝ᵥ Z ω) ^ 2 ∂μ = ∑ k, ∑ k', Θ k * Θ k' * ∫ ω, Z ω k * Z ω k' ∂μ ∧
    Integrable (fun ω => |Θ ⬝ᵥ Z ω| ^ (2 + ε)) μ ∧
    ∫ ω, |Θ ⬝ᵥ Z ω| ^ (2 + ε) ∂μ ≤ (∑ k, |Θ k|) ^ (2 + ε) * M := by
  have hcoord : ∀ k, Measurable fun ω => Z ω k := fun k => (measurable_pi_apply k).comp hZm
  have hdot : (fun ω => Θ ⬝ᵥ Z ω) = fun ω => ∑ k, Θ k * Z ω k := rfl
  have hm : Measurable (fun ω => Θ ⬝ᵥ Z ω) := by
    rw [hdot]; exact Finset.measurable_sum _ fun k _ => measurable_const.mul (hcoord k)
  have hsq : (fun ω => (Θ ⬝ᵥ Z ω) ^ 2) = fun ω => ∑ k, ∑ k', Θ k * Θ k' * (Z ω k * Z ω k') := by
    funext ω
    rw [show Θ ⬝ᵥ Z ω = ∑ k, Θ k * Z ω k from rfl, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  have hbd : ∀ ω, |Θ ⬝ᵥ Z ω| ≤ (∑ k, |Θ k|) * ‖Z ω‖ := by
    intro ω
    rw [show Θ ⬝ᵥ Z ω = ∑ k, Θ k * Z ω k from rfl, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (Z ω) k
  have hrp : ∀ ω, |Θ ⬝ᵥ Z ω| ^ (2 + ε) ≤ (∑ k, |Θ k|) ^ (2 + ε) * ‖Z ω‖ ^ (2 + ε) := by
    intro ω
    rw [← Real.mul_rpow (Finset.sum_nonneg fun k _ => abs_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hbd ω) (by linarith)
  have hint3 : Integrable (fun ω => |Θ ⬝ᵥ Z ω| ^ (2 + ε)) μ :=
    Integrable.mono' (hmI.const_mul _)
      ((hm.abs.pow_const _).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hrp ω)
  refine ⟨hm, ?_, ?_, ?_, ?_, hint3, ?_⟩
  · rw [hdot]; exact integrable_finset_sum _ fun k _ => (hZ1 k).const_mul _
  · rw [hdot, integral_finset_sum _ fun k _ => (hZ1 k).const_mul _]
    simp [integral_const_mul, hZ0]
  · rw [hsq]
    exact integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun k' _ =>
      (hZ2 k k').const_mul _
  · rw [hsq, integral_finset_sum _ fun k _ => integrable_finset_sum _ fun k' _ =>
      (hZ2 k k').const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ fun k' _ => (hZ2 k k').const_mul _]
    exact Finset.sum_congr rfl fun k' _ => integral_const_mul _ _
  · calc ∫ ω, |Θ ⬝ᵥ Z ω| ^ (2 + ε) ∂μ
        ≤ ∫ ω, (∑ k, |Θ k|) ^ (2 + ε) * ‖Z ω‖ ^ (2 + ε) ∂μ :=
          integral_mono hint3 (hmI.const_mul _) hrp
      _ = (∑ k, |Θ k|) ^ (2 + ε) * ∫ ω, ‖Z ω‖ ^ (2 + ε) ∂μ := integral_const_mul _ _
      _ ≤ (∑ k, |Θ k|) ^ (2 + ε) * M :=
          mul_le_mul_of_nonneg_left hmM (Real.rpow_nonneg (Finset.sum_nonneg fun k _ =>
            abs_nonneg _) _)

lemma quad_sum {K : ℕ} {S : Type} [Fintype S] (a : S → ℝ) (C : S → Matrix (Fin K) (Fin K) ℝ)
    (Θ : Fin K → ℝ) : Θ ⬝ᵥ ((∑ s, a s • C s) *ᵥ Θ) = ∑ s, a s * (Θ ⬝ᵥ (C s *ᵥ Θ)) := by
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul]

lemma quad_eq {K : ℕ} (C : Matrix (Fin K) (Fin K) ℝ) (Θ : Fin K → ℝ) :
    Θ ⬝ᵥ (C *ᵥ Θ) = ∑ k, ∑ k', Θ k * Θ k' * C k k' := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring

/-- fdd convergence with bounded Lipschitz tests (copy of `P5.FddConv`). -/
def FddConvA {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → ℝ → Fin K → ℝ) : Prop :=
  ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, τ i ∈ Set.Icc (0:ℝ) 1) →
    ∀ (f : (Fin m → Fin K → ℝ) → ℝ), (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∃ L : NNReal, LipschitzWith L f) →
      Tendsto (fun n => ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)) atTop
        (𝓝 (∫ ω, f (fun i => X' ω (τ i)) ∂P'))

section TCLT

variable {K : ℕ} {S : Type} [Fintype S] {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
  {Y : ∀ n, S → ℕ → Ω n → Fin K → ℝ} {α : ℕ → S → ℝ} {α₀ : S → ℝ}
  {C : S → Matrix (Fin K) (Fin K) ℝ} {c : Fin K → ℝ} {ε M : ℝ}

theorem tclt_mono
    (hYm : ∀ n s i, Measurable (Y n s i))
    (hind : ∀ n, iIndepFun (fun p : S × ℕ => Y n p.1 p.2) (P n))
    (hid : ∀ n s i, IdentDistrib (Y n s i) (Y n s 0) (P n) (P n))
    (hY1 : ∀ n s k, Integrable (fun ω => Y n s 0 ω k) (P n))
    (hY0 : ∀ n s k, ∫ ω, Y n s 0 ω k ∂(P n) = 0)
    (hY2 : ∀ n s k k', Integrable (fun ω => Y n s 0 ω k * Y n s 0 ω k') (P n))
    (hC : ∀ s k k', Tendsto (fun n => ∫ ω, Y n s 0 ω k * Y n s 0 ω k' ∂(P n)) atTop
      (𝓝 (C s k k')))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmI : ∀ n s, Integrable (fun ω => ‖Y n s 0 ω‖ ^ (2 + ε)) (P n))
    (hmM : ∀ n s, ∫ ω, ‖Y n s 0 ω‖ ^ (2 + ε) ∂(P n) ≤ M)
    (hα0 : ∀ n s, 0 ≤ α n s) (hα : ∀ s, Tendsto (fun n => α n s) atTop (𝓝 (α₀ s)))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {ζ : Ω' → ℝ → Fin K → ℝ}
    (hζ : IsDriftedBM c (∑ s, α₀ s • C s) P' ζ)
    (m : ℕ) (τ : Fin m → ℝ) (hτ01 : ∀ i, τ i ∈ Set.Icc (0:ℝ) 1) (hmono : Monotone τ)
    (θ : Fin m → Fin K → ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I *
      ((∑ l, θ l ⬝ᵥ Wp Y α c n ω (τ l) : ℝ) : ℂ)) ∂(P n)) atTop
      (𝓝 (∫ ω, Complex.exp (Complex.I * ((∑ l, θ l ⬝ᵥ ζ ω (τ l) : ℝ) : ℂ)) ∂P')) := by
  classical
  set τN : ℕ → ℝ := fun j => if h : 0 < j ∧ j ≤ m then τ ⟨j - 1, by omega⟩ else 0 with hτN
  set θN : ℕ → Fin K → ℝ := fun l => if h : l < m then θ ⟨l, h⟩ else 0 with hθN
  set ΘN : ℕ → Fin K → ℝ := fun l => ∑ l' ∈ Finset.Ico l m, θN l' with hΘN
  set Δ : ℕ → ℝ := fun l => τN (l + 1) - τN l with hΔ
  have hτN0 : τN 0 = 0 := by simp [hτN]
  have hτNs : ∀ l : Fin m, τN (l + 1) = τ l := by
    intro l
    simp only [hτN]
    rw [dif_pos ⟨Nat.succ_pos _, l.2⟩]
    congr 1
  have hθNl : ∀ l : Fin m, θN l = θ l := fun l => by simp [hθN, l.2]
  have hτN_nonneg : ∀ j, 0 ≤ τN j := by
    intro j; simp only [hτN]; split_ifs
    · exact (hτ01 _).1
    · exact le_rfl
  have hτN_mono : ∀ j j', j ≤ j' → j' ≤ m → τN j ≤ τN j' := by
    intro j j' h h'
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hτN0]; exact hτN_nonneg _
    · simp only [hτN]
      rw [dif_pos ⟨hj, by omega⟩, dif_pos ⟨by omega, h'⟩]
      exact hmono (Fin.mk_le_mk.2 (by omega))
  have habel : ∀ V : ℝ → Fin K → ℝ, V 0 = 0 → ∑ l, θ l ⬝ᵥ V (τ l) =
      ∑ l ∈ Finset.range m, ΘN l ⬝ᵥ (V (τN (l + 1)) - V (τN l)) := by
    intro V hV
    have h1 : ∑ l, θ l ⬝ᵥ V (τ l) = ∑ l ∈ Finset.range m, θN l ⬝ᵥ V (τN (l + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun l => θN l ⬝ᵥ V (τN (l + 1))) m]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hθNl, hτNs]
    rw [h1]
    exact abel_sum m θN (fun j => V (τN j)) (by simp only [hτN0, hV])
  -- the Brownian side
  set A := ∑ s, α₀ s • C s with hA
  set τ' : Fin (m + 1) → ℝ := fun j => τN j with hτ'
  have hτ'mono : Monotone τ' := fun j j' h => hτN_mono j j' h (Nat.lt_succ_iff.1 j'.2)
  have hRHS : ∫ ω, Complex.exp (Complex.I * ((∑ l, θ l ⬝ᵥ ζ ω (τ l) : ℝ) : ℂ)) ∂P' =
      ∏ l ∈ Finset.range m, Complex.exp (Complex.I * ((Δ l * (ΘN l ⬝ᵥ c) : ℝ) : ℂ)
        - ((Δ l / 2 * (ΘN l ⬝ᵥ (A *ᵥ ΘN l)) : ℝ) : ℂ)) := by
    have h1 : ∀ ω, ∑ l, θ l ⬝ᵥ ζ ω (τ l) =
        ∑ l : Fin m, ΘN l ⬝ᵥ (ζ ω (τ' l.succ) - ζ ω (τ' l.castSucc)) := by
      intro ω
      rw [habel (ζ ω) (hζ.2.2.1 ω),
        ← Fin.sum_univ_eq_sum_range (fun l => ΘN l ⬝ᵥ (ζ ω (τN (l + 1)) - ζ ω (τN l))) m]
      rfl
    simp_rw [h1]
    rw [bm_prod hζ m τ' (by rw [hτ']; exact hτN_nonneg _) hτ'mono (fun l => ΘN l)]
    exact Fin.prod_univ_eq_prod_range (fun l => Complex.exp (Complex.I *
      ((Δ l * (ΘN l ⬝ᵥ c) : ℝ) : ℂ) - ((Δ l / 2 * (ΘN l ⬝ᵥ (A *ᵥ ΘN l)) : ℝ) : ℂ))) m
  -- the triangular-array side
  set B : ℕ → S → ℕ → ℕ := fun n s j => ⌊α n s * n * τN j⌋₊ with hB
  have hBmono : ∀ n s l l', l ≤ l' → l' ≤ m → B n s l ≤ B n s l' := by
    intro n s l l' h h'
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hτN_mono l l' h h')
      (mul_nonneg (hα0 n s) (Nat.cast_nonneg n)))
  have hW0 : ∀ n ω, Wp Y α c n ω 0 = 0 := by intro n ω; simp [Wp]
  have hWinc : ∀ n ω l, l < m → Wp Y α c n ω (τN (l + 1)) - Wp Y α c n ω (τN l) =
      (Real.sqrt n)⁻¹ • ∑ s, ∑ i ∈ Finset.Ico (B n s l) (B n s (l + 1)), Y n s i ω +
        Δ l • c := by
    intro n ω l hl
    have h1 : ∀ s, ∑ i ∈ Finset.Ico (B n s l) (B n s (l + 1)), Y n s i ω =
        ∑ i ∈ Finset.range (B n s (l + 1)), Y n s i ω -
          ∑ i ∈ Finset.range (B n s l), Y n s i ω :=
      fun s => Finset.sum_Ico_eq_sub _ (hBmono n s l (l + 1) (by omega) (by omega))
    simp only [h1]
    simp only [Finset.sum_sub_distrib, smul_sub, hΔ, sub_smul, hB, Wp]
    abel
  have hreal : ∀ n ω, ∑ l, θ l ⬝ᵥ Wp Y α c n ω (τ l) =
      ∑ l ∈ Finset.range m, Δ l * (ΘN l ⬝ᵥ c) + ∑ s, ∑ l ∈ Finset.range m,
        ∑ i ∈ Finset.Ico (B n s l) (B n s (l + 1)), (Real.sqrt n)⁻¹ * (ΘN l ⬝ᵥ Y n s i ω) := by
    intro n ω
    rw [habel _ (hW0 n ω), Finset.sum_congr rfl fun l hl => by
      rw [hWinc n ω l (Finset.mem_range.1 hl)]]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_sum, Finset.mul_sum]
    rw [Finset.sum_add_distrib, add_comm]
    congr 1
    exact Finset.sum_comm
  have hLHS : ∀ n, ∫ ω, Complex.exp (Complex.I *
      ((∑ l, θ l ⬝ᵥ Wp Y α c n ω (τ l) : ℝ) : ℂ)) ∂(P n) =
      Complex.exp (Complex.I * ((∑ l ∈ Finset.range m, Δ l * (ΘN l ⬝ᵥ c) : ℝ) : ℂ)) *
      ∏ s, ∏ l ∈ Finset.range m, (∫ ω, Complex.exp (Complex.I *
        (((Real.sqrt n)⁻¹ * (ΘN l ⬝ᵥ Y n s 0 ω) : ℝ) : ℂ)) ∂(P n)) ^
          (B n s (l + 1) - B n s l) := by
    intro n
    simp_rw [hreal n]
    simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
    rw [integral_const_mul, wside_prod (Y n) (hYm n) (hind n) (hid n) m (B n) (hBmono n) ΘN _]
  have hblk : ∀ s, ∀ l ∈ Finset.range m, Tendsto (fun n => (∫ ω, Complex.exp (Complex.I *
      (((Real.sqrt n)⁻¹ * (ΘN l ⬝ᵥ Y n s 0 ω) : ℝ) : ℂ)) ∂(P n)) ^ (B n s (l + 1) - B n s l))
      atTop (𝓝 (Complex.exp (-((α₀ s * Δ l * (ΘN l ⬝ᵥ (C s *ᵥ ΘN l)) / 2 : ℝ) : ℂ)))) := by
    intro s l hl
    have hl' := Finset.mem_range.1 hl
    have hpf := fun n => proj_facts (hYm n s 0) (hY1 n s) (hY0 n s) (hY2 n s) hε0 (hmI n s)
      (hmM n s) (ΘN l)
    refine block_limit P (fun n ω => ΘN l ⬝ᵥ Y n s 0 ω) (fun n => (hpf n).1)
      (fun n => (hpf n).2.1) (fun n => (hpf n).2.2.1) (fun n => (hpf n).2.2.2.1) ?_ hε0 hε1
      (fun n => (hpf n).2.2.2.2.2.1) (fun n => (hpf n).2.2.2.2.2.2) _ ?_
    · have h2 : ∀ n, ∫ ω, (ΘN l ⬝ᵥ Y n s 0 ω) ^ 2 ∂(P n) = ∑ k, ∑ k', ΘN l k * ΘN l k' *
          ∫ ω, Y n s 0 ω k * Y n s 0 ω k' ∂(P n) := fun n => (hpf n).2.2.2.2.1
      simp only [h2]
      rw [quad_eq]
      exact tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun k' _ =>
        (hC s k k').const_mul _
    · have h1 := floor_ratio (hα s) (fun n => hα0 n s) (hτN_nonneg (l + 1))
      have h2 := floor_ratio (hα s) (fun n => hα0 n s) (hτN_nonneg l)
      have h3 : (fun n : ℕ => ((B n s (l + 1) - B n s l : ℕ) : ℝ) / n) =
          fun n => (⌊α n s * n * τN (l + 1)⌋₊ : ℝ) / n - (⌊α n s * n * τN l⌋₊ : ℝ) / n := by
        funext n
        rw [Nat.cast_sub (hBmono n s l (l + 1) (by omega) (by omega)), sub_div]
      rw [h3]
      convert h1.sub h2 using 2
      simp only [hΔ]; ring
  have hprod := tendsto_finsetProd (Finset.univ : Finset S) fun s _ =>
    tendsto_finsetProd (Finset.range m) fun l hl => hblk s l hl
  have hfinal : Complex.exp (Complex.I * ((∑ l ∈ Finset.range m, Δ l * (ΘN l ⬝ᵥ c) : ℝ) : ℂ)) *
      ∏ s, ∏ l ∈ Finset.range m,
        Complex.exp (-((α₀ s * Δ l * (ΘN l ⬝ᵥ (C s *ᵥ ΘN l)) / 2 : ℝ) : ℂ)) =
      ∏ l ∈ Finset.range m, Complex.exp (Complex.I * ((Δ l * (ΘN l ⬝ᵥ c) : ℝ) : ℂ)
        - ((Δ l / 2 * (ΘN l ⬝ᵥ (A *ᵥ ΘN l)) : ℝ) : ℂ)) := by
    have e1 : ∏ s, ∏ l ∈ Finset.range m,
        Complex.exp (-((α₀ s * Δ l * (ΘN l ⬝ᵥ (C s *ᵥ ΘN l)) / 2 : ℝ) : ℂ)) =
        Complex.exp (∑ s, ∑ l ∈ Finset.range m,
          -((α₀ s * Δ l * (ΘN l ⬝ᵥ (C s *ᵥ ΘN l)) / 2 : ℝ) : ℂ)) := by
      rw [Complex.exp_sum]
      exact Finset.prod_congr rfl fun s _ => (Complex.exp_sum _ _).symm
    rw [e1, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum, sub_eq_add_neg]
    congr 1
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA, quad_sum, Finset.mul_sum, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast; ring
  rw [hRHS, ← hfinal]
  simp only [hLHS]
  exact hprod.const_mul _

theorem tclt
    (hYm : ∀ n s i, Measurable (Y n s i))
    (hind : ∀ n, iIndepFun (fun p : S × ℕ => Y n p.1 p.2) (P n))
    (hid : ∀ n s i, IdentDistrib (Y n s i) (Y n s 0) (P n) (P n))
    (hY1 : ∀ n s k, Integrable (fun ω => Y n s 0 ω k) (P n))
    (hY0 : ∀ n s k, ∫ ω, Y n s 0 ω k ∂(P n) = 0)
    (hY2 : ∀ n s k k', Integrable (fun ω => Y n s 0 ω k * Y n s 0 ω k') (P n))
    (hC : ∀ s k k', Tendsto (fun n => ∫ ω, Y n s 0 ω k * Y n s 0 ω k' ∂(P n)) atTop
      (𝓝 (C s k k')))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmI : ∀ n s, Integrable (fun ω => ‖Y n s 0 ω‖ ^ (2 + ε)) (P n))
    (hmM : ∀ n s, ∫ ω, ‖Y n s 0 ω‖ ^ (2 + ε) ∂(P n) ≤ M)
    (hα0 : ∀ n s, 0 ≤ α n s) (hα : ∀ s, Tendsto (fun n => α n s) atTop (𝓝 (α₀ s)))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {ζ : Ω' → ℝ → Fin K → ℝ}
    (hζ : IsDriftedBM c (∑ s, α₀ s • C s) P' ζ) :
    FddConvA P (Wp Y α c) P' ζ := by
  intro m τ hτ f hfC hfL
  haveI : IsProbabilityMeasure P' := hζ.1
  obtain ⟨Cf, hCf⟩ := hfC
  obtain ⟨L, hL⟩ := hfL
  set σ := Tuple.sort τ with hσ
  have hmono : Monotone (τ ∘ σ) := Tuple.monotone_sort τ
  have hWm : ∀ n t, Measurable fun ω => Wp Y α c n ω t := by
    intro n t
    have h1 : Measurable fun ω => ∑ s, ∑ i ∈ Finset.range ⌊α n s * n * t⌋₊, Y n s i ω :=
      Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun i _ => hYm n s i
    exact (h1.const_smul ((Real.sqrt n)⁻¹)).add_const (t • c)
  set f' : (Fin m → Fin K → ℝ) → ℝ := fun y => f (fun i => y (σ.symm i)) with hf'
  have hf'c : Continuous f' :=
    hL.continuous.comp (continuous_pi fun i => continuous_apply (σ.symm i))
  have key := levy_fdd P (fun n ω l => Wp Y α c n ω (τ (σ l)))
    (fun n => measurable_pi_lambda _ fun l => hWm n _) P' (fun ω l => ζ ω (τ (σ l)))
    (measurable_pi_lambda _ fun l => hζ.2.1 _)
    (fun θ => tclt_mono hYm hind hid hY1 hY0 hY2 hC hε0 hε1 hmI hmM hα0 hα hζ m (τ ∘ σ)
      (fun i => hτ _) hmono θ) f' hf'c Cf (fun x => hCf _)
  simp only [hf', Equiv.apply_symm_apply] at key
  exact key

end TCLT

/-- Slutsky, pointwise form: fdd convergence transfers along processes that are close in
probability at every fixed time of `[0,1]`. -/
theorem slutsky_pt {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {X Y : ∀ n, Ω n → ℝ → Fin K → ℝ}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {X' : Ω' → ℝ → Fin K → ℝ}
    (hXm : ∀ n t, AEMeasurable (fun ω => X n ω t) (P n))
    (hYm : ∀ n t, AEMeasurable (fun ω => Y n ω t) (P n))
    (hF : FddConvA P X P' X')
    (hcl : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {ω | ε ≤ ‖Y n ω t - X n ω t‖} ≤ ENNReal.ofReal η) :
    FddConvA P Y P' X' := by
  intro m τ hτ f hfC hfL
  obtain ⟨C, hC⟩ := hfC
  obtain ⟨L, hL⟩ := hfL
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have aem : ∀ (Z : ∀ n, Ω n → ℝ → Fin K → ℝ), (∀ n t, AEMeasurable (fun ω => Z n ω t) (P n)) →
      ∀ n, AEMeasurable (fun ω => fun i => Z n ω (τ i)) (P n) := fun Z hZ n =>
    aemeasurable_pi_lambda _ fun i => hZ n (τ i)
  have key : Tendsto (fun n => ∫ ω, f (fun i => Y n ω (τ i)) ∂(P n) -
      ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro e he
    set ε := e / (3 * ((L:ℝ) + 1)) with hε
    set η := e / (3 * (2 * C + 1)) with hη
    have hε0 : 0 < ε := by positivity
    have hη0 : 0 < η := by positivity
    have hall : ∀ᶠ n in atTop, ∀ i : Fin m,
        P n {ω | ε ≤ ‖Y n ω (τ i) - X n ω (τ i)‖} ≤ ENNReal.ofReal (η / (m + 1)) :=
      Filter.eventually_all.2 fun i => hcl (τ i) (hτ i) ε hε0 _ (by positivity)
    filter_upwards [hall] with n hn
    set E := {ω | ∃ i : Fin m, ε ≤ ‖Y n ω (τ i) - X n ω (τ i)‖} with hEdef
    set E' := toMeasurable (P n) E
    have hE'm : MeasurableSet E' := measurableSet_toMeasurable _ _
    have hPE0 : P n E ≤ ENNReal.ofReal η := by
      have hU : E = ⋃ i : Fin m, {ω | ε ≤ ‖Y n ω (τ i) - X n ω (τ i)‖} := by
        ext ω; simp [hEdef]
      rw [hU]
      refine (measure_iUnion_fintype_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hn i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hm1 : (0:ℝ) < m + 1 := by positivity
      rw [mul_div_assoc', div_le_iff₀ hm1]
      nlinarith
    have hPE : (P n).real E' ≤ η := by
      rw [measureReal_def, measure_toMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hη0.le hPE0
    have hfc : Continuous f := hL.continuous
    have hg1 : Integrable (fun ω => f (fun i => Y n ω (τ i))) (P n) :=
      Integrable.of_bound (hfc.measurable.comp_aemeasurable (aem Y hYm n)).aestronglyMeasurable
        C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC _)
    have hg2 : Integrable (fun ω => f (fun i => X n ω (τ i))) (P n) :=
      Integrable.of_bound (hfc.measurable.comp_aemeasurable (aem X hXm n)).aestronglyMeasurable
        C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC _)
    have hpt : ∀ ω, ‖f (fun i => Y n ω (τ i)) - f (fun i => X n ω (τ i))‖ ≤
        (L:ℝ) * ε + E'.indicator (fun _ => 2 * C) ω := by
      intro ω
      rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ E'
      · rw [Set.indicator_of_mem hω]
        have h1 := abs_sub (f (fun i => Y n ω (τ i))) (f (fun i => X n ω (τ i)))
        have h2 := hC (fun i => Y n ω (τ i))
        have h3 := hC (fun i => X n ω (τ i))
        have : 0 ≤ (L:ℝ) * ε := mul_nonneg L.coe_nonneg hε0.le
        linarith
      · rw [Set.indicator_of_notMem hω, add_zero]
        have hωE : ω ∉ E := fun h => hω (subset_toMeasurable _ _ h)
        have hd : dist (fun i => Y n ω (τ i)) (fun i => X n ω (τ i)) ≤ ε := by
          refine (dist_pi_le_iff hε0.le).2 fun i => ?_
          rw [dist_eq_norm]
          by_contra hlt
          exact hωE ⟨i, (not_le.1 hlt).le⟩
        rw [← Real.dist_eq]
        exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
    have hint : ‖∫ ω, f (fun i => Y n ω (τ i)) ∂(P n) - ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)‖
        ≤ (L:ℝ) * ε + 2 * C * η := by
      rw [← integral_sub hg1 hg2]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hgi : Integrable (fun ω => (L:ℝ) * ε + E'.indicator (fun _ => 2 * C) ω) (P n) :=
        (integrable_const ((L:ℝ) * ε)).add ((integrable_const (2 * C)).indicator hE'm)
      have hval : ∫ ω, ((L:ℝ) * ε + E'.indicator (fun _ => 2 * C) ω) ∂(P n) =
          (L:ℝ) * ε + (P n).real E' * (2 * C) := by
        rw [integral_add (integrable_const ((L:ℝ) * ε))
          ((integrable_const (2 * C)).indicator hE'm), integral_const,
          integral_indicator_const _ hE'm]
        simp only [probReal_univ, smul_eq_mul, one_mul]
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hgi
        (ae_of_all _ hpt)).trans ?_
      rw [hval]
      have : (P n).real E' * (2 * C) ≤ η * (2 * C) :=
        mul_le_mul_of_nonneg_right hPE (by linarith)
      linarith
    rw [dist_eq_norm, sub_zero]
    refine lt_of_le_of_lt hint ?_
    have h1 : (L:ℝ) * ε ≤ e / 3 := by
      have : ((L:ℝ) + 1) * ε = e / 3 := by rw [hε]; field_simp
      nlinarith
    have h2 : 2 * C * η ≤ e / 3 := by
      have : (2 * C + 1) * η = e / 3 := by rw [hη]; field_simp
      nlinarith
    linarith
  have := (hF m τ hτ f ⟨C, hC⟩ ⟨L, hL⟩).add key
  rw [add_zero] at this
  exact this.congr fun n => by ring

end FddA

/-! ## F2: pointwise approximation of the netput by partial sums at deterministic indices -/

namespace FddB

open Filter Topology MeasureTheory ProbabilityTheory RW

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)]

lemma third_sum {η : ℝ} (hη : 0 < η) :
    ENNReal.ofReal (η / 3) + (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) =
      ENNReal.ofReal η := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

/-- a random index within `δ n` of a deterministic one moves a walk by `o(√n)`. -/
lemma idx_close (P : ∀ n, Measure (Ωs n)) (ξ : ∀ n, ℕ → Ωs n → ℝ)
    (hmod : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤ ENNReal.ofReal η)
    (Nr : ∀ n, Ωs n → ℕ) (jd : ℕ → ℕ)
    (hT : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | T * n < Nr n ω} ≤ ENNReal.ofReal η)
    (hTd : ∃ T : ℝ, ∀ᶠ n : ℕ in atTop, (jd n : ℝ) ≤ T * n)
    (hcl : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      P n {ω | δ * n < |(Nr n ω : ℝ) - jd n|} ≤ ENNReal.ofReal η)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, P n {ω | ε * Real.sqrt n ≤
      |psum (ξ n) (Nr n ω) ω - psum (ξ n) (jd n) ω|} ≤ ENNReal.ofReal η := by
  obtain ⟨T1, hT1, hT1e⟩ := hT (η / 3) (by linarith)
  obtain ⟨T2, hT2⟩ := hTd
  set T := max T1 T2 + 1 with hTdef
  have hTpos : 0 < T := by have := le_max_left T1 T2; linarith
  obtain ⟨δ, hδ, hδe⟩ := hmod T hTpos ε hε (η / 3) (by linarith)
  filter_upwards [hT1e, hT2, hδe, hcl δ hδ (η / 3) (by linarith)] with n h1 h2 h3 h4
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hsub : {ω | ε * Real.sqrt n ≤ |psum (ξ n) (Nr n ω) ω - psum (ξ n) (jd n) ω|} ⊆
      {ω | T1 * n < Nr n ω} ∪ ({ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ∪
        {ω | δ * n < |(Nr n ω : ℝ) - jd n|}) := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_exists, not_and,
      not_le] at hc
    obtain ⟨hc1, hc2, hc3⟩ := hc
    have hNT : (Nr n ω : ℝ) ≤ T * n := hc1.trans (by nlinarith [le_max_left T1 T2])
    have hjT : (jd n : ℝ) ≤ T * n := h2.trans (by nlinarith [le_max_right T1 T2])
    rw [abs_le] at hc3
    rcases le_total (Nr n ω) (jd n) with hle | hle
    · have := hc2 (Nr n ω) (jd n) hle (by linarith [hc3.1]) hjT
      rw [abs_sub_comm] at this
      exact absurd hω (not_le.2 this)
    · have := hc2 (jd n) (Nr n ω) hle (by linarith [hc3.2]) hNT
      exact absurd hω (not_le.2 this)
  calc P n {ω | ε * Real.sqrt n ≤ |psum (ξ n) (Nr n ω) ω - psum (ξ n) (jd n) ω|}
      ≤ P n {ω | T1 * n < Nr n ω} + (P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
          (j:ℝ) ≤ T * n ∧ ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} +
          P n {ω | δ * n < |(Nr n ω : ℝ) - jd n|}) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ ENNReal.ofReal (η / 3) + (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) :=
        add_le_add h1 (add_le_add h3 h4)
    _ = ENNReal.ofReal η := third_sum hη

lemma psum_strictMono {Ω : Type} {v : ℕ → Ω → ℝ} (hpos : ∀ i ω, 0 < v i ω) (ω : Ω) :
    StrictMono (fun l => psum v l ω) :=
  strictMono_nat_of_lt_succ fun l => by
    simp only [psum, Finset.sum_range_succ]; linarith [hpos l ω]

lemma psum_zero {Ω : Type} (v : ℕ → Ω → ℝ) (ω : Ω) : psum v 0 ω = 0 := by simp [psum]

/-- the counting process at a fixed time is `O(n)` and within `o(n)` of `⌊n t / m⌋`. -/
lemma cnt_near (P : ∀ n, Measure (Ωs n)) (v : ∀ n, ℕ → Ωs n → ℝ)
    (hpos : ∀ n i ω, 0 < v n i ω) (m : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (hm : ∀ᶠ n in atTop, a ≤ m n)
    (hMT : MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) - (m n)⁻¹ * (n * t))))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | T * n < cnt (fun l => psum (v n) l ω) (n * t)} ≤ ENNReal.ofReal η) ∧
    (∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      P n {ω | δ * n < |(cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
        ⌊(m n)⁻¹ * n * t⌋₊|} ≤ ENNReal.ofReal η) := by
  have h0 : ∀ (n : ℕ) (ω : Ωs n), (Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * 0) : ℝ) -
      (m n)⁻¹ * (n * 0)) = 0 := by
    intro n ω
    rw [mul_zero, NetT.cnt_zero (psum_zero _ ω) (psum_strictMono (hpos n) ω)]
    simp
  have hbd : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | M < |(Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
        (m n)⁻¹ * (n * t))|} ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨M, hM, N0, hN0⟩ := MT_bdd hMT h0 η hη
    refine ⟨M, hM, eventually_atTop.2 ⟨N0, fun n hn => ?_⟩⟩
    refine le_trans (measure_mono ?_) (hN0 n hn)
    intro ω hω
    exact ⟨t, ht, hω⟩
  -- on the good event: `|cnt - n t / m| ≤ M √n`
  have hgood : ∀ (M : ℝ) (n : ℕ) (ω : Ωs n), 1 ≤ n → a ≤ m n →
      ¬ M < |(Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
        (m n)⁻¹ * (n * t))| →
      |(cnt (fun l => psum (v n) l ω) (n * t) : ℝ) - (m n)⁻¹ * (n * t)| ≤ M * Real.sqrt n := by
    intro M n ω hn ham h
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [not_lt, abs_mul, abs_of_pos (inv_pos.2 hs), inv_mul_le_iff₀ hs] at h
    linarith
  refine ⟨fun η hη => ?_, fun δ hδ η hη => ?_⟩
  · obtain ⟨M, hM, hMe⟩ := hbd η hη
    refine ⟨a⁻¹ + M, by positivity, ?_⟩
    filter_upwards [hMe, hm, eventually_ge_atTop 1] with n h1 h2 h3
    refine (measure_mono fun ω hω => ?_).trans h1
    by_contra hc
    have hg := hgood M n ω h3 h2 hc
    have hnp : (1:ℝ) ≤ n := by exact_mod_cast h3
    have hsq : Real.sqrt n ≤ n := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hlam : (m n)⁻¹ ≤ a⁻¹ := inv_anti₀ ha h2
    have hlt : (m n)⁻¹ * (n * t) ≤ a⁻¹ * n := by
      have : (m n)⁻¹ * (n * t) ≤ (m n)⁻¹ * n :=
        mul_le_mul_of_nonneg_left (by nlinarith [ht.2]) (inv_nonneg.2 (ha.le.trans h2))
      nlinarith
    have hω' : (a⁻¹ + M) * n < cnt (fun l => psum (v n) l ω) (n * t) := hω
    rw [abs_le] at hg
    nlinarith
  · obtain ⟨M, hM, hMe⟩ := hbd η hη
    have hev : ∀ᶠ n : ℕ in atTop, M * Real.sqrt n + 1 ≤ δ * n := by
      filter_upwards [eventually_ge_atTop (⌈((M + 1) / δ) ^ 2⌉₊ + 1)] with n hn
      have hn1 : ((M + 1) / δ) ^ 2 + 1 ≤ (n : ℝ) := by
        have := Nat.le_ceil (((M + 1) / δ) ^ 2)
        have h' : ((⌈((M + 1) / δ) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
        push_cast at h'; linarith
      have hnp : (0:ℝ) < n := by nlinarith [sq_nonneg ((M + 1) / δ)]
      have hs1 : 1 ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by norm_num) hnp.le]; nlinarith [sq_nonneg ((M + 1) / δ)]
      have hs2 : (M + 1) / δ ≤ Real.sqrt n :=
        Real.le_sqrt_of_sq_le (by nlinarith)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnp.le
      have : M + 1 ≤ δ * Real.sqrt n := by rwa [div_le_iff₀ hδ, mul_comm] at hs2
      nlinarith
    filter_upwards [hMe, hm, eventually_ge_atTop 1, hev] with n h1 h2 h3 h4
    refine (measure_mono fun ω hω => ?_).trans h1
    by_contra hc
    have hg := hgood M n ω h3 h2 hc
    have hfl1 := Nat.floor_le (show 0 ≤ (m n)⁻¹ * n * t by
      have := ha.le.trans h2; have := ht.1; positivity)
    have hfl2 := Nat.lt_floor_add_one ((m n)⁻¹ * n * t)
    have hω' : δ * n < |(cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
        ⌊(m n)⁻¹ * n * t⌋₊| := hω
    have e : (m n)⁻¹ * (n * t) = (m n)⁻¹ * n * t := by ring
    rw [e] at hg
    rw [abs_le] at hg
    rw [lt_abs] at hω'
    rcases hω' with h | h <;> linarith

end FddB

namespace FddB

open Filter Topology MeasureTheory ProbabilityTheory RW

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)]

lemma psum_split {Ω : Type} (v : ℕ → Ω → ℝ) (m : ℝ) (l : ℕ) (ω : Ω) :
    psum v l ω = l * m + psum (fun i ω => v i ω - m) l ω := by
  simp only [psum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- renewal inversion at a fixed time, in probability. -/
lemma ren_point (P : ∀ n, Measure (Ωs n)) (v : ∀ n, ℕ → Ωs n → ℝ)
    (hpos : ∀ n i ω, 0 < v n i ω)
    (hdiv : ∀ n, ∀ᵐ ω ∂(P n), Tendsto (fun l => psum (v n) l ω) atTop atTop)
    (m : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (hm : ∀ᶠ n in atTop, a ≤ m n)
    (hMT : MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) - (m n)⁻¹ * (n * t))))
    (hmod : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (fun i ω => v n i ω - m n) j ω -
          psum (fun i ω => v n i ω - m n) i ω|} ≤ ENNReal.ofReal η)
    (hjump : ∀ T : ℝ, 0 < T → ∀ θ : ℝ, 0 < θ → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |v n l ω - m n|} ≤ ENNReal.ofReal η)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, P n {ω | ε ≤ |(Real.sqrt n)⁻¹ *
      (((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) - (m n)⁻¹ * (n * t)) -
        ((⌊(m n)⁻¹ * n * t⌋₊ : ℝ) - (m n)⁻¹ * psum (v n) ⌊(m n)⁻¹ * n * t⌋₊ ω))|} ≤
      ENNReal.ofReal η := by
  obtain ⟨hTb, hcl⟩ := cnt_near P v hpos m ha hm hMT ht
  set ε' := ε * a / 3 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨T, hT0, hTe⟩ := hTb (η / 3) (by linarith)
  have hidx := idx_close P (fun n i ω => v n i ω - m n) hmod
    (fun n ω => cnt (fun l => psum (v n) l ω) (n * t)) (fun n => ⌊(m n)⁻¹ * n * t⌋₊) hTb
    ⟨a⁻¹, by
      filter_upwards [hm] with n hn
      have h1 := Nat.floor_le (show 0 ≤ (m n)⁻¹ * n * t by
        have := ha.le.trans hn; have := ht.1; positivity)
      have : (m n)⁻¹ * n * t ≤ a⁻¹ * n := by
        have hl : (m n)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hn
        have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
        have : (m n)⁻¹ * n * t ≤ (m n)⁻¹ * n * 1 :=
          mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (inv_nonneg.2 (ha.le.trans hn)) hn0)
        nlinarith
      linarith⟩ hcl ε' hε'0 (η / 3) (by linarith)
  have hJ := hjump T hT0 ε' hε'0 (η / 3) (by linarith)
  have hsq : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ ≤ ε / 3 := by
    have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop)).eventually (ge_mem_nhds (show (0:ℝ) < ε / 3 by positivity))
    exact this
  filter_upwards [hidx, hJ, hTe, hsq, hm, eventually_ge_atTop 1] with n h1 h2 h3 h4 h5 h6
  set N : Ωs n → ℕ := fun ω => cnt (fun l => psum (v n) l ω) (n * t) with hN
  set j := ⌊(m n)⁻¹ * n * t⌋₊ with hj
  set W : ℕ → Ωs n → ℝ := fun l ω => psum (fun i ω => v n i ω - m n) l ω with hW
  have hmpos : 0 < m n := ha.trans_le h5
  have hnp : (0:ℝ) < n := by exact_mod_cast h6
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnp
  have hnt : 0 ≤ (n:ℝ) * t := mul_nonneg hnp.le ht.1
  set Bad := {ω : Ωs n | ¬ Tendsto (fun l => psum (v n) l ω) atTop atTop} with hBad
  have hBad0 : P n Bad = 0 := by
    rw [hBad, ← ae_iff]; exact hdiv n
  have hsub : {ω | ε ≤ |(Real.sqrt n)⁻¹ *
      (((N ω : ℝ) - (m n)⁻¹ * (n * t)) - ((j : ℝ) - (m n)⁻¹ * psum (v n) j ω))|} ⊆
      Bad ∪ ({ω | ε' * Real.sqrt n ≤ |W (N ω) ω - W j ω|} ∪
        ({ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ ε' * Real.sqrt n < |v n l ω - m n|} ∪
          {ω | T * n < N ω})) := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le, not_exists,
      not_and, hBad, not_not] at hc
    obtain ⟨hdivω, hc1, hc2, hc3⟩ := hc
    have hspec := cnt_spec (psum_zero _ ω) (psum_strictMono (hpos n) ω) hdivω hnt
    have hNT : (N ω : ℝ) ≤ T * n := hc3
    have hjmp : |v n (N ω) ω - m n| ≤ ε' * Real.sqrt n := hc2 (N ω) hNT
    -- the identity
    have hFN := psum_split (v n) (m n) (N ω) ω
    have hFN1 := psum_split (v n) (m n) (N ω + 1) ω
    have hFj := psum_split (v n) (m n) j ω
    have hstep : psum (v n) (N ω + 1) ω = psum (v n) (N ω) ω + v n (N ω) ω := by
      simp only [psum, Finset.sum_range_succ]
    have hr0 : 0 ≤ n * t - psum (v n) (N ω) ω := by linarith [hspec.1]
    have hr1 : n * t - psum (v n) (N ω) ω < v n (N ω) ω := by linarith [hspec.2]
    have hE : ((N ω : ℝ) - (m n)⁻¹ * (n * t)) - ((j : ℝ) - (m n)⁻¹ * psum (v n) j ω) =
        -(m n)⁻¹ * (W (N ω) ω - W j ω) - (m n)⁻¹ * (n * t - psum (v n) (N ω) ω) := by
      simp only [hW]
      rw [hFN, hFj]
      field_simp
      ring
    have hω2 : ε ≤ |(Real.sqrt n)⁻¹ * (((N ω : ℝ) - (m n)⁻¹ * (n * t)) -
        ((j : ℝ) - (m n)⁻¹ * psum (v n) j ω))| := hω
    rw [hE] at hω2
    have hlam : (m n)⁻¹ ≤ a⁻¹ := inv_anti₀ ha h5
    have hlam0 : 0 < (m n)⁻¹ := inv_pos.2 hmpos
    have hb1 : |W (N ω) ω - W j ω| < ε' * Real.sqrt n := hc1
    have hv : v n (N ω) ω ≤ m n + ε' * Real.sqrt n := by
      rw [abs_le] at hjmp; linarith [hjmp.2]
    -- bound the error
    have hbound : |-(m n)⁻¹ * (W (N ω) ω - W j ω) - (m n)⁻¹ * (n * t - psum (v n) (N ω) ω)| <
        (m n)⁻¹ * (ε' * Real.sqrt n) + (m n)⁻¹ * (m n + ε' * Real.sqrt n) := by
      refine (abs_sub _ _).trans_lt ?_
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos hlam0, abs_of_nonneg hr0]
      have := mul_lt_mul_of_pos_left hb1 hlam0
      have := mul_le_mul_of_nonneg_left (hr1.le.trans hv) hlam0.le
      linarith
    rw [abs_mul, abs_of_pos (inv_pos.2 hs)] at hω2
    have hfin : (Real.sqrt n)⁻¹ * ((m n)⁻¹ * (ε' * Real.sqrt n) +
        (m n)⁻¹ * (m n + ε' * Real.sqrt n)) ≤ ε := by
      have e1 : (Real.sqrt n)⁻¹ * ((m n)⁻¹ * (ε' * Real.sqrt n) +
          (m n)⁻¹ * (m n + ε' * Real.sqrt n)) = 2 * (m n)⁻¹ * ε' + (Real.sqrt n)⁻¹ := by
        field_simp; ring
      rw [e1]
      have : (m n)⁻¹ * ε' ≤ a⁻¹ * ε' := mul_le_mul_of_nonneg_right hlam hε'0.le
      have e2 : a⁻¹ * ε' = ε / 3 := by rw [hε']; field_simp
      linarith
    have := mul_lt_mul_of_pos_left hbound (inv_pos.2 hs)
    linarith
  calc P n _ ≤ P n Bad + (P n {ω | ε' * Real.sqrt n ≤ |W (N ω) ω - W j ω|} +
        (P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ ε' * Real.sqrt n < |v n l ω - m n|} +
          P n {ω | T * n < N ω})) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl
          ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))))
    _ ≤ 0 + (ENNReal.ofReal (η / 3) + (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3))) :=
        add_le_add hBad0.le (add_le_add h1 (add_le_add h2 h3))
    _ = ENNReal.ofReal η := by rw [zero_add, third_sum hη]

end FddB

namespace FddB

open Filter Topology MeasureTheory ProbabilityTheory RW

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)]

/-- random time change of a walk at a fixed time, in probability. -/
lemma rout_point (P : ∀ n, Measure (Ωs n)) (v : ∀ n, ℕ → Ωs n → ℝ)
    (hpos : ∀ n i ω, 0 < v n i ω) (m : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (hm : ∀ᶠ n in atTop, a ≤ m n)
    (hMT : MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) - (m n)⁻¹ * (n * t))))
    (ρ : ∀ n, ℕ → Ωs n → ℝ)
    (hmod : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (ρ n) j ω - psum (ρ n) i ω|} ≤ ENNReal.ofReal η)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, P n {ω | ε ≤ |(Real.sqrt n)⁻¹ *
      (psum (ρ n) (cnt (fun l => psum (v n) l ω) (n * t)) ω -
        psum (ρ n) ⌊(m n)⁻¹ * n * t⌋₊ ω)|} ≤ ENNReal.ofReal η := by
  obtain ⟨hTb, hcl⟩ := cnt_near P v hpos m ha hm hMT ht
  have hidx := idx_close P ρ hmod
    (fun n ω => cnt (fun l => psum (v n) l ω) (n * t)) (fun n => ⌊(m n)⁻¹ * n * t⌋₊) hTb
    ⟨a⁻¹, by
      filter_upwards [hm] with n hn
      have h1 := Nat.floor_le (show 0 ≤ (m n)⁻¹ * n * t by
        have := ha.le.trans hn; have := ht.1; positivity)
      have hl : (m n)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hn
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have : (m n)⁻¹ * n * t ≤ (m n)⁻¹ * n * 1 :=
        mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (inv_nonneg.2 (ha.le.trans hn)) hn0)
      nlinarith⟩ hcl ε hε η hη
  filter_upwards [hidx, eventually_ge_atTop 1] with n h1 hn
  refine le_trans (measure_mono fun ω hω => ?_) h1
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hω' : ε ≤ |(Real.sqrt n)⁻¹ * (psum (ρ n) (cnt (fun l => psum (v n) l ω) (n * t)) ω -
      psum (ρ n) ⌊(m n)⁻¹ * n * t⌋₊ ω)| := hω
  rw [abs_mul, abs_of_pos (inv_pos.2 hs), ← div_eq_inv_mul, le_div_iff₀ hs] at hω'
  show ε * Real.sqrt n ≤ _
  exact hω'

end FddB

/-! ## F2 network: sources and the pathwise decomposition of `ζⁿ - Wₙ` -/

namespace FddN

open Filter Topology MeasureTheory ProbabilityTheory Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}

/-- the primitive sources: arrivals at `k ∈ J`, services and routings at every station. -/
abbrev Src (K : ℕ) (J : Finset (Fin K)) : Type := {k // k ∈ J} ⊕ Fin K ⊕ Fin K

variable {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

/-- the centred source vectors. -/
noncomputable def Ysrc (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) :
    ∀ n, Src K J → ℕ → Ω n → Fin K → ℝ
  | n, Sum.inl k, i, ω =>
      (-((net n).lam k.1 * ((net n).u k.1 i ω - ((net n).lam k.1)⁻¹))) • Pi.single k.1 1
  | n, Sum.inr (Sum.inl k), i, ω =>
      (-((net n).mu k * ((net n).v k i ω - ((net n).mu k)⁻¹))) • (R k - Pi.single k 1)
  | n, Sum.inr (Sum.inr k), i, ω => routeVec ((net n).φ k i ω) - R k

/-- the source rates. -/
noncomputable def αsrc (net : ∀ n, Network K J (P n)) : ℕ → Src K J → ℝ
  | n, Sum.inl k => (net n).lam k.1
  | n, Sum.inr (Sum.inl k) => (net n).mu k
  | n, Sum.inr (Sum.inr k) => (net n).mu k

lemma sum_arr {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} (N : Network K J μ)
    {k : Fin K} (hk : k ∈ J) (j : ℕ) (ω : Ω₁) :
    ∑ i ∈ Finset.range j, (-(N.lam k * (N.u k i ω - (N.lam k)⁻¹))) • (Pi.single k 1 : Fin K → ℝ) =
      ((j : ℝ) - N.lam k * N.U k j ω) • Pi.single k 1 := by
  have hl : N.lam k ≠ 0 := (NetT.lam_pos' N hk).ne'
  rw [← Finset.sum_smul]
  congr 1
  simp only [Network.U, Finset.mul_sum, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hl, mul_one]
  ring

lemma sum_serv {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} (N : Network K J μ)
    (k : Fin K) (w : Fin K → ℝ) (j : ℕ) (ω : Ω₁) :
    ∑ i ∈ Finset.range j, (-(N.mu k * (N.v k i ω - (N.mu k)⁻¹))) • w =
      ((j : ℝ) - N.mu k * N.V k j ω) • w := by
  have hl : N.mu k ≠ 0 := (NetT.mu_pos' N k).ne'
  rw [← Finset.sum_smul]
  congr 1
  simp only [Network.V, Finset.mul_sum, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hl, mul_one]
  ring

lemma Avec_eq {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} (N : Network K J μ)
    (t : ℝ) (ω : Ω₁) :
    N.Avec t ω = ∑ k : {k // k ∈ J}, (N.A k.1 t ω : ℝ) • (Pi.single k.1 1 : Fin K → ℝ) := by
  classical
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_coe_sort J (fun k => if j = k then (N.A k t ω : ℝ) else 0), Finset.sum_ite_eq]
  by_cases hj : j ∈ J
  · simp [Network.Avec, hj]
  · simp [Network.Avec, Network.A, hj]

lemma nu_sub_mu {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} (N : Network K J μ)
    {R : Matrix (Fin K) (Fin K) ℝ} (hR : N.routing = R) :
    N.nu - N.mu = ∑ k : {k // k ∈ J}, N.lam k.1 • (Pi.single k.1 1 : Fin K → ℝ) +
      ∑ k, N.mu k • (R k - Pi.single k 1) := by
  classical
  funext j
  simp only [Network.nu, Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, mul_sub, Finset.sum_sub_distrib,
    Matrix.vecMul, dotProduct, hR]
  rw [Finset.sum_coe_sort J (fun k => if j = k then N.lam k else 0), Finset.sum_ite_eq,
    Finset.sum_ite_eq]
  have hl : N.lam j = if j ∈ J then N.lam j else 0 := by
    by_cases hj : j ∈ J
    · simp [hj]
    · simp [hj, Network.lam]
  simp only [Finset.mem_univ, if_true]
  rw [← hl]
  have : ∑ x, N.mu x * R x j = ∑ x, N.mu x * R x j := rfl
  ring

end FddN

namespace FddN

open Filter Topology MeasureTheory ProbabilityTheory Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

/-- arrival error at station `k`. -/
noncomputable def EA (n : ℕ) (N : Network K J (P n)) (k : Fin K) (t : ℝ) (ω : Ω n) : ℝ :=
  ((N.A k (n * t) ω : ℝ) - N.lam k * (n * t)) -
    ((⌊N.lam k * n * t⌋₊ : ℝ) - N.lam k * N.U k ⌊N.lam k * n * t⌋₊ ω)

/-- service error at station `k`. -/
noncomputable def ES (n : ℕ) (N : Network K J (P n)) (k : Fin K) (t : ℝ) (ω : Ω n) : ℝ :=
  ((N.S k (n * t) ω : ℝ) - N.mu k * (n * t)) -
    ((⌊N.mu k * n * t⌋₊ : ℝ) - N.mu k * N.V k ⌊N.mu k * n * t⌋₊ ω)

/-- routing error at station `k`. -/
noncomputable def ER (n : ℕ) (N : Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (k : Fin K)
    (t : ℝ) (ω : Ω n) : Fin K → ℝ :=
  ∑ i ∈ Finset.range (N.S k (n * t) ω), (routeVec (N.φ k i ω) - R k) -
    ∑ i ∈ Finset.range ⌊N.mu k * n * t⌋₊, (routeVec (N.φ k i ω) - R k)

lemma decomp (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    (hR : ∀ n, (net n).routing = R) (c : Fin K → ℝ) (n : ℕ) (ω : Ω n) (t : ℝ) :
    diffScale n (fun s => (net n).X s ω) t - FddA.Wp (Ysrc net R) (αsrc net) c n ω t =
      (Real.sqrt n)⁻¹ • (∑ k : {k // k ∈ J}, EA n (net n) k.1 t ω • (Pi.single k.1 1 : Fin K → ℝ)
        + ∑ k, (ES n (net n) k t ω • (R k - Pi.single k 1) + ER n (net n) R k t ω))
      + (((Real.sqrt n)⁻¹ * (n * t)) • ((net n).nu - (net n).mu) - t • c) := by
  have hW : FddA.Wp (Ysrc net R) (αsrc net) c n ω t = (Real.sqrt n)⁻¹ • (
      ∑ k : {k // k ∈ J}, ((⌊(net n).lam k.1 * n * t⌋₊ : ℝ) -
        (net n).lam k.1 * (net n).U k.1 ⌊(net n).lam k.1 * n * t⌋₊ ω) •
          (Pi.single k.1 1 : Fin K → ℝ)
      + (∑ k, ((⌊(net n).mu k * n * t⌋₊ : ℝ) - (net n).mu k * (net n).V k ⌊(net n).mu k * n * t⌋₊ ω)
          • (R k - Pi.single k 1)
        + ∑ k, ∑ i ∈ Finset.range ⌊(net n).mu k * n * t⌋₊, (routeVec ((net n).φ k i ω) - R k)))
      + t • c := by
    simp only [FddA.Wp, Fintype.sum_sum_type, Ysrc, αsrc]
    congr 3
    · exact Finset.sum_congr rfl fun k _ => sum_arr (net n) k.2 _ ω
    · congr 1
      exact Finset.sum_congr rfl fun k _ => sum_serv (net n) k _ _ ω
  have T1 : ∀ k : {k // k ∈ J}, ((net n).A k.1 (n * t) ω : ℝ) • (Pi.single k.1 1 : Fin K → ℝ) -
      ((⌊(net n).lam k.1 * n * t⌋₊ : ℝ) - (net n).lam k.1 * (net n).U k.1
        ⌊(net n).lam k.1 * n * t⌋₊ ω) • (Pi.single k.1 1 : Fin K → ℝ) =
      EA n (net n) k.1 t ω • (Pi.single k.1 1 : Fin K → ℝ) +
        (n * t * (net n).lam k.1) • (Pi.single k.1 1 : Fin K → ℝ) := by
    intro k
    rw [← sub_smul, ← add_smul]
    congr 1
    simp only [EA]; ring
  have T2 : ∀ k : Fin K, (net n).Shat k (n * t) ω -
      ((⌊(net n).mu k * n * t⌋₊ : ℝ) - (net n).mu k * (net n).V k ⌊(net n).mu k * n * t⌋₊ ω) •
        (R k - Pi.single k 1) -
      ∑ i ∈ Finset.range ⌊(net n).mu k * n * t⌋₊, (routeVec ((net n).φ k i ω) - R k) =
      ES n (net n) k t ω • (R k - Pi.single k 1) + ER n (net n) R k t ω +
        (n * t * (net n).mu k) • (R k - Pi.single k 1) := by
    intro k
    simp only [Network.Shat, ES, ER]
    rw [Finset.sum_sub_distrib (s := Finset.range ((net n).S k (n * t) ω)), Finset.sum_const,
      Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
    module
  have key : (net n).X (n * t) ω - ((∑ k : {k // k ∈ J}, ((⌊(net n).lam k.1 * n * t⌋₊ : ℝ) -
        (net n).lam k.1 * (net n).U k.1 ⌊(net n).lam k.1 * n * t⌋₊ ω) •
          (Pi.single k.1 1 : Fin K → ℝ)
      + (∑ k, ((⌊(net n).mu k * n * t⌋₊ : ℝ) - (net n).mu k * (net n).V k ⌊(net n).mu k * n * t⌋₊ ω)
          • (R k - Pi.single k 1)
        + ∑ k, ∑ i ∈ Finset.range ⌊(net n).mu k * n * t⌋₊, (routeVec ((net n).φ k i ω) - R k)))) =
      (∑ k : {k // k ∈ J}, EA n (net n) k.1 t ω • (Pi.single k.1 1 : Fin K → ℝ)
        + ∑ k, (ES n (net n) k t ω • (R k - Pi.single k 1) + ER n (net n) R k t ω)) +
      (n * t) • ((net n).nu - (net n).mu) := by
    rw [nu_sub_mu (net n) (hR n), smul_add, Finset.smul_sum, Finset.smul_sum]
    simp only [smul_smul]
    have h1 : ∑ k : {k // k ∈ J}, ((net n).A k.1 (n * t) ω : ℝ) • (Pi.single k.1 1 : Fin K → ℝ) -
        ∑ k : {k // k ∈ J}, ((⌊(net n).lam k.1 * n * t⌋₊ : ℝ) - (net n).lam k.1 * (net n).U k.1
          ⌊(net n).lam k.1 * n * t⌋₊ ω) • (Pi.single k.1 1 : Fin K → ℝ) =
        ∑ k : {k // k ∈ J}, EA n (net n) k.1 t ω • (Pi.single k.1 1 : Fin K → ℝ) +
        ∑ k : {k // k ∈ J}, (n * t * (net n).lam k.1) • (Pi.single k.1 1 : Fin K → ℝ) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => T1 k
    have h2 : ∑ k, (net n).Shat k (n * t) ω -
        ∑ k, ((⌊(net n).mu k * n * t⌋₊ : ℝ) - (net n).mu k * (net n).V k ⌊(net n).mu k * n * t⌋₊ ω) •
          (R k - Pi.single k 1) -
        ∑ k, ∑ i ∈ Finset.range ⌊(net n).mu k * n * t⌋₊, (routeVec ((net n).φ k i ω) - R k) =
        ∑ k, (ES n (net n) k t ω • (R k - Pi.single k 1) + ER n (net n) R k t ω) +
        ∑ k, (n * t * (net n).mu k) • (R k - Pi.single k 1) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => T2 k
    simp only [Network.X, Avec_eq]
    linear_combination (norm := module) h1 + h2
  rw [hW, diffScale]
  linear_combination (norm := module) (Real.sqrt n)⁻¹ • key
end FddN

namespace FddC

open Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}

abbrev Src (K : ℕ) (J : Finset (Fin K)) : Type := {k // k ∈ J} ⊕ Fin K ⊕ Fin K

noncomputable def α0 (lam mu : Fin K → ℝ) : Src K J → ℝ
  | Sum.inl k => lam k.1
  | Sum.inr (Sum.inl k) => mu k
  | Sum.inr (Sum.inr k) => mu k

noncomputable def Clim (R : Matrix (Fin K) (Fin K) ℝ) (lam a mu s : Fin K → ℝ) :
    Src K J → Matrix (Fin K) (Fin K) ℝ
  | Sum.inl k => (lam k.1 ^ 2 * a k.1) •
      Matrix.vecMulVec (Pi.single k.1 1 : Fin K → ℝ) (Pi.single k.1 1)
  | Sum.inr (Sum.inl k) => (mu k ^ 2 * s k) •
      Matrix.vecMulVec (R k - Pi.single k 1) (R k - Pi.single k 1)
  | Sum.inr (Sum.inr k) => Matrix.diagonal (R k) - Matrix.vecMulVec (R k) (R k)

lemma part_A (lam a : Fin K → ℝ) (hJ : ∀ k ∉ J, lam k = 0) (i j : Fin K) :
    ∑ k : {k // k ∈ J}, lam k.1 * (lam k.1 ^ 2 * a k.1 *
      ((Pi.single k.1 1 : Fin K → ℝ) i * (Pi.single k.1 1 : Fin K → ℝ) j)) =
      if i = j then lam i ^ 3 * a i else 0 := by
  classical
  rw [Finset.sum_coe_sort J (fun k => lam k * (lam k ^ 2 * a k *
      ((Pi.single k 1 : Fin K → ℝ) i * (Pi.single k 1 : Fin K → ℝ) j)))]
  have hext : ∑ k ∈ J, lam k * (lam k ^ 2 * a k *
      ((Pi.single k 1 : Fin K → ℝ) i * (Pi.single k 1 : Fin K → ℝ) j)) =
      ∑ k, lam k * (lam k ^ 2 * a k *
      ((Pi.single k 1 : Fin K → ℝ) i * (Pi.single k 1 : Fin K → ℝ) j)) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
    rw [hJ k hk, zero_mul]
  rw [hext]
  simp only [Pi.single_apply]
  by_cases hij : i = j
  · subst hij
    simp only [if_true, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]; ring
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i = k
    · subst hik; simp [hij, Ne.symm hij]
    · simp [hik]

lemma cov_eq (R : Matrix (Fin K) (Fin K) ℝ) (lam a mu s : Fin K → ℝ)
    (hJ : ∀ k ∉ J, lam k = 0) :
    ∑ σ : Src K J, α0 lam mu σ • Clim (J := J) R lam a mu s σ = covA lam a mu s R := by
  classical
  ext i j
  simp only [Fintype.sum_sum_type, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, α0,
    Clim, Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.diagonal_apply, Pi.sub_apply,
    smul_eq_mul]
  rw [part_A lam a hJ i j]
  -- services and routings
  have hS : ∑ k, mu k * (mu k ^ 2 * s k * ((R k i - (Pi.single k 1 : Fin K → ℝ) i) *
      (R k j - (Pi.single k 1 : Fin K → ℝ) j))) =
      ∑ k, mu k ^ 3 * s k * R k i * R k j - mu j ^ 3 * s j * R j i - mu i ^ 3 * s i * R i j +
        (if i = j then mu i ^ 3 * s i else 0) := by
    have e : ∀ k, mu k * (mu k ^ 2 * s k * ((R k i - (Pi.single k 1 : Fin K → ℝ) i) *
        (R k j - (Pi.single k 1 : Fin K → ℝ) j))) =
        mu k ^ 3 * s k * R k i * R k j - (if j = k then mu k ^ 3 * s k * R k i else 0) -
          (if i = k then mu k ^ 3 * s k * R k j else 0) +
          (if i = k then (if j = k then mu k ^ 3 * s k else 0) else 0) := by
      intro k
      simp only [Pi.single_apply]
      split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hR : ∑ k, mu k * ((if i = j then R k i else 0) - R k i * R k j) =
      (if i = j then ∑ k, mu k * R k i else 0) - ∑ k, mu k * (R k i * R k j) := by
    by_cases hij : i = j
    · subst hij; simp [mul_sub, Finset.sum_sub_distrib]
    · simp [hij]
  rw [hS, hR]
  simp only [covA]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    have : ∑ l, mu l * R l i * (1 - R l i + R l i * mu l ^ 2 * s l) =
        ∑ l, mu l * R l i - ∑ l, mu l * (R l i * R l i) + ∑ l, mu l ^ 3 * s l * R l i * R l i := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]; ring
  · simp only [if_neg hij]
    have : ∑ l, mu l * R l i * R l j * (1 - mu l ^ 2 * s l) =
        ∑ l, mu l * (R l i * R l j) - ∑ l, mu l ^ 3 * s l * R l i * R l j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]; ring

end FddC

namespace FddS

open Filter Topology MeasureTheory

/-- a finite sum of terms that are small in probability is small in probability. -/
lemma small_sum {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    {ι : Type} [Fintype ι] (Z : ι → ∀ n, Ω n → ℝ)
    (hZ : ∀ q, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {ω | ε ≤ |Z q n ω|} ≤ ENNReal.ofReal η) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {ω | ε ≤ ∑ q, |Z q n ω|} ≤ ENNReal.ofReal η := by
  intro ε hε η hη
  set c : ℝ := Fintype.card ι + 1 with hc
  have hc0 : 0 < c := by positivity
  have hall : ∀ᶠ n in atTop, ∀ q, P n {ω | ε / c ≤ |Z q n ω|} ≤ ENNReal.ofReal (η / c) :=
    Filter.eventually_all.2 fun q => hZ q _ (by positivity) _ (by positivity)
  filter_upwards [hall] with n hn
  have hsub : {ω | ε ≤ ∑ q, |Z q n ω|} ⊆ ⋃ q, {ω | ε / c ≤ |Z q n ω|} := by
    intro ω hω
    by_contra hc'
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hc'
    have h1 : ∑ q, |Z q n ω| ≤ ∑ _q : ι, ε / c := Finset.sum_le_sum fun q _ => (hc' q).le
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 : (Fintype.card ι : ℝ) * (ε / c) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hc0, hc]; nlinarith
    have : ε ≤ ∑ q, |Z q n ω| := hω
    linarith
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun q _ => hn q).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_div_assoc', div_le_iff₀ hc0, hc]
  nlinarith

/-- deterministic terms tending to zero are small in probability. -/
lemma small_det {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {_ω | ε ≤ |d n|} ≤ ENNReal.ofReal η := by
  intro ε hε η hη
  have := (hd.abs).eventually (gt_mem_nhds (show |(0:ℝ)| < ε by simpa using hε))
  filter_upwards [this] with n hn
  have : {_ω : Ω n | ε ≤ |d n|} = ∅ := Set.eq_empty_of_forall_notMem fun ω h => by
    simp only [Set.mem_setOf_eq] at h; linarith
  rw [this, measure_empty]; exact bot_le

end FddS

/-! ### FddP: smallness in probability, pointwise approximation of ζⁿ by the source walk -/

namespace RW

open Filter Topology MeasureTheory ProbabilityTheory

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)]

/-- `Zₙ → 0` in probability. -/
def SP (P : ∀ n, Measure (Ωs n)) (Z : ∀ n, Ωs n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, P n {ω | ε ≤ |Z n ω|} ≤ ENNReal.ofReal η

lemma SP.mono {P : ∀ n, Measure (Ωs n)} {Z Z' : ∀ n, Ωs n → ℝ} (h : SP P Z)
    (hle : ∀ n ω, |Z' n ω| ≤ |Z n ω|) : SP P Z' := by
  intro ε hε η hη
  filter_upwards [h ε hε η hη] with n hn
  exact (measure_mono fun ω (hω : ε ≤ |Z' n ω|) =>
    (show ε ≤ |Z n ω| from hω.trans (hle n ω))).trans hn

lemma SP.congr {P : ∀ n, Measure (Ωs n)} {Z Z' : ∀ n, Ωs n → ℝ} (h : SP P Z)
    (he : ∀ n ω, Z' n ω = Z n ω) : SP P Z' :=
  h.mono fun n ω => by rw [he]

lemma SP.add {P : ∀ n, Measure (Ωs n)} {Z Z' : ∀ n, Ωs n → ℝ} (h : SP P Z) (h' : SP P Z') :
    SP P (fun n ω => Z n ω + Z' n ω) := by
  intro ε hε η hη
  filter_upwards [h (ε / 2) (by positivity) (η / 2) (by positivity),
    h' (ε / 2) (by positivity) (η / 2) (by positivity)] with n h1 h2
  have hsub : {ω | ε ≤ |Z n ω + Z' n ω|} ⊆ {ω | ε / 2 ≤ |Z n ω|} ∪ {ω | ε / 2 ≤ |Z' n ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hc
    push_neg at hc
    have := abs_add_le (Z n ω) (Z' n ω)
    linarith [hc.1, hc.2]
  calc P n {ω | ε ≤ |Z n ω + Z' n ω|}
      ≤ P n {ω | ε / 2 ≤ |Z n ω|} + P n {ω | ε / 2 ≤ |Z' n ω|} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

lemma SP.const_mul {P : ∀ n, Measure (Ωs n)} {Z : ∀ n, Ωs n → ℝ} (h : SP P Z) (c : ℝ) :
    SP P (fun n ω => c * Z n ω) := by
  intro ε hε η hη
  filter_upwards [h (ε / (|c| + 1)) (by positivity) η hη] with n hn
  refine (measure_mono fun ω (hω : ε ≤ |c * Z n ω|) => ?_).trans hn
  show ε / (|c| + 1) ≤ |Z n ω|
  rw [div_le_iff₀ (by positivity)]
  rw [abs_mul] at hω
  nlinarith [abs_nonneg c, abs_nonneg (Z n ω)]

lemma SP.fsum {P : ∀ n, Measure (Ωs n)} {ι : Type} [Fintype ι] (Z : ι → ∀ n, Ωs n → ℝ)
    (h : ∀ q, SP P (Z q)) : SP P (fun n ω => ∑ q, Z q n ω) := by
  intro ε hε η hη
  filter_upwards [FddS.small_sum P Z h ε hε η hη] with n hn
  refine (measure_mono fun ω (hω : ε ≤ |∑ q, Z q n ω|) => ?_).trans hn
  show ε ≤ ∑ q, |Z q n ω|
  exact hω.trans (Finset.abs_sum_le_sum_abs _ _)

lemma SP.det (P : ∀ n, Measure (Ωs n)) (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0)) :
    SP P (fun n _ => d n) :=
  fun ε hε η hη => FddS.small_det P d hd ε hε η hη

lemma SPV_of_coord {K : ℕ} {P : ∀ n, Measure (Ωs n)} (Z : ∀ n, Ωs n → Fin K → ℝ)
    (h : ∀ j, SP P (fun n ω => Z n ω j)) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {ω | ε ≤ ‖Z n ω‖} ≤ ENNReal.ofReal η := by
  intro ε hε η hη
  have hs := SP.fsum (P := P) (fun j n ω => |Z n ω j|)
    (fun j => (h j).mono fun n ω => by rw [abs_abs])
  filter_upwards [hs ε hε η hη] with n hn
  refine (measure_mono fun ω (hω : ε ≤ ‖Z n ω‖) => ?_).trans hn
  show ε ≤ abs (∑ j, |Z n ω j|)
  refine hω.trans (((pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun j _ => abs_nonneg (Z n ω j))).2 fun i => ?_).trans (le_abs_self _))
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |Z n ω j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- renewal inversion at a fixed time, from the renewal-tightness inputs. -/
lemma ren_pt' (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (v : ∀ n, ℕ → Ωs n → ℝ) (hind : ∀ n, iIndepFun (v n) (P n))
    (hmeas : ∀ n i, Measurable (v n i)) (hid : ∀ n i, IdentDistrib (v n i) (v n 0) (P n) (P n))
    (hL2 : ∀ n, MemLp (v n 0) 2 (P n)) (hpos : ∀ n i ω, 0 < v n i ω)
    (hdiv : ∀ n, ∀ᵐ ω ∂(P n), Tendsto (fun l => psum (v n) l ω) atTop atTop)
    (a : ℝ) (ha : 0 < a) (hm : ∀ᶠ n in atTop, a ≤ ∫ ω, v n 0 ω ∂(P n))
    (σ2 : ℝ) (hσ : ∀ᶠ n in atTop,
      ∫ ω, (v n 0 ω - ∫ ω', v n 0 ω' ∂(P n)) ^ 2 ∂(P n) ≤ σ2)
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |v n 0 ω - ∫ ω', v n 0 ω' ∂(P n)|}) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    SP P (fun n ω => (Real.sqrt n)⁻¹ *
      (((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) - (∫ ω', v n 0 ω' ∂(P n))⁻¹ * (n * t)) -
        ((⌊(∫ ω', v n 0 ω' ∂(P n))⁻¹ * n * t⌋₊ : ℝ) -
          (∫ ω', v n 0 ω' ∂(P n))⁻¹ * psum (v n) ⌊(∫ ω', v n 0 ω' ∂(P n))⁻¹ * n * t⌋₊ ω))) := by
  intro ε hε η hη
  have hMT := renewal_tight P hP v hind hmeas hid hL2 hpos hdiv a ha hm σ2 hσ hUI
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
  exact FddB.ren_point P v hpos hdiv m ha hm hMT
    (fun T hT ε hε η hη => rw_tight P hP ξ hξind hξm hξid hξL2 hξ0 σ2 hσ hUI T hT ε hε η hη)
    (fun T hT θ hθ η hη => jump_small P ξ hξm hξid hUI T hT θ hθ η hη) ht ε hε η hη

end RW

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

lemma sp_A (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) {k : Fin K}
    (hk : k ∈ J) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    RW.SP P (fun n ω => (Real.sqrt n)⁻¹ * FddN.EA n (net n) k t ω) := by
  have h : RW.SP P (fun n ω => (Real.sqrt n)⁻¹ *
      (((RW.cnt (fun l => RW.psum (fun i => (net n).u k i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).u k 0 ω' ∂(P n))⁻¹ * (n * t)) -
        ((⌊(∫ ω', (net n).u k 0 ω' ∂(P n))⁻¹ * n * t⌋₊ : ℝ) -
          (∫ ω', (net n).u k 0 ω' ∂(P n))⁻¹ * RW.psum (fun i => (net n).u k i)
            ⌊(∫ ω', (net n).u k 0 ω' ∂(P n))⁻¹ * n * t⌋₊ ω))) := by
    obtain ⟨ε0, hε0, C, hC⟩ := hA.2.2.2.2.2.2.2
    have hP := fun n => (net n).isProb
    have hlam0 : 0 ≤ lam k :=
      ge_of_tendsto (hA.2.2.1 k) (Eventually.of_forall fun n => (lam_pos' (net n) hk).le)
    have hmeas : ∀ n, Measurable ((net n).u k 0) := fun n => (net n).meas_u k hk 0
    refine RW.ren_pt' P hP (fun n i => (net n).u k i) (fun n => indep_u (net n) hk)
      (fun n i => (net n).meas_u k hk i) (fun n i => (net n).ident_u k hk i)
      (fun n => (net n).memLp_u k hk)
      (fun n i ω => (net n).pos_u k hk i ω) (fun n => ae_U (net n) hk) (lam k + 1)⁻¹
      (by positivity) ?_ (a k + 1) ?_ ?_ ht
    · filter_upwards [(hA.2.2.1 k).eventually (Iio_mem_nhds (by linarith : lam k < lam k + 1))]
        with n hn
      have h1 : ∫ ω', (net n).u k 0 ω' ∂(P n) = ((net n).lam k)⁻¹ := by
        simp only [Network.lam, if_pos hk, inv_inv]
      rw [h1]
      exact inv_anti₀ (lam_pos' (net n) hk) hn.le
    · filter_upwards [(hA.2.2.2.1 k hk).eventually (Iio_mem_nhds (by linarith : a k < a k + 1))]
        with n hn
      have := (net n).isProb
      have h1 : (net n).aVar k =
          ∫ ω, ((net n).u k 0 ω - ∫ ω', (net n).u k 0 ω' ∂(P n)) ^ 2 ∂(P n) :=
        variance_eq_integral (hmeas n).aemeasurable
      rw [← h1]; exact hn.le
    · refine RW.hUI_of_moment P (fun n => (net n).u k 0) hmeas
        (fun n ω => (net n).pos_u k hk 0 ω)
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
  refine h.congr fun n ω => ?_
  have hl : (net n).lam k = (∫ ω', (net n).u k 0 ω' ∂(P n))⁻¹ := by
    simp only [Network.lam, if_pos hk]
  have hAk : (net n).A k (n * t) ω =
      RW.cnt (fun l => RW.psum (fun i => (net n).u k i) l ω) (n * t) := by
    simp only [Network.A, if_pos hk]; rfl
  simp only [FddN.EA, hl, hAk]; rfl

lemma sp_S (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k : Fin K)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    RW.SP P (fun n ω => (Real.sqrt n)⁻¹ * FddN.ES n (net n) k t ω) := by
  have h : RW.SP P (fun n ω => (Real.sqrt n)⁻¹ *
      (((RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * (n * t)) -
        ((⌊(∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * n * t⌋₊ : ℝ) -
          (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * RW.psum (fun i => (net n).v k i)
            ⌊(∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * n * t⌋₊ ω))) := by
    obtain ⟨ε0, hε0, C, hC⟩ := hA.2.2.2.2.2.2.1
    have hP := fun n => (net n).isProb
    have hmu0 : 0 ≤ mu k :=
      ge_of_tendsto (hA.2.1 k) (Eventually.of_forall fun n => (mu_pos' (net n) k).le)
    have hmeas : ∀ n, Measurable ((net n).v k 0) := fun n => (net n).meas_v k 0
    refine RW.ren_pt' P hP (fun n i => (net n).v k i) (fun n => indep_v (net n) k)
      (fun n i => (net n).meas_v k i) (fun n i => (net n).ident_v k i)
      (fun n => (net n).memLp_v k)
      (fun n i ω => (net n).pos_v k i ω) (fun n => ae_V (net n) k) (mu k + 1)⁻¹ (by positivity)
      ?_ (s k + 1) ?_ ?_ ht
    · filter_upwards [(hA.2.1 k).eventually (Iio_mem_nhds (by linarith : mu k < mu k + 1))]
        with n hn
      have h1 : ∫ ω', (net n).v k 0 ω' ∂(P n) = ((net n).mu k)⁻¹ := by
        simp only [Network.mu, inv_inv]
      rw [h1]
      exact inv_anti₀ (mu_pos' (net n) k) hn.le
    · filter_upwards [(hA.2.2.2.2.1 k).eventually (Iio_mem_nhds (by linarith : s k < s k + 1))]
        with n hn
      have := (net n).isProb
      have h1 : (net n).sVar k =
          ∫ ω, ((net n).v k 0 ω - ∫ ω', (net n).v k 0 ω' ∂(P n)) ^ 2 ∂(P n) :=
        variance_eq_integral (hmeas n).aemeasurable
      rw [← h1]; exact hn.le
    · refine RW.hUI_of_moment P (fun n => (net n).v k 0) hmeas
        (fun n ω => (net n).pos_v k 0 ω)
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
  refine h.congr fun n ω => ?_
  rfl

lemma sp_R (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k j : Fin K)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    RW.SP P (fun n ω => (Real.sqrt n)⁻¹ * FddN.ER n (net n) R k t ω j) := by
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
  have hm : ∀ᶠ n in atTop, (mu k + 1)⁻¹ ≤ ∫ ω, (net n).v k 0 ω ∂(P n) := by
    filter_upwards [(hA.2.1 k).eventually (Iio_mem_nhds (by linarith : mu k < mu k + 1))]
      with n hn
    have h1 : ∫ ω', (net n).v k 0 ω' ∂(P n) = ((net n).mu k)⁻¹ := by
      simp only [Network.mu, inv_inv]
    rw [h1]
    exact inv_anti₀ (mu_pos' (net n) k) hn.le
  have hrp : RW.SP P (fun n ω => (Real.sqrt n)⁻¹ *
      (RW.psum (ξ n) (RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t)) ω -
        RW.psum (ξ n) ⌊(∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * n * t⌋₊ ω)) :=
    fun ε hε η hη => FddB.rout_point P (fun n i => (net n).v k i)
      (fun n i ω => (net n).pos_v k i ω) (fun n => ∫ ω', (net n).v k 0 ω' ∂(P n))
      (by positivity : (0:ℝ) < (mu k + 1)⁻¹) hm (ren_S net hA k) ξ hmod ht ε hε η hη
  refine hrp.congr fun n ω => ?_
  simp only [FddN.ER, Pi.sub_apply, Finset.sum_apply, RW.psum, hξ, Function.comp_apply]
  rfl

lemma sqrt_inv_mul (n : ℕ) : (Real.sqrt n)⁻¹ * n = Real.sqrt n := by
  rcases eq_or_ne (Real.sqrt n) 0 with h | h
  · rw [h, inv_zero, zero_mul]
  · have hn : (n:ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    calc (Real.sqrt n)⁻¹ * n = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n) := by rw [← hn]
      _ = Real.sqrt n := inv_mul_cancel_left₀ h _

/-- the pointwise approximation of the netput by the source walk. -/
lemma approx (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {ω | ε ≤ ‖diffScale n (fun s => (net n).X s ω) t -
        FddA.Wp (FddN.Ysrc net R) (FddN.αsrc net) c n ω t‖} ≤ ENNReal.ofReal η := by
  refine RW.SPV_of_coord (fun n ω => diffScale n (fun s => (net n).X s ω) t -
    FddA.Wp (FddN.Ysrc net R) (FddN.αsrc net) c n ω t) fun j => ?_
  have hEA : ∀ k : {k // k ∈ J}, RW.SP P (fun n ω => (Real.sqrt n)⁻¹ *
      (FddN.EA n (net n) k.1 t ω * (Pi.single k.1 1 : Fin K → ℝ) j)) := fun k =>
    ((sp_A net hA k.2 ht).const_mul ((Pi.single k.1 1 : Fin K → ℝ) j)).congr fun n ω => by ring
  have hES : ∀ k, RW.SP P (fun n ω => (Real.sqrt n)⁻¹ *
      (FddN.ES n (net n) k t ω * (R k j - (Pi.single k 1 : Fin K → ℝ) j)) +
      (Real.sqrt n)⁻¹ * FddN.ER n (net n) R k t ω j) := fun k =>
    (((sp_S net hA k ht).const_mul (R k j - (Pi.single k 1 : Fin K → ℝ) j)).congr
      fun n ω => by ring).add (sp_R net hA k j ht)
  have hD : RW.SP P (fun n _ => (Real.sqrt n)⁻¹ * (n * t) * ((net n).nu j - (net n).mu j) -
      t * c j) := by
    refine RW.SP.det P _ ?_
    have h1 : Tendsto (fun n : ℕ => t * (Real.sqrt n * ((net n).nu j - (net n).mu j) - c j))
        atTop (𝓝 (t * (c j - c j))) :=
      ((hA.2.2.2.2.2.1 j).sub tendsto_const_nhds).const_mul t
    rw [sub_self, mul_zero] at h1
    refine h1.congr fun n => ?_
    have e := sqrt_inv_mul n
    linear_combination (-(t * ((net n).nu j - (net n).mu j))) * e
  refine (((RW.SP.fsum _ hEA).add (RW.SP.fsum _ hES)).add hD).congr fun n ω => ?_
  rw [FddN.decomp net hA.1 c n ω t]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    Finset.mul_sum, mul_add]

end NetT

/-! ### FddT: the triangular-array CLT hypotheses for the source walk -/

namespace FddN

open Filter Topology MeasureTheory ProbabilityTheory Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

/-- zero at `n = 0` (keeps the `2+ε` moments uniform over all `n`). -/
noncomputable def gz (K : ℕ) (n : ℕ) (x : Fin K → ℝ) : Fin K → ℝ := if n = 0 then 0 else x

lemma gz_meas (n : ℕ) : Measurable (gz K n) := by
  by_cases h : n = 0
  · have : gz K n = fun _ => 0 := funext fun x => by simp [gz, h]
    rw [this]; exact measurable_const
  · have : gz K n = id := funext fun x => by simp [gz, h]
    rw [this]; exact measurable_id

noncomputable def Yz (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) :
    ∀ n, Src K J → ℕ → Ω n → Fin K → ℝ :=
  fun n σ i => gz K n ∘ Ysrc net R n σ i

lemma Yz_ne (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) {n : ℕ} (hn : n ≠ 0)
    (σ : Src K J) (i : ℕ) (ω : Ω n) : Yz net R n σ i ω = Ysrc net R n σ i ω := by
  simp [Yz, gz, hn]

lemma Yz_zero (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ)
    (σ : Src K J) (i : ℕ) (ω : Ω 0) : Yz net R 0 σ i ω = 0 := by
  simp [Yz, gz]

def gsrc : Src K J × ℕ → PrimIndex K J
  | (Sum.inl k, i) => Sum.inl (k, i)
  | (Sum.inr (Sum.inl k), i) => Sum.inr (Sum.inl (k, i))
  | (Sum.inr (Sum.inr k), i) => Sum.inr (Sum.inr (k, i))

lemma gsrc_inj : Function.Injective (gsrc (K := K) (J := J)) := by
  rintro ⟨(a | a | a), i⟩ ⟨(b | b | b), j⟩ h <;> simp_all [gsrc]

lemma comap_le_comp {α β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : α → β) (h : β → γ) (hh : Measurable h) :
    MeasurableSpace.comap (h ∘ f) mγ ≤ MeasurableSpace.comap f mβ := by
  rw [← MeasurableSpace.comap_comp]; exact MeasurableSpace.comap_mono hh.comap_le

lemma Ysrc_meas (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (σ : Src K J) (i : ℕ) : Measurable (Ysrc net R n σ i) := by
  rcases σ with k | k | k
  · exact (by fun_prop : Measurable fun x : ℝ => (-((net n).lam k.1 * (x - ((net n).lam k.1)⁻¹))) •
      (Pi.single k.1 1 : Fin K → ℝ)).comp ((net n).meas_u k.1 k.2 i)
  · exact (by fun_prop : Measurable fun x : ℝ => (-((net n).mu k * (x - ((net n).mu k)⁻¹))) •
      (R k - Pi.single k 1)).comp ((net n).meas_v k i)
  · exact (measurable_of_finite (fun r : Fin (K + 1) => routeVec r - R k)).comp
      ((net n).meas_φ k i)

lemma Ysrc_indep (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ) :
    iIndepFun (fun p : Src K J × ℕ => Ysrc net R n p.1 p.2) (P n) := by
  rw [iIndepFun_iff_iIndep]
  refine iIndep_of_iIndep_of_le ((net n).indep.precomp gsrc_inj) fun p => ?_
  rcases p with ⟨k | k | k, i⟩
  · exact comap_le_comp ((net n).u k.1 i) (fun x : ℝ => (-((net n).lam k.1 *
      (x - ((net n).lam k.1)⁻¹))) • (Pi.single k.1 1 : Fin K → ℝ)) (by fun_prop)
  · exact comap_le_comp ((net n).v k i) (fun x : ℝ => (-((net n).mu k *
      (x - ((net n).mu k)⁻¹))) • (R k - Pi.single k 1)) (by fun_prop)
  · exact comap_le_comp ((net n).φ k i) (fun r : Fin (K + 1) => routeVec r - R k)
      (measurable_of_finite _)

lemma Ysrc_ident (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (σ : Src K J) (i : ℕ) : IdentDistrib (Ysrc net R n σ i) (Ysrc net R n σ 0) (P n) (P n) := by
  rcases σ with k | k | k
  · exact ((net n).ident_u k.1 k.2 i).comp (by fun_prop : Measurable fun x : ℝ =>
      (-((net n).lam k.1 * (x - ((net n).lam k.1)⁻¹))) • (Pi.single k.1 1 : Fin K → ℝ))
  · exact ((net n).ident_v k i).comp (by fun_prop : Measurable fun x : ℝ =>
      (-((net n).mu k * (x - ((net n).mu k)⁻¹))) • (R k - Pi.single k 1))
  · exact ((net n).ident_φ k i).comp (measurable_of_finite (fun r : Fin (K + 1) => routeVec r - R k))

lemma Yz_meas (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (σ : Src K J) (i : ℕ) : Measurable (Yz net R n σ i) :=
  (gz_meas n).comp (Ysrc_meas net R n σ i)

lemma Yz_indep (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ) :
    iIndepFun (fun p : Src K J × ℕ => Yz net R n p.1 p.2) (P n) :=
  (Ysrc_indep net R n).comp (fun _ => gz K n) (fun _ => gz_meas n)

lemma Yz_ident (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (σ : Src K J) (i : ℕ) : IdentDistrib (Yz net R n σ i) (Yz net R n σ 0) (P n) (P n) :=
  (Ysrc_ident net R n σ i).comp (gz_meas n)

/-! coordinates -/

lemma coord_arr (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (k : {k // k ∈ J}) (j : Fin K) (ω : Ω n) :
    Ysrc net R n (Sum.inl k) 0 ω j = (-((net n).lam k.1) * (Pi.single k.1 1 : Fin K → ℝ) j) *
      ((net n).u k.1 0 ω - ∫ ω', (net n).u k.1 0 ω' ∂(P n)) := by
  have hl : ((net n).lam k.1)⁻¹ = ∫ ω', (net n).u k.1 0 ω' ∂(P n) := by
    simp [Network.lam, k.2]
  simp only [Ysrc, Pi.smul_apply, smul_eq_mul, hl]; ring

lemma coord_serv (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (k j : Fin K) (ω : Ω n) :
    Ysrc net R n (Sum.inr (Sum.inl k)) 0 ω j =
      (-((net n).mu k) * (R k j - (Pi.single k 1 : Fin K → ℝ) j)) *
      ((net n).v k 0 ω - ∫ ω', (net n).v k 0 ω' ∂(P n)) := by
  have hl : ((net n).mu k)⁻¹ = ∫ ω', (net n).v k 0 ω' ∂(P n) := by
    simp [Network.mu]
  simp only [Ysrc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hl]; ring

lemma coord_rout (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (k j : Fin K) (ω : Ω n) :
    Ysrc net R n (Sum.inr (Sum.inr k)) 0 ω j = routeVec ((net n).φ k 0 ω) j - R k j := rfl

lemma lin_facts {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} [IsProbabilityMeasure μ]
    {w : Ω₁ → ℝ} (hw : MemLp w 2 μ) (c c' : ℝ) :
    Integrable (fun ω => c * (w ω - ∫ x, w x ∂μ)) μ ∧ ∫ ω, c * (w ω - ∫ x, w x ∂μ) ∂μ = 0 ∧
    Integrable (fun ω => c * (w ω - ∫ x, w x ∂μ) * (c' * (w ω - ∫ x, w x ∂μ))) μ ∧
    ∫ ω, c * (w ω - ∫ x, w x ∂μ) * (c' * (w ω - ∫ x, w x ∂μ)) ∂μ = c * c' * variance w μ := by
  have h1 : MemLp (fun ω => w ω - ∫ x, w x ∂μ) 2 μ := hw.sub (memLp_const _)
  have hsq : Integrable (fun ω => (w ω - ∫ x, w x ∂μ) ^ 2) μ := h1.integrable_sq
  have e : (fun ω => c * (w ω - ∫ x, w x ∂μ) * (c' * (w ω - ∫ x, w x ∂μ))) =
      fun ω => (c * c') * (w ω - ∫ x, w x ∂μ) ^ 2 := funext fun ω => by ring
  refine ⟨(h1.integrable one_le_two).const_mul c, ?_, by rw [e]; exact hsq.const_mul _, ?_⟩
  · rw [integral_const_mul, integral_sub (hw.integrable one_le_two) (integrable_const _),
      integral_const, probReal_univ, one_smul, sub_self, mul_zero]
  · rw [e, integral_const_mul, variance_eq_integral hw.1.aemeasurable]

lemma routeVec_mul (r : Fin (K + 1)) (j j' : Fin K) :
    routeVec r j * routeVec r j' = if j = j' then routeVec r j else 0 := by
  unfold routeVec
  by_cases hj : j = j'
  · subst hj; split_ifs <;> simp_all
  · rw [if_neg hj]
    split_ifs with h1 h2 <;> simp_all

lemma rout_facts {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} (N : Network K J μ)
    (k j j' : Fin K) :
    Integrable (fun ω => routeVec (N.φ k 0 ω) j - N.routing k j) μ ∧
    ∫ ω, (routeVec (N.φ k 0 ω) j - N.routing k j) ∂μ = 0 ∧
    Integrable (fun ω => (routeVec (N.φ k 0 ω) j - N.routing k j) *
      (routeVec (N.φ k 0 ω) j' - N.routing k j')) μ ∧
    ∫ ω, (routeVec (N.φ k 0 ω) j - N.routing k j) *
      (routeVec (N.φ k 0 ω) j' - N.routing k j') ∂μ =
      (if j = j' then N.routing k j else 0) - N.routing k j * N.routing k j' := by
  have := N.isProb
  have hb : ∀ (i : Fin K), Integrable (fun ω => routeVec (N.φ k 0 ω) i) μ := fun i =>
    Integrable.of_bound (measurable_of_finite (fun r : Fin (K + 1) => routeVec r i) |>.comp
      (N.meas_φ k 0)).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
        have := NetT.routeVec_mem (N.φ k 0 ω) i
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
  have hI : ∀ i, ∫ ω, routeVec (N.φ k 0 ω) i ∂μ = N.routing k i := fun i =>
    NetT.routeVec_integral N k i
  have hm : Integrable (fun ω => routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j') μ := by
    have e : (fun ω => routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j') =
        fun ω => if j = j' then routeVec (N.φ k 0 ω) j else 0 :=
      funext fun ω => routeVec_mul _ j j'
    rw [e]; split_ifs
    · exact hb j
    · exact integrable_zero _ _ _
  have e2 : (fun ω => (routeVec (N.φ k 0 ω) j - N.routing k j) *
      (routeVec (N.φ k 0 ω) j' - N.routing k j')) = fun ω =>
      routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j' - N.routing k j * routeVec (N.φ k 0 ω) j' -
        N.routing k j' * routeVec (N.φ k 0 ω) j + N.routing k j * N.routing k j' :=
    funext fun ω => by ring
  have hi2 : Integrable (fun ω => routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j' -
      N.routing k j * routeVec (N.φ k 0 ω) j' - N.routing k j' * routeVec (N.φ k 0 ω) j +
        N.routing k j * N.routing k j') μ :=
    ((hm.sub ((hb j').const_mul _)).sub ((hb j).const_mul _)).add (integrable_const _)
  refine ⟨(hb j).sub (integrable_const _), ?_, by rw [e2]; exact hi2, ?_⟩
  · rw [integral_sub (hb j) (integrable_const _), integral_const, probReal_univ, one_smul, hI,
      sub_self]
  · have e3 : ∫ ω, routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j' ∂μ =
        if j = j' then N.routing k j else 0 := by
      rw [show (fun ω => routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j') =
        fun ω => if j = j' then routeVec (N.φ k 0 ω) j else 0 from
          funext fun ω => routeVec_mul _ j j']
      split_ifs
      · exact hI j
      · simp
    have hA1 := (hm.sub ((hb j').const_mul (N.routing k j))).sub ((hb j).const_mul (N.routing k j'))
    calc ∫ ω, (routeVec (N.φ k 0 ω) j - N.routing k j) *
          (routeVec (N.φ k 0 ω) j' - N.routing k j') ∂μ
        = ∫ ω, ((routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j' -
            N.routing k j * routeVec (N.φ k 0 ω) j') - N.routing k j' * routeVec (N.φ k 0 ω) j) +
            N.routing k j * N.routing k j' ∂μ := by rw [e2]
      _ = ∫ ω, ((routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j' -
            N.routing k j * routeVec (N.φ k 0 ω) j') - N.routing k j' * routeVec (N.φ k 0 ω) j) ∂μ +
            ∫ ω, N.routing k j * N.routing k j' ∂μ := integral_add hA1 (integrable_const _)
      _ = (∫ ω, (routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j' -
            N.routing k j * routeVec (N.φ k 0 ω) j') ∂μ -
            ∫ ω, N.routing k j' * routeVec (N.φ k 0 ω) j ∂μ) +
            ∫ ω, N.routing k j * N.routing k j' ∂μ :=
          congrArg (fun x => x + ∫ ω, N.routing k j * N.routing k j' ∂μ)
            (integral_sub (hm.sub ((hb j').const_mul (N.routing k j)))
              ((hb j).const_mul (N.routing k j')))
      _ = ((∫ ω, routeVec (N.φ k 0 ω) j * routeVec (N.φ k 0 ω) j' ∂μ -
            ∫ ω, N.routing k j * routeVec (N.φ k 0 ω) j' ∂μ) -
            ∫ ω, N.routing k j' * routeVec (N.φ k 0 ω) j ∂μ) +
            ∫ ω, N.routing k j * N.routing k j' ∂μ :=
          congrArg (fun x => (x - ∫ ω, N.routing k j' * routeVec (N.φ k 0 ω) j ∂μ) +
            ∫ ω, N.routing k j * N.routing k j' ∂μ)
            (integral_sub hm ((hb j').const_mul (N.routing k j)))
      _ = (((if j = j' then N.routing k j else 0) - N.routing k j * N.routing k j') -
            N.routing k j' * N.routing k j) + N.routing k j * N.routing k j' := by
          rw [integral_const_mul, integral_const_mul, hI, hI, e3, integral_const, probReal_univ,
            one_smul]
      _ = _ := by ring

/-- first and second moments of the source vectors. -/
lemma mom12 (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    (hR : ∀ n, (net n).routing = R) (n : ℕ) (σ : Src K J) (j j' : Fin K) :
    Integrable (fun ω => Yz net R n σ 0 ω j) (P n) ∧ ∫ ω, Yz net R n σ 0 ω j ∂(P n) = 0 ∧
    Integrable (fun ω => Yz net R n σ 0 ω j * Yz net R n σ 0 ω j') (P n) := by
  have := (net n).isProb
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Yz_zero, Pi.zero_apply, mul_zero]
    exact ⟨integrable_zero _ _ _, by simp, integrable_zero _ _ _⟩
  simp only [Yz_ne net R hn]
  rcases σ with k | k | k
  · simp only [coord_arr]
    obtain ⟨h1, h2, h3, -⟩ := lin_facts ((net n).memLp_u k.1 k.2)
      (-((net n).lam k.1) * (Pi.single k.1 1 : Fin K → ℝ) j)
      (-((net n).lam k.1) * (Pi.single k.1 1 : Fin K → ℝ) j')
    exact ⟨h1, h2, h3⟩
  · simp only [coord_serv]
    obtain ⟨h1, h2, h3, -⟩ := lin_facts ((net n).memLp_v k)
      (-((net n).mu k) * (R k j - (Pi.single k 1 : Fin K → ℝ) j))
      (-((net n).mu k) * (R k j' - (Pi.single k 1 : Fin K → ℝ) j'))
    exact ⟨h1, h2, h3⟩
  · simp only [coord_rout]
    obtain ⟨h1, h2, h3, -⟩ := rout_facts (net n) k j j'
    rw [hR n] at h1 h2 h3
    exact ⟨h1, h2, h3⟩

/-- covariance limits. -/
lemma cov_lim (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (σ : Src K J) (j j' : Fin K) :
    Tendsto (fun n => ∫ ω, Yz net R n σ 0 ω j * Yz net R n σ 0 ω j' ∂(P n)) atTop
      (𝓝 (FddC.Clim (J := J) R lam a mu s σ j j')) := by
  rcases σ with k | k | k
  · have hev : ∀ n, n ≠ 0 → ∫ ω, Yz net R n (Sum.inl k) 0 ω j * Yz net R n (Sum.inl k) 0 ω j'
        ∂(P n) = (-((net n).lam k.1) * (Pi.single k.1 1 : Fin K → ℝ) j) *
          (-((net n).lam k.1) * (Pi.single k.1 1 : Fin K → ℝ) j') * (net n).aVar k.1 := by
      intro n hn
      have := (net n).isProb
      simp only [Yz_ne net R hn, coord_arr]
      exact (lin_facts ((net n).memLp_u k.1 k.2) _ _).2.2.2
    refine Tendsto.congr' ((eventually_ne_atTop 0).mono fun n hn => (hev n hn).symm) ?_
    have h := ((((hA.2.2.1 k.1).neg.mul_const ((Pi.single k.1 1 : Fin K → ℝ) j)).mul
      ((hA.2.2.1 k.1).neg.mul_const ((Pi.single k.1 1 : Fin K → ℝ) j'))).mul (hA.2.2.2.1 k.1 k.2))
    have e : FddC.Clim (J := J) R lam a mu s (Sum.inl k) j j' =
        (-(lam k.1) * (Pi.single k.1 1 : Fin K → ℝ) j) *
          (-(lam k.1) * (Pi.single k.1 1 : Fin K → ℝ) j') * a k.1 := by
      simp only [FddC.Clim, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]; ring
    rw [e]; exact h
  · have hev : ∀ n, n ≠ 0 → ∫ ω, Yz net R n (Sum.inr (Sum.inl k)) 0 ω j *
        Yz net R n (Sum.inr (Sum.inl k)) 0 ω j' ∂(P n) =
          (-((net n).mu k) * (R k j - (Pi.single k 1 : Fin K → ℝ) j)) *
          (-((net n).mu k) * (R k j' - (Pi.single k 1 : Fin K → ℝ) j')) * (net n).sVar k := by
      intro n hn
      have := (net n).isProb
      simp only [Yz_ne net R hn, coord_serv]
      exact (lin_facts ((net n).memLp_v k) _ _).2.2.2
    refine Tendsto.congr' ((eventually_ne_atTop 0).mono fun n hn => (hev n hn).symm) ?_
    have h := ((((hA.2.1 k).neg.mul_const (R k j - (Pi.single k 1 : Fin K → ℝ) j)).mul
      ((hA.2.1 k).neg.mul_const (R k j' - (Pi.single k 1 : Fin K → ℝ) j'))).mul (hA.2.2.2.2.1 k))
    have e : FddC.Clim (J := J) R lam a mu s (Sum.inr (Sum.inl k)) j j' =
        (-(mu k) * (R k j - (Pi.single k 1 : Fin K → ℝ) j)) *
          (-(mu k) * (R k j' - (Pi.single k 1 : Fin K → ℝ) j')) * s k := by
      simp only [FddC.Clim, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Pi.sub_apply]
      ring
    rw [e]; exact h
  · have hev : ∀ n, n ≠ 0 → ∫ ω, Yz net R n (Sum.inr (Sum.inr k)) 0 ω j *
        Yz net R n (Sum.inr (Sum.inr k)) 0 ω j' ∂(P n) =
          FddC.Clim (J := J) R lam a mu s (Sum.inr (Sum.inr k)) j j' := by
      intro n hn
      simp only [Yz_ne net R hn, coord_rout]
      have h := (rout_facts (net n) k j j').2.2.2
      rw [hA.1 n] at h
      rw [h]
      simp only [FddC.Clim, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
    exact tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun n hn => (hev n hn).symm)

end FddN

/-! ### FddM: uniform `2+ε` moments, and the assembled fdd convergence -/

namespace FddN

open Filter Topology MeasureTheory ProbabilityTheory Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

lemma rpow_bd {x p q : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) (hp3 : p ≤ 3) (hpq : p ≤ q) :
    (x + 1) ^ p ≤ 8 * (1 + x ^ q) := by
  have hm : 1 ≤ max x 1 := le_max_right _ _
  have h1 : x + 1 ≤ 2 * max x 1 := by linarith [le_max_left x 1, le_max_right x 1]
  have h8 : (2:ℝ) ^ p ≤ 8 := by
    calc (2:ℝ) ^ p ≤ 2 ^ (3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3
      _ = 8 := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hmx : (max x 1) ^ q ≤ 1 + x ^ q := by
    rcases le_total x 1 with h | h
    · rw [max_eq_right h, Real.one_rpow]; linarith [Real.rpow_nonneg hx q]
    · rw [max_eq_left h]; linarith
  calc (x + 1) ^ p ≤ (2 * max x 1) ^ p := Real.rpow_le_rpow (by linarith) h1 hp
    _ = 2 ^ p * (max x 1) ^ p := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 8 * (max x 1) ^ q :=
        mul_le_mul h8 (Real.rpow_le_rpow_of_exponent_le hm hpq)
          (Real.rpow_nonneg (by linarith) _) (by norm_num)
    _ ≤ 8 * (1 + x ^ q) := mul_le_mul_of_nonneg_left hmx (by norm_num)

lemma int_of_lint {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} {f : Ω₁ → ℝ}
    (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {C : ℝ}
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal C) :
    Integrable f μ ∧ ∫ ω, f ω ∂μ ≤ max C 0 := by
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).2
    (h.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
    (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))

lemma mom_gen {Ω₁ : Type} [MeasurableSpace Ω₁] {μ : Measure Ω₁} [IsProbabilityMeasure μ]
    {Y : Ω₁ → Fin K → ℝ} {w : Ω₁ → ℝ} (hY : Measurable Y) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) {B p q C : ℝ} (hB : 0 ≤ B) (hp : 0 ≤ p) (hp3 : p ≤ 3) (hpq : p ≤ q)
    (hbd : ∀ ω, ‖Y ω‖ ≤ B * w ω + 1)
    (hmom : ∫⁻ ω, ENNReal.ofReal (w ω ^ q) ∂μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ‖Y ω‖ ^ p) μ ∧ ∫ ω, ‖Y ω‖ ^ p ∂μ ≤ 8 + 8 * (B ^ q * max C 0) := by
  obtain ⟨hi, hI⟩ := int_of_lint (hw.pow_const q) (fun ω => Real.rpow_nonneg (hw0 ω) q) hmom
  have hg : Integrable (fun ω => 8 + 8 * B ^ q * w ω ^ q) μ :=
    (integrable_const 8).add (hi.const_mul _)
  have hle : ∀ ω, ‖Y ω‖ ^ p ≤ 8 + 8 * B ^ q * w ω ^ q := fun ω =>
    calc ‖Y ω‖ ^ p ≤ (B * w ω + 1) ^ p := Real.rpow_le_rpow (norm_nonneg _) (hbd ω) hp
      _ ≤ 8 * (1 + (B * w ω) ^ q) := rpow_bd (mul_nonneg hB (hw0 ω)) hp hp3 hpq
      _ = 8 + 8 * B ^ q * w ω ^ q := by rw [Real.mul_rpow hB (hw0 ω)]; ring
  have hm : Measurable fun ω => ‖Y ω‖ ^ p := hY.norm.pow_const p
  have hI' : Integrable (fun ω => ‖Y ω‖ ^ p) μ :=
    hg.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; exact hle ω)
  refine ⟨hI', (integral_mono hI' hg hle).trans ?_⟩
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul,
    probReal_univ, one_smul]
  have hBq : (0:ℝ) ≤ 8 * B ^ q := by positivity
  have := mul_le_mul_of_nonneg_left hI hBq
  nlinarith [this]

lemma norm_vec1 {x : Fin K → ℝ} (h : ∀ j, |x j| ≤ 1) : ‖x‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by rw [Real.norm_eq_abs]; exact h j

lemma Rmem (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    (hR : ∀ n, (net n).routing = R) (k j : Fin K) : 0 ≤ R k j ∧ R k j ≤ 1 := by
  rw [← hR 0]; exact NetT.routing_mem (net 0) k j

lemma norm_arr (net : ∀ n, Network K J (P n)) (R : Matrix (Fin K) (Fin K) ℝ) (n : ℕ)
    (k : {k // k ∈ J}) (ω : Ω n) :
    ‖Ysrc net R n (Sum.inl k) 0 ω‖ ≤ (net n).lam k.1 * (net n).u k.1 0 ω + 1 := by
  have hL := NetT.lam_pos' (net n) k.2
  have hu := (net n).pos_u k.1 k.2 0 ω
  simp only [Ysrc]
  rw [norm_smul, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_neg]
  have e : (net n).lam k.1 * ((net n).u k.1 0 ω - ((net n).lam k.1)⁻¹) =
      (net n).lam k.1 * (net n).u k.1 0 ω - 1 := by
    rw [mul_sub, mul_inv_cancel₀ hL.ne']
  rw [e, abs_le]; constructor <;> nlinarith [mul_pos hL hu]

lemma norm_serv (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    (hR : ∀ n, (net n).routing = R) (n : ℕ) (k : Fin K) (ω : Ω n) :
    ‖Ysrc net R n (Sum.inr (Sum.inl k)) 0 ω‖ ≤ (net n).mu k * (net n).v k 0 ω + 1 := by
  have hL := NetT.mu_pos' (net n) k
  have hu := (net n).pos_v k 0 ω
  have hw : ‖R k - (Pi.single k 1 : Fin K → ℝ)‖ ≤ 1 := norm_vec1 fun j => by
    have := Rmem net hR k j
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  simp only [Ysrc]
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  have e : (net n).mu k * ((net n).v k 0 ω - ((net n).mu k)⁻¹) =
      (net n).mu k * (net n).v k 0 ω - 1 := by
    rw [mul_sub, mul_inv_cancel₀ hL.ne']
  rw [e]
  have h1 : |(net n).mu k * (net n).v k 0 ω - 1| ≤ (net n).mu k * (net n).v k 0 ω + 1 := by
    rw [abs_le]; constructor <;> nlinarith [mul_pos hL hu]
  exact (mul_le_mul h1 hw (norm_nonneg _) (by nlinarith [mul_pos hL hu])).trans
    (le_of_eq (mul_one _))

lemma norm_rout (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    (hR : ∀ n, (net n).routing = R) (n : ℕ) (k : Fin K) (ω : Ω n) :
    ‖Ysrc net R n (Sum.inr (Sum.inr k)) 0 ω‖ ≤ 0 * 0 + 1 := by
  rw [zero_mul, zero_add]
  refine norm_vec1 fun j => ?_
  have h1 := NetT.routeVec_mem ((net n).φ k 0 ω) j
  have h2 := Rmem net hR k j
  show |routeVec ((net n).φ k 0 ω) j - R k j| ≤ 1
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma mom_src (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ M : ℝ, ∀ n σ,
      Integrable (fun ω => ‖Yz net R n σ 0 ω‖ ^ (2 + ε)) (P n) ∧
      ∫ ω, ‖Yz net R n σ 0 ω‖ ^ (2 + ε) ∂(P n) ≤ M := by
  obtain ⟨εv, hεv, Cv, hCv⟩ := hA.2.2.2.2.2.2.1
  obtain ⟨εu, hεu, Cu, hCu⟩ := hA.2.2.2.2.2.2.2
  have hBl : ∀ k, ∃ B, ∀ n, (net n).lam k ≤ B := fun k => by
    obtain ⟨B, hB⟩ := (hA.2.2.1 k).bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hBm : ∀ k, ∃ B, ∀ n, (net n).mu k ≤ B := fun k => by
    obtain ⟨B, hB⟩ := (hA.2.1 k).bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  choose Bl hBl using hBl
  choose Bm hBm using hBm
  set ε := min (min εu εv) 1 with hε
  have hε0 : 0 < ε := lt_min (lt_min hεu hεv) one_pos
  have hεu' : ε ≤ εu := (min_le_left _ _).trans (min_le_left _ _)
  have hεv' : ε ≤ εv := (min_le_left _ _).trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := min_le_right _ _
  set F : Fin K → ℝ := fun k => (max (Bl k) 0) ^ (2 + εu) * max Cu 0 +
    (max (Bm k) 0) ^ (2 + εv) * max Cv 0 with hF
  have hF0 : ∀ k, 0 ≤ (max (Bl k) 0) ^ (2 + εu) * max Cu 0 ∧
      0 ≤ (max (Bm k) 0) ^ (2 + εv) * max Cv 0 := fun k =>
    ⟨mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (le_max_right _ _),
      mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (le_max_right _ _)⟩
  set S : ℝ := ∑ k, F k with hS
  have hSk : ∀ k, F k ≤ S := fun k =>
    Finset.single_le_sum (f := F) (fun k _ => add_nonneg (hF0 k).1 (hF0 k).2) (Finset.mem_univ k)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => add_nonneg (hF0 k).1 (hF0 k).2
  refine ⟨ε, hε0, hε1, 8 + 8 * S, fun n σ => ?_⟩
  have := (net n).isProb
  rcases eq_or_ne n 0 with rfl | hn
  · have e : (fun ω => ‖Yz net R 0 σ 0 ω‖ ^ (2 + ε)) = fun _ => 0 := funext fun ω => by
      rw [Yz_zero, norm_zero, Real.zero_rpow (by linarith)]
    rw [e, integral_zero]
    exact ⟨integrable_zero _ _ _, by linarith⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  simp only [Yz_ne net R hn]
  rcases σ with k | k | k
  · obtain ⟨h1, h2⟩ := mom_gen (μ := P n) (Ysrc_meas net R n _ 0) ((net n).meas_u k.1 k.2 0)
      (fun ω => ((net n).pos_u k.1 k.2 0 ω).le) (B := max (Bl k.1) 0) (le_max_right _ _)
      (by linarith : (0:ℝ) ≤ 2 + ε) (by linarith) (by linarith : 2 + ε ≤ 2 + εu)
      (fun ω => (norm_arr net R n k ω).trans (by
        have h := mul_le_mul_of_nonneg_right ((hBl k.1 n).trans (le_max_left (Bl k.1) 0))
          ((net n).pos_u k.1 k.2 0 ω).le
        linarith)) (hCu n hn1 k.1 k.2)
    refine ⟨h1, h2.trans ?_⟩
    have := hSk k.1
    have := (hF0 k.1).2
    simp only [hF] at *
    linarith
  · obtain ⟨h1, h2⟩ := mom_gen (μ := P n) (Ysrc_meas net R n _ 0) ((net n).meas_v k 0)
      (fun ω => ((net n).pos_v k 0 ω).le) (B := max (Bm k) 0) (le_max_right _ _)
      (by linarith : (0:ℝ) ≤ 2 + ε) (by linarith) (by linarith : 2 + ε ≤ 2 + εv)
      (fun ω => (norm_serv net hA.1 n k ω).trans (by
        have h := mul_le_mul_of_nonneg_right ((hBm k n).trans (le_max_left (Bm k) 0))
          ((net n).pos_v k 0 ω).le
        linarith)) (hCv n hn1 k)
    refine ⟨h1, h2.trans ?_⟩
    have := hSk k
    have := (hF0 k).1
    simp only [hF] at *
    linarith
  · obtain ⟨h1, h2⟩ := mom_gen (μ := P n) (Ysrc_meas net R n _ 0) (w := fun _ => (0:ℝ))
      measurable_const (fun _ => le_rfl) (B := 0) le_rfl (by linarith : (0:ℝ) ≤ 2 + ε)
      (by linarith) (le_refl (2 + ε)) (norm_rout net hA.1 n k) (C := 0)
      (by simp [Real.zero_rpow (by linarith : (2:ℝ) + ε ≠ 0)])
    refine ⟨h1, h2.trans ?_⟩
    rw [max_self, mul_zero, mul_zero, add_zero]; linarith

/-- **fdd convergence of the scaled netput** (Reiman 1984, Lemmas 3–5 / Prop. 3, fdd part). -/
theorem fdd_netput (K : ℕ) (J : Finset (Fin K)) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ)
    (hζ : IsDriftedBM c (covA lam a mu s R) P' ζ) :
    FddA.FddConvA P (fun n ω => diffScale n (fun t => (net n).X t ω)) P' ζ := by
  haveI : ∀ n, IsProbabilityMeasure (P n) := fun n => (net n).isProb
  have hJ : ∀ k ∉ J, lam k = 0 := fun k hk =>
    tendsto_nhds_unique (hA.2.2.1 k)
      (tendsto_const_nhds.congr fun n => by simp [Network.lam, hk])
  rw [← FddC.cov_eq R lam a mu s hJ] at hζ
  obtain ⟨ε, hε0, hε1, M, hM⟩ := mom_src net hA
  have hW : FddA.FddConvA P (FddA.Wp (Yz net R) (αsrc net) c) P' ζ := by
    refine FddA.tclt (Y := Yz net R) (α := αsrc net) (α₀ := FddC.α0 (J := J) lam mu)
      (C := FddC.Clim (J := J) R lam a mu s) (fun n σ i => Yz_meas net R n σ i)
      (fun n => Yz_indep net R n) (fun n σ i => Yz_ident net R n σ i)
      (fun n σ j => (mom12 net hA.1 n σ j j).1) (fun n σ j => (mom12 net hA.1 n σ j j).2.1)
      (fun n σ j j' => (mom12 net hA.1 n σ j j').2.2) (fun σ j j' => cov_lim net hA σ j j')
      hε0 hε1 (fun n σ => (hM n σ).1) (fun n σ => (hM n σ).2) (fun n σ => ?_) (fun σ => ?_) hζ
    · rcases σ with k | k | k
      · exact (NetT.lam_pos' (net n) k.2).le
      · exact (NetT.mu_pos' (net n) k).le
      · exact (NetT.mu_pos' (net n) k).le
    · rcases σ with k | k | k
      · exact hA.2.2.1 k.1
      · exact hA.2.1 k
      · exact hA.2.1 k
  refine FddA.slutsky_pt (X := FddA.Wp (Yz net R) (αsrc net) c)
    (Y := fun n ω => diffScale n (fun t => (net n).X t ω)) (fun n t => ?_) (fun n t => ?_) hW
    (fun t ht ε hε η hη => ?_)
  · have h1 : Measurable fun ω => ∑ σ, ∑ i ∈ Finset.range ⌊αsrc net n σ * n * t⌋₊,
        Yz net R n σ i ω :=
      Finset.measurable_sum _ fun σ _ => Finset.measurable_sum _ fun i _ => Yz_meas net R n σ i
    exact ((h1.const_smul ((Real.sqrt n)⁻¹)).add_const (t • c)).aemeasurable
  · exact ((MeasQ.X_meas (net n) (n * t)).const_smul ((Real.sqrt n)⁻¹)).aemeasurable
  · filter_upwards [NetT.approx net hA ht ε hε η hη, eventually_ne_atTop 0] with n hn hn0
    have e : ∀ ω, FddA.Wp (Yz net R) (αsrc net) c n ω t =
        FddA.Wp (Ysrc net R) (αsrc net) c n ω t := fun ω => by
      simp only [FddA.Wp, Yz_ne net R hn0]
    simp only [e]
    exact hn

end FddN

open Filter Topology MeasureTheory Reiman84.QueueLength in
theorem solution {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ)
    (hζ : IsDriftedBM c (covA lam a mu s R) P' ζ)
    (m : ℕ) (τ : Fin m → ℝ) (hτ : ∀ i, τ i ∈ Set.Icc (0:ℝ) 1)
    (f : (Fin m → Fin K → ℝ) → ℝ) (hfC : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hfL : ∃ L : NNReal, LipschitzWith L f) :
    Tendsto (fun n => ∫ ω, f (fun i => diffScale n (fun t => (net n).X t ω) (τ i)) ∂(P n))
      atTop (𝓝 (∫ ω, f (fun i => ζ ω (τ i)) ∂P')) := by
  exact FddN.fdd_netput K J Ω P net R mu s lam a c hA Ω' P' ζ hζ m τ hτ f hfC hfL
