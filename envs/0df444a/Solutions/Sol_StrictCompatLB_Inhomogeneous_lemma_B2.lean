-- Prove2me | solution 1 for StrictCompatLB.Inhomogeneous.lemma_B2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:11:48.566781+00:00
-- url     : https://prove2.me/submissions/505302ef-b9d1-4393-b59f-e087dcc7a90c

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Theorems.Thm_StrictCompatLB_Inhomogeneous_subcritical_of_A19

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace InhomAux

/-! ### Borel–Cantelli wrapper -/

lemma bc_wrapper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {α : ℕ → Type*} [∀ N, MeasurableSpace (α N)] (X : (N : ℕ) → Ω → α N)
    (hX_meas : ∀ N, Measurable (X N)) (μ : (N : ℕ) → Measure (α N))
    (hlaw : ∀ N, P.map (X N) = μ N) (S : (N : ℕ) → Set (α N))
    (hS : ∀ N, MeasurableSet (S N)) (N1 : ℕ)
    (hb : ∀ N ≥ N1, (μ N).real (S N) ≤ 2 / (N : ℝ) ^ 2) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop, X N ω ∉ S N := by
  have hP : ∀ N, P (X N ⁻¹' S N) = μ N (S N) := by
    intro N
    rw [← hlaw N, Measure.map_apply (hX_meas N) (hS N)]
  have hfin : ∀ N, IsFiniteMeasure (μ N) := by
    intro N; rw [← hlaw N]; infer_instance
  let g : ℕ → ℝ := fun N => if N < N1 then 1 else 2 / (N : ℝ) ^ 2
  have hg0 : ∀ N, 0 ≤ g N := by
    intro N; simp only [g]; split_ifs <;> positivity
  have hle : ∀ N, P (X N ⁻¹' S N) ≤ ENNReal.ofReal (g N) := by
    intro N
    simp only [g]
    split_ifs with h
    · simpa using prob_le_one
    · rw [← ofReal_measureReal (μ := P)]
      apply ENNReal.ofReal_le_ofReal
      rw [measureReal_def, hP N, ← measureReal_def]
      exact hb N (by omega)
  have hsum : Summable g := by
    rw [← summable_nat_add_iff N1]
    have h2 : Summable (fun n : ℕ => 2 / ((n + N1 : ℕ) : ℝ) ^ 2) := by
      have := (Real.summable_one_div_nat_pow.mpr (one_lt_two)).mul_left 2
      have h' := (summable_nat_add_iff N1).mpr this
      refine h'.congr (fun n => ?_)
      simp [div_eq_mul_inv]
    refine h2.congr (fun n => ?_)
    simp [g]
  apply ae_eventually_notMem
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hsum]
  exact ENNReal.ofReal_ne_top

/-! ### Chernoff bounds for sums of independent `{0,1}`-valued variables -/

lemma mgf_zero_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) (h01 : ∀ ω, Y ω = 0 ∨ Y ω = 1) (hint : Integrable Y μ)
    (t : ℝ) : mgf Y μ t = 1 + (Real.exp t - 1) * ∫ ω, Y ω ∂μ := by
  have : ∀ ω, Real.exp (t * Y ω) = 1 + (Real.exp t - 1) * Y ω := by
    intro ω
    rcases h01 ω with h | h <;> simp [h]
  unfold mgf
  simp_rw [this]
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul]
  simp

lemma mgf_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (Y : ι → Ω → ℝ) (hind : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (hint : ∀ i, Integrable (Y i) μ)
    (s : Finset ι) (t : ℝ) :
    mgf (∑ i ∈ s, Y i) μ t ≤ Real.exp ((Real.exp t - 1) * ∑ i ∈ s, ∫ ω, Y i ω ∂μ) := by
  rw [hind.mgf_sum hY s, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _; exact mgf_nonneg
  · intro i _
    rw [mgf_zero_one (hY i) (h01 i) (hint i)]
    have := Real.add_one_le_exp ((Real.exp t - 1) * ∫ ω, Y i ω ∂μ)
    linarith

lemma integrable_exp_of_zero_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S : Ω → ℝ} (hS : Measurable S) (B : ℝ) (hB : ∀ ω, |S ω| ≤ B)
    (t : ℝ) : Integrable (fun ω => Real.exp (t * S ω)) μ := by
  refine Integrable.of_bound (C := Real.exp (|t| * B)) ?_ ?_
  · exact (measurable_const.mul hS).exp.aestronglyMeasurable
  · refine ae_of_all _ (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc t * S ω ≤ |t * S ω| := le_abs_self _
      _ = |t| * |S ω| := abs_mul _ _
      _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB ω) (abs_nonneg _)

/-- Two-sided Chernoff bound, upper tail: if `∑ E Y_i ≤ ζ` and `0 ≤ t ≤ 2ζ`, then
`P(∑ Y_i ≥ ∑ E Y_i + t) ≤ exp(-t²/(4ζ))`. -/
lemma chernoff_upper {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (Y : ι → Ω → ℝ) (hind : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (s : Finset ι) (ζ t : ℝ) (hζ : 0 < ζ)
    (hmean : ∑ i ∈ s, ∫ ω, Y i ω ∂μ ≤ ζ) (ht0 : 0 ≤ t) (ht : t ≤ 2 * ζ) :
    μ.real {ω | (∑ i ∈ s, ∫ ω, Y i ω ∂μ) + t ≤ ∑ i ∈ s, Y i ω} ≤ Real.exp (-t ^ 2 / (4 * ζ)) := by
  have hint : ∀ i, Integrable (Y i) μ := fun i =>
    Integrable.of_bound (C := 1) (hY i).aestronglyMeasurable
      (ae_of_all _ fun ω => by rcases h01 i ω with h | h <;> simp [h])
  set m := ∑ i ∈ s, ∫ ω, Y i ω ∂μ with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => by
    rcases h01 i ω with h | h <;> simp [h]))
  set l := t / (2 * ζ) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; exact ht
  have hSmeas : Measurable (∑ i ∈ s, Y i) := by
    have h := Finset.measurable_sum s (fun i _ => hY i)
    have he : (∑ i ∈ s, Y i) = fun a => ∑ i ∈ s, Y i a := by ext; simp [Finset.sum_apply]
    rw [he]; exact h
  have hbound : ∀ ω, |(∑ i ∈ s, Y i) ω| ≤ s.card := by
    intro ω
    rw [Finset.sum_apply]
    calc |∑ i ∈ s, Y i ω| ≤ ∑ i ∈ s, |Y i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
          rcases h01 i ω with h | h <;> simp [h])
      _ = s.card := by simp
  have h1 := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ s, Y i) (m + t) hl0
    (integrable_exp_of_zero_one hSmeas _ hbound l)
  have h2 := mgf_sum_le Y hind hY h01 hint s l
  have hset : {ω | m + t ≤ ∑ i ∈ s, Y i ω} = {ω | m + t ≤ (∑ i ∈ s, Y i) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [hset]
  refine h1.trans ?_
  calc Real.exp (-l * (m + t)) * mgf (∑ i ∈ s, Y i) μ l
      ≤ Real.exp (-l * (m + t)) * Real.exp ((Real.exp l - 1) * m) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (m * (Real.exp l - 1 - l) - l * t) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-t ^ 2 / (4 * ζ)) := by
        apply Real.exp_le_exp.mpr
        have hb := Real.abs_exp_sub_one_sub_id_le (x := l) (by rw [abs_of_nonneg hl0]; exact hl1)
        have hb' : Real.exp l - 1 - l ≤ l ^ 2 := (abs_le.mp hb).2
        have hpos : 0 ≤ Real.exp l - 1 - l := by linarith [Real.add_one_le_exp l]
        have : m * (Real.exp l - 1 - l) ≤ ζ * l ^ 2 :=
          mul_le_mul hmean hb' hpos hζ.le
        have hcalc : ζ * l ^ 2 - l * t = -t ^ 2 / (4 * ζ) := by
          rw [hl]; field_simp; ring
        linarith

/-- Two-sided Chernoff bound, lower tail. -/
lemma chernoff_lower {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (Y : ι → Ω → ℝ) (hind : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (s : Finset ι) (ζ t : ℝ) (hζ : 0 < ζ)
    (hmean : ∑ i ∈ s, ∫ ω, Y i ω ∂μ ≤ ζ) (ht0 : 0 ≤ t) (ht : t ≤ 2 * ζ) :
    μ.real {ω | ∑ i ∈ s, Y i ω ≤ (∑ i ∈ s, ∫ ω, Y i ω ∂μ) - t} ≤ Real.exp (-t ^ 2 / (4 * ζ)) := by
  have hint : ∀ i, Integrable (Y i) μ := fun i =>
    Integrable.of_bound (C := 1) (hY i).aestronglyMeasurable
      (ae_of_all _ fun ω => by rcases h01 i ω with h | h <;> simp [h])
  set m := ∑ i ∈ s, ∫ ω, Y i ω ∂μ with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => by
    rcases h01 i ω with h | h <;> simp [h]))
  set l := t / (2 * ζ) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; exact ht
  have hSmeas : Measurable (∑ i ∈ s, Y i) := by
    have h := Finset.measurable_sum s (fun i _ => hY i)
    have he : (∑ i ∈ s, Y i) = fun a => ∑ i ∈ s, Y i a := by ext; simp [Finset.sum_apply]
    rw [he]; exact h
  have hbound : ∀ ω, |(∑ i ∈ s, Y i) ω| ≤ s.card := by
    intro ω
    rw [Finset.sum_apply]
    calc |∑ i ∈ s, Y i ω| ≤ ∑ i ∈ s, |Y i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
          rcases h01 i ω with h | h <;> simp [h])
      _ = s.card := by simp
  have h1 := measure_le_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ s, Y i) (m - t)
    (neg_nonpos.mpr hl0) (integrable_exp_of_zero_one hSmeas _ hbound (-l))
  have h2 := mgf_sum_le Y hind hY h01 hint s (-l)
  have hset : {ω | ∑ i ∈ s, Y i ω ≤ m - t} = {ω | (∑ i ∈ s, Y i) ω ≤ m - t} := by
    ext ω; simp [Finset.sum_apply]
  rw [hset]
  refine h1.trans ?_
  calc Real.exp (- -l * (m - t)) * mgf (∑ i ∈ s, Y i) μ (-l)
      ≤ Real.exp (- -l * (m - t)) * Real.exp ((Real.exp (-l) - 1) * m) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (m * (Real.exp (-l) - 1 - (-l)) - l * t) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-t ^ 2 / (4 * ζ)) := by
        apply Real.exp_le_exp.mpr
        have hb := Real.abs_exp_sub_one_sub_id_le (x := -l)
          (by rw [abs_neg, abs_of_nonneg hl0]; exact hl1)
        have hb' : Real.exp (-l) - 1 - (-l) ≤ (-l) ^ 2 := (abs_le.mp hb).2
        have hpos : 0 ≤ Real.exp (-l) - 1 - (-l) := by linarith [Real.add_one_le_exp (-l)]
        have : m * (Real.exp (-l) - 1 - (-l)) ≤ ζ * l ^ 2 := by
          have := mul_le_mul hmean hb' hpos hζ.le
          simpa using this
        have hcalc : ζ * l ^ 2 - l * t = -t ^ 2 / (4 * ζ) := by
          rw [hl]; field_simp; ring
        linarith

/-! ### The product Bernoulli law -/

open StrictCompatLB.Inhomogeneous

/-- indicator of `true` -/
noncomputable def bv (b : Bool) : ℝ := if b = true then 1 else 0

lemma bv_01 (b : Bool) : bv b = 0 ∨ bv b = 1 := by
  cases b <;> simp [bv]

lemma measurable_bv : Measurable bv := measurable_of_countable _

instance bernoulliEdge_isProb (q : ℝ) : IsProbabilityMeasure (bernoulliEdge q) := by
  unfold bernoulliEdge; infer_instance

/-- the product Bernoulli law with column probabilities `q`. -/
noncomputable abbrev PiB (N m : ℕ) (q : Fin m → ℝ) : Measure (Fin N × Fin m → Bool) :=
  Measure.pi fun e => bernoulliEdge (q e.2)

lemma coord_indep (N m : ℕ) (q : Fin m → ℝ) :
    iIndepFun (fun (e : Fin N × Fin m) (x : Fin N × Fin m → Bool) => x e) (PiB N m q) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

lemma integral_bernoulliEdge (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(bernoulliEdge q) = q * f true + (1 - q) * f false := by
  unfold bernoulliEdge
  rw [integral_bernoulliMeasure, Set.projIcc_of_mem _ ⟨hq0, hq1⟩]
  simp

lemma integral_coord (N m : ℕ) (q : Fin m → ℝ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∀ w, q w ≤ 1)
    (e : Fin N × Fin m) (f : Bool → ℝ) :
    ∫ x, f (x e) ∂(PiB N m q) = q e.2 * f true + (1 - q e.2) * f false := by
  have hmp := measurePreserving_eval (fun e : Fin N × Fin m => bernoulliEdge (q e.2)) e
  have : ∫ x, f (x e) ∂(PiB N m q) = ∫ b, f b ∂(bernoulliEdge (q e.2)) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (measurable_of_countable f).aestronglyMeasurable]
  rw [this, integral_bernoulliEdge _ (hq0 _) (hq1 _)]

lemma integral_bv_coord (N m : ℕ) (q : Fin m → ℝ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∀ w, q w ≤ 1)
    (e : Fin N × Fin m) : ∫ x, bv (x e) ∂(PiB N m q) = q e.2 := by
  rw [integral_coord N m q hq0 hq1 e bv]; simp [bv]

lemma col_indep (N m : ℕ) (q : Fin m → ℝ) (w : Fin m) :
    iIndepFun (fun (v : Fin N) (x : Fin N × Fin m → Bool) => bv (x (v, w))) (PiB N m q) := by
  have h := (coord_indep N m q).precomp (g := fun v : Fin N => (v, w))
    (fun a b hab => by simpa using hab)
  exact h.comp (fun _ => bv) (fun _ => measurable_bv)

lemma row_indep (N m : ℕ) (q : Fin m → ℝ) (v : Fin N) (g : Fin m → Bool → ℝ)
    (hg : ∀ w, Measurable (g w)) :
    iIndepFun (fun (w : Fin m) (x : Fin N × Fin m → Bool) => g w (x (v, w))) (PiB N m q) := by
  have h := (coord_indep N m q).precomp (g := fun w : Fin m => (v, w))
    (fun a b hab => by simpa using hab)
  exact h.comp g hg

lemma card_filter_eq_sum_bv {N m : ℕ} (x : Fin N × Fin m → Bool) (w : Fin m) :
    (((Finset.univ.filter fun v : Fin N => x (v, w) = true).card : ℕ) : ℝ) =
      ∑ v : Fin N, bv (x (v, w)) := by
  simp [bv, Finset.sum_boole]

end InhomAux

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace InhomAux

/-- The `N`-th bad event of Lemma B.2 has probability at most `2 / N²`. -/
lemma B2_perN (N m : ℕ) (hm : 0 < m) (hN : 2 ≤ N) (q : Fin m → ℝ) (hq0 : ∀ w, 0 < q w)
    (hq1 : ∀ w, q w ≤ 1) (δ η : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hA : ∀ w, 2 * (Real.log m + Real.log N) ≤ δ ^ 2 * (N * q w) / 4)
    (hB : 3 * Real.log N ≤ 2 * η ^ 2 * (m : ℝ) ^ 2 * (∑ w, (q w)⁻¹ ^ 2)⁻¹) :
    (PiB N m q).real {x | ∃ v : Fin N, (1 + η) / (1 - δ) < (N : ℝ) / m *
        ∑ w : Fin m, (if x (v, w) = true then
          (((Finset.univ.filter fun v' : Fin N => x (v', w) = true).card : ℕ) : ℝ)⁻¹ else 0)}
      ≤ 2 / (N : ℝ) ^ 2 := by
  have hq0' : ∀ w, 0 ≤ q w := fun w => (hq0 w).le
  have hNpos : (0 : ℝ) < N := by have : (2:ℝ) ≤ N := by exact_mod_cast hN
                                 linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  -- column variables
  let Y : Fin m → Fin N → (Fin N × Fin m → Bool) → ℝ := fun w v x => bv (x (v, w))
  have hYmean : ∀ w, ∑ v : Fin N, ∫ x, Y w v x ∂(PiB N m q) = N * q w := by
    intro w
    show ∑ v : Fin N, ∫ x, bv (x (v, w)) ∂(PiB N m q) = N * q w
    simp_rw [integral_bv_coord N m q hq0' hq1]
    simp
  -- row variables
  let X : Fin N → Fin m → (Fin N × Fin m → Bool) → ℝ := fun v w x => bv (x (v, w)) / (m * q w)
  have hXint : ∀ v w, ∫ x, X v w x ∂(PiB N m q) = 1 / m := by
    intro v w
    show ∫ x, bv (x (v, w)) / (m * q w) ∂(PiB N m q) = 1 / m
    rw [integral_div, integral_bv_coord N m q hq0' hq1]
    have := hq0 w
    field_simp
  let Z : Fin N → Fin m → (Fin N × Fin m → Bool) → ℝ := fun v w x => X v w x - ∫ y, X v w y ∂(PiB N m q)
  let L : Fin m → Set (Fin N × Fin m → Bool) := fun w =>
    {x | ∑ v : Fin N, Y w v x ≤ (∑ v : Fin N, ∫ y, Y w v y ∂(PiB N m q)) - δ * (N * q w)}
  let H : Fin N → Set (Fin N × Fin m → Bool) := fun v => {x | η ≤ ∑ w : Fin m, Z v w x}
  -- Step 1: inclusion
  have hincl : {x | ∃ v : Fin N, (1 + η) / (1 - δ) < (N : ℝ) / m *
        ∑ w : Fin m, (if x (v, w) = true then
          (((Finset.univ.filter fun v' : Fin N => x (v', w) = true).card : ℕ) : ℝ)⁻¹ else 0)}
      ⊆ (⋃ w ∈ (Finset.univ : Finset (Fin m)), L w) ∪ (⋃ v ∈ (Finset.univ : Finset (Fin N)), H v) := by
    intro x hx
    obtain ⟨v, hv⟩ := hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨hL, hH⟩ := hcon
    have hcol : ∀ w, (1 - δ) * (N * q w) <
        (((Finset.univ.filter fun v' : Fin N => x (v', w) = true).card : ℕ) : ℝ) := by
      intro w
      have := hL w (Finset.mem_univ _)
      simp only [L, Set.mem_ofPred_eq, not_le, hYmean] at this
      rw [card_filter_eq_sum_bv]
      simp only [Y] at this
      linarith
    have hrow : ∑ w : Fin m, X v w x < η + 1 := by
      have := hH v (Finset.mem_univ _)
      simp only [H, Z, Set.mem_ofPred_eq, not_le, Finset.sum_sub_distrib, hXint] at this
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      have h1 : (m : ℝ) * (1 / m) = 1 := by field_simp
      linarith
    have hterm : ∀ w, (if x (v, w) = true then
          (((Finset.univ.filter fun v' : Fin N => x (v', w) = true).card : ℕ) : ℝ)⁻¹ else 0)
        ≤ bv (x (v, w)) / ((1 - δ) * (N * q w)) := by
      intro w
      have hpos : 0 < (1 - δ) * (N * q w) := by
        have := hq0 w; have : 0 < 1 - δ := by linarith
        positivity
      by_cases hxw : x (v, w) = true
      · rw [if_pos hxw]
        simp only [bv, hxw, if_true]
        rw [one_div]
        exact inv_anti₀ hpos (hcol w).le
      · rw [if_neg hxw]
        simp [bv, hxw]
    have hsum : (N : ℝ) / m * ∑ w : Fin m, (if x (v, w) = true then
          (((Finset.univ.filter fun v' : Fin N => x (v', w) = true).card : ℕ) : ℝ)⁻¹ else 0)
        ≤ (1 / (1 - δ)) * ∑ w : Fin m, X v w x := by
      calc (N : ℝ) / m * ∑ w : Fin m, (if x (v, w) = true then
            (((Finset.univ.filter fun v' : Fin N => x (v', w) = true).card : ℕ) : ℝ)⁻¹ else 0)
          ≤ (N : ℝ) / m * ∑ w : Fin m, bv (x (v, w)) / ((1 - δ) * (N * q w)) := by
            apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ => hterm w))
            positivity
        _ = (1 / (1 - δ)) * ∑ w : Fin m, X v w x := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro w _
            simp only [X]
            have := hq0 w
            have : 0 < 1 - δ := by linarith
            field_simp
    have h1δ : 0 < 1 - δ := by linarith
    have : (1 / (1 - δ)) * ∑ w : Fin m, X v w x < (1 + η) / (1 - δ) := by
      rw [div_mul_eq_mul_div, one_mul]
      exact div_lt_div_of_pos_right (by linarith) h1δ
    linarith
  -- Step 2: probability bounds
  have hLbound : ∀ w, (PiB N m q).real (L w) ≤ 1 / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
    intro w
    have hζ : 0 < (N : ℝ) * q w := mul_pos hNpos (hq0 w)
    have hch := chernoff_lower (μ := PiB N m q) (Y w) (col_indep N m q w)
      (fun v => measurable_bv.comp (measurable_pi_apply _)) (fun v x => bv_01 _)
      Finset.univ (N * q w) (δ * (N * q w)) hζ (le_of_eq (hYmean w)) (by positivity)
      (by nlinarith)
    refine hch.trans ?_
    have hexp : -(δ * (N * q w)) ^ 2 / (4 * (N * q w)) = -(δ ^ 2 * (N * q w) / 4) := by
      field_simp
    rw [hexp]
    have hmN : (0 : ℝ) < m * N := mul_pos hmpos hNpos
    calc Real.exp (-(δ ^ 2 * (N * q w) / 4)) ≤ Real.exp (-(2 * (Real.log m + Real.log N))) :=
          Real.exp_le_exp.mpr (by linarith [hA w])
      _ = 1 / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
          rw [← Real.log_mul hmpos.ne' hNpos.ne',
            show (2 : ℝ) * Real.log (m * N) = ((2 : ℕ) : ℝ) * Real.log (m * N) by norm_num,
            ← Real.log_pow, Real.exp_neg,
            Real.exp_log (by positivity)]
          ring
  have hHbound : ∀ v, (PiB N m q).real (H v) ≤ 1 / (N : ℝ) ^ 3 := by
    intro v
    have hsub : ∀ w ∈ (Finset.univ : Finset (Fin m)),
        HasSubgaussianMGF (Z v w) ((‖(1 / (m * q w)) - 0‖₊ / 2) ^ 2) (PiB N m q) := by
      intro w _
      apply hasSubgaussianMGF_of_mem_Icc
      · exact ((measurable_bv.comp (measurable_pi_apply _)).div_const _).aemeasurable
      · refine ae_of_all _ (fun x => ?_)
        have := hq0 w
        show bv (x (v, w)) / (m * q w) ∈ Set.Icc 0 (1 / (m * q w))
        rcases bv_01 (x (v, w)) with h | h <;> rw [h]
        · rw [zero_div]; exact ⟨le_refl 0, by positivity⟩
        · exact ⟨by positivity, le_refl _⟩
    have hind : iIndepFun (Z v) (PiB N m q) := by
      have := row_indep N m q v (fun w b => bv b / (m * q w) - ∫ y, X v w y ∂(PiB N m q))
        (fun w => (measurable_bv.div_const _).sub_const _)
      exact this
    have hh := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hη.le
    have hset : H v = {x | η ≤ ∑ w ∈ Finset.univ, Z v w x} := rfl
    rw [hset]
    refine hh.trans ?_
    have hc : ((∑ w ∈ (Finset.univ : Finset (Fin m)), (‖(1 / (m * q w)) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ)
        = (∑ w : Fin m, (q w)⁻¹ ^ 2) / (4 * (m : ℝ) ^ 2) := by
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      have := hq0 w
      rw [sub_zero, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
      norm_num
    rw [hc]
    have hS : 0 < ∑ w : Fin m, (q w)⁻¹ ^ 2 := by
      have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      exact Finset.sum_pos (fun w _ => by have := hq0 w; positivity) Finset.univ_nonempty
    have hexp : -η ^ 2 / (2 * ((∑ w : Fin m, (q w)⁻¹ ^ 2) / (4 * (m : ℝ) ^ 2)))
        = -(2 * η ^ 2 * (m : ℝ) ^ 2 * (∑ w, (q w)⁻¹ ^ 2)⁻¹) := by
      field_simp
      norm_num
    rw [hexp]
    calc Real.exp (-(2 * η ^ 2 * (m : ℝ) ^ 2 * (∑ w, (q w)⁻¹ ^ 2)⁻¹))
        ≤ Real.exp (-(3 * Real.log N)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (N : ℝ) ^ 3 := by
          rw [show (3 : ℝ) * Real.log N = ((3 : ℕ) : ℝ) * Real.log N by norm_num,
            ← Real.log_pow, Real.exp_neg, Real.exp_log (by positivity)]
          ring
  calc (PiB N m q).real _ ≤ (PiB N m q).real ((⋃ w ∈ (Finset.univ : Finset (Fin m)), L w) ∪
        (⋃ v ∈ (Finset.univ : Finset (Fin N)), H v)) := measureReal_mono hincl
    _ ≤ (PiB N m q).real (⋃ w ∈ (Finset.univ : Finset (Fin m)), L w) +
        (PiB N m q).real (⋃ v ∈ (Finset.univ : Finset (Fin N)), H v) := measureReal_union_le _ _
    _ ≤ (∑ w ∈ (Finset.univ : Finset (Fin m)), (PiB N m q).real (L w)) +
        ∑ v ∈ (Finset.univ : Finset (Fin N)), (PiB N m q).real (H v) :=
          add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _)
    _ ≤ (∑ w ∈ (Finset.univ : Finset (Fin m)), 1 / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2)) +
        ∑ v ∈ (Finset.univ : Finset (Fin N)), 1 / (N : ℝ) ^ 3 :=
          add_le_add (Finset.sum_le_sum (fun w _ => hLbound w))
            (Finset.sum_le_sum (fun v _ => hHbound v))
    _ ≤ 2 / (N : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : (m : ℝ) * (1 / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2)) ≤ 1 / (N : ℝ) ^ 2 := by
          have he : (m : ℝ) * (1 / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2)) = 1 / ((m : ℝ) * (N : ℝ) ^ 2) := by
            field_simp
          rw [he]
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith [sq_nonneg (N : ℝ)]
        have h2 : (N : ℝ) * (1 / (N : ℝ) ^ 3) = 1 / (N : ℝ) ^ 2 := by
          field_simp
        have h3 : 1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 = 2 / (N : ℝ) ^ 2 := by ring
        linarith

end InhomAux

namespace InhomAux
open StrictCompatLB.Inhomogeneous

lemma minEdgeProb_le (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ) (w : Fin (M N)) :
    minEdgeProb M p N ≤ p N w :=
  ciInf_le (Finite.bddBelow_range _) w

lemma B2_main (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h_min : Tendsto (fun N : ℕ =>
      minEdgeProb M p N / ((Real.log (M N) + Real.log N) / (N : ℝ))) atTop atTop)
    (h_norm : Tendsto (fun N : ℕ =>
      invNormSq M p N / (Real.log N / (M N : ℝ) ^ 2)) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.RegularDegree.SatisfiesA19 M (fun N => graphOf (X N ω)) := by
  classical
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let Bad : ℕ → (N : ℕ) → Set (Fin N × Fin (M N) → Bool) := fun k N =>
    {x | ∃ v : Fin N, (1 + ε k / 4) / (1 - ε k / 4) < (N : ℝ) / (M N) *
        ∑ w : Fin (M N), (if x (v, w) = true then
          (((Finset.univ.filter fun v' : Fin N => x (v', w) = true).card : ℕ) : ℝ)⁻¹ else 0)}
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hε1 : ∀ k, ε k ≤ 1 := fun k => by
    simp only [ε]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hk : ∀ k, ∀ᵐ ω ∂P, ∀ᶠ N in atTop, X N ω ∉ Bad k N := by
    intro k
    set δ := ε k / 4 with hδdef
    have hδ : 0 < δ := by have := hεpos k; positivity
    have hδ1 : δ < 1 := by have := hε1 k; linarith
    have hKA := h_min.eventually_ge_atTop (8 / δ ^ 2)
    have hKB := h_norm.eventually_ge_atTop (3 / (2 * δ ^ 2))
    obtain ⟨N1, hN1⟩ := (hKA.and (hKB.and (eventually_ge_atTop 2))).exists_forall_of_atTop
    refine bc_wrapper P X hX_meas (edgeLaw M p) hX_law (Bad k)
      (fun N => (Set.toFinite _).measurableSet) N1 ?_
    intro N hN
    obtain ⟨hA', hB', hN2⟩ := hN1 N hN
    have hNpos : (0 : ℝ) < N := by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
                                   linarith
    have hMpos : (0 : ℝ) < M N := by exact_mod_cast hM N
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hlogM : 0 ≤ Real.log (M N) := Real.log_nonneg (by exact_mod_cast hM N)
    have hA : ∀ w, 2 * (Real.log (M N) + Real.log N) ≤ δ ^ 2 * (N * p N w) / 4 := by
      intro w
      have hL : 0 < (Real.log (M N) + Real.log N) / (N : ℝ) := by positivity
      have h1 : 8 / δ ^ 2 * ((Real.log (M N) + Real.log N) / (N : ℝ)) ≤ minEdgeProb M p N :=
        (le_div_iff₀ hL).mp hA'
      have h2 := minEdgeProb_le M p N w
      have h3 : 8 / δ ^ 2 * ((Real.log (M N) + Real.log N) / (N : ℝ)) * (δ ^ 2 * N / 4)
          = 2 * (Real.log (M N) + Real.log N) := by
        field_simp; ring
      have h4 : 0 ≤ δ ^ 2 * N / 4 := by positivity
      nlinarith
    have hB : 3 * Real.log N ≤ 2 * δ ^ 2 * (M N : ℝ) ^ 2 * (∑ w, (p N w)⁻¹ ^ 2)⁻¹ := by
      have hL : 0 < Real.log N / (M N : ℝ) ^ 2 := by positivity
      have h1 : 3 / (2 * δ ^ 2) * (Real.log N / (M N : ℝ) ^ 2) ≤ invNormSq M p N :=
        (le_div_iff₀ hL).mp hB'
      have h3 : 3 / (2 * δ ^ 2) * (Real.log N / (M N : ℝ) ^ 2) * (2 * δ ^ 2 * (M N : ℝ) ^ 2)
          = 3 * Real.log N := by
        field_simp
      have h4 : 0 ≤ 2 * δ ^ 2 * (M N : ℝ) ^ 2 := by positivity
      have : invNormSq M p N = (∑ w, (p N w)⁻¹ ^ 2)⁻¹ := rfl
      rw [← this]
      nlinarith
    exact B2_perN N (M N) (hM N) hN2 (p N) (hp_pos N) (hp_le N) δ δ hδ hδ1 hδ hA hB
  have hall := ae_all_iff.mpr hk
  filter_upwards [hall] with ω hω
  intro e he
  obtain ⟨k, hk'⟩ := exists_nat_one_div_lt he
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hω k)
  refine ⟨N0, fun N hN v => ?_⟩
  have hnot := hN0 N hN
  simp only [Bad, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
  have hv := hnot v
  have hδ1 : ε k / 4 < 1 := by have := hε1 k; linarith
  have hbound : (1 + ε k / 4) / (1 - ε k / 4) ≤ 1 + e := by
    rw [div_le_iff₀ (by linarith)]
    have := hε1 k
    have := hεpos k
    have hk'' : ε k < e := hk'
    nlinarith
  refine le_trans (le_of_eq ?_) (hv.trans hbound)
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  simp [StrictCompatLB.MeanField.nbrW, graphOf]

end InhomAux

open MeasureTheory Filter Topology

open StrictCompatLB.Inhomogeneous in
theorem solution (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h_min : Tendsto (fun N : ℕ =>
      minEdgeProb M p N / ((Real.log (M N) + Real.log N) / (N : ℝ))) atTop atTop)
    (h_norm : Tendsto (fun N : ℕ =>
      invNormSq M p N / (Real.log N / (M N : ℝ) ^ 2)) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsSubcritical d M (fun N => graphOf (X N ω)) := by
  filter_upwards [InhomAux.B2_main d hd M hM p hp_pos hp_le h_min h_norm P X hX_meas hX_law]
    with ω hω
  exact StrictCompatLB.Inhomogeneous.subcritical_of_A19 d (by omega) M _ hω
