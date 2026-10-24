-- Prove2me | solution 1 for StrictCompatLB.Inhomogeneous.lemma_B1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:22:19.445698+00:00
-- url     : https://prove2.me/submissions/70917c33-f0f0-4abf-81e0-6f09255c5d3d

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions

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
open StrictCompatLB.Inhomogeneous

/-- the swap reindexing of the product Bernoulli law. -/
lemma map_swap_PiB (N m : ℕ) (q : Fin m → ℝ) :
    (PiB N m q).map (fun x (e : Fin m × Fin N) => x e.swap) =
      Measure.pi (fun e : Fin m × Fin N => bernoulliEdge (q e.1)) := by
  have hmeas : Measurable (fun (x : Fin N × Fin m → Bool) (e : Fin m × Fin N) => x e.swap) :=
    measurable_pi_lambda _ (fun e => measurable_pi_apply _)
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : Fin N × Fin m → Bool) (e : Fin m × Fin N) => x e.swap) ⁻¹'
      (Set.univ.pi s) = Set.univ.pi (fun e : Fin N × Fin m => s e.swap) := by
    ext x; simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall, Prod.swap_prod_mk]
    exact ⟨fun h a b => h b a, fun h a b => h b a⟩
  rw [hpre, Measure.pi_pi]
  exact Fintype.prod_equiv (Equiv.prodComm (Fin N) (Fin m)) _ _ (fun e => rfl)

/-- the law of the matrix of columns. -/
lemma map_cols_PiB (N m : ℕ) (q : Fin m → ℝ) :
    (PiB N m q).map (fun x (w : Fin m) (v : Fin N) => x (v, w)) =
      Measure.pi (fun w : Fin m => Measure.pi (fun _ : Fin N => bernoulliEdge (q w))) := by
  have hmeas : Measurable (fun (x : Fin N × Fin m → Bool) (e : Fin m × Fin N) => x e.swap) :=
    measurable_pi_lambda _ (fun e => measurable_pi_apply _)
  have hcomp : (fun x (w : Fin m) (v : Fin N) => x (v, w)) =
      (MeasurableEquiv.curry (Fin m) (Fin N) Bool) ∘
        (fun (x : Fin N × Fin m → Bool) (e : Fin m × Fin N) => x e.swap) := by
    ext x w v; rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.curry (Fin m) (Fin N) Bool).measurable hmeas,
    map_swap_PiB]
  have := Measure.infinitePi_map_curry (ι := Fin m) (κ := Fin N) (X := Bool)
    (fun w _ => bernoulliEdge (q w))
  simp only [Measure.infinitePi_eq_pi] at this
  exact this

lemma col_vec_indep (N m : ℕ) (q : Fin m → ℝ) :
    iIndepFun (fun (w : Fin m) (x : Fin N × Fin m → Bool) => fun v : Fin N => x (v, w))
      (PiB N m q) := by
  have hm : ∀ w : Fin m, Measurable (fun (x : Fin N × Fin m → Bool) => fun v : Fin N => x (v, w)) :=
    fun w => measurable_pi_lambda _ (fun v => measurable_pi_apply _)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun w => (hm w).aemeasurable)]
  rw [map_cols_PiB]
  congr 1
  ext1 w
  have h1 : (fun (x : Fin N × Fin m → Bool) => fun v : Fin N => x (v, w)) =
      (Function.eval w) ∘ (fun (x : Fin N × Fin m → Bool) (w : Fin m) (v : Fin N) => x (v, w)) :=
    rfl
  rw [h1, ← Measure.map_map (measurable_pi_apply w)
    (measurable_pi_lambda _ (fun w => hm w)), map_cols_PiB]
  exact ((measurePreserving_eval
    (fun w : Fin m => Measure.pi (fun _ : Fin N => bernoulliEdge (q w))) w).map_eq).symm

/-- Chernoff bound for a sum of independent `{0,1}`-variables of small mean. -/
lemma sparse_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (Y : ι → Ω → ℝ) (hind : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (J δ : ℝ) (hJ : 1 ≤ J) (hδ : 0 ≤ δ)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ ≤ Real.exp (-J)) :
    μ.real {ω | δ * Fintype.card ι ≤ ∑ i, Y i ω} ≤
      Real.exp (-(J - 1) * δ * Fintype.card ι + Fintype.card ι) := by
  have hint : ∀ i, Integrable (Y i) μ := fun i =>
    Integrable.of_bound (C := 1) (hY i).aestronglyMeasurable
      (ae_of_all _ fun ω => by rcases h01 i ω with h | h <;> simp [h])
  have hSmeas : Measurable (∑ i, Y i) := by
    have h := Finset.measurable_sum Finset.univ (fun i _ => hY i)
    have he : (∑ i, Y i) = fun a => ∑ i, Y i a := by ext; simp [Finset.sum_apply]
    rw [he]; exact h
  have hbound : ∀ ω, |(∑ i, Y i) ω| ≤ (Finset.univ : Finset ι).card := by
    intro ω
    rw [Finset.sum_apply]
    calc |∑ i, Y i ω| ≤ ∑ i, |Y i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
          rcases h01 i ω with h | h <;> simp [h])
      _ = (Finset.univ : Finset ι).card := by simp
  have hl : 0 ≤ J - 1 := by linarith
  have h1 := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i, Y i) (δ * Fintype.card ι) hl
    (integrable_exp_of_zero_one hSmeas _ hbound (J - 1))
  have h2 := mgf_sum_le Y hind hY h01 hint Finset.univ (J - 1)
  have hset : {ω | δ * Fintype.card ι ≤ ∑ i, Y i ω} =
      {ω | δ * Fintype.card ι ≤ (∑ i, Y i) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [hset]
  refine h1.trans ?_
  have hsum : (Real.exp (J - 1) - 1) * ∑ i, ∫ ω, Y i ω ∂μ ≤ Fintype.card ι := by
    have hS : ∑ i, ∫ ω, Y i ω ∂μ ≤ Fintype.card ι * Real.exp (-J) := by
      calc ∑ i, ∫ ω, Y i ω ∂μ ≤ ∑ i : ι, Real.exp (-J) := Finset.sum_le_sum (fun i _ => hmean i)
        _ = Fintype.card ι * Real.exp (-J) := by simp
    have hS0 : 0 ≤ ∑ i, ∫ ω, Y i ω ∂μ := Finset.sum_nonneg (fun i _ => integral_nonneg
      (fun ω => by rcases h01 i ω with h | h <;> simp [h]))
    have he : 0 ≤ Real.exp (J - 1) - 1 := by
      have := Real.add_one_le_exp (J - 1); linarith
    have hexp : Real.exp (J - 1) * Real.exp (-J) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.mpr; linarith
    calc (Real.exp (J - 1) - 1) * ∑ i, ∫ ω, Y i ω ∂μ
        ≤ Real.exp (J - 1) * ∑ i, ∫ ω, Y i ω ∂μ := by nlinarith
      _ ≤ Real.exp (J - 1) * (Fintype.card ι * Real.exp (-J)) :=
          mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
      _ = Fintype.card ι * (Real.exp (J - 1) * Real.exp (-J)) := by ring
      _ ≤ Fintype.card ι * 1 := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
      _ = Fintype.card ι := by ring
  calc Real.exp (-(J - 1) * (δ * Fintype.card ι)) * mgf (∑ i, Y i) μ (J - 1)
      ≤ Real.exp (-(J - 1) * (δ * Fintype.card ι)) *
          Real.exp ((Real.exp (J - 1) - 1) * ∑ i, ∫ ω, Y i ω ∂μ) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-(J - 1) * (δ * Fintype.card ι) +
          (Real.exp (J - 1) - 1) * ∑ i, ∫ ω, Y i ω ∂μ) := by rw [Real.exp_add]
    _ ≤ Real.exp (-(J - 1) * δ * Fintype.card ι + Fintype.card ι) := by
        apply Real.exp_le_exp.mpr
        nlinarith

lemma ratio_close (a n η ζ ε : ℝ) (hζ : 0 < ζ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ha : |a - η * ζ| < ε / 6 * ζ) (hn : |n - ζ| < ε / 6 * ζ) :
    |a / n - η| < ε := by
  have hn' := (abs_lt.mp hn).1
  have hnpos : 5 / 6 * ζ < n := by nlinarith
  have hn0 : 0 < n := by linarith
  have h1 : |a - η * n| < 2 * (ε / 6 * ζ) := by
    have : |a - η * n| ≤ |a - η * ζ| + η * |n - ζ| := by
      have e : a - η * n = (a - η * ζ) - η * (n - ζ) := by ring
      rw [e]
      calc |(a - η * ζ) - η * (n - ζ)| ≤ |a - η * ζ| + |η * (n - ζ)| := abs_sub _ _
        _ = |a - η * ζ| + η * |n - ζ| := by rw [abs_mul, abs_of_nonneg hη0]
    have : η * |n - ζ| ≤ ε / 6 * ζ := by
      calc η * |n - ζ| ≤ 1 * |n - ζ| := mul_le_mul_of_nonneg_right hη1 (abs_nonneg _)
        _ ≤ ε / 6 * ζ := by linarith
    linarith
  have e2 : a / n - η = (a - η * n) / n := by field_simp
  rw [e2, abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
  nlinarith

lemma integral_ite_one {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Countable Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (P : Ω → Prop) [DecidablePred P] :
    ∫ x, (if P x then (1 : ℝ) else 0) ∂μ = μ.real {x | P x} := by
  rw [← integral_indicator_one ((Set.to_countable _).measurableSet)]
  congr 1
  ext x
  simp [Set.indicator]

/-- The `N`-th bad event of Lemma B.1 has probability at most `2 / N²`. -/
lemma B1_perN (N m : ℕ) (hm : 0 < m) (hN : 1 ≤ N) (q : Fin m → ℝ) (hq0 : ∀ w, 0 < q w)
    (hq1 : ∀ w, q w ≤ 1) (ε δ J : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hJ1 : 2 + 2 / δ ≤ J) (hJw : ∀ w, 2 * J ≤ (ε / 6) ^ 2 * (N * q w) / 4)
    (hJm : 2 * (N : ℝ) ≤ δ * J * m / 2) :
    (PiB N m q).real {x | ∃ U : Finset (Fin N), δ * m <
        (((Finset.univ.filter fun w : Fin m => ε ≤
          |((((Finset.univ.filter fun v : Fin N => x (v, w) = true) ∩ U).card : ℕ) : ℝ) /
              (((Finset.univ.filter fun v : Fin N => x (v, w) = true).card : ℕ) : ℝ)
            - (U.card : ℝ) / (N : ℝ)|).card : ℕ) : ℝ)}
      ≤ 2 / (N : ℝ) ^ 2 := by
  classical
  have hq0' : ∀ w, 0 ≤ q w := fun w => (hq0 w).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hJ2 : 2 ≤ J := by have : 0 < 2 / δ := by positivity
                         linarith
  -- column statistics
  let bad : Finset (Fin N) → (Fin N → Bool) → Prop := fun U y =>
    ε ≤ |((((Finset.univ.filter fun v : Fin N => y v = true) ∩ U).card : ℕ) : ℝ) /
        (((Finset.univ.filter fun v : Fin N => y v = true).card : ℕ) : ℝ) - (U.card : ℝ) / (N : ℝ)|
  let g : Finset (Fin N) → (Fin N → Bool) → ℝ := fun U y => if bad U y then 1 else 0
  let Y : Finset (Fin N) → Fin m → (Fin N × Fin m → Bool) → ℝ :=
    fun U w x => g U (fun v => x (v, w))
  -- per dispatcher bound
  have hmean : ∀ U w, ∫ x, Y U w x ∂(PiB N m q) ≤ Real.exp (-J) := by
    intro U w
    have hζ : 0 < (N : ℝ) * q w := mul_pos hNpos (hq0 w)
    set ζ := (N : ℝ) * q w with hζdef
    set t := ε / 6 * ζ with htdef
    have ht0 : 0 ≤ t := by positivity
    have ht2 : t ≤ 2 * ζ := by rw [htdef]; nlinarith
    let Z : Fin N → (Fin N × Fin m → Bool) → ℝ := fun v x => bv (x (v, w))
    have hZind : iIndepFun Z (PiB N m q) := col_indep N m q w
    have hZm : ∀ v, Measurable (Z v) := fun v => measurable_bv.comp (measurable_pi_apply _)
    have hZ01 : ∀ v x, Z v x = 0 ∨ Z v x = 1 := fun v x => bv_01 _
    have hZint : ∀ v, ∫ x, Z v x ∂(PiB N m q) = q w := fun v => integral_bv_coord N m q hq0' hq1 _
    have hmU : ∑ v ∈ U, ∫ x, Z v x ∂(PiB N m q) = (U.card : ℝ) / N * ζ := by
      simp_rw [hZint]; rw [Finset.sum_const, nsmul_eq_mul, hζdef]; field_simp
    have hmA : ∑ v ∈ (Finset.univ : Finset (Fin N)), ∫ x, Z v x ∂(PiB N m q) = ζ := by
      simp_rw [hZint]; rw [Finset.sum_const, nsmul_eq_mul, hζdef]; simp
    have hmU_le : ∑ v ∈ U, ∫ x, Z v x ∂(PiB N m q) ≤ ζ := by
      rw [hmU]
      have : (U.card : ℝ) ≤ N := by
        have := Finset.card_le_univ U; simp only [Fintype.card_fin] at this; exact_mod_cast this
      have : (U.card : ℝ) / N ≤ 1 := by rw [div_le_one hNpos]; exact this
      nlinarith
    have b1 := chernoff_upper Z hZind hZm hZ01 U ζ t hζ hmU_le ht0 ht2
    have b2 := chernoff_lower Z hZind hZm hZ01 U ζ t hζ hmU_le ht0 ht2
    have b3 := chernoff_upper Z hZind hZm hZ01 Finset.univ ζ t hζ (le_of_eq hmA) ht0 ht2
    have b4 := chernoff_lower Z hZind hZm hZ01 Finset.univ ζ t hζ (le_of_eq hmA) ht0 ht2
    have hint : ∫ x, Y U w x ∂(PiB N m q) = (PiB N m q).real {x | bad U (fun v => x (v, w))} := by
      simp only [Y, g]
      exact integral_ite_one _ _
    rw [hint]
    have hincl : {x : Fin N × Fin m → Bool | bad U (fun v => x (v, w))} ⊆
        ({x | (∑ v ∈ U, ∫ x, Z v x ∂(PiB N m q)) + t ≤ ∑ v ∈ U, Z v x} ∪
          {x | ∑ v ∈ U, Z v x ≤ (∑ v ∈ U, ∫ x, Z v x ∂(PiB N m q)) - t}) ∪
        ({x | (∑ v ∈ (Finset.univ : Finset (Fin N)), ∫ x, Z v x ∂(PiB N m q)) + t ≤
            ∑ v ∈ (Finset.univ : Finset (Fin N)), Z v x} ∪
          {x | ∑ v ∈ (Finset.univ : Finset (Fin N)), Z v x ≤
            (∑ v ∈ (Finset.univ : Finset (Fin N)), ∫ x, Z v x ∂(PiB N m q)) - t}) := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
      rw [hmU] at h1 h2
      rw [hmA] at h3 h4
      have hcA : ((((Finset.univ.filter fun v : Fin N => x (v, w) = true) ∩ U).card : ℕ) : ℝ) =
          ∑ v ∈ U, Z v x := by
        simp only [Z, bv]
        rw [Finset.sum_boole]
        congr 2
        ext v; simp [and_comm]
      have hcN : (((Finset.univ.filter fun v : Fin N => x (v, w) = true).card : ℕ) : ℝ) =
          ∑ v ∈ (Finset.univ : Finset (Fin N)), Z v x := by
        simp only [Z, bv]
        rw [Finset.sum_boole]
      have hη0 : 0 ≤ (U.card : ℝ) / N := by positivity
      have hη1 : (U.card : ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]
        have := Finset.card_le_univ U; simp only [Fintype.card_fin] at this; exact_mod_cast this
      have key := ratio_close (∑ v ∈ U, Z v x) (∑ v ∈ (Finset.univ : Finset (Fin N)), Z v x)
        ((U.card : ℝ) / N) ζ ε hζ hη0 hη1 hε hε1
        (abs_lt.mpr ⟨by linarith, by linarith⟩) (abs_lt.mpr ⟨by linarith, by linarith⟩)
      have hx' : ε ≤ |((((Finset.univ.filter fun v : Fin N => x (v, w) = true) ∩ U).card : ℕ) : ℝ) /
          (((Finset.univ.filter fun v : Fin N => x (v, w) = true).card : ℕ) : ℝ) -
            (U.card : ℝ) / (N : ℝ)| := hx
      rw [hcA, hcN] at hx'
      linarith
    have hexp : Real.exp (-t ^ 2 / (4 * ζ)) ≤ Real.exp (-(2 * J)) := by
      apply Real.exp_le_exp.mpr
      have e : -t ^ 2 / (4 * ζ) = -((ε / 6) ^ 2 * ζ / 4) := by rw [htdef]; field_simp
      rw [e]; linarith [hJw w]
    have h4J : 4 * Real.exp (-(2 * J)) ≤ Real.exp (-J) := by
      have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ J by linarith)
      have h4 : 4 ≤ Real.exp J := by nlinarith
      have : Real.exp (-(2 * J)) = Real.exp (-J) * (Real.exp J)⁻¹ := by
        rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
      rw [this]
      have hpos := Real.exp_pos (-J)
      have hinv : (Real.exp J)⁻¹ ≤ 1 / 4 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h4
      nlinarith
    calc (PiB N m q).real {x | bad U (fun v => x (v, w))}
        ≤ (PiB N m q).real (({x | (∑ v ∈ U, ∫ x, Z v x ∂(PiB N m q)) + t ≤ ∑ v ∈ U, Z v x} ∪
          {x | ∑ v ∈ U, Z v x ≤ (∑ v ∈ U, ∫ x, Z v x ∂(PiB N m q)) - t}) ∪
        ({x | (∑ v ∈ (Finset.univ : Finset (Fin N)), ∫ x, Z v x ∂(PiB N m q)) + t ≤
            ∑ v ∈ (Finset.univ : Finset (Fin N)), Z v x} ∪
          {x | ∑ v ∈ (Finset.univ : Finset (Fin N)), Z v x ≤
            (∑ v ∈ (Finset.univ : Finset (Fin N)), ∫ x, Z v x ∂(PiB N m q)) - t})) :=
          measureReal_mono hincl
      _ ≤ (Real.exp (-t ^ 2 / (4 * ζ)) + Real.exp (-t ^ 2 / (4 * ζ))) +
          (Real.exp (-t ^ 2 / (4 * ζ)) + Real.exp (-t ^ 2 / (4 * ζ))) := by
          refine (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
          · exact (measureReal_union_le _ _).trans (add_le_add b1 b2)
          · exact (measureReal_union_le _ _).trans (add_le_add b3 b4)
      _ ≤ Real.exp (-J) := by linarith
  -- per set bound
  have hset : ∀ U : Finset (Fin N), (PiB N m q).real
      {x | δ * Fintype.card (Fin m) ≤ ∑ w, Y U w x} ≤ Real.exp (-(2 * N)) := by
    intro U
    have hind : iIndepFun (Y U) (PiB N m q) :=
      (col_vec_indep N m q).comp (fun _ => g U) (fun _ => measurable_of_countable _)
    have hYm : ∀ w, Measurable (Y U w) := fun w => measurable_of_countable _
    have hY01 : ∀ w x, Y U w x = 0 ∨ Y U w x = 1 := by
      intro w x; simp only [Y, g]; split_ifs <;> simp
    have h := sparse_tail (Y U) hind hYm hY01 J δ (by linarith) hδ.le (hmean U)
    refine h.trans (Real.exp_le_exp.mpr ?_)
    simp only [Fintype.card_fin]
    have : (J - 1) * δ * m - m ≥ δ * J * m / 2 := by
      have h' : δ * J / 2 ≥ δ + 1 := by
        have := mul_le_mul_of_nonneg_left hJ1 hδ.le
        have e : δ * (2 + 2 / δ) = 2 * δ + 2 := by field_simp
        nlinarith
      nlinarith
    nlinarith
  -- union over U
  have hincl : {x | ∃ U : Finset (Fin N), δ * m <
        (((Finset.univ.filter fun w : Fin m => ε ≤
          |((((Finset.univ.filter fun v : Fin N => x (v, w) = true) ∩ U).card : ℕ) : ℝ) /
              (((Finset.univ.filter fun v : Fin N => x (v, w) = true).card : ℕ) : ℝ)
            - (U.card : ℝ) / (N : ℝ)|).card : ℕ) : ℝ)} ⊆
      ⋃ U ∈ (Finset.univ : Finset (Finset (Fin N))),
        {x | δ * Fintype.card (Fin m) ≤ ∑ w, Y U w x} := by
    intro x hx
    obtain ⟨U, hU⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨U, Finset.mem_univ _, ?_⟩
    rw [Fintype.card_fin]
    have : (((Finset.univ.filter fun w : Fin m => ε ≤
          |((((Finset.univ.filter fun v : Fin N => x (v, w) = true) ∩ U).card : ℕ) : ℝ) /
              (((Finset.univ.filter fun v : Fin N => x (v, w) = true).card : ℕ) : ℝ)
            - (U.card : ℝ) / (N : ℝ)|).card : ℕ) : ℝ) = ∑ w, Y U w x := by
      simp only [Y, g, bad]
      rw [Finset.sum_boole]
    linarith
  calc (PiB N m q).real _ ≤ (PiB N m q).real (⋃ U ∈ (Finset.univ : Finset (Finset (Fin N))),
        {x | δ * Fintype.card (Fin m) ≤ ∑ w, Y U w x}) := measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ U ∈ (Finset.univ : Finset (Finset (Fin N))),
          (PiB N m q).real {x | δ * Fintype.card (Fin m) ≤ ∑ w, Y U w x} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ U ∈ (Finset.univ : Finset (Finset (Fin N))), Real.exp (-(2 * N)) :=
        Finset.sum_le_sum (fun U _ => hset U)
    _ = (2 : ℝ) ^ N * Real.exp (-(2 * N)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_finset,
          Fintype.card_fin]
        push_cast; ring
    _ ≤ 2 / (N : ℝ) ^ 2 := by
        have h2e : (2 : ℝ) ^ N ≤ Real.exp N := by
          rw [← Real.exp_one_pow]
          apply pow_le_pow_left₀ (by norm_num)
          linarith [Real.exp_one_gt_d9]
        have hq := Real.quadratic_le_exp_of_nonneg hNpos.le
        have hsplit : Real.exp (-(2 * N)) = (Real.exp N)⁻¹ * (Real.exp N)⁻¹ := by
          rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
        rw [hsplit]
        have heN : 0 < Real.exp N := Real.exp_pos _
        have h1 : (2 : ℝ) ^ N * ((Real.exp N)⁻¹ * (Real.exp N)⁻¹) ≤ (Real.exp N)⁻¹ := by
          rw [← mul_assoc]
          have : (2 : ℝ) ^ N * (Real.exp N)⁻¹ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one heN]; exact h2e
          have hi : 0 < (Real.exp N)⁻¹ := inv_pos.mpr heN
          nlinarith
        refine h1.trans ?_
        rw [inv_eq_one_div, div_le_div_iff₀ heN (by positivity)]
        nlinarith

end InhomAux

namespace InhomAux
open StrictCompatLB.Inhomogeneous

lemma minEdgeProb_le' (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ) (w : Fin (M N)) :
    minEdgeProb M p N ≤ p N w :=
  ciInf_le (Finite.bddBelow_range _) w

lemma B1_main (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (hN : Tendsto (fun N : ℕ => (N : ℝ) * minEdgeProb M p N) atTop atTop)
    (hMp : Tendsto (fun N : ℕ => (M N : ℝ) * minEdgeProb M p N) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (fun N => graphOf (X N ω)) := by
  classical
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let Bad : ℕ → (N : ℕ) → Set (Fin N × Fin (M N) → Bool) := fun k N =>
    {x | ∃ U : Finset (Fin N), ε k * (M N) <
        (((Finset.univ.filter fun w : Fin (M N) => ε k ≤
          |((((Finset.univ.filter fun v : Fin N => x (v, w) = true) ∩ U).card : ℕ) : ℝ) /
              (((Finset.univ.filter fun v : Fin N => x (v, w) = true).card : ℕ) : ℝ)
            - (U.card : ℝ) / (N : ℝ)|).card : ℕ) : ℝ)}
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hε1 : ∀ k, ε k ≤ 1 := fun k => by
    simp only [ε]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hk : ∀ k, ∀ᵐ ω ∂P, ∀ᶠ N in atTop, X N ω ∉ Bad k N := by
    intro k
    set e := ε k with hedef
    have he : 0 < e := hεpos k
    have he1 : e ≤ 1 := hε1 k
    set c := (e / 6) ^ 2 with hcdef
    have hc : 0 < c := by positivity
    have hKA := hN.eventually_ge_atTop (8 * (2 + 2 / e) / c)
    have hKB := hMp.eventually_ge_atTop (32 / (e * c))
    obtain ⟨N1, hN1⟩ := (hKA.and (hKB.and (eventually_ge_atTop 1))).exists_forall_of_atTop
    refine bc_wrapper P X hX_meas (edgeLaw M p) hX_law (Bad k)
      (fun N => (Set.toFinite _).measurableSet) N1 ?_
    intro N hNN
    obtain ⟨hA', hB', hN2⟩ := hN1 N hNN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN2
    have hMpos : (0 : ℝ) < M N := by exact_mod_cast hM N
    set J := c * (N * minEdgeProb M p N) / 8 with hJdef
    have hJ1 : 2 + 2 / e ≤ J := by
      have : 8 * (2 + 2 / e) / c * c ≤ N * minEdgeProb M p N * c :=
        mul_le_mul_of_nonneg_right hA' hc.le
      have e2 : 8 * (2 + 2 / e) / c * c = 8 * (2 + 2 / e) := by field_simp
      rw [hJdef]; nlinarith
    have hJw : ∀ w, 2 * J ≤ (e / 6) ^ 2 * (N * p N w) / 4 := by
      intro w
      have := minEdgeProb_le' M p N w
      rw [hJdef, ← hcdef]
      have : N * minEdgeProb M p N ≤ N * p N w := mul_le_mul_of_nonneg_left this hNpos.le
      nlinarith
    have hJm : 2 * (N : ℝ) ≤ e * J * (M N) / 2 := by
      have h1 : 32 / (e * c) * (e * c) ≤ (M N) * minEdgeProb M p N * (e * c) :=
        mul_le_mul_of_nonneg_right hB' (by positivity)
      have e2 : 32 / (e * c) * (e * c) = 32 := by field_simp
      rw [hJdef]
      have : e * (c * (N * minEdgeProb M p N) / 8) * (M N) / 2 =
          N * ((M N) * minEdgeProb M p N * (e * c)) / 16 := by ring
      rw [this]
      nlinarith
    exact B1_perN N (M N) (hM N) hN2 (p N) (hp_pos N) (hp_le N) e e J he he1 he hJ1 hJw hJm
  have hall := ae_all_iff.mpr hk
  filter_upwards [hall] with ω hω
  intro εε hεε δδ hδδ
  obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (lt_min hεε hδδ)
  have hk1 : ε k < εε := lt_of_lt_of_le hk' (min_le_left _ _)
  have hk2 : ε k < δδ := lt_of_lt_of_le hk' (min_le_right _ _)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hω k)
  refine ⟨N0, fun N hN U => ?_⟩
  have hnot := hN0 N hN
  simp only [Bad, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
  have hU := hnot U
  have hnb : ∀ w, StrictCompatLB.MeanField.nbrW M (fun N => graphOf (X N ω)) N w =
      Finset.univ.filter (fun v : Fin N => X N ω (v, w) = true) := by
    intro w; ext v; simp [StrictCompatLB.MeanField.nbrW, graphOf]
  simp only [hnb]
  have hMpos : (0 : ℝ) ≤ M N := Nat.cast_nonneg _
  refine le_trans ?_ (hU.trans (mul_le_mul_of_nonneg_right hk2.le hMpos))
  exact_mod_cast Finset.card_le_card (fun w hw => by
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, le_trans hk1.le hw.2⟩)

end InhomAux

open MeasureTheory Filter Topology

open StrictCompatLB.Inhomogeneous in
theorem solution (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (hN : Tendsto (fun N : ℕ => (N : ℝ) * minEdgeProb M p N) atTop atTop)
    (hMp : Tendsto (fun N : ℕ => (M N : ℝ) * minEdgeProb M p N) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (fun N => graphOf (X N ω)) :=
  InhomAux.B1_main M hM p hp_pos hp_le hN hMp P X hX_meas hX_law
