-- Prove2me | solution 1 for TDApprox.Conv.lemma_6_cde
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T19:22:52.511275+00:00
-- url     : https://prove2.me/submissions/a4bbce04-c20c-47fe-81e4-46a6a8b9e661

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open TDApprox.Conv
set_option autoImplicit false

open scoped ENNReal
namespace StationaryMoments

variable {S Ω : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  [MeasurableSpace Ω] (P : Kernel S S) [IsMarkovKernel P]
  (π : Measure S) [IsProbabilityMeasure π] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i)

include hi in
lemma marginal (t : ℤ) : μ.map (i t) = π := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (hi.measurable t) (measurableSet_singleton x)]
  change μ {ω | i t ω = x} = π {x}
  simpa using hi.fdd t 0 (fun _ => x)

def segment (t : ℤ) (n : ℕ) (ω : Ω) : Fin (n+1) → S :=
  fun k => i (t + (k : ℕ)) ω

include hi in
lemma measurable_segment (t : ℤ) (n : ℕ) : Measurable (segment i t n) := by
  exact measurable_pi_lambda _ (fun k => hi.measurable _)

include hi in
lemma segment_singleton (t : ℤ) (n : ℕ) (s : Fin (n+1) → S) :
    μ.map (segment i t n) {s} = π {s 0} * ∏ k : Fin n, P (s k.castSucc) {s k.succ} := by
  rw [Measure.map_apply (measurable_segment P π μ i hi t n) (measurableSet_singleton s)]
  convert hi.fdd t n s using 1
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, funext_iff, segment]

include hi in
lemma segment_step (t : ℤ) (n : ℕ) :
    μ.map (fun ω => (segment i t n ω, i (t + (n+1 : ℕ)) ω)) =
      μ.map (segment i t n) ⊗ₘ
        P.comap (fun s : Fin (n+1) → S => s (Fin.last n)) (measurable_pi_apply _) := by
  classical
  let ν := μ.map (segment i t n)
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_segment P π μ i hi t n).aemeasurable
  apply Measure.ext_of_singleton
  rintro ⟨s, x⟩
  have hm : Measurable (fun ω => (segment i t n ω, i (t + (n+1 : ℕ)) ω)) :=
    (measurable_segment P π μ i hi t n).prodMk (hi.measurable _)
  rw [Measure.map_apply hm (measurableSet_singleton _)]
  rw [show ({(s,x)} : Set ((Fin (n+1) → S) × S)) = {s} ×ˢ {x} by
    ext y; simp [Prod.ext_iff]]
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
  rw [lintegral_singleton]
  rw [Kernel.comap_apply, segment_singleton P π μ i hi]
  have he : {ω | (segment i t n ω, i (t + (n+1 : ℕ)) ω) ∈ ({s} ×ˢ {x})} =
      {ω | ∀ k : Fin (n+2), i (t + (k : ℕ)) ω = Fin.snoc (α := fun _ => S) s x k} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hs,hx⟩ k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simpa using hx
      · simpa [segment] using congrFun hs j
    · intro h
      constructor
      · ext j
        simpa [segment] using h j.castSucc
      · simpa using h (Fin.last (n+1))
  change μ {ω | (segment i t n ω, i (t + (n+1 : ℕ)) ω) ∈ ({s} ×ˢ {x})} = _
  rw [he, hi.fdd]
  rw [Fin.prod_univ_castSucc]
  have hz : Fin.snoc (α := fun _ => S) s x 0 = s 0 := by simp
  have hl : Fin.snoc (α := fun _ => S) s x (Fin.last n).succ = x := by
    change Fin.snoc (α := fun _ => S) s x (Fin.last (n+1)) = x
    simp
  have hs (k : Fin n) : Fin.snoc (α := fun _ => S) s x k.castSucc.succ = s k.succ := by
    exact Fin.snoc_castSucc (α := fun _ => S) x s k.succ
  simp only [hz, hl, hs, Fin.snoc_castSucc]
  ac_rfl

end StationaryMoments

namespace StationaryMoments
variable {S Ω : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  [MeasurableSpace Ω] (P : Kernel S S) [IsMarkovKernel P]
  (π : Measure S) [IsProbabilityMeasure π] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i)

include hi in
lemma square_at (t : ℤ) (f : S → ℝ) (hf : Integrable (fun x => f x ^ 2) π) :
    Integrable (fun ω => f (i t ω) ^ 2) μ := by
  have h : Integrable (fun x => f x ^ 2) (μ.map (i t)) := by
    rw [marginal P π μ i hi t]
    exact hf
  exact h.comp_measurable (hi.measurable t)

include hi in
lemma correlation_integrable (t u : ℤ) (f g : S → ℝ)
    (hf : Integrable (fun x => f x ^ 2) π) (hg : Integrable (fun x => g x ^ 2) π) :
    Integrable (fun ω => f (i t ω) * g (i u ω)) μ := by
  have hfm := (measurable_of_countable f).comp (hi.measurable t)
  have hgm := (measurable_of_countable g).comp (hi.measurable u)
  exact ((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr
    (square_at P π μ i hi t f hf)).integrable_mul
    ((memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr
      (square_at P π μ i hi u g hg))

include hi in
lemma next_correlation (t : ℤ) (n : ℕ) (f g : S → ℝ)
    (hf : Integrable (fun x => f x ^ 2) π) (hg : Integrable (fun x => g x ^ 2) π) :
    (∫ ω, f (i t ω) * g (i (t + (n+1 : ℕ)) ω) ∂μ) =
      ∫ ω, f (i t ω) * Pop P g (i (t+n) ω) ∂μ := by
  let ν := μ.map (segment i t n)
  let Q := P.comap (fun s : Fin (n+1) → S => s (Fin.last n)) (measurable_pi_apply _)
  let W := fun ω => (segment i t n ω, i (t+(n+1 : ℕ)) ω)
  let F := fun z : (Fin (n+1) → S) × S => f (z.1 0) * g z.2
  have hW : Measurable W :=
    (measurable_segment P π μ i hi t n).prodMk (hi.measurable _)
  have hF : Measurable F := measurable_of_countable _
  have hFint : Integrable F (μ.map W) := by
    apply (integrable_map_measure hF.aestronglyMeasurable hW.aemeasurable).mpr
    simpa [F, W, segment, Function.comp_def] using correlation_integrable P π μ i hi t (t+(n+1 : ℕ)) f g hf hg
  have hmap : μ.map W = ν ⊗ₘ Q := segment_step P π μ i hi t n
  have hFprod : Integrable F (ν ⊗ₘ Q) := by rwa [← hmap]
  calc
    _ = ∫ z, F z ∂μ.map W := by
      rw [integral_map hW.aemeasurable hF.aestronglyMeasurable]
      simp [W, F, segment]
    _ = ∫ s, ∫ x, F (s,x) ∂Q s ∂ν := by
      rw [hmap, Measure.integral_compProd hFprod]
    _ = ∫ s, f (s 0) * Pop P g (s (Fin.last n)) ∂ν := by
      simp only [F, Q, Kernel.comap_apply, integral_const_mul, Pop]
    _ = _ := by
      rw [show ν = μ.map (segment i t n) from rfl,
        integral_map (measurable_segment P π μ i hi t n).aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]
      simp [segment]

lemma pow_markov (n : ℕ) : IsMarkovKernel (P ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel S S); infer_instance
  | succ n ih =>
    letI := ih
    rw [pow_succ']
    change IsMarkovKernel (P ∘ₖ (P ^ n))
    infer_instance

lemma pow_invariant (h : P.Invariant π) (n : ℕ) : (P ^ n).Invariant π := by
  induction n with
  | zero => exact Measure.id_comp
  | succ n ih =>
    rw [pow_succ']
    exact h.comp ih

lemma pow_row (h : Assumption1a P π) (n : ℕ) (g : S → ℝ)
    (hg : Integrable (fun x => g x ^ 2) π) (x : S) : Integrable g ((P ^ n) x) := by
  letI := pow_markov P n
  have he : ((P ^ n) : Kernel S S) ∘ₘ π = π := pow_invariant P π h.invariant n
  have hs : Integrable (fun x => g x ^ 2) (((P ^ n) : Kernel S S) ∘ₘ π) := by rwa [he]
  have hrow := (ae_iff_of_countable.mp (Measure.ae_integrable_of_integrable_comp hs))
    x (h.pos x).ne'
  exact ((memLp_two_iff_integrable_sq
    (measurable_of_countable g).aestronglyMeasurable).mpr hrow).integrable (by norm_num)

lemma kernel_mean_square_integrable {T : Type*} [MeasurableSpace T]
    (Q : Kernel S T) [IsMarkovKernel Q]
    (hpos : ∀ x, π {x} ≠ 0) (F : T → ℝ) (hF : MemLp F 2 (Q ∘ₘ π)) :
    Integrable (fun x => (∫ y, F y ∂Q x)^2) π := by
  have hsq := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  have hae := Measure.ae_integrable_of_integrable_comp hsq
  have hrow (x : S) : Integrable (fun y => F y ^ 2) (Q x) :=
    (ae_iff_of_countable.mp hae) x (hpos x)
  have hmeas : ∀ᵐ x ∂π, AEStronglyMeasurable F (Q x) := by
    have hm : AEStronglyMeasurable F ((Q ∘ₖ Kernel.const Unit π) ()) :=
      hF.aestronglyMeasurable
    exact hm.comp
  have hLp (x : S) : MemLp F 2 (Q x) := by
    apply (memLp_two_iff_integrable_sq ?_).mpr (hrow x)
    exact (ae_iff_of_countable.mp hmeas) x (hpos x)
  have houter : Integrable (fun x => ∫ y, F y ^ 2 ∂Q x) π := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      Measure.integrable_integral_norm_of_integrable_comp hsq
  apply houter.mono_nonneg (measurable_of_countable _).aestronglyMeasurable
    (ae_of_all _ (fun x => sq_nonneg _))
  apply ae_of_all
  intro x
  have h := variance_nonneg F (Q x)
  rw [variance_eq_sub (hLp x)] at h
  exact sub_nonneg.mp h

lemma pow_square (h : Assumption1a P π) (n : ℕ) (g : S → ℝ)
    (hg : Integrable (fun x => g x ^ 2) π) :
    Integrable (fun x => (∫ y, g y ∂(P ^ n) x)^2) π := by
  letI := pow_markov P n
  have he : ((P ^ n) : Kernel S S) ∘ₘ π = π := pow_invariant P π h.invariant n
  apply kernel_mean_square_integrable π (P ^ n) (fun x => (h.pos x).ne') g
  rw [he]
  exact (memLp_two_iff_integrable_sq (measurable_of_countable g).aestronglyMeasurable).mpr hg

lemma pow_integral_succ (h : Assumption1a P π) (n : ℕ) (g : S → ℝ)
    (hg : Integrable (fun x => g x ^ 2) π) (x : S) :
    (∫ y, Pop P g y ∂(P ^ n) x) = ∫ y, g y ∂(P ^ (n+1)) x := by
  letI := pow_markov P n
  have hr := pow_row P π h (n+1) g hg x
  rw [pow_succ'] at hr ⊢
  exact (Kernel.integral_comp hr).symm

include hi in
lemma correlation_formula (h : Assumption1a P π) (t : ℤ) (n : ℕ) (f g : S → ℝ)
    (hf : Integrable (fun x => f x ^ 2) π) (hg : Integrable (fun x => g x ^ 2) π) :
    (∫ ω, f (i t ω) * g (i (t+n) ω) ∂μ) =
      ∫ x, f x * ∫ y, g y ∂(P ^ n) x ∂π := by
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero, add_zero, pow_zero]
    change (∫ ω, f (i t ω) * g (i t ω) ∂μ) =
      ∫ x, f x * ∫ y, g y ∂(Kernel.id : Kernel S S) x ∂π
    simp only [Kernel.id_apply, integral_dirac]
    have he := integral_map (μ := μ) (hi.measurable t).aemeasurable
      (measurable_of_countable (fun x => f x * g x)).aestronglyMeasurable
    rw [marginal P π μ i hi] at he
    exact he.symm
  | succ n ih =>
    rw [next_correlation P π μ i hi t n f g hf hg]
    have hPg : Integrable (fun x => Pop P g x ^ 2) π := by
      simpa [Pop] using pow_square P π h 1 g hg
    rw [ih (Pop P g) hPg]
    congr 1
    ext x
    rw [pow_integral_succ P π h n g hg x]

lemma outer_integrable (h : Assumption1a P π) (n : ℕ) (f g : S → ℝ)
    (hf : Integrable (fun x => f x ^ 2) π) (hg : Integrable (fun x => g x ^ 2) π) :
    Integrable (fun x => f x * ∫ y, g y ∂(P ^ n) x) π := by
  exact ((memLp_two_iff_integrable_sq
    (measurable_of_countable f).aestronglyMeasurable).mpr hf).integrable_mul
    ((memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).mpr
      (pow_square P π h n g hg))

lemma outer_summable (h : Assumption1a P π) (n : ℕ) (f g : S → ℝ)
    (hf : Integrable (fun x => f x ^ 2) π) (hg : Integrable (fun x => g x ^ 2) π) :
    Summable (fun x => (π {x}).toReal * f x * ∫ y, g y ∂(P ^ n) x) := by
  have ho := outer_integrable P π h n f g hf hg
  rw [← Measure.sum_smul_dirac π] at ho
  have hh := ho.summable_integral
  apply Summable.of_norm
  simpa [integral_smul_measure, integral_dirac, mul_assoc, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hh

include hi in
lemma correlation_bound (t u : ℤ) (f g : S → ℝ)
    (hf : Integrable (fun x => f x ^ 2) π) (hg : Integrable (fun x => g x ^ 2) π) :
    |∫ ω, f (i t ω) * g (i u ω) ∂μ| ≤ (∫ x, f x ^ 2 ∂π) + ∫ x, g x ^ 2 ∂π := by
  have hfs := square_at P π μ i hi t f hf
  have hgs := square_at P π μ i hi u g hg
  have hfg := correlation_integrable P π μ i hi t u f g hf hg
  calc
    _ ≤ ∫ ω, |f (i t ω) * g (i u ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, f (i t ω)^2 + g (i u ω)^2 ∂μ := by
      apply integral_mono hfg.abs (hfs.add hgs)
      intro ω
      change |f (i t ω) * g (i u ω)| ≤ f (i t ω)^2 + g (i u ω)^2
      rw [abs_mul]
      nlinarith [sq_nonneg (|f (i t ω)| - |g (i u ω)|),
        sq_abs (f (i t ω)), sq_abs (g (i u ω))]
    _ = _ := by
      rw [integral_add hfs hgs]
      have he (v : ℤ) (h : S → ℝ) :
          (∫ ω, h (i v ω) ∂μ) = ∫ x, h x ∂π := by
        have hh := integral_map (μ := μ) (hi.measurable v).aemeasurable
          (measurable_of_countable h).aestronglyMeasurable
        rw [marginal P π μ i hi] at hh
        exact hh.symm
      rw [he t (fun x => f x ^ 2), he u (fun x => g x ^ 2)]

end StationaryMoments
namespace EligibilityMoments
open scoped ENNReal

lemma series_L1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (hs : Summable (fun n => ∫ ω, ‖F n ω‖ ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun n => F n ω)) ∧
    Integrable (fun ω => ∑' n, F n ω) μ ∧
    HasSum (fun n => ∫ ω, F n ω ∂μ) (∫ ω, ∑' n, F n ω ∂μ) := by
  have he (n : ℕ) : eLpNorm (F n) 1 μ = ‖∫ ω, ‖F n ω‖ ∂μ‖ₑ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF n).norm, ENNReal.coe_nnreal_eq]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg (F n ω)))]
  have ht : ∑' n, eLpNorm (F n) 1 μ ≠ ⊤ := by
    simp_rw [he]
    exact tsum_enorm_ne_top_iff_summable_norm.mpr hs.norm
  have hae : ∀ᵐ ω ∂μ, Summable (fun n => F n ω) := by
    filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
      (fun n => (hF n).aestronglyMeasurable) ht] with ω hω
    exact hω.of_norm
  have hlp (n : ℕ) : MemLp (F n) 1 μ := memLp_one_iff_integrable.mpr (hF n)
  let f : ℕ → Lp ℝ 1 μ := fun n => (hlp n).toLp (F n)
  have hf : ∑' n, ‖f n‖ₑ ≠ ⊤ := by simpa [f, Lp.enorm_toLp] using ht
  have hsum : MemLp (fun ω => ∑' n, F n ω) 1 μ := by
    apply (Lp.memLp (∑' n, f n)).ae_eq
    filter_upwards [Lp.coeFn_tsum hf, ae_all_iff.mpr (fun n => (hlp n).coeFn_toLp)] with ω hsum heq
    exact hsum.trans (tsum_congr (fun n => heq n))
  exact ⟨hae, memLp_one_iff_integrable.mp hsum,
    hasSum_integral_of_summable_integral_norm hF hs⟩

lemma weighted_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (F : ℕ → Ω → ℝ) (H : Ω → ℝ)
    (hmF : ∀ n, AEStronglyMeasurable (F n) μ) (hmH : AEStronglyMeasurable H μ)
    (hF : ∀ n, Integrable (fun ω => F n ω ^ 2) μ)
    (hH : Integrable (fun ω => H ω ^ 2) μ)
    (B : ℝ) (hB : ∀ n, (∫ ω, F n ω ^ 2 ∂μ) ≤ B) :
    (∀ᵐ ω ∂μ, Summable (fun n => q^n * F n ω * H ω)) ∧
    Integrable (fun ω => ∑' n, q^n * F n ω * H ω) μ ∧
    HasSum (fun n => q^n * ∫ ω, F n ω * H ω ∂μ)
      (∫ ω, ∑' n, q^n * F n ω * H ω ∂μ) := by
  have hprod (n : ℕ) : Integrable (fun ω => F n ω * H ω) μ :=
    ((memLp_two_iff_integrable_sq (hmF n)).mpr (hF n)).integrable_mul
      ((memLp_two_iff_integrable_sq hmH).mpr hH)
  have hb (n : ℕ) : (∫ ω, ‖F n ω * H ω‖ ∂μ) ≤ B + ∫ ω, H ω ^ 2 ∂μ := by
    calc
      _ ≤ ∫ ω, F n ω ^ 2 + H ω ^ 2 ∂μ := by
        apply integral_mono (hprod n).norm ((hF n).add hH)
        intro ω
        change ‖F n ω * H ω‖ ≤ F n ω ^ 2 + H ω ^ 2
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|F n ω| - |H ω|), sq_abs (F n ω), sq_abs (H ω)]
      _ ≤ _ := by rw [integral_add (hF n) hH]; exact add_le_add (hB n) le_rfl
  have hs : Summable (fun n => ∫ ω, ‖q^n * F n ω * H ω‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => norm_nonneg _))
      (fun n => ?_) ((summable_geometric_of_lt_one hq0 hq1).mul_right (B + ∫ ω, H ω^2 ∂μ))
    simp_rw [mul_assoc, norm_mul, Real.norm_of_nonneg (pow_nonneg hq0 n)]
    rw [integral_const_mul]
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left (hb n) (pow_nonneg hq0 n)
  have hh := series_L1 μ (fun n ω => q^n * F n ω * H ω)
    (fun n => by simpa [mul_assoc] using (hprod n).const_mul (q^n)) hs
  refine ⟨hh.1, hh.2.1, ?_⟩
  simpa only [mul_assoc, integral_const_mul] using hh.2.2

variable {S Ω : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  [MeasurableSpace Ω] (P : Kernel S S) [IsMarkovKernel P]
  (π : Measure S) [IsProbabilityMeasure π] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i)

include hi in
lemma pair_law (t : ℤ) : μ.map (fun ω => (i t ω, i (t+1) ω)) = π ⊗ₘ P := by
  apply Measure.ext_of_singleton
  rintro ⟨x,y⟩
  rw [Measure.map_apply ((hi.measurable t).prodMk (hi.measurable (t+1))) (measurableSet_singleton _)]
  rw [show ({(x,y)} : Set (S × S)) = {x} ×ˢ {y} by ext z; simp [Prod.ext_iff]]
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _), lintegral_singleton]
  change μ {ω | i t ω = x ∧ i (t+1) ω = y} = _
  have h := hi.fdd t 1 ![x,y]
  simpa [Fin.forall_fin_two, Fin.prod_univ_one, Set.mem_prod, and_comm, mul_comm] using h

include hi in
lemma cost_square (t : ℤ) (g : S → S → ℝ) (hg : Assumption1b P π g) :
    Integrable (fun ω => g (i t ω) (i (t+1) ω)^2) μ := by
  have h := (integrable_map_measure (μ := μ)
    (measurable_of_countable (fun z : S × S => g z.1 z.2 ^ 2)).aestronglyMeasurable
    ((hi.measurable t).prodMk (hi.measurable (t+1))).aemeasurable)
  rw [pair_law P π μ i hi t] at h
  exact h.mp hg

lemma gbar_square (g : S → S → ℝ) (h : Assumption1a P π) (hg : Assumption1b P π g) :
    Integrable (fun x => gbar P g x ^ 2) π := by
  have hrows := (Measure.integrable_compProd_iff hg.aestronglyMeasurable).mp hg
  have hr (x : S) : Integrable (fun y => g x y ^ 2) (P x) :=
    (ae_iff_of_countable.mp hrows.1) x (h.pos x).ne'
  have hout : Integrable (fun x => ∫ y, g x y ^ 2 ∂P x) π := by
    simpa [Real.norm_eq_abs, abs_sq] using hrows.2
  apply hout.mono_nonneg (measurable_of_countable _).aestronglyMeasurable
    (ae_of_all _ (fun x => sq_nonneg _))
  apply ae_of_all
  intro x
  have v := variance_nonneg (g x) (P x)
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq
    (measurable_of_countable (g x)).aestronglyMeasurable).mpr (hr x))] at v
  exact sub_nonneg.mp v

include hi in
lemma reward_correlation (h : Assumption1a P π) (g : S → S → ℝ)
    (hg : Assumption1b P π g) (t : ℤ) (n : ℕ) (f : S → ℝ)
    (hf : Integrable (fun x => f x ^ 2) π) :
    (∫ ω, f (i t ω) * g (i (t+n) ω) (i (t+n+1) ω) ∂μ) =
      ∫ x, f x * ∫ y, gbar P g y ∂(P ^ n) x ∂π := by
  let ν := μ.map (StationaryMoments.segment i t n)
  let Q := P.comap (fun s : Fin (n+1) → S => s (Fin.last n)) (measurable_pi_apply _)
  let W := fun ω => (StationaryMoments.segment i t n ω, i (t+(n+1 : ℕ)) ω)
  let F := fun z : (Fin (n+1) → S) × S => f (z.1 0) * g (z.1 (Fin.last n)) z.2
  have hW : Measurable W :=
    (StationaryMoments.measurable_segment P π μ i hi t n).prodMk (hi.measurable _)
  have hF : Measurable F := measurable_of_countable _
  have hfm := (measurable_of_countable f).comp (hi.measurable t)
  have hgm : Measurable (fun ω => g (i (t+n) ω) (i (t+n+1) ω)) :=
    (measurable_of_countable (fun z : S × S => g z.1 z.2)).comp
      ((hi.measurable _).prodMk (hi.measurable _))
  have hprod := ((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr
    (StationaryMoments.square_at P π μ i hi t f hf)).integrable_mul
      ((memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr
        (cost_square P π μ i hi (t+n) g hg))
  have hFint : Integrable F (μ.map W) := by
    apply (integrable_map_measure hF.aestronglyMeasurable hW.aemeasurable).mpr
    simpa [F, W, StationaryMoments.segment, Function.comp_def, Nat.cast_add, add_assoc, Pi.mul_def] using hprod
  have hmap : μ.map W = ν ⊗ₘ Q := StationaryMoments.segment_step P π μ i hi t n
  have hFprod : Integrable F (ν ⊗ₘ Q) := by rwa [← hmap]
  calc
    _ = ∫ z, F z ∂μ.map W := by
      rw [integral_map hW.aemeasurable hF.aestronglyMeasurable]
      simp [W, F, StationaryMoments.segment, Nat.cast_add, add_assoc]
    _ = ∫ s, ∫ x, F (s,x) ∂Q s ∂ν := by rw [hmap, Measure.integral_compProd hFprod]
    _ = ∫ s, f (s 0) * gbar P g (s (Fin.last n)) ∂ν := by
      simp only [F, Q, Kernel.comap_apply, integral_const_mul, gbar]
    _ = ∫ ω, f (i t ω) * gbar P g (i (t+n) ω) ∂μ := by
      rw [show ν = μ.map (StationaryMoments.segment i t n) from rfl,
        integral_map (StationaryMoments.measurable_segment P π μ i hi t n).aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]
      simp [StationaryMoments.segment]
    _ = _ := StationaryMoments.correlation_formula P π μ i hi h t n f (gbar P g)
      hf (gbar_square P π g h hg)

include hi in
lemma square_integral_at (t : ℤ) (f : S → ℝ) :
    (∫ ω, f (i t ω) ^ 2 ∂μ) = ∫ x, f x ^ 2 ∂π := by
  have h := integral_map (μ := μ) (hi.measurable t).aemeasurable
    (measurable_of_countable (fun x => f x ^ 2)).aestronglyMeasurable
  rw [StationaryMoments.marginal P π μ i hi] at h
  exact h.symm

include hi in
lemma trace_summable {K : ℕ} (φ : S → Fin K → ℝ) (hφ : ∀ k, Integrable (fun x => φ x k ^ 2) π)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℤ) :
    ∀ᵐ ω ∂μ, Summable (fun n : ℕ => q^n • φ (i (t-n) ω)) := by
  have hc (k : Fin K) : ∀ᵐ ω ∂μ, Summable (fun n : ℕ => q^n * φ (i (t-n) ω) k) := by
    have h := weighted_product μ q hq0 hq1 (fun n ω => φ (i (t-n) ω) k) (fun _ => 1)
      (fun n => ((measurable_of_countable (fun x => φ x k)).comp (hi.measurable _)).aestronglyMeasurable)
      measurable_const.aestronglyMeasurable
      (fun n => StationaryMoments.square_at P π μ i hi _ _ (hφ k))
      (by simpa using integrable_const (1 : ℝ))
      (∫ x, φ x k ^ 2 ∂π) (fun n => (square_integral_at P π μ i hi (t-n) (fun x => φ x k)).le)
    simpa only [mul_one] using h.1
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  exact Pi.summable.mpr hω

include hi in
lemma trace_product {K : ℕ} (φ : S → Fin K → ℝ) (hφ : ∀ k, Integrable (fun x => φ x k ^ 2) π)
    (α lam : ℝ) (hq0 : 0 ≤ α*lam) (hq1 : α*lam < 1) (t : ℤ) (k : Fin K)
    (H : Ω → ℝ) (hmH : AEStronglyMeasurable H μ) (hH : Integrable (fun ω => H ω ^ 2) μ) :
    Integrable (fun ω => zStat α lam φ i t ω k * H ω) μ ∧
    HasSum (fun n : ℕ => (α*lam)^n * ∫ ω, φ (i (t-n) ω) k * H ω ∂μ)
      (∫ ω, zStat α lam φ i t ω k * H ω ∂μ) := by
  have hw := weighted_product μ (α*lam) hq0 hq1 (fun n ω => φ (i (t-n) ω) k) H
    (fun n => ((measurable_of_countable (fun x => φ x k)).comp (hi.measurable _)).aestronglyMeasurable)
    hmH (fun n => StationaryMoments.square_at P π μ i hi _ _ (hφ k)) hH
    (∫ x, φ x k ^ 2 ∂π) (fun n => (square_integral_at P π μ i hi (t-n) (fun x => φ x k)).le)
  have he : (fun ω => ∑' n : ℕ, (α*lam)^n * φ (i (t-n) ω) k * H ω) =ᵐ[μ]
      (fun ω => zStat α lam φ i t ω k * H ω) := by
    filter_upwards [trace_summable P π μ i hi φ hφ (α*lam) hq0 hq1 t] with ω hω
    rw [zStat, tsum_apply hω]
    exact (Pi.summable.mp hω k).tsum_mul_right (H ω)
  exact ⟨hw.2.1.congr he, by simpa only [integral_congr_ae he] using hw.2.2⟩

end EligibilityMoments
theorem solution {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ) {N : ℕ} (σ : S → Fin N → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ) (h3 : Assumption3 P π g φ σ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i) :
    ∀ t : ℤ,
      (∀ᵐ ω ∂μ, Summable (fun τ : ℕ => (α * lam) ^ τ • φ (i (t - τ) ω))) ∧
      (∀ k l, Integrable (fun ω => zStat α lam φ i t ω k * φ (i t ω) l) μ) ∧
      HasSum (fun m : ℕ => (α * lam) ^ m • phiDPmPhi P π φ m)
        (fun k l => ∫ ω, zStat α lam φ i t ω k * φ (i t ω) l ∂μ) ∧
      (∀ k l, Integrable (fun ω => zStat α lam φ i t ω k * φ (i (t + 1) ω) l) μ) ∧
      HasSum (fun m : ℕ => (α * lam) ^ m • phiDPmPhi P π φ (m + 1))
        (fun k l => ∫ ω, zStat α lam φ i t ω k * φ (i (t + 1) ω) l ∂μ) ∧
      (∀ k, Integrable (fun ω => zStat α lam φ i t ω k * g (i t ω) (i (t + 1) ω)) μ) ∧
      HasSum (fun m : ℕ => (α * lam) ^ m • phiDPmGbar P π φ g m)
        (fun k => ∫ ω, zStat α lam φ i t ω k * g (i t ω) (i (t + 1) ω) ∂μ) := by
  have hq0 : 0 ≤ α*lam := mul_nonneg hα0.le hlam.1
  have hq1 : α*lam < 1 := lt_of_le_of_lt (by nlinarith [hlam.2]) hα1
  intro t
  have hprod (u : ℤ) (k l : Fin K) := EligibilityMoments.trace_product P π μ i hi
    φ h2.sq_integrable α lam hq0 hq1 t k (fun ω => φ (i u ω) l)
    (((measurable_of_countable (fun x => φ x l)).comp (hi.measurable u)).aestronglyMeasurable)
    (StationaryMoments.square_at P π μ i hi u (fun x => φ x l) (h2.sq_integrable l))
  have hseries (off : ℕ) (k l : Fin K) :
      HasSum (fun m : ℕ => (α*lam)^m * phiDPmPhi P π φ (m+off) k l)
        (∫ ω, zStat α lam φ i t ω k * φ (i (t+off) ω) l ∂μ) := by
    have heq : (fun m : ℕ => (α*lam)^m * ∫ ω, φ (i (t-m) ω) k * φ (i (t+off) ω) l ∂μ) =
        (fun m : ℕ => (α*lam)^m * phiDPmPhi P π φ (m+off) k l) := by
      funext m
      congr 1
      have hh := StationaryMoments.correlation_formula P π μ i hi h1.a (t-m) (m+off)
        (fun x => φ x k) (fun x => φ x l) (h2.sq_integrable k) (h2.sq_integrable l)
      have ht : t-(m : ℤ)+((m+off : ℕ) : ℤ) = t+off := by push_cast; ring
      rw [ht] at hh
      have hcount := integral_countable (StationaryMoments.outer_integrable P π h1.a (m+off)
        (fun x => φ x k) (fun x => φ x l) (h2.sq_integrable k) (h2.sq_integrable l))
      simpa [phiDPmPhi, Measure.real, smul_eq_mul, mul_assoc] using hh.trans hcount
    rw [← heq]
    exact (hprod (t+off) k l).2
  have hgm : Measurable (fun ω => g (i t ω) (i (t+1) ω)) :=
    (measurable_of_countable (fun z : S × S => g z.1 z.2)).comp
      ((hi.measurable t).prodMk (hi.measurable (t+1)))
  have hcost (k : Fin K) := EligibilityMoments.trace_product P π μ i hi
    φ h2.sq_integrable α lam hq0 hq1 t k (fun ω => g (i t ω) (i (t+1) ω))
    hgm.aestronglyMeasurable (EligibilityMoments.cost_square P π μ i hi t g h1.b)
  refine ⟨EligibilityMoments.trace_summable P π μ i hi φ h2.sq_integrable _ hq0 hq1 t,
    fun k l => (hprod t k l).1, ?_, fun k l => (hprod (t+1) k l).1, ?_,
    fun k => (hcost k).1, ?_⟩
  · apply Pi.hasSum.mpr
    intro k
    apply Pi.hasSum.mpr
    intro l
    simpa using hseries 0 k l
  · apply Pi.hasSum.mpr
    intro k
    apply Pi.hasSum.mpr
    intro l
    simpa using hseries 1 k l
  · apply Pi.hasSum.mpr
    intro k
    change HasSum (fun m : ℕ => (α*lam)^m * phiDPmGbar P π φ g m k) _
    have heq : (fun m : ℕ => (α*lam)^m * ∫ ω, φ (i (t-m) ω) k * g (i t ω) (i (t+1) ω) ∂μ) =
        (fun m : ℕ => (α*lam)^m * phiDPmGbar P π φ g m k) := by
      funext m
      congr 1
      have hh := EligibilityMoments.reward_correlation P π μ i hi h1.a g h1.b (t-m) m
        (fun x => φ x k) (h2.sq_integrable k)
      have ht : t-(m : ℤ)+(m : ℤ) = t := by ring
      rw [ht] at hh
      have hcount := integral_countable (StationaryMoments.outer_integrable P π h1.a m
        (fun x => φ x k) (gbar P g) (h2.sq_integrable k)
        (EligibilityMoments.gbar_square P π g h1.a h1.b))
      simpa [phiDPmGbar, Measure.real, smul_eq_mul, mul_assoc] using hh.trans hcount
    rw [← heq]
    exact (hcost k).2

#print axioms solution
