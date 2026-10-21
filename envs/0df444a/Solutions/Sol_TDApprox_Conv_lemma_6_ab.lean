-- Prove2me | solution 1 for TDApprox.Conv.lemma_6_ab
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T18:28:10.843804+00:00
-- url     : https://prove2.me/submissions/dc6fe171-e035-4ed7-bb44-1c87168cf21e

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

theorem solution {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ) {N : ℕ} (σ : S → Fin N → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ) (h3 : Assumption3 P π g φ σ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i) :
    (∀ (t : ℤ) (m : ℕ),
      (∀ k l, Integrable (fun ω => φ (i t ω) k * φ (i (t + m) ω) l) μ) ∧
      (∀ j l, Integrable (fun x => φ x l) ((P ^ m) j)) ∧
      (∀ k l, Summable (fun j => (π {j}).toReal * φ j k * ∫ x, φ x l ∂((P ^ m) j))) ∧
      (fun k l => ∫ ω, φ (i t ω) k * φ (i (t + m) ω) l ∂μ) = phiDPmPhi P π φ m) ∧
    ∃ G : ℝ, ∀ (t : ℤ) (m : ℕ),
      frobNorm (fun k l => ∫ ω, φ (i t ω) k * φ (i (t + m) ω) l ∂μ) ≤ G := by
  constructor
  · intro t m
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k l
      exact StationaryMoments.correlation_integrable P π μ i hi t (t+m)
        (fun x => φ x k) (fun x => φ x l) (h2.sq_integrable k) (h2.sq_integrable l)
    · intro j l
      exact StationaryMoments.pow_row P π h1.a m (fun x => φ x l) (h2.sq_integrable l) j
    · intro k l
      exact StationaryMoments.outer_summable P π h1.a m (fun x => φ x k) (fun x => φ x l)
        (h2.sq_integrable k) (h2.sq_integrable l)
    · ext k l
      change (∫ ω, φ (i t ω) k * φ (i (t+m) ω) l ∂μ) =
        ∑' j, (π {j}).toReal * φ j k * ∫ x, φ x l ∂(P ^ m) j
      rw [StationaryMoments.correlation_formula P π μ i hi h1.a t m
        (fun x => φ x k) (fun x => φ x l) (h2.sq_integrable k) (h2.sq_integrable l)]
      simpa [Measure.real, smul_eq_mul, mul_assoc] using
        integral_countable (StationaryMoments.outer_integrable P π h1.a m
          (fun x => φ x k) (fun x => φ x l) (h2.sq_integrable k) (h2.sq_integrable l))
  · let B : Fin K → Fin K → ℝ := fun k l => (∫ x, φ x k ^ 2 ∂π) + ∫ x, φ x l ^ 2 ∂π
    refine ⟨Real.sqrt (∑ k, ∑ l, B k l ^ 2), ?_⟩
    intro t m
    unfold frobNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro l hl
    have hb := StationaryMoments.correlation_bound P π μ i hi t (t+m)
      (fun x => φ x k) (fun x => φ x l) (h2.sq_integrable k) (h2.sq_integrable l)
    change |∫ ω, φ (i t ω) k * φ (i (t+m) ω) l ∂μ| ≤ B k l at hb
    have hB : 0 ≤ B k l :=
      add_nonneg (integral_nonneg (fun x => sq_nonneg _))
        (integral_nonneg (fun x => sq_nonneg _))
    nlinarith [mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg hB (abs_nonneg (∫ ω, φ (i t ω) k * φ (i (t+m) ω) l ∂μ))),
      sq_abs (∫ ω, φ (i t ω) k * φ (i (t+m) ω) l ∂μ)]

#print axioms solution
