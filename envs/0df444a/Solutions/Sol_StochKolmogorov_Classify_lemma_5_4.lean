-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T00:18:09.23838+00:00
-- url     : https://prove2.me/submissions/30edd57f-fda2-43df-9917-a365674cd756

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula
import Theorems.Thm_EthierKurtz_brownian_ito_integral_locality_and_continuity
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2

set_option linter.all false
set_option Elab.async false

-- ===== ItoM1 =====
section FlatM_ItoM1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

/-- The coordinates of a standard `d`-dimensional Brownian motion form one real Gaussian
process indexed by `time × coordinate`. -/
theorem stdBrownian_isGaussianProcess {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) :
    IsGaussianProcess (fun (p : ℝ≥0 × Fin d) ω => W p.1 ω p.2) P := by
  obtain ⟨_, _, hBM, hind⟩ := hW
  refine ⟨fun I => ?_⟩
  classical
  let I' : Finset ℝ≥0 := I.image Prod.fst
  let V : Fin d → Ω → (I' → ℝ) := fun i ω => fun t => W t ω i
  have hV : ∀ i, HasGaussianLaw (V i) P := fun i =>
    (hBM i).isGaussianProcess.hasGaussianLaw I'
  have hVind : iIndepFun V P :=
    hind.comp (fun _ (f : ℝ≥0 → ℝ) => fun t : I' => f t) (fun _ => by fun_prop)
  have hjoint := hVind.hasGaussianLaw hV
  let L0 : (Fin d → (I' → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x p => x p.1.2 ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have := hjoint.map (LinearMap.toContinuousLinearMap L0)
  have heq : (fun ω => I.restrict (fun p : ℝ≥0 × Fin d => W p.1 ω p.2)) =
      (LinearMap.toContinuousLinearMap L0) ∘ (fun ω x => V x ω) := by
    funext ω p; rfl
  rw [heq]; exact this

/-- The covariance of two coordinates of a standard Brownian motion. -/
theorem stdBrownian_cov {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s t : ℝ≥0) (i j : Fin d) :
    cov[fun ω => W s ω i, fun ω => W t ω j; P] = if i = j then ((min s t : ℝ≥0) : ℝ) else 0 := by
  obtain ⟨hm, _, hBM, hind⟩ := hW
  split_ifs with hij
  · subst hij
    exact (hBM i).covariance_fun_eval s t
  · have h2 : IndepFun (fun ω => W s ω i) (fun ω => W t ω j) P := by
      have := hind.indepFun hij
      exact this.comp (φ := fun f : ℝ≥0 → ℝ => f s) (ψ := fun f : ℝ≥0 → ℝ => f t)
        (by fun_prop) (by fun_prop)
    have hP : IsProbabilityMeasure P := (hBM i).isGaussianProcess.isProbabilityMeasure
    exact h2.covariance_eq_zero ((hBM i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      ((hBM j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem stdBrownian_coord_measurable {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : Measurable (fun ω => W t ω i) := by
  have := hW.1 t
  fun_prop

theorem stdBrownian_memLp_two {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : MemLp (fun ω => W t ω i) 2 P :=
  ((hW.2.2.1 i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

/-- Weak Markov property of a standard `d`-dimensional Brownian motion: all future increments
after `t₀` are independent of the whole past up to `t₀`. -/
theorem stdBrownian_indep_shift {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) :
    IndepFun (fun ω (p : ℝ≥0 × Fin d) => W (t₀ + p.1) ω p.2 - W t₀ ω p.2)
      (fun ω (q : Set.Iic t₀ × Fin d) => W q.1 ω q.2) P := by
  have hG := stdBrownian_isGaussianProcess hW
  have hP : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (X := fun (p : ℝ≥0 × Fin d) ω => W (t₀ + p.1) ω p.2 - W t₀ ω p.2)
    (Y := fun (q : Set.Iic t₀ × Fin d) ω => W q.1 ω q.2)
  · apply hG.of_isGaussianProcess
    rintro (⟨t, i⟩ | ⟨⟨t, ht⟩, i⟩)
    · exact ⟨{(t₀ + t, i), (t₀, i)},
        { toFun x := x ⟨(t₀ + t, i), by simp⟩ - x ⟨(t₀, i), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(t, i)},
        { toFun x := x ⟨(t, i), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro p; exact ((hm (t₀ + p.1) p.2).sub (hm t₀ p.2)).aemeasurable
  · intro q; exact (hm _ _).aemeasurable
  · rintro ⟨s, i⟩ ⟨⟨t, ht⟩, j⟩
    have ht' : t ≤ t₀ := ht
    simp only
    rw [covariance_fun_sub_left (stdBrownian_memLp_two hW _ _) (stdBrownian_memLp_two hW _ _)
      (stdBrownian_memLp_two hW _ _), stdBrownian_cov hW, stdBrownian_cov hW]
    split_ifs
    · rw [min_eq_right (ht'.trans (le_add_right le_rfl)), min_eq_right ht', sub_self]
    · simp

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

/-- The `P`-a.e. closure of a σ-algebra `G`: sets a.e. equal to a `G`-set (null sets taken
for the outer measure, so arbitrary subsets of null sets qualify). -/
@[instance_reducible]
def aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B, MeasurableSet[G] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ G, EventuallyEq.rfl⟩
  measurableSet_compl A := fun ⟨B, hB, h⟩ => ⟨Bᶜ, hB.compl, h.compl⟩
  measurableSet_iUnion f hf := by
    choose B hB h using hf
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, Filter.EventuallyEq.countable_iUnion h⟩

theorem le_aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : G ≤ aeClosure P G :=
  fun A hA => ⟨A, hA, EventuallyEq.rfl⟩

/-- Independence passes to the a.e. closure. -/
theorem indep_aeClosure {P : Measure Ω} {G H : MeasurableSpace Ω} (h : Indep G H P) :
    Indep (aeClosure P G) H P := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨B, hB, hAB⟩ hC
  rw [measure_congr (hAB.inter (EventuallyEq.refl _ C)), measure_congr hAB]
  exact h B C hB hC

end AEC

section CP
variable [MeasurableSpace Ω]

/-- With a constant initial value, the completed Brownian past lies in the a.e. closure of the
natural Brownian past. -/
theorem completedBrownianPast_const_le (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : ℝ≥0) :
    completedBrownianPast P W (fun _ => x₀) s ≤
      aeClosure P (⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance) := by
  set G : MeasurableSpace Ω := ⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance
  refine sup_le (sup_le (le_aeClosure _ _) ?_) ?_
  · rintro A ⟨T, -, rfl⟩
    by_cases hx : x₀ ∈ T
    · refine ⟨Set.univ, @MeasurableSet.univ Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = Set.univ := Set.preimage_const_of_mem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
    · refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = ∅ := Set.preimage_const_of_notMem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨N, -, hN, hAN⟩
    refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
    rw [ae_eq_empty]
    exact measure_mono_null hAN hN

/-- The future increments of a standard Brownian motion after `s` are independent of the
completed Brownian past at `s` (constant initial value). -/
theorem stdBrownian_indep_completedPast {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) :
    Indep (completedBrownianPast P W (fun _ => x₀) s)
      (MeasurableSpace.comap (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2)
        inferInstance) P := by
  refine indep_of_indep_of_le_left (indep_aeClosure ?_) (completedBrownianPast_const_le P W x₀ s)
  have h := ((IndepFun_iff_Indep _ _ _).1 (stdBrownian_indep_shift hW s)).symm
  refine indep_of_indep_of_le_left h ?_
  refine iSup_le fun r => ?_
  have hg : Measurable (fun f : Set.Iic s × Fin d → ℝ =>
      (WithLp.toLp 2 (fun i => f (r, i)) : SDEState d)) := by
    refine (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp ?_
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (r, i))
  have hc : Measurable[MeasurableSpace.comap (fun ω (q : Set.Iic s × Fin d) => W q.1 ω q.2)
      inferInstance] (W r.val) :=
    hg.comp (comap_measurable _)
  exact hc.comap_le

end CP

section M2

theorem nullMeasurable_of_aeClosure {G : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (hG : G ≤ mΩ) {f : Ω → ℝ} (hf : Measurable[aeClosure P G] f) :
    NullMeasurable f P := by
  intro A hA
  obtain ⟨B, hB, h⟩ := hf hA
  exact (hG _ hB).nullMeasurableSet.congr h.symm

variable [MeasurableSpace Ω]

theorem naturalPast_le {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s : ℝ≥0) :
    (⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance) ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun r => (hW.1 r.val).comap_le

/-- A function measurable for the completed Brownian past (constant initial value) is
a.e.-strongly measurable for the ambient σ-algebra. -/
theorem aestronglyMeasurable_of_completedPast {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    AEStronglyMeasurable a P :=
  (nullMeasurable_of_aeClosure (naturalPast_le hW s)
    (ha.mono (completedBrownianPast_const_le P W x₀ s) le_rfl)).aemeasurable.aestronglyMeasurable

/-- A completed-past-measurable function is independent of each later increment. -/
theorem indepFun_completedPast_increment {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    IndepFun a (fun ω => W (s + h) ω j - W s ω j) P := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (stdBrownian_indep_completedPast hW x₀ s) ha.comap_le) ?_
  have hm : Measurable[MeasurableSpace.comap
      (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) inferInstance]
      (fun ω => W (s + h) ω j - W s ω j) := by
    have := (measurable_pi_apply (h, j) : Measurable fun f : ℝ≥0 × Fin d → ℝ => f (h, j)).comp
      (comap_measurable (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2))
    exact this
  exact hm.comap_le

theorem stdBrownian_integral_increment {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    ∫ ω, (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hB := hW.2.2.1 j
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
    hB.integral_eval, sub_self]

theorem stdBrownian_integral_increment_sq {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    ∫ ω, (W (s + h) ω j - W s ω j) ^ 2 ∂P = h := by
  have hB := hW.2.2.1 j
  have hL := hB.hasLaw_sub (s + h) s
  have h1 : ∫ ω, (W (s + h) ω j - W s ω j) ^ 2 ∂P =
      ∫ x, x ^ 2 ∂(gaussianReal 0 (nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))) :=
    hL.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [h1]
  have h2 := variance_fun_id_gaussianReal (μ := (0 : ℝ))
    (v := nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))
  rw [variance_eq_integral (X := fun x : ℝ => x) aemeasurable_id'] at h2
  simp only [integral_id_gaussianReal, sub_zero] at h2
  rw [h2, coe_nndist, Real.dist_eq]
  push_cast
  rw [add_sub_cancel_left]
  exact abs_of_nonneg h.2

end M2

section M3
variable [MeasurableSpace Ω]

theorem completedBrownianPast_mono (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

theorem coord_measurable_completedPast (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {r t : ℝ≥0} (hrt : r ≤ t) (j : Fin d) :
    Measurable[completedBrownianPast P W ξ t] (fun ω => W r ω j) := by
  have h1 : Measurable[MeasurableSpace.comap (W r) inferInstance] (W r) := comap_measurable _
  have h0 : MeasurableSpace.comap (W r) inferInstance ≤
      ⨆ q : Set.Iic t, MeasurableSpace.comap (W q.val) inferInstance :=
    le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r, hrt⟩
  have h2 : MeasurableSpace.comap (W r) inferInstance ≤ completedBrownianPast P W ξ t := by
    unfold completedBrownianPast
    exact le_sup_of_le_left (le_sup_of_le_left h0)
  have h3 : Measurable[completedBrownianPast P W ξ t] (W r) := Measurable.mono h1 h2 le_rfl
  have h4 : Measurable fun x : SDEState d => x j := by fun_prop
  exact h4.comp h3

/-- `E[a · ΔW] = 0` for any completed-past-measurable `a` (no integrability needed). -/
theorem integral_mul_increment_eq_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    ∫ ω, a ω * (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hm := stdBrownian_coord_measurable hW
  rw [(indepFun_completedPast_increment hW x₀ s h j ha).integral_fun_mul_eq_mul_integral
    (aestronglyMeasurable_of_completedPast hW x₀ s ha)
    ((hm _ j).sub (hm _ j)).aestronglyMeasurable, stdBrownian_integral_increment hW, mul_zero]

/-- `E[a² · ΔW²] = E[a²] · h` for any completed-past-measurable `a`. -/
theorem integral_sq_mul_increment_sq {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    ∫ ω, (a ω * (W (s + h) ω j - W s ω j)) ^ 2 ∂P = (∫ ω, a ω ^ 2 ∂P) * h := by
  have hm := stdBrownian_coord_measurable hW
  have hi := (indepFun_completedPast_increment hW x₀ s h j ha).comp
    (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
  have key := hi.integral_fun_mul_eq_mul_integral
    ((aestronglyMeasurable_of_completedPast hW x₀ s ha).pow 2)
    (((hm _ j).sub (hm _ j)).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  simp_rw [mul_pow]
  rw [key, stdBrownian_integral_increment_sq hW]

end M3

section M4
variable [MeasurableSpace Ω]

/-- Discrete Itô isometry for the dyadic step sums of `HasBrownianItoIntegral`: bounded
coefficients measurable for the completed Brownian past at the left endpoints. -/
theorem itoStepSum_isometry {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (n : ℕ) (j : Fin d)
    (a : ℕ → Ω → ℝ)
    (ha : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (a k))
    (C₁ : ℝ) (hC₁ : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |a k ω| ≤ C₁) :
    ∫ ω, (itoStepSum (fun s ω => W s ω j) t n a ω) ^ 2 ∂P =
      ∑ k ∈ Finset.range (2 ^ n), (∫ ω, a k ω ^ 2 ∂P) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  set C : ℝ := max C₁ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |a k ω| ≤ C := fun k hk ω =>
    (hC₁ k hk ω).trans (le_max_left _ _)
  set h : ℝ≥0 := t / (2 : ℝ≥0) ^ n with hh
  let τ : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * t / (2 : ℝ≥0) ^ n
  have hstep : ∀ k : ℕ, ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n = τ k + h := by
    intro k; simp only [τ, hh]; ring
  have hτmono : ∀ l k : ℕ, l ≤ k → τ l ≤ τ k := by
    intro l k hlk; simp only [τ]; gcongr
  have hτsucc : ∀ l k : ℕ, l < k → τ l + h ≤ τ k := by
    intro l k hlk
    rw [← hstep]; simp only [τ]; gcongr
    exact_mod_cast Nat.succ_le_of_lt hlk
  let Δ : ℕ → Ω → ℝ := fun k ω => W (τ k + h) ω j - W (τ k) ω j
  let X : ℕ → Ω → ℝ := fun k ω => a k ω * Δ k ω
  have hsum : ∀ ω, itoStepSum (fun s ω => W s ω j) t n a ω =
      ∑ k ∈ Finset.range (2 ^ n), X k ω := by
    intro ω; unfold itoStepSum
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [X, Δ]; rw [hstep k]
  have hΔL2 : ∀ k, MemLp (Δ k) 2 P := fun k =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have haesm : ∀ k, k < 2 ^ n → AEStronglyMeasurable (a k) P := fun k hk =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (ha k hk)
  have hint : ∀ k, k < 2 ^ n → ∀ l, l < 2 ^ n → Integrable (fun ω => X k ω * X l ω) P := by
    intro k hk l hl
    have hg : Integrable (fun ω => (C * C) * |Δ k ω * Δ l ω|) P :=
      ((hΔL2 k).integrable_mul (hΔL2 l)).abs.const_mul _
    refine hg.mono' (((haesm k hk).mul (hΔL2 k).1).mul ((haesm l hl).mul (hΔL2 l).1)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    calc |X k ω * X l ω| = (|a k ω| * |a l ω|) * |Δ k ω * Δ l ω| := by
          simp only [X, abs_mul]; ring
      _ ≤ (C * C) * |Δ k ω * Δ l ω| :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hC k hk ω) (hC l hl ω) (abs_nonneg _) hC0)
            (abs_nonneg _)
  have off : ∀ l k, l < k → k < 2 ^ n → ∫ ω, X l ω * X k ω ∂P = 0 := by
    intro l k hlk hk
    have hl : l < 2 ^ n := hlk.trans hk
    have hb : Measurable[completedBrownianPast P W (fun _ => x₀) (τ k)]
        (fun ω => a l ω * Δ l ω * a k ω) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (ha k hk)
      · exact (ha l hl).mono (completedBrownianPast_mono P W _ (hτmono l k hlk.le)) le_rfl
      · exact (coord_measurable_completedPast P W _ (hτsucc l k hlk) j).sub
          (coord_measurable_completedPast P W _ (hτmono l k hlk.le) j)
    have := integral_mul_increment_eq_zero hW x₀ (τ k) h j hb
    rw [← this]
    congr 1; funext ω; simp only [X, Δ]; ring
  have hkey : ∀ ω, (itoStepSum (fun s ω => W s ω j) t n a ω) ^ 2 =
      ∑ k ∈ Finset.range (2 ^ n), ∑ l ∈ Finset.range (2 ^ n), X k ω * X l ω := by
    intro ω; rw [hsum ω, sq, Finset.sum_mul_sum]
  simp_rw [hkey]
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _
    (fun l hl => hint k (Finset.mem_range.1 hk) l (Finset.mem_range.1 hl)))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [integral_finsetSum _ (fun l hl => hint k hk' l (Finset.mem_range.1 hl))]
  rw [Finset.sum_eq_single k]
  · calc ∫ ω, X k ω * X k ω ∂P
          = ∫ ω, (a k ω * (W (τ k + h) ω j - W (τ k) ω j)) ^ 2 ∂P := by
            congr 1; funext ω; simp only [X, Δ]; ring
      _ = _ := integral_sq_mul_increment_sq hW x₀ (τ k) h j (ha k hk')
  · intro l hl hlk
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · rw [← off l k hlt hk']
      congr 1; funext ω; ring
    · exact off k l hgt (Finset.mem_range.1 hl)
  · intro hnot; exact absurd hk hnot

end M4

section StopCoef

/-- Coefficients stopped once the running discrete quadratic variation exceeds `δ`. -/
noncomputable def stopCoef (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if (∑ i ∈ Finset.range (k + 1), c i ω ^ 2) * h ≤ δ then c k ω else 0

theorem stopCoef_eq_of_le (c : ℕ → Ω → ℝ) {h δ : ℝ} (hh : 0 ≤ h) {N : ℕ} {ω : Ω}
    (hN : (∑ i ∈ Finset.range N, c i ω ^ 2) * h ≤ δ) {k : ℕ} (hk : k < N) :
    stopCoef c h δ k ω = c k ω := by
  unfold stopCoef
  rw [if_pos]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hh) hN
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hk))
    (fun i _ _ => sq_nonneg _)

theorem stopCoef_sum_le (c : ℕ → Ω → ℝ) {h δ : ℝ} (hh : 0 ≤ h) (hδ : 0 ≤ δ) (N : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range N, stopCoef c h δ k ω ^ 2) * h ≤ δ := by
  induction N with
  | zero => simpa using hδ
  | succ N ih =>
    by_cases hN : (∑ i ∈ Finset.range (N + 1), c i ω ^ 2) * h ≤ δ
    · have : ∑ k ∈ Finset.range (N + 1), stopCoef c h δ k ω ^ 2 =
          ∑ k ∈ Finset.range (N + 1), c k ω ^ 2 :=
        Finset.sum_congr rfl fun k hk => by
          rw [stopCoef_eq_of_le c hh hN (Finset.mem_range.1 hk)]
      rw [this]; exact hN
    · rw [Finset.sum_range_succ]
      have : stopCoef c h δ N ω = 0 := by unfold stopCoef; rw [if_neg hN]
      rw [this]; simpa using ih

theorem abs_stopCoef_le (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ) (ω : Ω) :
    |stopCoef c h δ k ω| ≤ |c k ω| := by
  unfold stopCoef; split_ifs <;> simp

theorem stopCoef_measurable [m : MeasurableSpace Ω] (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ)
    (hc : ∀ i, i ≤ k → Measurable (c i)) : Measurable (stopCoef c h δ k) := by
  unfold stopCoef
  refine Measurable.ite ?_ (hc k le_rfl) measurable_const
  refine measurableSet_le ?_ measurable_const
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun i hi =>
    (hc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).pow_const 2

end StopCoef

section M5
variable [MeasurableSpace Ω]

theorem itoStepSum_memLp {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (n : ℕ) (j : Fin d) (a : ℕ → Ω → ℝ)
    (ha : ∀ k, k < 2 ^ n → AEStronglyMeasurable (a k) P)
    (C : ℝ) (hC : ∀ k, k < 2 ^ n → ∀ ω, |a k ω| ≤ C) :
    MemLp (itoStepSum (fun s ω => W s ω j) t n a) 2 P := by
  have heq : itoStepSum (fun s ω => W s ω j) t n a = ∑ k ∈ Finset.range (2 ^ n),
      fun ω => a k ω * (W (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) ω j -
        W ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) ω j) := by
    funext ω; simp [itoStepSum, Finset.sum_apply]
  rw [heq]
  refine memLp_finsetSum' _ fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hΔ := (stdBrownian_memLp_two hW (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) j).sub
    (stdBrownian_memLp_two hW ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) j)
  refine hΔ.of_le_mul (c := C) ((ha k hk').mul hΔ.1) (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC k hk' ω) (abs_nonneg _)

/-- Localized Chebyshev bound for discrete Ito sums: the sum is large only if the discrete
quadratic variation of the integrand exceeds `δ`, or with probability at most `δ / ε²`. -/
theorem itoStepSum_local_chebyshev {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (n : ℕ) (j : Fin d)
    (c : ℕ → Ω → ℝ)
    (hc : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c k))
    (C : ℝ) (hC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c k ω| ≤ C) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) :
    P {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|} ≤
      ENNReal.ofReal (δ / ε ^ 2) +
      P {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) *
        ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)} := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  set h : ℝ := ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) with hhdef
  have hh : 0 ≤ h := NNReal.coe_nonneg _
  have hsm : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (stopCoef c h δ k) := by
    intro k hk
    exact stopCoef_measurable (m := completedBrownianPast P W (fun _ => x₀) _) c h δ k
      (fun i hi => (hc i (lt_of_le_of_lt hi hk)).mono
        (completedBrownianPast_mono P W _ (by gcongr)) le_rfl)
  have hsC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |stopCoef c h δ k ω| ≤ C := fun k hk ω =>
    (abs_stopCoef_le c h δ k ω).trans (hC k hk ω)
  have hiso := itoStepSum_isometry hW x₀ t n j (stopCoef c h δ) hsm C hsC
  have hL2 := itoStepSum_memLp hW t n j (stopCoef c h δ)
    (fun k hk => aestronglyMeasurable_of_completedPast hW x₀ _ (hsm k hk)) C hsC
  have hint : ∀ k ∈ Finset.range (2 ^ n), Integrable (fun ω => stopCoef c h δ k ω ^ 2) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine Integrable.of_bound
      ((aestronglyMeasurable_of_completedPast hW x₀ _ (hsm k hk')).pow 2) (C ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hsC k hk' ω) 2
  have hE : ∫ ω, (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2 ∂P ≤ δ := by
    rw [hiso]
    calc ∑ k ∈ Finset.range (2 ^ n), (∫ ω, stopCoef c h δ k ω ^ 2 ∂P) * h
        = (∫ ω, ∑ k ∈ Finset.range (2 ^ n), stopCoef c h δ k ω ^ 2 ∂P) * h := by
          rw [integral_finsetSum _ hint, Finset.sum_mul]
      _ = ∫ ω, (∑ k ∈ Finset.range (2 ^ n), stopCoef c h δ k ω ^ 2) * h ∂P := by
          rw [integral_mul_const]
      _ ≤ ∫ _ω, δ ∂P := integral_mono ((integrable_finsetSum _ hint).mul_const h)
          (integrable_const δ) (fun ω => stopCoef_sum_le c hh hδ _ ω)
      _ = δ := by simp
  have hsub : {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|} ⊆
      {ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ∪
      {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h} := by
    intro ω hω
    by_cases hq : (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h ≤ δ
    · left
      have heq : itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω =
          itoStepSum (fun s ω => W s ω j) t n c ω := by
        unfold itoStepSum
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [stopCoef_eq_of_le c hh hq (Finset.mem_range.1 hk)]
      show ε ^ 2 ≤ _
      rw [heq]
      calc ε ^ 2 ≤ |itoStepSum (fun s ω => W s ω j) t n c ω| ^ 2 :=
            pow_le_pow_left₀ hε.le hω 2
        _ = _ := sq_abs _
    · right; exact lt_of_not_ge hq
  have hA : P {ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ≤
      ENNReal.ofReal (δ / ε ^ 2) := by
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun ω => sq_nonneg
        (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω)) hL2.integrable_sq (ε ^ 2)
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hε2, mul_comm]
    exact hm.trans hE
  calc P {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|}
      ≤ P ({ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ∪
          {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add_left hA _

/-- Discrete Ito sums whose integrands have discrete quadratic variation tending to zero in
probability tend to zero in probability. -/
theorem itoStepSum_tendstoInMeasure_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (j : Fin d)
    (c : ℕ → ℕ → Ω → ℝ)
    (hc : ∀ n k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c n k))
    (hC : ∀ n, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C)
    (hq : TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n => itoStepSum (fun s ω => W s ω j) t n (c n)) atTop
      (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hq ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall fun _ => le_top
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have he2top : e / 2 ≠ ⊤ := ENNReal.div_ne_top hetop (by norm_num)
  set δ : ℝ := (e / 2).toReal * ε ^ 2 with hδdef
  have hδpos : 0 < δ := mul_pos (ENNReal.toReal_pos he2.ne' he2top) (by positivity)
  have hδe : ENNReal.ofReal (δ / ε ^ 2) = e / 2 := by
    rw [hδdef, mul_div_cancel_right₀ _ (by positivity), ENNReal.ofReal_toReal he2top]
  have h2 := (ENNReal.tendsto_nhds_zero.1 (hq δ hδpos)) (e / 2) he2
  filter_upwards [h2] with n hn
  obtain ⟨C, hCn⟩ := hC n
  have hset : {ω | ε ≤ dist (itoStepSum (fun s ω => W s ω j) t n (c n) ω) 0} =
      {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n (c n) ω|} := by
    ext ω; simp
  rw [hset]
  calc _ ≤ ENNReal.ofReal (δ / ε ^ 2) +
        P {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
          ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)} :=
        itoStepSum_local_chebyshev hW x₀ t n j (c n) (hc n) C hCn hε hδpos.le
    _ ≤ e / 2 + e / 2 := by
        rw [hδe]
        refine add_le_add le_rfl (le_trans (measure_mono fun ω hω => ?_) hn)
        simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
        exact hω.le.trans (le_abs_self _)
    _ = e := ENNReal.add_halves e

end M5

section M5b

theorem tendstoInMeasure_zero_of_abs_le [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {F A B : ι → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hA : TendstoInMeasure P A l (fun _ => 0)) (hB : TendstoInMeasure P B l (fun _ => 0))
    (hF : ∀ i ω, |F i ω| ≤ K * (|A i ω| + |B i ω|)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hA hB ⊢
  intro ε hε
  have hε' : 0 < ε / (2 * K) := by positivity
  have hsum := (hA _ hε').add (hB _ hε')
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hF i ω
  have h2 : K * (|A i ω| + |B i ω|) < K * (ε / (2 * K) + ε / (2 * K)) :=
    mul_lt_mul_of_pos_left (add_lt_add hcon.1 hcon.2) hK
  have h3 : K * (ε / (2 * K) + ε / (2 * K)) = ε := by field_simp; ring
  linarith

theorem tendstoInMeasure_real_iff_sub [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f : ι → Ω → ℝ} {g : Ω → ℝ} :
    TendstoInMeasure P f l g ↔ TendstoInMeasure P (fun i ω => f i ω - g ω) l (fun _ => 0) := by
  simp only [tendstoInMeasure_iff_dist, Real.dist_eq, sub_zero]

theorem tendstoInMeasure_sub_real [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω - f' i ω) l (fun ω => g ω - g' ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf hf' ⊢
  refine tendstoInMeasure_zero_of_abs_le one_pos hf hf' fun i ω => ?_
  rw [one_mul, abs_le]
  constructor <;> linarith [le_abs_self (f i ω - g ω), neg_abs_le (f i ω - g ω),
    le_abs_self (f' i ω - g' ω), neg_abs_le (f' i ω - g' ω)]

theorem itoStepValue_sub (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n a u ω - itoStepValue t n b u ω =
      itoStepValue t n (fun k ω => a k ω - b k ω) u ω := by
  unfold itoStepValue
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

theorem itoStepSum_sub (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t n a ω - itoStepSum W t n b ω =
      itoStepSum W t n (fun k ω => a k ω - b k ω) ω := by
  unfold itoStepSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]

theorem itoStepValue_sq (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    (itoStepValue t n c u ω) ^ 2 = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key : ∀ p q : ℕ, p < q →
      ((p : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ (q : ℝ) * t.val / (2 : ℝ) ^ n := by
    intro p q hpq
    have : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hT) h2.le
  unfold itoStepValue
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single k]
  · simp only [Set.indicator_apply, Set.mem_Ioc]; split_ifs <;> ring
  · intro l _ hlk
    split_ifs with h1 h2 <;> try ring
    exfalso
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · linarith [key l k hlt, h1.1, h2.2]
    · linarith [key k l hgt, h1.2, h2.1]
  · intro hk'; exact absurd hk hk'

theorem intervalIntegrable_indicator_Ioc_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ioc a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ioc

theorem itoStepValue_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => itoStepValue t n c u ω) volume 0 t.val := by
  have heq : (fun u => itoStepValue t n c u ω) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_eq_sum_indicator]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

theorem itoStepValue_sq_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue t n c u ω) ^ 2) volume 0 t.val := by
  have heq : (fun u => (itoStepValue t n c u ω) ^ 2) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_sq]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

theorem itoStepValue_sq_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω) ^ 2 =
      (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_sq]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

end M5b

section M5c
variable [MeasurableSpace Ω]

/-- The local Ito integral of `HasBrownianItoIntegral` is unique up to null sets at each time,
for integrands with continuous paths. -/
theorem hasBrownianItoIntegral_ae_unique {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J J' : ℝ≥0 → Ω → ℝ}
    (hH : ∀ ω, Continuous (fun u : ℝ => H u.toNNReal ω))
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J')
    (t : ℝ≥0) : J t =ᵐ[P] J' t := by
  obtain ⟨a, ham, haC, haH, haJ⟩ := hJ.2 t
  obtain ⟨b, hbm, hbC, hbH, hbJ⟩ := hJ'.2 t
  have hT : (0 : ℝ) ≤ t.val := t.2
  let c : ℕ → ℕ → Ω → ℝ := fun n k ω => a n k ω - b n k ω
  have hcm : ∀ n k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c n k) := fun n k hk =>
    (ham n k hk).sub (hbm n k hk)
  have hcC : ∀ n, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C := by
    intro n
    obtain ⟨C1, h1⟩ := haC n
    obtain ⟨C2, h2⟩ := hbC n
    refine ⟨C1 + C2, fun k hk ω => ?_⟩
    have h1' := abs_le.1 (h1 k hk ω)
    have h2' := abs_le.1 (h2 k hk ω)
    exact abs_le.2 ⟨by simp only [c]; linarith [h1'.1, h2'.2],
      by simp only [c]; linarith [h1'.2, h2'.1]⟩
  -- integrability of the squared errors
  have hfi : ∀ (n : ℕ) (e : ℕ → Ω → ℝ) ω, IntervalIntegrable
      (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) volume 0 t.val := by
    intro n e ω
    have h1 := itoStepValue_sq_intervalIntegrable t n e ω
    have h2 := (itoStepValue_intervalIntegrable t n e ω).mul_continuousOn (hH ω).continuousOn
    have h3 := ((hH ω).pow 2).intervalIntegrable (μ := volume) 0 t.val
    have h4 := (h1.sub (h2.const_mul 2)).add h3
    have heq : (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) = fun u =>
        (itoStepValue t n e u ω) ^ 2 - 2 * (itoStepValue t n e u ω * H u.toNNReal ω) +
          H u.toNNReal ω ^ 2 := by
      funext u; ring
    rw [heq]; exact h4
  have hq : TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_zero_of_abs_le (K := 2) two_pos haH hbH (fun n ω => ?_)
    rw [← itoStepValue_sq_integral]
    have hfa := hfi n (a n) ω
    have hfb := hfi n (b n) ω
    have hnn : ∀ e : ℕ → Ω → ℝ, 0 ≤ ∫ u in (0 : ℝ)..t.val,
        (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2 :=
      fun e => intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)),
      abs_of_nonneg (hnn (a n)), abs_of_nonneg (hnn (b n))]
    calc ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (c n) u ω) ^ 2
        ≤ ∫ u in (0 : ℝ)..t.val, (2 * (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2 +
            2 * (itoStepValue t n (b n) u ω - H u.toNNReal ω) ^ 2) := by
          refine intervalIntegral.integral_mono_on hT
            (itoStepValue_sq_intervalIntegrable t n (c n) ω)
            ((hfa.const_mul 2).add (hfb.const_mul 2)) (fun u _ => ?_)
          rw [← itoStepValue_sub]
          nlinarith [sq_nonneg (itoStepValue t n (a n) u ω - H u.toNNReal ω +
            (itoStepValue t n (b n) u ω - H u.toNNReal ω))]
      _ = 2 * ((∫ u in (0 : ℝ)..t.val, (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2) +
            ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (b n) u ω - H u.toNNReal ω) ^ 2) := by
          rw [intervalIntegral.integral_add (hfa.const_mul 2) (hfb.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
          ring
  have hS := itoStepSum_tendstoInMeasure_zero hW x₀ t j c hcm hcC hq
  have hsub := tendstoInMeasure_sub_real haJ hbJ
  have hsub' : TendstoInMeasure P (fun n => itoStepSum (fun s ω => W s ω j) t n (c n)) atTop
      (fun ω => J t ω - J' t ω) := by
    convert hsub using 2 with n
    funext ω
    exact (itoStepSum_sub _ t n (a n) (b n) ω).symm
  have hae := tendstoInMeasure_ae_unique hsub' hS
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.1 hω

end M5c

section M6refine

theorem sum_range_mul_block {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N K : ℕ) :
    ∑ j ∈ Finset.range (N * K), f j =
      ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range K, f (k * K + r) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A step sum on the grid of mesh `t / 2^n` is the step sum on the finer grid `t / 2^(n+m)`
with the coefficients held constant on each coarse cell. -/
theorem itoStepSum_refine (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n m : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t n a ω = itoStepSum W t (n + m) (fun k => a (k / 2 ^ m)) ω := by
  unfold itoStepSum
  rw [show (2 : ℕ) ^ (n + m) = 2 ^ n * 2 ^ m from pow_add 2 n m, sum_range_mul_block]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdiv : ∀ r ∈ Finset.range (2 ^ m), (k * 2 ^ m + r) / 2 ^ m = k := by
    intro r hr
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt (Finset.mem_range.1 hr), zero_add]
  set g : ℕ → ℝ := fun r => W (((k * 2 ^ m + r : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m)) ω
    with hg
  have hterm : ∀ r ∈ Finset.range (2 ^ m),
      a ((k * 2 ^ m + r) / 2 ^ m) ω *
        (W ((((k * 2 ^ m + r : ℕ) : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ (n + m)) ω -
          W (((k * 2 ^ m + r : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m)) ω) =
      a k ω * (g (r + 1) - g r) := by
    intro r hr
    have ht : ((k * 2 ^ m + r : ℕ) : ℝ≥0) + 1 = ((k * 2 ^ m + (r + 1) : ℕ) : ℝ≥0) := by
      push_cast; ring
    rw [hdiv r hr, ht]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_range_sub]
  have h1 : ((k * 2 ^ m + 2 ^ m : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m) =
      ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n := by
    push_cast; rw [pow_add]; field_simp; try ring
  have h0 : ((k * 2 ^ m + 0 : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m) =
      (k : ℝ≥0) * t / (2 : ℝ≥0) ^ n := by
    push_cast; rw [pow_add]; field_simp; try ring
  simp only [hg, h1, h0]

end M6refine

section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

/-- Left-point coefficients of a process on the dyadic grid of mesh `t / 2^n`. -/
noncomputable def leftCoef (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  H (dyTime t n k) ω

/-- Oscillation event: two dyadic times in `[0,t]` at distance at most `δ` at which `H` differs
by more than `η`. -/
def oscSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (δ η : ℝ) : Set Ω :=
  ⋃ p : (ℕ × ℕ) × (ℕ × ℕ), {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
    |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
    η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|}

theorem dyTime_le (t : ℝ≥0) {N j : ℕ} (h : j ≤ 2 ^ N) : dyTime t N j ≤ t := by
  unfold dyTime
  rw [div_le_iff₀ (by positivity)]
  calc (j : ℝ≥0) * t ≤ (2 : ℝ≥0) ^ N * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
    _ = t * 2 ^ N := mul_comm _ _

theorem dyTime_coarse (t : ℝ≥0) (n m k : ℕ) :
    dyTime t n (k / 2 ^ m) ≤ dyTime t (n + m) k ∧
    (dyTime t (n + m) k : ℝ) - dyTime t n (k / 2 ^ m) ≤ (t : ℝ) / 2 ^ n := by
  have hk := Nat.div_add_mod k (2 ^ m)
  have hr := Nat.mod_lt k (show 0 < 2 ^ m by positivity)
  set q := k / 2 ^ m
  set r := k % 2 ^ m
  have hkR : (k : ℝ) = 2 ^ m * q + r := by exact_mod_cast hk.symm
  have hrR : (r : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast hr
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have e1 : (dyTime t (n + m) k : ℝ) = (k : ℝ) * t / (2 ^ n * 2 ^ m) := by
    simp [dyTime, pow_add]
  have e2 : (dyTime t n q : ℝ) = (q : ℝ) * t / 2 ^ n := by simp [dyTime]
  have key : (dyTime t (n + m) k : ℝ) - dyTime t n q = (r : ℝ) * t / (2 ^ n * 2 ^ m) := by
    rw [e1, e2, hkR]; field_simp; try ring
  constructor
  · rw [← NNReal.coe_le_coe, ← sub_nonneg, key]; positivity
  · rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right (show (r : ℝ) ≤ 2 ^ m by linarith) ht
    calc (r : ℝ) * t * 2 ^ n ≤ 2 ^ m * t * 2 ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = t * (2 ^ n * 2 ^ m) := by ring

theorem oscSet_mono (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (η : ℝ) :
    oscSet H t δ η ⊆ oscSet H t δ' η := by
  intro ω hω
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
  exact Set.mem_iUnion.2 ⟨p, hp.1, hp.2.1, hp.2.2.1.trans hδ, hp.2.2.2⟩

theorem oscSet_nullMeasurable [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (t : ℝ≥0) (δ η : ℝ) :
    NullMeasurableSet (oscSet H t δ η) P := by
  refine NullMeasurableSet.iUnion fun p => ?_
  by_cases hc : p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
      |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ
  · have heq : {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
        |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
        η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} =
        {ω | η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} := by
      ext ω
      exact ⟨fun h => h.2.2.2, fun h => ⟨hc.1, hc.2.1, hc.2.2, h⟩⟩
    rw [heq]
    exact AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
      (continuous_abs.comp_aestronglyMeasurable ((hHm _).sub (hHm _)))
  · have heq : {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
        |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
        η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} = ∅ := by
      ext ω
      exact ⟨fun h => absurd ⟨h.1, h.2.1, h.2.2.1⟩ hc, fun h => h.elim⟩
    rw [heq]
    exact nullMeasurableSet_empty

theorem iInter_oscSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  have huc : UniformContinuousOn (fun s => H s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hHc ω).continuousOn
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / δ)
  have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have htn : (t : ℝ) / 2 ^ n < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  linarith

theorem oscSet_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => P (oscSet H t ((t : ℝ) / 2 ^ n) η)) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => oscSet H t ((t : ℝ) / 2 ^ n) η) := by
    intro n n' hnn'
    exact oscSet_mono H t (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hnn')) η
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun n => oscSet_nullMeasurable hHm t ((t : ℝ) / 2 ^ n) η) hanti ⟨0, measure_ne_top _ _⟩
  rw [iInter_oscSet_eq_empty hHc t hη, measure_empty] at this
  exact this

end M6osc

section M6cauchy
variable [MeasurableSpace Ω]

/-- L² Cauchy estimate for left-point Ito sums of a bounded adapted process: refining the grid
from `t/2^n` to `t/2^(n+m)` changes the sum by at most `η² t + 4K² t P(osc)` in mean square. -/
theorem leftPoint_cauchy_bound {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ s ω, |H s ω| ≤ K) (t : ℝ≥0) (n m : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    ∫ ω, (itoStepSum (fun s ω => W s ω j) t (n + m) (leftCoef H t (n + m)) ω -
        itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω) ^ 2 ∂P ≤
      η ^ 2 * t + 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  let D : ℕ → Ω → ℝ := fun k ω => leftCoef H t (n + m) k ω - leftCoef H t n (k / 2 ^ m) ω
  have hdiff : ∀ ω, itoStepSum (fun s ω => W s ω j) t (n + m) (leftCoef H t (n + m)) ω -
      itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω =
      itoStepSum (fun s ω => W s ω j) t (n + m) D ω := by
    intro ω
    rw [itoStepSum_refine _ t n m (leftCoef H t n) ω, itoStepSum_sub]
  simp_rw [hdiff]
  have hDm : ∀ k : ℕ, k < 2 ^ (n + m) → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m))] (D k) := by
    intro k _
    exact (hHm (dyTime t (n + m) k)).sub ((hHm (dyTime t n (k / 2 ^ m))).mono
      (completedBrownianPast_mono P W _ (dyTime_coarse t n m k).1) le_rfl)
  have hDb : ∀ k : ℕ, k < 2 ^ (n + m) → ∀ ω, |D k ω| ≤ 2 * K := by
    intro k _ ω
    have h1 := abs_le.1 (hHb (dyTime t (n + m) k) ω)
    have h2 := abs_le.1 (hHb (dyTime t n (k / 2 ^ m)) ω)
    exact abs_le.2 ⟨by simp only [D, leftCoef]; linarith [h1.1, h2.2],
      by simp only [D, leftCoef]; linarith [h1.2, h2.1]⟩
  rw [itoStepSum_isometry hW x₀ t (n + m) j D hDm (2 * K) hDb]
  have hint : ∀ k ∈ Finset.range (2 ^ (n + m)), Integrable (fun ω => D k ω ^ 2) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine Integrable.of_bound
      ((aestronglyMeasurable_of_completedPast hW x₀ _ (hDm k hk')).pow 2) ((2 * K) ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDb k hk' ω) 2
  set h : ℝ := ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ) with hhdef
  have hh : 0 ≤ h := NNReal.coe_nonneg _
  have hNh : ((2 ^ (n + m) : ℕ) : ℝ) * h = t := by
    rw [hhdef]; push_cast; field_simp
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  set O := toMeasurable P (oscSet H t ((t : ℝ) / 2 ^ n) η) with hO
  have hOm : MeasurableSet O := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h ≤
      η ^ 2 * t + 4 * K ^ 2 * t * O.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ O
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have hs : ∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2 ≤
          (Finset.range (2 ^ (n + m))).card • ((2 * K) ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        have := hDb k (Finset.mem_range.1 hk) ω
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      have := mul_le_mul_of_nonneg_right hs hh
      calc (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h
          ≤ ((2 ^ (n + m) : ℕ) : ℝ) * (2 * K) ^ 2 * h := this
        _ = 4 * K ^ 2 * (((2 ^ (n + m) : ℕ) : ℝ) * h) := by ring
        _ = 4 * K ^ 2 * t := by rw [hNh]
        _ ≤ η ^ 2 * t + 4 * K ^ 2 * t := le_add_of_nonneg_left (by positivity)
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hno : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h' => hω (subset_toMeasurable _ _ h')
      have hs : ∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2 ≤
          (Finset.range (2 ^ (n + m))).card • (η ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        have hDk : |D k ω| ≤ η := by
          by_contra hcon
          push Not at hcon
          refine hno (Set.mem_iUnion.2 ⟨((n + m, k), (n, k / 2 ^ m)), hk'.le, ?_, ?_, hcon⟩)
          · show k / 2 ^ m ≤ 2 ^ n
            rw [pow_add] at hk'
            exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hk' |>.le
          · show |(dyTime t (n + m) k : ℝ) - dyTime t n (k / 2 ^ m)| ≤ (t : ℝ) / 2 ^ n
            have hc := dyTime_coarse t n m k
            rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hc.1))]
            exact hc.2
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hDk 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      calc (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h
          ≤ ((2 ^ (n + m) : ℕ) : ℝ) * η ^ 2 * h := mul_le_mul_of_nonneg_right hs hh
        _ = η ^ 2 * (((2 ^ (n + m) : ℕ) : ℝ) * h) := by ring
        _ = η ^ 2 * t := by rw [hNh]
  have hOreal : P.real O = P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
    simp only [measureReal_def, hO, measure_toMeasurable]
  have hIi : Integrable (fun ω => 4 * K ^ 2 * (t : ℝ) * O.indicator 1 ω) P :=
    ((integrable_indicator_iff hOm).2 (integrable_const (1 : ℝ)).integrableOn).const_mul _
  calc ∑ k ∈ Finset.range (2 ^ (n + m)), (∫ ω, D k ω ^ 2 ∂P) * h
      = ∫ ω, (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h ∂P := by
        rw [integral_mul_const, integral_finsetSum _ hint, Finset.sum_mul]
    _ ≤ ∫ ω, (η ^ 2 * t + 4 * K ^ 2 * t * O.indicator 1 ω) ∂P :=
        integral_mono ((integrable_finsetSum _ hint).mul_const h)
          ((integrable_const _).add hIi) hpt
    _ = η ^ 2 * t + 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
        rw [integral_add (integrable_const _) hIi, integral_const, integral_const_mul,
          integral_indicator_one hOm, hOreal]
        simp

end M6cauchy

section M6limit
variable [MeasurableSpace Ω]

theorem dist_toLp_lt_of_integral_sq {P : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) {ε : ℝ} (hε : 0 < ε) (h : ∫ ω, (f ω - g ω) ^ 2 ∂P < ε ^ 2) :
    dist (hf.toLp f) (hg.toLp g) < ε := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp,
    (hf.sub hg).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hA : ∫ ω, ‖(f - g) ω‖ ^ (ENNReal.toReal 2) ∂P = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
    congr 1; funext ω; simp [Real.norm_eq_abs, sq_abs]
  rw [hA]
  have hnn : 0 ≤ ∫ ω, (f ω - g ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  have h2 : (ENNReal.toReal 2)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [h2, ← Real.sqrt_eq_rpow, Real.sqrt_lt' hε]
  exact h

/-- Left-point Ito sums of a bounded adapted process with continuous paths converge in
probability (indeed in `L²`). -/
theorem leftPoint_tendstoInMeasure {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ s ω, |H s ω| ≤ K) (t : ℝ≥0) :
    ∃ J : Ω → ℝ, TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n)) atTop J := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hS : ∀ n, MemLp (itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n)) 2 P := fun n =>
    itoStepSum_memLp hW t n j _
      (fun k _ => aestronglyMeasurable_of_completedPast hW x₀ _ (hHm (dyTime t n k))) K
      (fun k _ ω => hHb _ ω)
  let f : ℕ → Lp ℝ 2 P := fun n => (hS n).toLp _
  have hcau : CauchySeq f := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hε2 : 0 < ε ^ 2 := by positivity
    have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
    set η : ℝ := min 1 (ε ^ 2 / 2 / ((t : ℝ) + 1)) with hηdef
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    have hηt : η ^ 2 * t < ε ^ 2 / 2 := by
      have h1 : η ≤ 1 := min_le_left _ _
      have h2 : η ≤ ε ^ 2 / 2 / ((t : ℝ) + 1) := min_le_right _ _
      have h3 : η ^ 2 ≤ η := by nlinarith
      have h4 : η * ((t : ℝ) + 1) ≤ ε ^ 2 / 2 := by rwa [le_div_iff₀ (by positivity)] at h2
      nlinarith
    have hosc := oscSet_tendsto
      (fun s => aestronglyMeasurable_of_completedPast hW x₀ s (hHm s)) hHc t hηpos
    have hosc' : Tendsto (fun n : ℕ => P.real (oscSet H t ((t : ℝ) / 2 ^ n) η)) atTop
        (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hosc
      simpa [measureReal_def, Function.comp_def] using this
    have hev := hosc'.eventually (gt_mem_nhds
      (show (0 : ℝ) < (ε ^ 2 / 2) / (4 * K ^ 2 * t + 1) by positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine dist_toLp_lt_of_integral_sq (hS _) (hS _) hε ?_
    have hb := leftPoint_cauchy_bound hW x₀ j hHm hK hHb t N m hηpos.le
    have hpN := hN N le_rfl
    have hq : 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ N) η) < ε ^ 2 / 2 := by
      have hc : 0 ≤ 4 * K ^ 2 * (t : ℝ) := by positivity
      have hr : 0 ≤ P.real (oscSet H t ((t : ℝ) / 2 ^ N) η) := measureReal_nonneg
      rw [lt_div_iff₀ (by positivity)] at hpN
      nlinarith
    linarith
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcau
  exact ⟨F, (tendstoInMeasure_of_tendsto_Lp hF).congr_left (fun n => (hS n).coeFn_toLp)⟩

end M6limit

section M6trunc

/-- Truncation of a process at level `R`. -/
noncomputable def clampH (H : ℝ≥0 → Ω → ℝ) (R : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  max (-R) (min (H s ω) R)

theorem abs_clampH_le (H : ℝ≥0 → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (s : ℝ≥0) (ω : Ω) :
    |clampH H R s ω| ≤ R := by
  unfold clampH
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clampH_eq_of_abs_le (H : ℝ≥0 → Ω → ℝ) {R : ℝ} {s : ℝ≥0} {ω : Ω} (h : |H s ω| ≤ R) :
    clampH H R s ω = H s ω := by
  unfold clampH
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem clampH_continuous {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω) (R : ℝ)
    (ω : Ω) : Continuous fun s => clampH H R s ω := by
  unfold clampH
  exact continuous_const.max ((hHc ω).min continuous_const)

theorem clampH_measurable {m : MeasurableSpace Ω} {H : ℝ≥0 → Ω → ℝ} {s : ℝ≥0}
    (h : Measurable[m] (H s)) (R : ℝ) : Measurable[m] (clampH H R s) := by
  unfold clampH
  exact measurable_const.max (h.min measurable_const)

/-- Event that `|H|` exceeds `R` at some dyadic time of `[0,t]`. -/
def bigSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (R : ℝ) : Set Ω :=
  ⋃ p : ℕ × ℕ, {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|}

theorem abs_le_of_not_mem_bigSet {H : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {R : ℝ} {ω : Ω}
    (h : ω ∉ bigSet H t R) {N i : ℕ} (hi : i ≤ 2 ^ N) : |H (dyTime t N i) ω| ≤ R := by
  by_contra hc
  exact h (Set.mem_iUnion.2 ⟨(N, i), hi, lt_of_not_ge hc⟩)

theorem bigSet_nullMeasurable [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (t : ℝ≥0) (R : ℝ) :
    NullMeasurableSet (bigSet H t R) P := by
  refine NullMeasurableSet.iUnion fun p => ?_
  by_cases hc : p.2 ≤ 2 ^ p.1
  · have heq : {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|} =
        {ω | R < |H (dyTime t p.1 p.2) ω|} := by
      ext ω; exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
    rw [heq]
    exact AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
      (continuous_abs.comp_aestronglyMeasurable (hHm _))
  · have heq : {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|} = ∅ := by
      ext ω; exact ⟨fun h => absurd h.1 hc, fun h => h.elim⟩
    rw [heq]
    exact nullMeasurableSet_empty

theorem iInter_bigSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) : (⋂ R : ℕ, bigSet H t R) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hHc ω).continuousOn
  obtain ⟨R, hR⟩ := exists_nat_gt C
  obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.1 (hall R)
  have := hC _ ⟨zero_le, dyTime_le t hp1⟩
  rw [Real.norm_eq_abs] at this
  linarith

theorem bigSet_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) :
    Tendsto (fun R : ℕ => P (bigSet H t R)) atTop (𝓝 0) := by
  have hanti : Antitone (fun R : ℕ => bigSet H t R) := by
    intro R R' hRR' ω hω
    obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.1 hω
    exact Set.mem_iUnion.2 ⟨p, hp1, lt_of_le_of_lt (by exact_mod_cast hRR') hp2⟩
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun R : ℕ => bigSet_nullMeasurable hHm t (R : ℝ)) hanti ⟨0, measure_ne_top _ _⟩
  rw [iInter_bigSet_eq_empty hHc t, measure_empty] at this
  exact this

/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht]; nlinarith [hu.2]
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'

/-- Off the oscillation event of mesh `t/2^n`, `H` at the left grid point `t_k` is within `η` of
`H u` for every `u ∈ [t_k, t_{k+1}]` (dyadic approximation of `u` from the left + continuity). -/
theorem abs_H_sub_le_of_not_mem_oscSet {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n k : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω}
    (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η) (hk : k < 2 ^ n) {u : ℝ} (hu0 : 0 ≤ u)
    (hlo : (k : ℝ) * t.val / 2 ^ n ≤ u) (hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n)
    (hut : u ≤ t.val) :
    |H (dyTime t n k) ω - H u.toNNReal ω| ≤ η := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · have hu : u = 0 := le_antisymm (h0 ▸ hut) hu0
    have hd : dyTime t n k = 0 := by
      have : t = 0 := NNReal.coe_eq_zero.1 h0.symm
      simp [dyTime, this]
    rw [hu, hd, Real.toNNReal_zero, sub_self, abs_zero]
    exact hη
  set y : ℕ → ℝ := fun m => u * 2 ^ (m + n) / t.val with hy
  set s : ℕ → ℝ≥0 := fun m => dyTime t (m + n) ⌊y m⌋₊ with hs
  have hsR : ∀ m, (s m : ℝ) = (⌊y m⌋₊ : ℝ) * t.val / 2 ^ (m + n) := fun m => by
    simp [hs, dyTime]
  have hy0 : ∀ m, 0 ≤ y m := fun m => by simp only [hy]; positivity
  have hyt : ∀ m, y m * t.val / 2 ^ (m + n) = u := fun m => by
    simp only [hy]; field_simp
  have hs_le : ∀ m, (s m : ℝ) ≤ u := fun m => by
    rw [hsR, ← hyt m]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le (hy0 m)) ht)
      (by positivity)
  have hs_gt : ∀ m, u - t.val / 2 ^ (m + n) ≤ (s m : ℝ) := fun m => by
    have h1 := Nat.lt_floor_add_one (y m)
    have h3 : u - t.val / 2 ^ (m + n) = (y m - 1) * t.val / 2 ^ (m + n) := by
      rw [← hyt m]; field_simp; try ring
    rw [hsR, h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      first | linarith [pow_pos (two_pos (α := ℝ)) m] | nlinarith [pow_pos (two_pos (α := ℝ)) m]
    have hfl : ((k * 2 ^ m : ℕ) : ℝ) ≤ (⌊y m⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor hkm
    have e : (dyTime t n k : ℝ) = ((k * 2 ^ m : ℕ) : ℝ) * t.val / 2 ^ (m + n) := by
      simp only [dyTime]; push_cast; rw [pow_add]; field_simp; try rfl
    rw [e, hsR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfl ht) (by positivity)
  have hdk : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by simp [dyTime]
  have hbound : ∀ m, |H (dyTime t n k) ω - H (s m) ω| ≤ η := fun m => by
    by_contra hc
    refine hω (Set.mem_iUnion.2 ⟨((n, k), (m + n, ⌊y m⌋₊)), hk.le, ?_, ?_, lt_of_not_ge hc⟩)
    · refine Nat.floor_le_of_le ?_
      simp only [hy]
      rw [div_le_iff₀ hpos]; push_cast
      exact (mul_le_mul_of_nonneg_right hut (by positivity)).trans_eq (mul_comm _ _)
    · show |(dyTime t n k : ℝ) - (s m : ℝ)| ≤ (t : ℝ) / 2 ^ n
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hs_ge m])]
      have : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by ring
      have := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith
  have hreal : Tendsto (fun m => (s m : ℝ)) atTop (𝓝 u) := by
    have hpow : Tendsto (fun m : ℕ => t.val / 2 ^ (m + n)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))).comp
        (tendsto_add_atTop_nat n)
      exact Tendsto.div_atTop tendsto_const_nhds h
    have hlow : Tendsto (fun m : ℕ => u - t.val / 2 ^ (m + n)) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_gt hs_le
  have hnn : Tendsto s atTop (𝓝 u.toNNReal) := by
    have := (continuous_real_toNNReal.tendsto u).comp hreal
    simpa [Function.comp_def] using this
  have hcont : Continuous fun x : ℝ≥0 => |H (dyTime t n k) ω - H x ω| :=
    (continuous_const.sub (hHc ω)).abs
  exact le_of_tendsto' ((hcont.tendsto u.toNNReal).comp hnn) (fun m => hbound m)

/-- Pathwise approximation: off the oscillation event, a step process with the left-point values
of `H` is uniformly `η`-close to `H` on `(0,t]`, so its integrated squared error is at most
`η² t`. -/
theorem integral_stepValue_sub_sq_le {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω} (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η)
    {c : ℕ → Ω → ℝ} (hc : ∀ k < 2 ^ n, c k ω = H (dyTime t n k) ω) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω - H u.toNNReal ω) ^ 2 ≤ η ^ 2 * t.val := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖(itoStepValue t n c u ω - H u.toNNReal ω) ^ 2‖ ≤ η ^ 2 := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ := itoStepValue_eq_cell t n c hu ω
    rw [hval, hc k hk, Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_H_sub_le_of_not_mem_oscSet hHc t n k hη hω hk hu.1.le hlo.le hhi hu.2) 2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- The approximation clause of `HasBrownianItoIntegral` for the truncated left-point
coefficients `clamp_n (H t_k)` of a continuous process. -/
theorem clampLeft_approx [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) :
    TendstoInMeasure P (fun (n : ℕ) ω => ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (leftCoef (clampH H n) t n) u ω - H u.toNNReal ω) ^ 2)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have ht : (0 : ℝ) ≤ t.val := t.2
  set η : ℝ := min 1 (ε / (2 * (t.val + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hηt : η ^ 2 * t.val < ε := by
    have h1 : η ≤ 1 := min_le_left _ _
    have h2 : η ≤ ε / (2 * (t.val + 1)) := min_le_right _ _
    have h3 : η ^ 2 * t.val ≤ η * t.val := by
      have : η ^ 2 ≤ η := by nlinarith
      exact mul_le_mul_of_nonneg_right this ht
    have h4 : η * t.val ≤ ε / (2 * (t.val + 1)) * t.val := mul_le_mul_of_nonneg_right h2 ht
    have h5 : ε / (2 * (t.val + 1)) * t.val < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hsum := (oscSet_tendsto hHm hHc t hη).add (bigSet_tendsto hHm hHc t)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  have hc : ∀ k < 2 ^ n, leftCoef (clampH H n) t n k ω = H (dyTime t n k) ω := fun k hk =>
    clampH_eq_of_abs_le H (abs_le_of_not_mem_bigSet hcon.2 hk.le)
  have hle := integral_stepValue_sub_sq_le hHc t n hη.le hcon.1 hc
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (leftCoef (clampH H n) t n) u ω - H u.toNNReal ω) ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun u _ => sq_nonneg _)
  rw [abs_of_nonneg hnn] at hω
  linarith

/-- Limits in probability of two sequences that agree on a set `A` agree a.e. on `A`. -/
theorem tendstoInMeasure_ae_eq_on [MeasurableSpace Ω] {P : Measure Ω} {f f' : ℕ → Ω → ℝ}
    {g g' : Ω → ℝ} {A : Set Ω} (hf : TendstoInMeasure P f atTop g)
    (hf' : TendstoInMeasure P f' atTop g') (hA : ∀ n, ∀ ω ∈ A, f n ω = f' n ω) :
    ∀ᵐ ω ∂P, ω ∈ A → g ω = g' ω := by
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_sub_real hf hf').exists_seq_tendsto_ae
  filter_upwards [hns] with ω hω hωA
  have h0 : Tendsto (fun i => f (ns i) ω - f' (ns i) ω) atTop (𝓝 0) := by
    simp only [hA _ ω hωA, sub_self]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hω h0
  linarith

/-- Localization: `f n → J` in probability if, off sets of arbitrarily small measure, `f n`
eventually coincides with a sequence converging to a limit that equals `J` a.e. there. -/
theorem tendstoInMeasure_of_local [MeasurableSpace Ω] {P : Measure Ω} {f : ℕ → Ω → ℝ}
    {J : Ω → ℝ}
    (h : ∀ δ : ℝ≥0∞, 0 < δ → ∃ B : Set Ω, P B ≤ δ ∧ ∃ g : ℕ → Ω → ℝ, ∃ G : Ω → ℝ,
      TendstoInMeasure P g atTop G ∧ (∀ᶠ n in atTop, ∀ ω ∉ B, f n ω = g n ω) ∧
      (∀ᵐ ω ∂P, ω ∉ B → J ω = G ω)) :
    TendstoInMeasure P f atTop J := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨B, hB, g, G, hg, hfg, hJG⟩ := h (δ / 2) hδ2
  rw [tendstoInMeasure_iff_dist] at hg
  have hg' := (ENNReal.tendsto_nhds_zero.1 (hg ε hε)) (δ / 2) hδ2
  rw [ae_iff] at hJG
  filter_upwards [hg', hfg] with n hn hfn
  calc P {ω | ε ≤ dist (f n ω) (J ω)}
      ≤ P (B ∪ {ω | ε ≤ dist (g n ω) (G ω)} ∪ {ω | ¬(ω ∉ B → J ω = G ω)}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωB : ω ∈ B
        · exact Or.inl (Or.inl hωB)
        by_cases hJ : J ω = G ω
        · refine Or.inl (Or.inr ?_)
          simp only [Set.mem_setOf_eq] at hω ⊢
          rwa [← hfn ω hωB, ← hJ]
        · exact Or.inr (fun h => hJ (h hωB))
    _ ≤ P B + P {ω | ε ≤ dist (g n ω) (G ω)} + P {ω | ¬(ω ∉ B → J ω = G ω)} :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 + 0 := by rw [hJG]; gcongr
    _ = δ := by rw [add_zero, ENNReal.add_halves]

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate, in the sense of `HasBrownianItoIntegral` (truncated left-point
sums; localization by truncation `clamp_R H` on the events `{sup |H| ≤ R}`). -/
theorem exists_hasBrownianItoIntegral_clamp {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J ∧ ∀ t, TendstoInMeasure P
        (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop (J t) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  have key : ∀ t : ℝ≥0, ∃ J : Ω → ℝ, TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop J := by
    intro t
    have hJR : ∀ R : ℕ, ∃ JR : Ω → ℝ, TendstoInMeasure P
        (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R) t n)) atTop JR :=
      fun R => leftPoint_tendstoInMeasure hW x₀ j (fun s => clampH_measurable (hHm s) (R : ℝ))
        (clampH_continuous hHc (R : ℝ)) (Nat.cast_nonneg R)
        (abs_clampH_le H (Nat.cast_nonneg R)) t
    choose JR hJR using hJR
    have hagree : ∀ R R' : ℕ, R ≤ R' → ∀ n, ∀ ω ∉ bigSet H t R,
        itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R) t n) ω =
          itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R') t n) ω := by
      intro R R' hRR' n ω hω
      unfold itoStepSum
      refine Finset.sum_congr rfl fun k hk => ?_
      have hb := abs_le_of_not_mem_bigSet hω (N := n) (i := k) (Finset.mem_range.1 hk).le
      have hb' : |H (dyTime t n k) ω| ≤ (R' : ℝ) := hb.trans (by exact_mod_cast hRR')
      simp only [leftCoef, clampH_eq_of_abs_le H hb, clampH_eq_of_abs_le H hb']
    have hae : ∀ᵐ ω ∂P, ∀ R R' : ℕ, R ≤ R' → ω ∉ bigSet H t R → JR R ω = JR R' ω := by
      rw [ae_all_iff]; intro R; rw [ae_all_iff]; intro R'
      by_cases hRR : R ≤ R'
      · filter_upwards [tendstoInMeasure_ae_eq_on (A := (bigSet H t R)ᶜ) (hJR R) (hJR R')
          (fun n ω hω => hagree R R' hRR n ω hω)] with ω hω _ h2 using hω h2
      · exact Eventually.of_forall fun ω h => absurd h hRR
    have hex : ∀ ω, ∃ R : ℕ, ω ∉ bigSet H t R := by
      intro ω
      by_contra hc
      push Not at hc
      have hmem : ω ∈ ⋂ R : ℕ, bigSet H t R := Set.mem_iInter.2 hc
      rw [iInter_bigSet_eq_empty hHc t] at hmem
      exact hmem
    classical
    refine ⟨fun ω => JR (Nat.find (hex ω)) ω, tendstoInMeasure_of_local fun δ hδ => ?_⟩
    obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHae hHc t)) δ hδ).exists
    refine ⟨bigSet H t R, hR, _, JR R, hJR R, ?_, ?_⟩
    · filter_upwards [eventually_ge_atTop R] with n hn ω hω
      exact (hagree R n hn n ω hω).symm
    · filter_upwards [hae] with ω hω hωB
      exact hω _ _ (Nat.find_min' _ hωB) (Nat.find_spec (hex ω))
  choose J hJ using key
  refine ⟨J, ⟨fun t ω => ?_, fun t => ⟨fun n k => leftCoef (clampH H n) t n k, ?_, ?_, ?_, hJ t⟩⟩, hJ⟩
  · exact (((hHc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _
  · intro n k _
    exact clampH_measurable (hHm (dyTime t n k)) (n : ℝ)
  · intro n
    exact ⟨n, fun k _ ω => abs_clampH_le H (Nat.cast_nonneg n) _ ω⟩
  · exact clampLeft_approx hHae hHc t

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate. -/
theorem exists_hasBrownianItoIntegral {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).1 j H hHm hHc
/-- Any Ito integral of a continuous adapted integrand is the limit in probability of the
truncated left-point sums. -/
theorem clampLeft_tendsto_of_hasBrownianItoIntegral {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop (J t) := by
  obtain ⟨J', hJ', hconv⟩ := exists_hasBrownianItoIntegral_clamp hW x₀ j hHm hHc
  exact (hconv t).congr_right (hasBrownianItoIntegral_ae_unique hW x₀ j
    (fun ω => (hHc ω).comp continuous_real_toNNReal) hJ' hJ t)

end M6exist

section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero

section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

theorem tendstoInMeasure_add_real {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω + f' i ω) l (fun ω => g ω + g' ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf hf' ⊢
  refine tendstoInMeasure_zero_of_abs_le one_pos hf hf' fun i ω => ?_
  rw [one_mul]
  calc |f i ω + f' i ω - (g ω + g' ω)| = |(f i ω - g ω) + (f' i ω - g' ω)| := by
        congr 1; ring
    _ ≤ _ := abs_add_le _ _

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

/-- Locality of the Ito integral: integrands agreeing on the dyadic grid of `[0, s]` on an event
give integrals agreeing a.e. on that event at time `s`. -/
theorem hasBrownianItoIntegral_eq_on {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H H' J J' : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s))
    (hH'c : ∀ ω, Continuous fun s => H' s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H' J') (s : ℝ≥0) (E : Set Ω)
    (hE : ∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N → H (dyTime s N i) ω = H' (dyTime s N i) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).1 j H H' J J' hHm hHc hH'm hH'c hJ hJ' s E hE
end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e

section M8f
variable [MeasurableSpace Ω]

end M8f

section M8f2
variable [MeasurableSpace Ω]

theorem itoStepValue_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, itoStepValue t n c u ω =
      (∑ k ∈ Finset.range (2 ^ n), c k ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

/-- M8f: left-point Riemann sums of a pathwise continuous process converge pathwise. -/
theorem riemann_tendsto {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 (∫ u in (0 : ℝ)..t.val, H u.toNNReal ω)) := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (t.val + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hempty := iInter_oscSet_eq_empty hHc t hη
  have hex : ∃ n0 : ℕ, ω ∉ oscSet H t ((t : ℝ) / 2 ^ n0) η := by
    by_contra h
    push_neg at h
    have hmem : ω ∈ (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) := Set.mem_iInter.2 h
    rw [hempty] at hmem
    exact hmem
  obtain ⟨n0, hn0⟩ := hex
  refine ⟨n0, fun n hn => ?_⟩
  have hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h => hn0 (oscSet_mono H t
    (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hn)) η h)
  have hI := itoStepValue_integral t n (fun k ω => H (dyTime t n k) ω) ω
  have hHi : IntervalIntegrable (fun u : ℝ => H u.toNNReal ω) volume 0 t.val :=
    ((hHc ω).comp continuous_real_toNNReal).intervalIntegrable _ _
  rw [Real.dist_eq, ← hI, ← intervalIntegral.integral_sub
    (itoStepValue_intervalIntegrable _ _ _ _) hHi]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖itoStepValue t n (fun k ω => H (dyTime t n k) ω) u ω - H u.toNNReal ω‖ ≤ η := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ :=
      itoStepValue_eq_cell t n (fun k ω => H (dyTime t n k) ω) hu ω
    rw [hval, Real.norm_eq_abs]
    exact abs_H_sub_le_of_not_mem_oscSet hHc t n k hη.le hω hk hu.1.le hlo.le hhi hu.2
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at hle
  refine lt_of_le_of_lt hle ?_
  rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith [mul_nonneg hε.le ht]

end M8f2

section M8f3
variable [MeasurableSpace Ω]

end M8f3

section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g

section M8g2

end M8g2

section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

/-- Coordinates of a linear functional on `SDEState d`. -/
theorem clm_coord (L : SDEState d →L[ℝ] ℝ) (v : SDEState d) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]

theorem clm2_coord (B : SDEState d →L[ℝ] SDEState d →L[ℝ] ℝ) (v w : SDEState d) :
    B v w = ∑ i, ∑ i', v i * w i' *
      B (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) := by
  rw [clm_coord (B v) w]
  have h : ∀ i', B v (EuclideanSpace.single i' 1) =
      ∑ i, v i * B (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) := fun i' =>
    clm_coord (B.flip (EuclideanSpace.single i' 1)) v
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

end M8g4

section M8g5
variable [MeasurableSpace Ω]

/-- M8g5: **Ito's formula** for a `C²` function of a `d`-dimensional Ito process
`X^i = X^i_0 + Σ_j ∫ H^{ij} dW^j + ∫ b^i du` (continuous adapted coefficients). -/
theorem ito_formula {P : Measure Ω} [IsFiniteMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {e : ℕ} {X : ℝ≥0 → Ω → SDEState e}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω)
    (hXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (X s))
    {H J : Fin e → Fin d → ℝ≥0 → Ω → ℝ} {b : Fin e → ℝ≥0 → Ω → ℝ}
    (hHm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H i j s))
    (hHc : ∀ i j ω, Continuous fun s => H i j s ω)
    (hJ : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (H i j) (J i j))
    (hbm : ∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (b i s))
    (hbc : ∀ i ω, Continuous fun s => b i s ω)
    (hX : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin e), X s ω i = X 0 ω i + (∑ j, J i j s ω) +
      ∫ u in (0 : ℝ)..s.val, b i u.toNNReal ω)
    {f : SDEState e → ℝ} (hf : ContDiff ℝ 2 f) {K : Fin e → Fin d → ℝ≥0 → Ω → ℝ}
    (hK : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j)
      (fun s ω => fderiv ℝ f (X s ω) (EuclideanSpace.single i 1) * H i j s ω) (K i j))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂P, f (X t ω) = f (X 0 ω) + (∑ i, ∑ j, K i j t ω) +
      (∑ i, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ f (X u.toNNReal ω) (EuclideanSpace.single i 1) * b i u.toNNReal ω) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ f) (X u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H i j u.toNNReal ω * H i' j u.toNNReal ω := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).2.2 e X hXm hXc hXa H J b hHm hHc hJ hbm hbc hX f hf K hK t
end M8g5

section M9a
variable [MeasurableSpace Ω]

theorem abs_clampH_le_abs (H : ℝ≥0 → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (s : ℝ≥0) (ω : Ω) :
    |clampH H R s ω| ≤ |H s ω| := by
  unfold clampH
  rw [abs_le]
  exact ⟨le_max_of_le_right (le_min (neg_abs_le _) (by linarith [abs_nonneg (H s ω)])),
    max_le (by linarith [abs_nonneg (H s ω)]) ((min_le_left _ _).trans (le_abs_self _))⟩

end M9a

section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem line_hasDerivAt {f : E → ℝ} (hf : Differentiable ℝ f) (u v : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (u + r • v)) (fderiv ℝ f (u + s • v) v) s := by
  have h := (hf (u + s • v)).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const v).const_add u)
  simpa [Function.comp_def] using h

theorem line_hasDerivAt2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u v : E) :
    HasDerivAt (fun r : ℝ => fderiv ℝ f (u + r • v) v) (fderiv ℝ (fderiv ℝ f) u v v) 0 := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hc : ∀ w, HasFDerivAt (fun w => fderiv ℝ f w v) ((fderiv ℝ (fderiv ℝ f) w).flip v) w :=
    fun w => by simpa using (hd w).hasFDerivAt.clm_apply (hasFDerivAt_const v w)
  have h := (hc (u + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ)
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u)
  simpa [Function.comp_def] using h

/-- First directional derivative from an explicit line derivative. -/
theorem fderiv_eq_of_line {f : E → ℝ} (hf : Differentiable ℝ f) (u v : E) {c : ℝ}
    (h1 : HasDerivAt (fun r : ℝ => f (u + r • v)) c 0) : fderiv ℝ f u v = c := by
  have h := line_hasDerivAt hf u v 0
  simp only [zero_smul, add_zero] at h
  exact h.unique h1

/-- Second directional derivative `D²f(u)(v,v)` from explicit line derivatives. -/
theorem fderiv2_eq_of_line {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u v : E) {φ' : ℝ → ℝ} {c : ℝ}
    (h1 : ∀ s, HasDerivAt (fun r : ℝ => f (u + r • v)) (φ' s) s) (h2 : HasDerivAt φ' c 0) :
    fderiv ℝ (fderiv ℝ f) u v v = c := by
  have hdf : Differentiable ℝ f := hf.differentiable two_ne_zero
  have e : (fun r : ℝ => fderiv ℝ f (u + r • v) v) = φ' :=
    funext fun s => (line_hasDerivAt hdf u v s).unique (h1 s)
  have h := line_hasDerivAt2 hf u v
  rw [e] at h
  exact h.unique h2

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

theorem coord_contDiff {e : ℕ} (i : Fin e) {n : ℕ∞} :
    ContDiff ℝ n (fun u : SDEState e => u i) :=
  (EuclideanSpace.proj i : SDEState e →L[ℝ] ℝ).contDiff

end M9cF

section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2

section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

/-- Column `j` of a diffusion matrix. -/
noncomputable def scol (s : SDEDiffusion d) (j : Fin d) : SDEState d :=
  WithLp.toLp 2 (fun k => s (k, j))

end M9d

section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2

section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

theorem measurable_intervalIntegral_of_continuous [MeasurableSpace Ω] (m : MeasurableSpace Ω)
    {H : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (hHm : ∀ s, s ≤ t → Measurable[m] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    Measurable[m] (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω) := by
  refine measurable_of_tendsto_metrizable (f := fun n ω => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) (fun n => ?_)
    (tendsto_pi_nhds.2 fun ω => riemann_tendsto hHc t ω)
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun k hk =>
    hHm _ (dyTime_le t (Finset.mem_range.1 hk).le)

end M9e1

section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2

end ItoLib

end FlatM_ItoM1
-- ===== E =====
section FlatM_E
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10b1
/-! M10b-1: pathwise identification of Ito integrals. For an integrand that is an indefinite
integral in time (`h s = h 0 + ∫₀ˢ D`), left-point sums converge pathwise to the integration by
parts value `h t w t - h 0 w 0 - ∫₀ᵗ w D`; and pathwise limits of left-point sums are Ito
integrals in the sense of `HasBrownianItoIntegral`. -/

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

end M10b2

section M10b2s
/-! M10b-2: the truncated Euler scheme with lagged, linearly interpolated coefficients, driven by a
deterministic path `w`. `eulerZZ k = (Z_{k-1}, Z_k)`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)
  (w : ℝ≥0 → SDEState d)

variable {s₁ b₁ h w}

end M10b2s

section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2w

section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2i

section M10b4a
/-! M10b-4 (a): Ito formula for `Ff r` along `(X, Y, A)` where `X`, `Y` are general Ito
processes (matrix integrands `HX`, `HY`, drifts `bX`, `bY`), `A = ∫ κ(X, Y)`. -/

end M10b4a

section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

end M10b4b

end ItoLib

end FlatM_E
-- ===== F =====
section FlatM_F
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c1
/-! M10c-1: the saturating profile `ψ(Q) = 1 - (1 - st(Q/4)) e^{-Q}` (`ψ(0) = 0`, `ψ = 1` for
`Q ≥ 4`, `ψ(Q) ≥ Q/5` on `[0,4]`) and the test function
`Gf r (x, y, a) = e^{-a} χ_r(|x|²) ψ(|x-y|²)` (cut-off in `x` only). -/

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

end M10c3

end ItoLib

end FlatM_F
-- ===== G =====
section FlatM_G
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

end M10c4

section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5

section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

end FlatM_G
-- ===== H =====
section FlatM_H
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c7
/-! M10c-7: the Euler scheme's coefficient error `‖s₁(Y_u) - H_u‖`, `‖b₁(Y_u) - b_u‖` is
`≤ 2 L K` with `K = d (3 d S δ + 2 S h)` (`δ` = oscillation of `w` over gaps `≤ h` on `[0, T]`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c10

end ItoLib

end FlatM_H
-- ===== I =====
section FlatM_I
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d1
/-! M10d-1 (b5 groundwork): the cell noise `ζ_j = (1/h) ∫₀ʰ (W(s+h) - W(s+u)) du`: measurable for
the future-increment σ-algebra (so independent of the completed past), mean zero, `E ζ² ≤ h/2`. -/

/-- σ-algebra of the Brownian increments after time `s`. -/
def futBrownian [MeasurableSpace Ω] (W : ℝ≥0 → Ω → SDEState d) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) inferInstance

/-- Integrand of the cell noise. -/
noncomputable def zetaF (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (j : Fin d) (u : ℝ) (ω : Ω) : ℝ :=
  W (s + h) ω j - W (s + u.toNNReal) ω j

/-- The cell noise. -/
noncomputable def cellZeta (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (j : Fin d) (ω : Ω) : ℝ :=
  (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h, zetaF W s h j u ω

theorem incr_meas_fut [MeasurableSpace Ω] (W : ℝ≥0 → Ω → SDEState d) (s u : ℝ≥0) (j : Fin d) :
    Measurable[futBrownian W s] fun ω => W (s + u) ω j - W s ω j := by
  have hG : Measurable[futBrownian W s]
      (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) := Measurable.of_comap_le le_rfl
  let _ : MeasurableSpace Ω := futBrownian W s
  exact measurable_pi_iff.1 hG (u, j)

theorem zetaF_continuous {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (s h : ℝ≥0) (j : Fin d) (ω : Ω) : Continuous fun u => zetaF W s h j u ω := by
  unfold zetaF
  have : Continuous fun u : ℝ => W (s + u.toNNReal) ω j :=
    ((EuclideanSpace.proj j).continuous.comp (hWc ω)).comp
      (continuous_const.add continuous_real_toNNReal)
  exact continuous_const.sub this

theorem zeta_meas_fut [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    (hWc : ∀ ω, Continuous fun s => W s ω) (s h : ℝ≥0) (j : Fin d) :
    Measurable[futBrownian W s] (cellZeta W s h j) := by
  have hm : ∀ p : ℝ≥0, p ≤ h → Measurable[futBrownian W s]
      fun ω => W (s + h) ω j - W (s + p) ω j := fun p _ => by
    have e : (fun ω => W (s + h) ω j - W (s + p) ω j) =
        fun ω => (W (s + h) ω j - W s ω j) - (W (s + p) ω j - W s ω j) := by
      funext ω; ring
    rw [e]
    exact (incr_meas_fut W s h j).sub (incr_meas_fut W s p j)
  have hc : ∀ ω, Continuous fun p : ℝ≥0 => W (s + h) ω j - W (s + p) ω j := fun ω =>
    continuous_const.sub (((EuclideanSpace.proj j).continuous.comp (hWc ω)).comp
      (continuous_const.add continuous_id))
  exact (measurable_intervalIntegral_of_continuous (futBrownian W s) h hm hc).const_mul _

theorem indepFun_past_fut [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) {a b : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a)
    (hb : Measurable[futBrownian W s] b) : IndepFun a b P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (stdBrownian_indep_completedPast hW x₀ s) ha.comap_le) hb.comap_le

theorem futBrownian_le [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s : ℝ≥0) : futBrownian W s ≤ ‹MeasurableSpace Ω› := by
  refine MeasurableSpace.comap_le_iff_le_map.2 ?_
  refine (measurable_pi_lambda _ fun p => ?_).le_map
  refine Measurable.sub ?_ ?_ <;> exact stdBrownian_coord_measurable hW _ _

theorem zetaF_moments [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) {u : ℝ} (hu0 : 0 ≤ u) (huh : u ≤ h) :
    ∫ ω, zetaF W s h j u ω ∂P = 0 ∧ ∫ ω, zetaF W s h j u ω ^ 2 ∂P = h - u ∧
      MemLp (zetaF W s h j u) 2 P := by
  have hu' : u.toNNReal ≤ h := Real.toNNReal_le_iff_le_coe.2 huh
  have e : s + h = (s + u.toNNReal) + (h - u.toNNReal) := by
    rw [add_assoc, add_tsub_cancel_of_le hu']
  have hz : zetaF W s h j u = fun ω => W ((s + u.toNNReal) + (h - u.toNNReal)) ω j -
      W (s + u.toNNReal) ω j := by
    funext ω; unfold zetaF; rw [← e]
  rw [hz]
  refine ⟨stdBrownian_integral_increment hW _ _ j, ?_, ?_⟩
  · rw [stdBrownian_integral_increment_sq hW _ _ j, NNReal.coe_sub hu', Real.coe_toNNReal _ hu0]
  · exact (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)

theorem zetaF_measurable_uncurry [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    Measurable (Function.uncurry (zetaF W s h j)) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => zetaF_continuous hW.2.1 s h j ω)
    (fun u => (stdBrownian_coord_measurable hW _ j).sub (stdBrownian_coord_measurable hW _ j))

theorem integrable_restrict_prod [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : ℝ → Ω → ℝ} (hf : Measurable (Function.uncurry f)) {h : ℝ} (hh : 0 ≤ h) {K : ℝ}
    (hb : ∀ u ∈ Set.Ioc (0 : ℝ) h, ∫⁻ ω, ‖f u ω‖ₑ ∂P ≤ ENNReal.ofReal K) :
    Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc 0 h)).prod P) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hf.enorm.aemeasurable]
  calc ∫⁻ u, ∫⁻ ω, ‖Function.uncurry f (u, ω)‖ₑ ∂P ∂(volume.restrict (Set.uIoc 0 h))
      ≤ ∫⁻ _u, ENNReal.ofReal K ∂(volume.restrict (Set.uIoc 0 h)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_uIoc).2
          (Eventually.of_forall fun u hu => ?_))
        rw [Set.uIoc_of_le hh] at hu
        exact hb u hu
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by rw [Set.uIoc_of_le hh]; exact measure_Ioc_lt_top)

theorem lintegral_ofReal_sq_eq [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ} (hg : MemLp g 2 P) :
    ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P = ENNReal.ofReal (∫ ω, g ω ^ 2 ∂P) :=
  (ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Eventually.of_forall fun ω => sq_nonneg (g ω))).symm

theorem sq_intervalIntegral_le {F : ℝ → ℝ} (hF : Continuous F) {h : ℝ} (hh : 0 < h) :
    (∫ u in (0 : ℝ)..h, F u) ^ 2 ≤ h * ∫ u in (0 : ℝ)..h, F u ^ 2 := by
  set I := ∫ u in (0 : ℝ)..h, F u
  set J := ∫ u in (0 : ℝ)..h, F u ^ 2
  set m := I / h with hm
  have hmI : m * h = I := by rw [hm]; field_simp
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..h, (F u - m) ^ 2 :=
    intervalIntegral.integral_nonneg hh.le fun u _ => sq_nonneg _
  have e : ∫ u in (0 : ℝ)..h, (F u - m) ^ 2 = J - 2 * m * I + m ^ 2 * h := by
    have : (fun u => (F u - m) ^ 2) = fun u => F u ^ 2 - 2 * m * F u + m ^ 2 := by
      funext u; ring
    have i1 : IntervalIntegrable (fun u => F u ^ 2 - 2 * m * F u) volume 0 h :=
      ((hF.pow 2).sub (continuous_const.mul hF)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => F u ^ 2) volume 0 h := (hF.pow 2).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u => 2 * m * F u) volume 0 h :=
      (continuous_const.mul hF).intervalIntegrable _ _
    rw [this, intervalIntegral.integral_add i1 intervalIntegrable_const,
      intervalIntegral.integral_sub i2 i3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have hm2 : m ^ 2 * h = m * I := by rw [← hmI]; ring
  have h1 : 0 ≤ J - m * I := by linarith
  nlinarith [mul_nonneg hh.le h1]

theorem cellZeta_moments [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (s h : ℝ≥0) (hh : 0 < (h : ℝ))
    (j : Fin d) :
    ∫ ω, cellZeta W s h j ω ∂P = 0 ∧ MemLp (cellZeta W s h j) 2 P ∧
      ∫ ω, cellZeta W s h j ω ^ 2 ∂P ≤ h / 2 := by
  have hmeas := zetaF_measurable_uncurry hW s h j
  have hmom := fun u (hu : u ∈ Set.Ioc (0 : ℝ) h) => zetaF_moments hW s h j (P := P) hu.1.le hu.2
  -- integrability of `zetaF` and `zetaF²` on the product
  have hI1 : Integrable (Function.uncurry (zetaF W s h j))
      ((volume.restrict (Set.uIoc 0 (h : ℝ))).prod P) := by
    refine integrable_restrict_prod hmeas h.2 (K := h + 1) fun u hu => ?_
    obtain ⟨-, h2, hL⟩ := hmom u hu
    calc ∫⁻ ω, ‖zetaF W s h j u ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (zetaF W s h j u ω ^ 2 + 1) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ofReal_norm, Real.norm_eq_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [abs_nonneg (zetaF W s h j u ω), sq_abs (zetaF W s h j u ω)]
      _ = ENNReal.ofReal (h - u + 1) := by
          have hint : Integrable (fun ω => zetaF W s h j u ω ^ 2 + 1) P :=
            hL.integrable_sq.add (integrable_const 1)
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun ω => by positivity), integral_add hL.integrable_sq
            (integrable_const 1), h2]
          simp
      _ ≤ ENNReal.ofReal (h + 1) := ENNReal.ofReal_le_ofReal (by linarith [hu.1])
  have hI2 : Integrable (Function.uncurry fun u ω => zetaF W s h j u ω ^ 2)
      ((volume.restrict (Set.uIoc 0 (h : ℝ))).prod P) := by
    refine integrable_restrict_prod (hmeas.pow_const 2) h.2 (K := h) fun u hu => ?_
    obtain ⟨-, h2, hL⟩ := hmom u hu
    calc ∫⁻ ω, ‖zetaF W s h j u ω ^ 2‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (zetaF W s h j u ω ^ 2) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ = ENNReal.ofReal (h - u) := by rw [lintegral_ofReal_sq_eq hL, h2]
      _ ≤ ENNReal.ofReal h := ENNReal.ofReal_le_ofReal (by linarith [hu.1])
  have hsw1 := intervalIntegral_integral_swap hI1
  have hsw2 := intervalIntegral_integral_swap hI2
  -- mean zero
  have hmean : ∫ ω, (∫ u in (0 : ℝ)..h, zetaF W s h j u ω) ∂P = 0 := by
    rw [← hsw1]
    refine (intervalIntegral.integral_congr_ae ?_).trans intervalIntegral.integral_zero
    refine Eventually.of_forall fun u hu => ?_
    rw [Set.uIoc_of_le (NNReal.coe_nonneg h)] at hu
    exact (hmom u hu).1
  -- second moment of the integral
  have hsq : ∫ ω, (∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) ∂P = (h : ℝ) ^ 2 / 2 := by
    rw [← hsw2]
    have : ∫ u in (0 : ℝ)..h, ∫ ω, zetaF W s h j u ω ^ 2 ∂P = ∫ u in (0 : ℝ)..h, ((h : ℝ) - u) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
      rw [Set.uIoc_of_le (NNReal.coe_nonneg h)] at hu
      exact (hmom u hu).2.1
    rw [this, intervalIntegral.integral_sub (f := fun _ => (h : ℝ)) (g := fun u => u) intervalIntegrable_const
      (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id]
    simp; ring
  have hJi : Integrable (fun ω => ∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) P := by
    have := hI2.integral_prod_right
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg h), Set.uIoc_of_le (NNReal.coe_nonneg h)]
  have hZm : AEStronglyMeasurable (cellZeta W s h j) P :=
    ((zeta_meas_fut hW.2.1 s h j).mono (futBrownian_le hW s) le_rfl).aestronglyMeasurable
  have hpt : ∀ ω, cellZeta W s h j ω ^ 2 ≤
      (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2 := fun ω => by
    have hc := sq_intervalIntegral_le (zetaF_continuous hW.2.1 s h j ω) hh
    unfold cellZeta
    rw [mul_pow]
    calc (1 / (h : ℝ)) ^ 2 * (∫ u in (0 : ℝ)..h, zetaF W s h j u ω) ^ 2
        ≤ (1 / (h : ℝ)) ^ 2 * ((h : ℝ) * ∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by field_simp
  have hL2 : MemLp (cellZeta W s h j) 2 P := by
    refine (memLp_two_iff_integrable_sq hZm).2 ?_
    refine (hJi.const_mul (1 / (h : ℝ))).mono' (hZm.pow 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨?_, hL2, ?_⟩
  · unfold cellZeta
    rw [integral_const_mul, hmean, mul_zero]
  · calc ∫ ω, cellZeta W s h j ω ^ 2 ∂P ≤ ∫ ω, (1 / (h : ℝ)) *
          (∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) ∂P :=
          integral_mono hL2.integrable_sq (hJi.const_mul _) hpt
      _ = (h : ℝ) / 2 := by rw [integral_const_mul, hsq]; field_simp

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

/-- The cell noise vector. -/
noncomputable def cellNoise (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (A B : Ω → SDEDiffusion d)
    (ω : Ω) : SDEState d :=
  WithLp.toLp 2 fun i => ∑ j, (A ω (i, j) * (W (s + h) ω j - W s ω j) +
    B ω (i, j) * cellZeta W s h j ω)

theorem state_norm_sq (x : SDEState d) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem diff_norm_sq (A : SDEDiffusion d) : ‖A‖ ^ 2 = ∑ i, ∑ j, A (i, j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.univ_product_univ, Finset.sum_product]
  simp [Real.norm_eq_abs, sq_abs]

theorem cellNoise_pt (D : SDEState d) (a b : Fin d → Fin d → ℝ) (ξ ζ : Fin d → ℝ) :
    ‖D + WithLp.toLp 2 (fun i => ∑ j, (a i j * ξ j + b i j * ζ j))‖ ^ 2 ≤
      ‖D‖ ^ 2 + 2 * ∑ i, ∑ j, (D i * a i j * ξ j + D i * b i j * ζ j) +
        2 * d * ∑ i, ∑ j, (a i j ^ 2 * ξ j ^ 2 + b i j ^ 2 * ζ j ^ 2) := by
  rw [state_norm_sq, state_norm_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hN : (∑ j, (a i j * ξ j + b i j * ζ j)) ^ 2 ≤ d * ∑ j, 2 * (a i j ^ 2 * ξ j ^ 2 + b i j ^ 2 * ζ j ^ 2) := by
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg _)
    nlinarith [sq_nonneg (a i j * ξ j - b i j * ζ j)]
  have e : (D + WithLp.toLp 2 (fun i => ∑ j, (a i j * ξ j + b i j * ζ j))) i =
      D i + ∑ j, (a i j * ξ j + b i j * ζ j) := rfl
  rw [e, ← Finset.mul_sum] at *
  have e2 : ∑ j, (D i * a i j * ξ j + D i * b i j * ζ j) = D i * ∑ j, (a i j * ξ j + b i j * ζ j) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  rw [e2]
  first | linarith [hN] | nlinarith [hN]

set_option maxHeartbeats 1000000 in
theorem cellNoise_step [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) {D : Ω → SDEState d} {A B : Ω → SDEDiffusion d} {K : ℝ}
    (hD : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => D ω i)
    (hDL : ∀ i, MemLp (fun ω => D ω i) 2 P)
    (hA : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => A ω p)
    (hB : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => B ω p)
    (hAK : ∀ ω, ‖A ω‖ ≤ K) (hBK : ∀ ω, ‖B ω‖ ≤ K) :
    ∫ ω, ‖D ω + cellNoise W s h A B ω‖ ^ 2 ∂P ≤
      ∫ ω, ‖D ω‖ ^ 2 ∂P + 2 * d * h * ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P := by
  set ξ : Fin d → Ω → ℝ := fun j ω => W (s + h) ω j - W s ω j with hξ
  set ζ : Fin d → Ω → ℝ := fun j ω => cellZeta W s h j ω with hζ
  have hK : ∀ ω, 0 ≤ K := fun ω => (norm_nonneg _).trans (hAK ω)
  have hm := stdBrownian_coord_measurable hW
  have hξL : ∀ j, MemLp (ξ j) 2 P := fun j =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have hζm := fun j => cellZeta_moments (P := P) hW s h hh j
  have hasm : ∀ {a : Ω → ℝ}, Measurable[completedBrownianPast P W (fun _ => x₀) s] a →
      AEStronglyMeasurable a P :=
    fun ha => aestronglyMeasurable_of_completedPast hW x₀ s ha
  have hζas : ∀ j, AEStronglyMeasurable (ζ j) P := fun j =>
    ((zeta_meas_fut hW.2.1 s h j).mono (futBrownian_le hW s) le_rfl).aestronglyMeasurable
  have hAb : ∀ ω p, |A ω p| ≤ K := fun ω p => by
    have := PiLp.norm_apply_le (A ω) p; rw [Real.norm_eq_abs] at this; exact this.trans (hAK ω)
  have hBb : ∀ ω p, |B ω p| ≤ K := fun ω p => by
    have := PiLp.norm_apply_le (B ω) p; rw [Real.norm_eq_abs] at this; exact this.trans (hBK ω)
  -- integrability of the pieces
  have aA : ∀ p, AEStronglyMeasurable (fun ω => A ω p) P := fun p => hasm (hA p)
  have aB : ∀ p, AEStronglyMeasurable (fun ω => B ω p) P := fun p => hasm (hB p)
  have iDA : ∀ i j, Integrable (fun ω => D ω i * A ω (i, j)) P := fun i j =>
    (((hDL i).integrable one_le_two).norm.const_mul K).mono' (((hDL i).1).mul (aA _))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm K]
        exact mul_le_mul_of_nonneg_left (hAb ω _) (abs_nonneg _))
  have iDB : ∀ i j, Integrable (fun ω => D ω i * B ω (i, j)) P := fun i j =>
    (((hDL i).integrable one_le_two).norm.const_mul K).mono' (((hDL i).1).mul (aB _))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm K]
        exact mul_le_mul_of_nonneg_left (hBb ω _) (abs_nonneg _))
  have indA : ∀ i j, IndepFun (fun ω => D ω i * A ω (i, j)) (ξ j) P := fun i j =>
    indepFun_completedPast_increment hW x₀ s h j ((hD i).mul (hA _))
  have indB : ∀ i j, IndepFun (fun ω => D ω i * B ω (i, j)) (ζ j) P := fun i j =>
    indepFun_past_fut hW x₀ s ((hD i).mul (hB _)) (zeta_meas_fut hW.2.1 s h j)
  have i1 : ∀ i j, Integrable (fun ω => D ω i * A ω (i, j) * ξ j ω) P := fun i j =>
    (indA i j).integrable_mul (iDA i j) ((hξL j).integrable one_le_two)
  have i2 : ∀ i j, Integrable (fun ω => D ω i * B ω (i, j) * ζ j ω) P := fun i j =>
    (indB i j).integrable_mul (iDB i j) ((hζm j).2.1.integrable one_le_two)
  have hsqK : ∀ x : ℝ, |x| ≤ K → x ^ 2 ≤ K ^ 2 := fun x hx => by
    nlinarith [abs_nonneg x, sq_abs x]
  have i3 : ∀ i j, Integrable (fun ω => A ω (i, j) ^ 2 * ξ j ω ^ 2) P := fun i j =>
    ((hξL j).integrable_sq.const_mul (K ^ 2)).mono' (((aA _).pow 2).mul ((hξL j).1.pow 2))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (hsqK _ (hAb ω _)) (sq_nonneg _))
  have i4 : ∀ i j, Integrable (fun ω => B ω (i, j) ^ 2 * ζ j ω ^ 2) P := fun i j =>
    ((hζm j).2.1.integrable_sq.const_mul (K ^ 2)).mono' (((aB _).pow 2).mul ((hζas j).pow 2))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (hsqK _ (hBb ω _)) (sq_nonneg _))
  have iA2 : ∀ p, Integrable (fun ω => A ω p ^ 2) P := fun p =>
    (integrable_const (K ^ 2)).mono' ((aA p).pow 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsqK _ (hAb ω p))
  have iB2 : ∀ p, Integrable (fun ω => B ω p ^ 2) P := fun p =>
    (integrable_const (K ^ 2)).mono' ((aB p).pow 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsqK _ (hBb ω p))
  -- values
  have v1 : ∀ i j, ∫ ω, D ω i * A ω (i, j) * ξ j ω ∂P = 0 := fun i j =>
    integral_mul_increment_eq_zero hW x₀ s h j ((hD i).mul (hA _))
  have v2 : ∀ i j, ∫ ω, D ω i * B ω (i, j) * ζ j ω ∂P = 0 := fun i j => by
    rw [(indB i j).integral_fun_mul_eq_mul_integral (iDB i j).1 (hζas j), (hζm j).1, mul_zero]
  have v3 : ∀ i j, ∫ ω, A ω (i, j) ^ 2 * ξ j ω ^ 2 ∂P = (∫ ω, A ω (i, j) ^ 2 ∂P) * h := fun i j => by
    have := integral_sq_mul_increment_sq hW x₀ s h j (hA (i, j))
    simp only [mul_pow] at this
    exact this
  have v4 : ∀ i j, ∫ ω, B ω (i, j) ^ 2 * ζ j ω ^ 2 ∂P ≤ (∫ ω, B ω (i, j) ^ 2 ∂P) * h := fun i j => by
    have hi := indepFun_past_fut hW x₀ s ((hB (i, j)).pow_const 2)
      ((zeta_meas_fut hW.2.1 s h j).pow_const 2)
    rw [hi.integral_fun_mul_eq_mul_integral ((aB _).pow 2) ((hζas j).pow 2)]
    refine mul_le_mul_of_nonneg_left ((hζm j).2.2.trans (by linarith)) ?_
    exact integral_nonneg fun ω => sq_nonneg _
  have i12 : ∀ i j, Integrable (fun ω => D ω i * A ω (i, j) * ξ j ω +
      D ω i * B ω (i, j) * ζ j ω) P := fun i j => (i1 i j).add (i2 i j)
  have i34 : ∀ i j, Integrable (fun ω => A ω (i, j) ^ 2 * ξ j ω ^ 2 +
      B ω (i, j) ^ 2 * ζ j ω ^ 2) P := fun i j => (i3 i j).add (i4 i j)
  have iAB : ∀ i j, Integrable (fun ω => A ω (i, j) ^ 2 + B ω (i, j) ^ 2) P := fun i j =>
    (iA2 _).add (iB2 _)
  -- the pointwise bound, integrated
  set S1 : Ω → ℝ := fun ω => ∑ i, ∑ j, (D ω i * A ω (i, j) * ξ j ω +
      D ω i * B ω (i, j) * ζ j ω) with hS1d
  set S2 : Ω → ℝ := fun ω => ∑ i, ∑ j, (A ω (i, j) ^ 2 * ξ j ω ^ 2 + B ω (i, j) ^ 2 * ζ j ω ^ 2)
    with hS2d
  set T : Ω → ℝ := fun ω => ‖D ω‖ ^ 2 + 2 * S1 ω + 2 * d * S2 ω with hT
  have hpt : ∀ ω, ‖D ω + cellNoise W s h A B ω‖ ^ 2 ≤ T ω := fun ω =>
    cellNoise_pt (D ω) (fun i j => A ω (i, j)) (fun i j => B ω (i, j)) (fun j => ξ j ω)
      (fun j => ζ j ω)
  have iD2 : Integrable (fun ω => ‖D ω‖ ^ 2) P := by
    have : (fun ω => ‖D ω‖ ^ 2) = fun ω => ∑ i, D ω i ^ 2 := funext fun ω => state_norm_sq _
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hDL i).integrable_sq
  have iS1 : Integrable S1 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i12 i j
  have iS2 : Integrable S2 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i34 i j
  have iT : Integrable T P := (iD2.add (iS1.const_mul 2)).add (iS2.const_mul _)
  have hS1 : ∫ ω, S1 ω ∂P = 0 := by
    simp only [hS1d]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i12 i j]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => i12 i j]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_add (i1 i j) (i2 i j), v1, v2, add_zero]
  have hS2 : ∫ ω, S2 ω ∂P = ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 * ξ j ω ^ 2 ∂P +
      ∫ ω, B ω (i, j) ^ 2 * ζ j ω ^ 2 ∂P) := by
    simp only [hS2d]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i34 i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => i34 i j]
    exact Finset.sum_congr rfl fun j _ => integral_add (i3 i j) (i4 i j)
  have hIT : ∫ ω, T ω ∂P = ∫ ω, ‖D ω‖ ^ 2 ∂P + 2 * ∫ ω, S1 ω ∂P + 2 * d * ∫ ω, S2 ω ∂P := by
    have e : T = (fun ω => ‖D ω‖ ^ 2) + (fun ω => 2 * S1 ω) + (fun ω => 2 * d * S2 ω) := rfl
    rw [e, integral_add' (iD2.add (iS1.const_mul 2)) (iS2.const_mul _),
      integral_add' iD2 (iS1.const_mul 2)]
    rw [integral_const_mul, integral_const_mul]
  have hAB : ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P =
      ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 ∂P + ∫ ω, B ω (i, j) ^ 2 ∂P) := by
    have : (fun ω => ‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) =
        fun ω => ∑ i, ∑ j, (A ω (i, j) ^ 2 + B ω (i, j) ^ 2) := funext fun ω => by
      rw [diff_norm_sq, diff_norm_sq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]
    rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAB i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => iAB i j]
    exact Finset.sum_congr rfl fun j _ => integral_add (iA2 _) (iB2 _)
  calc ∫ ω, ‖D ω + cellNoise W s h A B ω‖ ^ 2 ∂P ≤ ∫ ω, T ω ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) iT
          (Eventually.of_forall hpt)
    _ ≤ ∫ ω, ‖D ω‖ ^ 2 ∂P + 2 * d * h * ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P := by
        have key : ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 * ξ j ω ^ 2 ∂P +
            ∫ ω, B ω (i, j) ^ 2 * ζ j ω ^ 2 ∂P) ≤
            (h : ℝ) * ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 ∂P + ∫ ω, B ω (i, j) ^ 2 ∂P) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [v3]
          first | linarith [v4 i j] | nlinarith [v4 i j]
        rw [hIT, hS1, hS2, hAB, mul_zero, add_zero]
        have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * d)
        first | linarith [this] | nlinarith [this]

end M10d2

end ItoLib

end FlatM_I
-- ===== J =====
section FlatM_J
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d3
/-! M10d-3 (b5): one full cell of the Euler scheme in cell-noise form, and L² of the grid values. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

/-- A bounded, a.e.-strongly measurable factor keeps a real function in `L²`. -/
theorem memLp_two_bdd_mul [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {φ f : Ω → ℝ}
    {K : ℝ} (hφ : AEStronglyMeasurable φ P) (hK : ∀ ω, |φ ω| ≤ K) (hf : MemLp f 2 P) :
    MemLp (fun ω => φ ω * f ω) 2 P :=
  hf.mul' (p := ∞) (MemLp.of_bound hφ K (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hK ω))

theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

theorem coord_abs_le_diff (A : SDEDiffusion d) (p : Fin d × Fin d) : |A p| ≤ ‖A‖ := by
  have := PiLp.norm_apply_le A p; rwa [Real.norm_eq_abs] at this

theorem integrable_norm_sq_of_coords [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → SDEState d}
    (hf : ∀ i, MemLp (fun ω => f ω i) 2 P) : Integrable (fun ω => ‖f ω‖ ^ 2) P := by
  simp_rw [state_norm_sq]
  exact integrable_finsetSum _ fun i _ => (hf i).integrable_sq

end M10d3

end ItoLib

end FlatM_J
-- ===== K =====
section FlatM_K
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e1
/-! M10e-1 (b6 groundwork): the scheme as a deterministic recursion `zrec` driven by the cell
noises `(ξ_l, ζ_l)`; restart identity `Z_{m+k} = zrec_k(Z_{m-1}, Z_m; noises of cells m, m+1, ...)`;
the noises after cell `m` are measurable for the future-increment σ-algebra. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable {s₁ b₁ h}

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e2

end ItoLib

end FlatM_K
-- ===== L =====
section FlatM_L
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e3
/-! M10e-3 (b6): time homogeneity. The restarted Brownian motion is standard; the noises after
cell `m` are the noises of the restarted motion; any two standard Brownian motions have the same
finite-dimensional laws. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e4

end ItoLib

end FlatM_L
-- ===== CB =====
section FlatM_CB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

end FlatM_CB
-- ===== CC =====
section FlatM_CC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C2b
/-! CORE route C2b (s23): one-cell Cameron-Martin for the cell noise `(ξ, ζ)` with a constant shift:
weighting by `cmwPi h u ξ` and shifting `(ξ, ζ) ↦ (ξ + u, ζ + u/2)` preserves the law.
Route: dyadic increments are i.i.d. `N(0, h/2^n)` (`dInc_law`), the dyadic approximation of the
noise is a linear function `psiN` of them (`apx_eq_psiN`), finite-dimensional Cameron-Martin
(`gauss_pi_shift`) at each level, then the limit `n → ∞`. -/

end C2b

end ItoLib

end FlatM_CC
-- ===== CD =====
section FlatM_CD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C3
/-! CORE route C3 (s23): adapted discrete Girsanov over the cells. The first `k` cell noises have
law `ν_k = ν_{k-1} ⊗ ν_1` (independence of the past and time homogeneity); shifting cell `l` by
`(u_l, u_l/2)` with `u_l` a measurable function of the earlier noises and weighting by
`∏ cmwPi h u_l ξ_l` preserves `ν_k` (`girsanov_cells`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end C3

end ItoLib

end FlatM_CD
-- ===== CE =====
section FlatM_CE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {d : ℕ}

section C4a
/-! CORE route C4a (s23): the steered coupling, deterministic part. Two copies of the scheme are run
on one noise sequence; the second copy uses the shifted noise `n + (u, u/2)` with the adapted
steering `u_l = J(Ŷ pair)((X_l - Ŷ_l)/(m - l))`. The shift adds `avgApply p u` to a step
(`zstep_shift`), so with a right inverse `J` of `avgApply` the step adds `(X_l - Ŷ_l)/(m - l)`
(`cstep_steer`). The steered copy is the plain scheme driven by `shV (steerN ..)` (`shV_crec`). -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

end FlatM_CE
-- ===== CF =====
section FlatM_CF
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

end FlatM_CF
-- ===== CG =====
section FlatM_CG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C4c
/-! CORE route C4c (s24): the steered coupling driven by a Brownian motion. Past-measurability of
the coupled chain, the one-step identity `D_{k+1} = (1 - 1/(m-k)) D_k + h/2 Δb + cellNoise`,
and the second-moment step feeding `steer_rec` (CF.lean). -/

theorem cellZeta_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (s h : ℝ≥0) {t : ℝ≥0} (ht : s + h ≤ t) (j : Fin d) :
    Measurable[G t] (cellZeta W s h j) := by
  have hI := measurable_intervalIntegral_of_continuous (G t)
    (H := fun r ω => W (s + h) ω j - W (s + r) ω j) h
    (fun r hr => (hG _ _ ht j).sub (hG _ _ ((add_le_add le_rfl hr).trans ht) j))
    (fun ω => continuous_const.sub ((EuclideanSpace.proj j).continuous.comp
      ((hWc ω).comp (continuous_const.add continuous_id))))
  unfold cellZeta zetaF
  exact hI.const_mul _

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4c

end ItoLib

end FlatM_CG
-- ===== CH =====
section FlatM_CH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
variable {Ω : Type*}

section C4d
/-! CORE route C4d (s24): lower bound of a weighted event by the relative entropy, with no second
moment of the Girsanov martingale. If `f > 0`, `E f ≤ 1` and `E[-log f] ≤ K`, then
`E[1_E f] ≥ e^{-a} (P E - (K+1)/a)` (Markov on `-log f + f ≥ (-log f)⁺`). -/

open EthierKurtz in
/-- A past-measurable factor times a future Brownian increment has mean zero. -/
theorem past_incr_mean_zero [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (j : Fin d) {u : Ω → ℝ} (hu : Measurable[completedBrownianPast P W (fun _ => x₀) s] u) :
    ∫ ω, u ω * (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hind := indepFun_past_fut hW x₀ s hu (incr_meas_fut W s h j)
  have hm := stdBrownian_coord_measurable hW
  have e := hind.integral_mul_eq_mul_integral (aestronglyMeasurable_of_completedPast hW x₀ s hu)
    (((hm _ j).sub (hm _ j)).aestronglyMeasurable)
  have e2 : (u * fun ω => W (s + h) ω j - W s ω j) = fun ω => u ω * (W (s + h) ω j - W s ω j) :=
    rfl
  rw [e2] at e
  rw [e, stdBrownian_integral_increment hW s h j, mul_zero]

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4d2

end ItoLib

end FlatM_CH
-- ===== CI =====
section FlatM_CI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace ItoLib

section C5a
/-! CORE route C5a (s25): Kolmogorov's maximal inequality in the abstract form needed for the
exit estimate of the Euler chain. The only probabilistic input is the orthogonality of the
"stopped" value `1_{F_k} M_k` to the remaining increment `M_m - M_k`. -/

variable {Ω : Type*} {d : ℕ}

/-- The event that `‖M k‖` reaches `λ` for the first time at step `k`. -/
def firstHit (M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : ℝ) (k : ℕ) : Set Ω :=
  {ω | lam ≤ ‖M k ω‖ ∧ ∀ j < k, ‖M j ω‖ < lam}

theorem firstHit_measurable [MeasurableSpace Ω] {M : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hM : ∀ k, Measurable (M k)) (lam : ℝ) (k : ℕ) : MeasurableSet (firstHit M lam k) := by
  have h1 : MeasurableSet {ω | lam ≤ ‖M k ω‖} :=
    measurableSet_le measurable_const (hM k).norm
  have h2 : MeasurableSet {ω | ∀ j < k, ‖M j ω‖ < lam} := by
    have : {ω | ∀ j < k, ‖M j ω‖ < lam} = ⋂ j ∈ Finset.range k, {ω | ‖M j ω‖ < lam} := by
      ext ω; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ => measurableSet_lt (hM j).norm measurable_const
  exact h1.inter h2

theorem firstHit_disjoint (M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : ℝ) {k k' : ℕ}
    (hkk : k ≠ k') : Disjoint (firstHit M lam k) (firstHit M lam k') := by
  rw [Set.disjoint_left]
  rintro ω ⟨h1, h2⟩ ⟨h1', h2'⟩
  rcases lt_or_gt_of_ne hkk with h | h
  · exact absurd h1 (not_le.2 (h2' k h))
  · exact absurd h1' (not_le.2 (h2 k' h))

theorem exists_hit_eq_iUnion (M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : ℝ) (m : ℕ) :
    {ω | ∃ k ≤ m, lam ≤ ‖M k ω‖} = ⋃ k ∈ Finset.range (m + 1), firstHit M lam k := by
  ext ω
  simp only [mem_setOf_eq, mem_iUnion, Finset.mem_range, exists_prop, firstHit]
  constructor
  · rintro ⟨k, hk, hl⟩
    classical
    have hex : ∃ k, lam ≤ ‖M k ω‖ := ⟨k, hl⟩
    refine ⟨Nat.find hex, by have := Nat.find_min' hex hl; omega, Nat.find_spec hex,
      fun j hj => not_le.1 (Nat.find_min hex hj)⟩
  · rintro ⟨k, hk, hl, -⟩
    exact ⟨k, by omega, hl⟩

/-- Kolmogorov's maximal inequality. -/
theorem kolmogorov_max [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {M : ℕ → Ω → EuclideanSpace ℝ (Fin d)} (hM : ∀ k, Measurable (M k)) (m : ℕ)
    (hint : ∀ k ≤ m, Integrable (fun ω => ‖M k ω‖ ^ 2) μ) {lam : ℝ} (hlam : 0 < lam)
    (hort : ∀ k ≤ m, ∫ ω in firstHit M lam k, ⟪M k ω, M m ω - M k ω⟫ ∂μ = 0) :
    lam ^ 2 * μ.real {ω | ∃ k ≤ m, lam ≤ ‖M k ω‖} ≤ ∫ ω, ‖M m ω‖ ^ 2 ∂μ := by
  rw [exists_hit_eq_iUnion]
  have hFm := firstHit_measurable hM lam
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (m + 1))) (firstHit M lam) :=
    fun k _ k' _ hkk => firstHit_disjoint M lam hkk
  rw [measureReal_biUnion_finset hdisj (fun k _ => hFm k), Finset.mul_sum]
  have hmi := hint m le_rfl
  have hkey : ∀ k ∈ Finset.range (m + 1),
      lam ^ 2 * μ.real (firstHit M lam k) ≤ ∫ ω in firstHit M lam k, ‖M m ω‖ ^ 2 ∂μ := by
    intro k hk
    have hk' : k ≤ m := by have := Finset.mem_range.1 hk; omega
    have hki := hint k hk'
    have hin : Integrable (fun ω => ⟪M k ω, M m ω - M k ω⟫) μ := by
      refine Integrable.mono' ((hki.add hmi).const_mul 2)
        ((hM k).inner ((hM m).sub (hM k))).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      show ‖M k ω‖ * ‖M m ω - M k ω‖ ≤ 2 * (‖M k ω‖ ^ 2 + ‖M m ω‖ ^ 2)
      have h1 := norm_sub_le (M m ω) (M k ω)
      have h2 := norm_nonneg (M m ω)
      have h3 := norm_nonneg (M k ω)
      have h4 := norm_nonneg (M m ω - M k ω)
      have h5 := mul_le_mul_of_nonneg_left (h1.trans (le_of_eq (add_comm _ _))) h3
      first | linarith [sq_nonneg (‖M m ω‖ - ‖M k ω‖)] | nlinarith [sq_nonneg (‖M m ω‖ - ‖M k ω‖)]
    have hpt : ∀ ω, ‖M k ω‖ ^ 2 + 2 * ⟪M k ω, M m ω - M k ω⟫ ≤ ‖M m ω‖ ^ 2 := fun ω => by
      have e : M m ω = M k ω + (M m ω - M k ω) := by abel
      have := norm_add_sq_real (M k ω) (M m ω - M k ω)
      rw [← e] at this
      first | linarith [sq_nonneg ‖M m ω - M k ω‖] | nlinarith [sq_nonneg ‖M m ω - M k ω‖]
    have i1 : lam ^ 2 * μ.real (firstHit M lam k) ≤ ∫ ω in firstHit M lam k, ‖M k ω‖ ^ 2 ∂μ := by
      have := setIntegral_mono_on (integrableOn_const (μ := μ) (s := firstHit M lam k)
        (C := lam ^ 2) (measure_ne_top _ _)) hki.integrableOn (hFm k)
        (fun ω hω => pow_le_pow_left₀ hlam.le hω.1 2)
      rw [setIntegral_const, smul_eq_mul, mul_comm] at this
      exact this
    have i2 : ∫ ω in firstHit M lam k, ‖M k ω‖ ^ 2 ∂μ ≤
        ∫ ω in firstHit M lam k, ‖M m ω‖ ^ 2 ∂μ := by
      have e2 : ∫ ω in firstHit M lam k, (‖M k ω‖ ^ 2 + 2 * ⟪M k ω, M m ω - M k ω⟫) ∂μ =
          ∫ ω in firstHit M lam k, ‖M k ω‖ ^ 2 ∂μ := by
        rw [integral_add hki.integrableOn (hin.const_mul 2).integrableOn, integral_const_mul,
          hort k hk', mul_zero, add_zero]
      rw [← e2]
      exact setIntegral_mono_on (hki.add (hin.const_mul 2)).integrableOn hmi.integrableOn (hFm k)
        (fun ω _ => hpt ω)
    exact i1.trans i2
  refine (Finset.sum_le_sum hkey).trans ?_
  rw [← integral_biUnion_finset _ (fun k _ => hFm k) hdisj (fun k _ => hmi.integrableOn)]
  exact setIntegral_le_integral hmi (ae_of_all _ fun ω => sq_nonneg _)

end C5a

end ItoLib

end FlatM_CI
-- ===== CK =====
section FlatM_CK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5c
/-! CORE route C5c (s26): exit estimate for the Euler chain with bounded coefficients.
`Z_k = Z_0 + M_k + D_k` with `M` the martingale part (orthogonal cell increments) and `D` the
drift part (`‖D_k‖ ≤ k h S`); Kolmogorov's maximal inequality on `M` gives
`(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem past_zeta_mean_zero [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) (j : Fin d) {u : Ω → ℝ}
    (hu : Measurable[completedBrownianPast P W (fun _ => x₀) s] u) :
    ∫ ω, u ω * cellZeta W s h j ω ∂P = 0 := by
  have hind := indepFun_past_fut hW x₀ s hu (zeta_meas_fut hW.2.1 s h j)
  have e := hind.integral_mul_eq_mul_integral (aestronglyMeasurable_of_completedPast hW x₀ s hu)
    ((cellZeta_moments hW s h hh j).2.1.aestronglyMeasurable)
  have e2 : (u * cellZeta W s h j) = fun ω => u ω * cellZeta W s h j ω := rfl
  rw [e2] at e
  rw [e, (cellZeta_moments hW s h hh j).1, mul_zero]

theorem inner_cellNoise (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (A B : Ω → SDEDiffusion d)
    (Y : Ω → SDEState d) (ω : Ω) :
    ⟪Y ω, cellNoise W s h A B ω⟫_ℝ = ∑ i, ∑ j, ((A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
      (B ω (i, j) * Y ω i) * cellZeta W s h j ω) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cellNoise, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring

/-- Orthogonality of a past-measurable `L²` vector to the next cell's martingale increment. -/
theorem cell_orth [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) {Y : Ω → SDEState d} {A B : Ω → SDEDiffusion d} {K : ℝ}
    (hY : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => Y ω i)
    (hYL : ∀ i, MemLp (fun ω => Y ω i) 2 P)
    (hA : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => A ω p)
    (hB : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => B ω p)
    (hAK : ∀ ω, ‖A ω‖ ≤ K) (hBK : ∀ ω, ‖B ω‖ ≤ K) :
    Integrable (fun ω => ⟪Y ω, cellNoise W s h A B ω⟫_ℝ) P ∧
      ∫ ω, ⟪Y ω, cellNoise W s h A B ω⟫_ℝ ∂P = 0 := by
  have hu : ∀ (F : Ω → SDEDiffusion d), (∀ p, Measurable[completedBrownianPast P W
      (fun _ => x₀) s] fun ω => F ω p) → (∀ ω, ‖F ω‖ ≤ K) → ∀ i j,
      Measurable[completedBrownianPast P W (fun _ => x₀) s] (fun ω => F ω (i, j) * Y ω i) ∧
      MemLp (fun ω => F ω (i, j) * Y ω i) 2 P := by
    intro F hF hFK i j
    have hm : Measurable[completedBrownianPast P W (fun _ => x₀) s]
        (fun ω => F ω (i, j) * Y ω i) := by
      let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) s
      exact (hF (i, j)).mul (hY i)
    exact ⟨hm, memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ s (hF (i, j)))
      (fun ω => (coord_abs_le_diff _ (i, j)).trans (hFK ω)) (hYL i)⟩
  have hξL : ∀ j, MemLp (fun ω => W (s + h) ω j - W s ω j) 2 P := fun j =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have hζL : ∀ j, MemLp (fun ω => cellZeta W s h j ω) 2 P := fun j =>
    (cellZeta_moments hW s h hh j).2.1
  have i1 : ∀ i j, Integrable (fun ω => (A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j)) P :=
    fun i j => (hu A hA hAK i j).2.integrable_mul (hξL j)
  have i2 : ∀ i j, Integrable (fun ω => (B ω (i, j) * Y ω i) * cellZeta W s h j ω) P :=
    fun i j => (hu B hB hBK i j).2.integrable_mul (hζL j)
  have i3 : ∀ i j, Integrable (fun ω => (A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
      (B ω (i, j) * Y ω i) * cellZeta W s h j ω) P := fun i j => (i1 i j).add (i2 i j)
  have i4 : ∀ i, Integrable (fun ω => ∑ j, ((A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
      (B ω (i, j) * Y ω i) * cellZeta W s h j ω)) P := fun i =>
    integrable_finsetSum _ fun j _ => i3 i j
  have e : (fun ω => ⟪Y ω, cellNoise W s h A B ω⟫_ℝ) = fun ω => ∑ i, ∑ j,
      ((A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
        (B ω (i, j) * Y ω i) * cellZeta W s h j ω) := funext fun ω => inner_cellNoise W s h A B Y ω
  rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => i4 i, ?_⟩
  rw [integral_finsetSum _ fun i _ => i4 i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => i3 i j]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_add (i1 i j) (i2 i j), past_incr_mean_zero hW x₀ s h j (hu A hA hAK i j).1,
    past_zeta_mean_zero hW x₀ s h hh j (hu B hB hBK i j).1, add_zero]

theorem cellNoise_memLp [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) {A B : Ω → SDEDiffusion d} {K : ℝ}
    (hA : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => A ω p)
    (hB : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => B ω p)
    (hAK : ∀ ω, ‖A ω‖ ≤ K) (hBK : ∀ ω, ‖B ω‖ ≤ K) (i : Fin d) :
    MemLp (fun ω => (cellNoise W s h A B ω) i) 2 P := by
  have hb4 : ∀ (F : Ω → SDEDiffusion d), (∀ ω, ‖F ω‖ ≤ K) → ∀ ω p, |F ω p| ≤ K :=
    fun F hF ω p => (coord_abs_le_diff _ p).trans (hF ω)
  show MemLp (fun ω => ∑ j, (A ω (i, j) * (W (s + h) ω j - W s ω j) +
    B ω (i, j) * cellZeta W s h j ω)) 2 P
  refine memLp_finsetSum _ fun j _ => ?_
  refine (memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ s (hA (i, j)))
    (fun ω => hb4 A hAK ω (i, j))
    ((stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j))).add ?_
  exact memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ s (hB (i, j)))
    (fun ω => hb4 B hBK ω (i, j)) (cellZeta_moments hW s h hh j).2.1

theorem firstHit_meas_le [MeasurableSpace Ω] {M : ℕ → Ω → SDEState d} {k : ℕ}
    (hM : ∀ j ≤ k, Measurable (M j)) (lam : ℝ) : MeasurableSet (firstHit M lam k) := by
  have h1 : MeasurableSet {ω | lam ≤ ‖M k ω‖} :=
    measurableSet_le measurable_const (hM k le_rfl).norm
  have h2 : MeasurableSet {ω | ∀ j < k, ‖M j ω‖ < lam} := by
    have : {ω | ∀ j < k, ‖M j ω‖ < lam} = ⋂ j ∈ Finset.range k, {ω | ‖M j ω‖ < lam} := by
      ext ω; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun j hj =>
      measurableSet_lt (hM j (Finset.mem_range.1 hj).le).norm measurable_const
  exact h1.inter h2

end C5c
end ItoLib

end FlatM_CK
-- ===== CL =====
section FlatM_CL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5d
/-! CORE route C5d (s26): a global, measurable, bounded right inverse of `avgApply` for diffusions
of the form `s x (i, j) = a i x * Γ j i` (the Kolmogorov diffusion read through a projection),
when `Γ` is invertible and `|a i x + a i y| ≥ κ > 0`. -/

variable {d : ℕ}

end C5d
end ItoLib

end FlatM_CL
-- ===== M =====
section FlatM_M
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f1
/-! M10f-1 (b7 groundwork): the restart function `G_k(a, y) = E f(Z_k from (a, y))` is Lipschitz
in the initial pair for Lipschitz `f`, uniformly in the mesh (via `euler_stab_exp`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f1

end ItoLib

end FlatM_M
-- ===== N =====
section FlatM_N
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f2
/-! M10f-2 (b7): uniform smallness of Euler cell increments, and the exit probability
`P(path leaves B̄_R before T) → 0`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {w : ℝ≥0 → SDEState d}

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

variable [MeasurableSpace Ω]

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f6

end ItoLib

end FlatM_N
-- ===== O =====
section FlatM_O
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10g
/-! M10g: from integrated Chapman-Kolmogorov identities for thickened indicators (bounded
Lipschitz test functions) to a Markov kernel and set-wise Chapman-Kolmogorov. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10g

end ItoLib

end FlatM_O
-- ===== P =====
section FlatM_P
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

/-- Local Lipschitz on `s` gives a Lipschitz bound on every compact `K ⊆ s`. -/
theorem lipOn_of_locLip_compact {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {s K : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ L * dist x y := by
  classical
  have hloc : ∀ x : K, ∃ r > (0 : ℝ), ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.ball (x : α) r ∩ s) := by
    intro x
    obtain ⟨L, t, ht, hL⟩ := hf (hKs x.2)
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨r, hr, L, hL.mono hrt⟩
  choose r hr L hL using hloc
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : α) (r x / 2) := fun y hy =>
    Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hr _))⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcov
  -- bound on `f` over `K`
  have hbdd : Bornology.IsBounded (f '' K) :=
    (hK.image_of_continuousOn (hf.continuousOn.mono hKs)).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
  by_cases hTn : T.Nonempty
  · set δ : ℝ := T.inf' hTn (fun x => r x / 2) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]; exact fun x _ => half_pos (hr x)
    set Lm : ℝ≥0 := T.sup L
    refine ⟨Lm + max C 0 / δ, by positivity, fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by linarith [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by linarith
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y := by positivity
      nlinarith [dist_nonneg (x := x) (y := y)]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := by positivity
      nlinarith
  · have hK0 : K = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hTn
      subst hTn; simpa using hT
    exact ⟨0, le_rfl, fun x hx => by simp [hK0] at hx⟩

variable {d : ℕ}

/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem clamp1_lip (M a b : ℝ) : |max (-M) (min M a) - max (-M) (min M b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Coordinate clamp to the box `[-M, M]^d`. -/
noncomputable def clampM (M : ℝ) (x : SDEState d) : SDEState d :=
  WithLp.toLp 2 (fun i => max (-M) (min M (x i)))

theorem clampM_apply (M : ℝ) (x : SDEState d) (i : Fin d) :
    clampM M x i = max (-M) (min M (x i)) := rfl

theorem clampM_lip (M : ℝ) (x y : SDEState d) : ‖clampM M x - clampM M y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [clampM_apply, clampM_apply]; exact clamp1_lip _ _ _

theorem clampM_abs_le {M : ℝ} (hM : 0 ≤ M) (x : SDEState d) (i : Fin d) : |clampM M x i| ≤ M := by
  rw [clampM_apply, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampM_eq {M : ℝ} {x : SDEState d} (hx : ‖x‖ ≤ M) : clampM M x = x := by
  ext i
  rw [clampM_apply]
  have := (coord_abs_le_state x i).trans hx
  rw [abs_le] at this
  rw [min_eq_right this.2, max_eq_right this.1]

theorem norm_le_card_mul {M : ℝ} {x : SDEState d} (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ d * M := by
  calc ‖x‖ ≤ ∑ i, |x i| := euc_norm_le_sum' x
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hx i
    _ = d * M := by simp

/-- b9: a truncation family for coordinate functions that are Lipschitz on every box. -/
theorem trunc_family {ι : Type*} [Fintype ι] (φ : ι → SDEState d → ℝ)
    (hL : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ k x y, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |φ k x - φ k y| ≤ L * ‖x - y‖) :
    ∃ (s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι) (S L : ℕ → ℝ), (∀ R, Continuous (s₁ R)) ∧
      (∀ R, 0 ≤ L R) ∧ (∀ R x, ‖s₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = WithLp.toLp 2 (fun k => φ k x)) := by
  classical
  choose Lb hLb0 hLb using fun R : ℕ => hL ((R : ℝ) + 3) (by positivity)
  set s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι :=
    fun R x => WithLp.toLp 2 (fun k => φ k (clampM ((R : ℝ) + 3) x)) with hs₁
  have hM : ∀ R : ℕ, (0 : ℝ) ≤ (R : ℝ) + 3 := fun R => by positivity
  have hlip : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ (Fintype.card ι * Lb R) * ‖x - y‖ := by
    intro R x y
    calc ‖s₁ R x - s₁ R y‖ ≤ ∑ k, |(s₁ R x - s₁ R y) k| := euc_norm_le_sum' _
      _ ≤ ∑ _k : ι, Lb R * ‖x - y‖ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁, PiLp.sub_apply]
          exact (hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) y)).trans
            (mul_le_mul_of_nonneg_left (clampM_lip _ _ _) (hLb0 R))
      _ = (Fintype.card ι * Lb R) * ‖x - y‖ := by simp [mul_assoc]
  refine ⟨s₁, fun R => ∑ k : ι, (|φ k (clampM ((R : ℝ) + 3) 0)| + Lb R * (2 * (d * ((R : ℝ) + 3)))),
    fun R => Fintype.card ι * Lb R, fun R => ?_, fun R => by have := hLb0 R; positivity,
    fun R x => ?_, hlip, fun R x hx => ?_⟩
  · exact LipschitzWith.continuous (K := ⟨Fintype.card ι * Lb R, by have := hLb0 R; positivity⟩)
      (LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hlip R x y)
  · calc ‖s₁ R x‖ ≤ ∑ k, |s₁ R x k| := euc_norm_le_sum' _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁]
          set M : ℝ := (R : ℝ) + 3
          have hc := hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) 0)
          have hn : ‖clampM M x - clampM M 0‖ ≤ 2 * (d * M) := by
            calc ‖clampM M x - clampM M 0‖ ≤ ‖clampM M x‖ + ‖clampM M 0‖ := norm_sub_le _ _
              _ ≤ d * M + d * M := add_le_add (norm_le_card_mul (clampM_abs_le (hM R) x))
                  (norm_le_card_mul (clampM_abs_le (hM R) 0))
              _ = 2 * (d * M) := by ring
          have := mul_le_mul_of_nonneg_left hn (hLb0 R)
          have h3 := abs_sub_abs_le_abs_sub (φ k (clampM M x)) (φ k (clampM M 0))
          linarith
  · simp only [hs₁, clampM_eq hx]

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem posPart_mem_orthant (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [posPart_apply']; exact le_max_right _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

/-- A locally Lipschitz function on the orthant, read at `x⁺`, is Lipschitz and bounded on boxes. -/
theorem locLip_posPart_box {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L G : ℝ, 0 ≤ L ∧ 0 ≤ G ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |h (posPart x) - h (posPart y)| ≤ L * ‖x - y‖ ∧ |h (posPart x)| ≤ G := by
  set K : Set (SDEState n) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ M} with hKdef
  have hKc : IsClosed K := by
    have : K = ⋂ i, ({y : SDEState n | 0 ≤ y i} ∩ {y | y i ≤ M}) := by
      ext y; simp [hKdef, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  have hKb : Bornology.IsBounded K := (Metric.isBounded_closedBall (x := (0 : SDEState n))
      (r := n * M)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hy i).1]; exact (hy i).2
  have hKo : K ⊆ orthant n := fun y hy i => (hy i).1
  obtain ⟨L, hL0, hL⟩ := lipOn_of_locLip_compact hh (Metric.isCompact_of_isClosed_isBounded hKc hKb) hKo
  have hpK : ∀ x : SDEState n, (∀ i, |x i| ≤ M) → posPart x ∈ K := fun x hx i => by
    rw [posPart_apply']
    exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hx i)) hM⟩
  have h0 : ∀ i, |(0 : SDEState n) i| ≤ M := fun i => by simpa using hM
  refine ⟨L, L * (n * M) + |h (posPart 0)|, hL0, by positivity, fun x y hx hy => ⟨?_, ?_⟩⟩
  · have := hL _ (hpK x hx) _ (hpK y hy)
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (posPart_lip x y) hL0)
  · have h1 := hL _ (hpK x hx) _ (hpK 0 h0)
    rw [Real.dist_eq, dist_eq_norm] at h1
    have h2 : ‖posPart x - posPart (0 : SDEState n)‖ ≤ n * M := by
      calc ‖posPart x - posPart (0 : SDEState n)‖ ≤ ‖x - 0‖ := posPart_lip x 0
        _ = ‖x‖ := by rw [sub_zero]
        _ ≤ n * M := norm_le_card_mul hx
    have h3 := abs_sub_abs_le_abs_sub (h (posPart x)) (h (posPart 0))
    have h4 := mul_le_mul_of_nonneg_left h2 hL0
    linarith

/-- Products `x_i · h(x⁺) · c` are Lipschitz on boxes. -/
theorem prod_box_lip {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h) (c : ℝ) (i : Fin n)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x i * h (posPart x) * c - y i * h (posPart y) * c| ≤ L * ‖x - y‖ := by
  obtain ⟨L, G, hL0, hG0, hLG⟩ := locLip_posPart_box hh hM
  refine ⟨|c| * (M * L + G), by positivity, fun x y hx hy => ?_⟩
  obtain ⟨h1, -⟩ := hLG x y hx hy
  obtain ⟨-, h2⟩ := hLG y x hy hx
  have hxy : |x i - y i| ≤ ‖x - y‖ := by
    have := coord_abs_le_state (x - y) i; rwa [PiLp.sub_apply] at this
  have e : x i * h (posPart x) * c - y i * h (posPart y) * c =
      c * (x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)) := by ring
  rw [e, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc |x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)|
      ≤ |x i| * |h (posPart x) - h (posPart y)| + |h (posPart y)| * |x i - y i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ M * (L * ‖x - y‖) + G * ‖x - y‖ := by
        gcongr
        · exact hx i
    _ = (M * L + G) * ‖x - y‖ := by ring

/-- b11: the Kolmogorov coefficients are continuous and have truncation families as needed by
`markov_core`. -/
theorem kolm_trunc (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (fun x : SDEState n => diffusion C (0, x)) ∧
    Continuous (fun x : SDEState n => drift C (0, x)) ∧
    ∃ (s₁ : ℕ → SDEState n → SDEDiffusion n) (b₁ : ℕ → SDEState n → SDEState n) (S L : ℕ → ℝ),
      (∀ R, Continuous (s₁ R)) ∧ (∀ R, Continuous (b₁ R)) ∧ (∀ R, 0 ≤ L R) ∧
      (∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState n), ‖x‖ ≤ (R : ℝ) + 3 →
        s₁ R x = diffusion C (0, x) ∧ b₁ R x = drift C (0, x)) := by
  have hgc : ∀ i, Continuous fun x : SDEState n => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hfc : ∀ i, Continuous fun x : SDEState n => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (((PiLp.continuous_apply 2 _ k.1).mul (hgc k.1)).mul continuous_const)),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      ((PiLp.continuous_apply 2 _ k).mul (hfc k))), ?_⟩
  -- the two coordinate families
  have hLs : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n × Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k.1 * C.g k.1 (posPart x) * C.Γ k.2 k.1 - y k.1 * C.g k.1 (posPart y) * C.Γ k.2 k.1|
        ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n × Fin n => prod_box_lip (hC k.1).2 (C.Γ k.2 k.1) k.1 hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  have hLb : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k * C.f k (posPart x) * 1 - y k * C.f k (posPart y) * 1| ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n => prod_box_lip (hC k).1 1 k hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  obtain ⟨s₁, S1, L1, hs1c, hL1, hS1, hl1, he1⟩ := trunc_family _ hLs
  obtain ⟨b₁, S2, L2, hb1c, hL2, hS2, hl2, he2⟩ := trunc_family _ hLb
  refine ⟨s₁, b₁, fun R => max (S1 R) (S2 R), fun R => max (L1 R) (L2 R), hs1c, hb1c,
    fun R => (hL1 R).trans (le_max_left _ _), fun R x => ⟨(hS1 R x).trans (le_max_left _ _),
      (hS2 R x).trans (le_max_right _ _)⟩, fun R x y => ⟨(hl1 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), (hl2 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩, fun R x hx => ⟨?_, ?_⟩⟩
  · rw [he1 R x hx]; rfl
  · rw [he2 R x hx]; simp only [mul_one]; rfl

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

end M10j

end ItoLib

end FlatM_P
-- ===== CM =====
section FlatM_CM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5dK
/-! CORE route C5d, Kolmogorov instance (s26): the coefficients read through the box clamp
`boxP α β` (box `[α, β]^n` inside the open orthant) are globally Lipschitz and bounded, have the
form `s x (i, j) = aK i x * Γ j i`, and `|aK i x + aK i y| ≥ κ > 0` (Assumption 1.1 part 1). -/

variable {n : ℕ}

open StochKolmogorov.Persist

end C5dK
end ItoLib

end FlatM_CM
-- ===== CN =====
section FlatM_CN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5g
/-! CORE route, s27: (1) `Γ` is invertible under Assumption 1.1 part 1; (2) a generic discrete
martingale `gmart` built from bounded past-measurable cell coefficients: measurability, second
moment, orthogonality and the Kolmogorov maximal inequality (used for the tracking estimate of
the steered chain). -/

/-- Discrete martingale with cell coefficients `A l`, `B l`. -/
noncomputable def gmart (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (A B : ℕ → Ω → SDEDiffusion d)
    (k : ℕ) (ω : Ω) : SDEState d :=
  ∑ l ∈ Finset.range k, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω

theorem tnn_succ (h : ℝ≥0) (l : ℕ) :
    (((l + 1 : ℕ) : ℝ) * h).toNNReal = ((l : ℝ) * h).toNNReal + h := by
  rw [show ((l + 1 : ℕ) : ℝ) * h = (l : ℝ) * h + (h : ℝ) by push_cast; ring,
    Real.toNNReal_add (mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg h))
      (NNReal.coe_nonneg h), Real.toNNReal_coe]

theorem tnn_mono (h : ℝ≥0) {l k : ℕ} (hlk : l ≤ k) :
    ((l : ℝ) * h).toNNReal ≤ ((k : ℝ) * h).toNNReal :=
  Real.toNNReal_le_toNNReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hlk) h.2)

theorem cellNoise_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (s h : ℝ≥0) {t : ℝ≥0} (ht : s + h ≤ t)
    {A B : Ω → SDEDiffusion d} (hA : ∀ p, Measurable[G t] fun ω => A ω p)
    (hB : ∀ p, Measurable[G t] fun ω => B ω p) :
    Measurable[G t] (cellNoise W s h A B) := by
  let _ : MeasurableSpace Ω := G t
  have hc : Measurable fun ω => (fun i => ∑ j, (A ω (i, j) * (W (s + h) ω j - W s ω j) +
      B ω (i, j) * cellZeta W s h j ω) : Fin d → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((hA (i, j)).mul ((hG _ _ ht j).sub (hG _ _ (le_self_add.trans ht) j))).add
      ((hB (i, j)).mul (cellZeta_meas_G hG hWc s h ht j))
  exact (PiLp.continuous_toLp 2 _).measurable.comp hc

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

theorem gmart_meas_G {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j) (hGm : Monotone G)
    (hWc : ∀ ω, Continuous fun s => W s ω)
    (hA : ∀ (l : ℕ) p, Measurable[G ((l : ℝ) * h).toNNReal] fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[G ((l : ℝ) * h).toNNReal] fun ω => B l ω p) (k : ℕ) :
    Measurable[G ((k : ℝ) * h).toNNReal] (gmart W h A B k) := by
  let _ : MeasurableSpace Ω := G ((k : ℝ) * h).toNNReal
  unfold gmart
  refine Finset.measurable_sum _ fun l hl => ?_
  have hlk : l + 1 ≤ k := Finset.mem_range.1 hl
  have ht : ((l : ℝ) * h).toNNReal + h ≤ ((k : ℝ) * h).toNNReal := by
    rw [← tnn_succ]; exact tnn_mono h hlk
  have hmono := hGm (tnn_mono h (Nat.le_of_succ_le hlk))
  exact cellNoise_meas_G hG hWc _ h ht (fun p => (hA l p).mono hmono le_rfl)
    (fun p => (hB l p).mono hmono le_rfl)

theorem gmart_meas (x₀ : SDEState d) (hWc : ∀ ω, Continuous fun s => W s ω)
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) (k : ℕ) :
    Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
      (gmart W h A B k) :=
  gmart_meas_G (fun r t hrt j => coord_measurable_completedPast P W _ hrt j)
    (fun _ _ hst => completedBrownianPast_mono P W _ hst) hWc hA hB k

theorem gmart_meas_amb (hW : IsStandardBrownian P W)
    (hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p) (hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p)
    (k : ℕ) : Measurable (gmart W h A B k) :=
  gmart_meas_G (G := fun _ => ‹MeasurableSpace Ω›)
    (fun r _ _ j => stdBrownian_coord_measurable hW r j) (fun _ _ _ => le_rfl) hW.2.1 hAa hBa k

theorem gmart_moment (hW : IsStandardBrownian P W) (x₀ : SDEState d) (hh : 0 < (h : ℝ))
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) {K : ℝ} (hAK : ∀ l ω, ‖A l ω‖ ≤ K) (hBK : ∀ l ω, ‖B l ω‖ ≤ K)
    (k : ℕ) :
    (∀ i, MemLp (fun ω => gmart W h A B k ω i) 2 P) ∧
      ∫ ω, ‖gmart W h A B k ω‖ ^ 2 ∂P ≤
        ∑ l ∈ Finset.range k, 2 * d * h * ∫ ω, (‖A l ω‖ ^ 2 + ‖B l ω‖ ^ 2) ∂P := by
  induction k with
  | zero => refine ⟨fun i => ?_, ?_⟩ <;> simp [gmart]
  | succ k ih =>
    obtain ⟨ihL, ihB⟩ := ih
    have hDm := gmart_meas (P := P) x₀ hW.2.1 hA hB k
    have hDc : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
        fun ω => gmart W h A B k ω i := fun i =>
      (EuclideanSpace.proj i).continuous.measurable.comp hDm
    have step := cellNoise_step hW x₀ _ h hh hDc ihL (hA k) (hB k) (hAK k) (hBK k)
    have hNL := cellNoise_memLp hW x₀ _ h hh (hA k) (hB k) (hAK k) (hBK k)
    have e : ∀ ω, gmart W h A B (k + 1) ω = gmart W h A B k ω +
        cellNoise W ((k : ℝ) * h).toNNReal h (A k) (B k) ω := fun ω => by
      simp only [gmart, Finset.sum_range_succ]
    simp_rw [e]
    refine ⟨fun i => (ihL i).add (hNL i), ?_⟩
    rw [Finset.sum_range_succ]
    linarith

/-- The orthogonality hypothesis of `kolmogorov_max` for `gmart`. -/
theorem gmart_orth (hW : IsStandardBrownian P W) (x₀ : SDEState d) (hh : 0 < (h : ℝ))
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) {K : ℝ} (hAK : ∀ l ω, ‖A l ω‖ ≤ K) (hBK : ∀ l ω, ‖B l ω‖ ≤ K)
    (hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p) (hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p)
    (lam : ℝ) {k m : ℕ} (hkm : k ≤ m) :
    ∫ ω in firstHit (gmart W h A B) lam k,
      ⟪gmart W h A B k ω, gmart W h A B m ω - gmart W h A B k ω⟫_ℝ ∂P = 0 := by
  set M : ℕ → Ω → SDEState d := gmart W h A B with hMdef
  set F := firstHit M lam k with hFdef
  have hMa : ∀ j, Measurable (M j) := gmart_meas_amb hW hAa hBa
  have hF : MeasurableSet F := firstHit_measurable hMa lam k
  set tk : ℝ≥0 := ((k : ℝ) * h).toNNReal with htk
  have hFG : MeasurableSet[completedBrownianPast P W (fun _ => x₀) tk] F := by
    have hj' : ∀ j ≤ k, Measurable[completedBrownianPast P W (fun _ => x₀) tk] (M j) :=
      fun j hj => (gmart_meas (P := P) x₀ hW.2.1 hA hB j).mono
        (completedBrownianPast_mono P W _ (tnn_mono h hj)) le_rfl
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) tk
    exact firstHit_meas_le hj' lam
  set Y : Ω → SDEState d := F.indicator (M k) with hYdef
  have hYm : Measurable[completedBrownianPast P W (fun _ => x₀) tk] Y := by
    have hk := gmart_meas (P := P) x₀ hW.2.1 hA hB k
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) tk
    exact hk.indicator hFG
  have hML := (gmart_moment hW x₀ hh hA hB hAK hBK k).1
  have hYc : ∀ i, (fun ω => Y ω i) = F.indicator (fun ω => M k ω i) := fun i => by
    funext ω; by_cases hω : ω ∈ F <;> simp [hYdef, hω]
  have hYL : ∀ i, MemLp (fun ω => Y ω i) 2 P := fun i => by
    rw [hYc i]; exact (hML i).indicator hF
  have hdiff : ∀ ω, M m ω - M k ω = ∑ l ∈ Finset.Ico k m,
      cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω := by
    intro ω
    simp only [hMdef, gmart]
    rw [← Finset.sum_Ico_eq_sub _ hkm]
  have hind : ∀ ω, F.indicator (fun ω => ⟪M k ω, M m ω - M k ω⟫_ℝ) ω =
      ∑ l ∈ Finset.Ico k m, ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω⟫_ℝ := by
    intro ω
    rw [← inner_sum, ← hdiff ω]
    by_cases hω : ω ∈ F <;> simp [hYdef, hω]
  have hl : ∀ l ∈ Finset.Ico k m,
      Integrable (fun ω => ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω⟫_ℝ) P ∧
      ∫ ω, ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω⟫_ℝ ∂P = 0 := fun l hl' => by
    have hkl : k ≤ l := (Finset.mem_Ico.1 hl').1
    have hmono := completedBrownianPast_mono P W (fun _ => x₀) (tnn_mono h hkl)
    refine cell_orth hW x₀ _ h hh (fun i => ?_) hYL (hA l) (hB l) (hAK l) (hBK l)
    exact ((EuclideanSpace.proj i).continuous.measurable.comp hYm).mono hmono le_rfl
  rw [← integral_indicator hF, integral_congr_ae (ae_of_all _ hind),
    integral_finsetSum _ fun l hl' => (hl l hl').1]
  exact Finset.sum_eq_zero fun l hl' => (hl l hl').2

/-- Kolmogorov's maximal inequality for `gmart`. -/
theorem gmart_max (hW : IsStandardBrownian P W) (x₀ : SDEState d) (hh : 0 < (h : ℝ))
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) {K : ℝ} (hAK : ∀ l ω, ‖A l ω‖ ≤ K) (hBK : ∀ l ω, ‖B l ω‖ ≤ K)
    (hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p) (hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p)
    (m : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ k ≤ m, lam ≤ ‖gmart W h A B k ω‖} ≤
      ∑ l ∈ Finset.range m, 2 * d * h * ∫ ω, (‖A l ω‖ ^ 2 + ‖B l ω‖ ^ 2) ∂P := by
  have hMa : ∀ j, Measurable (gmart W h A B j) := gmart_meas_amb hW hAa hBa
  have hK := kolmogorov_max (μ := P) hMa m
    (fun k _ => integrable_norm_sq_of_coords (gmart_moment hW x₀ hh hA hB hAK hBK k).1)
    hlam (fun k hk => gmart_orth hW x₀ hh hA hB hAK hBK hAa hBa lam hk)
  exact hK.trans (gmart_moment hW x₀ hh hA hB hAK hBK m).2

end C5g
end ItoLib

end FlatM_CN
-- ===== QA =====
section FlatM_QA
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QA
/-! lemma_3_1 (aaf23e78) toolkit, part QA: continuous versions of Ito integrals.
Dyadic grid `gpt m l = l / 2^m`, the horizon-free step integral `stepM` (mesh `2^{-q}` on
`[0,q]`), its values at finer grid points, and a continuous-time maximal inequality for
differences of step integrals (via `gmart_max`). -/

noncomputable def hm (m : ℕ) : ℝ≥0 := 1 / 2 ^ m

noncomputable def gpt (m l : ℕ) : ℝ≥0 := ((l : ℝ) * (hm m : ℝ)).toNNReal

theorem hm_coe (m : ℕ) : (hm m : ℝ) = 1 / 2 ^ m := by simp [hm]

theorem gpt_coe (m l : ℕ) : (gpt m l : ℝ) = l / 2 ^ m := by
  unfold gpt
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg _)), hm_coe]
  ring

theorem gpt_le_iff (m a b : ℕ) : gpt m a ≤ gpt m b ↔ a ≤ b := by
  rw [← NNReal.coe_le_coe, gpt_coe, gpt_coe, div_le_div_iff_of_pos_right (by positivity)]
  exact Nat.cast_le

theorem gpt_lift {q r : ℕ} (hqr : q ≤ r) (l : ℕ) : gpt q l = gpt r (l * 2 ^ (r - q)) := by
  apply NNReal.coe_injective
  rw [gpt_coe, gpt_coe]
  push_cast
  have h2 : (2 : ℝ) ^ r = 2 ^ q * 2 ^ (r - q) := by
    rw [← pow_add, Nat.add_sub_cancel' hqr]
  rw [h2]
  field_simp

theorem gpt_nat (r N : ℕ) : gpt r (N * 2 ^ r) = (N : ℝ≥0) := by
  apply NNReal.coe_injective
  rw [gpt_coe]; push_cast; field_simp

/-- The step integral of `H` (left points of mesh `2^{-q}` on `[0,q]`), stopped at time `t`. -/
noncomputable def stepM (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) (q : ℕ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range (q * 2 ^ q),
    H (gpt q l) ω * (W (min (gpt q (l + 1)) t) ω j - W (min (gpt q l) t) ω j)

/-- The discrete martingale of a level-`r` coefficient sequence. -/
noncomputable def dsum (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (r : ℕ) (φ : ℕ → Ω → ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, φ i ω * (W (gpt r (i + 1)) ω j - W (gpt r i) ω j)

theorem stepM_continuous {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (j : Fin d) (H : ℝ≥0 → Ω → ℝ) (q : ℕ) (ω : Ω) : Continuous fun t => stepM W j H q t ω := by
  unfold stepM
  have hc : ∀ a : ℝ≥0, Continuous fun t : ℝ≥0 => W (min a t) ω j := fun a =>
    (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp
      ((hWc ω).comp (continuous_const.min continuous_id)))
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((hc _).sub (hc _))

/-- One fine-grid step of `stepM`: on the level-`r` cell `k` the increment is the left
coefficient of the enclosing level-`q` cell times the Brownian increment. -/
theorem stepM_succ (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {q r : ℕ}
    (hqr : q ≤ r) {k : ℕ} (hk : k < q * 2 ^ r) (ω : Ω) :
    stepM W j H q (gpt r (k + 1)) ω - stepM W j H q (gpt r k) ω =
      H (gpt q (k / 2 ^ (r - q))) ω * (W (gpt r (k + 1)) ω j - W (gpt r k) ω j) := by
  set e := 2 ^ (r - q) with he
  have he0 : 0 < e := by positivity
  set l0 := k / e with hl0
  have hlo : l0 * e ≤ k := Nat.div_mul_le_self k e
  have hhi : k < (l0 + 1) * e := by
    rw [hl0, add_mul, one_mul]; exact Nat.lt_div_mul_add he0
  have hl0q : l0 < q * 2 ^ q := by
    rw [hl0, Nat.div_lt_iff_lt_mul he0, mul_assoc, he, ← pow_add, Nat.add_sub_cancel' hqr]
    exact hk
  unfold stepM
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l0]
  · have h1 : min (gpt q (l0 + 1)) (gpt r (k + 1)) = gpt r (k + 1) := by
      rw [gpt_lift hqr]; exact min_eq_right ((gpt_le_iff _ _ _).2 hhi)
    have h2 : min (gpt q (l0 + 1)) (gpt r k) = gpt r k := by
      rw [gpt_lift hqr]; exact min_eq_right ((gpt_le_iff _ _ _).2 hhi.le)
    have h3 : min (gpt q l0) (gpt r (k + 1)) = gpt q l0 := by
      rw [gpt_lift hqr]; exact min_eq_left ((gpt_le_iff _ _ _).2 (hlo.trans (Nat.le_succ k)))
    have h4 : min (gpt q l0) (gpt r k) = gpt q l0 := by
      rw [gpt_lift hqr]; exact min_eq_left ((gpt_le_iff _ _ _).2 hlo)
    rw [h1, h2, h3, h4]; ring
  · intro l _ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hA : ∀ t ∈ ({gpt r k, gpt r (k + 1)} : Set ℝ≥0), min (gpt q (l + 1)) t = gpt q (l + 1) ∧
          min (gpt q l) t = gpt q l := by
        intro t ht
        have hkt : gpt r k ≤ t := by
          rcases ht with rfl | rfl
          · exact le_rfl
          · exact (gpt_le_iff _ _ _).2 (Nat.le_succ k)
        have hb : gpt q (l + 1) ≤ gpt r k := by
          rw [gpt_lift hqr]; refine (gpt_le_iff _ _ _).2 (le_trans ?_ hlo)
          exact Nat.mul_le_mul_right _ hlt
        have hb' : gpt q l ≤ gpt q (l + 1) := (gpt_le_iff _ _ _).2 (Nat.le_succ l)
        exact ⟨min_eq_left (hb.trans hkt), min_eq_left ((hb'.trans hb).trans hkt)⟩
      obtain ⟨a1, a2⟩ := hA (gpt r (k + 1)) (by simp)
      obtain ⟨b1, b2⟩ := hA (gpt r k) (by simp)
      rw [a1, a2, b1, b2]; ring
    · have hb : gpt r (k + 1) ≤ gpt q l := by
        rw [gpt_lift hqr]; refine (gpt_le_iff _ _ _).2 (le_trans (Nat.succ_le_of_lt hhi) ?_)
        exact Nat.mul_le_mul_right _ hgt
      have hb' : gpt q l ≤ gpt q (l + 1) := (gpt_le_iff _ _ _).2 (Nat.le_succ l)
      have hk1 : gpt r k ≤ gpt r (k + 1) := (gpt_le_iff _ _ _).2 (Nat.le_succ k)
      rw [min_eq_right (hb.trans hb'), min_eq_right hb, min_eq_right ((hk1.trans hb).trans hb'),
        min_eq_right (hk1.trans hb)]
      ring
  · intro h; exact absurd (Finset.mem_range.2 hl0q) h

theorem stepM_zero (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) (q : ℕ) (ω : Ω) :
    stepM W j H q 0 ω = 0 := by
  unfold stepM
  exact Finset.sum_eq_zero fun l _ => by simp

/-- `stepM` at fine grid points is a discrete martingale sum. -/
theorem stepM_grid (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {q r : ℕ}
    (hqr : q ≤ r) {k : ℕ} (hk : k ≤ q * 2 ^ r) (ω : Ω) :
    stepM W j H q (gpt r k) ω =
      dsum W j r (fun i ω => H (gpt q (i / 2 ^ (r - q))) ω) k ω := by
  induction k with
  | zero =>
    have : gpt r 0 = 0 := by simp [gpt]
    rw [this, stepM_zero]; simp [dsum]
  | succ k ih =>
    have h1 := stepM_succ W j H hqr (k := k) (by omega) ω
    rw [dsum, Finset.sum_range_succ, ← dsum, ← ih (by omega)]
    linarith

theorem dsum_sub (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (r : ℕ) (φ ψ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    dsum W j r φ k ω - dsum W j r ψ k ω = dsum W j r (fun i ω => φ i ω - ψ i ω) k ω := by
  unfold dsum; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem div_mul_le_div_mul' {i a b : ℕ} (hb : 0 < b) (hba : b ∣ a) : i / a * a ≤ i / b * b := by
  obtain ⟨c, rfl⟩ := hba
  have h1 : i / (b * c) * c ≤ i / b := by
    rw [Nat.le_div_iff_mul_le hb]
    calc i / (b * c) * c * b = i / (b * c) * (b * c) := by ring
      _ ≤ i := Nat.div_mul_le_self _ _
  calc i / (b * c) * (b * c) = (i / (b * c) * c) * b := by ring
    _ ≤ i / b * b := Nat.mul_le_mul_right _ h1

/-- Discrete Kolmogorov maximal inequality for a scalar level-`r` martingale sum. -/
theorem dsum_max [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    (r : ℕ) {φ : ℕ → Ω → ℝ}
    (hφ : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) (gpt r i)] (φ i))
    (hφa : ∀ i, Measurable (φ i)) {K : ℝ} (hK : ∀ i ω, |φ i ω| ≤ K) (m : ℕ) {lam : ℝ}
    (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ k ≤ m, lam ≤ |dsum W j r φ k ω|} ≤
      ∑ i ∈ Finset.range m, 2 * d * (hm r : ℝ) * ∫ ω, φ i ω ^ 2 ∂P := by
  let A : ℕ → Ω → SDEDiffusion d := fun i ω => EuclideanSpace.single (j, j) (φ i ω)
  let B : ℕ → Ω → SDEDiffusion d := fun _ _ => 0
  have hAm : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀)
      ((l : ℝ) * (hm r : ℝ)).toNNReal] fun ω => A l ω p := by
    intro l p
    simp only [A, EuclideanSpace.single_apply]
    split_ifs
    · exact hφ l
    · exact measurable_const
  have hBm : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀)
      ((l : ℝ) * (hm r : ℝ)).toNNReal] fun ω => B l ω p := fun _ _ => measurable_const
  have hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p := by
    intro l p
    simp only [A, EuclideanSpace.single_apply]
    split_ifs
    · exact hφa l
    · exact measurable_const
  have hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p := fun _ _ => measurable_const
  have hAK : ∀ l ω, ‖A l ω‖ ≤ max K 0 := fun l ω => by
    simp only [A, EuclideanSpace.norm_single, Real.norm_eq_abs]
    exact (hK l ω).trans (le_max_left _ _)
  have hBK : ∀ l ω, ‖B l ω‖ ≤ max K 0 := fun l ω => by simp [B]
  have hh : 0 < (hm r : ℝ) := by rw [hm_coe]; positivity
  have key : ∀ k ω, ‖gmart W (hm r) A B k ω‖ = |dsum W j r φ k ω| := by
    intro k ω
    have : gmart W (hm r) A B k ω = EuclideanSpace.single j (dsum W j r φ k ω) := by
      ext i
      simp only [gmart, cellNoise, dsum, A, B, EuclideanSpace.single_apply, WithLp.ofLp_sum,
        Finset.sum_apply, PiLp.toLp_apply]
      have hs : ∀ l : ℕ, ((l : ℝ) * (hm r : ℝ)).toNNReal + hm r = gpt r (l + 1) :=
        fun l => (tnn_succ _ l).symm
      simp only [hs]
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_eq_single i]
        · simp [gpt]
        · intro b _ hb; simp [Prod.ext_iff, hb]
        · simp
      · simp only [hij, if_false]
        refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun b _ => ?_
        simp [Prod.ext_iff, hij]
    rw [this, EuclideanSpace.norm_single, Real.norm_eq_abs]
  have hmax := gmart_max hW x₀ hh hAm hBm hAK hBK hAa hBa m hlam
  have hset : {ω | ∃ k ≤ m, lam ≤ ‖gmart W (hm r) A B k ω‖} =
      {ω | ∃ k ≤ m, lam ≤ |dsum W j r φ k ω|} := by
    ext ω; simp only [Set.mem_setOf_eq, key]
  rw [hset] at hmax
  refine hmax.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp [A, B, EuclideanSpace.norm_single, sq_abs]

/-- Continuous-time maximal inequality for the difference of two step integrals of a bounded
adapted continuous integrand, given an `L²` modulus bound `β` at mesh `2^{-p}`. -/
theorem stepM_sup_max [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C) {N p q : ℕ}
    (hNp : N ≤ p) (hpq : p ≤ q) {β : ℝ}
    (hβ : ∀ s u : ℝ≥0, s ≤ u → u ≤ N → (u : ℝ) - s ≤ 1 / 2 ^ p →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ β) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧
      lam < |stepM W j H q t ω - stepM W j H p t ω|} ≤ 2 * d * N * β := by
  have hβ0 : 0 ≤ β := le_trans (integral_nonneg fun ω => sq_nonneg _)
    (hβ 0 0 le_rfl (by simp) (by simp))
  set D : ℝ≥0 → Ω → ℝ := fun t ω => stepM W j H q t ω - stepM W j H p t ω with hD
  have hDc : ∀ ω, Continuous fun t => D t ω := fun ω =>
    (stepM_continuous hW.2.1 j H q ω).sub (stepM_continuous hW.2.1 j H p ω)
  let A : ℕ → Set Ω := fun r => {ω | ∃ k ≤ N * 2 ^ r, lam ≤ |D (gpt r k) ω|}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun r ω hω => ?_
    obtain ⟨k, hk, hl⟩ := hω
    refine ⟨k * 2 ^ (r + 1 - r), ?_, ?_⟩
    · have h2 : 2 ^ (r + 1 - r) = 2 := by simp
      rw [h2, pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_right 2 hk
    · rwa [← gpt_lift (Nat.le_succ r)]
  set Bd : ℝ := 2 * d * N * β / lam ^ 2 with hBd
  have hlev : ∀ r, q ≤ r → P.real (A r) ≤ Bd := by
    intro r hqr
    have hpr : p ≤ r := hpq.trans hqr
    set φ : ℕ → Ω → ℝ := fun i ω => H (gpt q (i / 2 ^ (r - q))) ω - H (gpt p (i / 2 ^ (r - p))) ω
      with hφ
    have hAeq : A r = {ω | ∃ k ≤ N * 2 ^ r, lam ≤ |dsum W j r φ k ω|} := by
      ext ω
      simp only [A, Set.mem_setOf_eq]
      refine exists_congr fun k => and_congr_right fun hk => ?_
      have h1 := stepM_grid W j H (le_refl q |>.trans hqr) (k := k)
        (hk.trans (Nat.mul_le_mul_right _ (hNp.trans hpq))) ω
      have h2 := stepM_grid W j H hpr (k := k) (hk.trans (Nat.mul_le_mul_right _ hNp)) ω
      simp only [hD]
      rw [h1, h2, dsum_sub]
    -- timing facts for the coefficient
    have htime : ∀ i, gpt p (i / 2 ^ (r - p)) ≤ gpt q (i / 2 ^ (r - q)) ∧
        gpt q (i / 2 ^ (r - q)) ≤ gpt r i ∧
        (gpt q (i / 2 ^ (r - q)) : ℝ) - gpt p (i / 2 ^ (r - p)) ≤ 1 / 2 ^ p := by
      intro i
      have hdv : 2 ^ (r - q) ∣ 2 ^ (r - p) := pow_dvd_pow 2 (by omega)
      have hle : i / 2 ^ (r - p) * 2 ^ (r - p) ≤ i / 2 ^ (r - q) * 2 ^ (r - q) :=
        div_mul_le_div_mul' (by positivity) hdv
      refine ⟨?_, ?_, ?_⟩
      · rw [gpt_lift hpr, gpt_lift hqr]; exact (gpt_le_iff _ _ _).2 hle
      · rw [gpt_lift hqr]; exact (gpt_le_iff _ _ _).2 (Nat.div_mul_le_self _ _)
      · rw [gpt_lift hpr, gpt_lift hqr, gpt_coe, gpt_coe]
        have hm1 : ((i / 2 ^ (r - q) * 2 ^ (r - q) : ℕ) : ℝ) ≤ i := by
          exact_mod_cast Nat.div_mul_le_self _ _
        have hm2 : (i : ℝ) < (i / 2 ^ (r - p) * 2 ^ (r - p) : ℕ) + 2 ^ (r - p) := by
          have h3 := Nat.div_add_mod' i (2 ^ (r - p))
          have h4 := Nat.mod_lt i (show 0 < 2 ^ (r - p) by positivity)
          have : i < i / 2 ^ (r - p) * 2 ^ (r - p) + 2 ^ (r - p) := by omega
          exact_mod_cast this
        have h2r : (2 : ℝ) ^ r = 2 ^ p * 2 ^ (r - p) := by
          rw [← pow_add, Nat.add_sub_cancel' hpr]
        rw [div_sub_div_same, div_le_div_iff₀ (by positivity) (by positivity), h2r]
        have : ((i / 2 ^ (r - q) * 2 ^ (r - q) : ℕ) : ℝ) - (i / 2 ^ (r - p) * 2 ^ (r - p) : ℕ)
            ≤ 2 ^ (r - p) := by push_cast at hm1 hm2 ⊢; linarith
        first | linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) p] | nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) p]
    have hφm : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) (gpt r i)] (φ i) := by
      intro i
      obtain ⟨h1, h2, -⟩ := htime i
      exact ((hHm _).mono (completedBrownianPast_mono P W _ h2) le_rfl).sub
        ((hHm _).mono (completedBrownianPast_mono P W _ (h1.trans h2)) le_rfl)
    have hφa : ∀ i, Measurable (φ i) := fun i => (hHa _).sub (hHa _)
    have hφK : ∀ i ω, |φ i ω| ≤ 2 * C := fun i ω => by
      calc |φ i ω| ≤ |H (gpt q (i / 2 ^ (r - q))) ω| + |H (gpt p (i / 2 ^ (r - p))) ω| :=
            abs_sub _ _
        _ ≤ 2 * C := by linarith [hC (gpt q (i / 2 ^ (r - q))) ω, hC (gpt p (i / 2 ^ (r - p))) ω]
    have hmax := dsum_max hW x₀ j r hφm hφa hφK (N * 2 ^ r) hlam
    rw [← hAeq] at hmax
    have hsum : ∑ i ∈ Finset.range (N * 2 ^ r), 2 * d * (hm r : ℝ) * ∫ ω, φ i ω ^ 2 ∂P ≤
        2 * d * N * β := by
      calc ∑ i ∈ Finset.range (N * 2 ^ r), 2 * d * (hm r : ℝ) * ∫ ω, φ i ω ^ 2 ∂P
          ≤ ∑ i ∈ Finset.range (N * 2 ^ r), 2 * d * (hm r : ℝ) * β := by
            refine Finset.sum_le_sum fun i hi => ?_
            refine mul_le_mul_of_nonneg_left ?_ (by rw [hm_coe]; positivity)
            obtain ⟨h1, h2, h3⟩ := htime i
            refine hβ _ _ h1 ?_ h3
            refine h2.trans ?_
            rw [← gpt_nat r N]
            exact (gpt_le_iff _ _ _).2 (Finset.mem_range.1 hi).le
        _ = 2 * d * N * β := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hm_coe]
            push_cast
            field_simp
    have := hmax.trans hsum
    rw [hBd, le_div_iff₀ (by positivity)]
    linarith
  have hall : ∀ r, P.real (A r) ≤ Bd := fun r =>
    (measureReal_mono (hAmono (le_max_left r q))).trans (hlev _ (le_max_right r q))
  -- the continuous-time event is inside the union of the grid events
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ⊆ ⋃ r, A r := by
    rintro ω ⟨t, htN, hlt⟩
    let kr : ℕ → ℕ := fun r => ⌊(t : ℝ) * 2 ^ r⌋₊
    have hconv : Tendsto (fun r => gpt r (kr r)) atTop (𝓝 t) := by
      rw [← NNReal.tendsto_coe]
      have hup : ∀ r, (gpt r (kr r) : ℝ) ≤ t := fun r => by
        rw [gpt_coe, div_le_iff₀ (by positivity)]
        exact Nat.floor_le (by positivity)
      have hlo : ∀ r, (t : ℝ) - 1 / 2 ^ r ≤ gpt r (kr r) := fun r => by
        rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div,
          inv_mul_cancel₀ (by positivity)]
        linarith [Nat.lt_floor_add_one ((t : ℝ) * 2 ^ r)]
      have hl : Tendsto (fun r : ℕ => (t : ℝ) - 1 / 2 ^ r) atTop (𝓝 t) := by
        have h0 : Tendsto (fun r : ℕ => (1 : ℝ) / 2 ^ r) atTop (𝓝 0) := by
          simpa [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        simpa using h0.const_sub (t : ℝ)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hup
    have hev := ((continuous_abs.comp (hDc ω)).tendsto t).comp hconv
    obtain ⟨r, hr⟩ := (hev.eventually (lt_mem_nhds hlt)).exists
    refine Set.mem_iUnion.2 ⟨r, kr r, ?_, hr.le⟩
    have : (t : ℝ) * 2 ^ r ≤ ((N * 2 ^ r : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htN) (by positivity)
    exact (Nat.floor_le_floor this).trans (by rw [Nat.floor_natCast])
  have hU : P (⋃ r, A r) ≤ ENNReal.ofReal Bd := by
    rw [hAmono.measure_iUnion]
    refine iSup_le fun r => ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hall r)
  have hS : P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ≤ Bd := by
    have h1 := (measure_mono hsub).trans hU
    have hB0 : 0 ≤ Bd := by rw [hBd]; positivity
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hB0 h1
  have := mul_le_mul_of_nonneg_left hS (sq_nonneg lam)
  rw [hBd, mul_div_cancel₀ _ (by positivity)] at this
  exact this

end QA
end ItoLib

end FlatM_QA
-- ===== QB =====
section FlatM_QB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QB
/-! lemma_3_1 toolkit, part QB: uniform `L²`-continuity of a bounded continuous integrand, and
the pathwise identification of `stepM q t` as the limit of `t`-grid Riemann sums whose
coefficients are the level-`q` left values (grid comparison, step 1). -/

theorem osc_L2 [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω)
    {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C) (N : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s u : ℝ≥0, s ≤ N → u ≤ N → |(u : ℝ) - s| < δ →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P < ε := by
  let F : ℝ≥0 × ℝ≥0 → ℝ := fun p => ∫ ω, (H p.2 ω - H p.1 ω) ^ 2 ∂P
  have hF : Continuous F := by
    refine continuous_of_dominated (bound := fun _ => (2 * C) ^ 2)
      (fun p => (((hHa p.2).sub (hHa p.1)).pow_const 2).aestronglyMeasurable)
      (fun p => ae_of_all _ fun ω => ?_) (integrable_const _) (ae_of_all _ fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |H p.2 ω - H p.1 ω| ≤ |H p.2 ω| + |H p.1 ω| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hC p.2 ω, hC p.1 ω]
    · exact (((hHc ω).comp continuous_snd).sub ((hHc ω).comp continuous_fst)).pow 2
  have hK : IsCompact (Set.Icc (0 : ℝ≥0) N ×ˢ Set.Icc (0 : ℝ≥0) N) :=
    isCompact_Icc.prod isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  refine ⟨δ, hδ, fun s u hs hu hsu => ?_⟩
  have hmem1 : (s, u) ∈ Set.Icc (0 : ℝ≥0) N ×ˢ Set.Icc (0 : ℝ≥0) N :=
    ⟨⟨by positivity, hs⟩, ⟨by positivity, hu⟩⟩
  have hmem2 : (s, s) ∈ Set.Icc (0 : ℝ≥0) N ×ˢ Set.Icc (0 : ℝ≥0) N :=
    ⟨⟨by positivity, hs⟩, ⟨by positivity, hs⟩⟩
  have hd : dist (s, u) (s, s) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, NNReal.dist_eq]; exact hsu
  have := hδ' _ hmem1 _ hmem2 hd
  have h0 : F (s, s) = 0 := by simp [F]
  rw [h0, Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

theorem sum_Ico_telescope (w : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (w (i + 1) - w i) = w b - w a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, ih]; ring

/-- Index of the first level-`r` point of the `t`-grid at or after `x`, capped at `2^r`. -/
noncomputable def idxT (t : ℝ≥0) (r : ℕ) (x : ℝ≥0) : ℕ := min (2 ^ r) ⌈(x : ℝ) * 2 ^ r / t⌉₊

theorem idxT_le (t : ℝ≥0) (r : ℕ) (x : ℝ≥0) : idxT t r x ≤ 2 ^ r := min_le_left _ _

theorem idxT_mono (t : ℝ≥0) (r : ℕ) {x y : ℝ≥0} (hxy : x ≤ y) : idxT t r x ≤ idxT t r y := by
  unfold idxT
  refine min_le_min le_rfl (Nat.ceil_mono ?_)
  have : (x : ℝ) ≤ y := hxy
  have ht : (0 : ℝ) ≤ t := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity)) ht

/-- For `i < 2^r`: `x ≤ i t / 2^r ↔ idxT x ≤ i`. -/
theorem le_grid_iff {t : ℝ≥0} (ht : 0 < (t : ℝ)) (r : ℕ) (x : ℝ≥0) {i : ℕ} (hi : i < 2 ^ r) :
    (x : ℝ) ≤ i * t / 2 ^ r ↔ idxT t r x ≤ i := by
  unfold idxT
  rw [min_le_iff, Nat.ceil_le, div_le_iff₀ ht]
  constructor
  · intro h; right
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · rintro (h | h)
    · omega
    · rw [le_div_iff₀ (by positivity)]; linarith

theorem floor_eq_iff_gpt {v : ℝ} (hv : 0 ≤ v) (q l : ℕ) :
    ⌊v * 2 ^ q⌋₊ = l ↔ (gpt q l : ℝ) ≤ v ∧ v < gpt q (l + 1) := by
  rw [Nat.floor_eq_iff (by positivity), gpt_coe, gpt_coe, div_le_iff₀ (by positivity),
    lt_div_iff₀ (by positivity)]
  push_cast; exact Iff.rfl

/-- Regrouping a `t`-grid Riemann sum with level-`q` left coefficients by level-`q` cells. -/
theorem regroup (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) {q : ℕ} (htq : (t : ℝ) ≤ q) (r : ℕ) (ω : Ω) :
    itoStepSum (fun s ω => W s ω j) t r
      (fun i ω => H (gpt q ⌊(i : ℝ) * t / 2 ^ r * 2 ^ q⌋₊) ω) ω =
    ∑ l ∈ Finset.range (q * 2 ^ q), H (gpt q l) ω *
      (W ((idxT t r (gpt q (l + 1)) : ℝ≥0) * t / (2 : ℝ≥0) ^ r) ω j -
        W ((idxT t r (gpt q l) : ℝ≥0) * t / (2 : ℝ≥0) ^ r) ω j) := by
  set w : ℕ → ℝ := fun i => W ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ r) ω j with hw
  have hstep : ∀ i : ℕ, W (((i : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ r) ω j = w (i + 1) := by
    intro i; simp only [hw]; push_cast; rfl
  set fl : ℕ → ℕ := fun i => ⌊(i : ℝ) * t / 2 ^ r * 2 ^ q⌋₊ with hfl
  have hvnn : ∀ i : ℕ, (0 : ℝ) ≤ (i : ℝ) * t / 2 ^ r := fun i => by positivity
  have hflt : ∀ i ∈ Finset.range (2 ^ r), fl i < q * 2 ^ q := by
    intro i hi
    have hi' : (i : ℝ) < 2 ^ r := by exact_mod_cast Finset.mem_range.1 hi
    have hv : (i : ℝ) * t / 2 ^ r < t := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    rw [hfl, Nat.floor_lt (by have := hvnn i; positivity)]
    push_cast
    first | linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) q] | nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) q]
  unfold itoStepSum
  simp only [hstep]
  have hc : ∀ i ∈ Finset.range (2 ^ r), H (gpt q (fl i)) ω =
      ∑ l ∈ Finset.range (q * 2 ^ q), if fl i = l then H (gpt q l) ω else 0 := by
    intro i hi
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (hflt i hi))]
  rw [Finset.sum_congr rfl fun i hi => by rw [hc i hi]]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  have hfil : (Finset.range (2 ^ r)).filter (fun i => fl i = l) =
      Finset.Ico (idxT t r (gpt q l)) (idxT t r (gpt q (l + 1))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hi, hfi⟩
      rw [hfl, floor_eq_iff_gpt (hvnn i)] at hfi
      refine ⟨(le_grid_iff ht r _ hi).1 hfi.1, ?_⟩
      by_contra hcon
      exact absurd ((le_grid_iff ht r _ hi).2 (not_lt.1 hcon)) (not_le.2 hfi.2)
    · rintro ⟨h1, h2⟩
      have hi : i < 2 ^ r := lt_of_lt_of_le h2 (idxT_le _ _ _)
      refine ⟨hi, ?_⟩
      rw [hfl, floor_eq_iff_gpt (hvnn i)]
      refine ⟨(le_grid_iff ht r _ hi).2 h1, ?_⟩
      by_contra hcon
      exact absurd ((le_grid_iff ht r _ hi).1 (not_lt.1 hcon)) (not_le.2 h2)
  rw [hfil, sum_Ico_telescope w (idxT_mono t r ((gpt_le_iff _ _ _).2 (Nat.le_succ l)))]

theorem idxT_tendsto {t : ℝ≥0} (ht : 0 < (t : ℝ)) (x : ℝ≥0) :
    Tendsto (fun r : ℕ => (idxT t r x : ℝ≥0) * t / (2 : ℝ≥0) ^ r) atTop (𝓝 (min x t)) := by
  rw [← NNReal.tendsto_coe]
  have hlo : ∀ r : ℕ, ((min x t : ℝ≥0) : ℝ) ≤ (((idxT t r x : ℝ≥0) * t / (2 : ℝ≥0) ^ r : ℝ≥0) : ℝ) := by
    intro r
    push_cast
    rw [le_div_iff₀ (by positivity)]
    unfold idxT
    rcases le_total (2 ^ r) ⌈(x : ℝ) * 2 ^ r / t⌉₊ with h | h
    · rw [min_eq_left h]; push_cast
      have : min (x : ℝ) t ≤ t := min_le_right _ _
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
    · rw [min_eq_right h]
      have h1 := Nat.le_ceil ((x : ℝ) * 2 ^ r / t)
      rw [div_le_iff₀ ht] at h1
      have : min (x : ℝ) t ≤ x := min_le_left _ _
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
  have hhi : ∀ r : ℕ, (((idxT t r x : ℝ≥0) * t / (2 : ℝ≥0) ^ r : ℝ≥0) : ℝ) ≤
      ((min x t : ℝ≥0) : ℝ) + t / 2 ^ r := by
    intro r
    push_cast
    have hA : (idxT t r x : ℝ) * t / 2 ^ r ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      have : (idxT t r x : ℝ) ≤ 2 ^ r := by exact_mod_cast idxT_le t r x
      nlinarith
    have hB : (idxT t r x : ℝ) * t / 2 ^ r ≤ x + t / 2 ^ r := by
      have : (idxT t r x : ℝ) < (x : ℝ) * 2 ^ r / t + 1 := by
        unfold idxT
        calc ((min (2 ^ r) ⌈(x : ℝ) * 2 ^ r / t⌉₊ : ℕ) : ℝ) ≤ (⌈(x : ℝ) * 2 ^ r / t⌉₊ : ℝ) := by
              exact_mod_cast min_le_right _ _
          _ < _ := Nat.ceil_lt_add_one (by positivity)
      have h' : (idxT t r x : ℝ) * t < x * 2 ^ r + t := by
        have := mul_lt_mul_of_pos_right this ht
        rwa [add_mul, div_mul_cancel₀ _ ht.ne', one_mul] at this
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      linarith
    rcases le_total x t with hxt | hxt
    · rw [min_eq_left (show (x : ℝ) ≤ t by exact_mod_cast hxt)]; exact hB
    · rw [min_eq_right (show (t : ℝ) ≤ x by exact_mod_cast hxt)]; linarith [div_nonneg ht.le (show (0:ℝ) ≤ 2 ^ r by positivity)]
  have hl : Tendsto (fun r : ℕ => ((min x t : ℝ≥0) : ℝ) + t / 2 ^ r) atTop
      (𝓝 ((min x t : ℝ≥0) : ℝ)) := by
    have h0 : Tendsto (fun r : ℕ => (t : ℝ) / 2 ^ r) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (t : ℝ)
      simpa [div_eq_mul_inv, one_div_pow] using this
    simpa using h0.const_add ((min x t : ℝ≥0) : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl hlo hhi

/-- Grid comparison, pathwise part: the `t`-grid sums with level-`q` left coefficients converge
to `stepM q t` as the `t`-grid is refined. -/
theorem regroup_tendsto {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} (ht : 0 < (t : ℝ)) {q : ℕ} (htq : (t : ℝ) ≤ q)
    (ω : Ω) :
    Tendsto (fun r => itoStepSum (fun s ω => W s ω j) t r
      (fun i ω => H (gpt q ⌊(i : ℝ) * t / 2 ^ r * 2 ^ q⌋₊) ω) ω) atTop
      (𝓝 (stepM W j H q t ω)) := by
  simp only [regroup W j H ht htq]
  unfold stepM
  refine tendsto_finset_sum _ fun l _ => tendsto_const_nhds.mul ?_
  have hWj : Continuous fun s => W s ω j :=
    (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp (hWc ω))
  exact ((hWj.tendsto _).comp (idxT_tendsto ht _)).sub ((hWj.tendsto _).comp (idxT_tendsto ht _))

end QB
end ItoLib

end FlatM_QB
-- ===== QC =====
section FlatM_QC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QC
/-! lemma_3_1 toolkit, part QC: grid comparison in `L²` and `stepM q t → J t` in probability
for every fixed `t` (bounded continuous adapted integrand). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

theorem stepM_measurable (hW : IsStandardBrownian P W) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHa : ∀ s, Measurable (H s)) (q : ℕ) (t : ℝ≥0) : Measurable (stepM W j H q t) := by
  unfold stepM
  exact Finset.measurable_sum _ fun l _ => (hHa _).mul
    ((stdBrownian_coord_measurable hW _ j).sub (stdBrownian_coord_measurable hW _ j))

theorem itoStepSum_measurable' (hW : IsStandardBrownian P W) (j : Fin d) (t : ℝ≥0) (n : ℕ)
    {a : ℕ → Ω → ℝ} (ha : ∀ k, Measurable (a k)) :
    Measurable (itoStepSum (fun s ω => W s ω j) t n a) := by
  unfold itoStepSum
  exact Finset.measurable_sum _ fun l _ => (ha _).mul
    ((stdBrownian_coord_measurable hW _ j).sub (stdBrownian_coord_measurable hW _ j))

/-- `L²` grid comparison: `stepM q t` versus the `t`-grid left sum of level `q`. -/
theorem stepM_S_lint (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) {q : ℕ} (htq : (t : ℝ) ≤ q) (hCq : C ≤ q) {β : ℝ}
    (hβ : ∀ s u : ℝ≥0, s ≤ t → u ≤ t → |(u : ℝ) - s| ≤ (1 + t) / 2 ^ q →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ β) :
    ∫⁻ ω, ENNReal.ofReal ((stepM W j H q t ω -
      itoStepSum (fun s ω => W s ω j) t q (leftCoef (clampH H q) t q) ω) ^ 2) ∂P ≤
      ENNReal.ofReal (t * β) := by
  set S : Ω → ℝ := itoStepSum (fun s ω => W s ω j) t q (leftCoef (clampH H q) t q) with hS
  -- level-(q+m) coefficients
  let c : ℕ → ℕ → Ω → ℝ := fun m i ω => H (gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊) ω
  let a : ℕ → ℕ → Ω → ℝ := fun m i ω => leftCoef (clampH H q) t q (i / 2 ^ m) ω
  let R : ℕ → Ω → ℝ := fun m => itoStepSum (fun s ω => W s ω j) t (q + m) (c m)
  have hlim : ∀ ω, Tendsto (fun m => R m ω) atTop (𝓝 (stepM W j H q t ω)) := by
    intro ω
    have h1 := regroup_tendsto hW.2.1 j H ht htq ω
    have h2 : Tendsto (fun m : ℕ => q + m) atTop atTop := by
      simpa [add_comm] using tendsto_add_atTop_nat q
    exact h1.comp h2
  have hSref : ∀ m ω, S ω = itoStepSum (fun s ω => W s ω j) t (q + m) (a m) ω := fun m ω =>
    itoStepSum_refine _ t q m _ ω
  -- times of the coefficients
  have hcpt : ∀ m i : ℕ, gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊ ≤
      (i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) := by
    intro m i
    rw [← NNReal.coe_le_coe, gpt_coe, div_le_iff₀ (by positivity)]
    push_cast
    exact Nat.floor_le (by positivity)
  have hcpt2 : ∀ m i : ℕ, ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ) - 1 / 2 ^ q ≤
      gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊ := by
    intro m i
    rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div, inv_mul_cancel₀ (by positivity)]
    push_cast
    linarith [Nat.lt_floor_add_one ((i : ℝ) * t / 2 ^ (q + m) * 2 ^ q)]
  have hdiff : ∀ m ω, R m ω - S ω =
      itoStepSum (fun s ω => W s ω j) t (q + m) (fun i ω => c m i ω - a m i ω) ω := by
    intro m ω; rw [hSref m ω]; exact itoStepSum_sub _ _ _ _ _ ω
  have hem : ∀ m, ∀ i : ℕ, i < 2 ^ (q + m) → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m))] (fun ω => c m i ω - a m i ω) := by
    intro m i _
    refine ((hHm _).mono (completedBrownianPast_mono P W _ (hcpt m i)) le_rfl).sub ?_
    exact (clampH_measurable (hHm _) _).mono
      (completedBrownianPast_mono P W _ (dyTime_coarse t q m i).1) le_rfl
  have heK : ∀ m, ∀ i : ℕ, i < 2 ^ (q + m) → ∀ ω, |c m i ω - a m i ω| ≤ 2 * C := by
    intro m i _ ω
    have h1 := hC (gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊) ω
    have h2 : |a m i ω| ≤ C :=
      (abs_clampH_le_abs H (Nat.cast_nonneg q) _ ω).trans (hC _ ω)
    calc |c m i ω - a m i ω| ≤ |c m i ω| + |a m i ω| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hbnd : ∀ m, ∫ ω, (R m ω - S ω) ^ 2 ∂P ≤ t * β := by
    intro m
    simp_rw [hdiff m]
    rw [itoStepSum_isometry hW x₀ t (q + m) j _ (hem m) (2 * C) (heK m)]
    have hterm : ∀ i ∈ Finset.range (2 ^ (q + m)), ∫ ω, (c m i ω - a m i ω) ^ 2 ∂P ≤ β := by
      intro i hi
      set u := gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊ with hu
      set s := dyTime t q (i / 2 ^ m) with hs
      have hv : ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) ≤ t := by
        have := dyTime_le t (N := q + m) (j := i) (Finset.mem_range.1 hi).le
        exact this
      have hsv := (dyTime_coarse t q m i)
      have hus : |(u : ℝ) - s| ≤ (1 + t) / 2 ^ q := by
        have e1 : (u : ℝ) ≤ ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) := hcpt m i
        have e2 := hcpt2 m i
        have e3 : (s : ℝ) ≤ ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) :=
          NNReal.coe_le_coe.2 hsv.1
        have e4 : ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) - (s : ℝ) ≤ t / 2 ^ q := hsv.2
        push_cast at e1 e2 e3 e4
        rw [abs_le, add_div]
        have h0 : (0 : ℝ) ≤ t / 2 ^ q := by positivity
        have h0' : (0 : ℝ) ≤ 1 / 2 ^ q := by positivity
        constructor <;> linarith
      have hcl : ∀ ω, a m i ω = H s ω := fun ω => by
        simp only [a, leftCoef]
        exact clampH_eq_of_abs_le H ((hC _ ω).trans hCq)
      have := hβ s u (dyTime_le t (Nat.div_le_of_le_mul (by
          have := (Finset.mem_range.1 hi).le; rw [pow_add] at this; linarith))) ((hcpt m i).trans hv) hus
      simpa [c, hcl] using this
    calc ∑ i ∈ Finset.range (2 ^ (q + m)), (∫ ω, (c m i ω - a m i ω) ^ 2 ∂P) *
          (((t / (2 : ℝ≥0) ^ (q + m)) : ℝ≥0) : ℝ)
        ≤ ∑ i ∈ Finset.range (2 ^ (q + m)), β * (((t / (2 : ℝ≥0) ^ (q + m)) : ℝ≥0) : ℝ) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hterm i hi) (by positivity)
      _ = t * β := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
  -- Fatou
  have hRm : ∀ m, Measurable (R m) := fun m =>
    itoStepSum_measurable' hW j t _ fun i => hHa _
  have hSm : Measurable S := itoStepSum_measurable' hW j t q fun i => clampH_measurable (hHa _) _
  have hfat := lintegral_liminf_le' (μ := P) (u := atTop)
    (f := fun m ω => ENNReal.ofReal ((R m ω - S ω) ^ 2))
    (fun m => (ENNReal.measurable_ofReal.comp (((hRm m).sub hSm).pow_const 2)).aemeasurable)
  have hpt : ∀ ω, liminf (fun m => ENNReal.ofReal ((R m ω - S ω) ^ 2)) atTop =
      ENNReal.ofReal ((stepM W j H q t ω - S ω) ^ 2) := by
    intro ω
    have : Tendsto (fun m => ENNReal.ofReal ((R m ω - S ω) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((stepM W j H q t ω - S ω) ^ 2))) :=
      ENNReal.tendsto_ofReal (((hlim ω).sub tendsto_const_nhds).pow 2)
    exact this.liminf_eq
  simp only [hpt] at hfat
  refine hfat.trans (liminf_le_of_frequently_le' (Eventually.frequently
    (Eventually.of_forall fun m => ?_)))
  have hint : Integrable (fun ω => (R m ω - S ω) ^ 2) P := by
    have := (itoStepSum_memLp hW t (q + m) j (fun i ω => c m i ω - a m i ω)
      (fun i _ => ((hHa _).sub (clampH_measurable (hHa _) _)).aestronglyMeasurable)
      (2 * C) (heK m)).integrable_sq
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [hdiff m ω]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hbnd m)

/-- For a bounded continuous adapted integrand, the horizon-free step integrals converge in
probability to the Ito integral at every fixed time. -/
theorem stepM_tendsto (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    TendstoInMeasure P (fun q => stepM W j H q t) atTop (J t) := by
  have hS := clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ t
  set S : ℕ → Ω → ℝ := fun q =>
    itoStepSum (fun s ω => W s ω j) t q (leftCoef (clampH H q) t q) with hSdef
  rcases (NNReal.coe_nonneg t).eq_or_lt with h0 | hpos
  · have ht0 : t = 0 := NNReal.coe_eq_zero.1 h0.symm
    subst ht0
    refine hS.congr_left (fun q => ae_of_all _ fun ω => ?_)
    rw [stepM_zero]; simp [hSdef, itoStepSum]
  have hX : TendstoInMeasure P (fun q ω => stepM W j H q t ω - S q ω) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    rcases eq_or_ne e ⊤ with rfl | hetop
    · exact Eventually.of_forall fun _ => le_top
    set η := e.toReal with hηdef
    have hη : 0 < η := ENNReal.toReal_pos he.ne' hetop
    set β := η * ε ^ 2 / (t + 1) with hβdef
    have hβ : 0 < β := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := osc_L2 (P := P) hHa hHc hC t hβ
    have ev1 : ∀ᶠ q : ℕ in atTop, ((1 : ℝ) + t) / 2 ^ q < δ := by
      have h0 : Tendsto (fun q : ℕ => ((1 : ℝ) + t) / 2 ^ q) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((1 : ℝ) + t)
        simpa [div_eq_mul_inv, one_div_pow] using this
      exact h0.eventually (gt_mem_nhds hδ)
    have ev2 : ∀ᶠ q : ℕ in atTop, (t : ℝ) ≤ q ∧ C ≤ q := by
      obtain ⟨n, hn⟩ := exists_nat_ge (max (t : ℝ) C)
      filter_upwards [eventually_ge_atTop n] with q hq
      have : (n : ℝ) ≤ q := by exact_mod_cast hq
      exact ⟨by linarith [le_max_left (t : ℝ) C], by linarith [le_max_right (t : ℝ) C]⟩
    filter_upwards [ev1, ev2] with q hq1 hq2
    obtain ⟨htq, hCq⟩ := hq2
    have hb := stepM_S_lint hW x₀ j hHm hHa hC hpos htq hCq (β := β)
      (fun s u hs hu hsu => (hδ' s u hs hu (lt_of_le_of_lt hsu hq1)).le)
    have hSm : Measurable (S q) := itoStepSum_measurable' hW j t q fun i => clampH_measurable (hHa _) _
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal ((stepM W j H q t ω - S q ω) ^ 2)) P :=
      (ENNReal.measurable_ofReal.comp
        (((stepM_measurable hW j hHa q t).sub hSm).pow_const 2)).aemeasurable
    refine le_trans (measure_mono (t := {ω | ENNReal.ofReal (ε ^ 2) ≤
      ENNReal.ofReal ((stepM W j H q t ω - S q ω) ^ 2)}) ?_) ?_
    · intro ω hω
      simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow_le_pow_left₀ hε.le hω 2
      rwa [sq_abs] at this
    · refine (meas_ge_le_lintegral_div hmeas (ENNReal.ofReal_pos.2 (by positivity)).ne'
        ENNReal.ofReal_ne_top).trans ?_
      calc (∫⁻ ω, ENNReal.ofReal ((stepM W j H q t ω - S q ω) ^ 2) ∂P) / ENNReal.ofReal (ε ^ 2)
          ≤ ENNReal.ofReal (t * β) / ENNReal.ofReal (ε ^ 2) := ENNReal.div_le_div_right hb _
        _ = ENNReal.ofReal (t * β / ε ^ 2) := (ENNReal.ofReal_div_of_pos (by positivity)).symm
        _ ≤ ENNReal.ofReal η := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [div_le_iff₀ (by positivity), hβdef]
            have ht1 : (0 : ℝ) < t + 1 := by positivity
            rw [mul_div_assoc', div_le_iff₀ ht1]
            first | linarith [mul_pos hη (pow_pos hε 2)] | nlinarith [mul_pos hη (pow_pos hε 2)]
        _ = e := ENNReal.ofReal_toReal hetop
  rw [tendstoInMeasure_real_iff_sub]
  have h2 := tendstoInMeasure_real_iff_sub.1 hS
  have h3 := tendstoInMeasure_add_real hX h2
  have h4 : (fun _ : Ω => (0 : ℝ) + 0) = fun _ => 0 := by simp
  rw [h4] at h3
  refine TendstoInMeasure.congr_left (fun q => ae_of_all _ fun ω => ?_) h3
  simp only [hSdef]
  ring

end QC
end ItoLib

end FlatM_QC
-- ===== QD =====
section FlatM_QD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

/-- **Continuous version of the Ito integral** of a bounded continuous adapted integrand. -/
theorem contIto_bdd (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C) :
    ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
      (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Jc t)) ∧
      (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H Jc := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).2.2.1 j H hHm hHa hHc C hC
end QD

end ItoLib

end FlatM_QD
-- ===== Q =====
section FlatM_Q
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10k
/-! M10k (b10 calculus): the cubic negative part `φ(v) = (v⁻)³` (C², `v φ' = 3φ`, `v² φ'' = 6φ`)
and the orthant test function `Hf r u = e^{-a} χ_r(|x|²) Σ_k φ(x_k)`. -/

variable {d : ℕ}

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

theorem scol_apply' (s : SDEDiffusion d) (j k : Fin d) : scol s j k = s (k, j) := rfl

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

end FlatM_Q
-- ===== R =====
section FlatM_R
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10n
/-! M10n (b10 expectation and Markov step): `E Hf_r(X_t, A_t) ≤ Hf_r(x₀) + B/M`, and
`P{X stays in B̄_R on [0,t], ε < Φ(X_t)} ≤ (Hf_r(x₀) + B/M) / (e^{-ct} ε)`. -/
variable {Ω : Type*} {d : ℕ}

end M10n

end ItoLib

end FlatM_R
-- ===== S =====
section FlatM_S
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10o
/-! M10o (b10 done): orthant invariance of the Kolmogorov solutions, and the Markov statement. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M10o

end ItoLib

end FlatM_S
-- ===== U =====
section FlatM_U
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal := by
  have hs : DenseRange Real.toNNReal := Function.Surjective.denseRange fun x =>
    ⟨(x : ℝ), Real.toNNReal_coe⟩
  exact hs.comp Rat.denseRange_cast continuous_real_toNNReal

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M11b

end ItoLib

end FlatM_U
-- ===== QE =====
section FlatM_QE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QEneg
variable {Ω : Type*} [MeasurableSpace Ω]

end QEneg

section QEF

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

theorem integral_sum_cont {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i, Continuous (f i))
    (a b : ℝ) : ∑ i ∈ s, ∫ u in a..b, f i u = ∫ u in a..b, ∑ i ∈ s, f i u :=
  (intervalIntegral.integral_finset_sum fun i _ => (hf i).intervalIntegrable a b).symm

theorem integral_sum3 {a b c : ℕ} (F : Fin a → Fin b → Fin c → ℝ → ℝ)
    (hF : ∀ i k l, Continuous (F i k l)) (α β : ℝ) :
    ∑ i, ∑ k, ∑ l, ∫ u in α..β, F i k l u = ∫ u in α..β, ∑ i, ∑ k, ∑ l, F i k l u := by
  have h1 : ∀ i k, ∑ l, ∫ u in α..β, F i k l u = ∫ u in α..β, ∑ l, F i k l u :=
    fun i k => integral_sum_cont _ (hF i k) α β
  have h2 : ∀ i, ∑ k, ∫ u in α..β, ∑ l, F i k l u = ∫ u in α..β, ∑ k, ∑ l, F i k l u :=
    fun i => integral_sum_cont (f := fun k u => ∑ l, F i k l u) _
      (fun k => continuous_finset_sum _ fun l _ => hF i k l) α β
  have h3 : ∑ i, ∫ u in α..β, ∑ k, ∑ l, F i k l u = ∫ u in α..β, ∑ i, ∑ k, ∑ l, F i k l u :=
    integral_sum_cont (f := fun i u => ∑ k, ∑ l, F i k l u) _
      (fun i => continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ => hF i k l) α β
  simp only [h1, h2]
  exact h3

end QEface

end ItoLib

end FlatM_QE
-- ===== QF =====
section FlatM_QF
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QFgen
/-! Generic test function `F(x,y,a) = e^{-a} G(y)` along `(X, Y, A)`. -/
variable {d : ℕ}

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

end QFgenL

end ItoLib

end FlatM_QF
-- ===== QG =====
section FlatM_QG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section QG
/-! Clause 4b (3.6) of Lemma 3.1: `E V^δ₀(X_t) ≤ e^{δ₀ H t} V^δ₀(x)`. -/
variable {n : ℕ}

end QG

end ItoLib

end FlatM_QG
-- ===== QH =====
section FlatM_QH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QH

end ItoLib

end FlatM_QH
-- ===== QI =====
section FlatM_QI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QI
end ItoLib

end FlatM_QI
-- ===== HK =====
section FlatM_HK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section HK
/-! 7ade6a3f K3ito toolkit: uniform-in-time convergence in probability of the step integrals
`stepM` to a continuous version of the Ito integral, first for bounded, then (by localisation)
for unbounded continuous adapted integrands. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem gpt_floor_le (t : ℝ≥0) (r : ℕ) : gpt r ⌊(t : ℝ) * 2 ^ r⌋₊ ≤ t := by
  rw [← NNReal.coe_le_coe, gpt_coe, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem gpt_floor_tendsto (t : ℝ≥0) :
    Tendsto (fun r => gpt r ⌊(t : ℝ) * 2 ^ r⌋₊) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hup : ∀ r, (gpt r ⌊(t : ℝ) * 2 ^ r⌋₊ : ℝ) ≤ t := fun r => by
    exact_mod_cast gpt_floor_le t r
  have hlo : ∀ r, (t : ℝ) - 1 / 2 ^ r ≤ gpt r ⌊(t : ℝ) * 2 ^ r⌋₊ := fun r => by
    rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div,
      inv_mul_cancel₀ (by positivity)]
    linarith [Nat.lt_floor_add_one ((t : ℝ) * 2 ^ r)]
  have hl : Tendsto (fun r : ℕ => (t : ℝ) - 1 / 2 ^ r) atTop (𝓝 t) := by
    have h0 : Tendsto (fun r : ℕ => (1 : ℝ) / 2 ^ r) atTop (𝓝 0) := by
      simpa [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h0.const_sub (t : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hup

theorem gpt_le_nat {r k N : ℕ} (hk : k ≤ N * 2 ^ r) : gpt r k ≤ (N : ℝ≥0) := by
  rw [← NNReal.coe_le_coe, gpt_coe, div_le_iff₀ (by positivity)]
  push_cast
  exact_mod_cast hk

theorem bound_of_grid {f : ℝ≥0 → ℝ} (hf : Continuous f) {N : ℝ≥0} {R : ℝ}
    (h : ∀ m l : ℕ, gpt m l ≤ N → |f (gpt m l)| ≤ R) : ∀ s ≤ N, |f s| ≤ R := by
  intro s hs
  have ht := ((continuous_abs.comp hf).tendsto s).comp (gpt_floor_tendsto s)
  exact le_of_tendsto ht (Eventually.of_forall fun r =>
    h r _ ((gpt_floor_le s r).trans hs))

theorem stepM_congr_le (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) {H H' : ℝ≥0 → Ω → ℝ}
    (q : ℕ) {t : ℝ≥0} {ω : Ω} (h : ∀ s ≤ t, H s ω = H' s ω) :
    stepM W j H q t ω = stepM W j H' q t ω := by
  unfold stepM
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : gpt q l ≤ t
  · rw [h _ hl]
  · push_neg at hl
    have h1 : gpt q l ≤ gpt q (l + 1) := (gpt_le_iff q l (l + 1)).2 (Nat.le_succ l)
    rw [min_eq_right (hl.le.trans h1), min_eq_right hl.le]
    simp

/-- Maximal inequality for `J − stepM p` (bounded continuous integrand). -/
theorem jc_stepM_max {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJc : ∀ ω, Continuous fun t => J t ω)
    {N p : ℕ} (hNp : N ≤ p) {β : ℝ}
    (hβ : ∀ s u : ℝ≥0, s ≤ u → u ≤ N → (u : ℝ) - s ≤ 1 / 2 ^ p →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ β) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω - stepM W j H p t ω|} ≤
      2 * d * N * β := by
  have hβ0 : 0 ≤ β := le_trans (integral_nonneg fun ω => sq_nonneg _)
    (hβ 0 0 le_rfl (by simp) (by simp))
  set D : ℝ≥0 → Ω → ℝ := fun t ω => J t ω - stepM W j H p t ω with hD
  have hDc : ∀ ω, Continuous fun t => D t ω := fun ω =>
    (hJc ω).sub (stepM_continuous hW.2.1 j H p ω)
  set S : ℕ → ℝ≥0 → Ω → ℝ := fun q t ω => stepM W j H q t ω - stepM W j H p t ω with hS
  have hconv : ∀ t, TendstoInMeasure P (fun q => S q t) atTop (D t) := by
    intro t
    have hc : TendstoInMeasure P (fun (_ : ℕ) => stepM W j H p t) atTop (stepM W j H p t) :=
      tendstoInMeasure_of_tendsto_ae
        (fun _ => (stepM_measurable hW j hHa p t).aestronglyMeasurable)
        (ae_of_all _ fun ω => tendsto_const_nhds)
    exact tendstoInMeasure_sub_real (stepM_tendsto hW x₀ j hHm hHa hHc hC hJ t) hc
  let A : ℕ → Set Ω := fun r => {ω | ∃ k ≤ N * 2 ^ r, lam < |D (gpt r k) ω|}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun r ω hω => ?_
    obtain ⟨k, hk, hl⟩ := hω
    refine ⟨k * 2 ^ (r + 1 - r), ?_, ?_⟩
    · have h2 : 2 ^ (r + 1 - r) = 2 := by simp
      rw [h2, pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_right 2 hk
    · rwa [← gpt_lift (Nat.le_succ r)]
  have hlev : ∀ r, ∀ lam' : ℝ, 0 < lam' → lam' < lam →
      P (A r) ≤ ENNReal.ofReal (2 * d * N * β / lam' ^ 2) := by
    intro r lam' hl0 hll
    set Bd' : ℝ := 2 * d * N * β / lam' ^ 2 with hBd'
    set E : ℕ → ℕ → Set Ω := fun q k =>
      {ω | lam - lam' ≤ dist (S q (gpt r k) ω) (D (gpt r k) ω)} with hE
    have hEt : ∀ k, Tendsto (fun q => P (E q k)) atTop (𝓝 0) := fun k =>
      tendstoInMeasure_iff_dist.1 (hconv (gpt r k)) (lam - lam') (by linarith)
    have hsumt : Tendsto (fun q => ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k)) atTop
        (𝓝 0) := by
      simpa using tendsto_finset_sum (Finset.range (N * 2 ^ r + 1)) fun k _ => hEt k
    have hle : ∀ q, max p r ≤ q →
        P (A r) ≤ ENNReal.ofReal Bd' + ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k) := by
      intro q hq
      have hpq : p ≤ q := (le_max_left _ _).trans hq
      have hrq : r ≤ q := (le_max_right _ _).trans hq
      set Gq : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ N ∧
        lam' < |stepM W j H q t ω - stepM W j H p t ω|} with hGq
      have hGqb : P Gq ≤ ENNReal.ofReal Bd' := by
        have h := stepM_sup_max hW x₀ j hHm hHa hC hNp hpq hβ hl0
        rw [← ofReal_measureReal (measure_ne_top P _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hBd', le_div_iff₀ (by positivity)]
        linarith
      have hsub : A r ⊆ Gq ∪ ⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k := by
        rintro ω ⟨k, hk, hlt⟩
        by_cases hEk : ω ∈ E q k
        · exact Or.inr (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hEk)
        · left
          simp only [hE, Set.mem_setOf_eq, not_le, Real.dist_eq] at hEk
          refine ⟨gpt r k, gpt_le_nat hk, ?_⟩
          have h1 : |D (gpt r k) ω| ≤ |S q (gpt r k) ω| + |S q (gpt r k) ω - D (gpt r k) ω| := by
            have h0 := abs_sub_abs_le_abs_sub (D (gpt r k) ω) (S q (gpt r k) ω)
            have h0' := abs_sub_comm (D (gpt r k) ω) (S q (gpt r k) ω)
            linarith
          have : lam' < |S q (gpt r k) ω| := by linarith
          simpa [hS] using this
      calc P (A r) ≤ P (Gq ∪ ⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k) := measure_mono hsub
        _ ≤ P Gq + P (⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k) := measure_union_le _ _
        _ ≤ ENNReal.ofReal Bd' + ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k) :=
            add_le_add hGqb (measure_biUnion_finset_le _ _)
    have hlim : Tendsto (fun q => ENNReal.ofReal Bd' +
        ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k)) atTop (𝓝 (ENNReal.ofReal Bd' + 0)) :=
      tendsto_const_nhds.add hsumt
    rw [add_zero] at hlim
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨max p r, hle⟩)
  have hlevR : ∀ r, lam ^ 2 * P.real (A r) ≤ 2 * d * N * β := by
    intro r
    have hev : ∀ᶠ l in 𝓝[<] lam, l ^ 2 * P.real (A r) ≤ 2 * d * N * β := by
      filter_upwards [Ioo_mem_nhdsLT hlam] with l hl
      have h := hlev r l hl.1 hl.2
      have h2 : P.real (A r) ≤ 2 * d * N * β / l ^ 2 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (by have := hl.1; positivity) h
      rw [le_div_iff₀ (by have := hl.1; positivity)] at h2
      linarith
    have ht : Tendsto (fun l : ℝ => l ^ 2 * P.real (A r)) (𝓝[<] lam)
        (𝓝 (lam ^ 2 * P.real (A r))) :=
      ((continuous_pow 2).mul continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto ht hev
  set Bd : ℝ := 2 * d * N * β / lam ^ 2 with hBd
  have hall : ∀ r, P.real (A r) ≤ Bd := fun r => by
    rw [hBd, le_div_iff₀ (by positivity)]; linarith [hlevR r]
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ⊆ ⋃ r, A r := by
    rintro ω ⟨t, htN, hlt⟩
    have hev := ((continuous_abs.comp (hDc ω)).tendsto t).comp (gpt_floor_tendsto t)
    obtain ⟨r, hr⟩ := (hev.eventually (lt_mem_nhds hlt)).exists
    refine Set.mem_iUnion.2 ⟨r, ⌊(t : ℝ) * 2 ^ r⌋₊, ?_, hr⟩
    have : (t : ℝ) * 2 ^ r ≤ ((N * 2 ^ r : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htN) (by positivity)
    exact (Nat.floor_le_floor this).trans (by rw [Nat.floor_natCast])
  have hU : P (⋃ r, A r) ≤ ENNReal.ofReal Bd := by
    rw [hAmono.measure_iUnion]
    refine iSup_le fun r => ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hall r)
  have hS' : P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ≤ Bd := by
    have h1 := (measure_mono hsub).trans hU
    have hB0 : 0 ≤ Bd := by rw [hBd]; positivity
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hB0 h1
  have := mul_le_mul_of_nonneg_left hS' (sq_nonneg lam)
  rw [hBd, mul_div_cancel₀ _ (by positivity)] at this
  exact this

/-- Bounded case: `stepM p` converges to the continuous version uniformly on `[0, N]`, in
probability. -/
theorem stepM_unif_bdd {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJc : ∀ ω, Continuous fun t => J t ω) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun p => P {ω | ∃ t : ℝ≥0, t ≤ N ∧ ε < |stepM W j H p t ω - J t ω|})
      atTop (𝓝 0) := by
  set S : ℕ → Set Ω := fun p => {ω | ∃ t : ℝ≥0, t ≤ N ∧ ε < |stepM W j H p t ω - J t ω|}
    with hSdef
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ p in atTop, P.real (S p) ≤ δ := by
    intro δ hδ
    set η : ℝ := δ * ε ^ 2 / (2 * d * N + 1) with hη
    have hηpos : 0 < η := by positivity
    obtain ⟨δ₀, hδ₀, hosc⟩ := osc_L2 (P := P) hHa hHc hC (N : ℝ≥0) hηpos
    obtain ⟨p₀, hp₀⟩ := exists_pow_lt_of_lt_one hδ₀ (by norm_num : (1 / 2 : ℝ) < 1)
    refine eventually_atTop.2 ⟨max N p₀, fun p hp => ?_⟩
    have hβ : ∀ s u : ℝ≥0, s ≤ u → u ≤ N → (u : ℝ) - s ≤ 1 / 2 ^ p →
        ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ η := by
      intro s u hsu huN hd
      refine (hosc s u (hsu.trans huN) huN ?_).le
      rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hsu))]
      calc (u : ℝ) - s ≤ 1 / 2 ^ p := hd
        _ = (1 / 2 : ℝ) ^ p := by rw [one_div_pow]
        _ ≤ (1 / 2 : ℝ) ^ p₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num)
            ((le_max_right _ _).trans hp)
        _ < δ₀ := hp₀
    have h := jc_stepM_max hW x₀ j hHm hHa hHc hC hJ hJc ((le_max_left _ _).trans hp) hβ hε
    have hset : S p = {ω | ∃ t : ℝ≥0, t ≤ N ∧ ε < |J t ω - stepM W j H p t ω|} := by
      ext ω
      simp only [hSdef, Set.mem_setOf_eq, abs_sub_comm]
    rw [hset]
    have h1 : 2 * (d : ℝ) * N * η ≤ δ * ε ^ 2 := by
      rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      have hp := mul_pos hδ (pow_pos hε 2)
      nlinarith
    exact le_of_mul_le_mul_left ((h.trans h1).trans_eq (mul_comm _ _)) (pow_pos hε 2)
  have hreal : Tendsto (fun p => P.real (S p)) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun p =>
      lt_of_lt_of_le ha measureReal_nonneg, fun a ha => ?_⟩
    exact (key (a / 2) (by linarith)).mono fun p hp => by linarith
  have := (ENNReal.tendsto_toReal_iff (fun p => measure_ne_top P (S p))
    ENNReal.zero_ne_top).1 (by simpa [measureReal_def] using hreal)
  exact this

/-- Unbounded continuous adapted integrand: a continuous adapted version `L` of the Ito integral
(continuous for every `ω`), and `stepM q H → L` uniformly on `[0, N]` in probability. -/
theorem contIto_unbdd {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ L : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => L t ω) ∧
      (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (L t)) ∧
      (∀ t, Measurable (L t)) ∧ (∀ ω, L 0 ω = 0) ∧
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H L ∧
      ∀ (N : ℕ) (ε : ℝ), 0 < ε → Tendsto (fun q => P {ω | ∃ t : ℝ≥0, t ≤ N ∧
        ε < |stepM W j H q t ω - L t ω|}) atTop (𝓝 0) := by
  classical
  have hJ := fun R : ℕ => contIto_bdd hW x₀ j (H := clampH H (R : ℝ))
    (fun s => clampH_measurable (hHm s) R) (fun s => clampH_measurable (hHa s) R)
    (clampH_continuous hHc R) (abs_clampH_le H (Nat.cast_nonneg R))
  choose Jc hJcc hJca hJcm hJc0 hJcI using hJ
  set A : ℕ → ℕ → Set Ω := fun N R => {ω | ∀ s : ℝ≥0, s ≤ N → |H s ω| ≤ R} with hA
  have hAmeas : ∀ N R, MeasurableSet (A N R) := by
    intro N R
    have he : A N R = ⋂ m : ℕ, ⋂ l : ℕ, {ω | gpt m l ≤ N → |H (gpt m l) ω| ≤ R} := by
      ext ω
      simp only [hA, Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h m l hml => h _ hml, fun h =>
        bound_of_grid (f := fun s => H s ω) (hHc ω) fun m l hml => h m l hml⟩
    rw [he]
    refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun l => ?_
    by_cases hml : gpt m l ≤ (N : ℝ≥0)
    · simp only [hml, true_implies]
      exact measurableSet_le (hHa _).abs measurable_const
    · simp only [hml, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  have hAmono : ∀ N {R R' : ℕ}, R ≤ R' → A N R ⊆ A N R' := fun N R R' hRR ω hω s hs =>
    (hω s hs).trans (by exact_mod_cast hRR)
  have hbdd : ∀ ω (N : ℕ), ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ω ∈ A N R := by
    intro ω N
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (N : ℝ≥0))).exists_bound_of_continuousOn
      (hHc ω).continuousOn
    refine ⟨⌈C⌉₊, fun R hR s hs => ?_⟩
    have h1 := hC s ⟨zero_le, hs⟩
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((Nat.le_ceil C).trans (by exact_mod_cast hR))
  have hstep : ∀ (N R q : ℕ) (t : ℝ≥0) (ω : Ω), ω ∈ A N R → t ≤ N →
      stepM W j (clampH H (R : ℝ)) q t ω = stepM W j H q t ω := fun N R q t ω hω ht =>
    stepM_congr_le W j q fun s hs => clampH_eq_of_abs_le H (hω s (hs.trans ht))
  have hunif : ∀ (R N : ℕ) (ε : ℝ), 0 < ε → Tendsto (fun q => P {ω | ∃ t : ℝ≥0, t ≤ N ∧
      ε < |stepM W j (clampH H (R : ℝ)) q t ω - Jc R t ω|}) atTop (𝓝 0) :=
    fun R N ε hε => stepM_unif_bdd hW x₀ j (fun s => clampH_measurable (hHm s) R)
      (fun s => clampH_measurable (hHa s) R) (clampH_continuous hHc R)
      (abs_clampH_le H (Nat.cast_nonneg R)) (hJcI R) (hJcc R) N hε
  have hnull : ∀ N R R' : ℕ, R ≤ R' →
      P {ω | ω ∈ A N R ∧ ∃ t : ℝ≥0, t ≤ N ∧ Jc R t ω ≠ Jc R' t ω} = 0 := by
    intro N R R' hRR
    have hsub : {ω | ω ∈ A N R ∧ ∃ t : ℝ≥0, t ≤ N ∧ Jc R t ω ≠ Jc R' t ω} ⊆
        ⋃ n : ℕ, {ω | ω ∈ A N R ∧ ∃ t : ℝ≥0, t ≤ N ∧
          1 / ((n : ℝ) + 1) < |Jc R t ω - Jc R' t ω|} := by
      rintro ω ⟨hA', t, ht, hne⟩
      have hpos : 0 < |Jc R t ω - Jc R' t ω| := abs_pos.2 (sub_ne_zero.2 hne)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact Set.mem_iUnion.2 ⟨n, hA', t, ht, hn⟩
    refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
    set e : ℝ := 1 / ((n : ℝ) + 1) / 2 with he
    have hepos : 0 < e := by positivity
    have hle : ∀ q, P {ω | ω ∈ A N R ∧ ∃ t : ℝ≥0, t ≤ N ∧
        1 / ((n : ℝ) + 1) < |Jc R t ω - Jc R' t ω|} ≤
        P {ω | ∃ t : ℝ≥0, t ≤ N ∧ e < |stepM W j (clampH H (R : ℝ)) q t ω - Jc R t ω|} +
        P {ω | ∃ t : ℝ≥0, t ≤ N ∧ e < |stepM W j (clampH H (R' : ℝ)) q t ω - Jc R' t ω|} := by
      intro q
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro ω ⟨hA', t, ht, hlt⟩
      have h1 := hstep N R q t ω hA' ht
      have h2 := hstep N R' q t ω (hAmono N hRR hA') ht
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_lt] at hc
      have a1 := hc.1 t ht
      have a2 := hc.2 t ht
      rw [h1] at a1
      rw [h2] at a2
      have e1 : Jc R t ω - Jc R' t ω =
          (stepM W j H q t ω - Jc R' t ω) - (stepM W j H q t ω - Jc R t ω) := by ring
      have e2 := abs_sub (stepM W j H q t ω - Jc R' t ω) (stepM W j H q t ω - Jc R t ω)
      rw [← e1] at e2
      have e3 : 1 / ((n : ℝ) + 1) = 2 * e := by rw [he]; ring
      linarith
    have ht := (hunif R N e hepos).add (hunif R' N e hepos)
    rw [add_zero] at ht
    exact nonpos_iff_eq_zero.1 (ge_of_tendsto' ht hle)
  set G0 : Set Ω := ⋂ N : ℕ, ⋂ R : ℕ, ⋂ R' : ℕ,
    {ω | R ≤ R' → ω ∈ A N R → ∀ t : ℝ≥0, t ≤ N → Jc R t ω = Jc R' t ω} with hG0
  have hG0c : P G0ᶜ = 0 := by
    have hsub : G0ᶜ ⊆ ⋃ N : ℕ, ⋃ R : ℕ, ⋃ R' : ℕ,
        {ω | R ≤ R' ∧ ω ∈ A N R ∧ ∃ t : ℝ≥0, t ≤ N ∧ Jc R t ω ≠ Jc R' t ω} := by
      intro ω hω
      by_contra hc
      apply hω
      simp only [hG0, Set.mem_iInter, Set.mem_setOf_eq]
      intro N R R' hRR hA' t ht
      by_contra hne
      exact hc (Set.mem_iUnion.2 ⟨N, Set.mem_iUnion.2 ⟨R, Set.mem_iUnion.2
        ⟨R', hRR, hA', t, ht, hne⟩⟩⟩)
    refine measure_mono_null hsub (measure_iUnion_null fun N => measure_iUnion_null fun R =>
      measure_iUnion_null fun R' => ?_)
    by_cases hRR : R ≤ R'
    · refine measure_mono_null ?_ (hnull N R R' hRR)
      rintro ω ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
    · exact measure_mono_null (fun ω hω => (hRR hω.1).elim) measure_empty
  set G : Set Ω := (toMeasurable P G0ᶜ)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P _).compl
  have hGsub : G ⊆ G0 := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have hGc : P Gᶜ = 0 := by rw [hG, compl_compl, measure_toMeasurable]; exact hG0c
  have hconst : ∀ ω ∈ G, ∀ N R : ℕ, ω ∈ A N R → ∀ t : ℝ≥0, t ≤ N → ∀ R' : ℕ, R ≤ R' →
      Jc R' t ω = Jc R t ω := by
    intro ω hω N R hA' t ht R' hRR
    have h := hGsub hω
    simp only [hG0, Set.mem_iInter, Set.mem_setOf_eq] at h
    exact (h N R R' hRR hA' t ht).symm
  set L : ℝ≥0 → Ω → ℝ := fun t ω =>
    if ω ∈ G then limUnder atTop (fun R : ℕ => Jc R t ω) else 0 with hL
  have hLeq : ∀ ω ∈ G, ∀ N R : ℕ, ω ∈ A N R → ∀ t : ℝ≥0, t ≤ N → L t ω = Jc R t ω := by
    intro ω hω N R hA' t ht
    simp only [hL, hω, if_true]
    exact (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R, fun R' hR' =>
      (hconst ω hω N R hA' t ht R' hR').symm⟩)).limUnder_eq
  have hceil : ∀ t : ℝ≥0, t ≤ ((⌈(t : ℝ)⌉₊ : ℕ) : ℝ≥0) := fun t => by
    rw [← NNReal.coe_le_coe]; push_cast; exact Nat.le_ceil _
  have hconvG : ∀ ω ∈ G, ∀ t, Tendsto (fun R : ℕ => Jc R t ω) atTop (𝓝 (L t ω)) := by
    intro ω hω t
    obtain ⟨R, hR⟩ := hbdd ω ⌈(t : ℝ)⌉₊
    rw [hLeq ω hω _ R (hR R le_rfl) t (hceil t)]
    exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R, fun R' hR' =>
      (hconst ω hω _ R (hR R le_rfl) t (hceil t) R' hR').symm⟩)
  have hLc : ∀ ω, Continuous fun t => L t ω := by
    intro ω
    by_cases hω : ω ∈ G
    · refine continuous_iff_continuousAt.2 fun t => ?_
      obtain ⟨R, hR⟩ := hbdd ω (⌈(t : ℝ)⌉₊ + 1)
      have htN : t < ((⌈(t : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
        rw [← NNReal.coe_lt_coe]; push_cast; linarith [Nat.le_ceil (t : ℝ)]
      have hev : (fun s => Jc R s ω) =ᶠ[𝓝 t] fun s => L s ω := by
        filter_upwards [Iio_mem_nhds htN] with s hs
        exact (hLeq ω hω _ R (hR R le_rfl) s (le_of_lt hs)).symm
      exact ((hJcc R ω).continuousAt).congr hev
    · simp only [hL, hω, if_false]
      exact continuous_const
  have hLa : ∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (L t) := by
    intro t
    have hGmt : MeasurableSet[completedBrownianPast P W (fun _ => x₀) t] G := by
      refine MeasurableSet.compl ?_
      refine (le_sup_right : MeasurableSpace.generateFrom
        {B | ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ B ⊆ N} ≤ _) _ ?_
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨_, measurableSet_toMeasurable P _, by rw [measure_toMeasurable]; exact hG0c, subset_rfl⟩
    have hfm : ∀ R : ℕ, Measurable[completedBrownianPast P W (fun _ => x₀) t]
        (G.indicator (Jc R t)) := fun R => (hJca R t).indicator hGmt
    refine @measurable_of_tendsto_metrizable Ω ℝ
      (completedBrownianPast P W (fun _ => x₀) t) _ _ _ _ _ _ hfm ?_
    refine tendsto_pi_nhds.2 fun ω => ?_
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
      exact hconvG ω hω t
    · simp only [indicator_of_notMem hω, hL, hω, if_false]
      exact tendsto_const_nhds
  have hLm : ∀ t, Measurable (L t) := by
    intro t
    have hfm : ∀ R : ℕ, Measurable (G.indicator (Jc R t)) := fun R => (hJcm R t).indicator hGm
    refine measurable_of_tendsto_metrizable hfm (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
      exact hconvG ω hω t
    · simp only [indicator_of_notMem hω, hL, hω, if_false]
      exact tendsto_const_nhds
  have hL0 : ∀ ω, L 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨R, hR⟩ := hbdd ω 0
      rw [hLeq ω hω 0 R (hR R le_rfl) 0 (by simp)]
      exact hJc0 R ω
    · simp only [hL, hω, if_false]
  obtain ⟨J', hJ'⟩ := exists_hasBrownianItoIntegral hW x₀ j hHm hHc
  have hLJ : ∀ t, L t =ᵐ[P] J' t := by
    intro t
    have hloc : ∀ R : ℕ, ∀ᵐ ω ∂P, ω ∈ A ⌈(t : ℝ)⌉₊ R → Jc R t ω = J' t ω := fun R =>
      hasBrownianItoIntegral_eq_on hW x₀ j (fun s => clampH_measurable (hHm s) R)
        (clampH_continuous hHc R) hHm hHc (hJcI R) hJ' t (A ⌈(t : ℝ)⌉₊ R)
        fun ω hω n i hi => clampH_eq_of_abs_le H (hω _ ((dyTime_le t hi).trans (hceil t)))
    have hloc' := ae_all_iff.2 hloc
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := mem_ae_iff.2 hGc
    filter_upwards [hloc', hGae] with ω h1 h2
    obtain ⟨R, hR⟩ := hbdd ω ⌈(t : ℝ)⌉₊
    rw [hLeq ω h2 _ R (hR R le_rfl) t (hceil t)]
    exact h1 R (hR R le_rfl)
  have hItoL : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H L :=
    ⟨hJ'.1, fun t => (hJ'.2 t).imp fun a ha =>
      ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.congr_right (hLJ t).symm⟩⟩
  have hAc : ∀ N : ℕ, Tendsto (fun R : ℕ => P (A N R)ᶜ) atTop (𝓝 0) := by
    intro N
    have h := tendsto_measure_iInter_atTop (μ := P) (s := fun R : ℕ => (A N R)ᶜ)
      (fun R => (hAmeas N R).compl.nullMeasurableSet)
      (fun R R' hRR => Set.compl_subset_compl.2 (hAmono N hRR)) ⟨0, measure_ne_top P _⟩
    have hempty : (⋂ R : ℕ, (A N R)ᶜ) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_forall, not_not]
      obtain ⟨R, hR⟩ := hbdd ω N
      exact ⟨R, hR R le_rfl⟩
    rw [hempty, measure_empty] at h
    exact h
  refine ⟨L, hLc, hLa, hLm, hL0, hItoL, fun N ε hε => ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 (hAc N)) _ hδ2).exists
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hunif R N ε hε)) _ hδ2] with q hq
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ N ∧ ε < |stepM W j H q t ω - L t ω|} ⊆
      (A N R)ᶜ ∪ Gᶜ ∪ {ω | ∃ t : ℝ≥0, t ≤ N ∧
        ε < |stepM W j (clampH H (R : ℝ)) q t ω - Jc R t ω|} := by
    rintro ω ⟨t, ht, hlt⟩
    by_cases h1 : ω ∈ A N R
    · by_cases h2 : ω ∈ G
      · refine Or.inr ⟨t, ht, ?_⟩
        rw [hstep N R q t ω h1 ht, ← hLeq ω h2 N R h1 t ht]
        exact hlt
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  calc P {ω | ∃ t : ℝ≥0, t ≤ N ∧ ε < |stepM W j H q t ω - L t ω|}
      ≤ P ((A N R)ᶜ ∪ Gᶜ ∪ {ω | ∃ t : ℝ≥0, t ≤ N ∧
        ε < |stepM W j (clampH H (R : ℝ)) q t ω - Jc R t ω|}) := measure_mono hsub
    _ ≤ P (A N R)ᶜ + P Gᶜ + P {ω | ∃ t : ℝ≥0, t ≤ N ∧
        ε < |stepM W j (clampH H (R : ℝ)) q t ω - Jc R t ω|} :=
      (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ δ / 2 + 0 + δ / 2 := add_le_add (add_le_add hR hGc.le) hq
    _ = δ := by rw [add_zero, ENNReal.add_halves]

end HK
end ItoLib

end FlatM_HK
-- ===== Doob =====
section FlatM_Doob
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section Doob
/-! 73c0fc13 step D1: Doob's L² maximal inequality for continuous versions of Itô integrals of
bounded continuous adapted integrands, with the integrated second moment `E ∫₀ᴺ G²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Left Riemann sums on the dyadic grid `gpt q` converge to the integral over `[0, N]`. -/
theorem riemann_gpt {f : ℝ≥0 → ℝ} (hf : Continuous f) (N : ℕ) :
    Tendsto (fun q : ℕ => ∑ i ∈ Finset.range (N * 2 ^ q), (hm q : ℝ) * f (gpt q i)) atTop
      (𝓝 (∫ u in (0 : ℝ)..(N : ℝ), f u.toNNReal)) := by
  set F : ℝ → ℝ := fun u => f u.toNNReal with hF
  have hFc : Continuous F := hf.comp continuous_real_toNNReal
  have hUC : UniformContinuousOn F (Icc (0 : ℝ) (N + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hFc.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * ((N : ℝ) + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1 hUC η hη0
  obtain ⟨q0, hq0⟩ := exists_pow_lt_of_lt_one hδ0 (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨q0, fun q hq => ?_⟩
  set h : ℝ := (hm q : ℝ) with hh
  have hh' : h = 1 / 2 ^ q := hm_coe q
  have hh0 : 0 < h := by rw [hh']; positivity
  have hhδ : h < δ := by
    rw [hh']
    calc (1 : ℝ) / 2 ^ q = (1 / 2) ^ q := by rw [one_div_pow]
      _ ≤ (1 / 2) ^ q0 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
      _ < δ := hq0
  have hgpt : ∀ i : ℕ, f (gpt q i) = F (i * h) := fun i => by
    simp only [hF, gpt, hh]
  have hNh : ((N * 2 ^ q : ℕ) : ℝ) * h = N := by
    rw [hh']; push_cast; field_simp
  -- split the integral into the grid cells
  have hsplit : ∫ u in (0 : ℝ)..(N : ℝ), F u =
      ∑ i ∈ Finset.range (N * 2 ^ q), ∫ u in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), F u := by
    have h1 := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => (i : ℝ) * h) (n := N * 2 ^ q) (f := F) (μ := volume)
      (fun k _ => hFc.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul] at h1
    rw [hNh] at h1
    rw [← h1]
  have hcell : ∀ i ∈ Finset.range (N * 2 ^ q),
      |h * F (i * h) - ∫ u in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), F u| ≤ h * η := by
    intro i hi
    have hi' : i + 1 ≤ N * 2 ^ q := Finset.mem_range.1 hi
    have hle : ((i : ℝ) * h) ≤ ((i + 1 : ℕ) : ℝ) * h := by
      push_cast; first | linarith | nlinarith
    have hlen : ((i + 1 : ℕ) : ℝ) * h - (i : ℝ) * h = h := by push_cast; ring
    have htop : ((i + 1 : ℕ) : ℝ) * h ≤ N := by
      rw [← hNh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi') hh0.le
    have hconst : h * F (i * h) = ∫ _u in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), F (i * h) := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hFc.intervalIntegrable _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (i : ℝ) * h) (b := ((i + 1 : ℕ) : ℝ) * h) (C := η)
      (f := fun u => F (i * h) - F u) (fun u hu => by
        rw [Set.uIoc_of_le hle] at hu
        have hi0 : (0 : ℝ) ≤ i * h := by positivity
        have hm1 : (i : ℝ) * h ∈ Icc (0 : ℝ) (N + 1) := ⟨hi0, by linarith⟩
        have hm2 : u ∈ Icc (0 : ℝ) (N + 1) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hd : dist ((i : ℝ) * h) u < δ := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]
          linarith [hu.2]
        exact (hδ _ hm1 _ hm2 hd).le)
    rw [hlen, abs_of_pos hh0] at hb
    rw [← Real.norm_eq_abs]
    linarith
  rw [Real.dist_eq, hsplit]
  simp only [hgpt]
  rw [← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range (N * 2 ^ q),
        (h * F (i * h) - ∫ u in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), F u)|
      ≤ ∑ i ∈ Finset.range (N * 2 ^ q),
        |h * F (i * h) - ∫ u in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), F u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (N * 2 ^ q), h * η := Finset.sum_le_sum hcell
    _ = N * η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, hNh]
    _ < ε := by
        rw [hη]
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- The dsum_max right-hand side converges to `2d E ∫₀ᴺ G²`. -/
theorem riemann_moment_tendsto {P : Measure Ω} [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ}
    (hGa : ∀ s, Measurable (G s)) (hGc : ∀ ω, Continuous fun s => G s ω) {C : ℝ}
    (hC : ∀ s ω, |G s ω| ≤ C) (N : ℕ) :
    Tendsto (fun q : ℕ => ∑ i ∈ Finset.range (N * 2 ^ q), 2 * d * (hm q : ℝ) *
        ∫ ω, G (gpt q i) ω ^ 2 ∂P) atTop
      (𝓝 (2 * d * ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G u.toNNReal ω ^ 2) ∂P)) := by
  have heq : ∀ q : ℕ, ∑ i ∈ Finset.range (N * 2 ^ q), 2 * d * (hm q : ℝ) *
      ∫ ω, G (gpt q i) ω ^ 2 ∂P =
      2 * d * ∫ ω, (∑ i ∈ Finset.range (N * 2 ^ q), (hm q : ℝ) * G (gpt q i) ω ^ 2) ∂P := by
    intro q
    rw [integral_finset_sum _ (fun i _ => by
      refine (Integrable.of_bound (C := C ^ 2) ((hGa _).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)).const_mul _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hC (gpt q i) ω
      nlinarith [abs_nonneg (G (gpt q i) ω), sq_abs (G (gpt q i) ω)]),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]; ring
  simp only [heq]
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_of_dominated_convergence (fun _ => N * C ^ 2) (fun q => ?_)
    (integrable_const _) (fun q => ae_of_all _ fun ω => ?_)
    (ae_of_all _ fun ω => riemann_gpt (f := fun s => G s ω ^ 2) ((hGc ω).pow 2) N)
  · exact (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((hGa _).pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hcell : ∀ i ∈ Finset.range (N * 2 ^ q), |(hm q : ℝ) * G (gpt q i) ω ^ 2| ≤
        (hm q : ℝ) * C ^ 2 := by
      intro i _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ hm q), abs_of_nonneg (sq_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 := hC (gpt q i) ω
      nlinarith [abs_nonneg (G (gpt q i) ω), sq_abs (G (gpt q i) ω)]
    refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hm_coe]
    push_cast; field_simp

end Doob
end ItoLib

end FlatM_Doob
-- ===== Doob2 =====
section FlatM_Doob2
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section Doob2
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Grid maximal bound for the step integral with the exact `dsum_max` right-hand side. -/
theorem stepM_grid_max' {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {G : ℝ≥0 → Ω → ℝ} (hGm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (G s))
    (hGa : ∀ s, Measurable (G s)) {C : ℝ} (hC : ∀ s ω, |G s ω| ≤ C) {N q : ℕ} (hNq : N ≤ q)
    {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ k ≤ N * 2 ^ q, lam ≤ |stepM W j G q (gpt q k) ω|} ≤
      ∑ i ∈ Finset.range (N * 2 ^ q), 2 * d * (hm q : ℝ) * ∫ ω, G (gpt q i) ω ^ 2 ∂P := by
  set φ : ℕ → Ω → ℝ := fun i ω => G (gpt q i) ω with hφ
  have hset : {ω | ∃ k ≤ N * 2 ^ q, lam ≤ |stepM W j G q (gpt q k) ω|} =
      {ω | ∃ k ≤ N * 2 ^ q, lam ≤ |dsum W j q φ k ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun k => and_congr_right fun hk => ?_
    rw [stepM_grid W j G (le_refl q) (hk.trans (Nat.mul_le_mul_right _ hNq)) ω]
    simp [hφ]
  have hφm : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) (gpt q i)] (φ i) :=
    fun i => hGm _
  have hφa : ∀ i, Measurable (φ i) := fun i => hGa _
  have hφK : ∀ i ω, |φ i ω| ≤ C := fun i ω => hC _ ω
  rw [hset]
  exact dsum_max hW x₀ j q hφm hφa hφK (N * 2 ^ q) hlam

set_option maxHeartbeats 1000000 in
/-- **Doob's L² maximal inequality** for the continuous version of the Itô integral of a bounded
continuous adapted integrand: `λ² P(sup_{t ≤ N} |J t| > λ) ≤ 2d E ∫₀ᴺ G²`. -/
theorem doob_ito {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {G J : ℝ≥0 → Ω → ℝ}
    (hGm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (G s))
    (hGa : ∀ s, Measurable (G s)) (hGc : ∀ ω, Continuous fun s => G s ω) {C : ℝ}
    (hC : ∀ s ω, |G s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) G J)
    (hJc : ∀ ω, Continuous fun t => J t ω) (N : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω|} ≤
      2 * d * ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G u.toNNReal ω ^ 2) ∂P := by
  set R : ℝ := 2 * d * ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G u.toNNReal ω ^ 2) ∂P with hR
  have hR0 : 0 ≤ R := by
    rw [hR]
    refine mul_nonneg (by positivity) (integral_nonneg fun ω => ?_)
    exact intervalIntegral.integral_nonneg (Nat.cast_nonneg N) fun u _ => sq_nonneg _
  set Rq : ℕ → ℝ := fun q => ∑ i ∈ Finset.range (N * 2 ^ q), 2 * d * (hm q : ℝ) *
    ∫ ω, G (gpt q i) ω ^ 2 ∂P with hRq
  have hRqt : Tendsto Rq atTop (𝓝 R) := riemann_moment_tendsto hGa hGc hC N
  set S : ℕ → ℝ≥0 → Ω → ℝ := fun q t ω => stepM W j G q t ω with hS
  have hconv : ∀ t, TendstoInMeasure P (fun q => S q t) atTop (J t) := fun t =>
    stepM_tendsto hW x₀ j hGm hGa hGc hC hJ t
  let A : ℕ → Set Ω := fun r => {ω | ∃ k ≤ N * 2 ^ r, lam < |J (gpt r k) ω|}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun r ω hω => ?_
    obtain ⟨k, hk, hl⟩ := hω
    refine ⟨k * 2 ^ (r + 1 - r), ?_, ?_⟩
    · have h2 : 2 ^ (r + 1 - r) = 2 := by simp
      rw [h2, pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_right 2 hk
    · rwa [← gpt_lift (Nat.le_succ r)]
  have hlev : ∀ r, ∀ lam' : ℝ, 0 < lam' → lam' < lam →
      P (A r) ≤ ENNReal.ofReal (R / lam' ^ 2) := by
    intro r lam' hl0 hll
    set E : ℕ → ℕ → Set Ω := fun q k =>
      {ω | lam - lam' ≤ dist (S q (gpt r k) ω) (J (gpt r k) ω)} with hE
    have hEt : ∀ k, Tendsto (fun q => P (E q k)) atTop (𝓝 0) := fun k =>
      tendstoInMeasure_iff_dist.1 (hconv (gpt r k)) (lam - lam') (by linarith)
    have hsumt : Tendsto (fun q => ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k)) atTop
        (𝓝 0) := by
      simpa using tendsto_finset_sum (Finset.range (N * 2 ^ r + 1)) fun k _ => hEt k
    have hle : ∀ q, max N r ≤ q →
        P (A r) ≤ ENNReal.ofReal (Rq q / lam' ^ 2) +
          ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k) := by
      intro q hq
      have hNq : N ≤ q := (le_max_left _ _).trans hq
      have hrq : r ≤ q := (le_max_right _ _).trans hq
      set Gq : Set Ω := {ω | ∃ k ≤ N * 2 ^ q, lam' ≤ |stepM W j G q (gpt q k) ω|} with hGq
      have hGqb : P Gq ≤ ENNReal.ofReal (Rq q / lam' ^ 2) := by
        have h := stepM_grid_max' hW x₀ j hGm hGa hC hNq hl0
        rw [← ofReal_measureReal (measure_ne_top P _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hsub : A r ⊆ Gq ∪ ⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k := by
        rintro ω ⟨k, hk, hlt⟩
        by_cases hEk : ω ∈ E q k
        · exact Or.inr (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hEk)
        · left
          simp only [hE, Set.mem_setOf_eq, not_le, Real.dist_eq] at hEk
          refine ⟨k * 2 ^ (q - r), ?_, ?_⟩
          · calc k * 2 ^ (q - r) ≤ N * 2 ^ r * 2 ^ (q - r) := Nat.mul_le_mul_right _ hk
              _ = N * 2 ^ q := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hrq]
          · rw [← gpt_lift hrq]
            have h1 : |J (gpt r k) ω| ≤ |S q (gpt r k) ω| + |S q (gpt r k) ω - J (gpt r k) ω| := by
              have h0 := abs_sub_abs_le_abs_sub (J (gpt r k) ω) (S q (gpt r k) ω)
              have h0' := abs_sub_comm (J (gpt r k) ω) (S q (gpt r k) ω)
              linarith
            have : lam' ≤ |S q (gpt r k) ω| := by linarith
            simpa [hS] using this
      calc P (A r) ≤ P (Gq ∪ ⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k) := measure_mono hsub
        _ ≤ P Gq + P (⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Rq q / lam' ^ 2) +
            ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k) :=
            add_le_add hGqb (measure_biUnion_finset_le _ _)
    have hlim : Tendsto (fun q => ENNReal.ofReal (Rq q / lam' ^ 2) +
        ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k)) atTop
        (𝓝 (ENNReal.ofReal (R / lam' ^ 2) + 0)) :=
      (ENNReal.tendsto_ofReal (hRqt.div_const _)).add hsumt
    rw [add_zero] at hlim
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨max N r, hle⟩)
  have hlevR : ∀ r, lam ^ 2 * P.real (A r) ≤ R := by
    intro r
    have hev : ∀ᶠ l in 𝓝[<] lam, l ^ 2 * P.real (A r) ≤ R := by
      filter_upwards [Ioo_mem_nhdsLT hlam] with l hl
      have h := hlev r l hl.1 hl.2
      have h2 : P.real (A r) ≤ R / l ^ 2 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (by have := hl.1; positivity) h
      rw [le_div_iff₀ (by have := hl.1; positivity)] at h2
      linarith
    have ht : Tendsto (fun l : ℝ => l ^ 2 * P.real (A r)) (𝓝[<] lam)
        (𝓝 (lam ^ 2 * P.real (A r))) :=
      ((continuous_pow 2).mul continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto ht hev
  set Bd : ℝ := R / lam ^ 2 with hBd
  have hall : ∀ r, P.real (A r) ≤ Bd := fun r => by
    rw [hBd, le_div_iff₀ (by positivity)]; linarith [hlevR r]
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω|} ⊆ ⋃ r, A r := by
    rintro ω ⟨t, htN, hlt⟩
    let kr : ℕ → ℕ := fun r => ⌊(t : ℝ) * 2 ^ r⌋₊
    have hconv' : Tendsto (fun r => gpt r (kr r)) atTop (𝓝 t) := by
      rw [← NNReal.tendsto_coe]
      have hup : ∀ r, (gpt r (kr r) : ℝ) ≤ t := fun r => by
        rw [gpt_coe, div_le_iff₀ (by positivity)]
        exact Nat.floor_le (by positivity)
      have hlo : ∀ r, (t : ℝ) - 1 / 2 ^ r ≤ gpt r (kr r) := fun r => by
        rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div,
          inv_mul_cancel₀ (by positivity)]
        linarith [Nat.lt_floor_add_one ((t : ℝ) * 2 ^ r)]
      have hl : Tendsto (fun r : ℕ => (t : ℝ) - 1 / 2 ^ r) atTop (𝓝 t) := by
        have h0 : Tendsto (fun r : ℕ => (1 : ℝ) / 2 ^ r) atTop (𝓝 0) := by
          simpa [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        simpa using h0.const_sub (t : ℝ)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hup
    have hev := ((continuous_abs.comp (hJc ω)).tendsto t).comp hconv'
    obtain ⟨r, hr⟩ := (hev.eventually (lt_mem_nhds hlt)).exists
    refine Set.mem_iUnion.2 ⟨r, kr r, ?_, hr⟩
    have : (t : ℝ) * 2 ^ r ≤ ((N * 2 ^ r : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htN) (by positivity)
    exact (Nat.floor_le_floor this).trans (by rw [Nat.floor_natCast])
  have hU : P (⋃ r, A r) ≤ ENNReal.ofReal Bd := by
    rw [hAmono.measure_iUnion]
    refine iSup_le fun r => ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hall r)
  have hS' : P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω|} ≤ Bd := by
    have h1 := (measure_mono hsub).trans hU
    have hB0 : 0 ≤ Bd := by rw [hBd]; positivity
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hB0 h1
  have := mul_le_mul_of_nonneg_left hS' (sq_nonneg lam)
  rw [hBd, mul_div_cancel₀ _ (by positivity)] at this
  exact this

end Doob2
end ItoLib

end FlatM_Doob2
-- ===== GateH =====
section FlatM_GateH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

/-! 73c0fc13 step D2: gated Doob maximal inequality for Itô integrals of unbounded continuous
adapted integrands (helpers copied from 8f909832_hl/C3.lean). -/

/-- Measurability of `ω ↦ ∫₀ˢ H(u) du` for `H` continuous in time and `m`-measurable up to `s`
(Carathéodory). -/
lemma measurable_integral_of_adapted {Ω : Type*} [m : MeasurableSpace Ω] {H : ℝ≥0 → Ω → ℝ}
    (s : ℝ≥0) (hm : ∀ u, u ≤ s → Measurable (H u)) (hc : ∀ ω, Continuous fun u => H u ω) :
    Measurable (fun ω => ∫ u in (0 : ℝ)..s.val, H u.toNNReal ω) := by
  set H' : ℝ → Ω → ℝ := fun u ω => H (min u.toNNReal s) ω with hH'
  have hH'c : ∀ ω, Continuous fun u => H' u ω :=
    fun ω => (hc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hH'm : ∀ u, Measurable (H' u) := fun u => hm _ (min_le_right _ _)
  have hj : Measurable (Function.uncurry H') :=
    measurable_uncurry_of_continuous_of_measurable hH'c hH'm
  have hj' : StronglyMeasurable (Function.uncurry fun (ω : Ω) (u : ℝ) => H' u ω) :=
    (hj.comp measurable_swap).stronglyMeasurable
  have hint := hj'.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) s.val))
  have heq : (fun ω => ∫ u in (0 : ℝ)..s.val, H u.toNNReal ω) =
      fun ω => ∫ u, H' u ω ∂(volume.restrict (Set.Ioc (0 : ℝ) s.val)) := by
    funext ω
    rw [intervalIntegral.integral_of_le s.2]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [hH']
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hu.2)]
  rw [heq]; exact hint.measurable

/-- The gate `ρ(y) = 1 − min 1 (max 0 y)`. -/
noncomputable def rho (y : ℝ) : ℝ := 1 - min 1 (max 0 y)

lemma rho_nonneg (y : ℝ) : 0 ≤ rho y := by
  unfold rho; have := min_le_left (1 : ℝ) (max 0 y); linarith

lemma rho_le_one (y : ℝ) : rho y ≤ 1 := by
  unfold rho; have := le_min (zero_le_one' ℝ) (le_max_left 0 y); linarith

lemma rho_of_le {y : ℝ} (hy : y ≤ 0) : rho y = 1 := by
  unfold rho; rw [max_eq_left hy, min_eq_right zero_le_one]; ring

lemma rho_of_ge {y : ℝ} (hy : 1 ≤ y) : rho y = 0 := by
  unfold rho; rw [max_eq_right (by linarith), min_eq_left hy]; ring

lemma continuous_rho : Continuous rho := by
  unfold rho; fun_prop

lemma rho_sq_le_one (y : ℝ) : rho y ^ 2 ≤ 1 := by
  have h0 := rho_nonneg y; have h1 := rho_le_one y; nlinarith

/-- Pathwise gate bound: `∫₀ᵗ φ ρ(∫₀ᵘφ − A)² ≤ A + 1` for continuous `φ ≥ 0`. -/
lemma gate_bound (φ : ℝ → ℝ) (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u) {A : ℝ} (hA : 0 ≤ A)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, φ u * rho ((∫ v in (0 : ℝ)..u, φ v) - A) ^ 2 ≤ A + 1 := by
  set Q : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, φ v with hQ
  have hQc : Continuous Q := intervalIntegral.continuous_primitive
    (fun a b => hφc.intervalIntegrable a b) 0
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => φ u * rho (Q u - A) ^ 2) volume a b :=
    fun a b => (hφc.mul ((continuous_rho.comp (hQc.sub continuous_const)).pow 2)).intervalIntegrable a b
  have hle : ∀ b, 0 ≤ b → ∫ u in (0 : ℝ)..b, φ u * rho (Q u - A) ^ 2 ≤ Q b := by
    intro b hb
    refine intervalIntegral.integral_mono_on hb (hint 0 b) (hφc.intervalIntegrable 0 b) ?_
    intro u _
    have := rho_sq_le_one (Q u - A)
    have := hφ0 u
    nlinarith
  have hQmono : ∀ a b, a ≤ b → Q a ≤ Q b := by
    intro a b hab
    have : Q b = Q a + ∫ v in a..b, φ v := by
      simp only [hQ]
      rw [intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable _ _)
        (hφc.intervalIntegrable _ _)]
    rw [this]
    have : 0 ≤ ∫ v in a..b, φ v := intervalIntegral.integral_nonneg hab (fun u _ => hφ0 u)
    linarith
  by_cases hT : Q t ≤ A + 1
  · exact (hle t ht).trans hT
  · replace hT := not_le.mp hT
    have hQ0 : Q 0 = 0 := by simp [hQ]
    obtain ⟨τ, hτ, hQτ⟩ : ∃ τ ∈ Set.Icc 0 t, Q τ = A + 1 :=
      intermediate_value_Icc ht hQc.continuousOn ⟨by rw [hQ0]; linarith, hT.le⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 τ) (hint τ t)]
    have h2 : ∫ u in τ..t, φ u * rho (Q u - A) ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro u hu
        rw [Set.uIcc_of_le hτ.2] at hu
        have : 1 ≤ Q u - A := by have := hQmono τ u hu.1; linarith
        simp only [rho_of_ge this]; ring
    rw [h2, add_zero]
    exact (hle τ hτ.1).trans hQτ.le

/-- `∫ Φ ≤ c` for `0 ≤ Φ ≤ c` pointwise on a probability space (also if `Φ` is not integrable). -/
lemma integral_le_of_le_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Φ : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ ω, Φ ω ≤ c) :
    ∫ ω, Φ ω ∂P ≤ c := by
  by_cases hi : Integrable Φ P
  · calc ∫ ω, Φ ω ∂P ≤ ∫ _ω, c ∂P := integral_mono hi (integrable_const c) h
      _ = c := by simp
  · rw [integral_undef hi]; exact hc

end ItoLib.G73

end FlatM_GateH
-- ===== Gate =====
section FlatM_Gate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Gate
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma completedBrownianPast_mono' (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

lemma toNNReal_le_of_mem' {t : ℝ≥0} {u : ℝ} (hu : u ∈ Set.uIcc (0 : ℝ) t.val) :
    u.toNNReal ≤ t := by
  rw [Set.uIcc_of_le t.2] at hu
  exact Real.toNNReal_le_iff_le_coe.mpr hu.2

set_option maxHeartbeats 1000000 in
/-- D2: gated Doob bound `P(sup_{t ≤ N} |L t| > λ, ∫₀ᴺ g² ≤ A) ≤ 2d c²(A+1)/λ²` for the
continuous Itô integral `L` of `g·c`, `g` continuous adapted (unbounded). -/
theorem gated_max {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) (g : ℝ≥0 → Ω → ℝ)
    (hgm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (g s))
    (hga : ∀ s, Measurable (g s))
    (hgc : ∀ ω, Continuous fun s => g s ω) (c : ℝ) (L : ℝ≥0 → Ω → ℝ)
    (hL : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => g s ω * c) L)
    (hLc : ∀ ω, Continuous fun t => L t ω)
    (N : ℕ) {A : ℝ} (hA : 0 ≤ A) {lam : ℝ} (hlam : 0 < lam) :
    P {ω | (∃ t : ℝ≥0, t ≤ N ∧ lam < |L t ω|) ∧
        ∫ u in (0 : ℝ)..(N : ℝ), g u.toNNReal ω ^ 2 ≤ A} ≤
      ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / lam ^ 2) := by
  set F := completedBrownianPast P W (fun _ => x₀) with hF
  have hFmono : ∀ {u s : ℝ≥0}, u ≤ s → F u ≤ F s := fun hus =>
    completedBrownianPast_mono' P W _ hus
  set T : ℝ≥0 := (N : ℝ≥0) with hT
  have hTv : T.val = (N : ℝ) := NNReal.coe_natCast N
  let cl : ℕ → ℝ → ℝ := fun M y => max (-(M : ℝ)) (min (M : ℝ) y)
  have hclc : ∀ M, Continuous (cl M) := fun M =>
    continuous_const.max (continuous_const.min continuous_id)
  have hclb : ∀ (M : ℕ) (y : ℝ), |cl M y| ≤ M := by
    intro M y
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcl_eq : ∀ (M : ℕ) (y : ℝ), |y| ≤ M → cl M y = y := by
    intro M y hy
    obtain ⟨h1, h2⟩ := abs_le.mp hy
    simp only [cl]; rw [min_eq_right h2, max_eq_right h1]
  let gM : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => cl M (g s ω)
  let Q : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => ∫ u in (0 : ℝ)..s.val, gM M u.toNNReal ω ^ 2
  let G : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => gM M s ω * c * rho (Q M s ω - A)
  have hgMc : ∀ M ω, Continuous fun s => gM M s ω := fun M ω => (hclc M).comp (hgc ω)
  have hgMm : ∀ M s, Measurable[F s] (gM M s) := fun M s => (hclc M).measurable.comp (hgm s)
  have hgMa : ∀ M s, Measurable (gM M s) := fun M s => (hclc M).measurable.comp (hga s)
  have hQc : ∀ M ω, Continuous fun s : ℝ≥0 => Q M s ω := fun M ω =>
    (intervalIntegral.continuous_primitive (fun a b =>
      (((hgMc M ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable a b) 0).comp
      NNReal.continuous_coe
  have hQm : ∀ M s, Measurable[F s] (Q M s) := fun M s =>
    @measurable_integral_of_adapted Ω (F s) (fun u ω => gM M u ω ^ 2) s
      (fun u hu => ((hgMm M u).pow_const 2).mono (hFmono hu) le_rfl) (fun ω => (hgMc M ω).pow 2)
  have hQa : ∀ M s, Measurable (Q M s) := fun M s =>
    measurable_integral_of_adapted (H := fun u ω => gM M u ω ^ 2) s
      (fun u _ => (hgMa M u).pow_const 2) (fun ω => (hgMc M ω).pow 2)
  have hGc : ∀ M ω, Continuous fun s => G M s ω := fun M ω =>
    ((hgMc M ω).mul continuous_const).mul (continuous_rho.comp ((hQc M ω).sub continuous_const))
  have hGm : ∀ M s, Measurable[F s] (G M s) := fun M s =>
    ((hgMm M s).mul_const c).mul (continuous_rho.measurable.comp ((hQm M s).sub_const A))
  have hGa : ∀ M s, Measurable (G M s) := fun M s =>
    ((hgMa M s).mul_const c).mul (continuous_rho.measurable.comp ((hQa M s).sub_const A))
  have hGb : ∀ M s ω, |G M s ω| ≤ M * |c| := by
    intro M s ω
    have h1 := hclb M (g s ω)
    have h2 := rho_nonneg (Q M s ω - A)
    have h3 := rho_le_one (Q M s ω - A)
    have : |G M s ω| = |cl M (g s ω)| * |c| * rho (Q M s ω - A) := by
      simp only [G, gM, abs_mul, abs_of_nonneg h2]
    rw [this]
    calc |cl M (g s ω)| * |c| * rho (Q M s ω - A) ≤ M * |c| * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg c)) h3 h2
            (mul_nonneg (Nat.cast_nonneg M) (abs_nonneg c))
      _ = M * |c| := mul_one _
  have hex := fun M => contIto_bdd hW x₀ j (hGm M) (hGa M) (hGc M) (hGb M)
  choose LG hLGc _ _ _ hLG using hex
  -- Doob for the gated integral
  have hdoob : ∀ M, P {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |LG M t ω|} ≤
      ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / lam ^ 2) := by
    intro M
    have h := doob_ito hW x₀ j (hGm M) (hGa M) (hGc M) (hGb M) (hLG M) (hLGc M) N hlam
    have hint : ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G M u.toNNReal ω ^ 2) ∂P ≤ c ^ 2 * (A + 1) := by
      refine integral_le_of_le_const (mul_nonneg (sq_nonneg c) (by linarith)) fun ω => ?_
      have hφc : Continuous fun u : ℝ => gM M u.toNNReal ω ^ 2 :=
        ((hgMc M ω).comp continuous_real_toNNReal).pow 2
      have hb := gate_bound (fun u : ℝ => gM M u.toNNReal ω ^ 2) hφc (fun u => sq_nonneg _) hA
        (Nat.cast_nonneg N)
      calc ∫ u in (0 : ℝ)..(N : ℝ), G M u.toNNReal ω ^ 2
          = c ^ 2 * ∫ u in (0 : ℝ)..(N : ℝ), gM M u.toNNReal ω ^ 2 *
              rho ((∫ v in (0 : ℝ)..u, gM M v.toNNReal ω ^ 2) - A) ^ 2 := by
            rw [← intervalIntegral.integral_const_mul]
            refine intervalIntegral.integral_congr fun u hu => ?_
            rw [Set.uIcc_of_le (Nat.cast_nonneg N)] at hu
            have hu' : (u.toNNReal).val = u := Real.coe_toNNReal u hu.1
            simp only [G, Q]
            rw [hu']
            ring
        _ ≤ c ^ 2 * (A + 1) := mul_le_mul_of_nonneg_left hb (sq_nonneg c)
    have hlam2 : 0 < lam ^ 2 := by positivity
    have hreal : P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |LG M t ω|} ≤
        2 * d * (c ^ 2 * (A + 1)) / lam ^ 2 := by
      rw [le_div_iff₀ hlam2]
      have h2 : 2 * (d : ℝ) * ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G M u.toNNReal ω ^ 2) ∂P ≤
          2 * d * (c ^ 2 * (A + 1)) := mul_le_mul_of_nonneg_left hint (by positivity)
      linarith
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal hreal
  set S : Set Ω := {ω | (∃ t : ℝ≥0, t ≤ N ∧ lam < |L t ω|) ∧
      ∫ u in (0 : ℝ)..(N : ℝ), g u.toNNReal ω ^ 2 ≤ A} with hS
  set SM : ℕ → Set Ω := fun M => S ∩ {ω | ∀ s ≤ T, |g s ω| ≤ M} with hSMdef
  -- on `SM M` the gated integrand equals `g c` up to time `N`
  have hGeq : ∀ M, ∀ ω ∈ SM M, ∀ s ≤ T, G M s ω = g s ω * c := by
    intro M ω hω s hs
    have hgs : ∀ s', s' ≤ T → gM M s' ω = g s' ω := fun s' hs' => hcl_eq M _ (hω.2 s' hs')
    have hQs : Q M s ω ≤ A := by
      have heq : Q M s ω = ∫ u in (0 : ℝ)..s.val, g u.toNNReal ω ^ 2 := by
        refine intervalIntegral.integral_congr fun u hu => ?_
        show gM M u.toNNReal ω ^ 2 = g u.toNNReal ω ^ 2
        rw [hgs _ ((toNNReal_le_of_mem' hu).trans hs)]
      rw [heq]
      refine le_trans ?_ hω.1.2
      refine intervalIntegral.integral_mono_interval le_rfl s.2
        (by rw [← hTv]; exact_mod_cast hs)
        (Eventually.of_forall fun u => sq_nonneg _)
        ((((hgc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _)
    simp only [G]
    rw [hgs _ hs, rho_of_le (by linarith), mul_one]
  have hSM : ∀ M, P (SM M) ≤ ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / lam ^ 2) := by
    intro M
    have hloc : ∀ r k : ℕ, ∀ᵐ ω ∂P, gpt r k ≤ T → ω ∈ SM M → LG M (gpt r k) ω = L (gpt r k) ω := by
      intro r k
      by_cases hk : gpt r k ≤ T
      · have h := hasBrownianItoIntegral_eq_on hW x₀ j (hGm M) (hGc M)
          (fun s => (hgm s).mul_const c) (fun ω => (hgc ω).mul continuous_const) (hLG M) hL
          (gpt r k) (SM M) (fun ω hω N' i hi => hGeq M ω hω _ ((dyTime_le _ hi).trans hk))
        filter_upwards [h] with ω hω _ hmem using hω hmem
      · exact ae_of_all _ fun ω h => absurd h hk
    have hall : ∀ᵐ ω ∂P, ∀ r k : ℕ, gpt r k ≤ T → ω ∈ SM M →
        LG M (gpt r k) ω = L (gpt r k) ω := by
      rw [ae_all_iff]; intro r; rw [ae_all_iff]; exact hloc r
    refine le_trans (measure_mono_ae ?_) (hdoob M)
    filter_upwards [hall] with ω hω hmem
    obtain ⟨t, htN, hlt⟩ := hmem.1.1
    have hev := ((continuous_abs.comp (hLc ω)).tendsto t).comp (gpt_floor_tendsto t)
    obtain ⟨r, hr⟩ := (hev.eventually (lt_mem_nhds hlt)).exists
    have hle : gpt r ⌊(t : ℝ) * 2 ^ r⌋₊ ≤ T := (gpt_floor_le t r).trans htN
    refine ⟨gpt r ⌊(t : ℝ) * 2 ^ r⌋₊, hle, ?_⟩
    rw [hω r _ hle hmem]
    exact hr
  have hmono : Monotone SM := by
    intro M M' h ω hω
    exact ⟨hω.1, fun s hs => (hω.2 s hs).trans (by exact_mod_cast h)⟩
  have hU : ⋃ M, SM M = S := by
    ext ω; simp only [Set.mem_iUnion]; constructor
    · rintro ⟨M, h⟩; exact h.1
    · intro h
      obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
        (hgc ω).continuousOn
      obtain ⟨M, hM⟩ := exists_nat_ge B0
      refine ⟨M, h, fun s hs => ?_⟩
      have := hB0 s ⟨by positivity, hs⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans hM
  rw [← hU]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hSM

end Gate
end ItoLib.G73

end FlatM_Gate
-- ===== Slln =====
section FlatM_Slln
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Slln
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma block_of (m0 k : ℕ) (hk : (m0 + 2) ^ 4 ≤ k) :
    ∃ m, m0 ≤ m ∧ (m + 1) ^ 4 ≤ k ∧ k < (m + 2) ^ 4 := by
  classical
  have hex : ∃ m, k < (m + 2) ^ 4 := ⟨k, by
    calc k < k + 2 := by omega
      _ ≤ (k + 2) ^ 4 := Nat.le_self_pow (by norm_num) _⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · by_contra h
    have h' : Nat.find hex < m0 := not_le.mp h
    have : (Nat.find hex + 2) ^ 4 ≤ (m0 + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    exact absurd (lt_of_lt_of_le (Nat.find_spec hex) this) (not_lt.mpr hk)
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; norm_num; exact le_trans (Nat.one_le_pow _ _ (by omega)) hk
    · have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      have e : Nat.find hex - 1 + 2 = Nat.find hex + 1 := by omega
      rw [e] at h1
      exact not_lt.mp h1

lemma block_arith1 {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    ((x + 1) ^ 6 + 1) / (ε * x ^ 4) ^ 2 ≤ 65 / ε ^ 2 * (1 / x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have h2 : x + 1 ≤ 2 * x := by linarith
  have h6 : (x + 1) ^ 6 ≤ (2 * x) ^ 6 := pow_le_pow_left₀ (by linarith) h2 6
  have h1 : 1 ≤ x ^ 6 := one_le_pow₀ hx
  have hnum : (x + 1) ^ 6 + 1 ≤ 65 * x ^ 6 := by nlinarith
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpos : 0 ≤ ε ^ 2 * x ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hnum hpos
  have e1 : 65 * x ^ 6 * (ε ^ 2 * x ^ 2) = 65 * (ε * x ^ 4) ^ 2 := by ring
  linarith

lemma block_arith2 {x : ℝ} (hx : 1 ≤ x) :
    (1 + (x + 1) ^ 4) / (x + 1) ^ 6 ≤ 2 * (1 / x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ x + 1 := by linarith
  have h4 : 1 ≤ (x + 1) ^ 4 := one_le_pow₀ hy
  have hxy : x ^ 2 ≤ (x + 1) ^ 2 := pow_le_pow_left₀ hx0.le (by linarith) 2
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hA : 1 + (x + 1) ^ 4 ≤ 2 * (x + 1) ^ 4 := by linarith
  have := mul_le_mul hA hxy (by positivity) (by positivity)
  have e1 : 2 * (x + 1) ^ 4 * (x + 1) ^ 2 = 2 * (x + 1) ^ 6 := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- D3: martingale strong law. If `E ∫₀ᵀ g² ≤ K(1+T)` for all integer `T`, the continuous Itô
integral `L` of `g c` satisfies `L t / t → 0` a.s. (blocks `[(m+1)⁴, (m+2)⁴]`, gated Doob). -/
theorem slln_exp {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) (g : ℝ≥0 → Ω → ℝ)
    (hgm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (g s))
    (hga : ∀ s, Measurable (g s))
    (hgc : ∀ ω, Continuous fun s => g s ω) (c : ℝ) (L : ℝ≥0 → Ω → ℝ)
    (hL : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => g s ω * c) L)
    (hLc : ∀ ω, Continuous fun t => L t ω) {K : ℝ}
    (hK : ∀ T : ℕ, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..(T : ℝ), g u.toNNReal ω ^ 2) ∂P ≤
      ENNReal.ofReal (K * (1 + T))) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => L t ω / (t : ℝ)) atTop (𝓝 0) := by
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  let ε : ℕ → ℝ := fun q => 1 / ((q : ℝ) + 1)
  have hε : ∀ q, 0 < ε q := fun q => by positivity
  let Bq : ℕ → ℕ → Set Ω := fun q m =>
    {ω | ∃ t : ℝ≥0, t ≤ (((m + 2) ^ 4 : ℕ) : ℝ≥0) ∧ ε q * (((m + 1) ^ 4 : ℕ) : ℝ) < |L t ω|}
  set aq : ℕ → ℝ := fun q => 2 * d * c ^ 2 * (65 / ε q ^ 2) + 2 * K' with haq
  have haq0 : ∀ q, 0 ≤ aq q := fun q => by
    simp only [haq]; have := hε q; positivity
  have hB : ∀ q m, P (Bq q m) ≤ ENNReal.ofReal (aq q * (1 / ((m : ℝ) + 1) ^ 2)) := by
    intro q m
    set x : ℝ := (m : ℝ) + 1 with hx
    have hx1 : 1 ≤ x := by simp only [hx]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hN : ((((m + 2) ^ 4 : ℕ) : ℕ) : ℝ) = (x + 1) ^ 4 := by
      simp only [hx]; push_cast; ring
    have hN1 : ((((m + 1) ^ 4 : ℕ) : ℕ) : ℝ) = x ^ 4 := by simp only [hx]; push_cast; ring
    set A : ℝ := (x + 1) ^ 6 with hA
    have hA0 : 0 < A := by positivity
    set Qf : Ω → ℝ := fun ω => ∫ u in (0 : ℝ)..((((m + 2) ^ 4 : ℕ) : ℕ) : ℝ), g u.toNNReal ω ^ 2
      with hQf
    have hlam : 0 < ε q * (((m + 1) ^ 4 : ℕ) : ℝ) := by rw [hN1]; have := hε q; positivity
    have hsub : Bq q m ⊆ {ω | (∃ t : ℝ≥0, t ≤ (((m + 2) ^ 4 : ℕ) : ℝ≥0) ∧
        ε q * (((m + 1) ^ 4 : ℕ) : ℝ) < |L t ω|) ∧ Qf ω ≤ A} ∪
        {ω | ENNReal.ofReal A ≤ ENNReal.ofReal (Qf ω)} := by
      intro ω hω
      by_cases hq : Qf ω ≤ A
      · exact Or.inl ⟨hω, hq⟩
      · exact Or.inr (ENNReal.ofReal_le_ofReal (not_le.mp hq).le)
    have h1 := gated_max hW x₀ j g hgm hga hgc c L hL hLc ((m + 2) ^ 4) hA0.le hlam
    have hQm : Measurable Qf := by
      have h := measurable_integral_of_adapted (H := fun u ω => g u ω ^ 2)
        (((m + 2) ^ 4 : ℕ) : ℝ≥0) (fun u _ => (hga u).pow_const 2) (fun ω => (hgc ω).pow 2)
      simp only [NNReal.val_eq_coe, NNReal.coe_natCast] at h
      exact h
    have h2 : ENNReal.ofReal A * P {ω | ENNReal.ofReal A ≤ ENNReal.ofReal (Qf ω)} ≤
        ENNReal.ofReal (K * (1 + (((m + 2) ^ 4 : ℕ) : ℝ))) :=
      (mul_meas_ge_le_lintegral₀ hQm.ennreal_ofReal.aemeasurable _).trans (hK _)
    have h2' : P {ω | ENNReal.ofReal A ≤ ENNReal.ofReal (Qf ω)} ≤
        ENNReal.ofReal (K' * ((1 + (x + 1) ^ 4) / A)) := by
      rw [← hN]
      have hKle : ENNReal.ofReal (K * (1 + (((m + 2) ^ 4 : ℕ) : ℝ))) ≤
          ENNReal.ofReal (K' * (1 + (((m + 2) ^ 4 : ℕ) : ℝ))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [mul_div_assoc', ENNReal.ofReal_div_of_pos hA0, ENNReal.le_div_iff_mul_le
        (Or.inl (by simpa using hA0)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact h2.trans hKle
    calc P (Bq q m) ≤ _ := measure_mono hsub
      _ ≤ _ + _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / (ε q * (((m + 1) ^ 4 : ℕ) : ℝ)) ^ 2) +
          ENNReal.ofReal (K' * ((1 + (x + 1) ^ 4) / A)) := by
          refine add_le_add ?_ h2'
          simpa only [NNReal.coe_natCast] using h1
      _ = ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / (ε q * (((m + 1) ^ 4 : ℕ) : ℝ)) ^ 2 +
          K' * ((1 + (x + 1) ^ 4) / A)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (aq q * (1 / ((m : ℝ) + 1) ^ 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hN1, ← hx]
          have b1 := block_arith1 hx1 (hε q)
          have b2 := block_arith2 hx1
          have e1 : 2 * (d : ℝ) * (c ^ 2 * (A + 1)) / (ε q * x ^ 4) ^ 2 =
              2 * d * c ^ 2 * (((x + 1) ^ 6 + 1) / (ε q * x ^ 4) ^ 2) := by
            rw [hA]; ring
          rw [e1, hA]
          have c1 : 2 * (d : ℝ) * c ^ 2 * (((x + 1) ^ 6 + 1) / (ε q * x ^ 4) ^ 2) ≤
              2 * d * c ^ 2 * (65 / ε q ^ 2 * (1 / x ^ 2)) :=
            mul_le_mul_of_nonneg_left b1 (by positivity)
          have c2 : K' * ((1 + (x + 1) ^ 4) / (x + 1) ^ 6) ≤ K' * (2 * (1 / x ^ 2)) :=
            mul_le_mul_of_nonneg_left b2 hK'0
          simp only [haq]
          first | linarith | nlinarith
  have hsum : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine h.congr fun m => ?_
    push_cast; ring
  have hBC : ∀ q, ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∉ Bq q m := by
    intro q
    refine ae_eventually_notMem ?_
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (hB q))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (haq0 q) (by positivity))
      (hsum.mul_left _)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_all_iff.mpr hBC] with ω hω
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt he
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 (hω q)
  rw [eventually_atTop]
  refine ⟨(((m0 + 2) ^ 4 : ℕ) : ℝ≥0), fun t ht => ?_⟩
  set k : ℕ := ⌊(t : ℝ)⌋₊ with hk
  have hkt : (k : ℝ) ≤ t := Nat.floor_le t.2
  have htk : (t : ℝ) < k + 1 := Nat.lt_floor_add_one _
  have hk0 : (m0 + 2) ^ 4 ≤ k := by
    rw [hk]
    refine Nat.le_floor ?_
    have : ((((m0 + 2) ^ 4 : ℕ) : ℝ≥0) : ℝ) ≤ t := by exact_mod_cast ht
    simpa using this
  obtain ⟨m, hmm, hlo, hhi⟩ := block_of m0 k hk0
  have hgood := hm0 m hmm
  have htle : t ≤ (((m + 2) ^ 4 : ℕ) : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    have : ((k : ℝ) + 1) ≤ (((m + 2) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hhi
    linarith
  have hLle : |L t ω| ≤ ε q * (((m + 1) ^ 4 : ℕ) : ℝ) := by
    by_contra hc
    exact hgood ⟨t, htle, not_le.mp hc⟩
  have hk1 : (((m + 1) ^ 4 : ℕ) : ℝ) ≤ t := le_trans (by exact_mod_cast hlo) hkt
  have hone : (1 : ℝ) ≤ t := by
    have : (1 : ℝ) ≤ (((m + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
    linarith
  have htpos : (0 : ℝ) < t := by linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
  calc |L t ω| ≤ ε q * (((m + 1) ^ 4 : ℕ) : ℝ) := hLle
    _ ≤ ε q * t := mul_le_mul_of_nonneg_left hk1 (hε q).le
    _ < e * t := mul_lt_mul_of_pos_right hq htpos

end Slln
end ItoLib.G73

end FlatM_Slln
-- ===== V =====
section FlatM_V
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11c
/-! M11c: the orthant test-function machinery of Q.lean/R.lean with a general family of C²
nonnegative coordinate functions `φ k` in place of `(v⁻)³`. -/

variable {Ω : Type*} {d : ℕ}

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

end M11c

end ItoLib

end FlatM_V
-- ===== W =====
section FlatM_W
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11d
/-! M11d (lemma_3_1 clause 3, interior part): a solution started with `x_k > 0` has `X_t k ≠ 0`
almost surely at every fixed time. Test function `φ_δ(v) = 1/(v² + δ)`, with
`|φ_δ'(v) v| ≤ 2 φ_δ(v)` and `φ_δ''(v) v² ≤ 8 φ_δ(v)`. -/
open StochKolmogorov.Persist

variable {δ : ℝ}

variable {n : ℕ}

/-- `orthant_inv` for one solution (no solution family needed). -/
theorem orthant_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ orthant n := by
  exact StochKolmogorov.Persist.orthant_invariance_closed P C B hB hC hx₀ hY t
end M11d

end ItoLib

end FlatM_W
-- ===== Y =====
section FlatM_Y
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

/-- Generator of `Φ = ψ ∘ ℓ` at `x` with coefficients `σx, bx`. -/
noncomputable def genL (ψ : ℝ → ℝ) (cv : SDEState d) (σx : SDEDiffusion d) (bx x : SDEState d) : ℝ :=
  deriv ψ (∑ k, cv k * x k) * (∑ k, cv k * bx k) +
    (1 / 2) * ∑ j, deriv (deriv ψ) (∑ k, cv k * x k) * (∑ k, cv k * σx (k, j)) ^ 2

end M12a

section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- A smooth positive function equal to `1 + s` for `s > -1/4`. -/
noncomputable def pL (s : ℝ) : ℝ := 1 + s * Real.smoothTransition (4 * s + 2)

noncomputable def psiK (s : ℝ) : ℝ := Real.log (pL s) + Real.log 2

theorem pL_ge (s : ℝ) : 1 / 2 ≤ pL s := by
  unfold pL
  have h0 := Real.smoothTransition.nonneg (4 * s + 2)
  have h1 := Real.smoothTransition.le_one (4 * s + 2)
  by_cases hs : 0 ≤ s
  · nlinarith
  · push Not at hs
    by_cases hs2 : s < -1 / 2
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; norm_num
    · push Not at hs2
      nlinarith

theorem pL_pos (s : ℝ) : 0 < pL s := lt_of_lt_of_le (by norm_num) (pL_ge s)

theorem pL_eq {s : ℝ} (hs : -1 / 4 < s) : pL s = 1 + s := by
  unfold pL; rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem pL_contDiff : ContDiff ℝ 2 pL :=
  contDiff_const.add (contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)))

theorem psiK_eq {s : ℝ} (hs : -1 / 4 < s) : psiK s = Real.log (1 + s) + Real.log 2 := by
  unfold psiK; rw [pL_eq hs]

theorem deriv_psiK {s : ℝ} (hs : -1 / 4 < s) : deriv psiK s = (1 + s)⁻¹ := by
  have hev : psiK =ᶠ[𝓝 s] fun s => Real.log (1 + s) + Real.log 2 := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs' using psiK_eq hs'
  rw [hev.deriv_eq]
  have h := (((hasDerivAt_id s).const_add 1).log (by simp; linarith)).add_const (Real.log 2)
  exact h.deriv.trans (by simp)

theorem deriv2_psiK {s : ℝ} (hs : -1 / 4 < s) : deriv (deriv psiK) s = -((1 + s) ^ 2)⁻¹ := by
  have hev : deriv psiK =ᶠ[𝓝 s] fun s => (1 + s)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs' using deriv_psiK hs'
  rw [hev.deriv_eq]
  have h := ((hasDerivAt_id s).const_add 1).inv (by simp; linarith)
  exact h.deriv.trans (by rw [neg_div, one_div]; rfl)

theorem posPart_of_mem {x : SDEState n} (hx : x ∈ orthant n) : posPart x = x := by
  ext i; rw [posPart_apply']; exact max_eq_left (hx i)

theorem sig_sum_sq (C : Coeffs n) (v : Fin n → ℝ) :
    ∑ j, (∑ k, v k * C.Γ j k) ^ 2 = ∑ i, ∑ l, C.sig i l * v i * v l := by
  calc ∑ j, (∑ k, v k * C.Γ j k) ^ 2 = ∑ j, ∑ i, ∑ l, (v i * C.Γ j i) * (v l * C.Γ j l) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ l, ∑ j, (v i * C.Γ j i) * (v l * C.Γ j l) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ l, C.sig i l * v i * v l := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [Coeffs.sig, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- On `ℝⁿ₊` the generator of `log(1 + cᵀx)` is the bracket of (1.2). -/
theorem genL_kolm (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ orthant n) :
    genL psiK c (diffusion C (0, x)) (drift C (0, x)) x = cBracket C c x := by
  have hℓ : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
  have hℓ' : -1 / 4 < ∑ k, c k * x k := by linarith
  have hp : 0 < 1 + ∑ k, c k * x k := by linarith
  unfold genL cBracket
  rw [deriv_psiK hℓ', deriv2_psiK hℓ']
  simp only [diffusion, drift, PiLp.toLp_apply, posPart_of_mem hx]
  have key := sig_sum_sq C (fun k => c k * x k * C.g k x)
  have e1 : ∑ j, (∑ k, c k * (x k * C.g k x * C.Γ j k)) ^ 2 =
      ∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x := by
    rw [show (∑ j, (∑ k, c k * (x k * C.g k x * C.Γ j k)) ^ 2) =
      ∑ j, (∑ k, (c k * x k * C.g k x) * C.Γ j k) ^ 2 from
        Finset.sum_congr rfl fun j _ => by congr 1; exact Finset.sum_congr rfl fun k _ => by ring, key]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∑ k, c k * (x k * C.f k x) = ∑ i, c i * x i * C.f i x :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [← Finset.mul_sum, e1, e2]
  field_simp
  ring

/-- A solution from `x₀ ∈ ℝⁿ₊` stays in `ℝⁿ₊` at all times, a.s. -/
theorem orthant_inv_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) :
    ∀ᵐ ω ∂P, ∀ u, Y u ω ∈ orthant n := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, Y ((q : ℝ).toNNReal) ω ∈ orthant n :=
    ae_all_iff.2 fun q => orthant_inv1 P C B hB hC hx₀ hY _
  filter_upwards [hq] with ω hω u
  have hcl : IsClosed {s : ℝ≥0 | Y s ω ∈ orthant n} := orthant_isClosed.preimage (hY.2.1 ω)
  have hsub : Set.range (fun q : ℚ => (q : ℝ).toNNReal) ⊆ {s : ℝ≥0 | Y s ω ∈ orthant n} := by
    rintro _ ⟨q, rfl⟩; exact hω q
  have := hcl.closure_subset_iff.2 hsub
  rw [denseRange_rat_toNNReal.closure_range] at this
  exact this (Set.mem_univ u)

end M12b

end ItoLib

end FlatM_Y
-- ===== Z =====
section FlatM_Z
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12c
/-! M12c: invariant measures integrate the weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`:
`∫ w dμ ≤ max H 0`, hence the Lyapunov integrands `fᵢ − σᵢᵢ gᵢ²/2` are `μ`-integrable. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12c

end ItoLib

end FlatM_Z
-- ===== L33 =====
section FlatM_L33
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L33
/-! L33 (lemma_3_2/3_3/3_4 work, s1 2026-10-30): generic Lyapunov bounds for the Kolmogorov family. -/
open StochKolmogorov.Persist
variable {n : ℕ}

theorem contDiff_deriv_of {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) : Continuous (deriv g) := by
  have h2 : ContDiff ℝ (1 + 1) g := hg.of_le (by norm_num)
  exact (contDiff_succ_iff_deriv.1 h2).2.2.continuous

theorem genL_continuous {d : ℕ} {ψ : ℝ → ℝ} (h1 : ContDiff ℝ 2 ψ) (cv : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d} (hσ : Continuous σ₀)
    (hb : Continuous b₀) : Continuous fun x => genL ψ cv (σ₀ x) (b₀ x) x := by
  have hl : Continuous fun x : SDEState d => ∑ k, cv k * x k :=
    continuous_finset_sum _ fun k _ => continuous_const.mul (PiLp.continuous_apply 2 _ k)
  have hd1 := contDiff_deriv_of h1
  have hd2 : Continuous (deriv (deriv ψ)) :=
    ((contDiff_succ_iff_deriv.1 (h1.of_le (by norm_num) : ContDiff ℝ (1 + 1) ψ)).2.2).continuous_deriv le_rfl
  unfold genL
  refine ((hd1.comp hl).mul (continuous_finset_sum _ fun k _ => continuous_const.mul
    ((PiLp.continuous_apply 2 _ k).comp hb))).add (continuous_const.mul
    (continuous_finset_sum _ fun j _ => (hd2.comp hl).mul ((continuous_finset_sum _ fun k _ =>
      continuous_const.mul ((PiLp.continuous_apply 2 _ (k, j)).comp hσ)).pow 2)))

/-- Continuous functions are bounded on `{x ∈ ℝⁿ₊ : cᵀx ≤ R}` (`c > 0`). -/
theorem bdd_on_ell {c : SDEState n} (hc : c ∈ openOrthant n) {g : SDEState n → ℝ}
    (hg : Continuous g) (R : ℝ) : ∃ K, ∀ x ∈ orthant n, ∑ k, c k * x k ≤ R → |g x| ≤ K := by
  set S : Set (SDEState n) := orthant n ∩ {x | ∑ k, c k * x k ≤ R} with hS
  have hcl : IsClosed S := orthant_isClosed.inter (isClosed_le (continuous_finset_sum _ fun k _ =>
    continuous_const.mul (PiLp.continuous_apply 2 _ k)) continuous_const)
  have hbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨∑ k, |R| / c k, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (euc_norm_le_sum' x).trans (Finset.sum_le_sum fun k _ => ?_)
    have hxk := hx.1 k
    have hck := hc k
    have hsum : c k * x k ≤ ∑ j, c j * x j := Finset.single_le_sum
      (f := fun j => c j * x j) (fun j _ => mul_nonneg (hc j).le (hx.1 j)) (Finset.mem_univ k)
    rw [abs_of_nonneg hxk, le_div_iff₀ hck]
    have := hx.2; simp only [Set.mem_setOf_eq] at this
    nlinarith [le_abs_self R]
  obtain ⟨K, hK⟩ := (Metric.isCompact_of_isClosed_isBounded hcl hbd).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨K, fun x hx hR => by have := hK x ⟨hx, hR⟩; rwa [Real.norm_eq_abs] at this⟩

end L33

end ItoLib

end FlatM_L33
-- ===== L32 =====
section FlatM_L32
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L32
/-! L32 (lemma_3_2 work, 15eaca53 s2 2026-10-30): the power Lyapunov function `(1 + cᵀx)^δ`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- Smooth global version of `s ↦ (1 + s)^δ` (equal to it for `s > -1/4`). -/
noncomputable def psiD (δ : ℝ) (s : ℝ) : ℝ := pL s ^ δ

theorem psiD_contDiff (δ : ℝ) : ContDiff ℝ 2 (psiD δ) :=
  pL_contDiff.rpow_const_of_ne fun s => (pL_pos s).ne'

theorem psiD_nonneg (δ s : ℝ) : 0 ≤ psiD δ s := Real.rpow_nonneg (pL_pos s).le _

theorem psiD_eq {δ s : ℝ} (hs : -1 / 4 < s) : psiD δ s = (1 + s) ^ δ := by
  unfold psiD; rw [pL_eq hs]

theorem deriv_psiD {δ s : ℝ} (hs : -1 / 4 < s) :
    deriv (psiD δ) s = δ * psiD δ s * deriv psiK s := by
  have hne : (1 + s) ≠ 0 := by linarith
  have hev : psiD δ =ᶠ[𝓝 s] fun s => (1 + s) ^ δ := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs' using psiD_eq hs'
  rw [hev.deriv_eq, deriv_psiK hs, psiD_eq hs]
  have h := ((hasDerivAt_id s).const_add 1).rpow_const (p := δ) (Or.inl (by simpa using hne))
  refine h.deriv.trans ?_
  simp only [id]
  rw [Real.rpow_sub_one hne]
  field_simp

theorem deriv2_psiD {δ s : ℝ} (hs : -1 / 4 < s) :
    deriv (deriv (psiD δ)) s =
      δ * psiD δ s * (deriv (deriv psiK) s + δ * deriv psiK s ^ 2) := by
  have hne : (1 + s) ≠ 0 := by linarith
  have hev : deriv (psiD δ) =ᶠ[𝓝 s] fun s => δ * (1 + s) ^ (δ - 1) := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs'
    have hs'' : -1 / 4 < s' := hs'
    have hne' : (1 + s') ≠ 0 := by linarith
    rw [deriv_psiD hs', psiD_eq hs', deriv_psiK hs', Real.rpow_sub_one hne']
    field_simp
  rw [hev.deriv_eq, deriv2_psiK hs, deriv_psiK hs, psiD_eq hs]
  have h := (((hasDerivAt_id s).const_add 1).rpow_const (p := δ - 1)
    (Or.inl (by simpa using hne))).const_mul δ
  refine h.deriv.trans ?_
  simp only [id]
  have hp : (0 : ℝ) < 1 + s := by linarith
  rw [show δ - 1 - 1 = δ - 2 by ring, Real.rpow_sub hp, Real.rpow_two]
  field_simp
  ring

theorem genL_psiD (δ : ℝ) (cv : SDEState n) (σx : SDEDiffusion n) (bx x : SDEState n)
    (hs : -1 / 4 < ∑ k, cv k * x k) :
    genL (psiD δ) cv σx bx x = δ * psiD δ (∑ k, cv k * x k) * (genL psiK cv σx bx x +
      (δ / 2) * deriv psiK (∑ k, cv k * x k) ^ 2 * ∑ j, (∑ k, cv k * σx (k, j)) ^ 2) := by
  unfold genL
  rw [deriv_psiD hs, deriv2_psiD hs, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- On `ℝⁿ₊`: `genL (1+cᵀx)^δ = δ V (cBracket + (δ/2) Q/(1+cᵀx)²)`. -/
theorem genL_psiD_kolm (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n)
    (hx : x ∈ orthant n) (δ : ℝ) :
    genL (psiD δ) c (diffusion C (0, x)) (drift C (0, x)) x =
      δ * psiD δ (∑ k, c k * x k) * (cBracket C c x + (δ / 2) *
        ((∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x) /
          (1 + ∑ k, c k * x k) ^ 2)) := by
  have hℓ : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
  have hℓ' : -1 / 4 < ∑ k, c k * x k := by linarith
  have hp : 0 < 1 + ∑ k, c k * x k := by linarith
  rw [genL_psiD δ c _ _ x hℓ', genL_kolm C hc hx, deriv_psiK hℓ']
  have key := sig_sum_sq C (fun k => c k * x k * C.g k x)
  have e1 : ∑ j, (∑ k, c k * diffusion C (0, x) (k, j)) ^ 2 =
      ∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x := by
    simp only [diffusion, PiLp.toLp_apply, posPart_of_mem hx]
    rw [show (∑ j, (∑ k, c k * (x k * C.g k x * C.Γ j k)) ^ 2) =
      ∑ j, (∑ k, (c k * x k * C.g k x) * C.Γ j k) ^ 2 from
        Finset.sum_congr rfl fun j _ => by congr 1; exact Finset.sum_congr rfl fun k _ => by ring, key]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [e1]
  field_simp

theorem quad_div_le (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n)
    (hx : x ∈ orthant n) :
    (∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x) /
        (1 + ∑ k, c k * x k) ^ 2 ≤ ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| := by
  have hℓ : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
  set p := 1 + ∑ k, c k * x k with hpdef
  have hp : 0 < p := by linarith
  have ha0 : ∀ i, 0 ≤ c i * x i := fun i => mul_nonneg (hc i).le (hx i)
  have hap : ∀ i, c i * x i ≤ p := fun i => by
    have := Finset.single_le_sum (f := fun j => c j * x j) (fun j _ => ha0 j) (Finset.mem_univ i)
    simp only at this; linarith
  rw [div_le_iff₀ (by positivity), Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x =
      (C.g i x * C.g j x * C.sig i j) * ((c i * x i) * (c j * x j)) := by ring
  have h2 : (c i * x i) * (c j * x j) ≤ p ^ 2 := by
    rw [sq]; exact mul_le_mul (hap i) (hap j) (ha0 j) hp.le
  rw [h1]
  calc (C.g i x * C.g j x * C.sig i j) * ((c i * x i) * (c j * x j))
      ≤ |C.g i x * C.g j x * C.sig i j| * ((c i * x i) * (c j * x j)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (ha0 i) (ha0 j))
    _ ≤ |C.g i x * C.g j x * C.sig i j| * p ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- The weight of (3.8): `κ (1 + cᵀx)^δ (1 + Σ (|fᵢ| + gᵢ²))`, read at `x⁺`. -/
noncomputable def w38 (C : Coeffs n) (c : SDEState n) (κ δ : ℝ) (x : SDEState n) : ℝ :=
  κ * psiD δ (∑ k, c k * x k) *
    (1 + ∑ i, (|C.f i (posPart x)| + C.g i (posPart x) ^ 2))

theorem w38_continuous (C : Coeffs n) (c : SDEState n) (κ δ : ℝ)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (w38 C c κ δ) := by
  have hf : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hg : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hl : Continuous fun x : SDEState n => ∑ k, c k * x k :=
    continuous_finset_sum _ fun k _ => continuous_const.mul (PiLp.continuous_apply 2 _ k)
  exact (continuous_const.mul ((psiD_contDiff δ).continuous.comp hl)).mul
    (continuous_const.add (continuous_finset_sum _ fun i _ => (hf i).abs.add ((hg i).pow 2)))

theorem w38_nonneg (C : Coeffs n) (c : SDEState n) {κ : ℝ} (hκ : 0 ≤ κ) (δ : ℝ) (x : SDEState n) :
    0 ≤ w38 C c κ δ x :=
  mul_nonneg (mul_nonneg hκ (psiD_nonneg _ _))
    (add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (sq_nonneg _)))

theorem le_l1 (x : SDEState n) (k : Fin n) : x k ≤ l1 x := by
  have := Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)
  exact (le_abs_self _).trans this

/-- Lyapunov inequality for (3.8): `genL (1+cᵀx)^δ₀ + w38 ≤ K` on `ℝⁿ₊`, `κ = δ₀ γb / 2`. -/
theorem genL38_le (C : Coeffs n) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ orthant n, genL (psiD δ₀) c (diffusion C (0, x)) (drift C (0, x)) x ≤
      K - w38 C c (δ₀ * γb / 2) δ₀ x := by
  obtain ⟨-, hC, hc, hγ, ε, hε, R, hR⟩ := hA
  obtain ⟨hδ, -, hD⟩ := hδ₀
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  have hGc : Continuous fun x => genL (psiD δ₀) c (diffusion C (0, x)) (drift C (0, x)) x +
      w38 C c (δ₀ * γb / 2) δ₀ x :=
    (genL_continuous (psiD_contDiff δ₀) c hσc hbc).add (w38_continuous C c _ _ hC)
  obtain ⟨K₀, hK₀⟩ := bdd_on_ell hc hGc (R * ∑ k, c k)
  refine ⟨max K₀ 0, le_max_right _ _, fun x hx => ?_⟩
  suffices h : genL (psiD δ₀) c (diffusion C (0, x)) (drift C (0, x)) x +
      w38 C c (δ₀ * γb / 2) δ₀ x ≤ max K₀ 0 by linarith
  by_cases hRx : R ≤ l1 x
  · refine le_trans ?_ (le_max_right _ _)
    have hb := hR x hx hRx
    have hT := quad_div_le C hc hx
    have hDx := hD x hx
    rw [genL_psiD_kolm C hc hx δ₀]
    unfold w38
    rw [posPart_of_mem hx]
    set V := psiD δ₀ (∑ k, c k * x k)
    have hV : 0 ≤ V := psiD_nonneg _ _
    set F := ∑ i, |C.f i x|
    set G := ∑ i, C.g i x ^ 2
    set S := ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
    have hFG : ∑ i, (|C.f i x| + C.g i x ^ 2) = F + G := Finset.sum_add_distrib
    rw [hFG] at hb ⊢
    have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    set Q := (∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x) /
          (1 + ∑ k, c k * x k) ^ 2
    have hQS : δ₀ * Q ≤ δ₀ * S := mul_le_mul_of_nonneg_left hT hδ.le
    have hbr : cBracket C c x + δ₀ / 2 * Q + γb / 2 * (1 + (F + G)) ≤ 0 := by
      nlinarith [mul_nonneg hγ.le hF0, mul_nonneg hγ.le hG0, mul_nonneg hδ.le hG0]
    have : δ₀ * V * (cBracket C c x + δ₀ / 2 * Q) + δ₀ * γb / 2 * V * (1 + (F + G)) =
        δ₀ * V * (cBracket C c x + δ₀ / 2 * Q + γb / 2 * (1 + (F + G))) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hδ.le hV) hbr
  · push Not at hRx
    refine le_trans (le_trans (le_abs_self _) (hK₀ x hx ?_)) (le_max_left _ _)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_comm R]
    exact mul_le_mul_of_nonneg_left ((le_l1 x k).trans hRx.le) (hc k).le

/-- Clause (3.8) of lemma_3_2. -/
theorem clause38 (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∃ H₂ : ℝ, 0 < H₂ ∧
      (∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
              (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
          ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t))) := by
  obtain ⟨-, H₂, -, hH₂, -, h38, -⟩ := StochKolmogorov.Persist.lemma_3_2 hn P C B X hX c γb hA δ₀ hδ₀
  exact ⟨H₂, hH₂, h38⟩
end L32

section L32T
/-! Dynkin bound keeping the terminal term (for (3.7)). -/
variable {Ω : Type*} {d : ℕ}
variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end L32T

section L32U
open StochKolmogorov.Persist
variable {n : ℕ}

end L32U

section L32V
open StochKolmogorov.Persist
variable {n : ℕ}

end L32V

section L32G

end L32G

end ItoLib

end FlatM_L32
-- ===== Part2 =====
section FlatM_Part2
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Part2
variable {n : ℕ}

/-- The Persist copy of Classify coefficients (the two structures are identical). -/
def toP (C : StochKolmogorov.Classify.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open StochKolmogorov.Classify

lemma cl_posPart_cont : Continuous (StochKolmogorov.Classify.posPart (n := n)) := by
  unfold StochKolmogorov.Classify.posPart
  first
  | fun_prop
  | exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).max
        continuous_const)

lemma cl_posPart_mem (y : SDEState n) :
    StochKolmogorov.Classify.posPart y ∈ StochKolmogorov.Classify.orthant n := by
  intro i; simp [StochKolmogorov.Classify.posPart]

lemma cl_posPart_eq {y : SDEState n} (hy : y ∈ StochKolmogorov.Classify.orthant n) :
    StochKolmogorov.Classify.posPart y = y := by
  ext i; simp [StochKolmogorov.Classify.posPart, max_eq_left (hy i)]

lemma cl_coord_cont (i : Fin n) : Continuous fun y : SDEState n => y i :=
  (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)

lemma itoIntegrand_continuous (C : StochKolmogorov.Classify.Coeffs n) {c : SDEState n}
    (hc : c ∈ StochKolmogorov.Classify.openOrthant n)
    (hg : ∀ i, ContinuousOn (C.g i) (StochKolmogorov.Classify.orthant n)) (j : Fin n) :
    Continuous (itoIntegrand C c j) := by
  have hco : ∀ i, Continuous fun y : SDEState n => StochKolmogorov.Classify.posPart y i :=
    fun i => (cl_coord_cont i).comp cl_posPart_cont
  have hgi : ∀ i, Continuous fun y : SDEState n => C.g i (StochKolmogorov.Classify.posPart y) :=
    fun i => (hg i).comp_continuous cl_posPart_cont cl_posPart_mem
  have hden : ∀ y : SDEState n, 0 < 1 + ∑ i, c i * StochKolmogorov.Classify.posPart y i := by
    intro y
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      mul_nonneg (hc i).le (cl_posPart_mem y i)
    linarith
  unfold itoIntegrand
  exact Continuous.div
    (continuous_finset_sum _ fun i _ => ((continuous_const.mul (hco i)).mul (hgi i)).mul
      continuous_const)
    (continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (hco i)))
    (fun y => (hden y).ne')

lemma itoIntegrand_sq_le (C : StochKolmogorov.Classify.Coeffs n) {c : SDEState n}
    (hc : c ∈ StochKolmogorov.Classify.openOrthant n) (j : Fin n) {δ : ℝ} (hδ : 0 ≤ δ)
    {y : SDEState n} (hy : y ∈ StochKolmogorov.Classify.orthant n) :
    itoIntegrand C c j y ^ 2 ≤ ((n : ℝ) * ∑ a, ∑ b, C.Γ a b ^ 2) *
      ((1 + ∑ i, c i * y i) ^ δ * (1 + ∑ i, (|C.f i y| + |C.g i y| ^ 2))) := by
  set G : ℝ := ∑ a, ∑ b, C.Γ a b ^ 2 with hG
  set S : ℝ := 1 + ∑ i, c i * y i with hS
  have hcy : ∀ i, 0 ≤ c i * y i := fun i => mul_nonneg (hc i).le (hy i)
  have hS1 : 1 ≤ S := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hcy i
    linarith
  have hS0 : 0 < S := by linarith
  have hci : ∀ i, c i * y i ≤ S := by
    intro i
    have := Finset.single_le_sum (f := fun k => c k * y k) (fun k _ => hcy k)
      (Finset.mem_univ i)
    simp only at this
    linarith
  set aa : Fin n → ℝ := fun i => |C.g i y * C.Γ j i| with ha
  have hnum : |∑ i, c i * y i * C.g i y * C.Γ j i| ≤ S * ∑ i, aa i := by
    calc |∑ i, c i * y i * C.g i y * C.Γ j i| ≤ ∑ i, |c i * y i * C.g i y * C.Γ j i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, (c i * y i) * aa i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_assoc, abs_mul, abs_of_nonneg (hcy i)]
      _ ≤ ∑ i, S * aa i := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hci i) (abs_nonneg _)
      _ = S * ∑ i, aa i := (Finset.mul_sum _ _ _).symm
  have h1 : |itoIntegrand C c j y| ≤ ∑ i, aa i := by
    unfold itoIntegrand
    rw [cl_posPart_eq hy, abs_div, abs_of_pos hS0, div_le_iff₀ hS0]
    linarith [hnum]
  have h2 : itoIntegrand C c j y ^ 2 ≤ (∑ i, aa i) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at this
  have h3 : (∑ i, aa i) ^ 2 ≤ (n : ℝ) * ∑ i, aa i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := aa)
    simpa using this
  have hΓ : ∀ i, C.Γ j i ^ 2 ≤ G := by
    intro i
    have e1 : C.Γ j i ^ 2 ≤ ∑ b, C.Γ j b ^ 2 :=
      Finset.single_le_sum (f := fun b => C.Γ j b ^ 2) (fun b _ => sq_nonneg _)
        (Finset.mem_univ i)
    have e2 : ∑ b, C.Γ j b ^ 2 ≤ G :=
      Finset.single_le_sum (f := fun a => ∑ b, C.Γ a b ^ 2)
        (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg (C.Γ a b)) (Finset.mem_univ j)
    linarith
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  set Q : ℝ := 1 + ∑ i, (|C.f i y| + |C.g i y| ^ 2) with hQ
  have h4 : ∑ i, aa i ^ 2 ≤ G * Q := by
    have hsum : ∑ i, aa i ^ 2 ≤ ∑ i, G * (|C.f i y| + |C.g i y| ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hai : aa i ^ 2 = C.g i y ^ 2 * C.Γ j i ^ 2 := by
        show |C.g i y * C.Γ j i| ^ 2 = _
        rw [sq_abs, mul_pow]
      rw [hai]
      have hgsq : C.g i y ^ 2 ≤ |C.f i y| + |C.g i y| ^ 2 := by
        rw [sq_abs]; linarith [abs_nonneg (C.f i y)]
      calc C.g i y ^ 2 * C.Γ j i ^ 2 ≤ C.g i y ^ 2 * G :=
            mul_le_mul_of_nonneg_left (hΓ i) (sq_nonneg _)
        _ ≤ (|C.f i y| + |C.g i y| ^ 2) * G := mul_le_mul_of_nonneg_right hgsq hG0
        _ = G * (|C.f i y| + |C.g i y| ^ 2) := mul_comm _ _
    rw [← Finset.mul_sum] at hsum
    have hQ0 : ∑ i, (|C.f i y| + |C.g i y| ^ 2) ≤ Q := by simp only [hQ]; linarith
    calc ∑ i, aa i ^ 2 ≤ G * ∑ i, (|C.f i y| + |C.g i y| ^ 2) := hsum
      _ ≤ G * Q := mul_le_mul_of_nonneg_left hQ0 hG0
  have hQ0 : 0 ≤ Q := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      add_nonneg (abs_nonneg (C.f i y)) (sq_nonneg |C.g i y|)
    simp only [hQ]; linarith
  have h5 : G * Q ≤ G * (S ^ δ * Q) := by
    have hSd : 1 ≤ S ^ δ := Real.one_le_rpow hS1 hδ
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hQ0 hSd) hG0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc itoIntegrand C c j y ^ 2 ≤ (n : ℝ) * ∑ i, aa i ^ 2 := h2.trans h3
    _ ≤ (n : ℝ) * (G * (S ^ δ * Q)) := mul_le_mul_of_nonneg_left (h4.trans h5) hn0
    _ = ((n : ℝ) * G) * (S ^ δ * Q) := by ring

/-- Part 2 of Lemma 5.4 ((5.17)): the martingale term divided by `t` tends to `0` a.s. -/
theorem part2 (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : StochKolmogorov.Classify.Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : StochKolmogorov.Classify.IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ)
    (hA : StochKolmogorov.Classify.Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : StochKolmogorov.Classify.IsDelta0 C γb δ₀) :
    ∀ x ∈ StochKolmogorov.Classify.orthant n, ∀ J : Fin n → ℝ≥0 → Ω → ℝ,
      (∀ j, (∀ ω, Continuous (fun t => J j t ω)) ∧
        HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
          (fun t ω => B t ω j) (fun t ω => itoIntegrand C c j (X x t ω)) (J j)) →
      ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => (∑ j, J j t ω) / (t : ℝ)) atTop (𝓝 0) := by
  intro x hx J hJ
  obtain ⟨hP, hB, hsol⟩ := hX
  have := hP
  have hXx := hsol x hx
  have hXP : StochKolmogorov.Persist.IsSolutionFamily P (toP C) B X := ⟨hP, hB, hsol⟩
  obtain ⟨H₂, hH₂, h38⟩ := ItoLib.clause38 hn P (toP C) B X hXP c γb hA δ₀ hδ₀
  have hall : ∀ᵐ ω ∂P, ∀ u, X x u ω ∈ StochKolmogorov.Classify.orthant n :=
    ItoLib.orthant_inv_all P (toP C) B hB hA.2.1 hx hXx
  have hc : c ∈ StochKolmogorov.Classify.openOrthant n := hA.2.2.1
  have hδ0 : 0 ≤ δ₀ := hδ₀.1.le
  have hgc : ∀ i, ContinuousOn (C.g i) (StochKolmogorov.Classify.orthant n) :=
    fun i => (hA.2.1 i).2.continuousOn
  set K0 : ℝ := (n : ℝ) * ∑ a, ∑ b, C.Γ a b ^ 2 with hK0
  have hK00 : 0 ≤ K0 := mul_nonneg (Nat.cast_nonneg n)
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
  set A : ℝ := (1 + ∑ i, c i * x i) ^ δ₀ with hAdef
  have hA0 : 0 ≤ A := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hc i).le (hx i)
    exact Real.rpow_nonneg (by linarith) _
  have hj : ∀ j : Fin n, ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => J j t ω / (t : ℝ)) atTop (𝓝 0) := by
    intro j
    have hcont := itoIntegrand_continuous C hc hgc j
    set g : ℝ≥0 → Ω → ℝ := fun s ω => itoIntegrand C c j (X x s ω) with hgdef
    have hgm : ∀ s, Measurable[completedBrownianPast P B (fun _ => x) s] (g s) :=
      fun s => hcont.measurable.comp (hXx.2.2.1 s)
    have hga : ∀ s, Measurable (g s) := fun s => hcont.measurable.comp (hXx.1 s)
    have hgc' : ∀ ω, Continuous fun s => g s ω := fun ω => hcont.comp (hXx.2.1 ω)
    have hL : HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
        (fun s ω => B s ω j) (fun s ω => g s ω * 1) (J j) := by
      simpa only [mul_one] using (hJ j).2
    refine slln_exp hB x j g hgm hga hgc' 1 (J j) hL (hJ j).1 (K := K0 * H₂ * (A + 1)) ?_
    intro T
    rcases Nat.eq_zero_or_pos T with hT0 | hT
    · subst hT0; simp
    have hT' : (0 : ℝ≥0) < (T : ℝ≥0) := by exact_mod_cast hT
    have h38T := h38 x hx (T : ℝ≥0) hT'
    have hTr : ((T : ℝ≥0) : ℝ) = (T : ℝ) := NNReal.coe_natCast T
    rw [hTr] at h38T
    set F : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
        (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2))) with hF
    have h38F : ∫⁻ ω, F ω ∂P ≤ ENNReal.ofReal (H₂ * (A + T)) := h38T
    have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ u in (0 : ℝ)..(T : ℝ), g u.toNNReal ω ^ 2) ≤
        ENNReal.ofReal K0 * F ω := by
      filter_upwards [hall] with ω hω
      have hcu : Continuous fun u : ℝ => g u.toNNReal ω ^ 2 :=
        ((hgc' ω).comp continuous_real_toNNReal).pow 2
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg T), ofReal_integral_eq_lintegral_ofReal
        (hcu.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (ae_of_all _ fun u => sq_nonneg _)]
      calc ∫⁻ u in Ioc 0 (T : ℝ), ENNReal.ofReal (g u.toNNReal ω ^ 2)
          ≤ ∫⁻ u in Icc 0 (T : ℝ), ENNReal.ofReal (g u.toNNReal ω ^ 2) :=
            lintegral_mono_set Ioc_subset_Icc_self
        _ ≤ ∫⁻ u in Icc 0 (T : ℝ), ENNReal.ofReal K0 *
              ENNReal.ofReal ((1 + ∑ i, c i * X x u.toNNReal ω i) ^ δ₀ *
                (1 + ∑ i, (|C.f i (X x u.toNNReal ω)| + |C.g i (X x u.toNNReal ω)| ^ 2))) := by
            refine lintegral_mono fun u => ?_
            rw [← ENNReal.ofReal_mul hK00]
            exact ENNReal.ofReal_le_ofReal (itoIntegrand_sq_le C hc j hδ0 (hω _))
        _ = ENNReal.ofReal K0 * F ω := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..(T : ℝ), g u.toNNReal ω ^ 2) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal K0 * F ω ∂P := lintegral_mono_ae hpt
      _ = ENNReal.ofReal K0 * ∫⁻ ω, F ω ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K0 * ENNReal.ofReal (H₂ * (A + T)) := by gcongr
      _ = ENNReal.ofReal (K0 * (H₂ * (A + T))) := (ENNReal.ofReal_mul hK00).symm
      _ ≤ ENNReal.ofReal (K0 * H₂ * (A + 1) * (1 + T)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
          have hKH : 0 ≤ K0 * H₂ := mul_nonneg hK00 hH₂.le
          have : A + T ≤ (A + 1) * (1 + T) := by linarith [mul_nonneg hA0 hT0]
          calc K0 * (H₂ * (A + T)) = (K0 * H₂) * (A + T) := by ring
            _ ≤ (K0 * H₂) * ((A + 1) * (1 + T)) := mul_le_mul_of_nonneg_left this hKH
            _ = K0 * H₂ * (A + 1) * (1 + T) := by ring
  filter_upwards [ae_all_iff.2 hj] with ω hω
  have h := tendsto_finset_sum (Finset.univ : Finset (Fin n)) (fun j _ => hω j)
  rw [Finset.sum_const_zero] at h
  exact h.congr fun t => (Finset.sum_div _ _ _).symm

end Part2
end ItoLib.G73

end FlatM_Part2
-- ===== QJ =====
section FlatM_QJ
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QJan
/-! Clause 1 toolkit (E4, part 1): analysis helpers. -/

end QJan

section QJ
/-! Clause 1 toolkit (E4, part 1): the continuous Ito integral as a function, and the Picard map. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QJ
end ItoLib

end FlatM_QJ
-- ===== QK =====
section FlatM_QK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QKan

end QKan

section QK
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QK
end ItoLib

end FlatM_QK
-- ===== QL =====
section FlatM_QL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QL
/-! Clause 1 toolkit (E4, part 3): initial bound and the Picard moment bound. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QL
end ItoLib

end FlatM_QL
-- ===== QM =====
section FlatM_QM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QM
/-! Clause 1 toolkit (E4, part 4): Borel–Cantelli for the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QM
end ItoLib

end FlatM_QM
-- ===== QN =====
section FlatM_QN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Nat
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QN
/-! Clause 1 toolkit (E4, part 5): almost-sure geometric convergence of the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QN
end ItoLib

end FlatM_QN
-- ===== QO =====
section FlatM_QO
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QO
/-! Clause 1 toolkit (E4, part 6): the Picard limit process. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QO
end ItoLib

end FlatM_QO
-- ===== QP =====
section FlatM_QP
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QP
/-! Clause 1 toolkit (E4, part 7): the Picard limit solves the SDE (bounded Lipschitz case). -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QP
end ItoLib

end FlatM_QP
-- ===== QZ4 =====
section FlatM_QZ4
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QZ4
/-! Clause 1 toolkit (E4, final): strong existence for bounded globally Lipschitz coefficients. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QZ4
end ItoLib

end FlatM_QZ4
-- ===== E5A =====
section FlatM_E5A
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5A
/-! Clause 1 toolkit (E5, part 1): two solutions from the same point, of SDEs whose bounded
coefficients agree on a ball, coincide as long as the first stays in a smaller ball. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5A

end ItoLib

end FlatM_E5A
-- ===== E5B =====
section FlatM_E5B
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5B
/-! Clause 1 toolkit (E5, part 2): gluing a consistent, non-exploding family of truncated
solutions into a global strong solution. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5B

end ItoLib

end FlatM_E5B
-- ===== E6F =====
section FlatM_E6F
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6F
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6F

end ItoLib

end FlatM_E6F
-- ===== E6P =====
section FlatM_E6P
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6P
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6P

end ItoLib

end FlatM_E6P
-- ===== E6Q =====
section FlatM_E6Q
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6Q
/-! Clause 1 toolkit (E6, part 2): a solution of a Kolmogorov-structured SDE started in the
orthant stays in the orthant for all times, almost surely. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6Q

end ItoLib

end FlatM_E6Q
-- ===== E6T =====
section FlatM_E6T
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6T
/-! Clause 1 toolkit (E6, part 3): a Kolmogorov-structured truncation of the coefficients:
evaluate the true coefficients at the box projection `boxP (-R) R y`. It is bounded, globally
Lipschitz, equal to the true coefficients on the box, and of the form `y_k * (bounded)`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6T

end ItoLib

end FlatM_E6T
-- ===== E6L =====
section FlatM_E6L
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6L
/-! Clause 1 toolkit (E6, part 4): the saturated Lyapunov profile `lyS m = hsat m ∘ psiK`,
derivatives of `y ↦ ψ(cᵀy)`, and the time-slot test function
`F(x,y,a) = e^{-a} (Φ(y) + K (T - x_{i0}) - λ) + λ` with its generator. -/
open StochKolmogorov.Persist

theorem contDiff_deriv_of_two {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) : ContDiff ℝ 1 (deriv ψ) := by
  have h := hψ
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h
  exact (contDiff_succ_iff_deriv.1 h).2.2

variable {n : ℕ}

theorem lin_comp_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (cv : SDEState n) :
    ContDiff ℝ 2 (fun y : SDEState n => ψ (∑ k, cv k * y k)) :=
  hψ.comp (ContDiff.sum fun k _ => contDiff_const.mul (coord_contDiff k))

theorem lin_line (cv y v : SDEState n) (r : ℝ) :
    ∑ k, cv k * (y + r • v) k = ∑ k, cv k * y k + r * ∑ k, cv k * v k := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem lin_comp_fderiv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (cv y v : SDEState n) :
    fderiv ℝ (fun y : SDEState n => ψ (∑ k, cv k * y k)) y v =
      deriv ψ (∑ k, cv k * y k) * ∑ k, cv k * v k := by
  refine fderiv_eq_of_line ((lin_comp_contDiff hψ cv).differentiable two_ne_zero) y v ?_
  simp only [lin_line]
  have h := ((hψ.differentiable two_ne_zero) (∑ k, cv k * y k + 0 * ∑ k, cv k * v k)).hasDerivAt.comp
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).mul_const (∑ k, cv k * v k)).const_add (∑ k, cv k * y k))
  simpa [Function.comp_def] using h

theorem lin_comp_fderiv2 {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (cv y v : SDEState n) :
    fderiv ℝ (fderiv ℝ (fun y : SDEState n => ψ (∑ k, cv k * y k))) y v v =
      deriv (deriv ψ) (∑ k, cv k * y k) * (∑ k, cv k * v k) ^ 2 := by
  have hψ1 := contDiff_deriv_of_two hψ
  refine fderiv2_eq_of_line (lin_comp_contDiff hψ cv) y v
    (φ' := fun s => deriv ψ (∑ k, cv k * y k + s * ∑ k, cv k * v k) * ∑ k, cv k * v k)
    (fun s => ?_) ?_
  · simp only [lin_line]
    have h := ((hψ.differentiable two_ne_zero)
      (∑ k, cv k * y k + s * ∑ k, cv k * v k)).hasDerivAt.comp s
      (((hasDerivAt_id s).mul_const (∑ k, cv k * v k)).const_add (∑ k, cv k * y k))
    simpa [Function.comp_def] using h
  · have h := ((hψ1.differentiable one_ne_zero)
      (∑ k, cv k * y k + 0 * ∑ k, cv k * v k)).hasDerivAt.comp (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).mul_const (∑ k, cv k * v k)).const_add (∑ k, cv k * y k))
    have h2 := h.mul_const (∑ k, cv k * v k)
    simp only [zero_mul, add_zero, one_mul, Function.comp_def, id] at h2
    exact h2.congr_deriv (by ring)

/-- The generator of `y ↦ ψ(cᵀy)` is `genL`. -/
theorem lin_comp_gen {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (cv : SDEState n) (σ : SDEDiffusion n)
    (b y : SDEState n) :
    fderiv ℝ (fun y : SDEState n => ψ (∑ k, cv k * y k)) y b +
      (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ (fun y : SDEState n => ψ (∑ k, cv k * y k))) y
        (scol σ j) (scol σ j) = genL ψ cv σ b y := by
  unfold genL
  rw [lin_comp_fderiv hψ]
  simp only [lin_comp_fderiv2 hψ, scol_apply']

end E6L

section E6Lb
variable {d : ℕ}

end E6Lb

end ItoLib

end FlatM_E6L
-- ===== Part1a =====
section FlatM_Part1a
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Part1a
variable {n : ℕ}
open StochKolmogorov.Classify

lemma isDelta0_mono (C : StochKolmogorov.Classify.Coeffs n) {γb δ₀ δ₁ : ℝ}
    (h : StochKolmogorov.Classify.IsDelta0 C γb δ₀) (h1 : 0 < δ₁) (h12 : δ₁ ≤ δ₀) :
    StochKolmogorov.Classify.IsDelta0 C γb δ₁ := by
  obtain ⟨h0, hlt, hD⟩ := h
  refine ⟨h1, lt_of_le_of_lt h12 hlt, fun x hx => ?_⟩
  have hS : 0 ≤ ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hG : 0 ≤ ∑ i, C.g i x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have := hD x hx
  nlinarith [mul_le_mul_of_nonneg_left h12 hS, mul_le_mul_of_nonneg_left h12 hG]

/-- Consequence of Assumption 1.4: `(1 + cᵀy)^δ ∑ gᵢ² ≤ K (1 + ∑ (|fᵢ| + gᵢ²))` on `ℝⁿ₊`. -/
lemma a14_bound (C : StochKolmogorov.Classify.Coeffs n) {c : SDEState n}
    (hc : c ∈ StochKolmogorov.Classify.openOrthant n)
    (hg : ∀ i, ContinuousOn (C.g i) (StochKolmogorov.Classify.orthant n)) {δ : ℝ}
    (h14 : StochKolmogorov.Classify.Assumption14 C δ) :
    ∃ K, 0 ≤ K ∧ ∀ y ∈ StochKolmogorov.Classify.orthant n,
      (1 + ∑ i, c i * y i) ^ δ * ∑ i, C.g i y ^ 2 ≤
        K * (1 + ∑ i, (|C.f i y| + C.g i y ^ 2)) := by
  obtain ⟨hδ, ht⟩ := h14
  have hev := ht.eventually (gt_mem_nhds zero_lt_one)
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  set R1 : ℝ := max R 1 with hR1
  set cm : ℝ := ∑ k, c k with hcm
  have hcm0 : 0 ≤ cm := Finset.sum_nonneg fun k _ => (hc k).le
  have hco : ∀ i, Continuous fun y : SDEState n => StochKolmogorov.Classify.posPart y i :=
    fun i => (cl_coord_cont i).comp cl_posPart_cont
  have hgi : ∀ i, Continuous fun y : SDEState n => C.g i (StochKolmogorov.Classify.posPart y) :=
    fun i => (hg i).comp_continuous cl_posPart_cont cl_posPart_mem
  have hden : ∀ y : SDEState n, 0 < 1 + ∑ i, c i * StochKolmogorov.Classify.posPart y i := by
    intro y
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      mul_nonneg (hc i).le (cl_posPart_mem y i)
    linarith
  have hGc : Continuous fun y : SDEState n =>
      (1 + ∑ i, c i * StochKolmogorov.Classify.posPart y i) ^ δ *
        ∑ i, C.g i (StochKolmogorov.Classify.posPart y) ^ 2 :=
    ((continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (hco i))).rpow_const
      fun y => Or.inl (hden y).ne').mul (continuous_finset_sum _ fun i _ => (hgi i).pow 2)
  obtain ⟨K2, hK2⟩ := ItoLib.bdd_on_ell hc hGc (cm * R1)
  refine ⟨(1 + cm) ^ δ + |K2|, add_nonneg (Real.rpow_nonneg (by linarith) _) (abs_nonneg _),
    fun y hy => ?_⟩
  set Q : ℝ := 1 + ∑ i, (|C.f i y| + C.g i y ^ 2) with hQ
  have hQ1 : 1 ≤ Q := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      add_nonneg (abs_nonneg (C.f i y)) (sq_nonneg (C.g i y))
    linarith
  have hQ0 : 0 < Q := by linarith
  have hcy0 : 0 ≤ ∑ i, c i * y i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hy i)
  have hl0 : 0 ≤ StochKolmogorov.Classify.l1 y :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hcy : ∑ i, c i * y i ≤ cm * StochKolmogorov.Classify.l1 y := by
    rw [hcm, Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (ItoLib.le_l1 y k) (hc k).le
  have hG0 : 0 ≤ ∑ i, C.g i y ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hpow0 : 0 ≤ (1 + ∑ i, c i * y i) ^ δ := Real.rpow_nonneg (by linarith) _
  by_cases hy1 : R1 ≤ StochKolmogorov.Classify.l1 y
  · have hl1 : 1 ≤ StochKolmogorov.Classify.l1 y := le_trans (le_max_right _ _) hy1
    have hrat := hR (StochKolmogorov.Classify.l1 y) (le_trans (le_max_left _ _) hy1) y rfl hy
    have hlq : StochKolmogorov.Classify.l1 y ^ δ * ∑ i, C.g i y ^ 2 ≤ Q :=
      ((div_lt_one hQ0).1 hrat).le
    have hbase : 1 + ∑ i, c i * y i ≤ (1 + cm) * StochKolmogorov.Classify.l1 y := by
      linarith
    have hp : (1 + ∑ i, c i * y i) ^ δ ≤ (1 + cm) ^ δ * StochKolmogorov.Classify.l1 y ^ δ := by
      rw [← Real.mul_rpow (by linarith) hl0]
      exact Real.rpow_le_rpow (by linarith) hbase hδ.le
    have hcmp : 0 ≤ (1 + cm) ^ δ := Real.rpow_nonneg (by linarith) _
    calc (1 + ∑ i, c i * y i) ^ δ * ∑ i, C.g i y ^ 2
        ≤ ((1 + cm) ^ δ * StochKolmogorov.Classify.l1 y ^ δ) * ∑ i, C.g i y ^ 2 :=
          mul_le_mul_of_nonneg_right hp hG0
      _ = (1 + cm) ^ δ * (StochKolmogorov.Classify.l1 y ^ δ * ∑ i, C.g i y ^ 2) := by ring
      _ ≤ (1 + cm) ^ δ * Q := mul_le_mul_of_nonneg_left hlq hcmp
      _ ≤ ((1 + cm) ^ δ + |K2|) * Q :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hQ0.le
  · push_neg at hy1
    have hcR : ∑ k, c k * y k ≤ cm * R1 :=
      hcy.trans (mul_le_mul_of_nonneg_left hy1.le hcm0)
    have hb := hK2 y hy hcR
    rw [cl_posPart_eq hy] at hb
    have hle : (1 + ∑ i, c i * y i) ^ δ * ∑ i, C.g i y ^ 2 ≤ |K2| :=
      (le_abs_self _).trans (hb.trans (le_abs_self _))
    have hK20 : 0 ≤ |K2| := abs_nonneg _
    have hcmp : 0 ≤ (1 + cm) ^ δ := Real.rpow_nonneg (by linarith) _
    linarith [mul_le_mul_of_nonneg_left hQ1 hK20, mul_nonneg hcmp hQ0.le]

/-- Coordinate form of the generator of `y ↦ ψ(cᵀy)` (the drift terms of `ito_formula`). -/
lemma drift_gen {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (c : SDEState n) (σ : SDEDiffusion n)
    (b y : SDEState n) :
    (∑ i, fderiv ℝ (fun y : SDEState n => ψ (∑ k, c k * y k)) y
        (EuclideanSpace.single i 1) * b i) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, fderiv ℝ (fderiv ℝ (fun y : SDEState n => ψ (∑ k, c k * y k))) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) * σ (i, j) * σ (i', j)
      = genL ψ c σ b y := by
  rw [← lin_comp_gen hψ c σ b y,
    clm_coord (fderiv ℝ (fun y : SDEState n => ψ (∑ k, c k * y k)) y) b]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · congr 1
    rw [Finset.sum_congr rfl fun j _ => clm2_coord
      (fderiv ℝ (fderiv ℝ (fun y : SDEState n => ψ (∑ k, c k * y k))) y) (scol σ j) (scol σ j)]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [scol_apply']
    ring

/-- Itô's formula for `ψ_δ(cᵀY)` along a solution of (1.1), at a fixed time. -/
theorem ito_psi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : StochKolmogorov.Classify.Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (StochKolmogorov.Classify.orthant n) (C.f i) ∧
      LocallyLipschitzOn (StochKolmogorov.Classify.orthant n) (C.g i))
    (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B) {x : SDEState n}
    {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (StochKolmogorov.Classify.diffusion C)
      (StochKolmogorov.Classify.drift C) B (fun _ => x) Y) (c : SDEState n) (δ : ℝ)
    {K : Fin n → Fin n → ℝ≥0 → Ω → ℝ}
    (hK : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
      (fun s ω => B s ω j)
      (fun s ω => fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k)) (Y s ω)
        (EuclideanSpace.single i 1) * StochKolmogorov.Classify.diffusion C (s, Y s ω) (i, j))
      (K i j)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, psiD δ (∑ k, c k * Y t ω k) = psiD δ (∑ k, c k * x k) + (∑ i, ∑ j, K i j t ω) +
      ∫ u in (0 : ℝ)..t.val, genL (psiD δ) c
        (StochKolmogorov.Classify.diffusion C (0, Y u.toNNReal ω))
        (StochKolmogorov.Classify.drift C (0, Y u.toNNReal ω)) (Y u.toNNReal ω) := by
  obtain ⟨hYm, hYc, hYa, hY0, Jd, -, -, hJ, -, hrep⟩ := hY
  obtain ⟨hσc, hbc, -⟩ := ItoLib.kolm_trunc (toP C) hC
  have hσc' : Continuous fun y : SDEState n => StochKolmogorov.Classify.diffusion C (0, y) := hσc
  have hbc' : Continuous fun y : SDEState n => StochKolmogorov.Classify.drift C (0, y) := hbc
  have hHc0 : ∀ i j, Continuous fun y : SDEState n =>
      StochKolmogorov.Classify.diffusion C (0, y) (i, j) := fun i j =>
    (continuous_apply (i, j)).comp ((PiLp.continuous_ofLp 2 _).comp hσc')
  have hbc0 : ∀ i, Continuous fun y : SDEState n =>
      StochKolmogorov.Classify.drift C (0, y) i := fun i =>
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp hbc')
  have hf : ContDiff ℝ 2 (fun y : SDEState n => psiD δ (∑ k, c k * y k)) :=
    lin_comp_contDiff (psiD_contDiff δ) c
  have hito := ito_formula hB x hYm hYc hYa
    (H := fun i j s ω => StochKolmogorov.Classify.diffusion C (s, Y s ω) (i, j))
    (J := fun i j s ω => Jd s ω (i, j))
    (b := fun i s ω => StochKolmogorov.Classify.drift C (s, Y s ω) i)
    (fun i j s => (hHc0 i j).measurable.comp (hYa s))
    (fun i j ω => (hHc0 i j).comp (hYc ω)) hJ
    (fun i s => (hbc0 i).measurable.comp (hYa s))
    (fun i ω => (hbc0 i).comp (hYc ω)) hrep hf hK t
  have hD1c : Continuous (fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k))) :=
    hf.continuous_fderiv two_ne_zero
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k)))) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  filter_upwards [hito, hY0] with ω h h0
  have h0' : Y 0 ω = x := h0
  beta_reduce at h
  rw [h, h0', add_assoc]
  congr 1
  have hYu : Continuous fun u : ℝ => Y u.toNNReal ω := (hYc ω).comp continuous_real_toNNReal
  have hA : ∀ i, Continuous fun u : ℝ =>
      fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k)) (Y u.toNNReal ω)
        (EuclideanSpace.single i 1) *
        StochKolmogorov.Classify.drift C (u.toNNReal, Y u.toNNReal ω) i := fun i =>
    ((hD1c.clm_apply continuous_const).comp hYu).mul ((hbc0 i).comp hYu)
  have hBc : ∀ i i' j, Continuous fun u : ℝ =>
      fderiv ℝ (fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k))) (Y u.toNNReal ω)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) *
        StochKolmogorov.Classify.diffusion C (u.toNNReal, Y u.toNNReal ω) (i, j) *
        StochKolmogorov.Classify.diffusion C (u.toNNReal, Y u.toNNReal ω) (i', j) :=
    fun i i' j => ((((hD2c.clm_apply continuous_const).clm_apply continuous_const).comp hYu).mul
      ((hHc0 i j).comp hYu)).mul ((hHc0 i' j).comp hYu)
  have hi1 := (continuous_finset_sum (Finset.univ : Finset (Fin n)) fun i _ => hA i).intervalIntegrable
    (μ := volume) 0 t.val
  have hi2 := (continuous_finset_sum (Finset.univ : Finset (Fin n)) fun i _ =>
    continuous_finset_sum (Finset.univ : Finset (Fin n)) fun i' _ =>
      continuous_finset_sum (Finset.univ : Finset (Fin n)) fun j _ => hBc i i' j).intervalIntegrable
        (μ := volume) 0 t.val
  have hpt : ∀ u : ℝ, genL (psiD δ) c
      (StochKolmogorov.Classify.diffusion C (0, Y u.toNNReal ω))
      (StochKolmogorov.Classify.drift C (0, Y u.toNNReal ω)) (Y u.toNNReal ω) =
      (∑ i, fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k)) (Y u.toNNReal ω)
        (EuclideanSpace.single i 1) *
        StochKolmogorov.Classify.drift C (u.toNNReal, Y u.toNNReal ω) i) +
      (1 / 2) * ∑ i, ∑ i', ∑ j,
        fderiv ℝ (fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k))) (Y u.toNNReal ω)
          (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) *
          StochKolmogorov.Classify.diffusion C (u.toNNReal, Y u.toNNReal ω) (i, j) *
          StochKolmogorov.Classify.diffusion C (u.toNNReal, Y u.toNNReal ω) (i', j) :=
    fun u => (drift_gen (psiD_contDiff δ) c _ _ _).symm
  rw [integral_sum_cont _ hA, integral_sum3 _ hBc,
    intervalIntegral.integral_congr (fun u _ => hpt u),
    intervalIntegral.integral_add hi1 (hi2.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul]

end Part1a
end ItoLib.G73

end FlatM_Part1a
-- ===== Part1 =====
section FlatM_Part1
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Part1
variable {n : ℕ}

lemma w38_eq_gw (C : StochKolmogorov.Classify.Coeffs n) {c : SDEState n}
    (hc : c ∈ StochKolmogorov.Classify.openOrthant n) (κ δ : ℝ) {y : SDEState n}
    (hy : y ∈ StochKolmogorov.Classify.orthant n) :
    w38 (toP C) c κ δ y = κ * StochKolmogorov.Classify.growthWeight C c δ y := by
  have hS : 0 ≤ ∑ k, c k * y k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hy k)
  unfold w38 StochKolmogorov.Classify.growthWeight
  rw [ItoLib.posPart_of_mem hy, psiD_eq (by linarith)]
  simp only [toP]
  ring

lemma gij_sq_le (C : StochKolmogorov.Classify.Coeffs n) {c : SDEState n}
    (hc : c ∈ StochKolmogorov.Classify.openOrthant n) {δ K14 : ℝ} (hK14 : 0 ≤ K14)
    (h14 : ∀ y ∈ StochKolmogorov.Classify.orthant n,
      (1 + ∑ i, c i * y i) ^ δ * ∑ i, C.g i y ^ 2 ≤ K14 * (1 + ∑ i, (|C.f i y| + C.g i y ^ 2)))
    (i j : Fin n) (s : ℝ≥0) {y : SDEState n} (hy : y ∈ StochKolmogorov.Classify.orthant n) :
    (fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k)) y (EuclideanSpace.single i 1) *
        StochKolmogorov.Classify.diffusion C (s, y) (i, j)) ^ 2 ≤
      (δ ^ 2 * C.Γ j i ^ 2 * K14) *
        ((1 + ∑ i, c i * y i) ^ δ * (1 + ∑ i, (|C.f i y| + |C.g i y| ^ 2))) := by
  set S : ℝ := ∑ k, c k * y k with hSdef
  have hcy : ∀ k, 0 ≤ c k * y k := fun k => mul_nonneg (hc k).le (hy k)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => hcy k
  have hfd : fderiv ℝ (fun y : SDEState n => psiD δ (∑ k, c k * y k)) y
      (EuclideanSpace.single i 1) = deriv (psiD δ) S * c i := by
    rw [lin_comp_fderiv (psiD_contDiff δ)]
    congr 1
    simp [EuclideanSpace.single_apply]
  have hdiff : StochKolmogorov.Classify.diffusion C (s, y) (i, j) = y i * C.g i y * C.Γ j i := by
    show y i * C.g i (StochKolmogorov.Classify.posPart y) * C.Γ j i = _
    rw [cl_posPart_eq hy]
  rw [hfd, hdiff, deriv_psiD (by linarith), deriv_psiK (by linarith), psiD_eq (by linarith)]
  set p : ℝ := (1 + S) ^ δ with hp
  have hp0 : 0 ≤ p := Real.rpow_nonneg (by linarith) _
  have hS1 : 0 < 1 + S := by linarith
  set r : ℝ := c i * y i * (1 + S)⁻¹ with hr
  have hci : c i * y i ≤ 1 + S := by
    have := Finset.single_le_sum (f := fun k => c k * y k) (fun k _ => hcy k)
      (Finset.mem_univ i)
    simp only at this
    linarith
  have hr0 : 0 ≤ r := mul_nonneg (hcy i) (inv_nonneg.2 hS1.le)
  have hr1 : r ≤ 1 := by
    rw [hr, ← div_eq_mul_inv, div_le_one hS1]; exact hci
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  set Q : ℝ := 1 + ∑ i, (|C.f i y| + C.g i y ^ 2) with hQ
  have hQ' : (1 + ∑ i, (|C.f i y| + |C.g i y| ^ 2)) = Q := by simp only [hQ, sq_abs]
  rw [hQ']
  have hgi : p * C.g i y ^ 2 ≤ K14 * Q := by
    have h1 := h14 y hy
    have h2 : C.g i y ^ 2 ≤ ∑ k, C.g k y ^ 2 :=
      Finset.single_le_sum (f := fun k => C.g k y ^ 2) (fun k _ => sq_nonneg _)
        (Finset.mem_univ i)
    calc p * C.g i y ^ 2 ≤ p * ∑ k, C.g k y ^ 2 := mul_le_mul_of_nonneg_left h2 hp0
      _ ≤ K14 * Q := h1
  have hpg0 : 0 ≤ p * C.g i y ^ 2 := mul_nonneg hp0 (sq_nonneg _)
  have hD : 0 ≤ δ ^ 2 * C.Γ j i ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have heq : (δ * p * (1 + S)⁻¹ * c i * (y i * C.g i y * C.Γ j i)) ^ 2 =
      (δ ^ 2 * C.Γ j i ^ 2) * p * r ^ 2 * (p * C.g i y ^ 2) := by
    rw [hr]; ring
  rw [heq]
  calc (δ ^ 2 * C.Γ j i ^ 2) * p * r ^ 2 * (p * C.g i y ^ 2)
      ≤ (δ ^ 2 * C.Γ j i ^ 2) * p * 1 * (p * C.g i y ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (mul_nonneg hD hp0)) hpg0
    _ ≤ (δ ^ 2 * C.Γ j i ^ 2) * p * 1 * (K14 * Q) :=
        mul_le_mul_of_nonneg_left hgi (mul_nonneg (mul_nonneg hD hp0) zero_le_one)
    _ = (δ ^ 2 * C.Γ j i ^ 2 * K14) * (p * Q) := by ring

/-- Expected quadratic variation from clause (3.8). -/
lemma qv_from38 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : StochKolmogorov.Classify.Coeffs n) (c : SDEState n) (δ : ℝ)
    {Y : ℝ≥0 → Ω → SDEState n}
    (hall : ∀ᵐ ω ∂P, ∀ u, Y u ω ∈ StochKolmogorov.Classify.orthant n)
    {G : SDEState n → ℝ} (hYG : ∀ ω, Continuous fun u : ℝ => G (Y u.toNNReal ω))
    {K0 : ℝ} (hK00 : 0 ≤ K0)
    (hGle : ∀ y ∈ StochKolmogorov.Classify.orthant n, G y ^ 2 ≤
      K0 * ((1 + ∑ i, c i * y i) ^ δ * (1 + ∑ i, (|C.f i y| + |C.g i y| ^ 2))))
    {H₂ A : ℝ} (hH₂ : 0 < H₂) (hA0 : 0 ≤ A)
    (h38 : ∀ t : ℝ≥0, 0 < t → ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal ((1 + ∑ i, c i * Y s.toNNReal ω i) ^ δ *
        (1 + ∑ i, (|C.f i (Y s.toNNReal ω)| + |C.g i (Y s.toNNReal ω)| ^ 2)))) ∂P ≤
      ENNReal.ofReal (H₂ * (A + t))) :
    ∀ T : ℕ, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..(T : ℝ), G (Y u.toNNReal ω) ^ 2) ∂P ≤
      ENNReal.ofReal (K0 * H₂ * (A + 1) * (1 + T)) := by
  intro T
  rcases Nat.eq_zero_or_pos T with hT0 | hT
  · subst hT0; simp
  have hT' : (0 : ℝ≥0) < (T : ℝ≥0) := by exact_mod_cast hT
  have h38T := h38 (T : ℝ≥0) hT'
  have hTr : ((T : ℝ≥0) : ℝ) = (T : ℝ) := NNReal.coe_natCast T
  rw [hTr] at h38T
  set F : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
    ENNReal.ofReal ((1 + ∑ i, c i * Y s.toNNReal ω i) ^ δ *
      (1 + ∑ i, (|C.f i (Y s.toNNReal ω)| + |C.g i (Y s.toNNReal ω)| ^ 2))) with hF
  have h38F : ∫⁻ ω, F ω ∂P ≤ ENNReal.ofReal (H₂ * (A + T)) := h38T
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ u in (0 : ℝ)..(T : ℝ), G (Y u.toNNReal ω) ^ 2) ≤
      ENNReal.ofReal K0 * F ω := by
    filter_upwards [hall] with ω hω
    have hcu : Continuous fun u : ℝ => G (Y u.toNNReal ω) ^ 2 := (hYG ω).pow 2
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg T), ofReal_integral_eq_lintegral_ofReal
      (hcu.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (ae_of_all _ fun u => sq_nonneg _)]
    calc ∫⁻ u in Ioc 0 (T : ℝ), ENNReal.ofReal (G (Y u.toNNReal ω) ^ 2)
        ≤ ∫⁻ u in Icc 0 (T : ℝ), ENNReal.ofReal (G (Y u.toNNReal ω) ^ 2) :=
          lintegral_mono_set Ioc_subset_Icc_self
      _ ≤ ∫⁻ u in Icc 0 (T : ℝ), ENNReal.ofReal K0 *
            ENNReal.ofReal ((1 + ∑ i, c i * Y u.toNNReal ω i) ^ δ *
              (1 + ∑ i, (|C.f i (Y u.toNNReal ω)| + |C.g i (Y u.toNNReal ω)| ^ 2))) := by
          refine lintegral_mono fun u => ?_
          rw [← ENNReal.ofReal_mul hK00]
          exact ENNReal.ofReal_le_ofReal (hGle _ (hω _))
      _ = ENNReal.ofReal K0 * F ω := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..(T : ℝ), G (Y u.toNNReal ω) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal K0 * F ω ∂P := lintegral_mono_ae hpt
    _ = ENNReal.ofReal K0 * ∫⁻ ω, F ω ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K0 * ENNReal.ofReal (H₂ * (A + T)) := by gcongr
    _ = ENNReal.ofReal (K0 * (H₂ * (A + T))) := (ENNReal.ofReal_mul hK00).symm
    _ ≤ ENNReal.ofReal (K0 * H₂ * (A + 1) * (1 + T)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
        have hKH : 0 ≤ K0 * H₂ := mul_nonneg hK00 hH₂.le
        have : A + T ≤ (A + 1) * (1 + T) := by linarith [mul_nonneg hA0 hT0]
        calc K0 * (H₂ * (A + T)) = (K0 * H₂) * (A + T) := by ring
          _ ≤ (K0 * H₂) * ((A + 1) * (1 + T)) := mul_le_mul_of_nonneg_left this hKH
          _ = K0 * H₂ * (A + 1) * (1 + T) := by ring

end Part1
end ItoLib.G73

end FlatM_Part1
-- ===== Part1b =====
section FlatM_Part1b
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Part1b
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- Part 1 of Lemma 5.4: the time average of the growth weight `(1+cᵀX)^δ₁ (1 + Σ(|fᵢ|+gᵢ²))`
is eventually at most `Khat + ε`. -/
theorem part1 (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : StochKolmogorov.Classify.Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : StochKolmogorov.Classify.IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ)
    (hA : StochKolmogorov.Classify.Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : StochKolmogorov.Classify.IsDelta0 C γb δ₀) (δ₁ : ℝ)
    (h14 : StochKolmogorov.Classify.Assumption14 C δ₁) (hδ₁ : δ₁ ≤ δ₀) :
    ∃ Khat : ℝ, 0 < Khat ∧ ∀ x ∈ StochKolmogorov.Classify.orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal (StochKolmogorov.Classify.growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t) := by
  obtain ⟨hP, hB, hsol⟩ := hX
  have := hP
  have hXP : StochKolmogorov.Persist.IsSolutionFamily P (toP C) B X := ⟨hP, hB, hsol⟩
  have hδ1 : 0 < δ₁ := h14.1
  have hD1 : StochKolmogorov.Classify.IsDelta0 C γb δ₁ := isDelta0_mono C hδ₀ hδ1 hδ₁
  have hC := hA.2.1
  have hc : c ∈ StochKolmogorov.Classify.openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = δ₁ * γb / 2 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨K, hK0, hgen⟩ := ItoLib.genL38_le (toP C) c γb hA δ₁ hD1
  rw [← hκ] at hgen
  obtain ⟨H₂, hH₂, h38⟩ := ItoLib.clause38 hn P (toP C) B X hXP c γb hA δ₁ hD1
  have hgc : ∀ i, ContinuousOn (C.g i) (StochKolmogorov.Classify.orthant n) :=
    fun i => (hA.2.1 i).2.continuousOn
  obtain ⟨K14, hK14, h14b⟩ := a14_bound C hc hgc h14
  refine ⟨K / κ + 1, by positivity, fun x hx => ?_⟩
  have hXx := hsol x hx
  have hall : ∀ᵐ ω ∂P, ∀ u, X x u ω ∈ StochKolmogorov.Classify.orthant n :=
    ItoLib.orthant_inv_all P (toP C) B hB hA.2.1 hx hXx
  obtain ⟨hσc, hbc, -⟩ := ItoLib.kolm_trunc (toP C) hC
  have hσc' : Continuous fun y : SDEState n => StochKolmogorov.Classify.diffusion C (0, y) := hσc
  have hbc' : Continuous fun y : SDEState n => StochKolmogorov.Classify.drift C (0, y) := hbc
  have hf : ContDiff ℝ 2 (fun y : SDEState n => psiD δ₁ (∑ k, c k * y k)) :=
    lin_comp_contDiff (psiD_contDiff δ₁) c
  have hD1c : Continuous (fderiv ℝ (fun y : SDEState n => psiD δ₁ (∑ k, c k * y k))) :=
    hf.continuous_fderiv two_ne_zero
  have hGc : ∀ i j : Fin n, Continuous fun y : SDEState n =>
      fderiv ℝ (fun y : SDEState n => psiD δ₁ (∑ k, c k * y k)) y (EuclideanSpace.single i 1) *
        StochKolmogorov.Classify.diffusion C (0, y) (i, j) := fun i j =>
    (hD1c.clm_apply continuous_const).mul
      ((continuous_apply (i, j)).comp ((PiLp.continuous_ofLp 2 _).comp hσc'))
  have hL := fun i j : Fin n => contIto_unbdd hB x j (H := fun s ω =>
      fderiv ℝ (fun y : SDEState n => psiD δ₁ (∑ k, c k * y k)) (X x s ω)
        (EuclideanSpace.single i 1) * StochKolmogorov.Classify.diffusion C (0, X x s ω) (i, j))
    (fun s => (hGc i j).measurable.comp (hXx.2.2.1 s))
    (fun s => (hGc i j).measurable.comp (hXx.1 s)) (fun ω => (hGc i j).comp (hXx.2.1 ω))
  choose L hLc hLm hLa hL0 hLI _hLconv using hL
  have hA0 : 0 ≤ (1 + ∑ i, c i * x i) ^ δ₁ := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hc i).le (hx i)
    exact Real.rpow_nonneg (by linarith) _
  have hqv : ∀ i j : Fin n, ∀ T : ℕ, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..(T : ℝ),
      (fderiv ℝ (fun y : SDEState n => psiD δ₁ (∑ k, c k * y k)) (X x u.toNNReal ω)
        (EuclideanSpace.single i 1) *
          StochKolmogorov.Classify.diffusion C (0, X x u.toNNReal ω) (i, j)) ^ 2) ∂P ≤
      ENNReal.ofReal ((δ₁ ^ 2 * C.Γ j i ^ 2 * K14) * H₂ * ((1 + ∑ i, c i * x i) ^ δ₁ + 1) *
        (1 + T)) := fun i j =>
    qv_from38 C c δ₁ hall (fun ω => (hGc i j).comp ((hXx.2.1 ω).comp continuous_real_toNNReal))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hK14)
      (fun y hy => gij_sq_le C hc hK14 h14b i j 0 hy) hH₂ hA0 (fun t ht => h38 x hx t ht)
  have hsl : ∀ i j : Fin n, ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => L i j t ω / (t : ℝ)) atTop (𝓝 0) :=
    fun i j => slln_exp hB x j (fun s ω =>
      fderiv ℝ (fun y : SDEState n => psiD δ₁ (∑ k, c k * y k)) (X x s ω)
        (EuclideanSpace.single i 1) * StochKolmogorov.Classify.diffusion C (0, X x s ω) (i, j))
      (fun s => (hGc i j).measurable.comp (hXx.2.2.1 s))
      (fun s => (hGc i j).measurable.comp (hXx.1 s)) (fun ω => (hGc i j).comp (hXx.2.1 ω)) 1
      (L i j) (by simpa only [mul_one] using hLI i j) (hLc i j) (hqv i j)
  have hS : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => (∑ i, ∑ j, L i j t ω) / (t : ℝ)) atTop (𝓝 0) := by
    have h2 : ∀ᵐ ω ∂P, ∀ i j, Tendsto (fun t : ℝ≥0 => L i j t ω / (t : ℝ)) atTop (𝓝 0) :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hsl i j
    filter_upwards [h2] with ω hω
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin n)) fun i _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin n)) fun j _ => hω i j
    simp only [Finset.sum_const_zero] at h
    exact h.congr fun t => by simp only [Finset.sum_div]
  have hito : ∀ᵐ ω ∂P, ∀ N : ℕ, psiD δ₁ (∑ k, c k * X x (N : ℝ≥0) ω k) =
      psiD δ₁ (∑ k, c k * x k) + (∑ i, ∑ j, L i j (N : ℝ≥0) ω) +
        ∫ u in (0 : ℝ)..(N : ℝ), genL (psiD δ₁) c
          (StochKolmogorov.Classify.diffusion C (0, X x u.toNNReal ω))
          (StochKolmogorov.Classify.drift C (0, X x u.toNNReal ω)) (X x u.toNNReal ω) := by
    refine ae_all_iff.2 fun N => ?_
    have h := ito_psi C hC B hB hXx c δ₁ (K := L) (fun i j => hLI i j) (N : ℝ≥0)
    simpa only [NNReal.val_eq_coe, NNReal.coe_natCast] using h
  filter_upwards [hall, hito, hS] with ω hω hI hSω
  intro ε hε
  have hYu : Continuous fun u : ℝ => X x u.toNNReal ω := (hXx.2.1 ω).comp continuous_real_toNNReal
  have hwc : Continuous fun u : ℝ => w38 (toP C) c κ δ₁ (X x u.toNNReal ω) :=
    (w38_continuous (toP C) c κ δ₁ hC).comp hYu
  have hnat : ∀ N : ℕ, ∫ u in (0 : ℝ)..(N : ℝ), w38 (toP C) c κ δ₁ (X x u.toNNReal ω) ≤
      psiD δ₁ (∑ k, c k * x k) + K * N + ∑ i, ∑ j, L i j (N : ℝ≥0) ω := by
    intro N
    have h := hI N
    have hgc2 : Continuous fun u : ℝ => genL (psiD δ₁) c
        (StochKolmogorov.Classify.diffusion C (0, X x u.toNNReal ω))
        (StochKolmogorov.Classify.drift C (0, X x u.toNNReal ω)) (X x u.toNNReal ω) :=
      (genL_continuous (psiD_contDiff δ₁) c hσc' hbc').comp hYu
    have hmono : ∫ u in (0 : ℝ)..(N : ℝ), genL (psiD δ₁) c
        (StochKolmogorov.Classify.diffusion C (0, X x u.toNNReal ω))
        (StochKolmogorov.Classify.drift C (0, X x u.toNNReal ω)) (X x u.toNNReal ω) ≤
        ∫ u in (0 : ℝ)..(N : ℝ), (K - w38 (toP C) c κ δ₁ (X x u.toNNReal ω)) :=
      intervalIntegral.integral_mono_on (Nat.cast_nonneg N) (hgc2.intervalIntegrable _ _)
        ((continuous_const.sub hwc).intervalIntegrable _ _) fun u _ => hgen _ (hω _)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hwc.intervalIntegrable _ _)] at hmono
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    have hψN := psiD_nonneg δ₁ (∑ k, c k * X x (N : ℝ≥0) ω k)
    linarith
  have hw0 : ∀ u : ℝ, 0 ≤ w38 (toP C) c κ δ₁ (X x u.toNNReal ω) :=
    fun u => w38_nonneg (toP C) c hκ0.le δ₁ _
  have hlin : ∀ N : ℕ, ∀ t : ℝ, t ≤ N →
      ∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal (StochKolmogorov.Classify.growthWeight C c δ₁ (X x s.toNNReal ω)) ≤
        ENNReal.ofReal (κ⁻¹ * (psiD δ₁ (∑ k, c k * x k) + K * N +
          ∑ i, ∑ j, L i j (N : ℝ≥0) ω)) := by
    intro N t htN
    have hint : IntegrableOn (fun u : ℝ => κ⁻¹ * w38 (toP C) c κ δ₁ (X x u.toNNReal ω))
        (Icc 0 (N : ℝ)) := (continuous_const.mul hwc).integrableOn_Icc
    calc ∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal (StochKolmogorov.Classify.growthWeight C c δ₁ (X x s.toNNReal ω))
        = ∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal (κ⁻¹ * w38 (toP C) c κ δ₁ (X x s.toNNReal ω)) := by
          refine lintegral_congr fun s => ?_
          rw [w38_eq_gw C hc κ δ₁ (hω _), ← mul_assoc, inv_mul_cancel₀ hκ0.ne', one_mul]
      _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) (N : ℝ),
            ENNReal.ofReal (κ⁻¹ * w38 (toP C) c κ δ₁ (X x s.toNNReal ω)) :=
          lintegral_mono_set (Icc_subset_Icc_right htN)
      _ = ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) (N : ℝ),
            κ⁻¹ * w38 (toP C) c κ δ₁ (X x s.toNNReal ω)) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (ae_of_all _ fun u => mul_nonneg (inv_nonneg.2 hκ0.le) (hw0 u))).symm
      _ = ENNReal.ofReal (κ⁻¹ * ∫ u in (0 : ℝ)..(N : ℝ),
            w38 (toP C) c κ δ₁ (X x u.toNNReal ω)) := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
            intervalIntegral.integral_const_mul]
      _ ≤ ENNReal.ofReal (κ⁻¹ * (psiD δ₁ (∑ k, c k * x k) + K * N +
            ∑ i, ∑ j, L i j (N : ℝ≥0) ω)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hnat N) (inv_nonneg.2 hκ0.le))
  have hNt : Tendsto (fun t : ℝ => ((⌈t⌉₊ : ℕ) : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_ceil_atTop
  have hev := (hSω.comp hNt).eventually (gt_mem_nhds (half_pos hκ0))
  filter_upwards [hev, eventually_ge_atTop
    (max (2 * (psiD δ₁ (∑ k, c k * x k) + K) / κ + 1) 1)] with t hSt ht
  have hSt' : (∑ i, ∑ j, L i j ((⌈t⌉₊ : ℕ) : ℝ≥0) ω) / ((((⌈t⌉₊ : ℕ) : ℝ≥0)) : ℝ) < κ / 2 := hSt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈t⌉₊ := ⟨_, rfl⟩
  rw [← hN] at hSt'
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have hT0 : 2 * (psiD δ₁ (∑ k, c k * x k) + K) / κ + 1 ≤ t := le_trans (le_max_left _ _) ht
  have htN : t ≤ (N : ℝ) := hN ▸ Nat.le_ceil t
  have hNt1 : (N : ℝ) < t + 1 := hN ▸ Nat.ceil_lt_add_one (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have hNr : (((N : ℕ) : ℝ≥0) : ℝ) = (N : ℝ) := NNReal.coe_natCast N
  rw [hNr, div_lt_iff₀ hNpos] at hSt'
  refine (hlin N t htN).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [inv_mul_le_iff₀ hκ0]
  have e : κ * ((K / κ + 1 + ε) * t) = (κ * (K / κ)) * t + κ * t + κ * ε * t := by ring
  rw [e, mul_div_cancel₀ K hκ0.ne']
  have h1 : K * N ≤ K * (t + 1) := mul_le_mul_of_nonneg_left hNt1.le hK0
  have h2 : κ / 2 * N ≤ κ / 2 * (t + 1) := mul_le_mul_of_nonneg_left hNt1.le (by positivity)
  have h3 : 2 * (psiD δ₁ (∑ k, c k * x k) + K) ≤ κ * (t - 1) := by
    have : 2 * (psiD δ₁ (∑ k, c k * x k) + K) / κ ≤ t - 1 := by linarith
    have h5 := (div_le_iff₀ hκ0).1 this
    linarith
  have h4 : 0 ≤ κ * ε * t := mul_nonneg (mul_nonneg hκ0.le hε.le) (by linarith)
  linarith

end Part1b
end ItoLib.G73

end FlatM_Part1b

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
open StochKolmogorov.Classify in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (hδ₁ : δ₁ ≤ δ₀) :
    (∃ Khat : ℝ, 0 < Khat ∧ ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) ∧
    ∀ x ∈ orthant n, ∀ J : Fin n → ℝ≥0 → Ω → ℝ,
      (∀ j, (∀ ω, Continuous (fun t => J j t ω)) ∧
        HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
          (fun t ω => B t ω j) (fun t ω => itoIntegrand C c j (X x t ω)) (J j)) →
      ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => (∑ j, J j t ω) / (t : ℝ)) atTop (𝓝 0) := by
  exact ⟨ItoLib.G73.part1 hn P C B X hX c γb hA δ₀ hδ₀ δ₁ h14 hδ₁, ItoLib.G73.part2 hn P C B X hX c γb hA δ₀ hδ₀⟩
