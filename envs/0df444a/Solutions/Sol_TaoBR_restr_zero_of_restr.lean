-- Prove2me | solution 1 for TaoBR.restr_zero_of_restr
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:11:55.607019+00:00
-- url     : https://prove2.me/submissions/93df9d5c-58f7-46ea-a7f0-eac30ce81134
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_restr_sparse_of_restr_uniform
import Theorems.Thm_TaoBR_exists_sparse_cover
import Theorems.Thm_TaoBR_restr_zero_of_cubeUnion_bound
import Mathlib

section
section
open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap ContDiff

namespace TaoBR.T12

variable {n : ℕ}

instance : IsFiniteMeasure (sphereMeasure n) := by unfold sphereMeasure; infer_instance

/-- The indicator of a set, with value `1 : ℂ`. -/
noncomputable def chi (G : Set (E n)) : E n → ℂ := G.indicator fun _ => (1 : ℂ)

lemma unique_ball {M : ℕ} {x : Fin M → E n} {R : ℝ}
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) {y : E n} {i j : Fin M}
    (hi : y ∈ ball (x i) (2 * R)) (hj : y ∈ ball (x j) (2 * R)) : i = j := by
  by_contra h
  have := hsep i j h
  rw [mem_ball] at hi hj
  have := dist_triangle_left (x i) (x j) y
  linarith

/-- A smooth cutoff: `1` on the `R`-balls, supported in the `2R`-balls. -/
lemma exists_cutoff {M : ℕ} (x : Fin M → E n) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) :
    ∃ θ : E n → ℝ, ContDiff ℝ ∞ θ ∧ (∀ y, 0 ≤ θ y ∧ θ y ≤ 1) ∧
      (∀ y ∈ ⋃ i, closedBall (x i) R, θ y = 1) ∧
      tsupport θ ⊆ ⋃ i, closedBall (x i) (2 * R) := by
  let b : ∀ i, ContDiffBump (x i) := fun i => ⟨R, 2 * R, hR, by linarith⟩
  refine ⟨fun y => ∑ i, b i y, ?_, ?_, ?_, ?_⟩
  · exact ContDiff.sum fun i _ => (b i).contDiff
  · intro y
    dsimp only
    by_cases h : ∃ i, y ∈ ball (x i) (2 * R)
    · obtain ⟨i, hi⟩ := h
      rw [Finset.sum_eq_single i]
      · exact ⟨(b i).nonneg, (b i).le_one⟩
      · intro j _ hj
        apply (b j).zero_of_le_dist
        by_contra hlt; push_neg at hlt
        exact hj (unique_ball hsep (by simpa [mem_ball] using hlt) hi)
      · simp
    · push_neg at h
      rw [Finset.sum_eq_zero fun j _ => (b j).zero_of_le_dist (by
        have := h j; rw [mem_ball] at this; push_neg at this; exact this)]
      simp
  · intro y hy
    dsimp only
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [Finset.sum_eq_single i]
    · exact (b i).one_of_mem_closedBall hi
    · intro j _ hj
      apply (b j).zero_of_le_dist
      by_contra hlt; push_neg at hlt
      have hi' : y ∈ ball (x i) (2 * R) := by
        rw [mem_closedBall] at hi; rw [mem_ball]; linarith
      exact hj (unique_ball hsep (by simpa [mem_ball] using hlt) hi')
    · simp
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_closedBall)
    intro y hy
    rw [Function.mem_support] at hy
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have : y ∈ Function.support (b i) := hi
    rw [(b i).support_eq] at this
    exact Set.mem_iUnion.mpr ⟨i, ball_subset_closedBall this⟩

lemma measure_iUnion_closedBall_lt_top {M : ℕ} (x : Fin M → E n) (r : ℝ) :
    volume (⋃ i, closedBall (x i) r) < ⊤ :=
  (measure_iUnion_fintype_le _ _).trans_lt
    (ENNReal.sum_lt_top.mpr fun i _ => measure_closedBall_lt_top)

/-- Schwartz approximation of an indicator, supported in the doubled balls. -/
lemma exists_schwartz_approx {M : ℕ} (x : Fin M → E n) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) {G : Set (E n)} (hG : MeasurableSet G)
    (hGsub : G ⊆ ⋃ i, closedBall (x i) R) {q : ℝ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) (2 * R) ∧
      eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal ε ∧
      ∫⁻ y, ‖f y - chi G y‖ₑ ≤ ENNReal.ofReal ε := by
  obtain ⟨θ, hθs, hθ01, hθ1, hθsupp⟩ := exists_cutoff x hR hsep
  set K₂ := ⋃ i, closedBall (x i) (2 * R)
  have hK₂m : MeasurableSet K₂ := MeasurableSet.iUnion fun i => measurableSet_closedBall
  set V := volume K₂ with hV
  have hVtop : V ≠ ⊤ := (measure_iUnion_closedBall_lt_top x _).ne
  have hq0 : 0 < q := by linarith
  set e : ℝ := 1 - 1 / q
  have he0 : 0 ≤ e := by simp only [e]; rw [sub_nonneg, div_le_one hq0]; exact hq
  set ε₁ : ℝ := ε / (1 + V.toReal ^ e)
  have hε₁ : 0 < ε₁ := div_pos hε (by positivity)
  have hGfin : volume G < ⊤ := (measure_mono hGsub).trans_lt
    (measure_iUnion_closedBall_lt_top x R)
  have hmem : MemLp (chi G) (ENNReal.ofReal q) volume :=
    memLp_indicator_const _ hG _ (Or.inr hGfin.ne)
  obtain ⟨g, hgc, hgs, hgε⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top
    (by rw [ENNReal.one_le_ofReal]; exact hq) hmem hε₁
  set F : E n → ℂ := fun y => (θ y : ℂ) * g y
  have hFs : ContDiff ℝ ∞ F := (Complex.ofRealCLM.contDiff.comp hθs).mul hgs
  have hFc : HasCompactSupport F := hgc.mul_left
  let f : 𝓢(E n, ℂ) := hFc.toSchwartzMap hFs
  have hfF : ∀ y, f y = F y := fun y => rfl
  have hdiff : ∀ y, f y - chi G y = (θ y : ℂ) * (g y - chi G y) := by
    intro y
    rw [hfF]
    by_cases hy : y ∈ G
    · simp [F, chi, hy, hθ1 y (hGsub hy)]
    · simp [F, chi, hy]
  have hpt : ∀ y, ‖f y - chi G y‖ₑ ≤ ‖(chi G - g) y‖ₑ := by
    intro y
    rw [hdiff, enorm_mul, Pi.sub_apply, ← enorm_neg (chi G y - g y), neg_sub]
    calc ‖(θ y : ℂ)‖ₑ * ‖g y - chi G y‖ₑ ≤ 1 * ‖g y - chi G y‖ₑ := by
          gcongr
          rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hθ01 y).1]
          simpa using (hθ01 y).2
      _ = _ := one_mul _
  have hLq : eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal ε₁ :=
    (eLpNorm_mono_enorm hpt).trans hgε
  have hsupp : Function.support (fun y => f y - chi G y) ⊆ K₂ := by
    intro y hy
    rw [Function.mem_support, hdiff] at hy
    have : θ y ≠ 0 := fun h => hy (by simp [h])
    exact hθsupp (subset_tsupport _ this)
  refine ⟨f, ?_, hLq.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · exact (closure_mono (fun y hy => by
      rw [Function.mem_support, hfF] at hy
      exact fun h => hy (by simp [F, h]))).trans hθsupp
  · exact div_le_self hε.le (le_add_of_nonneg_right (by positivity))
  · -- `L¹` on the bounded set `K₂`
    have hrest : eLpNorm (fun y => f y - chi G y) 1 volume =
        eLpNorm (fun y => f y - chi G y) 1 (volume.restrict K₂) :=
      (eLpNorm_restrict_eq_of_support_subset hsupp).symm
    have hrestq : eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) (volume.restrict K₂) =
        eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume :=
      eLpNorm_restrict_eq_of_support_subset hsupp
    have hm : AEStronglyMeasurable (fun y => f y - chi G y) (volume.restrict K₂) :=
      (f.continuous.aestronglyMeasurable.sub
        ((aestronglyMeasurable_const.indicator hG))).restrict
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K₂) (p := 1)
      (q := ENNReal.ofReal q) (by rw [ENNReal.one_le_ofReal]; exact hq) hm
    rw [← hrest, hrestq, Measure.restrict_apply_univ, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hq0.le, eLpNorm_one_eq_lintegral_enorm] at h1
    refine h1.trans ?_
    calc eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume * V ^ (1 / 1 - 1 / q)
        ≤ ENNReal.ofReal ε₁ * ENNReal.ofReal (V.toReal ^ e) := by
          gcongr
          rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he0,
            ENNReal.ofReal_toReal hVtop]
          simp [e]
      _ = ENNReal.ofReal (ε₁ * V.toReal ^ e) := (ENNReal.ofReal_mul hε₁.le).symm
      _ ≤ ENNReal.ofReal ε := by
          apply ENNReal.ofReal_le_ofReal
          simp only [ε₁]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [show 0 ≤ V.toReal ^ e by positivity]

end TaoBR.T12

end
end

section
section
open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.T12

variable {n : ℕ}

lemma enorm_restriction_sub_le {f g : E n → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ω : sphere (0 : E n) 1) :
    ‖restriction f ω - restriction g ω‖ₑ ≤ ∫⁻ y, ‖f y - g y‖ₑ := by
  simp only [restriction, Real.fourier_eq]
  rw [← integral_sub ((Real.fourierIntegral_convergent_iff _).2 hf)
    ((Real.fourierIntegral_convergent_iff _).2 hg)]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; funext y
  rw [← smul_sub, Circle.smul_def, enorm_smul, ← ofReal_norm_eq_enorm (𝐞 _ : ℂ), Circle.norm_coe,
    ENNReal.ofReal_one, one_mul]

lemma continuous_restriction {f : E n → ℂ} (hf : Integrable f) : Continuous (restriction f) := by
  have : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E n × E n => ⟪p.1, p.2⟫)) hf
  exact this.comp continuous_subtype_val

lemma integrable_chi {G : Set (E n)} (hG : MeasurableSet G) (hfin : volume G < ⊤) :
    Integrable (chi G) :=
  (integrableOn_const hfin.ne).integrable_indicator hG

/-- The Schwartz bound on the doubled balls passes to indicators of subsets of the balls. -/
lemma restriction_chi_le {M : ℕ} (x : Fin M → E n) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) {G : Set (E n)} (hG : MeasurableSet G)
    (hGsub : G ⊆ ⋃ i, closedBall (x i) R) {q : ℝ} (hq : 1 ≤ q) {K : ℝ≥0∞} (hKtop : K ≠ ⊤)
    (hK : ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) (2 * R) →
      eLpNorm (restriction f) (ENNReal.ofReal q) (sphereMeasure n) ≤
        K * eLpNorm f (ENNReal.ofReal q) volume) :
    eLpNorm (restriction (chi G)) (ENNReal.ofReal q) (sphereMeasure n) ≤
      K * eLpNorm (chi G) (ENNReal.ofReal q) volume := by
  have hGfin : volume G < ⊤ := (measure_mono hGsub).trans_lt
    (measure_iUnion_closedBall_lt_top x R)
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
  set Ms : ℝ≥0∞ := sphereMeasure n Set.univ ^ (ENNReal.ofReal q).toReal⁻¹
  have hMs : Ms ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ := ε / (K.toReal + Ms.toReal + 1)
  have hδ : 0 < δ := div_pos (by exact_mod_cast hε) (by positivity)
  obtain ⟨f, hfs, hLq, hL1⟩ := exists_schwartz_approx x hR hsep hG hGsub hq hδ
  have hdiff : ∀ ω, ‖restriction (chi G) ω - restriction f ω‖ ≤ δ := by
    intro ω
    have h := enorm_restriction_sub_le (integrable_chi hG hGfin) f.integrable ω
    have h2 : ∫⁻ y, ‖chi G y - f y‖ₑ = ∫⁻ y, ‖f y - chi G y‖ₑ := by
      congr 1; funext y; rw [← enorm_neg, neg_sub]
    rw [h2] at h
    have := h.trans hL1
    rw [← ofReal_norm_eq_enorm] at this
    exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp this
  have hsplit : restriction (chi G) =
      restriction ⇑f + (restriction (chi G) - restriction ⇑f) := by abel
  have hcf := (continuous_restriction f.integrable).aestronglyMeasurable (μ := sphereMeasure n)
  have hcg := (continuous_restriction (integrable_chi hG hGfin)).aestronglyMeasurable
    (μ := sphereMeasure n)
  have hfχ : eLpNorm (⇑f) (ENNReal.ofReal q) volume ≤
      eLpNorm (chi G) (ENNReal.ofReal q) volume + ENNReal.ofReal δ := by
    have : (⇑f) = chi G + (fun y => f y - chi G y) := by funext y; simp
    rw [this]
    refine (eLpNorm_add_le ?_ ?_ hq1).trans (by gcongr)
    · exact (aestronglyMeasurable_const.indicator hG)
    · exact f.continuous.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hG)
  calc eLpNorm (restriction (chi G)) (ENNReal.ofReal q) (sphereMeasure n)
      ≤ eLpNorm (restriction ⇑f) (ENNReal.ofReal q) (sphereMeasure n) +
        eLpNorm (restriction (chi G) - restriction ⇑f) (ENNReal.ofReal q) (sphereMeasure n) := by
        conv_lhs => rw [hsplit]
        exact eLpNorm_add_le hcf (hcg.sub hcf) hq1
    _ ≤ K * (eLpNorm (chi G) (ENNReal.ofReal q) volume + ENNReal.ofReal δ) +
        Ms * ENNReal.ofReal δ := by
        gcongr
        · exact (hK f hfs).trans (by gcongr)
        · exact eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hdiff)
    _ = K * eLpNorm (chi G) (ENNReal.ofReal q) volume + (K + Ms) * ENNReal.ofReal δ := by ring
    _ ≤ K * eLpNorm (chi G) (ENNReal.ofReal q) volume + ε := by
        gcongr
        rw [← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_toReal hMs,
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        simp only [δ]
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ ε := ε.2
        nlinarith

/-! ### Disjointifying a finite cover -/

/-- The `k`-th set of a finite family, as an `ℕ`-indexed sequence (empty past the end). -/
def ext {J : ℕ} (B : Fin J → Set (E n)) (k : ℕ) : Set (E n) :=
  if h : k < J then B ⟨k, h⟩ else ∅

lemma chi_eq_sum {J : ℕ} (B : Fin J → Set (E n)) {S : Set (E n)} (hS : S ⊆ ⋃ j, B j)
    (y : E n) :
    chi S y = ∑ k ∈ Finset.range J, chi (S ∩ disjointed (ext B) k) y := by
  by_cases hy : y ∈ S
  · have hU : y ∈ ⋃ k, disjointed (ext B) k := by
      rw [iUnion_disjointed]
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hS hy)
      exact Set.mem_iUnion.mpr ⟨j, by simp [ext, j.2, hj]⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hU
    have hkJ : k < J := by
      by_contra h
      have := disjointed_subset (ext B) k hk
      simp [ext, h] at this
    rw [Finset.sum_eq_single k]
    · simp [chi, hy, hk]
    · intro l _ hl
      have : y ∉ disjointed (ext B) l := fun h =>
        Set.disjoint_left.mp (disjoint_disjointed (ext B) hl) h hk
      simp [chi, this]
    · intro h; exact absurd (Finset.mem_range.mpr hkJ) h
  · rw [Finset.sum_eq_zero]
    · simp [chi, hy]
    · intro k _; simp [chi, hy]

lemma restriction_finset_sum {ι : Type*} (s : Finset ι) (F : ι → E n → ℂ)
    (hF : ∀ i ∈ s, Integrable (F i)) :
    restriction (fun y => ∑ i ∈ s, F i y) = fun ω => ∑ i ∈ s, restriction (F i) ω := by
  funext ω
  simp only [restriction, Real.fourier_eq, Finset.smul_sum]
  exact integral_finset_sum s fun i hi => (Real.fourierIntegral_convergent_iff _).2 (hF i hi)

end TaoBR.T12

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.CU

variable {n : ℕ}

/-- The `c`-cube as a box of `Fin n → ℝ`. -/
lemma cCube_eq (c : ℝ) (k : Fin n → ℤ) :
    cCube c k = (WithLp.ofLp : E n → (Fin n → ℝ)) ⁻¹'
      Set.pi Set.univ (fun i => Set.Icc ((k i : ℝ) - c / 2) (k i + c / 2)) := by
  ext x
  simp only [cCube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  show (∀ i, |x i - k i| ≤ c / 2) ↔ _
  constructor
  · intro h i; have := abs_le.mp (h i); exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro h i; have := h i; exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩

lemma measurableSet_cCube (c : ℝ) (k : Fin n → ℤ) : MeasurableSet (cCube c k) := by
  rw [cCube_eq]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Icc).preimage
    (WithLp.measurable_ofLp 2 _)

lemma volume_cCube {c : ℝ} (hc : 0 ≤ c) (k : Fin n → ℤ) :
    volume (cCube c k) = ENNReal.ofReal c ^ n := by
  rw [cCube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Icc).nullMeasurableSet), volume_pi,
    Measure.pi_pi]
  have : ∀ i : Fin n, ((k i : ℝ) + c / 2 - (k i - c / 2)) = c := fun i => by ring
  simp only [Real.volume_Icc, this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma volume_cCube_lt_top (c : ℝ) (k : Fin n → ℤ) : volume (cCube c k) < ⊤ := by
  have hsub : cCube c k ⊆ cCube |c| k := fun x hx i => (hx i).trans (by
    have := le_abs_self c; linarith)
  calc volume (cCube c k) ≤ volume (cCube |c| k) := measure_mono hsub
    _ < ⊤ := by rw [volume_cCube (abs_nonneg c)]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

end TaoBR.CU

end
end

section
section
open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap

namespace TaoBR.T12

variable {n : ℕ}

lemma sparse_double {M : ℕ} {x : Fin M → E n} {C₀ R : ℝ} (hR : 1 ≤ R)
    (h : IsSparse (2 * max C₀ 2) R x) :
    IsSparse C₀ (2 * R) x ∧ ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j) := by
  set C := max C₀ 2
  have hC2 : (2 : ℝ) ≤ C := le_max_right _ _
  have hC0 : C₀ ≤ C := le_max_left _ _
  have key : ∀ i j, i ≠ j → (2 * R) ^ C * (M : ℝ) ^ C ≤ dist (x i) (x j) := by
    intro i j hij
    have hM : (2 : ℝ) ≤ M := by
      have : (2 : ℕ) ≤ M := by
        have := i.2; have := j.2; have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega
      exact_mod_cast this
    have hM1 : (1 : ℝ) ≤ M := by linarith
    have hRC : 1 ≤ R ^ C := Real.one_le_rpow hR (by linarith)
    have hMC : 1 ≤ (M : ℝ) ^ C := Real.one_le_rpow hM1 (by linarith)
    have h2M : (2 : ℝ) ^ C ≤ (M : ℝ) ^ C := Real.rpow_le_rpow (by norm_num) hM (by linarith)
    calc (2 * R) ^ C * (M : ℝ) ^ C = 2 ^ C * R ^ C * (M : ℝ) ^ C := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]
      _ ≤ (M : ℝ) ^ C * R ^ C * (M : ℝ) ^ C := by gcongr
      _ = (R ^ C * ((M : ℝ) ^ C * (M : ℝ) ^ C)) * 1 := by ring
      _ ≤ (R ^ C * ((M : ℝ) ^ C * (M : ℝ) ^ C)) * R ^ C :=
          mul_le_mul_of_nonneg_left hRC (by positivity)
      _ = (R ^ C * R ^ C) * ((M : ℝ) ^ C * (M : ℝ) ^ C) := by ring
      _ = R ^ (2 * C) * (M : ℝ) ^ (2 * C) := by
          rw [two_mul, Real.rpow_add (by linarith), Real.rpow_add (by linarith)]
      _ ≤ dist (x i) (x j) := h i j hij
  constructor
  · intro i j hij
    refine le_trans ?_ (key i j hij)
    have hM1 : (1 : ℝ) ≤ M := by
      have : (1 : ℕ) ≤ M := Nat.one_le_iff_ne_zero.mpr (fun h0 => by subst h0; exact i.elim0)
      exact_mod_cast this
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by linarith) hC0)
      (Real.rpow_le_rpow_of_exponent_le hM1 hC0) (by positivity) (by positivity)
  · intro i j hij
    refine le_trans ?_ (key i j hij)
    have hM1 : (1 : ℝ) ≤ M := by
      have : (1 : ℕ) ≤ M := Nat.one_le_iff_ne_zero.mpr (fun h0 => by subst h0; exact i.elim0)
      exact_mod_cast this
    have h1 : (2 * R) ^ (2 : ℝ) ≤ (2 * R) ^ C := Real.rpow_le_rpow_of_exponent_le (by linarith) hC2
    have h2 : 1 ≤ (M : ℝ) ^ C := Real.one_le_rpow hM1 (by linarith)
    rw [Real.rpow_two] at h1
    nlinarith

lemma volume_cubeUnion_lt_top {c : ℝ} {S : Set (E n)} (hS : IsCubeUnion c S) : volume S < ⊤ := by
  obtain ⟨s, rfl⟩ := hS
  exact (measure_biUnion_finset_le _ _).trans_lt
    (ENNReal.sum_lt_top.mpr fun k _ => CU.volume_cCube_lt_top c k)

lemma measurableSet_cubeUnion {c : ℝ} {S : Set (E n)} (hS : IsCubeUnion c S) : MeasurableSet S := by
  obtain ⟨s, rfl⟩ := hS
  exact Finset.measurableSet_biUnion _ fun k _ => CU.measurableSet_cCube c k

/-- The bound (4) for one union of cubes, from a sparse cover and the sparse estimate. -/
lemma cube_bound_from_cover {p : ℝ} (hp : 1 ≤ p) {α : ℝ} (hα : 0 < α) {C₀ : ℝ} {C : ℝ≥0}
    (hU : ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse C₀ R x →
      ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
        eLpNorm (restriction f) (ENNReal.ofReal p) (sphereMeasure n) ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f (ENNReal.ofReal p) volume)
    {S : Set (E n)} (hSm : MeasurableSet S) (hSfin : volume S < ⊤)
    {J : ℕ} {R : Fin J → ℝ} {M : Fin J → ℕ} {x : (j : Fin J) → Fin (M j) → E n}
    {Rmax : ℝ} (hR : ∀ j, 1 ≤ R j ∧ R j ≤ Rmax ∧ IsSparse (2 * max C₀ 2) (R j) (x j))
    (hcov : S ⊆ ⋃ (j) (i), closedBall (x j i) (R j)) :
    eLpNorm (restriction (chi S)) (ENNReal.ofReal p) (sphereMeasure n) ≤
      J * (C * ENNReal.ofReal ((2 * Rmax) ^ α) * volume S ^ (1 / p)) := by
  set B : Fin J → Set (E n) := fun j => ⋃ i, closedBall (x j i) (R j)
  set G : ℕ → Set (E n) := fun k => S ∩ disjointed (ext B) k
  have hBm : ∀ k, MeasurableSet (ext B k) := by
    intro k; unfold ext; split_ifs
    · exact MeasurableSet.iUnion fun i => measurableSet_closedBall
    · exact MeasurableSet.empty
  have hGm : ∀ k, MeasurableSet (G k) := fun k => hSm.inter (MeasurableSet.disjointed hBm k)
  have hGfin : ∀ k, volume (G k) < ⊤ := fun k =>
    (measure_mono Set.inter_subset_left).trans_lt hSfin
  have hS' : S ⊆ ⋃ j, B j := by
    intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hy)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have hsum : restriction (chi S) = ∑ k ∈ Finset.range J, restriction (chi (G k)) := by
    have : chi S = fun y => ∑ k ∈ Finset.range J, chi (G k) y := funext (chi_eq_sum B hS')
    rw [this, restriction_finset_sum _ _ fun k _ => integrable_chi (hGm k) (hGfin k)]
    funext ω; simp [Finset.sum_apply]
  rw [hsum]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [ENNReal.one_le_ofReal]; exact hp
  refine (eLpNorm_sum_le (fun k _ =>
    (continuous_restriction (integrable_chi (hGm k) (hGfin k))).aestronglyMeasurable) hp1).trans ?_
  have hterm : ∀ k ∈ Finset.range J, eLpNorm (restriction (chi (G k))) (ENNReal.ofReal p)
      (sphereMeasure n) ≤ C * ENNReal.ofReal ((2 * Rmax) ^ α) * volume S ^ (1 / p) := by
    intro k hk
    have hkJ := Finset.mem_range.mp hk
    set j : Fin J := ⟨k, hkJ⟩
    obtain ⟨hR1, hRle, hsp⟩ := hR j
    obtain ⟨hsp2, hsep⟩ := sparse_double hR1 hsp
    have hGsub : G k ⊆ ⋃ i, closedBall (x j i) (R j) := by
      intro y hy
      have := disjointed_subset (ext B) k hy.2
      simpa [ext, hkJ, B, j] using this
    have hK : ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x j i) (2 * R j) →
        eLpNorm (restriction f) (ENNReal.ofReal p) (sphereMeasure n) ≤
          (C * ENNReal.ofReal ((2 * R j) ^ α)) * eLpNorm f (ENNReal.ofReal p) volume :=
      fun f hf => hU (2 * R j) (by linarith) (M j) (x j) hsp2 f hf
    have h1 := restriction_chi_le (x j) (by linarith) hsep (hGm k) hGsub hp
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hK
    refine h1.trans ?_
    have hchi : eLpNorm (chi (G k)) (ENNReal.ofReal p) volume ≤ volume S ^ (1 / p) := by
      unfold chi
      rw [eLpNorm_indicator_const (hGm k) (by simp; linarith) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith)]
      simp only [enorm_one, one_mul]
      exact ENNReal.rpow_le_rpow (measure_mono Set.inter_subset_left) (by positivity)
    have hRR : ENNReal.ofReal ((2 * R j) ^ α) ≤ ENNReal.ofReal ((2 * Rmax) ^ α) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith) (by linarith) hα.le)
    exact mul_le_mul' (mul_le_mul' le_rfl hRR) hchi
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end TaoBR.T12

end
end

section
section
open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap

namespace TaoBR.T12

variable {n : ℕ}

/-- The choice `N ≈ log(1/α) / (2 log C₁)`. -/
lemma key_N {C₁ L : ℝ} (hC₁ : 2 ≤ C₁) (hL : 4 * Real.log (4 * C₁) < L) :
    ∃ N : ℕ, 1 ≤ N ∧ 1 / (N : ℝ) + Real.exp (-L) * C₁ ^ N ≤ (2 * Real.log C₁ + 1) / L := by
  have hlc : 0 < Real.log C₁ := Real.log_pos (by linarith)
  have h4 : 0 < Real.log (4 * C₁) := Real.log_pos (by linarith)
  have hL0 : 0 < L := by linarith
  set N := ⌈L / (2 * Real.log C₁)⌉₊
  have hpos : 0 < L / (2 * Real.log C₁) := by positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hpos).ne'
  have hNge : L / (2 * Real.log C₁) ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < L / (2 * Real.log C₁) + 1 := Nat.ceil_lt_add_one hpos.le
  refine ⟨N, hN1, ?_⟩
  have h1 : 1 / (N : ℝ) ≤ 2 * Real.log C₁ / L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    rw [div_le_iff₀ (by positivity)] at hNge
    linarith
  have hpow : C₁ ^ N = Real.exp (N * Real.log C₁) := by
    rw [← Real.exp_log (show 0 < C₁ by linarith), ← Real.exp_nat_mul, Real.log_exp]
  have h2 : Real.exp (-L) * C₁ ^ N ≤ 1 / L := by
    rw [hpow, ← Real.exp_add]
    have hlt : -L + N * Real.log C₁ ≤ -L / 2 + Real.log C₁ := by
      have : (N : ℝ) * Real.log C₁ ≤ (L / (2 * Real.log C₁) + 1) * Real.log C₁ :=
        mul_le_mul_of_nonneg_right hNlt.le hlc.le
      rw [add_mul, div_mul_eq_mul_div, mul_div_assoc, mul_comm 2 (Real.log C₁),
        div_mul_cancel_left₀ hlc.ne'] at this
      linarith
    refine (Real.exp_le_exp.mpr hlt).trans ?_
    rw [Real.exp_add, Real.exp_log (by linarith), le_div_iff₀ hL0]
    -- `L C₁ ≤ exp(L/2)`
    have hq : 4 * C₁ < Real.exp (L / 4) := by
      rw [← Real.exp_log (show 0 < 4 * C₁ by linarith)]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hq2 : L / 4 ≤ Real.exp (L / 4) := by linarith [Real.add_one_le_exp (L / 4)]
    have hsq : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hneg : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have key : L * C₁ ≤ Real.exp (L / 2) := by
      rw [hsq]; nlinarith [Real.exp_pos (L / 4)]
    have hE := Real.exp_pos (-L / 2)
    calc Real.exp (-L / 2) * C₁ * L = Real.exp (-L / 2) * (L * C₁) := by ring
      _ ≤ Real.exp (-L / 2) * Real.exp (L / 2) := mul_le_mul_of_nonneg_left key hE.le
      _ = 1 := hneg
  calc 1 / (N : ℝ) + Real.exp (-L) * C₁ ^ N ≤ 2 * Real.log C₁ / L + 1 / L := add_le_add h1 h2
    _ = _ := by ring

/-- The numerical bound behind (4). -/
lemma numeric {A C α m N p r c0 s : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hα : 0 < α) (hm : 0 ≤ m)
    (hN : 1 ≤ N) (hp : 0 < p) (hr : 1 / p ≤ r) (hexp : 1 / N + α * m + 1 / p ≤ r)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hs : s = 0 ∨ c0 ≤ s) :
    A * N * s ^ (1 / N) * (C * (2 * (A * (max 1 s) ^ m)) ^ α * s ^ (1 / p)) ≤
      (A * N * C * (2 * A) ^ α * c0 ^ (1 / p - r)) * s ^ r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hK0 : 0 ≤ A * N * C * (2 * A) ^ α := by positivity
  have hcz : 1 ≤ c0 ^ (1 / p - r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc0 hc01 (by linarith)
  rcases hs with hs | hs
  · subst hs
    rw [Real.zero_rpow (by positivity), Real.zero_rpow hr0.ne']; simp
  have hs0 : 0 < s := lt_of_lt_of_le hc0 hs
  have hsplit : (2 * (A * (max 1 s) ^ m)) ^ α = (2 * A) ^ α * (max 1 s) ^ (m * α) := by
    rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
  rw [hsplit]
  rcases le_total 1 s with h1 | h1
  · rw [max_eq_right h1]
    have : s ^ (1 / N) * (s ^ (m * α) * s ^ (1 / p)) = s ^ (1 / N + α * m + 1 / p) := by
      rw [← Real.rpow_add hs0, ← Real.rpow_add hs0]; ring_nf
    calc A * N * s ^ (1 / N) * (C * ((2 * A) ^ α * s ^ (m * α)) * s ^ (1 / p))
        = (A * N * C * (2 * A) ^ α) * (s ^ (1 / N) * (s ^ (m * α) * s ^ (1 / p))) := by ring
      _ = (A * N * C * (2 * A) ^ α) * s ^ (1 / N + α * m + 1 / p) := by rw [this]
      _ ≤ (A * N * C * (2 * A) ^ α) * s ^ r :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hexp) hK0
      _ ≤ (A * N * C * (2 * A) ^ α * c0 ^ (1 / p - r)) * s ^ r := by
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0 hcz) (by positivity)
  · rw [max_eq_left h1, Real.one_rpow, mul_one]
    have hsN : s ^ (1 / N) ≤ 1 := Real.rpow_le_one hs0.le h1 (by positivity)
    have hsp : s ^ (1 / p) = s ^ r * s ^ (1 / p - r) := by
      rw [← Real.rpow_add hs0]; ring_nf
    have hsc : s ^ (1 / p - r) ≤ c0 ^ (1 / p - r) :=
      Real.rpow_le_rpow_of_nonpos hc0 hs (by linarith)
    calc A * N * s ^ (1 / N) * (C * (2 * A) ^ α * s ^ (1 / p))
        = (A * N * C * (2 * A) ^ α) * s ^ (1 / N) * s ^ (1 / p) := by ring
      _ ≤ (A * N * C * (2 * A) ^ α) * 1 * s ^ (1 / p) := by gcongr
      _ = (A * N * C * (2 * A) ^ α) * (s ^ r * s ^ (1 / p - r)) := by rw [hsp]; ring
      _ ≤ (A * N * C * (2 * A) ^ α) * (s ^ r * c0 ^ (1 / p - r)) := by gcongr
      _ = _ := by ring

end TaoBR.T12

end
end

section
section
open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap

namespace TaoBR.T12

variable {n : ℕ}

lemma cubeUnion_volume_cases {S : Set (E n)} (hS : IsCubeUnion (1 / 2) S) :
    (volume S).toReal = 0 ∨ (1 / 2 : ℝ) ^ n ≤ (volume S).toReal := by
  obtain ⟨s, rfl⟩ := hS
  rcases s.eq_empty_or_nonempty with h | ⟨k, hk⟩
  · left; subst h; simp
  · right
    have hle : volume (cCube (1 / 2) k) ≤ volume (⋃ k ∈ s, cCube (1 / 2 : ℝ) k) :=
      measure_mono (Set.subset_biUnion_of_mem (u := fun k => cCube (1 / 2 : ℝ) k) hk)
    rw [CU.volume_cCube (by norm_num)] at hle
    have := ENNReal.toReal_mono (volume_cubeUnion_lt_top ⟨s, rfl⟩).ne hle
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num)] at this

end TaoBR.T12

namespace TaoBR

open T12

theorem restr_zero_of_restr_dev (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ C α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ → Restr n (ENNReal.ofReal p) α →
      ∀ q : ℝ, 1 ≤ q → 1 / p + C / Real.log (1 / α) < 1 / q → Restr n (ENNReal.ofReal q) 0 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C₀, hU⟩ := restr_sparse_of_restr_uniform n hn (ENNReal.ofReal p)
    (ENNReal.one_lt_ofReal.mpr hp)
    (by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
        exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hp2)
  obtain ⟨A, C₁, hcov⟩ := exists_sparse_cover n hn (1 / 2) (by norm_num) (2 * max C₀ 2)
  set A' := max A 1
  set C₁' := max |C₁| 2
  have hA' : 1 ≤ A' := le_max_right _ _
  have hC₁' : 2 ≤ C₁' := le_max_right _ _
  set κ := 2 * Real.log C₁' + 1
  set α₀ := min (1 / 2) (Real.exp (-(4 * Real.log (4 * C₁'))))
  refine ⟨κ, α₀, lt_min (by norm_num) (Real.exp_pos _), ?_⟩
  intro α hα hαα hR q hq hqr
  have hα1 : α < 1 := lt_of_lt_of_le hαα ((min_le_left _ _).trans (by norm_num))
  set L := Real.log (1 / α)
  have hLeq : L = -Real.log α := by simp [L, Real.log_inv]
  have hLbig : 4 * Real.log (4 * C₁') < L := by
    rw [hLeq]
    have := Real.log_lt_log hα (lt_of_lt_of_le hαα (min_le_right _ _))
    rw [Real.log_exp] at this; linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by
    have := Real.log_pos (show (1 : ℝ) < 4 * C₁' by linarith); linarith) hLbig
  have hαexp : α = Real.exp (-L) := by rw [hLeq, neg_neg, Real.exp_log hα]
  obtain ⟨N, hN1, hNkey⟩ := key_N hC₁' hLbig
  obtain ⟨C, hC⟩ := hU α hα hR
  set r := 1 / p + κ / L
  have hr1 : r < 1 := by
    by_contra h
    push_neg at h
    have : 1 / q ≤ 1 := by rw [div_le_one (by linarith)]; exact hq
    linarith
  have hrp : 1 / p ≤ r := by
    have : 0 ≤ κ / L := div_nonneg (by have := Real.log_pos (show (1:ℝ) < C₁' by linarith); linarith) hL0.le
    simp only [r]; linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hrp
  set q₀ := 1 / r
  have hq₀ : 1 < q₀ := by rw [lt_one_div (by norm_num) hr0]; simpa using hr1
  have hq₀p : q₀ ≤ p := by
    simp only [q₀]; rw [div_le_iff₀ hr0]
    rw [div_le_iff₀ hp0] at hrp; linarith
  have hqq₀ : q < q₀ := by
    simp only [q₀]; rw [lt_div_iff₀ hr0]
    rw [lt_div_iff₀ (by linarith)] at hqr; linarith
  have hexp : 1 / (N : ℝ) + α * C₁' ^ N + 1 / p ≤ r := by
    simp only [r]; rw [hαexp]; linarith
  set c0 : ℝ := (1 / 2) ^ n
  set Cα : ℝ := A' * N * C * (2 * A') ^ α * c0 ^ (1 / p - r)
  refine restr_zero_of_cubeUnion_bound n hn p hp hp2 q₀ hq₀ hq₀p (1 / 2) (by norm_num)
    (by norm_num) ⟨Cα, fun S hS => ?_⟩ (ENNReal.ofReal q)
    (by rw [ENNReal.one_le_ofReal]; exact hq) ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hqq₀)
  -- the bound (4) for `S`
  have hSfin := volume_cubeUnion_lt_top hS
  set s := (volume S).toReal
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  obtain ⟨J, R, M, x, hJ, hRb, hScov⟩ := hcov S hS N hN1
  set Rmax := A' * (max 1 s) ^ (C₁' ^ N)
  have hRb' : ∀ j, 1 ≤ R j ∧ R j ≤ Rmax ∧ IsSparse (2 * max C₀ 2) (R j) (x j) := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hRb j
    refine ⟨h1, h2.trans ?_, h3⟩
    have hu : 1 ≤ max 1 s := le_max_left _ _
    have hab : |C₁| ^ N ≤ C₁' ^ N := pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) N
    have hpow : C₁ ^ N ≤ C₁' ^ N := by
      have := le_abs_self (C₁ ^ N)
      rw [abs_pow] at this
      linarith
    calc A * max 1 s ^ C₁ ^ N ≤ A' * max 1 s ^ C₁ ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ A' * max 1 s ^ C₁' ^ N := by
          gcongr
  have hmain := cube_bound_from_cover hp.le hα hC (measurableSet_cubeUnion hS) hSfin hRb' hScov
  have hchi : chi S = S.indicator fun _ => (1 : ℂ) := rfl
  rw [← hchi]
  refine hmain.trans ?_
  have hJ' : (J : ℝ≥0∞) ≤ ENNReal.ofReal (A' * N * s ^ (1 / (N : ℝ))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hJ.trans (by gcongr; exact le_max_left _ _))
  have hvol : volume S ^ (1 / p) = ENNReal.ofReal (s ^ (1 / p)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hs0 (by positivity), ENNReal.ofReal_toReal hSfin.ne]
  have hRpos : 0 ≤ Rmax := by positivity
  calc (J : ℝ≥0∞) * (C * ENNReal.ofReal ((2 * Rmax) ^ α) * volume S ^ (1 / p))
      ≤ ENNReal.ofReal (A' * N * s ^ (1 / (N : ℝ))) *
          (ENNReal.ofReal C * ENNReal.ofReal ((2 * Rmax) ^ α) * ENNReal.ofReal (s ^ (1 / p))) := by
        rw [hvol, ENNReal.ofReal_coe_nnreal]; gcongr
    _ = ENNReal.ofReal (A' * N * s ^ (1 / (N : ℝ)) *
          (C * (2 * Rmax) ^ α * s ^ (1 / p))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Cα * s ^ (1 / q₀)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1q : 1 / q₀ = r := by simp [q₀]
        rw [h1q]
        exact numeric hA' C.2 hα (by positivity) (by exact_mod_cast hN1) hp0 hrp hexp
          (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
          (cubeUnion_volume_cases hS)

end TaoBR

end
end

section
open TaoBR

theorem solution (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ C α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ → Restr n (ENNReal.ofReal p) α →
      ∀ q : ℝ, 1 ≤ q → 1 / p + C / Real.log (1 / α) < 1 / q → Restr n (ENNReal.ofReal q) 0 := by
  exact TaoBR.restr_zero_of_restr_dev n hn p hp hp2

end
