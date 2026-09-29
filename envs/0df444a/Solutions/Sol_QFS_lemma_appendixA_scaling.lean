-- Prove2me | solution 1 for QFS.lemma_appendixA_scaling
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-07T08:37:17.604371+00:00
-- url     : https://prove2.me/submissions/19609752-f18a-4a46-8431-4979152999e1

import Theorems.Thm_QFS_lemma_appendixA
import Theorems.Thm_QFS_formHs_le_form_domain
import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_FavoredGraph
import Definitions.Def_QFS_Indicator
import Definitions.Def_QFS_WhitneyDomain
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Appendix A: the auxiliary lemmas

The paper's `\appendix` prints as Appendix A, with Lemmas A.1 and A.2.

**The chain (18) inside Lemma A.1.** Lemma A.1 passes from balls to a bounded
Lipschitz domain using a Whitney family and Dyda's inequality (13), both quoted
rather than proved. The one step the paper carries out itself is the
finite-overlap estimate, and it is proved here
(`tsum_setLIntegral_le_of_overlap`); `lemma_ball_to_domain` then assembles the
whole chain with the two quoted inputs as explicit hypotheses.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}

lemma jumpKernel_smul {h : ℝ} (hh : 0 < h) (α : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    jumpKernel d α (h • x) (h • y)
      = ENNReal.ofReal (h ^ (-(d:ℝ) - α)) * jumpKernel d α x y := by
  have hnorm : ‖h • x - h • y‖ = h * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  rw [jumpKernel, jumpKernel, hnorm, Real.mul_rpow hh.le (norm_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _)]

private lemma haar_prod :
    (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))).IsAddHaarMeasure := by
  rw [show (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
        = (volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume from rfl]
  infer_instance

private lemma map_vol {a : ℝ} (ha : 0 < a) :
    Measure.map (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) volume
      = ENNReal.ofReal ((a ^ (2*d))⁻¹) • volume := by
  haveI := haar_prod (d := d)
  rw [Measure.map_addHaar_smul volume ha.ne']
  congr 2
  · rw [abs_of_nonneg (by positivity)]
    congr 2
    simp [Module.finrank_prod, two_mul]

/-- the image of a product under the diagonal scaling -/
private lemma prod_image_smul (a : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    ((a • ·) '' Ω) ×ˢ ((a • ·) '' Ω)
      = (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) '' (Ω ×ˢ Ω) := by
  rw [Set.prod_image_image_eq]
  rfl

noncomputable def smulEquivProd {a : ℝ} (ha : a ≠ 0) :
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ≃ᵐ
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  (Homeomorph.smulOfNeZero a ha).toMeasurableEquiv

@[simp] lemma smulEquivProd_apply {a : ℝ} (ha : a ≠ 0) (p) :
    smulEquivProd (d := d) ha p = a • p := rfl

lemma setLIntegral_image_smul {a : ℝ} (ha : 0 < a)
    (A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ p in (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) '' A, F p
      = ENNReal.ofReal (a ^ (2*d)) * ∫⁻ q in A, F (a • q) := by
  set e := smulEquivProd (d := d) ha.ne' with he
  have hmap : Measure.map (⇑e) volume = ENNReal.ofReal ((a ^ (2*d))⁻¹) • volume := map_vol ha
  have hpow : (0:ℝ) < a ^ (2*d) := by positivity
  have hcancel : ENNReal.ofReal (a ^ (2*d)) * ENNReal.ofReal ((a ^ (2*d))⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hpow.le, mul_inv_cancel₀ hpow.ne', ENNReal.ofReal_one]
  have himg : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) '' A
      = ⇑e '' A := rfl
  have hres : volume.restrict (⇑e '' A)
      = ENNReal.ofReal (a ^ (2*d)) • Measure.map (⇑e) (volume.restrict A) := by
    refine Measure.ext fun s hs => ?_
    have h1 : (volume.restrict (⇑e '' A)) s = volume (s ∩ ⇑e '' A) :=
      Measure.restrict_apply hs
    have h2 : (Measure.map (⇑e) (volume.restrict A)) s = volume (⇑e ⁻¹' s ∩ A) := by
      rw [MeasurableEquiv.map_apply, Measure.restrict_apply (e.measurable hs)]
    have h3 : volume (⇑e ⁻¹' s ∩ A) = ENNReal.ofReal ((a ^ (2*d))⁻¹) * volume (s ∩ ⇑e '' A) := by
      have := congrArg (fun μ : Measure _ => μ (s ∩ ⇑e '' A)) hmap
      simp only [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul] at this
      rw [← this]
      congr 1
      rw [Set.preimage_inter, e.preimage_image]
    rw [Measure.smul_apply, smul_eq_mul, h1, h2, h3, ← mul_assoc, hcancel, one_mul]
  rw [himg]
  show ∫⁻ p, F p ∂(volume.restrict (⇑e '' A)) = _
  rw [hres, lintegral_smul_measure, lintegral_map_equiv]
  rfl

/-- **The Gagliardo seminorm scales.** Dilating the domain by `a > 0` multiplies
`|·|²_{H^{α/2}}` by `a^{d-α}`, once the function is precomposed with the dilation. -/
theorem formHs_smul {a : ℝ} (ha : 0 < a) (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    formHs ((a • ·) '' Ω) α f
      = ENNReal.ofReal (a ^ ((d : ℝ) - α)) * formHs Ω α (fun x => f (a • x)) := by
  have hjk : ∀ q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f (a • q).2 - f (a • q).1) ^ 2) * jumpKernel d α (a • q).1 (a • q).2
        = ENNReal.ofReal (a ^ (-(d:ℝ) - α)) *
          (ENNReal.ofReal ((f (a • q.2) - f (a • q.1)) ^ 2) * jumpKernel d α q.1 q.2) := by
    intro q
    show ENNReal.ofReal ((f (a • q.2) - f (a • q.1)) ^ 2)
        * jumpKernel d α (a • q.1) (a • q.2) = _
    rw [jumpKernel_smul ha]; ring
  simp only [formHs, form]
  rw [prod_image_smul, setLIntegral_image_smul ha]
  simp only [hjk]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [← Real.rpow_natCast a (2*d), ← Real.rpow_add ha]
  congr 1
  push_cast; ring

lemma image_smul_ball {a : ℝ} (ha : 0 < a) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    (a • ·) '' (ball x r) = ball (a • x) (a * r) := by
  rw [Set.image_smul, _root_.smul_ball ha.ne' x r, Real.norm_eq_abs, abs_of_pos ha]

/-- **Lemma A.1's constant depends on the domain only up to scaling.** A Whitney family
for `Ω` transports along the dilation `x ↦ a • x` to one for `a • Ω`, with the *same*
overlap bound and the *same* Dyda constant — hence the same constant in Lemma A.1. -/
noncomputable def WhitneyDomainData.smul {α κ : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (W : WhitneyDomainData d α κ Ω) {a : ℝ} (ha : 0 < a) :
    WhitneyDomainData d α κ ((a • ·) '' Ω) where
  idx := W.idx
  countable := W.countable
  overlapBound := W.overlapBound
  overlapBound_pos := W.overlapBound_pos
  dydaConst := W.dydaConst
  dydaConst_pos := W.dydaConst_pos
  ctr i := a • W.ctr i
  rad i := a * W.rad i
  enlarged_subset i := by
    have : κ * (a * W.rad i) = a * (κ * W.rad i) := by ring
    rw [this, ← image_smul_ball ha]
    exact Set.image_mono (W.enlarged_subset i)
  overlap y := by
    have hset : {i | y ∈ ball (a • W.ctr i) (κ * (a * W.rad i))}
        = {i | a⁻¹ • y ∈ ball (W.ctr i) (κ * W.rad i)} := by
      ext i
      have h : κ * (a * W.rad i) = a * (κ * W.rad i) := by ring
      simp only [Set.mem_setOf_eq, h, ← image_smul_ball ha, Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩; simpa [inv_smul_smul₀ ha.ne'] using hz
      · intro hy; exact ⟨a⁻¹ • y, hy, by rw [smul_inv_smul₀ ha.ne']⟩
    rw [hset]; exact W.overlap _
  dyda f := by
    have hballs : ∀ i, ball (a • W.ctr i) (a * W.rad i)
        = (a • ·) '' (ball (W.ctr i) (W.rad i)) := fun i => (image_smul_ball ha _ _).symm
    have hW := W.dyda (fun x => f (a • x))
    calc ENNReal.ofReal W.dydaConst * formHs ((a • ·) '' Ω) α f
        = ENNReal.ofReal (a ^ ((d:ℝ) - α)) *
            (ENNReal.ofReal W.dydaConst * formHs Ω α (fun x => f (a • x))) := by
          rw [formHs_smul ha]; ring
      _ ≤ ENNReal.ofReal (a ^ ((d:ℝ) - α)) *
            ∑' i, formHs (ball (W.ctr i) (W.rad i)) α (fun x => f (a • x)) :=
          mul_le_mul' le_rfl hW
      _ = ∑' i, formHs (ball (a • W.ctr i) (a * W.rad i)) α f := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun i => by rw [hballs i, formHs_smul ha]

theorem solution {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : MeasurableSet Ω)
    (W : WhitneyDomainData d α κ Ω) {a : ℝ} (ha : 0 < a)
    (hf : MemLp f 2 (volume.restrict ((a • ·) '' Ω))) :
    ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs ((a • ·) '' Ω) α f
      ≤ form ((a • ·) '' Ω) k f :=
  QFS.formHs_le_form_domain hc₀ (by rw [Set.image_smul]; exact hΩ.const_smul₀ a)
    (WhitneyDomainData.smul W ha) H hf hFmeas
