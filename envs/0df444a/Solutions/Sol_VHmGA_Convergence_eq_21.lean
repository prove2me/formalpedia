-- Prove2me | solution 1 for VHmGA.Convergence.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T07:08:58.447662+00:00
-- url     : https://prove2.me/submissions/949eee7f-c789-424b-a28c-6aa6fa705477

import Mathlib
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_VHmGA_Convergence_Defs

set_option autoImplicit false
open scoped InnerProductSpace
open MeasureTheory

namespace VHmGA.Convergence.Eq21Route

abbrev EE (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma hasDerivAt_line {n : ℕ} (F : EE n → ℝ) (g : EE n → EE n) (L : ℝ)
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (x d : EE n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • d)) (inner ℝ (g (x + t • d)) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h2 := (hF.2.1 (x + t • d)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt t h1
  simp only [InnerProductSpace.toDual_apply_apply] at h3
  exact h3

lemma smooth_descent {n : ℕ} (F : EE n → ℝ) (g : EE n → EE n) (L : ℝ)
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (x y : EE n) :
    F y ≤ F x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  set ψ : ℝ → ℝ := fun t => F (x + t • d) - t * inner ℝ (g x) d - L / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  have hder : ∀ t, HasDerivAt ψ
      (inner ℝ (g (x + t • d)) d - inner ℝ (g x) d - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := hasDerivAt_line F g L hF x d t
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g x) d) (inner ℝ (g x) d) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (g x) d)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
      have h := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      exact h.congr_deriv (by rw [show (2 : ℕ) - 1 = 1 from rfl]; push_cast; ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hder t).continuousAt.continuousWithinAt
    · exact fun t _ => (hder t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t).deriv]
      have h1 : inner ℝ (g (x + t • d)) d - inner ℝ (g x) d =
          inner ℝ (g (x + t • d) - g x) d := by
        rw [inner_sub_left]
      have h2 : inner ℝ (g (x + t • d) - g x) d ≤
          ‖g (x + t • d) - g x‖ * ‖d‖ := real_inner_le_norm _ _
      have h3 : ‖g (x + t • d) - g x‖ ≤ L * ‖t • d‖ := by
        have h := hF.2.2 (x + t • d) x
        simpa using h
      have h4 : ‖t • d‖ = t * ‖d‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      have h5 : ‖g (x + t • d) - g x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ := by
        rw [h4] at h3
        exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      nlinarith
  have hmono := hanti (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
    (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [hψ] at hmono
  have hxd : x + d = y := by simp [hd]
  simp at hmono
  rw [hxd] at hmono
  linarith

lemma one_step_descent {n : ℕ} (F : EE n → ℝ) (g : EE n → EE n) (L η : ℝ)
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (x v : EE n) :
    F (x - η • v) ≤ F x - η * inner ℝ (g x) v + L * η ^ 2 / 2 * ‖v‖ ^ 2 := by
  have h := smooth_descent F g L hF x (x - η • v)
  have hsub : (x - η • v) - x = -(η • v) := by
    exact sub_sub_cancel_left x (η • v)
  rw [hsub] at h
  simp only [inner_neg_right, norm_neg, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at h
  nlinarith

lemma condExp_inner_pullout {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {f g : Ω → E} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (fun ω => inner ℝ (f ω) (g ω)) μ) (hg : Integrable g μ) :
    μ[fun ω => inner ℝ (f ω) (g ω) | m] =ᵐ[μ]
      fun ω => inner ℝ (f ω) (μ[g | m] ω) := by
  exact MeasureTheory.condExp_bilin_of_stronglyMeasurable_left
    (innerSL ℝ) hf hfg hg


lemma gradient_memLp {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : EE d → ℝ} {g : EE d → EE d} {L : ℝ}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L)
    {w : Ω → EE d} (hw : MemLp w 2 μ) : MemLp (fun ω => g (w ω)) 2 μ := by
  have hgl : LipschitzWith ⟨L, hF.1⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖g x - g y‖ ≤ L * ‖x - y‖
    exact hF.2.2 x y
  have hcenter : LipschitzWith ⟨L, hF.1⟩ (fun x => g x - g 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hgl.dist_le_mul x y
  have hcomp := hcenter.comp_memLp (by simp) hw
  have hconst : MemLp (fun _ : Ω => g 0) 2 μ := memLp_const _
  convert hcomp.add hconst using 1 <;> ext x <;> simp [Function.comp_def]


lemma error_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} {u v : Ω → EE d}
    (hu : Integrable u μ) (hv : MemLp v 2 μ)
    (he : Integrable (fun ω => ‖u ω - v ω‖ ^ 2) μ) :
    MemLp (fun ω => u ω - v ω) 2 μ := by
  have hsm : AEStronglyMeasurable (fun ω => u ω - v ω) μ :=
    hu.aestronglyMeasurable.sub hv.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hsm).2 he


lemma aggregate_memLp {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : EE d → ℝ} {g : EE d → EE d} {L : ℝ} {η : ℕ → ℝ}
    {w1 : EE d} {w gt : ℕ → Ω → EE d} {m : ℕ → MeasurableSpace Ω} {s : ℝ}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L)
    (hrun : VHmGA.Convergence.IsVerifiedSGDRun μ g η w1 w gt m s)
    (t : ℕ) (ht : 1 ≤ t) (hw : MemLp (w t) 2 μ) : MemLp (gt t) 2 μ := by
  letI := hrun.isProbabilityMeasure
  have hg := gradient_memLp hF hw
  have he := error_memLp (hrun.integrable_agg t ht) hg (hrun.integrable_err t ht)
  convert he.add hg using 1 <;> ext ω <;> simp [Function.comp_def]


lemma iterates_memLp {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : EE d → ℝ} {g : EE d → EE d} {L : ℝ} {η : ℕ → ℝ}
    {w1 : EE d} {w gt : ℕ → Ω → EE d} {m : ℕ → MeasurableSpace Ω} {s : ℝ}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L)
    (hrun : VHmGA.Convergence.IsVerifiedSGDRun μ g η w1 w gt m s) :
    ∀ t, 1 ≤ t → MemLp (w t) 2 μ := by
  intro t ht
  letI := hrun.isProbabilityMeasure
  induction t, ht using Nat.le_induction with
  | base =>
      rw [hrun.init]
      exact memLp_const _
  | succ n hn ih =>
      have hg := aggregate_memLp hF hrun n hn ih
      rw [funext (hrun.update n hn)]
      exact ih.sub (hg.const_smul (η n))

lemma smooth_abs_bound {d : ℕ} (F : EE d → ℝ) (g : EE d → EE d) (L : ℝ)
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (x : EE d) :
    ‖F x‖ ≤ |F 0| + ‖g 0‖ * ‖x‖ + (2 * L) * ‖x‖ ^ 2 := by
  have hupper := smooth_descent F g L hF 0 x
  have hlower := smooth_descent F g L hF x 0
  have hgrad : ‖g x‖ ≤ ‖g 0‖ + L * ‖x‖ := by
    have h := hF.2.2 x 0
    have hsub : ‖g x‖ ≤ ‖g x - g 0‖ + ‖g 0‖ := by
      calc
        ‖g x‖ = ‖(g x - g 0) + g 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖g x - g 0‖ + ‖g 0‖ := norm_add_le _ _
    rw [show x - (0 : EE d) = x by simp] at h
    linarith
  have hinner0 := abs_real_inner_le_norm (g 0) x
  have hinnerx := abs_real_inner_le_norm (g x) x
  have hinner0lo : -(‖g 0‖ * ‖x‖) ≤ inner ℝ (g 0) x := (abs_le.mp hinner0).1
  have hinner0hi : inner ℝ (g 0) x ≤ ‖g 0‖ * ‖x‖ := (abs_le.mp hinner0).2
  have hinnerxlo : -(‖g x‖ * ‖x‖) ≤ inner ℝ (g x) x := (abs_le.mp hinnerx).1
  have hgradmul : ‖g x‖ * ‖x‖ ≤ (‖g 0‖ + L * ‖x‖) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hgrad (norm_nonneg _)
  have hu : F x ≤ |F 0| + ‖g 0‖ * ‖x‖ + (2 * L) * ‖x‖ ^ 2 := by
    have h : F x ≤ F 0 + inner ℝ (g 0) x + L / 2 * ‖x‖ ^ 2 := by
      simpa [sub_zero] using hupper
    have hF0 : F 0 ≤ |F 0| := le_abs_self _
    nlinarith [hF.1, hF0, sq_nonneg (‖x‖)]
  have hl : -( |F 0| + ‖g 0‖ * ‖x‖ + (2 * L) * ‖x‖ ^ 2) ≤ F x := by
    have h : F 0 ≤ F x + -inner ℝ (g x) x + L / 2 * ‖x‖ ^ 2 := by
      simpa using hlower
    have hF0 : -|F 0| ≤ F 0 := neg_abs_le _
    nlinarith [hF.1, hF0, sq_nonneg (‖x‖)]
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hl, hu⟩

lemma objective_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : EE d → ℝ} {g : EE d → EE d} {L : ℝ}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L)
    {w : Ω → EE d} (hw : MemLp w 2 μ) : Integrable (fun ω => F (w ω)) μ := by
  have hnorm : Integrable (fun ω => ‖w ω‖) μ := (hw.norm).integrable (by norm_num)
  have hnorm2 : Integrable (fun ω => ‖w ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  have hconst : Integrable (fun _ : Ω => |F 0|) μ := integrable_const _
  have hbound : Integrable
      (fun ω => |F 0| + ‖g 0‖ * ‖w ω‖ + (2 * L) * ‖w ω‖ ^ 2) μ := by
    exact (hconst.add (hnorm.const_mul ‖g 0‖)).add
      (hnorm2.const_mul (2 * L))
  have hcont : Continuous F :=
    continuous_iff_continuousAt.mpr (fun x => (hF.2.1 x).continuousAt)
  have hmeas : AEStronglyMeasurable (fun ω => F (w ω)) μ :=
    hcont.comp_aestronglyMeasurable hw.aestronglyMeasurable
  apply hbound.mono' hmeas
  filter_upwards [] with ω
  exact smooth_abs_bound F g L hF (w ω)


lemma inner_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → EE d} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => inner ℝ (f ω) (g ω)) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  apply h.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hωf hωg
  rw [← hωf, ← hωg]


theorem eq21_integrability {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : EE d → ℝ} {g : EE d → EE d} {L : ℝ} {η : ℕ → ℝ}
    {σ σDP σa α : ℝ} {w1 : EE d} {w gt : ℕ → Ω → EE d}
    {m : ℕ → MeasurableSpace Ω}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hL : 0 < L)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrun : VHmGA.Convergence.IsVerifiedSGDRun μ g η w1 w gt m
      (VHmGA.Convergence.sigmaTotalSq σ σDP σa α))
    (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun ω => F (w (t + 1) ω)) μ ∧
    Integrable (fun ω => ‖gt t ω‖ ^ 2) μ := by
  letI := hrun.isProbabilityMeasure
  have hw := iterates_memLp hF hrun t ht
  have hwNext := iterates_memLp hF hrun (t + 1) (by omega)
  have hgt := aggregate_memLp hF hrun t ht hw
  exact ⟨objective_integrable hF hwNext,
    (memLp_two_iff_integrable_sq_norm hgt.aestronglyMeasurable).mp hgt⟩


theorem eq21_complete {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : EE d → ℝ} {g : EE d → EE d} {L : ℝ} {η : ℕ → ℝ}
    {σ σDP σa α : ℝ} {w1 : EE d} {w gt : ℕ → Ω → EE d}
    {m : ℕ → MeasurableSpace Ω}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hL : 0 < L)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrun : VHmGA.Convergence.IsVerifiedSGDRun μ g η w1 w gt m
      (VHmGA.Convergence.sigmaTotalSq σ σDP σa α))
    (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun ω => F (w (t + 1) ω)) μ ∧
    Integrable (fun ω => ‖gt t ω‖ ^ 2) μ ∧
    μ[fun ω => F (w (t + 1) ω) | m t] ≤ᵐ[μ] fun ω =>
      F (w t ω) - η t * ‖g (w t ω)‖ ^ 2 +
        L * η t ^ 2 / 2 * μ[fun ω' => ‖gt t ω'‖ ^ 2 | m t] ω := by
  letI := hrun.isProbabilityMeasure
  have hFint := objective_integrable hF (iterates_memLp hF hrun t ht)
  have hgtMem := aggregate_memLp hF hrun t ht (iterates_memLp hF hrun t ht)
  have hgtSq := (memLp_two_iff_integrable_sq_norm hgtMem.aestronglyMeasurable).mp hgtMem
  have hFnext := objective_integrable hF (iterates_memLp hF hrun (t + 1) (by omega))
  have hinner := inner_integrable (gradient_memLp hF (iterates_memLp hF hrun t ht)) hgtMem
  have hgtInt := hrun.integrable_agg t ht
  let f0 : Ω → ℝ := fun ω => F (w t ω)
  let f1 : Ω → ℝ := fun ω => inner ℝ (g (w t ω)) (gt t ω)
  let f2 : Ω → ℝ := fun ω => ‖gt t ω‖ ^ 2
  let coeff : ℝ := L * η t ^ 2 / 2
  let rhs : Ω → ℝ := fun ω => f0 ω - η t * f1 ω + coeff * f2 ω
  have hcross : Integrable (fun ω => η t * f1 ω) μ := hinner.const_mul (η t)
  have hnoise : Integrable (fun ω => coeff * f2 ω) μ := hgtSq.const_mul coeff
  have hrhs : Integrable rhs μ := by
    dsimp [rhs]
    exact (hFint.sub hcross).add hnoise
  have hstep : ∀ ω, F (w (t + 1) ω) ≤ rhs ω := by
    intro ω
    dsimp [rhs, f0, f1, f2, coeff]
    rw [hrun.update t ht ω]
    exact one_step_descent F g L (η t) hF (w t ω) (gt t ω)
  have hmono := condExp_mono (m := m t) hFnext hrhs (Filter.Eventually.of_forall hstep)
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.mpr (fun x => (hF.2.1 x).continuousAt)
  have hFsm : StronglyMeasurable[m t] f0 := by
    exact hFcont.comp_stronglyMeasurable (hrun.stronglyMeasurable_iter t ht)
  have hceF := condExp_of_stronglyMeasurable (hrun.le_ambient t ht) hFsm hFint
  have hceFae : μ[f0 | m t] =ᵐ[μ] f0 := Filter.Eventually.of_forall fun ω => congrFun hceF ω
  have hgl : LipschitzWith ⟨L, hF.1⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖g x - g y‖ ≤ L * ‖x - y‖
    exact hF.2.2 x y
  have hgsm : StronglyMeasurable[m t] (fun ω => g (w t ω)) :=
    hgl.continuous.comp_stronglyMeasurable (hrun.stronglyMeasurable_iter t ht)
  have hceInner := condExp_inner_pullout hgsm hinner hgtInt
  have hceInner' : μ[f1 | m t] =ᵐ[μ] fun ω => ‖g (w t ω)‖ ^ 2 := by
    filter_upwards [hceInner, hrun.unbiased t ht] with ω hleft hmean
    calc
      μ[f1 | m t] ω = inner ℝ (g (w t ω)) (μ[gt t | m t] ω) := hleft
      _ = inner ℝ (g (w t ω)) (g (w t ω)) := by rw [hmean]
      _ = ‖g (w t ω)‖ ^ 2 := by simpa using (inner_self_eq_norm_sq_to_K (g (w t ω)))
  have hceCross : μ[fun ω => η t * f1 ω | m t] =ᵐ[μ]
      fun ω => η t * μ[f1 | m t] ω := by
    convert (condExp_smul (μ := μ) (η t) f1 (m t)) using 1 <;> ext ω <;> rfl
  have hceNoise : μ[fun ω => coeff * f2 ω | m t] =ᵐ[μ]
      fun ω => coeff * μ[f2 | m t] ω := by
    convert (condExp_smul (μ := μ) coeff f2 (m t)) using 1 <;> ext ω <;> rfl
  have hceRhs : μ[rhs | m t] =ᵐ[μ]
      fun ω => μ[f0 | m t] ω - η t * μ[f1 | m t] ω + coeff * μ[f2 | m t] ω := by
    calc
      μ[rhs | m t] =ᵐ[μ]
          μ[fun ω => f0 ω - η t * f1 ω + coeff * f2 ω | m t] :=
            Filter.EventuallyEq.rfl
      _ =ᵐ[μ]
          fun ω => μ[fun ω => f0 ω - η t * f1 ω | m t] ω +
            μ[fun ω => coeff * f2 ω | m t] ω :=
              condExp_add (μ := μ) (hFint.sub hcross) hnoise (m t)
      _ =ᵐ[μ] fun ω =>
          (μ[f0 | m t] ω - μ[fun ω => η t * f1 ω | m t] ω) +
            μ[fun ω => coeff * f2 ω | m t] ω := by
              exact (condExp_sub (μ := μ) hFint hcross (m t)).add
                (Filter.EventuallyEq.rfl)
      _ =ᵐ[μ] fun ω =>
          μ[f0 | m t] ω - η t * μ[f1 | m t] ω + coeff * μ[f2 | m t] ω := by
              filter_upwards [hceCross, hceNoise] with ω hc hn
              rw [hc, hn]
  have hfinal : μ[rhs | m t] =ᵐ[μ] fun ω =>
      F (w t ω) - η t * ‖g (w t ω)‖ ^ 2 +
        L * η t ^ 2 / 2 * μ[fun ω' => ‖gt t ω'‖ ^ 2 | m t] ω := by
    filter_upwards [hceRhs, hceFae, hceInner'] with ω hr hf hi
    dsimp [f0, f1, f2, coeff] at hr
    rw [hf, hi] at hr
    simpa using hr
  exact ⟨hFnext, hgtSq, hmono.trans_eq hfinal⟩

end VHmGA.Convergence.Eq21Route


theorem solution {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {L : ℝ} {η : ℕ → ℝ}
    {σ σDP σa α : ℝ} {w1 : EuclideanSpace ℝ (Fin d)}
    {w gt : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {m : ℕ → MeasurableSpace Ω}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hL : 0 < L)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrun : VHmGA.Convergence.IsVerifiedSGDRun μ g η w1 w gt m
      (VHmGA.Convergence.sigmaTotalSq σ σDP σa α))
    (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun ω => F (w (t + 1) ω)) μ ∧
    Integrable (fun ω => ‖gt t ω‖ ^ 2) μ ∧
    μ[fun ω => F (w (t + 1) ω) | m t] ≤ᵐ[μ] fun ω =>
      F (w t ω) - η t * ‖g (w t ω)‖ ^ 2 +
        L * η t ^ 2 / 2 * μ[fun ω' => ‖gt t ω'‖ ^ 2 | m t] ω := by
  exact VHmGA.Convergence.Eq21Route.eq21_complete hF hL hα0 hα1 hrun t ht
