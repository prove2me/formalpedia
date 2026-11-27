-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.coreB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:49.097207+00:00
-- url     : https://prove2.me/submissions/5dc8276b-ac0d-4ae7-a947-c1ffc37ac237

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_rationalWeight_le
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_mj
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_Dec_bound
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuousOn_rationalWeight
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_open_U
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_shift
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_ch
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_nm
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_pr
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_core_bump
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_exists_density
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_measurable_reduced_size
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_pos
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_ch
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_rationalWeight_ne_zero
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_tate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution [FirstCountableTopology K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {π : K × (ι → ℂ) → X} {x₀ : X} (hπ : Prp π x₀)
    (κ : ι → ℕ) (e : ℕ) (hκ : ∀ w, 2 * e < κ w) {a : K × (ι → ℂ) → ℂ} (ha : Continuous a) (hd : Dec a) (c : ℂ)
    (β : K × X → ι → ℂ) (hβ : Continuous β) (D : ℝ) (hD : ∀ k η, ‖β (k, η)‖ ≤ D * ‖η‖)
    (hp : ∀ k η t, pr (β (k, η)) t = ⟪η, π (k, t)⟫)
    (hpos : ∀ p, π p = x₀ → 0 < (FT (fun x => a (p.1, x)) p.2 * ((r0 κ e p.2)⁻¹ * ((nm p.2 : ℝ) : ℂ)⁻¹) * c).re)
    (h : ∀ η, ∫ k, ∫ x, a (k, x + β (k, η)) * r0 κ e x ∂volume ∂μ = 0) : False := by
  obtain ⟨ε, S, hε, hS, hSU, hb⟩ := hπ.cpt
  obtain ⟨p₀, h₀⟩ := hπ.pt
  obtain ⟨C, N, hC0, hC⟩ := hd.bound (2 * e * Fintype.card ι)
  have hle : ∀ k x b, ‖a (k, x + b)‖ ≤ C * (1 + ‖b‖) ^ N * mj x := fun k x b =>
    le_trans (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg x]))) (hC k x b)
  have hler : ∀ k x b, ‖a (k, x + b) * r0 κ e x‖ ≤ C * (1 + ‖b‖) ^ N * mj x := fun k x b => by
    rw [norm_mul]; exact le_trans (by gcongr; exact norm_rationalWeight_le κ e x) (hC k x b)
  have hF : Continuous fun p : K × (ι → ℂ) => FT (fun x => a (p.1, x)) p.2 := by
    have : Continuous fun p : K × (ι → ℂ) => ∫ x, ch (-pr x p.2) * a (p.1, x) := by
      have hu : Continuous (Function.uncurry fun (p : K × (ι → ℂ)) (x : ι → ℂ) => ch (-pr x p.2) * a (p.1, x)) :=
        (continuous_ch.comp (continuous_pr.comp (f := fun q : (K × (ι → ℂ)) × (ι → ℂ) => (q.2, q.1.2)) (by fun_prop)).neg).mul
          (ha.comp (f := fun q : (K × (ι → ℂ)) × (ι → ℂ) => (q.1.1, q.2)) (by fun_prop))
      refine continuous_of_dominated (bound := fun x => C * mj x) (fun p => (hu.uncurry_left p).aestronglyMeasurable)
        (fun p => Eventually.of_forall fun x => ?_) (integrable_mj.const_mul C)
        (Eventually.of_forall fun x => hu.uncurry_right x)
      rw [norm_mul, norm_ch, one_mul]
      simpa using hle p.1 x 0
    exact this
  obtain ⟨φ, -, hint, hφ⟩ := core_bump (μ.prod volume) π hπ.cont x₀
    (fun p => FT (fun x => a (p.1, x)) p.2 * ((r0 κ e p.2)⁻¹ * ((nm p.2 : ℝ) : ℂ)⁻¹) * c) _ S open_U
    ((hF.continuousOn.mul ((((continuousOn_rationalWeight κ e).comp continuous_snd.continuousOn fun p hp => hp).inv₀ fun p hp => rationalWeight_ne_zero κ e hp).mul
      ((Complex.continuous_ofReal.comp (continuous_nm.comp continuous_snd)).continuousOn.inv₀ fun p hp => by
        simpa using (nm_pos hp).ne'))).mul continuousOn_const) hS hSU ε hε hb hpos p₀ h₀
  obtain ⟨b, hb'⟩ := exists_density φ
  obtain ⟨Z, hZ⟩ := tate κ e hκ
  have hD0 : ∀ η : X, ∀ k, (1 + ‖β (k, η)‖) ^ N ≤ (1 + |D|) ^ N * (1 + ‖η‖) ^ N := fun η k => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    nlinarith [hD k η, le_abs_self D, abs_nonneg D, norm_nonneg η]
  have hbi : Integrable fun η : X => C * ((1 + |D|) ^ N * (1 + ‖η‖) ^ N) * ‖b η‖ := by
    have : Integrable fun η : X => (1 + ‖η‖) ^ N * ‖b η‖ := by
      simp only [add_comm (1 : ℝ), add_pow, one_pow, mul_one, Finset.sum_mul]
      exact integrable_finsetSum _ fun i _ => by
        simpa [mul_right_comm] using (b.integrable_pow_mul volume i).mul_const (N.choose i : ℝ)
    simpa [mul_assoc] using this.const_mul (C * (1 + |D|) ^ N)
  have hcont : Continuous fun q : (K × (ι → ℂ)) × X => b q.2 * a (q.1.1, q.1.2 + β (q.1.1, q.2)) := by
    have := b.continuous; fun_prop
  have bd : ∀ (k : K) (x : ι → ℂ) (η : X) (t : ℂ), ‖t‖ ≤ C * (1 + ‖β (k, η)‖) ^ N * mj x →
      ‖b η * t‖ ≤ mj x * (C * ((1 + |D|) ^ N * (1 + ‖η‖) ^ N) * ‖b η‖) := fun k x η t ht => by
    have hm : 0 ≤ mj x := by unfold mj; positivity
    rw [norm_mul]
    calc _ ≤ ‖b η‖ * (C * ((1 + |D|) ^ N * (1 + ‖η‖) ^ N) * mj x) := by
          gcongr; exact ht.trans (by gcongr; exact hD0 η k)
      _ = _ := by ring
  have I3 : Integrable (fun q : (K × (ι → ℂ)) × X => b q.2 * (a (q.1.1, q.1.2 + β (q.1.1, q.2)) * r0 κ e q.1.2))
      ((μ.prod volume).prod volume) := by
    refine (((integrable_const (1 : ℝ)).mul_prod integrable_mj).mul_prod hbi).mono' ?_ (Eventually.of_forall fun q => ?_)
    · simp only [← mul_assoc]
      exact (hcont.measurable.mul ((measurable_reduced_size κ e).comp (measurable_snd.comp measurable_fst))).aestronglyMeasurable
    · rw [one_mul]; exact bd _ _ _ _ (hler _ _ _)
  have I2 : ∀ k, Integrable (fun q : (ι → ℂ) × X => b q.2 * a (k, q.1 + β (k, q.2))) (volume.prod volume) := fun k =>
    (integrable_mj.mul_prod hbi).mono' (hcont.comp (f := fun q : (ι → ℂ) × X => ((k, q.1), q.2)) (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun q => bd _ _ _ _ (hle _ _ _))
  have I2r : ∀ k, Integrable (fun q : (ι → ℂ) × X => b q.2 * (a (k, q.1 + β (k, q.2)) * r0 κ e q.1)) (volume.prod volume) := fun k => by
    refine (integrable_mj.mul_prod hbi).mono' ?_ (Eventually.of_forall fun q => bd _ _ _ _ (hler _ _ _))
    simp only [← mul_assoc]
    exact (I2 k).1.mul ((measurable_reduced_size κ e).comp measurable_fst).aestronglyMeasurable
  let H : K → (ι → ℂ) → ℂ := fun k x => ∫ η, b η * a (k, x + β (k, η))
  have hHr : ∀ k x, H k x * r0 κ e x = ∫ η, b η * (a (k, x + β (k, η)) * r0 κ e x) := fun k x => by
    simp only [H, ← mul_assoc]; rw [integral_mul_const]
  have hFH : ∀ k t, FT (H k) t = φ (π (k, t)) * FT (fun x => a (k, x)) t := fun k t => by
    have hi : Integrable (fun q : (ι → ℂ) × X => ch (-pr q.1 t) * (b q.2 * a (k, q.1 + β (k, q.2)))) (volume.prod volume) :=
      (I2 k).bdd_mul (c := 1) (continuous_ch.comp (continuous_pr.comp (continuous_fst.prodMk continuous_const)).neg).aestronglyMeasurable
        (Eventually.of_forall fun q => (norm_ch _).le)
    calc FT (H k) t = ∫ x, ∫ η, ch (-pr x t) * (b η * a (k, x + β (k, η))) := by
          rw [FT]; congr 1; funext x; rw [integral_const_mul]
      _ = ∫ η, ∫ x, ch (-pr x t) * (b η * a (k, x + β (k, η))) := integral_integral_swap hi
      _ = _ := by
          rw [hb', ← integral_mul_const]; congr 1; funext η
          simp only [mul_left_comm _ (b η)]
          rw [integral_const_mul, FT_shift (fun x => a (k, x)), hp]; ring
  have h0 : ∫ k, ∫ x, H k x * r0 κ e x ∂volume ∂μ = 0 := by
    simp only [hHr]
    rw [← integral_prod _ I3.integral_prod_left, integral_integral_swap I3]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [I3.swap.prod_right_ae] with η hη
    refine (integral_prod _ hη).trans ?_
    simp only [Function.comp, Prod.swap, integral_const_mul, h, mul_zero]
  apply hφ
  by_cases hc : c = 0
  · simp [hc]
  rw [integral_prod _ hint]
  have : ∀ᵐ k ∂μ, ∫ t, φ (π (k, t)) * (FT (fun x => a (k, x)) t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) * c) =
      (Z * c) * ∫ x, H k x * r0 κ e x := by
    filter_upwards [hint.prod_right_ae] with k hk
    have e1 : ∀ t, φ (π (k, t)) * (FT (fun x => a (k, x)) t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) * c) =
        FT (H k) t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) * c := fun t => by rw [hFH]; ring
    simp only [e1] at hk ⊢
    rw [integral_mul_const, hZ (H k) (I2 k).integral_prod_left (by simpa only [hHr] using (I2r k).integral_prod_left)
      (by simpa [mul_assoc, hc] using hk.mul_const c⁻¹)]
    ring
  rw [integral_congr_ae this, integral_const_mul, h0, mul_zero]
end PositivityTheory.ThKG.Loc.Bump
