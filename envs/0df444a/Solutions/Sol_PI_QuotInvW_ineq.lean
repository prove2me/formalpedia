-- Prove2me | solution 1 for PI.QuotInvW.ineq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:57.101795+00:00
-- url     : https://prove2.me/submissions/1a8b11e0-81ed-43bb-8dbc-e43535c8c51c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
import Theorems.Thm_PI_QuotInvW_measurable_avgS
import Theorems.Thm_PI_QuotInvW_avgS_mm
import Theorems.Thm_PI_QuotInvW_avgS_ne_zero
import Theorems.Thm_PI_QuotInvW_measurable_mm_left
import Theorems.Thm_PI_QuotInvW_mm_assoc
import Theorems.Thm_PI_QuotInvW_mm_mem
import Theorems.Thm_PI_QuotInvW_mm_oneM
import Theorems.Thm_PI_QuotInvW_weil
import Theorems.Thm_PI_QuotInvW_weil_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
namespace PI.QuotInvW
theorem _root_.solution (h : QuotientSetting G S μG μS ν) {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x)
    {g : MtM m} (hg : Matrix.of g ∈ G) :
    ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν := by
  have hGg := h.1
  haveI : SigmaFinite μG := h.2.2.2.1.1
  haveI : SigmaFinite μS := h.2.2.2.2.1.1
  obtain ⟨f0, hf0pos, hf0m, hf0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set f : MtM m → ℝ≥0∞ := fun x => (f0 x : ℝ≥0∞) with hfdef
  have hfm : Measurable f := measurable_coe_nnreal_ennreal.comp hf0m
  have hfpos : ∀ x, f x ≠ 0 := fun x => by simp [f, (hf0pos x).ne']
  have ham : Measurable (avgS μS f) := measurable_avgS hfm
  have ha0 : ∀ x, avgS μS f x ≠ 0 := avgS_ne_zero h hfm hfpos

  have hafin : ∀ᵐ x ∂ν, avgS μS f x < ⊤ := by
    apply ae_lt_top ham
    have := weil h hfm
    change ∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν ≠ ⊤
    rw [← this]
    exact (hf0int.trans ENNReal.one_lt_top).ne
  obtain ⟨hginvG, hgg⟩ := hGg.2.2.2 _ hg
  have hgiG : Matrix.of (minv g) ∈ G := hginvG
  have hdet : IsUnit (Matrix.of g).det :=
    isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩
  have hgig : mm (minv g) g = oneM := by
    have := Matrix.nonsing_inv_mul (Matrix.of g) hdet
    funext i j; exact congrFun (congrFun this i) j
  have hggi : mm g (minv g) = oneM := by
    funext i j; exact congrFun (congrFun hgg i) j
  have hRG : μG.map (rmulQ (Matrix.of (minv g))) = μG := h.2.2.2.2.2.1 _ hgiG

  set F' : MtM m → ℝ≥0∞ := fun x => F x / avgS μS f (mm x (minv g)) with hF'def
  have hF'm : Measurable F' := hF.div (ham.comp (measurable_mm_left (minv g)))
  have hF'i0 : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x := by
    intro s hs x hx
    simp only [F']
    rw [hFi s hs x hx, mm_assoc, avgS_mm h hfm hs]
  have hF'i : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x :=
    fun s hs x hx => hF'i0 (Matrix.of.symm s) hs x hx
  have hL : ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν = ∫⁻ x, F' (mm x g) * f x ∂μG := by
    have := weil_inv h (H := fun x => F' (mm x g)) (f := f) (hF'm.comp (measurable_mm_left g)) hfm
      (by
        intro s hs x hx
        have key : ∀ s' : MtM m, Matrix.of s' ∈ S → F' (mm (mm s' x) g) = F' (mm x g) := by
          intro s' hs'
          rw [mm_assoc]
          exact hF'i0 s' hs' (mm x g) (mm_mem hGg hx hg)
        exact key (Matrix.of.symm s) hs)
    exact this.symm
  have hmid : ∫⁻ x, F' (mm x g) * f x ∂μG = ∫⁻ x, F' x * f (mm x (minv g)) ∂μG := by
    have hφ : Measurable fun x => F' (mm x g) * f x := (hF'm.comp (measurable_mm_left g)).mul hfm
    calc ∫⁻ x, F' (mm x g) * f x ∂μG
        = ∫⁻ x, F' (mm x g) * f x ∂(μG.map (rmulQ (Matrix.of (minv g)))) := by rw [hRG]
      _ = ∫⁻ x, F' (mm (rmulQ (Matrix.of (minv g)) x) g) * f (rmulQ (Matrix.of (minv g)) x) ∂μG :=
          lintegral_map hφ (measurable_mm_left (minv g))
      _ = ∫⁻ x, F' x * f (mm x (minv g)) ∂μG := by
        congr 1; funext x
        have e : mm (rmulQ (Matrix.of (minv g)) x) g = x := by
          change mm (mm x (minv g)) g = x
          rw [mm_assoc, hgig, mm_oneM]
        rw [e]; rfl
  have hR : ∫⁻ x, F' x * f (mm x (minv g)) ∂μG = ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν := by
    have := weil_inv h (H := F') (f := fun x => f (mm x (minv g))) hF'm
      (hfm.comp (measurable_mm_left (minv g))) hF'i
    rw [this]
    congr 1; funext x; congr 1
    unfold avgS
    congr 1; funext s; simp only [mm_assoc]
  have hRHS : ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν ≤ ∫⁻ x, F x ∂ν := by
    apply lintegral_mono; intro x
    simp only [F']
    by_cases hx : avgS μS f (mm x (minv g)) = ⊤
    · rw [hx]; simp
    · rw [ENNReal.div_mul_cancel (ha0 _) hx]
  have hLHS : ∫⁻ x, F (mm x g) ∂ν = ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hafin] with x hx
    simp only [F']
    rw [mm_assoc, hggi, mm_oneM, ENNReal.div_mul_cancel (ha0 x) hx.ne]
  calc ∫⁻ x, F (mm x g) ∂ν = _ := hLHS
    _ = _ := hL
    _ = _ := hmid
    _ = _ := hR
    _ ≤ _ := hRHS
end PI.QuotInvW
