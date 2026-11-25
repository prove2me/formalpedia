-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsE_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:43.373272+00:00
-- url     : https://prove2.me/submissions/aa9b994e-dfd1-464c-8925-846d9817b94f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_sqn_s_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_meas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_sqn_cont
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_sqn_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_Mset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
open Classical
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 2 ≤ T') (h : A.Mset w0 s De → ℂ) (hh : Holo n (flatStein A hD hF).z h)
    (hint : ∫⁻ y in A.Mset w0 s De, (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) y ∂A.mu < ⊤) (y : Y) :
    ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ∂A.mu < ⊤ := by
  obtain ⟨C, hC⟩ := hD.s_le_w
  have hMo := isOpen_Mset A (De := De) hD
  set C' := max C 1 with hC'
  set K := A.sqn L w y + 1 with hK
  have hK0 : 0 < K := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => bsA_nsq_nonneg A L (w k) y
    simp only [sqn] at hK ⊢; linarith
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hp : 0 ≤ (T' : ℝ) - 3 / 2 := by
    have : (2 : ℝ) ≤ T' := by exact_mod_cast hT
    linarith
  set c := (C' * K) ^ (-((T' : ℝ) - 3 / 2)) * K ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hK0 _)
  set U := {y' | A.sqn L w y' < K} with hU
  have hUo : IsOpen U := isOpen_lt (bsA_sqn_cont A hD.sec_w) continuous_const
  have hyU : y ∈ U := by simp [hU, hK]
  refine ⟨U, hUo.mem_nhds hyU, ?_⟩
  set ψ := (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) with hψ
  have hbound : ∀ x ∈ U ∩ A.Mset w0 s De, ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ≤
      ENNReal.ofReal c⁻¹ * ψ x := by
    intro x hx
    rw [hψ, Set.piecewise_eq_of_mem _ _ _ hx.2, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs := bsE_sqn_s_pos A hD hF hσ hX hx.2
    have hw := bsA_sqn_pos A (la := L) (hD.no_common_zero x) (w := w)
    have hwK : A.sqn L w x ≤ K := le_of_lt hx.1
    have hsK : A.sqn L s x ≤ C' * K := by
      calc A.sqn L s x ≤ C * A.sqn L w x := hC x
        _ ≤ C' * A.sqn L w x := mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le
        _ ≤ C' * K := mul_le_mul_of_nonneg_left hwK (by positivity)
    have hW : c ≤ bsW A L w s T' x := by
      unfold bsW
      exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hs hsK (by linarith))
        (Real.rpow_le_rpow_of_nonpos hw hwK (by norm_num)) (Real.rpow_pos_of_pos hK0 _).le
        (Real.rpow_nonneg hs.le _)
    have hn0 := bsA_nsq_nonneg A (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x
    calc A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x
        = c⁻¹ * (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x * c) := by
          field_simp
      _ ≤ c⁻¹ * (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
          bsW A L w s T' x) := by gcongr
  calc ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal
        (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ∂A.mu
      ≤ ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal c⁻¹ * ψ x ∂A.mu :=
        setLIntegral_mono' (hUo.inter hMo).measurableSet hbound
    _ ≤ ∫⁻ x in A.Mset w0 s De, ENNReal.ofReal c⁻¹ * ψ x ∂A.mu :=
        lintegral_mono_set Set.inter_subset_right
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x in A.Mset w0 s De, ψ x ∂A.mu :=
        lintegral_const_mul _ (bsE_meas A hD hF hσ hX T' h hh)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
end ReciprocityTheory.L2DbarEstimates.Y
