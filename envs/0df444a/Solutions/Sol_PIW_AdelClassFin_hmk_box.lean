-- Prove2me | solution 1 for PIW.AdelClassFin.hmk_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:49.843014+00:00
-- url     : https://prove2.me/submissions/9f6cadc6-53e0-4568-b0ba-e74664bb723a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor
import Theorems.Thm_PIW_AdelClassFin_hmk_int
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open MeasureTheory Matrix Module
open scoped MatrixOrder
namespace PIW.AdelClassFin
theorem _root_.solution {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.det ≠ 0) :
    ∃ c : Fin N → ℤ, c ≠ 0 ∧
      ∀ i, |(B *ᵥ fun j => (c j : ℝ)) i| ≤ 2 * |B.det| ^ ((1 : ℝ) / N) := by
  set d := |B.det| with hd
  have hd0 : 0 < d := abs_pos.mpr hB
  set t := 2 * d ^ ((1 : ℝ) / N) with ht
  have ht0 : 0 < t := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have htN : t ^ N = 2 ^ N * d := by
    rw [ht, mul_pow, ← Real.rpow_natCast (d ^ _), ← Real.rpow_mul hd0.le]
    rw [one_div_mul_cancel hN0, Real.rpow_one]
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Matrix.toLin' B
  have hf : LinearMap.det f ≠ 0 := by rw [LinearMap.det_toLin']; exact hB
  let box : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-t) t
  let s : Set (Fin N → ℝ) := f ⁻¹' box
  let b := Pi.basisFun ℝ (Fin N)
  have fund := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin N → ℝ))
  have hvolF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp
  have hvolbox : volume box = ENNReal.ofReal (2 * t) ^ N := by
    simp only [box]
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hvols : volume s = ENNReal.ofReal (4 ^ N) := by
    simp only [s]
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hf, hvolbox,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [LinearMap.det_toLin', abs_inv, ← hd, mul_pow, htN]
    rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
    field_simp
  have h_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      map_neg, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  have h_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Icc (-t) t).linear_preimage f
  have h : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (Fin N → ℝ) < volume s := by
    rw [hvolF, one_mul, hvols, Module.finrank_fin_fun]
    rw [show (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv h
  obtain ⟨c, hc⟩ := hmk_int (x : Fin N → ℝ) x.2
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply hx0
    ext i
    have := congrFun hc i
    simp at this
    simp [← this]
  · intro i
    have := hxs
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc] at this
    rw [hc]
    exact abs_le.mpr (this i)
end PIW.AdelClassFin
