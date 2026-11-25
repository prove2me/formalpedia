-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isSmallFor_mul_7d4a8514a9a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:12:29.979422+00:00
-- url     : https://prove2.me/submissions/f21d030f-078f-4712-93cf-9afcf3779f17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_mul_03f427722e35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_pow_7a3509d44448
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_chartMonomial_ne_zero_74ae91588762
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isLive_of_point_532e268d2994
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_chartForm_c55ff95110ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartForm_bound_86ac715e5797
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {L : HermLine n} {q m r : ℕ} (hrq : r < q) {g : IntegralSection P L.deg}
    {h : IntegralSection P (HermLine.standard n).deg} (hgs : g.SupNormLE L 0)
    (hhs : h.SupNormLE (HermLine.standard n) 0) {s : P.FunField} (hsS : P.IsSmallFor (L.pow (q * m + r)) s) :
    P.IsSmallFor (((L.pow q).mul (HermLine.standard n)).pow (m + 1))
      (s * g.toFun ^ (q - r) * h.toFun ^ (m + 1)) := by
  intro p₀ q₀ δp δq hp hq hδ hrep z hz
  obtain ⟨c, hcz⟩ : ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
    choose c hc using fun k ↦ Function.ne_iff.mp (hz.1 k)
    exact ⟨c, hc⟩
  have hc := isLive_of_point P hz hcz
  obtain ⟨dg, eg, ⟨δg, heg, hδg⟩, hmg⟩ := g.regular c hc
  obtain ⟨dh, eh, ⟨δh, heh, hδh⟩, hmh⟩ := h.regular c hc
  have hfg : IsChartForm P L.deg g.num g.den c dg eg := ⟨⟨δg, heg, hδg⟩, hmg⟩
  have hfh : IsChartForm P (HermLine.standard n).deg h.num h.den c dh eh := ⟨⟨δh, heh, hδh⟩, hmh⟩
  have bg := chartForm_bound P hgs hz hfg hcz
  have bh := chartForm_bound P hhs hz hfh hcz
  have hrepr : P.mkF (p₀ * chartMonomial c dg ^ (q - r) * chartMonomial c dh ^ (m + 1)) =
      s * P.mkF (q₀ * eg ^ (q - r) * eh ^ (m + 1)) := by
    simp only [map_mul, map_pow, mkF_chartForm P g hfg, mkF_chartForm P h hfh, hrep]
    ring
  have hdeg : ∀ k, (((δp + (q - r) • dg + (m + 1) • dh) k : ℕ) : ℤ) =
      ((δq + (q - r) • δg + (m + 1) • δh) k : ℕ) + (L.pow (q * m + r)).deg k := by
    intro k
    have e1 := hδ k
    have e2 := hδg k
    have e3 := hδh k
    simp only [HermLine.pow, HermLine.mul, HermLine.standard, Pi.add_apply, Pi.smul_apply] at e1 e2 e3 ⊢
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at e1 e2 e3 ⊢
    push_cast [Nat.cast_sub hrq.le] at e1 e2 e3 ⊢
    linear_combination e1 - ((q : ℤ) - r) * e2 - ((m : ℤ) + 1) * e3
  have hb := hsS _ _ _ _
    ((hp.mul ((isWeightedHomogeneous_chartMonomial c dg).pow (q - r))).mul
      ((isWeightedHomogeneous_chartMonomial c dh).pow (m + 1)))
    ((hq.mul (heg.pow (q - r))).mul (heh.pow (m + 1))) hdeg hrepr z hz
  have hLm : (L.pow (q * m + r)).metric z = L.metric z ^ (q * m + r) := rfl
  rw [hLm] at hb
  simp only [evalCone_mul, evalCone_pow, norm_mul, norm_pow] at hb
  change ‖evalCone z p₀‖ ≤ ‖evalCone z q₀‖ * (L.metric z ^ q * (HermLine.standard n).metric z) ^ (m + 1)
  have hA : 0 < ‖evalCone z (chartMonomial c dg)‖ := norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hcz dg)
  have hB : 0 < ‖evalCone z (chartMonomial c dh)‖ := norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hcz dh)
  have hl : 0 < L.metric z := L.metric_pos z hz.1
  have hH : 0 < (HermLine.standard n).metric z := (HermLine.standard n).metric_pos z hz.1
  set A := ‖evalCone z (chartMonomial c dg)‖
  set B := ‖evalCone z (chartMonomial c dh)‖
  set l := L.metric z
  set H := (HermLine.standard n).metric z
  have hexp : q - r + (q * m + r) = q * (m + 1) := by
    zify [hrq.le]
    ring
  have key : A ^ (q - r) * B ^ (m + 1) * ‖evalCone z p₀‖ ≤
      A ^ (q - r) * B ^ (m + 1) * (‖evalCone z q₀‖ * (l ^ q * H) ^ (m + 1)) := by
    calc A ^ (q - r) * B ^ (m + 1) * ‖evalCone z p₀‖ = ‖evalCone z p₀‖ * A ^ (q - r) * B ^ (m + 1) := by ring
      _ ≤ ‖evalCone z q₀‖ * ‖evalCone z eg‖ ^ (q - r) * ‖evalCone z eh‖ ^ (m + 1) * l ^ (q * m + r) := hb
      _ ≤ ‖evalCone z q₀‖ * (A * l) ^ (q - r) * (B * H) ^ (m + 1) * l ^ (q * m + r) := by gcongr
      _ = A ^ (q - r) * B ^ (m + 1) * (‖evalCone z q₀‖ * (l ^ q * H) ^ (m + 1)) := by
        rw [mul_pow (l ^ q), ← pow_mul, ← hexp, pow_add l (q - r)]
        ring
  exact le_of_mul_le_mul_left key (by positivity)
end GroundTheory.Heights₂.Heights.MonomialMapNorm
