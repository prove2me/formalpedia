-- Prove2me | solution 1 for ZetaZeros.D.EllReg.weakEquationFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:56:39.643053+00:00
-- url     : https://prove2.me/submissions/6407b9b9-7e72-466e-a490-05b8d994b0d6

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_dw
import Theorems.Thm_ZetaZeros_D_EllReg_WF_lb_good
import Theorems.Thm_ZetaZeros_D_EllReg_WF_leib
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_sb
import Theorems.Thm_ZetaZeros_D_EllReg_WF_sb_good
import Theorems.Thm_ZetaZeros_D_EllReg_WF_good_mono
import Theorems.Thm_ZetaZeros_D_EllReg_WF_cf_good
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_eq_cf
import Theorems.Thm_ZetaZeros_D_EllReg_WF_dw_congr
import Theorems.Thm_P2M_ZetaZeros_D_EllReg_WF_contDiff_ofReal__ad18da8cd330
import Theorems.Thm_ZetaZeros_D_EllReg_WF_smooth_cut
import Theorems.Thm_ZetaZeros_D_EllReg_WF_intg
import Theorems.Thm_ZetaZeros_D_EllReg_WF_swap4
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_eF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
namespace WF
variable {d : ℕ}
private theorem formalAdjoint_mul_expand_lemma_3 {m : ℕ} {B : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ}
    (hB : ∀ n w, ContDiff ℝ ∞ (B n w)) {a φ : ZetaZeros.D.EllReg.E d → ℂ} (ha : ContDiff ℝ ∞ a) (hφ : ContDiff ℝ ∞ φ) (y : ZetaZeros.D.EllReg.E d) :
    ZetaZeros.D.EllReg.trOp m B (fun z => a z * φ z) y = a y * ZetaZeros.D.EllReg.trOp m B φ y +
      ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ev (sb (B n w) (lb (List.ofFn w) a)) φ y := by
  have key : ∀ (n : ℕ) (w : Fin n → Fin d), ZetaZeros.D.EllReg.dw (List.ofFn w) (fun z => B n w z * (a z * φ z)) y =
      a y * ZetaZeros.D.EllReg.dw (List.ofFn w) (fun z => B n w z * φ z) y +
        ev (sb (B n w) (lb (List.ofFn w) a)) φ y := by
    intro n w
    have e1 : (fun z => B n w z * (a z * φ z)) = fun z => a z * (B n w z * φ z) := by
      funext z; ring
    rw [e1, leib ha (List.ofFn w) _ ((hB n w).mul hφ)]
    simp only [ev_sb (hB n w) hφ y]
  simp only [ZetaZeros.D.EllReg.trOp, key, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro w _
  ring
private theorem continuous_formalAdjoint_lemma_4 {m : ℕ} {B : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ}
    (hB : ∀ n w, ContDiff ℝ ∞ (B n w)) {φ : ZetaZeros.D.EllReg.E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (ZetaZeros.D.EllReg.trOp m B φ) := by
  have e : ZetaZeros.D.EllReg.trOp m B φ = fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.dw (List.ofFn w) (fun y => B n w y * φ y) x := by
    funext x; rfl
  rw [e]
  refine continuous_finsetSum _ (fun n _ => continuous_finsetSum _ (fun w _ => ?_))
  exact continuous_const.mul (contDiff_dw ((hB n w).mul hφ) _).continuous
private theorem formalAdjoint_congr_at_lemma_5 {m : ℕ} {b b' : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ} {φ : ZetaZeros.D.EllReg.E d → ℂ}
    {y : ZetaZeros.D.EllReg.E d} (h : ∀ n w, b n w =ᶠ[𝓝 y] b' n w) : ZetaZeros.D.EllReg.trOp m b φ y = ZetaZeros.D.EllReg.trOp m b' φ y := by
  unfold ZetaZeros.D.EllReg.trOp
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro w _
  congr 1
  apply Filter.EventuallyEq.eq_of_nhds
  apply dw_congr
  filter_upwards [h n w] with z hz
  rw [hz]
end WF
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open WF
namespace ZetaZeros.D.EllReg
theorem _root_.solution : WeakFourier := by
  intro d ι _ P U u hE i χ χ' hχ hχc hχU hχ' hχ'c hχ'U hχχ'
  obtain ⟨hU, hcoef, -, hu, hweak⟩ := hE
  have hKcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  have hKc : IsCompact (tsupport χ) := hχc.isCompact
  have hz0 : ∀ z, z ∉ tsupport χ → χ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  have hone : ∀ z ∈ tsupport χ, χ' z = 1 := fun z hz => (hχχ' z hz).eq_of_nhds
  obtain ⟨a, ha_def⟩ : ∃ a : E d → ℂ, a = fun z => (χ z : ℂ) := ⟨_, rfl⟩
  have ha : ContDiff ℝ ∞ a := by rw [ha_def]; exact ZetaZeros.D.EllReg.WF.contDiff_ofReal' hχ
  have haK : ∀ z ∉ tsupport χ, a z = 0 := fun z hz => by rw [ha_def]; simp [hz0 z hz]
  obtain ⟨B, hB_def⟩ : ∃ B : (n : ℕ) → (Fin n → Fin d) → E d → ℂ,
      B = fun n w z => (χ' z : ℂ) * P.a i n w z := ⟨_, rfl⟩
  have hB : ∀ n w, ContDiff ℝ ∞ (B n w) := by
    intro n w; rw [hB_def]; exact ZetaZeros.D.EllReg.WF.smooth_cut hU (hcoef i n w) hχ' hχ'U
  have hBev : ∀ y ∈ tsupport χ, ∀ n w, P.a i n w =ᶠ[𝓝 y] B n w := by
    intro y hy n w
    filter_upwards [hχχ' y hy] with z hz
    rw [hB_def]; simp [hz]
  have hMadm : ∀ n ∈ Finset.range (P.ord i + 1), ∀ w : Fin n → Fin d,
      ZetaZeros.D.EllReg.WF.Good (P.ord i) (tsupport χ) (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) := by
    intro n hn w
    have h1 := ZetaZeros.D.EllReg.WF.sb_good (hB n w) _ (ZetaZeros.D.EllReg.WF.lb_good ha hKcl haK (List.ofFn w))
    rw [List.length_ofFn] at h1
    have hn' : n ≤ P.ord i := by have := Finset.mem_range.mp hn; omega
    exact (ZetaZeros.D.EllReg.WF.good_mono h1) hn'
  obtain ⟨c, hc_def⟩ : ∃ c : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, c = fun n' w' y =>
      -∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y := ⟨_, rfl⟩
  have hc : ∀ n' (w' : Fin n' → Fin d), ContDiff ℝ ∞ (c n' w') := by
    intro n' w'
    rw [hc_def]
    apply ContDiff.neg
    apply ContDiff.sum; intro n hn
    apply ContDiff.sum; intro w _
    exact contDiff_const.mul (ZetaZeros.D.EllReg.WF.cf_good (hMadm n hn w) n' w').1
  have hc0 : ∀ n' (w' : Fin n' → Fin d), ∀ y ∉ tsupport χ, c n' w' y = 0 := by
    intro n' w' y hy
    simp only [hc_def, neg_eq_zero]
    apply Finset.sum_eq_zero; intro n hn
    apply Finset.sum_eq_zero; intro w _
    rw [(ZetaZeros.D.EllReg.WF.cf_good (hMadm n hn w) n' w').2 y hy, mul_zero]
  refine ⟨c, fun n' w' => ⟨hc n' w', HasCompactSupport.intro hKc (hc0 n' w')⟩, fun ξ => ?_⟩
  have hφ := ZetaZeros.D.EllReg.WF.contDiff_eF ξ
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : E d → ℂ, ψ = fun z => a z * eF ξ z := ⟨_, rfl⟩
  have hψs : ContDiff ℝ ∞ ψ := by rw [hψ_def]; exact ha.mul hφ
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro hKc (fun z hz => by rw [hψ_def]; simp [haK z hz])
  have hψU : tsupport ψ ⊆ U := by
    refine subset_trans ?_ hχU
    refine closure_minimal ?_ hKcl
    intro z hz
    by_contra hzK
    exact (Function.mem_support.mp hz) (by rw [hψ_def]; simp [haK z hzK])
  have hint_r : ∫ x, u x * P.tr i ψ x = 0 := hweak i ψ hψs hψc hψU
  have hψB : ∀ y, P.tr i ψ y = trOp (P.ord i) B ψ y := by
    intro y
    show trOp (P.ord i) (P.a i) ψ y = _
    unfold trOp
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro w _
    have e : (fun z => P.a i n w z * ψ z) = fun z => B n w z * ψ z := by
      funext z
      by_cases hz : z ∈ tsupport χ
      · rw [hB_def]; simp [hone z hz]
      · rw [hψ_def]; simp [haK z hz]
    rw [e]
  have hL : ∀ y, cut χ u y * P.tr i (eF ξ) y =
      u y * (a y * trOp (P.ord i) B (eF ξ) y) := by
    intro y
    by_cases hy : y ∈ tsupport χ
    · have e : P.tr i (eF ξ) y = trOp (P.ord i) B (eF ξ) y := by
        show trOp (P.ord i) (P.a i) (eF ξ) y = _
        exact _root_.ZetaZeros.D.EllReg.WF.formalAdjoint_congr_at_lemma_5 (hBev y hy)
      rw [e, ha_def]
      simp only [cut]
      ring
    · have h0 : χ y = 0 := hz0 y hy
      rw [ha_def]
      simp [cut, h0]
  have hR : ∀ y, ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y =
      -∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        c n' w' y * dw (List.ofFn w') (eF ξ) y := by
    intro y
    have h1 : ∀ n ∈ Finset.range (P.ord i + 1), ∀ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y =
        ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
            dw (List.ofFn w') (eF ξ) y) := by
      intro n hn w
      rw [ZetaZeros.D.EllReg.WF.ev_eq_cf (eF ξ) y _ (fun p hp => (hMadm n hn w p hp).1), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n' _
      rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
          (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y
        = ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
            ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
              (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
                dw (List.ofFn w') (eF ξ) y) := by
          apply Finset.sum_congr rfl; intro n hn
          apply Finset.sum_congr rfl; intro w _
          exact h1 n hn w
      _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
              (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
                dw (List.ofFn w') (eF ξ) y) := ZetaZeros.D.EllReg.WF.swap4 _ _ _
      _ = -∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            c n' w' y * dw (List.ofFn w') (eF ξ) y := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro n' _
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro w' _
          rw [hc_def]
          simp only [Finset.sum_mul, neg_mul, neg_neg, mul_assoc]
  have hpt : ∀ y, u y * P.tr i ψ y = u y * (a y * trOp (P.ord i) B (eF ξ) y) -
      ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := by
    intro y
    rw [hψB y, hψ_def, _root_.ZetaZeros.D.EllReg.WF.formalAdjoint_mul_expand_lemma_3 hB ha hφ y, hR y, mul_add, mul_neg, sub_eq_add_neg,
      Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl; intro n' _
    rw [Finset.mul_sum]
  have hG : Integrable (fun y => u y * (a y * trOp (P.ord i) B (eF ξ) y)) :=
    ZetaZeros.D.EllReg.WF.intg hU hKc hχU hu
      (ha.continuous.mul (_root_.ZetaZeros.D.EllReg.WF.continuous_formalAdjoint_lemma_4 hB hφ)) (fun y hy => by simp [haK y hy])
  have hH : ∀ n' (w' : Fin n' → Fin d),
      Integrable (fun y => u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y)) :=
    fun n' w' => ZetaZeros.D.EllReg.WF.intg hU hKc hχU hu
      ((hc n' w').continuous.mul (ZetaZeros.D.EllReg.WF.contDiff_dw hφ _).continuous) (fun y hy => by simp [hc0 n' w' y hy])
  have hmain : ∫ y, u y * (a y * trOp (P.ord i) B (eF ξ) y) =
      ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := by
    have e := hint_r
    rw [show (fun x => u x * P.tr i ψ x) = fun y =>
        u y * (a y * trOp (P.ord i) B (eF ξ) y) -
          ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) from funext hpt] at e
    rw [integral_sub hG (integrable_finsetSum _ fun n' _ => integrable_finsetSum _ fun w' _ => hH n' w'),
      integral_finsetSum _ (fun n' _ => integrable_finsetSum _ fun w' _ => hH n' w')] at e
    have e2 : ∀ n' ∈ Finset.range (P.ord i), ∫ y, ∑ w' : Fin n' → Fin d,
        u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) =
        ∑ w' : Fin n' → Fin d, ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) :=
      fun n' _ => integral_finsetSum _ (fun w' _ => hH n' w')
    rw [Finset.sum_congr rfl e2] at e
    exact sub_eq_zero.mp e
  calc ∫ y, cut χ u y * P.tr i (eF ξ) y
      = ∫ y, u y * (a y * trOp (P.ord i) B (eF ξ) y) := by
        congr 1; funext y; exact hL y
    _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := hmain
    _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          ∫ y, cut χ' u y * c n' w' y * dw (List.ofFn w') (eF ξ) y := by
        apply Finset.sum_congr rfl; intro n' _
        apply Finset.sum_congr rfl; intro w' _
        congr 1; funext y
        by_cases hy : y ∈ tsupport χ
        · simp only [cut, hone y hy, Complex.ofReal_one]
          ring
        · rw [hc0 n' w' y hy]
          simp
end ZetaZeros.D.EllReg
