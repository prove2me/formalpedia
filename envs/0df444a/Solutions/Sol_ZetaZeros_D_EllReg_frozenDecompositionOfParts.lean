-- Prove2me | solution 1 for ZetaZeros.D.EllReg.frozenDecompositionOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:31.720783+00:00
-- url     : https://prove2.me/submissions/332774b9-a4af-4d9d-9f4f-1c62c53f3210

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_dw_zero
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_dw_const_mul
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_trOp_add
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_continuous_trOp
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_eF
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_mul_of_tsupport
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_cut_cont
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_tsupport_cut
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_psi_props
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_prod_neg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
namespace ZetaZeros.D.EllReg
theorem _root_.solution : DecomposeOf := by
  intro hPF hDw hFP hPL hWF d ι _ P U u hyp x0 ψ0 r hψ hψc hψ1 hψs hr hball χ χ' hχ hχc hχs
    hχ' hχ'c hχ's hχχ' i
  obtain ⟨hUo, hA, -, hu, -⟩ := id hyp
  have hχU : tsupport χ ⊆ U := hχs.trans ((ball_subset_ball (by linarith)).trans hball)
  obtain ⟨c, hc, hcw⟩ := hWF d ι P U u hyp i χ χ' hχ hχc hχU hχ' hχ'c hχ's hχχ'
  obtain ⟨hψC, hψH, hψT, hψ1'⟩ := Dec.psi_props x0 ψ0 r hψ hψc hψ1 hψs hr
  obtain ⟨hgc, hgs⟩ := Dec.cut_cont hUo hu hχ hχc hχU
  obtain ⟨hg'c, hg's⟩ := Dec.cut_cont hUo hu hχ' hχ'c hχ's
  set m := P.ord i with hm
  have hψU := hψT.trans hball
  let lo : (n : ℕ) → (Fin n → Fin d) → E d → ℂ := fun n w x =>
    ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (P.a i n w x - if n = m then P.a i n w x0 else 0)
  let b2 : (n : ℕ) → (Fin n → Fin d) → E d → ℂ := fun n w _ => if n = m then P.a i n w x0 else 0
  have hlo : ∀ n w, ContDiff ℝ ∞ (lo n w) ∧ HasCompactSupport (lo n w) := fun n w =>
    ⟨Dec.contDiff_mul_of_tsupport hUo hψC hψU ((hA i n w).sub contDiffOn_const), hψH.mul_right⟩
  have hb2 : ∀ n w, ContDiff ℝ ∞ (b2 n w) := fun n w => contDiff_const
  refine ⟨lo, c, hlo, hc, fun ξ => ?_⟩
  have hφ := Dec.contDiff_eF ξ
  have hterm : ∀ n (w : Fin n → Fin d), ∫ y, cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y =
      (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) (𝓕 (cut χ' u)) ξ := by
    intro n w
    have hpf := hPF d 0 (fun _ _ => c n w) (cut χ' u) (fun _ _ => hc n w) hg'c hg's ξ
    have htr0 : ∀ y, trOp 0 (fun _ _ => c n w) (eF ξ) y = c n w y * eF ξ y := by
      intro y
      simp [trOp, dw]
    have hmono0 : ∀ (w' : Fin 0 → Fin d) (η : E d), mono w' η = 1 := by
      intro w' η
      simp [mono]
    simp only [htr0] at hpf
    have e1 : (fun y => cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y) =
        fun y => ((-1 : ℂ) ^ n * mono w ξ) * (cut χ' u y * (c n w y * eF ξ y)) := by
      funext y
      simp only [hDw d ξ (List.ofFn w), Dec.prod_neg_eq]
      ring
    rw [e1, integral_const_mul, hpf]
    simp [hmono0]
  have hR : ∫ y, cut χ u y * P.tr i (eF ξ) y = ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) (𝓕 (cut χ' u)) ξ := by
    rw [hcw ξ]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => hterm n w
  have hloc := hPL d m (P.a i) (fun n w y => lo n w y + b2 n w y) (cut χ u) (eF ξ) (ball x0 r)
    isOpen_ball ((Dec.tsupport_cut χ u).trans hχs) (by
      intro n w x hx
      have h1 := hψ1' x hx
      simp only [lo, b2, h1]
      split_ifs <;> ring)
  have hsplit : ∀ y, trOp m (fun n w y => lo n w y + b2 n w y) (eF ξ) y =
      trOp m lo (eF ξ) y + trOp m b2 (eF ξ) y :=
    fun y => Dec.trOp_add m lo b2 (eF ξ) (fun n w => (hlo n w).1) hb2 hφ y
  have hb2e : ∀ y, trOp m b2 (eF ξ) y =
      (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * eF ξ y := by
    intro y
    simp only [trOp]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Finset.sum_mul]
    · refine Finset.sum_congr rfl fun w _ => ?_
      simp only [b2, eq_self_iff_true, if_true]
      rw [Dec.dw_const_mul hφ, hDw d ξ (List.ofFn w), Dec.prod_neg_eq]
      beta_reduce
      have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by
        rw [← mul_pow]
        norm_num
      linear_combination (P.a i m w x0 * mono w ξ * eF ξ y) * hsq
    · intro n hn
      have hne : n ≠ m := (Finset.mem_range.mp hn).ne
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [b2, if_neg hne, zero_mul]
      rw [Dec.dw_zero]
      simp
  have hint1 : Integrable (fun y => cut χ u y * trOp m lo (eF ξ) y) :=
    (hgc.mul (Dec.continuous_trOp m lo (eF ξ) (fun n w => (hlo n w).1) hφ)).integrable_of_hasCompactSupport
      hgs.mul_right
  have hint2 : Integrable (fun y => cut χ u y * trOp m b2 (eF ξ) y) :=
    (hgc.mul (Dec.continuous_trOp m b2 (eF ξ) hb2 hφ)).integrable_of_hasCompactSupport hgs.mul_right
  have hconst : ∫ y, cut χ u y * trOp m b2 (eF ξ) y =
      (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * 𝓕 (cut χ u) ξ := by
    simp_rw [hb2e]
    rw [← hFP d (cut χ u) hgc hgs ξ, ← integral_const_mul]
    congr 1
    funext y
    ring
  have key : ∫ y, cut χ u y * P.tr i (eF ξ) y =
      (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * 𝓕 (cut χ u) ξ +
        ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          conv (𝓕 (lo n w)) (fun η => mono w η * 𝓕 (cut χ u) η) ξ := by
    calc ∫ y, cut χ u y * P.tr i (eF ξ) y
        = ∫ y, cut χ u y * trOp m (fun n w y => lo n w y + b2 n w y) (eF ξ) y := hloc
      _ = ∫ y, (cut χ u y * trOp m lo (eF ξ) y + cut χ u y * trOp m b2 (eF ξ) y) := by
          congr 1
          funext y
          rw [hsplit y, mul_add]
      _ = (∫ y, cut χ u y * trOp m lo (eF ξ) y) + ∫ y, cut χ u y * trOp m b2 (eF ξ) y :=
          integral_add hint1 hint2
      _ = _ := by
          rw [hPF d m lo (cut χ u) hlo hgc hgs ξ, hconst, add_comm]
  have hlom : ∀ w : Fin m → Fin d,
      lo m w = fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (P.a i m w x - P.a i m w x0) := by
    intro w
    funext x
    simp only [lo, eq_self_iff_true, if_true]
  rw [← hR, key, Finset.sum_range_succ]
  simp only [hlom]
  ring
end ZetaZeros.D.EllReg
