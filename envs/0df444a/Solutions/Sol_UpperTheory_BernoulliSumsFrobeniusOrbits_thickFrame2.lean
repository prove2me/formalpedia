-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:16.072969+00:00
-- url     : https://prove2.me/submissions/c05550b2-8c4b-46b8-83df-cb890ef3b1a1

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_ThickFrame2Large
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_hostThickExists
import Theorems.Thm_Formalism_HC_Frame_cyclic_order_le_exponent
import Theorems.Thm_Formalism_HC_Frame_exponent_eq_index_mul_cyclic_order
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_n0_pos
import Theorems.Thm_Formalism_HC_Frame_o_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
private theorem UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_card (c n : ℕ) (T : Finset ℕ) (h0 : 0 ∉ T)
    (h : ∀ a ∈ T, c * a < n) : c * T.card ≤ n := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  have hsub : T ⊆ Finset.Icc 1 (T.max' hne) := by
    intro a ha
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (fun e => h0 (e ▸ ha)), T.le_max' a ha⟩
  have hc : T.card ≤ T.max' hne := by simpa using Finset.card_le_card hsub
  exact (Nat.mul_le_mul_left c hc).trans (h _ (T.max'_mem hne)).le
private theorem UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_large (A B t : ℝ) (ht : 0 < t) :
    ∃ y0 : ℝ, ∀ y, y0 ≤ y → 2 ≤ y ∧ A + Real.log y ≤ t * y ∧ B ≤ t * y := by
  refine ⟨max 2 (max ((A - Real.log (t / 2)) / (t / 2)) (B / t)), fun y hy => ?_⟩
  have h2 : 2 ≤ y := (le_max_left _ _).trans hy
  have h3 : (A - Real.log (t / 2)) / (t / 2) ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have h4 : B / t ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  rw [div_le_iff₀ (by positivity)] at h3 h4
  have h5 := Real.log_le_sub_one_of_pos (show 0 < t / 2 * y by positivity)
  rw [Real.log_mul (by positivity) (by positivity)] at h5
  exact ⟨h2, by linarith, by linarith⟩
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∃ CT : ℝ, 0 < CT ∧ ∀ eps Co CL : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (φ : Formalism.HC.Frame) (Lw : ℕ), 2 ≤ Lw →
      (Lw : ℝ) ≤ CL * Real.log x → (φ.o : ℝ) ≤ Co → x ^ hE eps / 2 ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ Co * x ^ hE eps →
      ∃ T2 : Finset ℕ, (∀ s ∈ T2, 4 * Lw * s < φ.n0) ∧ Formalism.FrobeniusOrbits.NoRel T2 Lw ∧
        (φ.n0 : ℝ) * Real.exp (-(CT * Real.sqrt (Real.log (φ.n0 : ℝ) * Real.log Lw))) / Lw ≤ T2.card ∧
        x ^ (-eps) * φ.ord ≤ (T2.card : ℝ) ∧ 4 * Lw * T2.card ≤ φ.n0 := by
  have amgm : ∀ p q : ℝ, p * q ≤ ((p + q) / 2) ^ 2 := fun p q => by
    nlinarith [sq_nonneg (p - q)]
  obtain ⟨C, hC, hT⟩ := Formalism.FrobeniusOrbits.hostThickExists
  refine ⟨2 * C, by positivity, ?_⟩
  intro eps Co CL he he'
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + 3 * C ^ 2 / (2 * eps) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = eps / (2 * K) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [htd]; positivity
  obtain ⟨y0, hy0⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_large
    ((Real.log (4 * Co) + eps / 6 * Real.log Co + K * Real.log CL) / K)
    (t * (Real.log (2 * Co) + Real.log 2 / C ^ 2) / 2) t htpos
  refine ⟨Real.exp y0, fun x hx φ Lw hLw hLwx hoC hord1 hord2 => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  obtain ⟨h2y, hA, hB⟩ := hy0 (Real.log x) (by
    calc y0 = Real.log (Real.exp y0) := (Real.log_exp y0).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hx)
  have hypos : 0 < Real.log x := by linarith
  have hx2 : 2 ≤ x := by
    have h1 : Real.exp 2 ≤ x := by
      calc Real.exp 2 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h2y
        _ = x := Real.exp_log hxpos
    have h2 : (2:ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    linarith
  have hx1 : 1 ≤ x := by linarith
  have hn0pos : (0:ℝ) < φ.n0 := by exact_mod_cast φ.n0_pos
  have hn01 : (1:ℝ) ≤ φ.n0 := by exact_mod_cast φ.n0_pos
  have hopos : (0:ℝ) < φ.o := by exact_mod_cast φ.o_pos
  have hordeq : (φ.ord : ℝ) = (φ.o : ℝ) * φ.n0 := by exact_mod_cast φ.exponent_eq_index_mul_cyclic_order
  have hn0ord : (φ.n0 : ℝ) ≤ φ.ord := by exact_mod_cast φ.cyclic_order_le_exponent
  have hCo : 0 < Co := lt_of_lt_of_le hopos hoC
  have hordCo : (φ.ord : ℝ) ≤ Co * φ.n0 := by
    rw [hordeq]; exact mul_le_mul_of_nonneg_right hoC hn0pos.le
  have hxE : 0 < x ^ hE eps := Real.rpow_pos_of_pos hxpos _
  have hEval : hE eps = 2 + 8 * eps := rfl
  have hLw2 : (2:ℝ) ≤ Lw := by exact_mod_cast hLw
  have hLwpos : (0:ℝ) < Lw := by linarith
  have hCL : 0 < CL := by
    by_contra hneg
    push_neg at hneg
    have := mul_le_mul_of_nonneg_right hneg hypos.le
    linarith
  have hb : Real.log Lw ≤ Real.log CL + Real.log (Real.log x) := by
    rw [← Real.log_mul hCL.ne' hypos.ne']
    exact Real.log_le_log hLwpos hLwx
  have hb0 : Real.log 2 ≤ Real.log Lw := Real.log_le_log (by norm_num) hLw2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ Real.log φ.n0 := Real.log_nonneg hn01
  have hepsx : eps * Real.log x ≤ 1 / 52 * Real.log x := mul_le_mul_of_nonneg_right he'.le hypos.le
  have hepsx0 : 0 ≤ eps * Real.log x := mul_nonneg he.le hypos.le
  have ha : Real.log φ.n0 ≤ Real.log Co + 3 * Real.log x := by
    have h1 : Real.log φ.n0 ≤ Real.log (Co * x ^ hE eps) :=
      Real.log_le_log hn0pos (le_trans hn0ord hord2)
    rw [Real.log_mul hCo.ne' hxE.ne', Real.log_rpow hxpos, hEval] at h1
    linarith
  have hlow : (Real.log (2 * Co) + Real.log 2 / C ^ 2) / 2 ≤ Real.log x := by
    have : t * ((Real.log (2 * Co) + Real.log 2 / C ^ 2) / 2) ≤ t * Real.log x := by
      linarith
    exact le_of_mul_le_mul_left this htpos
  have ha_low : Real.log 2 / C ^ 2 ≤ Real.log φ.n0 := by
    have h1 : x ^ hE eps / (2 * Co) ≤ φ.n0 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div hxE.ne' (by positivity), Real.log_rpow hxpos, hEval] at h2
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.sqrt (Real.log φ.n0 * Real.log Lw) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = eps / (3 * C) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hu_up : u ≤ (δ * Real.log φ.n0 + Real.log Lw / δ) / 2 := by
    have key : Real.log φ.n0 * Real.log Lw
        = (δ * Real.log φ.n0) * (Real.log Lw / δ) := by
      field_simp
    have hsq : Real.log φ.n0 * Real.log Lw ≤ ((δ * Real.log φ.n0 + Real.log Lw / δ) / 2) ^ 2 := by
      rw [key]; exact amgm _ _
    have h3 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity)] at h3
    rw [hu]; exact h3
  have hu_low : Real.log 2 / C ≤ u := by
    have hsq : (Real.log 2 / C) ^ 2 ≤ Real.log φ.n0 * Real.log Lw := by
      have e : (Real.log 2 / C) ^ 2 = (Real.log 2 / C ^ 2) * Real.log 2 := by
        field_simp
      rw [e]
      exact mul_le_mul ha_low hb0 hlog2.le ha0
    have h3 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity)] at h3
    rw [hu]; exact h3
  have hCu_eq : C * ((δ * Real.log φ.n0 + Real.log Lw / δ) / 2)
      = eps / 6 * Real.log φ.n0 + (K - 1) * Real.log Lw := by
    rw [hδ, hK]; field_simp; ring
  have hCu : C * u ≤ eps / 6 * Real.log φ.n0 + (K - 1) * Real.log Lw := by
    rw [← hCu_eq]; exact mul_le_mul_of_nonneg_left hu_up hC.le
  have hKt : K * t = eps / 2 := by rw [htd]; field_simp
  have hKt' : K * (t * Real.log x) = eps / 2 * Real.log x := by rw [← mul_assoc, hKt]
  have hKA : K * ((Real.log (4 * Co) + eps / 6 * Real.log Co + K * Real.log CL) / K)
      = Real.log (4 * Co) + eps / 6 * Real.log Co + K * Real.log CL := by
    field_simp
  have hA' := mul_le_mul_of_nonneg_left hA hKpos.le
  have hKb := mul_le_mul_of_nonneg_left hb hKpos.le
  have hea := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ eps / 6)
  have hgoal : Real.log (4 * Co) + Real.log Lw + C * u ≤ eps * Real.log x := by
    rw [mul_add] at hA' hKb hea
    linarith
  obtain ⟨E, hE'⟩ : ∃ E : ℝ, E = Real.exp (C * u) := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE']; exact Real.exp_pos _
  have hexp : 4 * Co * Lw * E ≤ x ^ eps := by
    rw [Real.rpow_def_of_pos hxpos]
    have e : 4 * Co * Lw * E = Real.exp (Real.log (4 * Co) + Real.log Lw + C * u) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_log hLwpos, hE']
    rw [e]
    apply Real.exp_le_exp.mpr
    linarith [mul_comm eps (Real.log x)]
  have hE2 : 2 ≤ E := by
    have h1 : Real.log 2 ≤ C * u := by
      have h3 := mul_le_mul_of_nonneg_left hu_low hC.le
      rw [mul_div_cancel₀ _ hC.ne'] at h3
      exact h3
    rw [hE']
    calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (C * u) := Real.exp_le_exp.mpr h1
  have hP : 0 < x ^ eps := Real.rpow_pos_of_pos hxpos _
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = φ.n0 * E⁻¹ / Lw := ⟨_, rfl⟩
  have hX : x ^ (-eps) * φ.ord ≤ Q / 4 := by
    rw [Real.rpow_neg hxpos.le, hQ]
    rw [show (x ^ eps)⁻¹ * (φ.ord : ℝ) = φ.ord / x ^ eps by ring,
      show (φ.n0 : ℝ) * E⁻¹ / Lw / 4 = φ.n0 / (4 * Lw * E) by field_simp]
    rw [div_le_div_iff₀ hP (by positivity)]
    calc (φ.ord : ℝ) * (4 * Lw * E) ≤ (Co * φ.n0) * (4 * Lw * E) := by gcongr
      _ = φ.n0 * (4 * Co * Lw * E) := by ring
      _ ≤ φ.n0 * x ^ eps := by gcongr
  have hX1 : 1 ≤ x ^ (-eps) * φ.ord := by
    have h1 : x ^ (1:ℝ) ≤ x ^ (-eps + hE eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hEval]; linarith)
    rw [Real.rpow_add hxpos, Real.rpow_one] at h1
    have h2 := mul_le_mul_of_nonneg_left hord1 (Real.rpow_pos_of_pos hxpos (-eps)).le
    linarith
  obtain ⟨T, hTs, hTnr, hTc⟩ := hT φ.n0 Lw hLw
  rw [← hu] at hTc
  have hTc' : Q ≤ T.card := by
    rw [hQ, hE', ← Real.exp_neg, ← neg_mul]
    exact hTc
  have hcardN : T.card ≤ (T.erase 0).card + 1 := by
    have := Finset.pred_card_le_card_erase (s := T) (a := 0)
    omega
  have hcard : (T.card : ℝ) ≤ (T.erase 0).card + 1 := by exact_mod_cast hcardN
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨T.erase 0, fun s hs => hTs s (Finset.mem_of_mem_erase hs), ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FrobeniusOrbits.NoRel at hTnr ⊢
    intro s1 h1 s2 h2 s3 h3
    exact hTnr s1 (Finset.mem_of_mem_erase h1) s2 (Finset.mem_of_mem_erase h2) s3
      (Finset.mem_of_mem_erase h3)
  · have e : (φ.n0 : ℝ) * Real.exp (-(2 * C * Real.sqrt (Real.log φ.n0 * Real.log Lw))) / Lw
        = Q * E⁻¹ := by
      rw [hQ, hE', ← hu, ← Real.exp_neg, show -(2 * C * u) = -(C * u) + -(C * u) by ring,
        Real.exp_add]
      ring
    rw [e]
    have hEinv : E⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hE2
    have h3 := mul_le_mul_of_nonneg_left hEinv hQ0
    linarith
  · linarith
  · exact UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_card (4 * Lw) φ.n0 (T.erase 0) (Finset.notMem_erase 0 T)
      (fun s hs => hTs s (Finset.mem_of_mem_erase hs))
end UpperTheory.BernoulliSumsFrobeniusOrbits
