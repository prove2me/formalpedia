-- Prove2me | solution 1 for SysRiskPortfolio.CoER.landsman_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:01:10.475248+00:00
-- url     : https://prove2.me/submissions/9f2be83b-cf70-4f01-8c22-4d1e3ea7f01b

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_Optimizer

open Matrix SysRiskPortfolio.CoER

namespace LandsmanAux

/-- The embedding `u ↦ (u, -∑ u)` of `ℝ^m` onto the hyperplane `∑ x = 0`. -/
def E {m : ℕ} (u : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.snoc u (-(∑ i, u i))

lemma sum_E {m : ℕ} (u : Fin m → ℝ) : ∑ i, E u i = 0 := by
  simp [E, Fin.sum_univ_castSucc]

lemma E_dot {m : ℕ} (u : Fin m → ℝ) (x : Fin (m + 1) → ℝ) :
    E u ⬝ᵥ x = ∑ i, u i * (x i.castSucc - x (Fin.last m)) := by
  simp [E, dotProduct, Fin.sum_univ_castSucc, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  ring

lemma E_of_sum_zero {m : ℕ} (x : Fin (m + 1) → ℝ) (hx : ∑ i, x i = 0) :
    x = E (fun i => x i.castSucc) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [E, Fin.snoc_last]; rw [Fin.sum_univ_castSucc] at hx; linarith
  · simp [E]

lemma mulVec_E {m : ℕ} (S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (v : Fin m → ℝ)
    (k : Fin (m + 1)) :
    (S *ᵥ E v) k = ∑ j, v j * (S k j.castSucc - S k (Fin.last m)) := by
  rw [mulVec, dotProduct_comm, E_dot]

lemma symm_form {n : Type} [Fintype n] (S : Matrix n n ℝ) (hT : Sᵀ = S) (x y : n → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

lemma E_form {m : ℕ} (d : OptimData m) (u v : Fin m → ℝ) :
    E u ⬝ᵥ (d.SigHat *ᵥ E v) = u ⬝ᵥ (Qm d *ᵥ v) := by
  rw [E_dot, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [mulVec_E, mulVec_E, ← Finset.sum_sub_distrib, mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Qm]; ring

end LandsmanAux

open LandsmanAux

theorem solution {m : ℕ} (hm : 1 ≤ m) (d : OptimData m) (hS : d.SigHat.PosDef) (hlam : Real.sqrt (Del d ⬝ᵥ ((Qm d)⁻¹ *ᵥ Del d)) < d.lam) : (∑ i, wStar d i) = 1 ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → objective d w ≤ objective d (wStar d)) ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → objective d w = objective d (wStar d) → w = wStar d) := by
  set S := d.SigHat with hSdef
  set Q := Qm d with hQdef
  set Δ := Del d with hΔdef
  have hST : Sᵀ = S := by
    have := hS.isHermitian; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hQT : Qᵀ = Q := by
    ext i j
    have h1 : ∀ a b, d.SigHat b a = d.SigHat a b := fun a b => by
      simpa using congrFun (congrFun hST a) b
    simp only [transpose_apply, hQdef, Qm]
    rw [h1 i.castSucc j.castSucc, h1 (Fin.last m) j.castSucc, h1 i.castSucc (Fin.last m)]
    ring
  have hSpos : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (S *ᵥ x) := fun x hx => by
    simpa using hS.dotProduct_mulVec_pos hx
  have hSnn : ∀ x, 0 ≤ x ⬝ᵥ (S *ᵥ x) := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hSpos x hx).le
  have hEinj : ∀ u : Fin m → ℝ, E u = 0 → u = 0 := by
    intro u hu; funext i
    have := congrFun hu i.castSucc
    simpa [E] using this
  have hQ : Q.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hQT]
    · intro u hu
      rw [star_trivial, hQdef, ← E_form]
      exact hSpos _ (fun h => hu (hEinj u h))
  have hSu : IsUnit S.det := (isUnit_iff_isUnit_det S).mp hS.isUnit
  have hQu : IsUnit Q.det := (isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hSiT : S⁻¹ᵀ = S⁻¹ := by rw [transpose_nonsing_inv, hST]
  have hQiT : Q⁻¹ᵀ = Q⁻¹ := by rw [transpose_nonsing_inv, hQT]
  have hSSi : ∀ x, S *ᵥ (S⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hSu, one_mulVec]
  have hQQi : ∀ x, Q *ᵥ (Q⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
  -- notation
  set a := S⁻¹ *ᵥ ones (m + 1) with ha
  set h := ones (m + 1) ⬝ᵥ a with hh
  set z := Q⁻¹ *ᵥ Δ with hz
  set g := Δ ⬝ᵥ z with hg
  set v := E z with hv
  have hones : ∀ x : Fin (m + 1) → ℝ, ones (m + 1) ⬝ᵥ x = ∑ i, x i := fun x => by
    simp [ones, dotProduct]
  have hBa : ∀ y, y ⬝ᵥ (S *ᵥ a) = ∑ i, y i := fun y => by
    rw [ha, hSSi, dotProduct_comm, hones]
  have hBa' : ∀ y, a ⬝ᵥ (S *ᵥ y) = ∑ i, y i := fun y => by
    rw [symm_form S hST, hBa]
  have ha0 : a ≠ 0 := by
    intro h0
    have := hSSi (ones (m + 1))
    rw [← ha, h0, mulVec_zero] at this
    have := congrFun this 0
    simp [ones] at this
  have hhpos : 0 < h := by
    have := hSpos a ha0
    rw [hBa', ← hones] at this
    rw [hh, dotProduct_comm] at *
    simpa [hones] using this
  have hgnn : 0 ≤ g := by
    have := hSnn v
    rw [hv, E_form, ← hQdef, hz, hQQi, dotProduct_comm] at this
    exact this
  have hlampos : 0 < d.lam := lt_of_le_of_lt (Real.sqrt_nonneg _) hlam
  have hlam2 : g < d.lam ^ 2 := by
    have h1 : Real.sqrt g < d.lam := by rw [hg, hz]; exact hlam
    have h2 := Real.sq_sqrt hgnn
    nlinarith [Real.sqrt_nonneg g]
  set t := 1 / Real.sqrt ((d.lam ^ 2 - g) * h) with ht
  have hprod : 0 < (d.lam ^ 2 - g) * h := mul_pos (by linarith) hhpos
  have htpos : 0 < t := by rw [ht]; exact one_div_pos.mpr (Real.sqrt_pos.mpr hprod)
  have ht2 : t ^ 2 * ((d.lam ^ 2 - g) * h) = 1 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hprod.le]; exact one_div_mul_cancel hprod.ne'
  have hws : wStar d = (1 / h) • a - t • v := by
    have e1 : Fin.snoc ((Qm d)⁻¹ᵀ *ᵥ Del d) (-(ones m ⬝ᵥ ((Qm d)⁻¹ *ᵥ Del d))) = v := by
      rw [← hQdef, ← hΔdef, hQiT, ← hz, hv, E]
      congr 2
      simp [ones, dotProduct]
    unfold wStar
    simp only []
    rw [e1]
  clear_value t
  set ws := (1 / h) • a - t • v with hwsdef
  have hBvv : v ⬝ᵥ (S *ᵥ v) = g := by
    rw [hv, E_form, ← hQdef, hz, hQQi, dotProduct_comm]
  have hBav : a ⬝ᵥ (S *ᵥ v) = 0 := by rw [hBa', hv, sum_E]
  have hBva : v ⬝ᵥ (S *ᵥ a) = 0 := by rw [hBa, hv, sum_E]
  have hBaa : a ⬝ᵥ (S *ᵥ a) = h := by rw [hBa', hh, hones]
  have hsumv : ∑ i, v i = 0 := by rw [hv, sum_E]
  have hsuma : ∑ i, a i = h := by rw [hh, hones]
  have hsum_ws : ∑ i, ws i = 1 := by
    simp only [hwsdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsumv, hsuma]
    field_simp; ring
  have hNN : ws ⬝ᵥ (S *ᵥ ws) = (d.lam * t) ^ 2 := by
    simp only [hwsdef, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hBvv, hBav, hBva, hBaa]
    have e2 : 1 / h * (1 / h * h) = t ^ 2 * (d.lam ^ 2 - g) := by
      field_simp; linear_combination (-1 : ℝ) * ht2
    linear_combination e2
  have hq : Real.sqrt (ws ⬝ᵥ (S *ᵥ ws)) = d.lam * t := by
    rw [hNN, Real.sqrt_sq (by positivity)]
  set q := d.lam * t with hqdef
  have hqpos : 0 < q := by positivity
  -- analysis of a competitor
  have main : ∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 →
      objective d w ≤ objective d ws ∧ (objective d w = objective d ws → w = ws) := by
    intro w hw
    set x := w - ws with hxdef
    have hsx : ∑ i, x i = 0 := by
      simp [hxdef, Finset.sum_sub_distrib, hw, hsum_ws]
    set u : Fin m → ℝ := fun i => x i.castSucc with hu
    have hxE : x = E u := E_of_sum_zero x hsx
    have hwx : w = ws + x := by rw [hxdef]; abel
    have hBxws : x ⬝ᵥ (S *ᵥ ws) = -t * (u ⬝ᵥ Δ) := by
      simp only [hwsdef, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [hBa, hsx, hxE, hv, E_form, ← hQdef, hz, hQQi]
      ring
    have hxmu : x ⬝ᵥ d.muHat = -(u ⬝ᵥ Δ) := by
      rw [hxE, E_dot, hΔdef, dotProduct, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Del]; ring
    have hsymm : ws ⬝ᵥ (S *ᵥ w) = w ⬝ᵥ (S *ᵥ ws) := symm_form S hST _ _
    have hBw : w ⬝ᵥ (S *ᵥ ws) = q ^ 2 - t * (u ⬝ᵥ Δ) := by
      rw [hwx, add_dotProduct, hNN, hBxws]; ring
    have hwmu : w ⬝ᵥ d.muHat = ws ⬝ᵥ d.muHat - u ⬝ᵥ Δ := by
      rw [hwx, add_dotProduct, hxmu]; ring
    set p := Real.sqrt (w ⬝ᵥ (S *ᵥ w)) with hpdef
    have hp2 : p ^ 2 = w ⬝ᵥ (S *ᵥ w) := Real.sq_sqrt (hSnn w)
    have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
    have hppos : 0 < p := Real.sqrt_pos.mpr (hSpos w hw0)
    have hexp : (q • w - p • ws) ⬝ᵥ (S *ᵥ (q • w - p • ws))
        = 2 * p * q * (p * q - w ⬝ᵥ (S *ᵥ ws)) := by
      simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, hsymm, ← hp2, hNN]
      ring
    have hCS : w ⬝ᵥ (S *ᵥ ws) ≤ p * q := by
      have h0 := hSnn (q • w - p • ws)
      rw [hexp] at h0
      have : 0 ≤ p * q - w ⬝ᵥ (S *ᵥ ws) := by
        by_contra hc
        push Not at hc
        have : 2 * p * q * (p * q - w ⬝ᵥ (S *ᵥ ws)) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) hc
        linarith
      linarith
    have hobjw : objective d w = ws ⬝ᵥ d.muHat - u ⬝ᵥ Δ - d.lam * p := by
      rw [objective, hwmu]
    have hobjws : objective d ws = ws ⬝ᵥ d.muHat - d.lam * q := by
      rw [objective, hq]
    -- t * (u ⬝ Δ) = q^2 - B(w,ws) ≥ q^2 - p q = t * (lam * (q - p))
    have hkey : t * (u ⬝ᵥ Δ) - t * (d.lam * (q - p)) = p * q - w ⬝ᵥ (S *ᵥ ws) := by
      rw [hBw, hqdef]; ring
    refine ⟨?_, fun he => ?_⟩
    · rw [hobjw, hobjws]
      have : 0 ≤ t * (u ⬝ᵥ Δ - d.lam * (q - p)) := by rw [mul_sub]; linarith
      have := nonneg_of_mul_nonneg_right (by linarith [this] : 0 ≤ t * (u ⬝ᵥ Δ - d.lam * (q - p))) htpos
      nlinarith
    · rw [hobjw, hobjws] at he
      have h1 : u ⬝ᵥ Δ - d.lam * (q - p) = 0 := by linarith
      have h2 : p * q - w ⬝ᵥ (S *ᵥ ws) = 0 := by rw [← hkey, ← mul_sub, h1, mul_zero]
      have h3 : (q • w - p • ws) ⬝ᵥ (S *ᵥ (q • w - p • ws)) = 0 := by rw [hexp, h2, mul_zero]
      have h4 : q • w - p • ws = 0 := by
        by_contra hne
        have := hSpos _ hne
        linarith
      have h5 : q - p = 0 := by
        have := congrArg (fun y => ∑ i, y i) h4
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
          ← Finset.mul_sum, hw, hsum_ws, Pi.zero_apply, Finset.sum_const_zero] at this
        linarith
      have hpq : p = q := by linarith
      rw [hpq, ← smul_sub] at h4
      have := (smul_eq_zero.mp h4).resolve_left hqpos.ne'
      exact sub_eq_zero.mp this
  rw [hws]
  refine ⟨hsum_ws, fun w hw => (main w hw).1, fun w hw he => (main w hw).2 he⟩
