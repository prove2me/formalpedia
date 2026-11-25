-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.top_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:46:25.341238+00:00
-- url     : https://prove2.me/submissions/6a56957d-6be4-4544-b024-e8545f3786b0

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hypForm_h
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_abs_norm_neg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_isIntegralElt_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_isIntegralElt_c
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_kBasisIn_single
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_latDeg_single
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_norm_c
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_spanIdx_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_spanIdx_pair
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_sum_log_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution (hN : IntegralIndexStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (j p : Fin r) (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K))
    (hGj : Gj.FG) (hGp : Gp.FG) (hj : ∀ x ∈ Gj, IsAt j x) (hp : ∀ x ∈ Gp, IsAt p x)
    (hpair : ∀ x ∈ Gj, ∀ y ∈ Gp, IsIntegralElt (S.c (x j) * y p))
    (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hx0j : x0 j ≠ 0) (hy : y ∈ Gp) (hyp : y p ≠ 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (d : ℝ) (hd : 0 < d) (hδj : ∀ σ, δ σ j = d)
    (hδp : ∀ σ, δ σ p = d⁻¹) (h0 : latDeg (diagMet δ) Gj ![x0] = 0) :
    latDeg (diagMet δ) Gp ![y] ≤ 0 := by
  have hjp' : j ≠ p := fun h => by rw [h] at hjp; omega
  have hx0p : x0 p = 0 := hj x0 hx0 p (Ne.symm hjp')
  have hyj : y j = 0 := hp y hy j hjp'

  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ)
  have e0 := h0
  rw [latDeg_single δ Gj j x0 (hj x0 hx0)] at e0
  simp only [hδj] at e0
  rw [sum_log_single (x0 j) hx0j d hd] at e0
  rw [latDeg_single δ Gp p y (hp y hy)]
  simp only [hδp]
  rw [sum_log_single (y p) hyp d⁻¹ (inv_pos.2 hd), Real.log_inv]

  set A : ℝ := (spanIdx Gj ![x0] : ℝ)
  set B : ℝ := (spanIdx Gp ![y] : ℝ)
  set X : ℝ := |((Algebra.norm ℚ (x0 j) : ℚ) : ℝ)|
  set Y : ℝ := |((Algebra.norm ℚ (y p) : ℚ) : ℝ)|
  have hA : 1 ≤ A := by
    have := spanIdx_ne_zero Gj ![x0] hGj (kBasisIn_single j Gj hj x0 hx0 hx0j)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hB : 1 ≤ B := by
    have := spanIdx_ne_zero Gp ![y] hGp (kBasisIn_single p Gp hp y hy hyp)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hX : 0 < X := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hx0j
  have hY : 0 < Y := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hyp
  have key : A * B ≤ X * Y := by
    set T := Gj ⊔ Gp
    have hT : T.FG := hGj.sup hGp
    have hbT : IsKBasisIn T ![x0, y] := by
      refine ⟨fun i => ?_, ?_, ?_⟩
      · fin_cases i
        · exact Submodule.mem_sup_left hx0
        · exact Submodule.mem_sup_right hy
      · rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 := congr_fun hst j
        have h2 := congr_fun hst p
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx0p, hyj,
          mul_zero, add_zero, zero_add] at h1 h2
        exact ⟨(mul_eq_zero.1 h1).resolve_right hx0j, (mul_eq_zero.1 h2).resolve_right hyp⟩
      · intro z hz
        obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
        rw [Matrix.range_cons_cons_empty]
        have e1 : z1 = (z1 j / x0 j) • x0 := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = j
          · subst ha; field_simp
          · rw [hj z1 hz1 a ha, hj x0 hx0 a ha, mul_zero]
        have e2 : z2 = (z2 p / y p) • y := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = p
          · subst ha; field_simp
          · rw [hp z2 hz2 a ha, hp y hy a ha, mul_zero]
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hint : IsIntegralOn (hypForm S j p) T := by
      intro z hz w hw
      obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
      rw [hypForm_h]
      simp only [Pi.add_apply, hj z1 hz1 p (Ne.symm hjp'), hj w1 hw1 p (Ne.symm hjp'),
        hp z2 hz2 j hjp', hp w2 hw2 j hjp', add_zero, zero_add]
      refine isIntegralElt_add (hpair z1 hz1 w2 hw2) ?_
      have := isIntegralElt_c S (hpair w1 hw1 z2 hz2)
      rwa [map_mul, S.c_invol, mul_comm] at this
    have hgram : hGram (hypForm S j p) ![x0, y] =
        !![0, S.c (x0 j) * y p; S.c (y p) * x0 j, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [hGram, hypForm_h, hx0p, hyj]
    have hdet : (hGram (hypForm S j p) ![x0, y]).det = -((S.c (x0 j) * y p) * (S.c (y p) * x0 j)) := by
      rw [hgram, Matrix.det_fin_two_of]
      ring
    have hcx : S.c (x0 j) ≠ 0 := fun h => hx0j (S.c.injective (by rw [h, map_zero]))
    have hcy : S.c (y p) ≠ 0 := fun h => hyp (S.c.injective (by rw [h, map_zero]))
    have hdet0 : (hGram (hypForm S j p) ![x0, y]).det ≠ 0 := by
      rw [hdet, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero hcx hyp) (mul_ne_zero hcy hx0j)
    have hb := hN K r 2 (hypForm S j p) T ![x0, y] hT hbT hint hdet0
    rw [hdet, abs_norm_neg, map_mul, map_mul, map_mul, norm_c, norm_c] at hb
    push_cast at hb
    rw [spanIdx_pair j p hjp Gj Gp hj hp x0 y hx0 hy] at hb
    push_cast at hb
    have hb' : (A * B) ^ 2 ≤ (X * Y) ^ 2 :=
      le_of_le_of_eq hb (by simp only [X, Y]; rw [abs_mul, abs_mul, abs_mul]; ring)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hb'
  have hlog : Real.log A + Real.log B ≤ Real.log X + Real.log Y := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul hX.ne' hY.ne']
    exact Real.log_le_log (by positivity) key
  linarith
end ReciprocityTheory.MultiplicativeHeights.SemiPt
