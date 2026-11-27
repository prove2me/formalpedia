-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:50:57.852334+00:00
-- url     : https://prove2.me/submissions/38a8be97-3c2e-45ad-93c8-3e33d82eb36c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_choose_exp
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (D N n n' deF u del : ℕ) (h1 : 1 ≤ deF) (hdel : deF ≤ del)
    (hu : u ≤ (D + 1) * del) (hn : 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) * del ≤ n)
    (hn' : n' = 8 * n * ((D + 2) * (N + 1)) * (D + 1) * del) :
    (n : ℝ) * cardUX D N n n' ≤ ((n : ℝ) + (D + 2) * deF) * cardUX D N (n - deF) (n' - u) := by
  have hdel1 : 1 ≤ del := le_trans h1 hdel
  have hM1 : D + 2 ≤ (D + 2) * (N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos N)
  have hbig : del ≤ n := by
    have : 1 ≤ 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) := Nat.succ_le_of_lt (by positivity)
    calc del = 1 * del := (one_mul _).symm
      _ ≤ 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) * del := Nat.mul_le_mul_right _ this
      _ ≤ n := hn
  have haN : deF ≤ n := le_trans hdel hbig
  have huN : u ≤ n' := by
    have hn1 : 1 ≤ n := le_trans hdel1 hbig
    have : 1 ≤ 8 * n * ((D + 2) * (N + 1)) :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by positivity))
    rw [hn']
    calc u ≤ (D + 1) * del := hu
      _ = 1 * ((D + 1) * del) := (one_mul _).symm
      _ ≤ 8 * n * ((D + 2) * (N + 1)) * ((D + 1) * del) := Nat.mul_le_mul_right _ this
      _ = 8 * n * ((D + 2) * (N + 1)) * (D + 1) * del := by ring
  have hA := hups_choose_exp n (n - deF) (D + 1) (Nat.sub_le n deF)
  have hB := hups_choose_exp n' (n' - u) ((D + 2) * (N + 1)) (Nat.sub_le n' u)
  rw [Nat.sub_sub_self haN] at hA
  rw [Nat.sub_sub_self huN] at hB
  have hc1 : (cardUX D N n n' : ℝ) = (((n + (D + 1)).choose (D + 1) : ℕ) : ℝ) *
      (((n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) := by
    simp only [cardUX, Nat.cast_mul]
    rw [show n + D + 1 = n + (D + 1) by omega]
  have hc2 : (cardUX D N (n - deF) (n' - u) : ℝ) = (((n - deF + (D + 1)).choose (D + 1) : ℕ) : ℝ) *
      (((n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) := by
    simp only [cardUX, Nat.cast_mul]
    rw [show n - deF + D + 1 = n - deF + (D + 1) by omega]
  set K : ℝ := ((D + 1 : ℕ) : ℝ) with hK
  set Mr : ℝ := (((D + 2) * (N + 1) : ℕ) : ℝ) with hMr
  set a : ℝ := (deF : ℝ) with ha
  set nr : ℝ := (n : ℝ) with hnr
  set dl : ℝ := (del : ℝ) with hdl
  set ur : ℝ := (u : ℝ) with hur
  set n'r : ℝ := (n' : ℝ) with hn'r
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast Nat.le_add_left 1 D
  have hMK : K + 1 ≤ Mr := by
    rw [hK, hMr]; exact_mod_cast (show D + 1 + 1 ≤ (D + 2) * (N + 1) by omega)
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast h1
  have had : a ≤ dl := by rw [ha, hdl]; exact_mod_cast hdel
  have hud : ur ≤ K * dl := by rw [hur, hK, hdl]; exact_mod_cast hu
  have hnbig : 8 * Mr ^ 2 * K * dl ≤ nr := by
    rw [hnr, hMr, hK, hdl]; exact_mod_cast hn
  have hn'eq : n'r = 8 * nr * Mr * K * dl := by
    rw [hn'r, hnr, hMr, hK, hdl, hn']; push_cast; ring
  have hsub1 : (((n - deF : ℕ) : ℝ)) = nr - a := by rw [Nat.cast_sub haN]
  have hsub2 : (((n' - u : ℕ) : ℝ)) = n'r - ur := by rw [Nat.cast_sub huN]
  rw [hsub1] at hA
  rw [hsub2] at hB
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hdl1 : 1 ≤ dl := by linarith
  have hMr1 : 1 ≤ Mr := by linarith
  have hur0 : 0 ≤ ur := by rw [hur]; exact Nat.cast_nonneg u
  have hnr_ge : 8 * (K + 1) ^ 2 * K * a ≤ nr := by
    have hsq : (K + 1) ^ 2 ≤ Mr ^ 2 := pow_le_pow_left₀ (by linarith) hMK 2
    have h8 : 8 * (K + 1) ^ 2 * K * a ≤ 8 * Mr ^ 2 * K * dl := by
      calc 8 * (K + 1) ^ 2 * K * a ≤ 8 * Mr ^ 2 * K * a := by gcongr
        _ ≤ 8 * Mr ^ 2 * K * dl := by gcongr
    linarith
  have hKa_le : (K + 1) * a ≤ nr := by
    have h8 : 1 ≤ 8 * (K + 1) * K := by nlinarith
    have : (K + 1) * a ≤ 8 * (K + 1) ^ 2 * K * a := by
      calc (K + 1) * a = 1 * ((K + 1) * a) := (one_mul _).symm
        _ ≤ (8 * (K + 1) * K) * ((K + 1) * a) :=
            mul_le_mul_of_nonneg_right h8 (mul_nonneg (by linarith) ha0)
        _ = 8 * (K + 1) ^ 2 * K * a := by ring
    linarith
  have hnr1 : 1 ≤ nr := by nlinarith
  set y1 : ℝ := K * (a / (nr - a + 1)) with hy1
  set y2 : ℝ := Mr * (ur / (n'r - ur + 1)) with hy2
  set S : ℝ := nr + (K + 1) * a with hS
  have hKa_pos : 0 < (K + 1) * a := mul_pos (by linarith) (by linarith)
  have hSpos : 0 < S := by rw [hS]; linarith
  have hd1 : 0 < nr - a + 1 := by nlinarith
  have hnrMr : 1 ≤ nr * Mr := by nlinarith
  have hKdl0 : 0 ≤ K * dl := mul_nonneg hK0 (by linarith)
  have hq : K * dl ≤ nr * Mr * K * dl := by
    calc K * dl = 1 * (K * dl) := (one_mul _).symm
      _ ≤ (nr * Mr) * (K * dl) := mul_le_mul_of_nonneg_right hnrMr hKdl0
      _ = nr * Mr * K * dl := by ring
  have hd2 : 0 < n'r - ur + 1 := by rw [hn'eq]; nlinarith
  have hpoly : K * (K + 2) + 3 / 16 ≤ 3 / 2 * (K + 1) ^ 2 * K := by
    nlinarith [mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hK1),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hK1)) (sub_nonneg.2 hK1)]
  have e1 : K * (K + 2) * a + 3 * a / 16 ≤ 3 * nr / 16 := by
    have := mul_le_mul_of_nonneg_right hpoly ha0
    nlinarith
  have hy1S : y1 * S ≤ K * a + 3 * a / 16 := by
    have : y1 * S = K * a * S / (nr - a + 1) := by
      rw [hy1, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [this, div_le_iff₀ hd1, hS]
    have h2 := mul_le_mul_of_nonneg_left e1 ha0
    nlinarith
  have hy2S : y2 * S ≤ 1 / 2 := by
    have : y2 * S = Mr * ur * S / (n'r - ur + 1) := by
      rw [hy2, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [this, div_le_iff₀ hd2, hn'eq]
    have hS2 : S ≤ 2 * nr := by rw [hS]; linarith
    have p1 : Mr * ur * S ≤ Mr * (K * dl) * (2 * nr) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hud (by linarith)) hS2 hSpos.le
        (mul_nonneg (by linarith) hKdl0)
    have e2 : Mr * (K * dl) * (2 * nr) = 2 * (nr * Mr * K * dl) := by ring
    have e3 : 8 * nr * Mr * K * dl = 8 * (nr * Mr * K * dl) := by ring
    rw [e2] at p1
    rw [e3]
    linarith
  have hyS : (y1 + y2) * S ≤ (K + 1) * a := by
    have e4 : (K + 1) * a = K * a + a := by ring
    rw [add_mul, e4]; linarith
  have hny : nr ≤ S * (1 - (y1 + y2)) := by
    have : S * (1 - (y1 + y2)) = S - (y1 + y2) * S := by ring
    rw [this]; linarith
  have hexp : Real.exp (y1 + y2) * (1 - (y1 + y2)) ≤ 1 := by
    have h0 := Real.add_one_le_exp (-(y1 + y2))
    have h2 : Real.exp (y1 + y2) * Real.exp (-(y1 + y2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (y1 + y2) * (1 - (y1 + y2)) ≤ Real.exp (y1 + y2) * Real.exp (-(y1 + y2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := h2
  have hmain : nr * Real.exp (y1 + y2) ≤ S := by
    calc nr * Real.exp (y1 + y2) ≤ (S * (1 - (y1 + y2))) * Real.exp (y1 + y2) :=
          mul_le_mul_of_nonneg_right hny (Real.exp_pos _).le
      _ = S * (Real.exp (y1 + y2) * (1 - (y1 + y2))) := by ring
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hexp hSpos.le
      _ = S := mul_one S
  have hX0 : 0 ≤ (cardUX D N (n - deF) (n' - u) : ℝ) := Nat.cast_nonneg _
  have hprod : (cardUX D N n n' : ℝ) ≤
      (cardUX D N (n - deF) (n' - u) : ℝ) * Real.exp (y1 + y2) := by
    rw [hc1, hc2, Real.exp_add]
    calc _ ≤ ((((n - deF + (D + 1)).choose (D + 1) : ℕ) : ℝ) * Real.exp y1) *
          ((((n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) * Real.exp y2) :=
          mul_le_mul hA hB (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
      _ = _ := by ring
  have hnr0 : 0 ≤ nr := by linarith
  calc (n : ℝ) * cardUX D N n n' ≤ nr * ((cardUX D N (n - deF) (n' - u) : ℝ) * Real.exp (y1 + y2)) :=
        mul_le_mul_of_nonneg_left hprod hnr0
    _ = (cardUX D N (n - deF) (n' - u) : ℝ) * (nr * Real.exp (y1 + y2)) := by ring
    _ ≤ (cardUX D N (n - deF) (n' - u) : ℝ) * S := mul_le_mul_of_nonneg_left hmain hX0
    _ = ((n : ℝ) + (D + 2) * deF) * cardUX D N (n - deF) (n' - u) := by
        rw [hS, hK, ha, hnr]; push_cast; ring
end ReciprocityTheory.ChartRestriction.G.T0
