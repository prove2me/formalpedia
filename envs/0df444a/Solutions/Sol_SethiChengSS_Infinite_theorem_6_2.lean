-- Prove2me | solution 1 for SethiChengSS.Infinite.theorem_6_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:09:49.467993+00:00
-- url     : https://prove2.me/submissions/93430a6d-2836-4d55-b0da-2790b80f7a51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model
import Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_9
import Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_10
import Theorems.Thm_SethiChengSS_Infinite_value_kconvex

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Infinite.Red62

open SethiChengSS.Infinite

variable {L : ℕ}

lemma tri_abs (y z : ℝ) : |y - z| ≤ |y| + |z| := by
  rcases abs_cases y with h1 | h1 <;> rcases abs_cases z with h2 | h2 <;>
    rcases abs_cases (y - z) with h3 | h3 <;> linarith

lemma P_nonneg {D : Model L} (hD : Standing D) : ∀ i j, 0 ≤ D.P i j := hD.1
lemma P_sum {D : Model L} (hD : Standing D) : ∀ i, ∑ j, D.P i j = 1 := hD.2.1
lemma φ_meas {D : Model L} (hD : Standing D) : ∀ k i, Measurable (D.φ k i) := hD.2.2.1
lemma φ_nonneg {D : Model L} (hD : Standing D) : ∀ k i z, 0 ≤ D.φ k i z := hD.2.2.2.1
lemma φ_neg {D : Model L} (hD : Standing D) : ∀ k i z, z < 0 → D.φ k i z = 0 := hD.2.2.2.2.1
lemma φ_lint {D : Model L} (hD : Standing D) : ∀ k i, ∫⁻ z, ENNReal.ofReal (D.φ k i z) = 1 :=
  hD.2.2.2.2.2.1
lemma mean_lint {D : Model L} (hD : Standing D) :
    ∀ k i, ∫⁻ z, ENNReal.ofReal (z * D.φ k i z) ≤ ENNReal.ofReal D.M := hD.2.2.2.2.2.2.1
lemma K_nonneg {D : Model L} (hD : Standing D) : ∀ k i, 0 ≤ D.K k i := hD.2.2.2.2.2.2.2.1
lemma c_nonneg {D : Model L} (hD : Standing D) : ∀ k i, 0 ≤ D.c k i := hD.2.2.2.2.2.2.2.2.1
lemma f_nonneg {D : Model L} (hD : Standing D) : ∀ k i x, 0 ≤ D.f k i x :=
  hD.2.2.2.2.2.2.2.2.2.2.1

lemma absmul_eq {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (z : ℝ) :
    |z| * D.φ k i z = z * D.φ k i z := by
  rcases lt_or_ge z 0 with h | h
  · rw [φ_neg hD k i z h]; simp
  · rw [abs_of_nonneg h]

lemma phi_integrable {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    Integrable (D.φ k i) := by
  refine ⟨(φ_meas hD k i).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => φ_nonneg hD k i z), φ_lint hD k i]
  exact ENNReal.one_lt_top

lemma absmul_integrable {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    Integrable (fun z => |z| * D.φ k i z) := by
  refine ⟨((continuous_abs.measurable).mul (φ_meas hD k i)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
    mul_nonneg (abs_nonneg z) (φ_nonneg hD k i z))]
  have : (fun z => ENNReal.ofReal (|z| * D.φ k i z)) = fun z => ENNReal.ofReal (z * D.φ k i z) := by
    funext z; rw [absmul_eq hD]
  rw [this]
  exact lt_of_le_of_lt (mean_lint hD k i) ENNReal.ofReal_lt_top

lemma setInt_phi_le {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi 0, D.φ k i z ≤ 1 := by
  have h1 : ∫ z, D.φ k i z = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => φ_nonneg hD k i z)
      (φ_meas hD k i).aestronglyMeasurable, φ_lint hD k i]
    simp
  rw [← h1]
  exact setIntegral_le_integral (phi_integrable hD k i)
    (Eventually.of_forall fun z => φ_nonneg hD k i z)

lemma setInt_phi_eq {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi 0, D.φ k i z = 1 := by
  have h1 : ∫ z, D.φ k i z = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => φ_nonneg hD k i z)
      (φ_meas hD k i).aestronglyMeasurable, φ_lint hD k i]
    simp
  rw [← integral_Ici_eq_integral_Ioi, ← h1]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact φ_neg hD k i z (by simpa using hz)

lemma setInt_absmul_le {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi 0, |z| * D.φ k i z ≤ |D.M| := by
  have h1 : ∫ z, |z| * D.φ k i z ≤ |D.M| := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z =>
      mul_nonneg (abs_nonneg z) (φ_nonneg hD k i z))
      ((continuous_abs.measurable).mul (φ_meas hD k i)).aestronglyMeasurable]
    have : (fun z => ENNReal.ofReal (|z| * D.φ k i z)) =
        fun z => ENNReal.ofReal (z * D.φ k i z) := by
      funext z; rw [absmul_eq hD]
    rw [this]
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (mean_lint hD k i)
    rw [ENNReal.toReal_ofReal'] at h2
    exact h2.trans (max_le (le_abs_self _) (abs_nonneg _))
  refine le_trans ?_ h1
  exact setIntegral_le_integral (absmul_integrable hD k i)
    (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (φ_nonneg hD k i z))

lemma Cb_nonneg {b : ℝ → ℝ} (h0 : ∀ y, 0 ≤ b y) {Cb : ℝ} (hg : ∀ y, b y ≤ Cb * (1 + |y|)) :
    0 ≤ Cb := by
  have := h0 0; have := hg 0; simp at *; linarith

lemma shift_bound {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L) (b : ℝ → ℝ)
    (h0 : ∀ y, 0 ≤ b y) (Cb : ℝ) (hg : ∀ y, b y ≤ Cb * (1 + |y|)) (y z : ℝ) :
    ‖b (y - z) * D.φ n i z‖ ≤ Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z) := by
  have hφ := φ_nonneg hD n i z
  have hCb := Cb_nonneg h0 hg
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 _) hφ)]
  have h1 := hg (y - z)
  have h2 := tri_abs y z
  calc b (y - z) * D.φ n i z ≤ Cb * (1 + |y - z|) * D.φ n i z :=
        mul_le_mul_of_nonneg_right h1 hφ
    _ ≤ Cb * (1 + (|y| + |z|)) * D.φ n i z := by gcongr
    _ = _ := by ring

lemma shift_integrable {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L)
    (b : ℝ → ℝ) (hb : Continuous b) (h0 : ∀ y, 0 ≤ b y) (Cb : ℝ)
    (hg : ∀ y, b y ≤ Cb * (1 + |y|)) (y : ℝ) :
    Integrable (fun z => b (y - z) * D.φ n i z) := by
  refine Integrable.mono' (g := fun z => Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z))
    ?_ ?_ ?_
  · exact ((phi_integrable hD n i).const_mul _).add ((absmul_integrable hD n i).const_mul _)
  · exact ((hb.comp (continuous_const.sub continuous_id)).measurable.mul
      (φ_meas hD n i)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => shift_bound hD n i b h0 Cb hg y z

lemma setInt_shift_cont {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L)
    (b : ℝ → ℝ) (hb : Continuous b) (h0 : ∀ y, 0 ≤ b y) (Cb : ℝ)
    (hg : ∀ y, b y ≤ Cb * (1 + |y|)) :
    Continuous (fun y => ∫ z in Set.Ioi 0, b (y - z) * D.φ n i z) := by
  rw [continuous_iff_continuousAt]
  intro y0
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun z => Cb * (1 + (|y0| + 1)) * D.φ n i z + Cb * (|z| * D.φ n i z)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y => ((hb.comp (continuous_const.sub continuous_id)).measurable.mul
      (φ_meas hD n i)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds y0 one_pos] with y hy
    refine Eventually.of_forall fun z => ?_
    have hy' : |y| ≤ |y0| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have : |y| ≤ |y - y0| + |y0| := by
        rcases abs_cases y with h1 | h1 <;> rcases abs_cases y0 with h2 | h2 <;>
          rcases abs_cases (y - y0) with h3 | h3 <;> linarith
      linarith
    refine (shift_bound hD n i b h0 Cb hg y z).trans ?_
    have hφ := φ_nonneg hD n i z
    have hCb := Cb_nonneg h0 hg
    gcongr
  · exact (((phi_integrable hD n i).const_mul _).add
      ((absmul_integrable hD n i).const_mul _)).integrableOn
  · exact Eventually.of_forall fun z =>
      ((hb.comp (continuous_id.sub continuous_const)).mul continuous_const).continuousAt

lemma F_cont {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hb : ∀ j, Continuous (b j)) (h0 : ∀ j y, 0 ≤ b j y) (Cb : ℝ)
    (hg : ∀ j y, b j y ≤ Cb * (1 + |y|)) (i : Fin L) : Continuous (Fnext D n b i) := by
  unfold Fnext
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul
    (setInt_shift_cont hD n i (b j) (hb j) (h0 j) Cb (hg j)))

lemma F_nonneg {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (h0 : ∀ j y, 0 ≤ b j y) (i : Fin L) (y : ℝ) : 0 ≤ Fnext D n b i y := by
  unfold Fnext
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (P_nonneg hD i j)
    (integral_nonneg (fun z => mul_nonneg (h0 j _) (φ_nonneg hD n i z))))

lemma F_mono {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hb : ∀ j, Continuous (b j)) (h0 : ∀ j y, 0 ≤ b j y) (Cb : ℝ)
    (hg : ∀ j y, b j y ≤ Cb * (1 + |y|)) (i : Fin L)
    (b' : Fin L → ℝ → ℝ) (h0' : ∀ j y, 0 ≤ b' j y) (hle : ∀ j y, b' j y ≤ b j y) (y : ℝ) :
    Fnext D n b' i y ≤ Fnext D n b i y := by
  unfold Fnext
  refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (P_nonneg hD i j))
  exact integral_mono_of_nonneg
    (Eventually.of_forall fun z => mul_nonneg (h0' j _) (φ_nonneg hD n i z))
    (shift_integrable hD n i (b j) (hb j) (h0 j) Cb (hg j) y).integrableOn
    (Eventually.of_forall fun z => mul_le_mul_of_nonneg_right (hle j _) (φ_nonneg hD n i z))

theorem F_kconvex {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hb : ∀ j, Continuous (b j)) (h0 : ∀ j y, 0 ≤ b j y) (Cb : ℝ)
    (hg : ∀ j y, b j y ≤ Cb * (1 + |y|)) (Kj : Fin L → ℝ)
    (hK : ∀ j, BertsekasKConvex (Kj j) (b j)) (i : Fin L) :
    BertsekasKConvex (∑ j, D.P i j * Kj j) (Fnext D n b i) := by
  intro z w y hz hw
  have hint : ∀ j t, IntegrableOn (fun ξ => b j (t - ξ) * D.φ n i ξ) (Set.Ioi 0) :=
    fun j t => (shift_integrable hD n i (b j) (hb j) (h0 j) Cb (hg j) t).integrableOn
  have hphi : IntegrableOn (D.φ n i) (Set.Ioi 0) := (phi_integrable hD n i).integrableOn
  have hj : ∀ j, (∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) +
      z / w * ((∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
        (∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ)) ≤
      Kj j + (∫ ξ in Set.Ioi 0, b j ((z + y) - ξ) * D.φ n i ξ) := by
    intro j
    have hmono : (∫ ξ in Set.Ioi 0, ((1 + z / w) * (b j (y - ξ) * D.φ n i ξ) -
          z / w * (b j ((y - w) - ξ) * D.φ n i ξ))) ≤
        ∫ ξ in Set.Ioi 0, (Kj j * D.φ n i ξ + b j ((z + y) - ξ) * D.φ n i ξ) := by
      apply integral_mono (((hint j y).const_mul _).sub ((hint j (y - w)).const_mul _))
        ((hphi.const_mul _).add (hint j (z + y)))
      intro ξ
      have h := hK j z w (y - ξ) hz hw
      have hφ := φ_nonneg hD n i ξ
      have e1 : y - ξ - w = (y - w) - ξ := by ring
      have e2 : z + (y - ξ) = (z + y) - ξ := by ring
      rw [e1, e2] at h
      have h2 := mul_le_mul_of_nonneg_right h hφ
      have e3 : (1 + z / w) * (b j (y - ξ) * D.φ n i ξ) - z / w * (b j ((y - w) - ξ) * D.φ n i ξ)
          = (b j (y - ξ) + z / w * (b j (y - ξ) - b j ((y - w) - ξ))) * D.φ n i ξ := by ring
      have e4 : Kj j * D.φ n i ξ + b j ((z + y) - ξ) * D.φ n i ξ =
          (Kj j + b j ((z + y) - ξ)) * D.φ n i ξ := by ring
      show (1 + z / w) * (b j (y - ξ) * D.φ n i ξ) - z / w * (b j ((y - w) - ξ) * D.φ n i ξ) ≤
        Kj j * D.φ n i ξ + b j ((z + y) - ξ) * D.φ n i ξ
      rw [e3, e4]; exact h2
    rw [integral_sub ((hint j y).const_mul _) ((hint j (y - w)).const_mul _),
      integral_add (hphi.const_mul _) (hint j (z + y)), integral_const_mul, integral_const_mul,
      integral_const_mul, setInt_phi_eq hD n i] at hmono
    have e5 : (∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) +
      z / w * ((∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
        (∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ)) =
        (1 + z / w) * (∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
          z / w * (∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ) := by ring
    rw [e5]; linarith
  unfold Fnext
  calc (∑ j, D.P i j * ∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) +
        z / w * ((∑ j, D.P i j * ∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
          ∑ j, D.P i j * ∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ)
      = ∑ j, D.P i j * ((∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) +
          z / w * ((∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
            (∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ))) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, D.P i j * (Kj j + (∫ ξ in Set.Ioi 0, b j ((z + y) - ξ) * D.φ n i ξ)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hj j) (P_nonneg hD i j))
    _ = (∑ j, D.P i j * Kj j) + ∑ j, D.P i j * ∫ ξ in Set.Ioi 0, b j ((z + y) - ξ) * D.φ n i ξ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)

section SS

variable {K : ℝ} {g : ℝ → ℝ}

lemma kc_step (hg : BertsekasKConvex K g) {a y c : ℝ} (hay : a < y) (hyc : y ≤ c)
    (h : g a ≤ g y) : g y ≤ K + g c := by
  have hk := hg (c - y) (y - a) y (by linarith) (by linarith)
  have e1 : y - (y - a) = a := by ring
  have e2 : c - y + y = c := by ring
  rw [e1, e2] at hk
  have : 0 ≤ (c - y) / (y - a) * (g y - g a) :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

lemma kc_step2 (hg : BertsekasKConvex K g) {a x S : ℝ} (hax : a < x) (hxS : x ≤ S)
    (h : g a ≤ K + g S) : g x ≤ K + g S := by
  by_cases h' : g a ≤ g x
  · exact kc_step hg hax hxS h'
  · push Not at h'; linarith

lemma exists_min_Ici (hc : Continuous g) (hco : Tendsto g atTop atTop) (x : ℝ) :
    ∃ y, x ≤ y ∧ ∀ t, x ≤ t → g y ≤ g t := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 (tendsto_atTop.1 hco (g x))
  obtain ⟨y, hy, hmin⟩ := (isCompact_Icc (a := x) (b := max R x)).exists_isMinOn
    (Set.nonempty_Icc.2 (le_max_right R x)) hc.continuousOn
  refine ⟨y, hy.1, fun t ht => ?_⟩
  by_cases htR : t ≤ max R x
  · exact hmin ⟨ht, htR⟩
  · push Not at htR
    have h1 := hR t (le_trans (le_max_left R x) htR.le)
    have h2 : g y ≤ g x := hmin ⟨le_rfl, le_max_right R x⟩
    linarith

lemma ss_dichotomy (hg : BertsekasKConvex K g) (hc : Continuous g)
    (hco : Tendsto g atTop atTop) :
    (∀ x u, 0 < u → g x ≤ K + g (x + u)) ∨
    ∃ s0 S0 : ℝ, s0 ≤ S0 ∧ (∀ y, g S0 ≤ g y) ∧ g s0 = K + g S0 ∧
      (∀ x, x < s0 → K + g S0 < g x) ∧ (∀ x, s0 ≤ x → x ≤ S0 → g x ≤ K + g S0) ∧
      (∀ x u, s0 ≤ x → 0 < u → g x ≤ K + g (x + u)) := by
  by_cases hmin : ∃ S0, ∀ y, g S0 ≤ g y
  · obtain ⟨S0, hS0⟩ := hmin
    have hfar : ∀ x u, S0 < x → 0 < u → g x ≤ K + g (x + u) :=
      fun x u hx hu => kc_step hg hx (by linarith) (hS0 x)
    have hnear : ∀ x u, g x ≤ K + g S0 → g x ≤ K + g (x + u) :=
      fun x u h => by linarith [hS0 (x + u)]
    let A : Set ℝ := {x : ℝ | x ≤ S0 ∧ g x ≤ K + g S0}
    have hKS : g S0 ≤ K + g S0 := by
      have hk := hg 0 1 S0 le_rfl one_pos
      simp at hk
      linarith
    have hSA : S0 ∈ A := ⟨le_rfl, hKS⟩
    have hAcl : IsClosed A :=
      (isClosed_le continuous_id continuous_const).inter (isClosed_le hc continuous_const)
    by_cases hbdd : BddBelow A
    · right
      have hs0A : sInf A ∈ A := hAcl.csInf_mem ⟨S0, hSA⟩ hbdd
      have hlt : ∀ x, x < sInf A → K + g S0 < g x := by
        intro x hx
        by_contra h; push Not at h
        have hxA : x ∈ A := ⟨by linarith [hs0A.1], h⟩
        have := csInf_le hbdd hxA
        linarith
      have hmid : ∀ x, sInf A ≤ x → x ≤ S0 → g x ≤ K + g S0 := by
        intro x hx hxS
        rcases eq_or_lt_of_le hx with h | h
        · rw [← h]; exact hs0A.2
        · obtain ⟨a, haA, hax⟩ := exists_lt_of_csInf_lt ⟨S0, hSA⟩ h
          exact kc_step2 hg hax hxS haA.2
      refine ⟨sInf A, S0, hs0A.1, hS0, le_antisymm hs0A.2 ?_, hlt, hmid, ?_⟩
      · have ht : Tendsto g (𝓝[<] (sInf A)) (𝓝 (g (sInf A))) :=
          hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall
          (fun x (hx : x ∈ Set.Iio (sInf A)) => (hlt x hx).le))
      · intro x u hx hu
        by_cases hxS : x ≤ S0
        · exact hnear x u (hmid x hx hxS)
        · push Not at hxS; exact hfar x u hxS hu
    · left
      intro x u hu
      by_cases hxS : x ≤ S0
      · rw [not_bddBelow_iff] at hbdd
        obtain ⟨a, haA, hax⟩ := hbdd x
        exact hnear x u (kc_step2 hg hax hxS haA.2)
      · push Not at hxS; exact hfar x u hxS hu
  · left
    intro x u hu
    push Not at hmin
    have : ∃ a, a < x ∧ g a ≤ g x := by
      by_contra hne
      push Not at hne
      obtain ⟨y, hxy, hy⟩ := exists_min_Ici hc hco x
      obtain ⟨t, ht⟩ := hmin y
      rcases lt_or_ge t x with htx | htx
      · have := hne t htx; have := hy x le_rfl; linarith
      · have := hy t htx; linarith
    obtain ⟨a, hax, ha⟩ := this
    exact kc_step hg hax (by linarith) ha

lemma delta_zero : delta 0 = 0 := by simp [delta]

lemma delta_pos {u : ℝ} (hu : 0 < u) : delta u = 1 := by simp [delta, hu]

lemma delta_nonneg (z : ℝ) : 0 ≤ delta z := by
  unfold delta; split_ifs <;> norm_num

lemma never_min (hnev : ∀ x u, 0 < u → g x ≤ K + g (x + u)) (x u : ℝ) (hu : 0 ≤ u) :
    g x ≤ K * delta u + g (x + u) := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, delta_zero]; simp
  · rw [delta_pos h, mul_one]; exact hnev x u h

/-- The `(s, S)` choice for a `K`-convex, continuous, coercive `g` (Section 4 of the paper),
recording that either `s = S = ⊥` (never order) or `s ≤ S` are both real. -/
theorem ss_attains (g : ℝ → ℝ) (hg : BertsekasKConvex K g)
    (hc : Continuous g) (hco : Tendsto g atTop atTop) :
    ∃ s S : EReal, ((s = ⊥ ∧ S = ⊥) ∨ ∃ s0 S0 : ℝ, s0 ≤ S0 ∧ s = s0 ∧ S = S0) ∧ ∀ x : ℝ,
      0 ≤ orderSS s S x ∧ ∀ u : ℝ, 0 ≤ u →
        K * delta (orderSS s S x) + g (x + orderSS s S x) ≤ K * delta u + g (x + u) := by
  rcases ss_dichotomy hg hc hco with hnev | ⟨s0, S0, hsS, hS0, heq, hlt, hmid, hright⟩
  · refine ⟨⊥, ⊥, Or.inl ⟨rfl, rfl⟩, fun x => ?_⟩
    have ho : orderSS ⊥ ⊥ x = 0 := by simp [orderSS]
    rw [ho, delta_zero, add_zero]
    exact ⟨le_rfl, fun u hu => by simpa using never_min hnev x u hu⟩
  · refine ⟨(s0 : EReal), (S0 : EReal), Or.inr ⟨s0, S0, hsS, rfl, rfl⟩, fun x => ?_⟩
    by_cases hx : x < s0
    · have ho : orderSS s0 S0 x = S0 - x := by simp [orderSS, hx]
      rw [ho]
      have hpos : 0 < S0 - x := by linarith
      refine ⟨hpos.le, fun u hu => ?_⟩
      have e : x + (S0 - x) = S0 := by ring
      rw [e, delta_pos hpos, mul_one]
      rcases eq_or_lt_of_le hu with h | h
      · rw [← h, delta_zero]; simp; linarith [hlt x hx]
      · rw [delta_pos h, mul_one]; linarith [hS0 (x + u)]
    · have ho : orderSS s0 S0 x = 0 := by simp [orderSS, hx]
      rw [ho, delta_zero, add_zero]
      push Not at hx
      refine ⟨le_rfl, fun u hu => ?_⟩
      rcases eq_or_lt_of_le hu with h | h
      · rw [← h, delta_zero]; simp
      · rw [delta_pos h, mul_one]; simpa using hright x u hx h

end SS

lemma kconvex_mono {K1 K2 : ℝ} {g : ℝ → ℝ} (h : BertsekasKConvex K1 g) (hK : K1 ≤ K2) :
    BertsekasKConvex K2 g := fun z b y hz hb => (h z b y hz hb).trans (by linarith)

lemma kconvex_smul {K : ℝ} (a : ℝ) (ha : 0 ≤ a) {g : ℝ → ℝ} (h : BertsekasKConvex K g) :
    BertsekasKConvex (a * K) (fun y => a * g y) := by
  intro z b y hz hb
  have h1 := mul_le_mul_of_nonneg_left (h z b y hz hb) ha
  have e : a * g y + z / b * (a * g y - a * g (y - b)) = a * (g y + z / b * (g y - g (y - b))) := by
    ring
  rw [e]; linarith

lemma kconvex_linear {K : ℝ} (a : ℝ) {g : ℝ → ℝ} (h : BertsekasKConvex K g) :
    BertsekasKConvex K (fun y => a * y + g y) := by
  intro z b y hz hb
  have a1 := h z b y hz hb
  have hb' : b ≠ 0 := hb.ne'
  have e : (z / b) * ((a * y + g y) - (a * (y - b) + g (y - b))) =
      (z / b) * (g y - g (y - b)) + a * z := by field_simp; ring
  show a * y + g y + (z / b) * ((a * y + g y) - (a * (y - b) + g (y - b))) ≤
    K + (a * (z + y) + g (z + y))
  rw [e]
  have e2 : a * (z + y) = a * z + a * y := by ring
  linarith

/-- The `(s, S)` order rule is in `B_0`: it is nonnegative and the pointwise limit of
continuous nonnegative functions `(S − x) · min(1, max(0, m(s − x)))`. -/
lemma orderSS_B0 (s S : ℕ → Fin L → EReal)
    (hsS : ∀ n i, (s n i = ⊥ ∧ S n i = ⊥) ∨ ∃ s0 S0 : ℝ, s0 ≤ S0 ∧ s n i = s0 ∧ S n i = S0)
    (n : ℕ) : InB0 (fun i x => orderSS (s n i) (S n i) x) := by
  classical
  have key : ∀ i, (∀ x, 0 ≤ orderSS (s n i) (S n i) x) ∧
      ∃ g : ℕ → ℝ → ℝ, (∀ m, Continuous (g m)) ∧ (∀ m x, 0 ≤ g m x) ∧
        ∀ x, Tendsto (fun m => g m x) atTop (𝓝 (orderSS (s n i) (S n i) x)) := by
    intro i
    rcases hsS n i with ⟨h1, h2⟩ | ⟨s0, S0, hle, h1, h2⟩
    · rw [h1, h2]
      have ho : ∀ x, orderSS ⊥ ⊥ x = 0 := fun x => by simp [orderSS]
      refine ⟨fun x => (ho x).ge, fun _ _ => 0, fun _ => continuous_const, fun _ _ => le_rfl,
        fun x => ?_⟩
      rw [ho x]; exact tendsto_const_nhds
    · rw [h1, h2]
      have ho : ∀ x, orderSS s0 S0 x = if x < s0 then S0 - x else 0 := fun x => by
        simp [orderSS]
      refine ⟨fun x => ?_, fun m x => (S0 - x) * min 1 (max 0 ((m : ℝ) * (s0 - x))),
        fun m => ?_, fun m x => ?_, fun x => ?_⟩
      · rw [ho x]; split_ifs with h
        · linarith
        · exact le_rfl
      · fun_prop
      · show 0 ≤ (S0 - x) * min 1 (max 0 ((m : ℝ) * (s0 - x)))
        by_cases h : x < s0
        · have : 0 ≤ S0 - x := by linarith
          exact mul_nonneg this (le_min zero_le_one (le_max_left _ _))
        · push Not at h
          have : (m : ℝ) * (s0 - x) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) (by linarith)
          rw [max_eq_left this, min_eq_right zero_le_one, mul_zero]
      · rw [ho x]
        split_ifs with h
        · have hpos : 0 < s0 - x := by linarith
          have hev : ∀ᶠ m : ℕ in atTop, (S0 - x) * min 1 (max 0 ((m : ℝ) * (s0 - x))) = S0 - x := by
            obtain ⟨N, hN⟩ := exists_nat_gt (1 / (s0 - x))
            filter_upwards [eventually_ge_atTop N] with m hm
            have : 1 ≤ (m : ℝ) * (s0 - x) := by
              have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
              have : 1 / (s0 - x) < m := lt_of_lt_of_le hN hm'
              rw [div_lt_iff₀ hpos] at this
              linarith
            rw [max_eq_right (by linarith), min_eq_left this, mul_one]
          exact tendsto_const_nhds.congr' (EventuallyEq.symm hev)
        · push Not at h
          have hev : ∀ m : ℕ, (S0 - x) * min 1 (max 0 ((m : ℝ) * (s0 - x))) = 0 := by
            intro m
            have : (m : ℝ) * (s0 - x) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) (by linarith)
            rw [max_eq_left this, min_eq_right zero_le_one, mul_zero]
          simp only [hev]; exact tendsto_const_nhds
  choose hnn g hgc hg0 hgt using key
  exact ⟨fun i x => hnn i x, fun m i x => g i m x, fun m i => hgc i m, fun m i x => hg0 i m x,
    fun i x => hgt i x⟩

end SethiChengSS.Infinite.Red62

open SethiChengSS.Infinite SethiChengSS.Infinite.Red62

theorem solution {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h41 : Cond41 D)
    (h42 : Cond42 D) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ s S : ℕ → Fin L → EReal,
      (∀ n i, s n i ≤ S n i ∧ S n i ≠ ⊤ ∧ (s n i ≠ ⊥ → S n i ≠ ⊥)) ∧
      AttainsInf D α (fun n i x => (value D α n i x).toReal)
        (fun n i x => orderSS (s n i) (S n i) x) ∧
      ∀ n i x,
        Admissible (feedback (fun n i x => orderSS (s n i) (S n i) x) n x) ∧
        Jinf D α n i x (feedback (fun n i x => orderSS (s n i) (S n i) x) n x) =
          value D α n i x := by
  obtain ⟨_, _, hBell, _⟩ := theorem_6_1_eq_6_9 D α hD h42 hα0 hα1
  obtain ⟨hC1, ⟨û0, hû0B, hû0A⟩, hver⟩ := theorem_6_1_eq_6_10 D α hD h42 hα0 hα1
  have hkc := value_kconvex D α hD h41 h42 hα0 hα1
  -- value = vLim
  have hval : ∀ n i x, value D α n i x = vLim D α n i x :=
    fun n i x => (hver û0 hû0B hû0A n i x).2.1
  set V : ℕ → Fin L → ℝ → ℝ := fun n i x => (vLim D α n i x).toReal with hVdef
  have hVfun : (fun n i x => (value D α n i x).toReal) = V := by
    funext n i x; rw [hval]
  have hV0 : ∀ n i x, 0 ≤ V n i x := fun n i x => ENNReal.toReal_nonneg
  have hVc : ∀ n i, Continuous (V n i) := fun n i => (hC1 n).2 i |>.continuous
  have hVg : ∀ n, ∃ Cb : ℝ, ∀ i x, V n i x ≤ Cb * (1 + |x|) := fun n => by
    obtain ⟨Cb, _, h⟩ := (hC1 n).1.2
    exact ⟨Cb, h⟩
  have hVk : ∀ n i, BertsekasKConvex (D.K n i) (V n i) := by
    intro n i
    have := hkc n i
    simpa [hval] using this
  -- V ≥ f
  have hVf : ∀ n i x, D.f n i x ≤ V n i x := by
    intro n i x
    rw [hBell n i x]
    have : 0 ≤ ⨅ u : {u : ℝ // 0 ≤ u},
        (orderCost D n i u + α * Fnext D n (V (n + 1)) i (x + u)) := by
      apply Real.iInf_nonneg
      intro u
      have := F_nonneg hD n (V (n + 1)) (fun j y => hV0 _ j y) i (x + u)
      have := delta_nonneg u.1
      have := K_nonneg hD n i
      have := c_nonneg hD n i
      have := u.2
      simp only [orderCost]
      positivity
    linarith
  -- the function G
  have hG : ∀ n i, Continuous (fun y => D.c n i * y + α * Fnext D n (V (n + 1)) i y) ∧
      BertsekasKConvex (D.K n i) (fun y => D.c n i * y + α * Fnext D n (V (n + 1)) i y) ∧
      Tendsto (fun y => D.c n i * y + α * Fnext D n (V (n + 1)) i y) atTop atTop := by
    intro n i
    obtain ⟨Cb, hCb⟩ := hVg (n + 1)
    refine ⟨(continuous_const.mul continuous_id).add (continuous_const.mul
      (F_cont hD n (V (n + 1)) (hVc (n + 1)) (hV0 (n + 1)) Cb hCb i)), ?_, ?_⟩
    · apply kconvex_linear
      have h1 := F_kconvex hD n (V (n + 1)) (hVc (n + 1)) (hV0 (n + 1)) Cb hCb
        (fun j => D.K (n + 1) j) (hVk (n + 1)) i
      have h2 := kconvex_smul α hα0.le h1
      refine kconvex_mono h2 ?_
      have hKb := h41 n i
      calc α * ∑ j, D.P i j * D.K (n + 1) j ≤ 1 * ∑ j, D.P i j * D.K (n + 1) j :=
            mul_le_mul_of_nonneg_right hα1.le hKb.2
        _ ≤ D.K n i := by rw [one_mul]; exact hKb.1
    · have hT := (h42 n i).const_mul_atTop hα0
      refine tendsto_atTop_mono' atTop ?_ hT
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
      have hm := F_mono hD n (V (n + 1)) (hVc (n + 1)) (hV0 (n + 1)) Cb hCb i (D.f (n + 1))
        (fun j y => f_nonneg hD _ _ _) (hVf (n + 1)) y
      have hc := c_nonneg hD n i
      have h1 : α * (D.c n i * y) ≤ D.c n i * y := by
        have : 0 ≤ D.c n i * y := mul_nonneg hc hy
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left hm hα0.le
      show α * (D.c n i * y + Fnext D n (D.f (n + 1)) i y) ≤
        D.c n i * y + α * Fnext D n (V (n + 1)) i y
      nlinarith
  have hss : ∀ n i, ∃ s S : EReal, ((s = ⊥ ∧ S = ⊥) ∨ ∃ s0 S0 : ℝ, s0 ≤ S0 ∧ s = s0 ∧ S = S0) ∧
      ∀ x : ℝ, 0 ≤ orderSS s S x ∧ ∀ u : ℝ, 0 ≤ u →
        D.K n i * delta (orderSS s S x) +
            (D.c n i * (x + orderSS s S x) + α * Fnext D n (V (n + 1)) i (x + orderSS s S x)) ≤
          D.K n i * delta u + (D.c n i * (x + u) + α * Fnext D n (V (n + 1)) i (x + u)) :=
    fun n i => ss_attains _ (hG n i).2.1 (hG n i).1 (hG n i).2.2
  choose s S hsS hmin using hss
  have hatt : AttainsInf D α V (fun n i x => orderSS (s n i) (S n i) x) := by
    intro n i x
    refine ⟨(hmin n i x).1, ?_⟩
    have hle : ∀ u : {u : ℝ // 0 ≤ u},
        orderCost D n i (orderSS (s n i) (S n i) x) +
            α * Fnext D n (V (n + 1)) i (x + orderSS (s n i) (S n i) x) ≤
          orderCost D n i u + α * Fnext D n (V (n + 1)) i (x + u) := by
      intro u
      have := (hmin n i x).2 u.1 u.2
      simp only [orderCost]
      linarith
    let u0 : {u : ℝ // 0 ≤ u} := ⟨orderSS (s n i) (S n i) x, (hmin n i x).1⟩
    exact (le_antisymm (ciInf_le ⟨_, by rintro _ ⟨u, rfl⟩; exact hle u⟩ u0) (le_ciInf hle)).symm
  have hB0 : ∀ n, InB0 ((fun n i x => orderSS (s n i) (S n i) x) n) :=
    fun n => orderSS_B0 s S hsS n
  refine ⟨s, S, fun n i => ?_, ?_, fun n i x => ?_⟩
  · rcases hsS n i with ⟨h1, h2⟩ | ⟨s0, S0, hle, h1, h2⟩
    · rw [h1, h2]; exact ⟨le_rfl, bot_ne_top, fun h => absurd rfl h⟩
    · rw [h1, h2]
      exact ⟨EReal.coe_le_coe_iff.2 hle, EReal.coe_ne_top _, fun _ => EReal.coe_ne_bot _⟩
  · rw [hVfun]; exact hatt
  · obtain ⟨hadm, _, hJ⟩ := hver _ hB0 hatt n i x
    exact ⟨hadm, hJ⟩
