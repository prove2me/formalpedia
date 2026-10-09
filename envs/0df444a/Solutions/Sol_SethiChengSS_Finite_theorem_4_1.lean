-- Prove2me | solution 1 for SethiChengSS.Finite.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T20:53:24.794569+00:00
-- url     : https://prove2.me/submissions/f50bd8d5-901f-4402-8e4d-5e266e485f81

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
import Definitions.Def_SethiChengSS_Finite_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Finite

lemma tri_abs (y z : ℝ) : |y - z| ≤ |y| + |z| := by
  rcases abs_cases y with h1 | h1 <;> rcases abs_cases z with h2 | h2 <;>
    rcases abs_cases (y - z) with h3 | h3 <;> linarith

lemma phi_integrable {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (i : Fin L) :
    Integrable (D.φ k i) := by
  by_contra h
  have := integral_undef h
  rw [hS.φ_int k i] at this
  norm_num at this

lemma absmul_integrable {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (i : Fin L) :
    Integrable (fun z => |z| * D.φ k i z) := by
  refine (hS.mean_integrable k i).norm.congr (Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hS.φ_nonneg k i z)]

lemma absmul_eq {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (i : Fin L) (z : ℝ) :
    |z| * D.φ k i z = z * D.φ k i z := by
  rcases lt_or_ge z 0 with h | h
  · rw [hS.φ_neg k i z h]; simp
  · rw [abs_of_nonneg h]

lemma M_nonneg {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (i : Fin L) : 0 ≤ D.M := by
  have h1 := hS.mean_le k i
  have h2 : 0 ≤ ∫ z, z * D.φ k i z := by
    apply integral_nonneg; intro z
    show 0 ≤ z * D.φ k i z
    rw [← absmul_eq D hS]; exact mul_nonneg (abs_nonneg _) (hS.φ_nonneg k i z)
  linarith

lemma setInt_phi_le {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi 0, D.φ k i z ≤ 1 := by
  rw [← hS.φ_int k i]
  exact setIntegral_le_integral (phi_integrable D hS k i)
    (Eventually.of_forall fun z => hS.φ_nonneg k i z)

lemma setInt_absmul_le {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi 0, |z| * D.φ k i z ≤ D.M := by
  refine le_trans ?_ (hS.mean_le k i)
  have : ∫ z, z * D.φ k i z = ∫ z, |z| * D.φ k i z := by
    congr 1; funext z; rw [absmul_eq D hS]
  rw [this]
  exact setIntegral_le_integral (absmul_integrable D hS k i)
    (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (hS.φ_nonneg k i z))

lemma Cb_nonneg {b : ℝ → ℝ} (h0 : ∀ y, 0 ≤ b y) {Cb : ℝ} (hg : ∀ y, b y ≤ Cb * (1 + |y|)) :
    0 ≤ Cb := by
  have := h0 0; have := hg 0; simp at *; linarith

lemma shift_bound {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) (i : Fin L) (b : ℝ → ℝ)
    (h0 : ∀ y, 0 ≤ b y) (Cb : ℝ) (hg : ∀ y, b y ≤ Cb * (1 + |y|)) (y z : ℝ) :
    ‖b (y - z) * D.φ n i z‖ ≤ Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z) := by
  have hφ := hS.φ_nonneg n i z
  have hCb := Cb_nonneg h0 hg
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 _) hφ)]
  have h1 := hg (y - z)
  have h2 := tri_abs y z
  calc b (y - z) * D.φ n i z ≤ Cb * (1 + |y - z|) * D.φ n i z :=
        mul_le_mul_of_nonneg_right h1 hφ
    _ ≤ Cb * (1 + (|y| + |z|)) * D.φ n i z := by gcongr
    _ = _ := by ring

lemma shift_integrable {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) (i : Fin L)
    (b : ℝ → ℝ) (hb : Continuous b) (h0 : ∀ y, 0 ≤ b y) (Cb : ℝ)
    (hg : ∀ y, b y ≤ Cb * (1 + |y|)) (y : ℝ) :
    Integrable (fun z => b (y - z) * D.φ n i z) := by
  refine Integrable.mono' (g := fun z => Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z))
    ?_ ?_ ?_
  · exact ((phi_integrable D hS n i).const_mul _).add ((absmul_integrable D hS n i).const_mul _)
  · exact ((hb.comp (continuous_const.sub continuous_id)).measurable.mul
      (hS.φ_meas n i)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => shift_bound D hS n i b h0 Cb hg y z

lemma setInt_shift_cont {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) (i : Fin L)
    (b : ℝ → ℝ) (hb : Continuous b) (h0 : ∀ y, 0 ≤ b y) (Cb : ℝ)
    (hg : ∀ y, b y ≤ Cb * (1 + |y|)) :
    Continuous (fun y => ∫ z in Set.Ioi 0, b (y - z) * D.φ n i z) := by
  rw [continuous_iff_continuousAt]
  intro y0
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun z => Cb * (1 + (|y0| + 1)) * D.φ n i z + Cb * (|z| * D.φ n i z)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y => ((hb.comp (continuous_const.sub continuous_id)).measurable.mul
      (hS.φ_meas n i)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds y0 one_pos] with y hy
    refine Eventually.of_forall fun z => ?_
    have hy' : |y| ≤ |y0| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have := tri_abs y y0
      have : |y| ≤ |y - y0| + |y0| := by
        rcases abs_cases y with h1 | h1 <;> rcases abs_cases y0 with h2 | h2 <;>
          rcases abs_cases (y - y0) with h3 | h3 <;> linarith
      linarith
    refine (shift_bound D hS n i b h0 Cb hg y z).trans ?_
    have hφ := hS.φ_nonneg n i z
    have hCb := Cb_nonneg h0 hg
    gcongr
  · exact (((phi_integrable D hS n i).const_mul _).add
      ((absmul_integrable D hS n i).const_mul _)).integrableOn
  · exact Eventually.of_forall fun z =>
      ((hb.comp (continuous_id.sub continuous_const)).mul continuous_const).continuousAt

theorem child_F_regular {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hb : ∀ j, Continuous (b j)) (h0 : ∀ j y, 0 ≤ b j y) (Cb : ℝ)
    (hg : ∀ j y, b j y ≤ Cb * (1 + |y|)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ i, Continuous (F D n b i) ∧ (∀ y, 0 ≤ F D n b i y) ∧
      (∀ y, F D n b i y ≤ C' * (1 + |y|)) ∧
      ∀ b' : Fin L → ℝ → ℝ, (∀ j y, 0 ≤ b' j y) → (∀ j y, b' j y ≤ b j y) →
        ∀ y, F D n b' i y ≤ F D n b i y := by
  refine ⟨|Cb| * (1 + |D.M|) + 1, by positivity, fun i => ⟨?_, ?_, ?_, ?_⟩⟩
  · unfold F
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul
      (setInt_shift_cont D hS n i (b j) (hb j) (h0 j) Cb (hg j)))
  · intro y
    unfold F
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hS.P_nonneg i j)
      (setIntegral_nonneg measurableSet_Ioi (fun z _ => mul_nonneg (h0 j _) (hS.φ_nonneg n i z))))
  · intro y
    have hCb : 0 ≤ Cb := Cb_nonneg (h0 i) (hg i)
    have hM := M_nonneg D hS n i
    have hI : ∀ j, ∫ z in Set.Ioi 0, b j (y - z) * D.φ n i z ≤ Cb * (1 + D.M) * (1 + |y|) := by
      intro j
      have hi1 := (shift_integrable D hS n i (b j) (hb j) (h0 j) Cb (hg j) y).integrableOn
        (s := Set.Ioi 0)
      have hi2 : IntegrableOn (fun z => Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z))
          (Set.Ioi 0) :=
        (((phi_integrable D hS n i).const_mul _).add
          ((absmul_integrable D hS n i).const_mul _)).integrableOn
      calc ∫ z in Set.Ioi 0, b j (y - z) * D.φ n i z
          ≤ ∫ z in Set.Ioi 0, (Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z)) :=
            integral_mono hi1 hi2 (fun z => (Real.le_norm_self _).trans
              (shift_bound D hS n i (b j) (h0 j) Cb (hg j) y z))
        _ = Cb * (1 + |y|) * (∫ z in Set.Ioi 0, D.φ n i z) +
              Cb * (∫ z in Set.Ioi 0, |z| * D.φ n i z) := by
            rw [integral_add ((phi_integrable D hS n i).const_mul _).integrableOn
              ((absmul_integrable D hS n i).const_mul _).integrableOn, integral_const_mul,
              integral_const_mul]
        _ ≤ Cb * (1 + |y|) * 1 + Cb * D.M := by
            have a1 := mul_le_mul_of_nonneg_left (setInt_phi_le D hS n i)
              (by positivity : 0 ≤ Cb * (1 + |y|))
            have a2 := mul_le_mul_of_nonneg_left (setInt_absmul_le D hS n i) hCb
            linarith
        _ ≤ Cb * (1 + D.M) * (1 + |y|) := by
            have : 0 ≤ Cb * D.M * |y| := by positivity
            nlinarith
    unfold F
    calc ∑ j, D.P i j * ∫ z in Set.Ioi 0, b j (y - z) * D.φ n i z
        ≤ ∑ j, D.P i j * (Cb * (1 + D.M) * (1 + |y|)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hI j) (hS.P_nonneg i j))
      _ = Cb * (1 + D.M) * (1 + |y|) := by rw [← Finset.sum_mul, hS.P_sum i, one_mul]
      _ ≤ (|Cb| * (1 + |D.M|) + 1) * (1 + |y|) := by
          have : 0 ≤ 1 + |y| := by positivity
          rw [abs_of_nonneg hCb, abs_of_nonneg hM]
          nlinarith
  · intro b' h0' hle y
    unfold F
    refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (hS.P_nonneg i j))
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (h0' j _) (hS.φ_nonneg n i z))
      (shift_integrable D hS n i (b j) (hb j) (h0 j) Cb (hg j) y).integrableOn
      (Eventually.of_forall fun z => mul_le_mul_of_nonneg_right (hle j _) (hS.φ_nonneg n i z))

lemma setInt_phi_eq {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi 0, D.φ k i z = 1 := by
  rw [← integral_Ici_eq_integral_Ioi, ← hS.φ_int k i]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hS.φ_neg k i z (by simpa using hz)

theorem child_F_kconvex {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hb : ∀ j, Continuous (b j)) (h0 : ∀ j y, 0 ≤ b j y) (Cb : ℝ)
    (hg : ∀ j y, b j y ≤ Cb * (1 + |y|)) (Kj : Fin L → ℝ)
    (hK : ∀ j, BertsekasKConvex (Kj j) (b j)) (i : Fin L) :
    BertsekasKConvex (∑ j, D.P i j * Kj j) (F D n b i) := by
  intro z w y hz hw
  have hint : ∀ j t, IntegrableOn (fun ξ => b j (t - ξ) * D.φ n i ξ) (Set.Ioi 0) :=
    fun j t => (shift_integrable D hS n i (b j) (hb j) (h0 j) Cb (hg j) t).integrableOn
  have hphi : IntegrableOn (D.φ n i) (Set.Ioi 0) := (phi_integrable D hS n i).integrableOn
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
      have hφ := hS.φ_nonneg n i ξ
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
      integral_const_mul, setInt_phi_eq D hS n i] at hmono
    have e5 : (∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) +
      z / w * ((∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
        (∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ)) =
        (1 + z / w) * (∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
          z / w * (∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ) := by ring
    rw [e5]; linarith
  unfold F
  calc (∑ j, D.P i j * ∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) +
        z / w * ((∑ j, D.P i j * ∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
          ∑ j, D.P i j * ∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ)
      = ∑ j, D.P i j * ((∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) +
          z / w * ((∫ ξ in Set.Ioi 0, b j (y - ξ) * D.φ n i ξ) -
            (∫ ξ in Set.Ioi 0, b j ((y - w) - ξ) * D.φ n i ξ))) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, D.P i j * (Kj j + (∫ ξ in Set.Ioi 0, b j ((z + y) - ξ) * D.φ n i ξ)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hj j) (hS.P_nonneg i j))
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

lemma never_min (hnev : ∀ x u, 0 < u → g x ≤ K + g (x + u)) (x u : ℝ) (hu : 0 ≤ u) :
    g x ≤ K * delta u + g (x + u) := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, delta_zero]; simp
  · rw [delta_pos h, mul_one]; exact hnev x u h

lemma iInf_eq_of_min (f : {u : ℝ // 0 ≤ u} → ℝ) (u0 : {u : ℝ // 0 ≤ u})
    (h : ∀ u, f u0 ≤ f u) : ⨅ u, f u = f u0 :=
  le_antisymm (ciInf_le ⟨f u0, by rintro _ ⟨u, rfl⟩; exact h u⟩ u0) (le_ciInf h)

theorem child_ss_attains (K : ℝ) (hK : 0 ≤ K) (g : ℝ → ℝ) (hg : BertsekasKConvex K g)
    (hc : Continuous g) (hco : Tendsto g atTop atTop) :
    ∃ s S : EReal, s ≤ S ∧ S ≠ ⊤ ∧ (s ≠ ⊥ → S ≠ ⊥) ∧ ∀ x : ℝ,
      0 ≤ orderSS s S x ∧ ∀ u : ℝ, 0 ≤ u →
        K * delta (orderSS s S x) + g (x + orderSS s S x) ≤ K * delta u + g (x + u) := by
  rcases ss_dichotomy hg hc hco with hnev | ⟨s0, S0, hsS, hS0, heq, hlt, hmid, hright⟩
  · refine ⟨⊥, ⊥, le_rfl, bot_ne_top, fun h => absurd rfl h, fun x => ?_⟩
    have ho : orderSS ⊥ ⊥ x = 0 := by simp [orderSS]
    rw [ho, delta_zero, add_zero]
    exact ⟨le_rfl, fun u hu => by simpa using never_min hnev x u hu⟩
  · refine ⟨(s0 : EReal), (S0 : EReal), EReal.coe_le_coe_iff.2 hsS, EReal.coe_ne_top _,
      fun _ => EReal.coe_ne_bot _, fun x => ?_⟩
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

lemma H_kconvex (hg : BertsekasKConvex K g) (s0 S0 : ℝ) (hsS : s0 ≤ S0) (hS0 : ∀ y, g S0 ≤ g y)
    (heq : g s0 = K + g S0) (hmid : ∀ x, s0 ≤ x → x ≤ S0 → g x ≤ K + g S0)
    (hright : ∀ x u, s0 ≤ x → 0 < u → g x ≤ K + g (x + u)) :
    BertsekasKConvex K (fun x => g (max x s0)) := by
  intro z b y hz hb
  have hK0 : 0 ≤ K := by
    have hk := hg 0 1 y le_rfl one_pos
    simp at hk
    linarith
  have hc' := hS0 (max (z + y) s0)
  show g (max y s0) + z / b * (g (max y s0) - g (max (y - b) s0)) ≤ K + g (max (z + y) s0)
  by_cases hy : y < s0
  · rw [max_eq_right hy.le, max_eq_right (by linarith : y - b ≤ s0), heq]
    simp only [sub_self, mul_zero, add_zero]
    linarith
  · push Not at hy
    rw [max_eq_left hy, max_eq_left (by linarith : s0 ≤ z + y)]
    by_cases hyb : s0 ≤ y - b
    · rw [max_eq_left hyb]; exact hg z b y hz hb
    · push Not at hyb
      rw [max_eq_right hyb.le, heq]
      have hyz : g y ≤ K + g (z + y) := by
        rcases eq_or_lt_of_le hz with h | h
        · rw [← h, zero_add]
          have hk := hg 0 1 y le_rfl one_pos
          simp at hk
          linarith
        · have := hright y z hy h; rwa [add_comm y z] at this
      by_cases hgy : g y ≤ K + g S0
      · have : z / b * (g y - (K + g S0)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg hz hb.le) (by linarith)
        linarith
      · push Not at hgy
        have hyS : S0 < y := by
          by_contra h; push Not at h; linarith [hmid y hy h]
        have hk := hg z (y - S0) y hz (by linarith)
        have e : y - (y - S0) = S0 := by ring
        rw [e] at hk
        have hdiv : z / b ≤ z / (y - S0) :=
          div_le_div_of_nonneg_left hz (by linarith) (by linarith)
        have : z / b * (g y - (K + g S0)) ≤ z / (y - S0) * (g y - g S0) :=
          mul_le_mul hdiv (by linarith) (by linarith) (div_nonneg hz (by linarith))
        linarith

theorem child_h_props (K : ℝ) (hK : 0 ≤ K) (g : ℝ → ℝ) (hg : BertsekasKConvex K g)
    (hc : Continuous g) (hco : Tendsto g atTop atTop) :
    Continuous (fun x => ⨅ u : {u : ℝ // 0 ≤ u}, (K * delta u.1 + g (x + u.1))) ∧
      BertsekasKConvex K (fun x => ⨅ u : {u : ℝ // 0 ≤ u}, (K * delta u.1 + g (x + u.1))) := by
  rcases ss_dichotomy hg hc hco with hnev | ⟨s0, S0, hsS, hS0, heq, hlt, hmid, hright⟩
  · have e : (fun x => ⨅ u : {u : ℝ // 0 ≤ u}, (K * delta u.1 + g (x + u.1))) = g := by
      funext x
      rw [iInf_eq_of_min _ ⟨0, le_rfl⟩ (fun u => ?_)]
      · simp [delta_zero]
      · simpa [delta_zero] using never_min hnev x u.1 u.2
    rw [e]; exact ⟨hc, hg⟩
  · have e : (fun x => ⨅ u : {u : ℝ // 0 ≤ u}, (K * delta u.1 + g (x + u.1))) =
        fun x => g (max x s0) := by
      funext x
      by_cases hx : x < s0
      · have hpos : 0 < S0 - x := by linarith
        rw [iInf_eq_of_min _ ⟨S0 - x, hpos.le⟩ (fun u => ?_)]
        · show K * delta (S0 - x) + g (x + (S0 - x)) = g (max x s0)
          rw [max_eq_right hx.le, heq, delta_pos hpos, mul_one]
          ring_nf
        · show K * delta (S0 - x) + g (x + (S0 - x)) ≤ K * delta u.1 + g (x + u.1)
          have e : x + (S0 - x) = S0 := by ring
          rw [e, delta_pos hpos, mul_one]
          rcases eq_or_lt_of_le u.2 with h | h
          · rw [← h, delta_zero]; simp; linarith [hlt x hx]
          · rw [delta_pos h, mul_one]; linarith [hS0 (x + u.1)]
      · push Not at hx
        rw [iInf_eq_of_min _ ⟨0, le_rfl⟩ (fun u => ?_)]
        · show K * delta 0 + g (x + 0) = g (max x s0)
          rw [max_eq_left hx, delta_zero]; simp
        · show K * delta 0 + g (x + 0) ≤ K * delta u.1 + g (x + u.1)
          rw [delta_zero, mul_zero, zero_add, add_zero]
          rcases eq_or_lt_of_le u.2 with h | h
          · rw [← h, delta_zero]; simp
          · rw [delta_pos h, mul_one]; exact hright x u.1 hx h
    rw [e]
    exact ⟨hc.comp (continuous_id.max continuous_const),
      H_kconvex hg s0 S0 hsS hS0 heq hmid hright⟩

end SS

lemma kconvex_mono {K1 K2 : ℝ} {g : ℝ → ℝ} (h : BertsekasKConvex K1 g) (hK : K1 ≤ K2) :
    BertsekasKConvex K2 g := fun z b y hz hb => (h z b y hz hb).trans (by linarith)

lemma kconvex_add {K1 K2 : ℝ} {g1 g2 : ℝ → ℝ} (h1 : BertsekasKConvex K1 g1)
    (h2 : BertsekasKConvex K2 g2) : BertsekasKConvex (K1 + K2) (fun y => g1 y + g2 y) := by
  intro z b y hz hb
  have a1 := h1 z b y hz hb
  have a2 := h2 z b y hz hb
  have e : (z / b) * ((g1 y + g2 y) - (g1 (y - b) + g2 (y - b))) =
      (z / b) * (g1 y - g1 (y - b)) + (z / b) * (g2 y - g2 (y - b)) := by ring
  show g1 y + g2 y + (z / b) * ((g1 y + g2 y) - (g1 (y - b) + g2 (y - b))) ≤
    K1 + K2 + (g1 (z + y) + g2 (z + y))
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

lemma kconvex_of_convex {K : ℝ} (hK : 0 ≤ K) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) :
    BertsekasKConvex K g := by
  intro z b y hz hb
  rcases eq_or_lt_of_le hz with h0 | hz
  · rw [← h0, zero_div, zero_mul, add_zero, zero_add]; linarith
  have hs := hg.slope_mono_adjacent (x := y - b) (y := y) (z := z + y) trivial trivial
    (by linarith) (by linarith)
  have e1 : y - (y - b) = b := by ring
  have e2 : z + y - y = z := by ring
  rw [e1, e2] at hs
  have h3 : z / b * (g y - g (y - b)) ≤ g (z + y) - g y := by
    calc z / b * (g y - g (y - b)) = z * ((g y - g (y - b)) / b) := by ring
      _ ≤ z * ((g (z + y) - g y) / z) := mul_le_mul_of_nonneg_left hs hz.le
      _ = g (z + y) - g y := by field_simp
  linarith

lemma continuous_of_convex_univ {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) : Continuous g := by
  have := hg.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

lemma delta_nonneg (z : ℝ) : 0 ≤ delta z := by
  unfold delta; split_ifs <;> norm_num

lemma iInf_sub_const' {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : BddBelow (Set.range f))
    (c : ℝ) : ⨅ i, (f i - c) = (⨅ i, f i) - c := by
  have hf' : BddBelow (Set.range fun i => f i - c) := by
    obtain ⟨m, hm⟩ := hf
    refine ⟨m - c, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := hm ⟨j, rfl⟩
    simp only at this ⊢
    linarith
  apply le_antisymm
  · have : (⨅ i, (f i - c)) + c ≤ ⨅ i, f i := by
      apply le_ciInf; intro i
      have := ciInf_le hf' i
      linarith
    linarith
  · apply le_ciInf; intro i
    have := ciInf_le hf i
    linarith

/-! ## Verification (children C5, C6) -/

lemma snoc_lt' {α : Type*} {s : ℕ} (σ : Fin s → α) (j : α) (a : ℕ) (ha : a < s + 1) (h : a < s) :
    (Fin.snoc σ j : Fin (s + 1) → α) ⟨a, ha⟩ = σ ⟨a, h⟩ := by
  have : (⟨a, ha⟩ : Fin (s + 1)) = Fin.castSucc ⟨a, h⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma snoc_zero {α : Type*} {t : ℕ} (σ : Fin (t + 1) → α) (j : α) :
    (Fin.snoc σ j : Fin (t + 1 + 1) → α) 0 = σ 0 :=
  snoc_lt' σ j 0 (by omega) (by omega)

lemma initStates_snoc {L : ℕ} {t : ℕ} (σ : Fin (t + 1) → Fin L) (j : Fin L) (k : ℕ)
    (hk : k ≤ t + 1) (hk' : k ≤ t) :
    initStates (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) k hk = initStates σ k hk' := by
  funext a
  simp only [initStates]
  exact snoc_lt' σ j a.1 _ (by have := a.2; omega)

lemma initDemands_snoc {t : ℕ} (ξ : Fin t → ℝ) (z : ℝ) (k : ℕ) (hk : k ≤ t + 1) (hk' : k ≤ t) :
    initDemands (Fin.snoc ξ z : Fin (t + 1) → ℝ) k hk = initDemands ξ k hk' := by
  funext a
  simp only [initDemands]
  exact snoc_lt' ξ z a.1 _ (by have := a.2; omega)

lemma surplus_snoc {L : ℕ} (U : Policy L) (x : ℝ) {t : ℕ} (σ : Fin (t + 1) → Fin L) (j : Fin L)
    (ξ : Fin t → ℝ) (z : ℝ) :
    surplus U x (t + 1) (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (t + 1) → ℝ) =
      surplus U x t σ ξ + U t σ ξ - z := by
  simp only [surplus, Fin.init_snoc, Fin.snoc_last]

noncomputable def costTerm {L : ℕ} (D : Data L) (n : ℕ) (U : Policy L) (x : ℝ) {m : ℕ}
    (σ : Fin (m + 1) → Fin L) (ξ : Fin m → ℝ) (a : ℕ) (ha : a < m) : ℝ :=
  orderCost D (n + a) (σ ⟨a, by omega⟩) (U a (initStates σ a ha.le) (initDemands ξ a ha.le)) +
    D.f (n + a) (σ ⟨a, by omega⟩) (surplus U x a (initStates σ a ha.le) (initDemands ξ a ha.le))

noncomputable def partialCost {L : ℕ} (D : Data L) (n : ℕ) (U : Policy L) (x : ℝ) {m : ℕ}
    (σ : Fin (m + 1) → Fin L) (ξ : Fin m → ℝ) : ℝ :=
  ∑ k : Fin m, costTerm D n U x σ ξ k.1 k.2

lemma pathCost_eq {L : ℕ} (D : Data L) (N n : ℕ) (U : Policy L) (x : ℝ) {m : ℕ}
    (σ : Fin (m + 1) → Fin L) (ξ : Fin m → ℝ) :
    pathCost D N n U x σ ξ = partialCost D n U x σ ξ + D.f N (σ (Fin.last m)) (surplus U x m σ ξ) :=
  rfl

lemma costTerm_snoc {L : ℕ} (D : Data L) (n : ℕ) (U : Policy L) (x : ℝ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (j : Fin L) (ξ : Fin t → ℝ) (z : ℝ) (a : ℕ) (ha : a < t + 1)
    (ha' : a < t) :
    costTerm D n U x (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (t + 1) → ℝ) a ha =
      costTerm D n U x σ ξ a ha' := by
  unfold costTerm
  rw [initStates_snoc σ j a _ ha'.le, initDemands_snoc ξ z a _ ha'.le,
    snoc_lt' σ j a _ (by omega)]

lemma costTerm_last {L : ℕ} (D : Data L) (n : ℕ) (U : Policy L) (x : ℝ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (j : Fin L) (ξ : Fin t → ℝ) (z : ℝ) (ha : t < t + 1) :
    costTerm D n U x (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (t + 1) → ℝ) t ha =
      orderCost D (n + t) (σ (Fin.last t)) (U t σ ξ) +
        D.f (n + t) (σ (Fin.last t)) (surplus U x t σ ξ) := by
  unfold costTerm
  rw [initStates_snoc σ j t _ le_rfl, initDemands_snoc ξ z t _ le_rfl, snoc_lt' σ j t _ (by omega)]
  rfl

lemma partialCost_snoc {L : ℕ} (D : Data L) (n : ℕ) (U : Policy L) (x : ℝ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (j : Fin L) (ξ : Fin t → ℝ) (z : ℝ) :
    partialCost D n U x (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (t + 1) → ℝ) =
      partialCost D n U x σ ξ + (orderCost D (n + t) (σ (Fin.last t)) (U t σ ξ) +
        D.f (n + t) (σ (Fin.last t)) (surplus U x t σ ξ)) := by
  unfold partialCost
  rw [Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl (fun k _ => costTerm_snoc D n U x σ j ξ z k.1 _ k.2)
  · exact costTerm_last D n U x σ j ξ z _

lemma pathWeight_snoc {L : ℕ} (D : Data L) (n : ℕ) {t : ℕ} (σ : Fin (t + 1) → Fin L) (j : Fin L)
    (ξ : Fin t → ℝ) (z : ℝ) :
    pathWeight D n (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (t + 1) → ℝ) =
      pathWeight D n σ ξ * (D.P (σ (Fin.last t)) j * D.φ (n + t) (σ (Fin.last t)) z) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    have h1 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) k.castSucc.castSucc = σ k.castSucc :=
      Fin.snoc_castSucc ..
    have h2 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) k.castSucc.succ = σ k.succ := by
      show (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) ⟨k.1 + 1, by omega⟩ = σ ⟨k.1 + 1, by omega⟩
      exact snoc_lt' σ j _ _ _
    have h3 : (Fin.snoc ξ z : Fin (t + 1) → ℝ) k.castSucc = ξ k := Fin.snoc_castSucc ..
    simp only [h1, h2, h3, Fin.val_castSucc]
  · have h1 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.last t).castSucc = σ (Fin.last t) :=
      Fin.snoc_castSucc ..
    have h2 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.last t).succ = j := by
      show (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.last (t + 1)) = j
      exact Fin.snoc_last ..
    have h3 : (Fin.snoc ξ z : Fin (t + 1) → ℝ) (Fin.last t) = z := Fin.snoc_last ..
    simp only [h1, h2, h3, Fin.val_last]

lemma sum_snoc {L : ℕ} {t : ℕ} (f : (Fin (t + 1 + 1) → Fin L) → ℝ≥0∞) :
    ∑ σ', f σ' = ∑ σ : Fin (t + 1) → Fin L, ∑ j : Fin L, f (Fin.snoc σ j) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (t + 1 + 1) => Fin L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma snoc_symm_eq (t : ℕ) (p : ℝ × (Fin t → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)).symm p =
      (Fin.snoc p.2 p.1 : Fin (t + 1) → ℝ) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

lemma lintegral_snoc (t : ℕ) (G : (Fin (t + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ξ', G ξ' = ∫⁻ ξ : Fin t → ℝ, ∫⁻ z : ℝ, G (Fin.snoc ξ z : Fin (t + 1) → ℝ) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)
  have h1 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin t => (volume : Measure ℝ))) =
      ∫⁻ ξ', G ξ' := (MeasurePreserving.symm _ hmp).lintegral_comp hG
  have h2 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin t => (volume : Measure ℝ))) =
      ∫⁻ ξ, ∫⁻ z, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ)
        (Fin.last t)).symm (z, ξ)) ∂(volume : Measure ℝ)
        ∂(Measure.pi fun _ : Fin t => (volume : Measure ℝ)) :=
    lintegral_prod_symm _ (hG.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [← h1, h2]
  simp only [snoc_symm_eq]
  rfl

lemma meas_inner (t : ℕ) (G : (Fin (t + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    Measurable (fun ξ : Fin t → ℝ => ∫⁻ z : ℝ, G (Fin.snoc ξ z : Fin (t + 1) → ℝ)) := by
  have e : (fun p : ℝ × (Fin t → ℝ) => G (Fin.snoc p.2 p.1 : Fin (t + 1) → ℝ)) =
      G ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)).symm := by
    funext p; simp only [Function.comp_apply, snoc_symm_eq]
  have hm : Measurable (fun p : ℝ × (Fin t → ℝ) => G (Fin.snoc p.2 p.1 : Fin (t + 1) → ℝ)) := by
    rw [e]; exact hG.comp (MeasurableEquiv.measurable _)
  exact hm.lintegral_prod_left'

lemma meas_init {m : ℕ} : Measurable (fun ξ : Fin (m + 1) → ℝ => Fin.init ξ) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma meas_initDemands {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Measurable (fun ξ : Fin m → ℝ => initDemands ξ k hk) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma meas_surplus {L : ℕ} (U : Policy L) (x : ℝ) (T : ℕ)
    (hU : ∀ k < T, ∀ σ, Measurable (U k σ)) :
    ∀ k ≤ T, ∀ σ : Fin (k + 1) → Fin L, Measurable (surplus U x k σ) := by
  intro k
  induction k with
  | zero => intro _ σ; exact measurable_const
  | succ k ih =>
    intro hk σ
    exact (((ih (by omega) _).comp meas_init).add ((hU k (by omega) _).comp meas_init)).sub
      (measurable_pi_apply _)

lemma meas_fbSurplus {L : ℕ} (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hmeas : ∀ n i, Measurable (û n i)) :
    ∀ k, ∀ σ : Fin (k + 1) → Fin L, Measurable (fbSurplus û n x k σ) := by
  intro k
  induction k with
  | zero => intro σ; exact measurable_const
  | succ k ih =>
    intro σ
    exact (((ih _).comp meas_init).add ((hmeas _ _).comp ((ih _).comp meas_init))).sub
      (measurable_pi_apply _)

lemma meas_delta : Measurable delta := by
  unfold delta
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

lemma meas_orderCost {L : ℕ} (D : Data L) (k : ℕ) (j : Fin L) : Measurable (orderCost D k j) := by
  unfold orderCost
  exact (measurable_const.mul meas_delta).add (measurable_const.mul measurable_id)

lemma meas_partialCost {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) (U : Policy L) (x : ℝ)
    {t : ℕ} (hU : ∀ k < t, ∀ σ, Measurable (U k σ)) (σ : Fin (t + 1) → Fin L) :
    Measurable (fun ξ => partialCost D n U x σ ξ) := by
  unfold partialCost costTerm
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact ((meas_orderCost D _ _).comp ((hU k k.2 _).comp (meas_initDemands _ _))).add
    ((continuous_of_convex_univ (hS.f_convex _ _)).measurable.comp
      ((meas_surplus U x t hU k k.2.le _).comp (meas_initDemands _ _)))

lemma meas_pathWeight {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) : Measurable (fun ξ : Fin t → ℝ => pathWeight D n σ ξ) := by
  unfold pathWeight
  exact Finset.measurable_prod _ (fun k _ =>
    measurable_const.mul ((hS.φ_meas _ _).comp (measurable_pi_apply _)))

noncomputable def pathTerm {L : ℕ} (D : Data L) (N n : ℕ) (U : Policy L) (x : ℝ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (pathWeight D n σ ξ) *
    ENNReal.ofReal (partialCost D n U x σ ξ +
      dpV D N (n + t) (σ (Fin.last t)) (surplus U x t σ ξ))

lemma meas_pathTerm {L : ℕ} (D : Data L) (N n : ℕ) (hS : Standing D) (U : Policy L) (x : ℝ)
    {t : ℕ} (hU : ∀ k < t, ∀ σ, Measurable (U k σ)) (hV : ∀ j, Continuous (dpV D N (n + t) j))
    (σ : Fin (t + 1) → Fin L) : Measurable (pathTerm D N n U x σ) := by
  unfold pathTerm
  exact (ENNReal.measurable_ofReal.comp (meas_pathWeight D hS n σ)).mul
    (ENNReal.measurable_ofReal.comp ((meas_partialCost D hS n U x hU σ).add
      ((hV _).measurable.comp (meas_surplus U x t hU t le_rfl σ))))

noncomputable def phiSum {L : ℕ} (D : Data L) (N n : ℕ) (i : Fin L) (x : ℝ) (U : Policy L)
    (t : ℕ) : ℝ≥0∞ :=
  ∑ σ : Fin (t + 1) → Fin L, if σ 0 = i then ∫⁻ ξ : Fin t → ℝ, pathTerm D N n U x σ ξ else 0

lemma orderCost_nonneg {L : ℕ} (D : Data L) (hS : Standing D) {k : ℕ} {j : Fin L} {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ orderCost D k j u :=
  add_nonneg (mul_nonneg (hS.K_nonneg k j) (delta_nonneg u)) (mul_nonneg (hS.c_nonneg k j) hu)

lemma partialCost_nonneg {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) (U : Policy L) (x : ℝ)
    {t : ℕ} (hU : ∀ k < t, ∀ σ ξ, 0 ≤ U k σ ξ) (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ) :
    0 ≤ partialCost D n U x σ ξ := by
  unfold partialCost costTerm
  exact Finset.sum_nonneg (fun k _ => add_nonneg (orderCost_nonneg D hS (hU k k.2 _ _))
    (hS.f_nonneg _ _ _))

lemma pathWeight_nonneg {L : ℕ} (D : Data L) (hS : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ) : 0 ≤ pathWeight D n σ ξ := by
  unfold pathWeight
  exact Finset.prod_nonneg (fun k _ => mul_nonneg (hS.P_nonneg _ _) (hS.φ_nonneg _ _ _))

lemma F_nonneg {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (b : Fin L → ℝ → ℝ)
    (hb : ∀ j y, 0 ≤ b j y) (j0 : Fin L) (y : ℝ) : 0 ≤ F D k b j0 y :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hS.P_nonneg _ _)
    (setIntegral_nonneg measurableSet_Ioi (fun _ _ => mul_nonneg (hb _ _) (hS.φ_nonneg _ _ _))))

lemma dpV_succ {L : ℕ} (D : Data L) (N k : ℕ) (hk : k < N) (j : Fin L) (y : ℝ) :
    dpV D N k j y = D.f k j y + ⨅ u : {u : ℝ // 0 ≤ u},
      (orderCost D k j u + F D k (dpV D N (k + 1)) j (y + u)) := by
  have h1 : N - k = (N - (k + 1)) + 1 := by omega
  have h2 : N - (N - (k + 1) + 1) = k := by omega
  unfold dpV
  rw [h1]
  simp only [dpAux, h2]

lemma dp_le {L : ℕ} (D : Data L) (hS : Standing D) (N k : ℕ) (hk : k < N) (j : Fin L) (y u : ℝ)
    (hu : 0 ≤ u) (hF0 : ∀ y, 0 ≤ F D k (dpV D N (k + 1)) j y) :
    dpV D N k j y ≤ D.f k j y + (orderCost D k j u + F D k (dpV D N (k + 1)) j (y + u)) := by
  rw [dpV_succ D N k hk]
  have hb : BddBelow (Set.range fun v : {u : ℝ // 0 ≤ u} =>
      orderCost D k j v + F D k (dpV D N (k + 1)) j (y + v)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact add_nonneg (orderCost_nonneg D hS v.2) (hF0 _)
  have := ciInf_le hb ⟨u, hu⟩
  linarith

lemma inner_eq {L : ℕ} (D : Data L) (hS : Standing D) (k : ℕ) (j0 : Fin L)
    (V' : Fin L → ℝ → ℝ) (hc : ∀ j, Continuous (V' j)) (h0 : ∀ j y, 0 ≤ V' j y)
    (hg : ∀ j, ∃ Cb : ℝ, ∀ y, V' j y ≤ Cb * (1 + |y|)) (w A y : ℝ) (hw : 0 ≤ w) (hA : 0 ≤ A) :
    ∑ j, ∫⁻ z, ENNReal.ofReal (w * (D.P j0 j * D.φ k j0 z)) * ENNReal.ofReal (A + V' j (y - z)) =
      ENNReal.ofReal w * ENNReal.ofReal (A + F D k V' j0 y) := by
  have hj : ∀ j, ∫⁻ z, ENNReal.ofReal (w * (D.P j0 j * D.φ k j0 z)) *
      ENNReal.ofReal (A + V' j (y - z)) = ENNReal.ofReal w *
        ENNReal.ofReal (D.P j0 j * (A + ∫ z in Set.Ioi 0, V' j (y - z) * D.φ k j0 z)) := by
    intro j
    obtain ⟨Cb, hCb⟩ := hg j
    have hP := hS.P_nonneg j0 j
    have hsh := shift_integrable D hS k j0 (V' j) (hc j) (h0 j) Cb hCb y
    have hint : Integrable (fun z => A * D.φ k j0 z + V' j (y - z) * D.φ k j0 z) :=
      ((phi_integrable D hS k j0).const_mul A).add hsh
    have hnn : ∀ z, 0 ≤ A * D.φ k j0 z + V' j (y - z) * D.φ k j0 z := fun z =>
      add_nonneg (mul_nonneg hA (hS.φ_nonneg k j0 z)) (mul_nonneg (h0 j _) (hS.φ_nonneg k j0 z))
    have e1 : ∀ z, ENNReal.ofReal (w * (D.P j0 j * D.φ k j0 z)) * ENNReal.ofReal (A + V' j (y - z)) =
        ENNReal.ofReal w * ENNReal.ofReal (D.P j0 j) *
          ENNReal.ofReal (A * D.φ k j0 z + V' j (y - z) * D.φ k j0 z) := by
      intro z
      have hφ := hS.φ_nonneg k j0 z
      rw [show A * D.φ k j0 z + V' j (y - z) * D.φ k j0 z = D.φ k j0 z * (A + V' j (y - z)) by ring,
        ENNReal.ofReal_mul hw, ENNReal.ofReal_mul hP, ENNReal.ofReal_mul hφ]
      ring
    rw [lintegral_congr e1, lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
    have hIoi : ∫ z, (A * D.φ k j0 z + V' j (y - z) * D.φ k j0 z) =
        ∫ z in Set.Ioi 0, (A * D.φ k j0 z + V' j (y - z) * D.φ k j0 z) := by
      rw [← integral_Ici_eq_integral_Ioi]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [hS.φ_neg k j0 z (by simpa using hz)]; ring
    rw [hIoi, integral_add ((phi_integrable D hS k j0).const_mul A).integrableOn hsh.integrableOn,
      integral_const_mul, setInt_phi_eq D hS k j0, mul_one, mul_assoc, ← ENNReal.ofReal_mul hP]
  rw [Finset.sum_congr rfl (fun j _ => hj j), ← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
  · congr 2
    unfold F
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hS.P_sum j0, one_mul]
  · intro j _
    exact mul_nonneg (hS.P_nonneg j0 j) (add_nonneg hA (setIntegral_nonneg measurableSet_Ioi
      (fun z _ => mul_nonneg (h0 j _) (hS.φ_nonneg k j0 z))))

lemma phi_succ {L : ℕ} (D : Data L) (N n : ℕ) (hS : Standing D) (i : Fin L) (x : ℝ)
    (U : Policy L) (t : ℕ) (htN : n + t < N)
    (hreg : ∀ n ≤ N, ∀ i, Continuous (dpV D N n i) ∧ ∃ Cb : ℝ, ∀ x,
      0 ≤ dpV D N n i x ∧ dpV D N n i x ≤ Cb * (1 + |x|))
    (hU : ∀ k ≤ t, (∀ σ ξ, 0 ≤ U k σ ξ) ∧ ∀ σ, Measurable (U k σ)) :
    phiSum D N n i x U (t + 1) = ∑ σ : Fin (t + 1) → Fin L, if σ 0 = i then
      ∫⁻ ξ : Fin t → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) *
        ENNReal.ofReal (partialCost D n U x σ ξ + (orderCost D (n + t) (σ (Fin.last t)) (U t σ ξ) +
          D.f (n + t) (σ (Fin.last t)) (surplus U x t σ ξ)) +
          F D (n + t) (dpV D N (n + t + 1)) (σ (Fin.last t)) (surplus U x t σ ξ + U t σ ξ))
      else 0 := by
  have hVc : ∀ j, Continuous (dpV D N (n + (t + 1)) j) :=
    fun j => (hreg (n + (t + 1)) (by omega) j).1
  have hV0 : ∀ j y, 0 ≤ dpV D N (n + (t + 1)) j y :=
    fun j y => ((hreg (n + (t + 1)) (by omega) j).2.choose_spec y).1
  have hVg : ∀ j, ∃ Cb : ℝ, ∀ y, dpV D N (n + (t + 1)) j y ≤ Cb * (1 + |y|) :=
    fun j => ⟨_, fun y => ((hreg (n + (t + 1)) (by omega) j).2.choose_spec y).2⟩
  have hUm : ∀ k < t + 1, ∀ σ, Measurable (U k σ) := fun k hk => (hU k (by omega)).2
  have hU0 : ∀ k < t, ∀ σ ξ, 0 ≤ U k σ ξ := fun k hk => (hU k (by omega)).1
  have hmeasG : ∀ σ' : Fin (t + 1 + 1) → Fin L, Measurable (pathTerm D N n U x σ') :=
    fun σ' => meas_pathTerm D N n hS U x hUm hVc σ'
  unfold phiSum
  rw [sum_snoc]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [snoc_zero]
  by_cases h : σ 0 = i
  · simp only [if_pos h]
    have hsplit : ∀ j, ∫⁻ ξ', pathTerm D N n U x (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) ξ' =
        ∫⁻ ξ : Fin t → ℝ, ∫⁻ z : ℝ, pathTerm D N n U x (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L)
          (Fin.snoc ξ z : Fin (t + 1) → ℝ) := fun j => lintegral_snoc t _ (hmeasG _)
    rw [Finset.sum_congr rfl (fun j _ => hsplit j),
      ← lintegral_finsetSum Finset.univ (f := fun j ξ => ∫⁻ z : ℝ, pathTerm D N n U x
        (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (t + 1) → ℝ))
        (fun j _ => meas_inner t _ (hmeasG _))]
    refine lintegral_congr (fun ξ => ?_)
    have hpt : ∀ j z, pathTerm D N n U x (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L)
        (Fin.snoc ξ z : Fin (t + 1) → ℝ) =
        ENNReal.ofReal (pathWeight D n σ ξ * (D.P (σ (Fin.last t)) j *
          D.φ (n + t) (σ (Fin.last t)) z)) *
        ENNReal.ofReal ((partialCost D n U x σ ξ + (orderCost D (n + t) (σ (Fin.last t)) (U t σ ξ) +
          D.f (n + t) (σ (Fin.last t)) (surplus U x t σ ξ))) +
          dpV D N (n + (t + 1)) j ((surplus U x t σ ξ + U t σ ξ) - z)) := by
      intro j z
      unfold pathTerm
      rw [pathWeight_snoc, partialCost_snoc, surplus_snoc, Fin.snoc_last]
    simp only [hpt]
    exact inner_eq D hS (n + t) (σ (Fin.last t)) _ hVc hV0 hVg _ _ _
      (pathWeight_nonneg D hS n σ ξ)
      (add_nonneg (partialCost_nonneg D hS n U x hU0 σ ξ)
        (add_nonneg (orderCost_nonneg D hS ((hU t le_rfl).1 σ ξ)) (hS.f_nonneg _ _ _)))
  · simp only [if_neg h, Finset.sum_const_zero]

lemma phi_le_succ {L : ℕ} (D : Data L) (N n : ℕ) (hS : Standing D) (i : Fin L) (x : ℝ)
    (U : Policy L) (t : ℕ) (htN : n + t < N)
    (hreg : ∀ n ≤ N, ∀ i, Continuous (dpV D N n i) ∧ ∃ Cb : ℝ, ∀ x,
      0 ≤ dpV D N n i x ∧ dpV D N n i x ≤ Cb * (1 + |x|))
    (hU : ∀ k ≤ t, (∀ σ ξ, 0 ≤ U k σ ξ) ∧ ∀ σ, Measurable (U k σ)) :
    phiSum D N n i x U t ≤ phiSum D N n i x U (t + 1) := by
  rw [phi_succ D N n hS i x U t htN hreg hU]
  unfold phiSum
  refine Finset.sum_le_sum (fun σ _ => ?_)
  split_ifs
  · refine lintegral_mono (fun ξ => ?_)
    unfold pathTerm
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    have hFn : ∀ y, 0 ≤ F D (n + t) (dpV D N (n + t + 1)) (σ (Fin.last t)) y :=
      fun y => F_nonneg D hS _ _ (fun j y => ((hreg (n + t + 1) (by omega) j).2.choose_spec y).1) _ _
    have := dp_le D hS N (n + t) htN (σ (Fin.last t)) (surplus U x t σ ξ) (U t σ ξ)
      ((hU t le_rfl).1 σ ξ) hFn
    linarith
  · exact le_rfl

lemma surplus_feedback {L : ℕ} (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    ∀ t σ ξ, surplus (feedback û n x) x t σ ξ = fbSurplus û n x t σ ξ := by
  intro t
  induction t with
  | zero => intro σ ξ; rfl
  | succ t ih =>
    intro σ ξ
    simp only [surplus, fbSurplus, ih]
    rfl

lemma phi_eq_succ_fb {L : ℕ} (D : Data L) (N n : ℕ) (hS : Standing D) (i : Fin L) (x : ℝ)
    (û : ℕ → Fin L → ℝ → ℝ) (hmeas : ∀ n i, Measurable (û n i))
    (h0 : ∀ n < N, ∀ i x, 0 ≤ û n i x)
    (hatt : ∀ n < N, ∀ i x, ∀ u : ℝ, 0 ≤ u →
      orderCost D n i (û n i x) + F D n (dpV D N (n + 1)) i (x + û n i x) ≤
        orderCost D n i u + F D n (dpV D N (n + 1)) i (x + u))
    (t : ℕ) (htN : n + t < N)
    (hreg : ∀ n ≤ N, ∀ i, Continuous (dpV D N n i) ∧ ∃ Cb : ℝ, ∀ x,
      0 ≤ dpV D N n i x ∧ dpV D N n i x ≤ Cb * (1 + |x|)) :
    phiSum D N n i x (feedback û n x) t = phiSum D N n i x (feedback û n x) (t + 1) := by
  have hU : ∀ k ≤ t, (∀ σ ξ, 0 ≤ feedback û n x k σ ξ) ∧
      ∀ σ, Measurable (feedback û n x k σ) :=
    fun k hk => ⟨fun σ ξ => h0 (n + k) (by omega) _ _,
      fun σ => (hmeas _ _).comp (meas_fbSurplus û n x hmeas k σ)⟩
  rw [phi_succ D N n hS i x _ t htN hreg hU]
  unfold phiSum
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  split_ifs
  · refine lintegral_congr (fun ξ => ?_)
    unfold pathTerm
    congr 2
    have hfb : feedback û n x t σ ξ = û (n + t) (σ (Fin.last t)) (fbSurplus û n x t σ ξ) := rfl
    rw [surplus_feedback, hfb, dpV_succ D N (n + t) htN,
      iInf_eq_of_min (fun u : {u : ℝ // 0 ≤ u} => orderCost D (n + t) (σ (Fin.last t)) u.1 +
        F D (n + t) (dpV D N (n + t + 1)) (σ (Fin.last t)) (fbSurplus û n x t σ ξ + u.1))
        ⟨û (n + t) (σ (Fin.last t)) (fbSurplus û n x t σ ξ), h0 _ htN _ _⟩
        (fun u => hatt (n + t) htN _ _ u.1 u.2)]
    ring
  · rfl

lemma phi_zero {L : ℕ} (D : Data L) (N n : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) :
    phiSum D N n i x U 0 = ENNReal.ofReal (dpV D N n i x) := by
  unfold phiSum
  rw [Finset.sum_eq_single (fun _ => i)]
  · have hconst : ∀ ξ : Fin 0 → ℝ, pathTerm D N n U x (fun _ => i) ξ =
        ENNReal.ofReal (dpV D N n i x) := by
      intro ξ; simp [pathTerm, pathWeight, partialCost, surplus]
    have hv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
        Measure.pi_univ]
      simp
    simp only [if_true, lintegral_congr hconst, lintegral_const, hv, mul_one]
  · intro σ _ hne
    rw [if_neg]
    intro h
    apply hne
    funext a
    rw [Fin.fin_one_eq_zero a]
    exact h
  · intro h; exact absurd (Finset.mem_univ _) h

lemma phi_last {L : ℕ} (D : Data L) (N n : ℕ) (hn : n ≤ N) (i : Fin L) (x : ℝ) (U : Policy L) :
    phiSum D N n i x U (N - n) = J D N n i x U := by
  unfold phiSum J
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  split_ifs
  · refine lintegral_congr (fun ξ => ?_)
    unfold pathTerm
    rw [pathCost_eq]
    have h1 : n + (N - n) = N := by omega
    have h2 : dpV D N N = D.f N := by simp [dpV, dpAux]
    rw [h1, h2]
  · rfl

theorem child_lower_bound {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D)
    (hreg : ∀ n ≤ N, ∀ i, Continuous (dpV D N n i) ∧ ∃ Cb : ℝ, ∀ x,
      0 ≤ dpV D N n i x ∧ dpV D N n i x ≤ Cb * (1 + |x|))
    (n : ℕ) (hn : n ≤ N) (i : Fin L) (x : ℝ) (U : Policy L) (hU : Admissible (N - n) U) :
    ENNReal.ofReal (dpV D N n i x) ≤ J D N n i x U := by
  have chain : ∀ t ≤ N - n, phiSum D N n i x U 0 ≤ phiSum D N n i x U t := by
    intro t
    induction t with
    | zero => intro _; exact le_rfl
    | succ t ih =>
      intro ht
      exact (ih (by omega)).trans (phi_le_succ D N n hS i x U t (by omega) hreg
        (fun k hk => hU k (by omega)))
  rw [← phi_zero D N n i x U, ← phi_last D N n hn i x U]
  exact chain _ le_rfl

theorem child_feedback_cost {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D)
    (hreg : ∀ n ≤ N, ∀ i, Continuous (dpV D N n i) ∧ ∃ Cb : ℝ, ∀ x,
      0 ≤ dpV D N n i x ∧ dpV D N n i x ≤ Cb * (1 + |x|))
    (û : ℕ → Fin L → ℝ → ℝ) (hmeas : ∀ n i, Measurable (û n i))
    (h0 : ∀ n < N, ∀ i x, 0 ≤ û n i x)
    (hatt : ∀ n < N, ∀ i x, ∀ u : ℝ, 0 ≤ u →
      orderCost D n i (û n i x) + F D n (dpV D N (n + 1)) i (x + û n i x) ≤
        orderCost D n i u + F D n (dpV D N (n + 1)) i (x + u))
    (n : ℕ) (hn : n ≤ N) (i : Fin L) (x : ℝ) :
    Admissible (N - n) (feedback û n x) ∧
      J D N n i x (feedback û n x) = ENNReal.ofReal (dpV D N n i x) := by
  refine ⟨fun t ht => ⟨fun σ ξ => h0 (n + t) (by omega) _ _,
    fun σ => (hmeas _ _).comp (meas_fbSurplus û n x hmeas t σ)⟩, ?_⟩
  have chain : ∀ t ≤ N - n, phiSum D N n i x (feedback û n x) t =
      phiSum D N n i x (feedback û n x) 0 := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [← ih (by omega)]
      exact (phi_eq_succ_fb D N n hS i x û hmeas h0 hatt t (by omega) hreg).symm
  rw [← phi_last D N n hn i x, chain _ le_rfl, phi_zero]

lemma z_props_of {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D) (h41 : Cond41 D N)
    (h42 : Cond42 D N) (n : ℕ) (hn : n < N) (v : Fin L → ℝ → ℝ) (Cb : ℝ)
    (hv0 : ∀ i x, 0 ≤ v i x) (hvg : ∀ i x, v i x ≤ Cb * (1 + |x|))
    (hvf : ∀ i x, D.f (n + 1) i x ≤ v i x) (hvc : ∀ i, Continuous (v i))
    (hvk : ∀ i, BertsekasKConvex (D.K (n + 1) i) (v i)) (i : Fin L) :
    Continuous (fun y => D.c n i * y + F D n v i y) ∧
      BertsekasKConvex (D.K n i) (fun y => D.c n i * y + F D n v i y) ∧
      Tendsto (fun y => D.c n i * y + F D n v i y) atTop atTop := by
  obtain ⟨C', _, hF⟩ := child_F_regular D hS n v hvc hv0 Cb hvg
  obtain ⟨hFc, _, _, hFm⟩ := hF i
  refine ⟨(continuous_const.mul continuous_id).add hFc, ?_, ?_⟩
  · apply kconvex_linear
    exact kconvex_mono (child_F_kconvex D hS n v hvc hv0 Cb hvg (fun j => D.K (n + 1) j) hvk i)
      (h41 n hn i).1
  · refine tendsto_atTop_mono (fun y => ?_) (h42 n hn i)
    have := hFm (D.f (n + 1)) (fun j y => hS.f_nonneg _ _ _) hvf y
    linarith

theorem dp_props {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D) (h41 : Cond41 D N)
    (h42 : Cond42 D N) :
    ∀ m ≤ N, (∃ Cb : ℝ, ∀ i x, 0 ≤ dpAux D N m i x ∧ dpAux D N m i x ≤ Cb * (1 + |x|) ∧
        D.f (N - m) i x ≤ dpAux D N m i x) ∧
      ∀ i, Continuous (dpAux D N m i) ∧ BertsekasKConvex (D.K (N - m) i) (dpAux D N m i) := by
  have : Nonempty {u : ℝ // 0 ≤ u} := ⟨⟨0, le_rfl⟩⟩
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨⟨D.C, fun i x => ⟨hS.f_nonneg _ _ _, hS.f_growth _ _ _, le_rfl⟩⟩, fun i => ⟨?_, ?_⟩⟩
    · exact continuous_of_convex_univ (hS.f_convex N i)
    · exact kconvex_of_convex (hS.K_nonneg _ _) (hS.f_convex N i)
  | succ m ih =>
    intro hm
    obtain ⟨⟨Cb, hb⟩, hci⟩ := ih (by omega)
    have hn : N - (m + 1) < N := by omega
    have hn1 : N - (m + 1) + 1 = N - m := by omega
    have hz := fun i => z_props_of D N hS h41 h42 (N - (m + 1)) hn (dpAux D N m) Cb
      (fun i x => (hb i x).1) (fun i x => (hb i x).2.1)
      (fun i x => by rw [hn1]; exact (hb i x).2.2) (fun i => (hci i).1)
      (fun i => by rw [hn1]; exact (hci i).2) i
    obtain ⟨C', hC', hF⟩ := child_F_regular D hS (N - (m + 1)) (dpAux D N m) (fun i => (hci i).1)
      (fun i x => (hb i x).1) Cb (fun i x => (hb i x).2.1)
    have hunf : ∀ i x, dpAux D N (m + 1) i x = D.f (N - (m + 1)) i x +
        ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D (N - (m + 1)) i u +
          F D (N - (m + 1)) (dpAux D N m) i (x + u)) := fun i x => rfl
    have hbdd : ∀ i x, BddBelow (Set.range fun u : {u : ℝ // 0 ≤ u} =>
        orderCost D (N - (m + 1)) i u + F D (N - (m + 1)) (dpAux D N m) i (x + u)) := by
      intro i x
      refine ⟨0, ?_⟩
      rintro _ ⟨u, rfl⟩
      have := (hF i).2.1 (x + u)
      have := delta_nonneg u.1
      have := hS.K_nonneg (N - (m + 1)) i
      have := hS.c_nonneg (N - (m + 1)) i
      have := u.2
      simp only [orderCost]
      positivity
    have hinf0 : ∀ i x, 0 ≤ ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D (N - (m + 1)) i u +
          F D (N - (m + 1)) (dpAux D N m) i (x + u)) := by
      intro i x
      apply le_ciInf
      intro u
      have := (hF i).2.1 (x + u)
      have := delta_nonneg u.1
      have := hS.K_nonneg (N - (m + 1)) i
      have := hS.c_nonneg (N - (m + 1)) i
      have := u.2
      simp only [orderCost]
      positivity
    have key : ∀ i x, dpAux D N (m + 1) i x = D.f (N - (m + 1)) i x +
        (-(D.c (N - (m + 1)) i) * x + ⨅ u : {u : ℝ // 0 ≤ u}, (D.K (N - (m + 1)) i * delta u.1 +
          (D.c (N - (m + 1)) i * (x + u.1) + F D (N - (m + 1)) (dpAux D N m) i (x + u.1)))) := by
      intro i x
      rw [hunf]
      have e : (fun u : {u : ℝ // 0 ≤ u} => orderCost D (N - (m + 1)) i u +
          F D (N - (m + 1)) (dpAux D N m) i (x + u)) = fun u => (D.K (N - (m + 1)) i * delta u.1 +
          (D.c (N - (m + 1)) i * (x + u.1) + F D (N - (m + 1)) (dpAux D N m) i (x + u.1))) -
            D.c (N - (m + 1)) i * x := by
        funext u; simp only [orderCost]; ring
      have hb2 : BddBelow (Set.range fun u : {u : ℝ // 0 ≤ u} => (D.K (N - (m + 1)) i * delta u.1 +
          (D.c (N - (m + 1)) i * (x + u.1) + F D (N - (m + 1)) (dpAux D N m) i (x + u.1)))) := by
        obtain ⟨lb, hlb⟩ := hbdd i x
        refine ⟨lb + D.c (N - (m + 1)) i * x, ?_⟩
        rintro _ ⟨u, rfl⟩
        have := hlb ⟨u, rfl⟩
        simp only [orderCost] at this ⊢
        nlinarith
      rw [e, iInf_sub_const' _ hb2]
      ring
    refine ⟨⟨D.C + C', fun i x => ⟨?_, ?_, ?_⟩⟩, fun i => ⟨?_, ?_⟩⟩
    · rw [hunf]; have := hS.f_nonneg (N - (m + 1)) i x; have := hinf0 i x; linarith
    · rw [hunf]
      have h1 : (⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D (N - (m + 1)) i u +
          F D (N - (m + 1)) (dpAux D N m) i (x + u))) ≤
          orderCost D (N - (m + 1)) i 0 + F D (N - (m + 1)) (dpAux D N m) i (x + 0) :=
        ciInf_le (hbdd i x) ⟨0, le_rfl⟩
      have h0' : orderCost D (N - (m + 1)) i 0 = 0 := by simp [orderCost, delta]
      rw [h0', add_zero, zero_add] at h1
      have := hS.f_growth (N - (m + 1)) i x
      have := (hF i).2.2.1 x
      have : 0 ≤ 1 + |x| := by positivity
      nlinarith
    · rw [hunf, show N - (m + 1) = N - (m + 1) from rfl]; have := hinf0 i x; linarith
    · obtain ⟨hzc, hzk, hzt⟩ := hz i
      have hh := (child_h_props (D.K (N - (m + 1)) i) (hS.K_nonneg _ _) _ hzk hzc hzt).1
      have : dpAux D N (m + 1) i = fun x => D.f (N - (m + 1)) i x +
          (-(D.c (N - (m + 1)) i) * x + ⨅ u : {u : ℝ // 0 ≤ u}, (D.K (N - (m + 1)) i * delta u.1 +
          (D.c (N - (m + 1)) i * (x + u.1) + F D (N - (m + 1)) (dpAux D N m) i (x + u.1)))) :=
        funext (key i)
      rw [this]
      exact (continuous_of_convex_univ (hS.f_convex _ i)).add
        ((continuous_const.mul continuous_id).add hh)
    · obtain ⟨hzc, hzk, hzt⟩ := hz i
      have hh := (child_h_props (D.K (N - (m + 1)) i) (hS.K_nonneg _ _) _ hzk hzc hzt).2
      have : dpAux D N (m + 1) i = fun x => D.f (N - (m + 1)) i x +
          (-(D.c (N - (m + 1)) i) * x + ⨅ u : {u : ℝ // 0 ≤ u}, (D.K (N - (m + 1)) i * delta u.1 +
          (D.c (N - (m + 1)) i * (x + u.1) + F D (N - (m + 1)) (dpAux D N m) i (x + u.1)))) :=
        funext (key i)
      rw [this]
      have := kconvex_add (kconvex_of_convex le_rfl (hS.f_convex (N - (m + 1)) i))
        (kconvex_linear (-(D.c (N - (m + 1)) i)) hh)
      rw [zero_add] at this
      exact this

theorem main_4_1 {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D)
    (h41 : Cond41 D N) (h42 : Cond42 D N) :
    ∃ s S : ℕ → Fin L → EReal,
      (∀ n < N, ∀ i, s n i ≤ S n i ∧ S n i ≠ ⊤ ∧ (s n i ≠ ⊥ → S n i ≠ ⊥)) ∧
      (∀ n < N, ∀ i x,
        0 ≤ orderSS (s n i) (S n i) x ∧
        orderCost D n i (orderSS (s n i) (S n i) x) +
            F D n (dpV D N (n + 1)) i (x + orderSS (s n i) (S n i) x) =
          ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D n i u + F D n (dpV D N (n + 1)) i (x + u))) ∧
      (∀ i x,
        Admissible N (feedback (fun n i y => orderSS (s n i) (S n i) y) 0 x) ∧
        J D N 0 i x (feedback (fun n i y => orderSS (s n i) (S n i) y) 0 x) =
          value D N 0 i x) := by
  have : Nonempty {u : ℝ // 0 ≤ u} := ⟨⟨0, le_rfl⟩⟩
  have hdp := dp_props D N hS h41 h42
  have hreg : ∀ n ≤ N, ∀ i, Continuous (dpV D N n i) ∧ ∃ Cb : ℝ, ∀ x,
      0 ≤ dpV D N n i x ∧ dpV D N n i x ≤ Cb * (1 + |x|) := by
    intro n hn i
    obtain ⟨⟨Cb, hb⟩, hc⟩ := hdp (N - n) (by omega)
    exact ⟨(hc i).1, Cb, fun x => ⟨(hb i x).1, (hb i x).2.1⟩⟩
  have hz : ∀ n < N, ∀ i, Continuous (zFun D N n i) ∧ BertsekasKConvex (D.K n i) (zFun D N n i) ∧
      Tendsto (zFun D N n i) atTop atTop := by
    intro n hn i
    obtain ⟨⟨Cb, hb⟩, hc⟩ := hdp (N - (n + 1)) (by omega)
    have e : N - (N - (n + 1)) = n + 1 := by omega
    exact z_props_of D N hS h41 h42 n hn (dpV D N (n + 1)) Cb (fun i x => (hb i x).1)
      (fun i x => (hb i x).2.1) (fun i x => by have := (hb i x).2.2; rw [e] at this; exact this)
      (fun i => (hc i).1) (fun i => by have := (hc i).2; rw [e] at this; exact this) i
  have hss : ∀ n i, ∃ s S : EReal, n < N → (s ≤ S ∧ S ≠ ⊤ ∧ (s ≠ ⊥ → S ≠ ⊥) ∧ ∀ x : ℝ,
      0 ≤ orderSS s S x ∧ ∀ u : ℝ, 0 ≤ u →
        D.K n i * delta (orderSS s S x) + zFun D N n i (x + orderSS s S x) ≤
          D.K n i * delta u + zFun D N n i (x + u)) := by
    intro n i
    by_cases hn : n < N
    · obtain ⟨hc, hk, ht⟩ := hz n hn i
      obtain ⟨s, S, h⟩ := child_ss_attains (D.K n i) (hS.K_nonneg n i) (zFun D N n i) hk hc ht
      exact ⟨s, S, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hn⟩
  choose s S hsS using hss
  have hmin : ∀ n < N, ∀ i x, ∀ u : ℝ, 0 ≤ u →
      orderCost D n i (orderSS (s n i) (S n i) x) +
          F D n (dpV D N (n + 1)) i (x + orderSS (s n i) (S n i) x) ≤
        orderCost D n i u + F D n (dpV D N (n + 1)) i (x + u) := by
    intro n hn i x u hu
    have := ((hsS n i hn).2.2.2 x).2 u hu
    simp only [zFun] at this
    simp only [orderCost]
    linarith [mul_add (D.c n i) x (orderSS (s n i) (S n i) x), mul_add (D.c n i) x u]
  have hu_meas : ∀ n i, Measurable (fun y => orderSS (s n i) (S n i) y) := by
    intro n i
    unfold orderSS
    refine Measurable.ite ?_ (measurable_const.sub measurable_id) measurable_const
    exact measurableSet_Iio.preimage measurable_coe_real_ereal
  refine ⟨s, S, fun n hn i => ⟨(hsS n i hn).1, (hsS n i hn).2.1, (hsS n i hn).2.2.1⟩,
    fun n hn i x => ⟨((hsS n i hn).2.2.2 x).1, ?_⟩, fun i x => ?_⟩
  · apply le_antisymm
    · exact le_ciInf (fun u => hmin n hn i x u.1 u.2)
    · refine ciInf_le ?_ (⟨orderSS (s n i) (S n i) x, ((hsS n i hn).2.2.2 x).1⟩ : {u : ℝ // 0 ≤ u})
      refine ⟨orderCost D n i (orderSS (s n i) (S n i) x) +
          F D n (dpV D N (n + 1)) i (x + orderSS (s n i) (S n i) x), ?_⟩
      rintro _ ⟨u, rfl⟩
      exact hmin n hn i x u.1 u.2
  · have h6 := child_feedback_cost D N hS hreg (fun n i y => orderSS (s n i) (S n i) y) hu_meas
      (fun n hn i x => ((hsS n i hn).2.2.2 x).1) hmin 0 (Nat.zero_le _) i x
    refine ⟨by simpa using h6.1, ?_⟩
    unfold value
    apply le_antisymm
    · rw [h6.2]
      exact le_iInf₂ (fun U hU => child_lower_bound D N hS hreg 0 (Nat.zero_le _) i x U hU)
    · exact iInf₂_le _ h6.1

end SethiChengSS.Finite

open SethiChengSS SethiChengSS.Finite in open MeasureTheory Filter Topology in
theorem solution {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D)
    (h41 : Cond41 D N) (h42 : Cond42 D N) :
    ∃ s S : ℕ → Fin L → EReal,
      (∀ n < N, ∀ i, s n i ≤ S n i ∧ S n i ≠ ⊤ ∧ (s n i ≠ ⊥ → S n i ≠ ⊥)) ∧
      (∀ n < N, ∀ i x,
        0 ≤ orderSS (s n i) (S n i) x ∧
        orderCost D n i (orderSS (s n i) (S n i) x) +
            F D n (dpV D N (n + 1)) i (x + orderSS (s n i) (S n i) x) =
          ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D n i u + F D n (dpV D N (n + 1)) i (x + u))) ∧
      (∀ i x,
        Admissible N (feedback (fun n i y => orderSS (s n i) (S n i) y) 0 x) ∧
        J D N 0 i x (feedback (fun n i y => orderSS (s n i) (S n i) y) 0 x) =
          value D N 0 i x) := by
  exact SethiChengSS.Finite.main_4_1 D N hS h41 h42
