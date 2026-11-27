-- Prove2me | solution 1 for SethiChengSS.Finite.Supplement.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:46:28.813568+00:00
-- url     : https://prove2.me/submissions/08f6c405-c9ff-4a70-837c-c46a9a57f728

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Supplement_Capacity

open SethiChengSS
open SethiChengSS.Finite
open SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 5.3, p. 936: all threshold bounds and optimality on the entire half-line.
The (4.1) hypothesis is inherited from the induction explicitly invoked in the proof. -/
theorem solution {L : ℕ} (D : Data L) (T : ServiceData) (N : ℕ)
    (hD : Standing D) (hT : ServiceFeasible D T N) (h41 : Cond41 D N) :
    ∃ s S : ℕ → Fin L → ℝ,
      (∀ n < N, ∀ i, serviceA D T n i ≤ s n i ∧ s n i ≤ S n i ∧ S n i ≤ T.B) ∧
      (∀ n < N, InB0 (capRule T s S n)) ∧
      (∀ n < N, ∀ i x, x ≤ T.B →
        capAction D T n i x (capRule T s S n i x) ∧
        capV D T N n i x = D.f n i x + orderCost D n i (capRule T s S n i x) +
          F D n (capV D T N (n + 1)) i (x + capRule T s S n i x) ∧
        ∀ u : ℝ, capAction D T n i x u →
          orderCost D n i (capRule T s S n i x) +
              F D n (capV D T N (n + 1)) i (x + capRule T s S n i x) ≤
          orderCost D n i u + F D n (capV D T N (n + 1)) i (x + u)) ∧
      (∀ n ≤ N, ∀ i x, x ≤ T.B →
        CapAdmissible D T N n i x (feedback (capRule T s S) n x) ∧
        0 ≤ capV D T N n i x ∧
        J D N n i x (feedback (capRule T s S) n x) = ENNReal.ofReal (capV D T N n i x) ∧
        capValue D T N n i x = ENNReal.ofReal (capV D T N n i x) ∧
        ∀ U : Policy L, CapAdmissible D T N n i x U →
          J D N n i x (feedback (capRule T s S) n x) ≤ J D N n i x U) := by
            classical
            obtain ⟨V, hVdef⟩ : ∃ V, V = capV D T N := ⟨_, rfl⟩
            rw [← hVdef]
            have hVsucc : ∀ n < N, ∀ i x, V n i x = D.f n i x - D.c n i * x +
                sInf (capObjective D n (V (n+1)) i x '' capLevels D T n i x) := by
              intro n hn i x
              have h1 : N - n = (N - (n+1)) + 1 := by omega
              have h2 : N - ((N - (n+1)) + 1) = n := by omega
              subst hVdef
              simp only [capV, h1, capAux, h2]
            have hVN : ∀ i x, V N i x = D.f N i x := by
              intro i x; subst hVdef; simp [capV, capAux]
            have hFnn : ∀ n (b : Fin L → ℝ → ℝ) i y, (∀ j w, w ≤ y → 0 ≤ b j w) → 0 ≤ F D n b i y := by
              intro n b i y hb
              apply Finset.sum_nonneg
              intro j _
              apply mul_nonneg (hD.P_nonneg i j)
              apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
              intro z hz
              exact mul_nonneg (hb j _ (by linarith [show (0:ℝ) < z from hz])) (hD.φ_nonneg n i z)
            have hVnn : ∀ k n, n + k = N → ∀ i x, x ≤ T.B → 0 ≤ V n i x := by
              intro k
              induction k with
              | zero => intro n hn i x _; rw [show n = N by omega, hVN]; exact hD.f_nonneg N i x
              | succ k ih =>
                intro n hnk i x hx
                have hn : n < N := by omega
                rw [hVsucc n hn i x]
                have hne : (capObjective D n (V (n+1)) i x '' capLevels D T n i x).Nonempty :=
                  ⟨_, max x (serviceA D T n i), ⟨le_max_left _ _, le_max_right _ _,
                    max_le hx (hT.2.2 n hn i)⟩, rfl⟩
                have : D.c n i * x ≤ sInf (capObjective D n (V (n+1)) i x '' capLevels D T n i x) := by
                  apply le_csInf hne
                  rintro _ ⟨y, hy, rfl⟩
                  have hd : 0 ≤ delta (y - x) := by unfold delta; split_ifs <;> norm_num
                  have h1 : 0 ≤ D.K n i * delta (y - x) := mul_nonneg (hD.K_nonneg n i) hd
                  have h2 : D.c n i * x ≤ D.c n i * y := mul_le_mul_of_nonneg_left hy.1 (hD.c_nonneg n i)
                  have h3 : 0 ≤ F D n (V (n+1)) i y :=
                    hFnn n _ i y (fun j w hw => ih (n+1) (by omega) j w (hw.trans hy.2.2))
                  simp only [capObjective]; linarith
                linarith [hD.f_nonneg n i x]
            have hInt : ∀ (b : ℝ → ℝ) (C : ℝ), LowerSemicontinuousOn b (Set.Iic T.B) →
                (∀ x ≤ T.B, 0 ≤ b x) → (∀ x ≤ T.B, b x ≤ C * (1 + |x|)) →
                ∀ n i y, y ≤ T.B → Integrable (fun z => b (y - z) * D.φ n i z)
                  (volume.restrict (Set.Ioi 0)) := by
              intro b C hl h0 hC n i y hy
              have hC0 : 0 ≤ C := by
                have h1 := (h0 T.B le_rfl).trans (hC T.B le_rfl)
                have : 0 < 1 + |T.B| := add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _)
                exact (mul_nonneg_iff_of_pos_right this).mp h1
              have hW : LowerSemicontinuous (fun x => b (min x T.B)) := by
                have := hl.comp (g := fun x => min x T.B) (t := Set.univ)
                  (continuous_id.min continuous_const).continuousOn (fun x _ => min_le_right x T.B)
                exact lowerSemicontinuousOn_univ_iff.mp this
              have hWm : Measurable (fun x => b (min x T.B)) := hW.measurable
              have hφi : Integrable (D.φ n i) := by
                apply Integrable.of_integral_ne_zero; rw [hD.φ_int]; norm_num
              have hmeas : AEStronglyMeasurable (fun z => b (y - z) * D.φ n i z)
                  (volume.restrict (Set.Ioi 0)) := by
                have : AEStronglyMeasurable (fun z => b (min (y - z) T.B) * D.φ n i z)
                    (volume.restrict (Set.Ioi 0)) :=
                  ((hWm.comp (measurable_const.sub measurable_id)).mul (hD.φ_meas n i)).aestronglyMeasurable
                refine this.congr ?_
                filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
                have : y - z ≤ T.B := by have : (0:ℝ) < z := hz; linarith
                simp [min_eq_left this]
              refine Integrable.mono' (g := fun z => C * (1 + |y|) * D.φ n i z + C * (z * D.φ n i z))
                ((hφi.const_mul _).add ((hD.mean_integrable n i).const_mul _)).integrableOn hmeas ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
              have hz0 : (0:ℝ) < z := hz
              have hyz : y - z ≤ T.B := by linarith
              have hφ := hD.φ_nonneg n i z
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 _ hyz) hφ)]
              have h1 : b (y - z) ≤ C * (1 + |y|) + C * z := by
                have h2 := hC _ hyz
                have : |y - z| ≤ |y| + z := by
                  calc |y - z| ≤ |y| + |z| := abs_sub _ _
                    _ = |y| + z := by rw [abs_of_pos hz0]
                have := mul_le_mul_of_nonneg_left this hC0
                linarith
              have := mul_le_mul_of_nonneg_right h1 hφ
              linarith
            have hFK : ∀ n (b : Fin L → ℝ → ℝ) (Kj : Fin L → ℝ), (∀ j, 0 ≤ Kj j) →
                (∀ j, KConvexOn (Kj j) (Set.Iic T.B) (b j)) →
                (∀ i j y, y ≤ T.B → Integrable (fun z => b j (y - z) * D.φ n i z)
                  (volume.restrict (Set.Ioi 0))) →
                ∀ i, KConvexOn (∑ j, D.P i j * Kj j) (Set.Iic T.B) (F D n b i) := by
              intro n b Kj hK0 hK hI i z b' y hz hb' hyz hy hyb
              simp only [Set.mem_Iic] at hyz hy hyb
              have hφi : Integrable (D.φ n i) := by
                apply Integrable.of_integral_ne_zero; rw [hD.φ_int]; norm_num
              set c := ∫ w in Set.Ioi 0, D.φ n i w with hc
              have hc1 : c ≤ 1 := by
                rw [hc, ← hD.φ_int n i]
                exact setIntegral_le_integral hφi (Eventually.of_forall (hD.φ_nonneg n i))
              have hj : ∀ j, (∫ w in Set.Ioi 0, b j (y - w) * D.φ n i w) + (z / b') *
                  ((∫ w in Set.Ioi 0, b j (y - w) * D.φ n i w) -
                    ∫ w in Set.Ioi 0, b j (y - b' - w) * D.φ n i w) ≤
                  Kj j * c + ∫ w in Set.Ioi 0, b j (z + y - w) * D.φ n i w := by
                intro j
                have i1 := hI i j y hy
                have i2 := hI i j (y - b') hyb
                have i3 := hI i j (z + y) (by linarith)
                have e1 : (∫ w in Set.Ioi 0, b j (y - w) * D.φ n i w) + (z / b') *
                    ((∫ w in Set.Ioi 0, b j (y - w) * D.φ n i w) -
                      ∫ w in Set.Ioi 0, b j (y - b' - w) * D.φ n i w) =
                    ∫ w in Set.Ioi 0, (b j (y - w) * D.φ n i w + (z / b') *
                      (b j (y - w) * D.φ n i w - b j (y - b' - w) * D.φ n i w)) := by
                  have i4 : Integrable (fun w => z / b' * (b j (y - w) * D.φ n i w -
                      b j (y - b' - w) * D.φ n i w)) (volume.restrict (Set.Ioi 0)) := (i1.sub i2).const_mul _
                  rw [integral_add i1 i4, integral_const_mul, integral_sub i1 i2]
                have e2 : Kj j * c + ∫ w in Set.Ioi 0, b j (z + y - w) * D.φ n i w =
                    ∫ w in Set.Ioi 0, (Kj j * D.φ n i w + b j (z + y - w) * D.φ n i w) := by
                  rw [integral_add (hφi.integrableOn.const_mul _) i3, integral_const_mul]
                rw [e1, e2]
                apply integral_mono_ae (i1.add (((i1.sub i2).const_mul (z / b') : Integrable (fun w => z / b' * (b j (y - w) * D.φ n i w -
                      b j (y - b' - w) * D.φ n i w)) (volume.restrict (Set.Ioi 0)))))
                  ((hφi.integrableOn.const_mul _).add i3)
                filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
                have hw0 : (0:ℝ) < w := hw
                have h := hK j z b' (y - w) hz hb' (show y - w + z ∈ Set.Iic T.B by
                  simp only [Set.mem_Iic]; linarith) (show y - w ∈ Set.Iic T.B by
                  simp only [Set.mem_Iic]; linarith) (show y - w - b' ∈ Set.Iic T.B by
                  simp only [Set.mem_Iic]; linarith)
                rw [show y - w - b' = y - b' - w by ring, show z + (y - w) = z + y - w by ring] at h
                have hφ := hD.φ_nonneg n i w
                simp only [Pi.add_apply, Pi.sub_apply]
                have := mul_le_mul_of_nonneg_right h hφ
                linear_combination this
              unfold F
              have : ∀ j, D.P i j * (∫ w in Set.Ioi 0, b j (y - w) * D.φ n i w) + (z / b') *
                  (D.P i j * (∫ w in Set.Ioi 0, b j (y - w) * D.φ n i w) -
                    D.P i j * ∫ w in Set.Ioi 0, b j (y - b' - w) * D.φ n i w) ≤
                  D.P i j * Kj j + D.P i j * ∫ w in Set.Ioi 0, b j (z + y - w) * D.φ n i w := by
                intro j
                have h1 := mul_le_mul_of_nonneg_left (hj j) (hD.P_nonneg i j)
                have h2 : D.P i j * (Kj j * c) ≤ D.P i j * Kj j :=
                  mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hK0 j) hc1) (hD.P_nonneg i j)
                linear_combination h1 + h2
              have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => this j)
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
              rw [← Finset.sum_sub_distrib]; exact hs
            have hIL : ∀ (b : ℝ → ℝ), LowerSemicontinuousOn b (Set.Iic T.B) →
                (∀ x ≤ T.B, 0 ≤ b x) → ∀ n i, (∀ y, y ≤ T.B → Integrable (fun z => b (y - z) * D.φ n i z)
                  (volume.restrict (Set.Ioi 0))) →
                LowerSemicontinuousOn (fun y => ∫ z in Set.Ioi 0, b (y - z) * D.φ n i z) (Set.Iic T.B) := by
              intro b hl h0 n i hI
              set W : ℝ → ℝ := fun x => b (min x T.B) with hWdef
              have hW : LowerSemicontinuous W := by
                have := hl.comp (g := fun x => min x T.B) (t := Set.univ)
                  (continuous_id.min continuous_const).continuousOn (fun x _ => min_le_right x T.B)
                exact lowerSemicontinuousOn_univ_iff.mp this
              have hWm : Measurable W := hW.measurable
              set J : ℝ → ℝ≥0∞ := fun y => ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (W (y - z) * D.φ n i z) with hJ
              have hJeq : ∀ y ≤ T.B, ENNReal.ofReal (∫ z in Set.Ioi 0, b (y - z) * D.φ n i z) = J y := by
                intro y hy
                rw [ofReal_integral_eq_lintegral_ofReal (hI y hy)]
                · apply setLIntegral_congr_fun measurableSet_Ioi
                  intro z hz
                  have : y - z ≤ T.B := by have : (0:ℝ) < z := hz; linarith
                  simp [hWdef, min_eq_left this]
                · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
                  have : y - z ≤ T.B := by have : (0:ℝ) < z := hz; linarith
                  exact mul_nonneg (h0 _ this) (hD.φ_nonneg n i z)
              have hJl : LowerSemicontinuous J := by
                rw [lowerSemicontinuous_iff_le_liminf]
                intro y0
                have hpt : ∀ z, ENNReal.ofReal (W (y0 - z) * D.φ n i z) ≤
                    liminf (fun y => ENNReal.ofReal (W (y - z) * D.φ n i z)) (𝓝 y0) := by
                  intro z
                  have h1 : LowerSemicontinuous (fun y => W (y - z)) :=
                    lowerSemicontinuousOn_univ_iff.mp ((lowerSemicontinuousOn_univ_iff.mpr hW).comp
                      (g := fun y => y - z) (t := Set.univ) (continuous_id.sub continuous_const).continuousOn
                      (fun _ _ => Set.mem_univ _))
                  have h2 : LowerSemicontinuous (fun y => ENNReal.ofReal (W (y - z) * D.φ n i z)) := by
                    intro y c hc
                    have := (ENNReal.continuous_ofReal.comp (continuous_mul_const (D.φ n i z))).continuousAt
                      (x := W (y - z))
                    exact ContinuousAt.comp_lowerSemicontinuousAt (g := fun t => ENNReal.ofReal (t * D.φ n i z)) (f := fun y => W (y - z))
                      this (h1 y) (fun a b' hab => ENNReal.ofReal_le_ofReal
                        (mul_le_mul_of_nonneg_right hab (hD.φ_nonneg n i z))) c hc
                  exact (lowerSemicontinuous_iff_le_liminf.mp h2) y0
                calc J y0 ≤ ∫⁻ z in Set.Ioi 0, liminf (fun y => ENNReal.ofReal (W (y - z) * D.φ n i z)) (𝓝 y0) :=
                      lintegral_mono (fun z => hpt z)
                  _ ≤ liminf J (𝓝 y0) := lintegral_liminf_le (fun y => ENNReal.measurable_ofReal.comp
                        ((hWm.comp (measurable_const.sub measurable_id)).mul (hD.φ_meas n i)))
              intro y0 hy0 c hc
              by_cases hc0 : c < 0
              · filter_upwards [self_mem_nhdsWithin] with y hy
                exact lt_of_lt_of_le hc0 (setIntegral_nonneg measurableSet_Ioi (fun z hz =>
                  mul_nonneg (h0 _ (by have : (0:ℝ) < z := hz; simp only [Set.mem_Iic] at hy; linarith))
                    (hD.φ_nonneg n i z)))
              push Not at hc0
              have hlt : ENNReal.ofReal c < J y0 := by
                rw [← hJeq y0 hy0]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mpr hc
              filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hJl y0 _ hlt)] with y hy hy'
              rw [← hJeq y hy] at hy'
              exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mp hy'
            have stage : ∀ n, n < N → (∀ j, LowerSemicontinuousOn (V (n+1) j) (Set.Iic T.B) ∧
                (∃ C, ∀ x ≤ T.B, V (n+1) j x ≤ C * (1 + |x|)) ∧ KConvexOn (D.K (n+1) j) (Set.Iic T.B) (V (n+1) j)) →
                ∀ i, ∃ p : ℝ × ℝ, serviceA D T n i ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T.B ∧
                (∀ x ≤ T.B, ∀ y ∈ capLevels D T n i x,
                  capObjective D n (V (n+1)) i x (x + orderSS p.1 p.2 x) ≤
                    capObjective D n (V (n+1)) i x y) ∧
                KConvexOn (D.K n i) (Set.Icc (serviceA D T n i) T.B) (fun y => D.c n i * y + F D n (V (n+1)) i y) ∧
                LowerSemicontinuousOn (fun y => D.c n i * y + F D n (V (n+1)) i y) (Set.Icc (serviceA D T n i) T.B) ∧
                (∀ y, serviceA D T n i ≤ y → y ≤ T.B →
                  D.c n i * p.2 + F D n (V (n+1)) i p.2 ≤ D.c n i * y + F D n (V (n+1)) i y) ∧
                (∀ y, p.1 ≤ y → y ≤ p.2 →
                  D.c n i * y + F D n (V (n+1)) i y ≤ D.K n i + (D.c n i * p.2 + F D n (V (n+1)) i p.2)) := by
              intro n hn hP i
              have hoSS' : ∀ (s S x : ℝ), orderSS (s : EReal) (S : EReal) x =
                  if x < s then S - x else 0 := by
                intro s S x; simp [orderSS, EReal.coe_lt_coe_iff]
              set A := serviceA D T n i with hA
              set B := T.B with hB
              have hAB : A ≤ B := hT.2.2 n hn i
              set K := D.K n i with hK
              have hK0 : 0 ≤ K := hD.K_nonneg n i
              set G : ℝ → ℝ := fun y => D.c n i * y + F D n (V (n+1)) i y with hG
              have hconv : KConvexOn K (Set.Icc A B) G := by
                have hF := hFK n (V (n+1)) (fun j => D.K (n+1) j) (fun j => hD.K_nonneg _ j)
                  (fun j => (hP j).2.2)
                  (fun i' j y hy => by
                    obtain ⟨hl, ⟨C, hC⟩, -⟩ := hP j
                    exact hInt (V (n+1) j) C hl
                      (fun x hx => hVnn (N - (n+1)) (n+1) (by omega) j x hx) hC n i' y hy) i
                intro z b y hz hb h1 h2 h3
                have := hF z b y hz hb (Set.mem_Iic.mpr h1.2) (Set.mem_Iic.mpr h2.2) (Set.mem_Iic.mpr h3.2)
                have hk := (h41 n hn i).1
                have e : (z / b) * (D.c n i * y - D.c n i * (y - b)) = D.c n i * z := by
                  rw [show D.c n i * y - D.c n i * (y - b) = D.c n i * b by ring, mul_comm (D.c n i) b,
                    ← mul_assoc, div_mul_cancel₀ z hb.ne', mul_comm]
                simp only [hG, hK]
                linear_combination this + e + hk
              have hlsc : LowerSemicontinuousOn G (Set.Icc A B) := by
                have hI : ∀ j, LowerSemicontinuousOn
                    (fun y => D.P i j * ∫ z in Set.Ioi 0, V (n+1) j (y - z) * D.φ n i z) (Set.Iic T.B) := by
                  intro j
                  obtain ⟨hl, ⟨C, hC⟩, -⟩ := hP j
                  have h0 : ∀ x ≤ T.B, 0 ≤ V (n+1) j x := fun x hx => hVnn (N - (n+1)) (n+1) (by omega) j x hx
                  have := hIL _ hl h0 n i (fun y hy => hInt _ C hl h0 hC n i y hy)
                  intro y hy
                  exact ContinuousAt.comp_lowerSemicontinuousWithinAt
                    (g := fun t => D.P i j * t) (continuous_const.mul continuous_id).continuousAt (this y hy)
                    (fun a b' hab => mul_le_mul_of_nonneg_left hab (hD.P_nonneg i j))
                have hF : LowerSemicontinuousOn (F D n (V (n+1)) i) (Set.Iic T.B) := by
                  intro y hy
                  have := lowerSemicontinuousWithinAt_sum (a := Finset.univ) (fun j _ => hI j y hy)
                  unfold F
                  convert this using 1
                have hG' : LowerSemicontinuousOn G (Set.Iic T.B) :=
                  ((continuous_const.mul continuous_id).continuousOn.lowerSemicontinuousOn).add hF
                exact hG'.mono (fun y hy => Set.mem_Iic.mpr hy.2)
              have hobjG : ∀ x y, capObjective D n (V (n+1)) i x y = K * delta (y - x) + G y := by
                intro x y; simp only [capObjective, hG, hK]; ring
              obtain ⟨S, hSmem, hSmin⟩ := LowerSemicontinuousOn.exists_isMinOn (⟨A, le_refl A, hAB⟩ : (Set.Icc A B).Nonempty)
                isCompact_Icc hlsc
              obtain ⟨v, hvc, hv⟩ := (lowerSemicontinuousOn_iff_preimage_Iic.mp hlsc) (K + G S)
              set E := Set.Icc A S ∩ (Set.Icc A B ∩ v) with hE
              have hEc : IsCompact E := IsCompact.of_isClosed_subset isCompact_Icc
                (isClosed_Icc.inter (isClosed_Icc.inter hvc)) Set.inter_subset_left
              have hEmem : ∀ y, y ∈ E ↔ A ≤ y ∧ y ≤ S ∧ G y ≤ K + G S := by
                intro y
                constructor
                · rintro ⟨⟨h1, h2⟩, h3⟩
                  rw [← hv] at h3
                  exact ⟨h1, h2, h3.2⟩
                · rintro ⟨h1, h2, h3⟩
                  refine ⟨⟨h1, h2⟩, ?_⟩
                  rw [← hv]
                  exact ⟨⟨h1, h2.trans hSmem.2⟩, h3⟩
              obtain ⟨s, hsE, hsl⟩ := hEc.exists_isLeast ⟨S, (hEmem S).2 ⟨hSmem.1, le_refl _, by linarith⟩⟩
              obtain ⟨hs1, hs2, hs3⟩ := (hEmem s).1 hsE
              have hGmin : ∀ y, A ≤ y → y ≤ B → G S ≤ G y := fun y h1 h2 => hSmin ⟨h1, h2⟩
              have hd0 : delta 0 = 0 := by simp [delta]
              have hdpos : ∀ z, 0 < z → delta z = 1 := by intro z hz; simp [delta, hz]
              have hxleg : ∀ x, s ≤ x → x ≤ S → G x ≤ K + G S := by
                intro x hxs hxS
                rcases eq_or_lt_of_le hxs with h' | h'
                · subst h'; exact hs3
                · by_cases hcmp : G s ≤ G x
                  · rcases eq_or_lt_of_le hxS with h'' | h''
                    · rw [h'']; linarith only [hK0]
                    have hk := hconv (S - x) (x - s) x (sub_nonneg.mpr hxS) (sub_pos.mpr h')
                      ⟨by linarith only [hSmem.1], by linarith only [hSmem.2]⟩
                      ⟨by linarith only [hs1, hxs], by linarith only [hxS, hSmem.2]⟩
                      ⟨by linarith only [hs1], by linarith only [hs2, hSmem.2]⟩
                    have e2 : x - (x - s) = s := by ring
                    have e3 : S - x + x = S := by ring
                    rw [e2, e3] at hk
                    have : 0 ≤ (S - x) / (x - s) * (G x - G s) :=
                      mul_nonneg (div_nonneg (sub_nonneg.mpr hxS) (sub_pos.mpr h').le) (sub_nonneg.mpr hcmp)
                    exact le_trans (le_add_of_nonneg_right this) hk
                  · push Not at hcmp; linarith only [hcmp, hs3]
              refine ⟨(s, S), hs1, hs2, hSmem.2, ?_, hconv, hlsc, hGmin, hxleg⟩
              intro x hx y hy
              obtain ⟨hy1, hy2, hy3⟩ := hy
              rw [hoSS', hobjG, hobjG]
              split_ifs with hxs
              · -- order up to S
                have e1 : x + (S - x) = S := by ring
                rw [e1, hdpos _ (by linarith only [hxs, hs2])]
                rcases eq_or_lt_of_le hy1 with h | h
                · subst h
                  rw [sub_self, hd0]
                  -- x ∉ E
                  have hxE : ¬ (G x ≤ K + G S) := by
                    intro hc
                    have := hsl ((hEmem x).2 ⟨hy2, by linarith only [hxs, hs2], hc⟩)
                    simp only at hxs
                    linarith only [this, hxs]
                  push Not at hxE; simp only [mul_zero, mul_one, zero_add]; linarith only [hxE]
                · rw [hdpos _ (sub_pos.mpr h)]
                  linarith only [hGmin y hy2 hy3]
              · push Not at hxs
                rw [add_zero, sub_self, hd0]
                rcases eq_or_lt_of_le hy1 with h | h
                · subst h; rw [sub_self, hd0]
                · rw [hdpos _ (sub_pos.mpr h)]
                  simp only [mul_zero, mul_one, zero_add]
                  by_cases hxS : x ≤ S
                  · -- G x ≤ K + G S
                    have hxle : G x ≤ K + G S := hxleg x hxs hxS
                    linarith only [hxle, hGmin y hy2 hy3]
                  · push Not at hxS
                    have hk := hconv (y - x) (x - S) x (sub_nonneg.mpr hy1) (sub_pos.mpr hxS)
                      ⟨by linarith only [hy2], by linarith only [hy3]⟩ ⟨by linarith only [hs1, hxs], hx⟩
                      ⟨by linarith only [hSmem.1], by linarith only [hSmem.2]⟩
                    have e2 : x - (x - S) = S := by ring
                    have e3 : y - x + x = y := by ring
                    rw [e2, e3] at hk
                    have : 0 ≤ (y - x) / (x - S) * (G x - G S) :=
                      mul_nonneg (div_nonneg (sub_nonneg.mpr hy1) (sub_pos.mpr hxS).le)
                        (sub_nonneg.mpr (hGmin x (hs1.trans hxs) hx))
                    exact le_trans (le_add_of_nonneg_right this) hk
            have hoSS2 : ∀ (s S x : ℝ), orderSS (s : EReal) (S : EReal) x =
                if x < s then S - x else 0 := by
              intro s S x; simp [orderSS, EReal.coe_lt_coe_iff]
            have hVform : ∀ n, n < N → ∀ i (p : ℝ × ℝ), serviceA D T n i ≤ p.1 → p.1 ≤ p.2 → p.2 ≤ T.B →
                (∀ x ≤ T.B, ∀ y ∈ capLevels D T n i x,
                  capObjective D n (V (n+1)) i x (x + orderSS p.1 p.2 x) ≤
                    capObjective D n (V (n+1)) i x y) →
                ∀ x ≤ T.B, V n i x = D.f n i x - D.c n i * x +
                  (if x < p.1 then D.K n i + (D.c n i * p.2 + F D n (V (n+1)) i p.2)
                    else D.c n i * x + F D n (V (n+1)) i x) := by
              intro n hn i p h1 h2 h3 hmin x hx
              have hmem : x + orderSS p.1 p.2 x ∈ capLevels D T n i x := by
                rw [hoSS2]
                split_ifs with h
                · exact ⟨by linarith only [h, h2], by linarith only [h1, h2], by linarith only [h3]⟩
                · push Not at h; exact ⟨by linarith only [], by linarith only [h1, h], by linarith only [hx]⟩
              have hleast : IsLeast (capObjective D n (V (n+1)) i x '' capLevels D T n i x)
                  (capObjective D n (V (n+1)) i x (x + orderSS p.1 p.2 x)) :=
                ⟨⟨_, hmem, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmin x hx y hy⟩
              rw [hVsucc n hn i x, hleast.csInf_eq, hoSS2]
              simp only [capObjective]
              split_ifs with h
              · have e : x + (p.2 - x) = p.2 := by ring
                have hd : delta (p.2 - x) = 1 := by simp [delta]; linarith
                rw [e, hd]; ring
              · have hd : delta (0:ℝ) = 0 := by simp [delta]
                rw [add_zero, sub_self, hd]; ring
            have hfK : ∀ k i z b y, 0 ≤ z → 0 < b →
                D.f k i y + (z / b) * (D.f k i y - D.f k i (y - b)) ≤ D.f k i (z + y) := by
              intro k i z b y hz hb
              rcases eq_or_lt_of_le hz with h | h
              · subst h; simp
              have := (hD.f_convex k i).slope_mono_adjacent (x := y - b) (y := y) (z := z + y)
                (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith)
              rw [show y - (y - b) = b by ring, show z + y - y = z by ring] at this
              have e : (z / b) * (D.f k i y - D.f k i (y - b)) = z * ((D.f k i y - D.f k i (y - b)) / b) := by
                ring
              have e2 : z * ((D.f k i (z + y) - D.f k i y) / z) = D.f k i (z + y) - D.f k i y := by
                field_simp
              have := mul_le_mul_of_nonneg_left this hz
              rw [e, e2] at *
              linarith only [this]
            have hfcont : ∀ k i, Continuous (D.f k i) := by
              intro k i
              have := (hD.f_convex k i).continuousOn_interior
              rw [interior_univ] at this
              exact continuousOn_univ.mp this
            have hFgr : ∀ n (b : Fin L → ℝ → ℝ) (C : ℝ), 0 ≤ C →
                (∀ j, LowerSemicontinuousOn (b j) (Set.Iic T.B)) → (∀ j x, x ≤ T.B → 0 ≤ b j x) →
                (∀ j x, x ≤ T.B → b j x ≤ C * (1 + |x|)) →
                ∀ i y, y ≤ T.B → F D n b i y ≤ C * (1 + |y|) + C * D.M := by
              intro n b C hC hl h0 hb i y hy
              have hφi : Integrable (D.φ n i) := by
                apply Integrable.of_integral_ne_zero; rw [hD.φ_int]; norm_num
              have hc1 : ∫ w in Set.Ioi 0, D.φ n i w ≤ 1 := by
                rw [← hD.φ_int n i]
                exact setIntegral_le_integral hφi (Eventually.of_forall (hD.φ_nonneg n i))
              have hm1 : ∫ w in Set.Ioi 0, w * D.φ n i w ≤ D.M := by
                refine le_trans ?_ (hD.mean_le n i)
                apply setIntegral_le_integral (hD.mean_integrable n i)
                refine Eventually.of_forall (fun w => ?_)
                rcases lt_or_ge w 0 with h | h
                · simp [hD.φ_neg n i w h]
                · exact mul_nonneg h (hD.φ_nonneg n i w)
              have hj : ∀ j, ∫ z in Set.Ioi 0, b j (y - z) * D.φ n i z ≤ C * (1 + |y|) + C * D.M := by
                intro j
                have hI := hInt (b j) C (hl j) (h0 j) (hb j) n i y hy
                have hg : IntegrableOn (fun z => C * (1 + |y|) * D.φ n i z + C * (z * D.φ n i z)) (Set.Ioi 0) :=
                  ((hφi.const_mul _).add ((hD.mean_integrable n i).const_mul _)).integrableOn
                calc ∫ z in Set.Ioi 0, b j (y - z) * D.φ n i z
                    ≤ ∫ z in Set.Ioi 0, (C * (1 + |y|) * D.φ n i z + C * (z * D.φ n i z)) := by
                      apply setIntegral_mono_on hI hg measurableSet_Ioi
                      intro z hz
                      have hz0 : (0:ℝ) < z := hz
                      have hyz : y - z ≤ T.B := by linarith
                      have h1 : b j (y - z) ≤ C * (1 + |y|) + C * z := by
                        have h2 := hb j _ hyz
                        have : |y - z| ≤ |y| + z := by
                          calc |y - z| ≤ |y| + |z| := abs_sub _ _
                            _ = |y| + z := by rw [abs_of_pos hz0]
                        have := mul_le_mul_of_nonneg_left this hC
                        linarith
                      have := mul_le_mul_of_nonneg_right h1 (hD.φ_nonneg n i z)
                      linarith
                  _ = C * (1 + |y|) * (∫ z in Set.Ioi 0, D.φ n i z) + C * ∫ z in Set.Ioi 0, z * D.φ n i z := by
                      rw [integral_add (hφi.const_mul _).integrableOn ((hD.mean_integrable n i).const_mul _).integrableOn,
                        integral_const_mul, integral_const_mul]
                  _ ≤ C * (1 + |y|) + C * D.M := by
                      have h1 : 0 ≤ C * (1 + |y|) := mul_nonneg hC (add_nonneg zero_le_one (abs_nonneg y))
                      have := mul_le_mul_of_nonneg_left hc1 h1
                      have := mul_le_mul_of_nonneg_left hm1 hC
                      linarith
              unfold F
              calc ∑ j, D.P i j * ∫ z in Set.Ioi 0, b j (y - z) * D.φ n i z
                  ≤ ∑ j, D.P i j * (C * (1 + |y|) + C * D.M) :=
                    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hj j) (hD.P_nonneg i j))
                _ = C * (1 + |y|) + C * D.M := by rw [← Finset.sum_mul, hD.P_sum, one_mul]
            have hVprop : ∀ m ≤ N, ∀ j, LowerSemicontinuousOn (V m j) (Set.Iic T.B) ∧
                (∃ C, ∀ x ≤ T.B, V m j x ≤ C * (1 + |x|)) ∧ KConvexOn (D.K m j) (Set.Iic T.B) (V m j) := by
              have main : ∀ k, ∀ m, m + k = N → ∀ j, LowerSemicontinuousOn (V m j) (Set.Iic T.B) ∧
                  (∃ C, ∀ x ≤ T.B, V m j x ≤ C * (1 + |x|)) ∧ KConvexOn (D.K m j) (Set.Iic T.B) (V m j) := by
                intro k
                induction k with
                | zero =>
                  intro m hm j
                  rw [show m = N by omega]
                  refine ⟨?_, ⟨D.C, fun x _ => by rw [hVN]; exact hD.f_growth N j x⟩, ?_⟩
                  · have : V N j = D.f N j := funext (hVN j)
                    rw [this]; exact (hfcont N j).lowerSemicontinuous.lowerSemicontinuousOn _
                  · intro z b y hz hb _ _ _
                    rw [hVN, hVN, hVN]; linarith [hfK N j z b y hz hb, hD.K_nonneg N j]
                | succ k ih =>
                  intro n hnk i
                  have hn : n < N := by omega
                  have hP := ih (n+1) (by omega)
                  obtain ⟨p, h1, h2, h3, hmin, hconv, hlsc, hGmin, hxle⟩ := stage n hn hP i
                  have hform := hVform n hn i p h1 h2 h3 hmin
                  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun y => D.c n i * y + F D n (V (n+1)) i y := ⟨_, rfl⟩
                  obtain ⟨s, S, hsS⟩ : ∃ s S : ℝ, p = (s, S) := ⟨p.1, p.2, rfl⟩
                  subst hsS
                  simp only at h1 h2 h3
                  have hconv' : KConvexOn (D.K n i) (Set.Icc (serviceA D T n i) T.B) G := by subst hG; exact hconv
                  have hlsc' : LowerSemicontinuousOn G (Set.Icc (serviceA D T n i) T.B) := by subst hG; exact hlsc
                  have hGmin' : ∀ y, serviceA D T n i ≤ y → y ≤ T.B → G S ≤ G y := by subst hG; exact hGmin
                  have hxle' : ∀ y, s ≤ y → y ≤ S → G y ≤ D.K n i + G S := by subst hG; exact hxle
                  have hform' : ∀ x ≤ T.B, V n i x = D.f n i x - D.c n i * x +
                      (if x < s then D.K n i + G S else G x) := by subst hG; exact hform
                  have hK0 := hD.K_nonneg n i
                  refine ⟨?_, ?_, ?_⟩
                  · -- lower semicontinuity
                    intro x0 hx0 c hc
                    have hx0' : x0 ≤ T.B := hx0
                    rw [hform' x0 hx0'] at hc
                    rw [eventually_nhdsWithin_iff]
                    have hq : Continuous (fun x => D.f n i x - D.c n i * x) :=
                      (hfcont n i).sub (continuous_const.mul continuous_id)
                    by_cases hxs : x0 < s
                    · rw [if_pos hxs] at hc
                      have e1 : ∀ᶠ y in 𝓝 x0, c - (D.K n i + G S) < D.f n i y - D.c n i * y :=
                        Filter.Tendsto.eventually hq.continuousAt (lt_mem_nhds (by linarith))
                      filter_upwards [e1, Iio_mem_nhds hxs] with y hy hys hyB
                      have hys' : y < s := hys
                      rw [hform' y hyB, if_pos hys']; linarith
                    · push Not at hxs
                      rw [if_neg (not_lt.mpr hxs)] at hc
                      obtain ⟨d, hd, hdd⟩ : ∃ d, 0 < d ∧ d = D.f n i x0 - D.c n i * x0 + G x0 - c :=
                        ⟨_, by linarith, rfl⟩
                      have e1 : ∀ᶠ y in 𝓝 x0, D.f n i x0 - D.c n i * x0 - d/2 < D.f n i y - D.c n i * y :=
                        Filter.Tendsto.eventually hq.continuousAt (lt_mem_nhds (by linarith))
                      have e2 := hlsc' x0 ⟨by linarith, hx0'⟩ (G x0 - d/2) (by linarith)
                      rw [eventually_nhdsWithin_iff] at e2
                      rcases eq_or_lt_of_le hxs with hxe | hxlt
                      · have hGs : G x0 ≤ D.K n i + G S := hxe ▸ hxle' s le_rfl h2
                        filter_upwards [e1, e2] with y hy1 hy2 hyB
                        rw [hform' y hyB]
                        split_ifs with hys
                        · linarith
                        · push Not at hys; have := hy2 ⟨by linarith, hyB⟩; linarith
                      · filter_upwards [e1, e2, Ioi_mem_nhds hxlt] with y hy1 hy2 hys hyB
                        have hys' : s < y := hys
                        rw [hform' y hyB, if_neg (not_lt.mpr hys'.le)]
                        have := hy2 ⟨by linarith, hyB⟩; linarith
                  · -- growth
                    choose Cj hCj using fun j => (hP j).2.1
                    set Cs := ∑ j, |Cj j| with hCs
                    have hCs0 : 0 ≤ Cs := Finset.sum_nonneg (fun j _ => abs_nonneg _)
                    have hb : ∀ j x, x ≤ T.B → V (n+1) j x ≤ Cs * (1 + |x|) := by
                      intro j x hx
                      have h1 := hCj j x hx
                      have h2 : Cj j ≤ Cs := (le_abs_self _).trans
                        (Finset.single_le_sum (f := fun j => |Cj j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j))
                      exact h1.trans (mul_le_mul_of_nonneg_right h2 (add_nonneg zero_le_one (abs_nonneg x)))
                    have hFb := hFgr n (V (n+1)) Cs hCs0 (fun j => (hP j).1)
                      (fun j x hx => hVnn (N - (n+1)) (n+1) (by omega) j x hx) hb i
                    refine ⟨D.C + D.c n i + |D.K n i + G S| + Cs + Cs * |D.M|, fun x hx => ?_⟩
                    rw [hform' x hx]
                    have hax : 0 ≤ |x| := abs_nonneg x
                    have hc0 := hD.c_nonneg n i
                    have hfx := hD.f_growth n i x
                    have t1 : -(D.c n i * x) ≤ D.c n i * (1 + |x|) := by
                      have := mul_le_mul_of_nonneg_left (neg_le_abs x) hc0
                      linarith
                    have t2 : D.K n i + G S ≤ |D.K n i + G S| * (1 + |x|) := by
                      have := mul_nonneg (abs_nonneg (D.K n i + G S)) hax
                      linarith [le_abs_self (D.K n i + G S)]
                    have t3 : Cs * D.M ≤ Cs * |D.M| * (1 + |x|) := by
                      have := mul_nonneg (mul_nonneg hCs0 (abs_nonneg D.M)) hax
                      have := mul_le_mul_of_nonneg_left (le_abs_self D.M) hCs0
                      linarith
                    have t4 : 0 ≤ Cs * (1 + |x|) := mul_nonneg hCs0 (add_nonneg zero_le_one hax)
                    have t5 : 0 ≤ |D.K n i + G S| * (1 + |x|) := mul_nonneg (abs_nonneg _) (add_nonneg zero_le_one hax)
                    have t6 : 0 ≤ Cs * |D.M| * (1 + |x|) :=
                      mul_nonneg (mul_nonneg hCs0 (abs_nonneg _)) (add_nonneg zero_le_one hax)
                    have t7 : 0 ≤ D.c n i * (1 + |x|) := mul_nonneg hc0 (add_nonneg zero_le_one hax)
                    split_ifs with hxs
                    · linarith
                    · have := hFb x hx
                      have e : G x = D.c n i * x + F D n (V (n+1)) i x := by rw [hG]
                      rw [e]
                      linarith
                  · -- K-convexity
                    obtain ⟨h, hhd⟩ : ∃ h : ℝ → ℝ, ∀ x, h x = if x < s then D.K n i + G S else G x :=
                      ⟨_, fun _ => rfl⟩
                    have hhK : ∀ z b y, 0 ≤ z → 0 < b → y + z ≤ T.B → y ≤ T.B →
                        h y + (z / b) * (h y - h (y - b)) ≤ D.K n i + h (z + y) := by
                      intro z b y hz hb hyz hy
                      by_cases c1 : y < s
                      · have c1' : y - b < s := by linarith only [c1, hb]
                        rw [hhd y, hhd (y - b), if_pos c1, if_pos c1', sub_self, mul_zero, add_zero, hhd]
                        split_ifs with c4
                        · linarith only [hK0]
                        · exact add_le_add le_rfl (hGmin' (z + y) (by linarith only [h1, not_lt.mp c4])
                            (by linarith only [hyz]))
                      · have c1n : s ≤ y := not_lt.mp c1
                        have c4 : ¬ z + y < s := fun h' => by linarith only [h', c1n, hz]
                        rw [hhd y, hhd (z + y), if_neg c1, if_neg c4]
                        by_cases c2 : y - b < s
                        · rw [hhd (y - b), if_pos c2]
                          by_cases c3 : G y ≤ D.K n i + G S
                          · have ht : (z / b) * (G y - (D.K n i + G S)) ≤ 0 :=
                              mul_nonpos_of_nonneg_of_nonpos (div_nonneg hz hb.le) (sub_nonpos.mpr c3)
                            have hg := hGmin' (z + y) (by linarith only [h1, c1n, hz]) (by linarith only [hyz])
                            generalize (z / b) * (G y - (D.K n i + G S)) = t at ht ⊢
                            linarith only [ht, hg, c3]
                          · have c3' : D.K n i + G S < G y := lt_of_not_ge c3
                            have hyS : S < y := by
                              by_contra hc; exact c3 (hxle' y c1n (le_of_not_gt hc))
                            have hk := hconv' z (y - S) y hz (sub_pos.mpr hyS) ⟨by linarith only [h1, c1n, hz], hyz⟩
                              ⟨by linarith only [h1, c1n], hy⟩ ⟨by linarith only [h1, h2], by linarith only [h3]⟩
                            rw [show y - (y - S) = S by ring] at hk
                            have hdiv : z / b ≤ z / (y - S) :=
                              div_le_div_of_nonneg_left hz (sub_pos.mpr hyS) (by linarith only [c2, h2])
                            have m1 : (z / b) * (G y - (D.K n i + G S)) ≤ (z / (y - S)) * (G y - (D.K n i + G S)) :=
                              mul_le_mul_of_nonneg_right hdiv (sub_pos.mpr c3').le
                            have m2 : (z / (y - S)) * (G y - (D.K n i + G S)) ≤ (z / (y - S)) * (G y - G S) :=
                              mul_le_mul_of_nonneg_left (sub_le_sub_left (le_add_of_nonneg_left hK0) _)
                                (div_nonneg hz (sub_pos.mpr hyS).le)
                            exact le_trans (add_le_add le_rfl (m1.trans m2)) hk
                        · have c2n : s ≤ y - b := not_lt.mp c2
                          rw [hhd (y - b), if_neg c2]
                          have m1 : y + z ∈ Set.Icc (serviceA D T n i) T.B := ⟨by linarith only [h1, c1n, hz], hyz⟩
                          have m2 : y ∈ Set.Icc (serviceA D T n i) T.B := ⟨by linarith only [h1, c1n], hy⟩
                          have m3 : y - b ∈ Set.Icc (serviceA D T n i) T.B :=
                            ⟨by linarith only [h1, c2n], by linarith only [hy, hb]⟩
                          exact hconv' z b y hz hb m1 m2 m3
                    have hform2 : ∀ x ≤ T.B, V n i x = D.f n i x - D.c n i * x + h x := by
                      intro x hx; rw [hhd]; exact hform' x hx
                    intro z b y hz hb hyz hy hyb
                    have hyz' : y + z ≤ T.B := hyz
                    have hy' : y ≤ T.B := hy
                    have hyb' : y - b ≤ T.B := hyb
                    rw [hform2 _ hy', hform2 _ hyb', show z + y = y + z by ring, hform2 _ hyz',
                      show y + z = z + y by ring]
                    have hf := hfK n i z b y hz hb
                    have hh := hhK z b y hz hb hyz' hy'
                    have ecz : z / b * (D.c n i * b) = D.c n i * z := by
                      rw [mul_comm (D.c n i) b, ← mul_assoc, div_mul_cancel₀ z hb.ne', mul_comm]
                    have e : (z / b) * ((D.f n i y - D.c n i * y + h y) -
                        (D.f n i (y - b) - D.c n i * (y - b) + h (y - b))) =
                        (z / b) * (D.f n i y - D.f n i (y - b)) + (z / b) * (h y - h (y - b)) -
                          z / b * (D.c n i * b) := by ring
                    rw [e, ecz]
                    generalize z / b * (D.f n i y - D.f n i (y - b)) = t1 at hf ⊢
                    generalize z / b * (h y - h (y - b)) = t2 at hh ⊢
                    linarith only [hf, hh]
              intro m hm j
              exact main (N - m) m (by omega) j
            have key : ∀ n i, ∃ p : ℝ × ℝ, n < N → (serviceA D T n i ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T.B ∧
                ∀ x ≤ T.B, ∀ y ∈ capLevels D T n i x,
                  capObjective D n (V (n+1)) i x (x + orderSS p.1 p.2 x) ≤
                    capObjective D n (V (n+1)) i x y) := by
              intro n i
              by_cases hn : n < N
              · obtain ⟨p, h1, h2, h3, h4, -⟩ := stage n hn (hVprop (n+1) (by omega)) i
                exact ⟨p, fun _ => ⟨h1, h2, h3, h4⟩⟩
              · exact ⟨(0, 0), fun h => absurd h hn⟩
            choose p hp using key
            have hoSS : ∀ n i x, orderSS ((p n i).1 : EReal) ((p n i).2 : EReal) x =
                if x < (p n i).1 then (p n i).2 - x else 0 := by
              intro n i x; simp [orderSS, EReal.coe_lt_coe_iff]
            have hrule : ∀ n i x, x ≤ T.B → capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) n i x
                = orderSS ((p n i).1 : EReal) ((p n i).2 : EReal) x := by
              intro n i x hx; simp [capRule, hx]
            -- feasibility of the rule
            have hact : ∀ n < N, ∀ i x, x ≤ T.B →
                capAction D T n i x (orderSS ((p n i).1 : EReal) ((p n i).2 : EReal) x) := by
              intro n hn i x hx
              obtain ⟨h1, h2, h3, -⟩ := hp n i hn
              rw [hoSS]
              split_ifs with h
              · refine ⟨by linarith only [h, h2], by linarith only [h1, h2], by linarith only [h3]⟩
              · refine ⟨le_refl _, by linarith only [not_lt.mp h, h1], by linarith only [hx]⟩
            have hobj : ∀ n i x u, capObjective D n (V (n+1)) i x (x + u) =
                D.c n i * x + (orderCost D n i u + F D n (V (n+1)) i (x + u)) := by
              intro n i x u; simp only [capObjective, orderCost, add_sub_cancel_left]; ring
            have h3full : ∀ n < N, ∀ i x, x ≤ T.B →
                  capAction D T n i x (capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) n i x) ∧
                  V n i x = D.f n i x + orderCost D n i (capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) n i x) +
                    F D n (V (n + 1)) i (x + capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) n i x) ∧
                  ∀ u : ℝ, capAction D T n i x u →
                    orderCost D n i (capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) n i x) +
                        F D n (V (n + 1)) i (x + capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) n i x) ≤
                    orderCost D n i u + F D n (V (n + 1)) i (x + u) := by
              intro n hn i x hx
              rw [hrule n i x hx]
              have ha := hact n hn i x hx
              have hmin := (hp n i hn).2.2.2 x hx
              have hmem : x + orderSS ((p n i).1 : EReal) ((p n i).2 : EReal) x ∈ capLevels D T n i x :=
                ⟨le_add_of_nonneg_right ha.1, ha.2.1, ha.2.2⟩
              have hleast : IsLeast (capObjective D n (V (n+1)) i x '' capLevels D T n i x)
                  (capObjective D n (V (n+1)) i x (x + orderSS ((p n i).1 : EReal) ((p n i).2 : EReal) x)) :=
                ⟨⟨_, hmem, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmin y hy⟩
              refine ⟨ha, ?_, ?_⟩
              · rw [hVsucc n hn i x, hleast.csInf_eq, hobj]; ring
              · intro u hu
                have := hmin (x + u) ⟨by linarith [hu.1], hu.2.1, hu.2.2⟩
                rw [hobj, hobj] at this; linarith
            refine ⟨fun n i => (p n i).1, fun n i => (p n i).2, ?_, ?_, ?_, ?_⟩
            · intro n hn i; exact ⟨(hp n i hn).1, (hp n i hn).2.1, (hp n i hn).2.2.1⟩
            · intro n hn
              have hval : ∀ i x, capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) n i x =
                  if x < (p n i).1 then (p n i).2 - x else 0 := by
                intro i x
                by_cases hx : x ≤ T.B
                · rw [hrule n i x hx, hoSS]
                · have : ¬ x < (p n i).1 := by
                    have := (hp n i hn).2.2.1; have := (hp n i hn).2.1; intro h; exact hx (by linarith)
                  simp [capRule, hx, this]
              refine ⟨fun i x => ?_, fun k i x => ((p n i).2 - x) * max 0 (min 1 (((k:ℝ)+1) * ((p n i).1 - x))),
                fun k i => by fun_prop, fun k i x => ?_, fun i x => ?_⟩
              · rw [hval]; split_ifs with h
                · linarith [(hp n i hn).2.1]
                · exact le_refl _
              · by_cases h : x < (p n i).1
                · apply mul_nonneg (by linarith [(hp n i hn).2.1]) (le_max_left _ _)
                · have : ((k:ℝ)+1) * ((p n i).1 - x) ≤ 0 :=
                    mul_nonpos_of_nonneg_of_nonpos (add_nonneg (Nat.cast_nonneg k) zero_le_one)
                      (sub_nonpos.mpr (not_lt.mp h))
                  have : max 0 (min 1 (((k:ℝ)+1) * ((p n i).1 - x))) = 0 := by
                    apply le_antisymm (max_le (le_refl _) ((min_le_right _ _).trans this)) (le_max_left _ _)
                  show 0 ≤ ((p n i).2 - x) * max 0 (min 1 (((k:ℝ)+1) * ((p n i).1 - x)))
                  rw [this, mul_zero]
              · rw [hval]
                by_cases h : x < (p n i).1
                · rw [if_pos h]
                  apply tendsto_const_nhds.congr'
                  have hpos : 0 < (p n i).1 - x := by linarith
                  obtain ⟨k0, hk0⟩ := exists_nat_gt (1 / ((p n i).1 - x))
                  filter_upwards [eventually_ge_atTop k0] with k hk
                  have : 1 ≤ ((k:ℝ)+1) * ((p n i).1 - x) := by
                    have h1 : (1 / ((p n i).1 - x)) < (k:ℝ) + 1 := by
                      have : (k0:ℝ) ≤ k := by exact_mod_cast hk
                      linarith
                    rw [div_lt_iff₀ hpos] at h1; linarith
                  rw [min_eq_left this, max_eq_right zero_le_one, mul_one]
                · rw [if_neg h]
                  apply tendsto_const_nhds.congr'
                  filter_upwards with k
                  have : ((k:ℝ)+1) * ((p n i).1 - x) ≤ 0 :=
                    mul_nonpos_of_nonneg_of_nonpos (add_nonneg (Nat.cast_nonneg k) zero_le_one)
                      (sub_nonpos.mpr (not_lt.mp h))
                  have : max 0 (min 1 (((k:ℝ)+1) * ((p n i).1 - x))) = 0 := by
                    apply le_antisymm (max_le (le_refl _) ((min_le_right _ _).trans this)) (le_max_left _ _)
                  rw [this, mul_zero]
            · exact h3full
            · obtain ⟨R, hRdef⟩ : ∃ R, R = capRule T (fun n i => (p n i).1) (fun n i => (p n i).2) := ⟨_, rfl⟩
              rw [← hRdef] at h3full ⊢
              have hRact : ∀ k < N, ∀ i x, x ≤ T.B → capAction D T k i x (R k i x) :=
                fun k hk i x hx => (h3full k hk i x hx).1
              have h3 := fun k (hk : k < N) i x (hx : x ≤ T.B) => (h3full k hk i x hx).2
              have hR0 : ∀ k < N, ∀ i x, 0 ≤ R k i x := by
                intro k hk i x
                rw [hRdef]
                simp only [capRule, hoSS]
                split_ifs <;> linarith [(hp k i hk).2.1]
              have hRm : ∀ k i, Measurable (R k i) := by
                intro k i
                have e : R k i = fun x => if x ≤ T.B then (if x < (p k i).1 then (p k i).2 - x else 0) else 0 := by
                  funext x; rw [hRdef]; simp only [capRule, hoSS]
                rw [e]
                exact Measurable.ite measurableSet_Iic (Measurable.ite measurableSet_Iio
                  (measurable_const.sub measurable_id) measurable_const) measurable_const
              intro n hn i x hx
              have hinitc : ∀ {α : Type} (k : ℕ) (a : α) (q : Fin (k+1) → α),
                  Fin.init (Fin.cons a q : Fin (k+2) → α) = Fin.cons a (Fin.init q) := by
                intro α k a q; funext j; refine Fin.cases ?_ ?_ j
                · rfl
                · intro j; simp [Fin.init]
              have hsur : ∀ (U : Policy L) (x : ℝ) (i : Fin L) (z : ℝ) (t : ℕ) (σ : Fin (t+1) → Fin L) (ξ : Fin t → ℝ),
                  surplus U x (t+1) (Fin.cons i σ) (Fin.cons z ξ) =
                    surplus (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ'))
                      (x + U 0 (fun _ => i) (fun k => k.elim0) - z) t σ ξ := by
                intro U x i z t
                induction t with
                | zero =>
                  intro σ ξ
                  simp only [surplus]
                  have e1 : Fin.init (Fin.cons i σ : Fin 2 → Fin L) = fun _ => i := by funext k; fin_cases k; rfl
                  have e2 : Fin.init (Fin.cons z ξ : Fin 1 → ℝ) = fun k => k.elim0 := funext (fun k => k.elim0)
                  rw [e1, e2]; rfl
                | succ t ih =>
                  intro σ ξ
                  rw [surplus, hinitc, hinitc, ih]
                  simp only [surplus]
                  congr 1
              have hw : ∀ (n m : ℕ) (i : Fin L) (σ : Fin (m+1) → Fin L) (z : ℝ) (ξ : Fin m → ℝ),
                  pathWeight D n (Fin.cons i σ) (Fin.cons z ξ) = D.P i (σ 0) * D.φ n i z * pathWeight D (n+1) σ ξ := by
                intro n m i σ z ξ
                unfold pathWeight
                rw [Fin.prod_univ_succ]
                simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_zero, add_zero, Fin.val_succ]
                rw [mul_assoc, mul_assoc (D.P i (σ 0))]
                congr 1
                congr 1
                · apply Finset.prod_congr rfl; intro t _
                  simp only [← Fin.succ_castSucc, Fin.cons_succ]
                  rw [show n + (↑t + 1) = n + 1 + ↑t by ring]
              have hIS : ∀ (m : ℕ) (i : Fin L) (σ : Fin (m+1) → Fin L) (t : ℕ) (h : t + 1 ≤ m + 1),
                  initStates (Fin.cons i σ : Fin (m+2) → Fin L) (t+1) h = Fin.cons i (initStates σ t (by omega)) := by
                intro m i σ t h; funext j; refine Fin.cases ?_ ?_ j
                · rfl
                · intro j; simp only [initStates, Fin.cons_succ]; rfl
              have hID : ∀ (m : ℕ) (z : ℝ) (ξ : Fin m → ℝ) (t : ℕ) (h : t + 1 ≤ m + 1),
                  initDemands (Fin.cons z ξ : Fin (m+1) → ℝ) (t+1) h = Fin.cons z (initDemands ξ t (by omega)) := by
                intro m z ξ t h; funext j; refine Fin.cases ?_ ?_ j
                · rfl
                · intro j; simp only [initDemands, Fin.cons_succ]; rfl
              have hpc : ∀ (n m : ℕ) (U : Policy L) (x : ℝ) (i : Fin L) (σ : Fin (m+1) → Fin L) (z : ℝ) (ξ : Fin m → ℝ),
                  pathCost D N n U x (Fin.cons i σ) (Fin.cons z ξ) =
                    (orderCost D n i (U 0 (fun _ => i) (fun k => k.elim0)) + D.f n i x) +
                    pathCost D N (n+1) (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ'))
                      (x + U 0 (fun _ => i) (fun k => k.elim0) - z) σ ξ := by
                intro n m U x i σ z ξ
                unfold pathCost
                rw [Fin.sum_univ_succ, add_assoc]
                have hIS0 : initStates (Fin.cons i σ : Fin (m+2) → Fin L) 0 (by omega) = fun _ => i := by
                  funext k; fin_cases k; rfl
                have hID0 : initDemands (Fin.cons z ξ : Fin (m+1) → ℝ) 0 (by omega) = fun k => k.elim0 :=
                  funext (fun k => k.elim0)
                congr 1
                · simp [hIS0, hID0, surplus]
                congr 1
                · apply Finset.sum_congr rfl; intro t _
                  have e1 : (Fin.cons i σ : Fin (m+2) → Fin L) t.succ.castSucc = σ t.castSucc := by
                    rw [← Fin.succ_castSucc, Fin.cons_succ]
                  simp only [Fin.val_succ]
                  rw [e1, hIS, hID, hsur, show n + (↑t + 1) = n + 1 + ↑t by ring]
                · rw [show Fin.last (m+1) = (Fin.last m).succ from rfl, Fin.cons_succ, hsur]
              have hF4 : ∀ m (g : (Fin (m+1) → ℝ) → ℝ≥0∞), Measurable g →
                  ∫⁻ ξ, g ξ = ∫⁻ z, ∫⁻ ξ', g (Fin.cons z ξ') := by
                intro m g hg
                have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
                rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
                rw [Measure.volume_eq_prod, lintegral_prod
                  (fun a => g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm a))
                  (hg.comp (MeasurableEquiv.measurable _)).aemeasurable]
                simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
              have hRI : ∀ m (i : Fin L) (h : (Fin (m+2) → Fin L) → ℝ≥0∞),
                  ∑ σ, (if σ 0 = i then h σ else 0) = ∑ σ' : Fin (m+1) → Fin L, h (Fin.cons i σ') := by
                intro m i h
                rw [← (Fin.consEquiv (fun _ : Fin (m+2) => Fin L)).sum_comp, Fintype.sum_prod_type]
                simp [Fin.consEquiv]
              have hRG : ∀ m (a : Fin L → ℝ≥0∞) (h : (Fin (m+1) → Fin L) → ℝ≥0∞),
                  ∑ σ', a (σ' 0) * h σ' = ∑ j, a j * ∑ σ', (if σ' 0 = j then h σ' else 0) := by
                intro m a h
                simp_rw [Finset.mul_sum, mul_ite, mul_zero]
                rw [Finset.sum_comm]
                simp
              have hφi : ∀ n i, Integrable (D.φ n i) := by
                intro n i; apply Integrable.of_integral_ne_zero; rw [hD.φ_int]; norm_num
              have hφ1 : ∀ n i, ∫⁻ z, ENNReal.ofReal (D.φ n i z) = 1 := by
                intro n i
                rw [← ofReal_integral_eq_lintegral_ofReal (hφi n i) (Eventually.of_forall (hD.φ_nonneg n i)),
                  hD.φ_int, ENNReal.ofReal_one]
              have hwm : ∀ n m (σ : Fin (m+1) → Fin L), Measurable (fun ξ : Fin m → ℝ => pathWeight D n σ ξ) := by
                intro n m σ
                unfold pathWeight
                exact Finset.measurable_prod _ (fun t _ => measurable_const.mul
                  ((hD.φ_meas _ _).comp (measurable_pi_apply t)))
              have hw0 : ∀ n m (σ : Fin (m+1) → Fin L) ξ, 0 ≤ pathWeight D n σ ξ := by
                intro n m σ ξ
                exact Finset.prod_nonneg (fun t _ => mul_nonneg (hD.P_nonneg _ _) (hD.φ_nonneg _ _ _))
              have hmass : ∀ m n (i : Fin L), ∑ σ : Fin (m+1) → Fin L,
                  (if σ 0 = i then ∫⁻ ξ : Fin m → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) else 0) = 1 := by
                intro m
                induction m with
                | zero =>
                  intro n i
                  simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one,
                    lintegral_const, one_mul]
                  rw [Finset.sum_eq_single (fun _ => i)]
                  · rw [volume_pi, Measure.pi_empty_univ]; simp
                  · intro b _ hb; rw [if_neg]; intro h; apply hb; funext k; fin_cases k; exact h
                  · intro h; exact absurd (Finset.mem_univ _) h
                | succ m ih =>
                  intro n i
                  rw [hRI]
                  have : ∀ σ' : Fin (m+1) → Fin L, ∫⁻ ξ, ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) =
                      ENNReal.ofReal (D.P i (σ' 0)) * ∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ') := by
                    intro σ'
                    rw [hF4 _ (fun ξ => ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ))
                      (ENNReal.measurable_ofReal.comp (hwm _ _ _))]
                    simp_rw [hw]
                    have : ∀ z ξ', ENNReal.ofReal (D.P i (σ' 0) * D.φ n i z * pathWeight D (n + 1) σ' ξ') =
                        ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z) *
                          ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') := by
                      intro z ξ'
                      rw [ENNReal.ofReal_mul (mul_nonneg (hD.P_nonneg _ _) (hD.φ_nonneg _ _ _)),
                        ENNReal.ofReal_mul (hD.P_nonneg _ _)]
                    simp_rw [this]
                    calc ∫⁻ z, ∫⁻ ξ', ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z) *
                          ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
                        = ∫⁻ z, (ENNReal.ofReal (D.P i (σ' 0)) *
                            ∫⁻ ξ', ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')) * ENNReal.ofReal (D.φ n i z) := by
                          apply lintegral_congr; intro z
                          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
                          ring
                      _ = (ENNReal.ofReal (D.P i (σ' 0)) *
                            ∫⁻ ξ', ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')) * ∫⁻ z, ENNReal.ofReal (D.φ n i z) :=
                          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hD.φ_meas n i))
                      _ = _ := by rw [hφ1, mul_one]
                  simp_rw [this]
                  rw [hRG (a := fun j => ENNReal.ofReal (D.P i j))]
                  simp_rw [ih, mul_one]
                  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by simpa using hD.P_nonneg i j)]
                  simp [hD.P_sum]
              have hinitm : ∀ t, Measurable (fun ξ : Fin (t+1) → ℝ => Fin.init ξ) :=
                fun t => measurable_pi_lambda _ (fun j => measurable_pi_apply _)
              have hsm : ∀ (U : Policy L) x m, (∀ t < m, ∀ σ, Measurable (U t σ)) →
                  ∀ t ≤ m, ∀ σ : Fin (t+1) → Fin L, Measurable (surplus U x t σ) := by
                intro U x m hU t
                induction t with
                | zero => intro _ σ; exact measurable_const
                | succ t ih =>
                  intro ht σ
                  exact (((ih (by omega) _).comp (hinitm t)).add ((hU t (by omega) _).comp (hinitm t))).sub
                    (measurable_pi_apply _)
              have hocm : ∀ k i, Measurable (orderCost D k i) := by
                intro k i; unfold orderCost delta
                exact (measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const measurable_id)
                  measurable_const measurable_const)).add (measurable_const.mul measurable_id)
              have hfm : ∀ k i, Measurable (D.f k i) := by
                intro k i
                have := (hD.f_convex k i).continuousOn_interior
                rw [interior_univ] at this
                exact (continuousOn_univ.mp this).measurable
              have hpcm : ∀ (U : Policy L) x m n (σ : Fin (m+1) → Fin L), (∀ t < m, ∀ σ, Measurable (U t σ)) →
                  Measurable (fun ξ : Fin m → ℝ => pathCost D N n U x σ ξ) := by
                intro U x m n σ hU
                unfold pathCost
                have hid : ∀ t (h : t ≤ m), Measurable (fun ξ : Fin m → ℝ => initDemands ξ t h) :=
                  fun t h => measurable_pi_lambda _ (fun j => measurable_pi_apply _)
                refine (Finset.measurable_sum _ (fun t _ => ?_)).add ((hfm _ _).comp (hsm U x m hU m le_rfl σ))
                exact ((hocm _ _).comp ((hU t t.2 _).comp (hid t _))).add
                  ((hfm _ _).comp ((hsm U x m hU t t.2.le _).comp (hid t _)))
              have hpc0 : ∀ (U : Policy L) x m n (σ : Fin (m+1) → Fin L) ξ, (∀ t < m, ∀ σ ξ, 0 ≤ U t σ ξ) →
                  0 ≤ pathCost D N n U x σ ξ := by
                intro U x m n σ ξ hU
                unfold pathCost
                refine add_nonneg (Finset.sum_nonneg (fun t _ => add_nonneg ?_ (hD.f_nonneg _ _ _))) (hD.f_nonneg _ _ _)
                unfold orderCost
                have := hU t t.2 (initStates σ t t.2.le) (initDemands ξ t t.2.le)
                have hd : 0 ≤ delta (U t (initStates σ t t.2.le) (initDemands ξ t t.2.le)) := by
                  unfold delta; split_ifs <;> norm_num
                exact add_nonneg (mul_nonneg (hD.K_nonneg _ _) hd) (mul_nonneg (hD.c_nonneg _ _) this)
              -- J decomposition
              have hJd : ∀ m n i x (U : Policy L), (∀ t < m+1, ∀ σ ξ, 0 ≤ U t σ ξ) →
                  (∀ t < m+1, ∀ σ, Measurable (U t σ)) →
                  (∑ σ : Fin (m+2) → Fin L, if σ 0 = i then ∫⁻ ξ : Fin (m+1) → ℝ,
                    ENNReal.ofReal (pathWeight D n σ ξ) * ENNReal.ofReal (pathCost D N n U x σ ξ) else 0) =
                  ENNReal.ofReal (orderCost D n i (U 0 (fun _ => i) (fun k => k.elim0)) + D.f n i x) +
                    ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ∑ j, ENNReal.ofReal (D.P i j) *
                      ∑ σ' : Fin (m+1) → Fin L, if σ' 0 = j then ∫⁻ ξ' : Fin m → ℝ,
                        ENNReal.ofReal (pathWeight D (n+1) σ' ξ') * ENNReal.ofReal (pathCost D N (n+1)
                          (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ'))
                          (x + U 0 (fun _ => i) (fun k => k.elim0) - z) σ' ξ') else 0 := by
                intro m n i x U hU0 hUm
                set u0 := U 0 (fun _ => i) (fun k => k.elim0) with hu0
                set c0 := orderCost D n i u0 + D.f n i x with hc0
                have hc00 : 0 ≤ c0 := by
                  have hd : 0 ≤ delta u0 := by unfold delta; split_ifs <;> norm_num
                  exact add_nonneg (add_nonneg (mul_nonneg (hD.K_nonneg _ _) hd)
                    (mul_nonneg (hD.c_nonneg _ _) (hU0 0 (by omega) _ _))) (hD.f_nonneg _ _ _)
                rw [hRI]
                have hg : ∀ σ' : Fin (m+1) → Fin L, Measurable (fun ξ : Fin (m+1) → ℝ =>
                    ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) *
                      ENNReal.ofReal (pathCost D N n U x (Fin.cons i σ') ξ)) := fun σ' =>
                  (ENNReal.measurable_ofReal.comp (hwm _ _ _)).mul
                    (ENNReal.measurable_ofReal.comp (hpcm U x (m+1) n _ hUm))
                simp_rw [fun σ' => hF4 _ _ (hg σ')]
                have hgz : ∀ σ' : Fin (m+1) → Fin L, Measurable (fun z => ∫⁻ ξ' : Fin m → ℝ,
                    ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) *
                      ENNReal.ofReal (pathCost D N n U x (Fin.cons i σ') (Fin.cons z ξ'))) := by
                  intro σ'
                  have hc : Measurable (fun p : ℝ × (Fin m → ℝ) => (Fin.cons p.1 p.2 : Fin (m+1) → ℝ)) := by
                    have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm.measurable
                    convert this using 1
                    funext p
                    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
                  exact ((hg σ').comp hc).lintegral_prod_right'
                rw [← lintegral_finsetSum _ (fun σ' _ => hgz σ')]
                have hpt : ∀ z (σ' : Fin (m+1) → Fin L), ∫⁻ ξ' : Fin m → ℝ,
                    ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) *
                      ENNReal.ofReal (pathCost D N n U x (Fin.cons i σ') (Fin.cons z ξ')) =
                    ENNReal.ofReal (D.φ n i z) * (ENNReal.ofReal (D.P i (σ' 0)) *
                      (ENNReal.ofReal c0 * (∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ')) +
                      ∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ') * ENNReal.ofReal (pathCost D N (n+1)
                          (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ')) (x + u0 - z) σ' ξ'))) := by
                  intro z σ'
                  have e : ∀ ξ', ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) *
                      ENNReal.ofReal (pathCost D N n U x (Fin.cons i σ') (Fin.cons z ξ')) =
                      (ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (D.P i (σ' 0))) *
                      (ENNReal.ofReal c0 * ENNReal.ofReal (pathWeight D (n+1) σ' ξ') +
                        ENNReal.ofReal (pathWeight D (n+1) σ' ξ') * ENNReal.ofReal (pathCost D N (n+1)
                          (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ')) (x + u0 - z) σ' ξ')) := by
                    intro ξ'
                    rw [hw, hpc, ENNReal.ofReal_add hc00 (hpc0 _ _ _ _ _ _ (fun t ht σ ξ => hU0 _ (by omega) _ _)),
                      ENNReal.ofReal_mul (mul_nonneg (hD.P_nonneg _ _) (hD.φ_nonneg _ _ _)),
                      ENNReal.ofReal_mul (hD.P_nonneg _ _)]
                    ring
                  simp_rw [e]
                  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
                    lintegral_add_left (f := fun a => ENNReal.ofReal c0 * ENNReal.ofReal (pathWeight D (n+1) σ' a))
                      (by exact (ENNReal.measurable_ofReal.comp (hwm _ _ _)).const_mul _),
                    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                  ring
                simp_rw [hpt, ← Finset.mul_sum]
                have hsplit : ∀ z, ∑ σ' : Fin (m+1) → Fin L, ENNReal.ofReal (D.P i (σ' 0)) *
                      (ENNReal.ofReal c0 * (∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ')) +
                      ∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ') * ENNReal.ofReal (pathCost D N (n+1)
                          (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ')) (x + u0 - z) σ' ξ')) =
                    ENNReal.ofReal c0 + ∑ j, ENNReal.ofReal (D.P i j) *
                      ∑ σ' : Fin (m+1) → Fin L, if σ' 0 = j then ∫⁻ ξ' : Fin m → ℝ,
                        ENNReal.ofReal (pathWeight D (n+1) σ' ξ') * ENNReal.ofReal (pathCost D N (n+1)
                          (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ'))
                          (x + u0 - z) σ' ξ') else 0 := by
                  intro z
                  simp_rw [mul_add, Finset.sum_add_distrib]
                  congr 1
                  · have := hRG m (fun j => ENNReal.ofReal (D.P i j))
                      (fun σ' => ENNReal.ofReal c0 * (∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ')))
                    rw [this]
                    have h2 : ∀ j, (∑ σ' : Fin (m+1) → Fin L, if σ' 0 = j then
                        ENNReal.ofReal c0 * ∫⁻ ξ', ENNReal.ofReal (pathWeight D (n+1) σ' ξ') else 0) =
                        ENNReal.ofReal c0 := by
                      intro j
                      conv_rhs => rw [← mul_one (ENNReal.ofReal c0), ← hmass m (n+1) j, Finset.mul_sum]
                      apply Finset.sum_congr rfl; intro σ' _; split_ifs <;> simp
                    simp_rw [h2]
                    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.P_nonneg i j), hD.P_sum,
                      ENNReal.ofReal_one, one_mul]
                  · exact hRG m (fun j => ENNReal.ofReal (D.P i j)) _
                simp_rw [hsplit, mul_add]
                rw [lintegral_add_left (f := fun a => ENNReal.ofReal (D.φ n i a) * ENNReal.ofReal c0)
                  (by exact (ENNReal.measurable_ofReal.comp (hD.φ_meas n i)).mul_const _),
                  lintegral_mul_const _ (by exact ENNReal.measurable_ofReal.comp (hD.φ_meas n i)), hφ1, one_mul]
              have hver : ∀ n0 ≤ N, ∀ i0 x0, x0 ≤ T.B → CapAdmissible D T N n0 i0 x0 (feedback R n0 x0) ∧
                  J D N n0 i0 x0 (feedback R n0 x0) = ENNReal.ofReal (V n0 i0 x0) ∧
                  ∀ U : Policy L, CapAdmissible D T N n0 i0 x0 U →
                    J D N n0 i0 x0 (feedback R n0 x0) ≤ J D N n0 i0 x0 U := by
                intro n0 hn0 i0 x0 hx0
                have hsfb : ∀ n x t (σ : Fin (t+1) → Fin L) (ξ : Fin t → ℝ),
                    surplus (feedback R n x) x t σ ξ = fbSurplus R n x t σ ξ := by
                  intro n x t
                  induction t with
                  | zero => intro σ ξ; rfl
                  | succ t ih => intro σ ξ; simp only [surplus, fbSurplus, ih]; rfl
                have hfbS : ∀ n x i z t (σ : Fin (t+1) → Fin L) (ξ : Fin t → ℝ),
                    fbSurplus R n x (t+1) (Fin.cons i σ) (Fin.cons z ξ) =
                      fbSurplus R (n+1) (x + R n i x - z) t σ ξ := by
                  intro n x i z t
                  induction t with
                  | zero =>
                    intro σ ξ
                    simp only [fbSurplus, add_zero]
                    rfl
                  | succ t ih =>
                    intro σ ξ
                    rw [fbSurplus, hinitc, hinitc, ih]
                    simp only [fbSurplus]
                    rw [show n + (t + 1) = n + 1 + t by ring]
                    rfl
                have hfbshift : ∀ n x i z, (fun t σ' ξ' => feedback R n x (t+1) (Fin.cons i σ') (Fin.cons z ξ')) =
                    feedback R (n+1) (x + R n i x - z) := by
                  intro n x i z
                  funext t σ' ξ'
                  simp only [feedback]
                  rw [hfbS, show n + (t + 1) = n + 1 + t by ring]
                  rfl
                have hfb0 : ∀ n x i, feedback R n x 0 (fun _ => i) (fun k => k.elim0) = R n i x := by
                  intro n x i; rfl
                have hfbm : ∀ n x t (σ : Fin (t+1) → Fin L), Measurable (fbSurplus R n x t σ) := by
                  intro n x t
                  induction t with
                  | zero => intro σ; exact measurable_const
                  | succ t ih =>
                    intro σ
                    exact (((ih _).comp (hinitm t)).add ((hRm _ _).comp ((ih _).comp (hinitm t)))).sub
                      (measurable_pi_apply _)
                have hfbB : ∀ n x, x ≤ T.B → ∀ t (σ : Fin (t+1) → Fin L) (ξ : Fin t → ℝ), (∀ s, 0 ≤ ξ s) →
                    n + t ≤ N → fbSurplus R n x t σ ξ ≤ T.B := by
                  intro n x hx t
                  induction t with
                  | zero => intro σ ξ _ _; exact hx
                  | succ t ih =>
                    intro σ ξ hξ ht
                    have h1 := ih (Fin.init σ) (Fin.init ξ) (fun s => hξ _) (by omega)
                    have h2 := (hRact (n+t) (by omega) (Fin.init σ (Fin.last t)) _ h1).2.2
                    simp only [fbSurplus]
                    linarith [hξ (Fin.last t)]
                have hadm : ∀ n ≤ N, ∀ i x, x ≤ T.B → CapAdmissible D T N n i x (feedback R n x) := by
                  intro n hn i x hx
                  refine ⟨fun t ht => ⟨fun σ ξ => hR0 _ (by omega) _ _, fun σ => (hRm _ _).comp (hfbm _ _ _ _)⟩, ?_⟩
                  intro σ _
                  rw [demandPathLaw, ae_withDensity_iff (hwm _ _ _).ennreal_ofReal]
                  refine Eventually.of_forall (fun ξ hξ t => ?_)
                  have hpos : 0 < pathWeight D n σ ξ := by
                    rcases (hw0 n _ σ ξ).lt_or_eq with h | h
                    · exact h
                    · exact absurd (by rw [← h, ENNReal.ofReal_zero]) hξ
                  have hξ0 : ∀ s, 0 ≤ ξ s := by
                    intro s
                    by_contra hneg
                    push Not at hneg
                    have : pathWeight D n σ ξ = 0 := by
                      unfold pathWeight
                      apply Finset.prod_eq_zero (Finset.mem_univ s)
                      rw [hD.φ_neg _ _ _ hneg, mul_zero]
                    exact absurd this hpos.ne'
                  rw [hsfb]
                  exact hRact (n + t) (by omega) _ _ (hfbB n x hx t _ _ (fun s => hξ0 _) (by omega))
                obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℕ → Fin L → ℝ → Policy L → ℝ≥0∞, G = fun k n i x U =>
                    ∑ σ : Fin (k+1) → Fin L, if σ 0 = i then ∫⁻ ξ : Fin k → ℝ,
                      ENNReal.ofReal (pathWeight D n σ ξ) * ENNReal.ofReal (pathCost D N n U x σ ξ) else 0 :=
                  ⟨_, rfl⟩
                have hGJ : ∀ n i x U, J D N n i x U = G (N - n) n i x U := by
                  intro n i x U; rw [hGdef]; rfl
                obtain ⟨CA, hCAdef⟩ : ∃ CA : ℕ → ℕ → Fin L → ℝ → Policy L → Prop, CA = fun k n i x U =>
                    Admissible k U ∧ ∀ σ : Fin (k + 1) → Fin L, σ 0 = i →
                      ∀ᵐ ξ ∂demandPathLaw D n σ, ∀ t : Fin k,
                        capAction D T (n + t) (σ t.castSucc)
                          (surplus U x t (initStates σ t t.2.le) (initDemands ξ t t.2.le))
                          (U t (initStates σ t t.2.le) (initDemands ξ t t.2.le)) := ⟨_, rfl⟩
                have hCA : ∀ n i x U, CapAdmissible D T N n i x U ↔ CA (N - n) n i x U := by
                  intro n i x U; rw [hCAdef]; rfl
                have hG0 : ∀ n i x U, G 0 n i x U = ENNReal.ofReal (D.f N i x) := by
                  intro n i x U
                  rw [hGdef]
                  simp only [pathWeight, pathCost, Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty,
                    ENNReal.ofReal_one, one_mul, zero_add]
                  rw [Finset.sum_eq_single (fun _ => i)]
                  · simp only [surplus]; rw [lintegral_const, volume_pi, Measure.pi_empty_univ]; simp
                  · intro b _ hb; rw [if_neg]; intro h; apply hb; funext k; fin_cases k; exact h
                  · intro h; exact absurd (Finset.mem_univ _) h
                have hFconv : ∀ n < N, ∀ i y, y ≤ T.B → ENNReal.ofReal (F D n (V (n+1)) i y) =
                    ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ∑ j, ENNReal.ofReal (D.P i j) *
                      ENNReal.ofReal (V (n+1) j (y - z)) := by
                  intro n hn i y hy
                  have hI : ∀ j, Integrable (fun z => V (n+1) j (y - z) * D.φ n i z) (volume.restrict (Set.Ioi 0)) := by
                    intro j
                    obtain ⟨hl, ⟨C, hC⟩, -⟩ := hVprop (n+1) (by omega) j
                    exact hInt (V (n+1) j) C hl (fun x hx => hVnn (N - (n+1)) (n+1) (by omega) j x hx) hC n i y hy
                  have hnn : ∀ j z, 0 < z → 0 ≤ V (n+1) j (y - z) := fun j z hz =>
                    hVnn (N - (n+1)) (n+1) (by omega) j _ (by linarith only [hz, hy])
                  have hsupp : (Function.support fun z => ENNReal.ofReal (D.φ n i z) * ∑ j, ENNReal.ofReal (D.P i j) *
                      ENNReal.ofReal (V (n+1) j (y - z))) ⊆ Set.Ici 0 := by
                    intro z hz
                    by_contra h
                    apply hz
                    simp only [Set.mem_Ici, not_le] at h
                    simp [hD.φ_neg n i z h]
                  rw [← setLIntegral_eq_of_support_subset hsupp, ← setLIntegral_congr Ioi_ae_eq_Ici]
                  unfold F
                  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hD.P_nonneg i j)
                    (setIntegral_nonneg measurableSet_Ioi (fun z hz => mul_nonneg (hnn j z hz) (hD.φ_nonneg n i z))))]
                  have e1 : ∀ j, ENNReal.ofReal (D.P i j * ∫ z in Set.Ioi 0, V (n+1) j (y - z) * D.φ n i z) =
                      ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (D.P i j) * ENNReal.ofReal (V (n+1) j (y - z) * D.φ n i z) := by
                    intro j
                    rw [ENNReal.ofReal_mul (hD.P_nonneg i j), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                      ofReal_integral_eq_lintegral_ofReal (hI j)]
                    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
                    exact mul_nonneg (hnn j z hz) (hD.φ_nonneg n i z)
                  simp_rw [e1]
                  rw [← lintegral_finsetSum' _ (fun j _ =>
                    ((hI j).aestronglyMeasurable.aemeasurable.ennreal_ofReal).const_mul _)]
                  apply setLIntegral_congr_fun measurableSet_Ioi
                  intro z hz
                  simp only [Finset.mul_sum]
                  apply Finset.sum_congr rfl; intro j _
                  rw [ENNReal.ofReal_mul (hnn j z hz)]; ring
                have hfirst : ∀ m n i x (U : Policy L), CA (m+1) n i x U →
                    capAction D T n i x (U 0 (fun _ => i) (fun k => k.elim0)) := by
                  intro m n i x U hU
                  rw [hCAdef] at hU
                  obtain ⟨-, hA⟩ := hU
                  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero
                    (by rw [hmass (m+1) n i]; exact one_ne_zero)
                  by_cases hσi : σ 0 = i
                  swap
                  · exact absurd (if_neg hσi) hσ
                  rw [if_pos hσi] at hσ
                  have hne : demandPathLaw D n σ ≠ 0 := by
                    intro h0; apply hσ
                    have := congrArg (fun μ : Measure (Fin (m+1) → ℝ) => μ Set.univ) h0
                    simpa [demandPathLaw, withDensity_apply _ MeasurableSet.univ] using this
                  have := ae_neBot.2 hne
                  obtain ⟨ξ, hξ⟩ := (hA σ hσi).exists
                  have h0 := hξ ⟨0, by omega⟩
                  have e1 : initStates σ 0 (by omega) = fun _ => i := by
                    funext k; fin_cases k; exact hσi
                  have e2 : initDemands ξ 0 (by omega) = fun k => k.elim0 := funext (fun k => k.elim0)
                  have e3 : σ (Fin.castSucc ⟨0, by omega⟩) = i := hσi
                  rw [e3] at h0
                  exact (by simpa [e1, e2, surplus] using h0)
                have hrest : ∀ m n i x (U : Policy L), CA (m+1) n i x U →
                    ∀ᵐ z, D.φ n i z ≠ 0 → ∀ j, D.P i j ≠ 0 →
                      CA m (n+1) j (x + U 0 (fun _ => i) (fun k => k.elim0) - z)
                        (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ')) := by
                  intro m n i x U hU
                  rw [hCAdef] at hU
                  obtain ⟨hAd, hA⟩ := hU
                  have hσ' : ∀ σ' : Fin (m+1) → Fin L, ∀ᵐ z, D.φ n i z ≠ 0 → D.P i (σ' 0) ≠ 0 →
                      ∀ᵐ ξ' ∂demandPathLaw D (n+1) σ', ∀ t : Fin m, capAction D T (n + 1 + t) (σ' t.castSucc)
                        (surplus (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ'))
                          (x + U 0 (fun _ => i) (fun k => k.elim0) - z) t (initStates σ' t t.2.le)
                          (initDemands ξ' t t.2.le))
                        (U (t+1) (Fin.cons i (initStates σ' t t.2.le)) (Fin.cons z (initDemands ξ' t t.2.le))) := by
                    intro σ'
                    have h1 := hA (Fin.cons i σ') rfl
                    rw [demandPathLaw, ae_withDensity_iff (hwm _ _ _).ennreal_ofReal] at h1
                    have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
                    have h2 := Measure.ae_ae_of_ae_prod (hp.quasiMeasurePreserving.ae h1)
                    filter_upwards [h2] with z hz hφ hP
                    rw [demandPathLaw, ae_withDensity_iff (hwm _ _ _).ennreal_ofReal]
                    filter_upwards [hz] with ξ' hξ' hw' t
                    have hcons : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm (z, ξ') =
                        Fin.cons z ξ' := by
                      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
                    rw [hcons, hw] at hξ'
                    have hpos : ENNReal.ofReal (D.P i (σ' 0) * D.φ n i z * pathWeight D (n + 1) σ' ξ') ≠ 0 := by
                      rw [ENNReal.ofReal_ne_zero_iff] at hw' ⊢
                      exact mul_pos (mul_pos (lt_of_le_of_ne (hD.P_nonneg _ _) (Ne.symm hP))
                        (lt_of_le_of_ne (hD.φ_nonneg _ _ _) (Ne.symm hφ))) hw'
                    have h3 := hξ' hpos t.succ
                    simp only [Fin.val_succ] at h3
                    rw [hIS, hID, hsur, ← Fin.succ_castSucc, Fin.cons_succ,
                      show n + (↑t + 1) = n + 1 + ↑t by ring] at h3
                    exact h3
                  have hall := Filter.eventually_all.2 hσ'
                  filter_upwards [hall] with z hz hφ j hP
                  rw [hCAdef]
                  refine ⟨fun t ht => ⟨fun σ ξ => (hAd (t+1) (by omega)).1 _ _,
                    fun σ => ((hAd (t+1) (by omega)).2 _).comp ?_⟩, ?_⟩
                  · exact measurable_pi_iff.2 (fun k => by
                      refine Fin.cases ?_ (fun k => ?_) k
                      · exact measurable_const
                      · exact measurable_pi_apply k)
                  · intro σ' hσ0
                    subst hσ0
                    exact hz σ' hφ hP
                have main : ∀ m n, n + m = N → ∀ i x, x ≤ T.B →
                    G m n i x (feedback R n x) = ENNReal.ofReal (V n i x) ∧
                    ∀ U, CA m n i x U → ENNReal.ofReal (V n i x) ≤ G m n i x U := by
                  intro m
                  induction m with
                  | zero =>
                    intro n hn i x hx
                    have hnN : n = N := by omega
                    subst hnN
                    exact ⟨by rw [hG0, hVN], fun U _ => by rw [hG0, hVN]⟩
                  | succ m ih =>
                    intro n hn i x hx
                    have hnN : n < N := by omega
                    have hGs : ∀ U : Policy L, (∀ t < m+1, ∀ σ ξ, 0 ≤ U t σ ξ) →
                        (∀ t < m+1, ∀ σ, Measurable (U t σ)) →
                        G (m+1) n i x U = ENNReal.ofReal (orderCost D n i (U 0 (fun _ => i) (fun k => k.elim0)) +
                          D.f n i x) + ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ∑ j, ENNReal.ofReal (D.P i j) *
                            G m (n+1) j (x + U 0 (fun _ => i) (fun k => k.elim0) - z)
                              (fun t σ' ξ' => U (t+1) (Fin.cons i σ') (Fin.cons z ξ')) := by
                      intro U h0 h1
                      simp only [hGdef]; exact hJd m n i x U h0 h1
                    obtain ⟨hVe, hVmin⟩ := h3 n hnN i x hx
                    have hoc0 : ∀ u, 0 ≤ u → 0 ≤ orderCost D n i u := by
                      intro u hu; unfold orderCost
                      have hd : 0 ≤ delta u := by unfold delta; split_ifs <;> norm_num
                      exact add_nonneg (mul_nonneg (hD.K_nonneg _ _) hd) (mul_nonneg (hD.c_nonneg _ _) hu)
                    have hFn : ∀ y, y ≤ T.B → 0 ≤ F D n (V (n+1)) i y := fun y hy =>
                      hFnn n _ i y (fun j w hw => hVnn m (n+1) (by omega) j w (hw.trans hy))
                    have hsplit : ∀ u, capAction D T n i x u →
                        ENNReal.ofReal (D.f n i x + orderCost D n i u + F D n (V (n+1)) i (x + u)) =
                        ENNReal.ofReal (orderCost D n i u + D.f n i x) + ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                          ∑ j, ENNReal.ofReal (D.P i j) * ENNReal.ofReal (V (n+1) j (x + u - z)) := by
                      intro u hu
                      rw [← hFconv n hnN i (x+u) hu.2.2, ← ENNReal.ofReal_add
                        (add_nonneg (hoc0 u hu.1) (hD.f_nonneg _ _ _)) (hFn _ hu.2.2)]
                      congr 1; ring
                    have hRa := hRact n hnN i x hx
                    constructor
                    · rw [hGs (feedback R n x) (fun t ht σ ξ => hR0 _ (by omega) _ _) (fun t _ σ => (hRm _ _).comp (hfbm _ _ _ _)), hfb0,
                        hVe, hsplit _ hRa]
                      congr 1
                      apply lintegral_congr; intro z
                      rw [hfbshift n x i z]
                      by_cases hz : z < 0
                      · rw [hD.φ_neg n i z hz]; simp
                      · push Not at hz
                        congr 1; apply Finset.sum_congr rfl; intro j _
                        rw [(ih (n+1) (by omega) j _ (by linarith [hRa.2.2])).1]
                    · intro U hU
                      have hUc := hfirst m n i x U hU
                      have hrest' := hrest m n i x U hU
                      rw [hCAdef] at hU
                      have hAd := hU.1
                      rw [hGs U (fun t ht => (hAd t ht).1) (fun t ht => (hAd t ht).2)]
                      calc ENNReal.ofReal (V n i x) ≤ ENNReal.ofReal (D.f n i x +
                            orderCost D n i (U 0 (fun _ => i) (fun k => k.elim0)) +
                            F D n (V (n+1)) i (x + U 0 (fun _ => i) (fun k => k.elim0))) := by
                            apply ENNReal.ofReal_le_ofReal; rw [hVe]; linarith [hVmin _ hUc]
                        _ = _ := hsplit _ hUc
                        _ ≤ _ := by
                            refine add_le_add le_rfl ?_
                            apply lintegral_mono_ae
                            filter_upwards [hrest'] with z hz
                            by_cases hφ : D.φ n i z = 0
                            · simp [hφ]
                            · have hz0 : 0 ≤ z := by
                                by_contra h; push Not at h; exact hφ (hD.φ_neg n i z h)
                              refine mul_le_mul' le_rfl (Finset.sum_le_sum (fun j _ => ?_))
                              by_cases hP : D.P i j = 0
                              · simp [hP]
                              · exact mul_le_mul' le_rfl
                                  ((ih (n+1) (by omega) j _ (by linarith [hUc.2.2])).2 _ (hz hφ j hP))
                have hm := main (N - n0) n0 (by omega) i0 x0 hx0
                refine ⟨hadm n0 hn0 i0 x0 hx0, ?_, ?_⟩
                · rw [hGJ]; exact hm.1
                · intro U hU
                  rw [hGJ, hGJ, hm.1]
                  exact hm.2 U ((hCA _ _ _ _).1 hU)
              obtain ⟨h1, h3, h4⟩ := hver n hn i x hx
              refine ⟨h1, hVnn (N - n) n (by omega) i x hx, h3, ?_, h4⟩
              apply le_antisymm
              · exact (iInf₂_le _ h1).trans_eq h3
              · exact le_iInf₂ fun U hU => h3 ▸ h4 U hU
