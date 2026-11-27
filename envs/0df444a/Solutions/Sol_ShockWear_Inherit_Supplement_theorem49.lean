-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem49
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:19.825813+00:00
-- url     : https://prove2.me/submissions/cc1a1ef9-2872-42ee-9f9f-26d3b4929749

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity

open ShockWear
open ShockWear.Inherit
open ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (lam : ℝ) (hlam : 0 < lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    (IsPF2Function (fun x => (μ (Set.Iic x)).toReal) →
      IsTP 2 Set.univ Set.univ (fun k x => ShockWear.CumDamage.cdfPow μ k x)) ∧
    (IsTP 2 Set.univ Set.univ (fun k x => ShockWear.CumDamage.cdfPow μ k x) →
      ∀ x : ℝ, IsPF2Sequence (fun k => ShockWear.CumDamage.cdfPow μ k x)) ∧
    (∀ x : ℝ, IsPF2Sequence (fun k => ShockWear.CumDamage.cdfPow μ k x) →
      IsIHR (ShockWear.CumDamage.shockSurv lam (fun k => ShockWear.CumDamage.cdfPow μ k x))) := by
        have P1 : ∀ (G : ℝ → ℝ), (∀ x, 0 ≤ G x) → Monotone G →
            (∀ x, ContinuousWithinAt G (Set.Ici x) x) →
            (∀ u w, G u * G w ≤ G ((u + w) / 2) ^ 2) →
            ∀ x1 x2 y, x1 ≤ x2 → 0 ≤ y → G (x1 - y) * G x2 ≤ G (x2 - y) * G x1 := by
          intro G hG0 hmono hrc hmid
          have seq : ∀ a : ℕ → ℝ, (∀ k, 0 ≤ a k) → (∀ k, a k ≤ a (k+1)) →
              (∀ k, a k * a (k+2) ≤ a (k+1)^2) → ∀ N p, a 0 * a (p+N) ≤ a p * a N := by
            intro a h0 h1 h2
            have mono : Monotone a := monotone_nat_of_le_succ h1
            have L1 : ∀ N p, a (N+p+1) * a N ≤ a (N+p) * a (N+1) := by
              intro N p
              induction p with
              | zero => simp only [Nat.add_zero]; linarith [mul_comm (a (N+1)) (a N)]
              | succ p ih =>
                rcases (h0 (N+p)).eq_or_lt with hz | hpos
                · have : a N = 0 := le_antisymm (hz ▸ mono (by omega)) (h0 N)
                  rw [this, mul_zero]; exact mul_nonneg (h0 _) (h0 _)
                · have e1 := h2 (N+p)
                  have e3 : a (N+(p+1)+1) * a N * a (N+p) ≤ a (N+(p+1)) * a (N+1) * a (N+p) := by
                    have r1 : N+(p+1)+1 = N+p+2 := by omega
                    have r2 : N+(p+1) = N+p+1 := by omega
                    rw [r1, r2]
                    nlinarith [mul_le_mul_of_nonneg_right e1 (h0 N),
                      mul_le_mul_of_nonneg_left ih (h0 (N+p+1))]
                  exact le_of_mul_le_mul_right e3 hpos
            intro N p
            induction N with
            | zero => simp only [Nat.add_zero]; linarith [mul_comm (a 0) (a p)]
            | succ N ih =>
              rcases (h0 N).eq_or_lt with hz | hpos
              · have : a 0 = 0 := le_antisymm (hz ▸ mono (Nat.zero_le N)) (h0 0)
                rw [this, zero_mul]; exact mul_nonneg (h0 _) (h0 _)
              · have e1 := L1 N p
                have e3 : a 0 * a (p + (N+1)) * a N ≤ a p * a (N+1) * a N := by
                  have r1 : p + (N+1) = N+p+1 := by omega
                  have r2 : p + N = N + p := by omega
                  rw [r1]; rw [r2] at ih
                  nlinarith [mul_le_mul_of_nonneg_left e1 (h0 0), mul_le_mul_of_nonneg_right ih (h0 (N+1))]
                exact le_of_mul_le_mul_right e3 hpos
          intro x1 x2 y hx hy
          rcases hy.eq_or_lt with hy0 | hypos
          · subst hy0; simp only [sub_zero]; linarith [mul_comm (G x1) (G x2)]
          have key : ∀ n : ℕ, G (x1 - y) * G x2 ≤ G (x2 - y + y * (1 / ((n:ℝ) + 1))) * G x1 := by
            intro n
            set h := y * (1 / ((n:ℝ) + 1)) with hh
            have hpos : 0 < h := by positivity
            set p := ⌈(x2 - x1) / h⌉₊ with hp
            have hp1 : (x2 - x1) / h ≤ p := Nat.le_ceil _
            have hp2 : (p:ℝ) < (x2 - x1) / h + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hpos.le)
            have hph1 : x2 - x1 ≤ p * h := by rwa [div_le_iff₀ hpos] at hp1
            have hph2 : (p:ℝ) * h < x2 - x1 + h := by
              have := mul_lt_mul_of_pos_right hp2 hpos
              rwa [add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at this
            have yN : ((n+1:ℕ):ℝ) * h = y := by rw [hh]; push_cast; field_simp
            set a : ℕ → ℝ := fun j => G (x1 - y + (j:ℝ) * h) with ha
            have s := seq a (fun k => hG0 _)
              (fun k => hmono (by push_cast; nlinarith))
              (fun k => by
                have := hmid (x1 - y + (k:ℝ)*h) (x1 - y + ((k+2:ℕ):ℝ)*h)
                have e : (x1 - y + (k:ℝ)*h + (x1 - y + ((k+2:ℕ):ℝ)*h))/2 = x1 - y + ((k+1:ℕ):ℝ)*h := by
                  push_cast; ring
                rw [e] at this; exact this) (n+1) p
            have A0 : a 0 = G (x1 - y) := by simp [a]
            have A1 : a (n+1) = G x1 := by simp only [a]; congr 1; linarith [yN]
            have A2 : a (p + (n+1)) = G (x1 + p*h) := by
              simp only [a]; congr 1
              have : ((p + (n+1) : ℕ):ℝ) * h = p * h + ((n+1:ℕ):ℝ) * h := by push_cast; ring
              rw [this]; linarith [yN]
            have A3 : a p = G (x1 - y + p*h) := rfl
            rw [A0, A1, A2, A3] at s
            calc G (x1 - y) * G x2 ≤ G (x1 - y) * G (x1 + p*h) :=
                  mul_le_mul_of_nonneg_left (hmono (by linarith)) (hG0 _)
              _ ≤ G (x1 - y + p*h) * G x1 := s
              _ ≤ G (x2 - y + h) * G x1 := mul_le_mul_of_nonneg_right (hmono (by linarith)) (hG0 _)
          have tend : Filter.Tendsto (fun n : ℕ => G (x2 - y + y * (1 / ((n:ℝ) + 1))) * G x1)
              Filter.atTop (nhds (G (x2 - y) * G x1)) := by
            apply Filter.Tendsto.mul_const
            have h1 : Filter.Tendsto (fun n : ℕ => x2 - y + y * (1 / ((n:ℝ) + 1))) Filter.atTop
                (nhdsWithin (x2 - y) (Set.Ici (x2 - y))) := by
              apply tendsto_nhdsWithin_iff.mpr
              constructor
              · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul y).const_add (x2 - y)
                simpa using this
              · exact Filter.Eventually.of_forall fun n => by
                  simp only [Set.mem_Ici]; have : 0 ≤ y * (1 / ((n:ℝ) + 1)) := by positivity
                  linarith
            exact (hrc (x2 - y)).tendsto.comp h1
          exact ge_of_tendsto tend (Filter.Eventually.of_forall key)
        have P2 : ∀ (f g h : ℝ → ℝ), Measurable f → Measurable g → Measurable h →
            (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) →
            (∀ x, f x ≤ 1) → (∀ x, g x ≤ 1) → (∀ x, h x ≤ 1) →
            ∫⁻ x, ENNReal.ofReal (f x) ≠ ∞ → ∫⁻ x, ENNReal.ofReal (g x) ≠ ∞ →
            ∫⁻ x, ENNReal.ofReal (h x) ≠ ∞ →
            (∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) →
            (∫⁻ x, ENNReal.ofReal (f x)) * (∫⁻ x, ENNReal.ofReal (g x))
              ≤ (∫⁻ x, ENNReal.ofReal (h x)) ^ 2 := by
          intro f g h hf hg hh hf0 hg0 hh0 hf1 hg1 hh1 hfi hgi hhi hPL
          have BM : ∀ A B C : Set ℝ, MeasurableSet A → MeasurableSet B → A.Nonempty → B.Nonempty →
              (∀ a ∈ A, ∀ b ∈ B, (a + b) / 2 ∈ C) → volume A + volume B ≤ 2 * volume C := by
            intro A B C hA hB ⟨a0, ha0⟩ ⟨b0, hb0⟩ hC
            have key : ∀ K L : Set ℝ, K ⊆ A → IsCompact K → L ⊆ B → IsCompact L →
                volume K + volume L ≤ 2 * volume C := by
              intro K L hKA hK hLB hL
              set K' := insert a0 K with hK'def
              set L' := insert b0 L with hL'def
              have hK' : IsCompact K' := hK.insert a0
              have hL' : IsCompact L' := hL.insert b0
              have hK'ne : K'.Nonempty := Set.insert_nonempty _ _
              have hL'ne : L'.Nonempty := Set.insert_nonempty _ _
              have hK'A : K' ⊆ A := Set.insert_subset ha0 hKA
              have hL'B : L' ⊆ B := Set.insert_subset hb0 hLB
              set k1 := sInf K' with hk1def
              set l2 := sSup L' with hl2def
              have hk1 : k1 ∈ K' := hK'.sInf_mem hK'ne
              have hl2 : l2 ∈ L' := hL'.sSup_mem hL'ne
              have hk1le : ∀ k ∈ K', k1 ≤ k := fun k hk => csInf_le hK'.bddBelow hk
              have hl2ge : ∀ l ∈ L', l ≤ l2 := fun l hl => le_csSup hL'.bddAbove hl
              set S1 := (fun z : ℝ => 2 * z) ⁻¹' ((fun w : ℝ => w + -l2) ⁻¹' K') with hS1
              set S2 := (fun z : ℝ => 2 * z) ⁻¹' ((fun w : ℝ => w + -k1) ⁻¹' L') with hS2
              have v1 : volume S1 = ENNReal.ofReal (|(2:ℝ)⁻¹|) * volume K' := by
                rw [hS1, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add_right]
              have v2 : volume S2 = ENNReal.ofReal (|(2:ℝ)⁻¹|) * volume L' := by
                rw [hS2, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add_right]
              have s1C : S1 ⊆ C := by
                intro z hz
                simp only [hS1, Set.mem_preimage] at hz
                have := hC _ (hK'A hz) _ (hL'B hl2)
                convert this using 1; ring
              have s2C : S2 ⊆ C := by
                intro z hz
                simp only [hS2, Set.mem_preimage] at hz
                have := hC _ (hK'A hk1) _ (hL'B hz)
                convert this using 1; ring
              have s12 : S1 ∩ S2 ⊆ {(k1 + l2) / 2} := by
                rintro z ⟨h1, h2⟩
                simp only [hS1, hS2, Set.mem_preimage] at h1 h2
                have a1 := hk1le _ h1
                have a2 := hl2ge _ h2
                rw [Set.mem_singleton_iff]; linarith
              have hS2m : MeasurableSet S2 :=
                (hL'.isClosed.measurableSet.preimage (measurable_add_const _)).preimage
                  (measurable_const_mul _)
              have hu := measure_union_add_inter S1 hS2m (μ := volume)
              have hi : volume (S1 ∩ S2) = 0 := measure_mono_null s12 (measure_singleton _)
              rw [hi, add_zero] at hu
              have hle : volume (S1 ∪ S2) ≤ volume C := measure_mono (Set.union_subset s1C s2C)
              have hKK : volume K ≤ volume K' := measure_mono (Set.subset_insert _ _)
              have hLL : volume L ≤ volume L' := measure_mono (Set.subset_insert _ _)
              have e2 : ENNReal.ofReal (|(2:ℝ)⁻¹|) = 2⁻¹ := by
                rw [abs_of_pos (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
              calc volume K + volume L ≤ volume K' + volume L' := add_le_add hKK hLL
                _ = 2 * (volume S1 + volume S2) := by
                  rw [v1, v2, e2, ← mul_add, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
                _ ≤ 2 * volume C := by rw [← hu]; gcongr
            rw [hA.measure_eq_iSup_isCompact, hB.measure_eq_iSup_isCompact]
            simp_rw [iSup_and']
            exact ENNReal.biSup_add_biSup_le' ⟨∅, Set.empty_subset _, isCompact_empty⟩
              ⟨∅, Set.empty_subset _, isCompact_empty⟩
              (fun K hK L hL => key K L hK.1 hK.2 hL.1 hL.2)
          have core : ∀ F G Hf : ℝ → ℝ, Measurable F → Measurable G → Measurable Hf →
              (∀ x, 0 ≤ F x) → (∀ x, 0 ≤ G x) → (∀ x, 0 ≤ Hf x) → (∀ x, F x ≤ 1) → (∀ x, G x ≤ 1) →
              (∀ t < 1, ∃ x, t < F x) → (∀ t < 1, ∃ x, t < G x) →
              (∀ t, 0 < t → ∀ a b, t < F a → t < G b → t < Hf ((a + b) / 2)) →
              (∫⁻ x, ENNReal.ofReal (F x)) + (∫⁻ x, ENNReal.ofReal (G x)) ≤ 2 * ∫⁻ x, ENNReal.ofReal (Hf x) := by
            intro F G Hf hFm hGm hHm hF0 hG0 hH0 hF1 hG1 hFs hGs hmid
            have e1 : ∫⁻ x, ENNReal.ofReal (F x) = ∫⁻ t in Set.Ioi 0, volume {a | t < F a} :=
              lintegral_eq_lintegral_meas_lt (f := F) volume (Filter.Eventually.of_forall hF0) hFm.aemeasurable
            have e2 : ∫⁻ x, ENNReal.ofReal (G x) = ∫⁻ t in Set.Ioi 0, volume {a | t < G a} :=
              lintegral_eq_lintegral_meas_lt (f := G) volume (Filter.Eventually.of_forall hG0) hGm.aemeasurable
            have e3 : ∫⁻ x, ENNReal.ofReal (Hf x) = ∫⁻ t in Set.Ioi 0, volume {a | t < Hf a} :=
              lintegral_eq_lintegral_meas_lt (f := Hf) volume (Filter.Eventually.of_forall hH0) hHm.aemeasurable
            rw [e1, e2, e3]
            calc _ ≤ ∫⁻ t in Set.Ioi 0, (volume {a | t < F a} + volume {a | t < G a}) :=
                  le_lintegral_add _ _
              _ ≤ ∫⁻ t in Set.Ioi 0, 2 * volume {a | t < Hf a} := by
                  refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
                  have ht0 : 0 < t := ht
                  by_cases ht1 : t < 1
                  · obtain ⟨x0, hx0⟩ := hFs t ht1
                    obtain ⟨y0, hy0⟩ := hGs t ht1
                    exact BM _ _ _ (measurableSet_lt measurable_const hFm)
                      (measurableSet_lt measurable_const hGm) ⟨x0, hx0⟩ ⟨y0, hy0⟩
                      (fun a ha b hb => hmid t ht0 a b ha hb)
                  · have eF : {a | t < F a} = ∅ := by
                      ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                      linarith [hF1 a]
                    have eG : {a | t < G a} = ∅ := by
                      ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                      linarith [hG1 a]
                    rw [eF, eG]; simp
              _ = 2 * ∫⁻ t in Set.Ioi 0, volume {a | t < Hf a} := lintegral_const_mul' _ _ (by norm_num)
          -- normalization
          have hbf : BddAbove (Set.range f) := ⟨1, by rintro _ ⟨x, rfl⟩; exact hf1 x⟩
          have hbg : BddAbove (Set.range g) := ⟨1, by rintro _ ⟨x, rfl⟩; exact hg1 x⟩
          set Mf := ⨆ x, f x with hMf
          set Mg := ⨆ x, g x with hMg
          have hfle : ∀ x, f x ≤ Mf := fun x => le_ciSup hbf x
          have hgle : ∀ x, g x ≤ Mg := fun x => le_ciSup hbg x
          have hMf0 : 0 ≤ Mf := le_trans (hf0 0) (hfle 0)
          have hMg0 : 0 ≤ Mg := le_trans (hg0 0) (hgle 0)
          rcases hMf0.eq_or_lt with h0 | hMfpos
          · have : ∫⁻ x, ENNReal.ofReal (f x) = 0 := by
              have : ∀ x, ENNReal.ofReal (f x) = 0 := fun x =>
                ENNReal.ofReal_eq_zero.mpr (by linarith [hfle x])
              simp [this]
            rw [this, zero_mul]; exact bot_le
          rcases hMg0.eq_or_lt with h0 | hMgpos
          · have : ∫⁻ x, ENNReal.ofReal (g x) = 0 := by
              have : ∀ x, ENNReal.ofReal (g x) = 0 := fun x =>
                ENNReal.ofReal_eq_zero.mpr (by linarith [hgle x])
              simp [this]
            rw [this, mul_zero]; exact bot_le
          set s := Real.sqrt (Mf * Mg) with hs
          have hspos : 0 < s := Real.sqrt_pos.mpr (mul_pos hMfpos hMgpos)
          have hs2 : s ^ 2 = Mf * Mg := Real.sq_sqrt (mul_pos hMfpos hMgpos).le
          have hc := core (fun x => f x / Mf) (fun x => g x / Mg) (fun x => h x / s)
            (hf.div_const _) (hg.div_const _) (hh.div_const _)
            (fun x => div_nonneg (hf0 x) hMfpos.le) (fun x => div_nonneg (hg0 x) hMgpos.le)
            (fun x => div_nonneg (hh0 x) hspos.le)
            (fun x => (div_le_one hMfpos).mpr (hfle x)) (fun x => (div_le_one hMgpos).mpr (hgle x))
            (by
              intro t ht
              have : t * Mf < Mf := by nlinarith
              obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup this
              exact ⟨x, (lt_div_iff₀ hMfpos).mpr hx⟩)
            (by
              intro t ht
              have : t * Mg < Mg := by nlinarith
              obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup this
              exact ⟨x, (lt_div_iff₀ hMgpos).mpr hx⟩)
            (by
              intro t ht a b ha hb
              have ha' : t * Mf < f a := (lt_div_iff₀ hMfpos).mp ha
              have hb' : t * Mg < g b := (lt_div_iff₀ hMgpos).mp hb
              have hprod : (t * Mf) * (t * Mg) < f a * g b :=
                mul_lt_mul'' ha' hb' (by positivity) (by positivity)
              have hP := hPL a b
              rw [lt_div_iff₀ hspos]
              by_contra hcon
              push Not at hcon
              have hm0 := hh0 ((a + b) / 2)
              have : h ((a + b) / 2) ^ 2 ≤ (t * s) ^ 2 := pow_le_pow_left₀ hm0 hcon 2
              have e : (t * s) ^ 2 = t * Mf * (t * Mg) := by rw [mul_pow, hs2]; ring
              linarith)
          have eq1 : ∀ (u : ℝ → ℝ) (c : ℝ), 0 < c →
              ∫⁻ x, ENNReal.ofReal (u x / c) = ENNReal.ofReal c⁻¹ * ∫⁻ x, ENNReal.ofReal (u x) := by
            intro u c hc
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1; funext x
            rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
          rw [eq1 f Mf hMfpos, eq1 g Mg hMgpos, eq1 h s hspos] at hc
          set F := (∫⁻ x, ENNReal.ofReal (f x)).toReal with hFdef
          set G := (∫⁻ x, ENNReal.ofReal (g x)).toReal with hGdef
          set H := (∫⁻ x, ENNReal.ofReal (h x)).toReal with hHdef
          have eF : ∫⁻ x, ENNReal.ofReal (f x) = ENNReal.ofReal F := (ENNReal.ofReal_toReal hfi).symm
          have eG : ∫⁻ x, ENNReal.ofReal (g x) = ENNReal.ofReal G := (ENNReal.ofReal_toReal hgi).symm
          have eH : ∫⁻ x, ENNReal.ofReal (h x) = ENNReal.ofReal H := (ENNReal.ofReal_toReal hhi).symm
          have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
          have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
          have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
          rw [eF, eG, eH] at hc ⊢
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hMfpos.le), ← ENNReal.ofReal_mul (inv_nonneg.mpr hMgpos.le),
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hspos.le),
            ← ENNReal.ofReal_add (by positivity) (by positivity)] at hc
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          rw [h2, ← ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_le_ofReal_iff (by positivity)] at hc
          rw [← ENNReal.ofReal_mul hF0, ← ENNReal.ofReal_pow hH0]
          apply ENNReal.ofReal_le_ofReal
          -- real arithmetic
          set a := Mf⁻¹ * F with ha
          set b := Mg⁻¹ * G with hb
          have ha0 : 0 ≤ a := by positivity
          have hb0 : 0 ≤ b := by positivity
          have hFa : F = a * Mf := by rw [ha]; field_simp
          have hGb : G = b * Mg := by rw [hb]; field_simp
          have hab : (a + b) * s ≤ 2 * H := by
            have := mul_le_mul_of_nonneg_right hc hspos.le
            calc (a + b) * s ≤ 2 * (s⁻¹ * H) * s := this
              _ = 2 * H := by field_simp
          have h4 : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith only [sq_nonneg (a - b)]
          have hsq : ((a + b) * s) ^ 2 ≤ (2 * H) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (add_nonneg ha0 hb0) hspos.le) hab 2
          rw [hFa, hGb]
          have : a * Mf * (b * Mg) = a * b * s ^ 2 := by rw [hs2]; ring
          rw [this]
          have e1 := mul_le_mul_of_nonneg_right h4 (sq_nonneg s)
          nlinarith only [e1, hsq]
        have P3 : (∀ u w, (μ (Set.Iic u)).toReal * (μ (Set.Iic w)).toReal
              ≤ (μ (Set.Iic ((u + w) / 2))).toReal ^ 2) →
            ∃ ψ : ℝ → ℝ, Measurable ψ ∧
            (∀ r s, 0 < r → 0 < s → ψ ((r + s) / 2) ≤ (ψ r + ψ s) / 2) ∧
            ∀ f : ℝ → ℝ≥0∞, Measurable f →
              ∫⁻ y, f y ∂μ = ∫⁻ r in Set.Ioi 0, f (ψ r) * ENNReal.ofReal (Real.exp (-r)) := by
          intro hmid
          set G : ℝ → ℝ := fun x => ProbabilityTheory.cdf μ x with hGdef
          have hGμ : ∀ x, ENNReal.ofReal (G x) = μ (Set.Iic x) := fun x => ProbabilityTheory.ofReal_cdf μ x
          have hGr : ∀ x, G x = (μ (Set.Iic x)).toReal := by
            intro x; rw [← hGμ x, ENNReal.toReal_ofReal (ProbabilityTheory.cdf_nonneg μ x)]
          have hGmono : Monotone G := ProbabilityTheory.monotone_cdf μ
          have hGnn : ∀ x, 0 ≤ G x := fun x => ProbabilityTheory.cdf_nonneg μ x
          have hG1 : ∀ x, G x ≤ 1 := fun x => ProbabilityTheory.cdf_le_one μ x
          have hGneg : ∀ x, x < 0 → G x = 0 := by
            intro x hx
            have h1 : μ (Set.Iic x) = 0 :=
              le_antisymm (hμ ▸ measure_mono (Set.Iic_subset_Iio.mpr hx)) bot_le
            rw [hGr, h1]; rfl
          have hGmid : ∀ u w, G u * G w ≤ G ((u + w) / 2) ^ 2 := by
            intro u w; rw [hGr, hGr, hGr]; exact hmid u w
          set S : ℝ → Set ℝ := fun r => {v | Real.exp (-r) ≤ G v} with hS
          have hSne : ∀ r, 0 < r → (S r).Nonempty := by
            intro r hr
            have hlt : Real.exp (-r) < 1 := (Real.exp_lt_exp.mpr (by linarith : -r < 0)).trans_eq Real.exp_zero
            have := (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hlt)
            obtain ⟨v, hv⟩ := this.exists
            exact ⟨v, le_of_lt hv⟩
          have hSbdd : ∀ r, BddBelow (S r) := by
            intro r
            refine ⟨0, fun v hv => ?_⟩
            by_contra h
            push_neg at h
            have := hGneg v h
            simp only [hS, Set.mem_setOf_eq, this] at hv
            linarith [Real.exp_pos (-r)]
          have hSmem : ∀ r, 0 < r → sInf (S r) ∈ S r := by
            intro r hr
            set x := sInf (S r)
            show Real.exp (-r) ≤ G x
            have hc : ContinuousWithinAt G (Set.Ioi x) x :=
              ((ProbabilityTheory.cdf μ).right_continuous x).mono Set.Ioi_subset_Ici_self
            apply ge_of_tendsto hc
            filter_upwards [self_mem_nhdsWithin] with y hy
            obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt (hSne r hr) (show sInf (S r) < y from hy)
            exact le_trans hs (hGmono hsy.le)
          set ψ : ℝ → ℝ := fun r => if 0 < r then sInf (S r) else 0 with hψ
          have gal : ∀ r v, 0 < r → (ψ r ≤ v ↔ Real.exp (-r) ≤ G v) := by
            intro r v hr
            simp only [hψ, if_pos hr]
            constructor
            · intro h; exact le_trans (hSmem r hr) (hGmono h)
            · intro h; exact csInf_le (hSbdd r) h
          have hpre : ∀ a, ψ ⁻¹' Set.Iic a = {r | 0 < r ∧ Real.exp (-r) ≤ G a} ∪ {r | r ≤ 0 ∧ 0 ≤ a} := by
            intro a; ext r
            simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_setOf_eq]
            by_cases hr : 0 < r
            · rw [gal r a hr]; constructor
              · intro h; exact Or.inl ⟨hr, h⟩
              · rintro (h | h); exact h.2; exact absurd h.1 (not_le.mpr hr)
            · simp only [hψ, if_neg hr]; constructor
              · intro h; exact Or.inr ⟨not_lt.mp hr, h⟩
              · rintro (h | h); exact absurd h.1 hr; exact h.2
          have hψm : Measurable ψ := by
            apply measurable_of_Iic
            intro a
            rw [hpre]
            apply MeasurableSet.union
            · exact (measurableSet_lt measurable_const measurable_id).inter
                (measurableSet_le (Real.continuous_exp.comp continuous_neg).measurable measurable_const)
            · exact (measurableSet_le measurable_id measurable_const).inter (MeasurableSet.const _)
          refine ⟨ψ, hψm, ?_, ?_⟩
          · intro r s hr hs
            rw [gal _ _ (by linarith)]
            have h1 : Real.exp (-r) ≤ G (ψ r) := (gal r _ hr).mp le_rfl
            have h2 : Real.exp (-s) ≤ G (ψ s) := (gal s _ hs).mp le_rfl
            have h3 := hGmid (ψ r) (ψ s)
            have h4 : Real.exp (-r) * Real.exp (-s) = Real.exp (-((r+s)/2)) ^ 2 := by
              rw [← Real.exp_add, sq, ← Real.exp_add]; congr 1; ring
            have h5 : Real.exp (-r) * Real.exp (-s) ≤ G (ψ r) * G (ψ s) :=
              mul_le_mul h1 h2 (Real.exp_pos _).le (hGnn _)
            have h6 : Real.exp (-((r+s)/2)) ^ 2 ≤ G ((ψ r + ψ s) / 2) ^ 2 := by linarith
            exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (hGnn _) (by norm_num)).mp h6
          · set ν : Measure ℝ := (volume.restrict (Set.Ioi 0)).withDensity (fun r => ENNReal.ofReal (Real.exp (-r))) with hν
            have hdm : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r))) :=
              ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp continuous_neg).measurable
            have hmap : μ = ν.map ψ := by
              apply Measure.ext_of_Iic
              intro a
              rw [Measure.map_apply hψm measurableSet_Iic, hν, withDensity_apply _ (hψm measurableSet_Iic),
                Measure.restrict_restrict (hψm measurableSet_Iic)]
              have hset : ψ ⁻¹' Set.Iic a ∩ Set.Ioi 0 = {r | 0 < r ∧ Real.exp (-r) ≤ G a} := by
                rw [hpre]; ext r
                simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_Ioi]
                constructor
                · rintro ⟨h | h, h'⟩; exact h; exact absurd h.1 (not_le.mpr h')
                · intro h; exact ⟨Or.inl h, h.1⟩
              rw [hset, ← hGμ a]
              rcases (hGnn a).eq_or_lt with h0 | hpos
              · have : {r : ℝ | 0 < r ∧ Real.exp (-r) ≤ G a} = ∅ := by
                  ext r; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
                  intro _; rw [← h0]; exact Real.exp_pos _
                rw [this, ← h0]; simp
              · set L := -Real.log (G a) with hL
                have hL0 : 0 ≤ L := by
                  rw [hL, neg_nonneg]; exact Real.log_nonpos (le_of_lt hpos) (hG1 a)
                have hiff : ∀ r, Real.exp (-r) ≤ G a ↔ L ≤ r := by
                  intro r
                  rw [← Real.exp_log hpos, Real.exp_le_exp, hL]; constructor <;> intro h <;> linarith
                have hGa : G a = Real.exp (-L) := by rw [hL, neg_neg, Real.exp_log hpos]
                have key : ∫⁻ r in Set.Ioi L, ENNReal.ofReal (Real.exp (-r)) = ENNReal.ofReal (G a) := by
                  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi L)
                    (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le), integral_exp_neg_Ioi, hGa]
                rcases hL0.eq_or_lt with hLe | hLp
                · have : {r : ℝ | 0 < r ∧ Real.exp (-r) ≤ G a} = Set.Ioi L := by
                    ext r; simp only [Set.mem_setOf_eq, Set.mem_Ioi, hiff, ← hLe]
                    constructor
                    · intro h; exact h.1
                    · intro h; exact ⟨h, h.le⟩
                  rw [this, key]
                · have : {r : ℝ | 0 < r ∧ Real.exp (-r) ≤ G a} = Set.Ici L := by
                    ext r; simp only [Set.mem_setOf_eq, Set.mem_Ici, hiff]
                    constructor
                    · intro h; exact h.2
                    · intro h; exact ⟨by linarith, h⟩
                  rw [this, setLIntegral_congr Ioi_ae_eq_Ici.symm, key]
            intro f hf
            rw [hmap, lintegral_map hf hψm, hν, lintegral_withDensity_eq_lintegral_mul _ hdm (show Measurable (fun a => f (ψ a)) from hf.comp hψm)]
            refine lintegral_congr fun r => ?_
            simp only [Pi.mul_apply, Function.comp_apply]; ring
        have hprob : ∀ k, IsProbabilityMeasure (ShockWear.CumDamage.convPow μ k) := by
          intro k
          induction k with
          | zero => simp only [ShockWear.CumDamage.convPow]; infer_instance
          | succ k ih => simp only [ShockWear.CumDamage.convPow]; infer_instance
        have hconv : ∀ k x, ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x)
            = ∫⁻ y, ShockWear.CumDamage.convPow μ k (Set.Iic (x - y)) ∂μ := by
          intro k x
          have := hprob k
          simp only [ShockWear.CumDamage.convPow]
          rw [← lintegral_indicator_one measurableSet_Iic, Measure.lintegral_conv]
          · rw [lintegral_lintegral_swap]
            · congr 1; funext y
              rw [← lintegral_indicator_one measurableSet_Iic]
              congr 1; funext a
              simp only [Set.indicator, Set.mem_Iic, Pi.one_apply]
              congr 1; apply propext; constructor <;> intro h <;> linarith
            · exact ((measurable_one.indicator measurableSet_Iic).comp measurable_add).aemeasurable
          · exact measurable_one.indicator measurableSet_Iic
        have hae : ∀ᵐ y ∂μ, 0 ≤ y := by
          rw [ae_iff]
          have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
          rw [this, hμ]
        have hfin : ∀ k x, ShockWear.CumDamage.convPow μ k (Set.Iic x) ≠ ⊤ := by
          intro k x; have := hprob k; exact measure_ne_top _ _
        -- antitone in k
        have hanti : ∀ k x, ShockWear.CumDamage.cdfPow μ (k+1) x ≤ ShockWear.CumDamage.cdfPow μ k x := by
          intro k x
          have hle : ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x)
              ≤ ShockWear.CumDamage.convPow μ k (Set.Iic x) := by
            rw [hconv]
            calc ∫⁻ y, ShockWear.CumDamage.convPow μ k (Set.Iic (x - y)) ∂μ
                ≤ ∫⁻ _y, ShockWear.CumDamage.convPow μ k (Set.Iic x) ∂μ := by
                  apply lintegral_mono_ae
                  filter_upwards [hae] with y hy
                  exact measure_mono (Set.Iic_subset_Iic.mpr (by linarith))
              _ = _ := by simp
          exact ENNReal.toReal_mono (hfin _ _) hle
        have hnn : ∀ k x, 0 ≤ ShockWear.CumDamage.cdfPow μ k x := fun k x => ENNReal.toReal_nonneg
        -- sequence lemma
        have seqlem : ∀ a : ℕ → ℝ, (∀ k, 0 ≤ a k) → (∀ k, a (k+1) ≤ a k) →
            (∀ k, a (k+2) * a k ≤ a (k+1) ^ 2) →
            ∀ p m n q : ℕ, p ≤ m → m ≤ n → p + q = m + n → a p * a q ≤ a m * a n := by
          intro a ha0 ha1 ha2
          have hanti' : Antitone a := antitone_nat_of_succ_le ha1
          have L1 : ∀ j k, j ≤ k → a (k+1) * a j ≤ a (j+1) * a k := by
            intro j k hjk
            induction k, hjk using Nat.le_induction with
            | base => exact le_rfl
            | succ k hk ih =>
              rcases (ha0 (k+1)).eq_or_lt with h0 | hpos
              · have : a (k+2) = 0 := le_antisymm (h0 ▸ ha1 (k+1)) (ha0 _)
                rw [this, zero_mul]; exact mul_nonneg (ha0 _) (ha0 _)
              · have hk0 : 0 < a k := lt_of_lt_of_le hpos (ha1 k)
                have e1 := mul_le_mul_of_nonneg_right (ha2 k) (ha0 j)
                have e2 := mul_le_mul_of_nonneg_left ih (ha0 (k+1))
                apply le_of_mul_le_mul_right _ hk0
                nlinarith
          have L : ∀ d j k, j ≤ k → a (k+d) * a j ≤ a (j+d) * a k := by
            intro d
            induction d with
            | zero => intro j k _; exact le_of_eq (mul_comm _ _)
            | succ d ih =>
              intro j k hjk
              rcases (ha0 (k+d)).eq_or_lt with h0 | hpos
              · have : a (k+(d+1)) = 0 := le_antisymm (h0 ▸ ha1 (k+d)) (ha0 _)
                rw [this, zero_mul]; exact mul_nonneg (ha0 _) (ha0 _)
              · have hjd : 0 < a (j+d) := lt_of_lt_of_le hpos (hanti' (by omega))
                have e1 := L1 (j+d) (k+d) (by omega)
                have e2 := ih j k hjk
                have e3 := mul_le_mul e1 e2 (mul_nonneg (ha0 _) (ha0 _)) (mul_nonneg (ha0 _) (ha0 _))
                have e4 : a (k + (d+1)) * a j * (a (j+d) * a (k+d))
                    ≤ a (j+(d+1)) * a k * (a (j+d) * a (k+d)) := by
                  have r1 : k + (d+1) = k + d + 1 := by omega
                  have r2 : j + (d+1) = j + d + 1 := by omega
                  rw [r1, r2]; nlinarith
                exact le_of_mul_le_mul_right e4 (mul_pos hjd hpos)
          intro p m n q hpm hmn hsum
          have := L (m - p) p n (by omega)
          have r1 : n + (m - p) = q := by omega
          have r2 : p + (m - p) = m := by omega
          rw [r1, r2] at this
          linarith [mul_comm (a q) (a p)]
        refine ⟨?_, ?_, ?_⟩
        · intro hF
          have hmono : ∀ k x1 x2, x1 ≤ x2 → ShockWear.CumDamage.cdfPow μ k x1 ≤ ShockWear.CumDamage.cdfPow μ k x2 := by
            intro k x1 x2 h
            exact ENNReal.toReal_mono (hfin _ _) (measure_mono (Set.Iic_subset_Iic.mpr h))
          have hLC : ∀ k x1 x2 y, x1 ≤ x2 → 0 ≤ y →
              ShockWear.CumDamage.cdfPow μ k (x1 - y) * ShockWear.CumDamage.cdfPow μ k x2
                ≤ ShockWear.CumDamage.cdfPow μ k (x2 - y) * ShockWear.CumDamage.cdfPow μ k x1 := by
            have hGmid : ∀ u w, (μ (Set.Iic u)).toReal * (μ (Set.Iic w)).toReal
                ≤ (μ (Set.Iic ((u + w) / 2))).toReal ^ 2 := by
              have key : ∀ u w, u ≤ w → (μ (Set.Iic u)).toReal * (μ (Set.Iic w)).toReal
                  ≤ (μ (Set.Iic ((u + w) / 2))).toReal ^ 2 := by
                intro u w huw
                rcases huw.eq_or_lt with h | h
                · subst h
                  have : (u + u) / 2 = u := by ring
                  rw [this, sq]
                · have := hF 2 (by norm_num) le_rfl ![(u+w)/2, w] ![0, (w-u)/2] (by simp) (by simp)
                    (by
                      intro i j hij; fin_cases i <;> fin_cases j
                      · exact absurd hij (by decide)
                      · simp; linarith
                      · exact absurd hij (by decide)
                      · exact absurd hij (by decide))
                    (by
                      intro i j hij; fin_cases i <;> fin_cases j
                      · exact absurd hij (by decide)
                      · simp; linarith
                      · exact absurd hij (by decide)
                      · exact absurd hij (by decide))
                  rw [Matrix.det_fin_two] at this
                  have e1 : (u + w) / 2 - (w - u) / 2 = u := by ring
                  have e2 : w - (w - u) / 2 = (u + w) / 2 := by ring
                  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                    sub_zero, e1, e2, one_mul] at this
                  nlinarith
              intro u w
              rcases le_total u w with h | h
              · exact key u w h
              · rw [mul_comm, add_comm]; exact key w u h
            obtain ⟨ψ, hψm, hψc, hpush⟩ := P3 hGmid
            have hmonok : ∀ k, Monotone (ShockWear.CumDamage.cdfPow μ k) :=
              fun k x1 x2 h => hmono k x1 x2 h
            have hle1 : ∀ k x, ShockWear.CumDamage.cdfPow μ k x ≤ 1 := by
              intro k x; have := hprob k
              exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
            have hmidk : ∀ k u w, ShockWear.CumDamage.cdfPow μ k u * ShockWear.CumDamage.cdfPow μ k w
                ≤ ShockWear.CumDamage.cdfPow μ k ((u + w) / 2) ^ 2 := by
              intro k
              induction k with
              | zero =>
                intro u w
                have h0 : ∀ x, ShockWear.CumDamage.cdfPow μ 0 x = if 0 ≤ x then 1 else 0 := by
                  intro x
                  unfold ShockWear.CumDamage.cdfPow
                  simp only [ShockWear.CumDamage.convPow]
                  rw [Measure.dirac_apply' _ measurableSet_Iic]
                  by_cases h : 0 ≤ x
                  · simp [Set.indicator, h]
                  · simp [Set.indicator, h]
                rw [h0, h0, h0]
                by_cases hu : 0 ≤ u
                · by_cases hw : 0 ≤ w
                  · rw [if_pos hu, if_pos hw, if_pos (by linarith)]; norm_num
                  · rw [if_neg hw, mul_zero]; positivity
                · rw [if_neg hu, zero_mul]; positivity
              | succ k ih =>
                intro a b
                set φ : ℝ → ℝ → ℝ := fun s => Set.indicator (Set.Ioi 0)
                  (fun r => ShockWear.CumDamage.cdfPow μ k (s - ψ r) * Real.exp (-r)) with hφ
                have hφint : ∀ s, ∫⁻ r, ENNReal.ofReal (φ s r)
                    = ShockWear.CumDamage.convPow μ (k+1) (Set.Iic s) := by
                  intro s
                  have hmeas : Measurable fun y => ShockWear.CumDamage.convPow μ k (Set.Iic (s - y)) := by
                    apply Antitone.measurable
                    intro y1 y2 hy
                    exact measure_mono (Set.Iic_subset_Iic.mpr (by linarith))
                  rw [hconv k s, hpush _ hmeas]
                  have : ∀ r, ENNReal.ofReal (φ s r) = Set.indicator (Set.Ioi 0)
                      (fun r => ShockWear.CumDamage.convPow μ k (Set.Iic (s - ψ r))
                        * ENNReal.ofReal (Real.exp (-r))) r := by
                    intro r
                    simp only [hφ, Set.indicator]
                    split_ifs
                    · rw [ENNReal.ofReal_mul (hnn _ _)]
                      unfold ShockWear.CumDamage.cdfPow
                      rw [ENNReal.ofReal_toReal (hfin _ _)]
                    · simp
                  simp_rw [this]
                  rw [lintegral_indicator measurableSet_Ioi]
                have hφm : ∀ s, Measurable (φ s) := by
                  intro s
                  apply Measurable.indicator _ measurableSet_Ioi
                  exact ((hmonok k).measurable.comp (measurable_const.sub hψm)).mul
                    (Real.measurable_exp.comp measurable_neg)
                have hφ0 : ∀ s r, 0 ≤ φ s r := by
                  intro s r
                  exact Set.indicator_nonneg (fun r _ => mul_nonneg (hnn _ _) (Real.exp_pos _).le) r
                have hφ1 : ∀ s r, φ s r ≤ 1 := by
                  intro s r
                  simp only [hφ, Set.indicator]
                  split_ifs with hr
                  · have : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by simp at hr; linarith)
                    calc ShockWear.CumDamage.cdfPow μ k (s - ψ r) * Real.exp (-r) ≤ 1 * 1 :=
                          mul_le_mul (hle1 _ _) this (Real.exp_pos _).le zero_le_one
                      _ = 1 := by norm_num
                  · norm_num
                have hφfin : ∀ s, ∫⁻ r, ENNReal.ofReal (φ s r) ≠ ∞ := by
                  intro s; rw [hφint]; exact hfin _ _
                have hPL : ∀ x y, φ a x * φ b y ≤ φ ((a + b) / 2) ((x + y) / 2) ^ 2 := by
                  intro x y
                  by_cases hx : 0 < x
                  · by_cases hy : 0 < y
                    · have hxy : (0:ℝ) < (x + y) / 2 := by linarith
                      simp only [hφ, Set.indicator, Set.mem_Ioi, if_pos hx, if_pos hy, if_pos hxy]
                      have e : Real.exp (-x) * Real.exp (-y) = Real.exp (-((x + y) / 2)) ^ 2 := by
                        rw [← Real.exp_add, sq, ← Real.exp_add]; congr 1; ring
                      have i1 := ih (a - ψ x) (b - ψ y)
                      have i2 : ShockWear.CumDamage.cdfPow μ k ((a - ψ x + (b - ψ y)) / 2)
                          ≤ ShockWear.CumDamage.cdfPow μ k ((a + b) / 2 - ψ ((x + y) / 2)) := by
                        apply hmonok k
                        have := hψc x y hx hy
                        linarith
                      have i3 : ShockWear.CumDamage.cdfPow μ k ((a - ψ x + (b - ψ y)) / 2) ^ 2
                          ≤ ShockWear.CumDamage.cdfPow μ k ((a + b) / 2 - ψ ((x + y) / 2)) ^ 2 :=
                        pow_le_pow_left₀ (hnn _ _) i2 2
                      calc ShockWear.CumDamage.cdfPow μ k (a - ψ x) * Real.exp (-x)
                            * (ShockWear.CumDamage.cdfPow μ k (b - ψ y) * Real.exp (-y))
                          = (ShockWear.CumDamage.cdfPow μ k (a - ψ x)
                            * ShockWear.CumDamage.cdfPow μ k (b - ψ y))
                            * (Real.exp (-x) * Real.exp (-y)) := by ring
                        _ ≤ ShockWear.CumDamage.cdfPow μ k ((a + b) / 2 - ψ ((x + y) / 2)) ^ 2
                            * (Real.exp (-x) * Real.exp (-y)) :=
                          mul_le_mul_of_nonneg_right (i1.trans i3)
                            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
                        _ = _ := by rw [e]; ring
                    · have : φ b y = 0 := by
                        simp only [hφ, Set.indicator, Set.mem_Ioi, if_neg hy]
                      rw [this, mul_zero]; positivity
                  · have : φ a x = 0 := by
                      simp only [hφ, Set.indicator, Set.mem_Ioi, if_neg hx]
                    rw [this, zero_mul]; positivity
                have hE := P2 (φ a) (φ b) (φ ((a + b) / 2)) (hφm _) (hφm _) (hφm _) (hφ0 _) (hφ0 _)
                  (hφ0 _) (hφ1 _) (hφ1 _) (hφ1 _) (hφfin _) (hφfin _) (hφfin _) hPL
                rw [hφint, hφint, hφint] at hE
                have := ENNReal.toReal_mono (ENNReal.pow_ne_top (hfin _ _)) hE
                rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at this
                exact this
            intro k
            apply P1 (ShockWear.CumDamage.cdfPow μ k) (hnn k) (hmonok k) _ (hmidk k)
            intro x
            have := hprob k
            have hc := (ProbabilityTheory.cdf (ShockWear.CumDamage.convPow μ k)).right_continuous x
            have heq : (fun x => ProbabilityTheory.cdf (ShockWear.CumDamage.convPow μ k) x)
                = ShockWear.CumDamage.cdfPow μ k := by
              funext x
              rw [ProbabilityTheory.cdf_eq_real]; rfl
            rw [← heq]; exact hc
          have hcons : ∀ k x1 x2, x1 ≤ x2 →
              ShockWear.CumDamage.cdfPow μ (k+1) x1 * ShockWear.CumDamage.cdfPow μ k x2
                ≤ ShockWear.CumDamage.cdfPow μ (k+1) x2 * ShockWear.CumDamage.cdfPow μ k x1 := by
            intro k x1 x2 hx
            have hE : ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x1)
                  * ShockWear.CumDamage.convPow μ k (Set.Iic x2)
                ≤ ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x2)
                  * ShockWear.CumDamage.convPow μ k (Set.Iic x1) := by
              calc ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x1)
                    * ShockWear.CumDamage.convPow μ k (Set.Iic x2)
                  = ∫⁻ y, ShockWear.CumDamage.convPow μ k (Set.Iic (x1 - y))
                      * ShockWear.CumDamage.convPow μ k (Set.Iic x2) ∂μ := by
                    rw [hconv k x1, lintegral_mul_const' _ _ (hfin _ _)]
                _ ≤ ∫⁻ y, ShockWear.CumDamage.convPow μ k (Set.Iic (x2 - y))
                      * ShockWear.CumDamage.convPow μ k (Set.Iic x1) ∂μ := by
                    apply lintegral_mono_ae
                    filter_upwards [hae] with y hy
                    have h := hLC k x1 x2 y hx hy
                    unfold ShockWear.CumDamage.cdfPow at h
                    rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (hfin _ _) (hfin _ _))
                      (ENNReal.mul_ne_top (hfin _ _) (hfin _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul]
                    exact h
                _ = _ := by rw [hconv k x2, lintegral_mul_const' _ _ (hfin _ _)]
            have := ENNReal.toReal_mono (ENNReal.mul_ne_top (hfin _ _) (hfin _ _)) hE
            rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
            exact this
          have hgen : ∀ d j x1 x2, x1 ≤ x2 →
              ShockWear.CumDamage.cdfPow μ (j+d) x1 * ShockWear.CumDamage.cdfPow μ j x2
                ≤ ShockWear.CumDamage.cdfPow μ (j+d) x2 * ShockWear.CumDamage.cdfPow μ j x1 := by
            intro d
            induction d with
            | zero => intro j x1 x2 _; simp only [Nat.add_zero]; exact le_of_eq (mul_comm _ _)
            | succ d ih =>
              intro j x1 x2 hx
              rcases (hnn (j+(d+1)) x1).eq_or_lt with h0 | hpos
              · rw [← h0, zero_mul]; exact mul_nonneg (hnn _ _) (hnn _ _)
              · have hd1 : 0 < ShockWear.CumDamage.cdfPow μ (j+d) x1 :=
                  lt_of_lt_of_le hpos (by rw [show j + (d+1) = j + d + 1 by omega]; exact hanti _ _)
                have hd2 : 0 < ShockWear.CumDamage.cdfPow μ (j+d) x2 := lt_of_lt_of_le hd1 (hmono _ _ _ hx)
                have e1 := hcons (j+d) x1 x2 hx
                have e2 := ih j x1 x2 hx
                rw [show j + (d+1) = j + d + 1 by omega]
                have e3 := mul_le_mul e1 e2 (mul_nonneg (hnn _ _) (hnn _ _)) (mul_nonneg (hnn _ _) (hnn _ _))
                have e4 : ShockWear.CumDamage.cdfPow μ (j+d+1) x1 * ShockWear.CumDamage.cdfPow μ j x2
                      * (ShockWear.CumDamage.cdfPow μ (j+d) x1 * ShockWear.CumDamage.cdfPow μ (j+d) x2)
                    ≤ ShockWear.CumDamage.cdfPow μ (j+d+1) x2 * ShockWear.CumDamage.cdfPow μ j x1
                      * (ShockWear.CumDamage.cdfPow μ (j+d) x1 * ShockWear.CumDamage.cdfPow μ (j+d) x2) := by
                  nlinarith
                exact le_of_mul_le_mul_right e4 (mul_pos hd1 hd2)
          intro r hr1 hr2
          interval_cases r
          · intro u v _ _ _ _
            rw [Matrix.det_fin_one]
            simp only [Matrix.of_apply, one_mul]
            exact hnn _ _
          · intro u v _ _ hu hv
            rw [Matrix.det_fin_two]
            simp only [Matrix.of_apply, one_mul, sub_nonneg]
            have hu' : u 0 < u 1 := hu (by decide)
            have hv' : v 0 < v 1 := hv (by decide)
            have := hgen (u 1 - u 0) (u 0) (v 0) (v 1) hv'.le
            rw [show u 0 + (u 1 - u 0) = u 1 by omega] at this
            linarith [mul_comm (ShockWear.CumDamage.cdfPow μ (u 0) (v 1)) (ShockWear.CumDamage.cdfPow μ (u 1) (v 0)),
              mul_comm (ShockWear.CumDamage.cdfPow μ (u 0) (v 0)) (ShockWear.CumDamage.cdfPow μ (u 1) (v 1))]
        · 
            clear P1 P2 P3
            intro hTP x
            -- log-concavity in k
            have hTP2 : ∀ k x₁ x₂, x₁ ≤ x₂ →
                ShockWear.CumDamage.cdfPow μ k x₂ * ShockWear.CumDamage.cdfPow μ (k+1) x₁
                  ≤ ShockWear.CumDamage.cdfPow μ k x₁ * ShockWear.CumDamage.cdfPow μ (k+1) x₂ := by
              intro k x₁ x₂ hx
              rcases hx.eq_or_lt with h | h
              · subst h; exact le_of_eq rfl
              have := hTP 2 (by norm_num) le_rfl ![k, k+1] ![x₁, x₂] (by simp) (by simp)
                (by
                  intro i j hij; fin_cases i <;> fin_cases j
                  · exact absurd hij (by decide)
                  · simp
                  · exact absurd hij (by decide)
                  · exact absurd hij (by decide))
                (by
                  intro i j hij; fin_cases i <;> fin_cases j
                  · exact absurd hij (by decide)
                  · simpa using h
                  · exact absurd hij (by decide)
                  · exact absurd hij (by decide))
              rw [Matrix.det_fin_two] at this
              simp at this
              linarith
            have hlc : ∀ k, ShockWear.CumDamage.cdfPow μ (k+2) x * ShockWear.CumDamage.cdfPow μ k x
                ≤ ShockWear.CumDamage.cdfPow μ (k+1) x ^ 2 := by
              intro k
              have hE : ShockWear.CumDamage.convPow μ (k+2) (Set.Iic x)
                    * ShockWear.CumDamage.convPow μ k (Set.Iic x)
                  ≤ ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x)
                    * ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x) := by
                calc ShockWear.CumDamage.convPow μ (k+2) (Set.Iic x)
                      * ShockWear.CumDamage.convPow μ k (Set.Iic x)
                    = ∫⁻ y, ShockWear.CumDamage.convPow μ (k+1) (Set.Iic (x - y))
                        * ShockWear.CumDamage.convPow μ k (Set.Iic x) ∂μ := by
                      rw [hconv (k+1) x, lintegral_mul_const' _ _ (hfin _ _)]
                  _ ≤ ∫⁻ y, ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x)
                        * ShockWear.CumDamage.convPow μ k (Set.Iic (x - y)) ∂μ := by
                      apply lintegral_mono_ae
                      filter_upwards [hae] with y hy
                      have h := hTP2 k (x - y) x (by linarith)
                      unfold ShockWear.CumDamage.cdfPow at h
                      rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (hfin _ _) (hfin _ _))
                        (ENNReal.mul_ne_top (hfin _ _) (hfin _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul]
                      linarith [mul_comm (ShockWear.CumDamage.convPow μ k (Set.Iic x)).toReal
                          (ShockWear.CumDamage.convPow μ (k+1) (Set.Iic (x - y))).toReal,
                        mul_comm (ShockWear.CumDamage.convPow μ k (Set.Iic (x-y))).toReal
                          (ShockWear.CumDamage.convPow μ (k+1) (Set.Iic x)).toReal]
                  _ = _ := by rw [lintegral_const_mul' _ _ (hfin _ _), ← hconv k x]
              have := ENNReal.toReal_mono (ENNReal.mul_ne_top (hfin _ _) (hfin _ _)) hE
              rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
              unfold ShockWear.CumDamage.cdfPow; rw [sq]; exact this
            set a : ℕ → ℝ := fun k => ShockWear.CumDamage.cdfPow μ k x with ha
            have key := seqlem a (fun k => hnn k x) (fun k => hanti k x) hlc
            intro r hr1 hr2
            interval_cases r
            · intro u v _ _ _ _
              rw [Matrix.det_fin_one]
              simp only [Matrix.of_apply, seqOnInt, one_mul]
              split_ifs
              · exact hnn _ _
              · exact le_rfl
            · intro u v _ _ hu hv
              rw [Matrix.det_fin_two]
              simp only [Matrix.of_apply]
              have hu' : u 0 < u 1 := hu (by decide)
              have hv' : v 0 < v 1 := hv (by decide)
              simp only [one_mul, sub_nonneg]
              by_cases hp : 0 ≤ u 0 - v 1
              · have e1 : seqOnInt a (u 0 - v 1) = a (u 0 - v 1).toNat := if_pos hp
                have e2 : seqOnInt a (u 1 - v 0) = a (u 1 - v 0).toNat := if_pos (by omega)
                have e3 : seqOnInt a (u 0 - v 0) = a (u 0 - v 0).toNat := if_pos (by omega)
                have e4 : seqOnInt a (u 1 - v 1) = a (u 1 - v 1).toNat := if_pos (by omega)
                rw [e1, e2, e3, e4]
                rcases le_total (u 0 - v 0) (u 1 - v 1) with h | h
                · have := key (u 0 - v 1).toNat (u 0 - v 0).toNat (u 1 - v 1).toNat (u 1 - v 0).toNat
                    (by omega) (by omega) (by omega)
                  linarith [mul_comm (a (u 0 - v 1).toNat) (a (u 1 - v 0).toNat)]
                · have := key (u 0 - v 1).toNat (u 1 - v 1).toNat (u 0 - v 0).toNat (u 1 - v 0).toNat
                    (by omega) (by omega) (by omega)
                  linarith [mul_comm (a (u 0 - v 1).toNat) (a (u 1 - v 0).toNat),
                    mul_comm (a (u 0 - v 0).toNat) (a (u 1 - v 1).toNat)]
              · have e1 : seqOnInt a (u 0 - v 1) = 0 := if_neg hp
                rw [e1, zero_mul]
                apply mul_nonneg <;> (unfold seqOnInt; split_ifs <;> simp [ha, hnn])
        · clear P1 P2 P3
          intro x hPF
          set a : ℕ → ℝ := fun k => ShockWear.CumDamage.cdfPow μ k x with ha
          have ha0 : ∀ k, 0 ≤ a k := fun k => hnn k x
          have hle1 : ∀ k, a k ≤ 1 := by
            intro k; have := hprob k
            exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
          have hlc : ∀ k, a (k+2) * a k ≤ a (k+1) ^ 2 := by
            intro k
            have := hPF 2 (by norm_num) le_rfl ![(k:ℤ)+1, (k:ℤ)+2] ![0, 1] (by simp) (by simp)
              (by
                intro i j hij; fin_cases i <;> fin_cases j
                · exact absurd hij (by decide)
                · simp
                · exact absurd hij (by decide)
                · exact absurd hij (by decide))
              (by
                intro i j hij; fin_cases i <;> fin_cases j
                · exact absurd hij (by decide)
                · simp
                · exact absurd hij (by decide)
                · exact absurd hij (by decide))
            rw [Matrix.det_fin_two] at this
            have q1 : ![(k:ℤ)+1, (k:ℤ)+2] 0 = (k:ℤ)+1 := rfl
            have q2 : ![(k:ℤ)+1, (k:ℤ)+2] 1 = (k:ℤ)+2 := rfl
            have r1 : ![(0:ℤ), 1] 0 = 0 := rfl
            have r2 : ![(0:ℤ), 1] 1 = 1 := rfl
            have s1 : seqOnInt a ((k:ℤ)+1 - 0) = a (k+1) := by
              unfold seqOnInt; rw [if_pos (by omega)]; congr 1 <;> omega
            have s2 : seqOnInt a ((k:ℤ)+2 - 1) = a (k+1) := by
              unfold seqOnInt; rw [if_pos (by omega)]; congr 1 <;> omega
            have s3 : seqOnInt a ((k:ℤ)+1 - 1) = a k := by
              unfold seqOnInt; rw [if_pos (by omega)]; congr 1 <;> omega
            have s4 : seqOnInt a ((k:ℤ)+2 - 0) = a (k+2) := by
              unfold seqOnInt; rw [if_pos (by omega)]; congr 1 <;> omega
            simp only [Matrix.of_apply, q1, q2, r1, r2, s1, s2, s3, s4] at this
            nlinarith [this]
          have key := seqlem a ha0 (fun k => hanti k x) hlc
          have core : ∀ X S T : ℝ, 0 ≤ X → 0 ≤ S → S ≤ T →
              (∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((X+T)^k / k.factorial))
                * (∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (S^k / k.factorial))
              ≤ (∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((X+S)^k / k.factorial))
                * (∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (T^k / k.factorial)) := by
            intro X S T hX hS hST
            set b : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (a k) with hb
            set E : ℝ → ℕ → ℝ≥0∞ := fun v k => ENNReal.ofReal (v^k / k.factorial) with hE'
            have hT : 0 ≤ T := le_trans hS hST
            have taylor : ∀ T : ℝ, 0 ≤ T → ∑' n, b n * E (X+T) n
                = ∑' p : ℕ × ℕ, b (p.1 + p.2) * (E X p.1 * E T p.2) := by
              intro T hT
              simp only [hE']
              have hbin : ∀ n : ℕ, (X+T)^n / n.factorial = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
                  X^p.1 / p.1.factorial * (T^p.2 / p.2.factorial) := by
                intro n
                rw [(Commute.all X T).add_pow', Finset.sum_div]
                refine Finset.sum_congr rfl fun kl hkl => ?_
                have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
                rw [nsmul_eq_mul, ← h, Nat.cast_add_choose]
                field_simp
              have hE : ∀ n : ℕ, b n * ENNReal.ofReal ((X+T)^n / n.factorial) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
                  b (p.1 + p.2) * (ENNReal.ofReal (X^p.1 / p.1.factorial)
                      * ENNReal.ofReal (T^p.2 / p.2.factorial)) := by
                intro n
                rw [hbin, ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity), Finset.mul_sum]
                refine Finset.sum_congr rfl fun kl hkl => ?_
                rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, ENNReal.ofReal_mul (by positivity)]
              simp_rw [hE]
              rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq, ENNReal.tsum_sigma']
              refine tsum_congr fun n => ?_
              rw [← Finset.tsum_subtype]
              rfl

            set h : ℕ → ℝ≥0∞ := fun j => ∑' i, b (i + j) * E X i with hh
            have hG : ∀ T : ℝ, 0 ≤ T → ∑' n, b n * E (X+T) n = ∑' j, h j * E T j := by
              intro T hT
              rw [taylor T hT, ENNReal.tsum_prod', ENNReal.tsum_comm]
              refine tsum_congr fun j => ?_
              rw [hh, ← ENNReal.tsum_mul_right]
              refine tsum_congr fun i => ?_
              ring
            have R : ∀ α β p q : ℝ≥0∞, α ≤ β → q ≤ p → α * p + β * q ≤ β * p + α * q := by
              intro α β p q h1 h2
              obtain ⟨δ, rfl⟩ := le_iff_exists_add.mp h1
              obtain ⟨ε, rfl⟩ := le_iff_exists_add.mp h2
              have : (α + δ) * (q + ε) + α * q = α * (q + ε) + (α + δ) * q + δ * ε := by ring
              rw [this]; exact le_self_add
            have hαβ : ∀ j l, l ≤ j → h j * b l ≤ h l * b j := by
              intro j l hlj
              simp only [hh, ← ENNReal.tsum_mul_right]
              refine ENNReal.tsum_le_tsum fun i => ?_
              have hr : a l * a (i + j) ≤ a j * a (i + l) := by
                rcases le_total j (i + l) with h1 | h1
                · exact key l j (i+l) (i+j) hlj h1 (by omega)
                · have := key l (i+l) j (i+j) (by omega) h1 (by omega); linarith [mul_comm (a j) (a (i+l))]
              have : b (i + j) * E X i * b l ≤ b (i + l) * E X i * b j := by
                simp only [hb, hE']
                rw [mul_right_comm, mul_right_comm (ENNReal.ofReal (a (i+l))), ← ENNReal.ofReal_mul (ha0 _),
                  ← ENNReal.ofReal_mul (ha0 _)]
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
                  (by linarith [mul_comm (a l) (a (i+j)), mul_comm (a j) (a (i+l))])) bot_le
              exact this
            have hpq : ∀ j l, l ≤ j → E T l * E S j ≤ E T j * E S l := by
              intro j l hlj
              simp only [hE']
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              apply ENNReal.ofReal_le_ofReal
              obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlj
              have h1 : S ^ d ≤ T ^ d := pow_le_pow_left₀ hS hST d
              have h2 : 0 ≤ T ^ l * S ^ l := by positivity
              rw [div_mul_div_comm, div_mul_div_comm, mul_comm ((l+d).factorial : ℝ)]
              apply div_le_div_of_nonneg_right _ (by positivity)
              rw [pow_add, pow_add]
              nlinarith [mul_le_mul_of_nonneg_left h1 h2]
            set F : ℕ → ℕ → ℝ≥0∞ := fun j l => h j * b l * (E T j * E S l) with hF
            set H : ℕ → ℕ → ℝ≥0∞ := fun j l => h l * b j * (E T j * E S l) with hH
            have hpt : ∀ j l, F j l + F l j ≤ H j l + H l j := by
              intro j l
              simp only [hF, hH]
              rcases le_total l j with hlj | hjl
              · have := R (h j * b l) (h l * b j) (E T j * E S l) (E T l * E S j) (hαβ j l hlj) (hpq j l hlj)
                exact this
              · have := R (h l * b j) (h j * b l) (E T l * E S j) (E T j * E S l) (hαβ l j hjl) (hpq l j hjl)
                rw [add_comm (h j * b l * (E T j * E S l)), add_comm (h l * b j * (E T j * E S l))]
                exact this
            have hU : (∑' n, b n * E (X+T) n) * (∑' n, b n * E S n) = ∑' j, ∑' l, F j l := by
              rw [hG T hT, ← ENNReal.tsum_mul_right]
              refine tsum_congr fun j => ?_
              rw [← ENNReal.tsum_mul_left]
              refine tsum_congr fun l => ?_
              simp only [hF]; ring
            have hV : (∑' n, b n * E (X+S) n) * (∑' n, b n * E T n) = ∑' j, ∑' l, H j l := by
              rw [hG S hS, ← ENNReal.tsum_mul_right]
              conv_rhs => rw [ENNReal.tsum_comm]
              refine tsum_congr fun l => ?_
              rw [← ENNReal.tsum_mul_left]
              refine tsum_congr fun j => ?_
              simp only [hH]; ring
            have hsum : ∑' j, ∑' l, (F j l + F l j) ≤ ∑' j, ∑' l, (H j l + H l j) :=
              ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun l => hpt j l
            simp only [ENNReal.tsum_add] at hsum
            rw [ENNReal.tsum_comm (f := fun j l => F l j), ENNReal.tsum_comm (f := fun j l => H l j)] at hsum
            rw [hU, hV]
            have h2 : (2:ℝ≥0∞) * ∑' j, ∑' l, F j l ≤ 2 * ∑' j, ∑' l, H j l := by
              rw [two_mul, two_mul]; exact hsum
            exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
          have hconvS : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (ShockWear.CumDamage.shockSurv lam a t)
              = ENNReal.ofReal (Real.exp (-(lam * t))) *
                ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((lam * t)^k / k.factorial) := by
            intro t ht
            unfold ShockWear.CumDamage.shockSurv
            rw [if_neg (not_lt.mpr ht)]
            have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
            have hsum : Summable fun k => a k * ShockWear.CumDamage.poisW lam t k := by
              refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
                ((Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t))))
              · unfold ShockWear.CumDamage.poisW; exact mul_nonneg (ha0 k) (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlt k)) (Nat.cast_nonneg _))
              · unfold ShockWear.CumDamage.poisW
                have : 0 ≤ Real.exp (-(lam * t)) * (lam * t) ^ k / k.factorial := div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlt k)) (Nat.cast_nonneg _)
                calc a k * (Real.exp (-(lam * t)) * (lam * t) ^ k / k.factorial)
                    ≤ 1 * (Real.exp (-(lam * t)) * (lam * t) ^ k / k.factorial) :=
                      mul_le_mul_of_nonneg_right (hle1 k) this
                  _ = _ := by ring
            rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by unfold ShockWear.CumDamage.poisW; exact mul_nonneg (ha0 k) (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlt k)) (Nat.cast_nonneg _))) hsum,
              ← ENNReal.tsum_mul_left]
            refine tsum_congr fun k => ?_
            unfold ShockWear.CumDamage.poisW
            rw [← ENNReal.ofReal_mul (ha0 k), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 1; ring
          have hSnn : ∀ t, 0 ≤ ShockWear.CumDamage.shockSurv lam a t := by
            intro t; unfold ShockWear.CumDamage.shockSurv; split_ifs with h0
            · norm_num
            · have hlt : 0 ≤ lam * t := mul_nonneg hlam.le (not_lt.mp h0)
              exact tsum_nonneg fun k => mul_nonneg (ha0 k) (by unfold ShockWear.CumDamage.poisW; exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlt k)) (Nat.cast_nonneg _))
          intro y hy s t hs hst
          have ht : 0 ≤ t := le_trans hs hst
          rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hSnn _) (hSnn _)),
            ENNReal.ofReal_mul (hSnn _), ENNReal.ofReal_mul (hSnn _),
            hconvS _ (by linarith), hconvS _ hs, hconvS _ (by linarith), hconvS _ ht]
          have hc := core (lam * y) (lam * s) (lam * t) (by positivity) (mul_nonneg hlam.le hs)
            (mul_le_mul_of_nonneg_left hst hlam.le)
          rw [← mul_add, ← mul_add] at hc
          have hexp : ENNReal.ofReal (Real.exp (-(lam * (y + t)))) * ENNReal.ofReal (Real.exp (-(lam * s)))
              = ENNReal.ofReal (Real.exp (-(lam * (y + s)))) * ENNReal.ofReal (Real.exp (-(lam * t))) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← Real.exp_add, ← Real.exp_add]
            congr 2; ring
          calc ENNReal.ofReal (Real.exp (-(lam * (y + t)))) * (∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((lam * (y + t))^k / k.factorial))
                * (ENNReal.ofReal (Real.exp (-(lam * s))) * ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((lam * s)^k / k.factorial))
              = (ENNReal.ofReal (Real.exp (-(lam * (y + t)))) * ENNReal.ofReal (Real.exp (-(lam * s)))) *
                ((∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((lam * (y + t))^k / k.factorial))
                * ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((lam * s)^k / k.factorial)) := by ring
            _ ≤ (ENNReal.ofReal (Real.exp (-(lam * (y + s)))) * ENNReal.ofReal (Real.exp (-(lam * t)))) *
                ((∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((lam * (y + s))^k / k.factorial))
                * ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal ((lam * t)^k / k.factorial)) := by
                  rw [hexp]; exact mul_le_mul_of_nonneg_left hc bot_le
            _ = _ := by ring
