-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:37.855817+00:00
-- url     : https://prove2.me/submissions/e808bda8-39be-44c8-b902-e43754ecd886

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (hI : Standing I)
    (hpc : PerfectCompetition I) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ b : Fin n → Fin m → ℝ, IsPNE I Δ b := by
      classical
      have hB0 : ∀ i, 0 < I.B i := fun i => lt_of_lt_of_le one_pos (hI.one_le_B i)
      let act : Fin n → Prop := fun i => ((D I i).card : ℝ) * Δ ≤ I.B i
      have hmemD : ∀ i j, j ∈ D I i ↔ 0 < I.v i j := by
        intro i j; simp [D]
      let j0 : Fin m := ⟨0, hI.pos_m⟩
      let s : Fin n → Fin m → ℝ := fun i j => if j = j0 then I.B i else 0
      let c : Fin n → Fin m → ℝ := fun i j => if Δ ≤ s i j then s i j else 0
      have hs0 : ∀ i j, 0 ≤ s i j ∧ s i j ≤ I.B i := by
        intro i j
        simp only [s]
        split_ifs
        · exact ⟨(hB0 i).le, le_refl _⟩
        · exact ⟨le_refl _, (hB0 i).le⟩
      have hc0 : ∀ i j, 0 ≤ c i j ∧ c i j ≤ I.B i := by
        intro i j
        simp only [c]
        split_ifs
        · exact hs0 i j
        · exact ⟨le_refl _, (hB0 i).le⟩
      let K : Set (Fin n → Fin m → ℝ) := {e | ∀ i, (act i → (∀ j, 0 < I.v i j → Δ ≤ e i j) ∧
        (∀ j, ¬ 0 < I.v i j → e i j = 0) ∧ ∑ j, e i j = I.B i) ∧ (¬ act i → ∀ j, e i j = c i j)}
      have hKbd : ∀ e ∈ K, ∀ i j, 0 ≤ e i j ∧ e i j ≤ I.B i := by
        intro e he i j
        by_cases ha : act i
        · obtain ⟨h1, h2, h3⟩ := (he i).1 ha
          have hnn : ∀ l, 0 ≤ e i l := by
            intro l
            by_cases hv : 0 < I.v i l
            · exact hΔ.le.trans (h1 l hv)
            · rw [h2 l hv]
          refine ⟨hnn j, ?_⟩
          rw [← h3]
          exact Finset.single_le_sum (f := fun l => e i l) (fun l _ => hnn l) (Finset.mem_univ j)
        · rw [(he i).2 ha j]
          exact hc0 i j
      have hev : ∀ i j, Continuous (fun e : Fin n → Fin m → ℝ => e i j) := by
        intro i j
        exact (continuous_apply j).comp (continuous_apply i)
      have hKclosed : IsClosed K := by
        simp only [K, Set.ofPred_forall]
        refine isClosed_iInter fun i => ?_
        by_cases ha : act i
        · simp only [ha, true_implies, not_true_eq_false, false_implies, and_true]
          have c1 : IsClosed {e : Fin n → Fin m → ℝ | ∀ j, 0 < I.v i j → Δ ≤ e i j} := by
            simp only [Set.ofPred_forall]
            exact isClosed_iInter fun j => isClosed_iInter fun _ =>
              isClosed_le continuous_const (hev i j)
          have c2 : IsClosed {e : Fin n → Fin m → ℝ | ∀ j, ¬ 0 < I.v i j → e i j = 0} := by
            simp only [Set.ofPred_forall]
            exact isClosed_iInter fun j => isClosed_iInter fun _ =>
              isClosed_eq (hev i j) continuous_const
          refine IsClosed.inter c1 (IsClosed.inter c2 ?_)
          · exact isClosed_eq (continuous_finsetSum _ fun j _ => hev i j) continuous_const
        · simp only [ha, false_implies, not_false_eq_true, true_implies, true_and]
          simp only [Set.ofPred_forall]
          exact isClosed_iInter fun j => isClosed_eq (hev i j) continuous_const
      have hKcompact : IsCompact K := by
        refine IsCompact.of_isClosed_subset
          (isCompact_Icc (a := (0 : Fin n → Fin m → ℝ)) (b := fun i _ => I.B i)) hKclosed ?_
        intro e he
        exact ⟨fun i j => (hKbd e he i j).1, fun i j => (hKbd e he i j).2⟩
      have hKne : K.Nonempty := by
        refine ⟨fun i j => if act i then (if 0 < I.v i j then I.B i / (D I i).card else 0) else c i j,
          ?_⟩
        intro i
        have hcard : (0 : ℝ) < (D I i).card := by
          exact_mod_cast Finset.card_pos.mpr (hI.D_nonempty i)
        refine ⟨fun ha => ⟨?_, ?_, ?_⟩, ?_⟩
        · intro j hv
          simp only [ha, hv, if_true]
          rw [le_div_iff₀ hcard, mul_comm]
          exact ha
        · intro j hv
          simp [ha, hv]
        · simp only [ha, if_true]
          rw [← Finset.sum_filter]
          change ∑ j ∈ D I i, I.B i / ((D I i).card : ℝ) = I.B i
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
        · intro ha j
          simp [ha]
      let F : (Fin n → Fin m → ℝ) → ℝ := fun e =>
        (∑ i, ∑ j, (e i j * Real.log (e i j) - e i j * Real.log (I.v i j)))
          - ∑ j, (∑ i, e i j) * Real.log (∑ i, e i j)
      have hFc : Continuous F := by
        refine Continuous.sub ?_ ?_
        · refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
          exact (Real.continuous_mul_log.comp (hev i j)).sub ((hev i j).mul continuous_const)
        · refine continuous_finsetSum _ fun j _ => ?_
          exact Real.continuous_mul_log.comp (continuous_finsetSum _ fun i _ => hev i j)
      obtain ⟨e, heK, hemin⟩ := hKcompact.exists_isMinOn hKne hFc.continuousOn
      have hEnn : ∀ i j, 0 ≤ e i j := fun i j => (hKbd e heK i j).1
      have hEpos : ∀ i j, 0 < e i j → 0 < ∑ a, e a j := by
        intro i j h
        exact lt_of_lt_of_le h
          (Finset.single_le_sum (f := fun a => e a j) (fun a _ => hEnn a j) (Finset.mem_univ i))
      have key : ∀ i, act i → ∀ j k, 0 < I.v i j → 0 < I.v i k → Δ < e i j →
          e i j / (∑ a, e a j) / I.v i j ≤ e i k / (∑ a, e a k) / I.v i k := by
        intro i ha j k hvj hvk hj
        by_cases hjk : j = k
        · subst hjk; exact le_refl _
        obtain ⟨h1, h2, h3⟩ := (heK i).1 ha
        have hekpos : 0 < e i k := hΔ.trans_le (h1 k hvk)
        have hejpos : 0 < e i j := hΔ.trans hj
        have hPj := hEpos i j hejpos
        have hPk := hEpos i k hekpos
        let δ : Fin m → ℝ := fun l => (if l = k then 1 else 0) - (if l = j then 1 else 0)
        let d : Fin n → Fin m → ℝ := fun a l => if a = i then δ l else 0
        have hδk : δ k = 1 := by simp [δ, Ne.symm hjk]
        have hδj : δ j = -1 := by simp [δ, hjk]
        have hδo : ∀ l, l ≠ k → l ≠ j → δ l = 0 := by
          intro l hl hl'; simp [δ, hl, hl']
        have hdsum : ∀ l, ∑ a, d a l = δ l := by
          intro l; simp [d]
        let G : ℝ := (∑ a, ∑ l, d a l * (Real.log (e a l) + 1 - Real.log (I.v a l)))
          - ∑ l, δ l * (Real.log (∑ a, e a l) + 1)
        have hlin : ∀ x y : ℝ, HasDerivAt (fun ε : ℝ => x + ε * y) y 0 := by
          intro x y
          simpa using ((hasDerivAt_id (0:ℝ)).mul_const y).const_add x
        have hml : ∀ x y : ℝ, (y ≠ 0 → x ≠ 0) →
            HasDerivAt (fun ε : ℝ => (x + ε * y) * Real.log (x + ε * y)) (y * (Real.log x + 1)) 0 := by
          intro x y hxy
          by_cases hy : y = 0
          · subst hy
            simpa using hasDerivAt_const (0:ℝ) (x * Real.log x)
          · have hx := hxy hy
            have h := Real.hasDerivAt_mul_log hx
            have h' : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log x + 1) (x + 0 * y) := by
              simpa using h
            have := h'.comp (0:ℝ) (hlin x y)
            rw [mul_comm]
            exact this
        have hsumlin : ∀ l (ε : ℝ), ∑ a, (e a l + ε * d a l) = (∑ a, e a l) + ε * δ l := by
          intro l ε
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdsum]
        have hcase : ∀ l, δ l ≠ 0 → 0 < e i l := by
          intro l hl
          by_cases hlk : l = k
          · rw [hlk]; exact hekpos
          · by_cases hlj : l = j
            · rw [hlj]; exact hejpos
            · exact absurd (hδo l hlk hlj) hl
        have hder : HasDerivAt (fun ε : ℝ => F (fun a l => e a l + ε * d a l)) G 0 := by
          simp only [F, hsumlin]
          refine HasDerivAt.fun_sub ?_ ?_
          · refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun l _ => ?_
            have h := (hml (e a l) (d a l) (by
              intro hne
              by_cases hai : a = i
              · subst hai
                have : δ l ≠ 0 := by simpa [d] using hne
                exact (hcase l this).ne'
              · exact absurd (by simp [d, hai]) hne)).fun_sub
              ((hlin (e a l) (d a l)).mul_const (Real.log (I.v a l)))
            convert h using 1
            ring
          · refine HasDerivAt.fun_sum fun l _ => ?_
            exact hml _ _ (fun hne => (hEpos i l (hcase l hne)).ne')
        have hGval : G = (Real.log (e i k) + 1 - Real.log (I.v i k) - (Real.log (∑ a, e a k) + 1))
            - (Real.log (e i j) + 1 - Real.log (I.v i j) - (Real.log (∑ a, e a j) + 1)) := by
          have hgen : ∀ w : Fin m → ℝ, ∑ l, δ l * w l = w k - w j := by
            intro w
            simp [δ, sub_mul, Finset.sum_sub_distrib]
          have h1' : ∑ a, ∑ l, d a l * (Real.log (e a l) + 1 - Real.log (I.v a l))
              = ∑ l, δ l * (Real.log (e i l) + 1 - Real.log (I.v i l)) := by
            rw [Finset.sum_eq_single i]
            · simp [d]
            · intro a _ hai
              simp [d, hai]
            · simp
          simp only [G]
          rw [h1', hgen, hgen]
          ring
        have hG0 : 0 ≤ G := by
          have ht := hder.tendsto_slope_zero_right
          refine ge_of_tendsto ht ?_
          have hmem : Set.Ioo (0:ℝ) (e i j - Δ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
            Ioo_mem_nhdsGT (by linarith)
          filter_upwards [hmem] with ε hε
          have hinK : (fun a l => e a l + ε * d a l) ∈ K := by
            intro a
            by_cases hai : a = i
            · subst hai
              refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun h => absurd ha h⟩
              · intro l hl
                have := h1 l hl
                simp only [d, if_true]
                by_cases hlk : l = k
                · rw [hlk, hδk]; rw [hlk] at this; linarith [hε.1]
                · by_cases hlj : l = j
                  · rw [hlj, hδj]; linarith [hε.2]
                  · rw [hδo l hlk hlj]; linarith
              · intro l hl
                have hlk : l ≠ k := by rintro rfl; exact hl hvk
                have hlj : l ≠ j := by rintro rfl; exact hl hvj
                simp [d, hδo l hlk hlj, h2 l hl]
              · have : ∑ l, δ l = 0 := by simp [δ, Finset.sum_sub_distrib]
                simp only [d, if_true]
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, this, h3]
                ring
            · have : ∀ l, e a l + ε * d a l = e a l := by intro l; simp [d, hai]
              simp only [this]
              exact heK a
          have hle : F e ≤ F (fun a l => e a l + ε * d a l) := hemin hinK
          simp only [zero_add, zero_mul, add_zero, smul_eq_mul]
          exact mul_nonneg (inv_nonneg.mpr hε.1.le) (by simpa using sub_nonneg.mpr hle)
        rw [hGval] at hG0
        have hl : ∀ l, 0 < e i l → 0 < (∑ a, e a l) → 0 < I.v i l →
            Real.log (e i l / (∑ a, e a l) / I.v i l)
              = Real.log (e i l) - Real.log (∑ a, e a l) - Real.log (I.v i l) := by
          intro l p1 p2 p3
          rw [Real.log_div (div_pos p1 p2).ne' p3.ne', Real.log_div p1.ne' p2.ne']
        rw [← Real.log_le_log_iff (div_pos (div_pos hejpos hPj) hvj) (div_pos (div_pos hekpos hPk) hvk),
          hl j hejpos hPj hvj, hl k hekpos hPk hvk]
        linarith
      let b : Fin n → Fin m → ℝ := fun i j => if act i then e i j else s i j
      have heff : ∀ i j, effBid Δ b i j = e i j := by
        intro i j
        by_cases ha : act i
        · obtain ⟨h1, h2, h3⟩ := (heK i).1 ha
          simp only [effBid, b, ha, if_true]
          by_cases hv : 0 < I.v i j
          · rw [if_pos (h1 j hv)]
          · rw [h2 j hv, if_neg (not_le.mpr hΔ)]
        · rw [(heK i).2 ha j]
          simp [effBid, b, ha, c]
      have hunn : ∀ i, 0 ≤ u I i (tpAlloc Δ b i) := by
        intro i
        rw [u, dif_pos (hI.D_nonempty i)]
        rw [Finset.le_inf'_iff]
        intro j hj
        refine div_nonneg ?_ (hI.v_nonneg i j)
        rw [tpAlloc]
        simp only [heff]
        split_ifs
        · exact div_nonneg (hEnn i j) (Finset.sum_nonneg fun a _ => hEnn a j)
        · exact le_refl _
      refine ⟨b, ?_, ?_⟩
      · intro i
        by_cases ha : act i
        · have hbi : b i = e i := by funext j; simp [b, ha]
          rw [hbi]
          exact ⟨fun j => hKbd e heK i j, ((heK i).1 ha).2.2⟩
        · have hbi : b i = s i := by funext j; simp [b, ha]
          rw [hbi]
          refine ⟨fun j => hs0 i j, ?_⟩
          simp [s]
      · intro i b' hb'
        have hbase : u I i (tpAlloc Δ (Function.update b i b') i) ≤ 0 ∨
            ∀ j, 0 < I.v i j → Δ ≤ b' j := by
          by_contra hcon
          push Not at hcon
          obtain ⟨hpos, j, hvj, hlt⟩ := hcon
          have hle : u I i (tpAlloc Δ (Function.update b i b') i) ≤
              tpAlloc Δ (Function.update b i b') i j / I.v i j := by
            rw [u, dif_pos (hI.D_nonempty i)]
            exact Finset.inf'_le _ ((hmemD i j).2 hvj)
          have : tpAlloc Δ (Function.update b i b') i j = 0 := by
            simp [tpAlloc, effBid, not_le.mpr hlt]
          rw [this, zero_div] at hle
          linarith
        rcases hbase with h0 | hall
        · exact h0.trans (hunn i)
        have hsumD : ∑ j ∈ D I i, b' j ≤ I.B i := by
          rw [← hb'.2]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => (hb'.1 j).1)
        have ha : act i := by
          refine le_trans ?_ hsumD
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          exact Finset.sum_le_sum fun j hj => hall j ((hmemD i j).1 hj)
        obtain ⟨h1, h2, h3⟩ := (heK i).1 ha
        have hsumE : ∑ j ∈ D I i, e i j = I.B i := by
          rw [← h3]
          refine Finset.sum_subset (Finset.subset_univ _) ?_
          intro j _ hj
          exact h2 j (fun h => hj ((hmemD i j).2 h))
        have hx : ∀ j, 0 < I.v i j → tpAlloc Δ b i j = e i j / ∑ a, e a j := by
          intro j hv
          rw [tpAlloc]
          simp only [heff]
          rw [if_pos (hΔ.trans_le (h1 j hv))]
        -- deviation is no better on goods where the bid is not raised
        have hdev : ∀ j, 0 < I.v i j → b' j ≤ e i j →
            u I i (tpAlloc Δ (Function.update b i b') i) ≤ e i j / (∑ a, e a j) / I.v i j := by
          intro j hv hle
          have hle1 : u I i (tpAlloc Δ (Function.update b i b') i) ≤
              tpAlloc Δ (Function.update b i b') i j / I.v i j := by
            rw [u, dif_pos (hI.D_nonempty i)]
            exact Finset.inf'_le _ ((hmemD i j).2 hv)
          refine hle1.trans ?_
          refine div_le_div_of_nonneg_right ?_ hv.le
          have hb'j := hall j hv
          have hself : effBid Δ (Function.update b i b') i j = b' j := by
            simp [effBid, hb'j]
          have hother : ∀ a, a ≠ i → effBid Δ (Function.update b i b') a j = e a j := by
            intro a hai
            rw [← heff a j]
            simp [effBid, hai]
          have hb'pos : 0 < b' j := hΔ.trans_le hb'j
          rw [tpAlloc, hself, if_pos hb'pos,
            ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase (Finset.univ) (fun a => e a j) (Finset.mem_univ i), hself]
          rw [Finset.sum_congr rfl (fun a h => hother a (Finset.ne_of_mem_erase h))]
          have hQ : 0 ≤ ∑ a ∈ Finset.univ.erase i, e a j := Finset.sum_nonneg fun a _ => hEnn a j
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith
        obtain ⟨j1, hj1, hj1min⟩ := Finset.exists_mem_eq_inf' (hI.D_nonempty i)
          (fun j => tpAlloc Δ b i j / I.v i j)
        have hv1 := (hmemD i j1).1 hj1
        have hu : u I i (tpAlloc Δ b i) = e i j1 / (∑ a, e a j1) / I.v i j1 := by
          rw [u, dif_pos (hI.D_nonempty i), hj1min, hx j1 hv1]
        rw [hu]
        by_cases hle : b' j1 ≤ e i j1
        · exact hdev j1 hv1 hle
        · push Not at hle
          have hex : ∃ k ∈ D I i, b' k < e i k := by
            by_contra hno
            push Not at hno
            have := Finset.sum_lt_sum hno ⟨j1, hj1, hle⟩
            linarith
          obtain ⟨k, hk, hlt⟩ := hex
          have hvk := (hmemD i k).1 hk
          exact (hdev k hvk hlt.le).trans
            (key i ha k j1 hvk hv1 (lt_of_le_of_lt (hall k hvk) hlt))
