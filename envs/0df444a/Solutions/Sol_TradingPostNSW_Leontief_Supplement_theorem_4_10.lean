-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_4_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:52.170542+00:00
-- url     : https://prove2.me/submissions/6062d43c-8902-4a11-bc8d-bc4e1a2108c4

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (hI : GenStanding I)
    (U : Fin n → (Fin m → ℝ) → ℝ) (hU : ∀ i, IsConcaveUtility (U i))
    (hpc : PerfectCompetitionU U) (b : Fin n → Fin m → ℝ) (hb : IsPNEU I U 0 b)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSWU I U y ≤ 2 * NSWU I U (tpAlloc 0 b) := by
      obtain ⟨hstrat, hdev⟩ := hb
      have hBpos : ∀ i, 0 < I.B i := fun i => lt_of_lt_of_le one_pos (hI.one_le_B i)
      have hbnn : ∀ i j, 0 ≤ b i j := fun i j => ((hstrat i).1 j).1
      have hmne : (Finset.univ : Finset (Fin m)).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, hI.pos_m⟩⟩
      -- allocations lie in the box
      have halloc : ∀ (c : Fin n → Fin m → ℝ), (∀ i j, 0 ≤ c i j) → ∀ i,
          tpAlloc 0 c i ∈ box m := by
        intro c hc i
        refine ⟨fun j => ?_, fun j => ?_⟩
        · simp only [Pi.zero_apply, tpAlloc]
          split_ifs with h
          · apply div_nonneg h.le
            exact Finset.sum_nonneg (fun k _ => by simp only [effBid]; split_ifs <;> simp [hc k j])
          · exact le_refl _
        · simp only [Pi.one_apply, tpAlloc]
          split_ifs with h
          · apply div_le_one_of_le₀
            · exact Finset.single_le_sum (f := fun k => effBid 0 c k j)
                (fun k _ => by simp only [effBid]; split_ifs <;> simp [hc k j]) (Finset.mem_univ i)
            · exact Finset.sum_nonneg (fun k _ => by simp only [effBid]; split_ifs <;> simp [hc k j])
          · exact zero_le_one
      have hyle : ∀ i j, y i j ≤ 1 := by
        intro i j
        rw [← hy.2 j]
        exact Finset.single_le_sum (f := fun k => y k j) (fun k _ => hy.1 k j) (Finset.mem_univ i)
      have hybox : ∀ i, y i ∈ box m := fun i => ⟨fun j => hy.1 i j, fun j => hyle i j⟩
      have h0box : (0 : Fin m → ℝ) ∈ box m := ⟨le_refl _, fun j => zero_le_one⟩
      set x := tpAlloc 0 b with hx
      have hxbox : ∀ i, x i ∈ box m := halloc b hbnn
      have hp : ∀ j, 0 ≤ bidPrice b j := fun j => Finset.sum_nonneg (fun k _ => hbnn k j)
      -- key per-agent inequality
      have key : ∀ i, I.B i * U i (y i) ≤ U i (x i) * (I.B i + ∑ j, y i j * bidPrice b j) := by
        intro i
        have hUx : 0 ≤ U i (x i) := (hU i).2.2 _ (hxbox i)
        have hUy : 0 ≤ U i (y i) := (hU i).2.2 _ (hybox i)
        have hε : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → I.B i * U i (y i) ≤
            U i (x i) * (I.B i * (1 + ε) + ∑ j, (y i j + ε) * (bidPrice b j + ε)) := by
          intro ε hε0 hε1
          have hw : ∀ j, 0 < (y i j + ε) * (bidPrice b j + ε) := fun j =>
            mul_pos (by linarith [hy.1 i j]) (by linarith [hp j])
          set W := ∑ j, (y i j + ε) * (bidPrice b j + ε) with hW
          have hWpos : 0 < W := Finset.sum_pos (fun j _ => hw j) hmne
          have hwle : ∀ j, (y i j + ε) * (bidPrice b j + ε) ≤ W := fun j =>
            Finset.single_le_sum (f := fun j => (y i j + ε) * (bidPrice b j + ε))
              (fun j _ => (hw j).le) (Finset.mem_univ j)
          set b' : Fin m → ℝ := fun j => I.B i * ((y i j + ε) * (bidPrice b j + ε)) / W with hb'
          have hb'pos : ∀ j, 0 < b' j := fun j => div_pos (mul_pos (hBpos i) (hw j)) hWpos
          have hb'S : Strategy I i b' := by
            refine ⟨fun j => ⟨(hb'pos j).le, ?_⟩, ?_⟩
            · simp only [hb']
              rw [div_le_iff₀ hWpos]
              exact mul_le_mul_of_nonneg_left (hwle j) (hBpos i).le
            · simp only [hb']
              rw [← Finset.sum_div, ← Finset.mul_sum, ← hW]
              field_simp
          have hdev' := hdev i b' hb'S
          set c := Function.update b i b' with hc
          have hcnn : ∀ k j, 0 ≤ c k j := by
            intro k j
            simp only [hc, Function.update_apply]
            split_ifs
            · exact (hb'pos j).le
            · exact hbnn k j
          have hcii : c i = b' := by simp [hc]
          have heff : ∀ k j, effBid 0 c k j = c k j := by
            intro k j; simp [effBid, hcnn k j]
          have hS : ∀ j, ∑ k, c k j ≤ b' j + bidPrice b j := by
            intro j
            calc ∑ k, c k j ≤ ∑ k, (b k j + if k = i then b' j else 0) := by
                  apply Finset.sum_le_sum
                  intro k _
                  simp only [hc, Function.update_apply]
                  split_ifs
                  · linarith [hbnn k j]
                  · linarith
              _ = b' j + bidPrice b j := by
                  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
                  simp [bidPrice, add_comm]
          have hSge : ∀ j, b' j ≤ ∑ k, c k j := by
            intro j
            have := Finset.single_le_sum (f := fun k => c k j) (fun k _ => hcnn k j)
              (Finset.mem_univ i)
            simpa [hcii] using this
          set D := I.B i * (1 + ε) + W with hD
          have hDpos : 0 < D := by have := hBpos i; nlinarith
          set lam := I.B i / D with hlam
          have hlam0 : 0 ≤ lam := div_nonneg (hBpos i).le hDpos.le
          have hlam1 : lam ≤ 1 := by
            rw [hlam, div_le_one hDpos]; have := hBpos i; nlinarith
          have hx'ge : ∀ j, lam * y i j ≤ tpAlloc 0 c i j := by
            intro j
            simp only [tpAlloc, heff, hcii, if_pos (hb'pos j)]
            have hSpos : 0 < ∑ k, c k j := lt_of_lt_of_le (hb'pos j) (hSge j)
            rw [hlam, div_mul_eq_mul_div, div_le_div_iff₀ hDpos hSpos]
            -- b' * D ≥ B y S
            have h1 : b' j * W = I.B i * ((y i j + ε) * (bidPrice b j + ε)) := by
              simp only [hb']; field_simp
            have hyy := hy.1 i j
            have hyl := hyle i j
            have hpj := hp j
            have hBi := hBpos i
            have h2 : I.B i * y i j * bidPrice b j ≤ b' j * W := by
              rw [h1, mul_assoc]
              apply mul_le_mul_of_nonneg_left _ hBi.le
              nlinarith [mul_nonneg hyy hpj]
            have h3 : I.B i * y i j * b' j ≤ b' j * (I.B i * (1 + ε)) := by
              have := hb'pos j; nlinarith [mul_nonneg hBi.le this.le]
            have h4 : I.B i * y i j * ∑ k, c k j ≤ I.B i * y i j * (b' j + bidPrice b j) :=
              mul_le_mul_of_nonneg_left (hS j) (mul_nonneg hBi.le hyy)
            rw [hD]; nlinarith
          have hmono : U i (lam • y i) ≤ U i (tpAlloc 0 c i) := by
            apply (hU i).2.1
            · refine ⟨fun j => ?_, fun j => ?_⟩
              · simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
                exact mul_nonneg hlam0 (hy.1 i j)
              · simp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul]
                nlinarith [hy.1 i j, hyle i j]
            · exact halloc c hcnn i
            · intro j; simpa [smul_eq_mul] using hx'ge j
          have hconc : lam * U i (y i) ≤ U i (lam • y i) := by
            have := (hU i).1.2 (hybox i) h0box hlam0 (by linarith : 0 ≤ 1 - lam)
              (by ring : lam + (1 - lam) = 1)
            simp only [smul_zero, add_zero, smul_eq_mul] at this
            have hU0 := (hU i).2.2 _ h0box
            nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - lam) hU0]
          have hfin : lam * U i (y i) ≤ U i (x i) := le_trans hconc (le_trans hmono hdev')
          rw [hlam, div_mul_eq_mul_div, div_le_iff₀ hDpos] at hfin
          linarith
        -- W bound
        set K := ∑ j, (y i j + bidPrice b j + 1) with hK
        have hK0 : 0 ≤ K := Finset.sum_nonneg (fun j _ => by linarith [hy.1 i j, hp j])
        have hWb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∑ j, (y i j + ε) * (bidPrice b j + ε) ≤ ∑ j, y i j * bidPrice b j + ε * K := by
          intro ε hε0 hε1
          rw [hK, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro j _
          nlinarith [hy.1 i j, hp j]
        set cc := ∑ j, y i j * bidPrice b j
        have hall : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            I.B i * U i (y i) ≤ U i (x i) * (I.B i + cc) + ε * (U i (x i) * (I.B i + K)) := by
          intro ε hε0 hε1
          have h1 := hε ε hε0 hε1
          have h2 := hWb ε hε0 hε1
          have h3 : U i (x i) * (I.B i * (1 + ε) + ∑ j, (y i j + ε) * (bidPrice b j + ε)) ≤
              U i (x i) * (I.B i * (1 + ε) + (cc + ε * K)) :=
            mul_le_mul_of_nonneg_left (by linarith) hUx
          nlinarith
        apply le_of_forall_pos_le_add
        intro δ hδ
        set L := U i (x i) * (I.B i + K) with hL
        have hL0 : 0 ≤ L := mul_nonneg hUx (by linarith [hBpos i])
        set ε := min 1 (δ / (L + 1)) with hεdef
        have hε0 : 0 < ε := lt_min one_pos (div_pos hδ (by linarith))
        have hε1 : ε ≤ 1 := min_le_left _ _
        have hεL : ε * L ≤ δ := by
          have : ε ≤ δ / (L + 1) := min_le_right _ _
          rw [le_div_iff₀ (by linarith)] at this
          nlinarith
        have := hall ε hε0 hε1
        linarith
      have hsumc : ∑ i, ∑ j, y i j * bidPrice b j = totalBudget I := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hy.2, one_mul]
        simp only [bidPrice, totalBudget]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => (hstrat i).2)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [NSWU]
      have hBt : 0 < totalBudget I :=
        Finset.sum_pos (fun i _ => hBpos i) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      have hN : ∀ z : Fin n → Fin m → ℝ, (∀ i, 0 ≤ U i (z i)) →
          NSWU I U z = ∏ i, U i (z i) ^ (I.B i / totalBudget I) := by
        intro z hz
        unfold NSWU
        rw [← Real.finsetProd_rpow _ _ (fun i _ => Real.rpow_nonneg (hz i) _)]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [← Real.rpow_mul (hz i), mul_one_div]
      have hUxn : ∀ i, 0 ≤ U i (x i) := fun i => (hU i).2.2 _ (hxbox i)
      have hUyn : ∀ i, 0 ≤ U i (y i) := fun i => (hU i).2.2 _ (hybox i)
      have hcc0 : ∀ i, 0 ≤ ∑ j, y i j * bidPrice b j := fun i =>
        Finset.sum_nonneg (fun j _ => mul_nonneg (hy.1 i j) (hp j))
      set r : Fin n → ℝ := fun i => (I.B i + ∑ j, y i j * bidPrice b j) / I.B i with hr
      have hr0 : ∀ i, 0 ≤ r i := fun i =>
        div_nonneg (by linarith [hBpos i, hcc0 i]) (hBpos i).le
      have hvr : ∀ i, U i (y i) ≤ U i (x i) * r i := by
        intro i; rw [hr]; simp only; rw [mul_div_assoc', le_div_iff₀ (hBpos i)]; linarith [key i]
      rw [hN y hUyn, hN x hUxn]
      have hw0 : ∀ i, 0 ≤ I.B i / totalBudget I := fun i => div_nonneg (hBpos i).le hBt.le
      calc ∏ i, U i (y i) ^ (I.B i / totalBudget I)
            ≤ ∏ i, (U i (x i) * r i) ^ (I.B i / totalBudget I) :=
            Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hUyn i) _)
              (fun i _ => Real.rpow_le_rpow (hUyn i) (hvr i) (hw0 i))
        _ = (∏ i, U i (x i) ^ (I.B i / totalBudget I)) * ∏ i, r i ^ (I.B i / totalBudget I) := by
            rw [← Finset.prod_mul_distrib]
            exact Finset.prod_congr rfl (fun i _ => Real.mul_rpow (hUxn i) (hr0 i))
        _ ≤ (∏ i, U i (x i) ^ (I.B i / totalBudget I)) * 2 := by
            apply mul_le_mul_of_nonneg_left _
              (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hUxn i) _))
            calc ∏ i, r i ^ (I.B i / totalBudget I) ≤ ∑ i, (I.B i / totalBudget I) * r i :=
                  Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => hw0 i)
                    (by rw [← Finset.sum_div]; exact div_self hBt.ne') (fun i _ => hr0 i)
              _ = 2 := by
                  have : ∀ i, (I.B i / totalBudget I) * r i =
                      (I.B i + ∑ j, y i j * bidPrice b j) / totalBudget I := by
                    intro i; rw [hr]; field_simp [(hBpos i).ne']
                  simp_rw [this]
                  rw [← Finset.sum_div, Finset.sum_add_distrib, hsumc]
                  have : ∑ i, I.B i = totalBudget I := rfl
                  rw [this]; field_simp; ring
        _ = 2 * ∏ i, U i (x i) ^ (I.B i / totalBudget I) := mul_comm _ _
