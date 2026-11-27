-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:27.753802+00:00
-- url     : https://prove2.me/submissions/ec8fa8f5-245c-4bea-8a54-b469af72e69b

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (hI : Standing I)
    (hpc : PerfectCompetition I) :
    ((∃ b : Fin n → Fin m → ℝ, IsPNE I 0 b) ↔
        ∃ (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ), IsEpsME I 0 p x ∧ ∀ j, 0 < p j) ∧
      ((∃ (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ), IsEpsME I 0 p x ∧ ∀ j, 0 < p j) →
        ∀ b b' : Fin n → Fin m → ℝ, IsPNE I 0 b → IsPNE I 0 b' →
          ∀ i, u I i (tpAlloc 0 b i) = u I i (tpAlloc 0 b' i)) ∧
      (∀ b : Fin n → Fin m → ℝ, IsPNE I 0 b →
        Feasible I (tpAlloc 0 b) ∧
          ∀ y : Fin n → Fin m → ℝ, Feasible I y → NSW I y ≤ NSW I (tpAlloc 0 b)) := by
            classical
            have hB : ∀ i, 0 < I.B i := fun i => lt_of_lt_of_le zero_lt_one (hI.one_le_B i)
            have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hI.pos_m
            have hu_le : ∀ i y j, 0 < I.v i j → u I i y ≤ y j / I.v i j := by
              intro i y j hj
              simp only [u, dif_pos (hI.D_nonempty i)]
              exact Finset.inf'_le _ (by simpa [D] using hj)
            have hu_ge : ∀ i y t, (∀ j, 0 < I.v i j → t ≤ y j / I.v i j) → t ≤ u I i y := by
              intro i y t ht
              simp only [u, dif_pos (hI.D_nonempty i)]
              exact Finset.le_inf' _ _ (fun j hj => ht j (by simpa [D] using hj))
            have hu_gt : ∀ i y t, (∀ j, 0 < I.v i j → t < y j / I.v i j) → t < u I i y := by
              intro i y t ht
              simp only [u, dif_pos (hI.D_nonempty i)]
              exact (Finset.lt_inf'_iff _).mpr (fun j hj => ht j (by simpa [D] using hj))
            have hu_nonneg : ∀ i y, (∀ j, 0 ≤ y j) → 0 ≤ u I i y := by
              intro i y hy
              exact hu_ge i y 0 (fun j hj => div_nonneg (hy j) hj.le)
            have hu_bound : ∀ i y, (∀ j, 0 ≤ y j) → ∀ j, u I i y * I.v i j ≤ y j := by
              intro i y hy j
              rcases (hI.v_nonneg i j).eq_or_lt with hj | hj
              · simp [← hj, hy j]
              · exact (le_div_iff₀ hj).mp (hu_le i y j hj)
            have hu_scale : ∀ i t, u I i (fun j => t * I.v i j) = t := by
              intro i t
              apply le_antisymm
              · obtain ⟨j, hj⟩ := hI.D_nonempty i
                have hj : 0 < I.v i j := by simpa [D] using hj
                simpa [hj.ne'] using hu_le i (fun j => t * I.v i j) j hj
              · exact hu_ge i _ t (fun j hj => by simp [hj.ne'])
            have ha : ∀ (b : Fin n → Fin m → ℝ), (∀ i j, 0 ≤ b i j) →
                ∀ i j, tpAlloc 0 b i j = b i j / (∑ k, b k j) := by
              intro b hb i j
              have he : ∀ k, effBid 0 b k j = b k j := fun k => if_pos (hb k j)
              simp only [tpAlloc, he]
              split_ifs with h
              · rfl
              · have hz : b i j = 0 := le_antisymm (le_of_not_gt h) (hb i j)
                simp [hz]
            have ha_nonneg : ∀ b : Fin n → Fin m → ℝ, (∀ i j, 0 ≤ b i j) →
                ∀ i j, 0 ≤ tpAlloc 0 b i j := by
              intro b hb i j
              rw [ha b hb]
              exact div_nonneg (hb i j) (Finset.sum_nonneg (fun k _ => hb k j))
            have hupdate : ∀ (b : Fin n → Fin m → ℝ) i c j,
                (∑ k, Function.update b i c k j) = c j + ∑ k ∈ Finset.univ.erase i, b k j := by
              intro b i c j
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
              simp only [Function.update_self]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
            have hpos : ∀ b, IsPNE I 0 b → ∀ i, 0 < u I i (tpAlloc 0 b i) := by
              intro b hb i
              let c : Fin m → ℝ := fun _ => I.B i / m
              have hcpos : ∀ j, 0 < c j := fun _ => div_pos (hB i) hm
              have hc : Strategy I i c := by
                constructor
                · intro j
                  exact ⟨(hcpos j).le, (div_le_self (hB i).le (by exact_mod_cast hI.pos_m)).trans le_rfl⟩
                · simp only [c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  field_simp
              have hn : ∀ k j, 0 ≤ Function.update b i c k j := by
                intro k j
                by_cases hk : k = i
                · subst k; simpa using (hcpos j).le
                · simpa [Function.update_of_ne hk] using (hb.1 k).1 j |>.1
              have hp : 0 < u I i (tpAlloc 0 (Function.update b i c) i) := by
                apply hu_gt
                intro j hj
                rw [ha _ hn, Function.update_self]
                apply div_pos _ hj
                apply div_pos (hcpos j)
                exact lt_of_lt_of_le (by simpa using hcpos j)
                  (Finset.single_le_sum (fun k _ => hn k j) (Finset.mem_univ i))
              exact lt_of_lt_of_le hp (hb.2 i c hc)
            have hbpos : ∀ b, IsPNE I 0 b → ∀ i j, 0 < I.v i j → 0 < b i j := by
              intro b hb i j hv
              have h := hu_le i (tpAlloc 0 b i) j hv
              have hx : 0 < tpAlloc 0 b i j := (div_pos_iff.mp (lt_of_lt_of_le (hpos b hb i) h)).elim
                (fun h => h.1) (fun h => False.elim (not_lt_of_ge hv.le h.2))
              have hn : ∀ k j, 0 ≤ b k j := fun k j => ((hb.1 k).1 j).1
              rw [ha b hn] at hx
              exact lt_of_le_of_ne (hn i j) (Ne.symm (fun hz => by simp [hz] at hx))
            have hqpos : ∀ b, IsPNE I 0 b → ∀ i j,
                0 < ∑ k ∈ Finset.univ.erase i, b k j := by
              intro b hb i j
              obtain ⟨a, k, hak, ha, hk⟩ := hpc j
              have hn : ∀ k j, 0 ≤ b k j := fun k j => ((hb.1 k).1 j).1
              by_cases hai : a = i
              · have hki : k ≠ i := by simpa [hai] using hak.symm
                exact lt_of_lt_of_le (hbpos b hb k j hk)
                  (Finset.single_le_sum (fun k _ => hn k j) (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩))
              · exact lt_of_lt_of_le (hbpos b hb a j ha)
                  (Finset.single_le_sum (fun k _ => hn k j) (Finset.mem_erase.mpr ⟨hai, Finset.mem_univ a⟩))
            have hchar : ∀ b, IsPNE I 0 b → ∀ i j,
                tpAlloc 0 b i j = u I i (tpAlloc 0 b i) * I.v i j := by
              intro b hb i j
              let t := u I i (tpAlloc 0 b i)
              let q : Fin m → ℝ := fun j => ∑ k ∈ Finset.univ.erase i, b k j
              have ht : 0 < t := hpos b hb i
              have hq : ∀ j, 0 < q j := hqpos b hb i
              have hn : ∀ k j, 0 ≤ b k j := fun k j => ((hb.1 k).1 j).1
              have hprice : ∀ j, (∑ k, b k j) = b i j + q j := by
                intro j
                exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
              have hp : ∀ j, 0 < b i j + q j := fun j => add_pos_of_nonneg_of_pos (hn i j) (hq j)
              have hr : ∀ j, 0 ≤ t * I.v i j ∧ t * I.v i j < 1 := by
                intro j
                have hh := hu_bound i (tpAlloc 0 b i) (ha_nonneg b hn i) j
                rw [ha b hn, hprice] at hh
                have hx : b i j / (b i j + q j) < 1 := (div_lt_one (hp j)).mpr (by linarith [hq j])
                exact ⟨mul_nonneg ht.le (hI.v_nonneg i j), lt_of_le_of_lt hh hx⟩
              let c : Fin m → ℝ := fun j => (t * I.v i j) * q j / (1 - t * I.v i j)
              have hc0 : ∀ j, 0 ≤ c j := fun j =>
                div_nonneg (mul_nonneg (hr j).1 (hq j).le) (by linarith [(hr j).2])
              have hceq : ∀ j, c j * (1 - t * I.v i j) = (t * I.v i j) * q j := by
                intro j
                exact div_mul_cancel₀ _ (by linarith [(hr j).2])
              have hcle : ∀ j, c j ≤ b i j := by
                intro j
                apply (div_le_iff₀ (by linarith [(hr j).2] : 0 < 1 - t * I.v i j)).mpr
                have hh := hu_bound i (tpAlloc 0 b i) (ha_nonneg b hn i) j
                rw [ha b hn, hprice] at hh
                have hh' := (le_div_iff₀ (hp j)).mp hh
                dsimp [t] at *
                nlinarith
              have hcs : ∑ j, c j ≤ I.B i := by
                calc
                  ∑ j, c j ≤ ∑ j, b i j := Finset.sum_le_sum (fun j _ => hcle j)
                  _ = I.B i := (hb.1 i).2
              have hcse : ∑ j, c j = I.B i := by
                by_contra hne
                have hlt : ∑ j, c j < I.B i := lt_of_le_of_ne hcs hne
                let δ := (I.B i - ∑ j, c j) / m
                have hd : 0 < δ := div_pos (sub_pos.mpr hlt) hm
                let d : Fin m → ℝ := fun j => c j + δ
                have hd0 : ∀ j, 0 ≤ d j := fun j => (add_pos_of_nonneg_of_pos (hc0 j) hd).le
                have hds : ∑ j, d j = I.B i := by
                  simp only [d, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
                    Fintype.card_fin, nsmul_eq_mul]
                  dsimp [δ]
                  field_simp
                  ring
                have hdst : Strategy I i d := by
                  refine ⟨fun j => ⟨hd0 j, ?_⟩, hds⟩
                  rw [← hds]
                  exact Finset.single_le_sum (fun k _ => hd0 k) (Finset.mem_univ j)
                have hdn : ∀ k j, 0 ≤ Function.update b i d k j := by
                  intro k j
                  by_cases hk : k = i
                  · subst k; simpa using hd0 j
                  · simpa [Function.update_of_ne hk] using hn k j
                have hg : t < u I i (tpAlloc 0 (Function.update b i d) i) := by
                  apply hu_gt
                  intro k hk
                  apply (lt_div_iff₀ hk).mpr
                  rw [ha _ hdn, Function.update_self, hupdate]
                  change t * I.v i k < d k / (d k + q k)
                  apply (lt_div_iff₀ (add_pos_of_nonneg_of_pos (hd0 k) (hq k))).mpr
                  have he := hceq k
                  have hrk := (hr k).2
                  dsimp [d]
                  nlinarith
                exact (not_lt_of_ge (hb.2 i d hdst)) hg
              have hcb : ∀ k, c k = b i k := by
                have he : ∑ k, c k = ∑ k, b i k := hcse.trans (hb.1 i).2.symm
                intro k
                exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hcle k)).mp he k (Finset.mem_univ k)
              rw [ha b hn, hprice]
              apply (div_eq_iff (hp j).ne').mpr
              have he := hceq j
              rw [hcb j] at he
              change b i j = t * I.v i j * (b i j + q j)
              nlinarith
            have hphi : ∀ p : Fin m → ℝ, (∀ j, 0 < p j) → ∀ i, 0 < phi I i p := by
              intro p hp i
              obtain ⟨j, hj⟩ := hI.D_nonempty i
              have hv : 0 < I.v i j := by simpa [D] using hj
              exact Finset.sum_pos' (fun k _ => mul_nonneg (hI.v_nonneg i k) (hp k).le)
                ⟨j, Finset.mem_univ j, mul_pos hv (hp j)⟩
            have hcost : ∀ (p : Fin m → ℝ), (∀ j, 0 ≤ p j) → ∀ i y,
                (∀ j, 0 ≤ y j) → u I i y * phi I i p ≤ ∑ j, y j * p j := by
              intro p hp i y hy
              simp only [phi, Finset.mul_sum]
              exact Finset.sum_le_sum (fun j _ => by
                simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hu_bound i y hy j) (hp j))
            have hcost_scale : ∀ (p : Fin m → ℝ) i t,
                (∑ j, (t * I.v i j) * p j) = t * phi I i p := by
              intro p i t
              simp only [phi, Finset.mul_sum, mul_assoc]
            have hopt : ∀ (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ),
                (∀ j, 0 < p j) → (∀ i j, x i j = u I i (x i) * I.v i j) →
                (∀ i, ∑ j, x i j * p j = I.B i) →
                ∀ i y, (∀ j, 0 ≤ y j) → (∑ j, p j * y j ≤ I.B i) →
                  u I i y ≤ u I i (x i) := by
              intro p x hp hx hbudget i y hy hby
              have he : u I i (x i) * phi I i p = I.B i := by
                rw [← hcost_scale]
                simpa only [← hx] using hbudget i
              apply (mul_le_mul_iff_left₀ (hphi p hp i)).mp
              calc
                u I i y * phi I i p ≤ ∑ j, y j * p j := hcost p (fun j => (hp j).le) i y hy
                _ ≤ I.B i := by simpa only [mul_comm] using hby
                _ = u I i (x i) * phi I i p := he.symm
            have hme_char : ∀ (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ),
                IsEpsME I 0 p x → (∀ j, 0 < p j) →
                (∀ i, 0 < u I i (x i)) ∧ (∀ i j, x i j = u I i (x i) * I.v i j) := by
              intro p x he hp
              have huval : ∀ i, u I i (x i) * phi I i p = I.B i := by
                intro i
                have hph := hphi p hp i
                have hupper := hcost p he.p_nonneg i (x i) (he.x_nonneg i)
                rw [he.budget i] at hupper
                have hlower := he.eps_opt i (fun j => (I.B i / phi I i p) * I.v i j)
                  (fun j => mul_nonneg (div_nonneg (hB i).le hph.le) (hI.v_nonneg i j))
                  (by
                    simp only [mul_comm (p _)]
                    rw [hcost_scale, div_mul_cancel₀ _ hph.ne'])
                rw [hu_scale] at hlower
                simp only [add_zero, mul_one] at hlower
                exact le_antisymm hupper ((div_le_iff₀ hph).mp hlower)
              constructor
              · intro i
                have heq := huval i
                have hp' := hphi p hp i
                exact (mul_pos_iff.mp (heq.symm ▸ hB i)).elim
                  (fun h => h.1) (fun h => False.elim (not_lt_of_ge hp'.le h.2))
              · intro i j
                have hle : ∀ j, (u I i (x i) * I.v i j) * p j ≤ x i j * p j :=
                  fun j => mul_le_mul_of_nonneg_right (hu_bound i (x i) (he.x_nonneg i) j) (hp j).le
                have hs : ∑ j, (u I i (x i) * I.v i j) * p j = ∑ j, x i j * p j := by
                  rw [hcost_scale, huval, he.budget]
                have hh := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hs j (Finset.mem_univ j)
                exact ((mul_left_inj' (hp j).ne').mp hh).symm
            have hpne_me : ∀ b, IsPNE I 0 b →
                IsEpsME I 0 (bidPrice b) (tpAlloc 0 b) ∧ ∀ j, 0 < bidPrice b j := by
              intro b hb
              have hn : ∀ i j, 0 ≤ b i j := fun i j => ((hb.1 i).1 j).1
              have hp : ∀ j, 0 < bidPrice b j := by
                intro j
                obtain ⟨i, k, hik, hi, hk⟩ := hpc j
                exact lt_of_lt_of_le (hbpos b hb i j hi)
                  (Finset.single_le_sum (fun i _ => hn i j) (Finset.mem_univ i))
              have hs : ∀ j, ∑ i, tpAlloc 0 b i j = 1 := by
                intro j
                simp only [ha b hn, ← Finset.sum_div]
                exact div_self (hp j).ne'
              have hbudget : ∀ i, ∑ j, tpAlloc 0 b i j * bidPrice b j = I.B i := by
                intro i
                calc
                  _ = ∑ j, b i j := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [ha b hn]
                    exact div_mul_cancel₀ _ (hp j).ne'
                  _ = I.B i := (hb.1 i).2
              refine ⟨⟨fun j => (hp j).le, ha_nonneg b hn, fun j => (hs j).le,
                fun j _ => hs j, hbudget, ?_⟩, hp⟩
              intro i y hy hby
              simpa using hopt (bidPrice b) (tpAlloc 0 b) hp (hchar b hb) hbudget i y hy hby
            have hme_pne : ∀ (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ),
                IsEpsME I 0 p x → (∀ j, 0 < p j) → ∃ b, IsPNE I 0 b := by
              intro p x he hp
              obtain ⟨ht, hx⟩ := hme_char p x he hp
              let b : Fin n → Fin m → ℝ := fun i j => x i j * p j
              have hn : ∀ i j, 0 ≤ b i j := fun i j => mul_nonneg (he.x_nonneg i j) (hp j).le
              have hbs : ∀ i, ∑ j, b i j = I.B i := he.budget
              have hbstr : ∀ i, Strategy I i (b i) := by
                intro i
                refine ⟨fun j => ⟨hn i j, ?_⟩, hbs i⟩
                rw [← hbs i]
                exact Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ j)
              have hbp : ∀ j, (∑ i, b i j) = p j := by
                intro j
                simp only [b, ← Finset.sum_mul, he.sold j (hp j), one_mul]
              have halloc : ∀ i j, tpAlloc 0 b i j = x i j := by
                intro i j
                rw [ha b hn, hbp]
                exact mul_div_cancel_right₀ _ (hp j).ne'
              have hbidpos : ∀ i j, 0 < I.v i j → 0 < b i j := by
                intro i j hv
                dsimp [b]
                rw [hx]
                exact mul_pos (mul_pos (ht i) hv) (hp j)
              have hq : ∀ i j, 0 < ∑ k ∈ Finset.univ.erase i, b k j := by
                intro i j
                obtain ⟨a, k, hak, ha, hk⟩ := hpc j
                by_cases hai : a = i
                · have hki : k ≠ i := by simpa [hai] using hak.symm
                  exact lt_of_lt_of_le (hbidpos k j hk)
                    (Finset.single_le_sum (fun k _ => hn k j) (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩))
                · exact lt_of_lt_of_le (hbidpos a j ha)
                    (Finset.single_le_sum (fun k _ => hn k j) (Finset.mem_erase.mpr ⟨hai, Finset.mem_univ a⟩))
              refine ⟨b, hbstr, ?_⟩
              intro i c hc
              have hxn : tpAlloc 0 b i = x i := funext (halloc i)
              rw [hxn]
              by_contra hle
              have hg : u I i (x i) < u I i (tpAlloc 0 (Function.update b i c) i) := lt_of_not_ge hle
              have hcn : ∀ k j, 0 ≤ Function.update b i c k j := by
                intro k j
                by_cases hk : k = i
                · subst k; simpa using (hc.1 j).1
                · simpa [Function.update_of_ne hk] using hn k j
              have hbidlt : ∀ j, 0 < I.v i j → b i j < c j := by
                intro j hv
                have hutil := hu_le i (tpAlloc 0 (Function.update b i c) i) j hv
                have hshare : x i j < tpAlloc 0 (Function.update b i c) i j := by
                  rw [hx]
                  exact (lt_div_iff₀ hv).mp (lt_of_lt_of_le hg hutil)
                rw [← halloc i j, ha b hn, ha _ hcn, Function.update_self, hupdate] at hshare
                have hsum : (∑ k, b k j) = b i j + ∑ k ∈ Finset.univ.erase i, b k j :=
                  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
                rw [hsum] at hshare
                have hp1 := add_pos_of_nonneg_of_pos (hn i j) (hq i j)
                have hp2 := add_pos_of_nonneg_of_pos (hc.1 j).1 (hq i j)
                have hh := (div_lt_div_iff₀ hp1 hp2).mp hshare
                nlinarith [hq i j]
              have hbidle : ∀ j, b i j ≤ c j := by
                intro j
                by_cases hv : 0 < I.v i j
                · exact (hbidlt j hv).le
                · have hz : I.v i j = 0 := le_antisymm (le_of_not_gt hv) (hI.v_nonneg i j)
                  have hbz : b i j = 0 := by simp [b, hx i j, hz]
                  rw [hbz]
                  exact (hc.1 j).1
              obtain ⟨j, hj⟩ := hI.D_nonempty i
              have hv : 0 < I.v i j := by simpa [D] using hj
              have hsumlt := Finset.sum_lt_sum (fun j _ => hbidle j)
                ⟨j, Finset.mem_univ j, hbidlt j hv⟩
              rw [hbs i, hc.2] at hsumlt
              exact (lt_irrefl _ hsumlt)
            have htotal : 0 < totalBudget I := by
              obtain ⟨i, k, hik, hi, hk⟩ := hpc ⟨0, hI.pos_m⟩
              exact Finset.sum_pos' (fun a _ => (hB a).le) ⟨i, Finset.mem_univ i, hB i⟩
            have hfeas : ∀ p x, IsEpsME I 0 p x → (∀ j, 0 < p j) → Feasible I x := by
              intro p x he hp
              exact ⟨he.x_nonneg, fun j => he.sold j (hp j)⟩
            have hsupport : ∀ p x, IsEpsME I 0 p x → (∀ j, 0 < p j) →
                ∀ y, Feasible I y →
                  ∑ i, I.B i * (u I i (y i) / u I i (x i)) ≤ totalBudget I := by
              intro p x he hp y hy
              obtain ⟨ht, hx⟩ := hme_char p x he hp
              have hbu : ∀ i, u I i (x i) * phi I i p = I.B i := by
                intro i
                rw [← hcost_scale]
                simpa only [← hx] using he.budget i
              have htp : (∑ j, p j) = totalBudget I := by
                unfold totalBudget
                simp_rw [← he.budget]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro j hj
                rw [← Finset.sum_mul, he.sold j (hp j), one_mul]
              calc
                _ = ∑ i, u I i (y i) * phi I i p := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [← hbu i]
                  field_simp [(ht i).ne']
                _ ≤ ∑ i, ∑ j, y i j * p j :=
                  Finset.sum_le_sum (fun i _ => hcost p he.p_nonneg i (y i) (hy.1 i))
                _ = ∑ j, p j := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [← Finset.sum_mul, hy.2 j, one_mul]
                _ = totalBudget I := htp
            have hmax : ∀ p x, IsEpsME I 0 p x → (∀ j, 0 < p j) →
                ∀ y, Feasible I y → NSW I y ≤ NSW I x := by
              intro p x he hp y hy
              have ht := (hme_char p x he hp).1
              have hs := hsupport p x he hp y hy
              have hny : ∀ i, 0 ≤ u I i (y i) := fun i => hu_nonneg i (y i) (hy.1 i)
              have hz : ∀ i, 0 ≤ u I i (y i) / u I i (x i) :=
                fun i => div_nonneg (hny i) (ht i).le
              have hg : (∏ i, (u I i (y i) / u I i (x i)) ^ I.B i) ^ (totalBudget I)⁻¹ ≤
                  (∑ i, I.B i * (u I i (y i) / u I i (x i))) / totalBudget I :=
                Real.geom_mean_le_arith_mean Finset.univ I.B
                  (fun i => u I i (y i) / u I i (x i))
                  (fun i _ => (hB i).le) htotal (fun i _ => hz i)
              have hg1 : (∏ i, (u I i (y i) / u I i (x i)) ^ I.B i) ^ (totalBudget I)⁻¹ ≤ 1 :=
                hg.trans ((div_le_one htotal).mpr hs)
              have hpx : 0 < ∏ i, (u I i (x i)) ^ I.B i :=
                Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (ht i) _)
              have hpy : 0 ≤ ∏ i, (u I i (y i)) ^ I.B i :=
                Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hny i) _)
              have hrat : (∏ i, (u I i (y i) / u I i (x i)) ^ I.B i) ^ (totalBudget I)⁻¹ =
                  NSW I y / NSW I x := by
                simp_rw [Real.div_rpow (hny _) (ht _).le, Finset.prod_div_distrib]
                rw [Real.div_rpow hpy hpx.le]
                simp only [NSW, one_div]
              rw [hrat] at hg1
              exact (div_le_one (Real.rpow_pos_of_pos hpx _)).mp hg1
            have hunique : ∀ p x q y, IsEpsME I 0 p x → (∀ j, 0 < p j) →
                IsEpsME I 0 q y → (∀ j, 0 < q j) → ∀ i, u I i (x i) = u I i (y i) := by
              intro p x q y he hp he' hq
              have ht := (hme_char p x he hp).1
              have ht' := (hme_char q y he' hq).1
              have hs := hsupport p x he hp y (hfeas q y he' hq)
              have hs' := hsupport q y he' hq x (hfeas p x he hp)
              let a : Fin n → ℝ := fun i => I.B i *
                (u I i (y i) / u I i (x i) + u I i (x i) / u I i (y i) - 2)
              have hae : ∀ i, a i = I.B i * ((u I i (y i) - u I i (x i)) ^ 2 /
                  (u I i (x i) * u I i (y i))) := by
                intro i
                dsimp [a]
                congr 1
                field_simp [(ht i).ne', (ht' i).ne']
                ring
              have ha0 : ∀ i, 0 ≤ a i := by
                intro i
                rw [hae]
                exact mul_nonneg (hB i).le (div_nonneg (sq_nonneg _) (mul_pos (ht i) (ht' i)).le)
              have hsa : ∑ i, a i = 0 := by
                have heq : (∑ i, a i) =
                    (∑ i, I.B i * (u I i (y i) / u I i (x i))) +
                    (∑ i, I.B i * (u I i (x i) / u I i (y i))) - 2 * totalBudget I := by
                  simp only [a, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
                    ← Finset.sum_mul, totalBudget]
                  ring
                apply le_antisymm
                · rw [heq]
                  linarith
                · exact Finset.sum_nonneg (fun i _ => ha0 i)
              intro i
              have hai := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha0 i)).mp hsa i (Finset.mem_univ i)
              rw [hae] at hai
              have hz : (u I i (y i) - u I i (x i)) ^ 2 = 0 := by
                rcases mul_eq_zero.mp hai with h | h
                · exact False.elim ((hB i).ne' h)
                · exact (div_eq_zero_iff).mp h |>.resolve_right (mul_pos (ht i) (ht' i)).ne'
              nlinarith [sq_nonneg (u I i (y i) - u I i (x i))]
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
            · rintro ⟨b, hb⟩
              exact ⟨bidPrice b, tpAlloc 0 b, hpne_me b hb⟩
            · rintro ⟨p, x, he, hp⟩
              exact hme_pne p x he hp
            · intro hex b b' hb hb' i
              obtain ⟨he, hp⟩ := hpne_me b hb
              obtain ⟨he', hp'⟩ := hpne_me b' hb'
              exact hunique _ _ _ _ he hp he' hp' i
            · intro b hb
              obtain ⟨he, hp⟩ := hpne_me b hb
              exact ⟨hfeas _ _ he hp, hmax _ _ he hp⟩
