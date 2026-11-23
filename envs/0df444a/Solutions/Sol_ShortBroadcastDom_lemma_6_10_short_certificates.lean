-- Prove2me | solution 1 for ShortBroadcastDom.lemma_6_10_short_certificates
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:21.761096+00:00
-- url     : https://prove2.me/submissions/ef51acfe-b57d-4906-ae72-0b75aafdb0d7

import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_tauOn
import Theorems.Thm_ShortBroadcastDom_lemma_4_1_orientation

open ShortBroadcastDom

namespace Aux_6_10

lemma exists_nonzero_kernel {α β : Type} [DecidableEq α] [DecidableEq β] :
    ∀ (A : Finset α) (F : Finset β), A.card < F.card →
      ∀ M : α → β → ℝ,
        ∃ w : β → ℝ, (∀ u, u ∉ F → w u = 0) ∧ (∃ u ∈ F, w u ≠ 0) ∧
          ∀ r ∈ A, ∑ u ∈ F, M r u * w u = 0 := by
  intro A
  induction A using Finset.induction with
  | empty =>
    intro F hcard _M
    rcases Finset.card_pos.mp hcard with ⟨u0, hu0F⟩
    refine ⟨fun u => if u = u0 then 1 else 0, ?_, ⟨u0, hu0F, by simp⟩, fun _ hr => (Finset.notMem_empty _ hr).elim⟩
    intro u huF
    have hne : u ≠ u0 := fun h => huF (h ▸ hu0F)
    simp [hne]
  | @insert r0 A hr0A ih =>
    intro F hcard M
    rw [Finset.card_insert_of_notMem hr0A] at hcard
    by_cases hall0 : ∀ u ∈ F, M r0 u = 0
    · rcases ih F (by omega) M with ⟨w, hw_supp, hw_nz, hw_A⟩
      refine ⟨w, hw_supp, hw_nz, ?_⟩
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrA
      · apply Finset.sum_eq_zero
        intro u huF
        simp [hall0 u huF]
      · exact hw_A r hrA
    · have hex : ∃ p ∈ F, M r0 p ≠ 0 := by
        by_contra hnone
        apply hall0
        intro u huF
        by_contra hne
        exact hnone ⟨u, huF, hne⟩
      rcases hex with ⟨p, hpF, hMp0⟩
      let F' : Finset β := F.erase p
      have hcard' : A.card < F'.card := by
        have hF' : F'.card + 1 = F.card := Finset.card_erase_add_one hpF
        omega
      let M' : α → β → ℝ := fun r u => M r u - (M r p / M r0 p) * M r0 u
      rcases ih F' hcard' M' with ⟨w', hw'_supp, ⟨u1, hu1F', hu1_nz⟩, hw'_A⟩
      let w : β → ℝ := fun u =>
        if u = p then - (∑ x ∈ F', M r0 x * w' x) / M r0 p else w' u
      have hu1_ne_p : u1 ≠ p := (Finset.mem_erase.mp hu1F').1
      have hu1F : u1 ∈ F := (Finset.mem_erase.mp hu1F').2
      refine ⟨w, ?_, ⟨u1, hu1F, by simp [w, hu1_ne_p, hu1_nz]⟩, ?_⟩
      · intro u huF
        have hne : u ≠ p := fun h => huF (h ▸ hpF)
        have huF' : u ∉ F' := fun h => huF (Finset.mem_erase.mp h).2
        simp [w, hne, hw'_supp u huF']
      · intro r hr
        have hsplit : ∑ u ∈ F, M r u * w u =
            M r p * w p + ∑ u ∈ F', M r u * w' u := by
          rw [← Finset.add_sum_erase F (fun u => M r u * w u) hpF]
          congr 1
          apply Finset.sum_congr rfl
          intro u huF'
          have hne : u ≠ p := (Finset.mem_erase.mp huF').1
          simp [w, hne]
        rw [hsplit]
        have hwp : w p = - (∑ x ∈ F', M r0 x * w' x) / M r0 p := by simp [w]
        rw [hwp]
        rcases Finset.mem_insert.mp hr with rfl | hrA
        · field_simp
          ring
        · have hA0 := hw'_A r hrA
          have hM'_exp : ∑ u ∈ F', M' r u * w' u =
              (∑ u ∈ F', M r u * w' u) - (M r p / M r0 p) * (∑ u ∈ F', M r0 u * w' u) := by
            simp only [M', sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
          have hsum_eq : ∑ u ∈ F', M r u * w' u =
              (M r p / M r0 p) * (∑ u ∈ F', M r0 u * w' u) := by linarith
          rw [hsum_eq]
          field_simp
          ring

end Aux_6_10

theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (a : ℝ) (ha : 1 ≤ a) (hH : SubgraphDensityLE a H) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 < c v) (q : ℕ) (hq : 0 < q) :
    ∃ μ : V → ℕ, (∀ r ∈ R, q ≤ ∑ v ∈ closedNbhd H r, μ v) ∧
      ∑ v, c v * (μ v : ℝ) ≤ ((q : ℝ) + 2 * (⌈a⌉₊ : ℝ)) * tau H R c := by
  classical
  let _ := hq
  set p : ℕ := ⌈a⌉₊
  have hp : 1 ≤ p := Nat.ceil_pos.mpr (by linarith)
  have hp_pos_r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have ha_le_p : a ≤ (p : ℝ) := Nat.le_ceil a
  have hHp : SubgraphDensityLE (p : ℝ) H := by
    intro S
    calc (({e | e ∈ H.edgeSet ∧ ∀ v ∈ e, v ∈ S} : Set (Sym2 V)).ncard : ℝ)
        ≤ a * (S.card : ℝ) := hH S
      _ ≤ (p : ℝ) * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_right ha_le_p (Nat.cast_nonneg _)
  rcases lemma_4_1_orientation H p hp hHp with ⟨o, ho_adj, ho_dir, ho_out⟩
  let inSet : V → Finset V := fun r => Finset.univ.filter fun u => o u r
  let outSet : V → Finset V := fun v => Finset.univ.filter fun w => o v w
  let restSet : V → Finset V := fun r => insert r (outSet r)
  have hout_card : ∀ v : V, (outSet v).card ≤ p := by
    intro v
    have heq : ({w | o v w} : Set V) = (outSet v : Set V) := by ext w; simp [outSet]
    have h := ho_out v
    rwa [heq, Set.ncard_coe_finset] at h
  have hrest_card : ∀ r : V, (restSet r).card ≤ p + 1 := by
    intro r
    have hr_not_out : r ∉ outSet r := by
      intro hmem
      exact H.loopless.irrefl r (ho_adj r r (Finset.mem_filter.mp hmem).2)
    rw [Finset.card_insert_of_notMem hr_not_out]
    exact Nat.add_le_add_right (hout_card r) 1
  have hdisj_nbhd : ∀ r : V, Disjoint (inSet r) (restSet r) := by
    intro r
    rw [Finset.disjoint_left]
    intro u hu_in hu_rest
    have hour : o u r := (Finset.mem_filter.mp hu_in).2
    have hadj : H.Adj u r := ho_adj u r hour
    rcases Finset.mem_insert.mp hu_rest with rfl | hu_out
    · exact H.loopless.irrefl u hadj
    · have horu : o r u := (Finset.mem_filter.mp hu_out).2
      exact (ho_dir u r hadj).mp hour horu
  have hunion_nbhd : ∀ r : V, inSet r ∪ restSet r = closedNbhd H r := by
    intro r
    ext u
    simp only [inSet, restSet, outSet, closedNbhd, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (hour | rfl | horu)
      · exact Or.inr (ho_adj u r hour).symm
      · exact Or.inl rfl
      · exact Or.inr (ho_adj r u horu)
    · rintro (rfl | hadj)
      · exact Or.inr (Or.inl rfl)
      · by_cases horu : o r u
        · exact Or.inr (Or.inr horu)
        · exact Or.inl ((ho_dir u r hadj.symm).mpr horu)

  -- Iterative floating rounding
  have round_frac : ∀ (m : ℕ) (y : V → ℝ),
      (∀ v, 0 ≤ y v ∧ y v ≤ 1) →
      (Finset.univ.filter fun v => 0 < y v ∧ y v < 1).card ≤ m →
      ∃ z : V → ℕ,
        (∀ v, z v ≤ 1) ∧
        (∀ v, (y v = 0 ∨ y v = 1) → (z v : ℝ) = y v) ∧
        (∑ v, c v * (z v : ℝ) ≤ ∑ v, c v * y v) ∧
        (∀ r : V, (∑ u ∈ inSet r, y u) - (p : ℝ) < ∑ u ∈ inSet r, (z u : ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro y hy hF0
      have hF_empty : (Finset.univ.filter fun v => 0 < y v ∧ y v < 1) = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hF0)
      let z : V → ℕ := fun v => if y v = 1 then 1 else 0
      have hz_eq : ∀ v, (z v : ℝ) = y v := by
        intro v
        have hnotF : ¬ (0 < y v ∧ y v < 1) := by
          intro h
          have hmem : v ∈ Finset.univ.filter (fun v => 0 < y v ∧ y v < 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩
          rw [hF_empty] at hmem
          exact Finset.notMem_empty v hmem
        rcases eq_or_lt_of_le (hy v).1 with hy0 | hy_pos
        · simp [z, ← hy0]
        · rcases lt_or_eq_of_le (hy v).2 with hy_lt1 | hy1
          · exact False.elim (hnotF ⟨hy_pos, hy_lt1⟩)
          · simp [z, hy1]
      refine ⟨z, fun v => by by_cases h : y v = 1 <;> simp [z, h],
        fun v _ => hz_eq v, ?_, ?_⟩
      · apply le_of_eq
        apply Finset.sum_congr rfl
        intro v _
        rw [hz_eq v]
      · intro r
        have hsum_eq : ∑ u ∈ inSet r, (z u : ℝ) = ∑ u ∈ inSet r, y u :=
          Finset.sum_congr rfl (fun u _ => hz_eq u)
        rw [hsum_eq]
        linarith [hp_pos_r]
    | succ m ih =>
      intro y hy hFm
      let F : Finset V := Finset.univ.filter fun v => 0 < y v ∧ y v < 1
      by_cases hle_m : F.card ≤ m
      · exact ih y hy hle_m
      · have hF_pos : 0 < F.card := by omega
        let A : Finset V := Finset.univ.filter fun r => p < (inSet r ∩ F).card
        have hA_lt_F : A.card < F.card := by
          let B : Finset (V × V) := (F ×ˢ A).filter fun ur => o ur.1 ur.2
          have hB_lower : (p + 1) * A.card ≤ B.card := by
            have hB_eq : B.card = ∑ r ∈ A, (inSet r ∩ F).card := by
              rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro r _
              rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
              congr 1
              ext u
              simp [inSet, Finset.mem_filter, Finset.mem_inter, and_comm]
            rw [hB_eq]
            calc (p + 1) * A.card = ∑ _r ∈ A, (p + 1) := by
                  rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
              _ ≤ ∑ r ∈ A, (inSet r ∩ F).card :=
                  Finset.sum_le_sum (fun r hrA => (Finset.mem_filter.mp hrA).2)
          have hB_upper : B.card ≤ p * F.card := by
            have hB_eq : B.card = ∑ u ∈ F, (outSet u ∩ A).card := by
              rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
              apply Finset.sum_congr rfl
              intro u _
              rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
              congr 1
              ext r
              simp [outSet, Finset.mem_filter, Finset.mem_inter, and_comm]
            rw [hB_eq]
            calc ∑ u ∈ F, (outSet u ∩ A).card
                ≤ ∑ u ∈ F, p := Finset.sum_le_sum (fun u _ =>
                    (Finset.card_le_card Finset.inter_subset_left).trans (hout_card u))
              _ = p * F.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
          have hineq : (p + 1) * A.card ≤ p * F.card := hB_lower.trans hB_upper
          nlinarith
        rcases Aux_6_10.exists_nonzero_kernel A F hA_lt_F
            (fun r u => if o u r then (1 : ℝ) else 0) with ⟨w0, hw0_supp, hw0_nz, hw0_ker⟩
        let dvec : V → ℝ := if ∑ v : V, c v * w0 v ≤ 0 then w0 else fun v => - w0 v
        have hd_supp : ∀ v, v ∉ F → dvec v = 0 := by
          intro v hvF
          by_cases hsum : ∑ v : V, c v * w0 v ≤ 0 <;> simp [dvec, hsum, hw0_supp v hvF]
        have hd_nz : ∃ u ∈ F, dvec u ≠ 0 := by
          rcases hw0_nz with ⟨u, huF, hu0⟩
          refine ⟨u, huF, ?_⟩
          by_cases hsum : ∑ v : V, c v * w0 v ≤ 0 <;> simp [dvec, hsum, hu0]
        have hd_cost : ∑ v : V, c v * dvec v ≤ 0 := by
          by_cases hsum : ∑ v : V, c v * w0 v ≤ 0
          · simp [dvec, hsum]
          · simp only [dvec, hsum, ↓reduceIte, mul_neg, Finset.sum_neg_distrib]
            linarith
        have hd_ker : ∀ r ∈ A, ∑ u ∈ inSet r, dvec u = 0 := by
          intro r hrA
          have h0 : ∑ u ∈ inSet r, w0 u = 0 := by
            calc ∑ u ∈ inSet r, w0 u
                = ∑ u : V, (if o u r then (1 : ℝ) else 0) * w0 u := by
                    change ∑ u ∈ Finset.univ.filter (fun u => o u r), w0 u = _
                    rw [Finset.sum_filter]
                    apply Finset.sum_congr rfl
                    intro u _
                    by_cases hour : o u r <;> simp [hour]
              _ = ∑ u ∈ F, (if o u r then (1 : ℝ) else 0) * w0 u := by
                    rw [← Finset.sum_subset (Finset.subset_univ F)]
                    intro u _ huF
                    simp [hw0_supp u huF]
              _ = 0 := hw0_ker r hrA
          by_cases hsum : ∑ v : V, c v * w0 v ≤ 0
          · simp [dvec, hsum, h0]
          · simp [dvec, hsum, Finset.sum_neg_distrib, h0]
        let Fnz : Finset V := F.filter fun u => dvec u ≠ 0
        have hFnz_ne : Fnz.Nonempty := by
          rcases hd_nz with ⟨u, huF, hunz⟩
          exact ⟨u, Finset.mem_filter.mpr ⟨huF, hunz⟩⟩
        let stepBound : V → ℝ := fun u =>
          if 0 < dvec u then (1 - y u) / dvec u else - y u / dvec u
        have hstep_pos : ∀ u ∈ Fnz, 0 < stepBound u := by
          intro u huFnz
          rcases Finset.mem_filter.mp huFnz with ⟨huF, hunz⟩
          rcases (Finset.mem_filter.mp huF).2 with ⟨hyu0, hyu1⟩
          by_cases hpos : 0 < dvec u
          · simp only [stepBound, hpos, ↓reduceIte]
            exact div_pos (by linarith) hpos
          · simp only [stepBound, hpos, ↓reduceIte]
            have hneg : dvec u < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hunz
            exact div_pos_of_neg_of_neg (by linarith) hneg
        let t : ℝ := Fnz.inf' hFnz_ne stepBound
        have ht_pos : 0 < t := (Finset.lt_inf'_iff hFnz_ne).mpr hstep_pos
        rcases Finset.exists_mem_eq_inf' hFnz_ne stepBound with ⟨u0, hu0Fnz, ht_eq⟩
        let y' : V → ℝ := fun v => y v + t * dvec v
        have hy'_bounds : ∀ v, 0 ≤ y' v ∧ y' v ≤ 1 := by
          intro v
          by_cases hvF : v ∈ F
          · by_cases hvnz : dvec v = 0
            · simp [y', hvnz, (hy v).1, (hy v).2]
            · have hvFnz : v ∈ Fnz := Finset.mem_filter.mpr ⟨hvF, hvnz⟩
              have ht_le : t ≤ stepBound v := Finset.inf'_le stepBound hvFnz
              rcases (Finset.mem_filter.mp hvF).2 with ⟨hyv0, hyv1⟩
              by_cases hpos : 0 < dvec v
              · simp only [stepBound, hpos, ↓reduceIte] at ht_le
                have hmul : t * dvec v ≤ 1 - y v := (le_div_iff₀ hpos).mp ht_le
                have hmul_pos : 0 < t * dvec v := mul_pos ht_pos hpos
                dsimp [y']
                exact ⟨by linarith, by linarith⟩
              · simp only [stepBound, hpos, ↓reduceIte] at ht_le
                have hneg : dvec v < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hvnz
                have hpos_neg : 0 < - dvec v := by linarith
                have ht_le' : t ≤ y v / (- dvec v) := by
                  have heq : - y v / dvec v = y v / (- dvec v) := by ring
                  linarith
                have hmul : t * (- dvec v) ≤ y v := (le_div_iff₀ hpos_neg).mp ht_le'
                have hmul_neg : t * dvec v < 0 := mul_neg_of_pos_of_neg ht_pos hneg
                dsimp [y']
                exact ⟨by linarith, by linarith⟩
          · simp [y', hd_supp v hvF, (hy v).1, (hy v).2]
        let F' : Finset V := Finset.univ.filter fun v => 0 < y' v ∧ y' v < 1
        have hF'_sub : F' ⊆ F.erase u0 := by
          intro v hvF'
          rcases (Finset.mem_filter.mp hvF').2 with ⟨hy'0, hy'1⟩
          have hvF : v ∈ F := by
            by_contra hvNotF
            have heq : y' v = y v := by simp [y', hd_supp v hvNotF]
            rw [heq] at hy'0 hy'1
            exact hvNotF (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hy'0, hy'1⟩)
          have hv_ne_u0 : v ≠ u0 := by
            rintro rfl
            rcases Finset.mem_filter.mp hu0Fnz with ⟨_, hu0nz⟩
            by_cases hpos : 0 < dvec v
            · have ht_val : t = (1 - y v) / dvec v := by simpa [stepBound, hpos] using ht_eq
              have hy'v : y' v = 1 := by
                dsimp [y']
                rw [ht_val]
                field_simp
                ring
              linarith
            · have hneg : dvec v < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hu0nz
              have hne0 : dvec v ≠ 0 := ne_of_lt hneg
              have ht_val : t = - y v / dvec v := by simpa [stepBound, hpos] using ht_eq
              have hy'v : y' v = 0 := by
                dsimp [y']
                rw [ht_val]
                field_simp
                ring
              linarith
          exact Finset.mem_erase.mpr ⟨hv_ne_u0, hvF⟩
        have hF'_card : F'.card ≤ m := by
          have hFm' : F.card ≤ m + 1 := hFm
          have hu0F : u0 ∈ F := (Finset.mem_filter.mp hu0Fnz).1
          have herase : (F.erase u0).card + 1 = F.card := Finset.card_erase_add_one hu0F
          have hle : F'.card ≤ (F.erase u0).card := Finset.card_le_card hF'_sub
          omega
        rcases ih y' hy'_bounds hF'_card with ⟨z, hz01, hz_fix, hz_cost, hz_in⟩
        refine ⟨z, hz01, ?_, ?_, ?_⟩
        · intro v hv01
          have hvNotF : v ∉ F := by
            intro hvF
            rcases (Finset.mem_filter.mp hvF).2 with ⟨h0, h1⟩
            rcases hv01 with rfl_eq | rfl_eq <;> linarith
          have hy'_eq : y' v = y v := by simp [y', hd_supp v hvNotF]
          have hv01' : y' v = 0 ∨ y' v = 1 := hy'_eq ▸ hv01
          rw [hz_fix v hv01', hy'_eq]
        · have hy'_cost : ∑ v : V, c v * y' v =
              (∑ v : V, c v * y v) + t * (∑ v : V, c v * dvec v) := by
            simp only [y', mul_add, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro v _
            ring
          have htd_nonpos : t * (∑ v : V, c v * dvec v) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht_pos) hd_cost
          linarith [hz_cost, hy'_cost, htd_nonpos]
        · intro r
          by_cases hrA : r ∈ A
          · have hin_eq : ∑ u ∈ inSet r, y' u = ∑ u ∈ inSet r, y u := by
              simp only [y', Finset.sum_add_distrib, ← Finset.mul_sum, hd_ker r hrA, mul_zero, add_zero]
            linarith [hz_in r, hin_eq]
          · have hcard_le_p : (inSet r ∩ F).card ≤ p := by
              by_contra hgt
              exact hrA (Finset.mem_filter.mpr ⟨Finset.mem_univ r, lt_of_not_ge hgt⟩)
            have hpart : (inSet r \ F) ∪ (inSet r ∩ F) = inSet r :=
              Finset.sdiff_union_inter (inSet r) F
            have hdisj : Disjoint (inSet r \ F) (inSet r ∩ F) :=
              Finset.disjoint_sdiff_inter (inSet r) F
            have hfix_sum : ∑ u ∈ inSet r \ F, y u = ∑ u ∈ inSet r \ F, (z u : ℝ) := by
              apply Finset.sum_congr rfl
              intro u hu
              have huNotF : u ∉ F := (Finset.mem_sdiff.mp hu).2
              have hu01 : y u = 0 ∨ y u = 1 := by
                rcases eq_or_lt_of_le (hy u).1 with h0 | hpos
                · exact Or.inl h0.symm
                · rcases lt_or_eq_of_le (hy u).2 with hlt1 | h1
                  · exact False.elim (huNotF (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hpos, hlt1⟩))
                  · exact Or.inr h1
              have hy'_eq : y' u = y u := by simp [y', hd_supp u huNotF]
              have hu01' : y' u = 0 ∨ y' u = 1 := hy'_eq.symm ▸ hu01
              exact ((hz_fix u hu01').trans hy'_eq).symm
            have hfloat_diff : ∑ u ∈ inSet r ∩ F, (y u - (z u : ℝ)) < (p : ℝ) := by
              by_cases hne : (inSet r ∩ F).Nonempty
              · have hlt1 : ∑ u ∈ inSet r ∩ F, (y u - (z u : ℝ)) <
                    ∑ _u ∈ inSet r ∩ F, (1 : ℝ) := by
                  apply Finset.sum_lt_sum_of_nonempty hne
                  intro u hu
                  have hyu1 : y u < 1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2.2
                  have hzu0 : (0 : ℝ) ≤ (z u : ℝ) := Nat.cast_nonneg _
                  linarith
                have hones : ∑ _u ∈ inSet r ∩ F, (1 : ℝ) = ((inSet r ∩ F).card : ℝ) := by simp
                have hcard_r : ((inSet r ∩ F).card : ℝ) ≤ (p : ℝ) := by exact_mod_cast hcard_le_p
                linarith
              · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
                exact hp_pos_r
            have hdiff_total : (∑ u ∈ inSet r, y u) - (∑ u ∈ inSet r, (z u : ℝ)) =
                ∑ u ∈ inSet r ∩ F, (y u - (z u : ℝ)) := by
              have hs1 : ∑ u ∈ inSet r, y u =
                  (∑ u ∈ inSet r \ F, y u) + (∑ u ∈ inSet r ∩ F, y u) := by
                rw [← Finset.sum_union hdisj, hpart]
              have hs2 : ∑ u ∈ inSet r, (z u : ℝ) =
                  (∑ u ∈ inSet r \ F, (z u : ℝ)) + (∑ u ∈ inSet r ∩ F, (z u : ℝ)) := by
                rw [← Finset.sum_union hdisj, hpart]
              rw [hs1, hs2, hfix_sum, Finset.sum_sub_distrib]
              ring
            linarith

  -- Rounding any feasible vector x
  set h : ℝ := (q : ℝ) + 2 * (p : ℝ)
  have hh_pos : 0 < h := by positivity
  have round_feas : ∀ x : V → ℝ, (∀ v, 0 ≤ x v) →
      (∀ r ∈ R, 1 ≤ ∑ v ∈ closedNbhd H r, x v) →
      ∃ μ : V → ℕ, (∀ r ∈ R, q ≤ ∑ v ∈ closedNbhd H r, μ v) ∧
        ∑ v, c v * (μ v : ℝ) ≤ h * ∑ v, c v * x v := by
    intro x hx0 hxcov
    let kpart : V → ℕ := fun v => ⌊h * x v⌋₊
    let y : V → ℝ := fun v => h * x v - (kpart v : ℝ)
    have hy_lt1 : ∀ v, 0 ≤ y v ∧ y v < 1 := by
      intro v
      have hxv0 : 0 ≤ h * x v := mul_nonneg (le_of_lt hh_pos) (hx0 v)
      have hfl_le : (kpart v : ℝ) ≤ h * x v := Nat.floor_le hxv0
      have hlt_fl : h * x v < (kpart v : ℝ) + 1 := Nat.lt_floor_add_one (h * x v)
      dsimp [y]
      exact ⟨by linarith, by linarith⟩
    have hy_bounds : ∀ v, 0 ≤ y v ∧ y v ≤ 1 :=
      fun v => ⟨(hy_lt1 v).1, le_of_lt (hy_lt1 v).2⟩
    have hF_le : (Finset.univ.filter fun v => 0 < y v ∧ y v < 1).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    rcases round_frac (Fintype.card V) y hy_bounds hF_le with ⟨z, _hz01, _hz_fix, hz_cost, hz_in⟩
    let μ : V → ℕ := fun v => kpart v + z v
    refine ⟨μ, ?_, ?_⟩
    · intro r hrR
      have hrest_ne : (restSet r).Nonempty := ⟨r, Finset.mem_insert_self r _⟩
      have hrest_diff : ∑ u ∈ restSet r, (y u - (z u : ℝ)) < (p : ℝ) + 1 := by
        have hlt : ∑ u ∈ restSet r, (y u - (z u : ℝ)) < ∑ _u ∈ restSet r, (1 : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty hrest_ne
          intro u _
          have hyu1 : y u < 1 := (hy_lt1 u).2
          have hzu0 : (0 : ℝ) ≤ (z u : ℝ) := Nat.cast_nonneg _
          linarith
        have hones : ∑ _u ∈ restSet r, (1 : ℝ) = ((restSet r).card : ℝ) := by simp
        have hcard_r : ((restSet r).card : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hrest_card r
        linarith
      have hin_diff : ∑ u ∈ inSet r, (y u - (z u : ℝ)) < (p : ℝ) := by
        rw [Finset.sum_sub_distrib]
        linarith [hz_in r]
      have hnbhd_diff : ∑ v ∈ closedNbhd H r, (h * x v - (μ v : ℝ)) < 2 * (p : ℝ) + 1 := by
        have hterm_eq : ∀ v, h * x v - (μ v : ℝ) = y v - (z v : ℝ) := by
          intro v
          dsimp [μ, y]
          push_cast
          ring
        have hsum_eq : ∑ v ∈ closedNbhd H r, (h * x v - (μ v : ℝ)) =
            (∑ u ∈ inSet r, (y u - (z u : ℝ))) + (∑ u ∈ restSet r, (y u - (z u : ℝ))) := by
          calc ∑ v ∈ closedNbhd H r, (h * x v - (μ v : ℝ))
              = ∑ v ∈ closedNbhd H r, (y v - (z v : ℝ)) :=
                  Finset.sum_congr rfl (fun v _ => hterm_eq v)
            _ = ∑ v ∈ inSet r ∪ restSet r, (y v - (z v : ℝ)) := by
                  rw [hunion_nbhd r]
            _ = (∑ u ∈ inSet r, (y u - (z u : ℝ))) + (∑ u ∈ restSet r, (y u - (z u : ℝ))) :=
                  Finset.sum_union (hdisj_nbhd r)
        linarith
      have hcov_scaled : h ≤ ∑ v ∈ closedNbhd H r, h * x v := by
        rw [← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left (hxcov r hrR) (le_of_lt hh_pos)
        linarith
      have hsum_gt : (q : ℝ) - 1 < (∑ v ∈ closedNbhd H r, μ v : ℝ) := by
        have hcast : (∑ v ∈ closedNbhd H r, μ v : ℝ) = ∑ v ∈ closedNbhd H r, (μ v : ℝ) := by
          push_cast; rfl
        rw [Finset.sum_sub_distrib] at hnbhd_diff
        have hh_def : h = (q : ℝ) + 2 * (p : ℝ) := rfl
        linarith
      have hlt_int_r : (((q : ℤ) - 1 : ℤ) : ℝ) < (((∑ v ∈ closedNbhd H r, μ v : ℕ) : ℤ) : ℝ) := by
        push_cast
        exact hsum_gt
      have hlt_int : (q : ℤ) - 1 < ((∑ v ∈ closedNbhd H r, μ v : ℕ) : ℤ) := Int.cast_lt.mp hlt_int_r
      omega
    · calc ∑ v : V, c v * (μ v : ℝ)
          = (∑ v : V, c v * (kpart v : ℝ)) + ∑ v : V, c v * (z v : ℝ) := by
              simp only [μ, Nat.cast_add, mul_add, Finset.sum_add_distrib]
        _ ≤ (∑ v : V, c v * (kpart v : ℝ)) + ∑ v : V, c v * y v :=
              add_le_add le_rfl hz_cost
        _ = h * ∑ v : V, c v * x v := by
              rw [← Finset.sum_add_distrib, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro v _
              dsimp [y]
              ring

  -- Pass to sInf via finite pigeonhole on bounded integer multiplicities
  let S_LP : Set ℝ := {s : ℝ | ∃ x : V → ℝ, (∀ v, 0 ≤ x v) ∧
    (∀ v, v ∉ (Finset.univ : Finset V) → x v = 0) ∧
    (∀ r ∈ R, 1 ≤ ∑ v ∈ closedNbhd H r, x v) ∧ s = ∑ v, c v * x v}
  have htau_eq : tau H R c = sInf S_LP := rfl
  have hSLP_ne : S_LP.Nonempty := by
    refine ⟨∑ v : V, c v * 1, fun _ => 1, fun _ => zero_le_one,
      fun _ hv => (hv (Finset.mem_univ _)).elim, ?_, rfl⟩
    intro r _
    have hr_mem : r ∈ closedNbhd H r := by simp [closedNbhd]
    calc (1 : ℝ) = ∑ _v ∈ ({r} : Finset V), (1 : ℝ) := by simp
      _ ≤ ∑ v ∈ closedNbhd H r, (1 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr hr_mem)
            (fun _ _ _ => zero_le_one)
  have htau_nonneg : 0 ≤ tau H R c := by
    rw [htau_eq]
    apply Real.sInf_nonneg
    rintro s ⟨x, hx0, -, -, rfl⟩
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (le_of_lt (hc v)) (hx0 v))
  have hex_seq : ∀ n : ℕ, ∃ μ : V → ℕ,
      (∀ r ∈ R, q ≤ ∑ v ∈ closedNbhd H r, μ v) ∧
      ∑ v, c v * (μ v : ℝ) ≤ h * (tau H R c + 1 / ((n : ℝ) + 1)) := by
    intro n
    have hlt : sInf S_LP < tau H R c + 1 / ((n : ℝ) + 1) := by
      rw [← htau_eq]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    rcases exists_lt_of_csInf_lt hSLP_ne hlt with ⟨s, ⟨x, hx0, -, hxcov, rfl⟩, hs_lt⟩
    rcases round_feas x hx0 hxcov with ⟨μ, hμ_cov, hμ_cost⟩
    refine ⟨μ, hμ_cov, ?_⟩
    have := mul_le_mul_of_nonneg_left (le_of_lt hs_lt) (le_of_lt hh_pos)
    linarith
  choose μ_seq hμ_seq_cov hμ_seq_cost using hex_seq
  let B : V → ℕ := fun v => ⌊h * (tau H R c + 1) / c v⌋₊
  have hμ_le_B : ∀ (n : ℕ) (v : V), μ_seq n v ≤ B v := by
    intro n v
    have hterm_le : c v * (μ_seq n v : ℝ) ≤ ∑ u : V, c u * (μ_seq n u : ℝ) := by
      apply Finset.single_le_sum (fun u _ => mul_nonneg (le_of_lt (hc u)) (Nat.cast_nonneg _))
        (Finset.mem_univ v)
    have h1_le : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hcost_le : ∑ u : V, c u * (μ_seq n u : ℝ) ≤ h * (tau H R c + 1) := by
      have := mul_le_mul_of_nonneg_left (add_le_add_left h1_le (tau H R c)) (le_of_lt hh_pos)
      linarith [hμ_seq_cost n]
    have hdiv : (μ_seq n v : ℝ) ≤ h * (tau H R c + 1) / c v := by
      rw [le_div_iff₀ (hc v)]
      linarith
    exact Nat.le_floor hdiv
  let φ : ℕ → ∀ v : V, Fin (B v + 1) := fun n v => ⟨μ_seq n v, Nat.lt_succ_of_le (hμ_le_B n v)⟩
  rcases Finite.exists_infinite_fiber φ with ⟨g, hg_inf⟩
  have hg_inf_set : {n : ℕ | φ n = g}.Infinite := Set.infinite_coe_iff.mp hg_inf
  rcases hg_inf_set.nonempty with ⟨n0, hn0⟩
  let μ_final : V → ℕ := fun v => (g v).val
  have hμ_eq : ∀ n, n ∈ {n : ℕ | φ n = g} → μ_seq n = μ_final := by
    intro n hn
    funext v
    have hgv : φ n v = g v := congrFun hn v
    exact congrArg Fin.val hgv
  refine ⟨μ_final, ?_, ?_⟩
  · rw [← hμ_eq n0 hn0]
    exact hμ_seq_cov n0
  · apply le_of_forall_pos_lt_add
    intro ε hε
    rcases exists_nat_gt (h / ε) with ⟨N, hN⟩
    rcases hg_inf_set.exists_gt N with ⟨n, hn_mem, hn_gt⟩
    have hN_lt_n1 : h / ε < (n : ℝ) + 1 := by
      have hNn : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt
      linarith
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have herr_lt : h * (1 / ((n : ℝ) + 1)) < ε := by
      have h1 : h < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hN_lt_n1
      rw [mul_one_div, div_lt_iff₀ hn1_pos]
      linarith
    have hcost_n := hμ_seq_cost n
    rw [hμ_eq n hn_mem] at hcost_n
    linarith
