-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_D_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:58.80987+00:00
-- url     : https://prove2.me/submissions/712fa8b8-3221-4a22-abc7-89ce9fbfdf16

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open MeasureTheory

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (hI : GenStanding I)
    (U : Fin n → (Fin m → ℝ) → ℝ) (hU : ∀ i, IsConcaveUtility (U i))
    (hns : ∀ i, StrictMonoOn (U i) (box m)) (hec : EnoughCompetition U)
    (σ : Fin n → ProbabilityMeasure (Fin m → ℝ)) (hσ : IsMixedNE I U 0 σ) :
    IsPure σ := by
      intro i
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := i.pos; omega⟩
      let F : (Fin (n'+1) → Fin m → ℝ) → ℝ := fun s => U i (tpAlloc 0 s i)
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n'+1) => Fin m → ℝ) i
      let ν : Measure (Fin n' → Fin m → ℝ) :=
        Measure.pi fun j => (σ (i.succAbove j) : Measure (Fin m → ℝ))
      let H : (Fin m → ℝ) × (Fin n' → Fin m → ℝ) → ℝ := fun p => F (e.symm p)
      have hHF : ∀ s, H (e s) = F s := fun s => by simp [H]
      have hmp : ∀ τ : Fin (n'+1) → ProbabilityMeasure (Fin m → ℝ),
          (∀ j, τ (i.succAbove j) = σ (i.succAbove j)) →
          MeasurePreserving e (joint τ) ((τ i : Measure (Fin m → ℝ)).prod ν) := by
        intro τ hτ
        have := measurePreserving_piFinSuccAbove (fun k => (τ k : Measure (Fin m → ℝ))) i
        simp only [hτ] at this
        exact this
      have hint : ∀ τ : Fin (n'+1) → ProbabilityMeasure (Fin m → ℝ),
          (∀ j, τ (i.succAbove j) = σ (i.succAbove j)) →
          (Integrable F (joint τ) ↔ Integrable H ((τ i : Measure (Fin m → ℝ)).prod ν)) := by
        intro τ hτ
        rw [← (hmp τ hτ).integrable_comp_emb e.measurableEmbedding]
        have : H ∘ e = F := funext hHF
        rw [this]
      have hexp : ∀ τ : Fin (n'+1) → ProbabilityMeasure (Fin m → ℝ),
          (∀ j, τ (i.succAbove j) = σ (i.succAbove j)) →
          expPay U 0 τ i = ∫ p, H p ∂((τ i : Measure (Fin m → ℝ)).prod ν) := by
        intro τ hτ
        rw [← (hmp τ hτ).integral_comp']
        simp only [hHF]; rfl
      have hupd : ∀ b : Fin m → ℝ, ∀ j, (Function.update σ i (pureBid b)) (i.succAbove j)
          = σ (i.succAbove j) := fun b j => Function.update_of_ne (Fin.succAbove_ne i j) _ _
      have hupdi : ∀ b : Fin m → ℝ, ((Function.update σ i (pureBid b) i : ProbabilityMeasure _) :
          Measure (Fin m → ℝ)) = Measure.dirac b := by
        intro b; rw [Function.update_self]; rfl
      let g : (Fin m → ℝ) → ℝ := fun b => ∫ y, H (b, y) ∂ν
      have hdev : ∀ b, Strategy I i b → Integrable (fun y => H (b, y)) ν ∧ g b ≤ expPay U 0 σ i := by
        intro b hb
        obtain ⟨h1, h2⟩ := hσ.2.2 i b hb
        rw [hint _ (hupd b), hupdi, Measure.dirac_prod,
          (measurableEmbedding_prodMk_left b).integrable_map_iff] at h1
        rw [hexp _ (hupd b), hupdi, Measure.dirac_prod,
          (measurableEmbedding_prodMk_left b).integral_map] at h2
        exact ⟨h1, h2⟩
      have hHint : Integrable H ((σ i : Measure (Fin m → ℝ)).prod ν) :=
        (hint σ (fun _ => rfl)).1 (hσ.2.1 i)
      have hV : expPay U 0 σ i = ∫ b, g b ∂(σ i : Measure (Fin m → ℝ)) := by
        rw [hexp σ (fun _ => rfl), integral_prod H hHint]
      have hgint : Integrable g (σ i : Measure (Fin m → ℝ)) := hHint.integral_prod_left
      -- φ lemmas
      let φ : ℝ → ℝ → ℝ := fun t S => if 0 < t then t / (t + S) else 0
      have φ01 : ∀ t S, 0 ≤ S → 0 ≤ φ t S ∧ φ t S ≤ 1 := by
        intro t S hS
        by_cases ht : 0 < t
        · simp only [φ, if_pos ht]
          exact ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩
        · simp [φ, ht]
      have φmono : ∀ t t' S, 0 ≤ S → 0 ≤ t → t ≤ t' → φ t S ≤ φ t' S := by
        intro t t' S hS ht htt
        by_cases ht0 : 0 < t
        · have ht0' : 0 < t' := by linarith
          simp only [φ, if_pos ht0, if_pos ht0']
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        · simp only [φ, if_neg ht0]; exact (φ01 t' S hS).1
      have φsmono : ∀ t t' S, 0 < S → 0 ≤ t → t < t' → φ t S < φ t' S := by
        intro t t' S hS ht htt
        have ht0' : 0 < t' := by linarith
        by_cases ht0 : 0 < t
        · simp only [φ, if_pos ht0, if_pos ht0']
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
        · simp only [φ, if_neg ht0, if_pos ht0']; positivity
      have φone : ∀ t, 0 < t → φ t 0 = 1 := by
        intro t ht; simp only [φ, if_pos ht, add_zero]; exact div_self ht.ne'
      have φconc : ∀ t t' S, 0 ≤ S → 0 ≤ t → 0 ≤ t' →
          1/2 * φ t S + 1/2 * φ t' S ≤ φ (1/2 * t + 1/2 * t') S ∧
          (0 < S → t ≠ t' → 1/2 * φ t S + 1/2 * φ t' S < φ (1/2 * t + 1/2 * t') S) := by
        intro t t' S hS ht ht'
        rcases ht.lt_or_eq with ht0 | ht0 <;> rcases ht'.lt_or_eq with ht0' | ht0'
        · have hc : 0 < 1/2 * t + 1/2 * t' := by positivity
          simp only [φ, if_pos ht0, if_pos ht0', if_pos hc]
          have hd : (1/2 * t + 1/2 * t') / (1/2 * t + 1/2 * t' + S) - (1/2 * (t / (t + S)) + 1/2 * (t' / (t' + S)))
              = S * (t - t')^2 / (2 * (t + S) * (t' + S) * (t + t' + 2 * S)) := by
            field_simp; ring
          constructor
          · have : 0 ≤ S * (t - t')^2 / (2 * (t + S) * (t' + S) * (t + t' + 2 * S)) := by positivity
            linarith
          · intro hS' hne
            have : 0 < (t - t')^2 := by have : t - t' ≠ 0 := sub_ne_zero.2 hne; positivity
            have : 0 < S * (t - t')^2 / (2 * (t + S) * (t' + S) * (t + t' + 2 * S)) := by positivity
            linarith
        · subst ht0'
          have hc : 0 < 1/2 * t + 1/2 * 0 := by linarith
          simp only [φ, if_pos ht0, if_pos hc, lt_irrefl, if_false]
          have : 1/2 * (t / (t + S)) < (1/2 * t + 1/2 * 0) / (1/2 * t + 1/2 * 0 + S) := by
            rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
          constructor
          · linarith
          · intro _ _; linarith
        · subst ht0
          have hc : 0 < 1/2 * 0 + 1/2 * t' := by linarith
          simp only [φ, if_pos ht0', if_pos hc, lt_irrefl, if_false]
          have : 1/2 * (t' / (t' + S)) < (1/2 * 0 + 1/2 * t') / (1/2 * 0 + 1/2 * t' + S) := by
            rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
          constructor
          · linarith
          · intro _ _; linarith
        · subst ht0 ht0'
          simp [φ]
      let T : (Fin n' → Fin m → ℝ) → Fin m → ℝ := fun y j => ∑ l, (if 0 ≤ y l j then y l j else 0)
      have hT0 : ∀ y j, 0 ≤ T y j := by
        intro y j; apply Finset.sum_nonneg; intro l _; split_ifs with h
        · exact h
        · exact le_rfl
      have halloc : ∀ b : Fin m → ℝ, (∀ j, 0 ≤ b j) → ∀ y,
          H (b, y) = U i (fun j => φ (b j) (T y j)) := by
        intro b hb y
        simp only [H, F]
        congr 1
        funext j
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply, tpAlloc, effBid, Fin.insertNth_apply_same]
        rw [Fin.sum_univ_succAbove _ i]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, if_pos (hb j), φ, T]
      have hbox : ∀ (b : Fin m → ℝ) (y : Fin n' → Fin m → ℝ), (∀ j, 0 ≤ b j) → (fun j => φ (b j) (T y j)) ∈ box m := by
        intro b y hb
        exact ⟨fun j => (φ01 _ _ (hT0 y j)).1, fun j => (φ01 _ _ (hT0 y j)).2⟩
      set V := expPay U 0 σ i with hVdef
      have hstrat : ∀ᵐ b ∂(σ i : Measure (Fin m → ℝ)), Strategy I i b := hσ.1 i
      have hopt : ∀ᵐ b ∂(σ i : Measure (Fin m → ℝ)), Strategy I i b ∧ g b = V := by
        have h0 : 0 ≤ᵐ[(σ i : Measure (Fin m → ℝ))] fun b => V - g b := by
          filter_upwards [hstrat] with b hb
          simp only [Pi.zero_apply]; linarith [(hdev b hb).2]
        have hzero : ∫ b, (V - g b) ∂(σ i : Measure (Fin m → ℝ)) = 0 := by
          rw [integral_sub (integrable_const _) hgint, integral_const, ← hV]; simp
        have := (integral_eq_zero_iff_of_nonneg_ae h0 ((integrable_const _).sub hgint)).1 hzero
        filter_upwards [hstrat, this] with b hb hb2
        simp only [Pi.zero_apply] at hb2
        exact ⟨hb, by linarith⟩
      have hUmono : ∀ x x' : Fin m → ℝ, x ∈ box m → x' ∈ box m → x ≤ x' → U i x ≤ U i x' :=
        fun x x' hx hx' h => (hU i).2.1 hx hx' h
      have hUsmono : ∀ x x' : Fin m → ℝ, x ∈ box m → x' ∈ box m → x ≤ x' → ∀ j, x j < x' j →
          U i x < U i x' := by
        intro x x' hx hx' h j hj
        exact hns i hx hx' (lt_of_le_of_ne h (fun heq => by rw [heq] at hj; exact lt_irrefl _ hj))
      have hUconc : ∀ x x' : Fin m → ℝ, x ∈ box m → x' ∈ box m →
          1/2 * U i x + 1/2 * U i x' ≤ U i ((1/2 : ℝ) • x + (1/2 : ℝ) • x') := by
        intro x x' hx hx'
        have := (hU i).1.2 hx hx' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        simpa [smul_eq_mul] using this
      have hstrict : ∀ (f1 f2 : (Fin n' → Fin m → ℝ) → ℝ) (j' : Fin m), Integrable f1 ν →
          Integrable f2 ν → (∀ᵐ y ∂ν, f1 y ≤ f2 y) → (∀ᵐ y ∂ν, T y j' ≠ 0 → f1 y < f2 y) →
          ¬ (∀ᵐ y ∂ν, T y j' = 0) → ∫ y, f1 y ∂ν < ∫ y, f2 y ∂ν := by
        intro f1 f2 j' h1 h2 hle hlt hne
        have h0 : 0 ≤ᵐ[ν] (f2 - f1) := by
          filter_upwards [hle] with y hy; simp only [Pi.zero_apply, Pi.sub_apply]; linarith
        have hpos : 0 < ∫ y, (f2 - f1) y ∂ν := by
          rw [integral_pos_iff_support_of_nonneg_ae h0 (h2.sub h1), pos_iff_ne_zero]
          intro hz
          apply hne
          have : ∀ᵐ y ∂ν, ¬ ((f2 - f1) y ≠ 0) := ae_iff.2 (by simpa [Function.support] using hz)
          filter_upwards [this, hlt] with y hy hy2
          by_contra hT
          have := hy2 hT
          simp only [Pi.sub_apply, ne_eq, not_not] at hy
          linarith
        simp only [Pi.sub_apply] at hpos
        rw [integral_sub h2 h1] at hpos
        linarith
      have hother : ∃ _ : Fin n', True := by
        obtain ⟨i1, k1, hik, -, -⟩ := hec ⟨0, hI.pos_m⟩
        by_cases h1 : i1 = i
        · have : k1 ≠ i := by rw [← h1]; exact hik.symm
          obtain ⟨z, -⟩ := Fin.exists_succAbove_eq this
          exact ⟨z, trivial⟩
        · obtain ⟨z, -⟩ := Fin.exists_succAbove_eq h1
          exact ⟨z, trivial⟩
      have hEx : ∃ j', ¬ (∀ᵐ y ∂ν, T y j' = 0) := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨l, -⟩ := hother
        have hall : ∀ᵐ y ∂ν, ∀ j', T y j' = 0 := ae_all_iff.2 hcon
        have hsl : ∀ᵐ y ∂ν, Strategy I (i.succAbove l) (y l) :=
          (Measure.quasiMeasurePreserving_eval
            (μ := fun j => (σ (i.succAbove j) : Measure (Fin m → ℝ))) l).ae (hσ.1 (i.succAbove l))
        have hfalse : ∀ᵐ y ∂ν, False := by
          filter_upwards [hall, hsl] with y hy hs
          have hzero : ∀ j', y l j' = 0 := by
            intro j'
            have h1 := hy j'
            simp only [T] at h1
            have hnn : ∀ l' ∈ Finset.univ, 0 ≤ (if 0 ≤ y l' j' then y l' j' else 0) := by
              intro l' _; split_ifs with h
              · exact h
              · exact le_rfl
            have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 l (Finset.mem_univ _)
            rw [if_pos (hs.1 j').1] at this; exact this
          have := hs.2
          rw [Finset.sum_eq_zero (fun j _ => hzero j)] at this
          linarith [hI.one_le_B (i.succAbove l)]
        obtain ⟨y, hy⟩ := hfalse.exists
        exact hy
      have hZ : ∀ b, Strategy I i b → g b = V → ∀ j, (∀ᵐ y ∂ν, T y j = 0) → b j = 0 := by
        intro b hb hgb j hTj
        by_contra hbj
        have hbjpos : 0 < b j := lt_of_le_of_ne (hb.1 j).1 (Ne.symm hbj)
        obtain ⟨j', hj'⟩ := hEx
        have hjj : j' ≠ j := by rintro rfl; exact hj' hTj
        let b'' : Fin m → ℝ := b + Pi.single j' (b j / 2) - Pi.single j (b j / 2)
        have hb''j : b'' j = b j / 2 := by
          simp [b'', Pi.single_apply, Ne.symm hjj]; ring
        have hb''j' : b'' j' = b j' + b j / 2 := by simp [b'', hjj]
        have hb''k : ∀ k, k ≠ j → k ≠ j' → b'' k = b k := by
          intro k h1 h2; simp [b'', h1, h2]
        have hsum2 : b j + b j' ≤ I.B i := by
          rw [← hb.2]
          have := Finset.sum_le_sum_of_subset_of_nonneg (f := b) (Finset.subset_univ {j, j'})
            (fun k _ _ => (hb.1 k).1)
          rw [Finset.sum_pair (Ne.symm hjj)] at this; exact this
        have hb''s : Strategy I i b'' := by
          refine ⟨fun k => ?_, ?_⟩
          · by_cases h1 : k = j
            · subst h1; rw [hb''j]; constructor <;> linarith [(hb.1 k).2]
            · by_cases h2 : k = j'
              · subst h2; rw [hb''j']; constructor <;> linarith [(hb.1 k).1, (hb.1 j).1]
              · rw [hb''k k h1 h2]; exact hb.1 k
          · simp [b'', Finset.sum_add_distrib, Finset.sum_sub_distrib, hb.2]
        have hb''nn : ∀ k, 0 ≤ b'' k := fun k => (hb''s.1 k).1
        have hbnn : ∀ k, 0 ≤ b k := fun k => (hb.1 k).1
        have hcoord : ∀ y, T y j = 0 → ∀ k, φ (b k) (T y k) ≤ φ (b'' k) (T y k) := by
          intro y hy k
          by_cases h1 : k = j
          · subst h1; rw [hy, hb''j, φone _ hbjpos, φone _ (by linarith)]
          · by_cases h2 : k = j'
            · subst h2; rw [hb''j']; exact φmono _ _ _ (hT0 y k) (hbnn k) (by linarith)
            · rw [hb''k k h1 h2]
        have hle : g b'' ≤ V := (hdev b'' hb''s).2
        have hlt : g b < g b'' := by
          apply hstrict _ _ j' (hdev b hb).1 (hdev b'' hb''s).1
          · filter_upwards [hTj] with y hy
            rw [halloc b hbnn, halloc b'' hb''nn]
            exact hUmono _ _ (hbox b y hbnn) (hbox b'' y hb''nn) (fun k => hcoord y hy k)
          · filter_upwards [hTj] with y hy hT'
            rw [halloc b hbnn, halloc b'' hb''nn]
            apply hUsmono _ _ (hbox b y hbnn) (hbox b'' y hb''nn) (fun k => hcoord y hy k) j'
            show φ (b j') (T y j') < φ (b'' j') (T y j')
            rw [hb''j']
            exact φsmono _ _ _ (lt_of_le_of_ne (hT0 y j') (Ne.symm hT')) (hbnn j') (by linarith)
          · exact hj'
        linarith
      have key : ∀ b b', Strategy I i b → g b = V → Strategy I i b' → g b' = V → b = b' := by
        intro b b' hb hgb hb' hgb'
        by_contra hne
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
        by_cases hTj : ∀ᵐ y ∂ν, T y j = 0
        · exact hj ((hZ b hb hgb j hTj).trans (hZ b' hb' hgb' j hTj).symm)
        · let c : Fin m → ℝ := (1/2 : ℝ) • b + (1/2 : ℝ) • b'
          have hcj : ∀ k, c k = 1/2 * b k + 1/2 * b' k := fun k => by simp [c]
          have hbnn : ∀ k, 0 ≤ b k := fun k => (hb.1 k).1
          have hb'nn : ∀ k, 0 ≤ b' k := fun k => (hb'.1 k).1
          have hcs : Strategy I i c := by
            refine ⟨fun k => ?_, ?_⟩
            · rw [hcj]; constructor <;> linarith [(hb.1 k).1, (hb'.1 k).1, (hb.1 k).2, (hb'.1 k).2]
            · simp only [hcj]
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hb.2, hb'.2]; ring
          have hcnn : ∀ k, 0 ≤ c k := fun k => (hcs.1 k).1
          have hpt : ∀ y, 1/2 * H (b, y) + 1/2 * H (b', y) ≤ H (c, y) ∧
              (T y j ≠ 0 → 1/2 * H (b, y) + 1/2 * H (b', y) < H (c, y)) := by
            intro y
            rw [halloc b hbnn, halloc b' hb'nn, halloc c hcnn]
            have hm : (1/2:ℝ) • (fun k => φ (b k) (T y k)) + (1/2:ℝ) • (fun k => φ (b' k) (T y k))
                ∈ box m := (hU i).1.1 (hbox b y hbnn) (hbox b' y hb'nn) (by norm_num) (by norm_num)
                  (by norm_num)
            have hcmp : (1/2:ℝ) • (fun k => φ (b k) (T y k)) + (1/2:ℝ) • (fun k => φ (b' k) (T y k))
                ≤ (fun k => φ (c k) (T y k)) := by
              intro k
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rw [hcj]; exact (φconc _ _ _ (hT0 y k) (hbnn k) (hb'nn k)).1
            have h1 := hUconc _ _ (hbox b y hbnn) (hbox b' y hb'nn)
            refine ⟨h1.trans (hUmono _ _ hm (hbox c y hcnn) hcmp),
              fun hT => h1.trans_lt (hUsmono _ _ hm (hbox c y hcnn) hcmp j ?_)⟩
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [hcj]
            exact (φconc _ _ _ (hT0 y j) (hbnn j) (hb'nn j)).2
              (lt_of_le_of_ne (hT0 y j) (Ne.symm hT)) hj
          have hle : g c ≤ V := (hdev c hcs).2
          have hlt : ∫ y, (1/2 * H (b, y) + 1/2 * H (b', y)) ∂ν < g c := by
            apply hstrict _ _ j (((hdev b hb).1.const_mul _).add ((hdev b' hb').1.const_mul _))
              (hdev c hcs).1
            · exact Filter.Eventually.of_forall (fun y => (hpt y).1)
            · exact Filter.Eventually.of_forall (fun y => (hpt y).2)
            · exact hTj
          have : ∫ y, (1/2 * H (b, y) + 1/2 * H (b', y)) ∂ν = 1/2 * g b + 1/2 * g b' := by
            rw [integral_add ((hdev b hb).1.const_mul _) ((hdev b' hb').1.const_mul _),
              integral_const_mul, integral_const_mul]
          linarith
      obtain ⟨b0, hb0⟩ := hopt.exists
      refine ⟨b0, ?_⟩
      have hae : ∀ᵐ b ∂(σ i : Measure (Fin m → ℝ)), b = b0 := by
        filter_upwards [hopt] with b hb; exact key _ _ hb.1 hb.2 hb0.1 hb0.2
      apply Subtype.ext
      show (σ i : Measure (Fin m → ℝ)) = Measure.dirac b0
      ext s hs
      rw [Measure.dirac_apply' _ hs]
      have hnull : (σ i : Measure (Fin m → ℝ)) {b | ¬ b = b0} = 0 := ae_iff.1 hae
      by_cases hb : b0 ∈ s
      · rw [Set.indicator_of_mem hb]
        have : (σ i : Measure (Fin m → ℝ)) sᶜ = 0 :=
          measure_mono_null (fun x hx => by rintro rfl; exact hx hb) hnull
        rw [prob_compl_eq_zero_iff hs] at this; simpa using this
      · rw [Set.indicator_of_notMem hb]
        exact measure_mono_null (fun x hx => by rintro rfl; exact hb hx) hnull
