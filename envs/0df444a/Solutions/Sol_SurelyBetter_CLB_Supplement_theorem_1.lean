-- Prove2me | solution 1 for SurelyBetter.CLB.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:42.905708+00:00
-- url     : https://prove2.me/submissions/12139a45-fb19-4b93-8f5d-a31a02e85080

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Definitions.Def_SurelyBetter_CLB_Supplement_SalesAgent

open SurelyBetter
open SurelyBetter.CLB
open SurelyBetter.CLB.Supplement

open SurelyBetter.CLB Supermodularity.Lattices
theorem solution (U : Set ℝ) (hU : Convex ℝ U) (V : (Fin 4 → ℝ) → ℝ) (hV : IsMBA U V)
    (u : ℝ → ℝ) (hu_mono : StrictMonoOn u (Set.Ici 0)) (hu0 : u 0 = 0)
    (hu_range : u '' Set.Ici 0 = U ∩ Set.Ici 0)
    (hq : ∀ w₁ : ℝ, 0 ≤ w₁ → ∀ w₂ : ℝ, 0 ≤ w₂ → (qStar V u w₁ w₂).Nonempty) :
    MOMOn V (salesActs U) ↔
      ((∀ w₂ : ℝ, 0 ≤ w₂ → ∀ w₁ w₁' : ℝ, 0 ≤ w₁ → w₁ ≤ w₁' →
          InducedSetOrder (qStar V u w₁ w₂) (qStar V u w₁' w₂)) ∧
        (∀ w₁ : ℝ, 0 ≤ w₁ → ∀ w₂ w₂' : ℝ, 0 ≤ w₂ → w₂ ≤ w₂' →
          InducedSetOrder (qStar V u w₁ w₂') (qStar V u w₁ w₂))) := by
            have h0U : (0:ℝ) ∈ U := by
              have h : u 0 ∈ u '' Set.Ici 0 := ⟨0, by simp, rfl⟩
              rw [hu_range, hu0] at h
              exact h.1
            have hUle : ∀ t y : ℝ, 0 ≤ t → t ≤ y → y ∈ U → t ∈ U := by
              intro t y ht hty hy
              exact hU.ordConnected.out h0U hy ⟨ht, hty⟩
            -- u maps nonnegative payments to nonnegative elements of U
            have huU : ∀ w : ℝ, 0 ≤ w → u w ∈ U ∧ 0 ≤ u w := by
              intro w hw
              have h : u w ∈ u '' Set.Ici 0 := ⟨w, hw, rfl⟩
              rw [hu_range] at h
              exact h
            have huS : ∀ a ∈ U, 0 ≤ a → ∃ w : ℝ, 0 ≤ w ∧ u w = a := by
              intro a ha ha0
              have h : a ∈ U ∩ Set.Ici 0 := ⟨ha, ha0⟩
              rw [← hu_range] at h
              obtain ⟨w, hw, h⟩ := h
              exact ⟨w, hw, h⟩
            have hule : ∀ w w' : ℝ, 0 ≤ w → 0 ≤ w' → (u w ≤ u w' ↔ w ≤ w') := by
              intro w w' hw hw'
              exact hu_mono.le_iff_le hw hw'
            -- flip
            have hmixflip : ∀ (α : ℝ) (f g : Fin 4 → ℝ), mix (1 - α) f g = mix α g f := by
              intro α f g
              unfold mix
              rw [sub_sub_cancel, add_comm]
            have hflip : ∀ (f g : Fin 4 → ℝ) (α : ℝ), α ∈ optMix V f g → 1 - α ∈ optMix V g f := by
              intro f g α h
              obtain ⟨⟨h1, h2⟩, h3⟩ := h
              refine ⟨⟨by linarith, by linarith⟩, ?_⟩
              intro β hβ
              rw [hmixflip, ← hmixflip β]
              exact h3 (1 - β) ⟨by linarith [hβ.2], by linarith [hβ.1]⟩
            have hflipISO : ∀ f f' g : Fin 4 → ℝ,
                InducedSetOrder (optMix V f g) (optMix V f' g) →
                InducedSetOrder (optMix V g f') (optMix V g f) := by
              intro f f' g h a ha b hb
              have h1 := h (hflip _ _ _ hb) (hflip _ _ _ ha)
              obtain ⟨h2, h3⟩ := h1
              have h4 := hflip _ _ _ h2
              have h5 := hflip _ _ _ h3
              rcases le_total a b with hab | hab
              · rw [inf_eq_left.mpr hab, sup_eq_right.mpr hab]
                exact ⟨ha, hb⟩
              · rw [inf_eq_right.mpr hab, sup_eq_left.mpr hab]
                rw [inf_eq_right.mpr (by linarith), sub_sub_cancel] at h4
                rw [sup_eq_left.mpr (by linarith), sub_sub_cancel] at h5
                exact ⟨h5, h4⟩
            have hflipISO' : ∀ f f' g : Fin 4 → ℝ,
                InducedSetOrder (optMix V g f') (optMix V g f) →
                InducedSetOrder (optMix V f g) (optMix V f' g) := by
              intro f f' g h a ha b hb
              have h1 := h (hflip _ _ _ hb) (hflip _ _ _ ha)
              obtain ⟨h2, h3⟩ := h1
              have h4 := hflip _ _ _ h2
              have h5 := hflip _ _ _ h3
              rcases le_total a b with hab | hab
              · rw [inf_eq_left.mpr hab, sup_eq_right.mpr hab]
                exact ⟨ha, hb⟩
              · rw [inf_eq_right.mpr hab, sup_eq_left.mpr hab]
                rw [inf_eq_right.mpr (by linarith), sub_sub_cancel] at h4
                rw [sup_eq_left.mpr (by linarith), sub_sub_cancel] at h5
                exact ⟨h5, h4⟩
            -- the collinear case
            have hline : ∀ d : Fin 4 → ℝ, (∀ s, d s = 0 ∨ d s = 1) →
                (∀ a ∈ U, ∀ a' ∈ U, 0 ≤ a → a ≤ a' →
                  InducedSetOrder (optMix V (a • d) ((0:ℝ) • d)) (optMix V (a' • d) ((0:ℝ) • d))) →
                ∀ a ∈ U, ∀ a' ∈ U, ∀ c ∈ U, 0 ≤ a → a ≤ a' → 0 ≤ c →
                  InducedSetOrder (optMix V (a • d) (c • d)) (optMix V (a' • d) (c • d)) := by
              intro d hd H0
              have hP : ∀ t ∈ U, t • d ∈ Profiles U := by
                intro t ht s
                rcases hd s with h | h
                · simp [h, h0U]
                · simp [h, ht]
              have hm : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → V (x • d) ≤ V (y • d) := by
                intro x hx y hy hxy
                refine hV.monotone _ (hP x hx) _ (hP y hy) ?_
                intro s
                rcases hd s with h | h
                · simp [h]
                · simp [h, hxy]
              have hmix : ∀ α a c : ℝ, mix α (a • d) (c • d) = (α * a + (1 - α) * c) • d := by
                intro α a c
                unfold mix
                rw [smul_smul, smul_smul, ← add_smul]
              have hcv : ∀ α ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ U, ∀ c ∈ U, α * a + (1 - α) * c ∈ U := by
                intro α hα a ha c hc
                exact hU ha hc hα.1 (by linarith [hα.2]) (by ring)
              have hone : ∀ a ∈ U, 0 ≤ a → (1:ℝ) ∈ optMix V (a • d) ((0:ℝ) • d) := by
                intro a ha ha0
                refine ⟨⟨by norm_num, le_refl _⟩, ?_⟩
                intro β hβ
                rw [hmix, hmix]
                refine hm _ (hcv β hβ a ha 0 h0U) _ (hcv 1 ⟨by norm_num, le_refl _⟩ a ha 0 h0U) ?_
                nlinarith [hβ.2]
              -- flatness anywhere forces flatness down to 0
              have hflat : ∀ x y : ℝ, 0 ≤ x → x < y → y ∈ U → V (y • d) ≤ V (x • d) →
                  V (y • d) ≤ V ((0:ℝ) • d) := by
                intro x y hx hxy hy hVxy
                have hy0 : 0 < y := lt_of_le_of_lt hx hxy
                have hβ0 : 0 ≤ x / y := div_nonneg hx hy0.le
                have hβ1 : x / y < 1 := (div_lt_one hy0).mpr hxy
                have hβy : x / y * y = x := div_mul_cancel₀ x hy0.ne'
                have hβmem : x / y ∈ optMix V (y • d) ((0:ℝ) • d) := by
                  refine ⟨⟨hβ0, hβ1.le⟩, ?_⟩
                  intro γ hγ
                  rw [hmix, hmix, hβy]
                  refine le_trans (hm _ (hcv γ hγ y hy 0 h0U) y hy ?_) (le_trans hVxy (le_of_eq ?_))
                  · nlinarith [hγ.2]
                  · simp
                have hstep : ∀ a : ℝ, 0 ≤ a → a ≤ y → V (a • d) ≤ V ((x / y * a) • d) := by
                  intro a ha hay
                  have haU := hUle a y ha hay hy
                  have h1 := (H0 a haU y hy ha hay (hone a haU ha) hβmem).1
                  rw [inf_eq_right.mpr hβ1.le] at h1
                  have h2 := h1.2 1 ⟨by norm_num, le_refl _⟩
                  rw [hmix, hmix] at h2
                  simpa using h2
                have hpow : ∀ n : ℕ, 0 ≤ (x / y) ^ n * y ∧ (x / y) ^ n * y ≤ y := by
                  intro n
                  refine ⟨mul_nonneg (pow_nonneg hβ0 n) hy0.le, ?_⟩
                  have := pow_le_one₀ (n := n) hβ0 hβ1.le
                  nlinarith
                have hiter : ∀ n : ℕ, V (y • d) ≤ V (((x / y) ^ n * y) • d) := by
                  intro n
                  induction n with
                  | zero => simp
                  | succ n ih =>
                    refine le_trans ih (le_trans (hstep _ (hpow n).1 (hpow n).2) (le_of_eq ?_))
                    congr 2
                    ring
                have hlim : Filter.Tendsto (fun n : ℕ => ((x / y) ^ n * y) • d) Filter.atTop
                    (nhds ((0:ℝ) • d)) := by
                  have h1 : Filter.Tendsto (fun n : ℕ => (x / y) ^ n * y) Filter.atTop (nhds (0 * y)) :=
                    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const y
                  rw [zero_mul] at h1
                  exact h1.smul_const d
                have hlim2 : Filter.Tendsto (fun n : ℕ => ((x / y) ^ n * y) • d) Filter.atTop
                    (nhdsWithin ((0:ℝ) • d) (Profiles U)) := by
                  refine tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall ?_⟩
                  intro n
                  exact hP _ (hUle _ y (hpow n).1 (hpow n).2 hy)
                have hlim3 := (hV.continuous _ (hP 0 h0U)).tendsto.comp hlim2
                exact ge_of_tendsto hlim3 (Filter.Eventually.of_forall hiter)
              intro a ha a' ha' c hc ha0 haa' hc0 α hα β hβ
              rcases le_or_gt α β with hab | hab
              · rw [inf_eq_left.mpr hab, sup_eq_right.mpr hab]
                exact ⟨hα, hβ⟩
              rw [inf_eq_right.mpr hab.le, sup_eq_left.mpr hab.le]
              obtain ⟨hα1, hα2⟩ := hα
              obtain ⟨hβ1, hβ2⟩ := hβ
              have hIcc0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
              have hIcc1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, le_refl _⟩
              have hαpos : 0 < α := lt_of_le_of_lt hβ1.1 hab
              have hβlt : β < 1 := lt_of_lt_of_le hab hα1.2
              -- if everything below y is flat, every weight is optimal
              have hall : ∀ y ∈ U, V (y • d) ≤ V ((0:ℝ) • d) → ∀ p ∈ U, ∀ q ∈ U, 0 ≤ p → 0 ≤ q → p ≤ y →
                  q ≤ y → ∀ γ ∈ Set.Icc (0:ℝ) 1, γ ∈ optMix V (p • d) (q • d) := by
                intro y hy hy0 p hp q hq hp0 hq0 hpy hqy γ hγ
                refine ⟨hγ, ?_⟩
                intro δ hδ
                rw [hmix, hmix]
                refine le_trans (hm _ (hcv δ hδ p hp q hq) y hy ?_) (le_trans hy0
                  (hm 0 h0U _ (hcv γ hγ p hp q hq) ?_))
                · nlinarith [mul_le_mul_of_nonneg_left hpy hδ.1,
                    mul_le_mul_of_nonneg_left hqy (sub_nonneg.mpr hδ.2)]
                · exact add_nonneg (mul_nonneg hγ.1 hp0) (mul_nonneg (sub_nonneg.mpr hγ.2) hq0)
              have hup : c ≤ a' → α ∈ optMix V (a' • d) (c • d) := by
                intro hca
                refine ⟨hα1, ?_⟩
                intro γ hγ
                refine le_trans (hβ2 γ hγ) ?_
                rw [hmix, hmix]
                refine hm _ (hcv β hβ1 a' ha' c hc) _ (hcv α hα1 a' ha' c hc) ?_
                nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hca)]
              rcases lt_or_ge a c with hac | hac
              · have h1 := hα2 0 hIcc0
                rw [hmix, hmix] at h1
                have h2 : V (c • d) ≤ V ((0:ℝ) • d) := by
                  refine hflat (α * a + (1 - α) * c) c ?_ ?_ hc ?_
                  · exact add_nonneg (mul_nonneg hα1.1 ha0) (mul_nonneg (sub_nonneg.mpr hα1.2) hc0)
                  · nlinarith [mul_pos hαpos (sub_pos.mpr hac)]
                  · simpa using h1
                refine ⟨hall c hc h2 a ha c hc ha0 hc0 hac.le le_rfl β hβ1, ?_⟩
                rcases le_total c a' with hca | hca
                · exact hup hca
                · exact hall c hc h2 a' ha' c hc (ha0.trans haa') hc0 hca le_rfl α hα1
              · refine ⟨?_, hup (hac.trans haa')⟩
                rcases lt_or_ge c a' with hca | hca
                · have h1 := hβ2 1 hIcc1
                  rw [hmix, hmix] at h1
                  have h2 : V (a' • d) ≤ V ((0:ℝ) • d) := by
                    refine hflat (β * a' + (1 - β) * c) a' ?_ ?_ ha' ?_
                    · exact add_nonneg (mul_nonneg hβ1.1 (ha0.trans haa'))
                        (mul_nonneg (sub_nonneg.mpr hβ1.2) hc0)
                    · nlinarith [mul_pos (sub_pos.mpr hβlt) (sub_pos.mpr hca)]
                    · simpa using h1
                  exact hall a' ha' h2 a ha c hc ha0 hc0 haa' hca.le β hβ1
                · have hac' : a = c := le_antisymm (haa'.trans hca) hac
                  subst hac'
                  refine ⟨hβ1, ?_⟩
                  intro γ hγ
                  rw [hmix, hmix]
                  refine le_of_eq ?_
                  congr 2
                  ring
            -- the two directions
            have hs1 : ∀ w, sale1Prof u w = (u w) • (![1, 0, 1, 0] : Fin 4 → ℝ) := by
              intro w
              ext s
              fin_cases s <;> simp [sale1Prof, hu0]
            have hs2 : ∀ w, sale2Prof u w = (u w) • (![0, 1, 1, 0] : Fin 4 → ℝ) := by
              intro w
              ext s
              fin_cases s <;> simp [sale2Prof, hu0]
            have hm1 : ∀ w, 0 ≤ w → sale1Prof u w ∈ salesActs U := by
              intro w hw
              have h := huU w hw
              refine ⟨?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
              · intro s
                fin_cases s <;> simp [sale1Prof, hu0, h.1, h0U]
              · intro s
                fin_cases s <;> simp [sale1Prof, hu0, h.2]
              all_goals simp [sale1Prof, hu0]
            have hm2 : ∀ w, 0 ≤ w → sale2Prof u w ∈ salesActs U := by
              intro w hw
              have h := huU w hw
              refine ⟨?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
              · intro s
                fin_cases s <;> simp [sale2Prof, hu0, h.1, h0U]
              · intro s
                fin_cases s <;> simp [sale2Prof, hu0, h.2]
              all_goals simp [sale2Prof, hu0]
            have hd1 : ∀ s, (![1, 0, 1, 0] : Fin 4 → ℝ) s = 0 ∨ (![1, 0, 1, 0] : Fin 4 → ℝ) s = 1 := by
              intro s
              fin_cases s <;> simp
            have hd2 : ∀ s, (![0, 1, 1, 0] : Fin 4 → ℝ) s = 0 ∨ (![0, 1, 1, 0] : Fin 4 → ℝ) s = 1 := by
              intro s
              fin_cases s <;> simp
            constructor
            · intro hM
              refine ⟨?_, ?_⟩
              · intro w₂ hw₂ w₁ w₁' hw₁ hww
                refine hM _ (hm1 w₁ hw₁) _ (hm1 w₁' (hw₁.trans hww)) _ (hm2 w₂ hw₂) ?_
                have h := (hule w₁ w₁' hw₁ (hw₁.trans hww)).mpr hww
                intro s
                fin_cases s <;> simp [sale1Prof, h]
              · intro w₁ hw₁ w₂ w₂' hw₂ hww
                refine hflipISO _ _ _ (hM _ (hm2 w₂ hw₂) _ (hm2 w₂' (hw₂.trans hww)) _ (hm1 w₁ hw₁) ?_)
                have h := (hule w₂ w₂' hw₂ (hw₂.trans hww)).mpr hww
                intro s
                fin_cases s <;> simp [sale2Prof, h]
            · rintro ⟨hA, hB⟩
              have hA' : ∀ a ∈ U, ∀ a' ∈ U, ∀ c ∈ U, 0 ≤ a → a ≤ a' → 0 ≤ c →
                  InducedSetOrder (optMix V (a • (![1, 0, 1, 0] : Fin 4 → ℝ)) (c • (![0, 1, 1, 0])))
                    (optMix V (a' • (![1, 0, 1, 0] : Fin 4 → ℝ)) (c • (![0, 1, 1, 0]))) := by
                intro a ha a' ha' c hc ha0 haa' hc0
                obtain ⟨w, hw, rfl⟩ := huS a ha ha0
                obtain ⟨w', hw', rfl⟩ := huS a' ha' (ha0.trans haa')
                obtain ⟨z, hz, rfl⟩ := huS c hc hc0
                rw [← hs1, ← hs1, ← hs2]
                exact hA z hz w w' hw ((hule w w' hw hw').mp haa')
              have hB' : ∀ a ∈ U, ∀ a' ∈ U, ∀ c ∈ U, 0 ≤ a → a ≤ a' → 0 ≤ c →
                  InducedSetOrder (optMix V (a • (![0, 1, 1, 0] : Fin 4 → ℝ)) (c • (![1, 0, 1, 0])))
                    (optMix V (a' • (![0, 1, 1, 0] : Fin 4 → ℝ)) (c • (![1, 0, 1, 0]))) := by
                intro a ha a' ha' c hc ha0 haa' hc0
                obtain ⟨w, hw, rfl⟩ := huS a ha ha0
                obtain ⟨w', hw', rfl⟩ := huS a' ha' (ha0.trans haa')
                obtain ⟨z, hz, rfl⟩ := huS c hc hc0
                rw [← hs2, ← hs2, ← hs1]
                exact hflipISO' _ _ _ (hB z hz w w' hw ((hule w w' hw hw').mp haa'))
              have hA'' := hline (![1, 0, 1, 0]) hd1 (by
                intro a ha a' ha' ha0 haa'
                have h := hA' a ha a' ha' 0 h0U ha0 haa' le_rfl
                rw [zero_smul] at h ⊢
                exact h)
              have hB'' := hline (![0, 1, 1, 0]) hd2 (by
                intro a ha a' ha' ha0 haa'
                have h := hB' a ha a' ha' 0 h0U ha0 haa' le_rfl
                rw [zero_smul] at h ⊢
                exact h)
              have hform : ∀ f ∈ salesActs U, (∃ a ∈ U, 0 ≤ a ∧ f = a • (![1, 0, 1, 0] : Fin 4 → ℝ)) ∨
                  (∃ a ∈ U, 0 ≤ a ∧ f = a • (![0, 1, 1, 0] : Fin 4 → ℝ)) := by
                rintro f ⟨h1, h2, h3, h4⟩
                rcases h4 with ⟨h4, h5⟩ | ⟨h4, h5⟩
                · left
                  refine ⟨f 2, h1 2, h2 2, ?_⟩
                  rw [h3] at h5
                  ext s
                  fin_cases s <;> simp [h3, h4, h5]
                · right
                  refine ⟨f 2, h1 2, h2 2, ?_⟩
                  rw [h3] at h5
                  ext s
                  fin_cases s <;> simp [h3, h4, h5]
              have hpair : ∀ f ∈ salesActs U, ∀ f' ∈ salesActs U, (∀ s, f s ≤ f' s) →
                  (∃ a ∈ U, ∃ a' ∈ U, 0 ≤ a ∧ a ≤ a' ∧ f = a • (![1, 0, 1, 0] : Fin 4 → ℝ) ∧
                    f' = a' • (![1, 0, 1, 0] : Fin 4 → ℝ)) ∨
                  (∃ a ∈ U, ∃ a' ∈ U, 0 ≤ a ∧ a ≤ a' ∧ f = a • (![0, 1, 1, 0] : Fin 4 → ℝ) ∧
                    f' = a' • (![0, 1, 1, 0] : Fin 4 → ℝ)) := by
                intro f hf f' hf' hle
                rcases hform f hf with ⟨a, ha, ha0, rfl⟩ | ⟨a, ha, ha0, rfl⟩ <;>
                rcases hform f' hf' with ⟨a', ha', ha0', rfl⟩ | ⟨a', ha', ha0', rfl⟩
                · left
                  have h := hle 2
                  simp at h
                  exact ⟨a, ha, a', ha', ha0, h, rfl, rfl⟩
                · right
                  have h := hle 0
                  simp at h
                  have h' : a = 0 := le_antisymm h ha0
                  subst h'
                  exact ⟨0, ha, a', ha', le_rfl, ha0', by rw [zero_smul, zero_smul], rfl⟩
                · left
                  have h := hle 1
                  simp at h
                  have h' : a = 0 := le_antisymm h ha0
                  subst h'
                  exact ⟨0, ha, a', ha', le_rfl, ha0', by rw [zero_smul, zero_smul], rfl⟩
                · right
                  have h := hle 2
                  simp at h
                  exact ⟨a, ha, a', ha', ha0, h, rfl, rfl⟩
              intro f hf f' hf' g hg hle
              rcases hpair f hf f' hf' hle with ⟨a, ha, a', ha', ha0, haa', rfl, rfl⟩ |
                ⟨a, ha, a', ha', ha0, haa', rfl, rfl⟩ <;>
              rcases hform g hg with ⟨c, hc, hc0, rfl⟩ | ⟨c, hc, hc0, rfl⟩
              · exact hA'' a ha a' ha' c hc ha0 haa' hc0
              · exact hA' a ha a' ha' c hc ha0 haa' hc0
              · exact hB' a ha a' ha' c hc ha0 haa' hc0
              · exact hB'' a ha a' ha' c hc ha0 haa' hc0
