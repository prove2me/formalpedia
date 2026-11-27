-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:16.752158+00:00
-- url     : https://prove2.me/submissions/a2b3e950-623f-4a98-8b17-1c94b03f97b9

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) (α : ℝ) (hα : α ∈ Set.Icc 0 1) :
    optOPQ (Measure.pi (fun _ : Fin N => ν)) α ≤
      ENNReal.ofReal (3 + (1 - α) * (1 - 2 / (N : ℝ))) *
        optSP (Measure.pi (fun _ : Fin N => ν)) := by
          have hPP : ∀ (p : ℝ) (q : ℕ → ℝ) (hp : 0 ≤ p) (hq : ∀ k, 0 ≤ q k)
            (A : ℝ → Set (Fin N → ℝ)) (hA : A = fun t => {v | ∃ i j, i ≠ j ∧ t ≤ v i ∧ t ≤ v j})
            (σ : ℕ → ℝ) (hσ : σ = fun k => if k ≤ N then 1 / (k : ℝ) else 0)
            (price : ℕ → ℝ) (hprice : price = fun k => if k = 1 then p else q k)
            (fam : Fin N → ℕ → Finset (Finset (Fin N)))
            (hfam : fam = fun i k => Finset.univ.filter (fun S => i ∈ S ∧ S.card = k))
            (B : Fin N → (Fin N → ℝ) → ℕ → ℝ)
            (hB : B = fun i v k => if h : (fam i k).Nonempty then
              (fam i k).sup' h (fun S => ∑ j ∈ S.erase i, v j) else 0)
            (cc : Fin N → (Fin N → ℝ) → ℕ → ℝ)
            (hcc : cc = fun i v k => if k ≤ N then price k - B i v k / k else 0)
            (hC' : ∀ c : ℕ → ℝ, ∃ θ : ℕ → ℝ, c (N+1) = 0 → ∀ u ∈ Finset.Icc 1 (N+1), ∀ x : ℝ,
              (∀ v ∈ Finset.Icc 1 (N+1), σ v * x - c v ≤ σ u * x - c u) →
              c u ≤ ∑ t ∈ Finset.Ico u (N+1), (σ t - σ (t+1)) * θ t ∧
                ∀ t ∈ Finset.Ico u (N+1), θ t ≤ x)
            (θ : Fin N → (Fin N → ℝ) → ℕ → ℝ)
            (hθ : θ = fun i v => Classical.choose (hC' (cc i v)))
            (w : ℕ → ℝ) (hw : w = fun t => max 0 (σ t - σ (t+1))),
            ∀ v : Fin N → ℝ, ENNReal.ofReal (opqRevenue rnValue p q v) ≤
              ENNReal.ofReal (1 - 1 / (N : ℝ)) * (∫⁻ t in Set.Ioi 0, (A t).indicator 1 v) +
              ∑ i : Fin N,
                {v : Fin N → ℝ | (∀ j, j < i → v j < v i) ∧ (∀ j, i < j → v j ≤ v i)}.indicator
                  (fun v => ∑ t ∈ Finset.Icc 1 N, ENNReal.ofReal (w t) * ENNReal.ofReal (θ i v t) *
                    (Set.Ici (θ i v t)).indicator 1 (v i)) v := by
            intro p q hp hq A hA σ hσ price hprice fam hfam B hB cc hcc hC' θ hθ w hw
            intro v
            classical
            haveI : NeZero N := ⟨by omega⟩
            have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
            -- first argmax
            obtain ⟨i, hi1, hi2⟩ : ∃ i : Fin N, (∀ j, j < i → v j < v i) ∧ (∀ j, i < j → v j ≤ v i) := by
              have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
              obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' hne v
              set M := Finset.univ.sup' hne v with hM
              have hAr : (Finset.univ.filter (fun j => v j = M)).Nonempty := ⟨j0, by simp [hj0]⟩
              have hmin := Finset.min'_mem _ hAr
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmin
              refine ⟨(Finset.univ.filter (fun j => v j = M)).min' hAr, ?_, ?_⟩
              · intro j hj
                have hle : v j ≤ M := Finset.le_sup' v (Finset.mem_univ j)
                rcases hle.lt_or_eq with h | h
                · rw [hmin]; exact h
                · exfalso
                  have : (Finset.univ.filter (fun j => v j = M)).min' hAr ≤ j :=
                    Finset.min'_le _ j (by simp [h])
                  exact absurd hj (not_lt.mpr this)
              · intro j _; rw [hmin]; exact Finset.le_sup' v (Finset.mem_univ j)
            have hmax : ∀ j, v j ≤ v i := fun j => by
              rcases lt_trichotomy j i with h | h | h
              · exact (hi1 j h).le
              · rw [h]
              · exact hi2 j h
            have hFi : v ∈ {v : Fin N → ℝ | (∀ j, j < i → v j < v i) ∧ (∀ j, i < j → v j ≤ v i)} :=
              ⟨hi1, hi2⟩
            -- second-largest bound
            have hne' : (Finset.univ.erase i).Nonempty := by
              have : 1 < (Finset.univ : Finset (Fin N)).card := by simp; omega
              obtain ⟨a, -, b, -, hab⟩ := Finset.one_lt_card.mp this
              by_cases hai : a = i
              · exact ⟨b, by simp; intro h; exact hab (hai.trans h.symm)⟩
              · exact ⟨a, by simp [hai]⟩
            obtain ⟨s, hs⟩ : ∃ s, s = (Finset.univ.erase i).sup' hne' v := ⟨_, rfl⟩
            have hsj : ∀ j, j ≠ i → v j ≤ s := fun j hj =>
              hs ▸ Finset.le_sup' v (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
            have hsA : ENNReal.ofReal (max s 0) ≤ ∫⁻ t in Set.Ioi 0, (A t).indicator 1 v := by
              rcases le_or_gt s 0 with hs0 | hs0
              · rw [max_eq_right hs0]; simp
              obtain ⟨j0, hj0, hj0s⟩ := Finset.exists_mem_eq_sup' hne' v
              have hj0i : j0 ≠ i := Finset.ne_of_mem_erase hj0
              have hsv : s = v j0 := hs.trans hj0s
              rw [max_eq_left hs0.le]
              calc ENNReal.ofReal s = ∫⁻ t in Set.Ioo 0 s, 1 := by simp [Real.volume_Ioo]
                _ = ∫⁻ t in Set.Ioo 0 s, (A t).indicator 1 v := by
                    apply setLIntegral_congr_fun measurableSet_Ioo
                    intro t ht
                    have : v ∈ A t := by
                      rw [hA]
                      refine ⟨i, j0, hj0i.symm, ?_, ?_⟩
                      · have := hmax j0; rw [hsv] at ht; linarith [ht.2]
                      · rw [hsv] at ht; exact ht.2.le
                    simp [Set.indicator_of_mem this]
                _ ≤ ∫⁻ t in Set.Ioi 0, (A t).indicator 1 v :=
                    lintegral_mono_set Set.Ioo_subset_Ioi_self
            -- the revenue
            have hutil : ∀ S : Finset (Fin N), i ∈ S →
                rnValue v S - opqPrice p q S = (v i + ∑ j ∈ S.erase i, v j) / S.card - price S.card := by
              intro S hS
              simp only [rnValue, opqPrice, hprice, Finset.add_sum_erase S v hS]
            have hσk : ∀ k, 1 ≤ k → k ≤ N → σ k = 1 / (k:ℝ) := fun k _ hk => by simp [hσ, hk]
            have hσN1 : σ (N+1) = 0 := by simp [hσ]
            have hccN : cc i v (N+1) = 0 := by simp [hcc]
            have hcck : ∀ k, k ≤ N → cc i v k = price k - B i v k / k := fun k hk => by simp [hcc, hk]
            have hfamne : ∀ k, 1 ≤ k → k ≤ N → (fam i k).Nonempty := by
              intro k hk1 hkN
              have : k - 1 ≤ (Finset.univ.erase i).card := by simp; omega
              obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq this
              have hit : i ∉ t := fun h => by simpa using ht h
              refine ⟨insert i t, ?_⟩
              simp only [hfam, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert_self,
                Finset.card_insert_of_notMem hit, htc]
              omega
            unfold opqRevenue menuRevenue
            simp only
            split_ifs with h
            swap
            · rw [ENNReal.ofReal_zero]; exact zero_le
            obtain ⟨o, ho, heq⟩ := Finset.exists_mem_eq_sup' h (opqPrice p q)
            rw [heq]
            rw [Finset.mem_filter] at ho
            obtain ⟨hoS, hu, hopt⟩ := ho
            have hone : o.Nonempty := by simpa [opqOptions] using hoS
            -- WLOG i ∈ o
            obtain ⟨o', ho'S, hio', hcard, hsum⟩ : ∃ o' ∈ opqOptions N, i ∈ o' ∧ o'.card = o.card ∧
                ∑ j ∈ o', v j = ∑ j ∈ o, v j := by
              by_cases hio : i ∈ o
              · exact ⟨o, hoS, hio, rfl, rfl⟩
              obtain ⟨j, hj, hjmax⟩ := o.exists_max_image v hone
              have hie : i ∉ o.erase j := fun h => hio (Finset.mem_of_mem_erase h)
              have hc' : (insert i (o.erase j)).card = o.card := by
                rw [Finset.card_insert_of_notMem hie, Finset.card_erase_of_mem hj]
                have := hone.card_pos; omega
              have hs' : ∑ x ∈ insert i (o.erase j), v x = v i + ∑ x ∈ o, v x - v j := by
                rw [Finset.sum_insert hie, Finset.sum_erase_eq_sub hj]; ring
              have hmem : insert i (o.erase j) ∈ opqOptions N := by
                simp [opqOptions]
              have hvj : v j = v i := by
                by_contra hne
                have hlt : v j < v i := lt_of_le_of_ne (hmax j) hne
                have := hopt _ hmem
                simp only [rnValue, opqPrice, hc', hs'] at this
                have hcpos : (0:ℝ) < o.card := by exact_mod_cast hone.card_pos
                have : (∑ x ∈ o, v x) / o.card < (v i + ∑ x ∈ o, v x - v j) / o.card :=
                  div_lt_div_of_pos_right (by linarith) hcpos
                linarith
              exact ⟨_, hmem, Finset.mem_insert_self _ _, hc', by rw [hs', hvj]; ring⟩
            have hpr : opqPrice p q o = opqPrice p q o' := by simp only [opqPrice, hcard]
            have hu' : rnValue v o' - opqPrice p q o' = rnValue v o - opqPrice p q o := by
              simp only [rnValue, hsum, hcard, hpr]
            rw [hpr]
            rw [← hu'] at hu hopt
            obtain ⟨k, hk⟩ : ∃ k, k = o'.card := ⟨_, rfl⟩
            have hk1 : 1 ≤ k := hk ▸ Finset.card_pos.mpr ⟨i, hio'⟩
            have hkN : k ≤ N := hk ▸ (Finset.card_le_univ o').trans (Fintype.card_fin N).le
            have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr hk1
            have ho'fam : o' ∈ fam i k := by simp [hfam, hio', hk]
            have hBk : B i v k = ∑ j ∈ o'.erase i, v j := by
              have hne := hfamne k hk1 hkN
              simp only [hB, dif_pos hne]
              apply le_antisymm
              · apply Finset.sup'_le
                intro S hS
                simp only [hfam, Finset.mem_filter, Finset.mem_univ, true_and] at hS
                have h1 := hopt S (by simp [opqOptions]; exact ⟨i, hS.1⟩)
                rw [hutil S hS.1, hutil o' hio', hS.2, ← hk] at h1
                have h2 : (v i + ∑ j ∈ S.erase i, v j) / (k:ℝ) ≤ (v i + ∑ j ∈ o'.erase i, v j) / (k:ℝ) := by
                  linarith
                have := (div_le_div_iff_of_pos_right hkpos).mp h2
                linarith
              · exact Finset.le_sup' (fun S => ∑ j ∈ S.erase i, v j) ho'fam
            have hUo : σ k * v i - cc i v k = rnValue v o' - opqPrice p q o' := by
              rw [hutil o' hio', hσk k hk1 hkN, hcck k hkN, hBk, ← hk]
              ring
            have hIC : ∀ k' ∈ Finset.Icc 1 (N+1), σ k' * v i - cc i v k' ≤ σ k * v i - cc i v k := by
              intro k' hk'
              simp only [Finset.mem_Icc] at hk'
              rw [hUo]
              rcases Nat.lt_or_ge N k' with hlt | hle
              · have : k' = N + 1 := by omega
                subst this; rw [hσN1, hccN]; linarith
              · have hne := hfamne k' hk'.1 hle
                obtain ⟨S, hS, hSe⟩ := Finset.exists_mem_eq_sup' hne (fun S => ∑ j ∈ S.erase i, v j)
                have hBk' : B i v k' = ∑ j ∈ S.erase i, v j := by simp only [hB, dif_pos hne, hSe]
                simp only [hfam, Finset.mem_filter, Finset.mem_univ, true_and] at hS
                have hk'pos : (0:ℝ) < k' := by exact_mod_cast hk'.1
                have h1 := hopt S (by simp [opqOptions]; exact ⟨i, hS.1⟩)
                rw [hutil S hS.1, hS.2] at h1
                rw [hσk k' hk'.1 hle, hcck k' hle, hBk']
                have : 1 / (k':ℝ) * v i - (price k' - (∑ j ∈ S.erase i, v j) / k') =
                    (v i + ∑ j ∈ S.erase i, v j) / k' - price k' := by ring
                linarith
            have hspec := Classical.choose_spec (hC' (cc i v)) hccN k (by simp; omega) (v i) hIC
            have hθiv : θ i v = Classical.choose (hC' (cc i v)) := by rw [hθ]
            rw [← hθiv] at hspec
            obtain ⟨hc1, hc2⟩ := hspec
            -- price = cc + B/k
            have hprk : opqPrice p q o' = cc i v k + B i v k / k := by
              rw [hcck k hkN, sub_add_cancel, hprice, hk]; rfl
            have hBs : B i v k / k ≤ (1 - 1 / (N:ℝ)) * max s 0 := by
              rw [hBk]
              have h1 : ∑ j ∈ o'.erase i, v j ≤ ((o'.erase i).card : ℝ) * max s 0 := by
                have := Finset.sum_le_card_nsmul (o'.erase i) v (max s 0) (fun j hj =>
                  le_trans (hsj j (Finset.ne_of_mem_erase hj)) (le_max_left _ _))
                simpa using this
              rw [Finset.card_erase_of_mem hio', ← hk] at h1
              have h2 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
              rw [h2] at h1
              have hm0 : 0 ≤ max s 0 := le_max_right _ _
              have h3 : (1 - 1 / (k:ℝ)) ≤ 1 - 1 / (N:ℝ) := by
                exact sub_le_sub_left (one_div_le_one_div_of_le hkpos (Nat.cast_le.mpr hkN)) 1
              calc (∑ j ∈ o'.erase i, v j) / k ≤ ((k:ℝ) - 1) * max s 0 / k :=
                    div_le_div_of_nonneg_right h1 hkpos.le
                _ = (1 - 1 / (k:ℝ)) * max s 0 := by
                    rw [sub_mul, sub_mul, one_mul, sub_div,
                      mul_div_cancel_left₀ _ hkpos.ne', one_div_mul_eq_div]
                _ ≤ (1 - 1 / (N:ℝ)) * max s 0 := mul_le_mul_of_nonneg_right h3 hm0
            have hdnn : ∀ t ∈ Finset.Ico k (N+1), 0 ≤ σ t - σ (t+1) := by
              intro t ht
              rw [Finset.mem_Ico] at ht
              have ht1' : 1 ≤ t := le_trans hk1 ht.1
              have htN : t ≤ N := Nat.lt_succ_iff.mp ht.2
              have htpos : (0:ℝ) < t := Nat.cast_pos.mpr ht1'
              rw [hσk t ht1' htN, sub_nonneg]
              by_cases ht1 : t + 1 ≤ N
              · rw [hσk (t+1) (Nat.le_add_left 1 t) ht1]
                exact one_div_le_one_div_of_le htpos (by
                  rw [Nat.cast_add, Nat.cast_one]; exact le_add_of_nonneg_right zero_le_one)
              · have : σ (t+1) = 0 := by rw [hσ]; exact if_neg ht1
                rw [this]; exact (one_div_pos.mpr htpos).le
            have hN1 : (0:ℝ) ≤ 1 - 1 / (N:ℝ) := by
              have : 1 / (N:ℝ) ≤ 1 := by
                rw [div_le_one hNpos]; exact Nat.one_le_cast.mpr (le_trans (by norm_num) hN)
              exact sub_nonneg.mpr this
            have hΦ : ENNReal.ofReal (∑ t ∈ Finset.Ico k (N+1), (σ t - σ (t+1)) * θ i v t) ≤
                ∑ t ∈ Finset.Icc 1 N, ENNReal.ofReal (w t) * ENNReal.ofReal (θ i v t) *
                      (Set.Ici (θ i v t)).indicator 1 (v i) := by
              calc ENNReal.ofReal (∑ t ∈ Finset.Ico k (N+1), (σ t - σ (t+1)) * θ i v t)
                  ≤ ∑ t ∈ Finset.Ico k (N+1), ENNReal.ofReal ((σ t - σ (t+1)) * θ i v t) :=
                    Finset.le_sum_of_subadditive _ ENNReal.ofReal_zero.le (fun x y => ENNReal.ofReal_add_le) _ _
                _ = ∑ t ∈ Finset.Ico k (N+1), ENNReal.ofReal (w t) * ENNReal.ofReal (θ i v t) *
                      (Set.Ici (θ i v t)).indicator 1 (v i) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    have hind : (Set.Ici (θ i v t)).indicator (1 : ℝ → ENNReal) (v i) = 1 :=
                      Set.indicator_of_mem (show v i ∈ Set.Ici (θ i v t) from hc2 t ht) _
                    rw [hind, mul_one, hw]
                    simp only
                    rw [max_eq_right (hdnn t ht), ENNReal.ofReal_mul (hdnn t ht)]
                _ ≤ _ := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · intro t ht; simp only [Finset.mem_Ico, Finset.mem_Icc] at ht ⊢; omega
                    · intros; exact zero_le
            calc ENNReal.ofReal (opqPrice p q o')
                ≤ ENNReal.ofReal (∑ t ∈ Finset.Ico k (N+1), (σ t - σ (t+1)) * θ i v t) +
                    ENNReal.ofReal ((1 - 1 / (N:ℝ)) * max s 0) := by
                  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add_le)
                  rw [hprk]; exact add_le_add hc1 hBs
              _ ≤ (∑ t ∈ Finset.Icc 1 N, ENNReal.ofReal (w t) * ENNReal.ofReal (θ i v t) *
                      (Set.Ici (θ i v t)).indicator 1 (v i)) +
                    ENNReal.ofReal (1 - 1 / (N : ℝ)) * (∫⁻ t in Set.Ioi 0, (A t).indicator 1 v) := by
                  refine add_le_add hΦ ?_
                  rw [ENNReal.ofReal_mul hN1]
                  exact mul_le_mul_right hsA _
              _ ≤ _ := by
                  rw [add_comm]
                  refine add_le_add le_rfl ?_
                  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun j _ => (bot_le : (⊥ : ENNReal) ≤ _)) (Finset.mem_univ i))
                  rw [Set.indicator_of_mem hFi]
          have hKK : ∀ (τ : ℝ) (E : Set ℝ), MeasurableSet E → (∀ x ∈ E, ∀ y, x ≤ y → y ∈ E) →
              ENNReal.ofReal τ * ν (Set.Ici τ ∩ E) ≤
                optSP (Measure.pi (fun _ : Fin N => ν)) / (N : ENNReal) +
                  optSP (Measure.pi (fun _ : Fin N => ν)) * ν E := by
            intro τ E hEm hEup
            set μ := Measure.pi (fun _ : Fin N => ν) with hμ
            by_cases hRt : optSP μ = ⊤
            · rw [hRt, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top N)]
              simp
            set r := (optSP μ).toReal with hr
            have hRr : optSP μ = ENNReal.ofReal r := (ENNReal.ofReal_toReal hRt).symm
            have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
            have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
            -- core Ici inequality
            have core : ∀ t : ℝ, ENNReal.ofReal t * ν (Set.Ici t) ≤
                optSP μ / (N : ENNReal) + optSP μ * ν (Set.Ici t) := by
              intro t
              rcases le_or_gt t 0 with ht | ht
              · rw [ENNReal.ofReal_of_nonpos ht, zero_mul]; exact zero_le
              have hBm : MeasurableSet {v : Fin N → ℝ | ∃ i, t ≤ v i} := by
                have : {v : Fin N → ℝ | ∃ i, t ≤ v i} = ⋃ i, {v : Fin N → ℝ | t ≤ v i} := by
                  ext v; simp
                rw [this]
                exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
              have hSP : ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i} ≤ optSP μ := by
                have : expSP μ t = ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i} := rfl
                rw [← this]
                exact le_iSup₂ (f := fun p (_ : 0 ≤ p) => expSP μ p) t ht.le
              have hBc : {v : Fin N → ℝ | ∃ i, t ≤ v i}ᶜ = Set.pi Set.univ (fun _ : Fin N => Set.Iio t) := by
                ext v; simp
              have hμBc : μ {v : Fin N → ℝ | ∃ i, t ≤ v i}ᶜ = ν (Set.Iio t) ^ N := by
                rw [hBc, hμ, Measure.pi_pi]; simp
              have hB1 := measure_add_measure_compl (μ := μ) hBm
              rw [measure_univ, hμBc] at hB1
              have hxy := measure_add_measure_compl (μ := ν) (measurableSet_Ici (a := t))
              rw [Set.compl_Ici, measure_univ] at hxy
              set X := (ν (Set.Ici t)).toReal with hX
              set Y := (ν (Set.Iio t)).toReal with hY
              have finν : ∀ s, ν s ≠ ⊤ := fun s => measure_ne_top ν s
              have fin : ∀ s, μ s ≠ ⊤ := fun s => measure_ne_top μ s
              have rxy := congrArg ENNReal.toReal hxy
              rw [ENNReal.toReal_add (finν _) (finν _), ENNReal.toReal_one] at rxy
              have rB1 := congrArg ENNReal.toReal hB1
              rw [ENNReal.toReal_add (fin _) (ENNReal.pow_ne_top (finν _)), ENNReal.toReal_one,
                ENNReal.toReal_pow] at rB1
              have rSP := ENNReal.toReal_mono hRt hSP
              rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le] at rSP
              have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
              have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
              have hYX : Y = 1 - X := by linarith
              have hX1 : X ≤ 1 := by linarith
              -- real inequality
              have bern : 1 + (N:ℝ) * X ≤ (1 + X) ^ N := one_add_mul_le_pow (by linarith) N
              have h1 : Y ^ N * (1 + N * X) ≤ 1 := by
                calc Y ^ N * (1 + N * X) ≤ Y ^ N * (1 + X) ^ N :=
                      mul_le_mul_of_nonneg_left bern (pow_nonneg hY0 _)
                  _ = (1 - X ^ 2) ^ N := by rw [← mul_pow, hYX]; ring
                  _ ≤ 1 := pow_le_one₀ (sub_nonneg.mpr (pow_le_one₀ hX0 hX1)) (sub_le_self _ (sq_nonneg X))
              have hmu : (μ {v : Fin N → ℝ | ∃ i, t ≤ v i}).toReal = 1 - Y ^ N := by linarith
              rw [hmu] at rSP
              have h2 : t * (N * X) ≤ r * (1 + N * X) := by
                have hNX : 0 ≤ 1 + N * X := by have := mul_nonneg hNpos.le hX0; linarith
                calc t * (N * X) ≤ t * ((1 - Y ^ N) * (1 + N * X)) := by
                      apply mul_le_mul_of_nonneg_left _ ht.le
                      have e : (1 - Y ^ N) * (1 + N * X) = (1 + N * X) - Y ^ N * (1 + N * X) := by ring
                      rw [e]; linarith
                  _ = t * (1 - Y ^ N) * (1 + N * X) := by ring
                  _ ≤ r * (1 + N * X) := mul_le_mul_of_nonneg_right rSP hNX
              have h3 : t * X ≤ r / N + r * X := by
                rw [div_add' _ _ _ hNpos.ne', le_div_iff₀ hNpos]
                have e1 : t * X * N = t * (N * X) := by ring
                have e2 : r + r * X * N = r * (1 + N * X) := by ring
                rw [e1, e2]; exact h2
              rw [← ENNReal.ofReal_toReal (finν (Set.Ici t)), ← hX, hRr,
                ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hNpos,
                ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul hr0,
                ← ENNReal.ofReal_add (div_nonneg hr0 hNpos.le) (mul_nonneg hr0 hX0)]
              exact ENNReal.ofReal_le_ofReal h3
            -- Ioi version
            have coreO : ∀ t : ℝ, ENNReal.ofReal t * ν (Set.Ioi t) ≤
                optSP μ / (N : ENNReal) + optSP μ * ν (Set.Ioi t) := by
              intro t
              have hU : Set.Ioi t = ⋃ n : ℕ, Set.Ici (t + 1 / ((n:ℝ) + 1)) := by
                ext x
                simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
                constructor
                · intro hx
                  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
                  exact ⟨n, by linarith⟩
                · rintro ⟨n, hn⟩
                  have : (0:ℝ) < 1 / ((n:ℝ) + 1) := Nat.one_div_pos_of_nat
                  linarith
              have hmono : Monotone (fun n : ℕ => Set.Ici (t + 1 / ((n:ℝ) + 1))) := by
                intro a b hab
                apply Set.Ici_subset_Ici.mpr
                have : (a:ℝ) + 1 ≤ (b:ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
                have := one_div_le_one_div_of_le (Nat.cast_add_one_pos a) this
                linarith
              have hlim : ν (Set.Ioi t) = ⨆ n : ℕ, ν (Set.Ici (t + 1 / ((n:ℝ) + 1))) := by
                rw [hU]; exact hmono.measure_iUnion
              rw [hlim, ENNReal.mul_iSup]
              refine iSup_le fun n => ?_
              have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := Nat.one_div_pos_of_nat
              calc ENNReal.ofReal t * ν (Set.Ici (t + 1 / ((n:ℝ) + 1)))
                  ≤ ENNReal.ofReal (t + 1 / ((n:ℝ) + 1)) * ν (Set.Ici (t + 1 / ((n:ℝ) + 1))) := by
                    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) bot_le
                _ ≤ optSP μ / (N : ENNReal) + optSP μ * ν (Set.Ici (t + 1 / ((n:ℝ) + 1))) := core _
                _ ≤ optSP μ / (N : ENNReal) + optSP μ * ⨆ n : ℕ, ν (Set.Ici (t + 1 / ((n:ℝ) + 1))) := by
                    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
                      (le_iSup (fun n : ℕ => ν (Set.Ici (t + 1 / ((n:ℝ) + 1)))) n) bot_le)
            -- general up-set
            set E' := Set.Ici τ ∩ E with hE'
            have hE'up : ∀ x ∈ E', ∀ y, x ≤ y → y ∈ E' := by
              intro x hx y hxy
              exact ⟨le_trans hx.1 hxy, hEup x hx.2 y hxy⟩
            have key : ENNReal.ofReal τ * ν E' ≤ optSP μ / (N : ENNReal) + optSP μ * ν E' := by
              rcases E'.eq_empty_or_nonempty with he | hne
              · rw [he]; simp
              have hbdd : BddBelow E' := ⟨τ, fun x hx => hx.1⟩
              set s := sInf E' with hs
              have hτs : τ ≤ s := le_csInf hne (fun x hx => hx.1)
              by_cases hsm : s ∈ E'
              · have : E' = Set.Ici s := by
                  ext x; constructor
                  · intro hx; exact csInf_le hbdd hx
                  · intro hx; exact hE'up s hsm x hx
                rw [this]
                calc ENNReal.ofReal τ * ν (Set.Ici s) ≤ ENNReal.ofReal s * ν (Set.Ici s) :=
                      mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hτs) bot_le
                  _ ≤ _ := core s
              · have : E' = Set.Ioi s := by
                  ext x; constructor
                  · intro hx
                    exact lt_of_le_of_ne (csInf_le hbdd hx) (fun h => hsm (by rw [hs, h]; exact hx))
                  · intro hx
                    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne hx
                    exact hE'up y hy x hyx.le
                rw [this]
                calc ENNReal.ofReal τ * ν (Set.Ioi s) ≤ ENNReal.ofReal s * ν (Set.Ioi s) :=
                      mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hτs) bot_le
                  _ ≤ _ := coreO s
            calc ENNReal.ofReal τ * ν E' ≤ optSP μ / (N : ENNReal) + optSP μ * ν E' := key
              _ ≤ optSP μ / (N : ENNReal) + optSP μ * ν E := by
                  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
                    (measure_mono Set.inter_subset_right) bot_le)
          have hCC : ∀ (σ : ℕ → ℝ), StrictAntiOn σ (Set.Icc 1 (N+1)) → σ (N+1) = 0 →
              ∀ (c : ℕ → ℝ), c (N+1) = 0 →
              ∃ θ : ℕ → ℝ, ∀ u ∈ Finset.Icc 1 (N+1), ∀ x : ℝ,
                (∀ v ∈ Finset.Icc 1 (N+1), σ v * x - c v ≤ σ u * x - c u) →
                c u ≤ ∑ t ∈ Finset.Ico u (N+1), (σ t - σ (t+1)) * θ t ∧
                  ∀ t ∈ Finset.Ico u (N+1), θ t ≤ x := by
            intro σ hσ hσN c hcN
            have hne1 : ∀ t, 1 ≤ t → (Finset.Icc 1 t).Nonempty := fun t ht => ⟨1, by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega⟩
            have hne2 : ∀ t, t ≤ N → (Finset.Ioc t (N+1)).Nonempty := fun t ht => ⟨N+1, by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega⟩
            have hsl : ∀ a b, 1 ≤ a → a < b → b ≤ N + 1 → σ b < σ a := fun a b ha hab hb =>
              hσ ⟨ha, by omega⟩ ⟨by omega, hb⟩ hab
            let θ : ℕ → ℝ := fun t => if h : 1 ≤ t ∧ t ≤ N then
              (Finset.Icc 1 t).inf' (hne1 t h.1) (fun u => (Finset.Ioc t (N+1)).sup' (hne2 t h.2)
                (fun v => (c u - c v) / (σ u - σ v))) else 0
            -- θ t ≤ sup over v for any u
            have hθle : ∀ t (h1 : 1 ≤ t) (h2 : t ≤ N), ∀ u ∈ Finset.Icc 1 t,
                θ t ≤ (Finset.Ioc t (N+1)).sup' (hne2 t h2) (fun v => (c u - c v) / (σ u - σ v)) := by
              intro t h1 h2 u hu
              simp only [θ, dif_pos (And.intro h1 h2)]
              exact Finset.inf'_le _ hu
            have hθge : ∀ t, 1 ≤ t → t ≤ N → ∃ u ∈ Finset.Icc 1 t, ∀ v ∈ Finset.Ioc t (N+1),
                (c u - c v) / (σ u - σ v) ≤ θ t := by
              intro t h1 h2
              obtain ⟨u, hu, he⟩ := Finset.exists_mem_eq_inf' (hne1 t h1)
                (fun u => (Finset.Ioc t (N+1)).sup' (hne2 t h2) (fun v => (c u - c v) / (σ u - σ v)))
              refine ⟨u, hu, fun v hv => ?_⟩
              simp only [θ, dif_pos (And.intro h1 h2)]
              rw [he]
              exact Finset.le_sup' (fun v => (c u - c v) / (σ u - σ v)) hv
            -- crossing ≤ x iff line comparison
            have hcross_le : ∀ u v x, 1 ≤ u → u < v → v ≤ N + 1 →
                σ v * x - c v ≤ σ u * x - c u → (c u - c v) / (σ u - σ v) ≤ x := by
              intro u v x hu huv hv h
              have := hsl u v hu huv hv
              rw [div_le_iff₀ (by linarith)]; linarith
            have hcross_ge : ∀ u v y, 1 ≤ u → u < v → v ≤ N + 1 →
                σ u * y - c u ≤ σ v * y - c v → y ≤ (c u - c v) / (σ u - σ v) := by
              intro u v y hu huv hv h
              have := hsl u v hu huv hv
              rw [le_div_iff₀ (by linarith)]; linarith
            have tele : ∀ u n, u ≤ n → ∑ t ∈ Finset.Ico u n, (σ t - σ (t+1)) = σ u - σ n := by
              intro u n hun
              induction n, hun using Nat.le_induction with
              | base => simp
              | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih]; ring
            refine ⟨θ, ?_⟩
            -- Part A
            have partA : ∀ u ∈ Finset.Icc 1 (N+1), ∀ x : ℝ,
                (∀ v ∈ Finset.Icc 1 (N+1), σ v * x - c v ≤ σ u * x - c u) →
                ∀ t ∈ Finset.Ico u (N+1), θ t ≤ x := by
              intro u hu x hopt t ht
              simp only [Finset.mem_Icc, Finset.mem_Ico] at hu ht
              refine le_trans (hθle t (by omega) (by omega) u (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega)) ?_
              refine Finset.sup'_le _ _ (fun v hv => ?_)
              simp only [Finset.mem_Ioc] at hv
              exact hcross_le u v x hu.1 (by omega) hv.2 (hopt v (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega))
            have key : ∀ d, ∀ u ∈ Finset.Icc 1 (N+1), N + 1 - u = d → ∀ x : ℝ,
                (∀ v ∈ Finset.Icc 1 (N+1), σ v * x - c v ≤ σ u * x - c u) →
                c u ≤ ∑ t ∈ Finset.Ico u (N+1), (σ t - σ (t+1)) * θ t := by
              intro d
              induction d using Nat.strong_induction_on with
              | _ d ih =>
              intro u hu hd x hopt
              simp only [Finset.mem_Icc] at hu
              rcases Nat.lt_or_ge u (N+1) with hlt | hge
              swap
              · have : u = N + 1 := by omega
                subst this; rw [hcN, Finset.Ico_self, Finset.sum_empty]
              have huN : u ≤ N := by omega
              set y := (Finset.Ioc u (N+1)).sup' (hne2 u huN) (fun v => (c u - c v) / (σ u - σ v)) with hy
              obtain ⟨v0, hv0, hv0e⟩ := Finset.exists_mem_eq_sup' (hne2 u huN)
                (fun v => (c u - c v) / (σ u - σ v))
              rw [← hy] at hv0e
              simp only [Finset.mem_Ioc] at hv0
              have hs0 := hsl u v0 hu.1 hv0.1 hv0.2
              have hyx : y ≤ x := Finset.sup'_le _ _ (fun v hv => by
                simp only [Finset.mem_Ioc] at hv
                exact hcross_le u v x hu.1 hv.1 hv.2 (hopt v (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega)))
              have hcu : c u = c v0 + (σ u - σ v0) * y := by
                rw [hv0e, mul_div_cancel₀ _ (by linarith : σ u - σ v0 ≠ 0)]; ring
              have hopty : ∀ v ∈ Finset.Icc 1 (N+1), σ v * y - c v ≤ σ v0 * y - c v0 := by
                intro v hv
                simp only [Finset.mem_Icc] at hv
                have e : σ v0 * y - c v0 = σ u * y - c u := by rw [hcu]; ring
                rw [e]
                rcases lt_trichotomy v u with h | h | h
                · have hs := hsl v u hv.1 h hu.2
                  have h1 := hopt v (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega)
                  have h2 : 0 ≤ (σ v - σ u) * (x - y) := mul_nonneg (by linarith) (by linarith)
                  linarith
                · rw [h]
                · have h1 : (c u - c v) / (σ u - σ v) ≤ y :=
                    Finset.le_sup' (fun v => (c u - c v) / (σ u - σ v)) (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega)
                  have hs := hsl u v hu.1 h hv.2
                  rw [div_le_iff₀ (by linarith)] at h1
                  linarith
              have IH := ih (N + 1 - v0) (by omega) v0 (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega) rfl y hopty
              have hθy : ∀ t ∈ Finset.Ico u v0, y ≤ θ t := by
                intro t ht
                simp only [Finset.mem_Ico] at ht
                obtain ⟨u', hu', hle⟩ := hθge t (by omega) (by omega)
                simp only [Finset.mem_Icc] at hu'
                refine le_trans ?_ (hle v0 (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega))
                exact hcross_ge u' v0 y hu'.1 (by omega) hv0.2 (hopty u' (by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega))
              rw [← Finset.sum_Ico_consecutive _ (le_of_lt hv0.1) hv0.2]
              have hsum : (σ u - σ v0) * y ≤ ∑ t ∈ Finset.Ico u v0, (σ t - σ (t+1)) * θ t := by
                rw [← tele u v0 (le_of_lt hv0.1), Finset.sum_mul]
                refine Finset.sum_le_sum (fun t ht => ?_)
                have ht' := ht
                simp only [Finset.mem_Ico] at ht'
                have hs := hsl t (t+1) (by omega) (by omega) (by omega)
                exact mul_le_mul_of_nonneg_left (hθy t ht) (by linarith)
              linarith
            intro u hu x hopt
            exact ⟨key _ u hu rfl x hopt, partA u hu x hopt⟩
          have hFF : ∀ (Rr : ENNReal), (∀ (τ : ℝ) (E : Set ℝ), MeasurableSet E →
                (∀ x ∈ E, ∀ y, x ≤ y → y ∈ E) →
                ENNReal.ofReal τ * ν (Set.Ici τ ∩ E) ≤ Rr / (N : ENNReal) + Rr * ν E) →
              ∀ (w : ℕ → ℝ), (∀ t, 0 ≤ w t) → (∑ t ∈ Finset.Icc 1 N, w t = 1) →
              ∀ (θ : Fin N → (Fin N → ℝ) → ℕ → ℝ),
              (∀ i v x t, θ i (Function.update v i x) t = θ i v t) →
              ∫⁻ v, ∑ i : Fin N,
                {v : Fin N → ℝ | (∀ j, j < i → v j < v i) ∧ (∀ j, i < j → v j ≤ v i)}.indicator
                  (fun v => ∑ t ∈ Finset.Icc 1 N, ENNReal.ofReal (w t) * ENNReal.ofReal (θ i v t) *
                    (Set.Ici (θ i v t)).indicator 1 (v i)) v
                ∂(Measure.pi (fun _ : Fin N => ν)) ≤ 2 * Rr := by
            intro Rr K w hw hw1 θ hθ
            obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
            set μ := Measure.pi (fun _ : Fin (n+1) => ν) with hμ
            set F : Fin (n+1) → Set (Fin (n+1) → ℝ) := fun i =>
              {v : Fin (n+1) → ℝ | (∀ j, j < i → v j < v i) ∧ (∀ j, i < j → v j ≤ v i)} with hF
            set Φ : Fin (n+1) → (Fin (n+1) → ℝ) → ENNReal := fun i v =>
              ∑ t ∈ Finset.Icc 1 (n+1), ENNReal.ofReal (w t) * ENNReal.ofReal (θ i v t) *
                (Set.Ici (θ i v t)).indicator 1 (v i) with hΦ
            change ∫⁻ v, ∑ i, (F i).indicator (Φ i) v ∂μ ≤ 2 * Rr
            have hFm : ∀ i, MeasurableSet (F i) := by
              intro i
              have : F i = (⋂ j ∈ {j | j < i}, {v : Fin (n+1) → ℝ | v j < v i}) ∩
                  (⋂ j ∈ {j | i < j}, {v : Fin (n+1) → ℝ | v j ≤ v i}) := by
                ext v; simp only [hF, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
              rw [this]
              exact (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
                  measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)).inter
                (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
                  measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i))
            have hdisj : Pairwise (Function.onFun Disjoint F) := by
              intro i j hij
              rw [Function.onFun, Set.disjoint_left]
              intro v hi hj
              rcases lt_or_gt_of_ne hij with h | h
              · have h1 := hj.1 i h
                have h2 := hi.2 j h
                linarith
              · have h1 := hi.1 j h
                have h2 := hj.2 i h
                linarith
            have hper : ∀ i, ∫⁻ v, (F i).indicator (Φ i) v ∂μ ≤
                Rr / ((n + 1 : ℕ) : ENNReal) + Rr * μ (F i) := by
              intro i
              set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i with he
              have hmp : MeasurePreserving e μ (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
                measurePreserving_piFinSuccAbove (fun _ => ν) i
              set μ' := Measure.pi fun _ : Fin n => ν with hμ'
              have hes : ∀ z : ℝ × (Fin n → ℝ), e.symm z = (Fin.insertNth (α := fun _ => ℝ) i z.1 z.2 : Fin (n+1) → ℝ) := fun z => rfl
              set g := (F i).indicator (Φ i) with hg
              set S := e.symm ⁻¹' (F i) with hS
              have hSm : MeasurableSet S := e.symm.measurable (hFm i)
              have h1 : ∫⁻ v, g v ∂μ = ∫⁻ z, g (e.symm (z.2, z.1)) ∂(μ'.prod ν) := by
                rw [← (MeasurePreserving.symm e hmp).lintegral_comp_emb e.symm.measurableEmbedding g]
                exact lintegral_prod_swap (μ := μ') (ν := ν) (fun z : (Fin n → ℝ) × ℝ => g (e.symm (z.2, z.1)))
              have hinner : ∀ y : Fin n → ℝ, ∫⁻ x, g (e.symm (x, y)) ∂ν ≤
                  Rr / ((n + 1 : ℕ) : ENNReal) + Rr * ν ((fun x => (x, y)) ⁻¹' S) := by
                intro y
                set v0 : Fin (n+1) → ℝ := Fin.insertNth (α := fun _ => ℝ) i (0:ℝ) y with hv0
                set E := (fun x => (x, y)) ⁻¹' S with hE
                have hEm : MeasurableSet E := measurable_prodMk_right hSm
                have hupd : ∀ x, e.symm (x, y) = Function.update v0 i x := by
                  intro x; rw [hes, hv0, Fin.update_insertNth]
                have hEup : ∀ x ∈ E, ∀ x', x ≤ x' → x' ∈ E := by
                  intro x hx x' hxx'
                  simp only [hE, hS, Set.mem_preimage, hupd, hF, Set.mem_ofPred_eq,
                    Function.update_self] at hx ⊢
                  obtain ⟨ha, hb⟩ := hx
                  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
                  · have := ha j hj
                    rw [Function.update_of_ne (ne_of_lt hj)] at this ⊢
                    linarith
                  · have := hb j hj
                    rw [Function.update_of_ne (ne_of_gt hj)] at this ⊢
                    linarith
                have hpt : ∀ x, g (e.symm (x, y)) = E.indicator (fun x => ∑ t ∈ Finset.Icc 1 (n+1),
                    ENNReal.ofReal (w t) * ENNReal.ofReal (θ i v0 t) *
                      (Set.Ici (θ i v0 t)).indicator 1 x) x := by
                  intro x
                  have hmem : (e.symm (x, y) ∈ F i) ↔ x ∈ E := Iff.rfl
                  by_cases hx : x ∈ E
                  · rw [Set.indicator_of_mem hx, hg, Set.indicator_of_mem (hmem.mpr hx), hΦ]
                    simp only [hupd, hθ, Function.update_self]
                  · rw [Set.indicator_of_notMem hx, hg, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]
                simp_rw [hpt]
                rw [lintegral_indicator hEm, lintegral_finsetSum]
                · calc ∑ t ∈ Finset.Icc 1 (n+1), ∫⁻ x in E, ENNReal.ofReal (w t) *
                        ENNReal.ofReal (θ i v0 t) * (Set.Ici (θ i v0 t)).indicator 1 x ∂ν
                      = ∑ t ∈ Finset.Icc 1 (n+1), ENNReal.ofReal (w t) *
                        (ENNReal.ofReal (θ i v0 t) * ν (Set.Ici (θ i v0 t) ∩ E)) := by
                        refine Finset.sum_congr rfl fun t _ => ?_
                        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Ici),
                          lintegral_indicator_one measurableSet_Ici,
                          Measure.restrict_apply measurableSet_Ici, mul_assoc]
                    _ ≤ ∑ t ∈ Finset.Icc 1 (n+1), ENNReal.ofReal (w t) *
                        (Rr / ((n + 1 : ℕ) : ENNReal) + Rr * ν E) := by
                        gcongr with t ht
                        exact K _ E hEm hEup
                    _ = Rr / ((n + 1 : ℕ) : ENNReal) + Rr * ν E := by
                        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun t _ => hw t), hw1,
                          ENNReal.ofReal_one, one_mul]
                · intro t _
                  exact (measurable_one.indicator measurableSet_Ici).const_mul _
              have hmeasE : Measurable fun y : Fin n → ℝ => ν ((fun x => (x, y)) ⁻¹' S) :=
                measurable_measure_prodMk_right hSm
              calc ∫⁻ v, g v ∂μ = ∫⁻ z, g (e.symm (z.2, z.1)) ∂(μ'.prod ν) := h1
                _ ≤ ∫⁻ y, ∫⁻ x, g (e.symm (x, y)) ∂ν ∂μ' := lintegral_prod_le _
                _ ≤ ∫⁻ y, (Rr / ((n + 1 : ℕ) : ENNReal) + Rr * ν ((fun x => (x, y)) ⁻¹' S)) ∂μ' :=
                    lintegral_mono hinner
                _ = Rr / ((n + 1 : ℕ) : ENNReal) + Rr * (ν.prod μ') S := by
                    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                      lintegral_const_mul _ hmeasE, Measure.prod_apply_symm hSm]
                _ = Rr / ((n + 1 : ℕ) : ENNReal) + Rr * μ (F i) := by
                    rw [hS, (MeasurePreserving.symm e hmp).measure_preimage (hFm i).nullMeasurableSet]
            -- assemble
            have hUm : MeasurableSet (⋃ i, F i) := MeasurableSet.iUnion hFm
            have hf_on : ∀ i, Set.EqOn (fun v => ∑ j, (F j).indicator (Φ j) v) ((F i).indicator (Φ i)) (F i) := by
              intro i v hv
              simp only
              rw [Finset.sum_eq_single i]
              · intro j _ hji
                exact Set.indicator_of_notMem (Set.disjoint_left.mp (hdisj hji.symm) hv) _
              · intro h; exact absurd (Finset.mem_univ i) h
            calc ∫⁻ v, ∑ i, (F i).indicator (Φ i) v ∂μ
                = ∫⁻ v in ⋃ i, F i, ∑ j, (F j).indicator (Φ j) v ∂μ +
                    ∫⁻ v in (⋃ i, F i)ᶜ, ∑ j, (F j).indicator (Φ j) v ∂μ :=
                  (lintegral_add_compl _ hUm).symm
              _ = ∫⁻ v in ⋃ i, F i, ∑ j, (F j).indicator (Φ j) v ∂μ := by
                  rw [setLIntegral_congr_fun hUm.compl (g := fun _ => 0), lintegral_zero, add_zero]
                  intro v hv
                  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hv
                  exact Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (hv j) _
              _ ≤ ∑' i, ∫⁻ v in F i, ∑ j, (F j).indicator (Φ j) v ∂μ := lintegral_iUnion_le _ _
              _ = ∑ i, ∫⁻ v, (F i).indicator (Φ i) v ∂μ := by
                  rw [tsum_fintype]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [setLIntegral_congr_fun (hFm i) (hf_on i), ← lintegral_indicator (hFm i),
                    Set.indicator_indicator, Set.inter_self]
              _ ≤ ∑ i, (Rr / ((n + 1 : ℕ) : ENNReal) + Rr * μ (F i)) := Finset.sum_le_sum fun i _ => hper i
              _ = ((n + 1 : ℕ) : ENNReal) * (Rr / ((n + 1 : ℕ) : ENNReal)) + Rr * μ (⋃ i, F i) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, measure_iUnion hdisj hFm, tsum_fintype,
                    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              _ ≤ Rr + Rr * 1 := by
                  rw [ENNReal.mul_div_cancel (by simp) (by simp)]
                  gcongr
                  exact prob_le_one
              _ = 2 * Rr := by ring
          set μ := Measure.pi (fun _ : Fin N => ν) with hμ
          obtain ⟨A, hA⟩ : ∃ A : ℝ → Set (Fin N → ℝ),
              A = fun t => {v | ∃ i j, i ≠ j ∧ t ≤ v i ∧ t ≤ v j} := ⟨_, rfl⟩
          obtain ⟨B, hB⟩ : ∃ B : ℝ → Set (Fin N → ℝ),
              B = fun t => {v | ∃ i, t ≤ v i} := ⟨_, rfl⟩
          have hBm : ∀ t, MeasurableSet (B t) := by
            intro t
            have : B t = ⋃ i, {v : Fin N → ℝ | t ≤ v i} := by ext v; simp [hB]
            rw [this]
            exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
          have hAm : ∀ t, MeasurableSet (A t) := by
            intro t
            have : A t = ⋃ i, ⋃ j, ({v : Fin N → ℝ | i ≠ j} ∩ {v | t ≤ v i} ∩ {v | t ≤ v j}) := by
              ext v; simp [hA, and_assoc]
            rw [this]
            exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
              ((MeasurableSet.const _).inter (measurableSet_le measurable_const (measurable_pi_apply i))).inter
                (measurableSet_le measurable_const (measurable_pi_apply j))
          have hCm : MeasurableSet {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2} := by
            have : {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2} = ⋃ i, ⋃ j,
                ({z : (Fin N → ℝ) × ℝ | i ≠ j} ∩ {z | z.2 ≤ z.1 i} ∩ {z | z.2 ≤ z.1 j}) := by
              ext z; simp [hA, and_assoc]
            rw [this]
            exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
              ((MeasurableSet.const _).inter (measurableSet_le measurable_snd
                ((measurable_pi_apply i).comp measurable_fst))).inter
                (measurableSet_le measurable_snd ((measurable_pi_apply j).comp measurable_fst))
          have hSP : ∀ t, 0 ≤ t → ENNReal.ofReal t * μ (B t) ≤ optSP μ := by
            intro t ht
            have : expSP μ t = ENNReal.ofReal t * μ (B t) := by simp [expSP, hB]
            rw [← this]
            exact le_iSup₂ (f := fun p (_ : 0 ≤ p) => expSP μ p) t ht
          have hAB : ∀ t, μ (A t) ≤ μ (B t) ^ 2 := by
            intro t
            set x := ν (Set.Ici t) with hx
            set y := ν (Set.Iio t) with hy
            have hxy : x + y = 1 := by
              have := measure_add_measure_compl (μ := ν) (measurableSet_Ici (a := t))
              rwa [Set.compl_Ici, measure_univ] at this
            have hBc : (B t)ᶜ = Set.pi Set.univ (fun _ : Fin N => Set.Iio t) := by
              ext v; simp [hB]
            have hμBc : μ (B t)ᶜ = y ^ N := by
              rw [hBc, hμ, Measure.pi_pi]; simp [hy]
            obtain ⟨E, hE⟩ : ∃ E : Fin N → Set (Fin N → ℝ),
                E = fun i => Set.pi Set.univ (fun j => if j = i then Set.Ici t else Set.Iio t) :=
              ⟨_, rfl⟩
            have hEm : ∀ i, MeasurableSet (E i) := by
              intro i; rw [hE]
              exact MeasurableSet.univ_pi fun j => by
                split_ifs
                · exact measurableSet_Ici
                · exact measurableSet_Iio
            have hμE : ∀ i, μ (E i) = x * y ^ (N - 1) := by
              intro i
              rw [hE, hμ, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl i]
              simp only [if_pos rfl]
              congr 1
              rw [Finset.prod_congr rfl (g := fun _ => y) (fun j hj => by
                simp only [Finset.mem_compl, Finset.mem_singleton] at hj; simp [hj, hy])]
              simp [Finset.card_compl]
            have hEdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) E := by
              intro i _ j _ hij
              rw [Function.onFun, Set.disjoint_left]
              intro v hvi hvj
              rw [hE] at hvi hvj
              have h1 := hvi i (Set.mem_univ _)
              have h2 := hvj i (Set.mem_univ _)
              simp [hij] at h1 h2
              linarith
            have hBEdisj : Disjoint (B t)ᶜ (⋃ i ∈ (Finset.univ : Finset (Fin N)), E i) := by
              rw [Set.disjoint_left]
              intro v hv hv'
              simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hv'
              obtain ⟨i, hi⟩ := hv'
              rw [hE] at hi
              have h1 := hi i (Set.mem_univ _)
              simp at h1
              exact hv (by rw [hB]; exact ⟨i, h1⟩)
            have hsub : (B t)ᶜ ∪ (⋃ i ∈ (Finset.univ : Finset (Fin N)), E i) ⊆ (A t)ᶜ := by
              intro v hv
              rcases hv with hv | hv
              · intro hvA
                rw [hA] at hvA
                obtain ⟨i, j, _, hi, _⟩ := hvA
                exact hv (by rw [hB]; exact ⟨i, hi⟩)
              · simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hv
                obtain ⟨k, hk⟩ := hv
                intro hvA
                rw [hA] at hvA
                obtain ⟨i, j, hij, hi, hj⟩ := hvA
                rw [hE] at hk
                have h1 := hk i (Set.mem_univ _)
                have h2 := hk j (Set.mem_univ _)
                by_cases hik : i = k
                · subst hik
                  simp only [if_neg (Ne.symm hij), Set.mem_Iio] at h2
                  linarith
                · simp only [if_neg hik, Set.mem_Iio] at h1
                  linarith
            have hle : y ^ N + N * (x * y ^ (N - 1)) ≤ μ (A t)ᶜ := by
              calc y ^ N + N * (x * y ^ (N - 1))
                  = μ ((B t)ᶜ ∪ (⋃ i ∈ (Finset.univ : Finset (Fin N)), E i)) := by
                    rw [measure_union hBEdisj (Finset.measurableSet_biUnion _ (fun i _ => hEm i)),
                      measure_biUnion_finset hEdisj (fun i _ => hEm i), hμBc]
                    simp [hμE]
                _ ≤ μ (A t)ᶜ := measure_mono hsub
            have hA1 : μ (A t) + μ (A t)ᶜ = 1 := by
              rw [measure_add_measure_compl (hAm t), measure_univ]
            have hB1 : μ (B t) + μ (B t)ᶜ = 1 := by
              rw [measure_add_measure_compl (hBm t), measure_univ]
            have fin : ∀ s, μ s ≠ ⊤ := fun s => measure_ne_top μ s
            have finν : ∀ s, ν s ≠ ⊤ := fun s => measure_ne_top ν s
            rw [← ENNReal.toReal_le_toReal (fin _) (by simp [fin]), ENNReal.toReal_pow]
            have rA1 := congrArg ENNReal.toReal hA1
            have rB1 := congrArg ENNReal.toReal hB1
            have rxy := congrArg ENNReal.toReal hxy
            have rle := ENNReal.toReal_mono (fin _) hle
            rw [ENNReal.toReal_add (fin _) (fin _)] at rA1 rB1
            rw [ENNReal.toReal_add (finν _) (finν _)] at rxy
            have hyfin : y ≠ ⊤ := finν _
            have hxfin : x ≠ ⊤ := finν _
            rw [ENNReal.toReal_add (ENNReal.pow_ne_top hyfin) (ENNReal.mul_ne_top
              (ENNReal.natCast_ne_top N) (ENNReal.mul_ne_top hxfin (ENNReal.pow_ne_top hyfin))),
              ENNReal.toReal_mul,
              ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast] at rle
            rw [hμBc, ENNReal.toReal_pow] at rB1
            simp only [ENNReal.toReal_one] at rA1 rB1 rxy
            set X := x.toReal
            set Y := y.toReal
            set Z := Y ^ N with hZ
            set W := Y ^ (N - 1) with hW
            have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
            have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
            have hY1 : Y ≤ 1 := by linarith
            have hYN : Z = W * Y := by rw [hZ, hW, ← pow_succ]; congr 1; omega
            have hbern : 1 - Z ≤ N * X := by
              have := one_add_mul_le_pow (a := Y - 1) (by linarith) N
              rw [add_sub_cancel] at this
              have : X = 1 - Y := by linarith
              rw [this]; linarith
            have hZ1 : Z ≤ 1 := pow_le_one₀ hY0 hY1
            have hW0 : 0 ≤ W := pow_nonneg hY0 _
            have k1 : Y * (1 - Z) ≤ N * X :=
              le_trans (mul_le_of_le_one_left (by linarith) hY1) hbern
            have k2 : W * (Y * (1 - Z)) ≤ W * (N * X) := mul_le_mul_of_nonneg_left k1 hW0
            have k3 : W * (Y * (1 - Z)) = Z - Z ^ 2 := by rw [hYN]; ring
            have hb : (μ (B t)).toReal = 1 - Z := by linarith
            rw [hb]
            have k4 : W * (N * X) = (N:ℝ) * (X * W) := by ring
            have k5 : (1 - Z) ^ 2 = 1 - 2 * Z + Z ^ 2 := by ring
            rw [k5]
            linarith
          have hint : ∫⁻ t in Set.Ioi 0, μ (A t) ≤ 2 * optSP μ := by
            by_cases hR : optSP μ = ⊤
            · rw [hR]; simp
            set r := (optSP μ).toReal with hr
            have hRr : optSP μ = ENNReal.ofReal r := (ENNReal.ofReal_toReal hR).symm
            have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
            have hbnd : ∀ t, 0 < t → μ (A t) ≤ ENNReal.ofReal (r ^ 2 * t ^ (-2 : ℝ)) := by
              intro t ht
              have h1 : μ (B t) ≤ ENNReal.ofReal (r / t) := by
                rw [ENNReal.ofReal_div_of_pos ht, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht))
                  (Or.inl ENNReal.ofReal_ne_top), mul_comm, ← hRr]
                exact hSP t ht.le
              have h2 : r ^ 2 * t ^ (-2 : ℝ) = (r / t) ^ 2 := by
                rw [Real.rpow_neg ht.le, Real.rpow_two]; field_simp
              rw [h2, ENNReal.ofReal_pow (div_nonneg hr0 ht.le)]
              exact le_trans (hAB t) (pow_le_pow_left₀ zero_le h1 2)
            rw [← Set.Ioc_union_Ioi_eq_Ioi hr0]
            refine le_trans (lintegral_union_le _ _ _) ?_
            have hI1 : ∫⁻ t in Set.Ioc 0 r, μ (A t) ≤ ENNReal.ofReal r := by
              calc ∫⁻ t in Set.Ioc 0 r, μ (A t) ≤ ∫⁻ t in Set.Ioc 0 r, 1 :=
                    lintegral_mono fun t => prob_le_one
                _ = ENNReal.ofReal r := by simp [Real.volume_Ioc]
            have hI2 : ∫⁻ t in Set.Ioi r, μ (A t) ≤ ENNReal.ofReal r := by
              calc ∫⁻ t in Set.Ioi r, μ (A t)
                  ≤ ∫⁻ t in Set.Ioi r, ENNReal.ofReal (r ^ 2 * t ^ (-2 : ℝ)) := by
                    apply lintegral_mono_ae
                    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
                      hbnd t (lt_of_le_of_lt hr0 ht)
                _ = ENNReal.ofReal r := by
                    rcases hr0.lt_or_eq with hrpos | hrz
                    · rw [← ofReal_integral_eq_lintegral_ofReal]
                      · congr 1
                        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hrpos]
                        have : r ^ ((-2 : ℝ) + 1) = r⁻¹ := by
                          norm_num [Real.rpow_neg_one]
                        rw [this]; field_simp; ring
                      · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hrpos).const_mul (r ^ 2)
                      · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
                          have : 0 < t := lt_trans hrpos ht
                          simp only [Pi.zero_apply]
                          positivity
                    · rw [← hrz]; simp
            rw [hRr, two_mul]
            exact add_le_add hI1 hI2
          have hpt : ∀ p : ℝ, ∀ q : ℕ → ℝ, 0 ≤ p → (∀ k, 0 ≤ q k) → ∀ v,
              ENNReal.ofReal (opqRevenue pessValue p q v) ≤
                (B p).indicator (fun _ => ENNReal.ofReal p) v +
                  ∫⁻ t in Set.Ioo 0 p, (A t).indicator 1 v := by
            intro p q hp hq v
            unfold opqRevenue menuRevenue
            dsimp only
            split_ifs with h
            · obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup' h (opqPrice p q)
              rw [hSeq]
              simp only [Finset.mem_filter, opqOptions, Finset.mem_univ, true_and] at hS
              obtain ⟨hne, h0, hmax⟩ := hS
              by_cases hc : S.card = 1
              · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
                have hpr : opqPrice p q {i} = p := by simp [opqPrice]
                have hpv : pessValue v {i} = v i := by simp [pessValue]
                rw [hpr, hpv] at h0
                rw [hpr]
                have hvB : v ∈ B p := by rw [hB]; exact ⟨i, by linarith⟩
                rw [Set.indicator_of_mem hvB]
                exact le_add_right le_rfl
              · have hpr : opqPrice p q S = q S.card := by simp [opqPrice, hc]
                have hpv : pessValue v S = S.inf' hne v := by simp [pessValue, hne]
                rw [hpr, hpv] at h0
                rw [hpr]
                have h1 : 1 < S.card := by
                  have := hne.card_pos; omega
                obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
                have hqp : q S.card ≤ p := by
                  have := hmax {a} (Finset.singleton_nonempty a)
                  have hpr' : opqPrice p q {a} = p := by simp [opqPrice]
                  have hpv' : pessValue v {a} = v a := by simp [pessValue]
                  rw [hpr', hpv', hpr, hpv] at this
                  have := Finset.inf'_le v ha
                  linarith
                have hqa : q S.card ≤ v a := le_trans (by linarith) (Finset.inf'_le v ha)
                have hqb : q S.card ≤ v b := le_trans (by linarith) (Finset.inf'_le v hb)
                refine le_add_left ?_
                calc ENNReal.ofReal (q S.card) = ∫⁻ t in Set.Ioo 0 (q S.card), 1 := by
                      simp [Real.volume_Ioo]
                  _ = ∫⁻ t in Set.Ioo 0 (q S.card), (A t).indicator 1 v := by
                      apply setLIntegral_congr_fun measurableSet_Ioo
                      intro t ht
                      have : v ∈ A t := by
                        rw [hA]; exact ⟨a, b, hab, by linarith [ht.2], by linarith [ht.2]⟩
                      simp [Set.indicator_of_mem this]
                  _ ≤ ∫⁻ t in Set.Ioo 0 p, (A t).indicator 1 v :=
                      lintegral_mono_set (Set.Ioo_subset_Ioo_right hqp)
            · simp
          have hP : ∀ (p : ℝ) (q : ℕ → ℝ), 0 ≤ p → (∀ k, 0 ≤ q k) →
              (∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ) ≤ 3 * optSP μ := by
            intro p q hp hq
            calc ∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ
                ≤ ∫⁻ v, ((B p).indicator (fun _ => ENNReal.ofReal p) v +
                    ∫⁻ t in Set.Ioo 0 p, (A t).indicator 1 v) ∂μ := lintegral_mono (hpt p q hp hq)
              _ = ENNReal.ofReal p * μ (B p) + ∫⁻ t in Set.Ioo 0 p, μ (A t) := by
                  rw [lintegral_add_left ((measurable_const.indicator (hBm p))),
                    lintegral_indicator_const (hBm p)]
                  congr 1
                  rw [lintegral_lintegral_swap]
                  · apply lintegral_congr; intro t
                    exact lintegral_indicator_one (hAm t)
                  · have : Function.uncurry (fun v t => (A t).indicator (1 : (Fin N → ℝ) → ENNReal) v)
                        = {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2}.indicator 1 := by
                      rfl
                    rw [this]
                    exact (measurable_one.indicator hCm).aemeasurable
              _ ≤ optSP μ + 2 * optSP μ := by
                  gcongr
                  · exact hSP p hp
                  · exact le_trans (lintegral_mono_set Set.Ioo_subset_Ioi_self) hint
              _ = 3 * optSP μ := by ring
          have hR : ∀ (p : ℝ) (q : ℕ → ℝ), 0 ≤ p → (∀ k, 0 ≤ q k) →
              (∫⁻ v, ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ) ≤
                ENNReal.ofReal (4 - 2 / (N : ℝ)) * optSP μ := by
            intro p q hp hq
            have hpq : 0 ≤ p ∧ ∀ k, 0 ≤ q k := ⟨hp, hq⟩
            have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
            obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℝ, σ = fun k => if k ≤ N then 1 / (k : ℝ) else 0 := ⟨_, rfl⟩
            obtain ⟨price, hprice⟩ : ∃ price : ℕ → ℝ, price = fun k => if k = 1 then p else q k :=
              ⟨_, rfl⟩
            obtain ⟨fam, hfam⟩ : ∃ fam : Fin N → ℕ → Finset (Finset (Fin N)),
                fam = fun i k => Finset.univ.filter (fun S => i ∈ S ∧ S.card = k) := ⟨_, rfl⟩
            obtain ⟨Bs, hBs⟩ : ∃ Bs : Fin N → (Fin N → ℝ) → ℕ → ℝ,
                Bs = fun i v k => if h : (fam i k).Nonempty then
                  (fam i k).sup' h (fun S => ∑ j ∈ S.erase i, v j) else 0 := ⟨_, rfl⟩
            obtain ⟨cc, hcc⟩ : ∃ cc : Fin N → (Fin N → ℝ) → ℕ → ℝ,
                cc = fun i v k => if k ≤ N then price k - Bs i v k / k else 0 := ⟨_, rfl⟩
            have hσanti : StrictAntiOn σ (Set.Icc 1 (N+1)) := by
              intro a ha b hb hab
              simp only [Set.mem_Icc] at ha hb
              have hapos : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
              have haN : a ≤ N := by omega
              by_cases hbN : b ≤ N
              · simp only [hσ, haN, hbN, ↓reduceIte]
                exact one_div_lt_one_div_of_lt hapos (by exact_mod_cast hab)
              · simp only [hσ, haN, hbN, ↓reduceIte]
                positivity
            have hσN1 : σ (N+1) = 0 := by simp [hσ]
            have hC' : ∀ c : ℕ → ℝ, ∃ θ : ℕ → ℝ, c (N+1) = 0 → ∀ u ∈ Finset.Icc 1 (N+1), ∀ x : ℝ,
                (∀ v ∈ Finset.Icc 1 (N+1), σ v * x - c v ≤ σ u * x - c u) →
                c u ≤ ∑ t ∈ Finset.Ico u (N+1), (σ t - σ (t+1)) * θ t ∧
                  ∀ t ∈ Finset.Ico u (N+1), θ t ≤ x := by
              intro c
              by_cases hc : c (N+1) = 0
              · obtain ⟨θ, hθ⟩ := hCC σ hσanti hσN1 c hc
                exact ⟨θ, fun _ => hθ⟩
              · exact ⟨fun _ => 0, fun h => absurd h hc⟩
            obtain ⟨θ, hθ⟩ : ∃ θ : Fin N → (Fin N → ℝ) → ℕ → ℝ,
                θ = fun i v => Classical.choose (hC' (cc i v)) := ⟨_, rfl⟩
            obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun t => max 0 (σ t - σ (t+1)) := ⟨_, rfl⟩
            have hpt2 := hPP p q hp hq A hA σ hσ price hprice fam hfam Bs hBs cc hcc hC' θ hθ w hw
            have hdnn' : ∀ t, 1 ≤ t → t ≤ N → 0 ≤ σ t - σ (t+1) := by
              intro t h1 h2
              have := hσanti (show t ∈ Set.Icc 1 (N+1) by simp; omega)
                (show t+1 ∈ Set.Icc 1 (N+1) by simp; omega) (by omega)
              linarith
            have hw0 : ∀ t, 0 ≤ w t := fun t => by rw [hw]; exact le_max_left _ _
            have tele : ∀ n, ∑ t ∈ Finset.Icc 1 n, (σ t - σ (t+1)) = σ 1 - σ (n+1) := by
              intro n
              induction n with
              | zero => simp
              | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
            have hwt : ∀ t ∈ Finset.Icc 1 N, w t = σ t - σ (t+1) := by
              intro t ht
              simp only [Finset.mem_Icc] at ht
              rw [hw]; exact max_eq_right (hdnn' t ht.1 ht.2)
            have hw1 : ∑ t ∈ Finset.Icc 1 N, w t = 1 := by
              rw [Finset.sum_congr rfl hwt, tele, hσN1]
              simp [hσ, show 1 ≤ N by omega]
            have hBs' : ∀ i v x k, Bs i (Function.update v i x) k = Bs i v k := by
              intro i v x k
              simp only [hBs]
              split_ifs with h
              · congr 1
                funext S
                apply Finset.sum_congr rfl
                intro j hj
                exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
              · rfl
            have hθ' : ∀ i v x t, θ i (Function.update v i x) t = θ i v t := by
              intro i v x t
              have : cc i (Function.update v i x) = cc i v := by
                funext k; simp only [hcc, hBs']
              simp only [hθ]; rw [this]
            have hΦ := hFF (optSP μ) hKK w hw0 hw1 θ hθ'
            have hmA : Measurable (fun v : Fin N → ℝ =>
                ∫⁻ t in Set.Ioi 0, (A t).indicator (1 : (Fin N → ℝ) → ENNReal) v) := by
              have hf : Measurable (Function.uncurry
                  (fun v t => (A t).indicator (1 : (Fin N → ℝ) → ENNReal) v)) := by
                have : Function.uncurry (fun v t => (A t).indicator (1 : (Fin N → ℝ) → ENNReal) v)
                    = {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2}.indicator 1 := rfl
                rw [this]; exact measurable_one.indicator hCm
              exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioi (0:ℝ))) hf
            have hAint : ∫⁻ v, (∫⁻ t in Set.Ioi 0, (A t).indicator 1 v) ∂μ ≤ 2 * optSP μ := by
              rw [lintegral_lintegral_swap]
              · calc ∫⁻ t in Set.Ioi 0, ∫⁻ v, (A t).indicator 1 v ∂μ
                    = ∫⁻ t in Set.Ioi 0, μ (A t) := by
                      apply lintegral_congr; intro t; exact lintegral_indicator_one (hAm t)
                  _ ≤ 2 * optSP μ := hint
              · have : Function.uncurry (fun v t => (A t).indicator (1 : (Fin N → ℝ) → ENNReal) v)
                    = {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2}.indicator 1 := rfl
                rw [this]
                exact (measurable_one.indicator hCm).aemeasurable
            have hN1' : (0:ℝ) ≤ 1 - 1 / (N:ℝ) := by
              have : 1 / (N:ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact_mod_cast (by omega : 1 ≤ N)
              linarith
            refine le_trans (lintegral_mono hpt2) ?_
            rw [lintegral_add_left (hmA.const_mul _), lintegral_const_mul _ hmA]
            calc _ ≤ ENNReal.ofReal (1 - 1 / (N:ℝ)) * (2 * optSP μ) + 2 * optSP μ :=
                  add_le_add (by gcongr) hΦ
              _ = ENNReal.ofReal (4 - 2 / (N : ℝ)) * optSP μ := by
                  have e : (4 - 2 / (N:ℝ)) = 2 * (1 - 1 / (N:ℝ)) + 2 := by ring
                  rw [e, ENNReal.ofReal_add (by linarith) (by norm_num),
                    ENNReal.ofReal_mul (by norm_num)]
                  simp only [ENNReal.ofReal_ofNat]
                  ring
          obtain ⟨hα0, hα1⟩ := hα
          have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
          have hc : (0 : ℝ) ≤ 4 - 2 / (N : ℝ) := by
            have : 2 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
            linarith
          unfold optOPQ
          refine iSup_le fun p => iSup_le fun q => iSup_le fun hpq => ?_
          unfold expOPQ
          have h1 := hP p q hpq.1 hpq.2
          have h2 := hR p q hpq.1 hpq.2
          calc ENNReal.ofReal α * (∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ) +
                ENNReal.ofReal (1 - α) * (∫⁻ v, ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ)
              ≤ ENNReal.ofReal α * (3 * optSP μ) +
                ENNReal.ofReal (1 - α) * (ENNReal.ofReal (4 - 2 / (N : ℝ)) * optSP μ) := by
                gcongr
            _ = (ENNReal.ofReal (α * 3) + ENNReal.ofReal ((1 - α) * (4 - 2 / (N : ℝ)))) * optSP μ := by
                rw [ENNReal.ofReal_mul hα0, ENNReal.ofReal_mul (by linarith)]
                simp only [ENNReal.ofReal_ofNat]
                ring
            _ = ENNReal.ofReal (3 + (1 - α) * (1 - 2 / (N : ℝ))) * optSP μ := by
                rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) hc)]
                congr 2
                ring
