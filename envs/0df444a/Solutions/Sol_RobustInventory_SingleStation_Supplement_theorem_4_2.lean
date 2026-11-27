-- Prove2me | solution 1 for RobustInventory.SingleStation.Supplement.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:37.612812+00:00
-- url     : https://prove2.me/submissions/3625bf76-192e-40c2-a021-7cb7ae7161e7

import Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkRobust

open RobustInventory
open RobustInventory.SingleStation
open RobustInventory.SingleStation.Supplement

/-- Theorem 4.2, p. 158, for a tree network.
1. (b), for every feasible order array `D`: the least objective of (32) at `D` is the cost of
   `D` under the modified demands (34) plus `extraCost`.
2. (a): `D` is the order part of an optimal solution of (32) iff it is optimal for the supply
   chain in which every echelon `k` sees the demands `W'_{s,k}` at the sinks `s ∈ O(k)`.
3. (b): the optimal cost of (32) is the optimal cost of that supply chain plus `extraCost`. -/
theorem solution (G : Network) :
    (∀ D : Fin G.N → ℕ → ℝ, G.OrdersFeasible D →
      (∀ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.RobustFeasible D Y q r →
        G.modifiedCost D + G.extraCost ≤ G.robustObjective D Y) ∧
      ∃ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.RobustFeasible D Y q r ∧
        G.robustObjective D Y = G.modifiedCost D + G.extraCost) ∧
    (∀ D : Fin G.N → ℕ → ℝ,
      (∃ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.IsRobustOptimal D Y q r) ↔
        G.IsModifiedOptimal D) ∧
    ∀ (D Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ) (D' : Fin G.N → ℕ → ℝ),
      G.IsRobustOptimal D Y q r → G.IsModifiedOptimal D' →
        G.robustObjective D Y = G.modifiedCost D' + G.extraCost := by
          classical
          have LP : ∀ (w : ℕ → ℝ) (S : Finset ℕ), (∀ τ ∈ S, 0 ≤ w τ) → ∀ g : ℝ, 0 ≤ g →
              ∃ q : ℝ, ∃ z : ℕ → ℝ, 0 ≤ q ∧ (q = 0 ∨ ∃ τ ∈ S, q ≤ w τ) ∧
                (∀ τ ∈ S, 0 ≤ z τ ∧ z τ ≤ 1) ∧ ∑ τ ∈ S, z τ ≤ g ∧
                ∑ τ ∈ S, w τ * z τ = q * g + ∑ τ ∈ S, max (w τ - q) 0 := by
            intro w S
            induction S using Finset.induction_on_max_value w with
            | empty =>
              intro _ g hg
              exact ⟨0, fun _ => 0, le_refl _, Or.inl rfl, by simp, by simpa using hg, by simp⟩
            | insert m S hm hmax ih =>
              intro hw g hg
              have hne : ∀ τ ∈ S, τ ≠ m := fun τ hτ h => hm (h ▸ hτ)
              have hwm : 0 ≤ w m := hw m (Finset.mem_insert_self _ _)
              have hwS : ∀ τ ∈ S, 0 ≤ w τ := fun τ hτ => hw τ (Finset.mem_insert_of_mem hτ)
              rcases lt_or_ge g 1 with hg1 | hg1
              · refine ⟨w m, fun τ => if τ = m then g else 0, hwm,
                  Or.inr ⟨m, Finset.mem_insert_self _ _, le_refl _⟩, ?_, ?_, ?_⟩
                · intro τ _
                  dsimp only
                  split_ifs <;> constructor <;> linarith
                · rw [Finset.sum_insert hm]
                  rw [Finset.sum_eq_zero (fun τ hτ => by simp [hne τ hτ])]
                  simp
                · rw [Finset.sum_insert hm, Finset.sum_insert hm]
                  rw [Finset.sum_eq_zero (fun τ hτ => by simp [hne τ hτ])]
                  rw [Finset.sum_eq_zero (fun τ hτ => by have := hmax τ hτ; simp; linarith)]
                  simp
              · obtain ⟨q, z, hq0, hqS, hz, hzs, heq⟩ := ih hwS (g - 1) (by linarith)
                have hqm : q ≤ w m := by
                  rcases hqS with h | ⟨τ, hτ, h⟩
                  · rw [h]; exact hwm
                  · exact h.trans (hmax τ hτ)
                refine ⟨q, fun τ => if τ = m then 1 else z τ, hq0, ?_, ?_, ?_, ?_⟩
                · rcases hqS with h | ⟨τ, hτ, h⟩
                  · exact Or.inl h
                  · exact Or.inr ⟨τ, Finset.mem_insert_of_mem hτ, h⟩
                · intro τ hτ
                  dsimp only
                  split_ifs with h
                  · norm_num
                  · rcases Finset.mem_insert.1 hτ with h' | h'
                    · exact absurd h' h
                    · exact hz τ h'
                · rw [Finset.sum_insert hm]
                  rw [Finset.sum_congr rfl (fun τ hτ => by simp [hne τ hτ] : ∀ τ ∈ S,
                    (if τ = m then (1:ℝ) else z τ) = z τ)]
                  simp only [if_pos]
                  linarith
                · rw [Finset.sum_insert hm, Finset.sum_insert hm]
                  rw [Finset.sum_congr rfl (fun τ hτ => by simp [hne τ hτ] : ∀ τ ∈ S,
                    w τ * (if τ = m then (1:ℝ) else z τ) = w τ * z τ)]
                  rw [heq, max_eq_left (by linarith)]
                  simp; ring
          have hΓnn : ∀ s, G.tree.IsSink s → ∀ t, 0 ≤ G.Γ s t := by
            intro s hs t
            induction t with
            | zero => exact G.hΓ0 s hs
            | succ n ih => exact ih.trans (G.hΓmono s hs n)
          have PW : ∀ (s : Fin G.N) (t : ℕ) (q : ℝ) (r z : ℕ → ℝ), G.tree.IsSink s → 0 ≤ q →
              (∀ τ ≤ t, 0 ≤ r τ ∧ G.What s τ ≤ q + r τ) →
              ((∀ τ ≤ t, 0 ≤ z τ ∧ z τ ≤ 1) ∧ ∑ τ ∈ Finset.range (t + 1), z τ ≤ G.Γ s t) →
              ∑ τ ∈ Finset.range (t + 1), G.What s τ * z τ ≤
                q * G.Γ s t + ∑ τ ∈ Finset.range (t + 1), r τ := by
            intro s t q r z hs hq hr hzz
            obtain ⟨hz, hzs⟩ := hzz
            have h1 : ∑ τ ∈ Finset.range (t + 1), G.What s τ * z τ ≤
                ∑ τ ∈ Finset.range (t + 1), (q * z τ + r τ) := by
              apply Finset.sum_le_sum
              intro τ hτ
              have hτ' : τ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hτ)
              obtain ⟨hr0, hrw⟩ := hr τ hτ'
              obtain ⟨hz0, hz1⟩ := hz τ hτ'
              nlinarith [mul_nonneg (sub_nonneg.mpr hrw) hz0, mul_nonneg hr0 (sub_nonneg.mpr hz1)]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
            nlinarith [mul_le_mul_of_nonneg_left hzs hq]
          have WD : ∀ (s : Fin G.N) (t : ℕ) (q : ℝ) (r : ℕ → ℝ), G.tree.IsSink s → 0 ≤ q →
              (∀ τ ≤ t, 0 ≤ r τ ∧ G.What s τ ≤ q + r τ) →
              G.A s t ≤ q * G.Γ s t + ∑ τ ∈ Finset.range (t + 1), r τ := by
            intro s t q r hs hq hr
            unfold Network.A deviationValue
            apply csSup_le
            · exact ⟨0, fun _ => 0, ⟨fun τ _ => ⟨le_refl _, zero_le_one⟩, by simpa using hΓnn s hs t⟩,
                by simp⟩
            · rintro v ⟨z, hz, rfl⟩
              exact PW s t q r z hs hq hr hz
          have hex : ∀ (s : Fin G.N) (t : ℕ), ∃ q : ℝ, G.tree.IsSink s → 0 ≤ q ∧
              G.A s t = q * G.Γ s t + ∑ τ ∈ Finset.range (t + 1), max (G.What s τ - q) 0 := by
            intro s t
            by_cases hs : G.tree.IsSink s
            · obtain ⟨q, z, hq0, -, hz, hzs, heq⟩ := LP (G.What s) (Finset.range (t+1))
                (fun τ _ => G.hWhat s hs τ) (G.Γ s t) (hΓnn s hs t)
              have hfe : ∀ τ ≤ t, 0 ≤ max (G.What s τ - q) 0 ∧ G.What s τ ≤ q + max (G.What s τ - q) 0 :=
                fun τ _ => ⟨le_max_right _ _, by linarith [le_max_left (G.What s τ - q) 0]⟩
              refine ⟨q, fun _ => ⟨hq0, le_antisymm (WD s t q _ hs hq0 hfe) ?_⟩⟩
              rw [← heq]
              unfold Network.A deviationValue
              apply le_csSup
              · refine ⟨q * G.Γ s t + ∑ τ ∈ Finset.range (t + 1), max (G.What s τ - q) 0, ?_⟩
                rintro v ⟨z', hz', rfl⟩
                exact PW s t q _ z' hs hq0 hfe hz'
              · exact ⟨z, ⟨fun τ hτ => hz τ (Finset.mem_range.mpr (Nat.lt_succ_of_le hτ)), hzs⟩, rfl⟩
            · exact ⟨0, fun h => absurd h hs⟩
          choose qf hqf using hex
          obtain ⟨rf, hrf⟩ : ∃ rf : Fin G.N → ℕ → ℕ → ℝ, ∀ s τ t, rf s τ t = max (G.What s τ - qf s t) 0 :=
            ⟨_, fun _ _ _ => rfl⟩
          obtain ⟨P, hP⟩ : ∃ P : Fin G.N → ℕ → ℝ, ∀ i t, P i t = ∑ s ∈ G.tree.sinksBelow i, G.A s t :=
            ⟨_, fun _ _ => rfl⟩
          have hsink : ∀ i s, s ∈ G.tree.sinksBelow i → G.tree.IsSink s := by
            intro i s hs
            unfold SupplyTree.sinksBelow at hs
            exact (Finset.mem_filter.mp hs).2.1
          have hprot : ∀ i t, G.protection qf rf i t = P i t := by
            intro i t
            unfold Network.protection
            rw [hP]
            apply Finset.sum_congr rfl
            intro s hs
            simp only [hrf]
            rw [(hqf s t (hsink i s hs)).2]
          have hph : ∀ i, 0 < G.p i + G.h i := fun i => by linarith [G.hc i, G.hpc i, G.hh i]
          have hp0 : ∀ i, 0 ≤ G.p i := fun i => by linarith [G.hc i, G.hpc i]
          have htel : ∀ s t, ∑ τ ∈ Finset.range (t + 1), (G.A s τ - G.Aprev s τ) = G.A s t := by
            intro s t
            induction t with
            | zero => simp [Network.Aprev]
            | succ n ih => rw [Finset.sum_range_succ, ih]; simp [Network.Aprev]
          have hXmod : ∀ D i t, G.Xmod D i (t + 1) =
              G.Xbar D i (t + 1) - (G.p i - G.h i) / (G.p i + G.h i) * P i t := by
            intro D i t
            have key : ∑ τ ∈ Finset.range (t + 1), ∑ s ∈ G.tree.sinksBelow i,
                (G.p i - G.h i) / (G.p i + G.h i) * (G.A s τ - G.Aprev s τ) =
                (G.p i - G.h i) / (G.p i + G.h i) * P i t := by
              rw [Finset.sum_comm, hP, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              rw [← Finset.mul_sum, htel]
            have hτ : ∀ τ, (D i τ - ∑ s ∈ G.tree.sinksBelow i, G.Wmod s i τ) =
                (D i τ - ∑ s ∈ G.tree.sinksBelow i, G.Wbar s τ) - ∑ s ∈ G.tree.sinksBelow i,
                (G.p i - G.h i) / (G.p i + G.h i) * (G.A s τ - G.Aprev s τ) := by
              intro τ
              unfold Network.Wmod
              rw [Finset.sum_add_distrib]; ring
            unfold Network.Xmod Network.Xbar
            rw [Finset.sum_congr rfl (fun τ _ => hτ τ), Finset.sum_sub_distrib, key]
            ring
          have KI : ∀ D i t, max (G.h i * (G.Xbar D i (t + 1) + P i t))
              (G.p i * (-G.Xbar D i (t + 1) + P i t)) =
              G.R i (G.Xmod D i (t + 1)) + 2 * G.p i * G.h i / (G.p i + G.h i) * P i t := by
            intro D i t
            rw [hXmod]
            unfold Network.R
            have hne : G.p i + G.h i ≠ 0 := (hph i).ne'
            have e1 : G.h i * (G.Xbar D i (t + 1) + P i t) =
                G.h i * (G.Xbar D i (t + 1) - (G.p i - G.h i) / (G.p i + G.h i) * P i t) +
                2 * G.p i * G.h i / (G.p i + G.h i) * P i t := by
              field_simp; ring
            have e2 : G.p i * (-G.Xbar D i (t + 1) + P i t) =
                -(G.p i * (G.Xbar D i (t + 1) - (G.p i - G.h i) / (G.p i + G.h i) * P i t)) +
                2 * G.p i * G.h i / (G.p i + G.h i) * P i t := by
              field_simp; ring
            rw [e1, e2, max_add_add_right]
          obtain ⟨Yf, hYf⟩ : ∃ Yf : (Fin G.N → ℕ → ℝ) → Fin G.N → ℕ → ℝ, ∀ D i t,
              Yf D i t = max (G.h i * (G.Xbar D i (t + 1) + P i t))
                (G.p i * (-G.Xbar D i (t + 1) + P i t)) := ⟨_, fun _ _ _ => rfl⟩
          have EqD : ∀ D, G.robustObjective D (Yf D) = G.modifiedCost D + G.extraCost := by
            intro D
            unfold Network.robustObjective Network.modifiedCost Network.extraCost
            have h1 : ∑ t ∈ Finset.range G.T, ∑ i, (G.C i (D i t) + Yf D i t) =
                ∑ t ∈ Finset.range G.T, ∑ i, (G.C i (D i t) + G.R i (G.Xmod D i (t + 1))) +
                ∑ t ∈ Finset.range G.T, ∑ i, 2 * G.p i * G.h i / (G.p i + G.h i) * P i t := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro t _
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i _
              rw [hYf, KI]; ring
            rw [h1]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [hP]
          have LB : ∀ D Y q r, G.RobustFeasible D Y q r →
              G.robustObjective D (Yf D) ≤ G.robustObjective D Y := by
            intro D Y q r hF
            unfold Network.robustObjective
            apply Finset.sum_le_sum
            intro t ht
            have ht' : t < G.T := Finset.mem_range.mp ht
            apply Finset.sum_le_sum
            intro i _
            apply add_le_add_right
            have hpr : P i t ≤ G.protection q r i t := by
              rw [hP]
              unfold Network.protection
              apply Finset.sum_le_sum
              intro s hs
              have hss := hsink i s hs
              obtain ⟨hq0, hr⟩ := hF.2.1 s hss t ht'
              exact WD s t (q s t) (fun τ => r s τ t) hss hq0 hr
            obtain ⟨hY1, hY2⟩ := hF.2.2 i t ht'
            rw [hYf]
            apply max_le
            · exact le_trans (mul_le_mul_of_nonneg_left (by linarith) (G.hh i)) hY1
            · exact le_trans (mul_le_mul_of_nonneg_left (by linarith) (hp0 i)) hY2
          have P1 : ∀ D : Fin G.N → ℕ → ℝ, G.OrdersFeasible D →
              (∀ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.RobustFeasible D Y q r →
                G.modifiedCost D + G.extraCost ≤ G.robustObjective D Y) ∧
              ∃ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.RobustFeasible D Y q r ∧
                G.robustObjective D Y = G.modifiedCost D + G.extraCost := by
            intro D hD
            refine ⟨fun Y q r hF => (EqD D) ▸ LB D Y q r hF, Yf D, qf, rf, ?_, EqD D⟩
            refine ⟨hD, fun s hs t _ => ⟨(hqf s t hs).1, fun τ _ => ⟨?_, ?_⟩⟩, fun i t _ => ⟨?_, ?_⟩⟩
            · rw [hrf]; exact le_max_right _ _
            · rw [hrf]; linarith [le_max_left (G.What s τ - qf s t) 0]
            · rw [hYf, hprot]; exact le_max_left _ _
            · rw [hYf, hprot]; exact le_max_right _ _
          refine ⟨P1, ?_, ?_⟩
          · intro D
            constructor
            · rintro ⟨Y, q, r, hF, hopt⟩
              refine ⟨hF.1, fun D' hD' => ?_⟩
              obtain ⟨Y', q', r', hF', heq'⟩ := (P1 D' hD').2
              have h1 := (P1 D hF.1).1 Y q r hF
              have h2 := hopt D' Y' q' r' hF'
              linarith
            · rintro ⟨hD, hopt⟩
              obtain ⟨Y, q, r, hF, heq⟩ := (P1 D hD).2
              refine ⟨Y, q, r, hF, fun D' Y' q' r' hF' => ?_⟩
              have h1 := (P1 D' hF'.1).1 Y' q' r' hF'
              have h2 := hopt D' hF'.1
              linarith
          · intro D Y q r D' hR hM
            obtain ⟨Y', q', r', hF', heq'⟩ := (P1 D' hM.1).2
            have h1 := hR.2 D' Y' q' r' hF'
            have h2 := (P1 D hR.1.1).1 Y q r hR.1
            have h3 := hM.2 D hR.1.1
            linarith
