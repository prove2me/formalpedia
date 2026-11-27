-- Prove2me | solution 1 for RobustInventory.SingleStation.Supplement.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:50.284613+00:00
-- url     : https://prove2.me/submissions/8fbc73b8-946e-4be3-b571-179637233e7e

import Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkCap

open RobustInventory
open RobustInventory.SingleStation
open RobustInventory.SingleStation.Supplement

/-- Theorem 4.3, p. 159: with link capacities (36) and echelon capacities (37), an order array is
the order part of an optimal solution of the robust network problem iff it is optimal for the
nominal network with the modified demands (34), the echelon capacities
`C'_k(t+1) = C_k - (2p_k/(p_k+h_k)) ∑_{s ∈ O(k)} A_s(t)` and the same link capacities. -/
theorem solution (G : Network) (d : Fin G.N → WithTop ℝ) (Cap : Fin G.N → ℝ)
    (D : Fin G.N → ℕ → ℝ) :
    (∃ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ),
      G.IsRobustCapOptimal d Cap D Y q r) ↔
      G.IsModifiedCapOptimal d Cap D := by
        classical
        have hpt : ∀ (w : ℕ → ℝ) (gt : ℝ) (t : ℕ) (qv : ℝ) (rv z : ℕ → ℝ), 0 ≤ qv →
            (∀ τ ≤ t, 0 ≤ rv τ ∧ w τ ≤ qv + rv τ) →
            ((∀ τ ≤ t, 0 ≤ z τ ∧ z τ ≤ 1) ∧ ∑ τ ∈ Finset.range (t+1), z τ ≤ gt) →
            ∑ τ ∈ Finset.range (t+1), w τ * z τ ≤ qv * gt + ∑ τ ∈ Finset.range (t+1), rv τ := by
          intro w gt t qv rv z hq hr hzz
          obtain ⟨hz, hzs⟩ := hzz
          calc ∑ τ ∈ Finset.range (t+1), w τ * z τ
              ≤ ∑ τ ∈ Finset.range (t+1), (qv * z τ + rv τ) := by
                apply Finset.sum_le_sum; intro τ hτ
                have hτ' : τ ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hτ)
                obtain ⟨h1, h2⟩ := hr τ hτ'
                obtain ⟨h3, h4⟩ := hz τ hτ'
                nlinarith
            _ = qv * ∑ τ ∈ Finset.range (t+1), z τ + ∑ τ ∈ Finset.range (t+1), rv τ := by
                rw [Finset.sum_add_distrib, Finset.mul_sum]
            _ ≤ qv * gt + ∑ τ ∈ Finset.range (t+1), rv τ := by
                have := mul_le_mul_of_nonneg_left hzs hq
                linarith
        have hweak : ∀ (w g : ℕ → ℝ) (t : ℕ) (qv : ℝ) (rv : ℕ → ℝ), 0 ≤ g t → 0 ≤ qv →
            (∀ τ ≤ t, 0 ≤ rv τ ∧ w τ ≤ qv + rv τ) →
            deviationValue w g t ≤ qv * g t + ∑ τ ∈ Finset.range (t+1), rv τ := by
          intro w g t qv rv hg hq hr
          unfold deviationValue
          apply csSup_le
          · exact ⟨_, fun _ => 0, ⟨fun τ _ => ⟨le_rfl, zero_le_one⟩, by simpa using hg⟩, rfl⟩
          · rintro v ⟨z, hz, rfl⟩
            exact hpt w (g t) t qv rv z hq hr hz
        have hstrong : ∀ (w g : ℕ → ℝ) (t : ℕ), (∀ τ, 0 ≤ w τ) → 0 ≤ g t →
            ∃ (qv : ℝ) (rv : ℕ → ℝ), 0 ≤ qv ∧ (∀ τ ≤ t, 0 ≤ rv τ ∧ w τ ≤ qv + rv τ) ∧
              qv * g t + ∑ τ ∈ Finset.range (t+1), rv τ ≤ deviationValue w g t := by
          intro w g t hw hg
          let Q : Finset ℝ := insert 0 ((Finset.range (t+1)).image w)
          let a : ℝ → ℕ := fun q => ((Finset.range (t+1)).filter (fun τ => q < w τ)).card
          have hQne : Q.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
          have hQnn : ∀ q ∈ Q, 0 ≤ q := by
            intro q hq
            rcases Finset.mem_insert.1 hq with h | h
            · rw [h]
            · obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 h; exact hw τ
          have hwQ : ∀ τ ∈ Finset.range (t+1), w τ ∈ Q := fun τ hτ =>
            Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hτ)
          let S := Q.filter (fun q => (a q : ℝ) ≤ g t)
          have hSne : S.Nonempty := by
            refine ⟨Q.max' hQne, Finset.mem_filter.2 ⟨Finset.max'_mem _ _, ?_⟩⟩
            have : a (Q.max' hQne) = 0 := by
              simp only [a, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro τ hτ
              exact not_lt.2 (Finset.le_max' _ _ (hwQ τ hτ))
            rw [this]; simpa using hg
          let qs := S.min' hSne
          have hqsS : qs ∈ S := Finset.min'_mem _ _
          have hqsQ : qs ∈ Q := (Finset.mem_filter.1 hqsS).1
          have hqsa : (a qs : ℝ) ≤ g t := (Finset.mem_filter.1 hqsS).2
          have hqs0 : 0 ≤ qs := hQnn _ hqsQ
          let b : ℕ := ((Finset.range (t+1)).filter (fun τ => w τ = qs)).card
          have hab : qs ≠ 0 → g t ≤ (a qs : ℝ) + b := by
            intro hne
            have hpos : 0 < qs := lt_of_le_of_ne hqs0 (Ne.symm hne)
            let L := Q.filter (fun q => q < qs)
            have hLne : L.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hpos⟩⟩
            have hq2L : L.max' hLne ∈ L := Finset.max'_mem _ _
            have hq2Q : L.max' hLne ∈ Q := (Finset.mem_filter.1 hq2L).1
            have hq2lt : L.max' hLne < qs := (Finset.mem_filter.1 hq2L).2
            have hq2S : L.max' hLne ∉ S := by
              intro h; exact absurd (Finset.min'_le _ _ h) (not_le.2 hq2lt)
            have hga : g t < a (L.max' hLne) := by
              by_contra hc; exact hq2S (Finset.mem_filter.2 ⟨hq2Q, not_lt.1 hc⟩)
            have hsub : (Finset.range (t+1)).filter (fun τ => L.max' hLne < w τ) ⊆
                (Finset.range (t+1)).filter (fun τ => qs < w τ) ∪
                  (Finset.range (t+1)).filter (fun τ => w τ = qs) := by
              intro τ hτ
              rw [Finset.mem_filter] at hτ
              rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
              rcases lt_trichotomy (w τ) qs with h | h | h
              · exfalso
                have : w τ ∈ L := Finset.mem_filter.2 ⟨hwQ τ hτ.1, h⟩
                exact absurd (Finset.le_max' _ _ this) (not_le.2 hτ.2)
              · exact Or.inr ⟨hτ.1, h⟩
              · exact Or.inl ⟨hτ.1, h⟩
            have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
            have h2 : (a (L.max' hLne) : ℝ) ≤ a qs + b := by exact_mod_cast h1
            linarith
          let θ : ℝ := min 1 ((g t - a qs) / b)
          let z : ℕ → ℝ := fun τ => (if qs < w τ then 1 else 0) + (if w τ = qs then θ else 0)
          refine ⟨qs, fun τ => max (w τ - qs) 0, hqs0,
            fun τ _ => ⟨le_max_right _ _, by linarith [le_max_left (w τ - qs) 0]⟩, ?_⟩
          have hθ0 : 0 ≤ θ := le_min zero_le_one (div_nonneg (by linarith) (Nat.cast_nonneg _))
          have hθ1 : θ ≤ 1 := min_le_left _ _
          have hbθ : (b : ℝ) * θ ≤ g t - a qs := by
            rcases Nat.eq_zero_or_pos b with hb | hb
            · rw [hb]; simp only [Nat.cast_zero, zero_mul]; linarith
            · have hbr : (0:ℝ) < b := by exact_mod_cast hb
              calc (b:ℝ) * θ ≤ b * ((g t - a qs) / b) :=
                    mul_le_mul_of_nonneg_left (min_le_right _ _) hbr.le
                _ = g t - a qs := by field_simp
          have hsumz : ∑ τ ∈ Finset.range (t+1), z τ = a qs + b * θ := by
            simp only [z, Finset.sum_add_distrib, Finset.sum_boole]
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hqz : qs * ∑ τ ∈ Finset.range (t+1), z τ = qs * g t := by
            by_cases h0 : qs = 0
            · rw [h0, zero_mul, zero_mul]
            · have h1 := hab h0
              congr 1
              rw [hsumz]
              rcases Nat.eq_zero_or_pos b with hb | hb
              · rw [hb] at h1 ⊢; simp only [Nat.cast_zero, zero_mul, add_zero] at h1 ⊢; linarith
              · have hbr : (0:ℝ) < b := by exact_mod_cast hb
                have : (g t - a qs)/b ≤ 1 := by rw [div_le_one hbr]; linarith
                simp only [θ, min_eq_right this]; field_simp; ring
          have hzfeas : ((∀ τ ≤ t, 0 ≤ z τ ∧ z τ ≤ 1) ∧ ∑ τ ∈ Finset.range (t+1), z τ ≤ g t) := by
            refine ⟨fun τ _ => ?_, ?_⟩
            · rcases lt_trichotomy (w τ) qs with h | h | h
              · simp only [z, if_neg (not_lt.2 h.le), if_neg h.ne]; norm_num
              · simp only [z, h, lt_irrefl, if_false, if_true]; constructor <;> linarith
              · simp only [z, if_pos h, if_neg h.ne']; norm_num
            · rw [hsumz]; linarith
          have hval : qs * g t + ∑ τ ∈ Finset.range (t+1), max (w τ - qs) 0 =
              ∑ τ ∈ Finset.range (t+1), w τ * z τ := by
            have hp : ∀ τ, w τ * z τ = max (w τ - qs) 0 + qs * z τ := by
              intro τ
              rcases lt_trichotomy (w τ) qs with h | h | h
              · simp only [z, if_neg (not_lt.2 h.le), if_neg h.ne]
                rw [max_eq_right (by linarith)]; ring
              · simp only [z, h, lt_irrefl, if_false, if_true]; rw [sub_self, max_self]; ring
              · simp only [z, if_pos h, if_neg h.ne']
                rw [max_eq_left (by linarith)]; ring
            rw [Finset.sum_congr rfl (fun τ _ => hp τ), Finset.sum_add_distrib, ← Finset.mul_sum, hqz]
            ring
          show _ ≤ sSup _
          rw [hval]
          apply le_csSup
          · refine ⟨qs * g t + ∑ τ ∈ Finset.range (t+1), max (w τ - qs) 0, ?_⟩
            rintro v ⟨z', hz', rfl⟩
            exact hpt w (g t) t qs _ z' hqs0
              (fun τ _ => ⟨le_max_right _ _, by linarith [le_max_left (w τ - qs) 0]⟩) hz'
          · exact ⟨z, hzfeas, rfl⟩
        have hΓnn : ∀ s, G.tree.IsSink s → ∀ t, 0 ≤ G.Γ s t := by
          intro s hs t
          induction t with
          | zero => exact G.hΓ0 s hs
          | succ t ih => exact ih.trans (G.hΓmono s hs t)
        have hdual : ∀ s t, ∃ (qv : ℝ) (rv : ℕ → ℝ), G.tree.IsSink s →
            (0 ≤ qv ∧ ∀ τ ≤ t, 0 ≤ rv τ ∧ G.What s τ ≤ qv + rv τ) ∧
            qv * G.Γ s t + ∑ τ ∈ Finset.range (t+1), rv τ = G.A s t := by
          intro s t
          by_cases hs : G.tree.IsSink s
          · obtain ⟨qv, rv, h1, h2, h3⟩ :=
              hstrong (G.What s) (G.Γ s) t (G.hWhat s hs) (hΓnn s hs t)
            exact ⟨qv, rv, fun _ => ⟨⟨h1, h2⟩,
              le_antisymm h3 (hweak _ _ _ _ _ (hΓnn s hs t) h1 h2)⟩⟩
          · exact ⟨0, fun _ => 0, fun h => absurd h hs⟩
        choose qf rf hqr using hdual
        have hsinkmem : ∀ k s, s ∈ G.tree.sinksBelow k → G.tree.IsSink s := by
          intro k s hs
          unfold SupplyTree.sinksBelow at hs
          exact (Finset.mem_filter.1 hs).2.1
        have hprot_ge : ∀ (q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ),
            (∀ s, G.tree.IsSink s → ∀ t < G.T,
              0 ≤ q s t ∧ ∀ τ ≤ t, 0 ≤ r s τ t ∧ G.What s τ ≤ q s t + r s τ t) →
            ∀ k, ∀ t < G.T, ∑ s ∈ G.tree.sinksBelow k, G.A s t ≤ G.protection q r k t := by
          intro q r hq k t ht
          unfold Network.protection
          apply Finset.sum_le_sum
          intro s hs
          have hs' := hsinkmem k s hs
          obtain ⟨h1, h2⟩ := hq s hs' t ht
          exact hweak (G.What s) (G.Γ s) t (q s t) (fun τ => r s τ t) (hΓnn s hs' t) h1 h2
        have hstar_feas : ∀ s, G.tree.IsSink s → ∀ t < G.T, 0 ≤ qf s t ∧
            ∀ τ ≤ t, 0 ≤ (fun s τ t => rf s t τ) s τ t ∧
              G.What s τ ≤ qf s t + (fun s τ t => rf s t τ) s τ t :=
          fun s hs t _ => (hqr s t hs).1
        have hprot_eq : ∀ k t, G.protection qf (fun s τ t => rf s t τ) k t =
            ∑ s ∈ G.tree.sinksBelow k, G.A s t := by
          intro k t
          unfold Network.protection
          apply Finset.sum_congr rfl
          intro s hs
          exact (hqr s t (hsinkmem k s hs)).2
        have htel : ∀ s t, ∑ τ ∈ Finset.range (t+1), (G.A s τ - G.Aprev s τ) = G.A s t := by
          intro s t
          calc ∑ τ ∈ Finset.range (t+1), (G.A s τ - G.Aprev s τ)
              = ∑ τ ∈ Finset.range (t+1), (G.Aprev s (τ+1) - G.Aprev s τ) := rfl
            _ = G.Aprev s (t+1) - G.Aprev s 0 := Finset.sum_range_sub _ _
            _ = G.A s t := by simp [Network.Aprev]
        have hXmod : ∀ (D : Fin G.N → ℕ → ℝ) k t, G.Xmod D k (t+1) = G.Xbar D k (t+1) -
            (G.p k - G.h k) / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t := by
          intro D k t
          have hstep : ∀ τ, (D k τ - ∑ s ∈ G.tree.sinksBelow k, G.Wmod s k τ) =
              (D k τ - ∑ s ∈ G.tree.sinksBelow k, G.Wbar s τ) -
                (G.p k - G.h k) / (G.p k + G.h k) *
                  ∑ s ∈ G.tree.sinksBelow k, (G.A s τ - G.Aprev s τ) := by
            intro τ
            simp only [Network.Wmod, Finset.sum_add_distrib, ← Finset.mul_sum]
            ring
          rw [Network.Xmod, Finset.sum_congr rfl (fun τ _ => hstep τ), Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl (fun s _ => htel s t),
            Network.Xbar]
          ring
        have hmax : ∀ k (X S : ℝ), max (G.h k * (X + S)) (G.p k * (-X + S)) =
            G.R k (X - (G.p k - G.h k) / (G.p k + G.h k) * S) +
              2 * G.p k * G.h k / (G.p k + G.h k) * S := by
          intro k X S
          have hp : 0 < G.p k := (G.hc k).trans (G.hpc k)
          have hpos : 0 < G.p k + G.h k := by linarith [G.hh k]
          unfold Network.R
          rw [← max_add_add_right]
          congr 1
          · field_simp; ring
          · field_simp; ring
        let E : ℝ := ∑ t ∈ Finset.range G.T, ∑ k,
          2 * G.p k * G.h k / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t
        have hlower : ∀ (D' Y' q' : Fin G.N → ℕ → ℝ) (r' : Fin G.N → ℕ → ℕ → ℝ),
            G.RobustCapFeasible d Cap D' Y' q' r' → G.modifiedCost D' + E ≤ G.robustObjective D' Y' := by
          intro D' Y' q' r' hf
          obtain ⟨⟨_, hsk, hY⟩, _, _⟩ := hf
          unfold Network.modifiedCost Network.robustObjective
          simp only [E]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro t ht
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro k _
          have ht' := Finset.mem_range.1 ht
          have hP := hprot_ge q' r' hsk k t ht'
          obtain ⟨h1, h2⟩ := hY k t ht'
          have hp : 0 < G.p k := (G.hc k).trans (G.hpc k)
          have hh := G.hh k
          have hm := hmax k (G.Xbar D' k (t+1)) (∑ s ∈ G.tree.sinksBelow k, G.A s t)
          rw [hXmod]
          have hle : max (G.h k * (G.Xbar D' k (t+1) + ∑ s ∈ G.tree.sinksBelow k, G.A s t))
              (G.p k * (-G.Xbar D' k (t+1) + ∑ s ∈ G.tree.sinksBelow k, G.A s t)) ≤ Y' k t :=
            max_le (by nlinarith) (by nlinarith)
          linarith
        let Ys : (Fin G.N → ℕ → ℝ) → Fin G.N → ℕ → ℝ := fun D' k t =>
          max (G.h k * (G.Xbar D' k (t+1) + ∑ s ∈ G.tree.sinksBelow k, G.A s t))
            (G.p k * (-G.Xbar D' k (t+1) + ∑ s ∈ G.tree.sinksBelow k, G.A s t))
        have hconstr : ∀ D', G.ModifiedCapFeasible d Cap D' →
            G.RobustCapFeasible d Cap D' (Ys D') qf (fun s τ t => rf s t τ) ∧
              G.robustObjective D' (Ys D') = G.modifiedCost D' + E := by
          intro D' hf
          obtain ⟨hord, hlink, hcap⟩ := hf
          refine ⟨⟨⟨hord, hstar_feas, fun i t _ => ?_⟩, hlink, fun k t ht => ?_⟩, ?_⟩
          · rw [hprot_eq]
            exact ⟨le_max_left _ _, le_max_right _ _⟩
          · rw [hprot_eq]
            have h := hcap k t ht
            rw [hXmod] at h
            unfold Network.modifiedCap at h
            have hp : 0 < G.p k := (G.hc k).trans (G.hpc k)
            have hpos : 0 < G.p k + G.h k := by linarith [G.hh k]
            have e : 2 * G.p k / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t =
                (G.p k - G.h k) / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t +
                  ∑ s ∈ G.tree.sinksBelow k, G.A s t := by
              field_simp; ring
            linarith
          · unfold Network.modifiedCost Network.robustObjective
            simp only [E]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t _
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            simp only [Ys]
            rw [hmax, hXmod]
            ring
        constructor
        · rintro ⟨Y, q, r, hf, hopt⟩
          have hmf : G.ModifiedCapFeasible d Cap D := by
            obtain ⟨⟨hord, hsk, _⟩, hlink, hcap⟩ := hf
            refine ⟨hord, hlink, fun k t ht => ?_⟩
            have hP := hprot_ge q r hsk k t ht
            have h := hcap k t ht
            rw [hXmod]
            unfold Network.modifiedCap
            have hp : 0 < G.p k := (G.hc k).trans (G.hpc k)
            have hpos : 0 < G.p k + G.h k := by linarith [G.hh k]
            have e : 2 * G.p k / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t =
                (G.p k - G.h k) / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t +
                  ∑ s ∈ G.tree.sinksBelow k, G.A s t := by
              field_simp; ring
            linarith
          refine ⟨hmf, fun D' hD' => ?_⟩
          obtain ⟨hf', hobj'⟩ := hconstr D' hD'
          have h1 := hopt D' (Ys D') qf (fun s τ t => rf s t τ) hf'
          have h2 := hlower D Y q r hf
          linarith
        · rintro ⟨hmf, hopt⟩
          obtain ⟨hf, hobj⟩ := hconstr D hmf
          refine ⟨Ys D, qf, fun s τ t => rf s t τ, hf, fun D' Y' q' r' hf' => ?_⟩
          have hmf' : G.ModifiedCapFeasible d Cap D' := by
            obtain ⟨⟨hord, hsk, _⟩, hlink, hcap⟩ := hf'
            refine ⟨hord, hlink, fun k t ht => ?_⟩
            have hP := hprot_ge q' r' hsk k t ht
            have h := hcap k t ht
            rw [hXmod]
            unfold Network.modifiedCap
            have hp : 0 < G.p k := (G.hc k).trans (G.hpc k)
            have hpos : 0 < G.p k + G.h k := by linarith [G.hh k]
            have e : 2 * G.p k / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t =
                (G.p k - G.h k) / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t +
                  ∑ s ∈ G.tree.sinksBelow k, G.A s t := by
              field_simp; ring
            linarith
          have h1 := hopt D' hmf'
          have h2 := hlower D' Y' q' r' hf'
          linarith
