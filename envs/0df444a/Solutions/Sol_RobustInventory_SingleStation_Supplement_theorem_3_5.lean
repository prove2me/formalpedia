-- Prove2me | solution 1 for RobustInventory.SingleStation.Supplement.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:26.616391+00:00
-- url     : https://prove2.me/submissions/ec40a7f1-4d1a-4445-8e22-c3fa9863d556

import Definitions.Def_RobustInventory_SingleStation_Supplement_InventoryCap

open RobustInventory
open RobustInventory.SingleStation
open RobustInventory.SingleStation.Supplement

/-- Theorem 3.5, p. 156: when stock can only be stored up to `Cap` (time `0` included), an order
sequence is the order part of an optimal solution of (14) with (26) iff it is optimal for the
nominal problem with demand `w'`, capacity `Cap` at time `0` and `Cap - (2p/(p+h)) A_k` at
time `k + 1`. -/
theorem solution (M : Model) (Cap : ℝ) (hx0 : M.x0 ≤ Cap) (u : ℕ → ℝ) :
    (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), IsRobustCapOptimal M Cap u y q r) ↔
      IsNominalCapOptimal M Cap u := by
        classical
        have hΓnn : ∀ k, 0 ≤ M.Γ k := by
          intro k; induction k with
          | zero => exact M.hΓ0
          | succ k ih => exact ih.trans (M.hΓmono k)
        have hwe : ∀ k q (r : ℕ → ℝ), M.LP13DualFeasible k q r → ∀ z, M.LP13Feasible k z →
            ∑ i ∈ Finset.range (k+1), M.what i * z i ≤ q * M.Γ k + ∑ i ∈ Finset.range (k+1), r i := by
          intro k q r ⟨hq, hr⟩ z ⟨hz1, hz2⟩
          have : ∀ i ∈ Finset.range (k+1), M.what i * z i ≤ q * z i + r i := by
            intro i hi
            have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            obtain ⟨hr0, hrw⟩ := hr i hik
            obtain ⟨hz0, hz1'⟩ := hz1 i hik
            nlinarith [mul_le_mul_of_nonneg_right hrw hz0, mul_le_mul_of_nonneg_left hz1' hr0]
          calc _ ≤ ∑ i ∈ Finset.range (k+1), (q * z i + r i) := Finset.sum_le_sum this
            _ = q * ∑ i ∈ Finset.range (k+1), z i + ∑ i ∈ Finset.range (k+1), r i := by
                rw [Finset.sum_add_distrib, Finset.mul_sum]
            _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hz2 hq]
        have hne : ∀ k, {v : ℝ | ∃ z : ℕ → ℝ, M.LP13Feasible k z ∧
            v = ∑ i ∈ Finset.range (k + 1), M.what i * z i}.Nonempty := fun k =>
          ⟨_, 0, ⟨fun i _ => ⟨le_refl _, zero_le_one⟩, by simp [hΓnn k]⟩, rfl⟩
        have hweak : ∀ k q (r : ℕ → ℝ), M.LP13DualFeasible k q r →
            M.A k ≤ q * M.Γ k + ∑ i ∈ Finset.range (k+1), r i := by
          intro k q r hqr
          unfold Model.A
          apply csSup_le (hne k)
          rintro v ⟨z, hz, rfl⟩
          exact hwe k q r hqr z hz
        have hdual : ∀ k, ∃ q : ℝ, ∃ r : ℕ → ℝ, M.LP13DualFeasible k q r ∧
            q * M.Γ k + ∑ i ∈ Finset.range (k+1), r i = M.A k := by
          intro k
          obtain ⟨I, hI⟩ : ∃ I, I = Finset.range (k+1) := ⟨_, rfl⟩
          rw [← hI]
          obtain ⟨cnt, hcnt⟩ : ∃ cnt : ℝ → ℝ, ∀ q, cnt q = ∑ i ∈ I, if q < M.what i then (1:ℝ) else 0 :=
            ⟨_, fun _ => rfl⟩
          obtain ⟨Q, hQ⟩ : ∃ Q : Finset ℝ, Q = insert 0 (I.image M.what) := ⟨_, rfl⟩
          have hQ0 : (0:ℝ) ∈ Q := by rw [hQ]; exact Finset.mem_insert_self _ _
          have hQw : ∀ i ∈ I, M.what i ∈ Q := fun i hi => by
            rw [hQ]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)
          have hQnn : ∀ q ∈ Q, 0 ≤ q := by
            intro q hq; rw [hQ, Finset.mem_insert, Finset.mem_image] at hq
            rcases hq with h | ⟨i, _, rfl⟩
            · rw [h]
            · exact M.hwhat i
          obtain ⟨P, hP⟩ : ∃ P : Finset ℝ, P = Q.filter (fun q => cnt q ≤ M.Γ k) := ⟨_, rfl⟩
          have hPne : P.Nonempty := by
            refine ⟨Q.max' ⟨0, hQ0⟩, ?_⟩
            rw [hP, Finset.mem_filter]
            refine ⟨Finset.max'_mem _ _, ?_⟩
            rw [hcnt, Finset.sum_eq_zero]
            · exact hΓnn k
            · intro i hi
              rw [if_neg (not_lt.2 (Finset.le_max' _ _ (hQw i hi)))]
          obtain ⟨qs, hqs⟩ : ∃ qs, qs = P.min' hPne := ⟨_, rfl⟩
          have hqsP : qs ∈ P := hqs ▸ Finset.min'_mem _ _
          rw [hP, Finset.mem_filter] at hqsP
          obtain ⟨hqsQ, hqsc⟩ := hqsP
          have hqs0 : 0 ≤ qs := hQnn qs hqsQ
          obtain ⟨neq, hneq⟩ : ∃ neq : ℝ, neq = ∑ i ∈ I, if M.what i = qs then (1:ℝ) else 0 :=
            ⟨_, rfl⟩
          obtain ⟨θ, hθ0, hθ1, hθΓ, hθq⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ cnt qs + θ * neq ≤ M.Γ k ∧
              qs * (cnt qs + θ * neq) = qs * M.Γ k := by
            rcases eq_or_lt_of_le hqs0 with h0 | h0
            · exact ⟨0, le_refl _, zero_le_one, by simpa using hqsc, by rw [← h0]; ring⟩
            · obtain ⟨L, hL⟩ : ∃ L : Finset ℝ, L = Q.filter (fun q => q < qs) := ⟨_, rfl⟩
              have hL0 : (0:ℝ) ∈ L := by rw [hL, Finset.mem_filter]; exact ⟨hQ0, h0⟩
              obtain ⟨q2, hq2⟩ : ∃ q2, q2 = L.max' ⟨0, hL0⟩ := ⟨_, rfl⟩
              have hq2L : q2 ∈ L := hq2 ▸ Finset.max'_mem _ _
              rw [hL, Finset.mem_filter] at hq2L
              obtain ⟨hq2Q, hq2lt⟩ := hq2L
              have hq2c : M.Γ k < cnt q2 := by
                by_contra hcon; push Not at hcon
                have : q2 ∈ P := by rw [hP, Finset.mem_filter]; exact ⟨hq2Q, hcon⟩
                have := Finset.min'_le P q2 this
                rw [← hqs] at this; linarith
              have hsub : ∀ i ∈ I, q2 < M.what i → qs ≤ M.what i := by
                intro i hi hlt
                by_contra hcon; push Not at hcon
                have : M.what i ∈ L := by rw [hL, Finset.mem_filter]; exact ⟨hQw i hi, hcon⟩
                have := Finset.le_max' L _ this
                rw [← hq2] at this; linarith
              have hcmp : cnt q2 ≤ cnt qs + neq := by
                rw [hcnt, hcnt, hneq, ← Finset.sum_add_distrib]
                refine Finset.sum_le_sum fun i hi => ?_
                by_cases ha : q2 < M.what i
                · have hb := hsub i hi ha
                  rw [if_pos ha]
                  rcases eq_or_lt_of_le hb with hb | hb
                  · rw [if_neg (by rw [← hb]; exact lt_irrefl _), if_pos hb.symm]; norm_num
                  · rw [if_pos hb, if_neg (ne_of_gt hb)]; norm_num
                · rw [if_neg ha]
                  have : (0:ℝ) ≤ if qs < M.what i then 1 else 0 := by split_ifs <;> norm_num
                  have : (0:ℝ) ≤ if M.what i = qs then 1 else 0 := by split_ifs <;> norm_num
                  linarith
              have hneqpos : 0 < neq := by linarith
              refine ⟨(M.Γ k - cnt qs) / neq, div_nonneg (by linarith) hneqpos.le, ?_, ?_, ?_⟩
              · rw [div_le_one hneqpos]; linarith
              · rw [div_mul_cancel₀ _ hneqpos.ne']; linarith
              · rw [div_mul_cancel₀ _ hneqpos.ne']; ring
          obtain ⟨z, hz⟩ : ∃ z : ℕ → ℝ, z = fun i => if qs < M.what i then 1 else
              if M.what i = qs then θ else 0 := ⟨_, rfl⟩
          have hzsum : ∑ i ∈ I, z i = cnt qs + θ * neq := by
            rw [hcnt, hneq, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hz]
            by_cases ha : qs < M.what i
            · simp [ha, ne_of_gt ha]
            · by_cases hb : M.what i = qs <;> simp [ha, hb]
          have hzval : ∑ i ∈ I, M.what i * z i =
              ∑ i ∈ I, max (M.what i - qs) 0 + qs * ∑ i ∈ I, z i := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hz]
            by_cases ha : qs < M.what i
            · simp only [if_pos ha]; rw [max_eq_left (by linarith)]; ring
            · by_cases hb : M.what i = qs
              · simp only [if_neg ha, if_pos hb]; rw [hb, max_eq_right (by linarith)]; ring
              · simp only [if_neg ha, if_neg hb]; push Not at ha
                rw [max_eq_right (by linarith)]; ring
          have hzf : M.LP13Feasible k z := by
            refine ⟨fun i _ => ?_, ?_⟩
            · rw [hz]; dsimp only; split_ifs <;> constructor <;> linarith
            · rw [← hI, hzsum]; exact hθΓ
          have hdf : M.LP13DualFeasible k qs (fun i => max (M.what i - qs) 0) :=
            ⟨hqs0, fun i _ => ⟨le_max_right _ _, by linarith [le_max_left (M.what i - qs) 0]⟩⟩
          refine ⟨qs, fun i => max (M.what i - qs) 0, hdf, ?_⟩
          have hA := hweak k qs _ hdf
          rw [← hI] at hA
          refine le_antisymm ?_ hA
          have heq : qs * M.Γ k + ∑ i ∈ I, max (M.what i - qs) 0 = ∑ i ∈ I, M.what i * z i := by
            rw [hzval, hzsum, hθq]; ring
          rw [heq]
          unfold Model.A
          refine le_csSup ⟨qs * M.Γ k + ∑ i ∈ Finset.range (k+1), max (M.what i - qs) 0, ?_⟩ ⟨z, hzf, ?_⟩
          · rintro v ⟨z', hz', rfl⟩; exact hwe k qs _ hdf z' hz'
          · rw [hI]
        choose qf rf hqf using hdual
        have hpos : 0 < M.p + M.h := by linarith [M.hc, M.hpc, M.hh]
        have hp0 : 0 ≤ M.p := by linarith [M.hc, M.hpc]
        have htele : ∀ k, ∑ i ∈ Finset.range (k+1), (M.A i - M.Aprev i) = M.A k := by
          intro k; induction k with
          | zero => simp [Model.Aprev]
          | succ k ih => rw [Finset.sum_range_succ, ih]; simp [Model.Aprev]
        have hstock : ∀ (v : ℕ → ℝ) k, M.stock M.wmod v k =
            M.xbar v k - (M.p - M.h) / (M.p + M.h) * M.A k := by
          intro v k
          simp only [Model.xbar, Model.stock]
          rw [← htele k, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Model.wmod]; ring
        have hmax : ∀ X A : ℝ, max (M.h * (X + A)) (M.p * (-X + A)) =
            M.R (X - (M.p - M.h) / (M.p + M.h) * A) + 2 * M.p * M.h / (M.p + M.h) * A := by
          intro X A
          have e1 : M.h * (X + A) = M.h * (X - (M.p - M.h) / (M.p + M.h) * A) +
              2 * M.p * M.h / (M.p + M.h) * A := by field_simp; ring
          have e2 : M.p * (-X + A) = -(M.p * (X - (M.p - M.h) / (M.p + M.h) * A)) +
              2 * M.p * M.h / (M.p + M.h) * A := by field_simp; ring
          rw [e1, e2, max_add_add_right]; rfl
        have hcap : ∀ (v : ℕ → ℝ) k, M.stock M.wmod v k - modifiedCap M Cap k =
            M.xbar v k + M.A k - Cap := by
          intro v k
          rw [hstock]; simp only [modifiedCap]; field_simp; ring
        obtain ⟨KK, hKK⟩ : ∃ KK : ℝ, KK = ∑ k ∈ Finset.range M.T, 2 * M.p * M.h / (M.p + M.h) * M.A k :=
          ⟨_, rfl⟩
        -- robust feasible → nominal feasible and cost bound
        have hF : ∀ (u' y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ), RobustCapFeasible M Cap u' y' q' r' →
            NominalCapFeasible M Cap u' ∧ M.nominalCost M.wmod u' + KK ≤ M.robustObjective u' y' := by
          intro u' y' q' r' ⟨hR, hC⟩
          have hw : ∀ k < M.T, M.A k ≤ q' k * M.Γ k + ∑ i ∈ Finset.range (k+1), r' i k := by
            intro k hk
            obtain ⟨_, hq, hr, _, _⟩ := hR k hk
            exact hweak k (q' k) (fun i => r' i k) ⟨hq, hr⟩
          refine ⟨⟨fun k hk => (hR k hk).1, hx0, fun k hk => ?_⟩, ?_⟩
          · have h1 := hcap u' k
            have h2 := hw k hk
            have h3 := hC k hk
            linarith
          · have hyk : ∀ k < M.T, M.R (M.stock M.wmod u' k) +
                2 * M.p * M.h / (M.p + M.h) * M.A k ≤ y' k := by
              intro k hk
              obtain ⟨_, hq, hr, hy1, hy2⟩ := hR k hk
              have h2 := hw k hk
              rw [hstock, ← hmax]
              apply max_le
              · nlinarith [mul_le_mul_of_nonneg_left h2 M.hh]
              · nlinarith [mul_le_mul_of_nonneg_left h2 hp0]
            unfold Model.nominalCost Model.robustObjective
            rw [hKK, ← Finset.sum_add_distrib]
            exact Finset.sum_le_sum fun k hk => by linarith [hyk k (Finset.mem_range.1 hk)]
        -- nominal feasible → robust feasible with equal cost
        have hG : ∀ v : ℕ → ℝ, NominalCapFeasible M Cap v →
            RobustCapFeasible M Cap v
              (fun k => max (M.h * (M.xbar v k + M.A k)) (M.p * (-M.xbar v k + M.A k)))
              qf (fun i k => rf k i) ∧
            M.robustObjective v
              (fun k => max (M.h * (M.xbar v k + M.A k)) (M.p * (-M.xbar v k + M.A k))) =
              M.nominalCost M.wmod v + KK := by
          intro v ⟨hv0, _, hvc⟩
          refine ⟨⟨fun k hk => ?_, fun k hk => ?_⟩, ?_⟩
          · obtain ⟨⟨hq0, hr⟩, he⟩ := hqf k
            refine ⟨hv0 k hk, hq0, hr, ?_, ?_⟩
            · show M.h * (_ + qf k * M.Γ k + _) ≤ _
              rw [add_assoc, he]; exact le_max_left _ _
            · show M.p * (_ + qf k * M.Γ k + _) ≤ _
              rw [add_assoc, he]; exact le_max_right _ _
          · obtain ⟨_, he⟩ := hqf k
            show M.xbar v k + qf k * M.Γ k + ∑ i ∈ Finset.range (k + 1), rf k i ≤ Cap
            rw [add_assoc, he]
            have h1 := hcap v k
            have h2 := hvc k hk
            linarith
          · unfold Model.nominalCost Model.robustObjective
            rw [hKK, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            show _ + max _ _ = _
            rw [hmax, ← hstock]; ring
        constructor
        · rintro ⟨y, q, r, hfe, hopt⟩
          obtain ⟨hN, hle⟩ := hF u y q r hfe
          refine ⟨hN, fun u' hu' => ?_⟩
          obtain ⟨hG1, hG2⟩ := hG u' hu'
          have := hopt _ _ _ _ hG1
          linarith
        · rintro ⟨hN, hopt⟩
          obtain ⟨hG1, hG2⟩ := hG u hN
          refine ⟨_, _, _, hG1, fun u' y' q' r' hfe => ?_⟩
          obtain ⟨hN', hle'⟩ := hF u' y' q' r' hfe
          have := hopt u' hN'
          linarith
