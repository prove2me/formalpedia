-- Prove2me | solution 1 for RobustInventory.SingleStation.Supplement.theorem_3_2c
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:44.766298+00:00
-- url     : https://prove2.me/submissions/246a3ded-2eb5-4b87-9ea7-9fe4b09b35fe

import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust
import Definitions.Def_RobustInventory_SingleStation_Supplement_Thresholds

open RobustInventory
open RobustInventory.SingleStation
open RobustInventory.SingleStation.Supplement

/-- Theorem 3.2(c), p. 155, for `K > 0` and `w'_k ≥ 0` on the horizon: if `t_1 < … < t_J` are
the ordering times of an optimal solution of (14), then some optimal solution of (14) orders
exactly at these times, and at each `t_j` its modified stock is `s_j` before the order and `S_j`
after it, (15)–(16) being evaluated at the modified demand `w'`. -/
theorem solution (M : Model) (hK : 0 < M.K) (hw' : ∀ k < M.T, 0 ≤ M.wmod k)
    (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (hu : M.IsRobustOptimal u y q r)
    (J : ℕ) (t : ℕ → ℕ) (ht : IsOrderingTimes M.T u J t) :
    ∃ (v y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ),
      M.IsRobustOptimal v y' q' r' ∧ IsOrderingTimes M.T v J t ∧
      ∀ j ∈ Finset.Icc 1 J,
        stockBefore M M.wmod v (t j) = lowerThreshold M M.wmod J t j ∧
        stockBefore M M.wmod v (t j) + v (t j) = upperThreshold M M.wmod J t j := by
          set_option maxHeartbeats 4000000 in
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
          have hp : 0 < M.p := by linarith [M.hc, M.hpc]
          have htele : ∀ k, ∑ i ∈ Finset.range (k+1), (M.A i - M.Aprev i) = M.A k := by
            intro k; induction k with
            | zero => simp [Model.Aprev]
            | succ k ih => rw [Finset.sum_range_succ, ih]; simp [Model.Aprev]
          have hstock : ∀ (v : ℕ → ℝ) k, M.stock M.wmod v k =
              M.xbar v k - (M.p - M.h) / (M.p + M.h) * M.A k := by
            intro v k
            unfold Model.xbar Model.stock
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
          obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ Finset.range M.T, M.A k :=
            ⟨_, rfl⟩
          have hR1 : ∀ (x y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ), M.RobustFeasible x y' q' r' →
              M.nominalCost M.wmod x + κ ≤ M.robustObjective x y' := by
            intro x y' q' r' hF
            have hyk : ∀ k < M.T, M.R (M.stock M.wmod x k) + 2 * M.p * M.h / (M.p + M.h) * M.A k
                ≤ y' k := by
              intro k hk
              obtain ⟨_, hq, hr, hy1, hy2⟩ := hF k hk
              have hw := hweak k (q' k) (fun i => r' i k) ⟨hq, hr⟩
              beta_reduce at hw
              rw [hstock, ← hmax]
              apply max_le
              · nlinarith [mul_le_mul_of_nonneg_left hw M.hh]
              · nlinarith [mul_le_mul_of_nonneg_left hw hp.le]
            unfold Model.nominalCost Model.robustObjective
            rw [hκ, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_le_sum fun k hk => by linarith [hyk k (Finset.mem_range.1 hk)]
          have hR2 : ∀ x : ℕ → ℝ, (∀ k < M.T, 0 ≤ x k) → ∃ (y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ),
              M.RobustFeasible x y' q' r' ∧ M.robustObjective x y' = M.nominalCost M.wmod x + κ := by
            intro x hx
            refine ⟨fun k => max (M.h * (M.xbar x k + M.A k)) (M.p * (-M.xbar x k + M.A k)), qf,
              fun i k => rf k i, ?_, ?_⟩
            · intro k hk
              obtain ⟨⟨hq0, hr⟩, he⟩ := hqf k
              refine ⟨hx k hk, hq0, hr, ?_, ?_⟩
              · show M.h * (_ + qf k * M.Γ k + _) ≤ _
                rw [add_assoc, he]; exact le_max_left _ _
              · show M.p * (_ + qf k * M.Γ k + _) ≤ _
                rw [add_assoc, he]; exact le_max_right _ _
            · unfold Model.nominalCost Model.robustObjective
              rw [hκ, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun k _ => ?_
              beta_reduce; rw [hmax, ← hstock]; ring
          have hun : ∀ k < M.T, 0 ≤ u k := fun k hk => (hu.1 k hk).1
          have hNopt : ∀ x : ℕ → ℝ, (∀ k < M.T, 0 ≤ x k) →
              M.nominalCost M.wmod u ≤ M.nominalCost M.wmod x := by
            intro x hx
            obtain ⟨y', q', r', hF, he⟩ := hR2 x hx
            have h1 := hR1 u y q r hu.1
            have h2 := hu.2 x y' q' r' hF
            linarith
          have hfinal : ∀ x : ℕ → ℝ, (∀ k < M.T, 0 ≤ x k) →
              M.nominalCost M.wmod x ≤ M.nominalCost M.wmod u →
              ∃ (y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ), M.IsRobustOptimal x y' q' r' := by
            intro x hx hle
            obtain ⟨y', q', r', hF, he⟩ := hR2 x hx
            refine ⟨y', q', r', hF, fun u'' y'' q'' r'' hF'' => ?_⟩
            have h1 := hR1 u y q r hu.1
            have h2 := hu.2 u'' y'' q'' r'' hF''
            linarith
          obtain ⟨hT1, htstep, htiff⟩ := ht
          rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
          · subst hJ0
            refine ⟨u, y, q, r, hu, ⟨hT1, htstep, htiff⟩, ?_⟩
            intro j hj; rw [Finset.mem_Icc] at hj; omega
          set w := M.wmod with hwdef
          have hc := M.hc
          have hpc := M.hpc
          have hhh := M.hh
          have hph : 0 < M.h + M.p := by linarith
          have tmono : ∀ a b, 1 ≤ a → a < b → b ≤ J + 1 → t a < t b := by
            intro a b ha hab hb
            induction b, hab using Nat.le_induction with
            | base => exact htstep a (Finset.mem_Icc.2 ⟨ha, by omega⟩)
            | succ n hn ih =>
              exact (ih (by omega)).trans (htstep n (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
          have tle : ∀ a b, 1 ≤ a → a ≤ b → b ≤ J + 1 → t a ≤ t b := by
            intro a b ha hab hb
            rcases eq_or_lt_of_le hab with h | h
            · rw [h]
            · exact (tmono a b ha h hb).le
          have tinj : ∀ a ∈ Finset.Icc 1 J, ∀ b ∈ Finset.Icc 1 J, t a = t b → a = b := by
            intro a ha b hb hab
            rw [Finset.mem_Icc] at ha hb
            rcases lt_trichotomy a b with h | h | h
            · have := tmono a b ha.1 h (by omega); omega
            · exact h
            · have := tmono b a hb.1 h (by omega); omega
          have htjL : ∀ j ∈ Finset.Icc 1 J, t j + intervalLength t j = t (j + 1) := by
            intro j hj; have := htstep j hj; unfold intervalLength; omega
          have hLpos : ∀ j ∈ Finset.Icc 1 J, 1 ≤ intervalLength t j := by
            intro j hj; have := htstep j hj; unfold intervalLength; omega
          have htT : ∀ j ∈ Finset.Icc 1 J, t (j + 1) ≤ M.T := by
            intro j hj; rw [Finset.mem_Icc] at hj; rw [← hT1]; exact tle (j+1) (J+1) (by omega) (by omega) le_rfl
          have hmid : ∀ j ∈ Finset.Icc 1 J, ∀ i, 0 < i → i < intervalLength t j →
              ∀ j' ∈ Finset.Icc 1 J, t j' ≠ t j + i := by
            intro j hj i hi0 hiL j' hj' heq
            have h1 := htjL j hj
            have hj1 := hj; have hj'1 := hj'
            rw [Finset.mem_Icc] at hj1 hj'1
            rcases lt_or_ge j j' with hjj | hjj
            · have := tle (j+1) j' (by omega) hjj (by omega); omega
            · have := tle j' j hj'1.1 hjj (by omega); omega
          have hbelow : ∀ k < t 1, ∀ j' ∈ Finset.Icc 1 J, t j' ≠ k := by
            intro k hk j' hj' heq
            rw [Finset.mem_Icc] at hj'
            have := tle 1 j' le_rfl hj'.1 (by omega); omega
          have hu0 : ∀ k < M.T, (∀ j' ∈ Finset.Icc 1 J, t j' ≠ k) → u k = 0 := by
            intro k hk hne
            by_contra hcon
            have hpos' : 0 < u k := lt_of_le_of_ne (hun k hk) (Ne.symm hcon)
            obtain ⟨j, hj, hjk⟩ := (htiff k).1 ⟨hk, hpos'⟩
            exact hne j hj hjk
          have hpart : ∀ f : ℕ → ℝ, ∑ k ∈ Finset.range M.T, f k = ∑ k ∈ Finset.range (t 1), f k +
              ∑ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range (intervalLength t j), f (t j + i) := by
            intro f
            have key : ∀ n, n ≤ J → ∑ k ∈ Finset.range (t (n+1)), f k = ∑ k ∈ Finset.range (t 1), f k +
                ∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.range (intervalLength t j), f (t j + i) := by
              intro n
              induction n with
              | zero => intro _; simp
              | succ n ih =>
                intro hn
                rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ← add_assoc, ← ih (by omega)]
                have hj : n + 1 ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨by omega, hn⟩
                rw [← htjL (n+1) hj, Finset.sum_range_add]
            rw [← hT1]; exact key J le_rfl
          have hSBsucc : ∀ x n, stockBefore M w x (n+1) = stockBefore M w x n + (x n - w n) := by
            intro x n; unfold stockBefore; rw [Finset.sum_range_succ]; ring
          have hbot : ∀ x : ℕ → ℝ, (∀ k < t 1, x k = 0) → ∀ n ≤ t 1,
              stockBefore M w x n = M.x0 - ∑ i ∈ Finset.range n, w i := by
            intro x hx n
            induction n with
            | zero => intro _; simp [stockBefore]
            | succ n ih =>
              intro hn
              rw [hSBsucc, ih (by omega), hx n (by omega), Finset.sum_range_succ]; ring
          have hint : ∀ x : ℕ → ℝ, ∀ j ∈ Finset.Icc 1 J,
              (∀ i, 0 < i → i < intervalLength t j → x (t j + i) = 0) → ∀ i < intervalLength t j,
              stockBefore M w x (t j + i + 1) = stockBefore M w x (t j) + x (t j) -
                ∑ l ∈ Finset.range (i+1), w (t j + l) := by
            intro x j hj hx i
            induction i with
            | zero => intro _; simp only [Nat.add_zero, zero_add, Finset.sum_range_one]; rw [hSBsucc]; ring
            | succ i ih =>
              intro hi
              rw [show t j + (i+1) + 1 = (t j + i + 1) + 1 by ring, hSBsucc, ih (by omega),
                show t j + i + 1 = t j + (i + 1) by ring, hx (i+1) (by omega) hi,
                Finset.sum_range_succ (fun l => w (t j + l)) (i+1)]
              ring
          obtain ⟨G, hG⟩ : ∃ G : (ℕ → ℝ) → ℝ, ∀ x, G x =
              ∑ k ∈ Finset.range M.T, M.R (stockBefore M w x (k+1)) := ⟨_, fun _ => rfl⟩
          have hNC : ∀ x : ℕ → ℝ, (∀ k < M.T, 0 ≤ x k) → M.nominalCost w x =
              M.c * (stockBefore M w x M.T - M.x0 + ∑ k ∈ Finset.range M.T, w k) +
              M.K * (((Finset.range M.T).filter (fun k => 0 < x k)).card : ℝ) + G x := by
            intro x hx
            have e1 : ∀ k ∈ Finset.range M.T, M.C (x k) + M.R (M.stock w x k) =
                M.c * x k + (if 0 < x k then M.K else 0) + M.R (stockBefore M w x (k+1)) := by
              intro k hk
              have h0 := hx k (Finset.mem_range.1 hk)
              have hs : M.stock w x k = stockBefore M w x (k+1) := rfl
              rw [hs]
              unfold Model.C
              by_cases hxk : 0 < x k
              · rw [if_pos hxk, if_pos hxk]; ring
              · rw [if_neg hxk, if_neg hxk]
                have : x k = 0 := le_antisymm (not_lt.1 hxk) h0
                rw [this]; ring
            unfold Model.nominalCost
            rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hG]
            unfold stockBefore
            rw [Finset.sum_sub_distrib]
            ring
          have hcard : ∀ x : ℕ → ℝ, (∀ k < M.T, (0 < x k ↔ ∃ j ∈ Finset.Icc 1 J, t j = k)) →
              ((Finset.range M.T).filter (fun k => 0 < x k)).card = J := by
            intro x hx
            have : (Finset.range M.T).filter (fun k => 0 < x k) = (Finset.Icc 1 J).image t := by
              ext k
              rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
              constructor
              · rintro ⟨hk, hpos'⟩; exact (hx k hk).1 hpos'
              · rintro ⟨j, hj, rfl⟩
                have hT' := htT j hj
                have := htstep j hj
                exact ⟨by omega, (hx (t j) (by omega)).2 ⟨j, hj, rfl⟩⟩
            rw [this, Finset.card_image_of_injOn (fun a ha b hb hab => tinj a ha b hb hab), Nat.card_Icc]
            omega
          have hZ : ∀ x : ℕ → ℝ, (∀ k < M.T, 0 ≤ x k) → ∀ j0 ∈ Finset.Icc 1 J,
              (∀ k < M.T, 0 < x k → ∃ j ∈ (Finset.Icc 1 J).erase j0, t j = k) →
              M.c * stockBefore M w x M.T + G x ≤ M.c * stockBefore M w u M.T + G u → False := by
            intro x hx j0 hj0 hsupp hle
            have h1 := hNopt x hx
            rw [hNC x hx, hNC u hun] at h1
            have hcu : ((Finset.range M.T).filter (fun k => 0 < u k)).card = J :=
              hcard u (fun k hk => ⟨fun h => (htiff k).1 ⟨hk, h⟩, fun h => ((htiff k).2 h).2⟩)
            have hcx : ((Finset.range M.T).filter (fun k => 0 < x k)).card ≤ J - 1 := by
              calc _ ≤ (((Finset.Icc 1 J).erase j0).image t).card := by
                    apply Finset.card_le_card
                    intro k hk
                    rw [Finset.mem_filter, Finset.mem_range] at hk
                    obtain ⟨j, hj, hjk⟩ := hsupp k hk.1 hk.2
                    exact Finset.mem_image.2 ⟨j, hj, hjk⟩
                _ ≤ ((Finset.Icc 1 J).erase j0).card := Finset.card_image_le
                _ = J - 1 := by rw [Finset.card_erase_of_mem hj0, Nat.card_Icc]; omega
            have hcx' : (((Finset.range M.T).filter (fun k => 0 < x k)).card : ℝ) ≤ (J:ℝ) - 1 := by
              have h2 : ((Finset.range M.T).filter (fun k => 0 < x k)).card + 1 ≤ J := by omega
              have h3 : (((Finset.range M.T).filter (fun k => 0 < x k)).card : ℝ) + 1 ≤ J := by
                exact_mod_cast h2
              linarith
            rw [hcu] at h1
            nlinarith [mul_le_mul_of_nonneg_left hcx' hK.le]
          have hnot : ¬ (M.h = 0 ∧ 2 ≤ J) := by
            rintro ⟨hh0, hJ2⟩
            have h1J : (1:ℕ) ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
            have h2J : (2:ℕ) ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨by norm_num, hJ2⟩
            have ht12 : t 1 < t 2 := tmono 1 2 le_rfl (by norm_num) (by omega)
            have ht2T : t 2 < M.T := lt_of_lt_of_le (htstep 2 h2J) (htT 2 h2J)
            obtain ⟨a, ha⟩ : ∃ a, a = u (t 2) := ⟨_, rfl⟩
            have ha0 : 0 < a := ha ▸ ((htiff (t 2)).2 ⟨2, h2J, rfl⟩).2
            obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, x = fun k => u k + (if k = t 1 then a else 0) -
                (if k = t 2 then a else 0) := ⟨_, rfl⟩
            have hxSB : ∀ n, stockBefore M w x n = stockBefore M w u n + (if t 1 < n then a else 0) -
                (if t 2 < n then a else 0) := by
              intro n
              simp only [stockBefore, hx]
              have e : ∀ i, (u i + (if i = t 1 then a else 0) - (if i = t 2 then a else 0) - w i) =
                  (u i - w i) + (if i = t 1 then a else 0) - (if i = t 2 then a else 0) := fun i => by ring
              simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
                Finset.mem_range]
              ring
            have hxnn : ∀ k < M.T, 0 ≤ x k := by
              intro k hk
              rw [hx]; dsimp only
              by_cases h1 : k = t 1
              · have h2 : ¬ k = t 2 := by omega
                rw [if_pos h1, if_neg h2]; linarith [hun k hk]
              · by_cases h2 : k = t 2
                · rw [if_neg h1, if_pos h2, h2, ← ha]; linarith
                · rw [if_neg h1, if_neg h2]; linarith [hun k hk]
            have hsupp : ∀ k < M.T, 0 < x k → ∃ j ∈ (Finset.Icc 1 J).erase 2, t j = k := by
              intro k hk hxk
              by_cases h1 : k = t 1
              · exact ⟨1, Finset.mem_erase.2 ⟨by norm_num, h1J⟩, h1.symm⟩
              · by_cases h2 : k = t 2
                · exfalso
                  rw [hx] at hxk; dsimp only at hxk
                  rw [if_neg h1, if_pos h2, h2, ← ha] at hxk; linarith
                · have hxu : x k = u k := by rw [hx]; dsimp only; rw [if_neg h1, if_neg h2]; ring
                  obtain ⟨j, hj, hjk⟩ := (htiff k).1 ⟨hk, hxu ▸ hxk⟩
                  refine ⟨j, Finset.mem_erase.2 ⟨?_, hj⟩, hjk⟩
                  rintro rfl; exact h2 hjk.symm
            apply hZ x hxnn 2 h2J hsupp
            have eT : stockBefore M w x M.T = stockBefore M w u M.T := by
              rw [hxSB, if_pos (by omega), if_pos ht2T]; ring
            have eG : G x ≤ G u := by
              rw [hG, hG]
              refine Finset.sum_le_sum fun k _ => ?_
              have hge : stockBefore M w u (k+1) ≤ stockBefore M w x (k+1) := by
                rw [hxSB]
                by_cases h2 : t 2 < k + 1
                · rw [if_pos h2, if_pos (by omega)]; linarith
                · rw [if_neg h2]; split_ifs <;> linarith
              unfold Model.R
              rw [hh0, zero_mul, zero_mul]
              exact max_le_max le_rfl (by nlinarith)
            rw [eT]; linarith
          have hfl : ∀ j ∈ Finset.Icc 1 J,
              ((floorIndex M J t j : ℕ) : ℝ) * (M.h + M.p) ≤
                M.p * (intervalLength t j : ℝ) - (if j = J then M.c else 0) ∧
              M.p * (intervalLength t j : ℝ) - (if j = J then M.c else 0) <
                (((floorIndex M J t j : ℕ) : ℝ) + 1) * (M.h + M.p) := by
            intro j hj
            have hL1 : (1:ℝ) ≤ (intervalLength t j : ℝ) := by exact_mod_cast hLpos j hj
            have hnum : 0 ≤ M.p * (intervalLength t j : ℝ) - (if j = J then M.c else 0) := by
              split_ifs <;> nlinarith
            have hdiv : 0 ≤ (M.p * (intervalLength t j : ℝ) - (if j = J then M.c else 0)) / (M.h + M.p) :=
              div_nonneg hnum hph.le
            have e1 := Nat.floor_le hdiv
            have e2 := Nat.lt_floor_add_one
              ((M.p * (intervalLength t j : ℝ) - (if j = J then M.c else 0)) / (M.h + M.p))
            unfold floorIndex
            constructor
            · rwa [le_div_iff₀ hph] at e1
            · rwa [div_lt_iff₀ hph] at e2
          have hIL : ∀ j ∈ Finset.Icc 1 J, floorIndex M J t j + 1 ≤ intervalLength t j := by
            intro j hj
            obtain ⟨e1, _⟩ := hfl j hj
            have hL1 : (1:ℝ) ≤ (intervalLength t j : ℝ) := by exact_mod_cast hLpos j hj
            by_contra hcon
            have hge : (intervalLength t j : ℝ) ≤ (floorIndex M J t j : ℝ) := by
              exact_mod_cast (by omega : intervalLength t j ≤ floorIndex M J t j)
            have hm := mul_le_mul_of_nonneg_right hge hph.le
            by_cases hjJ : j = J
            · rw [if_pos hjJ] at e1; nlinarith
            · rw [if_neg hjJ] at e1
              have hh0 : 0 < M.h := by
                rcases lt_or_eq_of_le M.hh with h | h
                · exact h
                · exfalso; apply hnot; refine ⟨h.symm, ?_⟩; rw [Finset.mem_Icc] at hj; omega
              nlinarith
          obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, v = fun k => ∑ j ∈ Finset.Icc 1 J,
              if t j = k then (upperThreshold M w J t j - lowerThreshold M w J t j) else 0 := ⟨_, rfl⟩
          have hvt : ∀ j ∈ Finset.Icc 1 J, v (t j) = upperThreshold M w J t j - lowerThreshold M w J t j := by
            intro j hj; rw [hv]; dsimp only
            rw [Finset.sum_eq_single j]
            · rw [if_pos rfl]
            · intro b hb hbj; rw [if_neg]; intro h; exact hbj (tinj b hb j hj h)
            · intro h; exact absurd hj h
          have hv0 : ∀ k, (∀ j' ∈ Finset.Icc 1 J, t j' ≠ k) → v k = 0 := by
            intro k hk; rw [hv]; exact Finset.sum_eq_zero fun j hj => if_neg (hk j hj)
          have hvint : ∀ j ∈ Finset.Icc 1 J, ∀ i, 0 < i → i < intervalLength t j → v (t j + i) = 0 :=
            fun j hj i hi hiL => hv0 _ (hmid j hj i hi hiL)
          have huint : ∀ j ∈ Finset.Icc 1 J, ∀ i, 0 < i → i < intervalLength t j → u (t j + i) = 0 := by
            intro j hj i hi hiL
            have := htjL j hj; have := htT j hj
            exact hu0 _ (by omega) (hmid j hj i hi hiL)
          have hvbot : ∀ k < t 1, v k = 0 := fun k hk => hv0 k (hbelow k hk)
          have hubot : ∀ k < t 1, u k = 0 := by
            intro k hk
            have h1J : (1:ℕ) ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
            have := htstep 1 h1J; have := htT 1 h1J
            exact hu0 k (by omega) (hbelow k hk)
          have hvs : ∀ n, 1 ≤ n → n ≤ J → stockBefore M w v (t n) = lowerThreshold M w J t n := by
            intro n hn
            induction n, hn using Nat.le_induction with
            | base =>
              intro _
              rw [hbot v hvbot (t 1) le_rfl]
              unfold lowerThreshold; rw [if_pos rfl]
            | succ n hn ih =>
              intro hnJ
              have hnI : n ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨hn, by omega⟩
              have hL := hLpos n hnI
              have hI := hIL n hnI
              have e := hint v n hnI (hvint n hnI) (intervalLength t n - 1) (by omega)
              rw [show t n + (intervalLength t n - 1) + 1 = t (n+1) by have := htjL n hnI; omega,
                show intervalLength t n - 1 + 1 = intervalLength t n by omega, ih (by omega),
                hvt n hnI] at e
              rw [e]
              unfold lowerThreshold
              rw [if_neg (show n + 1 ≠ 1 by omega), show n + 1 - 1 = n by omega]
              unfold upperThreshold
              rw [← Finset.sum_range_add_sum_Ico _ hI]
              ring
          have hvB : ∀ j ∈ Finset.Icc 1 J, stockBefore M w v (t j) + v (t j) = upperThreshold M w J t j := by
            intro j hj
            have hj' := Finset.mem_Icc.1 hj
            rw [hvs j hj'.1 hj'.2, hvt j hj]; ring
          obtain ⟨σl, hσl⟩ : ∃ σl : ℕ → ℕ → ℝ, ∀ j i, σl j i =
              if i < floorIndex M J t j then M.h else if i = floorIndex M J t j then
                (M.p * (intervalLength t j : ℝ) - (if j = J then M.c else 0) -
                  ((floorIndex M J t j : ℕ) : ℝ) * (M.h + M.p) - M.p) else -M.p := ⟨_, fun _ _ => rfl⟩
          have hσsum : ∀ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range (intervalLength t j), σl j i =
              -(if j = J then M.c else 0) := by
            intro j hj
            have hI := hIL j hj
            rw [← Finset.sum_range_add_sum_Ico _ hI, Finset.sum_range_succ]
            have e1 : ∑ i ∈ Finset.range (floorIndex M J t j), σl j i =
                ∑ i ∈ Finset.range (floorIndex M J t j), M.h :=
              Finset.sum_congr rfl fun i hi => by rw [hσl, if_pos (Finset.mem_range.1 hi)]
            have e2 : ∑ i ∈ Finset.Ico (floorIndex M J t j + 1) (intervalLength t j), σl j i =
                ∑ i ∈ Finset.Ico (floorIndex M J t j + 1) (intervalLength t j), (-M.p) :=
              Finset.sum_congr rfl fun i hi => by
                rw [Finset.mem_Ico] at hi
                rw [hσl, if_neg (show ¬ (i < floorIndex M J t j) by omega),
                  if_neg (show ¬ (i = floorIndex M J t j) by omega)]
            rw [e1, e2, hσl, if_neg (lt_irrefl _), if_pos rfl, Finset.sum_const, Finset.sum_const,
              Finset.card_range, Nat.card_Ico, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hI]
            push_cast; ring
          have hσrange : ∀ j ∈ Finset.Icc 1 J, ∀ i, -M.p ≤ σl j i ∧ σl j i ≤ M.h := by
            intro j hj i
            obtain ⟨e1, e2⟩ := hfl j hj
            rw [hσl]
            generalize (if j = J then M.c else 0) = c' at e1 e2 ⊢
            split_ifs
            · constructor <;> linarith
            · constructor <;> nlinarith
            · constructor <;> linarith
          have hRsub : ∀ σ a b : ℝ, -M.p ≤ σ → σ ≤ M.h → M.R b = σ * b →
              σ * (a - b) ≤ M.R a - M.R b := by
            intro σ a b h1 h2 hb
            have : σ * a ≤ M.R a := by
              unfold Model.R
              rcases le_total 0 a with ha | ha
              · exact le_max_of_le_left (by nlinarith)
              · exact le_max_of_le_right (by nlinarith)
            rw [hb]; nlinarith
          have hRb : ∀ j ∈ Finset.Icc 1 J, ∀ i < intervalLength t j,
              M.R (upperThreshold M w J t j - ∑ l ∈ Finset.range (i+1), w (t j + l)) =
                σl j i * (upperThreshold M w J t j - ∑ l ∈ Finset.range (i+1), w (t j + l)) := by
            intro j hj i hi
            have hI := hIL j hj
            have hwn : ∀ l < intervalLength t j, 0 ≤ w (t j + l) := fun l hl =>
              hw' _ (by have := htjL j hj; have := htT j hj; omega)
            unfold upperThreshold
            rw [hσl]
            rcases lt_trichotomy i (floorIndex M J t j) with hlt | heq | hgt
            · rw [if_pos hlt]
              have hnn : 0 ≤ ∑ l ∈ Finset.range (floorIndex M J t j + 1), w (t j + l) -
                  ∑ l ∈ Finset.range (i+1), w (t j + l) := by
                rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ floorIndex M J t j + 1 by omega),
                  add_sub_cancel_left]
                exact Finset.sum_nonneg fun l hl => hwn l (by rw [Finset.mem_Ico] at hl; omega)
              unfold Model.R; rw [max_eq_left (by nlinarith)]
            · rw [if_neg (show ¬ (i < floorIndex M J t j) by omega), if_pos heq, heq, sub_self]
              simp [Model.R]
            · rw [if_neg (show ¬ (i < floorIndex M J t j) by omega),
                if_neg (show ¬ (i = floorIndex M J t j) by omega)]
              have hnp : ∑ l ∈ Finset.range (floorIndex M J t j + 1), w (t j + l) -
                  ∑ l ∈ Finset.range (i+1), w (t j + l) ≤ 0 := by
                rw [← Finset.sum_range_add_sum_Ico _ (show floorIndex M J t j + 1 ≤ i + 1 by omega)]
                have := Finset.sum_nonneg fun l (hl : l ∈ Finset.Ico (floorIndex M J t j + 1) (i+1)) =>
                  hwn l (by rw [Finset.mem_Ico] at hl; omega)
                linarith
              unfold Model.R; rw [max_eq_right (by nlinarith)]; ring
          have hJJ : J ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨hJpos, le_rfl⟩
          have hSBT : ∀ x : ℕ → ℝ, (∀ i, 0 < i → i < intervalLength t J → x (t J + i) = 0) →
              stockBefore M w x M.T = stockBefore M w x (t J) + x (t J) -
                ∑ l ∈ Finset.range (intervalLength t J), w (t J + l) := by
            intro x hx
            have hL := hLpos J hJJ
            have e := hint x J hJJ hx (intervalLength t J - 1) (by omega)
            rwa [show t J + (intervalLength t J - 1) + 1 = M.T by have := htjL J hJJ; omega,
              show intervalLength t J - 1 + 1 = intervalLength t J by omega] at e
          have hGdiff : G u - G v = ∑ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range (intervalLength t j),
              (M.R (stockBefore M w u (t j + i + 1)) - M.R (stockBefore M w v (t j + i + 1))) := by
            rw [hG, hG, ← Finset.sum_sub_distrib, hpart]
            rw [Finset.sum_eq_zero (fun k hk => ?_), zero_add]
            rw [Finset.mem_range] at hk
            rw [hbot u hubot (k+1) (by omega), hbot v hvbot (k+1) (by omega), sub_self]
          have hGge : ∑ j ∈ Finset.Icc 1 J, (-(if j = J then M.c else 0)) *
              (stockBefore M w u (t j) + u (t j) - upperThreshold M w J t j) ≤ G u - G v := by
            rw [hGdiff]
            refine Finset.sum_le_sum fun j hj => ?_
            rw [← hσsum j hj, Finset.sum_mul]
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' := Finset.mem_range.1 hi
            rw [hint u j hj (huint j hj) i hi', hint v j hj (hvint j hj) i hi', hvB j hj]
            obtain ⟨h1, h2⟩ := hσrange j hj i
            have := hRsub (σl j i) (stockBefore M w u (t j) + u (t j) -
              ∑ l ∈ Finset.range (i+1), w (t j + l)) _ h1 h2 (hRb j hj i hi')
            have e : σl j i * (stockBefore M w u (t j) + u (t j) - upperThreshold M w J t j) =
                σl j i * ((stockBefore M w u (t j) + u (t j) - ∑ l ∈ Finset.range (i+1), w (t j + l)) -
                  (upperThreshold M w J t j - ∑ l ∈ Finset.range (i+1), w (t j + l))) := by ring
            rw [e]; exact this
          have hFv : M.c * stockBefore M w v M.T + G v ≤ M.c * stockBefore M w u M.T + G u := by
            have e : ∀ j, (-(if j = J then M.c else 0)) *
                (stockBefore M w u (t j) + u (t j) - upperThreshold M w J t j) =
                if j = J then -M.c * (stockBefore M w u (t J) + u (t J) - upperThreshold M w J t J)
                else 0 := by
              intro j; split_ifs with h
              · rw [h]
              · ring
            simp only [e, Finset.sum_ite_eq', hJJ, if_true] at hGge
            rw [hSBT u (huint J hJJ), hSBT v (hvint J hJJ), hvB J hJJ]
            nlinarith
          have hupos : ∀ j ∈ Finset.Icc 1 J, 0 < u (t j) := fun j hj => ((htiff (t j)).2 ⟨j, hj, rfl⟩).2
          have hvpos : ∀ j ∈ Finset.Icc 1 J, 0 < v (t j) := by
            by_contra hcon
            push_neg at hcon
            obtain ⟨jb, hjb, hvjb⟩ := hcon
            have hBne : ((Finset.Icc 1 J).filter (fun j => v (t j) ≤ 0)).Nonempty :=
              ⟨jb, Finset.mem_filter.2 ⟨hjb, hvjb⟩⟩
            obtain ⟨θf, hθf⟩ : ∃ θf : ℕ → ℝ, θf = fun j => u (t j) / (u (t j) - v (t j)) := ⟨_, rfl⟩
            obtain ⟨j0, hj0B, hj0min⟩ := Finset.exists_min_image _ θf hBne
            obtain ⟨hj0, hvj0⟩ := Finset.mem_filter.1 hj0B
            obtain ⟨θ, hθ⟩ : ∃ θ, θ = θf j0 := ⟨_, rfl⟩
            have hd0 : 0 < u (t j0) - v (t j0) := by linarith [hupos j0 hj0]
            have hθ0 : 0 ≤ θ := by rw [hθ, hθf]; exact div_nonneg (hupos j0 hj0).le hd0.le
            have hθ1 : θ ≤ 1 := by rw [hθ, hθf]; dsimp only; rw [div_le_one hd0]; linarith
            have hθeq : θ * (u (t j0) - v (t j0)) = u (t j0) := by
              rw [hθ, hθf]; dsimp only; field_simp
            obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, x = fun k => u k + θ * (v k - u k) := ⟨_, rfl⟩
            have hxSB : ∀ n, stockBefore M w x n =
                (1 - θ) * stockBefore M w u n + θ * stockBefore M w v n := by
              intro n; simp only [stockBefore, hx]
              have e : ∀ i, u i + θ * (v i - u i) - w i = (1 - θ) * (u i - w i) + θ * (v i - w i) :=
                fun i => by ring
              rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum]
              ring
            have hxnn : ∀ k < M.T, 0 ≤ x k := by
              intro k hk
              rw [hx]; dsimp only
              by_cases hex : ∃ j ∈ Finset.Icc 1 J, t j = k
              · obtain ⟨j, hj, rfl⟩ := hex
                have hu1 := hupos j hj
                by_cases hvj : v (t j) ≤ 0
                · have hmin := hj0min j (Finset.mem_filter.2 ⟨hj, hvj⟩)
                  rw [← hθ, hθf] at hmin; dsimp only at hmin
                  have hdj : 0 < u (t j) - v (t j) := by linarith
                  rw [le_div_iff₀ hdj] at hmin
                  nlinarith
                · push_neg at hvj; nlinarith
              · push_neg at hex
                rw [hu0 k hk hex, hv0 k hex]; ring_nf; exact le_rfl
            have hsupp : ∀ k < M.T, 0 < x k → ∃ j ∈ (Finset.Icc 1 J).erase j0, t j = k := by
              intro k hk hxk
              by_cases hex : ∃ j ∈ Finset.Icc 1 J, t j = k
              · obtain ⟨j, hj, rfl⟩ := hex
                refine ⟨j, Finset.mem_erase.2 ⟨?_, hj⟩, rfl⟩
                rintro rfl
                rw [hx] at hxk; dsimp only at hxk
                nlinarith
              · push_neg at hex
                rw [hx] at hxk; dsimp only at hxk
                rw [hu0 k hk hex, hv0 k hex] at hxk; linarith
            have hRconv : ∀ a b : ℝ, M.R ((1 - θ) * a + θ * b) ≤ (1 - θ) * M.R a + θ * M.R b := by
              intro a b
              unfold Model.R
              have h1 := le_max_left (M.h * a) (-(M.p * a))
              have h2 := le_max_right (M.h * a) (-(M.p * a))
              have h3 := le_max_left (M.h * b) (-(M.p * b))
              have h4 := le_max_right (M.h * b) (-(M.p * b))
              have hθ1' : 0 ≤ 1 - θ := by linarith
              apply max_le
              · have e : M.h * ((1 - θ) * a + θ * b) = (1 - θ) * (M.h * a) + θ * (M.h * b) := by ring
                linarith [mul_le_mul_of_nonneg_left h1 hθ1', mul_le_mul_of_nonneg_left h3 hθ0]
              · have e : -(M.p * ((1 - θ) * a + θ * b)) = (1 - θ) * (-(M.p * a)) + θ * (-(M.p * b)) := by
                  ring
                linarith [mul_le_mul_of_nonneg_left h2 hθ1', mul_le_mul_of_nonneg_left h4 hθ0]
            have hGx : G x ≤ (1 - θ) * G u + θ * G v := by
              rw [hG, hG, hG, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_le_sum fun k _ => by rw [hxSB]; exact hRconv _ _
            apply hZ x hxnn j0 hj0 hsupp
            rw [hxSB]
            nlinarith
          have hvnn : ∀ k < M.T, 0 ≤ v k := by
            intro k hk
            by_cases hex : ∃ j ∈ Finset.Icc 1 J, t j = k
            · obtain ⟨j, hj, rfl⟩ := hex; exact (hvpos j hj).le
            · push_neg at hex; rw [hv0 k hex]
          have hviff : ∀ k < M.T, (0 < v k ↔ ∃ j ∈ Finset.Icc 1 J, t j = k) := by
            intro k hk; constructor
            · intro h; by_contra hex; push_neg at hex; rw [hv0 k hex] at h; exact lt_irrefl _ h
            · rintro ⟨j, hj, rfl⟩; exact hvpos j hj
          have hNCv : M.nominalCost w v ≤ M.nominalCost w u := by
            rw [hNC v hvnn, hNC u hun, hcard v hviff,
              hcard u (fun k hk => ⟨fun h => (htiff k).1 ⟨hk, h⟩, fun h => ((htiff k).2 h).2⟩)]
            linarith [hFv]
          obtain ⟨y', q', r', hopt⟩ := hfinal v hvnn hNCv
          refine ⟨v, y', q', r', hopt, ⟨hT1, htstep, fun k => ?_⟩, fun j hj => ?_⟩
          · constructor
            · rintro ⟨hk, hpos'⟩; exact (hviff k hk).1 hpos'
            · rintro ⟨j, hj, rfl⟩
              have := htstep j hj; have := htT j hj
              exact ⟨by omega, hvpos j hj⟩
          · have hj' := Finset.mem_Icc.1 hj
            exact ⟨hvs j hj'.1 hj'.2, hvB j hj⟩
