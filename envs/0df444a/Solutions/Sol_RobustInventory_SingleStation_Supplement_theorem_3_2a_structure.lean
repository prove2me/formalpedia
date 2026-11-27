-- Prove2me | solution 1 for RobustInventory.SingleStation.Supplement.theorem_3_2a_structure
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:49.818904+00:00
-- url     : https://prove2.me/submissions/4cd33e90-fccc-49cd-a097-2ea4d22dfc15

import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust
import Definitions.Def_RobustInventory_SingleStation_Supplement_Policy

open RobustInventory
open RobustInventory.SingleStation
open RobustInventory.SingleStation.Supplement

/-- Theorem 3.2(a), last sentence, p. 155: the optimal robust policy is `(s, S)` on the modified
stock, and `(S, S)` without fixed cost. There are thresholds `s_k ≤ S_k`, chosen before any
stock, with `s_k = S_k` if `K = 0`, whose rule is optimal for the modified nominal problem that
remains from every period and every stock, and whose orders from every initial stock `x₀` are
the order part of an optimal solution of (14) with that initial stock. -/
theorem solution (M : Model) :
    ∃ s S : ℕ → ℝ,
      (∀ k < M.T, s k ≤ S k) ∧
      (M.K = 0 → ∀ k < M.T, s k = S k) ∧
      (∀ k < M.T, ∀ x : ℝ, IsTailOptimal M M.wmod k x (sSPolicy s S M.wmod k x)) ∧
      ∀ x₀ : ℝ, ∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ),
        ({ M with x0 := x₀ } : Model).IsRobustOptimal (sSPolicy s S M.wmod 0 x₀) y q r := by
          classical
          have hC0 : ∀ u, 0 ≤ M.C u := by
            intro u; unfold Model.C; split_ifs with h
            · have := M.hK; have := M.hc; nlinarith
            · exact le_refl _
          have hR0 : ∀ z, 0 ≤ M.R z := by
            intro z; unfold Model.R
            rcases le_total 0 z with hz | hz
            · exact le_max_of_le_left (mul_nonneg M.hh hz)
            · exact le_max_of_le_right (by nlinarith [M.hc, M.hpc])
          have hRh : ∀ z, M.h * z ≤ M.R z := fun z => le_max_left _ _
          have hRp : ∀ z, -(M.p * z) ≤ M.R z := fun z => le_max_right _ _
          have hRc : Continuous M.R :=
            (continuous_const.mul continuous_id).max ((continuous_const.mul continuous_id).neg)
          have hRconv : ∀ a x b : ℝ, a ≤ x → x ≤ b →
              (b - a) * M.R x ≤ (b - x) * M.R a + (x - a) * M.R b := by
            intro a x b hax hxb
            have h1 := mul_le_mul_of_nonneg_left (hRh a) (sub_nonneg.2 hxb)
            have h2 := mul_le_mul_of_nonneg_left (hRh b) (sub_nonneg.2 hax)
            have h3 := mul_le_mul_of_nonneg_left (hRp a) (sub_nonneg.2 hxb)
            have h4 := mul_le_mul_of_nonneg_left (hRp b) (sub_nonneg.2 hax)
            have : M.R x = M.h * x ∨ M.R x = -(M.p * x) := by
              unfold Model.R; rcases le_total (M.h * x) (-(M.p*x)) with h | h
              · right; exact max_eq_right h
              · left; exact max_eq_left h
            rcases this with h | h <;> rw [h] <;> nlinarith
          have htc0 : ∀ w k x u, 0 ≤ tailCost M w k x u := fun w k x u =>
            Finset.sum_nonneg fun i _ => add_nonneg (hC0 _) (hR0 _)
          have hord0 : ∀ a b x : ℝ, a ≤ b → 0 ≤ sSOrder a b x := by
            intro a b x hab; unfold sSOrder; split_ifs with h
            · linarith
            · exact le_refl _
          obtain ⟨KC, hKC⟩ : ∃ KC : (ℝ → ℝ) → Prop, ∀ f, KC f ↔ ∀ a x b : ℝ, a ≤ x → x ≤ b →
              (b - a) * f x ≤ (b - x) * f a + (x - a) * (f b + M.K) := ⟨_, fun _ => Iff.rfl⟩
          have hdet : ∀ w : ℕ → ℝ, ∃ s S : ℕ → ℝ, (∀ k < M.T, s k ≤ S k) ∧
              (M.K = 0 → ∀ k < M.T, s k = S k) ∧
              ∀ k < M.T, ∀ x, IsTailOptimal M w k x (sSPolicy s S w k x) := by
            intro w
            have hTCcongr : ∀ j x (u v : ℕ → ℝ), (∀ i, j ≤ i → u i = v i) →
                tailCost M w j x u = tailCost M w j x v := by
              intro j x u v huv
              unfold tailCost tailStock
              refine Finset.sum_congr rfl fun i hi => ?_
              have hi' := (Finset.mem_Ico.1 hi).1
              rw [huv i hi', Finset.sum_congr rfl (g := fun l => v l - w l) (fun l hl => by rw [huv l (Finset.mem_Ico.1 hl).1])]
            have hTOcongr : ∀ j x (u v : ℕ → ℝ), (∀ i, j ≤ i → u i = v i) →
                IsTailOptimal M w j x u → IsTailOptimal M w j x v := by
              intro j x u v huv ⟨h1, h2⟩
              refine ⟨fun i hi => (huv i (Finset.mem_Ico.1 hi).1) ▸ h1 i hi, fun u' hu' => ?_⟩
              rw [← hTCcongr j x u v huv]; exact h2 u' hu'
            have hD : ∀ k < M.T, ∀ x (u : ℕ → ℝ), tailCost M w k x u =
                M.C (u k) + M.R (x + u k - w k) + tailCost M w (k+1) (x + u k - w k) u := by
              intro k hk x u
              unfold tailCost
              rw [Finset.sum_eq_sum_Ico_succ_bot hk]
              have e1 : tailStock w u k x k = x + u k - w k := by
                unfold tailStock; simp; ring
              have e2 : ∀ i ∈ Finset.Ico (k+1) M.T, tailStock w u k x i = tailStock w u (k+1) (x + u k - w k) i := by
                intro i hi
                have hi' := (Finset.mem_Ico.1 hi).1
                unfold tailStock
                rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k < i + 1)]
                ring
              rw [e1, Finset.sum_congr rfl (fun i hi => by rw [e2 i hi])]
            have hstep : ∀ n, n ≤ M.T → ∃ s S : ℕ → ℝ, ∃ V : ℝ → ℝ,
                (∀ j, M.T - n ≤ j → j < M.T → s j ≤ S j ∧ (M.K = 0 → s j = S j)) ∧
                (∀ j, M.T - n ≤ j → j < M.T → ∀ x, IsTailOptimal M w j x (sSPolicy s S w j x)) ∧
                (∀ x, tailCost M w (M.T - n) x (sSPolicy s S w (M.T - n) x) = V x) ∧
                (∀ x (u' : ℕ → ℝ), (∀ i ∈ Finset.Ico (M.T - n) M.T, 0 ≤ u' i) →
                  V x ≤ tailCost M w (M.T - n) x u') ∧
                Continuous V ∧ KC V := by
              intro n
              induction n with
              | zero =>
                intro _
                refine ⟨0, 0, 0, fun j h1 h2 => by omega, fun j h1 h2 => by omega, ?_, ?_,
                  continuous_const, ?_⟩
                · intro x; simp [tailCost]
                · intro x u' _; simp [tailCost]
                · rw [hKC]; intro a x b hax hxb; simp; nlinarith [M.hK]
              | succ n ih =>
                intro hn
                obtain ⟨s, S, V, ha, hb, hc, hd, hVc, hVK⟩ := ih (by omega)
                obtain ⟨k, hk⟩ : ∃ k, k = M.T - (n+1) := ⟨_, rfl⟩
                rw [← hk]
                have hk1 : M.T - n = k + 1 := by omega
                have hkT : k < M.T := by omega
                rw [hk1] at ha hb hc hd
                have hVK' := (hKC V).1 hVK
                obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun y => M.c * y + M.R (y - w k) + V (y - w k) :=
                  ⟨_, rfl⟩
                have hGy : ∀ y, G y = M.c * y + M.R (y - w k) + V (y - w k) := fun y => by rw [hG]
                have hGc : Continuous G := by
                  rw [hG]; exact ((continuous_const.mul continuous_id).add (hRc.comp
                    (continuous_id.sub continuous_const))).add (hVc.comp (continuous_id.sub continuous_const))
                have hV0 : ∀ z, 0 ≤ V z := fun z => (hc z) ▸ htc0 _ _ _ _
                have hGlo1 : ∀ y, M.c * y ≤ G y := fun y => by
                  rw [hGy]; linarith [hR0 (y - w k), hV0 (y - w k)]
                have hGlo2 : ∀ y, (M.c - M.p) * y + M.p * w k ≤ G y := fun y => by
                  rw [hGy]; nlinarith [hRp (y - w k), hV0 (y - w k)]
                have hGK' : ∀ a x b : ℝ, a ≤ x → x ≤ b →
                    (b - a) * G x ≤ (b - x) * G a + (x - a) * (G b + M.K) := by
                  intro a x b hax hxb
                  have h1 := hVK' (a - w k) (x - w k) (b - w k) (by linarith) (by linarith)
                  have h2 := hRconv (a - w k) (x - w k) (b - w k) (by linarith) (by linarith)
                  simp only [sub_sub_sub_cancel_right] at h1 h2
                  rw [hGy, hGy, hGy]
                  nlinarith
                obtain ⟨S0, hS0⟩ : ∃ S0, ∀ y, G S0 ≤ G y := by
                  have hc := M.hc; have hpc := M.hpc
                  obtain ⟨U, hU⟩ : ∃ U, U = |G 0| / M.c := ⟨_, rfl⟩
                  obtain ⟨L, hL⟩ : ∃ L, L = -((|G 0| + |M.p * w k|) / (M.p - M.c)) := ⟨_, rfl⟩
                  have hU0 : 0 ≤ U := by rw [hU]; exact div_nonneg (abs_nonneg _) hc.le
                  have hL0 : L ≤ 0 := by
                    have := div_nonneg (add_nonneg (abs_nonneg (G 0)) (abs_nonneg (M.p * w k)))
                      (sub_pos.2 hpc).le
                    rw [hL]; linarith
                  obtain ⟨S0, -, hmin⟩ := isCompact_Icc.exists_isMinOn
                    (⟨0, hL0, hU0⟩ : (Set.Icc L U).Nonempty) hGc.continuousOn
                  rw [isMinOn_iff] at hmin
                  refine ⟨S0, fun y => ?_⟩
                  have h0 : G S0 ≤ G 0 := hmin 0 ⟨hL0, hU0⟩
                  by_cases hy : y ∈ Set.Icc L U
                  · exact hmin y hy
                  · simp only [Set.mem_Icc, not_and_or, not_le] at hy
                    rcases hy with hy | hy
                    · have h1 := hGlo2 y
                      have e : (M.p - M.c) * L = -(|G 0| + |M.p * w k|) := by
                        rw [hL]; field_simp [(sub_pos.2 hpc).ne']
                      have h3 : (M.c - M.p) * y ≥ |G 0| + |M.p * w k| := by nlinarith
                      have := le_abs_self (G 0); have := neg_abs_le (M.p * w k)
                      linarith
                    · have h1 := hGlo1 y
                      have e : M.c * U = |G 0| := by rw [hU]; field_simp
                      have := le_abs_self (G 0)
                      nlinarith
                obtain ⟨s0, hsS, hGs0, hsK, hP2, hP3⟩ : ∃ s0, s0 ≤ S0 ∧ G s0 = G S0 + M.K ∧
                    (M.K = 0 → s0 = S0) ∧ (∀ x, x < s0 → G S0 + M.K ≤ G x) ∧
                    (∀ x, s0 ≤ x → x ≤ S0 → G x ≤ G S0 + M.K) := by
                  rcases eq_or_lt_of_le M.hK with hK0 | hKpos
                  · refine ⟨S0, le_refl _, by rw [← hK0]; ring, fun _ => rfl,
                      fun x _ => by rw [← hK0]; simpa using hS0 x,
                      fun x h1 h2 => by rw [le_antisymm h2 h1, ← hK0]; simp⟩
                  · obtain ⟨Y, hY⟩ : ∃ Y, Y = -((|G S0 + M.K| + |M.p * w k|) / (M.p - M.c)) := ⟨_, rfl⟩
                    have hpc := M.hpc
                    have hy0 : G S0 + M.K ≤ G (min S0 Y) := by
                      have h1 := hGlo2 (min S0 Y)
                      have e : (M.p - M.c) * Y = -(|G S0 + M.K| + |M.p * w k|) := by
                        rw [hY]; field_simp [(sub_pos.2 hpc).ne']
                      have h2 : min S0 Y ≤ Y := min_le_right _ _
                      have h3 : (M.c - M.p) * (min S0 Y) ≥ (M.c - M.p) * Y := by nlinarith
                      have := le_abs_self (G S0 + M.K); have := neg_abs_le (M.p * w k)
                      linarith
                    obtain ⟨s0, ⟨hs1, hs2⟩, hs3⟩ := intermediate_value_Icc' (min_le_left S0 Y)
                      hGc.continuousOn ⟨by linarith, hy0⟩
                    have hlt : s0 < S0 := by
                      rcases eq_or_lt_of_le hs2 with h | h
                      · rw [h] at hs3; linarith
                      · exact h
                    refine ⟨s0, hs2, hs3, fun h => by linarith, fun x hx => ?_, fun x hx1 hx2 => ?_⟩
                    · have h := hGK' x s0 S0 hx.le hs2
                      rw [hs3] at h
                      by_contra hcon; push Not at hcon
                      have := mul_lt_mul_of_pos_left hcon (sub_pos.2 hlt)
                      nlinarith
                    · have h := hGK' s0 x S0 hx1 hx2
                      rw [hs3] at h
                      by_contra hcon; push Not at hcon
                      have := mul_lt_mul_of_pos_left hcon (sub_pos.2 hlt)
                      nlinarith
                have hP5 : ∀ x y, s0 ≤ x → x ≤ y → G x ≤ G y + M.K := by
                  intro x y hx hxy
                  by_cases hxS : x ≤ S0
                  · linarith [hP3 x hx hxS, hS0 y]
                  · push Not at hxS
                    have h := hGK' S0 x y hxS.le hxy
                    have hy := hS0 y
                    have hpos : 0 < y - S0 := by linarith
                    by_contra hcon; push Not at hcon
                    have := mul_lt_mul_of_pos_left hcon hpos
                    nlinarith [mul_nonneg (sub_nonneg.2 hxy) (by linarith [M.hK] : 0 ≤ G y + M.K - G S0)]
                obtain ⟨s', hs'⟩ : ∃ s' : ℕ → ℝ, s' = Function.update s k s0 := ⟨_, rfl⟩
                obtain ⟨S', hS'⟩ : ∃ S' : ℕ → ℝ, S' = Function.update S k S0 := ⟨_, rfl⟩
                have hsk : s' k = s0 := by rw [hs']; simp
                have hSk : S' k = S0 := by rw [hS']; simp
                have hsne : ∀ j, j ≠ k → s' j = s j := fun j hj => by rw [hs', Function.update_of_ne hj]
                have hSne : ∀ j, j ≠ k → S' j = S j := fun j hj => by rw [hS', Function.update_of_ne hj]
                have hstk : ∀ j, k + 1 ≤ j → ∀ x n, sSStock s' S' w j x n = sSStock s S w j x n := by
                  intro j hj x n
                  induction n with
                  | zero => rfl
                  | succ n ihn =>
                    simp only [sSStock, ihn]
                    rw [hsne _ (by omega), hSne _ (by omega)]
                have hpol : ∀ j, k + 1 ≤ j → ∀ x i, j ≤ i → sSPolicy s' S' w j x i = sSPolicy s S w j x i := by
                  intro j hj x i hi
                  unfold sSPolicy; rw [hstk j hj, hsne _ (by omega), hSne _ (by omega)]
                have hshift : ∀ x n, sSStock s' S' w k x (n+1) =
                    sSStock s' S' w (k+1) (x + sSOrder s0 S0 x - w k) n := by
                  intro x n
                  induction n with
                  | zero => simp [sSStock, hsk, hSk]
                  | succ n ihn =>
                    have e : k + (n + 1) = k + 1 + n := by omega
                    calc sSStock s' S' w k x (n + 1 + 1) = sSStock s' S' w k x (n+1) +
                        sSOrder (s' (k + (n+1))) (S' (k + (n+1))) (sSStock s' S' w k x (n+1)) - w (k + (n+1)) := rfl
                      _ = _ := by rw [ihn, e]; rfl
                have hpk : ∀ x, sSPolicy s' S' w k x k = sSOrder s0 S0 x := by
                  intro x; simp [sSPolicy, sSStock, hsk, hSk]
                have hpk1 : ∀ x i, k + 1 ≤ i → sSPolicy s' S' w k x i =
                    sSPolicy s S w (k+1) (x + sSOrder s0 S0 x - w k) i := by
                  intro x i hi
                  rw [← hpol (k+1) le_rfl _ i hi]
                  unfold sSPolicy
                  rw [show i - k = (i - (k+1)) + 1 by omega, hshift]
                have hCz : M.C 0 = 0 := by simp [Model.C]
                have hval : ∀ x, tailCost M w k x (sSPolicy s' S' w k x) = G (max x s0) - M.c * x := by
                  intro x
                  rw [hD k hkT, hpk, hTCcongr (k+1) _ _ _ (fun i hi => hpk1 x i hi), hc]
                  by_cases h1 : x < s0
                  · have ho : sSOrder s0 S0 x = S0 - x := if_pos h1
                    have hpos : 0 < S0 - x := by linarith
                    rw [ho, show x + (S0 - x) - w k = S0 - w k by ring, max_eq_right h1.le, hGs0, hGy]
                    simp only [Model.C, if_pos hpos]; ring
                  · have ho : sSOrder s0 S0 x = 0 := if_neg h1
                    push Not at h1
                    rw [ho, max_eq_left h1, hCz, hGy]; ring_nf
                have hopt : ∀ x (u' : ℕ → ℝ), (∀ i ∈ Finset.Ico k M.T, 0 ≤ u' i) →
                    G (max x s0) - M.c * x ≤ tailCost M w k x u' := by
                  intro x u' hu'
                  rw [hD k hkT]
                  have h1 := hd (x + u' k - w k) u' (fun i hi => hu' i (by simp at hi ⊢; omega))
                  have hu0 : 0 ≤ u' k := hu' k (by simp; omega)
                  suffices G (max x s0) - M.c * x ≤ M.C (u' k) + M.R (x + u' k - w k) + V (x + u' k - w k) by
                    linarith
                  rcases eq_or_lt_of_le hu0 with h0 | h0
                  · rw [← h0, hCz, add_zero]
                    have := hGy x
                    by_cases hx : x < s0
                    · rw [max_eq_right hx.le, hGs0]; linarith [hP2 x hx]
                    · push Not at hx; rw [max_eq_left hx]; linarith
                  · simp only [Model.C, if_pos h0]
                    have := hGy (x + u' k)
                    by_cases hx : x < s0
                    · rw [max_eq_right hx.le, hGs0]; linarith [hS0 (x + u' k)]
                    · push Not at hx; rw [max_eq_left hx]; linarith [hP5 x (x + u' k) hx (by linarith)]
                have hHK : ∀ a x b : ℝ, a ≤ x → x ≤ b → (b - a) * G (max x s0) ≤
                    (b - x) * G (max a s0) + (x - a) * (G (max b s0) + M.K) := by
                  intro a x b hax hxb
                  by_cases ha : s0 ≤ a
                  · rw [max_eq_left ha, max_eq_left (ha.trans hax), max_eq_left (ha.trans (hax.trans hxb))]
                    exact hGK' a x b hax hxb
                  · push Not at ha
                    rw [max_eq_right ha.le, hGs0]
                    have hb := hS0 (max b s0)
                    by_cases hx : x < s0
                    · rw [max_eq_right hx.le, hGs0]
                      nlinarith [mul_nonneg (sub_nonneg.2 hax) (sub_nonneg.2 hb)]
                    · push Not at hx
                      rw [max_eq_left hx, max_eq_left (hx.trans hxb)]
                      rw [max_eq_left (hx.trans hxb)] at hb
                      by_cases hxS : x ≤ S0
                      · have := hP3 x hx hxS
                        nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ b - a),
                          mul_nonneg (sub_nonneg.2 hax) (by linarith : 0 ≤ G b - G S0)]
                      · push Not at hxS
                        have h := hGK' S0 x b hxS.le hxb
                        have hD0 : 0 ≤ G b + M.K - G S0 := by linarith [M.hK]
                        have hgD : G x - G S0 ≤ G b + M.K - G S0 := by
                          by_contra hcon; push Not at hcon
                          have := mul_lt_mul_of_pos_left hcon (by linarith : (0:ℝ) < b - S0)
                          nlinarith [mul_le_mul_of_nonneg_right (by linarith : x - S0 ≤ b - S0) hD0]
                        nlinarith [mul_le_mul_of_nonneg_left hgD (by linarith : (0:ℝ) ≤ S0 - a),
                          mul_nonneg (sub_nonneg.2 hxb) M.hK]
                have hthr : ∀ j, k ≤ j → j < M.T → s' j ≤ S' j ∧ (M.K = 0 → s' j = S' j) := by
                  intro j hj1 hj2
                  by_cases hj : j = k
                  · rw [hj, hsk, hSk]; exact ⟨hsS, hsK⟩
                  · rw [hsne j hj, hSne j hj]; exact ha j (by omega) hj2
                refine ⟨s', S', fun x => G (max x s0) - M.c * x, hthr, ?_, hval, hopt, ?_, ?_⟩
                · intro j hj1 hj2 x
                  by_cases hj : j = k
                  · rw [hj]
                    refine ⟨fun i hi => ?_, fun u' hu' => (hval x) ▸ hopt x u' hu'⟩
                    have hi' := Finset.mem_Ico.1 hi
                    exact hord0 _ _ _ (hthr i hi'.1 hi'.2).1
                  · exact hTOcongr j x _ _ (fun i hi => (hpol j (by omega) x i hi).symm)
                      (hb j (by omega) hj2 x)
                · exact (hGc.comp (continuous_id.max continuous_const)).sub (continuous_const.mul continuous_id)
                · rw [hKC]; intro a x b hax hxb
                  have := hHK a x b hax hxb
                  nlinarith
            obtain ⟨s, S, V, ha, hb, -⟩ := hstep M.T le_rfl
            refine ⟨s, S, fun k hk => (ha k (by omega) hk).1, fun hK k hk => (ha k (by omega) hk).2 hK,
              fun k hk x => hb k (by omega) hk x⟩
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
          obtain ⟨s, S, h1, h2, h3⟩ := hdet M.wmod
          refine ⟨s, S, h1, h2, h3, fun x₀ => ?_⟩
          choose qf rf hqf using hdual
          obtain ⟨u, hu⟩ : ∃ u, u = sSPolicy s S M.wmod 0 x₀ := ⟨_, rfl⟩
          rw [← hu]
          have hpos : 0 < M.p + M.h := by linarith [M.hc, M.hpc, M.hh]
          have htele : ∀ k, ∑ i ∈ Finset.range (k+1), (M.A i - M.Aprev i) = M.A k := by
            intro k; induction k with
            | zero => simp [Model.Aprev]
            | succ k ih => rw [Finset.sum_range_succ, ih]; simp [Model.Aprev]
          have hstock : ∀ (v : ℕ → ℝ) k, x₀ + ∑ i ∈ Finset.range (k+1), (v i - M.wmod i) =
              (x₀ + ∑ i ∈ Finset.range (k+1), (v i - M.wbar i)) - (M.p - M.h) / (M.p + M.h) * M.A k := by
            intro v k
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
          have hTO : ∀ u' : ℕ → ℝ, (∀ k < M.T, 0 ≤ u' k) →
              tailCost M M.wmod 0 x₀ u ≤ tailCost M M.wmod 0 x₀ u' := by
            intro u' hu'
            rcases Nat.eq_zero_or_pos M.T with hT | hT
            · simp [tailCost, hT]
            · rw [hu]; exact (h3 0 hT x₀).2 u' (fun i hi => hu' i (Finset.mem_Ico.1 hi).2)
          have htc : ∀ v : ℕ → ℝ, tailCost M M.wmod 0 x₀ v = ∑ k ∈ Finset.range M.T,
              (M.C (v k) + M.R (x₀ + ∑ i ∈ Finset.range (k+1), (v i - M.wmod i))) := by
            intro v; unfold tailCost tailStock; simp only [Finset.range_eq_Ico]
          have hun : ∀ k < M.T, 0 ≤ u k := fun k hk => by
            rw [hu]; exact hord0 _ _ _ (h1 k hk)
          refine ⟨fun k => max (M.h * ((x₀ + ∑ i ∈ Finset.range (k+1), (u i - M.wbar i)) + M.A k))
            (M.p * (-(x₀ + ∑ i ∈ Finset.range (k+1), (u i - M.wbar i)) + M.A k)), qf,
            fun i k => rf k i, ?_, ?_⟩
          · intro k hk
            obtain ⟨⟨hq0, hr⟩, he⟩ := hqf k
            refine ⟨hun k hk, hq0, hr, ?_, ?_⟩
            · show M.h * (_ + qf k * M.Γ k + _) ≤ _
              rw [add_assoc, he]; exact le_max_left _ _
            · show M.p * (_ + qf k * M.Γ k + _) ≤ _
              rw [add_assoc, he]; exact le_max_right _ _
          · intro u' y' q' r' hF
            have hyk : ∀ k < M.T, M.R (x₀ + ∑ i ∈ Finset.range (k+1), (u' i - M.wmod i)) +
                2 * M.p * M.h / (M.p + M.h) * M.A k ≤ y' k := by
              intro k hk
              obtain ⟨_, hq, hr, hy1, hy2⟩ := hF k hk
              have hw := hweak k (q' k) (fun i => r' i k) ⟨hq, hr⟩
              rw [hstock, ← hmax]
              have hxb : ({ M with x0 := x₀ } : Model).xbar u' k =
                  x₀ + ∑ i ∈ Finset.range (k+1), (u' i - M.wbar i) := rfl
              rw [hxb] at hy1 hy2
              apply max_le
              · nlinarith [mul_le_mul_of_nonneg_left hw M.hh]
              · nlinarith [mul_le_mul_of_nonneg_left hw (by linarith [M.hc, M.hpc] : (0:ℝ) ≤ M.p)]
            have hu'n : ∀ k < M.T, 0 ≤ u' k := fun k hk => (hF k hk).1
            have key := hTO u' hu'n
            rw [htc, htc] at key
            show ∑ k ∈ Finset.range M.T, (M.C (u k) + _) ≤ ∑ k ∈ Finset.range M.T, (M.C (u' k) + y' k)
            have e : ∀ k, max (M.h * ((x₀ + ∑ i ∈ Finset.range (k+1), (u i - M.wbar i)) + M.A k))
                (M.p * (-(x₀ + ∑ i ∈ Finset.range (k+1), (u i - M.wbar i)) + M.A k)) =
                M.R (x₀ + ∑ i ∈ Finset.range (k+1), (u i - M.wmod i)) +
                2 * M.p * M.h / (M.p + M.h) * M.A k := fun k => by rw [hstock, hmax]
            simp only [e]
            have hle : ∑ k ∈ Finset.range M.T, (M.C (u' k) + (M.R (x₀ + ∑ i ∈ Finset.range (k+1),
                (u' i - M.wmod i)) + 2 * M.p * M.h / (M.p + M.h) * M.A k)) ≤
                ∑ k ∈ Finset.range M.T, (M.C (u' k) + y' k) :=
              Finset.sum_le_sum fun k hk => by linarith [hyk k (Finset.mem_range.1 hk)]
            have s1 : ∀ v : ℕ → ℝ, ∑ k ∈ Finset.range M.T, (M.C (v k) + (M.R (x₀ + ∑ i ∈ Finset.range (k+1),
                (v i - M.wmod i)) + 2 * M.p * M.h / (M.p + M.h) * M.A k)) =
                ∑ k ∈ Finset.range M.T, (M.C (v k) + M.R (x₀ + ∑ i ∈ Finset.range (k+1),
                (v i - M.wmod i))) + ∑ k ∈ Finset.range M.T, 2 * M.p * M.h / (M.p + M.h) * M.A k := by
              intro v; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
            rw [s1] at hle ⊢
            linarith
