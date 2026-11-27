-- Prove2me | solution 1 for StochSQP.Vanishing.Supplement.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:11.313985+00:00
-- url     : https://prove2.me/submissions/c4b03324-e25e-4e9e-9a8f-fd4c47dae2da

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry

open StochSQP
open StochSQP.Vanishing
open StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem solution
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hJ : EventualFullRank P R)
    (κg : ℝ) (hκg : 0 < κg) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ≤ κg) :
    ConstantMerit R := by
      set_option maxHeartbeats 2000000 in
      classical
      rcases hA with ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1,
        hσ, hσ1, hετ, hετ1, hrest⟩
      rcases hP with ⟨hopen, hconv, hmn, hdf, hdc, hfup, hflo, hglip,
        hgb, hcb, hJlip, hJb⟩
      rcases hH with ⟨hκH, hζH, hHs⟩
      obtain ⟨G₀, hG₀, hbG⟩ := hgb.exists_pos_norm_le
      obtain ⟨C, hC, hbC⟩ := hcb.exists_pos_norm_le
      obtain ⟨B, hB, hbB⟩ := hJb.exists_pos_norm_le
      let G := κg + G₀
      have hG : 0 < G := by dsimp [G]; positivity
      have hgB (k : ℕ) : ‖R.g k‖ ≤ G := by
        have h := norm_add_le (R.g k - P.grad (R.x k)) (P.grad (R.x k))
        rw [sub_add_cancel] at h
        exact h.trans (add_le_add (hg k) (hbG _ ⟨R.x k, hx k, rfl⟩))
      have hcB (k : ℕ) : ‖P.c (R.x k)‖ ≤ C := hbC _ ⟨R.x k, hx k, rfl⟩
      have hJB (k : ℕ) : ‖P.J (R.x k)‖ ≤ B := hbB _ ⟨R.x k, hx k, rfl⟩
      have hJtB (k : ℕ) (z : E m) : ‖P.Jt (R.x k) z‖ ≤ B * ‖z‖ := by
        have h := (P.Jt (R.x k)).le_opNorm z
        have heq : ‖P.Jt (R.x k)‖ = ‖P.J (R.x k)‖ :=
          ContinuousLinearMap.adjoint.norm_map _
        rw [heq] at h
        exact h.trans (mul_le_mul_of_nonneg_right (hJB k) (norm_nonneg _))
      have hJu (k : ℕ) : P.J (R.x k) (R.u k) = 0 := (hrun k).2.2.2.2.2.2.1
      have hd (k : ℕ) : R.d k = R.v k + R.u k := (hrun k).2.2.2.2.2.2.2.1
      have hvB (k : ℕ) : ‖R.v k‖ ≤ A.ω * (B * C) := by
        exact (hrun k).2.2.2.1 |>.trans
          (mul_le_mul_of_nonneg_left ((hJtB k _).trans
            (mul_le_mul_of_nonneg_left (hcB k) hB.le)) hω.le)
      have hstat (k : ℕ) :
          ⟪R.u k, R.H k (R.u k)⟫_ℝ =
            -⟪R.g k, R.u k⟫_ℝ - ⟪R.u k, R.H k (R.v k)⟫_ℝ := by
        have hz : ⟪R.u k, P.Jt (R.x k) (R.y k)⟫_ℝ = 0 := by
          change ⟪R.u k, ContinuousLinearMap.adjoint (P.J (R.x k)) (R.y k)⟫_ℝ = 0
          rw [ContinuousLinearMap.adjoint_inner_right, hJu k, inner_zero_left]
        have he := congrArg (fun w => ⟪R.u k, w⟫_ℝ) ((hrun k).2.2.2.2.2.1)
        simp only [inner_add_right, inner_neg_right, hz] at he
        have hc := real_inner_comm (R.u k) (R.g k)
        linarith only [he, hc]
      let U := (G + κH * (A.ω * (B * C))) / ζH
      have hU : 0 < U := by dsimp [U]; positivity
      have huB (k : ℕ) : ‖R.u k‖ ≤ U := by
        have hco := (hHs k).2.2 (R.u k) (by change P.J (R.x k) (R.u k) = 0; exact hJu k)
        have hgu := real_inner_le_norm (-(R.g k)) (R.u k)
        have huv := real_inner_le_norm (R.u k) (-(R.H k (R.v k)))
        simp only [inner_neg_left, inner_neg_right, norm_neg] at hgu huv
        have hHv : ‖R.H k (R.v k)‖ ≤ κH * (A.ω * (B * C)) :=
          ((R.H k).le_opNorm _).trans
            (mul_le_mul (hHs k).2.1 (hvB k) (norm_nonneg _) hκH.le)
        have h1 := mul_le_mul_of_nonneg_right (hgB k) (norm_nonneg (R.u k))
        have h2 := mul_le_mul_of_nonneg_left hHv (norm_nonneg (R.u k))
        rw [hstat k] at hco
        have hh : ζH * ‖R.u k‖ ^ 2 ≤
            (G + κH * (A.ω * (B * C))) * ‖R.u k‖ := by nlinarith only [hco, hgu, huv, h1, h2]
        by_cases hz : ‖R.u k‖ = 0
        · rw [hz]; exact hU.le
        · have hp : 0 < ‖R.u k‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
          apply (le_div_iff₀ hζH).2
          nlinarith only [hh, hp]
      let D := A.ω * (G + κH * U)
      have hD : 0 < D := by dsimp [D]; positivity
      let den := fun k => ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ
      have hden (k : ℕ) : den k ≤ D * ‖P.Jt (R.x k) (P.c (R.x k))‖ := by
        have he : den k = ⟪R.g k, R.v k⟫_ℝ - ⟪R.u k, R.H k (R.v k)⟫_ℝ := by
          dsimp [den]
          rw [hd k, inner_add_right, hstat k]
          ring
        have h1 := real_inner_le_norm (R.g k) (R.v k)
        have h2 := real_inner_le_norm (-(R.u k)) (R.H k (R.v k))
        simp only [inner_neg_left, norm_neg] at h2
        have h3 : ‖R.H k (R.v k)‖ ≤ κH * ‖R.v k‖ :=
          ((R.H k).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hHs k).2.1 (norm_nonneg _))
        have h4 := mul_le_mul_of_nonneg_right (hgB k) (norm_nonneg (R.v k))
        have h5 := mul_le_mul (huB k) h3 (norm_nonneg _) hU.le
        have h6 := mul_le_mul_of_nonneg_left ((hrun k).2.2.2.1)
          (show 0 ≤ G + κH * U by positivity)
        rw [he]
        dsimp [D]
        nlinarith only [h1, h2, h4, h5, h6]
      let a := min A.ω (1 / (B ^ 2 + 1))
      have ha : 0 < a := by dsimp [a]; positivity
      have haω : a ≤ A.ω := min_le_left _ _
      have haB : a * B ^ 2 ≤ 1 := by
        have h := min_le_right A.ω (1 / (B ^ 2 + 1))
        have hh : 0 < B ^ 2 + 1 := by positivity
        have hh' : a * (B ^ 2 + 1) ≤ 1 := (le_div_iff₀ hh).1 h
        nlinarith only [hh', ha]
      let rad := fun k => ‖P.c (R.x k) + a • P.J (R.x k) (-(P.Jt (R.x k) (P.c (R.x k))))‖
      have hrad (k : ℕ) :
          (rad k) ^ 2 ≤ ‖P.c (R.x k)‖ ^ 2 - a * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 := by
        have hi : ⟪P.c (R.x k), P.J (R.x k) (-(P.Jt (R.x k) (P.c (R.x k))))⟫_ℝ =
            -‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 := by
          rw [map_neg, inner_neg_right]
          congr 1
          rw [← ContinuousLinearMap.adjoint_inner_left]
          change ⟪P.Jt (R.x k) (P.c (R.x k)), P.Jt (R.x k) (P.c (R.x k))⟫_ℝ = _
          exact real_inner_self_eq_norm_sq _
        have hz : ‖P.J (R.x k) (-(P.Jt (R.x k) (P.c (R.x k))))‖ ≤
            B * ‖P.Jt (R.x k) (P.c (R.x k))‖ := by
          simpa only [norm_neg] using ((P.J (R.x k)).le_opNorm (-(P.Jt (R.x k) (P.c (R.x k))))).trans
            (mul_le_mul_of_nonneg_right (hJB k) (norm_nonneg _))
        have hz2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hz
        have hm := mul_le_mul_of_nonneg_left hz2 (sq_nonneg a)
        have hm' := mul_le_mul_of_nonneg_right haB
          (show 0 ≤ a * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 by positivity)
        dsimp [rad]
        rw [norm_add_sq_real, inner_smul_right, hi, norm_smul,
          Real.norm_eq_abs, abs_of_pos ha]
        nlinarith only [hm, hm']
      have hradle (k : ℕ) : rad k ≤ ‖P.c (R.x k)‖ := by
        have h := hrad k
        have hp : 0 ≤ a * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 := by positivity
        have hn := norm_nonneg (P.c (R.x k))
        have hr : 0 ≤ rad k := norm_nonneg _
        nlinarith only [h, hp, hn, hr]
      let red := fun k => ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖
      have hred (k : ℕ) : A.εv * (‖P.c (R.x k)‖ - rad k) ≤ red k := by
        have h := (hrun k).2.2.2.2.1 a ⟨ha.le, haω⟩
        dsimp [red]
        rw [hd k, map_add, hJu k, add_zero]
        exact h
      have hredpos (k : ℕ) (hk : 0 < den k) : 0 < red k := by
        have hw : 0 < ‖P.Jt (R.x k) (P.c (R.x k))‖ := by
          have h := hden k
          nlinarith only [h, hk, hD]
        have hsq : 0 < a * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 := by positivity
        have hh := hrad k
        have hn := norm_nonneg (P.c (R.x k))
        have hr : 0 ≤ rad k := norm_nonneg _
        have hlt : rad k < ‖P.c (R.x k)‖ := by nlinarith only [hh, hsq, hn, hr]
        exact lt_of_lt_of_le (mul_pos hεv (sub_pos.mpr hlt)) (hred k)
      obtain ⟨kJ, s, hs, hRank⟩ := hJ
      let F := A.εv * (a * s ^ 2 / 2)
      have hF : 0 < F := by dsimp [F]; positivity
      have hredB (k : ℕ) (hk : kJ ≤ k) : F * ‖P.c (R.x k)‖ ≤ red k := by
        have hw := hRank k hk (P.c (R.x k))
        have hw2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hw
        have hh := mul_le_mul_of_nonneg_left hw2 ha.le
        have hr := hrad k
        have hrl := hradle k
        have hrl0 : 0 ≤ rad k := norm_nonneg _
        have hc0 := norm_nonneg (P.c (R.x k))
        have hbasic : a * s ^ 2 * ‖P.c (R.x k)‖ ^ 2 ≤
            2 * ‖P.c (R.x k)‖ * (‖P.c (R.x k)‖ - rad k) := by
          nlinarith only [hh, hr, sq_nonneg (‖P.c (R.x k)‖ - rad k)]
        have hlin : (a * s ^ 2 / 2) * ‖P.c (R.x k)‖ ≤ ‖P.c (R.x k)‖ - rad k := by
          by_cases hc : ‖P.c (R.x k)‖ = 0
          · simpa only [hc, mul_zero] using sub_nonneg.mpr hrl
          · have hcpos : 0 < ‖P.c (R.x k)‖ := lt_of_le_of_ne hc0 (Ne.symm hc)
            nlinarith only [hbasic, hcpos]
        exact (by dsimp [F]; nlinarith only [mul_le_mul_of_nonneg_left hlin hεv.le] :
          F * ‖P.c (R.x k)‖ ≤ A.εv * (‖P.c (R.x k)‖ - rad k)) |>.trans (hred k)
      let T := (1 - A.σ) * F / (D * B)
      have hT : 0 < T := by dsimp [T]; positivity
      let trial := fun k => (1 - A.σ) * red k / den k
      have htrial (k : ℕ) (hk : 0 < den k) : 0 < trial k := by
        dsimp [trial]
        exact div_pos (mul_pos (sub_pos.mpr hσ1) (hredpos k hk)) hk
      have htrialB (k : ℕ) (hk : kJ ≤ k) (hp : 0 < den k) : T ≤ trial k := by
        have hdc : den k ≤ D * (B * ‖P.c (R.x k)‖) :=
          (hden k).trans (mul_le_mul_of_nonneg_left (hJtB k _) hD.le)
        apply (le_div_iff₀ hp).2
        calc
          T * den k ≤ T * (D * (B * ‖P.c (R.x k)‖)) :=
            mul_le_mul_of_nonneg_left hdc hT.le
          _ = (1 - A.σ) * (F * ‖P.c (R.x k)‖) := by
            dsimp [T]
            field_simp [ne_of_gt hD, ne_of_gt hB]
          _ ≤ (1 - A.σ) * red k :=
            mul_le_mul_of_nonneg_left (hredB k hk) (sub_nonneg.mpr hσ1.le)
      let q := 1 - A.ετ
      have hq : 0 < q := sub_pos.mpr hετ1
      have hq1 : q < 1 := by dsimp [q]; linarith
      have hupdate (k : ℕ) : R.τ k = prev R.τ A.τ₀ k ∨
          (R.τ k = min (q * prev R.τ A.τ₀ k) (trial k) ∧
            0 < trial k ∧ trial k < prev R.τ A.τ₀ k ∧
            (kJ ≤ k → T ≤ trial k)) := by
        by_cases hd0 : R.d k = 0
        · exact Or.inl (((hrun k).2.2.2.2.2.2.2.2.1 hd0).1)
        · have ht := ((hrun k).2.2.2.2.2.2.2.2.2.1 hd0).1
          by_cases hp : 0 < den k
          · have hrule := ht.2 hp
            change (prev R.τ A.τ₀ k ≤ trial k → R.τ k = prev R.τ A.τ₀ k) ∧
              (trial k < prev R.τ A.τ₀ k → R.τ k = min (q * prev R.τ A.τ₀ k) (trial k)) at hrule
            by_cases he : prev R.τ A.τ₀ k ≤ trial k
            · exact Or.inl (hrule.1 he)
            · exact Or.inr ⟨hrule.2 (lt_of_not_ge he), htrial k hp,
                lt_of_not_ge he, fun hk => htrialB k hk hp⟩
          · exact Or.inl (ht.1 (le_of_not_gt hp))
      have hτpos : ∀ k, 0 < R.τ k := by
        intro k
        induction k with
        | zero =>
          rcases hupdate 0 with he | ⟨he, ht, hlt, hb⟩
          · rw [he]; exact hτ0
          · rw [he]
            exact lt_min (mul_pos hq hτ0) ht
        | succ k ih =>
          rcases hupdate (k + 1) with he | ⟨he, ht, hlt, hb⟩
          · rw [he]; exact ih
          · rw [he]
            exact lt_min (mul_pos hq ih) ht
      let l := min (R.τ kJ) (q * T)
      have hl : 0 < l := lt_min (hτpos kJ) (mul_pos hq hT)
      have hlower : ∀ i : ℕ, l ≤ R.τ (kJ + i) := by
        intro i
        induction i with
        | zero => simpa only [Nat.add_zero] using (min_le_left (R.τ kJ) (q * T))
        | succ i ih =>
          rcases hupdate (kJ + i + 1) with he | ⟨he, ht, hlt, hb⟩
          · rw [Nat.add_succ, he]; exact ih
          · have htB := hb (by omega)
            have hp : T ≤ prev R.τ A.τ₀ (kJ + i + 1) := htB.trans hlt.le
            have hqT : q * T ≤ T := by nlinarith only [hq1, hT]
            have hlow : q * T ≤ R.τ (kJ + i + 1) := by
              rw [he]
              exact le_min (mul_le_mul_of_nonneg_left hp hq.le) (hqT.trans htB)
            exact (min_le_right (R.τ kJ) (q * T)).trans (by simpa only [Nat.add_succ] using hlow)
      let S : Set ℝ := Set.range (fun i : ℕ => R.τ (kJ + i))
      have hSne : S.Nonempty := ⟨R.τ (kJ + 0), ⟨0, rfl⟩⟩
      have hSlower : ∀ z ∈ S, l ≤ z := by
        rintro z ⟨i, rfl⟩
        exact hlower i
      have hSb : BddBelow S := ⟨l, hSlower⟩
      let b := sInf S
      have hb : 0 < b := hl.trans_le (le_csInf hSne hSlower)
      have hbq : b < b / q := by
        apply (lt_div_iff₀ hq).2
        nlinarith only [hq1, hb]
      obtain ⟨z, ⟨i, rfl⟩, hi⟩ := exists_lt_of_csInf_lt hSne hbq
      let K := kJ + i
      have hK : q * R.τ K < b := by
        have hh := (lt_div_iff₀ hq).1 hi
        dsimp [K]
        nlinarith only [hh]
      have hconst : ∀ j : ℕ, R.τ (K + j) = R.τ K := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rcases hupdate (K + j + 1) with he | ⟨he, ht, hlt, hbound⟩
          · simpa only [prev, ih, Nat.add_succ] using he
          · have hprev : prev R.τ A.τ₀ (K + j + 1) = R.τ K := by simpa only [prev] using ih
            have hltb : R.τ (K + j + 1) < b :=
              lt_of_le_of_lt (by rw [he, hprev]; exact min_le_left _ _) hK
            have hmem : R.τ (K + j + 1) ∈ S := by
              refine ⟨i + j + 1, ?_⟩
              dsimp [K]
              congr 1 <;> omega
            exact False.elim (not_lt_of_ge (csInf_le hSb hmem) hltb)
      refine ⟨K, R.τ K, hτpos K, ?_⟩
      intro k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact hconst j
