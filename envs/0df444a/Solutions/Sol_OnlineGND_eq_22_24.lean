-- Prove2me | solution 1 for OnlineGND.eq_22_24
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:27:20.511831+00:00
-- url     : https://prove2.me/submissions/3158344c-cab2-4415-91b9-8204fff6c972

import Definitions.Def_OnlineGND_DualFitting

namespace Aux_OnlineGND_eq_22_24

open OnlineGND

noncomputable def phi (c a ρ x : ℝ) : ℝ := if a = 1 then Real.exp 1 * ρ * c * x else c * x ^ a

lemma phi_zero (c a ρ : ℝ) (ha : 1 ≤ a) : phi c a ρ 0 = 0 := by
  unfold phi
  split_ifs
  · ring
  · rw [Real.zero_rpow (show a ≠ 0 from (by linarith : (0:ℝ) < a).ne')]; ring

/-- `(x+w)^a - x^a ≤ a (x+w)^(a-1) w`. -/
lemma bern (a x w : ℝ) (ha : 1 ≤ a) (hx : 0 ≤ x) (hw : 0 < w) :
    (x + w) ^ a - x ^ a ≤ a * (x + w) ^ (a - 1) * w := by
  have hs : 0 < x + w := by linarith
  have ht : -1 ≤ -w / (x + w) := by
    rw [neg_div, neg_le_neg_iff, div_le_one hs]; linarith
  have hb := one_add_mul_self_le_rpow_one_add ht ha
  have h1 : 1 + -w / (x + w) = x / (x + w) := by
    first | (field_simp; ring1) | field_simp
  rw [h1, Real.div_rpow hx hs.le] at hb
  have hsa : 0 < (x + w) ^ a := Real.rpow_pos_of_pos hs a
  rw [le_div_iff₀ hsa] at hb
  have h2 : (x + w) ^ (a - 1) = (x + w) ^ a / (x + w) := Real.rpow_sub_one hs.ne' a
  have h3 : (1 + a * (-w / (x + w))) * (x + w) ^ a = (x + w) ^ a - a * ((x + w) ^ a / (x + w)) * w := by
    first | (field_simp; ring1) | field_simp
  rw [h3] at hb
  rw [h2]
  linarith

/-- `(x+w)^(a-1) ≤ e x^(a-1) + a^(a-1) w^(a-1)` for `a > 1`. -/
lemma split_bound (a x w : ℝ) (ha : 1 < a) (hx : 0 ≤ x) (hw : 0 < w) :
    (x + w) ^ (a - 1) ≤ Real.exp 1 * x ^ (a - 1) + a ^ (a - 1) * w ^ (a - 1) := by
  have hb : 0 < a - 1 := by linarith
  have hT1 : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hx _
  have hT2 : 0 ≤ a ^ (a - 1) * w ^ (a - 1) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hw.le _)
  rcases le_or_gt (w * (a - 1)) x with h | h
  · have hxpos : 0 < x := lt_of_lt_of_le (mul_pos hw hb) h
    have hle : x + w ≤ x * (1 + 1 / (a - 1)) := by
      have : w ≤ x / (a - 1) := by rw [le_div_iff₀ hb]; exact h
      have : x * (1 + 1 / (a - 1)) = x + x / (a - 1) := by ring
      linarith
    have h1 : (x + w) ^ (a - 1) ≤ (x * (1 + 1 / (a - 1))) ^ (a - 1) :=
      Real.rpow_le_rpow (by linarith) hle hb.le
    have hpos1 : 0 ≤ 1 + 1 / (a - 1) := by positivity
    rw [Real.mul_rpow hx hpos1] at h1
    have h2 : (1 + 1 / (a - 1)) ^ (a - 1) ≤ Real.exp 1 := by
      have h3 : 1 + 1 / (a - 1) ≤ Real.exp (1 / (a - 1)) := by
        have := Real.add_one_le_exp (1 / (a - 1)); linarith
      have h4 := Real.rpow_le_rpow hpos1 h3 hb.le
      rw [← Real.exp_mul, div_mul_cancel₀ _ hb.ne'] at h4
      exact h4
    have h5 := mul_le_mul_of_nonneg_left h2 hT1
    linarith
  · have hle : x + w ≤ a * w := by linarith
    have h1 : (x + w) ^ (a - 1) ≤ (a * w) ^ (a - 1) :=
      Real.rpow_le_rpow (by linarith) hle hb.le
    rw [Real.mul_rpow (show (0:ℝ) ≤ a by linarith) hw.le] at h1
    have := mul_nonneg (Real.exp_pos 1).le hT1
    linarith

lemma coef_bound (a αm ρ : ℝ) (ha : 1 ≤ a) (haM : a ≤ αm)
    (hρ : (Real.exp 1 * αm) ^ (αm - 1) ≤ ρ) :
    a ^ (a - 1) ≤ Real.exp 1 * ρ / Real.exp αm := by
  have hαm : 1 ≤ αm := le_trans ha haM
  have h1 : a ^ (a - 1) ≤ αm ^ (a - 1) := Real.rpow_le_rpow (by linarith) haM (by linarith)
  have h2 : αm ^ (a - 1) ≤ αm ^ (αm - 1) := Real.rpow_le_rpow_of_exponent_le hαm (by linarith)
  rw [Real.mul_rpow (Real.exp_pos 1).le (show (0:ℝ) ≤ αm by linarith), Real.exp_one_rpow] at hρ
  have he : Real.exp (αm - 1) = Real.exp αm / Real.exp 1 := Real.exp_sub αm 1
  rw [he] at hρ
  have hpos : 0 < Real.exp αm / Real.exp 1 := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have h3 : αm ^ (αm - 1) ≤ ρ / (Real.exp αm / Real.exp 1) := by
    rw [le_div_iff₀ hpos]; linarith
  have h4 : ρ / (Real.exp αm / Real.exp 1) = Real.exp 1 * ρ / Real.exp αm := by
    rw [div_div_eq_mul_div]; ring
  linarith

lemma phi_inc (c a ρ αm x w : ℝ) (hc : 0 ≤ c) (ha : 1 ≤ a) (haM : a ≤ αm)
    (hρ : (Real.exp 1 * αm) ^ (αm - 1) ≤ ρ) (hx : 0 ≤ x) (hw : 1 ≤ w) :
    phi c a ρ (x + w) - phi c a ρ x ≤ Real.exp 1 * (if a = 1 then ρ * c * w
      else a * c * x ^ (a - 1) * w + ρ / Real.exp αm * c * a * w ^ a) := by
  unfold phi
  by_cases h1 : a = 1
  · rw [if_pos h1, if_pos h1, if_pos h1]
    exact le_of_eq (by ring)
  · rw [if_neg h1, if_neg h1, if_neg h1]
    have ha' : 1 < a := lt_of_le_of_ne ha (Ne.symm h1)
    have hw0 : 0 < w := by linarith
    have hB := bern a x w ha hx hw0
    have hS := split_bound a x w ha' hx hw0
    have hC := coef_bound a αm ρ ha haM hρ
    have hwa : w ^ (a - 1) * w = w ^ a := by
      rw [Real.rpow_sub_one hw0.ne', div_mul_cancel₀ _ hw0.ne']
    have hpos : 0 ≤ a * w := by positivity
    have hS' := mul_le_mul_of_nonneg_left hS hpos
    have hwa0 : 0 ≤ w ^ a := Real.rpow_nonneg hw0.le _
    have hC' := mul_le_mul_of_nonneg_right hC (mul_nonneg (by linarith : (0:ℝ) ≤ a) hwa0)
    have key : (x + w) ^ a - x ^ a ≤ Real.exp 1 * (a * x ^ (a - 1) * w)
        + Real.exp 1 * ρ / Real.exp αm * (a * w ^ a) := by
      have e1 : a * w * (Real.exp 1 * x ^ (a - 1) + a ^ (a - 1) * w ^ (a - 1)) =
          Real.exp 1 * (a * x ^ (a - 1) * w) + a ^ (a - 1) * (a * (w ^ (a - 1) * w)) := by ring
      rw [hwa] at e1
      have e2 : a * (x + w) ^ (a - 1) * w = a * w * (x + w) ^ (a - 1) := by ring
      linarith
    have key2 := mul_le_mul_of_nonneg_left key hc
    have e3 : Real.exp 1 * (a * c * x ^ (a - 1) * w + ρ / Real.exp αm * c * a * w ^ a) =
        c * (Real.exp 1 * (a * x ^ (a - 1) * w) + Real.exp 1 * ρ / Real.exp αm * (a * w ^ a)) := by
      ring
    rw [e3]
    have e4 : c * (x + w) ^ a - c * x ^ a = c * ((x + w) ^ a - x ^ a) := by ring
    rw [e4]
    exact key2

lemma alphaMax_ge {E : Type*} [Fintype E] (α : E → ℝ) (e : E) : α e ≤ alphaMax α := by
  unfold alphaMax
  rw [Finset.le_fold_max]
  exact Or.inr ⟨e, Finset.mem_univ _, le_refl _⟩

lemma alphaMax_one {E : Type*} [Fintype E] (α : E → ℝ) : 1 ≤ alphaMax α := by
  unfold alphaMax
  rw [Finset.le_fold_max]
  exact Or.inl (le_refl _)

end Aux_OnlineGND_eq_22_24

open OnlineGND Aux_OnlineGND_eq_22_24 in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (τ : ℝ) (hτ : 1 ≤ τ) (O : Request E → (E → ℝ) → Finset E)
    (hO : IsApproxOracle τ reqs O) (ρ : ℝ)
    (hρ : (Real.exp 1 * alphaMax α) ^ (alphaMax α - 1) ≤ ρ) :
    Real.exp 1 * ρ * costL c α (load reqs (powerAlg c α ρ O reqs))
        + costH c α (load reqs (powerAlg c α ρ O reqs)) ≤
      Real.exp 1 * τ * ρ * ∑ i, dualY c α ρ (load reqs (powerAlg c α ρ O reqs)) (reqs i) := by
  have hρpos : 0 < ρ := by
    have : 0 < (Real.exp 1 * alphaMax α) ^ (alphaMax α - 1) :=
      Real.rpow_pos_of_pos (mul_pos (Real.exp_pos 1) (by linarith [alphaMax_one α])) _
    linarith
  -- the online recursion
  have hsol : ∀ i : Fin N, powerAlg c α ρ O reqs i = O (reqs i) (psiBar c α ρ
      (fun e => ∑ j : Fin N, if (j : ℕ) < (i : ℕ) then
        (if e ∈ powerAlg c α ρ O reqs j then (reqs j).w e else 0) else 0) (reqs i)) := by
    intro i
    unfold powerAlg
    rw [onlineReplies]
    congr 2
    all_goals
      funext e
      apply Finset.sum_congr rfl
      intro j _
      rw [dite_eq_ite]
      by_cases h : j < i
      · rw [if_pos h, if_pos (Fin.lt_iff_val_lt_val.mp h)]
      · rw [if_neg h, if_neg (show ¬ ((j : ℕ) < (i : ℕ)) from fun h' => h (Fin.lt_iff_val_lt_val.mpr h'))]
  generalize powerAlg c α ρ O reqs = S at hsol ⊢
  set X : Fin N → E → ℝ := fun j e => if e ∈ S j then (reqs j).w e else 0 with hX
  set L : ℕ → E → ℝ := fun m e => ∑ j : Fin N, if (j : ℕ) < m then X j e else 0 with hL
  have hXnn : ∀ j e, 0 ≤ X j e := by
    intro j e; simp only [hX]; split_ifs
    · linarith [hw j e]
    · exact le_refl _
  have hLnn : ∀ m e, 0 ≤ L m e := by
    intro m e; simp only [hL]
    apply Finset.sum_nonneg; intro j _; split_ifs
    · exact hXnn j e
    · exact le_refl _
  have hA : load reqs S = L N := by
    funext e
    simp only [hL, load]
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos j.isLt]
  have hLle : ∀ m e, L m e ≤ L N e := by
    intro m e
    simp only [hL]
    apply Finset.sum_le_sum
    intro j _
    rw [if_pos j.isLt]
    split_ifs
    · exact le_refl _
    · exact hXnn j e
  have hL0 : ∀ e, L 0 e = 0 := by
    intro e; simp [hL]
  have hLsucc : ∀ i : Fin N, ∀ e, L ((i : ℕ) + 1) e = L i e + X i e := by
    intro i e
    simp only [hL]
    have : ∀ j : Fin N, (if (j : ℕ) < (i : ℕ) + 1 then X j e else 0) =
        (if (j : ℕ) < (i : ℕ) then X j e else 0) + (if j = i then X j e else 0) := by
      intro j
      by_cases h1 : (j : ℕ) < (i : ℕ)
      · have h2 : j ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
        rw [if_pos (show (j:ℕ) < (i:ℕ) + 1 by omega), if_pos h1, if_neg h2, add_zero]
      · by_cases h2 : j = i
        · rw [if_pos (show (j:ℕ) < (i:ℕ) + 1 by rw [h2]; omega), if_neg h1, if_pos h2, zero_add]
        · have h3 : (j : ℕ) ≠ (i : ℕ) := fun h => h2 (Fin.ext h)
          rw [if_neg (show ¬ ((j:ℕ) < (i:ℕ) + 1) by omega), if_neg h1, if_neg h2, add_zero]
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
  -- potential
  have hPhi : ∀ ℓ : E → ℝ, Real.exp 1 * ρ * costL c α ℓ + costH c α ℓ =
      ∑ e, phi (c e) (α e) ρ (ℓ e) := by
    intro ℓ
    unfold costL costH
    rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    unfold phi
    by_cases h : α e = 1
    · rw [if_pos h, if_neg (show ¬ (α e ≠ 1) from not_not.mpr h), if_pos h]; ring
    · rw [if_neg h, if_pos (show α e ≠ 1 from h), if_neg h]; ring
  rw [hPhi, hA]
  -- telescoping
  have htel : ∑ e, phi (c e) (α e) ρ (L N e) =
      ∑ i : Fin N, (∑ e, phi (c e) (α e) ρ (L ((i : ℕ) + 1) e) - ∑ e, phi (c e) (α e) ρ (L i e)) := by
    rw [Fin.sum_univ_eq_sum_range (fun m => ∑ e, phi (c e) (α e) ρ (L (m + 1) e) -
      ∑ e, phi (c e) (α e) ρ (L m e)) N, Finset.sum_range_sub (fun m => ∑ e, phi (c e) (α e) ρ (L m e)) N]
    have hz : ∀ e, phi (c e) (α e) ρ (L 0 e) = 0 := fun e => by
      rw [hL0]; exact phi_zero _ _ _ (hα e)
    simp only [hz, Finset.sum_const_zero, sub_zero]
  rw [htel, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  -- the stage-i step
  set d : E → ℝ := psiBar c α ρ (L i) (reqs i) with hd
  have hdnn : ∀ e, 0 ≤ d e := by
    intro e
    simp only [hd, psiBar]
    split_ifs
    · exact mul_nonneg (mul_nonneg hρpos.le (hc e)) (by linarith [hw i e])
    · have h1 := hc e; have h2 := hw i e; have h3 := hα e
      have h4 : 0 ≤ L i e ^ (α e - 1) := Real.rpow_nonneg (hLnn _ _) _
      have h5 : 0 ≤ (reqs i).w e ^ α e := Real.rpow_nonneg (by linarith) _
      have h6 : 0 ≤ ρ / Real.exp (alphaMax α) := div_nonneg hρpos.le (Real.exp_pos _).le
      have : 0 ≤ α e * c e * L i e ^ (α e - 1) * (reqs i).w e :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h1) h4) (by linarith)
      have : 0 ≤ ρ / Real.exp (alphaMax α) * c e * α e * (reqs i).w e ^ α e :=
        mul_nonneg (mul_nonneg (mul_nonneg h6 h1) (by linarith)) h5
      linarith
  have hSi : S i = O (reqs i) d := hsol i
  obtain ⟨hmemO, hopt⟩ := hO i d hdnn
  rw [← hSi] at hmemO hopt
  -- step 1: potential increase
  have hstep : ∑ e, phi (c e) (α e) ρ (L ((i : ℕ) + 1) e) - ∑ e, phi (c e) (α e) ρ (L i e) ≤
      Real.exp 1 * ∑ e ∈ S i, d e := by
    rw [← Finset.sum_sub_distrib]
    have hz : ∀ e ∈ Finset.univ, e ∉ S i →
        phi (c e) (α e) ρ (L ((i : ℕ) + 1) e) - phi (c e) (α e) ρ (L i e) = 0 := by
      intro e _ he
      rw [hLsucc i e]
      simp only [hX, if_neg he, add_zero, sub_self]
    rw [← Finset.sum_subset (Finset.subset_univ (S i)) hz, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [hLsucc i e]
    simp only [hX, if_pos he]
    have := phi_inc (c e) (α e) ρ (alphaMax α) (L i e) ((reqs i).w e) (hc e) (hα e)
      (alphaMax_ge α e) hρ (hLnn _ _) (hw i e)
    simp only [hd, psiBar]
    exact this
  -- step 2: oracle and dual
  have hdual : ∑ e ∈ S i, d e ≤ τ * ρ * dualY c α ρ (L N) (reqs i) := by
    haveI : Nonempty (reqs i).replies := ⟨⟨S i, hmemO⟩⟩
    have hle : ∀ p : (reqs i).replies, ∑ e ∈ S i, d e ≤ τ * ρ *
        (∑ e ∈ (p : Finset E).filter (fun e => α e = 1), c e * (reqs i).w e
          + ∑ e ∈ (p : Finset E).filter (fun e => α e ≠ 1),
            (c e * α e * (reqs i).w e * zVar α ρ (L N) e
              + c e * α e / Real.exp (alphaMax α) * (reqs i).w e ^ α e)) := by
      intro p
      have h1 := hopt p p.2
      have h2 : ∑ e ∈ (p : Finset E), d e ≤ ρ *
          (∑ e ∈ (p : Finset E).filter (fun e => α e = 1), c e * (reqs i).w e
          + ∑ e ∈ (p : Finset E).filter (fun e => α e ≠ 1),
            (c e * α e * (reqs i).w e * zVar α ρ (L N) e
              + c e * α e / Real.exp (alphaMax α) * (reqs i).w e ^ α e)) := by
        rw [← Finset.sum_filter_add_sum_filter_not (p : Finset E) (fun e => α e = 1), mul_add,
          Finset.mul_sum, Finset.mul_sum]
        apply add_le_add
        · apply Finset.sum_le_sum
          intro e he
          have hα1 : α e = 1 := (Finset.mem_filter.mp he).2
          show psiBar c α ρ (L i) (reqs i) e ≤ _
          unfold psiBar
          rw [if_pos hα1]
          exact le_of_eq (by ring)
        · apply Finset.sum_le_sum
          intro e he
          have hα1 : ¬ α e = 1 := (Finset.mem_filter.mp he).2
          show psiBar c α ρ (L i) (reqs i) e ≤ _
          unfold psiBar zVar
          rw [if_neg hα1, if_neg hα1]
          have hpow : L i e ^ (α e - 1) ≤ L N e ^ (α e - 1) :=
            Real.rpow_le_rpow (hLnn _ _) (hLle _ _) (by linarith [hα e])
          have hcw : 0 ≤ α e * c e * (reqs i).w e := by
            have := hc e; have := hw i e; have := hα e
            apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
          have h3 := mul_le_mul_of_nonneg_left hpow hcw
          have e1 : ρ * (c e * α e * (reqs i).w e * (1 / ρ * L N e ^ (α e - 1))
              + c e * α e / Real.exp (alphaMax α) * (reqs i).w e ^ α e) =
              α e * c e * (reqs i).w e * L N e ^ (α e - 1)
              + ρ / Real.exp (alphaMax α) * c e * α e * (reqs i).w e ^ α e := by
            have hρ1 : ρ * (1 / ρ) = 1 := mul_one_div_cancel hρpos.ne'
            calc ρ * (c e * α e * (reqs i).w e * (1 / ρ * L N e ^ (α e - 1))
                  + c e * α e / Real.exp (alphaMax α) * (reqs i).w e ^ α e)
                = (ρ * (1 / ρ)) * (α e * c e * (reqs i).w e * L N e ^ (α e - 1))
                  + ρ / Real.exp (alphaMax α) * c e * α e * (reqs i).w e ^ α e := by ring
              _ = _ := by rw [hρ1, one_mul]
          rw [e1]
          have e2 : α e * c e * L i e ^ (α e - 1) * (reqs i).w e =
              α e * c e * (reqs i).w e * L i e ^ (α e - 1) := by ring
          linarith
      have hτ0 : 0 ≤ τ := by linarith
      calc ∑ e ∈ S i, d e ≤ τ * ∑ e ∈ (p : Finset E), d e := h1
        _ ≤ τ * (ρ * _) := mul_le_mul_of_nonneg_left h2 hτ0
        _ = _ := by ring
    unfold dualY
    have hτρ : 0 < τ * ρ := mul_pos (by linarith) hρpos
    rw [← div_le_iff₀' hτρ]
    apply le_ciInf
    intro p
    rw [div_le_iff₀' hτρ]
    exact hle p
  calc ∑ e, phi (c e) (α e) ρ (L ((i : ℕ) + 1) e) - ∑ e, phi (c e) (α e) ρ (L i e)
      ≤ Real.exp 1 * ∑ e ∈ S i, d e := hstep
    _ ≤ Real.exp 1 * (τ * ρ * dualY c α ρ (L N) (reqs i)) :=
        mul_le_mul_of_nonneg_left hdual (Real.exp_pos 1).le
    _ = Real.exp 1 * τ * ρ * dualY c α ρ (L N) (reqs i) := by ring
