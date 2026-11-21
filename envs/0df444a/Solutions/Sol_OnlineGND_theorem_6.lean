-- Prove2me | solution 1 for OnlineGND.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:40:48.34971+00:00
-- url     : https://prove2.me/submissions/b3bd4832-1130-4f31-b028-0b9926c64f88

import Definitions.Def_OnlineGND_Doubled
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


theorem main_ineq_22_24 {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
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

end Aux_OnlineGND_eq_22_24

namespace Aux_OnlineGND_theorem_6

open OnlineGND Aux_OnlineGND_eq_22_24

lemma tangent_rpow (a t0 t : ℝ) (ha : 1 ≤ a) (ht0 : 0 < t0) (ht : 0 ≤ t) :
    t0 ^ a + a * t0 ^ (a - 1) * (t - t0) ≤ t ^ a := by
  have hs : -1 ≤ t / t0 - 1 := by
    have : 0 ≤ t / t0 := div_nonneg ht ht0.le
    linarith
  have hb := one_add_mul_self_le_rpow_one_add hs ha
  have h1 : 1 + (t / t0 - 1) = t / t0 := by ring
  rw [h1, Real.div_rpow ht ht0.le] at hb
  have hpos : 0 < t0 ^ a := Real.rpow_pos_of_pos ht0 a
  rw [le_div_iff₀ hpos] at hb
  have h2 : t0 ^ (a - 1) = t0 ^ a / t0 := Real.rpow_sub_one ht0.ne' a
  have h3 : (1 + a * (t / t0 - 1)) * t0 ^ a = t0 ^ a + a * (t0 ^ a / t0) * (t - t0) := by
    first | (field_simp; ring1) | field_simp
  rw [h3] at hb
  rw [h2]
  exact hb

lemma young_edge (a M τ A ℓ : ℝ) (ha : 1 < a) (haM : a ≤ M) (hτ : 1 ≤ τ) (hA : 0 ≤ A)
    (hℓ : 0 ≤ ℓ) :
    a * A ^ (a - 1) * ℓ ≤ (1 - 1 / M) / (Real.exp 1 * τ) * A ^ a +
      (Real.exp 1 * τ * M) ^ (M - 1) * ℓ ^ a := by
  have hM : 1 < M := lt_of_lt_of_le ha haM
  have hM0 : 0 < M := by linarith
  have he : 0 < Real.exp 1 * τ := mul_pos (Real.exp_pos 1) (by linarith)
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = (1 - 1 / M) / (Real.exp 1 * τ) := ⟨_, rfl⟩
  rw [← hκdef]
  have h1M : 1 / M < 1 := by rw [div_lt_one hM0]; exact hM
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos (by linarith) he
  have hκM : Real.exp 1 * τ * M * κ = M - 1 := by
    rw [hκdef]
    have hM0' : M ≠ 0 := hM0.ne'
    have he' : Real.exp 1 * τ ≠ 0 := he.ne'
    have he1 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    have hτ' : τ ≠ 0 := by linarith
    first | (field_simp; ring1) | field_simp
  obtain ⟨t0, ht0def⟩ : ∃ t0, t0 = κ / (a - 1) := ⟨_, rfl⟩
  have ha1 : 0 < a - 1 := by linarith
  have ht0 : 0 < t0 := by rw [ht0def]; exact div_pos hκ ha1
  have ht0a : (a - 1) * t0 = κ := by rw [ht0def]; exact mul_div_cancel₀ κ ha1.ne'
  obtain ⟨R, hRdef⟩ : ∃ R, R = (1 / t0) ^ (a - 1) := ⟨_, rfl⟩
  have hRt0 : R * t0 ^ (a - 1) = 1 := by
    rw [hRdef, ← Real.mul_rpow (div_nonneg zero_le_one ht0.le) ht0.le, one_div_mul_cancel ht0.ne',
      Real.one_rpow]
  have hR0 : 0 ≤ R := by rw [hRdef]; exact Real.rpow_nonneg (div_nonneg zero_le_one ht0.le) _
  have hRle : R ≤ (Real.exp 1 * τ * M) ^ (M - 1) := by
    have hinv : 1 / t0 ≤ Real.exp 1 * τ * M := by
      rw [div_le_iff₀ ht0]
      have : Real.exp 1 * τ * M * t0 = (M - 1) / (a - 1) := by
        rw [ht0def, ← hκM]; ring
      rw [this, le_div_iff₀ ha1]
      linarith
    have hbase : 1 ≤ Real.exp 1 * τ * M := by
      have h1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      have h2 : 1 ≤ Real.exp 1 * τ := by nlinarith
      nlinarith
    rw [hRdef]
    calc (1 / t0) ^ (a - 1) ≤ (Real.exp 1 * τ * M) ^ (a - 1) :=
          Real.rpow_le_rpow (div_nonneg zero_le_one ht0.le) hinv ha1.le
      _ ≤ (Real.exp 1 * τ * M) ^ (M - 1) :=
          Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hℓa : 0 ≤ ℓ ^ a := Real.rpow_nonneg hℓ _
  have hmain : a * A ^ (a - 1) * ℓ ≤ κ * A ^ a + R * ℓ ^ a := by
    rcases eq_or_lt_of_le hA with hA0 | hApos
    · rw [← hA0, Real.zero_rpow ha1.ne', Real.zero_rpow (by linarith : (0:ℝ) < a).ne']
      have := mul_nonneg hR0 hℓa
      linarith
    · obtain ⟨t, htdef⟩ : ∃ t, t = ℓ / A := ⟨_, rfl⟩
      have ht : 0 ≤ t := by rw [htdef]; exact div_nonneg hℓ hApos.le
      have htan := tangent_rpow a t0 t ha.le ht0 ht
      have ht0a' : t0 ^ a = t0 ^ (a - 1) * t0 := by
        rw [Real.rpow_sub_one ht0.ne', div_mul_cancel₀ _ ht0.ne']
      -- 1D inequality
      have h1d : a * t ≤ κ + R * t ^ a := by
        have := mul_le_mul_of_nonneg_left htan hR0
        have e1 : R * (t0 ^ a + a * t0 ^ (a - 1) * (t - t0)) =
            (R * t0 ^ (a - 1)) * t0 + a * (R * t0 ^ (a - 1)) * (t - t0) := by
          rw [ht0a']; ring
        rw [e1, hRt0] at this
        linarith [ht0a]
      have hAa : 0 < A ^ a := Real.rpow_pos_of_pos hApos a
      have h2 := mul_le_mul_of_nonneg_left h1d hAa.le
      have e2 : A ^ a * (a * t) = a * A ^ (a - 1) * ℓ := by
        rw [htdef, Real.rpow_sub_one hApos.ne']
        ring
      have e3 : A ^ a * t ^ a = ℓ ^ a := by
        rw [← Real.mul_rpow hApos.le ht, htdef, mul_div_cancel₀ _ hApos.ne']
      have e4 : A ^ a * (κ + R * t ^ a) = κ * A ^ a + R * (A ^ a * t ^ a) := by ring
      rw [e2, e4, e3] at h2
      exact h2
  have := mul_le_mul_of_nonneg_right hRle hℓa
  linarith

lemma superadd {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (a : ℝ) (ha : 1 ≤ a) :
    ∑ i ∈ s, x i ^ a ≤ (∑ i ∈ s, x i) ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Real.rpow_nonneg (le_refl _) _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hs : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg (fun i _ => hx i)
    calc x j ^ a + ∑ i ∈ s, x i ^ a ≤ x j ^ a + (∑ i ∈ s, x i) ^ a := by linarith
      _ ≤ (x j + ∑ i ∈ s, x i) ^ a := Real.add_rpow_le_rpow_add (hx j) hs ha

lemma psiBar_nonneg {E : Type*} [Fintype E] (c α : E → ℝ) (ρ : ℝ) (ℓ : E → ℝ) (r : Request E)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (hρ : 0 ≤ ρ) (hℓ : ∀ e, 0 ≤ ℓ e)
    (hw : ∀ e, 1 ≤ r.w e) (e : E) : 0 ≤ psiBar c α ρ ℓ r e := by
  unfold psiBar
  split_ifs
  · exact mul_nonneg (mul_nonneg hρ (hc e)) (by linarith [hw e])
  · have h1 := hc e; have h2 := hw e; have h3 := hα e
    have h4 : 0 ≤ ℓ e ^ (α e - 1) := Real.rpow_nonneg (hℓ e) _
    have h5 : 0 ≤ r.w e ^ α e := Real.rpow_nonneg (by linarith) _
    have h6 : 0 ≤ ρ / Real.exp (alphaMax α) := div_nonneg hρ (Real.exp_pos _).le
    have : 0 ≤ α e * c e * ℓ e ^ (α e - 1) * r.w e :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h1) h4) (by linarith)
    have : 0 ≤ ρ / Real.exp (alphaMax α) * c e * α e * r.w e ^ α e :=
      mul_nonneg (mul_nonneg (mul_nonneg h6 h1) (by linarith)) h5
    linarith

end Aux_OnlineGND_theorem_6

open OnlineGND Aux_OnlineGND_eq_22_24 Aux_OnlineGND_theorem_6 in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (τ : ℝ) (hτ : 1 ≤ τ) (O : Request E → (E → ℝ) → Finset E)
    (hO : IsApproxOracle τ reqs O) (sol : Fin N → Finset E) (hsol : IsReplyProfile reqs sol) :
    IsReplyProfile reqs (powerAlg c α (rhoStar τ α) O reqs) ∧
    costL c α (load reqs (powerAlg c α (rhoStar τ α) O reqs))
        + costH c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) ≤
      2 * (Real.exp 1 * alphaMax α * τ) ^ alphaMax α * powerCost c α (load reqs sol) ∧
    costL c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) ≤
      2 * τ * powerCost c α (load reqs sol) ∧
    costH c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) ≤
      2 * (Real.exp 1 * alphaMax α * τ) ^ alphaMax α * powerCost c α (load reqs sol) ∧
    costL c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) / τ
        + costH c α (load reqs (powerAlg c α (rhoStar τ α) O reqs))
          / (Real.exp 1 * τ * alphaMax α) ^ alphaMax α ≤
      2 * powerCost c α (load reqs sol) := by
  have hM1 : 1 ≤ alphaMax α := alphaMax_one α
  have hMpos : 0 < alphaMax α := by linarith
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hbase1 : 1 ≤ Real.exp 1 * τ * alphaMax α := by
    have h2 : 1 ≤ Real.exp 1 * τ := by nlinarith
    nlinarith
  have hρdef : rhoStar τ α = (Real.exp 1 * τ * alphaMax α) ^ (alphaMax α - 1) := rfl
  have hρpos : 0 < rhoStar τ α := by
    rw [hρdef]; exact Real.rpow_pos_of_pos (by linarith) _
  have hρ : (Real.exp 1 * alphaMax α) ^ (alphaMax α - 1) ≤ rhoStar τ α := by
    rw [hρdef]
    have h0 : 0 ≤ Real.exp 1 * alphaMax α := mul_nonneg (Real.exp_pos 1).le (by linarith)
    refine Real.rpow_le_rpow h0 ?_ (by linarith)
    have : Real.exp 1 * alphaMax α * 1 ≤ Real.exp 1 * alphaMax α * τ :=
      mul_le_mul_of_nonneg_left hτ h0
    nlinarith
  -- clause 1
  have hP1 : IsReplyProfile reqs (powerAlg c α (rhoStar τ α) O reqs) := by
    intro i
    unfold powerAlg
    rw [onlineReplies]
    refine (hO i _ ?_).1
    intro e
    refine psiBar_nonneg c α _ _ _ hc hα hρpos.le ?_ (hw i) e
    intro e'
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · linarith [hw j e']
    · exact le_refl _
    · exact le_refl _
  have hmain := main_ineq_22_24 c α hc hα reqs hw τ hτ O hO (rhoStar τ α) hρ
  generalize powerAlg c α (rhoStar τ α) O reqs = S at hmain hP1 ⊢
  refine ⟨hP1, ?_⟩
  -- abbreviations
  obtain ⟨M, hM⟩ : ∃ M, M = alphaMax α := ⟨_, rfl⟩
  obtain ⟨ρ, hρρ⟩ : ∃ ρ, ρ = rhoStar τ α := ⟨_, rfl⟩
  rw [← hρρ] at hmain hρpos
  rw [← hM] at hM1 hMpos hbase1 hρdef ⊢
  rw [← hρρ] at hρdef
  have hαM : ∀ e, α e ≤ M := fun e => by rw [hM]; exact alphaMax_ge α e
  generalize hAdef : load reqs S = A at hmain ⊢
  generalize hℓdef : load reqs sol = ℓ
  have hAnn : ∀ e, 0 ≤ A e := by
    intro e; rw [← hAdef]; unfold load
    apply Finset.sum_nonneg; intro i _; split_ifs
    · linarith [hw i e]
    · exact le_refl _
  have hℓnn : ∀ e, 0 ≤ ℓ e := by
    intro e; rw [← hℓdef]; unfold load
    apply Finset.sum_nonneg; intro i _; split_ifs
    · linarith [hw i e]
    · exact le_refl _
  -- G_e
  obtain ⟨G, hG⟩ : ∃ G : E → ℝ, G = fun e => if α e = 1 then c e * ℓ e else
      c e * α e * (1 / ρ * A e ^ (α e - 1)) * ℓ e + c e * α e / Real.exp M * ℓ e ^ α e := ⟨_, rfl⟩
  -- step: sum of duals bounded by sum of G
  have hy : ∑ i, dualY c α ρ A (reqs i) ≤ ∑ e, G e := by
    have h1 : ∀ i, dualY c α ρ A (reqs i) ≤
        ∑ e, (if e ∈ sol i then (if α e = 1 then c e * (reqs i).w e else
          c e * α e * (reqs i).w e * zVar α ρ A e
            + c e * α e / Real.exp M * (reqs i).w e ^ α e) else 0) := by
      intro i
      unfold dualY
      have hle := ciInf_le (Set.finite_range (fun p : (reqs i).replies =>
          ∑ e ∈ (p : Finset E).filter (fun e => α e = 1), c e * (reqs i).w e
          + ∑ e ∈ (p : Finset E).filter (fun e => α e ≠ 1),
            (c e * α e * (reqs i).w e * zVar α ρ A e
              + c e * α e / Real.exp (alphaMax α) * (reqs i).w e ^ α e))).bddBelow
        ⟨sol i, hsol i⟩
      refine le_trans hle (le_of_eq ?_)
      show ∑ e ∈ (sol i).filter (fun e => α e = 1), c e * (reqs i).w e
          + ∑ e ∈ (sol i).filter (fun e => α e ≠ 1),
            (c e * α e * (reqs i).w e * zVar α ρ A e
              + c e * α e / Real.exp (alphaMax α) * (reqs i).w e ^ α e) = _
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, Fintype.sum_ite_mem]
      apply Finset.sum_congr rfl
      intro e _
      rw [← hM]
      by_cases h : α e = 1
      · rw [if_pos h, if_neg (show ¬ (α e ≠ 1) from not_not.mpr h), if_pos h, add_zero]
      · rw [if_neg h, if_pos (show α e ≠ 1 from h), if_neg h, zero_add]
    calc ∑ i, dualY c α ρ A (reqs i)
        ≤ ∑ i, ∑ e, (if e ∈ sol i then (if α e = 1 then c e * (reqs i).w e else
          c e * α e * (reqs i).w e * zVar α ρ A e
            + c e * α e / Real.exp M * (reqs i).w e ^ α e) else 0) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = ∑ e, ∑ i, (if e ∈ sol i then (if α e = 1 then c e * (reqs i).w e else
          c e * α e * (reqs i).w e * zVar α ρ A e
            + c e * α e / Real.exp M * (reqs i).w e ^ α e) else 0) := Finset.sum_comm
      _ ≤ ∑ e, G e := by
        apply Finset.sum_le_sum
        intro e _
        rw [hG]
        show _ ≤ (if α e = 1 then c e * ℓ e else
          c e * α e * (1 / ρ * A e ^ (α e - 1)) * ℓ e + c e * α e / Real.exp M * ℓ e ^ α e)
        have hℓe : ℓ e = ∑ i, (if e ∈ sol i then (reqs i).w e else 0) := by
          rw [← hℓdef]; rfl
        by_cases h : α e = 1
        · rw [if_pos h, hℓe, Finset.mul_sum]
          apply le_of_eq
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : e ∈ sol i <;> simp [hi, h]
        · rw [if_neg h]
          have hz : zVar α ρ A e = 1 / ρ * A e ^ (α e - 1) := by
            unfold zVar; rw [if_neg h]
          have hsplit : ∑ i, (if e ∈ sol i then (if α e = 1 then c e * (reqs i).w e else
              c e * α e * (reqs i).w e * zVar α ρ A e
                + c e * α e / Real.exp M * (reqs i).w e ^ α e) else 0) =
              c e * α e * zVar α ρ A e * ∑ i, (if e ∈ sol i then (reqs i).w e else 0)
              + c e * α e / Real.exp M * ∑ i, (if e ∈ sol i then (reqs i).w e else 0) ^ α e := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : e ∈ sol i
            · rw [if_pos hi, if_pos hi, if_neg h]; ring
            · rw [if_neg hi, if_neg hi, Real.zero_rpow (by linarith [hα e] : (0:ℝ) < α e).ne']; ring
          rw [hsplit, hz, ← hℓe]
          have hsup := superadd Finset.univ (fun i => if e ∈ sol i then (reqs i).w e else 0)
            (fun i => by
              show 0 ≤ (if e ∈ sol i then (reqs i).w e else 0)
              split_ifs
              · linarith [hw i e]
              · exact le_refl _) (α e) (hα e)
          rw [← hℓe] at hsup
          have hcoef : 0 ≤ c e * α e / Real.exp M :=
            div_nonneg (mul_nonneg (hc e) (by linarith [hα e])) (Real.exp_pos _).le
          have := mul_le_mul_of_nonneg_left hsup hcoef
          linarith
  -- per-edge Young
  have hE : 0 < Real.exp 1 * τ * ρ := mul_pos (mul_pos (Real.exp_pos 1) (by linarith)) hρpos
  have hGe : ∀ e, Real.exp 1 * τ * ρ * G e ≤
      (if α e ≠ 1 then (1 - 1 / M) * (c e * A e ^ α e) else 0) +
        2 * (Real.exp 1 * τ * ρ) * (c e * ℓ e ^ α e) := by
    intro e
    rw [hG]
    show Real.exp 1 * τ * ρ * (if α e = 1 then c e * ℓ e else
      c e * α e * (1 / ρ * A e ^ (α e - 1)) * ℓ e + c e * α e / Real.exp M * ℓ e ^ α e) ≤ _
    by_cases h : α e = 1
    · rw [if_pos h, if_neg (show ¬ (α e ≠ 1) from not_not.mpr h), h, Real.rpow_one]
      have := mul_nonneg (hc e) (hℓnn e)
      have := mul_nonneg hE.le this
      linarith
    · rw [if_neg h, if_pos (show α e ≠ 1 from h)]
      have ha : 1 < α e := lt_of_le_of_ne (hα e) (Ne.symm h)
      have hy := young_edge (α e) M τ (A e) (ℓ e) ha (hαM e) hτ (hAnn e) (hℓnn e)
      rw [← hρdef] at hy
      have hce := hc e
      have hy2 := mul_le_mul_of_nonneg_left hy (mul_nonneg (mul_nonneg (Real.exp_pos 1).le
        (by linarith : (0:ℝ) ≤ τ)) hce)
      have hαe : α e / Real.exp M ≤ 1 := by
        rw [div_le_one (Real.exp_pos _)]
        linarith [Real.add_one_le_exp M, hαM e]
      have hℓa : 0 ≤ ℓ e ^ α e := Real.rpow_nonneg (hℓnn e) _
      have hz2 : Real.exp 1 * τ * ρ * c e * (α e / Real.exp M) * ℓ e ^ α e ≤
          Real.exp 1 * τ * ρ * c e * ℓ e ^ α e := by
        have h0 : 0 ≤ Real.exp 1 * τ * ρ * c e * ℓ e ^ α e :=
          mul_nonneg (mul_nonneg hE.le hce) hℓa
        have := mul_le_mul_of_nonneg_left hαe h0
        have e5 : Real.exp 1 * τ * ρ * c e * (α e / Real.exp M) * ℓ e ^ α e =
            α e / Real.exp M * (Real.exp 1 * τ * ρ * c e * ℓ e ^ α e) := by ring
        rw [e5]
        linarith
      have hρ1 : ρ * (1 / ρ) = 1 := mul_one_div_cancel hρpos.ne'
      have hτ0 : Real.exp 1 * τ ≠ 0 := by positivity
      have e1 : Real.exp 1 * τ * ρ * (c e * α e * (1 / ρ * A e ^ (α e - 1)) * ℓ e
          + c e * α e / Real.exp M * ℓ e ^ α e) =
          (ρ * (1 / ρ)) * (Real.exp 1 * τ * c e * (α e * A e ^ (α e - 1) * ℓ e))
          + Real.exp 1 * τ * ρ * c e * (α e / Real.exp M) * ℓ e ^ α e := by ring
      have e2 : Real.exp 1 * τ * c e * ((1 - 1 / M) / (Real.exp 1 * τ) * A e ^ α e
          + ρ * ℓ e ^ α e) =
          (1 - 1 / M) * (c e * A e ^ α e) + Real.exp 1 * τ * ρ * (c e * ℓ e ^ α e) := by
        first | (field_simp; ring1) | field_simp
      rw [e1, hρ1, one_mul]
      rw [e2] at hy2
      linarith
  -- combine
  have hH : costH c α A = ∑ e, (if α e ≠ 1 then c e * A e ^ α e else 0) := by
    unfold costH; rw [Finset.sum_filter]
  have hP : powerCost c α ℓ = ∑ e, c e * ℓ e ^ α e := rfl
  have hsumG : Real.exp 1 * τ * ρ * ∑ e, G e ≤ (1 - 1 / M) * costH c α A +
      2 * (Real.exp 1 * τ * ρ) * powerCost c α ℓ := by
    rw [Finset.mul_sum, hH, hP, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    have := hGe e
    by_cases h : α e ≠ 1
    · rw [if_pos h] at this ⊢; linarith
    · rw [if_neg h] at this ⊢; linarith
  have hL0 : 0 ≤ costL c α A := by
    unfold costL; apply Finset.sum_nonneg; intro e _; exact mul_nonneg (hc e) (hAnn e)
  have hH0 : 0 ≤ costH c α A := by
    unfold costH; apply Finset.sum_nonneg; intro e _
    exact mul_nonneg (hc e) (Real.rpow_nonneg (hAnn e) _)
  have hP0 : 0 ≤ powerCost c α ℓ := by
    rw [hP]; apply Finset.sum_nonneg; intro e _
    exact mul_nonneg (hc e) (Real.rpow_nonneg (hℓnn e) _)
  have key : Real.exp 1 * ρ * costL c α A + costH c α A / M ≤
      2 * (Real.exp 1 * τ * ρ) * powerCost c α ℓ := by
    have h1 : Real.exp 1 * τ * ρ * ∑ i, dualY c α ρ A (reqs i) ≤
        Real.exp 1 * τ * ρ * ∑ e, G e := mul_le_mul_of_nonneg_left hy hE.le
    have hMne : M ≠ 0 := hMpos.ne'
    have h2 : costH c α A / M = costH c α A - (1 - 1 / M) * costH c α A := by
      first | (field_simp; ring1) | field_simp
    rw [h2]
    linarith
  -- the power identity
  have hpow : (Real.exp 1 * τ * M) ^ M = M * (Real.exp 1 * τ * ρ) := by
    have h := Real.rpow_sub_one (show Real.exp 1 * τ * M ≠ 0 by positivity) M
    rw [← hρdef] at h
    have hx : (Real.exp 1 * τ * M) ^ M = ρ * (Real.exp 1 * τ * M) := by
      rw [h, div_mul_cancel₀ _ (show Real.exp 1 * τ * M ≠ 0 by positivity)]
    rw [hx]; ring
  have hQpos : 0 < (Real.exp 1 * τ * M) ^ M := by rw [hpow]; positivity
  have hτpos : 0 < τ := by linarith
  have C5 : costL c α A / τ + costH c α A / (Real.exp 1 * τ * M) ^ M ≤
      2 * powerCost c α ℓ := by
    have e1 : costL c α A / τ + costH c α A / (Real.exp 1 * τ * M) ^ M =
        (Real.exp 1 * ρ * costL c α A + costH c α A / M) / (Real.exp 1 * τ * ρ) := by
      rw [hpow]
      have hMne : M ≠ 0 := hMpos.ne'
      have hτne : τ ≠ 0 := hτpos.ne'
      have hρne : ρ ≠ 0 := hρpos.ne'
      have he1 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
      first | (field_simp; ring1) | field_simp
    rw [e1, div_le_iff₀ hE]
    linarith
  have hswap : (Real.exp 1 * M * τ) ^ M = (Real.exp 1 * τ * M) ^ M := by
    rw [mul_right_comm]
  rw [hswap]
  have hLτ : 0 ≤ costL c α A / τ := div_nonneg hL0 hτpos.le
  have hHQ : 0 ≤ costH c α A / (Real.exp 1 * τ * M) ^ M := div_nonneg hH0 hQpos.le
  have C3 : costL c α A ≤ 2 * τ * powerCost c α ℓ := by
    have : costL c α A / τ ≤ 2 * powerCost c α ℓ := by linarith
    rw [div_le_iff₀ hτpos] at this
    linarith
  have C4 : costH c α A ≤ 2 * (Real.exp 1 * τ * M) ^ M * powerCost c α ℓ := by
    have : costH c α A / (Real.exp 1 * τ * M) ^ M ≤ 2 * powerCost c α ℓ := by linarith
    rw [div_le_iff₀ hQpos] at this
    linarith
  have hτQ : τ ≤ (Real.exp 1 * τ * M) ^ M := by
    have h1 : (Real.exp 1 * τ * M) ^ (1:ℝ) ≤ (Real.exp 1 * τ * M) ^ M :=
      Real.rpow_le_rpow_of_exponent_le hbase1 hM1
    rw [Real.rpow_one] at h1
    have h2 : τ ≤ Real.exp 1 * τ * M := by
      have : τ * 1 ≤ τ * (Real.exp 1 * M) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hτpos.le
      nlinarith
    linarith
  have C2 : costL c α A + costH c α A ≤ 2 * (Real.exp 1 * τ * M) ^ M * powerCost c α ℓ := by
    have e1 : costL c α A = τ * (costL c α A / τ) := (mul_div_cancel₀ _ hτpos.ne').symm
    have e2 : costH c α A = (Real.exp 1 * τ * M) ^ M * (costH c α A / (Real.exp 1 * τ * M) ^ M) :=
      (mul_div_cancel₀ _ hQpos.ne').symm
    have h3 : τ * (costL c α A / τ) ≤ (Real.exp 1 * τ * M) ^ M * (costL c α A / τ) :=
      mul_le_mul_of_nonneg_right hτQ hLτ
    have h4 := mul_le_mul_of_nonneg_left C5 hQpos.le
    have e3 : (Real.exp 1 * τ * M) ^ M * (costL c α A / τ + costH c α A / (Real.exp 1 * τ * M) ^ M)
        = (Real.exp 1 * τ * M) ^ M * (costL c α A / τ)
          + (Real.exp 1 * τ * M) ^ M * (costH c α A / (Real.exp 1 * τ * M) ^ M) := by ring
    rw [e3] at h4
    linarith
  exact ⟨C2, C3, C4, C5⟩
