-- Prove2me | solution 1 for TamingMonster.CoordDescent.potential_rescale_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:06:37.006566+00:00
-- url     : https://prove2.me/submissions/7a786a0b-ad76-4bed-848e-5bfb1088d3b9

import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Potential
import Definitions.Def_TamingMonster_CoordDescent_Algorithm



namespace TamingMonster.CoordDescent

open Finset Classical

variable {X : Type*} {K t : ℕ}

lemma bCoef_nonneg (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (hμ : 0 < μ)
    (π : Pi) : 0 ≤ bCoef Pi H μ (π : X → Fin K) := by
  unfold bCoef estRegret
  refine div_nonneg ?_ (by positivity)
  rw [sub_nonneg]
  exact le_ciSup (f := fun π' : Pi => ipsEstimate H (π' : X → Fin K)) (Set.finite_range _).bddAbove π

lemma weightedMass_smul (Pi : Finset (X → Fin K)) (H : History X K t) (μ c : ℝ) (Q : Pi → ℝ) :
    weightedMass Pi H μ (fun π => c * Q π) = c * weightedMass Pi H μ Q := by
  unfold weightedMass; rw [mul_sum]; apply sum_congr rfl; intro π _; ring

lemma rescale_nonneg (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (hK : 0 < K)
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π) : ∀ π, 0 ≤ rescale Pi H μ Q π := by
  intro π
  unfold rescale
  split_ifs with h
  · have hW : 0 < weightedMass Pi H μ Q := lt_trans (by positivity) h
    exact mul_nonneg (div_nonneg (by positivity) hW.le) (hQ π)
  · exact hQ π

lemma rescale_mass_le (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (hK : 0 < K)
    (Q : Pi → ℝ) : weightedMass Pi H μ (rescale Pi H μ Q) ≤ 2 * (K : ℝ) := by
  unfold rescale
  split_ifs with h
  · have hW : 0 < weightedMass Pi H μ Q := lt_trans (by positivity) h
    rw [weightedMass_smul]; unfold scaleFactor; rw [div_mul_cancel₀ _ hW.ne']
  · exact not_lt.1 h

theorem halt_output_core {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q₀ : Pi → ℝ) (hQ₀ : ∀ π, 0 ≤ Q₀ π)
    (hhalt : HaltsAt Pi H μ Q₀) :
    SolvesOP Pi H μ (rescale Pi H μ Q₀) := by
  set R := rescale Pi H μ Q₀
  have hR := rescale_nonneg Pi H μ hK Q₀ hQ₀
  have hW := rescale_mass_le Pi H μ hK Q₀
  have hb := bCoef_nonneg Pi H μ hμ
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  unfold weightedMass at hW
  have hsplit : ∑ π, R π * (2 * (K : ℝ) + bCoef Pi H μ (π : X → Fin K)) =
      2 * K * ∑ π, R π + ∑ π, R π * bCoef Pi H μ (π : X → Fin K) := by
    rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro π _; ring
  have hRb : 0 ≤ ∑ π, R π * bCoef Pi H μ (π : X → Fin K) :=
    sum_nonneg (fun π _ => mul_nonneg (hR π) (hb π))
  have hRs : 0 ≤ ∑ π, R π := sum_nonneg (fun π _ => hR π)
  refine ⟨⟨hR, ?_⟩, ?_, ?_⟩
  · rw [hsplit] at hW
    have : 2 * K * ∑ π, R π ≤ 2 * K * 1 := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  · rw [hsplit] at hW
    nlinarith
  · intro π
    have := hhalt π
    unfold Dfun Vfun at this
    linarith


lemma log_one_add_ge (z : ℝ) (hz : 0 ≤ z) : z - z ^ 2 / 2 ≤ Real.log (1 + z) := by
  let g : ℝ → ℝ := fun z => Real.log (1 + z) - z + z ^ 2 / 2
  have hderiv : ∀ w : ℝ, 0 ≤ w → HasDerivAt g (w ^ 2 / (1 + w)) w := by
    intro w hw
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 w := (hasDerivAt_id w).const_add 1
    have h2 := h1.log (by simp; linarith)
    have h3 := (h2.sub (hasDerivAt_id w)).add ((hasDerivAt_pow 2 w).div_const 2)
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro w hw; exact (hderiv w hw).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Ici] at hw
      exact (hderiv w (le_of_lt hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Ici] at hw
      rw [(hderiv w (le_of_lt hw)).deriv]
      have : (0:ℝ) < 1 + w := by linarith [Set.mem_Ioi.1 hw]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
  simp only [g, add_zero, Real.log_one] at this
  norm_num at this
  linarith

lemma empExp_sub (H : History X K t) (f g : X → ℝ) :
    empExp H (fun x => f x - g x) = empExp H f - empExp H g := by
  unfold empExp; rw [sum_sub_distrib]; ring

lemma empExp_affine (H : History X K t) (a b d : ℝ) (f g : X → ℝ) (ht : 0 < t) :
    empExp H (fun x => a * f x + b * g x + d) = a * empExp H f + b * empExp H g + d := by
  unfold empExp
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (t : ℝ) ≠ 0 := by positivity
  field_simp

lemma empExp_mono (H : History X K t) (f g : X → ℝ) (h : ∀ x, f x ≤ g x) (ht : 0 < t) :
    empExp H f ≤ empExp H g := by
  unfold empExp
  exact mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => h _)) (by positivity)

lemma sp_ge (Pi : Finset (X → Fin K)) (μ : ℝ) (hKμ : (K : ℝ) * μ ≤ 1 / 2) (Q : Pi → ℝ)
    (hQ : ∀ π, 0 ≤ Q π) (x : X) (a : Fin K) : μ ≤ smoothedProj Pi μ Q x a := by
  unfold smoothedProj
  have : 0 ≤ ∑ π ∈ univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π :=
    sum_nonneg (fun π _ => hQ π)
  nlinarith

lemma sp_update (Pi : Finset (X → Fin K)) (μ : ℝ) (Q : Pi → ℝ) (π : Pi) (α : ℝ) (x : X)
    (a : Fin K) :
    smoothedProj Pi μ (Function.update Q π (Q π + α)) x a =
      smoothedProj Pi μ Q x a + if a = (π : X → Fin K) x then (1 - (K : ℝ) * μ) * α else 0 := by
  unfold smoothedProj
  have : ∀ π' ∈ univ.filter (fun π' : Pi => (π' : X → Fin K) x = a),
      Function.update Q π (Q π + α) π' = Q π' + if π = π' then α else 0 := by
    intro π' _
    rw [Function.update_apply]
    by_cases h : π' = π
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), add_zero]
  rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq]
  simp only [mem_filter, mem_univ, true_and]
  by_cases h : (π : X → Fin K) x = a
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

lemma key_alg (t μ c K V S b α G : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hc : 0 < c) (hK : 0 < K)
    (hS : 0 < S) (hb : 0 ≤ b) (hD : 0 < V - (2 * K + b))
    (hα : α = (V + (V - (2 * K + b))) / (2 * c * S)) (hμS : μ * S ≤ V)
    (hG : (1 / K) * (c * α * V - c ^ 2 * α ^ 2 * S / 2) - c * α ≤ G) :
    t * μ ^ 2 / (4 * c) ≤ t * μ * (G / c - α * b / (2 * K)) := by
  set A := V + (V - (2 * K + b)) with hA
  have hE : (1 / K) * (c * α * V - c ^ 2 * α ^ 2 * S / 2) - c * α - c * α * b / (2 * K) =
      c * (A ^ 2 / (8 * K * c * S)) := by
    rw [hα]; field_simp; ring
  have hV : 2 * K < V := by linarith
  have hAV : V ≤ A := by linarith
  have hA2 : 2 * K * μ * S ≤ A ^ 2 := by
    have h1 : 2 * K * (μ * S) ≤ 2 * K * V := mul_le_mul_of_nonneg_left hμS (by linarith)
    have h2 : 2 * K * V ≤ V * V := by nlinarith
    nlinarith
  have hGc : A ^ 2 / (8 * K * c * S) ≤ G / c - α * b / (2 * K) := by
    have : c * (A ^ 2 / (8 * K * c * S)) ≤ G - c * α * b / (2 * K) := by linarith
    rw [le_sub_iff_add_le, le_div_iff₀ hc]
    have e : (A ^ 2 / (8 * K * c * S) + α * b / (2 * K)) * c =
        c * (A ^ 2 / (8 * K * c * S)) + c * α * b / (2 * K) := by ring
    rw [e]; linarith
  have hfin : μ / (4 * c) ≤ A ^ 2 / (8 * K * c * S) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hK hc]
  calc t * μ ^ 2 / (4 * c) = t * μ * (μ / (4 * c)) := by ring
    _ ≤ t * μ * (A ^ 2 / (8 * K * c * S)) := mul_le_mul_of_nonneg_left hfin (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hGc (by positivity)

theorem potential_decrease_core {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π) (π : Pi)
    (hD : 0 < Dfun Pi H μ Q π) :
    0 < alphaStep Pi H μ Q π ∧
      (t : ℝ) * μ ^ 2 / (4 * (1 - (K : ℝ) * μ))
        ≤ potential Pi H μ Q - potential Pi H μ (addAlpha Pi H μ Q π) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hKμ : (K : ℝ) * μ ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hμK; nlinarith
  set c := 1 - (K : ℝ) * μ with hcdef
  have hc : 0 < c := by linarith
  set q : X → ℝ := fun x => smoothedProj Pi μ Q x ((π : X → Fin K) x) with hqdef
  have hq : ∀ x, μ ≤ q x := fun x => sp_ge Pi μ hKμ Q hQ x _
  have hqpos : ∀ x, 0 < q x := fun x => lt_of_lt_of_le hμ (hq x)
  set V := Vfun Pi H μ Q π with hVdef
  set S := Sfun Pi H μ Q π with hSdef
  set b := bCoef Pi H μ (π : X → Fin K) with hbdef
  have hb : 0 ≤ b := bCoef_nonneg Pi H μ hμ π
  have hDV : Dfun Pi H μ Q π = V - (2 * K + b) := rfl
  have hVs : V = (1 / (t : ℝ)) * ∑ i, 1 / q (H.x i) := rfl
  have hSs : S = (1 / (t : ℝ)) * ∑ i, 1 / (q (H.x i)) ^ 2 := rfl
  have hSpos : 0 < S := by
    rw [hSs]
    apply mul_pos (by positivity)
    apply sum_pos (fun i _ => by have := hqpos (H.x i); positivity)
    exact ⟨⟨0, ht⟩, mem_univ _⟩
  have hμS : μ * S ≤ V := by
    rw [hSs, hVs, ← mul_assoc, mul_comm μ, mul_assoc, mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum; intro i _
    have h1 := hq (H.x i); have h2 := hqpos (H.x i)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) h2]; nlinarith
  set α := alphaStep Pi H μ Q π with hαdef
  have hα : α = (V + (V - (2 * K + b))) / (2 * c * S) := rfl
  have hαpos : 0 < α := by
    rw [hα]; apply div_pos _ (by positivity); rw [hDV] at hD; linarith
  refine ⟨hαpos, ?_⟩
  -- the change of the potential
  have hQ' : addAlpha Pi H μ Q π = Function.update Q π (Q π + α) := rfl
  have hRE : ∀ x, relEntropy (uniformA K) (smoothedProj Pi μ (addAlpha Pi H μ Q π) x) =
      relEntropy (uniformA K) (smoothedProj Pi μ Q x) -
        ((1 / K) * Real.log (1 + c * α / q x) - c * α) := by
    intro x
    unfold relEntropy uniformA
    have hterm : ∀ a : Fin K,
        1 / (K : ℝ) * Real.log (1 / K / smoothedProj Pi μ (addAlpha Pi H μ Q π) x a) +
          smoothedProj Pi μ (addAlpha Pi H μ Q π) x a - 1 / K =
        (1 / (K : ℝ) * Real.log (1 / K / smoothedProj Pi μ Q x a) +
          smoothedProj Pi μ Q x a - 1 / K) +
        if a = (π : X → Fin K) x then
          -((1 / K) * Real.log (1 + c * α / q x) - c * α) else 0 := by
      intro a
      rw [hQ', sp_update]
      by_cases h : a = (π : X → Fin K) x
      · subst h
        rw [if_pos rfl, if_pos rfl]
        have hq1 := hqpos x
        have hq2 : 0 < q x + c * α := by positivity
        have e1 : Real.log (1 / K / (q x + c * α)) = Real.log (1 / K) - Real.log (q x + c * α) :=
          Real.log_div (by positivity) hq2.ne'
        have e2 : Real.log (1 / K / q x) = Real.log (1 / K) - Real.log (q x) :=
          Real.log_div (by positivity) hq1.ne'
        have e3 : Real.log (1 + c * α / q x) = Real.log (q x + c * α) - Real.log (q x) := by
          rw [show 1 + c * α / q x = (q x + c * α) / q x by field_simp,
            Real.log_div hq2.ne' hq1.ne']
        change 1 / (K : ℝ) * Real.log (1 / K / (q x + c * α)) + (q x + c * α) - 1 / K =
          1 / (K : ℝ) * Real.log (1 / K / q x) + q x - 1 / K +
            -(1 / K * Real.log (1 + c * α / q x) - c * α)
        rw [e1, e2, e3]; ring
      · rw [if_neg h, if_neg h, add_zero, add_zero]
    rw [sum_congr rfl (fun a _ => hterm a), sum_add_distrib, sum_ite_eq']
    simp only [mem_univ, if_true]; ring
  have hB : ∑ π', addAlpha Pi H μ Q π π' * bCoef Pi H μ (π' : X → Fin K) =
      ∑ π', Q π' * bCoef Pi H μ (π' : X → Fin K) + α * b := by
    rw [hQ']
    have : ∀ π' ∈ (univ : Finset Pi), Function.update Q π (Q π + α) π' *
        bCoef Pi H μ (π' : X → Fin K) = Q π' * bCoef Pi H μ (π' : X → Fin K) +
          if π = π' then α * b else 0 := by
      intro π' _
      rw [Function.update_apply]
      by_cases h : π' = π
      · subst h; simp [hbdef]; ring
      · rw [if_neg h, if_neg (Ne.symm h), add_zero]
    rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq]; simp
  set G := empExp H (fun x => (1 / K) * Real.log (1 + c * α / q x) - c * α) with hGdef
  have hdiff : potential Pi H μ Q - potential Pi H μ (addAlpha Pi H μ Q π) =
      t * μ * (G / c - α * b / (2 * K)) := by
    unfold potential
    rw [hB, show (fun x => relEntropy (uniformA K) (smoothedProj Pi μ (addAlpha Pi H μ Q π) x)) =
      (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x) -
        ((1 / K) * Real.log (1 + c * α / q x) - c * α)) from funext hRE, empExp_sub]
    rw [← hcdef, ← hGdef]; field_simp; ring
  rw [hdiff]
  apply key_alg t μ c K V S b α G htr hμ hc hKr hSpos hb (by rw [hDV] at hD; linarith) hα hμS
  -- lower bound on G
  have hlow : ∀ x, (1 / K) * (c * α * (1 / q x) - c ^ 2 * α ^ 2 * (1 / q x ^ 2) / 2) - c * α ≤
      (1 / K) * Real.log (1 + c * α / q x) - c * α := by
    intro x
    have hz : 0 ≤ c * α / q x := by have := hqpos x; positivity
    have := log_one_add_ge _ hz
    have e : c * α * (1 / q x) - c ^ 2 * α ^ 2 * (1 / q x ^ 2) / 2 =
        c * α / q x - (c * α / q x) ^ 2 / 2 := by field_simp
    rw [e]
    have hK' : 0 ≤ 1 / (K : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hK']
  have := empExp_mono H _ _ hlow ht
  refine le_trans (le_of_eq ?_) this
  have hfun : (fun x => (1 / K) * (c * α * (1 / q x) - c ^ 2 * α ^ 2 * (1 / q x ^ 2) / 2) - c * α) =
      (fun x => (c * α / K) * (1 / q x) + (-(c ^ 2 * α ^ 2) / (2 * K)) * (1 / q x ^ 2) +
        (-(c * α))) := by
    funext x; ring
  rw [hfun, empExp_affine H _ _ _ _ _ ht]
  have hV' : V = empExp H (fun x => 1 / q x) := rfl
  have hS' : S = empExp H (fun x => 1 / q x ^ 2) := rfl
  rw [← hV', ← hS']; ring


lemma empExp_const (H : History X K t) (k : ℝ) (ht : 0 < t) : empExp H (fun _ => k) = k := by
  unfold empExp; rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (t : ℝ) ≠ 0 := by positivity
  field_simp

lemma tangent (K μ y : ℝ) (hK : 0 < K) (hμ : 0 < μ) (hc : 0 < 1 - K * μ) (hy : 0 ≤ y) :
    y / ((1 - K * μ) * y + μ) ≤ 1 + μ * K ^ 2 * (y - 1 / K) := by
  have hden : 0 < (1 - K * μ) * y + μ := by positivity
  rw [div_le_iff₀ hden]
  have e : (1 + μ * K ^ 2 * (y - 1 / K)) * ((1 - K * μ) * y + μ) - y =
      μ * (1 - K * μ) * (K * y - 1) ^ 2 := by field_simp; ring
  have : 0 ≤ μ * (1 - K * μ) * (K * y - 1) ^ 2 := by positivity
  linarith

lemma sp_smul (Pi : Finset (X → Fin K)) (μ γ : ℝ) (Q : Pi → ℝ) (x : X) (a : Fin K) :
    smoothedProj Pi μ (fun π => γ * Q π) x a =
      (1 - (K : ℝ) * μ) * γ * (∑ π ∈ univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π) + μ := by
  unfold smoothedProj; rw [← mul_sum]; ring

theorem potential_rescale_core {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π)
    (hmass : 2 * (K : ℝ) < weightedMass Pi H μ Q) :
    potential Pi H μ (fun π => scaleFactor Pi H μ Q * Q π) ≤ potential Pi H μ Q := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hKμ : (K : ℝ) * μ ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hμK; nlinarith
  set c := 1 - (K : ℝ) * μ with hcdef
  have hc : 0 < c := by linarith
  set W := weightedMass Pi H μ Q with hWdef
  have hWpos : 0 < W := lt_trans (by positivity) hmass
  set γ := scaleFactor Pi H μ Q with hγdef
  have hγ : γ = 2 * K / W := rfl
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ1 : γ ≤ 1 := by rw [hγ, div_le_one hWpos]; exact hmass.le
  set Sm := ∑ π, Q π with hSm
  set B := ∑ π, Q π * bCoef Pi H μ (π : X → Fin K) with hBdef
  have hB0 : 0 ≤ B := sum_nonneg (fun π _ => mul_nonneg (hQ π) (bCoef_nonneg Pi H μ hμ π))
  have hWsplit : W = 2 * K * Sm + B := by
    rw [hWdef]; unfold weightedMass; rw [hSm, hBdef, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro π _; ring
  have hγinv : 1 / γ = Sm + B / (2 * K) := by
    rw [hγ, hWsplit]; field_simp
  have hγSm : γ * Sm ≤ 1 := by
    rw [hγ, div_mul_eq_mul_div, div_le_one hWpos, hWsplit]; linarith
  -- per-context bound on the relative entropy difference
  set s : X → Fin K → ℝ := fun x a =>
    ∑ π ∈ univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π with hsdef
  have hs0 : ∀ x a, 0 ≤ s x a := fun x a => sum_nonneg (fun π _ => hQ π)
  have hsum : ∀ x, ∑ a, s x a = Sm := fun x => by
    rw [hsdef]; simp only; exact sum_fiberwise univ (fun π : Pi => (π : X → Fin K) x) Q
  have hq1 : ∀ x a, smoothedProj Pi μ Q x a = c * s x a + μ := fun x a => rfl
  have hqs : ∀ x a, smoothedProj Pi μ (fun π => γ * Q π) x a = c * γ * s x a + μ :=
    fun x a => sp_smul Pi μ γ Q x a
  have hREdiff : ∀ x, c * (1 - γ) * (Sm - 1 / γ) ≤
      relEntropy (uniformA K) (smoothedProj Pi μ Q x) -
        relEntropy (uniformA K) (smoothedProj Pi μ (fun π => γ * Q π) x) := by
    intro x
    unfold relEntropy uniformA
    rw [← sum_sub_distrib]
    have hterm : ∀ a, c * (1 - γ) * (s x a - (1 / K) * s x a / (c * γ * s x a + μ)) ≤
        (1 / (K : ℝ) * Real.log (1 / K / smoothedProj Pi μ Q x a) + smoothedProj Pi μ Q x a
          - 1 / K) - (1 / (K : ℝ) * Real.log (1 / K / smoothedProj Pi μ (fun π => γ * Q π) x a)
          + smoothedProj Pi μ (fun π => γ * Q π) x a - 1 / K) := by
      intro a
      rw [hq1, hqs]
      have h0 := hs0 x a
      have hp1 : 0 < c * s x a + μ := by positivity
      have hps : 0 < c * γ * s x a + μ := by positivity
      rw [Real.log_div (by positivity) hp1.ne', Real.log_div (by positivity) hps.ne']
      have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < (c * γ * s x a + μ) / (c * s x a + μ)
        by positivity)
      rw [Real.log_div hps.ne' hp1.ne', inv_div] at hlog
      have e : 1 - (c * s x a + μ) / (c * γ * s x a + μ) =
          -(c * (1 - γ) * s x a) / (c * γ * s x a + μ) := by field_simp; ring
      rw [e] at hlog
      have e2 : c * (1 - γ) * (s x a - 1 / K * s x a / (c * γ * s x a + μ)) =
          1 / K * (-(c * (1 - γ) * s x a) / (c * γ * s x a + μ)) + c * (1 - γ) * s x a := by
        field_simp; ring
      rw [e2]
      have hK' : 0 ≤ 1 / (K : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hlog hK']
    refine le_trans ?_ (sum_le_sum (fun a _ => hterm a))
    -- lower bound the sum
    have htan : ∀ a, γ * s x a / (c * (γ * s x a) + μ) ≤ 1 + μ * K ^ 2 * (γ * s x a - 1 / K) :=
      fun a => tangent K μ (γ * s x a) hKr hμ hc (mul_nonneg hγpos.le (hs0 x a))
    have hsumtan : ∑ a, γ * s x a / (c * (γ * s x a) + μ) ≤ K := by
      refine le_trans (sum_le_sum (fun a _ => htan a)) ?_
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, ← mul_sum, sum_sub_distrib,
        ← mul_sum, hsum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
      have : γ * Sm - K * (1 / K) ≤ 0 := by field_simp; linarith
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ μ * K ^ 2) (by linarith : 0 ≤ -(γ * Sm - K * (1 / K)))]
    have hsum2 : ∑ a, (1 / (K : ℝ)) * s x a / (c * γ * s x a + μ) ≤ 1 / γ := by
      have e : ∑ a, (1 / (K : ℝ)) * s x a / (c * γ * s x a + μ) =
          (1 / (K * γ)) * ∑ a, γ * s x a / (c * (γ * s x a) + μ) := by
        rw [mul_sum]; apply sum_congr rfl; intro a _
        field_simp
      rw [e]
      calc (1 / (K * γ)) * ∑ a, γ * s x a / (c * (γ * s x a) + μ) ≤ (1 / (K * γ)) * K :=
            mul_le_mul_of_nonneg_left hsumtan (by positivity)
        _ = 1 / γ := by field_simp
    rw [← mul_sum, sum_sub_distrib, hsum]
    apply mul_le_mul_of_nonneg_left _ (by nlinarith)
    linarith
  have hE : c * (1 - γ) * (Sm - 1 / γ) ≤
      empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x)) -
        empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ (fun π => γ * Q π) x)) := by
    rw [← empExp_sub, ← empExp_const H (c * (1 - γ) * (Sm - 1 / γ)) ht]
    exact empExp_mono H _ _ hREdiff ht
  have hBs : ∑ π, γ * Q π * bCoef Pi H μ (π : X → Fin K) = γ * B := by
    rw [hBdef, mul_sum]; apply sum_congr rfl; intro π _; ring
  unfold potential
  rw [hBs, ← hcdef]
  rw [← sub_nonneg]
  have key : 0 ≤ (empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x)) -
        empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ (fun π => γ * Q π) x))) / c
      + (B - γ * B) / (2 * K) := by
    have h1 : (1 - γ) * (Sm - 1 / γ) ≤ (empExp H (fun x => relEntropy (uniformA K)
        (smoothedProj Pi μ Q x)) - empExp H (fun x => relEntropy (uniformA K)
        (smoothedProj Pi μ (fun π => γ * Q π) x))) / c := by
      rw [le_div_iff₀ hc]; linarith
    have h2 : (1 - γ) * (Sm - 1 / γ) + (B - γ * B) / (2 * K) = 0 := by
      rw [hγinv]; field_simp; ring
    linarith
  have : (t : ℝ) * μ * (empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x)) / c +
      B / (2 * K)) - t * μ * (empExp H (fun x => relEntropy (uniformA K)
        (smoothedProj Pi μ (fun π => γ * Q π) x)) / c + γ * B / (2 * K)) =
      t * μ * ((empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x)) -
        empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ (fun π => γ * Q π) x))) / c
      + (B - γ * B) / (2 * K)) := by ring
  rw [this]; positivity


lemma relEntropy_nonneg (hK : 0 < K) (q : Fin K → ℝ) (hq : ∀ a, 0 < q a) :
    0 ≤ relEntropy (uniformA K) q := by
  unfold relEntropy uniformA
  apply sum_nonneg; intro a _
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hx : 0 < 1 / (K : ℝ) / q a := by have := hq a; positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  rw [inv_div] at h
  have e : 1 / (K : ℝ) * (1 - q a / (1 / K)) = 1 / K - q a := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 1 / K)]

lemma potential_nonneg (hK : 0 < K) (ht : 0 < t) (Pi : Finset (X → Fin K)) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hKμ : (K : ℝ) * μ ≤ 1 / 2) (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π) :
    0 ≤ potential Pi H μ Q := by
  unfold potential
  have hc : 0 < 1 - (K : ℝ) * μ := by linarith
  have h1 : 0 ≤ empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x)) := by
    rw [← empExp_const H 0 ht]
    exact empExp_mono H _ _ (fun x => relEntropy_nonneg hK _
      (fun a => lt_of_lt_of_le hμ (sp_ge Pi μ hKμ Q hQ x a))) ht
  have h2 : 0 ≤ ∑ π, Q π * bCoef Pi H μ (π : X → Fin K) :=
    sum_nonneg (fun π _ => mul_nonneg (hQ π) (bCoef_nonneg Pi H μ hμ π))
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  positivity

lemma potential_zero (hK : 0 < K) (ht : 0 < t) (Pi : Finset (X → Fin K)) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) :
    potential Pi H μ (fun _ => 0) =
      t * μ * ((Real.log (1 / (K * μ)) + K * μ - 1) / (1 - K * μ)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hsp : ∀ x, smoothedProj Pi μ (fun _ => (0 : ℝ)) x = fun _ => μ := by
    intro x; funext a; unfold smoothedProj; simp
  unfold potential
  simp only [hsp, zero_mul, sum_const_zero, zero_div, add_zero]
  rw [empExp_const H _ ht]
  unfold relEntropy uniformA
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, div_div]
  congr 2
  field_simp

theorem cd_halts_core {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ))) :
    (∀ (n : ℕ) (Qs : ℕ → Pi → ℝ), IsRun Pi H μ (fun _ => 0) n Qs →
        (n : ℝ) ≤ 4 * Real.log (1 / ((K : ℝ) * μ)) / μ) ∧
    (∀ (n : ℕ) (Qs : ℕ → Pi → ℝ), IsRun Pi H μ (fun _ => 0) n Qs →
        HaltsAt Pi H μ (Qs n) → SolvesOP Pi H μ (rescale Pi H μ (Qs n))) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hKμ : (K : ℝ) * μ ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hμK; nlinarith
  have hc : 0 < 1 - (K : ℝ) * μ := by linarith
  set δ := (t : ℝ) * μ ^ 2 / (4 * (1 - (K : ℝ) * μ)) with hδ
  -- invariant along a run
  have hinv : ∀ (n : ℕ) (Qs : ℕ → Pi → ℝ), IsRun Pi H μ (fun _ => 0) n Qs →
      ∀ k ≤ n, (∀ π, 0 ≤ Qs k π) ∧
        potential Pi H μ (Qs k) + k * δ ≤ potential Pi H μ (fun _ => 0) := by
    intro n Qs hrun k
    induction k with
    | zero =>
      intro _; rw [hrun.1]; simp
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨π, hDπ, hstep⟩ := hrun.2 k (by omega)
      have hR := rescale_nonneg Pi H μ hK (Qs k) ih1
      have hdec := potential_decrease_core hK ht Pi hPi H μ hμ hμK _ hR π hDπ
      have hresc : potential Pi H μ (rescale Pi H μ (Qs k)) ≤ potential Pi H μ (Qs k) := by
        unfold rescale
        split_ifs with h
        · exact potential_rescale_core hK ht Pi hPi H μ hμ hμK _ ih1 h
        · exact le_rfl
      refine ⟨?_, ?_⟩
      · intro π'
        rw [hstep]; unfold cdStep addAlpha
        rw [Function.update_apply]
        split_ifs with h
        · subst h; linarith [hR π', hdec.1]
        · exact hR π'
      · rw [hstep]; unfold cdStep
        push_cast
        linarith [hdec.2]
  refine ⟨?_, ?_⟩
  · intro n Qs hrun
    obtain ⟨h1, h2⟩ := hinv n Qs hrun n le_rfl
    have h3 := potential_nonneg hK ht Pi H μ hμ hKμ (Qs n) h1
    rw [potential_zero hK ht Pi H μ hμ] at h2
    have hL : 0 ≤ Real.log (1 / ((K : ℝ) * μ)) := by
      apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
    have h4 : (n : ℝ) * δ ≤ t * μ * (Real.log (1 / (K * μ)) / (1 - K * μ)) := by
      have : (Real.log (1 / (K * μ)) + K * μ - 1) / (1 - K * μ) ≤
          Real.log (1 / (K * μ)) / (1 - K * μ) := by
        apply div_le_div_of_nonneg_right _ hc.le; linarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ t * μ)]
    rw [hδ] at h4
    rw [le_div_iff₀ hμ]
    have e : (n : ℝ) * (t * μ ^ 2 / (4 * (1 - K * μ))) =
        (t * μ / (4 * (1 - K * μ))) * (n * μ) := by ring
    have e2 : t * μ * (Real.log (1 / (K * μ)) / (1 - K * μ)) =
        (t * μ / (4 * (1 - K * μ))) * (4 * Real.log (1 / (K * μ))) := by
      field_simp
    rw [e, e2] at h4
    exact le_of_mul_le_mul_left h4 (by positivity)
  · intro n Qs hrun hhalt
    exact halt_output_core hK ht Pi hPi H μ hμ hμK (Qs n) (hinv n Qs hrun n le_rfl).1 hhalt

end TamingMonster.CoordDescent

open TamingMonster.CoordDescent

theorem solution {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π)
    (hmass : 2 * (K : ℝ) < weightedMass Pi H μ Q) :
    potential Pi H μ (fun π => scaleFactor Pi H μ Q * Q π) ≤ potential Pi H μ Q := by
  exact potential_rescale_core hK ht Pi hPi H μ hμ hμK Q hQ hmass
