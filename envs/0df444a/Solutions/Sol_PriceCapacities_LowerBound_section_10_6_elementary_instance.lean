-- Prove2me | solution 1 for PriceCapacities.LowerBound.section_10_6_elementary_instance
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T01:01:29.175646+00:00
-- url     : https://prove2.me/submissions/7676ec8c-6058-4590-9330-07cf8a1bcedc

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_ElementaryInstance

set_option autoImplicit false
set_option maxHeartbeats 600000

open PriceCapacities
open PriceCapacities.LowerBound

theorem solution (z : ℕ) (hz : 1 ≤ z) (k : ℕ) (hk : 2 ≤ k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (w : Fin k → Fin ⌈1 / ε⌉₊ → EuclideanSpace ℝ (Fin 2))
    (hw : ∀ i r, ‖w i r‖ = (4 * k : ℝ) ^ (-(1 / (z : ℝ))))
    (hinj : ∀ i, Function.Injective (w i)) :
    (elemInstance w).card = k * ⌈1 / ε⌉₊ ∧
    (k : ℝ) / ε ≤ ((elemInstance w).card : ℝ) ∧
    capCost (z : ℝ) (unweighted (elemInstance w)) (elemCenter k) (fun _ => (⌈1 / ε⌉₊ : ℝ))
      ≤ (k : ℝ) * ⌈1 / ε⌉₊ * ((4 * k : ℝ) ^ (-(1 / (z : ℝ)))) ^ (z : ℝ) ∧
    (k : ℝ) * ⌈1 / ε⌉₊ * ((4 * k : ℝ) ^ (-(1 / (z : ℝ)))) ^ (z : ℝ) = (⌈1 / ε⌉₊ : ℝ) / 4 ∧
    ∀ Q : WeightedSet (EuclideanSpace ℝ (Fin k ⊕ Fin 2)),
      IsCapacitatedCoreset k (z : ℝ) ε (unweighted (elemInstance w)) Q → k ≤ size Q := by
  classical
  let X := EuclideanSpace ℝ (Fin k ⊕ Fin 2)
  let m := ⌈1 / ε⌉₊
  let C := elemCenter k
  let τ : ℝ := (4 * (k : ℝ)) ^ (-(1 / (z : ℝ)))
  let e (p : Fin k × Fin m) : X := elemPoint w p.1 p.2
  let S := elemInstance w
  let P := unweighted S
  have mk : 0 < m := Nat.one_le_ceil_iff.mpr (by positivity)
  have mz : 0 < (m : ℝ) := by exact_mod_cast mk
  have kz : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let _ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let _ : Nonempty (Fin m) := ⟨⟨0, mk⟩⟩
  have einj : Function.Injective e := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := by
      by_contra he
      have v := congrArg (fun x : X => x (Sum.inl i)) h
      norm_num [e, elemPoint, he] at v
    subst j
    congr 1
    apply hinj i
    apply WithLp.ofLp_injective
    funext l
    exact congrArg (fun x : X => x (Sum.inr l)) h
  have card : S.card = k * m := by
    change (Finset.univ.image e).card = _
    rw [Finset.card_image_of_injective _ einj]
    simp
  have sw (x : X) : P x = if x ∈ S then 1 else 0 := by
    simp [P, unweighted, Finsupp.single_apply, Finsupp.finsetSum_apply, eq_comm]
  have supp : P.support = S := by
    ext x
    simp [Finsupp.mem_support_iff, sw]
  have weight : totalWeight P = (k : ℝ) * m := by
    unfold totalWeight wsum
    rw [supp]
    simp only [sw, mul_one]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp [card]
    · intro x h
      simp [h]
  have same (p : Fin k × Fin m) : dist (e p) (C p.1) = τ := by
    have zeroCoord (j : Fin k) : (e p - C p.1) (Sum.inl j) = 0 := by
      change ((if j = p.1 then 4 else 0) : ℝ) - (if j = p.1 then 4 else 0) = 0
      exact sub_self _
    have tailCoord (j : Fin 2) : (e p - C p.1) (Sum.inr j) = w p.1 p.2 j := by
      change w p.1 p.2 j - 0 = _
      exact sub_zero _
    have eqsq : ‖e p - C p.1‖ ^ 2 = ‖w p.1 p.2‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
      change (∑ j, (e p - C p.1) (Sum.inl j) ^ 2) +
        (∑ j, (e p - C p.1) (Sum.inr j) ^ 2) = ∑ j, w p.1 p.2 j ^ 2
      simp only [zeroCoord, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
        zero_add, tailCoord]
    have hτ : ‖w p.1 p.2‖ = τ := hw p.1 p.2
    rw [dist_eq_norm, ← hτ]
    nlinarith [norm_nonneg (e p - C p.1), norm_nonneg (w p.1 p.2)]
  have scale : (k : ℝ) * m * τ ^ (z : ℝ) = (m : ℝ) / 4 := by
    have zz : (z : ℝ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
    unfold τ
    rw [← Real.rpow_mul (by positivity), neg_mul, one_div_mul_cancel zz, Real.rpow_neg_one]
    field_simp
  let inv := Function.invFun e
  have inv_e (p : Fin k × Fin m) : inv (e p) = p := Function.leftInverse_invFun einj p
  let assign (x : X) (i : Fin k) : ℝ := if (inv x).1 = i then 1 else 0
  have assign_e (p : Fin k × Fin m) (i : Fin k) : assign (e p) i = if p.1 = i then 1 else 0 := by simp [assign, inv_e]
  have trans_sum (f : X → ℝ) : (∑ x ∈ P.support, f x) = ∑ p : Fin k × Fin m, f (e p) := by
    rw [supp]
    change ∑ x ∈ Finset.univ.image e, f x = _
    exact Finset.sum_image (fun _ _ _ _ h => einj h)
  have feasible : IsLoadAssignment P (fun _ => (m : ℝ)) assign := by
    refine ⟨fun x i => by unfold assign; split <;> norm_num, ?_, ?_⟩
    · intro x hx
      rw [supp] at hx
      simp [assign, sw, hx, eq_comm]
    · intro i
      rw [trans_sum, Fintype.sum_prod_type]
      simp only [assign_e]
      have column (j : Fin k) : (∑ _r : Fin m, if j = i then (1 : ℝ) else 0) =
          if j = i then (m : ℝ) else 0 := by split <;> simp
      simp [column]
  have original : capCost (z : ℝ) P C (fun _ => (m : ℝ)) ≤ (k : ℝ) * m * τ ^ (z : ℝ) := by
    have assign_value : assignmentCost (z : ℝ) P C assign = (k : ℝ) * m * τ ^ (z : ℝ) := by
      unfold assignmentCost
      rw [trans_sum]
      have h (p : Fin k × Fin m) : (∑ i, assign (e p) i * dist (e p) (C i) ^ (z : ℝ)) = τ ^ (z : ℝ) := by
        simp only [assign_e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, same]
      simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    rw [← assign_value]
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      exact Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => mul_nonneg (hb.1 _ _) (Real.rpow_nonneg dist_nonneg _)
    · exact ⟨assign, feasible, rfl⟩
  have sep (i j : Fin k) (hij : i ≠ j) : 4 ≤ dist (C i) (C j) := by
    have h := PiLp.norm_apply_le (C i - C j) (Sum.inl i)
    rw [← dist_eq_norm] at h
    simpa [C, elemCenter, hij, Real.norm_eq_abs] using h
  refine ⟨card, ?_, original, scale, ?_⟩
  · rw [card, Nat.cast_mul, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) kz.le
  intro Q hQ
  by_contra! hcard
  let pick (x : X) : Fin k := if h : ∃ i, dist x (C i) < 1 then Classical.choose h else Classical.choice inferInstance
  have hits (x : X) (i : Fin k) (hi : dist x (C i) < 1) : pick x = i := by
    have h : ∃ i, dist x (C i) < 1 := ⟨i, hi⟩
    unfold pick
    rw [dif_pos h]
    by_contra hc
    have lower := sep (Classical.choose h) i hc
    have tri := dist_triangle_left (C (Classical.choose h)) (C i) x
    linarith [Classical.choose_spec h]
  have missing : ∃ i : Fin k, i ∉ Q.support.image pick := by
    by_contra! hh
    have eq : Q.support.image pick = Finset.univ := Finset.eq_univ_of_forall hh
    have hle := Finset.card_image_le (s := Q.support) (f := pick)
    rw [eq, Finset.card_univ, Fintype.card_fin] at hle
    exact (not_le_of_gt hcard) hle
  obtain ⟨i, hi⟩ := missing
  have away (x : X) (hx : x ∈ Q.support) : 1 ≤ dist x (C i) := by
    by_contra! h
    exact hi (Finset.mem_image.mpr ⟨x, hx, hits x i h⟩)
  have hload : IsFeasibleLoad (totalWeight P) (fun _ : Fin k => (m : ℝ)) := by
    refine ⟨fun _ => mz.le, ?_⟩
    simp [weight, nsmul_eq_mul]
  have allcost (b : X → Fin k → ℝ) (hb : IsLoadAssignment Q (fun _ => (m : ℝ)) b) :
      (m : ℝ) ≤ assignmentCost (z : ℝ) Q C b := by
    have col : ∑ x ∈ Q.support, b x i = (m : ℝ) := hb.2.2 i
    rw [← col]
    unfold assignmentCost
    apply Finset.sum_le_sum
    intro x hx
    have hd : 1 ≤ dist x (C i) ^ (z : ℝ) := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (away x hx) (by positivity : 0 ≤ (z : ℝ))
    calc
      _ ≤ b x i * dist x (C i) ^ (z : ℝ) := le_mul_of_one_le_right (hb.1 x i) hd
      _ ≤ _ := Finset.single_le_sum (f := fun j => b x j * dist x (C j) ^ (z : ℝ))
        (fun j _ => mul_nonneg (hb.1 x j) (Real.rpow_nonneg dist_nonneg _)) (Finset.mem_univ i)
  have Q_lower : (m : ℝ) ≤ capCost (z : ℝ) Q C (fun _ => (m : ℝ)) := by
    let b (x : X) (_ : Fin k) : ℝ := (Q x : ℝ) / k
    have b_ok : IsLoadAssignment Q (fun _ => (m : ℝ)) b := by
      refine ⟨fun x i => div_nonneg (by positivity) kz.le, ?_, ?_⟩
      · intro x _
        simp only [b, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      · intro j
        simp only [b, ← Finset.sum_div]
        have ht : (∑ x ∈ Q.support, (Q x : ℝ)) = totalWeight Q := by simp [totalWeight, wsum]
        rw [ht, hQ.1, weight]
        exact mul_div_cancel_left₀ _ kz.ne'
    unfold capCost
    have hn : ({v : ℝ | ∃ a : X → Fin k → ℝ,
        IsLoadAssignment Q (fun _ => (m : ℝ)) a ∧ v = assignmentCost (z : ℝ) Q C a}).Nonempty :=
      ⟨_, b, b_ok, rfl⟩
    refine le_csInf hn ?_
    rintro _ ⟨b, hb, rfl⟩
    exact allcost b hb
  have Q_upper := (abs_le.mp (hQ.2 C _ hload)).2
  have P_upper : capCost (z : ℝ) P C (fun _ => (m : ℝ)) ≤ (m : ℝ) / 4 := original.trans_eq scale
  have bound := mul_le_mul_of_nonneg_left P_upper hε0.le
  nlinarith [mul_lt_mul_of_pos_right hε1 mz]
