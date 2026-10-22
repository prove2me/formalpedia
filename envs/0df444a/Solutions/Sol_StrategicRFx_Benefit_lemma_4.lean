-- Prove2me | solution 1 for StrategicRFx.Benefit.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:29:09.783679+00:00
-- url     : https://prove2.me/submissions/fa5dd1ce-d86a-4f89-9cf8-8415ed5debfe

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

open StrategicRFx.Benefit

lemma rfx5_Qbound (θ0 θ1 a0 a1 x0 x1 F0 F1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hF0 : F0 = θ0 * max (a0 - F1) 0) (hF1 : F1 = θ1 * max (a1 - F0) 0)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1)
    (hq0 : x0 ≤ θ0 * max (a0 - x1) 0) (hq1 : x1 ≤ θ1 * max (a1 - x0) 0) :
    x0 + x1 ≤ F0 + F1 := by
  have h01 : 0 < 1 - θ0 * θ1 := by nlinarith
  rcases le_total 0 (a0 - F1) with hA | hA <;>
  rcases le_total 0 (a1 - F0) with hB | hB <;>
  rcases le_total 0 (a0 - x1) with hC | hC <;>
  rcases le_total 0 (a1 - x0) with hD | hD <;>
  simp only [max_eq_left hA, max_eq_right hA, max_eq_left hB, max_eq_right hB,
    max_eq_left hC, max_eq_right hC, max_eq_left hD, max_eq_right hD, mul_zero] at hF0 hF1 hq0 hq1 <;>
  nlinarith [mul_le_mul_of_nonneg_left hq0 (by linarith : (0:ℝ) ≤ 1 - θ1),
    mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ 1 - θ0),
    mul_pos h0 h1, mul_pos h0 ha0, mul_pos h1 ha1, mul_pos (by linarith : (0:ℝ) < 1 - θ1) h0,
    mul_pos (by linarith : (0:ℝ) < 1 - θ0) h1]

lemma rfx5_Sbound (θ0 θ1 a0 a1 y0 y1 F0 F1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hF0 : F0 = θ0 * max (a0 - F1) 0) (hF1 : F1 = θ1 * max (a1 - F0) 0)
    (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1)
    (hq0 : θ0 * max (a0 - y1) 0 ≤ y0) (hq1 : θ1 * max (a1 - y0) 0 ≤ y1) :
    F0 + F1 ≤ y0 + y1 := by
  have h01 : 0 < 1 - θ0 * θ1 := by nlinarith
  rcases le_total 0 (a0 - F1) with hA | hA <;>
  rcases le_total 0 (a1 - F0) with hB | hB <;>
  rcases le_total 0 (a0 - y1) with hC | hC <;>
  rcases le_total 0 (a1 - y0) with hD | hD <;>
  simp only [max_eq_left hA, max_eq_right hA, max_eq_left hB, max_eq_right hB,
    max_eq_left hC, max_eq_right hC, max_eq_left hD, max_eq_right hD, mul_zero] at hF0 hF1 hq0 hq1 <;>
  nlinarith [mul_le_mul_of_nonneg_left hq0 (by linarith : (0:ℝ) ≤ 1 - θ1),
    mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ 1 - θ0),
    mul_pos h0 h1, mul_pos h0 ha0, mul_pos h1 ha1, mul_pos (by linarith : (0:ℝ) < 1 - θ1) h0,
    mul_pos (by linarith : (0:ℝ) < 1 - θ0) h1]

lemma rfx5_follower (θ A x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 ≤ x) (hxA : x ≤ A)
    (hmax : ∀ y, 0 ≤ y → y ≤ A → nashProduct θ y (A - y) ≤ nashProduct θ x (A - x)) :
    θ * A ≤ x := by
  by_contra hlt
  push_neg at hlt
  have hA : 0 < A := by nlinarith
  have hθA : 0 < θ * A := mul_pos hθ0 hA
  have h1θ : 0 < 1 - θ := by linarith
  have h1θA : 0 < (1 - θ) * A := mul_pos h1θ hA
  set p1 := x / (θ * A) with hp1
  set p2 := (A - x) / ((1 - θ) * A) with hp2
  have hp1n : 0 ≤ p1 := div_nonneg hx0 hθA.le
  have hp2n : 0 ≤ p2 := div_nonneg (by linarith) h1θA.le
  have hne : p1 ≠ p2 := by
    intro h
    rw [hp1, hp2, div_eq_div_iff hθA.ne' h1θA.ne'] at h
    have : (x - θ * A) * A = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  have hlt' := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos hθ0 h1θ hp1n hp2n
    (by ring)).2 hne
  have hsum : θ * p1 + (1 - θ) * p2 = 1 := by
    rw [hp1, hp2]; field_simp; ring
  have ex : x = p1 * (θ * A) := by rw [hp1]; field_simp
  have eAx : A - x = p2 * ((1 - θ) * A) := by rw [hp2]; field_simp
  have key : nashProduct θ x (A - x) =
      (p1 ^ θ * p2 ^ (1 - θ)) * nashProduct θ (θ * A) (A - θ * A) := by
    unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    rw [eAx]
    conv_lhs => rw [ex]
    rw [Real.mul_rpow hp1n hθA.le, Real.mul_rpow hp2n h1θA.le]
    ring
  have hpos : 0 < nashProduct θ (θ * A) (A - θ * A) := by
    unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    exact mul_pos (Real.rpow_pos_of_pos hθA _) (Real.rpow_pos_of_pos h1θA _)
  have hm := hmax (θ * A) hθA.le (by nlinarith)
  rw [key] at hm
  nlinarith

lemma rfx5_key (θ A y : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) (hy0 : 0 ≤ y)
    (hyA : y ≤ A) :
    ∃ p1 p2 : ℝ, 0 ≤ p1 ∧ 0 ≤ p2 ∧ θ * p1 + (1 - θ) * p2 = 1 ∧ (p1 = p2 ↔ y = θ * A) ∧
      nashProduct θ y (A - y) = (p1 ^ θ * p2 ^ (1 - θ)) * nashProduct θ (θ * A) (A - θ * A) ∧
      0 < nashProduct θ (θ * A) (A - θ * A) := by
  have hθA : 0 < θ * A := mul_pos hθ0 hA
  have h1θ : 0 < 1 - θ := by linarith
  have h1θA : 0 < (1 - θ) * A := mul_pos h1θ hA
  refine ⟨y / (θ * A), (A - y) / ((1 - θ) * A), div_nonneg hy0 hθA.le,
    div_nonneg (by linarith) h1θA.le, by field_simp; ring, ?_, ?_, ?_⟩
  · rw [div_eq_div_iff hθA.ne' h1θA.ne']
    constructor
    · intro h
      have : (y - θ * A) * A = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · linarith
    · intro h; rw [h]; ring
  · unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    have ex : y = y / (θ * A) * (θ * A) := by field_simp
    have eAx : A - y = (A - y) / ((1 - θ) * A) * ((1 - θ) * A) := by field_simp
    rw [eAx]
    conv_lhs => rw [ex]
    rw [Real.mul_rpow (div_nonneg hy0 hθA.le) hθA.le,
      Real.mul_rpow (div_nonneg (by linarith) h1θA.le) h1θA.le]
    rw [← ex, ← eAx]
    ring
  · unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    exact mul_pos (Real.rpow_pos_of_pos hθA _) (Real.rpow_pos_of_pos h1θA _)

lemma rfx5_strict (θ A y : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) (hy0 : 0 ≤ y)
    (hyA : y ≤ A) (hne : y ≠ θ * A) :
    nashProduct θ y (A - y) < nashProduct θ (θ * A) (A - θ * A) := by
  obtain ⟨p1, p2, hp1, hp2, hs, hiff, he, hpos⟩ := rfx5_key θ A y hθ0 hθ1 hA hy0 hyA
  have hlt := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos (w₂ := 1 - θ) hθ0 (by linarith) hp1 hp2
    (by ring)).2 (fun h => hne (hiff.1 h))
  rw [he]; nlinarith

lemma rfx5_max (θ A y : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA0 : 0 ≤ A) (hy0 : 0 ≤ y)
    (hyA : y ≤ A) : nashProduct θ y (A - y) ≤ nashProduct θ (θ * A) (A - θ * A) := by
  rcases eq_or_ne y (θ * A) with h | h
  · rw [h]
  rcases eq_or_lt_of_le hA0 with hA | hA
  · subst hA; exfalso; apply h; simp; linarith
  exact (rfx5_strict θ A y hθ0 hθ1 hA hy0 hyA h).le

lemma rfx5_other_other (i : Fin 2) : other (other i) = i := by
  fin_cases i <;> decide

lemma rfx5_sum (P : Params) (t : Fin 2 → ℝ) (k : Fin 2) :
    P.Pi - t k - t (other k) = P.Pi - t 0 - t 1 := by
  fin_cases k
  · rfl
  · show P.Pi - t 1 - t (other 1) = _
    rw [show other 1 = 0 by decide]; ring

lemma rfx5_better (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (k : Fin 2)
    (hv : P.θ (other k) * max (P.Pi - t k - P.PiEx (other k)) 0 < t (other k)) :
    ∃ xs ys, IsLeaderSolution P k true t xs ys ∧ resBuyer P k true t < leaderBuyer P k t xs ys := by
  have hθk := hP.θ_pos k
  have hθk1 := hP.θ_lt_one k
  have hθj := hP.θ_pos (other k)
  have hEj := hP.PiEx_lt (other k)
  have hAj := hP.PiExAt_lt (other k)
  have hAj0 := hP.PiExAt_pos (other k)
  have htk := ht k
  have htj := ht (other k)
  set j := other k with hj
  set θj := P.θ j with hθjdef
  set E := P.PiEx j with hEdef
  set D0 := resBuyer P k true t with hD0
  have hD0e : D0 = max (P.Pi - t k - t j) (P.Pi - t k - θj * (P.Pi - P.PiExAt j)) := by
    rw [hD0]; simp only [resBuyer, if_true, followerSplit]
    congr 2; ring
  have hRS : resSupplier P k true t = t k := by simp [resSupplier]
  set yh : ℝ → ℝ := fun x => min E (P.Pi - x) with hyh
  set g : ℝ → ℝ := fun x => nashProduct (P.θ k) (x - t k) (leaderBuyer P k t x (yh x) - D0)
    with hg
  have hLB : ∀ x y, leaderBuyer P k t x y = P.Pi - x - min (t j) (θj * (P.Pi - x - y)) := by
    intro x y; rfl
  have hLcont : Continuous fun x => leaderBuyer P k t x (yh x) := by
    simp only [hLB, hyh]
    fun_prop
  have hgcont : Continuous g := by
    simp only [hg, nashProduct]
    refine Continuous.mul (Continuous.rpow_const (by fun_prop) (fun _ => Or.inr hθk.le))
      (Continuous.rpow_const (hLcont.sub continuous_const) (fun _ => Or.inr (by linarith)))
  set K : Set ℝ := {x | t k ≤ x ∧ D0 ≤ leaderBuyer P k t x (yh x)} with hK
  have hminnn : ∀ x, 0 ≤ min (t j) (θj * (P.Pi - x - yh x)) := by
    intro x
    apply le_min htj
    apply mul_nonneg hθj.le
    simp only [hyh]
    linarith [min_le_right E (P.Pi - x)]
  have hKsub : K ⊆ Set.Icc (t k) (P.Pi - D0) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have := hx.2
    rw [hLB] at this
    linarith [hminnn x]
  have hKclosed : IsClosed K := by
    have : K = {x | t k ≤ x} ∩ {x | D0 ≤ leaderBuyer P k t x (yh x)} := by
      ext x; simp [hK]
    rw [this]
    exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const hLcont)
  have hKcpt : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed hKsub
  -- the strictly better point
  set M := max (P.Pi - t k - E) 0 with hM
  have hMlt : M < P.Pi - P.PiExAt j := by
    apply max_lt <;> linarith
  have hθM : θj * M < θj * (P.Pi - P.PiExAt j) := mul_lt_mul_of_pos_left hMlt hθj
  set ε := min (t j - θj * M) (θj * (P.Pi - P.PiExAt j) - θj * M) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]; apply half_pos; apply lt_min <;> linarith
  have hε1 : ε < t j - θj * M := by
    have := min_le_left (t j - θj * M) (θj * (P.Pi - P.PiExAt j) - θj * M); linarith
  have hε2 : ε < θj * (P.Pi - P.PiExAt j) - θj * M := by
    have := min_le_right (t j - θj * M) (θj * (P.Pi - P.PiExAt j) - θj * M); linarith
  set x0 := t k + ε with hx0
  have hgap : P.Pi - x0 - yh x0 ≤ M := by
    simp only [hyh]
    rcases min_choice E (P.Pi - x0) with h | h <;> rw [h]
    · have := le_max_left (P.Pi - t k - E) 0; rw [← hM] at this; linarith
    · have := le_max_right (P.Pi - t k - E) 0; rw [← hM] at this; linarith
  have hL0 : P.Pi - x0 - θj * M ≤ leaderBuyer P k t x0 (yh x0) := by
    rw [hLB]
    have : min (t j) (θj * (P.Pi - x0 - yh x0)) ≤ θj * M :=
      (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hgap hθj.le)
    linarith
  have hD0lt : D0 < leaderBuyer P k t x0 (yh x0) := by
    rw [hD0e]
    apply lt_of_lt_of_le _ hL0
    apply max_lt
    · linarith
    · have : θj * (P.Pi - P.PiExAt j) - θj * M > ε := hε2
      linarith
  have hx0K : x0 ∈ K := ⟨by linarith, hD0lt.le⟩
  have hg0 : 0 < g x0 := by
    simp only [hg, nashProduct]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨xs, hxsK, hxsmax⟩ := hKcpt.exists_isMaxOn ⟨x0, hx0K⟩ hgcont.continuousOn
  have hgxs : g x0 ≤ g xs := hxsmax hx0K
  -- (xs, yh xs) solves [RFx-k]
  have hsol : IsLeaderSolution P k true t xs (yh xs) := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [hyh]; linarith [min_le_right E (P.Pi - xs)]
    · exact min_le_left _ _
    · rw [hRS]; exact hxsK.1
    · exact hxsK.2
    · intro x y hxy
      obtain ⟨h1, h2, h3, h4⟩ := hxy
      rw [hRS] at h3 ⊢
      have hyle : y ≤ yh x := le_min h2 (by linarith)
      have hLle : leaderBuyer P k t x y ≤ leaderBuyer P k t x (yh x) := by
        rw [hLB, hLB]
        have : min (t j) (θj * (P.Pi - x - yh x)) ≤ min (t j) (θj * (P.Pi - x - y)) :=
          min_le_min_left _ (mul_le_mul_of_nonneg_left (by linarith) hθj.le)
        linarith
      have hxK : x ∈ K := ⟨h3, le_trans h4 hLle⟩
      have step1 : nashProduct (P.θ k) (x - t k) (leaderBuyer P k t x y - D0) ≤ g x := by
        simp only [hg, nashProduct]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
        exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      exact step1.trans (hxsmax hxK)
  -- the buyer's surplus at the solution is positive
  have hpos : D0 < leaderBuyer P k t xs (yh xs) := by
    rcases lt_or_eq_of_le hxsK.2 with h | h
    · exact h
    · exfalso
      have : g xs = 0 := by
        simp only [hg, nashProduct]
        rw [← h, sub_self, Real.zero_rpow (by linarith), mul_zero]
      linarith
  exact ⟨xs, yh xs, hsol, hpos⟩

lemma rfx5_gap (Pi E x : ℝ) : Pi - x - min E (Pi - x) = max (Pi - x - E) 0 := by
  rcases le_total E (Pi - x) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

lemma rfx5_LB (P : Params) (i : Fin 2) (t : Fin 2 → ℝ) (x y : ℝ) :
    leaderBuyer P i t x y = P.Pi - x - min (t (other i)) (P.θ (other i) * (P.Pi - x - y)) := rfl

/-- Any solution of [RFx-i] with the leader's offer rejected gives `π_i > θ_i (Π - Π^{-i})`. -/
lemma rfx5_false_bound (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (i : Fin 2) (π π' : ℝ) (hsol : IsLeaderSolution P i false t π π') :
    P.θ i * (P.Pi - P.PiEx i) < π := by
  have hθi := hP.θ_pos i
  have hθi1 := hP.θ_lt_one i
  have hθj := hP.θ_pos (other i)
  have hθj1 := hP.θ_lt_one (other i)
  have hsub := hP.submod
  have hc0 := hP.PiExAt_lt 0
  have hc1 := hP.PiExAt_lt 1
  have hcpos := hP.PiExAt_pos i
  have htj := ht (other i)
  have hBi : P.PiExAt i < P.PiEx i := hP.PiExAt_lt i
  -- Π - Π^{-j} < Π^{-i}
  have hsum2 : P.Pi - P.PiEx (other i) < P.PiEx i := by
    fin_cases i
    · show P.Pi - P.PiEx (other 0) < P.PiEx 0
      rw [show other 0 = 1 by decide]; linarith
    · show P.Pi - P.PiEx (other 1) < P.PiEx 1
      rw [show other 1 = 0 by decide]; linarith
  set j := other i with hj
  set θj := P.θ j
  set E := P.PiEx j with hE
  set B := P.PiEx i with hB
  set D0 := resBuyer P i false t with hD0
  have hD0e : D0 = max ((1 - θj) * B) ((1 - θj) * B + θj * P.PiExAt i - t j) := by
    rw [hD0]; simp only [resBuyer]; rfl
  have hRS : resSupplier P i false t = 0 := by simp [resSupplier]
  set yh : ℝ → ℝ := fun x => min E (P.Pi - x) with hyh
  set mm : ℝ → ℝ := fun x => min (t j) (θj * max (P.Pi - x - E) 0) with hmm
  have hLyh : ∀ x, leaderBuyer P i t x (yh x) = P.Pi - x - mm x := by
    intro x; rw [rfx5_LB]; simp only [hyh, hmm]; rw [rfx5_gap]
  have hmm_mono : ∀ x x', x ≤ x' → mm x' ≤ mm x := by
    intro x x' h
    simp only [hmm]
    exact min_le_min_left _ (mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hθj.le)
  have hLy : ∀ x y, y ≤ yh x → leaderBuyer P i t x y ≤ leaderBuyer P i t x (yh x) := by
    intro x y hy
    rw [rfx5_LB, rfx5_LB]
    have : min (t j) (θj * (P.Pi - x - yh x)) ≤ min (t j) (θj * (P.Pi - x - y)) :=
      min_le_min_left _ (mul_le_mul_of_nonneg_left (by linarith) hθj.le)
    linarith
  obtain ⟨⟨f1, f2, f3, f4⟩, hmax⟩ := hsol
  rw [hRS] at f3
  rw [← hD0] at f4
  simp only [hRS, ← hD0, sub_zero] at hmax
  have hyle : π' ≤ yh π := le_min f2 (by linarith)
  set H := leaderBuyer P i t π (yh π) - D0 with hH
  have hH0 : 0 ≤ H := by have := hLy π π' hyle; rw [hH]; linarith
  -- Claim 1: (1 - θ_i) π ≥ θ_i H
  have claim1 : P.θ i * H ≤ (1 - P.θ i) * π := by
    by_contra hcon
    push_neg at hcon
    set A := π + H with hA
    have hApos : 0 < A := by nlinarith
    set x' := P.θ i * A with hx'
    have hne : π ≠ P.θ i * A := by intro h; rw [hA] at h; nlinarith
    have hπA : π ≤ A := by linarith
    have hstrict := rfx5_strict (P.θ i) A π hθi hθi1 hApos f3 hπA hne
    have hlow : A - x' ≤ leaderBuyer P i t x' (yh x') - D0 := by
      rw [hLyh, hx']
      have h1 : leaderBuyer P i t π (yh π) = P.Pi - π - mm π := hLyh π
      have hle : π ≤ P.θ i * A := by nlinarith
      have := hmm_mono π (P.θ i * A) hle
      have hAH : A = P.Pi - mm π - D0 := by rw [hA, hH, h1]; ring
      linarith
    have hAx' : 0 < A - x' := by rw [hx']; nlinarith
    have hfeas : leaderFeasible P i false t x' (yh x') := by
      refine ⟨?_, min_le_left _ _, ?_, ?_⟩
      · simp only [hyh]; linarith [min_le_right E (P.Pi - x')]
      · rw [hRS]; exact (mul_pos hθi hApos).le
      · linarith
    have hm := hmax x' (yh x') hfeas
    have s1 : nashProduct (P.θ i) x' (A - x') ≤
        nashProduct (P.θ i) x' (leaderBuyer P i t x' (yh x') - D0) := by
      unfold nashProduct
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (mul_pos hθi hApos).le _)
      exact Real.rpow_le_rpow hAx'.le hlow (by linarith)
    have s2 : nashProduct (P.θ i) π (leaderBuyer P i t π π' - D0) ≤
        nashProduct (P.θ i) π (A - π) := by
      unfold nashProduct
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg f3 _)
      have := hLy π π' hyle
      exact Real.rpow_le_rpow (by linarith) (by rw [hA]; linarith) (by linarith)
    rw [hx'] at s1 hm
    linarith
  -- Claim 2: mm π + D0 < B
  have claim2 : mm π + D0 < B := by
    have hBpos : 0 < B := by linarith
    have hmax_lt : max (P.Pi - π - E) 0 < B := max_lt (by linarith) hBpos
    have hm1 : mm π ≤ θj * max (P.Pi - π - E) 0 := min_le_right _ _
    have hm2 : mm π ≤ t j := min_le_left _ _
    have hθB : θj * max (P.Pi - π - E) 0 < θj * B := mul_lt_mul_of_pos_left hmax_lt hθj
    have : D0 < B - mm π := by
      rw [hD0e]
      apply max_lt
      · nlinarith
      · nlinarith
    linarith
  have hHe : H = P.Pi - π - mm π - D0 := by rw [hH, hLyh]
  have : P.θ i * (P.Pi - B) < P.θ i * (π + H) := by
    apply mul_lt_mul_of_pos_left _ hθi; rw [hHe]; linarith
  nlinarith

/-- With the leader's offer accepted, if `π̃_j ≤ θ_j (Π - π̃_i - Π^{-j})^+` then every feasible
point of [RFx-i] has the follower's offer accepted. -/
lemma rfx5_true_accepts (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (i : Fin 2) (x y : ℝ) (hfeas : leaderFeasible P i true t x y)
    (hreg : t (other i) ≤ P.θ (other i) * max (P.Pi - t i - P.PiEx (other i)) 0) :
    AcceptsFollower P i t x y := by
  obtain ⟨f1, f2, f3, f4⟩ := hfeas
  simp only [resSupplier, if_true] at f3
  simp only [resBuyer, if_true, followerSplit] at f4
  have hD := le_max_left (P.Pi - t i - t (other i))
    (P.Pi - t i - P.θ (other i) * (P.Pi - t i - (P.PiExAt (other i) - t i)))
  have hθj := hP.θ_pos (other i)
  have hθj1 := hP.θ_lt_one (other i)
  have htj := ht (other i)
  unfold AcceptsFollower followerSplit
  by_contra hrej
  push_neg at hrej
  rw [rfx5_LB, min_eq_right hrej.le] at f4
  have hs0 : 0 ≤ P.θ (other i) * (P.Pi - x - y) := mul_nonneg hθj.le (by linarith)
  have htjpos : 0 < t (other i) := by linarith
  have hmaxpos : 0 < max (P.Pi - t i - P.PiEx (other i)) 0 := by
    by_contra h; push_neg at h
    have := mul_nonpos_of_nonneg_of_nonpos hθj.le h  -- wrong sign helper
    nlinarith [le_max_right (P.Pi - t i - P.PiEx (other i)) 0]
  rw [max_eq_left (by
    by_contra h; push_neg at h; rw [max_eq_right h.le] at hmaxpos; linarith)] at hreg
  nlinarith [mul_le_mul_of_nonneg_left f2 hθj.le]

theorem solution (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (i : Fin 2) (π π' : ℝ) (hopt : IsBuyerOptimal P t i true π π') :
    (AcceptsFollower P i t π π' →
      π = t i ∧ leaderBuyer P i t π π' = P.Pi - t i - t (other i)) ∧
    (¬ AcceptsFollower P i t π π' →
      followerSplit P (other i) π π' = P.θ (other i) * max (P.Pi - π - P.PiEx (other i)) 0 ∧
        leaderBuyer P i t π π' = P.Pi - π - followerSplit P (other i) π π') ∧
    (AcceptsFollower P i t π π' ↔
      t (other i) ≤ P.θ (other i) * max (P.Pi - t i - P.PiEx (other i)) 0) := by
  have hθi := hP.θ_pos i
  have hθi1 := hP.θ_lt_one i
  have hθj := hP.θ_pos (other i)
  have hθj1 := hP.θ_lt_one (other i)
  have htj := ht (other i)
  obtain ⟨⟨f1, f2, f3, f4⟩, hmax⟩ := hopt.1
  simp only [resSupplier, if_true] at f3
  have hD : P.Pi - t i - t (other i) ≤ resBuyer P i true t := by
    simp only [resBuyer, if_true]; exact le_max_left _ _
  have part1 : AcceptsFollower P i t π π' →
      π = t i ∧ leaderBuyer P i t π π' = P.Pi - t i - t (other i) := by
    intro hA
    unfold AcceptsFollower followerSplit at hA
    have hL : leaderBuyer P i t π π' = P.Pi - π - t (other i) := by
      rw [rfx5_LB, min_eq_left hA]
    have : π = t i := by linarith
    exact ⟨this, by rw [hL, this]⟩
  refine ⟨part1, ?_, ?_⟩
  · intro hrej
    unfold AcceptsFollower at hrej
    push_neg at hrej
    have hrej' : P.θ (other i) * (P.Pi - π - π') < t (other i) := hrej
    set yh := min (P.PiEx (other i)) (P.Pi - π) with hyh
    have hLrej : ∀ y, P.θ (other i) * (P.Pi - π - y) < t (other i) →
        leaderBuyer P i t π y = P.Pi - π - P.θ (other i) * (P.Pi - π - y) := by
      intro y hy; rw [rfx5_LB, min_eq_right hy.le]
    have hy : π' = yh := by
      by_contra hne
      have hlt : π' < yh := lt_of_le_of_ne (le_min f2 (by linarith)) hne
      have hLlt : leaderBuyer P i t π π' < leaderBuyer P i t π yh := by
        rw [hLrej π' hrej', rfx5_LB]
        have h1 : min (t (other i)) (P.θ (other i) * (P.Pi - π - yh)) ≤
            P.θ (other i) * (P.Pi - π - yh) := min_le_right _ _
        have h2 : P.θ (other i) * (P.Pi - π - yh) < P.θ (other i) * (P.Pi - π - π') :=
          mul_lt_mul_of_pos_left (by linarith) hθj
        linarith
      have hfeas : leaderFeasible P i true t π yh :=
        ⟨by linarith [min_le_right (P.PiEx (other i)) (P.Pi - π)], min_le_left _ _,
          by simp only [resSupplier, if_true]; exact f3, f4.trans hLlt.le⟩
      simp only [resSupplier, if_true] at hmax
      rcases eq_or_lt_of_le f3 with heq | hgt
      · have hzero : ∀ b, nashProduct (P.θ i) (π - t i) b = 0 := by
          intro b; rw [← heq, sub_self]; unfold nashProduct
          rw [Real.zero_rpow hθi.ne', zero_mul]
        have hsol' : IsLeaderSolution P i true t π yh := by
          refine ⟨hfeas, fun a b hab => ?_⟩
          simp only [resSupplier, if_true]
          rw [hzero]
          have := hmax a b hab
          rwa [hzero] at this
        have := hopt.2 i true π yh hsol'
        linarith
      · have hm := hmax π yh hfeas
        have hpos : 0 < (π - t i) ^ P.θ i := Real.rpow_pos_of_pos (by linarith) _
        have hst : (leaderBuyer P i t π π' - resBuyer P i true t) ^ (1 - P.θ i) <
            (leaderBuyer P i t π yh - resBuyer P i true t) ^ (1 - P.θ i) :=
          Real.rpow_lt_rpow (by linarith) (by linarith) (by linarith)
        unfold nashProduct at hm
        nlinarith [mul_lt_mul_of_pos_left hst hpos]
    have hfs : followerSplit P (other i) π π' =
        P.θ (other i) * max (P.Pi - π - P.PiEx (other i)) 0 := by
      unfold followerSplit; rw [hy, hyh, rfx5_gap]
    refine ⟨hfs, ?_⟩
    rw [hLrej π' hrej']; rfl
  · constructor
    · intro hA
      by_contra h
      push_neg at h
      obtain ⟨xs, ys, hsol, hlt⟩ := rfx5_better P hP t ht i h
      have hb := hopt.2 i true xs ys hsol
      have := (part1 hA).2
      linarith
    · intro hreg
      exact rfx5_true_accepts P hP t ht i π π' ⟨f1, f2, by simp only [resSupplier, if_true]; exact f3, f4⟩ hreg
