-- Prove2me | solution 1 for StrategicRFx.Benefit.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:07:56.991379+00:00
-- url     : https://prove2.me/submissions/c0e6f888-10d4-48a8-ba85-e76ba30e0902

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

lemma rfx5_other_other (i : Fin 2) : other (other i) = i := by
  fin_cases i <;> decide

lemma rfx5_sum (P : Params) (t : Fin 2 → ℝ) (k : Fin 2) :
    P.Pi - t k - t (other k) = P.Pi - t 0 - t 1 := by
  fin_cases k
  · rfl
  · show P.Pi - t 1 - t (other 1) = _
    rw [show other 1 = 0 by decide]; ring

lemma rfx5_not_accepts (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (k : Fin 2)
    (hv : P.θ (other k) * max (P.Pi - t k - P.PiEx (other k)) 0 < t (other k)) :
    ¬ AcceptsBoth P t := by
  intro hacc
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
  have hbound := hacc k true xs (yh xs) hsol
  rw [← rfx5_sum P t k] at hbound
  -- the buyer's surplus at the solution is positive
  have hpos : D0 < leaderBuyer P k t xs (yh xs) := by
    rcases lt_or_eq_of_le hxsK.2 with h | h
    · exact h
    · exfalso
      have : g xs = 0 := by
        simp only [hg, nashProduct]
        rw [← h, sub_self, Real.zero_rpow (by linarith), mul_zero]
      linarith
  have : P.Pi - t k - t j ≤ D0 := by rw [hD0e]; exact le_max_left _ _
  linarith

theorem solution (P : Params) (hP : Standing P) (πF : Fin 2 → ℝ)
    (hF : ∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0)
    (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i) (hacc : AcceptsBoth P t) :
    P.Pi - πF 0 - πF 1 ≤ P.Pi - t 0 - t 1 ∧
      ∀ π πex : Fin 2 → ℝ, IsSimuEquilibrium P π πex → P.Pi - π 0 - π 1 ≤ P.Pi - t 0 - t 1 := by
  have o0 : other 0 = 1 := by decide
  have o1 : other 1 = 0 := by decide
  have hQ : ∀ i, t i ≤ P.θ i * max (P.Pi - t (other i) - P.PiEx i) 0 := by
    intro i
    by_contra h
    push_neg at h
    apply rfx5_not_accepts P hP t ht (other i) _ hacc
    rw [rfx5_other_other]
    exact h
  have hF0 := hF 0
  have hF1 := hF 1
  rw [o0, show P.Pi - πF 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - πF 1 by ring] at hF0
  rw [o1, show P.Pi - πF 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - πF 0 by ring] at hF1
  have ha0 : 0 < P.Pi - P.PiEx 0 := by linarith [hP.PiEx_lt 0]
  have ha1 : 0 < P.Pi - P.PiEx 1 := by linarith [hP.PiEx_lt 1]
  have hq0 := hQ 0
  have hq1 := hQ 1
  rw [o0, show P.Pi - t 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - t 1 by ring] at hq0
  rw [o1, show P.Pi - t 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - t 0 by ring] at hq1
  have h1 := rfx5_Qbound (P.θ 0) (P.θ 1) _ _ (t 0) (t 1) (πF 0) (πF 1) (hP.θ_pos 0)
    (hP.θ_lt_one 0) (hP.θ_pos 1) (hP.θ_lt_one 1) ha0 ha1 hF0 hF1 (ht 0) (ht 1) hq0 hq1
  refine ⟨by linarith, fun π πex he => ?_⟩
  -- each equilibrium profit is at least θ_i (Π - π_j - Π^{-i})^+
  have hS : ∀ i, 0 ≤ π i ∧ P.θ i * max (P.Pi - π (other i) - P.PiEx i) 0 ≤ π i := by
    intro i
    obtain ⟨⟨hx0, hxA⟩, hmax⟩ := he.2 i
    set A := P.Pi - π (other i) - (P.PiEx i - πex (other i)) with hA
    have key : P.θ i * A ≤ π i := by
      apply rfx5_follower (P.θ i) A (π i) (hP.θ_pos i) (hP.θ_lt_one i) hx0 (by linarith)
      intro y hy0 hyA
      have e : ∀ z, P.Pi - π (other i) - z - (P.PiEx i - πex (other i)) = A - z := fun z => by
        rw [hA]; ring
      have := hmax y ⟨hy0, by linarith⟩
      rw [e, e] at this
      exact this
    refine ⟨hx0, ?_⟩
    have hex := he.1 (other i)
    have hA0 : 0 ≤ A := by linarith
    have : max (P.Pi - π (other i) - P.PiEx i) 0 ≤ A := max_le (by linarith) hA0
    exact (mul_le_mul_of_nonneg_left this (hP.θ_pos i).le).trans key
  obtain ⟨hy0, hs0⟩ := hS 0
  obtain ⟨hy1, hs1⟩ := hS 1
  rw [o0, show P.Pi - π 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - π 1 by ring] at hs0
  rw [o1, show P.Pi - π 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - π 0 by ring] at hs1
  have h2 := rfx5_Sbound (P.θ 0) (P.θ 1) _ _ (π 0) (π 1) (πF 0) (πF 1) (hP.θ_pos 0)
    (hP.θ_lt_one 0) (hP.θ_pos 1) (hP.θ_lt_one 1) ha0 ha1 hF0 hF1 hy0 hy1 hs0 hs1
  linarith
