-- Prove2me | solution 1 for PersonalizedAssortment.IB.Supplement.theorem2_optimal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:19.846813+00:00
-- url     : https://prove2.me/submissions/3d315bf5-7bea-48f5-a175-eeb643098e17

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_Supplement_OnlinePolicy

open PersonalizedAssortment
open PersonalizedAssortment.IB
open PersonalizedAssortment.IB.Supplement

open PersonalizedAssortment.IB

/-- Theorem 2 (Exponential IB Achieves the Optimal Competitive Ratio), p. 1539, both sentences.
(a) For `Ψ(x) = (e/(e-1))(1 - e^{-x})`, `α_{c_min}(Ψ) → 1 - 1/e` as `c_min → ∞`; and
`α(Ψ) = min_x (1 - x)/(1 - Ψ(x) + ∫_x^1 Ψ(y) dy) = 1 - 1/e`, the minimum taken over `x ∈ [0, 1)`
(at `x = 1` the printed ratio is `0/0`).
(b) No online algorithm, deterministic or randomized, has a competitive ratio better than
`1 - 1/e`: for every `ε > 0` and every inventory level `m` there is an instance of the model
(`n ≥ 1` products, finitely many types, `r_i > 0`, `c_i ≥ max(m, 1)`, `∅ ∈ 𝒮`, Assumption 1) and a
horizon `T` such that every randomized online algorithm offering feasible assortments earns, on
some arrival sequence, at most `1 - 1/e + ε` times the objective of a feasible solution of
`Primal` with positive objective. -/
theorem solution :
    Filter.Tendsto
      (fun m : ℕ => alphaC (fun x : ℝ => Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-x))) m)
      Filter.atTop (nhds (1 - 1 / Real.exp 1)) ∧
    sInf ((fun x : ℝ => (1 - x) /
        (1 - Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-x)) +
          ∫ y in x..1, Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-y)))) '' Set.Ico 0 1) =
      1 - 1 / Real.exp 1 ∧
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      ∃ (n : ℕ) (Z : Type) (_ : Fintype Z) (r : Fin n → ℝ) (c : Fin n → ℕ)
        (𝒮 : Finset (Finset (Fin n))) (φ : Z → ChoiceModel n) (T : ℕ),
        0 < n ∧ (∀ i, 0 < r i) ∧ (∀ i, 0 < c i ∧ m ≤ c i) ∧ ∅ ∈ 𝒮 ∧ Substitutable 𝒮 φ ∧
        ∀ A : RandomizedPolicy n Z, A.IsFeasible 𝒮 →
          ∃ (z : Fin T → Z) (y : Fin T → Finset (Fin n) → ℝ),
            PrimalFeasible c 𝒮 φ z y ∧ 0 < primalObj r 𝒮 φ z y ∧
            A.revenue r c φ z ≤ (1 - 1 / Real.exp 1 + ε) * primalObj r 𝒮 φ z y := by
              have PA :
                  Filter.Tendsto
                    (fun m : ℕ => alphaC (fun x : ℝ => Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-x))) m)
                    Filter.atTop (nhds (1 - 1 / Real.exp 1)) ∧
                  sInf ((fun x : ℝ => (1 - x) /
                      (1 - Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-x)) +
                        ∫ y in x..1, Real.exp 1 / (Real.exp 1 - 1) * (1 - Real.exp (-y)))) '' Set.Ico 0 1) =
                    1 - 1 / Real.exp 1 := by
                  set E := Real.exp 1 with hEdef
                  have hE1 : 1 < E := by rw [hEdef]; have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
                  have hE0 : 0 < E := by linarith
                  have hEm : E - 1 ≠ 0 := by linarith
                  set κ := E / (E - 1) with hκdef
                  have hκ : 0 < κ := div_pos hE0 (by linarith)
                  have he1 : Real.exp (-1) = E⁻¹ := by rw [Real.exp_neg]
                  have hκe : κ * (1 - Real.exp (-1)) = 1 := by
                    rw [he1, hκdef]; field_simp
                  have hint : ∀ a b : ℝ, ∫ y in a..b, κ * (1 - Real.exp (-y)) =
                      κ * (b + Real.exp (-b)) - κ * (a + Real.exp (-a)) := by
                    intro a b
                    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
                    · intro y _
                      have h1 : HasDerivAt (fun y : ℝ => y + Real.exp (-y)) (1 + Real.exp (-y) * (-1)) y :=
                        (hasDerivAt_id y).add ((hasDerivAt_neg y).exp)
                      have h2 := h1.const_mul κ
                      have h3 : κ * (1 + Real.exp (-y) * (-1)) = κ * (1 - Real.exp (-y)) := by ring
                      rw [h3] at h2
                      exact h2
                    · apply Continuous.intervalIntegrable
                      fun_prop
                  refine ⟨?_, ?_⟩
                  · -- part a1
                    have key : ∀ m : ℕ, 1 ≤ m →
                        1 / (κ * (1 + 1 / (m : ℝ))) ≤
                          alphaC (fun x : ℝ => κ * (1 - Real.exp (-x))) m ∧
                        alphaC (fun x : ℝ => κ * (1 - Real.exp (-x))) m ≤ 1 / κ := by
                      intro m hm
                      set h : ℝ := 1 / (m : ℝ) with hhdef
                      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
                      have hh0 : 0 < h := by rw [hhdef]; positivity
                      have hh1 : h ≤ 1 := by rw [hhdef, div_le_one (by linarith)]; exact hm'
                      have bnd : ∀ x ∈ Set.Icc (0 : ℝ) (1 - h),
                          1 / (κ * (1 + h)) ≤ ratioC (fun x : ℝ => κ * (1 - Real.exp (-x))) m x ∧
                          ratioC (fun x : ℝ => κ * (1 - Real.exp (-x))) m x ≤ 1 / κ := by
                        intro x hx
                        obtain ⟨hx0, hx1⟩ := hx
                        unfold ratioC
                        rw [hint]
                        rw [← hhdef]
                        set a := Real.exp (-x) with ha
                        set b := Real.exp (-h) with hb
                        have hab : Real.exp (-(x + h)) = a * b := by
                          rw [ha, hb, ← Real.exp_add, neg_add]
                        rw [hab]
                        set e1 := Real.exp (-1) with he1def
                        have hD : h + 1 - κ * (1 - a) + (κ * (1 + e1) - κ * (x + h + a * b)) =
                            κ * (1 - x) + h - κ * h + κ * a * (1 - b) := by
                          have : κ * e1 = κ - 1 := by linarith
                          linear_combination this
                        rw [hD]
                        -- facts
                        have hb1 : 1 - h ≤ b := by
                          have := Real.add_one_le_exp (-h); rw [hb]; linarith
                        have hbpos : 0 < b := Real.exp_pos _
                        have hb_le : b ≤ 1 := by rw [hb]; apply Real.exp_le_one_iff.mpr; linarith
                        have heh : 1 + h ≤ Real.exp h := by have := Real.add_one_le_exp h; linarith
                        have hehb : Real.exp h * b = 1 := by
                          rw [hb, ← Real.exp_add]; simp
                        have ha_ge : e1 * Real.exp h ≤ a := by
                          rw [he1def, ← Real.exp_add, ha]; apply Real.exp_le_exp.mpr; linarith
                        have ha_le : a ≤ 1 := by rw [ha]; apply Real.exp_le_one_iff.mpr; linarith
                        have hapos : 0 < a := Real.exp_pos _
                        have hx1' : x ≤ Real.exp (x - 1) := by have := Real.add_one_le_exp (x - 1); linarith
                        have hax : a * Real.exp (x - 1) = e1 := by
                          rw [ha, he1def, ← Real.exp_add]; ring_nf
                        have hexle : Real.exp (x - 1) ≤ 1 := by apply Real.exp_le_one_iff.mpr; linarith
                        have he1pos : 0 < e1 := Real.exp_pos _
                        -- (i) a(1-b) ≥ e1 h
                        have hi : e1 * h ≤ a * (1 - b) := by
                          have h1 : e1 * Real.exp h * (1 - b) ≤ a * (1 - b) :=
                            mul_le_mul_of_nonneg_right ha_ge (by linarith)
                          have h2 : e1 * Real.exp h * (1 - b) = e1 * (Real.exp h - 1) := by
                            linear_combination (-e1) * hehb
                          have h3 := mul_le_mul_of_nonneg_left (show h ≤ Real.exp h - 1 by linarith) he1pos.le; linarith
                        -- (ii) a(1-b) ≤ a h, a - e1 ≤ 1 - x
                        have hii : a * (1 - b) ≤ a * h := mul_le_mul_of_nonneg_left (by linarith) hapos.le
                        have hiii : a - e1 ≤ 1 - x := by
                          have : a - e1 = a * (1 - Real.exp (x - 1)) := by rw [← hax]; ring
                          rw [this]
                          have : a * (1 - Real.exp (x - 1)) ≤ 1 * (1 - Real.exp (x - 1)) :=
                            mul_le_mul_of_nonneg_right ha_le (by linarith)
                          linarith
                        have hx1pos : 0 < 1 - x := by linarith
                        have hDlo : κ * (1 - x) ≤ κ * (1 - x) + h - κ * h + κ * a * (1 - b) := by
                          have : κ * h - h = κ * e1 * h := by linear_combination h * hκe
                          have : κ * (e1 * h) ≤ κ * (a * (1 - b)) := mul_le_mul_of_nonneg_left hi hκ.le
                          linarith
                        have hDhi : κ * (1 - x) + h - κ * h + κ * a * (1 - b) ≤ κ * (1 - x) * (1 + h) := by
                          have e2 : h - κ * h = - κ * e1 * h := by linear_combination (-h) * hκe
                          have : κ * (a * (1 - b)) ≤ κ * (a * h) := mul_le_mul_of_nonneg_left hii hκ.le
                          have : κ * h * (a - e1) ≤ κ * h * (1 - x) :=
                            mul_le_mul_of_nonneg_left hiii (by positivity)
                          linarith
                        have hDpos : 0 < κ * (1 - x) := by positivity
                        constructor
                        · rw [div_le_div_iff₀ (by positivity) (by linarith)]
                          linarith
                        · rw [div_le_div_iff₀ (by linarith) hκ]
                          linarith
                      have hne : (ratioC (fun x : ℝ => κ * (1 - Real.exp (-x))) m '' Set.Icc 0 (1 - h)).Nonempty :=
                        ⟨_, Set.mem_image_of_mem _ (show (0:ℝ) ∈ Set.Icc 0 (1 - h) from ⟨le_refl _, by linarith⟩)⟩
                      have hbdd : BddBelow (ratioC (fun x : ℝ => κ * (1 - Real.exp (-x))) m '' Set.Icc 0 (1 - h)) := by
                        refine ⟨1 / (κ * (1 + h)), ?_⟩
                        rintro _ ⟨x, hx, rfl⟩
                        exact (bnd x hx).1
                      unfold alphaC
                      rw [← hhdef]
                      constructor
                      · apply le_csInf hne
                        rintro _ ⟨x, hx, rfl⟩
                        exact (bnd x hx).1
                      · apply csInf_le_of_le hbdd (Set.mem_image_of_mem _ (show (0:ℝ) ∈ Set.Icc 0 (1 - h) from ⟨le_refl _, by linarith⟩))
                        exact (bnd 0 ⟨le_refl _, by linarith⟩).2
                    have hlim : 1 - 1 / E = 1 / κ := by rw [hκdef]; field_simp
                    rw [hlim]
                    have hL : Filter.Tendsto (fun m : ℕ => 1 / (κ * (1 + 1 / (m : ℝ)))) Filter.atTop (nhds (1 / κ)) := by
                      have : Filter.Tendsto (fun m : ℕ => 1 / (m : ℝ)) Filter.atTop (nhds 0) :=
                        tendsto_one_div_atTop_nhds_zero_nat
                      have h2 := ((this.const_add 1).const_mul κ)
                      have h3 := h2.inv₀ (by simp; exact hκ.ne')
                      simp only [add_zero, mul_one] at h3
                      simpa [one_div] using h3
                    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds
                    · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
                      exact (key m hm).1
                    · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
                      exact (key m hm).2
                  · -- part a2
                    have heq : Set.EqOn (fun x : ℝ => (1 - x) /
                        (1 - κ * (1 - Real.exp (-x)) + ∫ y in x..1, κ * (1 - Real.exp (-y))))
                        (fun _ => 1 - 1 / E) (Set.Ico 0 1) := by
                      intro x hx
                      obtain ⟨hx0, hx1⟩ := hx
                      simp only
                      rw [hint, he1]
                      have hx' : 1 - x ≠ 0 := by linarith
                      have : 1 - κ * (1 - Real.exp (-x)) + (κ * (1 + E⁻¹) - κ * (x + Real.exp (-x))) =
                          κ * (1 - x) := by
                        rw [hκdef]; field_simp; ring
                      rw [this, hκdef]
                      field_simp
                    rw [heq.image_eq, Set.Nonempty.image_const (show (Set.Ico (0:ℝ) 1).Nonempty from ⟨0, le_refl _, one_pos⟩), csInf_singleton]
              refine ⟨PA.1, PA.2, ?_⟩
              clear PA
              have PB : ∀ E : ℝ, E = Real.exp 1 → ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
                  ∃ (n : ℕ) (Z : Type) (_ : Fintype Z) (r : Fin n → ℝ) (c : Fin n → ℕ)
                    (𝒮 : Finset (Finset (Fin n))) (φ : Z → ChoiceModel n) (T : ℕ),
                    0 < n ∧ (∀ i, 0 < r i) ∧ (∀ i, 0 < c i ∧ m ≤ c i) ∧ ∅ ∈ 𝒮 ∧ Substitutable 𝒮 φ ∧
                    ∀ A : RandomizedPolicy n Z, A.IsFeasible 𝒮 →
                      ∃ (z : Fin T → Z) (y : Fin T → Finset (Fin n) → ℝ),
                        PrimalFeasible c 𝒮 φ z y ∧ 0 < primalObj r 𝒮 φ z y ∧
                        A.revenue r c φ z ≤ (1 - 1 / E + ε) * primalObj r 𝒮 φ z y := by
                intro E hEdef
                have hE1 : 1 < E := by rw [hEdef]; have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
                have hE2 : 2 < E := by rw [hEdef]; have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
                have hE0 : 0 < E := by linarith
                intro ε hε m
                obtain ⟨M, hM3, hM2⟩ : ∃ M : ℕ, 3 / ε ≤ M ∧ 2 ≤ M :=
                  ⟨⌈3/ε⌉₊ + 2, by push_cast; linarith [Nat.le_ceil (3/ε)], by omega⟩
                have hM2r : (2:ℝ) ≤ M := by exact_mod_cast hM2
                set q : ℕ := ⌊E * M⌋₊ with hq
                have hq1 : (q:ℝ) ≤ E * M := Nat.floor_le (by positivity)
                have hq2 : E * M - 1 < q := by have := Nat.lt_floor_add_one (E*M); rw [← hq] at this; linarith
                have hqM : M + 1 ≤ q := by
                  have h1 : (2*M : ℝ) < q + 1 := by have := mul_le_mul_of_nonneg_right hE2.le (show (0:ℝ) ≤ M by positivity); linarith
                  have h2 : 2*M < q + 1 := by exact_mod_cast h1
                  omega
                set N : ℕ := q - 1 with hNdef
                set k : ℕ := q - M with hkdef
                have hN1 : 1 ≤ N := by omega
                have hkN : k ≤ N := by omega
                have hNr : (N:ℝ) = q - 1 := by rw [hNdef, Nat.cast_sub (by omega)]; simp
                have hkr : (k:ℝ) = q - M := by rw [hkdef, Nat.cast_sub (by omega)]
                set C : ℕ := m + 1 with hC
                have hCr : (0:ℝ) < C := by positivity
                -- analytic part
                set S : ℝ := ∑ j ∈ Finset.range k, 1 / ((N:ℝ) - j) with hSdef
                have hSlog : ∀ k' ≤ k, Real.log (N + 1) - Real.log (N + 1 - k') ≤ ∑ j ∈ Finset.range k', 1 / ((N:ℝ) - j) := by
                  intro k' hk'
                  induction k' with
                  | zero => simp
                  | succ k' ih =>
                    rw [Finset.sum_range_succ]
                    have ih := ih (by omega)
                    have hk'r : (k':ℝ) + 1 ≤ k := by exact_mod_cast hk'
                    have ht : (2:ℝ) ≤ (N:ℝ) - k' := by rw [hNr]; rw [hkr] at hk'r; linarith
                    have hl : Real.log ((N:ℝ) + 1 - k') - Real.log ((N:ℝ) - k') ≤ 1 / ((N:ℝ) - k') := by
                      rw [← Real.log_div (by linarith) (by linarith)]
                      have := Real.log_le_sub_one_of_pos (show 0 < ((N:ℝ) + 1 - k') / ((N:ℝ) - k') by apply div_pos <;> linarith)
                      have h2 : ((N:ℝ) + 1 - k') / ((N:ℝ) - k') - 1 = 1 / ((N:ℝ) - k') := by
                        field_simp; ring
                      linarith
                    push_cast
                    have : (N:ℝ) + 1 - (k' + 1) = N - k' := by ring
                    rw [this]
                    linarith
                have hS : 1 - (E * M / q - 1) ≤ S := by
                  have h1 := hSlog k le_rfl
                  have hqpos : (0:ℝ) < q := by linarith
                  have h2 : (N:ℝ) + 1 = q := by rw [hNr]; ring
                  have h3 : (q:ℝ) - k = M := by rw [hkr]; ring
                  rw [h2, h3] at h1
                  have h4 := Real.log_le_sub_one_of_pos (show 0 < E * M / q by positivity)
                  rw [Real.log_div (by positivity) hqpos.ne', Real.log_mul hE0.ne' (by positivity), hEdef, Real.log_exp, ← hEdef] at h4
                  linarith
                have hfinal : (C:ℝ) * (N - (N - k) * S) ≤ (1 - 1 / E + ε) * (N * C) := by
                  have hqpos : (0:ℝ) < q := by linarith
                  set D := E * M / q - 1 with hD
                  have hDq : D * q = E * M - q := by rw [hD]; field_simp
                  have hD0 : 0 ≤ D := by rw [hD, sub_nonneg, le_div_iff₀ hqpos]; linarith
                  have hNk : (N:ℝ) - k = M - 1 := by rw [hNr, hkr]; ring
                  rw [hNk]
                  have hMS : (M:ℝ) - 2 ≤ (M - 1) * S := by
                    have h1 : (M - 1) * (1 - D) ≤ (M - 1) * S := mul_le_mul_of_nonneg_left hS (by linarith)
                    have h2 : (M - 1) * D ≤ 1 := by
                      have : (M - 1) * D ≤ q * D := mul_le_mul_of_nonneg_right (by linarith) hD0
                      linarith
                    linarith
                  have hkey : (1 / E - ε) * N ≤ (M:ℝ) - 2 := by
                    rcases le_or_gt (1 / E - ε) 0 with h | h
                    · have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) N); linarith
                    · have h1 : (1 / E - ε) * N ≤ (1 / E - ε) * (E * M) := mul_le_mul_of_nonneg_left (by rw [hNr]; linarith) h.le
                      have h2 : (1 / E - ε) * (E * M) = M - ε * E * M := by field_simp
                      have h3 : ε * M ≥ 3 := by rw [div_le_iff₀ hε] at hM3; linarith
                      have := mul_nonneg (show (0:ℝ) ≤ E - 1 by linarith) (show (0:ℝ) ≤ ε * M by linarith); linarith
                  have : (N:ℝ) - (M - 1) * S ≤ (1 - 1 / E + ε) * N := by linarith
                  have := mul_le_mul_of_nonneg_left this hCr.le; linarith
                clear_value S C k N q
                obtain ⟨φ, hφ⟩ : ∃ φ : Finset (Fin N) → ChoiceModel N,
                    ∀ A S i, (φ A).prob S i = if S = {i} ∧ i ∈ A then 1 else 0 := by
                  refine ⟨fun A => ⟨fun S i => if S = {i} ∧ i ∈ A then 1 else 0, ?_, ?_, ?_⟩, fun _ _ _ => rfl⟩
                  · intro S i; split_ifs <;> norm_num
                  · intro S i hi
                    rw [if_neg]
                    rintro ⟨rfl, _⟩
                    exact hi (Finset.mem_singleton_self i)
                  · intro S
                    by_cases h : ∃ j, S = {j}
                    · obtain ⟨j, rfl⟩ := h
                      rw [Finset.sum_singleton]
                      split_ifs <;> norm_num
                    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun hh => h ⟨i, hh.1⟩))]
                      exact zero_le_one
                refine ⟨N, Finset (Fin N), inferInstance, fun _ => 1, fun _ => C,
                  insert ∅ (Finset.univ.image (fun i => ({i} : Finset (Fin N)))), φ, N * C,
                  by omega, fun _ => one_pos, fun _ => ⟨show 0 < C by omega, show m ≤ C by omega⟩, Finset.mem_insert_self _ _, ?_, ?_⟩
                · intro A S _ i j hij
                  rw [hφ, hφ, if_neg]
                  · split_ifs <;> norm_num
                  · rintro ⟨h, _⟩
                    have : j ∈ ({i} : Finset (Fin N)) := h ▸ Finset.mem_insert_self j S
                    exact hij (Finset.mem_singleton.mp this).symm
                · intro A hA
                  have step : ∀ (π : OnlinePolicy N (Finset (Fin N))),
                      π.IsFeasible (insert ∅ (Finset.univ.image (fun i => ({i} : Finset (Fin N))))) →
                      ∀ (R : Finset (Fin N)) (past : List (Finset (Fin N))) (hist : List (Option (Fin N)))
                        (I : Fin N → ℕ), ∃ (e : ℝ) (hist' : List (Option (Fin N))) (I' : Fin N → ℕ),
                        (∀ fut, revAux (fun _ => (1:ℝ)) φ π past (R :: fut) hist I =
                          e + revAux (fun _ => (1:ℝ)) φ π (past ++ [R]) fut hist' I') ∧
                        0 ≤ e ∧ e ≤ 1 ∧ e + ∑ i ∈ R, (I' i : ℝ) ≤ ∑ i ∈ R, (I i : ℝ) := by
                    intro π hπ R past hist I
                    have hS := hπ (past ++ [R]) hist
                    rw [Finset.mem_insert, Finset.mem_image] at hS
                    rcases hS with h0 | ⟨i, _, hi⟩
                    · refine ⟨0, hist ++ [none], I, fun fut => ?_, le_refl _, zero_le_one, by simp⟩
                      rw [revAux, h0]; simp
                    · by_cases hiR : i ∈ R
                      · refine ⟨if 0 < I i then 1 else 0, hist ++ [some i], Function.update I i (I i - 1),
                          fun fut => ?_, by split_ifs <;> norm_num, by split_ifs <;> norm_num, ?_⟩
                        · rw [revAux, ← hi]; simp only [Finset.sum_singleton, hφ]; simp [hiR]
                        · rw [← Finset.add_sum_erase R _ hiR, ← Finset.add_sum_erase R _ hiR]
                          rw [Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])]
                          simp only [Function.update_self]
                          split_ifs with hI
                          · have : ((I i - 1 : ℕ) : ℝ) = (I i : ℝ) - 1 := by
                              rw [Nat.cast_sub (by omega)]; simp
                            rw [this]; linarith
                          · have : I i = 0 := by omega
                            simp [this]
                      · refine ⟨0, hist ++ [none], I, fun fut => ?_, le_refl _, zero_le_one, by simp⟩
                        rw [revAux, ← hi]; simp only [Finset.sum_singleton, hφ]; simp [hiR]
                  have inner : ∀ (π : OnlinePolicy N (Finset (Fin N))),
                      π.IsFeasible (insert ∅ (Finset.univ.image (fun i => ({i} : Finset (Fin N))))) →
                      ∀ (R : Finset (Fin N)) (r : ℕ) (past : List (Finset (Fin N))) (hist : List (Option (Fin N)))
                        (I : Fin N → ℕ), ∃ (e : ℝ) (hist' : List (Option (Fin N))) (I' : Fin N → ℕ),
                        (∀ fut, revAux (fun _ => (1:ℝ)) φ π past (List.replicate r R ++ fut) hist I =
                          e + revAux (fun _ => (1:ℝ)) φ π (past ++ List.replicate r R) fut hist' I') ∧
                        0 ≤ e ∧ e ≤ r ∧ e + ∑ i ∈ R, (I' i : ℝ) ≤ ∑ i ∈ R, (I i : ℝ) := by
                    intro π hπ R r
                    induction r with
                    | zero =>
                      intro past hist I
                      exact ⟨0, hist, I, fun fut => by simp, le_refl _, by simp, by simp⟩
                    | succ r ih =>
                      intro past hist I
                      obtain ⟨e1, h1, I1, hr1, he1, he1', hX1⟩ := step π hπ R past hist I
                      obtain ⟨e2, h2, I2, hr2, he2, he2', hX2⟩ := ih (past ++ [R]) h1 I1
                      refine ⟨e1 + e2, h2, I2, fun fut => ?_, by linarith, by push_cast; linarith, by linarith⟩
                      rw [List.replicate_succ, List.cons_append, hr1, hr2]
                      simp only [List.append_assoc, List.singleton_append, add_assoc]
                  have PS : ∀ (β β' Kc' : ℝ) (R : Finset (Fin N)), 0 ≤ β → β ≤ 1 → 0 ≤ β' →
                      β' * ((R.card : ℝ) - 1) ≤ β * R.card → R.Nonempty →
                      (∀ a ∈ R, ∀ (past : List (Finset (Fin N))) (hist : A.ι → List (Option (Fin N)))
                        (I : A.ι → Fin N → ℕ), ∃ fut : List (Finset (Fin N) × Fin N),
                          fut.length = (R.erase a).card * C ∧ (∀ p ∈ fut, p.2 ∈ p.1 ∧ p.1 ⊆ R.erase a) ∧
                          (∀ i, (fut.map (fun p => if p.2 = i then (1:ℝ) else 0)).sum ≤ C) ∧
                          ∑ k, A.w k * revAux (fun _ => (1:ℝ)) φ (A.pol k) past (fut.map Prod.fst) (hist k) (I k)
                            ≤ ∑ k, A.w k * (Kc' + β' * ∑ i ∈ R.erase a, (I k i : ℝ))) →
                      ∀ (past : List (Finset (Fin N))) (hist : A.ι → List (Option (Fin N)))
                        (I : A.ι → Fin N → ℕ), ∃ fut : List (Finset (Fin N) × Fin N),
                          fut.length = R.card * C ∧ (∀ p ∈ fut, p.2 ∈ p.1 ∧ p.1 ⊆ R) ∧
                          (∀ i, (fut.map (fun p => if p.2 = i then (1:ℝ) else 0)).sum ≤ C) ∧
                          ∑ k, A.w k * revAux (fun _ => (1:ℝ)) φ (A.pol k) past (fut.map Prod.fst) (hist k) (I k)
                            ≤ ∑ k, A.w k * (Kc' + C * (1 - β) + β * ∑ i ∈ R, (I k i : ℝ)) := by
                    intro β β' Kc' R hβ0 hβ1 hβ'0 hββ hRne H past hist I
                    choose e hist' I' hrev he0 heC hX using fun k => inner (A.pol k) (hA k) R C past (hist k) (I k)
                    have hd : (1:ℝ) ≤ R.card := by have := hRne.card_pos; exact_mod_cast this
                    have hsub : ∀ k, ∑ a ∈ R, ∑ i ∈ R.erase a, (I' k i : ℝ) = ((R.card : ℝ) - 1) * ∑ i ∈ R, (I' k i : ℝ) := by
                      intro k
                      rw [Finset.sum_congr rfl (fun a ha => Finset.sum_erase_eq_sub ha), Finset.sum_sub_distrib,
                        Finset.sum_const, nsmul_eq_mul]
                      ring
                    have havg : ∑ a ∈ R, ∑ k, A.w k * ∑ i ∈ R.erase a, (I' k i : ℝ) =
                        ∑ a ∈ R, (((R.card : ℝ) - 1) / R.card * ∑ k, A.w k * ∑ i ∈ R, (I' k i : ℝ)) := by
                      have h1 : ∀ k, ∑ a ∈ R, A.w k * ∑ i ∈ R.erase a, (I' k i : ℝ) =
                          ((R.card : ℝ) - 1) * (A.w k * ∑ i ∈ R, (I' k i : ℝ)) := by
                        intro k; rw [← Finset.mul_sum, hsub k]; ring
                      rw [Finset.sum_comm, Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.mul_sum,
                        Finset.sum_const, nsmul_eq_mul]
                      field_simp
                    obtain ⟨a, haR, ha⟩ := Finset.exists_le_of_sum_le hRne havg.le
                    obtain ⟨fut', hlen, hmem, hcnt, hbd⟩ := H a haR (past ++ List.replicate C R) hist' I'
                    refine ⟨List.replicate C (R, a) ++ fut', ?_, ?_, ?_, ?_⟩
                    · rw [List.length_append, List.length_replicate, hlen, Finset.card_erase_of_mem haR]
                      obtain ⟨c', hc'⟩ : ∃ c', R.card = c' + 1 := ⟨R.card - 1, by have := hRne.card_pos; omega⟩
                      rw [hc']; simp; ring
                    · intro p hp
                      rw [List.mem_append] at hp
                      rcases hp with hp | hp
                      · rw [List.eq_of_mem_replicate hp]; exact ⟨haR, subset_refl _⟩
                      · exact ⟨(hmem p hp).1, (hmem p hp).2.trans (Finset.erase_subset _ _)⟩
                    · intro i
                      rw [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
                      by_cases hia : a = i
                      · subst hia
                        have h0 : (fut'.map (fun p => if p.2 = a then (1:ℝ) else 0)).sum = 0 := by
                          apply List.sum_eq_zero
                          intro x hx
                          rw [List.mem_map] at hx
                          obtain ⟨p, hp, rfl⟩ := hx
                          have := hmem p hp
                          rw [if_neg]
                          intro h
                          rw [h] at this
                          exact (Finset.notMem_erase a R) (this.2 this.1)
                        rw [h0]; simp
                      · have := hcnt i
                        simp only [hia, if_false, mul_zero, zero_add]
                        exact this
                    · have hr : ∀ k, revAux (fun _ => (1:ℝ)) φ (A.pol k) past
                          ((List.replicate C (R, a) ++ fut').map Prod.fst) (hist k) (I k) =
                          e k + revAux (fun _ => (1:ℝ)) φ (A.pol k) (past ++ List.replicate C R)
                            (fut'.map Prod.fst) (hist' k) (I' k) := by
                        intro k; rw [List.map_append, List.map_replicate]; exact hrev k _
                      simp_rw [hr]
                      have h4 : ∀ k, A.w k * e k + β * (A.w k * ∑ i ∈ R, (I' k i : ℝ)) ≤
                          A.w k * (C * (1 - β) + β * ∑ i ∈ R, (I k i : ℝ)) := by
                        intro k
                        have hw := A.w_nonneg k
                        have h1 := mul_le_mul_of_nonneg_left (heC k) (show 0 ≤ 1 - β by linarith)
                        have h2 := mul_le_mul_of_nonneg_left (hX k) hβ0
                        have h3 : e k + β * ∑ i ∈ R, (I' k i : ℝ) ≤ C * (1 - β) + β * ∑ i ∈ R, (I k i : ℝ) := by
                          linarith
                        have h5 := mul_le_mul_of_nonneg_left h3 hw
                        linarith
                      have h4s := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h4 k)
                      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h4s
                      have hY : ∑ k, A.w k * (Kc' + β' * ∑ i ∈ R.erase a, (I' k i : ℝ)) =
                          Kc' * ∑ k, A.w k + β' * ∑ k, A.w k * ∑ i ∈ R.erase a, (I' k i : ℝ) := by
                        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                        exact Finset.sum_congr rfl (fun k _ => by ring)
                      have hG : ∑ k, A.w k * (Kc' + C * (1 - β) + β * ∑ i ∈ R, (I k i : ℝ)) =
                          Kc' * ∑ k, A.w k + ∑ k, A.w k * (C * (1 - β) + β * ∑ i ∈ R, (I k i : ℝ)) := by
                        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                        exact Finset.sum_congr rfl (fun k _ => by ring)
                      have hX'0 : 0 ≤ ∑ k, A.w k * ∑ i ∈ R, (I' k i : ℝ) :=
                        Finset.sum_nonneg (fun k _ => mul_nonneg (A.w_nonneg k)
                          (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)))
                      have hβd : β' * (((R.card : ℝ) - 1) / R.card) ≤ β := by
                        rw [mul_div_assoc', div_le_iff₀ (by linarith)]; exact hββ
                      have h5 : β' * ∑ k, A.w k * ∑ i ∈ R.erase a, (I' k i : ℝ) ≤
                          β * ∑ k, A.w k * ∑ i ∈ R, (I' k i : ℝ) := by
                        calc β' * ∑ k, A.w k * ∑ i ∈ R.erase a, (I' k i : ℝ)
                            ≤ β' * (((R.card : ℝ) - 1) / R.card * ∑ k, A.w k * ∑ i ∈ R, (I' k i : ℝ)) :=
                              mul_le_mul_of_nonneg_left ha hβ'0
                          _ = (β' * (((R.card : ℝ) - 1) / R.card)) * ∑ k, A.w k * ∑ i ∈ R, (I' k i : ℝ) := by ring
                          _ ≤ β * ∑ k, A.w k * ∑ i ∈ R, (I' k i : ℝ) := mul_le_mul_of_nonneg_right hβd hX'0
                      rw [Finset.sum_congr rfl (fun k _ => mul_add (A.w k) (e k) _), Finset.sum_add_distrib, hG]
                      rw [hY] at hbd
                      linarith
                  have G2 : ∀ d : ℕ, ∀ R : Finset (Fin N), R.card = d →
                      ∀ (past : List (Finset (Fin N))) (hist : A.ι → List (Option (Fin N)))
                        (I : A.ι → Fin N → ℕ), ∃ fut : List (Finset (Fin N) × Fin N),
                          fut.length = R.card * C ∧ (∀ p ∈ fut, p.2 ∈ p.1 ∧ p.1 ⊆ R) ∧
                          (∀ i, (fut.map (fun p => if p.2 = i then (1:ℝ) else 0)).sum ≤ C) ∧
                          ∑ k, A.w k * revAux (fun _ => (1:ℝ)) φ (A.pol k) past (fut.map Prod.fst) (hist k) (I k)
                            ≤ ∑ k, A.w k * ∑ i ∈ R, (I k i : ℝ) := by
                    intro d
                    induction d with
                    | zero =>
                      intro R hR past hist I
                      rw [Finset.card_eq_zero] at hR
                      subst hR
                      refine ⟨[], by simp, by simp, by simp, ?_⟩
                      simp [revAux]
                    | succ d ih =>
                      intro R hR past hist I
                      have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
                      obtain ⟨fut, h1, h2, h3, h4⟩ := PS 1 1 0 R zero_le_one le_rfl zero_le_one (by linarith) hRne
                        (fun a ha past hist I => by
                          obtain ⟨fut, h1, h2, h3, h4⟩ := ih (R.erase a) (by rw [Finset.card_erase_of_mem ha]; omega) past hist I
                          exact ⟨fut, h1, h2, h3, by simpa using h4⟩) past hist I
                      exact ⟨fut, h1, h2, h3, by simpa using h4⟩
                  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = N - k := ⟨_, rfl⟩
                  have hL1 : 1 ≤ L := by omega
                  have hLk : L + k = N := by omega
                  have hLr : (0:ℝ) < L := by exact_mod_cast hL1
                  have G1 : ∀ t : ℕ, t ≤ k → ∀ R : Finset (Fin N), R.card = L + t →
                      ∀ (past : List (Finset (Fin N))) (hist : A.ι → List (Option (Fin N)))
                        (I : A.ι → Fin N → ℕ), ∃ fut : List (Finset (Fin N) × Fin N),
                          fut.length = R.card * C ∧ (∀ p ∈ fut, p.2 ∈ p.1 ∧ p.1 ⊆ R) ∧
                          (∀ i, (fut.map (fun p => if p.2 = i then (1:ℝ) else 0)).sum ≤ C) ∧
                          ∑ k, A.w k * revAux (fun _ => (1:ℝ)) φ (A.pol k) past (fut.map Prod.fst) (hist k) (I k)
                            ≤ ∑ k, A.w k * ((C:ℝ) * ∑ j ∈ Finset.range t, (1 - (L:ℝ) / ((L:ℝ) + j + 1)) +
                                (L:ℝ) / ((L:ℝ) + t) * ∑ i ∈ R, (I k i : ℝ)) := by
                    intro t
                    induction t with
                    | zero =>
                      intro _ R hR past hist I
                      obtain ⟨fut, h1, h2, h3, h4⟩ := G2 _ R hR past hist I
                      refine ⟨fut, h1, h2, h3, le_of_le_of_eq h4 ?_⟩
                      apply Finset.sum_congr rfl
                      intro k _
                      have : (L:ℝ) / ((L:ℝ) + ((0:ℕ):ℝ)) = 1 := by rw [Nat.cast_zero, add_zero, div_self hLr.ne']
                      rw [this]; simp
                    | succ t ih =>
                      intro ht R hR past hist I
                      have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
                      have hLt : (0:ℝ) < (L:ℝ) + t := by positivity
                      have hcond : (L:ℝ) / ((L:ℝ) + t) * ((R.card : ℝ) - 1) ≤
                          (L:ℝ) / ((L:ℝ) + ((t+1 : ℕ) : ℝ)) * R.card := by
                        rw [hR]; push_cast
                        have e1 : (L:ℝ) / ((L:ℝ) + t) * ((L:ℝ) + ((t:ℝ) + 1) - 1) = L := by
                          rw [show (L:ℝ) + ((t:ℝ) + 1) - 1 = (L:ℝ) + t by ring]; field_simp
                        have e2 : (L:ℝ) / ((L:ℝ) + (t + 1)) * ((L:ℝ) + (t + 1)) = L := by field_simp
                        rw [e1, e2]
                      obtain ⟨fut, h1, h2, h3, h4⟩ := PS ((L:ℝ) / ((L:ℝ) + ((t+1 : ℕ) : ℝ))) ((L:ℝ) / ((L:ℝ) + t))
                        ((C:ℝ) * ∑ j ∈ Finset.range t, (1 - (L:ℝ) / ((L:ℝ) + j + 1))) R (by positivity)
                        (by rw [div_le_one (by positivity)]; push_cast; linarith) (by positivity) hcond hRne
                        (fun a ha past hist I => ih (by omega) (R.erase a)
                          (by rw [Finset.card_erase_of_mem ha]; omega) past hist I) past hist I
                      refine ⟨fut, h1, h2, h3, le_of_le_of_eq h4 ?_⟩
                      apply Finset.sum_congr rfl
                      intro k _
                      rw [Finset.sum_range_succ]
                      push_cast
                      ring
                  obtain ⟨fut, hlen, hmem, hcnt, hbd⟩ := G1 k le_rfl Finset.univ (by simp; omega) []
                    (fun _ => []) (fun _ _ => C)
                  have hlen' : fut.length = N * C := by rw [hlen]; simp
                  have hrefl : ∑ j ∈ Finset.range k, 1 / ((L:ℝ) + j + 1) = S := by
                    rw [hSdef]
                    have := Finset.sum_range_reflect (fun j : ℕ => 1 / ((L:ℝ) + j + 1)) k
                    rw [← this]
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [Finset.mem_range] at hj
                    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
                    have : (N:ℝ) = L + k := by exact_mod_cast hLk.symm
                    rw [this]; push_cast; ring_nf
                  refine ⟨fun t => (fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).1,
                    fun t S => if S = {(fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).2} then 1 else 0, ?_⟩
                  have hz : List.ofFn (fun t : Fin (N * C) => (fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).1) =
                      fut.map Prod.fst := by
                    apply List.ext_getElem <;> simp [hlen']
                  have hsumL : ∀ g : Finset (Fin N) × Fin N → ℝ,
                      ∑ t : Fin (N * C), g (fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)) = (fut.map g).sum := by
                    intro g
                    rw [← List.sum_ofFn]
                    congr 1
                    apply List.ext_getElem <;> simp [hlen']
                  have hcol : ∀ (t : Fin (N * C)) (i : Fin N),
                      ∑ S ∈ insert ∅ (Finset.univ.image (fun i => ({i} : Finset (Fin N)))),
                        (φ (fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).1).prob S i *
                          (if S = {(fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).2} then 1 else 0) =
                      if (fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).2 = i then 1 else 0 := by
                    intro t i
                    have hm := (hmem _ (List.getElem_mem (by rw [hlen']; exact t.isLt))).1
                    simp only [mul_ite, mul_one, mul_zero]
                    rw [Finset.sum_ite_eq']
                    rw [if_pos (by simp), hφ]
                    by_cases hi : (fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).2 = i
                    · rw [if_pos hi, if_pos ⟨by rw [hi], hi ▸ hm⟩]
                    · rw [if_neg hi, if_neg]
                      rintro ⟨h, _⟩
                      exact hi (Finset.singleton_inj.mp h)
                  have hobj : primalObj (fun _ => (1:ℝ)) (insert ∅ (Finset.univ.image (fun i => ({i} : Finset (Fin N)))))
                      φ (fun t => (fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).1)
                      (fun t S => if S = {(fut[(t:ℕ)]'(by rw [hlen']; exact t.isLt)).2} then 1 else 0) =
                      (N:ℝ) * C := by
                    unfold primalObj
                    simp only [one_mul]
                    rw [Finset.sum_congr rfl (fun t _ => Finset.sum_comm)]
                    rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun i _ => hcol t i))]
                    simp
                  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
                  · intro t S _
                    dsimp only
                    split_ifs <;> norm_num
                  · intro t
                    rw [Finset.sum_ite_eq']
                    simp
                  · intro i
                    rw [Finset.sum_congr rfl (fun t _ => hcol t i)]
                    rw [hsumL (fun p => if p.2 = i then (1:ℝ) else 0)]
                    exact hcnt i
                  · rw [hobj]
                    have : (0:ℝ) < N := by exact_mod_cast hN1
                    positivity
                  · rw [hobj]
                    unfold RandomizedPolicy.revenue policyRevenue
                    rw [hz]
                    refine le_trans hbd ?_
                    rw [← Finset.sum_mul, A.w_sum, one_mul]
                    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                    have hdiv : ∀ j : ℕ, (L:ℝ) / ((L:ℝ) + j + 1) = L * (1 / ((L:ℝ) + j + 1)) := by
                      intro j; ring
                    simp only [hdiv]
                    rw [← Finset.mul_sum, hrefl]
                    have hNL : (N:ℝ) = L + k := by exact_mod_cast hLk.symm
                    have hkey : (C:ℝ) * (k * 1 - L * S) + L / (L + k) * (N * C) = C * (N - (N - k) * S) := by
                      rw [hNL]; field_simp; ring
                    rw [mul_one] at hkey ⊢
                    linarith [hkey, hfinal]
              exact PB _ rfl
