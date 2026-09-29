-- Prove2me | solution 1 for RobustMDP.FiniteHorizon.robust_dynamic_programming
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T06:44:56.110252+00:00
-- url     : https://prove2.me/submissions/565802d5-8d9b-4bf1-9850-c0172fa2e7ae

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_FiniteHorizon_Model
import Definitions.Def_RobustMDP_FiniteHorizon_expectedCost
import Definitions.Def_RobustMDP_FiniteHorizon_robustValue

set_option autoImplicit false

open RobustMDP RobustMDP.FiniteHorizon in
/-- Policy evaluation under a fixed transition family `P`: the cost-to-go of `π` from time `t`. -/
noncomputable def rdpEval {n N : ℕ} {A : Type} (M : Model n N A) (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then
    fun i => M.cost ⟨t, h⟩ i (π ⟨t, h⟩ i) + ∑ j, P ⟨t, h⟩ (π ⟨t, h⟩ i) i j * rdpEval M π P (t + 1) j
  else M.terminalCost
termination_by N - t

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdpEval_lt {n N : ℕ} {A : Type} (M : Model n N A) (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (t : Fin N) (i : Fin n) :
    rdpEval M π P t i = M.cost t i (π t i) + ∑ j, P t (π t i) i j * rdpEval M π P (t + 1) j := by
  conv_lhs => rw [rdpEval]
  simp only [dif_pos t.2, Fin.eta]

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdpEval_ge_N {n N : ℕ} {A : Type} (M : Model n N A) (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (t : ℕ) (h : ¬ t < N) :
    rdpEval M π P t = M.terminalCost := by
  rw [rdpEval, dif_neg h]

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_rv_lt {n N : ℕ} {A : Type} (M : Model n N A) (t : Fin N) (i : Fin n) :
    M.robustValue t i = ⨅ a : A, (M.cost t i a +
      Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) := by
  conv_lhs => rw [Model.robustValue]
  simp only [dif_pos t.2, Fin.eta]

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_rv_ge {n N : ℕ} {A : Type} (M : Model n N A) (t : ℕ) (h : ¬ t < N) :
    M.robustValue t = M.terminalCost := by
  rw [Model.robustValue, dif_neg h]

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_pv_lt {n N : ℕ} {A : Type} (M : Model n N A) (π : ControlPolicy n N A)
    (t : Fin N) (i : Fin n) :
    M.policyValue π t i = M.cost t i (π t i) +
      Shared.supportFunction (M.rows (π t i) i) (M.policyValue π (t + 1)) := by
  conv_lhs => rw [Model.policyValue]
  simp only [dif_pos t.2, Fin.eta]

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_pv_ge {n N : ℕ} {A : Type} (M : Model n N A) (π : ControlPolicy n N A) (t : ℕ)
    (h : ¬ t < N) : M.policyValue π t = M.terminalCost := by
  rw [Model.policyValue, dif_neg h]

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_stateDist_succ {n N : ℕ} {A : Type} (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (i₀ : Fin n) (t : Fin N) (j : Fin n) :
    stateDist π P i₀ (t + 1) j = ∑ i, stateDist π P i₀ t i * P t (π t i) i j := by
  simp only [stateDist, dif_pos t.2, Fin.eta]

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_expectedCost_eq {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) (P : Fin N → A → Fin n → Fin n → ℝ) :
    M.expectedCost i₀ π P = rdpEval M π P 0 i₀ := by
  have hstep : ∀ t : Fin N, ∑ i, stateDist π P i₀ t i * M.cost t i (π t i) =
      (∑ i, stateDist π P i₀ t i * rdpEval M π P t i) -
        ∑ i, stateDist π P i₀ (t + 1) i * rdpEval M π P (t + 1) i := by
    intro t
    have e1 : ∑ i, stateDist π P i₀ t i * rdpEval M π P t i =
        ∑ i, stateDist π P i₀ t i * M.cost t i (π t i) +
          ∑ i, ∑ j, stateDist π P i₀ t i * P t (π t i) i j * rdpEval M π P (t + 1) j := by
      simp only [rdpEval_lt, mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    have e2 : ∑ i, stateDist π P i₀ (t + 1) i * rdpEval M π P (t + 1) i =
        ∑ i, ∑ j, stateDist π P i₀ t i * P t (π t i) i j * rdpEval M π P (t + 1) j := by
      simp only [rdp_stateDist_succ, Finset.sum_mul]
      exact Finset.sum_comm
    rw [e1, e2]
    ring
  have htel := Finset.sum_range_sub'
    (fun t : ℕ => ∑ i, stateDist π P i₀ t i * rdpEval M π P t i) N
  rw [← Fin.sum_univ_eq_sum_range
    (fun t : ℕ => (∑ i, stateDist π P i₀ t i * rdpEval M π P t i) -
      ∑ i, stateDist π P i₀ (t + 1) i * rdpEval M π P (t + 1) i) N] at htel
  have h0 : ∑ i, stateDist π P i₀ 0 i * rdpEval M π P 0 i = rdpEval M π P 0 i₀ := by
    simp only [stateDist, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Model.expectedCost, Finset.sum_congr rfl (fun t _ => hstep t), htel, h0,
    rdpEval_ge_N M π P N (lt_irrefl N)]
  ring

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdpEval_le_of {n N : ℕ} {A : Type} (M : Model n N A) (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (hP : ∀ t a i j, 0 ≤ P t a i j)
    (V : ℕ → Fin n → ℝ) (hVt : ∀ t, ¬ t < N → V t = M.terminalCost)
    (hV : ∀ (t : Fin N) (i : Fin n),
      M.cost t i (π t i) + ∑ j, P t (π t i) i j * V (t + 1) j ≤ V t i) :
    ∀ t i, rdpEval M π P t i ≤ V t i := by
  suffices H : ∀ k t, N - t = k → ∀ i, rdpEval M π P t i ≤ V t i by
    intro t i; exact H _ t rfl i
  intro k
  induction k with
  | zero =>
    intro t ht i
    have h : ¬ t < N := by omega
    rw [rdpEval_ge_N M π P t h, hVt t h]
  | succ k ih =>
    intro t ht i
    have h : t < N := by omega
    have e := rdpEval_lt M π P ⟨t, h⟩ i
    have hv := hV ⟨t, h⟩ i
    simp only at e hv
    rw [e]
    refine le_trans ?_ hv
    gcongr with j _
    · exact hP _ _ _ _
    · exact ih (t + 1) (by omega) j

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdpEval_ge_of {n N : ℕ} {A : Type} (M : Model n N A) (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (hP : ∀ t a i j, 0 ≤ P t a i j)
    (hP1 : ∀ t a i, ∑ j, P t a i j = 1)
    (V : ℕ → Fin n → ℝ) (hVt : ∀ t, ¬ t < N → V t = M.terminalCost) (δ : ℝ)
    (hV : ∀ (t : Fin N) (i : Fin n),
      V t i ≤ M.cost t i (π t i) + ∑ j, P t (π t i) i j * V (t + 1) j + δ) :
    ∀ t i, V t i - ((N - t : ℕ) : ℝ) * δ ≤ rdpEval M π P t i := by
  suffices H : ∀ k t, N - t = k → ∀ i, V t i - (k : ℝ) * δ ≤ rdpEval M π P t i by
    intro t i; exact H _ t rfl i
  intro k
  induction k with
  | zero =>
    intro t ht i
    have h : ¬ t < N := by omega
    rw [rdpEval_ge_N M π P t h, hVt t h]
    simp
  | succ k ih =>
    intro t ht i
    have h : t < N := by omega
    have e := rdpEval_lt M π P ⟨t, h⟩ i
    have hv := hV ⟨t, h⟩ i
    have hs := hP1 ⟨t, h⟩ (π ⟨t, h⟩ i) i
    simp only at e hv
    rw [e]
    have hsum : ∑ j, P ⟨t, h⟩ (π ⟨t, h⟩ i) i j * (V (t + 1) j - (k : ℝ) * δ) ≤
        ∑ j, P ⟨t, h⟩ (π ⟨t, h⟩ i) i j * rdpEval M π P (t + 1) j := by
      gcongr with j _
      · exact hP _ _ _ _
      · exact ih (t + 1) (by omega) j
    have hlin : ∑ j, P ⟨t, h⟩ (π ⟨t, h⟩ i) i j * (V (t + 1) j - (k : ℝ) * δ) =
        ∑ j, P ⟨t, h⟩ (π ⟨t, h⟩ i) i j * V (t + 1) j - (k : ℝ) * δ := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
    push_cast
    linarith

open RobustMDP in
theorem rdp_sf_bdd {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S ⊆ stdSimplex ℝ (Fin n))
    (v : Fin n → ℝ) : BddAbove ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' S) := by
  refine ⟨∑ j, |v j|, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hp' := hS hp
  apply Finset.sum_le_sum
  intro j _
  have h0 : 0 ≤ p j := hp'.1 j
  have h1 : p j ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => hp'.1 k) (Finset.mem_univ j)
    rw [hp'.2] at this
    exact this
  calc p j * v j ≤ p j * |v j| := mul_le_mul_of_nonneg_left (le_abs_self _) h0
    _ ≤ 1 * |v j| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |v j| := one_mul _

open RobustMDP in
theorem rdp_sf_le {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S ⊆ stdSimplex ℝ (Fin n))
    (v : Fin n → ℝ) (p : Fin n → ℝ) (hp : p ∈ S) :
    ∑ j, p j * v j ≤ Shared.supportFunction S v :=
  le_csSup (rdp_sf_bdd S hS v) ⟨p, hp, rfl⟩

open RobustMDP in
theorem rdp_sf_approx {n : ℕ} (S : Set (Fin n → ℝ)) (hne : S.Nonempty)
    (v : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p ∈ S, Shared.supportFunction S v - δ < ∑ j, p j * v j := by
  obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ :=
    exists_lt_of_lt_csSup (hne.image (fun p : Fin n → ℝ => ∑ j, p j * v j))
      (sub_lt_self (Shared.supportFunction S v) hδ)
  exact ⟨p, hp, h⟩

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_exists_nature {n N : ℕ} {A : Type} (M : Model n N A) (V : ℕ → Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : M.NaturePolicy, ∀ (t : Fin N) (a : A) (i : Fin n),
      Shared.supportFunction (M.rows a i) (V (t + 1)) ≤ ∑ j, τ.1 t a i j * V (t + 1) j + δ := by
  have h : ∀ (t : Fin N) (a : A) (i : Fin n), ∃ p ∈ M.rows a i,
      Shared.supportFunction (M.rows a i) (V (t + 1)) - δ < ∑ j, p j * V (t + 1) j :=
    fun t a i => rdp_sf_approx _ (M.rows_nonempty a i) _ δ hδ
  choose f hf1 hf2 using h
  exact ⟨⟨f, hf1⟩, fun t a i => by have := hf2 t a i; linarith⟩

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_nature_nonneg {n N : ℕ} {A : Type} (M : Model n N A) (τ : M.NaturePolicy) :
    ∀ t a i j, 0 ≤ τ.1 t a i j :=
  fun t a i j => (M.rows_subset_simplex a i (τ.2 t a i)).1 j

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_nature_sum {n N : ℕ} {A : Type} (M : Model n N A) (τ : M.NaturePolicy) :
    ∀ t a i, ∑ j, τ.1 t a i j = 1 :=
  fun t a i => (M.rows_subset_simplex a i (τ.2 t a i)).2

theorem rdp_small {N : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ((N - 0 : ℕ) : ℝ) * (ε / ((N : ℝ) + 1)) ≤ ε := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [Nat.sub_zero]
  have h1 : (N : ℝ) * (ε / ((N : ℝ) + 1)) ≤ ((N : ℝ) + 1) * (ε / ((N : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : ((N : ℝ) + 1) * (ε / ((N : ℝ) + 1)) = ε := by field_simp
  linarith

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_sup_eq {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) (V : ℕ → Fin n → ℝ) (hVt : ∀ t, ¬ t < N → V t = M.terminalCost)
    (hV : ∀ (t : Fin N) (i : Fin n),
      V t i = M.cost t i (π t i) + Shared.supportFunction (M.rows (π t i) i) (V (t + 1))) :
    (∀ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1 ≤ V 0 i₀) ∧
      (⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1) = V 0 i₀ := by
  have hup : ∀ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1 ≤ V 0 i₀ := by
    intro τ
    rw [rdp_expectedCost_eq]
    refine rdpEval_le_of M π τ.1 (rdp_nature_nonneg M τ) V hVt ?_ 0 i₀
    intro t i
    rw [hV t i]
    have := rdp_sf_le _ (M.rows_subset_simplex (π t i) i) (V (t + 1)) _ (τ.2 t (π t i) i)
    linarith
  refine ⟨hup, ?_⟩
  obtain ⟨τ0, -⟩ := rdp_exists_nature M V 1 one_pos
  have : Nonempty M.NaturePolicy := ⟨τ0⟩
  apply le_antisymm (ciSup_le hup)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε / ((N : ℝ) + 1) := by positivity
  obtain ⟨τ, hτ⟩ := rdp_exists_nature M V (ε / ((N : ℝ) + 1)) hδ
  have hlow := rdpEval_ge_of M π τ.1 (rdp_nature_nonneg M τ) (rdp_nature_sum M τ) V hVt
    (ε / ((N : ℝ) + 1)) (fun t i => by rw [hV t i]; have := hτ t (π t i) i; linarith) 0 i₀
  have hb : BddAbove (Set.range fun τ : M.NaturePolicy => M.expectedCost i₀ π τ.1) :=
    ⟨V 0 i₀, by rintro _ ⟨τ, rfl⟩; exact hup τ⟩
  have h1 := le_ciSup hb τ
  have h2 := rdp_expectedCost_eq M i₀ π τ.1
  have h3 := rdp_small (N := N) ε hε
  linarith

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_exists_argmin {n N : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n N A) :
    ∃ πs : ControlPolicy n N A, ∀ (t : Fin N) (i : Fin n) (a : A),
      M.cost t i (πs t i) + Shared.supportFunction (M.rows (πs t i) i) (M.robustValue (t + 1)) ≤
        M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1)) := by
  have h : ∀ (t : Fin N) (i : Fin n), ∃ b : A, ∀ a : A,
      M.cost t i b + Shared.supportFunction (M.rows b i) (M.robustValue (t + 1)) ≤
        M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1)) := by
    intro t i
    obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ
      (fun a => M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1)))
      Finset.univ_nonempty
    exact ⟨b, fun a => hb a (Finset.mem_univ a)⟩
  choose f hf using h
  exact ⟨f, hf⟩

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_rv_le {n N : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n N A)
    (t : Fin N) (i : Fin n) (a : A) :
    M.robustValue t i ≤
      M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1)) := by
  rw [rdp_rv_lt]
  exact ciInf_le (Finite.bddBelow_range _) a

open RobustMDP RobustMDP.FiniteHorizon in
theorem rdp_rv_eq_of {n N : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n N A)
    (πs : ControlPolicy n N A)
    (hπs : ∀ (t : Fin N) (i : Fin n) (a : A),
      M.cost t i (πs t i) + Shared.supportFunction (M.rows (πs t i) i) (M.robustValue (t + 1)) ≤
        M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1)))
    (t : Fin N) (i : Fin n) :
    M.robustValue t i =
      M.cost t i (πs t i) + Shared.supportFunction (M.rows (πs t i) i) (M.robustValue (t + 1)) :=
  le_antisymm (rdp_rv_le M t i (πs t i)) (by rw [rdp_rv_lt]; exact le_ciInf (hπs t i))

open RobustMDP RobustMDP.FiniteHorizon in
theorem solution {n N : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n N A) (i₀ : Fin n) :
    ((⨅ π : ControlPolicy n N A, ⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1) =
        M.robustValue 0 i₀ ∧
      (⨆ τ : M.NaturePolicy, ⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1) =
        M.robustValue 0 i₀) ∧
    (∀ π : ControlPolicy n N A,
      (⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1) = M.policyValue π 0 i₀) ∧
    (∀ πstar : ControlPolicy n N A,
      (∀ (t : Fin N) (i : Fin n) (a : A),
        M.cost t i (πstar t i) + Shared.supportFunction (M.rows (πstar t i) i) (M.robustValue (t + 1)) ≤
          M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
      (⨆ τ : M.NaturePolicy, M.expectedCost i₀ πstar τ.1) = M.robustValue 0 i₀) ∧
    (∀ τstar : M.NaturePolicy,
      (∀ (t : Fin N) (a : A) (i : Fin n),
        ∑ j, τstar.1 t a i j * M.robustValue (t + 1) j =
          Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
      (⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τstar.1) = M.robustValue 0 i₀ ∧
      ∀ πstar : ControlPolicy n N A,
        (∀ (t : Fin N) (i : Fin n) (a : A),
          M.cost t i (πstar t i) + Shared.supportFunction (M.rows (πstar t i) i) (M.robustValue (t + 1)) ≤
            M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
        M.expectedCost i₀ πstar τstar.1 = M.robustValue 0 i₀) := by
  have hrvT : ∀ t, ¬ t < N → M.robustValue t = M.terminalCost := rdp_rv_ge M
  obtain ⟨πs, hπs⟩ := rdp_exists_argmin M
  have h3 : ∀ π : ControlPolicy n N A,
      (∀ (t : Fin N) (i : Fin n) (a : A),
        M.cost t i (π t i) + Shared.supportFunction (M.rows (π t i) i) (M.robustValue (t + 1)) ≤
          M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
      (∀ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1 ≤ M.robustValue 0 i₀) ∧
        (⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1) = M.robustValue 0 i₀ :=
    fun π hπ => rdp_sup_eq M i₀ π M.robustValue hrvT (rdp_rv_eq_of M π hπ)
  have h2 : ∀ π : ControlPolicy n N A,
      (∀ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1 ≤ M.policyValue π 0 i₀) ∧
        (⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1) = M.policyValue π 0 i₀ :=
    fun π => rdp_sup_eq M i₀ π (M.policyValue π) (rdp_pv_ge M π) (rdp_pv_lt M π)
  have hlow : ∀ ε : ℝ, 0 < ε → ∃ τ : M.NaturePolicy, ∀ π : ControlPolicy n N A,
      M.robustValue 0 i₀ - ε ≤ M.expectedCost i₀ π τ.1 := by
    intro ε hε
    have hδ : 0 < ε / ((N : ℝ) + 1) := by positivity
    obtain ⟨τ, hτ⟩ := rdp_exists_nature M M.robustValue (ε / ((N : ℝ) + 1)) hδ
    refine ⟨τ, fun π => ?_⟩
    have hl := rdpEval_ge_of M π τ.1 (rdp_nature_nonneg M τ) (rdp_nature_sum M τ)
      M.robustValue hrvT (ε / ((N : ℝ) + 1))
      (fun t i => by
        have e1 := rdp_rv_le M t i (π t i)
        have e2 := hτ t (π t i) i
        linarith) 0 i₀
    have h3' := rdp_small (N := N) ε hε
    rw [rdp_expectedCost_eq]
    linarith
  have hlow_star : ∀ τ : M.NaturePolicy,
      (∀ (t : Fin N) (a : A) (i : Fin n),
        ∑ j, τ.1 t a i j * M.robustValue (t + 1) j =
          Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
      ∀ π : ControlPolicy n N A, M.robustValue 0 i₀ ≤ M.expectedCost i₀ π τ.1 := by
    intro τ hτ π
    have hl := rdpEval_ge_of M π τ.1 (rdp_nature_nonneg M τ) (rdp_nature_sum M τ)
      M.robustValue hrvT 0
      (fun t i => by
        have e1 := rdp_rv_le M t i (π t i)
        have e2 := hτ t (π t i) i
        linarith) 0 i₀
    rw [rdp_expectedCost_eq]
    simpa using hl
  obtain ⟨τ0, -⟩ := rdp_exists_nature M M.robustValue 1 one_pos
  have : Nonempty M.NaturePolicy := ⟨τ0⟩
  refine ⟨⟨?_, ?_⟩, fun π => (h2 π).2, fun π hπ => (h3 π hπ).2, ?_⟩
  · apply le_antisymm
    · exact (ciInf_le (Finite.bddBelow_range _) πs).trans (h3 πs hπs).2.le
    · apply le_ciInf
      intro π
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨τ, hτ⟩ := hlow ε hε
      have hb : BddAbove (Set.range fun τ : M.NaturePolicy => M.expectedCost i₀ π τ.1) :=
        ⟨M.policyValue π 0 i₀, by rintro _ ⟨τ, rfl⟩; exact (h2 π).1 τ⟩
      have h1 := le_ciSup hb τ
      have h4 := hτ π
      linarith
  · have hup : ∀ τ : M.NaturePolicy,
        (⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1) ≤ M.robustValue 0 i₀ :=
      fun τ => (ciInf_le (Finite.bddBelow_range _) πs).trans ((h3 πs hπs).1 τ)
    apply le_antisymm (ciSup_le hup)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨τ, hτ⟩ := hlow ε hε
    have h1 : M.robustValue 0 i₀ - ε ≤ ⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1 :=
      le_ciInf hτ
    have hb : BddAbove (Set.range fun τ : M.NaturePolicy =>
        ⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1) :=
      ⟨M.robustValue 0 i₀, by rintro _ ⟨τ, rfl⟩; exact hup τ⟩
    have h4 := le_ciSup hb τ
    linarith
  · intro τs hτs
    refine ⟨le_antisymm ((ciInf_le (Finite.bddBelow_range _) πs).trans ((h3 πs hπs).1 τs))
      (le_ciInf (hlow_star τs hτs)), fun π hπ => le_antisymm ((h3 π hπ).1 τs) (hlow_star τs hτs π)⟩
