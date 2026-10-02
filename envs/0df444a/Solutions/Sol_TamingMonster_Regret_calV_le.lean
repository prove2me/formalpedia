-- Prove2me | solution 1 for TamingMonster.Regret.calV_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:54:37.963565+00:00
-- url     : https://prove2.me/submissions/1477f123-4fd9-4326-9728-01202ae9c536

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

set_option autoImplicit false

namespace TamingMonster.Regret

open MeasureTheory

lemma c128_hist_len {X : Type*} {K : ℕ} [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ t, (A.history Z U ω t).length = t := by
  intro t
  induction t with
  | zero => simp [AlgoParams.history]
  | succ n ih => simp [AlgoParams.history, ih]

lemma c128_roundRecord_ctx {X : Type*} {K : ℕ} [NeZero K] (A : AlgoParams X K)
    (h : List (Rec X K)) (t : ℕ) (z : X × (Fin K → ℝ)) (u : ℝ) :
    (A.roundRecord h t z u).1 = z.1 := rfl

lemma c128_hist_sum {X : Type*} {K : ℕ} [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (f : X → ℝ) :
    ∀ t, ((A.history Z U ω t).map (fun e => f e.ctx)).sum
      = ∑ i ∈ Finset.Icc 1 t, f (Z i ω).1 := by
  intro t
  induction t with
  | zero => simp [AlgoParams.history]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [AlgoParams.history, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [Rec.ctx, c128_roundRecord_ctx]

lemma c128_sp_ge {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (μ : ℝ)
    (hQ : ∀ π, 0 ≤ Q π) (hμ : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) :
    μ ≤ smoothProj Pi Q μ x a := by
  unfold smoothProj
  have h1 : 0 ≤ ∑ π ∈ Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π :=
    Finset.sum_nonneg (fun π _ => hQ π)
  have h2 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  nlinarith [mul_nonneg h2 h1]

lemma c128_sp_mono {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q Q' : Pi → ℝ) (μ : ℝ)
    (hQ : ∀ π, Q π ≤ Q' π) (hμ : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) :
    smoothProj Pi Q μ x a ≤ smoothProj Pi Q' μ x a := by
  unfold smoothProj
  have h2 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  have := Finset.sum_le_sum (s := Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a))
    (fun π _ => hQ π)
  nlinarith [mul_le_mul_of_nonneg_left this h2]

lemma c128_complete_ge {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (πbar : Pi)
    (hs : ∑ π, Q π ≤ 1) (π : Pi) : Q π ≤ complete Pi Q πbar π := by
  classical
  unfold complete
  split_ifs <;> linarith

lemma c128_complete_nonneg {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (πbar : Pi) (hQ : ∀ π, 0 ≤ Q π) (hs : ∑ π, Q π ≤ 1) (π : Pi) :
    0 ≤ complete Pi Q πbar π :=
  le_trans (hQ π) (c128_complete_ge Pi Q πbar hs π)

lemma c128_complete_sum {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (πbar : Pi) : ∑ π, complete Pi Q πbar π = 1 := by
  classical
  unfold complete
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma c128_Vpop_le {X : Type*} [MeasurableSpace X] {K : ℕ} (ν : Measure X)
    [IsProbabilityMeasure ν] (Pi : Finset (X → Fin K)) (P : Pi → ℝ) (π : X → Fin K) (μ : ℝ)
    (hμ : 0 < μ) (hsp : ∀ x a, μ ≤ smoothProj Pi P μ x a) :
    Vpop ν Pi P π μ ≤ 1 / μ := by
  unfold Vpop
  have h := integral_mono_of_nonneg (μ := ν)
    (f := fun x => 1 / smoothProj Pi P μ x (π x)) (g := fun _ => 1 / μ)
    (ae_of_all _ (fun x => by
      have := lt_of_lt_of_le hμ (hsp x (π x))
      show (0 : ℝ) ≤ 1 / smoothProj Pi P μ x (π x)
      positivity))
    (integrable_const _)
    (ae_of_all _ (fun x => one_div_le_one_div_of_le hμ (hsp x (π x))))
  simpa using h

/-- Main lemma, stated with namespace-local names. -/
lemma c128_main {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (hω : ω ∈ A.goodEvent D Z U)
    (π : A.Pi) (m : ℕ) :
    Vpop (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) (muM A.Pi A.δ A.τ m) ≤
      if muM A.Pi A.δ A.τ m = 1 / (2 * (K : ℝ)) then 2 * (K : ℝ)
      else theta1 * (K : ℝ)
        + estRegret A.Pi (A.history Z U ω (A.τ m)) (π : X → Fin K)
          / (theta2 * muM A.Pi A.δ A.τ m) := by
  have : IsProbabilityMeasure (D.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  set H := A.history Z U ω (A.τ m) with hH
  have hHlen : H.length = A.τ m := c128_hist_len A Z U ω _
  set μ := muM A.Pi A.δ A.τ m with hμdef
  by_cases hm0 : m = 0
  · -- epoch 0: μ = 1/(2K), Q̃ = indicator of the default policy
    have hμ : μ = 1 / (2 * (K : ℝ)) := by rw [hμdef, hm0]; simp [muM]
    rw [if_pos hμ]
    have hQ : A.Qtilde Z U ω m = complete A.Pi (fun _ => 0) (A.pick H) := by
      simp [AlgoParams.Qtilde, AlgoParams.weights, hm0, hH]
      rfl
    have hμpos : 0 < μ := by rw [hμ]; positivity
    have hKμ : (K : ℝ) * μ ≤ 1 := by
      rw [hμ]; field_simp; linarith
    have hnn : ∀ π', 0 ≤ A.Qtilde Z U ω m π' := by
      intro π'; rw [hQ]
      exact c128_complete_nonneg _ _ _ (fun _ => le_refl _) (by simp) π'
    have := c128_Vpop_le (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) μ hμpos
      (c128_sp_ge A.Pi _ μ hnn hKμ)
    calc _ ≤ 1 / μ := this
      _ = 2 * (K : ℝ) := by rw [hμ]; field_simp
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hOP : IsOPSolution A.Pi μ H (A.sel m H) := hsel m hm1 H hHlen
    obtain ⟨hQnn, hQs, -, hQv⟩ := hOP
    have hQ : A.Qtilde Z U ω m = complete A.Pi (A.sel m H) (A.pick H) := by
      simp [AlgoParams.Qtilde, AlgoParams.weights, hm0, hH]
    have hτpos : 0 < A.τ m := by
      have := hτ (Nat.pos_of_ne_zero hm0); omega
    have hτR : (0 : ℝ) < (A.τ m : ℝ) := by exact_mod_cast hτpos
    have hcard : (1 : ℝ) ≤ (A.Pi.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hPi
    have hd : 0 < dT A.Pi A.δ (A.τ m) := by
      unfold dT
      apply Real.log_pos
      rw [lt_div_iff₀ hδ0]
      have : (1 : ℝ) ≤ (A.τ m : ℝ) := by exact_mod_cast hτpos
      nlinarith [mul_le_mul this this zero_le_one (by linarith)]
    have hμeq : μ = min (1 / (2 * (K : ℝ)))
        (Real.sqrt (dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ)))) := by
      rw [hμdef]; simp [muM, hm0]
    have hμpos : 0 < μ := by
      rw [hμeq]
      exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
    have hμle : μ ≤ 1 / (2 * (K : ℝ)) := by rw [hμeq]; exact min_le_left _ _
    have hKμ : (K : ℝ) * μ ≤ 1 := by
      have : (K : ℝ) * μ ≤ (K : ℝ) * (1 / (2 * (K : ℝ))) :=
        mul_le_mul_of_nonneg_left hμle hK.le
      have e : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by field_simp
      linarith
    have hnn : ∀ π', 0 ≤ A.Qtilde Z U ω m π' := by
      intro π'; rw [hQ]
      exact c128_complete_nonneg _ _ _ hQnn hQs π'
    split_ifs with hc
    · have := c128_Vpop_le (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) μ hμpos
        (c128_sp_ge A.Pi _ μ hnn hKμ)
      calc _ ≤ 1 / μ := this
        _ = 2 * (K : ℝ) := by rw [hc]; field_simp
    · have hlt : μ < 1 / (2 * (K : ℝ)) := lt_of_le_of_ne hμle hc
      have hsq : Real.sqrt (dT A.Pi A.δ (A.τ m) / ((K : ℝ) * (A.τ m : ℝ)))
          < 1 / (2 * (K : ℝ)) := by
        rw [hμeq] at hlt
        rcases min_lt_iff.mp hlt with h | h
        · exact absurd h (lt_irrefl _)
        · exact h
      have h2 := Real.lt_sq_of_sqrt_lt hsq
      rw [div_lt_iff₀ (by positivity)] at h2
      have e : (1 / (2 * (K : ℝ))) ^ 2 * ((K : ℝ) * (A.τ m : ℝ)) * (4 * (K : ℝ))
          = (A.τ m : ℝ) := by field_simp; ring
      have h4 : 4 * (K : ℝ) * dT A.Pi A.δ (A.τ m) ≤ (A.τ m : ℝ) := by
        nlinarith [mul_lt_mul_of_pos_right h2 (by positivity : (0 : ℝ) < 4 * (K : ℝ))]
      have h13 := hω.1 (A.Qtilde Z U ω m) hnn (by rw [hQ]; exact c128_complete_sum _ _ _)
        π m hm1 h4
      -- Vhat on Q̃ ≤ empirical average on Q
      have hV : Vhat A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) μ (fun i => (Z i ω).1) (A.τ m)
          ≤ empAvg H (fun x => 1 / smoothProj A.Pi (A.sel m H) μ x ((π : X → Fin K) x)) := by
        unfold Vhat empAvg
        rw [c128_hist_sum A Z U ω (fun x => 1 / smoothProj A.Pi (A.sel m H) μ x
          ((π : X → Fin K) x)) (A.τ m), hHlen]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le
        · exact lt_of_lt_of_le hμpos (c128_sp_ge A.Pi _ μ hQnn hKμ _ _)
        · rw [hQ]
          exact c128_sp_mono A.Pi _ _ μ (c128_complete_ge A.Pi _ _ hQs) hKμ _ _
      have h3 := hQv π
      have eθ : 64 / 10 * (estRegret A.Pi H (π : X → Fin K) / (psi * μ))
          = estRegret A.Pi H (π : X → Fin K) / (theta2 * μ) := by
        unfold theta2 psi; field_simp
      have eθ1 : theta1 = 941 / 10 := rfl
      rw [eθ1]
      nlinarith [h13, hV, h3, eθ]

end TamingMonster.Regret

open MeasureTheory TamingMonster.Regret in
theorem solution {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (hω : ω ∈ A.goodEvent D Z U)
    (t : ℕ) (ht : 1 ≤ t) (π : A.Pi) (m : ℕ) (hm : m < epochOf A.τ t)
    (hmax : A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) =
      Vpop (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) (muM A.Pi A.δ A.τ m)) :
    A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) ≤
      if muM A.Pi A.δ A.τ m = 1 / (2 * (K : ℝ)) then 2 * (K : ℝ)
      else theta1 * (K : ℝ)
        + estRegret A.Pi (A.history Z U ω (A.τ m)) (π : X → Fin K)
          / (theta2 * muM A.Pi A.δ A.τ m) := by
  rw [hmax]
  exact c128_main A hPi hδ0 hδ1 hτ0 hτ hsel D Z U ω hω π m
