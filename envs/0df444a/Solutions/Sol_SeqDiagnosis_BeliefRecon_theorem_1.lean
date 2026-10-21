-- Prove2me | solution 1 for SeqDiagnosis.BeliefRecon.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:01:08.325451+00:00
-- url     : https://prove2.me/submissions/3601f823-d85b-489c-b3d0-85cff5f82aea

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model
import Theorems.Thm_SeqDiagnosis_BeliefRecon_belief_eq_batch
import Theorems.Thm_SeqDiagnosis_BeliefRecon_etm_list_prod
import Theorems.Thm_SeqDiagnosis_BeliefRecon_row_RP_eq_beta
import Theorems.Thm_SeqDiagnosis_BeliefRecon_tcal_zero

open Matrix SeqDiagnosis.BeliefRecon

theorem solution {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (hRP : M.Bmat = R * P) (hR : R.rank = r) (hP : P.rank = r)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1))) :
    M.Bmat.rank = r ∧
    (∀ ys : List Y, ys ≠ [] → belief M.f θ ys = Tcal M R P ys.length (diagStat M P ys) θ) ∧
    (∀ t : ℕ, 1 ≤ t → reachable M.f θ t = beliefManifold M R P θ t) ∧
    ((∀ i, 0 < θ i) → ∀ t : ℕ, 1 ≤ t →
      Function.Injective (fun x : Fin r → ℝ => Tcal M R P t x θ)) := by
  -- R has trivial kernel
  have hinj : Function.Injective R.mulVecLin := by
    have h := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
    have h' : Module.finrank ℝ (LinearMap.range R.mulVecLin) = r := hR
    rw [h', Module.finrank_fin_fun] at h
    have h0 : Module.finrank ℝ (LinearMap.ker R.mulVecLin) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.mp h0
  -- Part 1: rank
  have hrank : M.Bmat.rank = r := by
    rw [hRP]
    unfold Matrix.rank
    rw [mulVecLin_mul, LinearMap.range_comp,
      ← (Submodule.equivMapOfInjective R.mulVecLin hinj _).finrank_eq]
    exact hP
  -- positivity of the likelihoods
  have hf : ∀ i y, 0 < M.f i y := by
    intro i y
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hS.2.1 y
    · rw [hETM j y]; exact mul_pos (hS.2.1 y) (Real.exp_pos _)
  -- Part 2: reconstruction
  have hrecon : ∀ ys : List Y, ys ≠ [] →
      belief M.f θ ys = Tcal M R P ys.length (diagStat M P ys) θ := by
    intro ys hys
    set x := diagStat M P ys with hx
    set e : Fin N → ℝ := fun i =>
      Real.exp ((ys.length : ℝ) * (betaZero M R P i + (R *ᵥ x) i)) with he
    set F0 := (ys.map (M.f 0)).prod with hF0
    have hF0pos : 0 < F0 := by
      rw [hF0]
      apply List.prod_pos
      intro a ha
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp ha
      exact hS.2.1 y
    have hF : ∀ j : Fin N, (ys.map (M.f j.succ)).prod = F0 * e j := by
      intro j
      rw [etm_list_prod M hS hETM j ys, he]
      simp only
      rw [((row_RP_eq_beta M hS hETM R P hRP j).2.2 ys hys)]
    have hden : ∑ i, θ i * (ys.map (M.f i)).prod = F0 * (θ 0 + ∑ i, θ i.succ * e i) := by
      rw [Fin.sum_univ_succ, mul_add, Finset.mul_sum]
      simp only [hF]
      congr 1
      · ring
      · exact Finset.sum_congr rfl (fun i _ => by ring)
    obtain ⟨hT0, _⟩ := tcal_zero M hS hETM R P θ hθ ys.length x
    funext k
    rw [belief_eq_batch M.f hf θ hθ ys k, hden]
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [hT0]
      simp only [he]
      rw [← hF0, mul_comm (θ 0) F0, mul_div_mul_left _ _ hF0pos.ne']
    · simp only [Tcal, Fin.cases_succ]
      rw [hF j]
      have : θ j.succ * (F0 * e j) = F0 * (θ j.succ * e j) := by ring
      rw [this, mul_div_mul_left _ _ hF0pos.ne']
  refine ⟨hrank, hrecon, ?_, ?_⟩
  -- Part 3: reachable set
  · intro t ht
    ext q
    constructor
    · rintro ⟨ys, hlen, rfl⟩
      have hys : ys ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      refine ⟨diagStat M P ys, ⟨ys, hlen, rfl⟩, ?_⟩
      simp only
      rw [hrecon ys hys, hlen]
    · rintro ⟨x, ⟨ys, hlen, rfl⟩, rfl⟩
      have hys : ys ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      refine ⟨ys, hlen, ?_⟩
      rw [hrecon ys hys, hlen]
  -- Part 4: injectivity
  · intro hθpos t ht x x' hxx
    simp only at hxx
    set w : (Fin r → ℝ) → Fin N → ℝ := fun z i =>
      θ i.succ * Real.exp ((t : ℝ) * (betaZero M R P i + (R *ᵥ z) i)) with hw
    have hD : ∀ z, 0 < θ 0 + ∑ i, w z i := fun z =>
      add_pos_of_pos_of_nonneg (hθpos 0)
        (Finset.sum_nonneg (fun i _ => mul_nonneg (hθpos _).le (Real.exp_pos _).le))
    have h0 := congrFun hxx 0
    rw [(tcal_zero M hS hETM R P θ hθ t x).1, (tcal_zero M hS hETM R P θ hθ t x').1] at h0
    rw [div_eq_div_iff (hD x).ne' (hD x').ne'] at h0
    have hDeq : θ 0 + ∑ i, w x' i = θ 0 + ∑ i, w x i := mul_left_cancel₀ (hθpos 0).ne' h0
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    apply hinj
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    funext j
    have hj : w x j / (θ 0 + ∑ i, w x i) = w x' j / (θ 0 + ∑ i, w x' i) := by
      have := congrFun hxx j.succ
      simp only [Tcal, Fin.cases_succ] at this
      exact this
    rw [hDeq, div_left_inj' (hD x).ne'] at hj
    simp only [hw] at hj
    have h1 := Real.exp_injective (mul_left_cancel₀ (hθpos j.succ).ne' hj)
    exact add_left_cancel (mul_left_cancel₀ htR h1)
