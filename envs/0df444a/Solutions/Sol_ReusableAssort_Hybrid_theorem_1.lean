-- Prove2me | solution 1 for ReusableAssort.Hybrid.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:16:52.748677+00:00
-- url     : https://prove2.me/submissions/015df9f2-8e15-4083-9dd7-2703bd0cb2ef

import Theorems.Thm_ReusableAssort_Hybrid_theorem_1_per_product
import Definitions.Def_ReusableAssort_Hybrid_Algorithms

open ReusableAssort.Hybrid

/-- `hfun γ ·` is nonincreasing for `γ ∈ [0,1]`. -/
private lemma hfun_anti_x {γ x x' : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hx : x ≤ x') :
    hfun γ x' ≤ hfun γ x := by
  unfold hfun
  have h2 : 0 < 2 - γ := by linarith [hγ.2]
  have h1 : 0 ≤ 1 - γ := by linarith [hγ.2]
  have : γ ^ 2 * x / (2 - γ) ≤ γ ^ 2 * x' / (2 - γ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx (sq_nonneg γ)) h2.le
  have he : Real.exp (-(γ ^ 2 * x' / (2 - γ))) ≤ Real.exp (-(γ ^ 2 * x / (2 - γ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have := mul_le_mul_of_nonneg_left (show 1 - Real.exp (-(γ ^ 2 * x / (2 - γ)))
    ≤ 1 - Real.exp (-(γ ^ 2 * x' / (2 - γ))) by linarith) h1
  linarith

private lemma hfun_nonneg {γ x : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ hfun γ x := by
  unfold hfun
  have h1 : 0 ≤ 1 - γ := by linarith [hγ.2]
  have he := Real.exp_pos (-(γ ^ 2 * x / (2 - γ)))
  have : (1 - γ) * (1 - Real.exp (-(γ ^ 2 * x / (2 - γ)))) ≤ (1 - γ) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) h1
  linarith [hγ.1]

/-- `ε*` is nonincreasing. -/
private lemma epsStar_anti {x x' : ℝ} (hx : x ≤ x') : epsStar x' ≤ epsStar x := by
  unfold epsStar
  have hbdd : ∀ y : ℝ, BddBelow ((fun γ => hfun γ y) '' Set.Icc 0 1) := by
    intro y
    refine ⟨0, ?_⟩
    rintro b ⟨γ, hγ, rfl⟩
    exact hfun_nonneg hγ
  apply le_csInf
  · exact ⟨hfun 0 x, 0, ⟨le_refl _, zero_le_one⟩, rfl⟩
  · rintro b ⟨γ, hγ, rfl⟩
    exact (csInf_le (hbdd x') ⟨γ, hγ, rfl⟩).trans (hfun_anti_x hγ hx)

private lemma expRevProd_eq_sum {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (rule : Fin n → Rule Z)
    (ret : Fin n → ℕ → ℕ) (i : Fin n) :
    expRevProd I y rule 1 ret i = ∑ t ∈ Finset.Icc 1 T, expRevAt I y rule 1 ret i t := by
  unfold expRevProd expRevAt
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun k _ => ?_
  congr 1
  omega

private lemma lpObj_eq_sum {n T : ℕ} {Z : Type} [Fintype Z]
    (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) :
    lpObj I y = ∑ i, contrib I y i := by
  unfold lpObj contrib
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma contrib_nonneg {n T : ℕ} {Z : Type} [Fintype Z]
    (I : Instance n T Z) (hI : I.Assumptions) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (hy : LPFeasible I y) (i : Fin n) : 0 ≤ contrib I y i := by
  unfold contrib
  refine Finset.sum_nonneg fun t ht => Finset.sum_nonneg fun z _ =>
    Finset.sum_nonneg fun S hS => ?_
  have := hy.1 t ht z S hS
  have := hI.F_nonneg t z
  have := hI.phi_nonneg z S hS i
  have := hI.r_nonneg z i
  positivity

theorem solution {n T : ℕ} [NeZero n] {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPOptimal I y) (hN : Normalized I y)
    (γ : ℝ) (hγ : IsGammaStar (cmin I : ℝ) γ) :
    (1 - epsStar (cmin I : ℝ)) * lpObj I y ≤ expRev I y (alg2 γ) 1 (fun _ _ => 0) := by
  have hF : LPFeasible I y := hy.1
  have hvalid : ∀ j, ((alg2 γ : Fin n → Rule Z) j).Valid := fun _ => hγ.1
  have hcoef : (1 - γ) * (1 - Real.exp (-(γ ^ 2 * (cmin I : ℝ) / (2 - γ))))
      = 1 - epsStar (cmin I : ℝ) := by
    rw [← hγ.2]; unfold hfun; ring
  have key : ∀ i, (1 - epsStar (cmin I : ℝ)) * contrib I y i
      ≤ expRevProd I y (alg2 γ) 1 (fun _ _ => 0) i := by
    intro i
    have hc0 := contrib_nonneg I hI y hF i
    have hcmin : cmin I ≤ I.c i := Finset.inf'_le _ (Finset.mem_univ i)
    have hh : hfun γ (I.c i : ℝ) ≤ hfun γ (cmin I : ℝ) :=
      hfun_anti_x hγ.1 (by exact_mod_cast hcmin)
    have hcoef' : 1 - epsStar (cmin I : ℝ)
        ≤ (1 - γ) * (1 - Real.exp (-(γ ^ 2 * (I.c i : ℝ) / (2 - γ)))) := by
      rw [← hγ.2]; unfold hfun at hh ⊢; linarith
    have hper := theorem_1_per_product I hI y hF hN (alg2 γ) hvalid i γ hγ.1 rfl
    rw [expRevProd_eq_sum]
    unfold contrib
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => le_trans ?_ (hper t ht)
    have hA : 0 ≤ ∑ z, ∑ S ∈ I.feas, I.F t z * I.r z i * I.phi z S i * y t z S := by
      refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
      have := hF.1 t ht z S hS
      have := hI.F_nonneg t z
      have := hI.phi_nonneg z S hS i
      have := hI.r_nonneg z i
      positivity
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hcoef' hA)
    congr 1
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
    ring
  rw [lpObj_eq_sum, Finset.mul_sum]
  unfold expRev
  exact Finset.sum_le_sum fun i _ => key i
