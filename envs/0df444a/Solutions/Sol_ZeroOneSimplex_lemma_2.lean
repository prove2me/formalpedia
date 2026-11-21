-- Prove2me | solution 1 for ZeroOneSimplex.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:22:13.566179+00:00
-- url     : https://prove2.me/submissions/4427f7b5-accf-49d2-843e-f8b7c0bbede7

import Mathlib
import Definitions.Def_ZeroOneSimplex_IsCoherentPath
set_option autoImplicit false

open Matrix

namespace Aux_ZeroOneSimplex_lemma_2

open ZeroOneSimplex

lemma path_mem {n : ℕ} (Q : Set (Fin n → ℝ)) (v : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (k : ℕ)
    (hP : IsMonotonePath Q v x k) : ∀ j, j ≤ k → x j ∈ Q := by
  obtain ⟨hx0, hmono⟩ := hP
  intro j
  induction j with
  | zero => intro _; exact hx0.1
  | succ j ih =>
    intro hj
    have hE : IsEdge Q (x j) (x (j + 1)) := (hmono j (by omega)).1
    exact hE.2.1 (right_mem_segment ℝ (x j) (x (j + 1)))

lemma path_vmono {n : ℕ} (Q : Set (Fin n → ℝ)) (v : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (k : ℕ)
    (hP : IsMonotonePath Q v x k) (j1 : ℕ) : ∀ j2, j1 ≤ j2 → j2 ≤ k → v ⬝ᵥ x j1 ≤ v ⬝ᵥ x j2 := by
  obtain ⟨_, hmono⟩ := hP
  intro j2
  induction j2 with
  | zero =>
    intro h _
    have h0 : j1 = 0 := by omega
    rw [h0]
  | succ j ih =>
    intro h hk
    by_cases hj : j1 = j + 1
    · rw [hj]
    · have h1 : v ⬝ᵥ x j1 ≤ v ⬝ᵥ x j := ih (by omega) (by omega)
      have h2 : v ⬝ᵥ x j < v ⬝ᵥ x (j + 1) := (hmono j (by omega)).2
      linarith

end Aux_ZeroOneSimplex_lemma_2

open Aux_ZeroOneSimplex_lemma_2 in
open ZeroOneSimplex in
theorem solution {n : ℕ} (Q : Set (Fin n → ℝ)) (hQ : IsPolytope Q) (c v : Fin n → ℝ)
    (hv : v ≠ 0) (x : ℕ → Fin n → ℝ) (k : ℕ) (hΓ : IsCoherentPath Q c v x k) :
    ∃ i ≤ k, IsMaximizer Q c (x i) ∧
      ∀ j < i, c ⬝ᵥ x j < c ⬝ᵥ x (j + 1) ∧ v ⬝ᵥ x j < v ⬝ᵥ x (j + 1) := by
  obtain ⟨hP, hup, hvis⟩ := hΓ
  have hpathQ := path_mem Q v x k hP
  have hvmono := path_vmono Q v x k hP
  have hmono : ∀ i < k, IsEdge Q (x i) (x (i + 1)) ∧ v ⬝ᵥ x i < v ⬝ᵥ x (i + 1) := hP.2
  obtain ⟨F, hF⟩ := hQ
  have hQc : IsCompact Q := by
    rw [hF]
    exact Set.Finite.isCompact_convexHull ℝ F.finite_toSet
  have hQconv : Convex ℝ Q := by
    rw [hF]
    exact convex_convexHull ℝ _
  have hcont : ∀ w : Fin n → ℝ, Continuous (fun y : Fin n → ℝ => w ⬝ᵥ y) := fun w =>
    continuous_const.dotProduct continuous_id
  have hx0Q : x 0 ∈ Q := hpathQ 0 (Nat.zero_le k)
  obtain ⟨xM, hxMQ, hxMmax⟩ := hQc.exists_isMaxOn ⟨x 0, hx0Q⟩ (hcont c).continuousOn
  have hcmax : ∀ y ∈ Q, c ⬝ᵥ y ≤ c ⬝ᵥ xM := isMaxOn_iff.mp hxMmax
  have hQmc : IsCompact (Q ∩ {y | c ⬝ᵥ y = c ⬝ᵥ xM}) :=
    hQc.inter_right (isClosed_eq (hcont c) continuous_const)
  obtain ⟨xm, hxm, hxmmin⟩ := hQmc.exists_isMinOn ⟨xM, hxMQ, rfl⟩ (hcont v).continuousOn
  have hvmin : ∀ y ∈ Q ∩ {y | c ⬝ᵥ y = c ⬝ᵥ xM}, v ⬝ᵥ xm ≤ v ⬝ᵥ y := isMinOn_iff.mp hxmmin
  have hxmQ : xm ∈ Q := hxm.1
  have hxmc : c ⬝ᵥ xm = c ⬝ᵥ xM := hxm.2
  have hm_up : shadowMap c v xm ∈ upperBoundary (shadowMap c v '' Q) := by
    refine ⟨⟨xm, hxmQ, rfl⟩, ?_⟩
    intro q' hq' _
    obtain ⟨y, hy, rfl⟩ := hq'
    show c ⬝ᵥ y ≤ c ⬝ᵥ xm
    rw [hxmc]
    exact hcmax y hy
  have hm_ext : shadowMap c v xm ∈ Set.extremePoints ℝ (shadowMap c v '' Q) := by
    refine ⟨⟨xm, hxmQ, rfl⟩, ?_⟩
    intro p1 hp1 p2 hp2 hseg
    obtain ⟨y1, hy1, rfl⟩ := hp1
    obtain ⟨y2, hy2, rfl⟩ := hp2
    obtain ⟨a, b, ha, hb, hab, hab'⟩ := hseg
    have e1 := congrArg Prod.fst hab'
    have e2 := congrArg Prod.snd hab'
    simp only [shadowMap, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at e1 e2
    have hc1 : c ⬝ᵥ y1 ≤ c ⬝ᵥ xm := by rw [hxmc]; exact hcmax y1 hy1
    have hc2 : c ⬝ᵥ y2 ≤ c ⬝ᵥ xm := by rw [hxmc]; exact hcmax y2 hy2
    have hsum : a * c ⬝ᵥ xm + b * c ⬝ᵥ xm = c ⬝ᵥ xm := by
      rw [← add_mul, hab, one_mul]
    have hc1e : c ⬝ᵥ y1 = c ⬝ᵥ xm := by
      by_contra hne
      have hlt : c ⬝ᵥ y1 < c ⬝ᵥ xm := lt_of_le_of_ne hc1 hne
      have p1 : a * c ⬝ᵥ y1 < a * c ⬝ᵥ xm := mul_lt_mul_of_pos_left hlt ha
      have p2 : b * c ⬝ᵥ y2 ≤ b * c ⬝ᵥ xm := mul_le_mul_of_nonneg_left hc2 hb.le
      linarith
    have hc2e : c ⬝ᵥ y2 = c ⬝ᵥ xm := by
      by_contra hne
      have hlt : c ⬝ᵥ y2 < c ⬝ᵥ xm := lt_of_le_of_ne hc2 hne
      have p1 : a * c ⬝ᵥ y1 ≤ a * c ⬝ᵥ xm := mul_le_mul_of_nonneg_left hc1 ha.le
      have p2 : b * c ⬝ᵥ y2 < b * c ⬝ᵥ xm := mul_lt_mul_of_pos_left hlt hb
      linarith
    have hv1 : v ⬝ᵥ xm ≤ v ⬝ᵥ y1 := hvmin y1 ⟨hy1, hc1e.trans hxmc⟩
    have hv2 : v ⬝ᵥ xm ≤ v ⬝ᵥ y2 := hvmin y2 ⟨hy2, hc2e.trans hxmc⟩
    have hvsum : a * v ⬝ᵥ xm + b * v ⬝ᵥ xm = v ⬝ᵥ xm := by
      rw [← add_mul, hab, one_mul]
    have hv1e : v ⬝ᵥ y1 = v ⬝ᵥ xm := by
      by_contra hne
      have hlt : v ⬝ᵥ xm < v ⬝ᵥ y1 := lt_of_le_of_ne hv1 (Ne.symm hne)
      have p1 : a * v ⬝ᵥ xm < a * v ⬝ᵥ y1 := mul_lt_mul_of_pos_left hlt ha
      have p2 : b * v ⬝ᵥ xm ≤ b * v ⬝ᵥ y2 := mul_le_mul_of_nonneg_left hv2 hb.le
      linarith
    exact Prod.ext hv1e hc1e
  obtain ⟨i, hik, hxi⟩ := hvis _ hm_ext hm_up
  have hvi : v ⬝ᵥ x i = v ⬝ᵥ xm := congrArg Prod.fst hxi
  have hci : c ⬝ᵥ x i = c ⬝ᵥ xm := congrArg Prod.snd hxi
  have hmax : IsMaximizer Q c (x i) := by
    unfold IsMaximizer
    refine ⟨hpathQ i hik, ?_⟩
    intro y hy
    rw [hci, hxmc]
    exact hcmax y hy
  refine ⟨i, hik, hmax, ?_⟩
  intro j hj
  have hjk : j < k := by omega
  have hvj : v ⬝ᵥ x j < v ⬝ᵥ x (j + 1) := (hmono j hjk).2
  refine ⟨?_, hvj⟩
  have hvle : v ⬝ᵥ x (j + 1) ≤ v ⬝ᵥ x i := hvmono (j + 1) i (by omega) hik
  have hxjQ : x j ∈ Q := hpathQ j (by omega)
  have hcj_lt : c ⬝ᵥ x j < c ⬝ᵥ xm := by
    by_contra hcon
    push_neg at hcon
    have hle : c ⬝ᵥ x j ≤ c ⬝ᵥ xm := by rw [hxmc]; exact hcmax (x j) hxjQ
    have heq : c ⬝ᵥ x j = c ⬝ᵥ xM := (le_antisymm hle hcon).trans hxmc
    have := hvmin (x j) ⟨hxjQ, heq⟩
    linarith
  have hupj1 := hup (j + 1) (by omega)
  by_cases heq : v ⬝ᵥ x (j + 1) = v ⬝ᵥ xm
  · have h' : c ⬝ᵥ xm ≤ c ⬝ᵥ x (j + 1) :=
      hupj1.2 (shadowMap c v xm) ⟨xm, hxmQ, rfl⟩ heq.symm
    linarith
  · have hlt : v ⬝ᵥ x (j + 1) < v ⬝ᵥ xm := lt_of_le_of_ne (hvle.trans_eq hvi) heq
    have hd : 0 < v ⬝ᵥ xm - v ⬝ᵥ x j := by linarith
    have hdne : v ⬝ᵥ xm - v ⬝ᵥ x j ≠ 0 := hd.ne'
    obtain ⟨μ, hμ⟩ : ∃ μ : ℝ,
        μ = (v ⬝ᵥ x (j + 1) - v ⬝ᵥ x j) / (v ⬝ᵥ xm - v ⬝ᵥ x j) := ⟨_, rfl⟩
    have hμ0 : 0 < μ := by
      rw [hμ]
      exact div_pos (by linarith) hd
    have hμ1 : μ < 1 := by
      rw [hμ, div_lt_one hd]
      linarith
    have hzQ : (1 - μ) • x j + μ • xm ∈ Q :=
      hQconv hxjQ hxmQ (by linarith) hμ0.le (by ring)
    have hμm : μ * (v ⬝ᵥ xm - v ⬝ᵥ x j) = v ⬝ᵥ x (j + 1) - v ⬝ᵥ x j := by
      rw [hμ]
      exact div_mul_cancel₀ _ hdne
    have hvz : v ⬝ᵥ ((1 - μ) • x j + μ • xm) = v ⬝ᵥ x (j + 1) := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith
    have hcz : c ⬝ᵥ ((1 - μ) • x j + μ • xm) = (1 - μ) * c ⬝ᵥ x j + μ * c ⬝ᵥ xm := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hup' : c ⬝ᵥ ((1 - μ) • x j + μ • xm) ≤ c ⬝ᵥ x (j + 1) :=
      hupj1.2 (shadowMap c v ((1 - μ) • x j + μ • xm)) ⟨_, hzQ, rfl⟩ hvz
    have hprod : μ * c ⬝ᵥ x j < μ * c ⬝ᵥ xm := mul_lt_mul_of_pos_left hcj_lt hμ0
    linarith
