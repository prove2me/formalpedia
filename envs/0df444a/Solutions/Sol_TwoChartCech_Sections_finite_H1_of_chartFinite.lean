-- Prove2me | solution 1 for TwoChartCech.Sections.finite_H1_of_chartFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a325d3e4-2639-5e85-a4a6-d99c59224131

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_Sections_finite_H1_of_chartFinite

set_option autoImplicit false

universe u

open Polynomial

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply"
namespace ChartFinite
p2m_open "TwoChartCech"

variable {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, u} R} (S : TwoChartCech.Sections.{u, u, u} 𝒰)

theorem vpow_mul_upow (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1) (n j : ℕ) :
    𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ j = if j ≤ n then 𝒰.ρ1 g ^ (n - j) else 𝒰.ρ0 f ^ (j - n) := by
  have hvu : 𝒰.ρ1 g * 𝒰.ρ0 f = 1 := by rw [mul_comm]; exact hfg
  induction n generalizing j with
  | zero => cases j <;> simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      have : 𝒰.ρ1 g ^ (n + 1) * 𝒰.ρ0 f ^ (j + 1) = 𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ j := by
        rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc (𝒰.ρ1 g) (𝒰.ρ0 f), hvu, one_mul]
      rw [this, ih j]
      simp only [Nat.succ_le_succ_iff, Nat.succ_sub_succ]

noncomputable def T (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) : Finset S.M01 := by
  classical exact (s ×ˢ Finset.range N).image fun ek => 𝒰.ρ1 g ^ ek.2 • S.r0 ek.1

noncomputable def W (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) : Submodule R S.M01 :=
  Submodule.span R (T S g s N : Set S.M01) ⊔ LinearMap.range S.cechDiff

theorem range_r0_le (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) : LinearMap.range S.r0 ≤ W S g s N := by
  rintro _ ⟨x, rfl⟩
  apply Submodule.mem_sup_right
  refine ⟨((-x : S.M0), (0 : S.M1)), ?_⟩
  rw [TwoChartCech.Sections.cechDiff_apply, map_zero, map_neg, zero_sub, neg_neg]

theorem range_r1_le (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) : LinearMap.range S.r1 ≤ W S g s N := by
  rintro _ ⟨y, rfl⟩
  apply Submodule.mem_sup_right
  refine ⟨((0 : S.M0), y), ?_⟩
  rw [TwoChartCech.Sections.cechDiff_apply, map_zero, sub_zero]

theorem vpow_smul_mem_range_r1 (g : 𝒰.A1) {m : S.M01} {n : ℕ} (h : 𝒰.ρ1 g ^ n • m ∈ LinearMap.range S.r1)
    (k : ℕ) (hk : n ≤ k) : 𝒰.ρ1 g ^ k • m ∈ LinearMap.range S.r1 := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨g ^ d • y, ?_⟩
  rw [S.r1_smul, map_pow, hy, ← mul_smul, ← pow_add, add_comm]

theorem upow_smul_r0_mem (f : 𝒰.A0) (x : S.M0) (i : ℕ) : 𝒰.ρ0 f ^ i • S.r0 x ∈ LinearMap.range S.r0 :=
  ⟨f ^ i • x, by rw [S.r0_smul, map_pow]⟩

variable {S}

theorem vpow_smul_r0_mem_W {g : 𝒰.A1} {s : Finset S.M0} {N : ℕ}
    (hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1)
    {e : S.M0} (he : e ∈ s) (k : ℕ) : 𝒰.ρ1 g ^ k • S.r0 e ∈ W S g s N := by
  classical
  by_cases hk : k < N
  · apply Submodule.mem_sup_left
    apply Submodule.subset_span
    rw [T, Finset.coe_image]
    exact ⟨(e, k), by simp [he, hk], rfl⟩
  · exact range_r1_le S g s N (vpow_smul_mem_range_r1 S g (hN e he) k (not_lt.mp hk))

theorem vpow_smul_smul_mem_W {f : 𝒰.A0} {g : 𝒰.A1} (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1) {s : Finset S.M0} {N : ℕ} {y : S.M01}
    (hv : ∀ i : ℕ, 𝒰.ρ1 g ^ i • y ∈ W S g s N) (hu : ∀ i : ℕ, 𝒰.ρ0 f ^ i • y ∈ W S g s N)
    (p : Algebra.adjoin R ({f} : Set 𝒰.A0)) (n : ℕ) :
    𝒰.ρ1 g ^ n • ((𝒰.ρ0 (p : 𝒰.A0)) • y) ∈ W S g s N := by
  have hp : (p : 𝒰.A0) ∈ (Polynomial.aeval (R := R) f).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact p.2
  obtain ⟨P, hP⟩ := hp
  rw [← hP]
  change 𝒰.ρ1 g ^ n • (𝒰.ρ0 (Polynomial.aeval f P) • y) ∈ _
  rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_eq_sum_range, Finset.sum_smul, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_

  have hterm : 𝒰.ρ1 g ^ n • ((P.coeff j • 𝒰.ρ0 f ^ j) • y)
      = P.coeff j • ((𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ j) • y) := by
    rw [smul_assoc, smul_comm (𝒰.ρ1 g ^ n) (P.coeff j), ← mul_smul]
  rw [hterm, vpow_mul_upow f g hfg]
  refine Submodule.smul_mem _ _ ?_
  split_ifs
  · exact hv _
  · exact hu _

theorem vpow_smul_r0_mem_W_of_mem_span {f : 𝒰.A0} {g : 𝒰.A1} (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1) {s : Finset S.M0} {N : ℕ}
    (hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1)
    {x : S.M0} (hx : x ∈ Submodule.span (Algebra.adjoin R ({f} : Set 𝒰.A0)) (s : Set S.M0)) (n : ℕ) :
    𝒰.ρ1 g ^ n • S.r0 x ∈ W S g s N := by
  induction hx using Submodule.span_induction generalizing n with
  | mem e he => exact vpow_smul_r0_mem_W hN he n
  | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ (hx n) (hy n)
  | smul p x _ hx =>

    have : S.r0 ((p : Algebra.adjoin R ({f} : Set 𝒰.A0)) • x) = 𝒰.ρ0 (p : 𝒰.A0) • S.r0 x := by
      rw [← S.r0_smul]; rfl
    rw [this]
    exact vpow_smul_smul_mem_W hfg hx (fun i => range_r0_le S g s N (upow_smul_r0_mem S f x i)) p n

theorem W_eq_top {f : 𝒰.A0} {g : 𝒰.A1} (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1) {s : Finset S.M0}
    (hs : Submodule.span (Algebra.adjoin R ({f} : Set 𝒰.A0)) (s : Set S.M0) = ⊤) {N : ℕ}
    (hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, 𝒰.ρ0 f ^ n • m ∈ LinearMap.range S.r0) :
    W S g s N = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨n, x, hx⟩ := hloc0 m

  have hvu : 𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ n = 1 := by
    rw [vpow_mul_upow f g hfg]; simp
  have hm : m = 𝒰.ρ1 g ^ n • S.r0 x := by rw [hx, ← mul_smul, hvu, one_smul]
  rw [hm]
  exact vpow_smul_r0_mem_W_of_mem_span hfg hN (hs ▸ Submodule.mem_top) n

end TwoChartCech.ChartFinite

open TwoChartCech.ChartFinite in
theorem solution
    {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, u} R} (S : TwoChartCech.Sections.{u, u, u} 𝒰)
    (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1) :
    Module.Finite R S.H1 := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp hfin0

  choose nOf hnOf using fun m => hloc1 m
  let N : ℕ := s.sup fun e => nOf (S.r0 e)
  have hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1 := fun e he =>
    vpow_smul_mem_range_r1 S g (hnOf (S.r0 e)) N (Finset.le_sup (f := fun e => nOf (S.r0 e)) he)
  have hW := W_eq_top (S := S) hfg hs hN hloc0

  refine Module.finite_def.mpr ⟨(T S g s N).image (LinearMap.range S.cechDiff).mkQ, ?_⟩
  rw [Finset.coe_image, ← Submodule.map_span, eq_top_iff]
  rintro q -
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
  have hm : m ∈ W S g s N := by rw [hW]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  have hb0 : (LinearMap.range S.cechDiff).mkQ b = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hb
  rw [map_add, hb0, add_zero]
  exact Submodule.mem_map_of_mem ha

end S_TwoChartCech_Sections_finite_H1_of_chartFinite
end P2MW
export P2MW.S_TwoChartCech_Sections_finite_H1_of_chartFinite (solution)
