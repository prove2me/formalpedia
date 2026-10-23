-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:33:19.207466+00:00
-- url     : https://prove2.me/submissions/a2c434b9-29fb-40fd-ac50-5b128d955523

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

open Module
open scoped Matrix ComplexOrder ComplexConjugate

namespace X6P26P

/-- conic Carathéodory -/
theorem conic {ι V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq ι] (v : ι → V) :
    ∀ (s : Finset ι) (c : ι → ℝ), (∀ i ∈ s, 0 < c i) →
    ∃ s' ⊆ s, ∃ c' : ι → ℝ, (∀ i ∈ s', 0 < c' i) ∧ LinearIndepOn ℝ v (s' : Set ι) ∧
      ∑ i ∈ s, c i • v i = ∑ i ∈ s', c' i • v i := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hc
  by_cases hli : LinearIndepOn ℝ v (s : Set ι)
  · exact ⟨s, subset_rfl, c, hc, hli, rfl⟩
  rw [not_linearIndepOn_finset_iff] at hli
  obtain ⟨g0, hg0, i0, hi0, hgi0⟩ := hli
  -- make some coefficient positive
  obtain ⟨g, hg, i1, hi1, hgi1⟩ : ∃ g : ι → ℝ, ∑ i ∈ s, g i • v i = 0 ∧ ∃ i ∈ s, 0 < g i := by
    rcases lt_or_gt_of_ne hgi0 with h | h
    · refine ⟨fun i => -g0 i, ?_, i0, hi0, by linarith⟩
      simp only [neg_smul, Finset.sum_neg_distrib, hg0, neg_zero]
    · exact ⟨g0, hg0, i0, hi0, h⟩
  set T := s.filter (fun i => 0 < g i)
  have hT : T.Nonempty := ⟨i1, Finset.mem_filter.2 ⟨hi1, hgi1⟩⟩
  obtain ⟨j, hjT, hjmin⟩ := T.exists_min_image (fun i => c i / g i) hT
  have hjs : j ∈ s := (Finset.mem_filter.1 hjT).1
  have hgj : 0 < g j := (Finset.mem_filter.1 hjT).2
  set θ := c j / g j
  set c2 : ι → ℝ := fun i => c i - θ * g i
  have hc2 : ∀ i ∈ s, 0 ≤ c2 i := by
    intro i hi
    by_cases hgi : 0 < g i
    · have := hjmin i (Finset.mem_filter.2 ⟨hi, hgi⟩)
      have : θ * g i ≤ c i := by
        rw [le_div_iff₀ hgi] at this; linarith
      simp only [c2]; linarith
    · push Not at hgi
      have hθ : 0 ≤ θ := div_nonneg (hc j hjs).le hgj.le
      have := hc i hi
      simp only [c2]; nlinarith
  have hc2j : c2 j = 0 := by
    simp only [c2, θ]; field_simp; ring
  set s2 := s.filter (fun i => 0 < c2 i)
  have hs2 : s2 ⊂ s := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have : j ∈ s2 := h ▸ hjs
    rw [Finset.mem_filter, hc2j] at this
    exact lt_irrefl _ this.2
  have hsum : ∑ i ∈ s, c i • v i = ∑ i ∈ s2, c2 i • v i := by
    have h1 : ∑ i ∈ s, c i • v i = ∑ i ∈ s, c2 i • v i := by
      have : ∑ i ∈ s, c2 i • v i = ∑ i ∈ s, c i • v i - θ • ∑ i ∈ s, g i • v i := by
        simp only [c2, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
      rw [this, hg, smul_zero, sub_zero]
    rw [h1, Finset.sum_filter_of_ne]
    intro i hi hne
    rcases (hc2 i hi).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_smul] at hne; exact absurd rfl hne
  obtain ⟨s', hs', c', hc', hli', hsum'⟩ := ih s2 hs2 c2 (fun i hi => (Finset.mem_filter.1 hi).2)
  exact ⟨s', hs'.trans hs2.subset, c', hc', hli', hsum.trans hsum'⟩


open QAlgorithms.Papers.Independent.Information100.P26

theorem ad_smul {d : ℕ} (r : ℝ) (B : Mat d) : ad ((r : ℂ) • B) = (r ^ 2) • ad B := by
  ext p q
  simp only [ad, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Complex.real_smul]
  push_cast; ring

theorem rank_one_of {d : ℕ} (a b : Fin d → ℂ) (h : ad (Matrix.vecMulVec a b) ≠ 0) :
    (Matrix.vecMulVec a b).rank = 1 := by
  apply le_antisymm (Matrix.rank_vecMulVec_le a b)
  by_contra h0
  push Not at h0
  have hz : Matrix.vecMulVec a b = 0 := by
    have h0' : (Matrix.vecMulVec a b).rank = 0 := by omega
    unfold Matrix.rank at h0'
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0'
    ext i j
    have h1 := congrFun (LinearMap.congr_fun h0' (Pi.single j 1)) i
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using h1
  apply h; rw [hz]; ext p q; simp [ad]

theorem rank_smul_one {d : ℕ} (r : ℝ) (hr : r ≠ 0) (B : Mat d) (hB : B.rank = 1) :
    ((r : ℂ) • B).rank = 1 := by
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors] <;> try assumption
  exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hr)

end X6P26P

section
open QAlgorithms.Papers.Independent.Information100.P26
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {d : ℕ} (hd : 0 < d) (t : Map d) (ht : EB t) :
    ∃ n : ℕ, ∃ A : Fin n → Mat d,
      (∀ k, (A k).rank = 1) ∧ t = ∑ k, ad (A k) ∧
      LinearIndependent ℝ (fun k => ad (A k)) := by
  obtain ⟨q, w, A, B, hw, hdens, hX⟩ := ht
  choose mA va hva using fun j => Matrix.posSemidef_iff_eq_sum_vecMulVec.1 (hdens j).1.1
  choose mB vb hvb using fun j => Matrix.posSemidef_iff_eq_sum_vecMulVec.1 (hdens j).2.1
  let Bm : (Σ j : Fin q, Fin (mA j) × Fin (mB j)) → Mat d :=
    fun x => Matrix.vecMulVec (va x.1 x.2.1) (vb x.1 x.2.2)
  let c : (Σ j : Fin q, Fin (mA j) × Fin (mB j)) → ℝ := fun x => w x.1
  have ht' : t = ∑ x, c x • ad (Bm x) := by
    ext p r
    have h1 := congrFun (congrFun hX (p.1, r.1)) (p.2, r.2)
    change t p r = _ at h1
    rw [h1]
    simp only [Matrix.sum_apply, Matrix.smul_apply, hva, hvb, Bm, c, ad,
      Fintype.sum_sigma, Fintype.sum_prod_type, smul_eq_mul, Complex.real_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Finset.sum_mul, Finset.mul_sum, Pi.star_apply, RCLike.star_def, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  set s := Finset.univ.filter (fun x => 0 < c x)
  have ht'' : t = ∑ x ∈ s, c x • ad (Bm x) := by
    rw [ht', Finset.sum_filter_of_ne]
    intro x _ hne
    rcases (hw x.1).lt_or_eq with h | h
    · exact h
    · exfalso; apply hne; simp [c, ← h]
  obtain ⟨s', -, c', hc', hli, hsum⟩ :=
    X6P26P.conic (fun x => ad (Bm x)) s c (fun x hx => (Finset.mem_filter.1 hx).2)
  set e := s'.equivFin
  refine ⟨s'.card, fun k => (Real.sqrt (c' (e.symm k)) : ℂ) • Bm (e.symm k), ?_, ?_, ?_⟩
  · intro k
    have hne : ad (Bm (e.symm k)) ≠ 0 := hli.ne_zero (e.symm k).2
    have hc := hc' _ (e.symm k).2
    exact X6P26P.rank_smul_one _ (Real.sqrt_ne_zero'.2 hc) _ (X6P26P.rank_one_of _ _ hne)
  · rw [ht'', hsum, ← Finset.sum_coe_sort s']
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [X6P26P.ad_smul, Real.sq_sqrt (hc' _ (e.symm k).2).le]
  · have h1 : LinearIndependent ℝ (fun k => ad (Bm (e.symm k))) :=
      hli.comp e.symm e.symm.injective
    have h2 := h1.units_smul (fun k => Units.mk0 (c' (e.symm k)) (hc' _ (e.symm k).2).ne')
    convert h2 using 1
    funext k
    rw [X6P26P.ad_smul, Real.sq_sqrt (hc' _ (e.symm k).2).le]
    rfl
end
