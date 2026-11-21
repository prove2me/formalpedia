-- Prove2me | solution 1 for SoSLinAlg.WeakRank.lower_bound_identity_sec_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:13:58.947342+00:00
-- url     : https://prove2.me/submissions/c3732ded-930d-4bae-a814-333b06b01a75

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank
import Definitions.Def_SoSLinAlg_WeakRank_WPHP
import Definitions.Def_SoSLinAlg_WeakRank_Z
import Theorems.Thm_SoSLinAlg_WeakRank_proposition_4_1
import Theorems.Thm_SoSLinAlg_WeakRank_proposition_4_2

section
noncomputable section

namespace SoSLinAlg.Dev.Sub

open MvPolynomial

theorem totalDegree_map_le {σ τ : Type*} (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ)
    (hφ : ∀ s, (φ (X s)).totalDegree ≤ 1) (p : MvPolynomial σ ℝ) :
    (φ p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  have hm' := le_totalDegree hm
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
  have : (φ (C (coeff m p))).totalDegree = 0 := by
    have : φ (C (coeff m p)) = C (coeff m p) := φ.commutes _
    rw [this]; exact totalDegree_C _
  refine (totalDegree_mul _ _).trans ?_
  rw [this, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun s _ => ?_) hm'
  rw [map_pow]
  refine (totalDegree_pow _ _).trans ?_
  have := hφ s
  nlinarith

end SoSLinAlg.Dev.Sub
end
end

section
noncomputable section

namespace SoSLinAlg.Dev.P110

open MvPolynomial SoSLinAlg.WeakRank SoSLinAlg.Dev.Sub

theorem wrank_deg_ge {n r : ℕ} (hr : 0 < r) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    2 ≤ (WRank r A (i, j)).totalDegree := by
  set m : Var n r →₀ ℕ := Finsupp.single (Sum.inl (i, ⟨0, hr⟩)) 1 + Finsupp.single (Sum.inr (j, ⟨0, hr⟩)) 1 with hm
  have hc : coeff m (WRank r A (i, j)) = 1 := by
    simp only [WRank, xy, x, y, coeff_sub, coeff_sum, coeff_C]
    rw [Finset.sum_eq_single (⟨0, hr⟩ : Fin r)]
    · simp [hm, X, coeff_monomial, monomial_mul]
      intro h
      have := congrArg (fun f => f (Sum.inl (i, (⟨0, hr⟩ : Fin r)))) h
      simp at this
    · intro k _ hk
      simp only [X, monomial_mul, coeff_monomial]
      rw [if_neg]
      intro h
      have := congrArg (fun f => f (Sum.inl (i, k))) h
      simp [hm, Finsupp.single_apply] at this
      exact hk this.symm
    · simp
  have : m ∈ (WRank r A (i, j)).support := by
    rw [mem_support_iff, hc]; exact one_ne_zero
  have := le_totalDegree this
  simpa [hm, Finsupp.sum_add_index'] using this


theorem sub_C_deg_le {σ : Type*} (p : MvPolynomial σ ℝ) (c : ℝ) {d : ℕ} (h : p.totalDegree ≤ d) :
    (p - C c).totalDegree ≤ d := by
  rw [sub_eq_add_neg, ← map_neg]
  exact (totalDegree_add _ _).trans (max_le h (by simp [totalDegree_C]))

theorem wrank_deg_le {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (WRank r A (i, j)).totalDegree ≤ 2 := by
  refine sub_C_deg_le _ _ ?_
  refine totalDegree_finsetSum_le fun k _ => (totalDegree_mul _ _).trans ?_
  simp [x, y, totalDegree_X]

end SoSLinAlg.Dev.P110
end
end

section
noncomputable section

namespace SoSLinAlg.Dev.Deg

open MvPolynomial

/-- product of homogeneous components at the top degrees -/
theorem hc_mul {σ : Type*} (a b : MvPolynomial σ ℝ) {e f : ℕ}
    (ha : a.totalDegree ≤ e) (hb : b.totalDegree ≤ f) :
    homogeneousComponent (e + f) (a * b) = homogeneousComponent e a * homogeneousComponent f b := by
  have decomp : ∀ (p : MvPolynomial σ ℝ) (n : ℕ), p.totalDegree ≤ n →
      p = ∑ i ∈ Finset.range (n + 1), homogeneousComponent i p := by
    intro p n hp
    conv_lhs => rw [← sum_homogeneousComponent p]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro i hi hn
    simp only [Finset.mem_range] at hi hn
    exact homogeneousComponent_eq_zero i p (by omega)
  have da := decomp a e ha
  have db := decomp b f hb
  have key : a * b = ∑ i ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (f + 1),
      homogeneousComponent i a * homogeneousComponent j b := by
    rw [← Finset.sum_mul_sum, ← da, ← db]
  have hom : ∀ i j, homogeneousComponent i a * homogeneousComponent j b
      ∈ homogeneousSubmodule σ ℝ (i + j) := fun i j =>
    (mem_homogeneousSubmodule _ _).2
      ((homogeneousComponent_isHomogeneous i a).mul (homogeneousComponent_isHomogeneous j b))
  have comp : ∀ i j, homogeneousComponent (e + f) (homogeneousComponent i a * homogeneousComponent j b)
      = if e + f = i + j then homogeneousComponent i a * homogeneousComponent j b else 0 :=
    fun i j => homogeneousComponent_of_mem (hom i j)
  rw [key, map_sum]
  simp_rw [map_sum, comp]
  rw [Finset.sum_eq_single e
      (fun i hi hne => Finset.sum_eq_zero fun j hj => if_neg (by simp at hi hj; omega)) (by simp),
    Finset.sum_eq_single f (fun j hj hne => if_neg (by simp at hj; omega)) (by simp), if_pos rfl]

/-- in a sum of real squares no top-degree cancellation: each summand has 2*deg ≤ deg of the sum -/
theorem sumsq_deg {σ : Type*} {m : ℕ} (s : Fin m → MvPolynomial σ ℝ) (α : Fin m) :
    2 * (s α).totalDegree ≤ (∑ β, s β ^ 2).totalDegree := by
  classical
  obtain ⟨β0, -, hβ0⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
    ⟨α, Finset.mem_univ α⟩ (fun β => (s β).totalDegree)
  generalize he : Finset.univ.sup (fun β => (s β).totalDegree) = e at hβ0
  have hle : ∀ β, (s β).totalDegree ≤ e := fun β => by
    rw [← he]
    exact Finset.le_sup (f := fun β => (s β).totalDegree) (Finset.mem_univ β)
  have hα := hle α
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · omega
  by_contra hlt
  push Not at hlt
  have hz : homogeneousComponent (e + e) (∑ β, s β ^ 2) = 0 :=
    homogeneousComponent_eq_zero _ _ (by omega)
  have hsum : ∑ β, homogeneousComponent e (s β) * homogeneousComponent e (s β) = 0 := by
    rw [← hz, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [pow_two, hc_mul _ _ (hle β) (hle β)]
  have hall : ∀ β, homogeneousComponent e (s β) = 0 := by
    intro β
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (eval x) hsum
    simp only [map_sum, map_mul, map_zero] at h1
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (eval x (homogeneousComponent e (s i))))).1 h1 β
      (Finset.mem_univ β)
    simpa using h3
  have hsupp : (s β0).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    intro h
    have : e = 0 := by rw [hβ0, h]; simp
    omega
  obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup _ hsupp (fun d : σ →₀ ℕ => d.sum fun _ k => k)
  have hdeg : d.degree = e := by
    rw [hβ0]
    exact hdeq.symm
  have hc := congrArg (coeff d) (hall β0)
  rw [coeff_homogeneousComponent, if_pos hdeg, coeff_zero] at hc
  exact (mem_support_iff.1 hd) hc

end SoSLinAlg.Dev.Deg
end
end

section
noncomputable section

namespace SoSLinAlg.Dev.Sgn

open MvPolynomial SoSLinAlg.WeakRank SoSLinAlg.Dev.Sub

/-- (X,Y) ↦ (-X,-Y) -/
def sgn {σ : Type*} : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ := aeval (fun s => C (-1) * X s)

theorem sgn_monomial {σ : Type*} (m : σ →₀ ℕ) (c : ℝ) :
    sgn (monomial m c) = C ((-1) ^ (m.sum fun _ e => e)) * monomial m c := by
  have key : sgn (∏ x ∈ m.support, (X x : MvPolynomial σ ℝ) ^ m x) =
      C ((-1) ^ (∑ x ∈ m.support, m x)) * ∏ x ∈ m.support, (X x : MvPolynomial σ ℝ) ^ m x := by
    rw [map_prod]
    simp only [map_pow, sgn, aeval_X, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  rw [monomial_eq, map_mul, Finsupp.prod, key]
  have : (sgn (C c : MvPolynomial σ ℝ) : MvPolynomial σ ℝ) = C c := sgn.commutes c
  rw [this, Finsupp.sum]
  ring

theorem coeff_sgn {σ : Type*} (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    coeff m (sgn p) = (-1) ^ (m.sum fun _ e => e) * coeff m p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [sgn_monomial, coeff_C_mul, coeff_monomial]
    by_cases h : u = m
    · subst h; simp [mul_comm]
    · simp [h]
  | add p q hp hq => simp [hp, hq, mul_add]


theorem sgn_deg {σ : Type*} (p : MvPolynomial σ ℝ) : (sgn p).totalDegree ≤ p.totalDegree :=
  totalDegree_map_le sgn (fun s => by
    have h : (sgn (X s : MvPolynomial σ ℝ) : MvPolynomial σ ℝ) = C (-1) * X s := by
      simp [sgn]
    rw [h]
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_X, totalDegree_C]) p

theorem sgn_wrank {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ij : Fin n × Fin n) :
    sgn (WRank r A ij) = WRank r A ij := by
  have hx : ∀ s : Var n r, (sgn (X s : Poly n r) : Poly n r) = C (-1) * X s := fun s => by
    simp [sgn]
  simp only [WRank, xy, x, y, map_sub, map_sum, map_mul, hx, sgn.commutes]
  simp [Finset.sum_sub_distrib]

theorem sym_deg {σ : Type*} (p : MvPolynomial σ ℝ) {E : ℕ} (hp : p.totalDegree ≤ E + 1)
    (hE : Odd (E + 1)) : (p + sgn p).totalDegree ≤ E := by
  classical
  unfold totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hc : coeff m (p + sgn p) = (1 + (-1) ^ (m.sum fun _ e => e)) * coeff m p := by
    rw [coeff_add, coeff_sgn]; ring
  rw [mem_support_iff, hc] at hm
  have hm1 : coeff m p ≠ 0 := fun h => hm (by simp [h])
  have h1 : (m.sum fun _ e => e) ≤ E + 1 := (le_totalDegree (mem_support_iff.mpr hm1)).trans hp
  have h2 : (m.sum fun _ e => e) ≠ E + 1 := by
    intro h
    apply hm
    rw [h, Odd.neg_one_pow hE]; simp
  show (m.sum fun _ e => e) ≤ E
  omega

end SoSLinAlg.Dev.Sgn
end
end

section
noncomputable section

namespace SoSLinAlg.Dev.Lower

open MvPolynomial SoSLinAlg.WeakRank SoSLinAlg.Dev.Sub SoSLinAlg.Dev.Deg SoSLinAlg.Dev.Sgn

abbrev W (n r : ℕ) : Fin n × Fin n → Poly n r := WRank r (1 : Matrix (Fin n) (Fin n) ℝ)

def Good (n r D d : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (q : ι → Poly n r) (h : Fin n × Fin n → Poly n r),
    (∀ α, (q α).totalDegree ≤ d) ∧ (∀ ij, h ij = 0 ∨ (h ij).totalDegree + 2 ≤ D) ∧
    (∀ ij, (h ij).totalDegree ≤ 2 * r - 2) ∧
    (-1 : Poly n r) = ∑ α, q α ^ 2 + ∑ ij, h ij * W n r ij

theorem B_add {σ : Type*} {D : ℕ} {p q : MvPolynomial σ ℝ}
    (hp : p = 0 ∨ p.totalDegree + 2 ≤ D) (hq : q = 0 ∨ q.totalDegree + 2 ≤ D) :
    p + q = 0 ∨ (p + q).totalDegree + 2 ≤ D := by
  by_cases h : p + q = 0
  · exact Or.inl h
  right
  have := totalDegree_add p q
  rcases hp with rfl | hp
  · rcases hq with rfl | hq
    · simp at h
    · simp only [zero_add] at *; omega
  · rcases hq with rfl | hq
    · simp only [add_zero] at *; omega
    · omega

theorem B_sum {σ ι : Type*} {D : ℕ} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i ∈ s, f i = 0 ∨ (f i).totalDegree + 2 ≤ D) :
    ∑ i ∈ s, f i = 0 ∨ (∑ i ∈ s, f i).totalDegree + 2 ≤ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact B_add (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem B_mul {σ : Type*} {D d : ℕ} {p v : MvPolynomial σ ℝ}
    (hp : p = 0 ∨ p.totalDegree + 2 ≤ d) (hv : v.totalDegree ≤ d) (hd : 2 * d ≤ D) :
    p * v = 0 ∨ (p * v).totalDegree + 2 ≤ D := by
  rcases hp with rfl | hp
  · simp
  · right
    have := totalDegree_mul p v
    omega

theorem E_mul {σ : Type*} {r d : ℕ} {p v : MvPolynomial σ ℝ}
    (hp : p = 0 ∨ p.totalDegree + 2 ≤ d) (hv : v.totalDegree ≤ d) (hd : d ≤ r) :
    (p * v).totalDegree ≤ 2 * r - 2 := by
  rcases hp with rfl | hp
  · simp
  · have := totalDegree_mul p v
    omega

theorem vanish {n r d : ℕ} (hr : 0 < r) (hrn : r < n) (hdr : d ≤ r)
    {ι : Type} [Fintype ι] (q : ι → Poly n r) (h : Fin n × Fin n → Poly n r)
    (hq : ∀ α, (q α).totalDegree ≤ d) (hh2 : ∀ ij, (h ij).totalDegree ≤ 2 * r - 2)
    (heq : (-1 : Poly n r) = ∑ α, q α ^ 2 + ∑ ij, h ij * W n r ij) :
    VanishesOnZ d (homogeneousComponent (2 * d) (1 + ∑ α, q α ^ 2)) := by
  refine proposition_4_1 hr hrn hdr _ ?_ (fun ij => -h ij)
    (fun ij => by rw [totalDegree_neg]; exact hh2 ij) ?_
  · refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine totalDegree_finsetSum_le fun α _ => (totalDegree_pow _ _).trans ?_
    have := hq α
    omega
  · simp only [neg_mul, Finset.sum_neg_distrib]
    linear_combination (-1 : Poly n r) * heq


theorem sub_hc_deg {σ : Type*} (q : MvPolynomial σ ℝ) {d : ℕ} (hq : q.totalDegree ≤ d + 1) :
    (q - homogeneousComponent (d + 1) q).totalDegree ≤ d := by
  classical
  unfold totalDegree
  refine Finset.sup_le fun m hm => ?_
  rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
  have h1 : (m.sum fun _ e => e) ≤ d + 1 := by
    by_contra hlt
    push Not at hlt
    apply hm
    have : coeff m q = 0 := by
      by_contra hne
      have := le_totalDegree (mem_support_iff.mpr hne)
      omega
    simp [this]
  have h2 : (m.sum fun _ e => e) ≠ d + 1 := by
    intro h; apply hm; rw [if_pos (show Finsupp.degree m = d + 1 from h), sub_self]
  show (m.sum fun _ e => e) ≤ d
  omega

theorem step {n r D d : ℕ} (hr : 0 < r) (hrn : r < n) (hd : 2 * (d + 1) ≤ D) (hdr : d + 1 ≤ r)
    (hg : Good n r D (d + 1)) : Good n r D d := by
  obtain ⟨ι, inst, q, h, hq, hh1, hh2, heq⟩ := hg
  have hv := vanish hr hrn hdr q h hq hh2 heq
  have hcsum : homogeneousComponent (2 * (d + 1)) (1 + ∑ α, q α ^ 2) =
      ∑ α, (homogeneousComponent (d + 1) (q α)) ^ 2 := by
    rw [map_add, map_sum]
    have h1 : homogeneousComponent (2 * (d + 1)) (1 : Poly n r) = 0 :=
      homogeneousComponent_eq_zero _ _ (by rw [totalDegree_one]; omega)
    rw [h1, zero_add]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [pow_two, two_mul, hc_mul _ _ (hq α) (hq α), pow_two]
  have hvan : ∀ α, VanishesOnZ (d + 1) (homogeneousComponent (d + 1) (q α)) := by
    intro α X Y hXY
    have := hv X Y hXY
    rw [hcsum, map_sum] at this
    simp only [map_pow] at this
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 this α
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h0
  have hcdeg : ∀ α, (homogeneousComponent (d + 1) (q α)).totalDegree ≤ d + 1 := fun α =>
    (homogeneousComponent_isHomogeneous _ _).totalDegree_le
  choose hα hαeq hαb using fun α =>
    proposition_4_2 hr hrn hdr (homogeneousComponent (d + 1) (q α)) (hcdeg α) (hvan α)
  set L : ι → Poly n r := fun α => ∑ ij, hα α ij * W n r ij with hL
  set u : ι → Poly n r :=
    fun α => (q α - homogeneousComponent (d + 1) (q α)) + ∑ i, hα α (i, i) with hu
  set v : ι → Poly n r := fun α => u α + u α + L α with hv'
  have h1 : ∀ α, homogeneousComponent (d + 1) (q α) = L α + ∑ i, hα α (i, i) := by
    intro α
    rw [hαeq α]
    simp only [hL]
    have hxy : ∀ ij : Fin n × Fin n, xy ij.1 ij.2 =
        W n r ij + C ((1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2) := by
      intro ij; simp [W, WRank]
    simp only [hxy, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Fintype.sum_prod_type]
    simp [Matrix.one_apply, mul_ite, Finset.sum_ite_eq]
  have hqeq : ∀ α, q α = u α + L α := by
    intro α
    simp only [hu]
    rw [h1 α]; ring
  have hu_deg : ∀ α, (u α).totalDegree ≤ d := by
    intro α
    refine (totalDegree_add _ _).trans (max_le (sub_hc_deg _ (hq α)) ?_)
    refine totalDegree_finsetSum_le fun i _ => ?_
    rcases hαb α (i, i) with h0 | h0
    · simp [h0]
    · omega
  have hL_deg : ∀ α, (L α).totalDegree ≤ d + 1 := by
    intro α
    refine totalDegree_finsetSum_le fun ij _ => ?_
    have := SoSLinAlg.Dev.P110.wrank_deg_le (r := r) (1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2
    rcases hαb α ij with h0 | h0
    · simp [h0]
    · refine (totalDegree_mul _ _).trans ?_
      show _ + (WRank r 1 (ij.1, ij.2)).totalDegree ≤ _
      omega
  have hv_deg : ∀ α, (v α).totalDegree ≤ d + 1 := by
    intro α
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le ?_ ?_)) (hL_deg α)) <;> have := hu_deg α <;> omega
  refine ⟨ι, inst, u, fun ij => h ij + ∑ α, hα α ij * v α, hu_deg, ?_, ?_, ?_⟩
  · intro ij
    exact B_add (hh1 ij) (B_sum _ _ fun α _ => B_mul (hαb α ij) (hv_deg α) hd)
  · intro ij
    refine (totalDegree_add _ _).trans (max_le (hh2 ij) ?_)
    exact totalDegree_finsetSum_le fun α _ => E_mul (hαb α ij) (hv_deg α) hdr
  · have e1 : ∀ α, q α ^ 2 = u α ^ 2 + ∑ ij, hα α ij * v α * W n r ij := by
      intro α
      have : L α * v α = ∑ ij, hα α ij * v α * W n r ij := by
        simp only [hL, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ij _ => by ring
      rw [← this, hqeq α]
      simp only [hv']
      ring
    rw [heq]
    simp only [e1, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun ij α => hα α ij * v α * W n r ij)]
    ring


theorem not_good {n r D : ℕ} (hr : 0 < r) (hrn : r < n) (hD : D ≤ 2 * r + 1) :
    ∀ d, 2 * d ≤ D → ¬ Good n r D d := by
  intro d
  induction d with
  | succ d ih =>
    intro hd hg
    exact ih (by omega) (step hr hrn hd (by omega) hg)
  | zero =>
    intro _ hg
    obtain ⟨ι, inst, q, h, hq, hh1, hh2, heq⟩ := hg
    have hv := vanish hr hrn (Nat.zero_le r) q h hq hh2 heq
    have hqC : ∀ α, q α = C (coeff 0 (q α)) := fun α =>
      totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 (hq α))
    have hf : (1 : Poly n r) + ∑ α, q α ^ 2 = C (1 + ∑ α, (coeff 0 (q α)) ^ 2) := by
      simp only [map_add, map_one, map_sum, map_pow]
      congr 1
      exact Finset.sum_congr rfl fun α _ => by rw [← hqC α]
    have h0 := hv 0 0 (by simp [Z])
    rw [Nat.mul_zero, homogeneousComponent_zero, hf, coeff_C, if_pos rfl] at h0
    simp only [eval_C] at h0
    have : (0 : ℝ) ≤ ∑ α, (coeff 0 (q α)) ^ 2 := Finset.sum_nonneg fun α _ => sq_nonneg _
    linarith

theorem sumsq_exists {σ : Type*} {g : MvPolynomial σ ℝ} (hg : IsSumSq g) :
    ∃ (m : ℕ) (s : Fin m → MvPolynomial σ ℝ), g = ∑ β, s β ^ 2 := by
  induction hg with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | sq_add a _ ih =>
    obtain ⟨m, s, hs⟩ := ih
    refine ⟨m + 1, Fin.cons a s, ?_⟩
    simp [Fin.sum_univ_succ, pow_two, hs]


theorem lower_bound {n r : ℕ} (hr : 0 < r) (hrn : r < n) :
    ∀ D : ℕ, D ≤ 2 * r + 1 → ¬ SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D := by
  intro D hD hS
  obtain ⟨g, p, hg, hgd, hpd, heq⟩ := hS
  obtain ⟨m, s, rfl⟩ := sumsq_exists hg
  have hpb : ∀ ij, p ij = 0 ∨ (p ij).totalDegree + 2 ≤ D := by
    intro ij
    by_cases h0 : p ij = 0
    · exact Or.inl h0
    right
    have hw : W n r ij ≠ 0 := by
      intro hw
      have := SoSLinAlg.Dev.P110.wrank_deg_ge hr (1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2
      have h' : WRank r (1 : Matrix (Fin n) (Fin n) ℝ) (ij.1, ij.2) = 0 := hw
      rw [h'] at this
      simp at this
    have := hpd ij
    rw [totalDegree_mul_of_isDomain h0 hw] at this
    have := SoSLinAlg.Dev.P110.wrank_deg_ge hr (1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2
    show _ + 2 ≤ D
    have h3 : 2 ≤ (W n r ij).totalDegree := this
    omega
  set c : Poly n r := C (1 / 2 : ℝ) with hc
  have hc2 : c + c = 1 := by
    rw [hc, ← map_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, map_one]
  have hcs : C ((Real.sqrt 2)⁻¹) * C ((Real.sqrt 2)⁻¹) = (c : Poly n r) := by
    rw [hc, ← map_mul]
    congr 1
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have heq' := congrArg sgn heq
  rw [map_neg, map_one, map_add, map_sum, map_sum] at heq'
  simp only [map_mul, map_pow, sgn_wrank] at heq'
  have hnot := not_good (n := n) (r := r) (D := D) hr hrn hD (D / 2) (by omega)
  refine hnot ⟨Fin m ⊕ Fin m, inferInstance,
    Sum.elim (fun α => C ((Real.sqrt 2)⁻¹) * s α) (fun α => C ((Real.sqrt 2)⁻¹) * sgn (s α)),
    fun ij => c * (p ij + sgn (p ij)), ?_, ?_, ?_, ?_⟩
  · intro α
    rcases α with α | α
    · have h1 := sumsq_deg s α
      refine (totalDegree_mul _ _).trans ?_
      simp only [Sum.elim_inl, totalDegree_C, zero_add]
      omega
    · have h1 := sumsq_deg s α
      have h2 := sgn_deg (s α)
      refine (totalDegree_mul _ _).trans ?_
      simp only [Sum.elim_inr, totalDegree_C, zero_add]
      omega
  · intro ij
    by_cases h0 : c * (p ij + sgn (p ij)) = 0
    · exact Or.inl h0
    right
    rcases hpb ij with hp0 | hp1
    · rw [hp0] at h0; simp at h0
    · show (c * (p ij + sgn (p ij))).totalDegree + 2 ≤ D
      have hm := totalDegree_mul c (p ij + sgn (p ij))
      have := (totalDegree_add (p ij) (sgn (p ij)))
      have := sgn_deg (p ij)
      have h3 : (c : Poly n r).totalDegree = 0 := totalDegree_C _
      omega
  · intro ij
    refine (totalDegree_mul _ _).trans ?_
    have h3 : (c : Poly n r).totalDegree = 0 := totalDegree_C _
    rw [h3, zero_add]
    have hp : (p ij).totalDegree ≤ (2 * r - 2) + 1 := by
      rcases hpb ij with hp0 | hp1
      · rw [hp0]; simp
      · omega
    exact sym_deg (p ij) hp ⟨r - 1, by omega⟩
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_pow]
    have hk : (C ((Real.sqrt 2)⁻¹) : Poly n r) ^ 2 = c := by rw [pow_two]; exact hcs
    simp only [hk]
    have e1 : ∑ a, c * s a ^ 2 = c * ∑ a, s a ^ 2 := (Finset.mul_sum ..).symm
    have e2 : ∑ a, c * sgn (s a) ^ 2 = c * ∑ a, sgn (s a) ^ 2 := (Finset.mul_sum ..).symm
    have e3 : ∑ x, c * (p x + sgn (p x)) * W n r x =
        c * ∑ x, p x * W n r x + c * ∑ x, sgn (p x) * W n r x := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1, e2, e3]
    linear_combination c * heq + c * heq' + hc2

end SoSLinAlg.Dev.Lower
end
end

section
namespace SoSLinAlg.WeakRank

theorem chk_lower_bound_identity_sec_4_3 {n r : ℕ} (hr : 0 < r) (hrn : r < n) :
    ∀ D : ℕ, D ≤ 2 * r + 1 →
      ¬ SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D :=
  SoSLinAlg.Dev.Lower.lower_bound hr hrn

end SoSLinAlg.WeakRank
end

theorem solution : type_of% @SoSLinAlg.WeakRank.chk_lower_bound_identity_sec_4_3 := @SoSLinAlg.WeakRank.chk_lower_bound_identity_sec_4_3
