-- Prove2me | solution 1 for SoSLinAlg.WeakRank.proposition_1_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:58:19.244763+00:00
-- url     : https://prove2.me/submissions/1ebe96e6-ea26-47c2-83db-e7dc887f37df

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank
import Definitions.Def_SoSLinAlg_WeakRank_WPHP

section
noncomputable section

namespace SoSLinAlg.Dev.Sub

open MvPolynomial

theorem isSumSq_map {σ τ : Type*} (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ)
    {g : MvPolynomial σ ℝ} (hg : IsSumSq g) : IsSumSq (φ g) := by
  induction hg with
  | zero => simp [IsSumSq.zero]
  | sq_add a _ ih =>
    rw [map_add, map_mul]
    exact IsSumSq.sq_add _ ih

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

/-- The core transfer lemma: constant-linear-combination of constraints under a linear substitution. -/
theorem refutable_transfer {σ τ ι κ : Type*} [Fintype ι] [Fintype κ]
    (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ)
    (hφ : ∀ s, (φ (X s)).totalDegree ≤ 1)
    (p : ι → MvPolynomial σ ℝ) (q : κ → MvPolynomial τ ℝ) (c : ι → κ → ℝ)
    (hp : ∀ i, 2 ≤ (p i).totalDegree) (hq : ∀ k, (q k).totalDegree ≤ 2)
    (hc : ∀ i, φ (p i) = ∑ k, C (c i k) * q k) (D : ℕ)
    (h : SoSLinAlg.WeakRank.SoSRefutable p D) : SoSLinAlg.WeakRank.SoSRefutable q D := by
  obtain ⟨g, h, hg, hgd, hhd, heq⟩ := h
  have hdeg : ∀ i, h i = 0 ∨ (h i).totalDegree + 2 ≤ D := by
    intro i
    by_cases h0 : h i = 0
    · exact Or.inl h0
    right
    by_cases hp0 : p i = 0
    · have := hp i; rw [hp0] at this; simp at this
    have := hhd i
    rw [totalDegree_mul_of_isDomain h0 hp0] at this
    have := hp i
    omega
  refine ⟨φ g, fun k => ∑ i, C (c i k) * φ (h i), isSumSq_map φ hg,
    (totalDegree_map_le φ hφ g).trans hgd, ?_, ?_⟩
  · intro k
    by_cases hz : ∀ i, h i = 0
    · simp [hz]
    push Not at hz
    obtain ⟨i0, hi0⟩ := hz
    have hD : 2 ≤ D := by
      rcases hdeg i0 with h0 | h0
      · exact absurd h0 hi0
      · omega
    have hsum : (∑ i, C (c i k) * φ (h i)).totalDegree ≤ D - 2 := by
      refine totalDegree_finsetSum_le fun i _ => ?_
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_map_le φ hφ _).trans ?_
      rcases hdeg i with h0 | h0
      · simp [h0]
      · omega
    show (_ * q k).totalDegree ≤ D
    refine (totalDegree_mul _ _).trans ?_
    have := hq k
    beta_reduce
    omega
  · have := congrArg φ heq
    rw [map_neg, map_one, map_add, map_sum] at this
    rw [this]
    congr 1
    simp only [map_mul, hc, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

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

theorem tframe_deg_ge {n r : ℕ} (hr : 0 < r) (i k : Fin n) :
    2 ≤ (TFrame n r (i, k)).totalDegree := by
  set m : (Fin n × Fin r) →₀ ℕ := Finsupp.single (i, ⟨0, hr⟩) 1 + Finsupp.single (k, ⟨0, hr⟩) 1 with hm
  have hc : coeff m (TFrame n r (i, k)) = 1 := by
    simp only [TFrame, singleX, coeff_sub, coeff_sum, coeff_C]
    rw [Finset.sum_eq_single (⟨0, hr⟩ : Fin r)]
    · simp [hm, X, coeff_monomial, monomial_mul]
      intro h
      have := congrArg (fun f => f (i, (⟨0, hr⟩ : Fin r))) h
      simp [Finsupp.single_apply] at this
      split_ifs at this <;> omega
    · intro j _ hj
      simp only [X, monomial_mul, coeff_monomial]
      rw [if_neg]
      intro h
      have := congrArg (fun f => f (i, (⟨0, hr⟩ : Fin r))) h
      simp [hm, Finsupp.single_apply] at this
      rw [if_neg hj] at this
      split_ifs at this <;> omega
    · simp
  have : m ∈ (TFrame n r (i, k)).support := by
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

theorem tframe_deg_le {n r : ℕ} (i k : Fin n) : (TFrame n r (i, k)).totalDegree ≤ 2 := by
  refine sub_C_deg_le _ _ ?_
  refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
  simp [singleX, totalDegree_X]

theorem wphp_deg_le {n r : ℕ} (κ : WPHPIndex n r) : (WPHP n r κ).totalDegree ≤ 2 := by
  rcases κ with ij | ⟨ji, ik⟩ | i
  · simp only [WPHP]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_pow _ _).trans ?_
      simp [singleX, totalDegree_X]
    · simp [singleX, totalDegree_X]
  · simp only [WPHP]
    refine (totalDegree_mul _ _).trans ?_
    simp [singleX, totalDegree_X]
  · simp only [WPHP]
    refine sub_C_deg_le _ _ ?_
    refine le_trans (totalDegree_finsetSum_le (d := 1) fun j _ => ?_) (by norm_num)
    simp [singleX, totalDegree_X]


/-- X ↦ A X, Y ↦ Y -/
def phi1 {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Poly n r →ₐ[ℝ] Poly n r :=
  aeval (Sum.elim (fun lk : Fin n × Fin r => ∑ m : Fin n, C (A lk.1 m) * x m lk.2)
    (fun jk : Fin n × Fin r => y jk.1 jk.2))

theorem phi1_deg {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Var n r) :
    (phi1 A (X s)).totalDegree ≤ 1 := by
  rcases s with lk | jk
  · simp only [phi1, aeval_X, Sum.elim_inl]
    refine totalDegree_finsetSum_le fun m _ => (totalDegree_mul _ _).trans ?_
    simp [x, totalDegree_X, totalDegree_C]
  · simp [phi1, y, totalDegree_X]

theorem phi1_wrank {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    phi1 A (WRank r A (i, j)) =
      ∑ l : Fin n, C (A i l) * WRank r (1 : Matrix (Fin n) (Fin n) ℝ) (l, j) := by
  simp only [WRank, xy, phi1, x, y, map_sub, map_sum, map_mul, aeval_X, aeval_C,
    Sum.elim_inl, Sum.elim_inr, Finset.mul_sum, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [mul_assoc]
  · simp [Matrix.one_apply]

/-- Y ↦ X. -/
def phi2 {n r : ℕ} : Poly n r →ₐ[ℝ] SinglePoly n r :=
  aeval (Sum.elim (fun ik : Fin n × Fin r => singleX ik.1 ik.2)
    (fun ik : Fin n × Fin r => singleX ik.1 ik.2))

theorem phi2_deg {n r : ℕ} (s : Var n r) : (phi2 (n := n) (r := r) (X s)).totalDegree ≤ 1 := by
  rcases s with lk | jk <;> simp [phi2, singleX, totalDegree_X]

theorem phi2_wrank {n r : ℕ} (i j : Fin n) :
    phi2 (WRank r (1 : Matrix (Fin n) (Fin n) ℝ) (i, j)) = TFrame n r (i, j) := by
  simp [WRank, xy, phi2, x, y, TFrame, singleX]

theorem part1 {n r : ℕ} (hr : 0 < r) (A : Matrix (Fin n) (Fin n) ℝ) (D : ℕ)
    (h : SoSRefutable (WRank r A) D) :
    SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D :=
  refutable_transfer (phi1 A) (phi1_deg A) (WRank r A) (WRank r 1)
    (fun ij l => A ij.1 l.1 * (if l.2 = ij.2 then 1 else 0))
    (fun ij => wrank_deg_ge hr A ij.1 ij.2) (fun l => wrank_deg_le _ l.1 l.2)
    (fun ⟨i, j⟩ => by
      rw [phi1_wrank, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp) D h

theorem part2 {n r : ℕ} (hr : 0 < r) (D : ℕ)
    (h : SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D) :
    SoSRefutable (TFrame n r) D :=
  refutable_transfer phi2 phi2_deg (WRank r 1) (TFrame n r)
    (fun ij l => if ij = l then 1 else 0)
    (fun ij => wrank_deg_ge hr 1 ij.1 ij.2) (fun l => tframe_deg_le l.1 l.2)
    (fun ⟨i, j⟩ => by
      rw [phi2_wrank]; simp [Finset.sum_ite_eq]) D h


theorem tframe_offdiag {n r : ℕ} (a b : Fin n) (hab : a < b) :
    TFrame n r (a, b) = ∑ j : Fin r,
      WPHP n r (Sum.inr (Sum.inl (j, ⟨(a, b), hab⟩))) := by
  have : (1 : Matrix (Fin n) (Fin n) ℝ) a b = 0 := Matrix.one_apply_ne hab.ne
  simp [TFrame, WPHP, this]

theorem tframe_eq_sum {n r : ℕ} (i k : Fin n) :
    ∃ S : Finset (WPHPIndex n r), TFrame n r (i, k) = ∑ κ ∈ S, WPHP n r κ := by
  rcases lt_trichotomy i k with h | h | h
  · refine ⟨Finset.univ.image (fun j : Fin r => Sum.inr (Sum.inl (j, ⟨(i, k), h⟩))), ?_⟩
    rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab), tframe_offdiag i k h]
  · subst h
    refine ⟨Finset.univ.image (fun j : Fin r => (Sum.inl (i, j) : WPHPIndex n r)) ∪
      {Sum.inr (Sum.inr i)}, ?_⟩
    rw [Finset.sum_union (by simp [Finset.disjoint_left]),
      Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
    simp [TFrame, WPHP, singleX, Finset.sum_sub_distrib, pow_two]
  · refine ⟨Finset.univ.image (fun j : Fin r => Sum.inr (Sum.inl (j, ⟨(k, i), h⟩))), ?_⟩
    rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
    have : (1 : Matrix (Fin n) (Fin n) ℝ) i k = 0 := Matrix.one_apply_ne h.ne'
    simp [TFrame, WPHP, this, mul_comm]

theorem part3 {n r : ℕ} (hr : 0 < r) (D : ℕ)
    (h : SoSRefutable (TFrame n r) D) : SoSRefutable (WPHP n r) D := by
  classical
  refine refutable_transfer (AlgHom.id ℝ _) (fun s => by simp [totalDegree_X]) (TFrame n r)
    (WPHP n r) (fun ik κ => if κ ∈ Classical.choose (tframe_eq_sum (r := r) ik.1 ik.2) then 1 else 0)
    (fun ik => tframe_deg_ge hr ik.1 ik.2) (fun κ => wphp_deg_le κ) ?_ D h
  intro ik
  obtain ⟨i, k⟩ := ik
  have := Classical.choose_spec (tframe_eq_sum (r := r) i k)
  simp only [AlgHom.id_apply]
  refine this.trans ?_
  simp [apply_ite C, ite_mul, Finset.sum_ite_mem]

theorem prop_1_10 {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ D : ℕ,
      (SoSRefutable (WRank r A) D →
        SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D) ∧
      (SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D →
        SoSRefutable (TFrame n r) D) ∧
      (SoSRefutable (TFrame n r) D → SoSRefutable (WPHP n r) D) :=
  fun D => ⟨part1 hr A D, part2 hr D, part3 hr D⟩

end SoSLinAlg.Dev.P110
end
end

section
namespace SoSLinAlg.WeakRank

theorem chk_proposition_1_10 {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    ∀ D : ℕ,
      (SoSRefutable (WRank r A) D →
        SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D) ∧
      (SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D →
        SoSRefutable (TFrame n r) D) ∧
      (SoSRefutable (TFrame n r) D → SoSRefutable (WPHP n r) D) :=
  SoSLinAlg.Dev.P110.prop_1_10 hr A

end SoSLinAlg.WeakRank
end

theorem solution : type_of% @SoSLinAlg.WeakRank.chk_proposition_1_10 := @SoSLinAlg.WeakRank.chk_proposition_1_10
