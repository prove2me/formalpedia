-- Prove2me | solution 1 for SoSLinAlg.WeakRank.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:34:43.36955+00:00
-- url     : https://prove2.me/submissions/3e1780fc-9d5f-416b-a32b-ab9b9711f458

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_Z

section
namespace SoSLinAlg.Dev.P41

open Finset

abbrev V (n q : ℕ) := (Fin n × Fin q) ⊕ (Fin n × Fin q)

def goodCol {n : ℕ} (u v : Fin n → ℕ) : Prop :=
  (u = 0 ∧ v = 0) ∨ ∃ i, u = Pi.single i 1 ∧ v = Pi.single i 1

def colU {n q : ℕ} (μ : V n q → ℕ) (a : Fin q) : Fin n → ℕ := fun i => μ (Sum.inl (i, a))
def colV {n q : ℕ} (μ : V n q → ℕ) (a : Fin q) : Fin n → ℕ := fun i => μ (Sum.inr (i, a))

def Good {n q : ℕ} (μ : V n q → ℕ) : Prop := ∀ a, goodCol (colU μ a) (colV μ a)

open Classical in
noncomputable def used {n q : ℕ} (μ : V n q → ℕ) : Finset (Fin q) :=
  univ.filter fun a => ¬ (colU μ a = 0 ∧ colV μ a = 0)

open Classical in
noncomputable def wf {n : ℕ} (q : ℕ) (μ : V n q → ℕ) : ℝ :=
  if Good μ then ((Nat.factorial (q - (used μ).card) : ℕ) : ℝ) / ((Nat.factorial q : ℕ) : ℝ) else 0

def bump {n q : ℕ} (i j : Fin n) (a : Fin q) : V n q → ℕ :=
  Pi.single (Sum.inl (i, a)) 1 + Pi.single (Sum.inr (j, a)) 1

theorem sum_single_nat {n : ℕ} (i : Fin n) : ∑ k, (Pi.single i 1 : Fin n → ℕ) k = 1 := by
  simp [Finset.sum_pi_single']

theorem goodCol_iff {n : ℕ} (u v : Fin n → ℕ) (i j : Fin n) :
    goodCol (u + Pi.single i 1) (v + Pi.single j 1) ↔ (u = 0 ∧ v = 0 ∧ i = j) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨i', h1, h2⟩)
    · have := congrFun h1 i
      simp at this
    · have s1 := congrArg (fun w => ∑ k, w k) h1
      have s2 := congrArg (fun w => ∑ k, w k) h2
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_single_nat] at s1 s2
      have hu : u = 0 := by
        funext k
        have : ∑ k, u k = 0 := by omega
        exact (Finset.sum_eq_zero_iff.mp this) k (Finset.mem_univ k)
      have hv : v = 0 := by
        funext k
        have : ∑ k, v k = 0 := by omega
        exact (Finset.sum_eq_zero_iff.mp this) k (Finset.mem_univ k)
      subst hu hv
      simp only [zero_add] at h1 h2
      have e1 := congrFun h1 i
      have e2 := congrFun h2 j
      have e3 := congrFun h1 i'
      have e4 := congrFun h2 i'
      simp only [Pi.single_apply] at e1 e2 e3 e4
      refine ⟨by simp, by simp, ?_⟩
      by_cases hi : i = i'
      · by_cases hj : j = i'
        · rw [hi, hj]
        · simp [hi.symm] at e4 e2
          exact e4
      · simp [hi] at e1
  · rintro ⟨rfl, rfl, rfl⟩
    right
    exact ⟨i, by simp, by simp⟩

theorem colU_bump_self {n q : ℕ} (μ : V n q → ℕ) (i j : Fin n) (a : Fin q) :
    colU (μ + bump i j a) a = colU μ a + Pi.single i 1 := by
  funext k
  simp [colU, bump, Pi.single_apply]

theorem colV_bump_self {n q : ℕ} (μ : V n q → ℕ) (i j : Fin n) (a : Fin q) :
    colV (μ + bump i j a) a = colV μ a + Pi.single j 1 := by
  funext k
  simp [colV, bump, Pi.single_apply]

theorem colU_bump_ne {n q : ℕ} (μ : V n q → ℕ) (i j : Fin n) {a b : Fin q} (h : b ≠ a) :
    colU (μ + bump i j a) b = colU μ b := by
  funext k
  simp [colU, bump, Pi.single_apply, h]

theorem colV_bump_ne {n q : ℕ} (μ : V n q → ℕ) (i j : Fin n) {a b : Fin q} (h : b ≠ a) :
    colV (μ + bump i j a) b = colV μ b := by
  funext k
  simp [colV, bump, Pi.single_apply, h]

theorem good_bump_iff {n q : ℕ} (μ : V n q → ℕ) (i j : Fin n) (a : Fin q) :
    Good (μ + bump i j a) ↔
      (colU μ a = 0 ∧ colV μ a = 0 ∧ i = j) ∧ ∀ b, b ≠ a → goodCol (colU μ b) (colV μ b) := by
  constructor
  · intro h
    refine ⟨?_, fun b hb => ?_⟩
    · have := h a
      rw [colU_bump_self, colV_bump_self, goodCol_iff] at this
      exact this
    · have := h b
      rwa [colU_bump_ne _ _ _ hb, colV_bump_ne _ _ _ hb] at this
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩ b
    by_cases hb : b = a
    · subst hb
      rw [colU_bump_self, colV_bump_self, goodCol_iff]
      exact ⟨h1, h2, h3⟩
    · rw [colU_bump_ne _ _ _ hb, colV_bump_ne _ _ _ hb]
      exact h4 b hb

theorem good_of_good_bump {n q : ℕ} {μ : V n q → ℕ} {i j : Fin n} {a : Fin q}
    (h : Good (μ + bump i j a)) : Good μ := by
  rw [good_bump_iff] at h
  intro b
  by_cases hb : b = a
  · subst hb
    left; exact ⟨h.1.1, h.1.2.1⟩
  · exact h.2 b hb

theorem used_bump {n q : ℕ} {μ : V n q → ℕ} {i j : Fin n} {a : Fin q}
    (h1 : colU μ a = 0) (h2 : colV μ a = 0) :
    used (μ + bump i j a) = insert a (used μ) := by
  classical
  ext b
  simp only [used, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hb : b = a
  · subst hb
    rw [colU_bump_self, colV_bump_self]
    simp [h1, h2]
  · rw [colU_bump_ne _ _ _ hb, colV_bump_ne _ _ _ hb]
    simp [hb]

theorem sum_eq_two_card {n q : ℕ} {μ : V n q → ℕ} (hg : Good μ) :
    ∑ x, μ x = 2 * (used μ).card := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type_right, Fintype.sum_prod_type_right,
    ← Finset.sum_add_distrib]
  have : ∀ a, (∑ i, μ (Sum.inl (i, a))) + (∑ i, μ (Sum.inr (i, a))) =
      if a ∈ used μ then 2 else 0 := by
    intro a
    have hu : (∑ i, μ (Sum.inl (i, a))) = ∑ i, colU μ a i := rfl
    have hv : (∑ i, μ (Sum.inr (i, a))) = ∑ i, colV μ a i := rfl
    rw [hu, hv]
    by_cases ha : a ∈ used μ
    · rw [if_pos ha]
      have ha' : ¬ (colU μ a = 0 ∧ colV μ a = 0) := by
        simpa [used] using ha
      rcases hg a with h | ⟨i, h1, h2⟩
      · exact absurd h ha'
      · rw [h1, h2, sum_single_nat]
    · rw [if_neg ha]
      have ha' : (colU μ a = 0 ∧ colV μ a = 0) := by
        simpa [used] using ha
      rw [ha'.1, ha'.2]; simp
  simp only [this]
  rw [← Finset.sum_filter, Finset.sum_const]
  have : (Finset.univ.filter fun a => a ∈ used μ) = used μ := by ext; simp
  rw [this]; simp [mul_comm]

theorem key {n q : ℕ} (hq : 0 < q) (μ : V n q → ℕ) (hμ : ∑ x, μ x ≤ 2 * q - 2) (i j : Fin n) :
    ∑ a, wf q (μ + bump i j a) = if i = j then wf q μ else 0 := by
  classical
  by_cases hg : Good μ
  · have hk : (used μ).card < q := by
      have := sum_eq_two_card hg
      omega
    have term : ∀ a, wf q (μ + bump i j a) =
        if (a ∉ used μ ∧ i = j) then ((Nat.factorial (q - (used μ).card - 1) : ℕ) : ℝ) / ((Nat.factorial q : ℕ) : ℝ) else 0 := by
      intro a
      unfold wf
      by_cases ha : a ∈ used μ
      · have ha' : ¬ (colU μ a = 0 ∧ colV μ a = 0) := by simpa [used] using ha
        have hb : ¬ Good (μ + bump i j a) := fun h =>
          ha' ⟨((good_bump_iff μ i j a).1 h).1.1, ((good_bump_iff μ i j a).1 h).1.2.1⟩
        rw [if_neg hb, if_neg (by simp [ha])]
      · have ha' : (colU μ a = 0 ∧ colV μ a = 0) := by simpa [used] using ha
        by_cases hij : i = j
        · have hgood : Good (μ + bump i j a) := by
            rw [good_bump_iff]
            exact ⟨⟨ha'.1, ha'.2, hij⟩, fun b _ => hg b⟩
          rw [if_pos hgood, if_pos ⟨ha, hij⟩, used_bump ha'.1 ha'.2,
            Finset.card_insert_of_notMem ha]
          congr 3
        · rw [if_neg, if_neg (by simp [hij])]
          intro h
          exact hij ((good_bump_iff μ i j a).1 h).1.2.2
    simp only [term]
    unfold wf
    rw [if_pos hg]
    by_cases hij : i = j
    · simp only [hij, and_true, if_true]
      rw [← Finset.sum_filter, Finset.sum_const]
      have : (Finset.univ.filter fun a => a ∉ used μ) = (used μ)ᶜ := by ext; simp
      rw [this, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]
      have e : ((Nat.factorial (q - (used μ).card) : ℕ) : ℝ) =
          ((q - (used μ).card : ℕ) : ℝ) * ((Nat.factorial (q - (used μ).card - 1) : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_factorial_pred (by omega)]
      rw [e]; ring
    · simp [hij]
  · have : ∀ a, wf q (μ + bump i j a) = 0 := by
      intro a
      unfold wf
      rw [if_neg]
      exact fun h => hg (good_of_good_bump h)
    simp only [this]
    unfold wf
    rw [if_neg hg]
    simp

end SoSLinAlg.Dev.P41
end

section
namespace SoSLinAlg.Dev.P41

open Finset MvPolynomial

abbrev T (n q : ℕ) := MvPolynomial (Option (V n q)) ℝ

noncomputable def wT {n : ℕ} (q D : ℕ) (m : Option (V n q) →₀ ℕ) : ℝ :=
  if m none = D then wf q (fun v => m (some v)) else 0

noncomputable def Lam {n : ℕ} (q D : ℕ) : T n q →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials (Option (V n q)) ℝ).constr ℝ (fun m => wT q D m)

theorem Lam_monomial {n : ℕ} (q D : ℕ) (m : Option (V n q) →₀ ℕ) (c : ℝ) :
    Lam q D (monomial m c) = c * wT q D m := by
  have : monomial m c = c • (MvPolynomial.basisMonomials (Option (V n q)) ℝ) m := by
    simp [MvPolynomial.coe_basisMonomials, smul_monomial]
  rw [this, map_smul, Lam, Module.Basis.constr_basis]
  simp

theorem degree_eq {n q : ℕ} (m : Option (V n q) →₀ ℕ) :
    (∑ o, m o) = m none + ∑ v, m (some v) := by
  rw [Fintype.sum_option]

theorem totalDegree_ge {n q : ℕ} {p : T n q} {m : Option (V n q) →₀ ℕ} (h : m ∈ p.support) :
    (∑ o, m o) ≤ p.totalDegree := by
  have := MvPolynomial.le_totalDegree h
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

theorem Lam_eq_zero_of_lt {n : ℕ} (q D : ℕ) (p : T n q) (hp : p.totalDegree < D) :
    Lam q D p = 0 := by
  rw [p.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Lam_monomial, wT]
  have h1 := totalDegree_ge hm
  have h2 := degree_eq m
  rw [if_neg (by omega)]
  simp

theorem Lam_bump {n q : ℕ} (D : ℕ) (m : Option (V n q) →₀ ℕ) (c : ℝ) (i j : Fin n) (a : Fin q) :
    Lam q D (monomial m c * (X (some (Sum.inl (i, a))) * X (some (Sum.inr (j, a))))) =
      c * (if m none = D then wf q ((fun v => m (some v)) + bump i j a) else 0) := by
  simp only [X, monomial_mul, Lam_monomial, wT]
  have h1 : ((m + (Finsupp.single (some (Sum.inl (i, a))) 1 + Finsupp.single (some (Sum.inr (j, a))) 1) : Option (V n q) →₀ ℕ)) none = m none := by
    simp
  have h2 : (fun v => (m + (Finsupp.single (some (Sum.inl (i, a))) 1 + Finsupp.single (some (Sum.inr (j, a))) 1) : Option (V n q) →₀ ℕ) (some v)) = (fun v => m (some v)) + bump i j a := by
    funext v
    simp [bump, Pi.single_apply, Finsupp.single_apply]
    simp only [@eq_comm _ (Sum.inl (i,a)) v, @eq_comm _ (Sum.inr (j,a)) v]
  rw [h1, h2]; ring

noncomputable def xyW {n : ℕ} (q : ℕ) (i j : Fin n) : T n q :=
  ∑ a : Fin q, X (some (Sum.inl (i, a))) * X (some (Sum.inr (j, a)))

theorem Lam_mul_xyW {n q : ℕ} (hq : 0 < q) (D : ℕ) (p : T n q)
    (hp : p.totalDegree + 2 ≤ D + 2 * q) (i j : Fin n) :
    Lam q D (p * xyW q i j) = if i = j then Lam q D p else 0 := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [Finset.sum_mul, map_sum]
  have : ∀ m ∈ p.support, Lam q D (monomial m (p.coeff m) * xyW q i j) =
      if i = j then Lam q D (monomial m (p.coeff m)) else 0 := by
    intro m hm
    have hd := totalDegree_ge hm
    have hdeg := degree_eq m
    unfold xyW
    rw [Finset.mul_sum, map_sum]
    simp only [Lam_bump, Lam_monomial, wT]
    rw [← Finset.mul_sum]
    by_cases hmn : m none = D
    · simp only [hmn, if_true]
      rw [key hq _ (by omega) i j]
      split_ifs <;> simp
    · simp [hmn]
  rw [Finset.sum_congr rfl this]
  by_cases hij : i = j
  · simp only [hij, if_true]
    rw [← map_sum, ← p.as_sum]
  · simp [hij]

theorem mulC_eq {n q : ℕ} (p : T n q) (c : ℝ) : p * C c = c • p := by
  rw [mul_comm, ← smul_eq_C_mul]

theorem Lam_mul_G {n q : ℕ} (D : ℕ) (p : T n q)
    (hp : p.totalDegree + 2 ≤ D + 2 * q) (i j : Fin n) :
    Lam q D (p * (xyW q i j - C ((1 : Matrix (Fin n) (Fin n) ℝ) i j))) = 0 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have h0 : Lam 0 D p = 0 := Lam_eq_zero_of_lt _ _ _ (by omega)
    have : xyW 0 i j = 0 := by simp [xyW]
    rw [this, zero_sub, mul_neg, map_neg, mulC_eq, map_smul, h0]
    simp
  · rw [mul_sub, map_sub, Lam_mul_xyW hq D p hp, mulC_eq, map_smul, Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij]

theorem wf_zero {n : ℕ} (q : ℕ) : wf (n := n) q (fun _ => 0) = 1 := by
  classical
  have hg : Good (n := n) (q := q) (fun _ => 0) := fun a => Or.inl ⟨rfl, rfl⟩
  have hu : used (n := n) (q := q) (fun _ => 0) = ∅ := by
    ext a; simp [used, colU, colV]; exact ⟨rfl, rfl⟩
  unfold wf
  rw [if_pos hg, hu]
  have : (Nat.factorial q : ℝ) ≠ 0 := by positivity
  simp [this]

theorem Lam_homog {n q : ℕ} (D : ℕ) (g : T n q) (hg : g.IsHomogeneous D) :
    Lam q D g = eval (fun o => if o = none then 1 else 0) g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hdeg : (∑ o, m o) = D := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm) (hg.coeff_eq_zero (by
      rwa [Finsupp.degree_eq_sum]))
  rw [Lam_monomial, wT, eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_option]
  have h2 := degree_eq m
  by_cases hs : ∀ v, m (some v) = 0
  · have : m none = D := by
      have : ∑ v, m (some v) = 0 := Finset.sum_eq_zero (fun v _ => hs v)
      omega
    simp only [this, if_true, hs, pow_zero, Finset.prod_const_one, mul_one, if_pos rfl]
    rw [wf_zero]; simp
  · obtain ⟨v, hv⟩ := not_forall.mp hs
    have : ∏ v, (if (some v : Option (V n q)) = none then (1:ℝ) else 0) ^ m (some v) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [hv]
    rw [this, mul_zero, mul_zero]
    have : m none ≠ D := by
      have : 0 < ∑ v, m (some v) := Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨v, Finset.mem_univ _, Nat.pos_of_ne_zero hv⟩
      omega
    rw [if_neg this]; simp

end SoSLinAlg.Dev.P41
end

section
namespace SoSLinAlg.Dev.P41

open Finset MvPolynomial SoSLinAlg.WeakRank

section
variable {n r q : ℕ}

noncomputable def psiVar (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ) :
    Var n r → T n q
  | Sum.inl (i, k) => X none * C (A i k) + ∑ a, X (some (Sum.inl (i, a))) * C (E a k)
  | Sum.inr (j, k) => X none * C (B j k) + ∑ a, X (some (Sum.inr (j, a))) * C (E a k)

noncomputable def psi (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ) :
    Poly n r →ₐ[ℝ] T n q :=
  aeval (psiVar A B E)

theorem psiVar_homog (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ)
    (v : Var n r) : (psiVar A B E v).IsHomogeneous 1 := by
  rcases v with ⟨i, k⟩ | ⟨j, k⟩
  · simp only [psiVar]
    apply IsHomogeneous.add
    · simpa using (isHomogeneous_X ℝ (none : Option (V n q))).mul (isHomogeneous_C _ (A i k))
    · apply IsHomogeneous.sum
      intro a _
      simpa using (isHomogeneous_X ℝ (some (Sum.inl (i, a)) : Option (V n q))).mul
        (isHomogeneous_C _ (E a k))
  · simp only [psiVar]
    apply IsHomogeneous.add
    · simpa using (isHomogeneous_X ℝ (none : Option (V n q))).mul (isHomogeneous_C _ (B j k))
    · apply IsHomogeneous.sum
      intro a _
      simpa using (isHomogeneous_X ℝ (some (Sum.inr (j, a)) : Option (V n q))).mul
        (isHomogeneous_C _ (E a k))

theorem psi_homog (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ)
    {p : Poly n r} {e : ℕ} (hp : p.IsHomogeneous e) : (psi A B E p).IsHomogeneous e := by
  have h := hp.aeval (psiVar A B E) (fun v => psiVar_homog A B E v)
  rw [one_mul] at h
  exact h

theorem psi_totalDegree (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ)
    (p : Poly n r) : (psi A B E p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro e he
  refine (psi_homog A B E (homogeneousComponent_isHomogeneous e p)).totalDegree_le.trans ?_
  have := Finset.mem_range.mp he
  omega

theorem eval_psi (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ)
    (p : Poly n r) :
    eval (fun o : Option (V n q) => if o = none then (1 : ℝ) else 0) (psi A B E p) =
      eval (assignment A B) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [psi]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    rcases v with ⟨i, k⟩ | ⟨j, k⟩ <;> simp [psi, psiVar, assignment]

theorem Lam_psi (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ)
    (p : Poly n r) (D : ℕ) (hp : p.totalDegree ≤ D) :
    Lam q D (psi A B E p) = eval (assignment A B) (homogeneousComponent D p) := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  rw [map_sum, map_sum]
  have : ∀ e ∈ range (p.totalDegree + 1), Lam q D (psi A B E (homogeneousComponent e p)) =
      if e = D then eval (assignment A B) (homogeneousComponent D p) else 0 := by
    intro e he
    have he' := Finset.mem_range.mp he
    by_cases hed : e = D
    · subst hed
      rw [if_pos rfl, Lam_homog _ _ (psi_homog A B E (homogeneousComponent_isHomogeneous e p)),
        eval_psi]
    · rw [if_neg hed]
      apply Lam_eq_zero_of_lt
      refine lt_of_le_of_lt (psi_homog A B E (homogeneousComponent_isHomogeneous e p)).totalDegree_le ?_
      omega
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero]
    · simp
    · have := Finset.mem_range.not.mp h
      omega


theorem bil_aux (s : T n q) (U W : Fin q → T n q) (α β : ℝ) (e e' : Fin q → ℝ) :
    (s * C α + ∑ a, U a * C (e a)) * (s * C β + ∑ b, W b * C (e' b)) =
      s * s * C (α * β) + s * ∑ b, W b * C (α * e' b)
        + s * ∑ a, U a * C (e a * β) + ∑ a, ∑ b, U a * W b * C (e a * e' b) := by
  have t1 : s * C α * (s * C β) = s * s * C (α * β) := by simp only [map_mul]; ring
  have t2 : s * C α * ∑ b, W b * C (e' b) = s * ∑ b, W b * C (α * e' b) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; simp only [map_mul]; ring
  have t3 : (∑ a, U a * C (e a)) * (s * C β) = s * ∑ a, U a * C (e a * β) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; simp only [map_mul]; ring
  have t4 : (∑ a, U a * C (e a)) * (∑ b, W b * C (e' b)) =
      ∑ a, ∑ b, U a * W b * C (e a * e' b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intros
    apply Finset.sum_congr rfl; intros
    simp only [map_mul]; ring
  rw [add_mul, mul_add, mul_add]
  linear_combination t1 + t2 + t3 + t4

theorem sumC_aux (W : Fin q → T n q) (f : Fin q → Fin r → ℝ) :
    ∑ k, ∑ b, W b * C (f b k) = ∑ b, W b * C (∑ k, f b k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intros
  rw [map_sum, Finset.mul_sum]

theorem sumC2_aux (U W : Fin q → T n q) (f : Fin q → Fin q → Fin r → ℝ) :
    ∑ k, ∑ a, ∑ b, U a * W b * C (f a b k) = ∑ a, ∑ b, U a * W b * C (∑ k, f a b k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [map_sum, Finset.mul_sum]

theorem psi_xy (A B : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin q) (Fin r) ℝ)
    (hAB : A * B.transpose = 0) (hAE : A * E.transpose = 0) (hBE : B * E.transpose = 0)
    (hEE : E * E.transpose = 1) (i j : Fin n) :
    psi A B E (xy i j) = xyW q i j := by
  have h1 : ∑ k, A i k * B j k = 0 := by
    have := congrFun (congrFun hAB i) j
    simpa [Matrix.mul_apply] using this
  have h2 : ∀ b, ∑ k, A i k * E b k = 0 := fun b => by
    have := congrFun (congrFun hAE i) b
    simpa [Matrix.mul_apply] using this
  have h3 : ∀ a, ∑ k, E a k * B j k = 0 := fun a => by
    have := congrFun (congrFun hBE j) a
    simpa [Matrix.mul_apply, mul_comm] using this
  have h4 : ∀ a b, ∑ k, E a k * E b k = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hEE a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [xy, x, y, map_sum, map_mul, psi, aeval_X, psiVar, xyW]
  simp only [bil_aux, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum, sumC_aux, sumC_aux,
    sumC2_aux (fun a => X (some (Sum.inl (i, a)))) (fun b => X (some (Sum.inr (j, b))))
      (fun a b k => E a k * E b k)]
  simp only [h1, h2, h3, h4]
  simp [apply_ite C]

end

end SoSLinAlg.Dev.P41
end

section
namespace SoSLinAlg.Dev.P41

open Finset Module

theorem exists_E {n r d : ℕ} (hd : d ≤ r) (A B : Matrix (Fin n) (Fin r) ℝ)
    (hrk : A.rank + B.rank ≤ d) :
    ∃ E : Matrix (Fin (r - d)) (Fin r) ℝ,
      A * E.transpose = 0 ∧ B * E.transpose = 0 ∧ E * E.transpose = 1 := by
  classical
  let fA : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin A
  let fB : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin B
  have hA : A.rank = finrank ℝ (LinearMap.range fA) := by
    rw [Matrix.rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin r) ℝ).toBasis]
    rfl
  have hB : B.rank = finrank ℝ (LinearMap.range fB) := by
    rw [Matrix.rank_eq_finrank_range_toLin B (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin r) ℝ).toBasis]
    rfl
  have h1 := LinearMap.finrank_range_add_finrank_ker fA
  have h2 := LinearMap.finrank_range_add_finrank_ker fB
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker fA) (LinearMap.ker fB)
  have h4 : finrank ℝ ↥(LinearMap.ker fA ⊔ LinearMap.ker fB) ≤ r := by
    have := Submodule.finrank_le (LinearMap.ker fA ⊔ LinearMap.ker fB)
    simpa using this
  simp only [finrank_euclideanSpace_fin] at h1 h2
  set K := LinearMap.ker fA ⊓ LinearMap.ker fB with hK
  have hle : r - d ≤ finrank ℝ K := by omega
  obtain ⟨vec, hvec, hon⟩ : ∃ vec : Fin (r - d) → EuclideanSpace ℝ (Fin r),
      (∀ a, vec a ∈ K) ∧ ∀ a c, inner ℝ (vec a) (vec c) = if a = c then (1 : ℝ) else 0 := by
    let b := stdOrthonormalBasis ℝ K
    refine ⟨fun a => ((b (Fin.castLE (by simpa using hle) a) : K) : EuclideanSpace ℝ (Fin r)),
      fun a => (b _).2, ?_⟩
    intro a c
    have := orthonormal_iff_ite.mp b.orthonormal (Fin.castLE (by simpa using hle) a)
      (Fin.castLE (by simpa using hle) c)
    simpa [Fin.castLE_inj] using this
  refine ⟨Matrix.of (fun a k => vec a k), ?_, ?_, ?_⟩
  · ext i a
    have := (Submodule.mem_inf.mp (hvec a)).1
    rw [LinearMap.mem_ker] at this
    have := congrFun (congrArg (fun w => (w : EuclideanSpace ℝ (Fin n)).ofLp) this) i
    simp [fA, Matrix.mulVec, dotProduct, Matrix.mul_apply] at this ⊢
    simpa [mul_comm] using this
  · ext i a
    have := (Submodule.mem_inf.mp (hvec a)).2
    rw [LinearMap.mem_ker] at this
    have := congrFun (congrArg (fun w => (w : EuclideanSpace ℝ (Fin n)).ofLp) this) i
    simp [fB, Matrix.mulVec, dotProduct, Matrix.mul_apply] at this ⊢
    simpa [mul_comm] using this
  · ext a c
    have := hon a c
    have e : inner ℝ (vec a) (vec c) = ∑ k, vec a k * vec c k := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_eq_re_inner]
      simp [mul_comm]
    rw [e] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    exact this

end SoSLinAlg.Dev.P41
end

section
namespace SoSLinAlg.WeakRank

open SoSLinAlg.Dev.P41 in
theorem chk_proposition_4_1 {n r d : ℕ} (hr : 0 < r) (hrn : r < n) (hdr : d ≤ r)
    (f : Poly n r) (hf : f.totalDegree ≤ 2 * d)
    (h : (Fin n × Fin n) → Poly n r)
    (hdeg : ∀ ij, (h ij).totalDegree ≤ 2 * r - 2)
    (hrep : f = ∑ ij, h ij * WRank r (1 : Matrix (Fin n) (Fin n) ℝ) ij) :
    VanishesOnZ d (MvPolynomial.homogeneousComponent (2 * d) f) := by
  intro X Y hZ
  obtain ⟨hXY, hrk⟩ := hZ
  simp only at hXY hrk
  obtain ⟨E, hXE, hYE, hEE⟩ := exists_E hdr X Y hrk
  have hψ : psi X Y E f = ∑ ij, psi X Y E (h ij) *
      (xyW (r - d) ij.1 ij.2 - MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2)) := by
    conv_lhs => rw [hrep]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ij _
    rw [map_mul, WRank, map_sub, psi_xy X Y E hXY hXE hYE hEE]
    congr 2
    simp [psi]
  have h0 : Lam (r - d) (2 * d) (psi X Y E f) = 0 := by
    rw [hψ, map_sum]
    apply Finset.sum_eq_zero
    intro ij _
    apply Lam_mul_G
    have := psi_totalDegree X Y E (h ij)
    have := hdeg ij
    omega
  rw [Lam_psi X Y E f (2 * d) hf] at h0
  exact h0

end SoSLinAlg.WeakRank
end

theorem solution : type_of% @SoSLinAlg.WeakRank.chk_proposition_4_1 := @SoSLinAlg.WeakRank.chk_proposition_4_1
