-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P01.generallyCoupled_normalized_and_M_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:40:47.988071+00:00
-- url     : https://prove2.me/submissions/90fb1f01-c086-459a-8240-bb24ca87a5cf

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

lemma g64i_pi {k : ℕ} {κ : Fin k → Type} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    ∑ x : (∀ i, κ i), ∏ i, f i (x i) = ∏ i, ∑ y, f i y := (Fintype.prod_sum f).symm

lemma g64i_orth (K : ℕ) : ∀ (t : CouplingTree) (A : CouplingData t), CouplingValid t A K →
    ∀ M N : Fin t.rootDim,
      (∑ x : t.Config, star (coupledAmplitude t A M x) * coupledAmplitude t A N x) =
        if M = N then 1 else 0 := by
  intro t
  induction t with
  | leaf p d => intro A h M N; exact h.2 M N
  | node d k children ih =>
    intro A h M N
    obtain ⟨_, _, hc, hA⟩ := h
    have key : ∀ m n : (i : Fin k) → Fin (children i).rootDim,
        (∑ x : ((i : Fin k) → (children i).Config), ∏ i, (star (coupledAmplitude (children i)
          (A.2 i) (m i) (x i)) * coupledAmplitude (children i) (A.2 i) (n i) (x i))) =
          if m = n then 1 else 0 := by
      intro m n
      refine (g64i_pi (fun i y => star (coupledAmplitude (children i) (A.2 i) (m i) y) *
        coupledAmplitude (children i) (A.2 i) (n i) y)).trans ?_
      rw [Finset.prod_congr rfl fun i _ => ih i (A.2 i) (hc i) (m i) (n i)]
      by_cases hmn : m = n
      · subst hmn; simp
      · rw [if_neg hmn]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    have e1 : ∀ x : (CouplingTree.node d k children).Config,
        star (coupledAmplitude (CouplingTree.node d k children) A M x) *
          coupledAmplitude (CouplingTree.node d k children) A N x =
        ∑ m, ∑ n, (star (A.1 M m) * A.1 N n) * ∏ i, (star (coupledAmplitude (children i)
          (A.2 i) (m i) (x i)) * coupledAmplitude (children i) (A.2 i) (n i) (x i)) := by
      intro x
      simp only [coupledAmplitude, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum,
        Finset.prod_mul_distrib, star_prod]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      ring
    calc (∑ x : (CouplingTree.node d k children).Config,
          star (coupledAmplitude (CouplingTree.node d k children) A M x) *
            coupledAmplitude (CouplingTree.node d k children) A N x)
        = ∑ x : ((i : Fin k) → (children i).Config), ∑ m, ∑ n, (star (A.1 M m) * A.1 N n) *
            ∏ i, (star (coupledAmplitude (children i) (A.2 i) (m i) (x i)) *
              coupledAmplitude (children i) (A.2 i) (n i) (x i)) := by
          rw [Finset.sum_congr rfl fun x _ => e1 x]; rfl
      _ = ∑ m, ∑ n, (star (A.1 M m) * A.1 N n) * (if m = n then 1 else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← Finset.mul_sum, key]
      _ = if M = N then 1 else 0 := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          exact hA M N

theorem solution
    (K : ℕ) (t : CouplingTree) (A : CouplingData t) (h : CouplingValid t A K) :
    (∀ M N : Fin t.rootDim,
      (∑ x : t.Config, star (coupledAmplitude t A M x) * coupledAmplitude t A N x) =
        if M = N then 1 else 0) ∧
      (∀ M : Fin t.rootDim, IsState (coupledState t A M)) := by
  refine ⟨g64i_orth K t A h, fun M => ?_⟩
  have h1 := g64i_orth K t A h M M
  rw [if_pos rfl] at h1
  unfold IsState coupledState
  rw [EuclideanSpace.norm_eq]
  have h2 : (∑ x, ‖coupledAmplitude t A M x‖ ^ 2 : ℝ) = 1 := by
    have : ((∑ x, ‖coupledAmplitude t A M x‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]; push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    exact_mod_cast this
  simp [h2]

end
