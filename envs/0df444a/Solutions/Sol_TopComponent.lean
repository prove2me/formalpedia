-- Prove2me | solution 1 for TopComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:48:36.132455+00:00
-- url     : https://prove2.me/submissions/d6aaad54-1d01-45ea-bda3-8c1d6b029ec7

module
public import Definitions.Def_PHarmonicPoly_EpAlgHomogeneous
public import Definitions.Def_PHarmonicPoly_TotalDegreePDeriv
public import Definitions.Def_PHarmonicPoly_TopComponent
public import Theorems.Thm_EpAlgHomogeneous
public import Theorems.Thm_TotalDegreePDeriv


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (p : ℝ) {P : MvPolynomial (Fin n) ℝ}
    (hm : 2 ≤ P.totalDegree) (hE : EpAlg p P = 0) :
    EpAlg p (homogeneousComponent P.totalDegree P) = 0 := by
  classical
  have hpos : ∀ (η : MvPolynomial (Fin n) ℝ) (b : Fin n),
      pderiv b η ≠ 0 → 1 ≤ η.totalDegree := by
    intro η b hb
    by_contra h
    have h0 : η.totalDegree = 0 := by omega
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0] at hb
    simp at hb
  have hd1 : ∀ (φ : MvPolynomial (Fin n) ℝ) (D : ℕ), φ.totalDegree ≤ D →
      ∀ a : Fin n, (pderiv a φ).totalDegree ≤ D - 1 := by
    intro φ D hD a
    exact le_trans (TotalDegreePDeriv a φ) (by omega)
  have hdisj : ∀ (φ : MvPolynomial (Fin n) ℝ) (D : ℕ), φ.totalDegree ≤ D →
      ∀ a c : Fin n, pderiv a (pderiv c φ) = 0
        ∨ (pderiv a (pderiv c φ)).totalDegree + 2 ≤ D := by
    intro φ D hD a c
    by_cases hx : pderiv a (pderiv c φ) = 0
    · exact Or.inl hx
    refine Or.inr ?_
    have hpsi : pderiv c φ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx
      exact hx rfl
    have h1 : 1 ≤ (pderiv c φ).totalDegree := hpos _ a hx
    have h2 : 1 ≤ φ.totalDegree := hpos _ c hpsi
    have h3 := TotalDegreePDeriv c φ
    have h4 := TotalDegreePDeriv a (pderiv c φ)
    omega
  have h3fac : ∀ (F G H : MvPolynomial (Fin n) ℝ) (a b c : ℕ),
      F.totalDegree ≤ a → G.totalDegree ≤ b → H.totalDegree ≤ c →
      (F * G * H).totalDegree ≤ a + b + c := by
    intro F G H a b c hF hG hH
    have k1 := MvPolynomial.totalDegree_mul (F * G) H
    have k2 := MvPolynomial.totalDegree_mul F G
    omega
  have haddle : ∀ (F G : MvPolynomial (Fin n) ℝ) (a : ℕ),
      F.totalDegree ≤ a → G.totalDegree ≤ a → (F + G).totalDegree ≤ a := by
    intro F G a hF hG
    exact le_trans (MvPolynomial.totalDegree_add F G) (max_le hF hG)
  have main : ∀ (M : ℕ) (Q R : MvPolynomial (Fin n) ℝ), 2 ≤ M →
      Q.totalDegree ≤ M → R.totalDegree ≤ M - 1 →
      (EpAlg p (Q + R) - EpAlg p Q).totalDegree ≤ 3 * M - 5 := by
    intro M Q R hM hQ hR
    have dQ1 : ∀ i : Fin n, (pderiv i Q).totalDegree ≤ M - 1 := hd1 Q M hQ
    have dR1 : ∀ i : Fin n, (pderiv i R).totalDegree ≤ M - 2 := by
      intro i
      have h := hd1 R (M - 1) hR i
      omega
    have dQ2 : ∀ a c : Fin n, (pderiv a (pderiv c Q)).totalDegree ≤ M - 2 := by
      intro a c
      have h := hd1 (pderiv c Q) (M - 1) (dQ1 c) a
      omega
    have dR2 : ∀ a c : Fin n, (pderiv a (pderiv c R)).totalDegree ≤ M - 2 := by
      intro a c
      have h := hd1 (pderiv c R) (M - 2) (dR1 c) a
      omega
    have dR2d : ∀ a c : Fin n, pderiv a (pderiv c R) = 0
        ∨ (pderiv a (pderiv c R)).totalDegree + 2 ≤ M - 1 := hdisj R (M - 1) hR
    have dsum1 : ∀ i : Fin n, (pderiv i Q + pderiv i R).totalDegree ≤ M - 1 := by
      intro i
      refine haddle _ _ _ (dQ1 i) ?_
      have h := dR1 i
      omega
    have hpa : ∀ i : Fin n, pderiv i (Q + R) = pderiv i Q + pderiv i R := by
      intro i
      rw [map_add]
    have hT1 : (∑ i, (pderiv i Q + pderiv i R) ^ 2)
          * (∑ k, (pderiv k (pderiv k Q) + pderiv k (pderiv k R)))
        - (∑ i, (pderiv i Q) ^ 2) * (∑ k, pderiv k (pderiv k Q))
        = ∑ i, ∑ k, ((pderiv i R) * ((pderiv i Q + pderiv i R) + pderiv i Q)
              * (pderiv k (pderiv k Q) + pderiv k (pderiv k R))
            + (pderiv i Q) * (pderiv i Q) * (pderiv k (pderiv k R))) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hT2 : (∑ i, ∑ j, (pderiv i (pderiv j Q) + pderiv i (pderiv j R))
            * (pderiv i Q + pderiv i R) * (pderiv j Q + pderiv j R))
        - (∑ i, ∑ j, pderiv i (pderiv j Q) * pderiv i Q * pderiv j Q)
        = ∑ i, ∑ j, ((pderiv i (pderiv j R)) * (pderiv i Q + pderiv i R)
              * (pderiv j Q + pderiv j R)
            + (pderiv i (pderiv j Q)) * (pderiv i R) * (pderiv j Q + pderiv j R)
            + (pderiv i (pderiv j Q)) * (pderiv i Q) * (pderiv j R)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hdiff : EpAlg p (Q + R) - EpAlg p Q
        = (∑ i, ∑ k, ((pderiv i R) * ((pderiv i Q + pderiv i R) + pderiv i Q)
              * (pderiv k (pderiv k Q) + pderiv k (pderiv k R))
            + (pderiv i Q) * (pderiv i Q) * (pderiv k (pderiv k R))))
          + MvPolynomial.C (p - 2) * (∑ i, ∑ j,
            ((pderiv i (pderiv j R)) * (pderiv i Q + pderiv i R)
                * (pderiv j Q + pderiv j R)
              + (pderiv i (pderiv j Q)) * (pderiv i R) * (pderiv j Q + pderiv j R)
              + (pderiv i (pderiv j Q)) * (pderiv i Q) * (pderiv j R))) := by
      simp only [EpAlg, hpa, map_add]
      linear_combination hT1 + MvPolynomial.C (p - 2) * hT2
    rw [hdiff]
    refine haddle _ _ _ ?_ ?_
    · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _)
        (Finset.sup_le (fun i _ => ?_))
      refine le_trans (MvPolynomial.totalDegree_finsetSum _ _)
        (Finset.sup_le (fun k _ => ?_))
      refine haddle _ _ _ ?_ ?_
      · refine le_trans (h3fac _ _ _ (M - 2) (M - 1) (M - 2) (dR1 i)
          (haddle _ _ _ (dsum1 i) (dQ1 i))
          (haddle _ _ _ (dQ2 k k) (dR2 k k))) (by omega)
      · rcases dR2d k k with h | h
        · simp [h]
        · exact le_trans (h3fac _ _ _ (M - 1) (M - 1)
            ((pderiv k (pderiv k R)).totalDegree) (dQ1 i) (dQ1 i) le_rfl) (by omega)
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine le_trans (MvPolynomial.totalDegree_finsetSum _ _)
        (Finset.sup_le (fun i _ => ?_))
      refine le_trans (MvPolynomial.totalDegree_finsetSum _ _)
        (Finset.sup_le (fun j _ => ?_))
      refine haddle _ _ _ (haddle _ _ _ ?_ ?_) ?_
      · rcases dR2d i j with h | h
        · simp [h]
        · exact le_trans (h3fac _ _ _ ((pderiv i (pderiv j R)).totalDegree)
            (M - 1) (M - 1) le_rfl (dsum1 i) (dsum1 j)) (by omega)
      · exact le_trans (h3fac _ _ _ (M - 2) (M - 2) (M - 1)
          (dQ2 i j) (dR1 i) (dsum1 j)) (by omega)
      · exact le_trans (h3fac _ _ _ (M - 2) (M - 1) (M - 2)
          (dQ2 i j) (dQ1 i) (dR1 j)) (by omega)
  have hPmhom : (homogeneousComponent P.totalDegree P).IsHomogeneous P.totalDegree :=
    MvPolynomial.homogeneousComponent_isHomogeneous _ _
  have hPmdeg : (homogeneousComponent P.totalDegree P).totalDegree ≤ P.totalDegree :=
    hPmhom.totalDegree_le
  have hrdeg : (P - homogeneousComponent P.totalDegree P).totalDegree
      ≤ P.totalDegree - 1 := by
    have hsum := MvPolynomial.sum_homogeneousComponent P
    rw [Finset.sum_range_succ] at hsum
    have hr : P - homogeneousComponent P.totalDegree P
        = ∑ d ∈ Finset.range P.totalDegree, homogeneousComponent d P :=
      (eq_sub_of_add_eq hsum).symm
    rw [hr]
    refine le_trans (MvPolynomial.totalDegree_finsetSum _ _)
      (Finset.sup_le (fun d hd => ?_))
    have hdd := Finset.mem_range.mp hd
    exact le_trans (MvPolynomial.homogeneousComponent_isHomogeneous d P).totalDegree_le
      (by omega)
  have hsplitP : P = homogeneousComponent P.totalDegree P
      + (P - homogeneousComponent P.totalDegree P) := by ring
  have hMdeg := main P.totalDegree (homogeneousComponent P.totalDegree P)
    (P - homogeneousComponent P.totalDegree P) hm hPmdeg hrdeg
  rw [← hsplitP] at hMdeg
  have hcomp : EpAlg p (homogeneousComponent P.totalDegree P)
      = homogeneousComponent (3 * P.totalDegree - 4) (EpAlg p P) := by
    rw [show EpAlg p P = EpAlg p (homogeneousComponent P.totalDegree P)
          + (EpAlg p P - EpAlg p (homogeneousComponent P.totalDegree P)) from by ring,
      map_add,
      MvPolynomial.homogeneousComponent_eq_zero (3 * P.totalDegree - 4)
        (EpAlg p P - EpAlg p (homogeneousComponent P.totalDegree P)) (by omega),
      add_zero,
      MvPolynomial.homogeneousComponent_eq_self (EpAlgHomogeneous p hm hPmhom)]
  rw [hcomp, hE, map_zero]
