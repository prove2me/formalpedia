-- Prove2me | solution 1 for VanderbeiLP.StrictComp.separation_polyhedra
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T19:00:42.617536+00:00
-- url     : https://prove2.me/submissions/214ce90d-d400-4796-be75-78ba5a05ebf2

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_Polyhedron
import Theorems.Thm_VanderbeiLP_StrictComp_farkas_lemma

open Matrix


namespace VanderbeiLP.StrictComp
open Matrix Set
noncomputable section

-- Reindex finite rows, then use only the public accepted Farkas theorem.
lemma sc_farkas_rows {ι : Type} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ)
    (h : ¬ ∃ x, A *ᵥ x ≤ b) :
    ∃ y : ι → ℝ, 0 ≤ y ∧ Aᵀ *ᵥ y=0 ∧ b ⬝ᵥ y < 0 := by
  classical
  let e := Fintype.equivFin ι
  let AF : Matrix (Fin (Fintype.card ι)) (Fin n) ℝ := fun i j => A (e.symm i) j
  let bf : Fin (Fintype.card ι) → ℝ := fun i => b (e.symm i)
  have hn : ¬ ∃ x, AF *ᵥ x ≤ bf := by
    rintro ⟨x,hx⟩
    apply h
    refine ⟨x,fun i => ?_⟩
    simpa [AF,bf,mulVec,dotProduct] using hx (e i)
  obtain ⟨y,hy1,hy0,hy2⟩ := (farkas_lemma AF bf).mp hn
  refine ⟨fun i => y (e i),fun i => hy0 (e i),?_,?_⟩
  · ext j
    change (∑ i, A i j*y (e i))=0
    have hs : (∑ i, A i j*y (e i))=∑ k, AF k j*y k :=
      Fintype.sum_equiv e _ _ (fun i => by simp [AF])
    rw [hs]
    simpa [mulVec,dotProduct] using congrFun hy1 j
  · change (∑ i, b i*y (e i)) < 0
    have hs : (∑ i, b i*y (e i))=∑ k, bf k*y k :=
      Fintype.sum_equiv e _ _ (fun i => by simp [bf])
    rw [hs]
    exact hy2

lemma sc_weighted_bound {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (b y : ι → ℝ) (x : κ → ℝ)
    (hy : 0 ≤ y) (hx : A *ᵥ x ≤ b) :
    (Aᵀ *ᵥ y) ⬝ᵥ x ≤ b ⬝ᵥ y := by
  calc (Aᵀ *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (A *ᵥ x) := by
        rw [dotProduct_comm,dotProduct_transpose_mulVec]
    _ ≤ y ⬝ᵥ b := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy i)
    _ = b ⬝ᵥ y := dotProduct_comm _ _

lemma sc_separation_polyhedra {n : ℕ} (P Q : Set (Fin n → ℝ))
    (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hPne : P.Nonempty) (hQne : Q.Nonempty) (hdisj : Disjoint P Q) :
    ∃ H K : Set (Fin n → ℝ), IsHalfspace H ∧ IsHalfspace K ∧ Disjoint H K ∧
      P ⊆ H ∧ Q ⊆ K := by
  rcases hP with ⟨m,A,b,rfl⟩
  rcases hQ with ⟨r,C,d,rfl⟩
  let B : Matrix (Fin m ⊕ Fin r) (Fin n) ℝ := Sum.elim A C
  let e : Fin m ⊕ Fin r → ℝ := Sum.elim b d
  have hnone : ¬ ∃ x, B *ᵥ x ≤ e := by
    rintro ⟨x,hx⟩
    have hxA : A *ᵥ x ≤ b := fun i => hx (Sum.inl i)
    have hxC : C *ᵥ x ≤ d := fun i => hx (Sum.inr i)
    exact Set.disjoint_left.mp hdisj hxA hxC
  obtain ⟨y,hy0,hy1,hy2⟩ := sc_farkas_rows B e hnone
  let u : Fin m → ℝ := fun i => y (Sum.inl i)
  let v : Fin r → ℝ := fun i => y (Sum.inr i)
  let a := Aᵀ *ᵥ u
  have hu : 0 ≤ u := fun i => hy0 (Sum.inl i)
  have hv : 0 ≤ v := fun i => hy0 (Sum.inr i)
  have hcoeff : Cᵀ *ᵥ v= -a := by
    ext j
    have hs := congrFun hy1 j
    change (∑ i : Fin m ⊕ Fin r, B i j*y i)=0 at hs
    rw [Fintype.sum_sum_type] at hs
    change (∑ i, A i j*y (Sum.inl i))+(∑ i, C i j*y (Sum.inr i))=0 at hs
    change (∑ i, C i j*v i)= -(∑ i, A i j*u i)
    dsimp [u,v] at hs ⊢
    linarith
  have hneg : b ⬝ᵥ u+d ⬝ᵥ v < 0 := by
    simpa [dotProduct,Fintype.sum_sum_type,e,u,v] using hy2
  have ha : a ≠ 0 := by
    intro ha
    obtain ⟨x,hx⟩ := hPne
    obtain ⟨z,hz⟩ := hQne
    have hb := sc_weighted_bound A b u x hu hx
    have hd := sc_weighted_bound C d v z hv hz
    change a ⬝ᵥ x ≤ b ⬝ᵥ u at hb
    rw [ha,zero_dotProduct] at hb
    rw [hcoeff,ha,neg_zero,zero_dotProduct] at hd
    linarith
  refine ⟨{x | a ⬝ᵥ x ≤ b ⬝ᵥ u},{x | (-a) ⬝ᵥ x ≤ d ⬝ᵥ v},
    ⟨a,b ⬝ᵥ u,ha,rfl⟩,⟨-a,d ⬝ᵥ v,neg_ne_zero.mpr ha,rfl⟩,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hx'
    change a ⬝ᵥ x ≤ b ⬝ᵥ u at hx
    change (-a) ⬝ᵥ x ≤ d ⬝ᵥ v at hx'
    rw [neg_dotProduct] at hx'
    linarith
  · intro x hx
    exact sc_weighted_bound A b u x hu hx
  · intro x hx
    have h := sc_weighted_bound C d v x hv hx
    rwa [hcoeff] at h

end
end VanderbeiLP.StrictComp

open VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 10.4 (p. 145), Separation Theorem for polyhedra.** Two disjoint
nonempty polyhedra `P`, `P̃` of `ℝⁿ` lie in disjoint halfspaces `H ⊇ P`, `H̃ ⊇ P̃`
(halfspaces in the sense of (10.3): nonzero normal). -/
theorem solution {n : ℕ} (P Ptil : Set (Fin n → ℝ))
    (hP : IsPolyhedron P) (hPtil : IsPolyhedron Ptil)
    (hPne : P.Nonempty) (hPtilne : Ptil.Nonempty) (hdisj : Disjoint P Ptil) :
    ∃ H Htil : Set (Fin n → ℝ), IsHalfspace H ∧ IsHalfspace Htil ∧ Disjoint H Htil ∧
      P ⊆ H ∧ Ptil ⊆ Htil := by
  exact sc_separation_polyhedra P Ptil hP hPtil hPne hPtilne hdisj

#print axioms solution
