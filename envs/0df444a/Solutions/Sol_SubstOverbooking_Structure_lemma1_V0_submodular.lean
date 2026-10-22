-- Prove2me | solution 1 for SubstOverbooking.Structure.lemma1_V0_submodular
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T17:54:22.658368+00:00
-- url     : https://prove2.me/submissions/b89b4b77-5ba7-4b23-ae1e-06289a02c1d9

import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
set_option autoImplicit false

namespace MiaoConcavity
open SubstOverbooking.Structure
open scoped BigOperators

theorem feasible_nonempty {n m : ℕ} (c : Fin (m + 1) → ℝ)
    (z : Fin n → ℝ) (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (hz : ∀ i, 0 ≤ z i) :
    Set.Nonempty {y | IsTPFeasible c z y} := by
  classical
  refine ⟨fun i j => if j = 0 then z i else 0, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    dsimp
    split_ifs <;> simp [hz]
  · intro i
    simp
  · intro j hj
    simpa [hj] using hc j hj

theorem feasible_compact {n m : ℕ} (c : Fin (m + 1) → ℝ)
    (z : Fin n → ℝ) : IsCompact {y | IsTPFeasible c z y} := by
  have hclosed : IsClosed {y | IsTPFeasible c z y} := by
    unfold IsTPFeasible
    simp only [Set.setOf_and, Set.setOf_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (show Continuous (fun y : Fin n → Fin (m + 1) → ℝ => y i j) by fun_prop)).inter
      ((isClosed_iInter fun i => isClosed_eq
        (show Continuous (fun y : Fin n → Fin (m + 1) → ℝ => ∑ j, y i j) by fun_prop) continuous_const).inter
        (isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_le (show Continuous (fun y : Fin n → Fin (m + 1) → ℝ => ∑ i, y i j) by fun_prop) continuous_const))
  apply (isCompact_Icc (a := (0 : Fin n → Fin (m + 1) → ℝ))
    (b := fun i _ => z i)).of_isClosed_subset hclosed
  intro y hy
  refine ⟨hy.1, ?_⟩
  intro i j
  have := Finset.single_le_sum (fun k _ => hy.1 i k) (Finset.mem_univ j)
  simpa [hy.2.1 i] using this

theorem objective_continuous {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) :
    Continuous (tpObjective a) := by
  unfold tpObjective
  fun_prop

theorem optimum {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (hz : ∀ i, 0 ≤ z i) :
    ∃ y, IsTPFeasible c z y ∧ tpObjective a y = V0 a c z := by
  obtain ⟨y, hy, he⟩ := (feasible_compact c z).exists_sSup_image_eq
    (feasible_nonempty c z hc hz) (objective_continuous a).continuousOn
  exact ⟨y, hy, he.symm⟩

theorem objective_le_value {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ)
    (y : Fin n → Fin (m + 1) → ℝ) (hy : IsTPFeasible c z y) :
    tpObjective a y ≤ V0 a c z := by
  exact le_csSup ((feasible_compact c z).bddAbove_image
    (objective_continuous a).continuousOn) ⟨y, hy, rfl⟩

theorem combine_feasible {n m : ℕ}
    (c d : Fin (m + 1) → ℝ) (z w : Fin n → ℝ)
    (y v : Fin n → Fin (m + 1) → ℝ)
    (hy : IsTPFeasible c z y) (hv : IsTPFeasible d w v)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    IsTPFeasible (α • c + β • d) (α • z + β • w) (α • y + β • v) := by
  refine ⟨fun i j => add_nonneg (mul_nonneg hα (hy.1 i j))
    (mul_nonneg hβ (hv.1 i j)), ?_, ?_⟩
  · intro i
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hy.2.1 i, hv.2.1 i]
  · intro j hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left (hy.2.2 j hj) hα)
      (mul_le_mul_of_nonneg_left (hv.2.2 j hj) hβ)

theorem combine_objective {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (y v : Fin n → Fin (m + 1) → ℝ) (α β : ℝ) :
    tpObjective a (α • y + β • v) = α * tpObjective a y + β * tpObjective a v := by
  simp only [tpObjective, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  simp_rw [mul_left_comm (a _ _) α, mul_left_comm (a _ _) β]
  simp_rw [← Finset.mul_sum]

open SubstOverbooking.Structure

theorem prior_concavity {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) :
    (∀ c : Fin (m + 1) → ℝ, (∀ j, j ≠ 0 → 0 ≤ c j) →
      ConcaveOn ℝ {z : Fin n → ℝ | ∀ i, 0 ≤ z i} (fun z => V0 a c z)) ∧
    (∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) →
      ConcaveOn ℝ {c : Fin (m + 1) → ℝ | ∀ j, j ≠ 0 → 0 ≤ c j} (fun c => V0 a c z)) := by
  constructor
  · intro c hc
    refine ⟨?_, ?_⟩
    · intro z hz w hw α β hα hβ hab i
      exact add_nonneg (mul_nonneg hα (hz i)) (mul_nonneg hβ (hw i))
    · intro z hz w hw α β hα hβ hab
      obtain ⟨y, hy, ey⟩ := optimum a c z hc hz
      obtain ⟨v, hv, ev⟩ := optimum a c w hc hw
      have hf := combine_feasible c c z w y v hy hv α β hα hβ
      rw [← add_smul, hab, one_smul] at hf
      have h := objective_le_value a c _ _ hf
      simpa [combine_objective, ey, ev, smul_eq_mul] using h
  · intro z hz
    refine ⟨?_, ?_⟩
    · intro c hc d hd α β hα hβ hab j hj
      exact add_nonneg (mul_nonneg hα (hc j hj)) (mul_nonneg hβ (hd j hj))
    · intro c hc d hd α β hα hβ hab
      obtain ⟨y, hy, ey⟩ := optimum a c z hc hz
      obtain ⟨v, hv, ev⟩ := optimum a d z hd hz
      have hf := combine_feasible c d z z y v hy hv α β hα hβ
      rw [← add_smul, hab, one_smul] at hf
      have h := objective_le_value a _ z _ hf
      simpa [combine_objective, ey, ev, smul_eq_mul] using h

#print axioms prior_concavity

end MiaoConcavity
open SubstOverbooking.Structure
namespace OverbookingResearch
lemma weak_duality {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ) (c : Fin (m+1) → ℝ)
    (z : Fin n → ℝ) (y : Fin n → Fin (m+1) → ℝ) (hy : IsTPFeasible c z y)
    (u : Fin n → ℝ) (l : Fin (m+1) → ℝ) (hd : IsDTPFeasible a u l) :
    tpObjective a y ≤ dtpObjective c z u l := by
  have h1 : tpObjective a y ≤ ∑ i, ∑ j, (u i+l j)*y i j := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hd.2.2 i j) (hy.1 i j)
  have he : (∑ i,∑ j,(u i+l j)*y i j) =
      (∑ i,z i*u i)+(∑ j,l j*∑ i,y i j) := by
    simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum,hy.2.1]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h2 : (∑ j,l j*∑ i,y i j) ≤ ∑ j,c j*l j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hj0 : j=0
    · subst j;simp [hd.1]
    · have h := mul_le_mul_of_nonneg_left (hy.2.2 j hj0) (hd.2.1 j)
      simpa only [mul_comm] using h
  rw [he] at h1
  exact h1.trans (add_le_add_right h2 _)
lemma value_le_dual {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ) (c : Fin (m+1) → ℝ)
    (hc : ∀ j,j≠0 → 0≤c j) (z : Fin n → ℝ) (hz : ∀ i,0≤z i)
    (u : Fin n → ℝ) (l : Fin (m+1) → ℝ) (hd : IsDTPFeasible a u l) :
    V0 a c z ≤ dtpObjective c z u l := by
  obtain ⟨y,hy,he⟩ := MiaoConcavity.optimum a c z hc hz
  rw [← he]
  exact weak_duality a c z y hy u l hd
lemma dual_uncross {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ)
    (u v : Fin n → ℝ) (l k : Fin (m+1) → ℝ)
    (h1 : IsDTPFeasible a u l) (h2 : IsDTPFeasible a v k) :
    IsDTPFeasible a (u ⊓ v) (l ⊔ k) ∧ IsDTPFeasible a (u ⊔ v) (l ⊓ k) := by
  constructor
  · refine ⟨by simp [Pi.sup_apply,h1.1,h2.1],fun j => le_sup_of_le_left (h1.2.1 j),?_⟩
    intro i j
    change a i j ≤ min (u i) (v i)+max (l j) (k j)
    rcases le_total (u i) (v i) with h | h
    · rw [min_eq_left h];exact (h1.2.2 i j).trans (add_le_add_right (le_max_left _ _) _)
    · rw [min_eq_right h];exact (h2.2.2 i j).trans (add_le_add_right (le_max_right _ _) _)
  · refine ⟨by simp [Pi.inf_apply,h1.1,h2.1],fun j => le_inf (h1.2.1 j) (h2.2.1 j),?_⟩
    intro i j
    change a i j ≤ max (u i) (v i)+min (l j) (k j)
    rcases le_total (l j) (k j) with h | h
    · rw [min_eq_left h];exact (h1.2.2 i j).trans (add_le_add_left (le_max_left _ _) _)
    · rw [min_eq_right h];exact (h2.2.2 i j).trans (add_le_add_left (le_max_right _ _) _)
lemma rearrange (x y u v : ℝ) : max x y*min u v+min x y*max u v ≤ x*u+y*v := by
  rcases le_total x y with hxy | hyx <;> rcases le_total u v with huv | hvu
  · rw [max_eq_right hxy,min_eq_left hxy,min_eq_left huv,max_eq_right huv]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr huv)]
  · rw [max_eq_right hxy,min_eq_left hxy,min_eq_right hvu,max_eq_left hvu] <;> ring_nf <;> exact le_rfl
  · rw [max_eq_left hyx,min_eq_right hyx,min_eq_left huv,max_eq_right huv] <;> ring_nf <;> exact le_rfl
  · rw [max_eq_left hyx,min_eq_right hyx,min_eq_right hvu,max_eq_left hvu]
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hvu)]
lemma dual_uncross_value {n m : ℕ} (c : Fin (m+1) → ℝ) (x y u v : Fin n → ℝ)
    (l k : Fin (m+1) → ℝ) :
    dtpObjective c (x ⊔ y) (u ⊓ v) (l ⊔ k)+dtpObjective c (x ⊓ y) (u ⊔ v) (l ⊓ k) ≤
      dtpObjective c x u l+dtpObjective c y v k := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin n) _ => rearrange (x i) (y i) (u i) (v i))
  have hlam : (∑ j,c j*max (l j) (k j))+(∑ j,c j*min (l j) (k j)) =
      (∑ j,c j*l j)+(∑ j,c j*k j) := by
    simp only [← Finset.sum_add_distrib,← mul_add,max_add_min]
  unfold dtpObjective
  simp only [Pi.sup_apply,Pi.inf_apply]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hsum
  linarith
end OverbookingResearch
#print axioms OverbookingResearch.value_le_dual
#print axioms OverbookingResearch.dual_uncross_value

open Matrix
namespace OverbookingResearch
lemma farkas_finite {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℝ) (b : I → ℝ) (c : J → ℝ) (d : ℝ)
    (hfeas : ∃ x : J → ℝ, A.mulVec x ≤ b)
    (hbound : ∀ x : J → ℝ, A.mulVec x ≤ b → c ⬝ᵥ x ≤ d) :
    ∃ p : I → ℝ, 0 ≤ p ∧ Aᵀ.mulVec p = c ∧ p ⬝ᵥ b ≤ d := by
  classical
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let A' : Matrix I (Fin (Fintype.card J)) ℝ := fun i k => A i (e.symm k)
  let c' : Fin (Fintype.card J) → ℝ := fun k => c (e.symm k)
  have hrow (x : Fin (Fintype.card J) → ℝ) : A'.mulVec x = A.mulVec (fun j => x (e j)) := by
    funext i
    simpa [A',Matrix.mulVec,dotProduct] using (e.sum_comp (fun k => A i (e.symm k)*x k)).symm
  have hfeas' : ∃ x, A'.mulVec x ≤ b := by
    obtain ⟨x,hx⟩ := hfeas
    refine ⟨fun k => x (e.symm k),?_⟩
    rw [hrow]
    simpa using hx
  have hbound' : ∀ x, A'.mulVec x ≤ b → c' ⬝ᵥ x ≤ d := by
    intro x hx
    rw [hrow] at hx
    have hh := hbound (fun j => x (e j)) hx
    have he : c ⬝ᵥ (fun j => x (e j)) = c' ⬝ᵥ x := by
      simpa [c',dotProduct] using e.sum_comp (fun k => c (e.symm k)*x k)
    rwa [he] at hh
  obtain ⟨p,hp,hpA,hpb⟩ := (LinearOptimization.farkas_inequality_form_fintype A' b c' d hfeas').mp hbound'
  refine ⟨p,hp,?_,hpb⟩
  funext j
  have hj := congrFun hpA (e j)
  simpa [A',c',Matrix.mulVec,Matrix.transpose] using hj

abbrev TPRow (n m : ℕ) := (Fin n × Bool) ⊕ (Fin m ⊕ (Fin n × Fin (m+1)))
def tpMatrix {n m : ℕ} : Matrix (TPRow n m) (Fin n × Fin (m+1)) ℝ
  | Sum.inl (i,b), (k,j) => if i=k then (if b then 1 else -1) else 0
  | Sum.inr (Sum.inl j), (i,k) => if j.succ=k then 1 else 0
  | Sum.inr (Sum.inr q), k => if q=k then -1 else 0
def tpRhs {n m : ℕ} (c : Fin (m+1) → ℝ) (z : Fin n → ℝ) : TPRow n m → ℝ
  | Sum.inl (i,b) => if b then z i else -z i
  | Sum.inr (Sum.inl j) => c j.succ
  | Sum.inr (Sum.inr _) => 0
lemma tpMatrix_rows {n m : ℕ} (x : Fin n × Fin (m+1) → ℝ) :
    (∀ i, (tpMatrix.mulVec x) (Sum.inl (i,true)) = ∑ j,x (i,j)) ∧
    (∀ i, (tpMatrix.mulVec x) (Sum.inl (i,false)) = -(∑ j,x (i,j))) ∧
    (∀ j, (tpMatrix.mulVec x) (Sum.inr (Sum.inl j)) = ∑ i,x (i,j.succ)) ∧
    (∀ q, (tpMatrix.mulVec x) (Sum.inr (Sum.inr q)) = -x q) := by
  constructor
  · intro i
    simp only [Matrix.mulVec,dotProduct,tpMatrix,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp
  constructor
  · intro i
    simp only [Matrix.mulVec,dotProduct,tpMatrix,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp
  constructor
  · intro j
    simp [Matrix.mulVec,dotProduct,tpMatrix,Fintype.sum_prod_type]
  · intro q
    simp [Matrix.mulVec,dotProduct,tpMatrix]
lemma tpMatrix_feasible {n m : ℕ} (c : Fin (m+1) → ℝ) (z : Fin n → ℝ)
    (x : Fin n × Fin (m+1) → ℝ) :
    tpMatrix.mulVec x ≤ tpRhs c z ↔ IsTPFeasible c z (fun i j => x (i,j)) := by
  have hr := tpMatrix_rows x
  constructor
  · intro hx
    refine ⟨?_,?_,?_⟩
    · intro i j
      have h := hx (Sum.inr (Sum.inr (i,j)))
      rw [hr.2.2.2] at h
      change -x (i,j) ≤ 0 at h
      linarith
    · intro i
      have h1 := hx (Sum.inl (i,true));have h2 := hx (Sum.inl (i,false))
      rw [hr.1] at h1;rw [hr.2.1] at h2
      change (∑ j,x (i,j)) ≤ z i at h1
      change -(∑ j,x (i,j)) ≤ -z i at h2
      linarith
    · intro j hj
      induction j using Fin.cases with
      | zero => exact (hj rfl).elim
      | succ j =>
        have h := hx (Sum.inr (Sum.inl j))
        rw [hr.2.2.1] at h
        exact h
  · intro hx r
    rcases r with ⟨i,b⟩ | j
    · cases b
      · simpa [hr.2.1,tpRhs,hx.2.1 i]
      · simpa [hr.1,tpRhs,hx.2.1 i]
    · rcases j with j | q
      · rw [hr.2.2.1];exact hx.2.2 j.succ (Fin.succ_ne_zero j)
      · rw [hr.2.2.2];exact neg_nonpos.mpr (hx.1 q.1 q.2)

lemma dual_attainment {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ)
    (c : Fin (m+1) → ℝ) (hc : ∀ j,j≠0 → 0≤c j)
    (z : Fin n → ℝ) (hz : ∀ i,0≤z i) :
    ∃ u l,IsDTPFeasible a u l ∧ dtpObjective c z u l=V0 a c z := by
  classical
  have hfeas : ∃ x : Fin n × Fin (m+1) → ℝ, tpMatrix.mulVec x ≤ tpRhs c z := by
    obtain ⟨y,hy⟩ := MiaoConcavity.feasible_nonempty c z hc hz
    exact ⟨fun ij => y ij.1 ij.2,(tpMatrix_feasible c z _).2 hy⟩
  have hbound : ∀ x : Fin n × Fin (m+1) → ℝ, tpMatrix.mulVec x ≤ tpRhs c z →
      (fun ij => a ij.1 ij.2) ⬝ᵥ x ≤ V0 a c z := by
    intro x hx
    have h := MiaoConcavity.objective_le_value a c z (fun i j => x (i,j)) ((tpMatrix_feasible c z x).1 hx)
    simpa [dotProduct,Fintype.sum_prod_type,tpObjective] using h
  obtain ⟨p,hp,hpA,hpb⟩ := farkas_finite tpMatrix (tpRhs c z) (fun ij => a ij.1 ij.2) (V0 a c z) hfeas hbound
  let u : Fin n → ℝ := fun i => p (Sum.inl (i,true))-p (Sum.inl (i,false))
  let l : Fin (m+1) → ℝ := Fin.cases 0 (fun j => p (Sum.inr (Sum.inl j)))
  have hd : IsDTPFeasible a u l := by
    refine ⟨rfl,?_,?_⟩
    · intro j
      induction j using Fin.cases with
      | zero => exact le_rfl
      | succ j => exact hp (Sum.inr (Sum.inl j))
    · intro i j
      have hh := congrFun hpA (i,j)
      have hn : (0:ℝ) ≤ p (Sum.inr (Sum.inr (i,j))) := hp (Sum.inr (Sum.inr (i,j)))
      induction j using Fin.cases with
      | zero =>
        simp [Matrix.mulVec,Matrix.transpose,dotProduct,tpMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type] at hh
        dsimp [u,l]
        linarith
      | succ j =>
        simp [Matrix.mulVec,Matrix.transpose,dotProduct,tpMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type] at hh
        dsimp [u,l]
        linarith
  have he : p ⬝ᵥ tpRhs c z = dtpObjective c z u l := by
    simp [dotProduct,tpRhs,dtpObjective,Fintype.sum_sum_type,Fintype.sum_prod_type,u,l,
      Fin.sum_univ_succ,mul_sub,Finset.sum_sub_distrib,mul_comm,Finset.sum_add_distrib,sub_eq_add_neg,mul_add]
  rw [he] at hpb
  exact ⟨u,l,hd,le_antisymm hpb (value_le_dual a c hc z hz u l hd)⟩
end OverbookingResearch
#print axioms OverbookingResearch.dual_attainment

open SubstOverbooking.Structure

theorem accepted_transport {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ) (c : Fin (m+1) → ℝ)
    (hc : ∀ j,j≠0 → 0≤c j) (z : Fin n → ℝ) (hz : ∀ i,0≤z i) :
    (∃ y,IsTPFeasible c z y ∧ tpObjective a y=V0 a c z) ∧
    (∀ u l,IsDTPFeasible a u l → V0 a c z ≤ dtpObjective c z u l) ∧
    (∃ u l,IsDTPFeasible a u l ∧ dtpObjective c z u l=V0 a c z) := by
  exact ⟨MiaoConcavity.optimum a c z hc hz,
    fun u l h => OverbookingResearch.value_le_dual a c hc z hz u l h,
    OverbookingResearch.dual_attainment a c hc z hz⟩
#print axioms accepted_transport
open SubstOverbooking.Structure
namespace OverbookingResearch
lemma submodular_of_dual_attainment {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ)
    (c : Fin (m+1) → ℝ) (hc : ∀ j,j≠0 → 0≤c j)
    (hD : ∀ z : Fin n → ℝ,(∀ i,0≤z i) →
      ∃ u l,IsDTPFeasible a u l ∧ dtpObjective c z u l=V0 a c z) :
    Supermodularity.Monotonicity.SupermodularOn (fun z => -V0 a c z) {z | ∀ i,0≤z i} := by
  intro x hx y hy
  obtain ⟨u,l,hul,he1⟩ := hD x hx
  obtain ⟨v,k,hvk,he2⟩ := hD y hy
  have hu := dual_uncross a u v l k hul hvk
  have hx' : ∀ i,0≤(x ⊔ y) i := fun i => le_sup_of_le_left (hx i)
  have hy' : ∀ i,0≤(x ⊓ y) i := fun i => le_inf (hx i) (hy i)
  have h1 := value_le_dual a c hc (x ⊔ y) hx' (u ⊓ v) (l ⊔ k) hu.1
  have h2 := value_le_dual a c hc (x ⊓ y) hy' (u ⊔ v) (l ⊓ k) hu.2
  have h3 := dual_uncross_value c x y u v l k
  rw [he1,he2] at h3
  linarith
end OverbookingResearch
#print axioms OverbookingResearch.submodular_of_dual_attainment

theorem solution {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ) (c : Fin (m+1) → ℝ)
    (hc : ∀ j,j≠0 → 0≤c j) :
    Supermodularity.Monotonicity.SupermodularOn (fun z => -V0 a c z) {z | ∀ i,0≤z i} := by
  exact OverbookingResearch.submodular_of_dual_attainment a c hc
    (fun z hz => OverbookingResearch.dual_attainment a c hc z hz)
#print axioms solution
