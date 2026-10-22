-- Prove2me | solution 1 for SubstOverbooking.Structure.theorem2_concave_submodular
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T20:04:42.775281+00:00
-- url     : https://prove2.me/submissions/9879f811-09e7-45f3-93ff-828192282899

/-
Alexander Richard Towell (queelius): research direction and stewardship.
OpenAI Codex: substantial proof construction, integration, checking and documentation.
Itir Karaesmen and Garrett van Ryzin: original overbooking mathematics,
Operations Research 52(1):83–104 (2004), Theorem 2, pp.87–88.
The platform's virtual class is explicitly uncapacitated; this differs from the
source's finite-but-large virtual capacity and is not silently identified with it.
mikedeng1: platform formulation. Shuze Chen: statement confirmation, not proof review.

Community credit: miao's accepted primal-compactness/concavity proof is included
in MiaoConcavity; sample-path concavity and the lattice/decreasing-differences
equivalence are included in MiaoSample and MiaoLattice. The measure-preserving
coordinate coupling is adapted directly from miao's accepted semigroup proof
8fd22dbf-974e-4dd1-8bb6-c9554fb359c9, submission35c1d866-4221-4fe0-b959-6d7ba1775076.
Mean additivity was already accepted from miao (59155d5c-6a52-47c3-9409-c7a406e642e4)
and is not claimed as a new result. Exact source hashes and transformations are
preserved in the accompanying provenance record.
Harry_Xu's complete accepted Farkas/separation/polyhedron chain is imported as
actual proof bodies, not theorem placeholders. Bertsimas and Tsitsiklis retain
source credit for that established linear-optimization mathematics. The earlier
transportation, uncrossing and sample-path submodularity proofs are this session's
already accepted contributions, reused here rather than counted again.

New completion here: absolute service-value bounds and integrability from finite
means; common-product-space transport of four sample-path terms; separation and
cancellation of the affine revenue terms; full coordinate concavity and lattice
submodularity for the exact quantified root. Lean/Mathlib provide foundations.
No mathematical novelty or independent human proof review is claimed.
-/
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

theorem accepted_submodular {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ) (c : Fin (m+1) → ℝ)
    (hc : ∀ j,j≠0 → 0≤c j) :
    Supermodularity.Monotonicity.SupermodularOn (fun z => -V0 a c z) {z | ∀ i,0≤z i} := by
  exact OverbookingResearch.submodular_of_dual_attainment a c hc
    (fun z hz => OverbookingResearch.dual_attainment a c hc z hz)
#print axioms accepted_submodular

theorem accepted_sample_path {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ) (c : Fin (m+1) → ℝ)
    (hc : ∀ j,j≠0 → 0≤c j) (z : Fin n → ℝ) (hz : ∀ k,0≤z k) (i j : Fin n) (hij : i≠j)
    (k₁ k₂ : ℝ) (hk₁ : 0≤k₁) (hk₂ : 0≤k₂) :
    V0 a c (z+Pi.single i k₁+Pi.single j k₂)-V0 a c (z+Pi.single j k₂) ≤
      V0 a c (z+Pi.single i k₁)-V0 a c z := by
  classical
  let x : Fin n → ℝ := z+Pi.single i k₁
  let y : Fin n → ℝ := z+Pi.single j k₂
  have hx : ∀ t,0≤x t := by
    intro t
    dsimp [x]
    by_cases ht : i=t <;> simp [Pi.single_apply,ht] <;> linarith [hz t]
  have hy : ∀ t,0≤y t := by
    intro t
    dsimp [y]
    by_cases ht : j=t <;> simp [Pi.single_apply,ht] <;> linarith [hz t]
  have hsup : x ⊔ y = z+Pi.single i k₁+Pi.single j k₂ := by
    ext t
    by_cases hi : i=t
    · subst t
      simp [x,y,Pi.sup_apply,Pi.single_apply,hij,Ne.symm hij,max_eq_left (by linarith : z i≤z i+k₁)]
    · by_cases hj : j=t
      · subst t
        simp [x,y,Pi.sup_apply,Pi.single_apply,hi,max_eq_right (by linarith : z j≤z j+k₂)]
      · simp [x,y,Pi.sup_apply,Pi.single_apply,hi,hj]
  have hinf : x ⊓ y = z := by
    ext t
    by_cases hi : i=t
    · subst t
      simp [x,y,Pi.inf_apply,Pi.single_apply,hij,Ne.symm hij,min_eq_right (by linarith : z i≤z i+k₁)]
    · by_cases hj : j=t
      · subst t
        simp [x,y,Pi.inf_apply,Pi.single_apply,hi,min_eq_left (by linarith : z j≤z j+k₂)]
      · simp [x,y,Pi.inf_apply,Pi.single_apply,hi,hj]
  have h := accepted_submodular a c hc hx hy
  rw [hsup,hinf] at h
  dsimp [x,y] at h
  linarith
#print axioms accepted_sample_path

open MeasureTheory
namespace OverbookingResearch
lemma value_abs_bound {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ)
    (c : Fin (m+1) → ℝ) (hc : ∀ j, j ≠ 0 → 0 ≤ c j)
    (K : ℝ) (ha : ∀ i j, |a i j| ≤ K)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    |V0 a c z| ≤ K * ∑ i, z i := by
  obtain ⟨y, hy, he⟩ := MiaoConcavity.optimum a c z hc hz
  rw [← he]
  calc
    |tpObjective a y| ≤ ∑ i, ∑ j, |a i j * y i j| := by
      unfold tpObjective
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, K*y i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hy.1 i j)]
      exact mul_le_mul_of_nonneg_right (ha i j) (hy.1 i j)
    _ = K * ∑ i, z i := by simp_rw [← Finset.mul_sum, hy.2.1]

lemma survival_coordinate_integrable {n : ℕ} (P : Set ℝ) (L : Fin n → ℝ → PMF ℕ)
    (hL : ∀ i, IsSemigroupFamily P (L i)) (u : Fin n → ℝ) (hu : ∀ i, u i ∈ P) (i : Fin n) :
    Integrable (fun z : Fin n → ℕ => (z i : ℝ)) (survivalLaw L u) := by
  exact integrable_comp_eval ((hL i).2 (u i) (hu i))

lemma service_integrable {n m : ℕ} (a : Fin n → Fin (m+1) → ℝ)
    (c : Fin (m+1) → ℝ) (hc : ∀ j, j ≠ 0 → 0 ≤ c j)
    (P : Set ℝ) (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i))
    (u : Fin n → ℝ) (hu : ∀ i, u i ∈ P) :
    Integrable (fun z : Fin n → ℕ => V0 a c (fun i => (z i : ℝ))) (survivalLaw L u) := by
  classical
  let K : ℝ := ∑ i : Fin n, ∑ j : Fin (m+1), |a i j|
  have hK : ∀ i j, |a i j| ≤ K := by
    intro i j
    calc
      |a i j| ≤ ∑ k : Fin (m+1), |a i k| := Finset.single_le_sum (f := fun k : Fin (m+1) => |a i k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ K := by
        apply Finset.single_le_sum (f := fun k : Fin n => ∑ j : Fin (m+1), |a k j|) _ (Finset.mem_univ i)
        intro k hk
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hi : Integrable (fun z : Fin n → ℕ => K * ∑ i, (z i : ℝ)) (survivalLaw L u) :=
    (integrable_finset_sum _ (fun i _ => survival_coordinate_integrable P L hL u hu i)).const_mul K
  apply hi.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs] using value_abs_bound a c hc K hK (fun i => (z i : ℝ)) (fun i => Nat.cast_nonneg _)

lemma refund_integrable {n : ℕ} (q u : Fin n → ℝ) (P : Set ℝ)
    (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i)) (hu : ∀ i, u i ∈ P) :
    Integrable (fun z : Fin n → ℕ => ∑ i, q i * (u i - (z i : ℝ))) (survivalLaw L u) := by
  haveI : IsProbabilityMeasure (survivalLaw L u) := by unfold survivalLaw; infer_instance
  exact integrable_finset_sum _ (fun i _ => ((integrable_const (u i)).sub
    (survival_coordinate_integrable P L hL u hu i)).const_mul (q i))

lemma survival_add {n : ℕ} (P : Set ℝ) (L : Fin n → ℝ → PMF ℕ)
    (hL : ∀ i, IsSemigroupFamily P (L i)) (u v : Fin n → ℝ)
    (hu : ∀ i, u i ∈ P) (hv : ∀ i, v i ∈ P) :
    ((survivalLaw L u).prod (survivalLaw L v)).map (fun p => p.1 + p.2) = survivalLaw L (u+v) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin n)
    (fun i => (L i (u i)).toMeasure) (fun i => (L i (v i)).toMeasure)
  change ((Measure.pi fun i => (L i (u i)).toMeasure).prod
    (Measure.pi fun i => (L i (v i)).toMeasure)).map _ = _
  rw [← he.map_eq, Measure.map_map (measurable_of_countable _) he.measurable]
  change (Measure.pi (fun i => ((L i (u i)).toMeasure).prod (L i (v i)).toMeasure)).map
    (fun x i => (x i).1 + (x i).2) = _
  rw [Measure.pi_map_pi (μ := fun i : Fin n => ((L i (u i)).toMeasure).prod (L i (v i)).toMeasure)
    (f := fun (_ : Fin n) (p : ℕ × ℕ) => p.1 + p.2) (fun _ => (measurable_of_countable _).aemeasurable)]
  congr 1
  funext i
  exact ((hL i).1 (u i) (hu i) (v i) (hv i)).symm


lemma mean_add (P : Set ℝ) (L : ℝ → PMF ℕ) (hL : IsSemigroupFamily P L)
    (u v : ℝ) (hu : u ∈ P) (hv : v ∈ P) :
    (∫ k : ℕ, (k : ℝ) ∂(L (u+v)).toMeasure) =
      (∫ k : ℕ, (k : ℝ) ∂(L u).toMeasure) + (∫ k : ℕ, (k : ℝ) ∂(L v).toMeasure) := by
  rw [hL.1 u hu v hv, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp_rw [Nat.cast_add]
  rw [integral_add ((hL.2 u hu).comp_fst _) ((hL.2 v hv).comp_snd _)]
  congr 1
  · rw [integral_prod _ ((hL.2 u hu).comp_fst _)]
    simp
  · rw [integral_prod _ ((hL.2 v hv).comp_snd _)]
    simp

lemma zero_law_ae (P : Set ℝ) (hP : IsParamSet P) (L : ℝ → PMF ℕ)
    (hL : IsSemigroupFamily P L) : ∀ᵐ k ∂(L 0).toMeasure, k = 0 := by
  have h := mean_add P L hL 0 0 hP.1 hP.1
  simp only [zero_add] at h
  have hz : (∫ k : ℕ, (k : ℝ) ∂(L 0).toMeasure) = 0 := by linarith
  have he := (integral_eq_zero_iff_of_nonneg (fun k : ℕ => Nat.cast_nonneg (α := ℝ) k)
    (hL.2 0 hP.1)).mp hz
  filter_upwards [he] with k hk
  change (k : ℝ) = 0 at hk
  exact_mod_cast hk

lemma survival_zero_coordinate {n : ℕ} (P : Set ℝ) (hP : IsParamSet P)
    (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i))
    (u : Fin n → ℝ) (i : Fin n) (hi : u i = 0) :
    ∀ᵐ z ∂survivalLaw L u, z i = 0 := by
  have he : ∀ᵐ k ∂(L i (u i)).toMeasure, k = 0 := by rw [hi]; exact zero_law_ae P hP (L i) (hL i)
  exact (measurePreserving_eval (fun j => (L j (u j)).toMeasure) i).quasiMeasurePreserving.ae he
end OverbookingResearch


/- Accepted proof by miao, target fc7c0f66-42f4-4dcd-bbe5-2738f46d002c. Reused with namespace isolation. -/
namespace MiaoSample

open SubstOverbooking.Structure
open scoped BigOperators

private theorem feasible_nonempty {n m : ℕ} (c : Fin (m + 1) → ℝ)
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

private theorem feasible_compact {n m : ℕ} (c : Fin (m + 1) → ℝ)
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

private theorem objective_continuous {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) :
    Continuous (tpObjective a) := by
  unfold tpObjective
  fun_prop

private theorem optimum {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (hz : ∀ i, 0 ≤ z i) :
    ∃ y, IsTPFeasible c z y ∧ tpObjective a y = V0 a c z := by
  obtain ⟨y, hy, he⟩ := (feasible_compact c z).exists_sSup_image_eq
    (feasible_nonempty c z hc hz) (objective_continuous a).continuousOn
  exact ⟨y, hy, he.symm⟩

private theorem objective_le_value {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ)
    (y : Fin n → Fin (m + 1) → ℝ) (hy : IsTPFeasible c z y) :
    tpObjective a y ≤ V0 a c z := by
  exact le_csSup ((feasible_compact c z).bddAbove_image
    (objective_continuous a).continuousOn) ⟨y, hy, rfl⟩

private theorem combine_feasible {n m : ℕ}
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

private theorem combine_objective {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ)
    (y v : Fin n → Fin (m + 1) → ℝ) (α β : ℝ) :
    tpObjective a (α • y + β • v) = α * tpObjective a y + β * tpObjective a v := by
  simp only [tpObjective, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  simp_rw [mul_left_comm (a _ _) α, mul_left_comm (a _ _) β]
  simp_rw [← Finset.mul_sum]

open SubstOverbooking.Structure

private theorem value_concavity {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) :
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



theorem solution {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (z : Fin n → ℝ) (hz : ∀ k, 0 ≤ z k) (i : Fin n)
    (k₂ k₃ : ℝ) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃) :
    V0 a c (z + Pi.single i (k₂ + k₃)) - V0 a c (z + Pi.single i k₃) ≤
      V0 a c (z + Pi.single i k₂) - V0 a c z := by
  classical
  by_cases ht : k₂ + k₃ = 0
  · have h2 : k₂ = 0 := by linarith
    have h3 : k₃ = 0 := by linarith
    simp [h2, h3]
  have hpos : 0 < k₂ + k₃ := lt_of_le_of_ne (add_nonneg hk₂ hk₃) (Ne.symm ht)
  have h2 := div_nonneg hk₂ hpos.le
  have h3 := div_nonneg hk₃ hpos.le
  have hab : k₃ / (k₂ + k₃) + k₂ / (k₂ + k₃) = 1 := by
    field_simp
    ring
  have hz' : ∀ k : Fin n, 0 ≤ (z + (Pi.single i (k₂ + k₃) : Fin n → ℝ)) k := by
    intro k
    by_cases h : k = i
    · subst k; simpa using add_nonneg (hz i) (add_nonneg hk₂ hk₃)
    · simpa [Pi.single_eq_of_ne h] using hz k
  have e2 : (k₃ / (k₂ + k₃)) • z +
      (k₂ / (k₂ + k₃)) • (z + Pi.single i (k₂ + k₃)) = z + Pi.single i k₂ := by
    ext k
    by_cases h : k = i
    · subst k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne h, add_zero]
      field_simp
      ring
  have e3 : (k₂ / (k₂ + k₃)) • z +
      (k₃ / (k₂ + k₃)) • (z + Pi.single i (k₂ + k₃)) = z + Pi.single i k₃ := by
    ext k
    by_cases h : k = i
    · subst k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne h, add_zero]
      field_simp
  have hconc := (value_concavity a).1 c hc
  have H2 := hconc.2 hz hz' h3 h2 hab
  have H3 := hconc.2 hz hz' h2 h3 (by linarith : k₂ / (k₂ + k₃) + k₃ / (k₂ + k₃) = 1)
  rw [e2] at H2
  rw [e3] at H3
  simp only [smul_eq_mul] at H2 H3
  nlinarith [show (k₃ / (k₂ + k₃) + k₂ / (k₂ + k₃)) *
      (V0 a c z + V0 a c (z + Pi.single i (k₂ + k₃))) =
      V0 a c z + V0 a c (z + Pi.single i (k₂ + k₃)) by rw [hab, one_mul]]


#print axioms solution
end MiaoSample

/- Accepted proof by miao, target 5ebdf6c0-243d-4533-aabd-2b5dcdd373b5. Reused with namespace isolation. -/
namespace MiaoLattice

open SubstOverbooking.Structure

private theorem mem_product {n : ℕ} (T : Fin n → Set ℝ) (x : Fin n → ℝ) :
    x ∈ Set.pi Set.univ T ↔ ∀ k, x k ∈ T k := by simp

private theorem update_mem {n : ℕ} (T : Fin n → Set ℝ) (x : Fin n → ℝ)
    (hx : x ∈ Set.pi Set.univ T) (i : Fin n) (t : ℝ) (ht : t ∈ T i) :
    Function.update x i t ∈ Set.pi Set.univ T := by
  classical
  rw [mem_product] at hx ⊢
  intro k
  by_cases h : k = i
  · subst k; simpa using ht
  · simpa [Function.update_of_ne h] using hx k

private theorem marginal {n : ℕ} (T : Fin n → Set ℝ)
    (f : (Fin n → ℝ) → ℝ) (hdd : DecreasingDifferencesOn f (Set.pi Set.univ T))
    (i : Fin n) (t : ℝ) (ht : t ∈ T i) :
    ∀ (s : Finset (Fin n)) (x y : Fin n → ℝ),
      x ∈ Set.pi Set.univ T → y ∈ Set.pi Set.univ T →
      x ≤ y → x i = y i → (∀ k, k ∉ s → x k = y k) → x i ≤ t →
      f (Function.update y i t) - f y ≤ f (Function.update x i t) - f x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hx hy hxy hi he hxt
    have e : x = y := funext (fun k => he k (by simp))
    simp [e]
  | @insert j s hjs ih =>
    intro x y hx hy hxy hi he hxt
    let y' := Function.update y j (x j)
    have hy' : y' ∈ Set.pi Set.univ T := update_mem T y hy j (x j) ((mem_product T x).mp hx j)
    have hxy' : x ≤ y' := by
      intro k
      by_cases h : k = j
      · subst k; simp [y']
      · simpa [y', Function.update_of_ne h] using hxy k
    have hi' : x i = y' i := by
      by_cases h : i = j
      · subst i; simp [y']
      · simpa [y', Function.update_of_ne h] using hi
    have he' : ∀ k, k ∉ s → x k = y' k := by
      intro k hk
      by_cases h : k = j
      · subst k; simp [y']
      · simpa [y', Function.update_of_ne h] using he k (by simp [hk, h])
    have H := ih x y' hx hy' hxy' hi' he' hxt
    by_cases hij : i = j
    · have ey : y' = y := by
        ext k
        by_cases h : k = j
        · subst k; simpa [y', hij] using hi
        · simp [y', Function.update_of_ne h]
      simpa [ey] using H
    have ey : Function.update y' j (y j) = y := by
      ext k
      by_cases h : k = j
      · subst k; simp
      · simp [y', Function.update_of_ne h]
    have eij : Function.update (Function.update y' i t) j (y j) = Function.update y i t := by
      rw [Function.update_comm hij, ey]
    have D := hdd y' hy' i j hij t (y j) (by simpa [hi'] using hxt)
      (by simpa [y'] using hxy j) (update_mem T y' hy' i t ht)
      (update_mem T y' hy' j (y j) ((mem_product T y).mp hy j))
      (update_mem T _ (update_mem T y' hy' i t ht) j (y j) ((mem_product T y).mp hy j))
    rw [ey, eij] at D
    linarith

private theorem lattice_inequality {n : ℕ} (T : Fin n → Set ℝ)
    (f : (Fin n → ℝ) → ℝ) (hdd : DecreasingDifferencesOn f (Set.pi Set.univ T)) :
    ∀ (s : Finset (Fin n)) (x y : Fin n → ℝ),
      x ∈ Set.pi Set.univ T → y ∈ Set.pi Set.univ T →
      (∀ k, k ∉ s → x k ≤ y k) →
      f (x ⊔ y) + f (x ⊓ y) ≤ f x + f y := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hx hy he
    have hxy : x ≤ y := fun k => he k (by simp)
    simp [sup_eq_right.mpr hxy, inf_eq_left.mpr hxy, add_comm]
  | @insert j s hjs ih =>
    intro x y hx hy he
    by_cases hj : x j ≤ y j
    · apply ih x y hx hy
      intro k hk
      by_cases h : k = j
      · subst k; exact hj
      · exact he k (by simp [hk, h])
    have hyj : y j ≤ x j := le_of_lt (lt_of_not_ge hj)
    let x' := Function.update x j (y j)
    have hx' : x' ∈ Set.pi Set.univ T := update_mem T x hx j (y j) ((mem_product T y).mp hy j)
    have H := ih x' y hx' hy (by
      intro k hk
      by_cases h : k = j
      · subst k; simp [x']
      · simpa [x', Function.update_of_ne h] using he k (by simp [hk, h]))
    have hs : x' ⊔ y ∈ Set.pi Set.univ T := by
      rw [mem_product]
      intro k
      rcases le_total (x' k) (y k) with h | h
      · simpa [sup_eq_right.mpr h] using (mem_product T y).mp hy k
      · simpa [sup_eq_left.mpr h] using (mem_product T x').mp hx' k
    have D := marginal T f hdd j (x j) ((mem_product T x).mp hx j)
      Finset.univ x' (x' ⊔ y) hx' hs le_sup_left
      (by simp [x']) (by simp) (by simpa [x'] using hyj)
    have e1 : Function.update x' j (x j) = x := by
      ext k
      by_cases h : k = j
      · subst k; simp
      · simp [x', Function.update_of_ne h]
    have e2 : Function.update (x' ⊔ y) j (x j) = x ⊔ y := by
      ext k
      by_cases h : k = j
      · subst k; simp [Pi.sup_apply, sup_eq_left.mpr hyj]
      · simp [x', Pi.sup_apply, Function.update_of_ne h]
    have e3 : x' ⊓ y = x ⊓ y := by
      ext k
      by_cases h : k = j
      · subst k; simp [x', Pi.inf_apply, inf_eq_right.mpr hyj]
      · simp [x', Pi.inf_apply, Function.update_of_ne h]
    rw [e1, e2] at D
    rw [e3] at H
    linarith

theorem solution {n : ℕ} (T : Fin n → Set ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    Supermodularity.Monotonicity.SupermodularOn (fun s => - f s) (Set.pi Set.univ T) ↔
      DecreasingDifferencesOn f (Set.pi Set.univ T) := by
  classical
  constructor
  · intro h s hs i j hij si sj hi hj hsi hsj hsij
    have H := h hsi hsj
    have es : Function.update s i si ⊔ Function.update s j sj =
        Function.update (Function.update s i si) j sj := by
      ext k
      by_cases hki : k = i
      · subst k; simp [Pi.sup_apply, Function.update_of_ne hij, sup_eq_left.mpr hi]
      by_cases hkj : k = j
      · subst k; simp [Pi.sup_apply, Function.update_of_ne hij.symm, sup_eq_right.mpr hj]
      · simp [Pi.sup_apply, Function.update_of_ne hki, Function.update_of_ne hkj]
    have ei : Function.update s i si ⊓ Function.update s j sj = s := by
      ext k
      by_cases hki : k = i
      · subst k; simp [Pi.inf_apply, Function.update_of_ne hij, inf_eq_right.mpr hi]
      by_cases hkj : k = j
      · subst k; simp [Pi.inf_apply, Function.update_of_ne hij.symm, inf_eq_left.mpr hj]
      · simp [Pi.inf_apply, Function.update_of_ne hki, Function.update_of_ne hkj]
    rw [es, ei] at H
    linarith
  · intro h x hx y hy
    have H := lattice_inequality T f h Finset.univ x y hx hy (by simp)
    linarith

#print axioms solution
end MiaoLattice

namespace OverbookingResearch
/-- Adapted from miao's accepted semigroup_representation proof to expose its measure-preserving map. -/
lemma survival_update_map {n : ℕ} (P : Set ℝ) (L : Fin n → ℝ → PMF ℕ)
    (hL : ∀ i, IsSemigroupFamily P (L i)) (u : Fin n → ℝ)
    (hu : ∀ k, u k ∈ P) (i : Fin n) (ε : ℝ) (hε : ε ∈ P) :
    MeasurePreserving (fun p : (Fin n → ℕ) × ℕ => p.1 + Pi.single i p.2)
      ((survivalLaw L u).prod (L i ε).toMeasure)
      (survivalLaw L (Function.update u i (u i + ε))) := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let μ : Fin (n + 1) → Measure ℕ := fun k => (L k (u k)).toMeasure
    let ν := (L i ε).toMeasure
    let ρ := Measure.pi (fun j : Fin n => μ (i.succAbove j))
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℕ) i
    have H1 := (measurePreserving_piFinSuccAbove μ i).prod (MeasurePreserving.id ν)
    have H2 := (measurePreserving_prodAssoc (μ i) ρ ν).comp H1
    have H3 := ((MeasurePreserving.id (μ i)).prod
      (Measure.measurePreserving_swap (μ := ρ) (ν := ν))).comp H2
    have H4 := ((measurePreserving_prodAssoc (μ i) ν ρ).symm
      MeasurableEquiv.prodAssoc).comp H3
    have hadd : MeasurePreserving (fun p : ℕ × ℕ => p.1 + p.2)
        ((μ i).prod ν) (L i (u i + ε)).toMeasure :=
      ⟨by fun_prop, (hL i).1 (u i) (hu i) ε hε |>.symm⟩
    have H5 := (hadd.prod (MeasurePreserving.id ρ)).comp H4
    have H6 := (measurePreserving_piFinSuccAbove
      (fun k => (L k (Function.update u i (u i + ε) k)).toMeasure) i).symm e
    have H6' : MeasurePreserving e.symm
        ((L i (u i + ε)).toMeasure.prod ρ)
        (survivalLaw L (Function.update u i (u i + ε))) := by
      simpa [e, ρ, μ, survivalLaw, Function.update_of_ne (Fin.succAbove_ne i _)] using H6
    have H := H6'.comp H5
    have heq : e.symm ∘ (fun p => (p.1.1 + p.1.2, p.2)) ∘
        MeasurableEquiv.prodAssoc.symm ∘ (fun p => (p.1, p.2.swap)) ∘
        MeasurableEquiv.prodAssoc ∘ (fun p => (e p.1, p.2)) =
        (fun p : (Fin (n + 1) → ℕ) × ℕ => p.1 + Pi.single i p.2) := by
      ext p k
      obtain rfl | ⟨j, rfl⟩ := i.eq_self_or_eq_succAbove k
      · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
          MeasurableEquiv.prodAssoc, Fin.removeNth]
      · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
          MeasurableEquiv.prodAssoc, Fin.removeNth]
    have H' : MeasurePreserving
        (fun p : (Fin (n + 1) → ℕ) × ℕ => p.1 + Pi.single i p.2)
        ((survivalLaw L u).prod (L i ε).toMeasure)
        (survivalLaw L (Function.update u i (u i + ε))) := by
      convert H using 1
      · exact heq.symm
      · rfl
    exact H'

end OverbookingResearch

namespace OverbookingResearch
lemma integral_preserved {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (h : MeasurePreserving f μ ν)
    (F : Y → ℝ) (hF : AEStronglyMeasurable F ν) :
    (∫ x, F (f x) ∂μ) = ∫ y, F y ∂ν := by
  rw [← h.map_eq, integral_map h.measurable.aemeasurable]
  simpa only [h.map_eq] using hF

lemma expected_differences {n : ℕ} (P : Set ℝ) (hP : IsParamSet P)
    (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i))
    (F : (Fin n → ℕ) → ℝ)
    (hF : ∀ u : Fin n → ℝ, (∀ k, u k ∈ P) → Integrable F (survivalLaw L u))
    (u : Fin n → ℝ) (hu : ∀ k, u k ∈ P) (i j : Fin n)
    (ε α : ℝ) (hε : ε ∈ P) (hα : α ∈ P)
    (hd : ∀ z k l, F (z+Pi.single i k+Pi.single j l) - F (z+Pi.single j l)
      ≤ F (z+Pi.single i k)-F z) :
    (∫ z, F z ∂survivalLaw L (Function.update (Function.update u i (u i+ε)) j
      ((Function.update u i (u i+ε)) j+α))) -
    (∫ z, F z ∂survivalLaw L (Function.update u j (u j+α))) ≤
    (∫ z, F z ∂survivalLaw L (Function.update u i (u i+ε))) -
    (∫ z, F z ∂survivalLaw L u) := by
  classical
  let ue := Function.update u i (u i+ε)
  let ua := Function.update u j (u j+α)
  let uea := Function.update ue j (ue j+α)
  have hue : ∀ k, ue k ∈ P := by
    intro k
    by_cases hk : k=i
    · subst k; simpa [ue] using hP.2.1 _ (hu i) _ hε
    · simpa [ue,Function.update_of_ne hk] using hu k
  have hua : ∀ k, ua k ∈ P := by
    intro k
    by_cases hk : k=j
    · subst k; simpa [ua] using hP.2.1 _ (hu j) _ hα
    · simpa [ua,Function.update_of_ne hk] using hu k
  have huea : ∀ k, uea k ∈ P := by
    intro k
    by_cases hk : k=j
    · subst k; simpa [uea] using hP.2.1 _ (hue j) _ hα
    · simpa [uea,Function.update_of_ne hk] using hue k
  let μ := survivalLaw L u
  let ν := (L i ε).toMeasure
  let ρ := (L j α).toMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ,survivalLaw]; infer_instance
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  haveI : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have he := survival_update_map P L hL u hu i ε hε
  have ha := survival_update_map P L hL u hu j α hα
  have hea := survival_update_map P L hL ue hue j α hα
  have H0 : MeasurePreserving (fun p : ((Fin n → ℕ) × ℕ) × ℕ => p.1.1)
      ((μ.prod ν).prod ρ) μ :=
    (measurePreserving_fst (μ:=μ) (ν:=ν)).comp (measurePreserving_fst (μ:=μ.prod ν) (ν:=ρ))
  have He : MeasurePreserving (fun p : ((Fin n → ℕ) × ℕ) × ℕ => p.1.1+Pi.single i p.1.2)
      ((μ.prod ν).prod ρ) (survivalLaw L ue) :=
    he.comp (measurePreserving_fst (μ:=μ.prod ν) (ν:=ρ))
  have Ha : MeasurePreserving (fun p : ((Fin n → ℕ) × ℕ) × ℕ => p.1.1+Pi.single j p.2)
      ((μ.prod ν).prod ρ) (survivalLaw L ua) :=
    ha.comp ((measurePreserving_fst (μ:=μ) (ν:=ν)).prod (MeasurePreserving.id ρ))
  have Hea : MeasurePreserving (fun p : ((Fin n → ℕ) × ℕ) × ℕ => p.1.1+Pi.single i p.1.2+Pi.single j p.2)
      ((μ.prod ν).prod ρ) (survivalLaw L uea) := hea.comp (he.prod (MeasurePreserving.id ρ))
  have h := integral_mono
    ((Hea.integrable_comp_of_integrable (hF uea huea)).sub (Ha.integrable_comp_of_integrable (hF ua hua)))
    ((He.integrable_comp_of_integrable (hF ue hue)).sub (H0.integrable_comp_of_integrable (hF u hu)))
    (fun p => hd p.1.1 p.1.2 p.2)
  simp only [Pi.sub_apply, Function.comp_apply] at h
  have hs1 := integral_sub (Hea.integrable_comp_of_integrable (hF uea huea)) (Ha.integrable_comp_of_integrable (hF ua hua))
  have hs2 := integral_sub (He.integrable_comp_of_integrable (hF ue hue)) (H0.integrable_comp_of_integrable (hF u hu))
  simp only [Function.comp_apply] at hs1 hs2
  rw [hs1, hs2,
    integral_preserved Hea F (hF uea huea).aestronglyMeasurable,
    integral_preserved Ha F (hF ua hua).aestronglyMeasurable,
    integral_preserved He F (hF ue hue).aestronglyMeasurable,
    integral_preserved H0 F (hF u hu).aestronglyMeasurable] at h
  exact h
end OverbookingResearch

namespace OverbookingResearch
noncomputable def affineRevenue {n : ℕ} (r q x : Fin n → ℝ) (L : Fin n → ℝ → PMF ℕ)
    (u : Fin n → ℝ) : ℝ := ∑ i, ((r i-q i)*u i+q i*(∫ k : ℕ, (k : ℝ) ∂(L i (u i)).toMeasure)-r i*x i)

lemma revenue_split {n m : ℕ} (r q x : Fin n → ℝ) (a : Fin n → Fin (m+1) → ℝ)
    (c : Fin (m+1) → ℝ) (P : Set ℝ) (L : Fin n → ℝ → PMF ℕ)
    (hL : ∀ i, IsSemigroupFamily P (L i)) (u : Fin n → ℝ) (hu : ∀ i, u i ∈ P) :
    G r q x a c L u = affineRevenue r q x L u +
      ∫ z, V0 a c (fun i => (z i : ℝ)) ∂survivalLaw L u := by
  haveI : IsProbabilityMeasure (survivalLaw L u) := by unfold survivalLaw; infer_instance
  have hr : ∀ i, Integrable (fun z : Fin n → ℕ => q i*(u i-(z i : ℝ))) (survivalLaw L u) :=
    fun i => ((integrable_const _).sub (survival_coordinate_integrable P L hL u hu i)).const_mul (q i)
  unfold G affineRevenue
  rw [integral_finsetSum _ (fun i _ => hr i)]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_sub (integrable_const _) (survival_coordinate_integrable P L hL u hu i)]
  have he := integral_preserved (measurePreserving_eval (fun j => (L j (u j)).toMeasure) i)
    (fun k : ℕ => (k : ℝ)) (hL i |>.2 (u i) (hu i)).aestronglyMeasurable
  change (∫ z : Fin n → ℕ, (z i : ℝ) ∂survivalLaw L u) = _ at he
  rw [he]
  simp only [integral_const, probReal_univ, one_smul]
  ring

end OverbookingResearch
namespace OverbookingResearch
lemma affine_increment {n : ℕ} (r q x : Fin n → ℝ) (P : Set ℝ)
    (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i))
    (u : Fin n → ℝ) (hu : ∀ k, u k ∈ P) (i : Fin n) (ε : ℝ) (hε : ε ∈ P) :
    affineRevenue r q x L (Function.update u i (u i+ε)) - affineRevenue r q x L u =
      (r i-q i)*ε + q i*(∫ k : ℕ, (k : ℝ) ∂(L i ε).toMeasure) := by
  classical
  let f := fun k t => (r k-q k)*t+q k*(∫ z : ℕ, (z : ℝ) ∂(L k t).toMeasure)-r k*x k
  let C := (r i-q i)*ε + q i*(∫ z : ℕ, (z : ℝ) ∂(L i ε).toMeasure)
  have he : ∀ k, f k (Function.update u i (u i+ε) k) = f k (u k) + if k=i then C else 0 := by
    intro k
    by_cases hk : k=i
    · subst k
      simp only [Function.update_self, if_pos rfl]
      dsimp [f,C]
      rw [mean_add P (L i) (hL i) (u i) ε (hu i) hε]
      ring
    · simp [Function.update_of_ne hk, hk]
  change (∑ k, f k (Function.update u i (u i+ε) k)) - (∑ k, f k (u k)) = C
  simp_rw [he]
  simp [Finset.sum_add_distrib]

lemma update_mem {n : ℕ} (P : Set ℝ) (hP : IsParamSet P) (u : Fin n → ℝ)
    (hu : ∀ k, u k ∈ P) (i : Fin n) (ε : ℝ) (hε : ε ∈ P) :
    ∀ k, Function.update u i (u i+ε) k ∈ P := by
  classical
  intro k
  by_cases hk : k=i
  · subst k; simpa using hP.2.1 _ (hu i) _ hε
  · simpa [Function.update_of_ne hk] using hu k

lemma revenue_increment {n m : ℕ} (r q x : Fin n → ℝ) (a : Fin n → Fin (m+1) → ℝ)
    (c : Fin (m+1) → ℝ) (P : Set ℝ) (hP : IsParamSet P) (L : Fin n → ℝ → PMF ℕ)
    (hL : ∀ i, IsSemigroupFamily P (L i)) (u : Fin n → ℝ) (hu : ∀ i, u i ∈ P)
    (i : Fin n) (ε : ℝ) (hε : ε ∈ P) :
    G r q x a c L (Function.update u i (u i+ε)) - G r q x a c L u =
      (r i-q i)*ε + q i*(∫ k : ℕ, (k : ℝ) ∂(L i ε).toMeasure) +
        ((∫ z, V0 a c (fun k => (z k : ℝ)) ∂survivalLaw L (Function.update u i (u i+ε))) -
          (∫ z, V0 a c (fun k => (z k : ℝ)) ∂survivalLaw L u)) := by
  rw [revenue_split r q x a c P L hL _ (update_mem P hP u hu i ε hε),
    revenue_split r q x a c P L hL u hu]
  have h := affine_increment r q x P L hL u hu i ε hε
  linarith

lemma increments_commute {n : ℕ} (u : Fin n → ℝ) (i j : Fin n) (ε α : ℝ) :
    Function.update (Function.update u i (u i+ε)) j ((Function.update u i (u i+ε)) j+α) =
    Function.update (Function.update u j (u j+α)) i ((Function.update u j (u j+α)) i+ε) := by
  classical
  by_cases hij : i=j
  · subst j
    simp [add_comm,add_left_comm,add_assoc]
  · ext k
    by_cases hki : k=i
    · subst k; simp [hij,Ne.symm hij]
    · by_cases hkj : k=j
      · subst k; simp [hij,Ne.symm hij]
      · simp [Function.update_of_ne hki, Function.update_of_ne hkj]

lemma revenue_differences {n m : ℕ} (r q x : Fin n → ℝ) (a : Fin n → Fin (m+1) → ℝ)
    (c : Fin (m+1) → ℝ) (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (P : Set ℝ) (hP : IsParamSet P)
    (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i))
    (u : Fin n → ℝ) (hu : ∀ k, u k ∈ P) (i j : Fin n)
    (ε α : ℝ) (hε : ε ∈ P) (hα : α ∈ P)
    (hd : ∀ z : Fin n → ℕ, ∀ k l : ℕ,
      V0 a c (fun t => ((z+Pi.single i k+Pi.single j l : Fin n → ℕ) t : ℝ)) -
        V0 a c (fun t => ((z+Pi.single j l : Fin n → ℕ) t : ℝ)) ≤
      V0 a c (fun t => ((z+Pi.single i k : Fin n → ℕ) t : ℝ)) - V0 a c (fun t => (z t : ℝ))) :
    G r q x a c L (Function.update (Function.update u j (u j+α)) i
      ((Function.update u j (u j+α)) i+ε)) - G r q x a c L (Function.update u j (u j+α)) ≤
      G r q x a c L (Function.update u i (u i+ε)) - G r q x a c L u := by
  have h := expected_differences P hP L hL (fun z => V0 a c (fun t => (z t : ℝ)))
    (fun u hu => service_integrable a c hc P L hL u hu) u hu i j ε α hε hα hd
  rw [increments_commute u i j ε α] at h
  rw [revenue_increment r q x a c P hP L hL _ (update_mem P hP u hu j α hα) i ε hε,
    revenue_increment r q x a c P hP L hL u hu i ε hε]
  linarith
end OverbookingResearch
namespace OverbookingResearch
lemma cast_add_single {n : ℕ} (z : Fin n → ℕ) (i : Fin n) (k : ℕ) :
    (fun t => ((z+Pi.single i k : Fin n → ℕ) t : ℝ)) = (fun t => (z t : ℝ)) + Pi.single i (k : ℝ) := by
  classical
  ext t
  by_cases ht : t=i
  · subst t; simp
  · simp [Pi.single_eq_of_ne ht]
end OverbookingResearch

open OverbookingResearch

theorem solution {n m : ℕ} (r q x : Fin n → ℝ) (hqr : ∀ i, q i ≤ r i)
    (a : Fin n → Fin (m+1) → ℝ) (c : Fin (m+1) → ℝ) (hc : ∀ j, j ≠ 0 → 0 ≤ c j)
    (P : Set ℝ) (hP : IsParamSet P) (L : Fin n → ℝ → PMF ℕ)
    (hL : ∀ i, IsSemigroupFamily P (L i)) :
    (∀ u : Fin n → ℝ, (∀ k, u k ∈ P) → ∀ i : Fin n, ∀ ε ∈ P, ∀ α ∈ P,
      G r q x a c L (Function.update u i (u i+ε+α)) - G r q x a c L (Function.update u i (u i+α))
        ≤ G r q x a c L (Function.update u i (u i+ε)) - G r q x a c L u) ∧
    Supermodularity.Monotonicity.SupermodularOn (fun u => - G r q x a c L u)
      {u : Fin n → ℝ | ∀ k, u k ∈ P} := by
  classical
  constructor
  · intro u hu i ε hε α hα
    have hd := revenue_differences r q x a c hc P hP L hL u hu i i ε α hε hα (by
      intro z k l
      simp only [cast_add_single]
      simpa only [Pi.single_add, add_assoc] using
        MiaoSample.solution a c hc (fun t => (z t : ℝ)) (fun _ => Nat.cast_nonneg _) i
          (k : ℝ) (l : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    simpa only [Function.update_self, Function.update_idem, add_right_comm (u i) α ε] using hd
  · have hdd : DecreasingDifferencesOn (G r q x a c L) (Set.pi Set.univ (fun _ : Fin n => P)) := by
      intro u hu i j hij si sj hi hj hsi hsj hsij
      have hu' : ∀ k, u k ∈ P := by simpa only [Set.mem_pi, Set.mem_univ, forall_true_left] using hu
      have hsi' : si ∈ P := by simpa using hsi i (Set.mem_univ i)
      have hsj' : sj ∈ P := by simpa using hsj j (Set.mem_univ j)
      have he : si-u i ∈ P := hP.2.2.1 _ (hu' i) _ hsi' hi
      have ha : sj-u j ∈ P := hP.2.2.1 _ (hu' j) _ hsj' hj
      have hd := revenue_differences r q x a c hc P hP L hL u hu' j i (sj-u j) (si-u i) ha he (by
        intro z k l
        simp only [cast_add_single]
        exact accepted_sample_path a c hc (fun t => (z t : ℝ))
          (fun _ => Nat.cast_nonneg _) j i hij.symm (k : ℝ) (l : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      simpa [Function.update_of_ne hij.symm] using hd
    have hh := (MiaoLattice.solution (fun _ : Fin n => P) (G r q x a c L)).mpr hdd
    simpa only [Set.pi, Set.mem_univ, forall_true_left] using hh
