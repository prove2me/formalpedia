-- Prove2me | solution 2 for WorstCaseCVaR.Box.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:56:08.657981+00:00
-- url     : https://prove2.me/submissions/efd983d9-47e4-420d-89f2-fe794bfe5204

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_DualPair
import Definitions.Def_WorstCaseCVaR_Box_Problems
import Theorems.Thm_MatousekLP_Duality_farkas_geometric

-- carved verbatim out of submission 221ed57a-3746-4605-9ef4-2d3c9169ad3e, lines 901-915

section
set_option autoImplicit false
open Matrix
variable {ρ ι : Type*} [Fintype ρ] [Fintype ι]

def IsDualFeasible (A : Matrix ρ ι ℝ) (c : ι → ℝ) (y : ρ → ℝ) : Prop := c ≤ Aᵀ *ᵥ y ∧ 0 ≤ y

def DualUnbounded (A : Matrix ρ ι ℝ) (b : ρ → ℝ) (c : ι → ℝ) : Prop :=
  ∀ M : ℝ, ∃ y, IsDualFeasible A c y ∧ b ⬝ᵥ y < M

def IsPrimalFeasible (A : Matrix ρ ι ℝ) (b : ρ → ℝ) (x : ι → ℝ) : Prop := A *ᵥ x ≤ b ∧ 0 ≤ x

end

section
set_option autoImplicit false
open Finset
open Matrix
variable {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι] (A : Matrix (ρ) (ι) ℝ) (b : ρ → ℝ) (c : ι → ℝ)

def blockM : Matrix ((ρ ⊕ ι) ⊕ Unit) (ι ⊕ ρ) ℝ := fun r s =>
  match r, s with
  | .inl (.inl i), .inl j => A i j
  | .inl (.inl _), .inr _ => 0
  | .inl (.inr _), .inl _ => 0
  | .inl (.inr j), .inr i => -A i j
  | .inr _, .inl j => -c j
  | .inr _, .inr i => b i

end

section
set_option autoImplicit false
open Matrix WorstCaseCVaR.Box

def boxA (S : ℕ) : Matrix (Fin S ⊕ Fin 2) (Fin S) ℝ := fun r j =>
  Sum.elim (fun i => if i = j then 1 else 0) (fun k => if k = 0 then 1 else -1) r

def boxB {S : ℕ} (lo hi : Fin S → ℝ) : (Fin S ⊕ Fin 2) → ℝ :=
  Sum.elim (fun i => hi i-lo i) (fun k => if k = 0 then -(∑ i,lo i) else ∑ i,lo i)

lemma box_transpose {S : ℕ} (y : (Fin S ⊕ Fin 2) → ℝ) (i : Fin S) :
    ((boxA S)ᵀ *ᵥ y) i = y (Sum.inl i) + y (Sum.inr 0) - y (Sum.inr 1) := by
  simp [boxA,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type,Fin.sum_univ_two]
  ring

lemma box_dual_exists {S : ℕ} (u : Fin S → ℝ) :
    ∃ y, IsDualFeasible (boxA S) u y := by
  let y : (Fin S ⊕ Fin 2) → ℝ := Sum.elim (fun i => max (u i) 0) (fun _ => 0)
  refine ⟨y,?_,?_⟩
  · intro i
    rw [box_transpose]
    simp only [y,Sum.elim_inl,Sum.elim_inr,add_zero,sub_zero]
    exact le_max_left _ _
  · intro r
    rcases r with i | k
    · exact le_max_right _ _
    · exact le_rfl

def recoverDual {S : ℕ} (u : Fin S → ℝ) (y : (Fin S ⊕ Fin 2) → ℝ) : Dual23 S :=
  ⟨y (Sum.inr 0)-y (Sum.inr 1),fun i => y (Sum.inl i),
    fun i => u i-(y (Sum.inr 0)-y (Sum.inr 1))-y (Sum.inl i)⟩

lemma box_objective {S : ℕ} (lo hi u : Fin S → ℝ) (y : (Fin S ⊕ Fin 2) → ℝ) :
    lp23Obj lo hi (recoverDual u y) = lo ⬝ᵥ u + boxB lo hi ⬝ᵥ y := by
  simp only [lp23Obj,recoverDual,dotProduct,boxB,Fintype.sum_sum_type,Sum.elim_inl,
    Sum.elim_inr,Fin.sum_univ_two,Fin.reduceEq,ite_true,ite_false]
  simp_rw [mul_sub,sub_mul]
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum]
  ring

lemma box_rows {S : ℕ} (x : Fin S → ℝ) :
    (∀ i, (boxA S *ᵥ x) (Sum.inl i) = x i) ∧
    (boxA S *ᵥ x) (Sum.inr 0) = ∑ i,x i ∧
    (boxA S *ᵥ x) (Sum.inr 1) = -(∑ i,x i) := by
  constructor
  · intro i
    simp [boxA,mulVec,dotProduct]
  · constructor <;> simp [boxA,mulVec,dotProduct,← Finset.sum_neg_distrib]

lemma box_primal_exists {S : ℕ} (lo hi : Fin S → ℝ)
    (hf : (lp22Feasible lo hi).Nonempty) :
    ∃ x, IsPrimalFeasible (boxA S) (boxB lo hi) x := by
  obtain ⟨η,hη⟩ := hf
  rcases hη with ⟨hs,hl,hh⟩
  refine ⟨η-lo,?_,fun i => sub_nonneg.mpr (hl i)⟩
  have hsum : (∑ i,(η-lo) i) = -(∑ i,lo i) := by
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,hs,zero_sub]
  intro r
  rcases r with i | k
  · rw [(box_rows _).1 i]
    change η i - lo i ≤ hi i - lo i
    exact sub_le_sub_right (hh i) _
  · fin_cases k
    · change (boxA S *ᵥ (η-lo)) (Sum.inr (0 : Fin 2)) ≤ _
      rw [(box_rows _).2.1,hsum]; exact le_rfl
    · change (boxA S *ᵥ (η-lo)) (Sum.inr (1 : Fin 2)) ≤ _
      rw [(box_rows _).2.2,hsum]; simp [boxB]

lemma box_recover_dual {S : ℕ} (u : Fin S → ℝ) (y : (Fin S ⊕ Fin 2) → ℝ)
    (hy : IsDualFeasible (boxA S) u y) : recoverDual u y ∈ lp23Feasible u := by
  refine ⟨?_,fun i => hy.2 (Sum.inl i),?_⟩
  · funext i
    simp only [recoverDual,Pi.add_apply]
    ring
  · intro i
    have hi := hy.1 i
    rw [box_transpose] at hi
    change u i - (y (Sum.inr 0)-y (Sum.inr 1))-y (Sum.inl i) ≤ 0
    linarith

lemma box_recover_primal {S : ℕ} (lo hi x : Fin S → ℝ)
    (hx : IsPrimalFeasible (boxA S) (boxB lo hi) x) :
    lo+x ∈ lp22Feasible lo hi := by
  have h0 := hx.1 (Sum.inr 0)
  have h1 := hx.1 (Sum.inr 1)
  rw [(box_rows _).2.1] at h0
  rw [(box_rows _).2.2] at h1
  have hs : (∑ i,x i) = -(∑ i,lo i) := by
    simp only [boxB,Sum.elim_inr,ite_true,Fin.reduceEq,ite_false] at h0 h1
    linarith
  refine ⟨?_,?_,?_⟩
  · simp only [Pi.add_apply,Finset.sum_add_distrib,hs,add_neg_cancel]
  · intro i
    have hi : 0 ≤ x i := hx.2 i
    change lo i ≤ lo i+x i
    linarith
  · intro i
    have hbound := hx.1 (Sum.inl i)
    rw [(box_rows _).1] at hbound
    change x i ≤ hi i-lo i at hbound
    change lo i+x i ≤ hi i
    linarith

end

section
set_option autoImplicit false
open Finset
open Matrix

theorem farkas_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro h
    set a : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
    rcases MatousekLP.Duality.farkas_geometric a (WithLp.toLp 2 b) with ⟨hb, -⟩ | ⟨⟨y, hy, hyb⟩, -⟩
    · obtain ⟨t, ht, hbt⟩ := hb
      refine ⟨t, fun i => ht i, ?_⟩
      have hb' : b = ∑ j, t j • (fun i => A i j) := by
        have := congrArg WithLp.ofLp hbt
        simpa [a, WithLp.ofLp_sum, WithLp.ofLp_smul] using this
      rw [hb']
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · exfalso
      set y' : Fin m → ℝ := WithLp.ofLp y
      have hy' : 0 ≤ Aᵀ *ᵥ y' := by
        intro j
        have := hy j
        simp only [a] at this
        have hy_eq : y = WithLp.toLp 2 y' := rfl
        rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at this
        simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
      have := h y' hy'
      have hy_eq : y = WithLp.toLp 2 y' := rfl
      rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at hyb
      simp only [star_trivial] at hyb
      rw [dotProduct_comm] at hyb
      linarith

theorem farkas_eq_fintype {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ι
  set A' : Matrix (Fin m) (Fin (Fintype.card ι)) ℝ := A.submatrix id e.symm
  have hmul : ∀ x : ι → ℝ, A' *ᵥ (x ∘ e.symm) = A *ᵥ x := by
    intro x; funext i
    simp only [A', mulVec, dotProduct, submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp e.symm (fun j => A i j * x j)
  have htr : ∀ y : Fin m → ℝ, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := by
    intro y; funext j; simp [A', mulVec, dotProduct, transpose_apply]
  have hnonneg : ∀ y : Fin m → ℝ, (0 ≤ A'ᵀ *ᵥ y ↔ 0 ≤ Aᵀ *ᵥ y) := by
    intro y; rw [htr]
    constructor
    · intro h j; simpa using h (e j)
    · intro h j; exact h _
  rw [show (∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      (∀ y : Fin m → ℝ, 0 ≤ A'ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) from
      forall_congr' fun y => by rw [hnonneg]]
  rw [← farkas_eq A' b]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x ∘ e.symm, fun j => hx _, hmul x⟩
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x' ∘ e, fun j => hx' _, ?_⟩
    rw [← hmul]; congr 1; funext j; simp

theorem farkas_eq_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : ρ → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ρ
  set A' : Matrix (Fin (Fintype.card ρ)) ι ℝ := A.submatrix e.symm id
  have h := farkas_eq_fintype A' (b ∘ e.symm)
  have hrow : ∀ x : ι → ℝ, A' *ᵥ x = (A *ᵥ x) ∘ e.symm := by
    intro x; funext r; simp [A', mulVec, dotProduct]
  have hcol : ∀ y' : Fin (Fintype.card ρ) → ℝ, A'ᵀ *ᵥ y' = Aᵀ *ᵥ (y' ∘ e) := by
    intro y'; funext j
    simp only [A', mulVec, dotProduct, transpose_apply, submatrix_apply, id, Function.comp]
    rw [← Equiv.sum_comp e (fun x => A (e.symm x) j * y' x)]
    simp
  have hdot : ∀ y' : Fin (Fintype.card ρ) → ℝ, y' ⬝ᵥ (b ∘ e.symm) = (y' ∘ e) ⬝ᵥ b := by
    intro y'
    simp only [dotProduct, Function.comp]
    rw [← Equiv.sum_comp e (fun x => y' x * b (e.symm x))]
    simp
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro hy
    obtain ⟨x, hx, hAx⟩ := h.mpr fun y' hy' => by
      rw [hcol] at hy'; rw [hdot]; exact hy _ hy'
    refine ⟨x, hx, ?_⟩
    funext r
    have := congrFun hAx (e r)
    rw [hrow] at this; simpa using this

theorem farkas_le_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ↔ ∀ y : ρ → ℝ, 0 ≤ y → 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  have h := farkas_eq_gen (fromCols A (1 : Matrix ρ ρ ℝ)) b
  have hleft : (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ↔
      ∃ z : ι ⊕ ρ → ℝ, 0 ≤ z ∧ fromCols A 1 *ᵥ z = b := by
    constructor
    · rintro ⟨x, hx, hAx⟩
      refine ⟨Sum.elim x (b - A *ᵥ x), fun j => ?_, ?_⟩
      · rcases j with j | j
        · exact hx j
        · simpa using hAx j
      · rw [fromCols_mulVec_sumElim, one_mulVec]; abel
    · rintro ⟨z, hz, hzb⟩
      refine ⟨fun j => z (Sum.inl j), fun j => hz _, ?_⟩
      have hz' : z = Sum.elim (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j)) := by
        funext j; rcases j <;> rfl
      rw [hz', fromCols_mulVec_sumElim, one_mulVec] at hzb
      intro i
      have h1 := congrFun hzb i
      have h2 := hz (Sum.inr i)
      simp only [Pi.add_apply, Pi.zero_apply] at h1 h2
      linarith
  have hright : (∀ y : ρ → ℝ, 0 ≤ (fromCols A (1 : Matrix ρ ρ ℝ))ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      ∀ y : ρ → ℝ, 0 ≤ y → 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
    refine forall_congr' fun y => ?_
    rw [transpose_fromCols, transpose_one]
    constructor
    · intro hh hy hAy
      refine hh fun j => ?_
      rcases j with j | j
      · simpa [fromRows_mulVec] using hAy j
      · simpa [fromRows_mulVec] using hy j
    · intro hh hpos
      exact hh (fun i => by simpa [fromRows_mulVec] using hpos (Sum.inr i))
        (fun j => by simpa [fromRows_mulVec] using hpos (Sum.inl j))
  rw [hleft, h, hright]

end

section
set_option autoImplicit false
open Finset
open Matrix
variable {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι] (A : Matrix (ρ) (ι) ℝ) (b : ρ → ℝ) (c : ι → ℝ)

lemma weak {x : ι → ℝ} {y : ρ → ℝ} (hx : IsPrimalFeasible A b x)
    (hy : IsDualFeasible A c y) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  obtain ⟨hAx, hx0⟩ := hx; obtain ⟨hAy, hy0⟩ := hy
  calc c ⬝ᵥ x ≤ (Aᵀ *ᵥ y) ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hAy hx0
    _ = y ⬝ᵥ (A *ᵥ x) := by rw [mulVec_transpose, ← dotProduct_mulVec]
    _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hAx hy0
    _ = b ⬝ᵥ y := dotProduct_comm _ _

lemma strong (hP : ∃ x, IsPrimalFeasible A b x) (hD : ∃ y, IsDualFeasible A c y) :
    ∃ x y, IsPrimalFeasible A b x ∧ IsDualFeasible A c y ∧ b ⬝ᵥ y ≤ c ⬝ᵥ x := by
  classical
  set rhs : (ρ ⊕ ι) ⊕ Unit → ℝ := Sum.elim (Sum.elim b (-c)) (fun _ => 0)
  by_cases hfeas : ∃ z : ι ⊕ ρ → ℝ, 0 ≤ z ∧ blockM A b c *ᵥ z ≤ rhs
  · obtain ⟨z, hz, hMz⟩ := hfeas
    set x : ι → ℝ := fun j => z (Sum.inl j)
    set y : ρ → ℝ := fun i => z (Sum.inr i)
    have hrow : ∀ r, (blockM A b c *ᵥ z) r = match r with
        | .inl (.inl i) => (A *ᵥ x) i
        | .inl (.inr j) => -(Aᵀ *ᵥ y) j
        | .inr _ => -(c ⬝ᵥ x) + b ⬝ᵥ y := by
      intro r
      rcases r with (i | j) | u
      · simp [mulVec, dotProduct, blockM, Fintype.sum_sum_type, x]
      · simp [mulVec, dotProduct, blockM, Fintype.sum_sum_type, y, transpose_apply, Finset.sum_neg_distrib]
      · simp [mulVec, dotProduct, blockM, Fintype.sum_sum_type, x, y, Finset.sum_neg_distrib, mul_comm]
    refine ⟨x, y, ⟨fun i => ?_, fun j => hz _⟩, ⟨fun j => ?_, fun i => hz _⟩, ?_⟩
    · have := hMz (Sum.inl (Sum.inl i)); rw [hrow] at this; simpa [rhs] using this
    · have := hMz (Sum.inl (Sum.inr j)); rw [hrow] at this; simp [rhs] at this; linarith
    · have := hMz (Sum.inr ()); rw [hrow] at this; simp [rhs] at this; linarith
  · exfalso
    rw [farkas_le_gen] at hfeas
    push_neg at hfeas
    obtain ⟨w, hw0, hMw, hwr⟩ := hfeas
    set u : ρ → ℝ := fun i => w (Sum.inl (Sum.inl i))
    set v : ι → ℝ := fun j => w (Sum.inl (Sum.inr j))
    set s : ℝ := w (Sum.inr ())
    have hu0 : 0 ≤ u := fun i => hw0 _
    have hv0 : 0 ≤ v := fun j => hw0 _
    have hs0 : 0 ≤ s := hw0 _
    have hcolx : ∀ j, s * c j ≤ (Aᵀ *ᵥ u) j := by
      intro j
      have := hMw (Sum.inl j)
      simp [mulVec, dotProduct, blockM, transpose_apply, Fintype.sum_sum_type, u, s] at this
      simp [mulVec, dotProduct, transpose_apply, u]
      linarith
    have hcoly : ∀ i, (A *ᵥ v) i ≤ s * b i := by
      intro i
      have := hMw (Sum.inr i)
      simp [mulVec, dotProduct, blockM, transpose_apply, Fintype.sum_sum_type, v, s,
        Finset.sum_neg_distrib] at this
      simp [mulVec, dotProduct, v]
      linarith
    have hval : u ⬝ᵥ b - v ⬝ᵥ c < 0 := by
      simp [dotProduct, rhs, Fintype.sum_sum_type, u, v] at hwr
      simp [dotProduct, Finset.sum_neg_distrib] at hwr ⊢
      linarith
    obtain ⟨x₀, hx₀⟩ := hP
    obtain ⟨y₀, hy₀⟩ := hD
    rcases hs0.lt_or_eq with hs | hs
    · -- scale: v/s is primal feasible, u/s is dual feasible
      have hxs : IsPrimalFeasible A b (s⁻¹ • v) := by
        refine ⟨fun i => ?_, fun j => ?_⟩
        · rw [mulVec_smul]; simp only [Pi.smul_apply, smul_eq_mul]
          rw [inv_mul_le_iff₀ hs]; exact hcoly i
        · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact mul_nonneg (inv_nonneg.mpr hs.le) (hv0 j)
      have hys : IsDualFeasible A c (s⁻¹ • u) := by
        refine ⟨fun j => ?_, fun i => ?_⟩
        · rw [mulVec_smul]; simp only [Pi.smul_apply, smul_eq_mul]
          rw [le_inv_mul_iff₀ hs]; exact hcolx j
        · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact mul_nonneg (inv_nonneg.mpr hs.le) (hu0 i)
      have := weak A b c hxs hys
      rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      have h2 := mul_le_mul_of_nonneg_left this hs.le
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, one_mul] at h2
      rw [dotProduct_comm u b, dotProduct_comm v c] at hval
      linarith
    · -- s = 0: rays in both problems contradict weak duality for large t
      have hAu : ∀ j, 0 ≤ (Aᵀ *ᵥ u) j := fun j => by have := hcolx j; rw [← hs] at this; simpa using this
      have hAv : ∀ i, (A *ᵥ v) i ≤ 0 := fun i => by have := hcoly i; rw [← hs] at this; simpa using this
      have hgap : 0 < c ⬝ᵥ v - b ⬝ᵥ u := by
        rw [dotProduct_comm u b, dotProduct_comm v c] at hval; linarith
      set t : ℝ := (b ⬝ᵥ y₀ - c ⬝ᵥ x₀) / (c ⬝ᵥ v - b ⬝ᵥ u) + 1
      have ht : 0 ≤ t := by
        have := weak A b c hx₀ hy₀
        have : 0 ≤ (b ⬝ᵥ y₀ - c ⬝ᵥ x₀) / (c ⬝ᵥ v - b ⬝ᵥ u) := div_nonneg (by linarith) hgap.le
        linarith
      have hxt : IsPrimalFeasible A b (x₀ + t • v) := by
        refine ⟨fun i => ?_, fun j => ?_⟩
        · have h1 := hx₀.1 i; have h2 := hAv i
          simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
          nlinarith
        · have := hx₀.2 j; have := hv0 j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
          positivity
      have hyt : IsDualFeasible A c (y₀ + t • u) := by
        refine ⟨fun j => ?_, fun i => ?_⟩
        · have h1 := hy₀.1 j; have h2 := hAu j
          simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
          nlinarith
        · have := hy₀.2 i; have := hu0 i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
          positivity
      have := weak A b c hxt hyt
      rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul] at this
      have hmul : (b ⬝ᵥ y₀ - c ⬝ᵥ x₀) < t * (c ⬝ᵥ v - b ⬝ᵥ u) := by
        rw [← div_lt_iff₀ hgap]; linarith
      nlinarith

end

section
set_option autoImplicit false
open Matrix WorstCaseCVaR.Box

lemma weak_pair {S : ℕ} (ηlo ηhi u η : Fin S → ℝ)
    (hη : η ∈ lp22Feasible ηlo ηhi) (d : Dual23 S) (hd : d ∈ lp23Feasible u) :
    u ⬝ᵥ η ≤ lp23Obj ηlo ηhi d := by
  classical
  rcases hη with ⟨hs,hl,hh⟩
  rcases hd with ⟨hu,hξ,hω⟩
  change (∑ k, u k * η k) ≤ (∑ k, ηhi k * d.ξ k) + ∑ k, ηlo k * d.ω k
  have hp (k : Fin S) : u k = d.z + d.ξ k + d.ω k := by
    have h := congrFun hu k
    simpa only [Pi.add_apply] using h.symm
  simp_rw [hp,add_mul,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,hs,mul_zero,zero_add,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have h1 := mul_le_mul_of_nonneg_left (hh k) (hξ k)
  have h2 := mul_le_mul_of_nonpos_left (hl k) (hω k)
  nlinarith

lemma box_certificate {S : ℕ} (lo hi u : Fin S → ℝ)
    (hf : (lp22Feasible lo hi).Nonempty) :
    ∃ η ∈ lp22Feasible lo hi, ∃ d ∈ lp23Feasible u, u ⬝ᵥ η = lp23Obj lo hi d := by
  obtain ⟨x,y,hx,hy,hval⟩ := strong (boxA S) (boxB lo hi) u
    (box_primal_exists lo hi hf) (box_dual_exists u)
  have hp := box_recover_primal lo hi x hx
  have hd := box_recover_dual u y hy
  refine ⟨lo+x,hp,recoverDual u y,hd,le_antisymm (weak_pair lo hi u _ hp _ hd) ?_⟩
  rw [box_objective,dotProduct_add,dotProduct_comm u lo]
  exact add_le_add le_rfl hval

lemma box_gamma_attained {S : ℕ} (lo hi u : Fin S → ℝ)
    (hf : (lp22Feasible lo hi).Nonempty) :
    IsGreatest ((fun η => u ⬝ᵥ η) '' lp22Feasible lo hi) (gammaStar lo hi u) := by
  obtain ⟨η,hη,d,hd,he⟩ := box_certificate lo hi u hf
  have hm : IsGreatest ((fun η => u ⬝ᵥ η) '' lp22Feasible lo hi) (u ⬝ᵥ η) := by
    refine ⟨⟨η,hη,rfl⟩,?_⟩
    rintro y ⟨η',hη',rfl⟩
    rw [he]
    exact weak_pair lo hi u η' hη' d hd
  change IsGreatest _ (sSup _)
  rw [hm.csSup_eq]
  exact hm

end

section
set_option autoImplicit false
open Finset
open Matrix
variable {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι] (A : Matrix (ρ) (ι) ℝ) (b : ρ → ℝ) (c : ι → ℝ)

lemma dual_unbounded (hD : ∃ y, IsDualFeasible A c y) (hP : ¬ ∃ x, IsPrimalFeasible A b x) :
    DualUnbounded A b c := by
  have hF := farkas_le_gen A b
  have hinf : ¬ ∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b := by
    rintro ⟨x, hx, hAx⟩; exact hP ⟨x, hAx, hx⟩
  rw [hF] at hinf
  push_neg at hinf
  obtain ⟨v, hv0, hAv, hvb⟩ := hinf
  obtain ⟨y₀, hAy₀, hy₀⟩ := hD
  intro M
  have hbv : b ⬝ᵥ v < 0 := by rw [dotProduct_comm]; exact hvb
  set t : ℝ := max 0 ((b ⬝ᵥ y₀ - M) / (-(b ⬝ᵥ v)) + 1)
  have ht : 0 ≤ t := le_max_left _ _
  refine ⟨y₀ + t • v, ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
  · have h1 := hAy₀ j; have h2 := hAv j
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    nlinarith
  · have := hy₀ i; have := hv0 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    positivity
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have h1 : (b ⬝ᵥ y₀ - M) / (-(b ⬝ᵥ v)) + 1 ≤ t := le_max_right _ _
    have hpos : 0 < -(b ⬝ᵥ v) := by linarith
    have h2 : b ⬝ᵥ y₀ - M < t * (-(b ⬝ᵥ v)) := by
      rw [← div_lt_iff₀ hpos]; linarith
    linarith

end

section
set_option autoImplicit false
open Matrix WorstCaseCVaR.Box

lemma box_nonempty_of_dual_bound {S : ℕ} (lo hi u : Fin S → ℝ) (B : ℝ)
    (hb : ∀ d ∈ lp23Feasible u, B ≤ lp23Obj lo hi d) :
    (lp22Feasible lo hi).Nonempty := by
  by_contra hn
  have hp : ¬ ∃ x, IsPrimalFeasible (boxA S) (boxB lo hi) x := by
    rintro ⟨x,hx⟩
    exact hn ⟨lo+x,box_recover_primal lo hi x hx⟩
  obtain ⟨y,hy,hval⟩ := dual_unbounded (boxA S) (boxB lo hi) u
    (box_dual_exists u) hp (B-lo ⬝ᵥ u)
  have h := hb (recoverDual u y) (box_recover_dual u y hy)
  rw [box_objective] at h
  linarith

lemma box_nonempty_of_optimal {S : ℕ} (lo hi u : Fin S → ℝ) (d : Dual23 S)
    (hd : IsOptimal23 lo hi u d) : (lp22Feasible lo hi).Nonempty :=
  box_nonempty_of_dual_bound lo hi u (lp23Obj lo hi d)
    (fun d' hd' => isMinOn_iff.mp hd.2 d' hd')

theorem weak_duality {S : ℕ} (ηlo ηhi u : Fin S → ℝ) :
    (∀ η ∈ lp22Feasible ηlo ηhi, ∀ d ∈ lp23Feasible u, u ⬝ᵥ η ≤ lp23Obj ηlo ηhi d) ∧
    ((lp22Feasible ηlo ηhi).Nonempty →
      ∀ d ∈ lp23Feasible u, gammaStar ηlo ηhi u ≤ lp23Obj ηlo ηhi d) := by
  refine ⟨fun η hη d hd => weak_pair ηlo ηhi u η hη d hd,?_⟩
  intro hne d hd
  apply csSup_le (hne.image _)
  rintro y ⟨η,hη,rfl⟩
  exact weak_pair ηlo ηhi u η hη d hd

theorem strong_duality {S : ℕ} (ηlo ηhi u : Fin S → ℝ)
    (hfeas : (lp22Feasible ηlo ηhi).Nonempty) :
    (∃ d, IsOptimal23 ηlo ηhi u d) ∧
    ∀ d, IsOptimal23 ηlo ηhi u d → lp23Obj ηlo ηhi d = gammaStar ηlo ηhi u := by
  obtain ⟨η,hη,d,hd,he⟩ := box_certificate ηlo ηhi u hfeas
  have hg := box_gamma_attained ηlo ηhi u hfeas
  have hopt : IsOptimal23 ηlo ηhi u d := by
    refine ⟨hd,isMinOn_iff.mpr ?_⟩
    intro d' hd'
    rw [← he]
    exact weak_pair ηlo ηhi u η hη d' hd'
  refine ⟨⟨d,hopt⟩,?_⟩
  intro d' hd'
  have h1 := (weak_duality ηlo ηhi u).2 hfeas d' hd'.1
  have h2 := isMinOn_iff.mp hd'.2 d hd
  have h3 := hg.2 ⟨η,hη,rfl⟩
  exact le_antisymm (h2.trans (he.symm.le.trans h3)) h1

theorem feasible_16_to_24 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi : Fin S → ℝ) :
    ∀ p ∈ feas16 f ys 𝒳 β π0 ηlo ηhi, ∀ d, IsOptimal23 ηlo ηhi p.u d →
      p.withDual d ∈ feas24 f ys 𝒳 β π0 ηlo ηhi := by
  intro p hp d hd
  rcases hp with ⟨hX,hθ,hL,hN⟩
  have hf := box_nonempty_of_optimal ηlo ηhi p.u d hd
  have hv := (strong_duality ηlo ηhi p.u hf).2 d hd
  obtain ⟨η,hη,he⟩ := (box_gamma_attained ηlo ηhi p.u hf).1
  change p.u ⬝ᵥ η = gammaStar ηlo ηhi p.u at he
  have hπ : π0+η ∈ boxSet π0 ηlo ηhi := ⟨η,rfl,hη.1,hη.2⟩
  change p.x ∈ 𝒳 ∧
    p.α+(1-β)⁻¹*(π0 ⬝ᵥ p.u)+(1-β)⁻¹*(ηhi ⬝ᵥ d.ξ+ηlo ⬝ᵥ d.ω) ≤ p.θ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hX,?_,hd.1.1,hd.1.2.1,hd.1.2.2,hL,hN⟩
  change p.α+(1-β)⁻¹*(π0 ⬝ᵥ p.u)+(1-β)⁻¹*lp23Obj ηlo ηhi d ≤ p.θ
  calc
    _ = p.α+(1-β)⁻¹*((π0+η) ⬝ᵥ p.u) := by
      rw [hv,add_dotProduct,dotProduct_comm η p.u,he]
      ring
    _ ≤ _ := hθ _ hπ

theorem feasible_24_to_16 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi : Fin S → ℝ) :
    ∀ q ∈ feas24 f ys 𝒳 β π0 ηlo ηhi, q.toVar16 ∈ feas16 f ys 𝒳 β π0 ηlo ηhi := by
  intro q hq
  rcases hq with ⟨hX,hθ,he,hξ,hω,hL,hN⟩
  change q.x ∈ 𝒳 ∧ (∀ π ∈ boxSet π0 ηlo ηhi, q.α+(1-β)⁻¹*(π ⬝ᵥ q.u) ≤ q.θ) ∧ _ ∧ _
  refine ⟨hX,?_,hL,hN⟩
  intro π hπ
  rcases hπ with ⟨η,hπ,hs,hl,hh⟩
  let d : Dual23 S := ⟨q.z,q.ξ,q.ω⟩
  have hd : d ∈ lp23Feasible q.u := ⟨he,hξ,hω⟩
  have hw := weak_pair ηlo ηhi q.u η ⟨hs,hl,hh⟩ d hd
  change q.u ⬝ᵥ η ≤ ηhi ⬝ᵥ q.ξ+ηlo ⬝ᵥ q.ω at hw
  rw [hπ,add_dotProduct,dotProduct_comm η q.u]
  have hc : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hw hc]

lemma nonempty_of_solves16 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ)
    (π0 lo hi : Fin S → ℝ) (p : Var16 n S)
    (hp : Solves16 f ys 𝒳 β π0 lo hi p) : (lp22Feasible lo hi).Nonempty := by
  by_contra hn
  let p' : Var16 n S := ⟨p.x,p.u,p.α,p.θ-1⟩
  have hf : p' ∈ feas16 f ys 𝒳 β π0 lo hi := by
    refine ⟨hp.1.1,?_,hp.1.2.2.1,hp.1.2.2.2⟩
    intro π hπ
    rcases hπ with ⟨η,he,hs,hl,hh⟩
    exact False.elim (hn ⟨η,hs,hl,hh⟩)
  have h := isMinOn_iff.mp hp.2 p' hf
  change p.θ ≤ p.θ-1 at h
  linarith

lemma nonempty_of_solves24 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ1 : β < 1)
    (π0 lo hi : Fin S → ℝ) (q : Var24 n S)
    (hq : Solves24 f ys 𝒳 β π0 lo hi q) : (lp22Feasible lo hi).Nonempty := by
  let c := (1-β)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  apply box_nonempty_of_dual_bound lo hi q.u ((q.θ-q.α-c*(π0 ⬝ᵥ q.u))/c)
  intro d hd
  let q' : Var24 n S := ⟨q.x,q.u,d.z,d.ξ,d.ω,q.α,q.α+c*(π0 ⬝ᵥ q.u)+c*lp23Obj lo hi d⟩
  have hf : q' ∈ feas24 f ys 𝒳 β π0 lo hi := by
    exact ⟨hq.1.1,le_rfl,hd.1,hd.2.1,hd.2.2,hq.1.2.2.2.2.2.1,hq.1.2.2.2.2.2.2⟩
  have h := isMinOn_iff.mp hq.2 q' hf
  change q.θ ≤ q.α+c*(π0 ⬝ᵥ q.u)+c*lp23Obj lo hi d at h
  apply (div_le_iff₀ hc).mpr
  linarith

theorem proposition_2 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi : Fin S → ℝ) :
    (∀ q : Var24 n S, Solves24 f ys 𝒳 β π0 ηlo ηhi q →
      Solves16 f ys 𝒳 β π0 ηlo ηhi q.toVar16) ∧
    (∀ p : Var16 n S, Solves16 f ys 𝒳 β π0 ηlo ηhi p →
      ∀ d : Dual23 S, IsOptimal23 ηlo ηhi p.u d →
        Solves24 f ys 𝒳 β π0 ηlo ηhi (p.withDual d)) ∧
    (∀ p : Var16 n S, Solves16 f ys 𝒳 β π0 ηlo ηhi p →
      ∃ d : Dual23 S, IsOptimal23 ηlo ηhi p.u d) := by
  constructor
  · intro q hq
    have hbox := nonempty_of_solves24 f ys 𝒳 β hβ1 π0 ηlo ηhi q hq
    refine ⟨feasible_24_to_16 f ys 𝒳 β hβ0 hβ1 π0 ηlo ηhi q hq.1,isMinOn_iff.mpr ?_⟩
    intro p hp
    obtain ⟨d,hd⟩ := (strong_duality ηlo ηhi p.u hbox).1
    have hf := feasible_16_to_24 f ys 𝒳 β hβ0 hβ1 π0 ηlo ηhi p hp d hd
    exact isMinOn_iff.mp hq.2 (p.withDual d) hf
  · constructor
    · intro p hp d hd
      refine ⟨feasible_16_to_24 f ys 𝒳 β hβ0 hβ1 π0 ηlo ηhi p hp.1 d hd,isMinOn_iff.mpr ?_⟩
      intro q hq
      have hf := feasible_24_to_16 f ys 𝒳 β hβ0 hβ1 π0 ηlo ηhi q hq
      exact isMinOn_iff.mp hp.2 q.toVar16 hf
    · intro p hp
      exact (strong_duality ηlo ηhi p.u (nonempty_of_solves16 f ys 𝒳 β π0 ηlo ηhi p hp)).1

theorem solution {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π0 ηlo ηhi : Fin S → ℝ) :
    (∀ q : Var24 n S, Solves24 f ys 𝒳 β π0 ηlo ηhi q →
      Solves16 f ys 𝒳 β π0 ηlo ηhi q.toVar16) ∧
    (∀ p : Var16 n S, Solves16 f ys 𝒳 β π0 ηlo ηhi p →
      ∀ d : Dual23 S, IsOptimal23 ηlo ηhi p.u d →
        Solves24 f ys 𝒳 β π0 ηlo ηhi (p.withDual d)) ∧
    (∀ p : Var16 n S, Solves16 f ys 𝒳 β π0 ηlo ηhi p →
      ∃ d : Dual23 S, IsOptimal23 ηlo ηhi p.u d) := proposition_2 f ys 𝒳 β hβ0 hβ1 π0 ηlo ηhi

end
