-- Prove2me | solution 1 for RvsCert.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T01:06:09.433517+00:00
-- url     : https://prove2.me/submissions/bce2bf42-ca05-43e2-87d5-0207a057bc47

import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_quantQC
import Definitions.Def_RvsCert_randQC
import Mathlib
import Theorems.Thm_RvsCert_lemma_3_first_stage

section File_Ops

open QAlgorithms

namespace QComp

/-! ### Op lists and their semantics on plain vectors -/

abbrev R (ι W : Type) := (ι × Bool) × W

inductive Op (X : Type) where
  | u : Matrix X X ℂ → Op X
  | q : Op X

section Sem

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-- The query matrix `O ⊗ I_W`. -/
noncomputable def qmat (O : Matrix (ι × Bool) (ι × Bool) ℂ) : Matrix (R ι W) (R ι W) ℂ :=
  Matrix.kronecker O (1 : Matrix W W ℂ)

noncomputable def Op.apply (O : Matrix (ι × Bool) (ι × Bool) ℂ) :
    Op (R ι W) → (R ι W → ℂ) → (R ι W → ℂ)
  | .u M, v => M.mulVec v
  | .q, v => (qmat O).mulVec v

noncomputable def runOps (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l : List (Op (R ι W)))
    (v : R ι W → ℂ) : R ι W → ℂ :=
  l.foldl (fun v op => Op.apply O op v) v

theorem runOps_nil (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι W → ℂ) :
    runOps O [] v = v := rfl

theorem runOps_append (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l₁ l₂ : List (Op (R ι W)))
    (v : R ι W → ℂ) : runOps O (l₁ ++ l₂) v = runOps O l₂ (runOps O l₁ v) := by
  simp [runOps, List.foldl_append]

theorem runOps_cons (O : Matrix (ι × Bool) (ι × Bool) ℂ) (op : Op (R ι W)) (l : List (Op (R ι W)))
    (v : R ι W → ℂ) : runOps O (op :: l) v = runOps O l (Op.apply O op v) := rfl

theorem runOps_snoc (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l : List (Op (R ι W))) (op : Op (R ι W))
    (v : R ι W → ℂ) : runOps O (l ++ [op]) v = Op.apply O op (runOps O l v) := by
  rw [runOps_append]; rfl

end Sem

/-- Number of queries in an op list. -/
def nq {X : Type} : List (Op X) → ℕ
  | [] => 0
  | .q :: l => nq l + 1
  | .u _ :: l => nq l

theorem nq_append {X : Type} (l₁ l₂ : List (Op X)) : nq (l₁ ++ l₂) = nq l₁ + nq l₂ := by
  induction l₁ with
  | nil => simp [nq]
  | cons op l ih => cases op <;> simp [nq, ih] <;> omega

/-- All unitary steps are unitary. -/
def OkOps {X : Type} [Fintype X] [DecidableEq X] (l : List (Op X)) : Prop :=
  ∀ M, Op.u M ∈ l → M ∈ Matrix.unitaryGroup X ℂ

theorem OkOps.append {X : Type} [Fintype X] [DecidableEq X] {l₁ l₂ : List (Op X)}
    (h₁ : OkOps l₁) (h₂ : OkOps l₂) : OkOps (l₁ ++ l₂) := by
  intro M hM
  rcases List.mem_append.1 hM with h | h
  · exact h₁ M h
  · exact h₂ M h

/-! ### Unitary sequences in `QueryAlg` form -/

section RunU

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

noncomputable def indU {T : ℕ} (U : Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι W → ℂ) : Fin (T + 1) → (R ι W → ℂ) :=
  Fin.induction ((U 0).mulVec v) (fun i φ => (U i.succ).mulVec ((qmat O).mulVec φ))

noncomputable def runU {T : ℕ} (U : Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι W → ℂ) : R ι W → ℂ :=
  indU U O v (Fin.last T)

theorem indU_snoc {T : ℕ} (U : Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (M : Matrix (R ι W) (R ι W) ℂ) (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι W → ℂ) :
    ∀ j : Fin (T + 1),
      indU (Fin.snoc (α := fun _ => Matrix (R ι W) (R ι W) ℂ) U M) O v j.castSucc =
        indU U O v j := by
  intro j
  induction j using Fin.induction with
  | zero =>
    simp only [indU, Fin.castSucc_zero, Fin.induction_zero]
    have h0 := Fin.snoc_castSucc (α := fun _ => Matrix (R ι W) (R ι W) ℂ) (p := U) (x := M) 0
    simp only [Fin.castSucc_zero] at h0
    rw [h0]
  | succ i ih =>
    have h1 : (i.succ).castSucc = (i.castSucc).succ := rfl
    rw [h1]
    simp only [indU] at ih ⊢
    rw [Fin.induction_succ, Fin.induction_succ, ih]
    congr 1
    exact Fin.snoc_castSucc (α := fun _ => Matrix (R ι W) (R ι W) ℂ) (p := U) (x := M) i.succ

theorem runU_snoc {T : ℕ} (U : Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (M : Matrix (R ι W) (R ι W) ℂ) (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι W → ℂ) :
    runU (Fin.snoc (α := fun _ => Matrix (R ι W) (R ι W) ℂ) U M) O v =
      M.mulVec ((qmat O).mulVec (runU U O v)) := by
  unfold runU
  have : (Fin.last (T + 1)) = (Fin.last T).succ := rfl
  rw [this]
  simp only [indU] at *
  rw [Fin.induction_succ]
  have h2 := indU_snoc U M O v (Fin.last T)
  simp only [indU] at h2
  rw [h2]
  congr 1
  exact Fin.snoc_last (α := fun _ => Matrix (R ι W) (R ι W) ℂ) (p := U) (x := M)

theorem indU_updateLast {T : ℕ} (U : Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (M : Matrix (R ι W) (R ι W) ℂ) (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι W → ℂ) :
    ∀ j : Fin (T + 1),
      indU (fun t => if t = Fin.last T then M * U t else U t) O v j =
        if j = Fin.last T then M.mulVec (indU U O v j) else indU U O v j := by
  intro j
  induction j using Fin.induction with
  | zero =>
    simp only [indU, Fin.induction_zero]
    split_ifs with h
    · rw [Matrix.mulVec_mulVec]
    · rfl
  | succ i ih =>
    simp only [indU] at ih ⊢
    rw [Fin.induction_succ, Fin.induction_succ]
    have hne : i.castSucc ≠ Fin.last T := Fin.castSucc_ne_last i
    rw [ih, if_neg hne]
    split_ifs with h
    · simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rfl

theorem runU_updateLast {T : ℕ} (U : Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (M : Matrix (R ι W) (R ι W) ℂ) (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι W → ℂ) :
    runU (fun t => if t = Fin.last T then M * U t else U t) O v = M.mulVec (runU U O v) := by
  unfold runU
  rw [indU_updateLast, if_pos rfl]

/-- Every unitary op list is a `QueryAlg`-shaped unitary sequence. -/
theorem exists_U (l : List (Op (R ι W))) (hl : OkOps l) :
    ∃ (T : ℕ) (U : Fin (T + 1) → Matrix.unitaryGroup (R ι W) ℂ), T = nq l ∧
      ∀ O v, runU (fun t => (U t : Matrix (R ι W) (R ι W) ℂ)) O v = runOps O l v := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨0, fun _ => 1, rfl, fun O v => ?_⟩
    simp [runU, indU, runOps]
  | append_singleton l op ih =>
    have hl' : OkOps l := fun M hM => hl M (List.mem_append_left _ hM)
    obtain ⟨T, U, hT, hU⟩ := ih hl'
    cases op with
    | q =>
      refine ⟨T + 1, Fin.snoc (α := fun _ => Matrix.unitaryGroup (R ι W) ℂ) U 1, ?_, fun O v => ?_⟩
      · rw [nq_append]; simp [nq, hT]
      · rw [runOps_snoc]
        have : (fun t => ((Fin.snoc (α := fun _ => Matrix.unitaryGroup (R ι W) ℂ) U 1 t :
              Matrix.unitaryGroup (R ι W) ℂ) : Matrix (R ι W) (R ι W) ℂ)) =
            Fin.snoc (α := fun _ => Matrix (R ι W) (R ι W) ℂ)
              (fun t => (U t : Matrix (R ι W) (R ι W) ℂ)) 1 := by
          funext t
          refine Fin.lastCases ?_ (fun i => ?_) t
          · simp
          · simp
        rw [this, runU_snoc, hU]
        simp [Op.apply]
    | u M =>
      have hM : M ∈ Matrix.unitaryGroup (R ι W) ℂ := hl M (by simp)
      refine ⟨T, fun t => if t = Fin.last T then ⟨M, hM⟩ * U t else U t, ?_, fun O v => ?_⟩
      · rw [nq_append]; simp [nq, hT]
      · rw [runOps_snoc]
        have : (fun t => (((if t = Fin.last T then ⟨M, hM⟩ * U t else U t) :
              Matrix.unitaryGroup (R ι W) ℂ) : Matrix (R ι W) (R ι W) ℂ)) =
            fun t => if t = Fin.last T then M * (U t : Matrix (R ι W) (R ι W) ℂ)
              else (U t : Matrix (R ι W) (R ι W) ℂ) := by
          funext t
          split_ifs <;> rfl
        rw [this, runU_updateLast, hU]
        rfl

/-- `QueryAlg.finalState` is `runU` of its unitaries on its start vector. -/
theorem ofLp_stateAt {T : ℕ} (A : QueryAlg ι Bool W T) (x : ι → Bool) (j : Fin (T + 1)) :
    WithLp.ofLp (A.stateAt (xorOracle x) j) =
      indU (fun t => (A.U t : Matrix (R ι W) (R ι W) ℂ)) (xorOracle x) (WithLp.ofLp A.start) j := by
  induction j using Fin.induction with
  | zero =>
    simp only [QueryAlg.stateAt, Fin.induction_zero, indU, act]
  | succ i ih =>
    simp only [QueryAlg.stateAt, Fin.induction_succ, indU, act] at ih ⊢
    rw [← ih]
    rfl

theorem ofLp_finalState {T : ℕ} (A : QueryAlg ι Bool W T) (x : ι → Bool) :
    WithLp.ofLp (A.finalState (xorOracle x)) =
      runU (fun t => (A.U t : Matrix (R ι W) (R ι W) ℂ)) (xorOracle x) (WithLp.ofLp A.start) :=
  ofLp_stateAt A x (Fin.last T)

/-- From an op list and a unit start vector, build a `QueryAlg` with the same final state. -/
theorem exists_alg (l : List (Op (R ι W))) (hl : OkOps l) (s : R ι W → ℂ)
    (hs : ∑ z, ‖s z‖ ^ 2 = 1) :
    ∃ A : QueryAlg ι Bool W (nq l), ∀ x : ι → Bool,
      WithLp.ofLp (A.finalState (xorOracle x)) = runOps (xorOracle x) l s := by
  obtain ⟨T, U, hT, hU⟩ := exists_U l hl
  subst hT
  refine ⟨⟨WithLp.toLp 2 s, ?_, U⟩, fun x => ?_⟩
  · rw [EuclideanSpace.norm_eq]
    simp [hs]
  · rw [ofLp_finalState]
    exact hU _ _

end RunU

end QComp

end File_Ops

section File_Block

open QAlgorithms

set_option linter.unusedSectionVars false

namespace QComp

section Block

variable {ι W C : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C]

/-- Block-diagonal matrix: `F c` on the fiber of control value `c`. -/
def blockM (F : C → Matrix (R ι W) (R ι W) ℂ) : Matrix (R ι (W × C)) (R ι (W × C)) ℂ :=
  Matrix.of fun z z' => if z.2.2 = z'.2.2 then F z.2.2 (z.1, z.2.1) (z'.1, z'.2.1) else 0

/-- The fiber of a vector over control value `c`. -/
def fiber (v : R ι (W × C) → ℂ) (c : C) : R ι W → ℂ := fun z => v (z.1, (z.2, c))

def splitE : (R ι W × C) ≃ R ι (W × C) where
  toFun p := (p.1.1, (p.1.2, p.2))
  invFun z := ((z.1, z.2.1), z.2.2)
  left_inv p := rfl
  right_inv z := rfl

theorem sum_split {M : Type} [AddCommMonoid M] (f : R ι (W × C) → M) :
    ∑ z, f z = ∑ y : R ι W, ∑ c : C, f (y.1, (y.2, c)) := by
  rw [← Equiv.sum_comp (splitE (ι := ι) (W := W) (C := C)), Fintype.sum_prod_type]
  rfl

theorem fiber_blockM_mulVec (F : C → Matrix (R ι W) (R ι W) ℂ) (v : R ι (W × C) → ℂ) (c : C) :
    fiber ((blockM F).mulVec v) c = (F c).mulVec (fiber v c) := by
  funext z
  simp only [fiber, Matrix.mulVec, dotProduct]
  rw [sum_split]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [blockM, Matrix.of_apply]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'; simp [Ne.symm hc']
  · simp

theorem fiber_qmat_mulVec (O : Matrix (ι × Bool) (ι × Bool) ℂ) (v : R ι (W × C) → ℂ) (c : C) :
    fiber ((qmat (W := W × C) O).mulVec v) c = (qmat (W := W) O).mulVec (fiber v c) := by
  funext z
  simp only [fiber, Matrix.mulVec, dotProduct]
  rw [sum_split]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single c]
  · simp [qmat, Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply, Prod.ext_iff]
  · intro c' _ hc'
    simp [qmat, Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply, Prod.ext_iff,
      Ne.symm hc']
  · simp

theorem blockM_mem_unitary (F : C → Matrix (R ι W) (R ι W) ℂ)
    (hF : ∀ c, F c ∈ Matrix.unitaryGroup (R ι W) ℂ) :
    blockM F ∈ Matrix.unitaryGroup (R ι (W × C)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext z z'
  have hc := fun c => (Matrix.mem_unitaryGroup_iff.1 (hF c))
  simp only [Matrix.mul_apply, Matrix.star_apply]
  rw [sum_split]
  have hrw : ∀ y : R ι W,
      (∑ c : C, blockM F z (y.1, (y.2, c)) * star (blockM F z' (y.1, (y.2, c)))) =
        if z.2.2 = z'.2.2 then F z.2.2 (z.1, z.2.1) y * star (F z.2.2 (z'.1, z'.2.1) y)
        else 0 := by
    intro y
    simp only [blockM, Matrix.of_apply]
    rw [Finset.sum_eq_single z.2.2]
    · by_cases h1 : z.2.2 = z'.2.2
      · rw [if_pos rfl, if_pos h1.symm, if_pos h1, h1]
      · rw [if_pos rfl, if_neg (fun h => h1 h.symm), if_neg h1]; simp
    · intro c _ hc'; simp [Ne.symm hc']
    · simp
  simp only [hrw]
  by_cases hzc : z.2.2 = z'.2.2
  · simp only [if_pos hzc]
    have key := congrFun (congrFun (hc z.2.2) (z.1, z.2.1)) (z'.1, z'.2.1)
    simp only [Matrix.mul_apply, Matrix.star_apply] at key
    rw [key]
    simp only [Matrix.one_apply]
    by_cases h : z = z'
    · subst h; simp
    · have : ¬ ((z.1, z.2.1) = (z'.1, z'.2.1)) := by
        intro h'
        apply h
        obtain ⟨q, w, c⟩ := z
        obtain ⟨q', w', c'⟩ := z'
        simp only [Prod.mk.injEq] at h' hzc
        simp [h'.1, h'.2, hzc]
      simp [h, this]
  · simp only [if_neg hzc, Finset.sum_const_zero]
    have : z ≠ z' := fun h => hzc (by rw [h])
    simp [Matrix.one_apply, this]

/-- A family of op lists with a common shape. -/
inductive FOp (C X : Type) where
  | u : (C → Matrix X X ℂ) → FOp C X
  | q : FOp C X

def FOp.big : FOp C (R ι W) → Op (R ι (W × C))
  | .u F => .u (blockM F)
  | .q => .q

def FOp.proj (c : C) : FOp C (R ι W) → Op (R ι W)
  | .u F => .u (F c)
  | .q => .q

theorem fiber_runOps (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l : List (FOp C (R ι W)))
    (v : R ι (W × C) → ℂ) (c : C) :
    fiber (runOps O (l.map FOp.big) v) c = runOps O (l.map (FOp.proj c)) (fiber v c) := by
  induction l generalizing v with
  | nil => rfl
  | cons op l ih =>
    simp only [List.map_cons, runOps_cons]
    rw [ih]
    congr 1
    cases op with
    | u F => exact fiber_blockM_mulVec F v c
    | q => exact fiber_qmat_mulVec O v c

def FOkOps (l : List (FOp C (R ι W))) : Prop :=
  ∀ F, FOp.u F ∈ l → ∀ c, F c ∈ Matrix.unitaryGroup (R ι W) ℂ

theorem FOkOps.big {l : List (FOp C (R ι W))} (h : FOkOps l) : OkOps (l.map FOp.big) := by
  intro M hM
  obtain ⟨op, hop, he⟩ := List.mem_map.1 hM
  cases op with
  | u F =>
    simp only [FOp.big, Op.u.injEq] at he
    subst he
    exact blockM_mem_unitary F (h F hop)
  | q => simp [FOp.big] at he

def nqF : List (FOp C (R ι W)) → ℕ
  | [] => 0
  | .q :: l => nqF l + 1
  | .u _ :: l => nqF l

theorem nq_big (l : List (FOp C (R ι W))) : nq (l.map FOp.big) = nqF l := by
  induction l with
  | nil => rfl
  | cons op l ih => cases op <;> simp [FOp.big, nq, nqF, ih]

theorem nqF_append (l₁ l₂ : List (FOp C (R ι W))) : nqF (l₁ ++ l₂) = nqF l₁ + nqF l₂ := by
  induction l₁ with
  | nil => simp [nqF]
  | cons op l ih => cases op <;> simp [nqF, ih] <;> omega

theorem FOkOps.append {l₁ l₂ : List (FOp C (R ι W))} (h₁ : FOkOps l₁) (h₂ : FOkOps l₂) :
    FOkOps (l₁ ++ l₂) := by
  intro F hF
  rcases List.mem_append.1 hF with h | h
  · exact h₁ F h
  · exact h₂ F h

/-- The op list of a unitary sequence, as a family. -/
def fopsU : (T : ℕ) → (C → Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ) → List (FOp C (R ι W))
  | 0, U => [.u fun c => U c 0]
  | T + 1, U => fopsU T (fun c t => U c t.castSucc) ++ [.q, .u fun c => U c (Fin.last (T + 1))]

theorem nqF_fopsU (T : ℕ) (U : C → Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ) :
    nqF (fopsU T U) = T := by
  induction T with
  | zero => simp [fopsU, nqF]
  | succ T ih => simp [fopsU, nqF_append, ih, nqF]

theorem fopsU_ok (T : ℕ) (U : C → Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (hU : ∀ c t, U c t ∈ Matrix.unitaryGroup (R ι W) ℂ) : FOkOps (fopsU T U) := by
  induction T with
  | zero =>
    intro F hF c
    simp only [fopsU, List.mem_singleton, FOp.u.injEq] at hF
    subst hF; exact hU c 0
  | succ T ih =>
    refine FOkOps.append (ih _ fun c t => hU c _) ?_
    intro F hF c
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hF
    rcases hF with hF | hF
    · cases hF
    · simp only [FOp.u.injEq] at hF; subst hF; exact hU c _

theorem runOps_proj_fopsU (O : Matrix (ι × Bool) (ι × Bool) ℂ) (T : ℕ)
    (U : C → Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ) (c : C) (v : R ι W → ℂ) :
    runOps O ((fopsU T U).map (FOp.proj c)) v = runU (U c) O v := by
  induction T with
  | zero => simp [fopsU, FOp.proj, runOps, Op.apply, runU, indU]
  | succ T ih =>
    simp only [fopsU, List.map_append, List.map_cons, List.map_nil, FOp.proj]
    rw [runOps_append, ih]
    have hU : U c = Fin.snoc (α := fun _ => Matrix (R ι W) (R ι W) ℂ)
        (fun t => U c t.castSucc) (U c (Fin.last (T + 1))) := by
      funext t
      refine Fin.lastCases ?_ (fun i => ?_) t <;> simp
    conv_rhs => rw [hU]
    rw [runU_snoc]
    rfl

end Block

/-! ### Vectors, probabilities and linearity -/

section Prob

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The probability of an event under measuring `v`. -/
noncomputable def pr (v : X → ℂ) (P : X → Prop) [DecidablePred P] : ℝ :=
  ∑ z, if P z then ‖v z‖ ^ 2 else 0

theorem probEvent_eq_pr (ψ : EuclideanSpace ℂ X) (P : X → Prop) [DecidablePred P] :
    probEvent ψ P = pr (WithLp.ofLp ψ) P := by
  unfold probEvent pr prob
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs
  · simp [ket, EuclideanSpace.inner_single_left]
  · rfl

end Prob

section Linear

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

theorem runOps_smul (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l : List (Op (R ι W))) (a : ℂ)
    (v : R ι W → ℂ) : runOps O l (a • v) = a • runOps O l v := by
  induction l generalizing v with
  | nil => rfl
  | cons op l ih =>
    simp only [runOps_cons]
    rw [← ih]
    congr 1
    cases op <;> simp [Op.apply, Matrix.mulVec_smul]

end Linear

/-! ### Transport along a workspace equivalence; permutations -/

section Transport

variable {ι W W' : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
  [Fintype W'] [DecidableEq W']

def regEq (e : W' ≃ W) : R ι W' ≃ R ι W := (Equiv.refl _).prodCongr e

def Op.transport (e : W' ≃ W) : Op (R ι W) → Op (R ι W')
  | .u M => .u (M.submatrix (regEq (ι := ι) e) (regEq (ι := ι) e))
  | .q => .q

theorem runOps_transport (O : Matrix (ι × Bool) (ι × Bool) ℂ) (e : W' ≃ W)
    (l : List (Op (R ι W))) (v : R ι W → ℂ) :
    runOps O (l.map (Op.transport e)) (v ∘ regEq e) = runOps O l v ∘ regEq e := by
  induction l generalizing v with
  | nil => rfl
  | cons op l ih =>
    simp only [List.map_cons, runOps_cons]
    rw [← ih]
    congr 1
    funext z
    cases op with
    | u M =>
      simp only [Op.transport, Op.apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
        Function.comp_apply]
      exact Equiv.sum_comp (regEq e) (fun y => M (regEq e z) y * v y)
    | q =>
      simp only [Op.apply, Matrix.mulVec, dotProduct, Function.comp_apply]
      rw [← Equiv.sum_comp (regEq e)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [qmat, regEq, Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply,
        e.injective.eq_iff]

theorem submatrix_mem_unitary' {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (σ : Y ≃ X) (U : Matrix X X ℂ)
    (hU : U ∈ Matrix.unitaryGroup X ℂ) : U.submatrix σ σ ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  rw [Matrix.star_eq_conjTranspose] at hU ⊢
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv]

theorem OkOps.transport (e : W' ≃ W) {l : List (Op (R ι W))} (h : OkOps l) :
    OkOps (l.map (Op.transport e)) := by
  intro M hM
  obtain ⟨op, hop, he⟩ := List.mem_map.1 hM
  cases op with
  | u M' =>
    simp only [Op.transport, Op.u.injEq] at he
    subst he
    exact submatrix_mem_unitary' _ _ (h M' hop)
  | q => simp [Op.transport] at he

theorem nq_transport (e : W' ≃ W) (l : List (Op (R ι W))) : nq (l.map (Op.transport e)) = nq l := by
  induction l with
  | nil => rfl
  | cons op l ih => cases op <;> simp [Op.transport, nq, ih]

/-- Permutation matrix: `(perm σ).mulVec v = v ∘ σ`. -/
def perm {X : Type} [DecidableEq X] (σ : X ≃ X) : Matrix X X ℂ :=
  Matrix.of fun z z' => if z' = σ z then 1 else 0

theorem perm_mulVec {X : Type} [Fintype X] [DecidableEq X] (σ : X ≃ X) (v : X → ℂ) :
    (perm σ).mulVec v = v ∘ σ := by
  funext z
  simp [perm, Matrix.mulVec, dotProduct]

theorem perm_mem_unitary {X : Type} [Fintype X] [DecidableEq X] (σ : X ≃ X) :
    perm σ ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext z z'
  simp only [Matrix.mul_apply, perm, Matrix.of_apply, Matrix.star_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ z)]
  · by_cases h : z = z'
    · subst h; simp
    · have : σ z ≠ σ z' := fun h' => h (σ.injective h')
      simp [h, this, eq_comm]
  · intro y _ hy; simp [hy]
  · simp

end Transport

end QComp

end File_Block

section File_Prep

namespace QComp

open scoped ComplexConjugate

section Prep

variable {X : Type} [Fintype X] [DecidableEq X]

/-- `⟨v, u⟩ = Σ conj(v z) u z`. -/
noncomputable def ip (v u : X → ℂ) : ℂ := ∑ z, conj (v z) * u z

theorem ip_self (u : X → ℂ) : ip u u = ((∑ z, ‖u z‖ ^ 2 : ℝ) : ℂ) := by
  unfold ip
  push_cast
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- Householder matrix `I - k |w⟩⟨w|`. -/
noncomputable def house (k : ℝ) (w : X → ℂ) : Matrix X X ℂ :=
  Matrix.of fun z z' => (if z = z' then 1 else 0) - (k : ℂ) * w z * conj (w z')

theorem house_mulVec (k : ℝ) (w u : X → ℂ) :
    (house k w).mulVec u = u - ((k : ℂ) * ip w u) • w := by
  funext z
  simp only [house, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · simp
  · unfold ip
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring

theorem house_mem_unitary (k : ℝ) (w : X → ℂ) (hk : k * k * (∑ z, ‖w z‖ ^ 2) = 2 * k) :
    house k w ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext z z'
  have hn : (∑ y, w y * conj (w y)) = ((∑ y, ‖w y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp only [Matrix.mul_apply, Matrix.star_apply, house, Matrix.of_apply, Matrix.one_apply]
  have expand : ∀ y, ((if z = y then (1 : ℂ) else 0) - (k : ℂ) * w z * conj (w y)) *
      star ((if z' = y then (1 : ℂ) else 0) - (k : ℂ) * w z' * conj (w y)) =
      (if z = y then 1 else 0) * (if z' = y then 1 else 0)
        - (if z = y then 1 else 0) * ((k : ℂ) * conj (w z') * w y)
        - (k : ℂ) * w z * conj (w y) * (if z' = y then 1 else 0)
        + (k : ℂ) * (k : ℂ) * w z * conj (w z') * (w y * conj (w y)) := by
    intro y
    simp only [star_sub, star_mul', Complex.star_def, map_one, map_zero, Complex.conj_ofReal,
      Complex.conj_conj, apply_ite (starRingEnd ℂ)]
    ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hn]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hk' : (k : ℂ) * (k : ℂ) * ((∑ y, ‖w y‖ ^ 2 : ℝ) : ℂ) = 2 * (k : ℂ) := by
    exact_mod_cast hk
  by_cases h : z = z'
  · subst h
    try simp only [if_true]
    linear_combination (w z * conj (w z)) * hk'
  · simp only [if_neg h]
    try simp only [if_neg (Ne.symm h)]
    linear_combination (w z * conj (w z')) * hk'

/-- State preparation: any unit vector can be mapped to any other, up to a phase. -/
theorem exists_prep (u v : X → ℂ) (hu : ∑ z, ‖u z‖ ^ 2 = 1) (hv : ∑ z, ‖v z‖ ^ 2 = 1) :
    ∃ P ∈ Matrix.unitaryGroup X ℂ, ∃ c : ℂ, ‖c‖ = 1 ∧ P.mulVec u = c • v := by
  set a := ip v u with ha
  -- phase making `⟨c v, u⟩` real and nonnegative
  set c : ℂ := if a = 0 then 1 else a / (‖a‖ : ℂ) with hc
  have hcn : ‖c‖ = 1 := by
    rw [hc]; split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h)]
  set v' := c • v with hv'
  have hip : ip v' u = ((‖a‖ : ℝ) : ℂ) := by
    simp only [hv', ip, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
    rw [← ip, ← ha, hc]
    split_ifs with h
    · simp [h]
    · rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm (conj a) a,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
      push_cast
      field_simp
  by_cases heq : v' = u
  · exact ⟨1, one_mem _, c, hcn, by rw [Matrix.one_mulVec, ← heq]⟩
  set w := u - v' with hw
  have hv'n : ∑ z, ‖v' z‖ ^ 2 = 1 := by
    simp only [hv', Pi.smul_apply, smul_eq_mul, norm_mul, hcn, one_mul, hv]
  -- `‖w‖² = 2 - 2‖a‖`
  have hwn : ((∑ z, ‖w z‖ ^ 2 : ℝ) : ℂ) = 2 - 2 * ((‖a‖ : ℝ) : ℂ) := by
    rw [← ip_self]
    have h1 : ip w w = ip u u - ip v' u - ip u v' + ip v' v' := by
      simp only [ip, hw, Pi.sub_apply, map_sub]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    have h2 : ip u v' = conj (ip v' u) := by
      simp only [ip, map_sum, map_mul, Complex.conj_conj]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [h1, h2, hip, ip_self, ip_self, hu, hv'n, Complex.conj_ofReal]
    push_cast; ring
  have hwpos : 0 < ∑ z, ‖w z‖ ^ 2 := by
    rcases (Finset.sum_nonneg (fun z _ => sq_nonneg ‖w z‖)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply heq
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg ‖w z‖)).1 h.symm
      funext z
      have := hz z (Finset.mem_univ z)
      have : w z = 0 := by simpa using this
      simp only [hw, Pi.sub_apply, sub_eq_zero] at this
      exact this.symm
  set n := ∑ z, ‖w z‖ ^ 2 with hn
  refine ⟨house (2 / n) w, house_mem_unitary _ _ ?_, c, hcn, ?_⟩
  · rw [← hn]
    have := hwpos.ne'
    field_simp
  · rw [house_mulVec]
    have hwu : ip w u = 1 - ((‖a‖ : ℝ) : ℂ) := by
      have : ip w u = ip u u - ip v' u := by
        simp only [ip, hw, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
      rw [this, hip, ip_self, hu]; push_cast; ring
    have hcoef : ((2 / n : ℝ) : ℂ) * ip w u = 1 := by
      rw [hwu]
      have hn' : (n : ℂ) = 2 - 2 * ((‖a‖ : ℝ) : ℂ) := hwn
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
      push_cast
      rw [div_mul_eq_mul_div, div_eq_one_iff_eq hn0, hn']
      ring
    rw [hcoef, one_smul, hw]
    simp [hv']

end Prep

end QComp

end File_Prep

section File_Norm

open QAlgorithms

set_option linter.unusedSectionVars false

namespace QComp

open scoped ComplexConjugate

section Norm

variable {X : Type} [Fintype X] [DecidableEq X]

theorem ip_eq_dot (v u : X → ℂ) : ip v u = star v ⬝ᵥ u := by
  unfold ip dotProduct; rfl

theorem sumsq_eq_ip (v : X → ℂ) : ((∑ z, ‖v z‖ ^ 2 : ℝ) : ℂ) = ip v v := (ip_self v).symm

theorem unitary_preserves (M : Matrix X X ℂ) (hM : M ∈ Matrix.unitaryGroup X ℂ) (v : X → ℂ) :
    ∑ z, ‖(M.mulVec v) z‖ ^ 2 = ∑ z, ‖v z‖ ^ 2 := by
  have h : ip (M.mulVec v) (M.mulVec v) = ip v v := by
    rw [ip_eq_dot, ip_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
    have : M.conjTranspose * M = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 hM
      rwa [Matrix.star_eq_conjTranspose] at this
    rw [this, Matrix.one_mulVec]
  exact_mod_cast (sumsq_eq_ip _).trans (h.trans (sumsq_eq_ip _).symm)

end Norm

section Query

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

theorem bool_ff : (false + false : Bool) = false := rfl
theorem bool_ft : (false + true : Bool) = true := rfl
theorem bool_tf : (true + false : Bool) = true := rfl
theorem bool_tt : (true + true : Bool) = false := rfl
theorem bool_zero : (0 : Bool) = false := rfl

def xorPerm (x : ι → Bool) : (ι × Bool) ≃ (ι × Bool) where
  toFun p := (p.1, p.2 + x p.1)
  invFun p := (p.1, p.2 + x p.1)
  left_inv p := by
    obtain ⟨i, b⟩ := p
    simp only [Prod.mk.injEq, true_and]
    cases b <;> cases x i <;> rfl
  right_inv p := by
    obtain ⟨i, b⟩ := p
    simp only [Prod.mk.injEq, true_and]
    cases b <;> cases x i <;> rfl

theorem xorOracle_eq_perm (x : ι → Bool) : xorOracle x = perm (xorPerm x) := by
  ext p q
  simp only [xorOracle, perm, Matrix.of_apply, xorPerm, Equiv.coe_fn_mk]
  obtain ⟨i, b⟩ := p
  obtain ⟨i', b'⟩ := q
  simp only [Prod.mk.injEq]
  by_cases h : i = i'
  · subst h
    cases b <;> cases b' <;> cases x i <;>
      simp [bool_ff, bool_ft, bool_tf, bool_tt, bool_zero]
  · simp [h, Ne.symm h]

theorem qmat_mem_unitary (x : ι → Bool) :
    qmat (W := W) (xorOracle x) ∈ Matrix.unitaryGroup (R ι W) ℂ := by
  unfold qmat
  rw [xorOracle_eq_perm]
  exact Matrix.kronecker_mem_unitary (perm_mem_unitary _) (one_mem _)

theorem runOps_preserves (x : ι → Bool) (l : List (Op (R ι W))) (hl : OkOps l) (v : R ι W → ℂ) :
    ∑ z, ‖runOps (xorOracle x) l v z‖ ^ 2 = ∑ z, ‖v z‖ ^ 2 := by
  induction l generalizing v with
  | nil => rfl
  | cons op l ih =>
    rw [runOps_cons, ih (fun M hM => hl M (List.mem_cons_of_mem _ hM))]
    cases op with
    | u M => exact unitary_preserves M (hl M (by simp)) v
    | q => exact unitary_preserves _ (qmat_mem_unitary x) v

end Query

end QComp

end File_Norm

section File_Closure

open QAlgorithms

set_option linter.unusedSectionVars false

namespace QComp

open scoped ComplexConjugate

/-! ### Helper lemmas -/

section Helpers

variable {ι W C : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C]

theorem pr_smul {X : Type} [Fintype X] [DecidableEq X] (c : ℂ) (v : X → ℂ) (P : X → Prop)
    [DecidablePred P] : pr (c • v) P = ‖c‖ ^ 2 * pr v P := by
  unfold pr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp [norm_mul, mul_pow]

theorem pr_comp {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (σ : Y ≃ X) (v : X → ℂ) (P : X → Prop) [DecidablePred P] :
    pr (v ∘ σ) (fun y => P (σ y)) = pr v P := by
  unfold pr
  exact Equiv.sum_comp σ (fun z => if P z then ‖v z‖ ^ 2 else 0)

def Op.toConst : Op (R ι W) → FOp C (R ι W)
  | .u M => .u fun _ => M
  | .q => .q

theorem map_proj_toConst (l : List (Op (R ι W))) (c : C) :
    (l.map (Op.toConst (C := C))).map (FOp.proj c) = l := by
  induction l with
  | nil => rfl
  | cons op l ih => cases op <;> simp [Op.toConst, FOp.proj, ih]

theorem nqF_toConst (l : List (Op (R ι W))) : nqF (l.map (Op.toConst (C := C))) = nq l := by
  induction l with
  | nil => rfl
  | cons op l ih => cases op <;> simp [Op.toConst, nqF, nq, ih]

theorem FOkOps_toConst {l : List (Op (R ι W))} (h : OkOps l) :
    FOkOps (l.map (Op.toConst (C := C))) := by
  intro F hF c
  obtain ⟨op, hop, he⟩ := List.mem_map.1 hF
  cases op with
  | u M =>
    simp only [Op.toConst, FOp.u.injEq] at he
    subst he
    exact h M hop
  | q => simp [Op.toConst] at he

theorem nq_proj (l : List (FOp C (R ι W))) (c : C) : nq (l.map (FOp.proj c)) = nqF l := by
  induction l with
  | nil => rfl
  | cons op l ih => cases op <;> simp [FOp.proj, nq, nqF, ih]

theorem FOkOps.proj {l : List (FOp C (R ι W))} (h : FOkOps l) (c : C) :
    OkOps (l.map (FOp.proj c)) := by
  intro M hM
  obtain ⟨op, hop, he⟩ := List.mem_map.1 hM
  cases op with
  | u F =>
    simp only [FOp.proj, Op.u.injEq] at he
    subst he
    exact h F hop c
  | q => simp [FOp.proj] at he

theorem runU_smul {T : ℕ} (U : Fin (T + 1) → Matrix (R ι W) (R ι W) ℂ)
    (O : Matrix (ι × Bool) (ι × Bool) ℂ) (a : ℂ) (v : R ι W → ℂ) :
    runU U O (a • v) = a • runU U O v := by
  have h := fun v => runOps_proj_fopsU (C := Unit) O T (fun _ => U) () v
  rw [← h, ← h, runOps_smul]

theorem sumsq_of_norm {X : Type} [Fintype X] (ψ : EuclideanSpace ℂ X) (h : ‖ψ‖ = 1) :
    ∑ z, ‖WithLp.ofLp ψ z‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq] at h
  have h0 : 0 ≤ ∑ z, ‖ψ z‖ ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  have := (Real.sqrt_eq_one).1 h
  simpa using this

end Helpers

/-! ### Realizability and achievability -/

section Achievable

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Internal: realized by a unitary op list on workspace `W`. -/
def Real (W : Type) [Fintype W] [DecidableEq W] {α : Type} [DecidableEq α] (T : ℕ)
    (μ : (ι → Bool) → α → ℝ) : Prop :=
  ∃ (l : List (Op (R ι W))) (s : R ι W → ℂ) (out : R ι W → α),
    OkOps l ∧ nq l = T ∧ (∑ z, ‖s z‖ ^ 2 = 1) ∧
    ∀ x a, pr (runOps (xorOracle x) l s) (fun z => out z = a) = μ x a

/-- A family of output distributions produced by some `T`-query `QueryAlg`. -/
def Achievable {α : Type} [DecidableEq α] (T : ℕ) (μ : (ι → Bool) → α → ℝ) : Prop :=
  ∃ (w : ℕ) (A : QueryAlg ι Bool (Fin w) T) (out : R ι (Fin w) → α),
    ∀ x a, probEvent (A.finalState (xorOracle x)) (fun z => out z = a) = μ x a

variable {α : Type} [DecidableEq α]

theorem Real.transport {W W' : Type} [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']
    (e : W' ≃ W) {T : ℕ} {μ : (ι → Bool) → α → ℝ} (h : Real W T μ) : Real W' T μ := by
  obtain ⟨l, s, out, hl, hT, hs, hμ⟩ := h
  refine ⟨l.map (Op.transport e), s ∘ regEq e, out ∘ regEq e, hl.transport e,
    (nq_transport e l).trans hT, ?_, fun x a => ?_⟩
  · rw [← hs]; exact Equiv.sum_comp (regEq (ι := ι) e) (fun z => ‖s z‖ ^ 2)
  · rw [runOps_transport]
    rw [← hμ x a]
    exact pr_comp (regEq e) _ (fun z => out z = a)

theorem Real.achievable {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    {μ : (ι → Bool) → α → ℝ} (h : Real W T μ) : Achievable T μ := by
  obtain ⟨l, s, out, hl, hT, hs, hμ⟩ := h.transport (Fintype.equivFin W).symm
  obtain ⟨A, hA⟩ := exists_alg l hl s hs
  subst hT
  refine ⟨Fintype.card W, A, out, fun x a => ?_⟩
  rw [probEvent_eq_pr, hA x]
  exact hμ x a

theorem Achievable.real {T : ℕ} {μ : (ι → Bool) → α → ℝ} (h : Achievable T μ) :
    ∃ w : ℕ, Real (Fin w) T μ := by
  obtain ⟨w, A, out, hA⟩ := h
  let U : Unit → Fin (T + 1) → Matrix (R ι (Fin w)) (R ι (Fin w)) ℂ :=
    fun _ t => (A.U t : Matrix _ _ ℂ)
  refine ⟨w, (fopsU T U).map (FOp.proj ()), WithLp.ofLp A.start, out,
    (fopsU_ok T U fun _ t => (A.U t).2).proj (), ?_, sumsq_of_norm _ A.start_unit,
    fun x a => ?_⟩
  · rw [nq_proj, nqF_fopsU]
  · rw [runOps_proj_fopsU, ← hA x a, probEvent_eq_pr, ofLp_finalState]

/-- Normal form: a unitary sequence started at a fixed basis vector. -/
theorem Real.normal {W : Type} [Fintype W] [DecidableEq W] {T : ℕ} {μ : (ι → Bool) → α → ℝ}
    (h : Real W T μ) (z0 : R ι W) :
    ∃ (U : Fin (T + 1) → Matrix.unitaryGroup (R ι W) ℂ) (out : R ι W → α),
      ∀ x a, pr (runU (fun t => (U t : Matrix _ _ ℂ)) (xorOracle x)
        (fun z => if z = z0 then 1 else 0)) (fun z => out z = a) = μ x a := by
  obtain ⟨l, s, out, hl, hT, hs, hμ⟩ := h
  have he : ∑ z : R ι W, ‖(if z = z0 then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single z0]
    · simp
    · intro z _ hz; simp [hz]
    · simp
  obtain ⟨P, hP, c, hc, hPc⟩ := exists_prep _ s he hs
  have hl' : OkOps (Op.u P :: l) := by
    intro M hM
    rcases List.mem_cons.1 hM with h | h
    · cases h; exact hP
    · exact hl M h
  obtain ⟨T', U, hT', hU⟩ := exists_U (Op.u P :: l) hl'
  have : T' = T := by rw [hT', ← hT]; rfl
  subst this
  refine ⟨U, out, fun x a => ?_⟩
  rw [hU, runOps_cons]
  simp only [Op.apply]
  rw [hPc, runOps_smul, pr_smul, hc, one_pow, one_mul]
  exact hμ x a

end Achievable

/-! ### Embedding, padding of the workspace, and bind -/

section Bind

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem pr_zero {X : Type} [Fintype X] (P : X → Prop) [DecidablePred P] :
    pr (0 : X → ℂ) P = 0 := by
  unfold pr; simp

theorem pr_split {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (v : R ι (W × C) → ℂ) (P : R ι (W × C) → Prop) [DecidablePred P] :
    pr v P = ∑ c, pr (fiber v c) (fun y => P (y.1, (y.2, c))) := by
  unfold pr
  rw [sum_split, Finset.sum_comm]
  rfl

theorem runOps_zero {W : Type} [Fintype W] [DecidableEq W]
    (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l : List (Op (R ι W))) :
    runOps O l 0 = 0 := by
  have := runOps_smul O l 0 0
  simpa using this

variable {W K : Type} [Fintype W] [DecidableEq W] [Fintype K] [DecidableEq K]

def embed (s : R ι W → ℂ) (k0 : K) : R ι (W × K) → ℂ :=
  fun z => if z.2.2 = k0 then s (z.1, z.2.1) else 0

theorem fiber_embed (s : R ι W → ℂ) (k0 k : K) :
    fiber (embed s k0) k = if k = k0 then s else 0 := by
  funext y
  by_cases h : k = k0 <;> simp [fiber, embed, h]

theorem sumsq_embed (s : R ι W → ℂ) (k0 : K) :
    ∑ z, ‖embed s k0 z‖ ^ 2 = ∑ z, ‖s z‖ ^ 2 := by
  rw [sum_split]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single k0]
  · simp [embed]
  · intro k _ hk; simp [embed, hk]
  · simp

theorem fiber_run_embed (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l : List (Op (R ι W)))
    (s : R ι W → ℂ) (k0 k : K) :
    fiber (runOps O ((l.map (Op.toConst (C := K))).map FOp.big) (embed s k0)) k =
      if k = k0 then runOps O l s else 0 := by
  rw [fiber_runOps, map_proj_toConst, fiber_embed]
  by_cases h : k = k0
  · simp [h]
  · simp [h, runOps_zero]

theorem run_embed (O : Matrix (ι × Bool) (ι × Bool) ℂ) (l : List (Op (R ι W)))
    (s : R ι W → ℂ) (k0 : K) (q : ι × Bool) (w : W) (k : K) :
    runOps O ((l.map (Op.toConst (C := K))).map FOp.big) (embed s k0) (q, (w, k)) =
      if k = k0 then runOps O l s (q, w) else 0 := by
  have h := congrFun (fiber_run_embed O l s k0 k) (q, w)
  simp only [fiber] at h
  rw [h]
  by_cases hk : k = k0 <;> simp [hk]

variable {α : Type} [DecidableEq α]

theorem Real.nonempty {T : ℕ} {μ : (ι → Bool) → α → ℝ} (h : Real W T μ) :
    Nonempty (R ι W) := by
  obtain ⟨l, s, out, -, -, hs, -⟩ := h
  by_contra hne
  rw [not_nonempty_iff] at hne
  simp [Finset.univ_eq_empty] at hs

/-- Padding the workspace with an idle register. -/
theorem Real.pad {T : ℕ} {μ : (ι → Bool) → α → ℝ} (h : Real W T μ) (k0 : K) :
    Real (W × K) T μ := by
  obtain ⟨l, s, out, hl, hT, hs, hμ⟩ := h
  refine ⟨(l.map (Op.toConst (C := K))).map FOp.big, embed s k0, fun z => out (z.1, z.2.1),
    (FOkOps_toConst hl).big, by rw [nq_big, nqF_toConst, hT], by rw [sumsq_embed, hs],
    fun x a => ?_⟩
  rw [pr_split, Finset.sum_eq_single k0]
  · rw [fiber_run_embed, if_pos rfl]
    simp only [Prod.mk.eta]
    exact hμ x a
  · intro k _ hk
    rw [fiber_run_embed, if_neg hk, pr_zero]
  · simp

theorem bind_sum {C : Type} [Fintype C] [Fintype α] (φ : C → ℂ) (out1 : C → α)
    (f : α → ℝ) :
    ∑ c, ‖φ c‖ ^ 2 * f (out1 c) =
      ∑ a, (∑ c, if out1 c = a then ‖φ c‖ ^ 2 else 0) * f a := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [ite_mul, Finset.sum_ite_eq]

/-- Sequential composition, with the second stage chosen by the first stage's output. -/
theorem Real.bind {W1 W2 : Type} [Fintype W1] [DecidableEq W1] [Fintype W2] [DecidableEq W2]
    [Fintype α] {β : Type} [DecidableEq β] {T1 T2 : ℕ} {μ : (ι → Bool) → α → ℝ}
    {ν : α → (ι → Bool) → β → ℝ} (h1 : Real W1 T1 μ) (h2 : ∀ a, Real W2 T2 (ν a))
    (z0 : R ι W2) :
    Real (W2 × R ι W1) (T1 + T2) (fun x b => ∑ a, μ x a * ν a x b) := by
  obtain ⟨l1, s1, out1, hl1, hT1, hs1, hμ⟩ := h1
  choose U out2 hU using fun a => (h2 a).normal z0
  let e : W2 × R ι W1 ≃ W1 × R ι W2 :=
    { toFun := fun p => (p.2.2, (p.2.1, p.1)), invFun := fun p => (p.2.2, (p.2.1, p.1)),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let σ : R ι (W2 × R ι W1) ≃ R ι (W2 × R ι W1) :=
    { toFun := fun z => (z.2.2.1, (z.2.1, (z.1, z.2.2.2))),
      invFun := fun z => (z.2.2.1, (z.2.1, (z.1, z.2.2.2))),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let F : R ι W1 → Fin (T2 + 1) → Matrix (R ι W2) (R ι W2) ℂ :=
    fun c t => (U (out1 c) t : Matrix _ _ ℂ)
  let L1 : List (Op (R ι (W2 × R ι W1))) :=
    ((l1.map (Op.toConst (C := R ι W2))).map FOp.big).map (Op.transport e)
  let L2 : List (Op (R ι (W2 × R ι W1))) := (fopsU T2 F).map FOp.big
  refine ⟨L1 ++ [Op.u (perm σ)] ++ L2, embed s1 z0 ∘ regEq e,
    fun z => out2 (out1 z.2.2) (z.1, z.2.1), ?_, ?_, ?_, fun x b => ?_⟩
  · refine OkOps.append (OkOps.append (((FOkOps_toConst hl1).big).transport e) ?_)
      (fopsU_ok T2 F fun c t => (U (out1 c) t).2).big
    intro M hM
    simp only [List.mem_singleton, Op.u.injEq] at hM
    subst hM
    exact perm_mem_unitary σ
  · simp only [L1, L2, nq_append, nq_transport, nq_big, nqF_toConst, nqF_fopsU, hT1]
    simp [nq]
  · exact (Equiv.sum_comp (regEq e) (fun z => ‖embed s1 z0 z‖ ^ 2)).trans
      (by rw [sumsq_embed, hs1])
  · set φ := runOps (xorOracle x) l1 s1 with hφ
    let δ : R ι W2 → ℂ := fun y => if y = z0 then 1 else 0
    let vD : R ι (W2 × R ι W1) → ℂ := fun z => if (z.1, z.2.1) = z0 then φ z.2.2 else 0
    have hrun : runOps (xorOracle x) (L1 ++ [Op.u (perm σ)] ++ L2) (embed s1 z0 ∘ regEq e) =
        runOps (xorOracle x) L2 vD := by
      rw [runOps_append, runOps_append, runOps_transport]
      congr 1
      funext z
      simp only [runOps_cons, runOps_nil, Op.apply, perm_mulVec, Function.comp_apply]
      obtain ⟨q, w2, q1, w1⟩ := z
      exact run_embed (xorOracle x) l1 s1 z0 q1 w1 (q, w2)
    have hfib : ∀ c, fiber vD c = φ c • δ := by
      intro c
      funext y
      by_cases hy : y = z0 <;> simp [fiber, vD, δ, hy]
    rw [hrun, pr_split]
    have hc : ∀ c, pr (fiber (runOps (xorOracle x) L2 vD) c)
        (fun y => out2 (out1 (y.1, (y.2, c)).2.2) ((y.1, (y.2, c)).1, (y.1, (y.2, c)).2.1) = b) =
        ‖φ c‖ ^ 2 * ν (out1 c) x b := by
      intro c
      rw [fiber_runOps, runOps_proj_fopsU, hfib, runU_smul, pr_smul]
      simp only [Prod.mk.eta]
      rw [hU (out1 c) x b]
    rw [Finset.sum_congr rfl fun c _ => hc c, bind_sum φ out1 (fun a => ν a x b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hμ x a]
    rfl

theorem Achievable.bind [Fintype α] {β : Type} [DecidableEq β] {T1 T2 : ℕ}
    {μ : (ι → Bool) → α → ℝ} {ν : α → (ι → Bool) → β → ℝ}
    (h1 : Achievable T1 μ) (h2 : ∀ a, Achievable T2 (ν a)) :
    Achievable (T1 + T2) (fun x b => ∑ a, μ x a * ν a x b) := by
  obtain ⟨w1, h1⟩ := h1.real
  choose w h2 using fun a => (h2 a).real
  have k : ∀ a, Fin (w a) := fun a => (h2 a).nonempty.some.2
  have h2' : ∀ a, Real ((j : α) → Fin (w j)) T2 (ν a) := fun a =>
    ((h2 a).pad (K := (j : {j // j ≠ a}) → Fin (w j)) (fun j => k j)).transport
      (Equiv.piSplitAt a (fun j => Fin (w j)))
  let z0 : R ι ((j : α) → Fin (w j)) := (h1.nonempty.some.1, k)
  exact (h1.bind h2' z0).achievable

end Bind

/-! ### Derived closure properties -/

section More

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} [DecidableEq α]

theorem Achievable.congr {T : ℕ} {μ μ' : (ι → Bool) → α → ℝ} (h : Achievable T μ)
    (he : ∀ x a, μ x a = μ' x a) : Achievable T μ' := by
  obtain ⟨w, A, out, hA⟩ := h
  exact ⟨w, A, out, fun x a => (hA x a).trans (he x a)⟩

theorem Achievable.nonempty {T : ℕ} {μ : (ι → Bool) → α → ℝ} (h : Achievable T μ) :
    Nonempty ι := by
  obtain ⟨w, hw⟩ := h.real
  exact ⟨hw.nonempty.some.1.1⟩

/-- Classical post-processing of the output. -/
theorem Achievable.map [Fintype α] {β : Type} [DecidableEq β] {T : ℕ}
    {μ : (ι → Bool) → α → ℝ} (h : Achievable T μ) (f : α → β) :
    Achievable T (fun x b => ∑ a, if f a = b then μ x a else 0) := by
  obtain ⟨w, A, out, hA⟩ := h
  refine ⟨w, A, f ∘ out, fun x b => ?_⟩
  have hA' : ∀ a, μ x a = pr (WithLp.ofLp (A.finalState (xorOracle x))) (fun z => out z = a) :=
    fun a => by rw [← hA x a, probEvent_eq_pr]
  simp only [hA', probEvent_eq_pr]
  unfold pr
  set n := fun z => ‖WithLp.ofLp (A.finalState (xorOracle x)) z‖ ^ 2 with hn
  have key : ∀ a, (if f a = b then ∑ z, (if out z = a then n z else 0) else 0) =
      ∑ z, if out z = a then (if f a = b then n z else 0) else 0 := by
    intro a; split_ifs with h <;> simp [h]
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [Finset.sum_ite_eq, Function.comp_apply, hn]

/-- `k` idle queries, then a fixed output. -/
theorem Achievable.const [Nonempty ι] (k : ℕ) (a : α) :
    Achievable k (fun (_ : ι → Bool) b => if b = a then (1 : ℝ) else 0) := by
  apply Real.achievable (W := Unit)
  let z0 : R ι Unit := ((Classical.arbitrary ι, false), ())
  have hok : OkOps (List.replicate k (Op.q : Op (R ι Unit))) := by
    intro M hM; simp at hM
  have hs : ∑ z : R ι Unit, ‖(if z = z0 then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single z0]
    · simp
    · intro z _ hz; simp [hz]
    · simp
  refine ⟨List.replicate k .q, fun z => if z = z0 then 1 else 0, fun _ => a, hok, ?_, hs,
    fun x b => ?_⟩
  · induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, nq, ih (by intro M hM; simp at hM)]
  · unfold pr
    have hp := runOps_preserves x _ hok (fun z => if z = z0 then 1 else 0)
    rw [hs] at hp
    by_cases hb : b = a
    · subst hb; simpa using hp
    · simp [hb, Ne.symm hb]

/-- Padding with extra (ignored) queries. -/
theorem Achievable.mono [Fintype α] {T T' : ℕ} {μ : (ι → Bool) → α → ℝ}
    (h : Achievable T μ) (hT : T ≤ T') : Achievable T' μ := by
  have := h.nonempty
  have h' := h.bind (fun a => Achievable.const (ι := ι) (T' - T) a)
  rw [Nat.add_sub_cancel' hT] at h'
  refine h'.congr fun x b => ?_
  simp [mul_ite, Finset.sum_ite_eq']

/-- A 0-query algorithm sampling a classical seed from `π`. -/
theorem Achievable.seed {S : Type} [Fintype S] [DecidableEq S] [Nonempty ι] (π : S → ℝ)
    (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) :
    Achievable 0 (fun (_ : ι → Bool) s => π s) := by
  apply Real.achievable (W := S)
  let q0 : ι × Bool := (Classical.arbitrary ι, false)
  let v : R ι S → ℂ := fun z => if z.1 = q0 then ((Real.sqrt (π z.2) : ℝ) : ℂ) else 0
  have hn : ∀ z : R ι S, ‖v z‖ ^ 2 = if z.1 = q0 then π z.2 else 0 := by
    intro z
    by_cases h : z.1 = q0
    · simp only [v, h, if_true, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (hπ _)
    · simp [v, h]
  refine ⟨[.u 1], v, fun z => z.2, ?_, rfl, ?_, fun x s => ?_⟩
  · intro M hM
    simp only [List.mem_singleton, Op.u.injEq] at hM
    subst hM; exact one_mem _
  · simp only [hn]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single q0]
    · simpa using hπ1
    · intro q _ hq; simp [hq]
    · simp
  · simp only [runOps_cons, runOps_nil, Op.apply, Matrix.one_mulVec]
    unfold pr
    simp only [hn]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single q0]
    · simp
    · intro q _ hq; simp [hq]
    · simp

/-- Mixture over a classical seed. -/
theorem Achievable.mix {S : Type} [Fintype S] [DecidableEq S] {T : ℕ}
    {μ : S → (ι → Bool) → α → ℝ} (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    (h : ∀ s, Achievable T (μ s)) : Achievable T (fun x a => ∑ s, π s * μ s x a) := by
  have hS : Nonempty S := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [Finset.univ_eq_empty] at hπ1
  have := (h hS.some).nonempty
  have h' := (Achievable.seed (ι := ι) π hπ hπ1).bind h
  rwa [Nat.zero_add] at h'

end More

end QComp

end File_Closure

section File_Tree

open QAlgorithms

set_option linter.unusedSectionVars false

namespace QComp

/-! ### Reversible classical op lists -/

section COps

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-- A reversible classical op: an involution of the computational basis, or a query. -/
inductive COp (X : Type) where
  | p : (f : X → X) → Function.Involutive f → COp X
  | q : COp X

def COp.fn (x : ι → Bool) : COp (R ι W) → R ι W → R ι W
  | .p f _ => f
  | .q => fun z => ((z.1.1, z.1.2 + x z.1.1), z.2)

theorem COp.fn_invol (x : ι → Bool) (op : COp (R ι W)) : Function.Involutive (op.fn x) := by
  cases op with
  | p f h => exact h
  | q =>
    intro z
    obtain ⟨⟨i, b⟩, w⟩ := z
    simp only [COp.fn]
    cases b <;> cases x i <;> rfl

noncomputable def COp.toOp : COp (R ι W) → Op (R ι W)
  | .p f h => .u (perm (h.toPerm f))
  | .q => .q

def ncq {X : Type} : List (COp X) → ℕ
  | [] => 0
  | .q :: l => ncq l + 1
  | .p _ _ :: l => ncq l

theorem ncq_append {X : Type} (l₁ l₂ : List (COp X)) : ncq (l₁ ++ l₂) = ncq l₁ + ncq l₂ := by
  induction l₁ with
  | nil => simp [ncq]
  | cons op l ih => cases op <;> simp [ncq, ih] <;> omega

theorem nq_cops (l : List (COp (R ι W))) : nq (l.map COp.toOp) = ncq l := by
  induction l with
  | nil => rfl
  | cons op l ih => cases op <;> simp [COp.toOp, nq, ncq, ih]

theorem OkOps_cops (l : List (COp (R ι W))) : OkOps (l.map COp.toOp) := by
  intro M hM
  obtain ⟨op, -, he⟩ := List.mem_map.1 hM
  cases op with
  | p f h =>
    simp only [COp.toOp, Op.u.injEq] at he
    subst he
    exact perm_mem_unitary _
  | q => simp [COp.toOp] at he

theorem qmat_xor_mulVec (x : ι → Bool) (v : R ι W → ℂ) :
    (qmat (W := W) (xorOracle x)).mulVec v = fun z => v ((z.1.1, z.1.2 + x z.1.1), z.2) := by
  rw [xorOracle_eq_perm]
  funext z
  simp only [qmat, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    perm, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((z.1.1, z.1.2 + x z.1.1), z.2)]
  · simp [xorPerm]
  · intro y _ hy
    have : ¬ (y.1 = xorPerm x z.1 ∧ z.2 = y.2) := by
      rintro ⟨h1, h2⟩
      exact hy (Prod.ext (by rw [h1]; rfl) h2.symm)
    by_cases h1 : y.1 = xorPerm x z.1
    · have h2 : z.2 ≠ y.2 := fun h2 => this ⟨h1, h2⟩
      simp [h1, h2]
    · simp [h1]
  · simp

/-- Backward composite: `runOps` of the ops is precomposition with it. -/
def cG (x : ι → Bool) : List (COp (R ι W)) → R ι W → R ι W
  | [] => id
  | op :: l => op.fn x ∘ cG x l

/-- Forward simulation on basis states. -/
def cF (x : ι → Bool) : List (COp (R ι W)) → R ι W → R ι W
  | [] => id
  | op :: l => cF x l ∘ op.fn x

theorem apply_toOp (x : ι → Bool) (op : COp (R ι W)) (v : R ι W → ℂ) :
    Op.apply (xorOracle x) op.toOp v = v ∘ op.fn x := by
  cases op with
  | p f h => simp only [COp.toOp, Op.apply, perm_mulVec]; rfl
  | q => simp only [COp.toOp, Op.apply]; rw [qmat_xor_mulVec]; rfl

theorem runOps_cops (x : ι → Bool) (l : List (COp (R ι W))) (v : R ι W → ℂ) :
    runOps (xorOracle x) (l.map COp.toOp) v = v ∘ cG x l := by
  induction l generalizing v with
  | nil => rfl
  | cons op l ih => simp only [List.map_cons, runOps_cons, apply_toOp, ih]; rfl

theorem cG_cF (x : ι → Bool) (l : List (COp (R ι W))) (z : R ι W) : cG x l (cF x l z) = z := by
  induction l generalizing z with
  | nil => rfl
  | cons op l ih =>
    simp only [cG, cF, Function.comp_apply]
    rw [ih]
    exact COp.fn_invol x op z

theorem cF_cG (x : ι → Bool) (l : List (COp (R ι W))) (z : R ι W) : cF x l (cG x l z) = z := by
  induction l generalizing z with
  | nil => rfl
  | cons op l ih =>
    simp only [cG, cF, Function.comp_apply]
    rw [COp.fn_invol x op]
    exact ih z

theorem cG_append (x : ι → Bool) (l₁ l₂ : List (COp (R ι W))) :
    cG x (l₁ ++ l₂) = cG x l₁ ∘ cG x l₂ := by
  induction l₁ with
  | nil => rfl
  | cons op l ih => simp only [List.cons_append, cG, ih]; rfl

theorem cF_append (x : ι → Bool) (l₁ l₂ : List (COp (R ι W))) :
    cF x (l₁ ++ l₂) = cF x l₂ ∘ cF x l₁ := by
  induction l₁ with
  | nil => rfl
  | cons op l ih => simp only [List.cons_append, cF, ih]; rfl

theorem cG_reverse (x : ι → Bool) (l : List (COp (R ι W))) : cG x l.reverse = cF x l := by
  induction l with
  | nil => rfl
  | cons op l ih =>
    rw [List.reverse_cons, cG_append, ih]
    rfl

/-- Basis-state action. -/
theorem runOps_cops_basis (x : ι → Bool) (l : List (COp (R ι W))) (z0 : R ι W) :
    runOps (xorOracle x) (l.map COp.toOp) (fun z => if z = z0 then 1 else 0) =
      fun z => if z = cF x l z0 then 1 else 0 := by
  rw [runOps_cops]
  funext y
  simp only [Function.comp_apply]
  congr 1
  apply propext
  constructor
  · intro h; rw [← h, cF_cG]
  · intro h; rw [h, cG_cF]

/-- A diagonal `±1` phase. -/
noncomputable def phaseM {X : Type} [DecidableEq X] (g : X → Bool) : Matrix X X ℂ :=
  Matrix.diagonal fun z => if g z then -1 else 1

theorem phaseM_mem_unitary {X : Type} [Fintype X] [DecidableEq X] (g : X → Bool) :
    phaseM g ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  unfold phaseM
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext z
  by_cases h : g z <;> simp [h]

/-- Compute, apply a phase, uncompute. -/
theorem runOps_sandwich (x : ι → Bool) (C : List (COp (R ι W))) (g : R ι W → Bool)
    (v : R ι W → ℂ) :
    runOps (xorOracle x) (C.map COp.toOp ++ [Op.u (phaseM g)] ++ C.reverse.map COp.toOp) v =
      fun z => (if g (cF x C z) then -1 else 1) * v z := by
  rw [runOps_append, runOps_append, runOps_cops, runOps_cops, cG_reverse]
  funext z
  simp only [runOps_cons, runOps_nil, Op.apply, phaseM, Matrix.mulVec_diagonal,
    Function.comp_apply, cG_cF]

end COps

/-! ### Following a decision tree along a sequence of answers -/

section Paths

variable {ι α : Type}

def qAt : DecisionTree ι Bool α → (ℕ → Bool) → ℕ → Option ι
  | .leaf _, _, _ => none
  | .node i _, _, 0 => some i
  | .node _ nx, a, s + 1 => qAt (nx (a 0)) (fun j => a (j + 1)) s

def leafAt : DecisionTree ι Bool α → (ℕ → Bool) → α
  | .leaf v, _ => v
  | .node _ nx, a => leafAt (nx (a 0)) (fun j => a (j + 1))

/-- The answers the simulation records: real answers along the path, then `x i0`. -/
def ansSeq (i0 : ι) : DecisionTree ι Bool α → (ι → Bool) → ℕ → Bool
  | .leaf _, x, _ => x i0
  | .node i _, x, 0 => x i
  | .node i nx, x, s + 1 => ansSeq i0 (nx (x i)) x s

theorem qAt_congr (t : DecisionTree ι Bool α) (a a' : ℕ → Bool) (s : ℕ)
    (h : ∀ j < s, a j = a' j) : qAt t a s = qAt t a' s := by
  induction t generalizing a a' s with
  | leaf v => rfl
  | node i nx ih =>
    cases s with
    | zero => rfl
    | succ s =>
      simp only [qAt]
      rw [h 0 (by omega)]
      exact ih _ _ _ s fun j hj => h (j + 1) (by omega)

theorem ansSeq_spec (i0 : ι) (t : DecisionTree ι Bool α) (x : ι → Bool) (s : ℕ) :
    x ((qAt t (ansSeq i0 t x) s).getD i0) = ansSeq i0 t x s := by
  induction t generalizing s with
  | leaf v => rfl
  | node i nx ih =>
    cases s with
    | zero => rfl
    | succ s => exact ih (x i) s

theorem leafAt_ans (i0 : ι) (t : DecisionTree ι Bool α) (x : ι → Bool) (a : ℕ → Bool)
    (h : ∀ j < t.queries x, a j = ansSeq i0 t x j) : leafAt t a = t.eval x := by
  induction t generalizing a with
  | leaf v => rfl
  | node i nx ih =>
    simp only [DecisionTree.queries] at h
    simp only [leafAt, DecisionTree.eval]
    have h0 : a 0 = x i := h 0 (by omega)
    rw [h0]
    exact ih (x i) _ fun j hj => h (j + 1) (by omega)

end Paths

/-! ### Coherent simulation of a family of decision trees -/

section Sim

variable {ι K α : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
variable (d : ℕ)

def ext (a : Fin d → Bool) : ℕ → Bool := fun j => if h : j < d then a ⟨j, h⟩ else false

abbrev SW (K : Type) (d : ℕ) := K × (Fin d → Bool)

variable (t : K → DecisionTree ι Bool α) (i0 : ι)

def idxAt (s : ℕ) (z : R ι (SW K d)) : ι := (qAt (t z.2.1) (ext d z.2.2) s).getD i0

def loadF (s : ℕ) (z : R ι (SW K d)) : R ι (SW K d) :=
  ((Equiv.swap i0 (idxAt d t i0 s z) z.1.1, z.1.2), z.2)

theorem loadF_invol (s : ℕ) : Function.Involutive (loadF d t i0 s) := by
  intro z
  simp [loadF, idxAt]

def storeF (s : Fin d) (z : R ι (SW K d)) : R ι (SW K d) :=
  (z.1, (z.2.1, Function.update z.2.2 s (z.2.2 s + z.1.2)))

theorem bool_add_add (a b : Bool) : a + b + b = a := by cases a <;> cases b <;> rfl

theorem storeF_invol (s : Fin d) : Function.Involutive (storeF (K := K) (ι := ι) d s) := by
  intro z
  simp only [storeF, Function.update_self, Function.update_idem, bool_add_add,
    Function.update_eq_self]

def clrF (s : Fin d) (z : R ι (SW K d)) : R ι (SW K d) :=
  ((z.1.1, z.1.2 + z.2.2 s), z.2)

theorem clrF_invol (s : Fin d) : Function.Involutive (clrF (K := K) (ι := ι) d s) := by
  intro z
  simp only [clrF, bool_add_add]

def stepOps (s : Fin d) : List (COp (R ι (SW K d))) :=
  [.p (loadF d t i0 s) (loadF_invol d t i0 s), .q, .p (storeF d s) (storeF_invol d s),
    .p (clrF d s) (clrF_invol d s), .p (loadF d t i0 s) (loadF_invol d t i0 s)]

def computeOps : ℕ → List (COp (R ι (SW K d)))
  | 0 => []
  | m + 1 => computeOps m ++ (if h : m < d then stepOps d t i0 ⟨m, h⟩ else [])

theorem ncq_computeOps (m : ℕ) (hm : m ≤ d) : ncq (computeOps d t i0 m) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [computeOps, ncq_append, dif_pos (show m < d by omega), stepOps, ncq]
    rw [ih (by omega)]

/-- The register after `m` steps: the recorded answers below `m`. -/
def regAt (k : K) (x : ι → Bool) (m : ℕ) : Fin d → Bool :=
  fun j => if (j : ℕ) < m then ansSeq i0 (t k) x j else false

theorem ext_regAt (k : K) (x : ι → Bool) (m : ℕ) (j : ℕ) (hj : j < m) (hjd : j < d) :
    ext d (regAt d t i0 k x m) j = ansSeq i0 (t k) x j := by
  simp [ext, regAt, hjd, hj]

theorem cF_step (x : ι → Bool) (k : K) (s : Fin d) :
    cF x (stepOps d t i0 s) ((i0, false), (k, regAt d t i0 k x s)) =
      ((i0, false), (k, regAt d t i0 k x (s + 1))) := by
  set A := ansSeq i0 (t k) x
  set a := regAt d t i0 k x s
  have hI : idxAt d t i0 s ((i0, false), (k, a)) = (qAt (t k) A s).getD i0 := by
    simp only [idxAt]
    rw [qAt_congr (t k) (ext d a) A s fun j hj => ext_regAt d t i0 k x s j hj (by omega)]
  set I := (qAt (t k) A s).getD i0 with hIdef
  have hxI : x I = A s := ansSeq_spec i0 (t k) x s
  have has : a s = false := by simp [a, regAt]
  have hupd : Function.update a s (A s) = regAt d t i0 k x (s + 1) := by
    funext j
    by_cases hj : j = s
    · subst hj; simp [regAt, A]
    · rw [Function.update_of_ne hj]
      simp only [a, regAt]
      have : (j : ℕ) ≠ s := fun h => hj (Fin.ext h)
      by_cases h1 : (j : ℕ) < s
      · simp [h1, show (j : ℕ) < s + 1 by omega]
      · simp [h1, show ¬ (j : ℕ) < s + 1 by omega]
  have hI2 : ∀ a' : Fin d → Bool, (∀ j : Fin d, (j : ℕ) < s → a' j = a j) →
      idxAt d t i0 s ((I, false), (k, a')) = I := by
    intro a' ha'
    simp only [idxAt]
    rw [qAt_congr (t k) (ext d a') A s]
    intro j hj
    have hjd : j < d := by omega
    have h1 := ext_regAt d t i0 k x s j hj hjd
    simp only [ext, dif_pos hjd] at h1 ⊢
    rw [ha' ⟨j, hjd⟩ hj]
    exact h1
  have hz : (false + A s : Bool) = A s := by cases A s <;> rfl
  have hzz : (A s + A s : Bool) = false := by cases A s <;> rfl
  simp only [stepOps, cF, Function.comp_apply, COp.fn, loadF, storeF, clrF, id_eq]
  rw [hI]
  simp only [Equiv.swap_apply_left, has, hxI, hz, hzz, Function.update_self]
  rw [hI2 (Function.update a s (A s)) (fun j hj => Function.update_of_ne
    (fun h => by rw [h] at hj; exact lt_irrefl _ hj) _ _)]
  simp only [Equiv.swap_apply_right, hupd]

theorem cF_compute (x : ι → Bool) (k : K) (m : ℕ) (hm : m ≤ d) :
    cF x (computeOps d t i0 m) ((i0, false), (k, fun _ => false)) =
      ((i0, false), (k, regAt d t i0 k x m)) := by
  induction m with
  | zero =>
    show ((i0, false), (k, fun _ => false)) = _
    congr
  | succ m ih =>
    simp only [computeOps, dif_pos (show m < d by omega), cF_append, Function.comp_apply]
    rw [ih (by omega)]
    exact cF_step d t i0 x k ⟨m, by omega⟩

theorem leafAt_reg (x : ι → Bool) (k : K) (ht : (t k).queries x ≤ d) :
    leafAt (t k) (ext d (regAt d t i0 k x d)) = (t k).eval x :=
  leafAt_ans i0 (t k) x _ fun j hj => ext_regAt d t i0 k x d j (by omega) (by omega)

/-- **Phase oracle** for a family of depth-`d` decision trees: `2d` queries, diagonal, and
`(-1)^{g (t k).eval x}` on the clean state `|i0, 0⟩|k⟩|0⟩`. -/
theorem phaseOracle (ht : ∀ k x, (t k).queries x ≤ d) (g : α → Bool) :
    ∃ L : List (Op (R ι (SW K d))), OkOps L ∧ nq L = 2 * d ∧
      ∃ b : (ι → Bool) → R ι (SW K d) → Bool,
        (∀ x v, runOps (xorOracle x) L v = fun z => (if b x z then -1 else 1) * v z) ∧
        ∀ x k, b x ((i0, false), (k, fun _ => false)) = g ((t k).eval x) := by
  set C := computeOps d t i0 d
  let gg : R ι (SW K d) → Bool := fun z => g (leafAt (t z.2.1) (ext d z.2.2))
  refine ⟨C.map COp.toOp ++ [Op.u (phaseM gg)] ++ C.reverse.map COp.toOp, ?_, ?_,
    fun x z => gg (cF x C z), fun x v => runOps_sandwich x C gg v, fun x k => ?_⟩
  · refine OkOps.append (OkOps.append (OkOps_cops C) ?_) (OkOps_cops _)
    intro M hM
    simp only [List.mem_singleton, Op.u.injEq] at hM
    subst hM
    exact phaseM_mem_unitary gg
  · rw [nq_append, nq_append, nq_cops, nq_cops]
    have hrev : ncq C.reverse = ncq C := by
      clear_value C
      induction C with
      | nil => rfl
      | cons op l ih =>
        rw [List.reverse_cons, ncq_append, ih]
        cases op <;> simp [ncq] <;> omega
    rw [hrev, ncq_computeOps d t i0 d le_rfl]
    simp [nq]; omega
  · simp only [gg, C, cF_compute d t i0 x k d le_rfl]
    rw [leafAt_reg d t i0 x k (ht k x)]

end Sim

/-! ### Deterministic decision trees are achievable -/

section TreeAch

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

theorem Achievable.tree (i0 : ι) (t : DecisionTree ι Bool α) (d : ℕ)
    (ht : ∀ x, t.queries x ≤ d) :
    Achievable d (fun x a => if a = t.eval x then (1 : ℝ) else 0) := by
  apply Real.achievable (W := SW Unit d)
  let tt : Unit → DecisionTree ι Bool α := fun _ => t
  let C := computeOps d tt i0 d
  let z0 : R ι (SW Unit d) := ((i0, false), ((), fun _ => false))
  have hs : ∑ z : R ι (SW Unit d), ‖(if z = z0 then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single z0]
    · simp
    · intro z _ hz; simp [hz]
    · simp
  refine ⟨C.map COp.toOp, fun z => if z = z0 then 1 else 0,
    fun z => leafAt t (ext d z.2.2), OkOps_cops C,
    by rw [nq_cops]; exact ncq_computeOps d tt i0 d le_rfl, hs, fun x a => ?_⟩
  rw [runOps_cops_basis]
  have hF : cF x C z0 = ((i0, false), ((), regAt d tt i0 () x d)) :=
    cF_compute d tt i0 x () d le_rfl
  have hl : leafAt t (ext d (regAt d tt i0 () x d)) = t.eval x :=
    leafAt_reg d tt i0 x () (ht x)
  unfold pr
  rw [Finset.sum_eq_single (cF x C z0)]
  · rw [hF]
    simp only [if_true, norm_one, one_pow]
    rw [hl]
    by_cases h : t.eval x = a
    · simp [h]
    · simp [h, Ne.symm h]
  · intro z _ hz; simp [hz]
  · simp

end TreeAch

end QComp

end File_Tree

section File_Grover

open QAlgorithms

set_option linter.unusedSectionVars false

namespace QComp

open scoped ComplexConjugate

/-! ### Mapping the leaves of a decision tree -/

section TMap

variable {ι α β : Type}

def tmap (f : α → β) : DecisionTree ι Bool α → DecisionTree ι Bool β
  | .leaf a => .leaf (f a)
  | .node i nx => .node i fun b => tmap f (nx b)

theorem eval_tmap (f : α → β) (t : DecisionTree ι Bool α) (x : ι → Bool) :
    (tmap f t).eval x = f (t.eval x) := by
  induction t with
  | leaf a => rfl
  | node i nx ih => exact ih (x i)

theorem queries_tmap (f : α → β) (t : DecisionTree ι Bool α) (x : ι → Bool) :
    (tmap f t).queries x = t.queries x := by
  induction t with
  | leaf a => rfl
  | node i nx ih => simp only [tmap, DecisionTree.queries]; rw [ih]

end TMap

/-! ### Achievable distributions are probability distributions -/

section Prob

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} [DecidableEq α]

theorem pr_nonneg {X : Type} [Fintype X] (v : X → ℂ) (P : X → Prop) [DecidablePred P] :
    0 ≤ pr v P := by
  unfold pr
  exact Finset.sum_nonneg fun z _ => by split_ifs <;> positivity

theorem Achievable.nonneg {T : ℕ} {μ : (ι → Bool) → α → ℝ} (h : Achievable T μ) (x : ι → Bool)
    (a : α) : 0 ≤ μ x a := by
  obtain ⟨w, hw⟩ := h.real
  obtain ⟨l, s, out, -, -, -, hμ⟩ := hw
  rw [← hμ x a]
  exact pr_nonneg _ _

theorem Achievable.sum_one [Fintype α] {T : ℕ} {μ : (ι → Bool) → α → ℝ} (h : Achievable T μ)
    (x : ι → Bool) : ∑ a, μ x a = 1 := by
  obtain ⟨w, hw⟩ := h.real
  obtain ⟨l, s, out, hl, -, hs, hμ⟩ := hw
  simp only [← hμ x]
  unfold pr
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [runOps_preserves x l hl s, hs]

end Prob

/-! ### The clean subspace `|i0, 0⟩|k⟩|0⟩` -/

section Lift

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K] {d : ℕ}
variable (i0 : ι)

def emb (k : K) : R ι (SW K d) := ((i0, false), (k, fun _ => false))

theorem emb_inj : Function.Injective (emb (K := K) (d := d) i0) := by
  intro k k' h
  simp only [emb, Prod.mk.injEq] at h
  exact h.2.1

noncomputable def lift (u : K → ℂ) : R ι (SW K d) → ℂ :=
  fun z => if z.1 = (i0, false) ∧ z.2.2 = (fun _ => false) then u z.2.1 else 0

theorem lift_emb (u : K → ℂ) (k : K) : lift (d := d) i0 u (emb i0 k) = u k := by
  simp [lift, emb]

theorem eq_emb_of (z : R ι (SW K d)) (h : z.1 = (i0, false) ∧ z.2.2 = (fun _ => false)) :
    z = emb i0 z.2.1 := by
  obtain ⟨q, k, a⟩ := z
  simp only at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem lift_off (u : K → ℂ) (z : R ι (SW K d)) (hz : ∀ k, z ≠ emb i0 k) :
    lift i0 u z = 0 := by
  unfold lift
  rw [if_neg]
  intro h
  exact hz _ (eq_emb_of i0 z h)

theorem sum_emb {M : Type} [AddCommMonoid M] (F : R ι (SW K d) → M)
    (hF : ∀ z, (∀ k, z ≠ emb i0 k) → F z = 0) : ∑ z, F z = ∑ k, F (emb i0 k) := by
  have hmap := Finset.sum_map Finset.univ ⟨emb i0, emb_inj i0⟩ F
  simp only [Function.Embedding.coeFn_mk] at hmap
  rw [← hmap]
  refine (Finset.sum_subset (Finset.subset_univ _) fun z _ hz => hF z fun k hk => hz ?_).symm
  rw [hk]
  exact Finset.mem_map_of_mem _ (Finset.mem_univ k)

theorem lift_smul (c : ℂ) (u : K → ℂ) : lift (d := d) i0 (c • u) = c • lift i0 u := by
  funext z
  simp only [lift, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem lift_sub (u v : K → ℂ) : lift (d := d) i0 (u - v) = lift i0 u - lift i0 v := by
  funext z
  simp only [lift, Pi.sub_apply]
  split_ifs <;> simp

theorem ip_lift (u v : K → ℂ) : ip (lift (d := d) i0 u) (lift i0 v) = ip u v := by
  unfold ip
  rw [sum_emb i0 (fun z => conj (lift i0 u z) * lift i0 v z)
    (fun z hz => by simp [lift_off i0 _ z hz])]
  simp only [lift_emb]

theorem sumsq_lift (u : K → ℂ) : ∑ z, ‖lift (d := d) i0 u z‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
  rw [sum_emb i0 (fun z => ‖lift i0 u z‖ ^ 2) (fun z hz => by simp [lift_off i0 _ z hz])]
  simp only [lift_emb]

theorem pr_lift (u : K → ℂ) (k : K) :
    pr (lift (d := d) i0 u) (fun z => z.2.1 = k) = ‖u k‖ ^ 2 := by
  unfold pr
  rw [sum_emb i0 (fun z => if z.2.1 = k then ‖lift i0 u z‖ ^ 2 else 0)
    (fun z hz => by simp [lift_off i0 _ z hz])]
  rw [Finset.sum_eq_single k]
  · rw [lift_emb]; simp [emb]
  · intro k' _ hk'; simp [emb, hk']
  · simp

theorem oracle_lift (b : R ι (SW K d) → Bool) (mk : K → Bool) (hb : ∀ k, b (emb i0 k) = mk k)
    (u : K → ℂ) :
    (fun z => (if b z then -1 else 1) * lift i0 u z) =
      lift i0 (fun k => (if mk k then -1 else 1) * u k) := by
  funext z
  by_cases hz : ∃ k, z = emb i0 k
  · obtain ⟨k, rfl⟩ := hz
    rw [lift_emb, lift_emb, hb]
  · push Not at hz
    rw [lift_off i0 _ z hz, lift_off i0 _ z hz, mul_zero]

end Lift

/-! ### Grover's rotation, over the reals -/

section Rot

variable {K : Type} [Fintype K] [DecidableEq K]

noncomputable def cnt (mk : K → Bool) : ℝ := ((Finset.univ.filter fun k => mk k = true).card : ℝ)

noncomputable def gθ (mk : K → Bool) : ℝ :=
  Real.arcsin (Real.sqrt (cnt mk / Fintype.card K))

noncomputable def gw (mk : K → Bool) (φ : ℝ) : K → ℝ := fun k =>
  if mk k then Real.sin φ / Real.sqrt (cnt mk) else
    Real.cos φ / Real.sqrt (Fintype.card K - cnt mk)

noncomputable def unif : K → ℝ := fun _ => 1 / Real.sqrt (Fintype.card K)

/-- One Grover iteration (oracle, then reflection about the uniform vector). -/
noncomputable def Gr (mk : K → Bool) (r : K → ℝ) : K → ℝ := fun k =>
  (if mk k then -1 else 1) * r k -
    2 * (∑ l, unif l * ((if mk l then -1 else 1) * r l)) * unif k

theorem cnt_nonneg (mk : K → Bool) : 0 ≤ cnt mk := Nat.cast_nonneg _

theorem cnt_le (mk : K → Bool) : cnt mk ≤ Fintype.card K := by
  unfold cnt
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

theorem cnt_pos {mk : K → Bool} {k : K} (hk : mk k = true) : 0 < cnt mk := by
  unfold cnt
  exact_mod_cast Finset.card_pos.2 ⟨k, by simp [hk]⟩

theorem cnt_lt {mk : K → Bool} {k : K} (hk : mk k = false) : cnt mk < Fintype.card K := by
  unfold cnt
  have : (Finset.univ.filter fun k => mk k = true).card < (Finset.univ : Finset K).card :=
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨k, Finset.mem_univ _, by simp [hk]⟩)
  simpa using (show (((Finset.univ.filter fun k => mk k = true).card : ℕ) : ℝ) <
    ((Finset.univ : Finset K).card : ℝ) by exact_mod_cast this)

theorem sum_mk (mk : K → Bool) (a b : ℝ) :
    ∑ k, (if mk k then a else b) = cnt mk * a + (Fintype.card K - cnt mk) * b := by
  have h1 : ∑ k, (if mk k then a else b) = ∑ k : K, b + ∑ k, (if mk k then a - b else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [h1, Finset.sum_const, Finset.card_univ, ← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul]
  unfold cnt
  ring

variable [Nonempty K]

theorem card_pos' : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos

theorem sin_gθ (mk : K → Bool) :
    Real.sin (gθ mk) = Real.sqrt (cnt mk) / Real.sqrt (Fintype.card K) := by
  have hm := card_pos' (K := K)
  have h0 : 0 ≤ cnt mk / Fintype.card K := div_nonneg (cnt_nonneg mk) hm.le
  have h1 : cnt mk / Fintype.card K ≤ 1 := (div_le_one hm).2 (cnt_le mk)
  unfold gθ
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg (cnt mk / Fintype.card K)])
    (Real.sqrt_le_one.2 h1), Real.sqrt_div (cnt_nonneg mk)]

theorem cos_gθ (mk : K → Bool) :
    Real.cos (gθ mk) = Real.sqrt (Fintype.card K - cnt mk) / Real.sqrt (Fintype.card K) := by
  have hm := card_pos' (K := K)
  have h0 : 0 ≤ cnt mk / Fintype.card K := div_nonneg (cnt_nonneg mk) hm.le
  unfold gθ
  rw [Real.cos_arcsin, Real.sq_sqrt h0, ← Real.sqrt_div (by linarith [cnt_le mk])]
  congr 1
  field_simp

theorem aux_div (x c y : ℝ) (hx : 0 ≤ x) :
    x * (c / (Real.sqrt x * y)) = c * (Real.sqrt x / y) := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 h).ne'
    have hxx := Real.mul_self_sqrt hx
    by_cases hy : y = 0
    · simp [hy]
    · calc x * (c / (Real.sqrt x * y)) = Real.sqrt x * Real.sqrt x * (c / (Real.sqrt x * y)) := by
            rw [hxx]
        _ = c * (Real.sqrt x / y) := by field_simp

theorem unif_eq (mk : K → Bool) : gw mk (gθ mk) = unif := by
  have hm := card_pos' (K := K)
  have hsm : Real.sqrt (Fintype.card K) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
  funext k
  unfold gw unif
  cases hk : mk k
  · simp only [Bool.false_eq_true, if_false]
    have hp : 0 < Real.sqrt (Fintype.card K - cnt mk) :=
      Real.sqrt_pos.2 (by linarith [cnt_lt hk])
    rw [cos_gθ]
    field_simp
  · simp only [if_true]
    have hp : 0 < Real.sqrt (cnt mk) := Real.sqrt_pos.2 (cnt_pos hk)
    rw [sin_gθ]
    field_simp

theorem inner_gw (mk : K → Bool) (φ : ℝ) :
    ∑ l, unif l * ((if mk l then -1 else 1) * gw mk φ l) = Real.cos (φ + gθ mk) := by
  have hm := card_pos' (K := K)
  have hsm : Real.sqrt (Fintype.card K) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
  have h1 : ∀ l, unif l * ((if mk l then -1 else 1) * gw mk φ l) =
      if mk l then -Real.sin φ / (Real.sqrt (cnt mk) * Real.sqrt (Fintype.card K)) else
        Real.cos φ / (Real.sqrt (Fintype.card K - cnt mk) * Real.sqrt (Fintype.card K)) := by
    intro l
    unfold unif gw
    cases mk l <;> simp only [Bool.false_eq_true, if_false, if_true] <;> field_simp
  simp only [h1]
  rw [sum_mk, aux_div _ _ _ (cnt_nonneg mk),
    aux_div _ _ _ (by linarith [cnt_le mk]), Real.cos_add, sin_gθ, cos_gθ]
  ring

theorem Gr_gw (mk : K → Bool) (φ : ℝ) :
    Gr mk (gw mk φ) = fun k => -gw mk (φ + 2 * gθ mk) k := by
  have hm := card_pos' (K := K)
  have hsm : Real.sqrt (Fintype.card K) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
  funext k
  unfold Gr
  rw [inner_gw]
  set θ := gθ mk
  have hss : Real.sin (φ + 2 * θ) = Real.sin φ + 2 * Real.cos (φ + θ) * Real.sin θ := by
    have e1 : φ + 2 * θ = (φ + θ) + θ := by ring
    have e2 : φ = (φ + θ) - θ := by ring
    rw [e1, Real.sin_add (φ + θ) θ]
    conv_rhs => rw [e2, Real.sin_sub (φ + θ) θ]
    rw [← e2]; ring
  have hcc : Real.cos (φ + 2 * θ) = 2 * Real.cos (φ + θ) * Real.cos θ - Real.cos φ := by
    have e1 : φ + 2 * θ = (φ + θ) + θ := by ring
    have e2 : φ = (φ + θ) - θ := by ring
    rw [e1, Real.cos_add (φ + θ) θ]
    conv_rhs => rw [e2, Real.cos_sub (φ + θ) θ]
    rw [← e2]; ring
  unfold gw unif
  cases hk : mk k
  · simp only [Bool.false_eq_true, if_false]
    have hp : Real.sqrt (Fintype.card K - cnt mk) ≠ 0 :=
      (Real.sqrt_pos.2 (by linarith [cnt_lt hk])).ne'
    rw [hcc, show Real.cos θ = _ from cos_gθ mk]
    field_simp
    ring
  · simp only [if_true]
    have hp : Real.sqrt (cnt mk) ≠ 0 := (Real.sqrt_pos.2 (cnt_pos hk)).ne'
    rw [hss, show Real.sin θ = _ from sin_gθ mk]
    field_simp
    ring

end Rot

/-! ### The BBHT averaging bound -/

section BBHT

theorem telescope (θ : ℝ) (M : ℕ) :
    2 * Real.sin (2 * θ) * ∑ j ∈ Finset.range M, Real.cos ((4 * j + 2) * θ) =
      Real.sin (4 * M * θ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e1 : Real.sin (4 * ((M + 1 : ℕ) : ℝ) * θ) = Real.sin ((4 * M + 2) * θ + 2 * θ) := by
      push_cast; ring_nf
    have e2 : Real.sin (4 * (M : ℝ) * θ) = Real.sin ((4 * M + 2) * θ - 2 * θ) := by ring_nf
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring

theorem bbht (θ p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) (hs : Real.sin θ ^ 2 = p)
    (hc : Real.cos θ ^ 2 = 1 - p) (hθs : 0 ≤ Real.sin θ) (hθc : 0 ≤ Real.cos θ) (M : ℕ)
    (hM : p = 1 ∨ 1 ≤ 4 * (M : ℝ) ^ 2 * p * (1 - p)) :
    (M : ℝ) / 4 ≤ ∑ j ∈ Finset.range M, Real.sin ((2 * j + 1) * θ) ^ 2 := by
  rcases hM with h1 | hM
  · -- all items marked: every term is `1`
    have hc0 : Real.cos θ = 0 := by
      have : Real.cos θ ^ 2 = 0 := by rw [hc, h1]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have hterm : ∀ j : ℕ, Real.sin ((2 * j + 1) * θ) ^ 2 = 1 := by
      intro j
      induction j with
      | zero => simp [hs, h1]
      | succ j ih =>
        have e : (2 * ((j + 1 : ℕ) : ℝ) + 1) * θ = (2 * j + 1) * θ + 2 * θ := by push_cast; ring
        rw [e, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul, hc0]
        simpa using ih
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  · have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
    have hsq : Real.sin (2 * θ) ^ 2 = 4 * p * (1 - p) := by
      rw [hsin2, mul_pow, mul_pow, hs, hc]; ring
    have hnn : 0 ≤ Real.sin (2 * θ) := by rw [hsin2]; positivity
    have hMs : 1 ≤ (M : ℝ) * Real.sin (2 * θ) := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      have hprod : 1 ≤ ((M : ℝ) * Real.sin (2 * θ)) ^ 2 := by
        rw [mul_pow, hsq]; nlinarith
      nlinarith [mul_nonneg hM0 hnn]
    have hpos : 0 < Real.sin (2 * θ) := by
      rcases hnn.eq_or_lt with h | h
      · rw [← h] at hMs; simp at hMs; linarith
      · exact h
    have hsum : ∑ j ∈ Finset.range M, Real.sin ((2 * j + 1) * θ) ^ 2 =
        M / 2 - (∑ j ∈ Finset.range M, Real.cos ((4 * j + 2) * θ)) / 2 := by
      have : ∀ j : ℕ, Real.sin ((2 * j + 1) * θ) ^ 2 = 1 / 2 - Real.cos ((4 * j + 2) * θ) / 2 := by
        intro j
        rw [Real.sin_sq, Real.cos_sq]
        ring_nf
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, ← Finset.sum_div, nsmul_eq_mul]
      ring
    have ht := telescope θ M
    have hsin1 := Real.sin_le_one (4 * M * θ)
    have hcos : ∑ j ∈ Finset.range M, Real.cos ((4 * j + 2) * θ) ≤ M / 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    rw [hsum]
    linarith

end BBHT

/-! ### Grover search in the query model -/

section Grover

variable {ι K α : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]

noncomputable def cv (r : K → ℝ) : K → ℂ := fun k => (r k : ℂ)

theorem ip_cv (r s : K → ℝ) : ip (cv s) (cv r) = ((∑ k, s k * r k : ℝ) : ℂ) := by
  unfold ip cv
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_ofReal]

def iterOps {X : Type} (st : List (Op X)) : ℕ → List (Op X)
  | 0 => []
  | j + 1 => iterOps st j ++ st

theorem nq_iterOps {X : Type} (st : List (Op X)) (j : ℕ) : nq (iterOps st j) = j * nq st := by
  induction j with
  | zero => simp [iterOps, nq]
  | succ j ih => rw [iterOps, nq_append, ih]; ring

theorem OkOps_iterOps {X : Type} [Fintype X] [DecidableEq X] {st : List (Op X)} (h : OkOps st)
    (j : ℕ) : OkOps (iterOps st j) := by
  induction j with
  | zero => intro M hM; simp [iterOps] at hM
  | succ j ih => exact OkOps.append ih h

variable [Nonempty K]

theorem sumsq_unif : ∑ k : K, ‖cv unif k‖ ^ 2 = 1 := by
  have hm := card_pos' (K := K)
  unfold cv unif
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow,
    Real.sq_sqrt hm.le, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Grover with `j` iterations**: on the index register, the outcome `k` has probability
`gw mk ((2j+1)θ) k ^ 2`. -/
theorem grover_real (i0 : ι) (t : K → DecisionTree ι Bool α) (d : ℕ)
    (ht : ∀ k x, (t k).queries x ≤ d) (g : α → Bool) (j : ℕ) :
    Real (SW K d) (j * (2 * d))
      (fun x k => gw (fun k => g ((t k).eval x)) ((2 * j + 1) * gθ (fun k => g ((t k).eval x))) k ^ 2) := by
  obtain ⟨L, hL, hnL, b, hb, hb0⟩ := phaseOracle d t i0 ht g
  let H : Matrix (R ι (SW K d)) (R ι (SW K d)) ℂ := house 2 (lift i0 (cv unif))
  have hH : H ∈ Matrix.unitaryGroup _ ℂ := by
    apply house_mem_unitary
    rw [sumsq_lift, sumsq_unif]; ring
  let st := L ++ [Op.u H]
  have hst : OkOps st := by
    refine OkOps.append hL ?_
    intro M hM
    simp only [List.mem_singleton, Op.u.injEq] at hM
    subst hM; exact hH
  have hnst : nq st = 2 * d := by simp [st, nq_append, hnL, nq]
  -- one iteration on the clean subspace
  have hstep : ∀ x (r : K → ℝ), runOps (xorOracle x) st (lift i0 (cv r)) =
      lift i0 (cv (Gr (fun k => g ((t k).eval x)) r)) := by
    intro x r
    set mk := fun k => g ((t k).eval x)
    simp only [st, runOps_append, runOps_cons, runOps_nil, Op.apply]
    rw [hb x, oracle_lift i0 (b x) mk (fun k => hb0 x k), house_mulVec, ip_lift]
    have hcv : (fun k => (if mk k then -1 else 1) * cv r k) =
        cv (fun k => (if mk k then -1 else 1) * r k) := by
      funext k; unfold cv; by_cases h : mk k <;> simp [h]
    rw [hcv, ip_cv, ← lift_smul, ← lift_sub]
    congr 1
    funext k
    simp only [cv, Gr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hiter : ∀ x (φ : ℝ) (j : ℕ), runOps (xorOracle x) (iterOps st j)
      (lift i0 (cv (gw (fun k => g ((t k).eval x)) φ))) =
      ((-1 : ℂ) ^ j) • lift i0 (cv (gw (fun k => g ((t k).eval x))
        (φ + 2 * j * gθ (fun k => g ((t k).eval x))))) := by
    intro x φ j
    induction j with
    | zero => simp [iterOps, runOps_nil]
    | succ j ih =>
      rw [iterOps, runOps_append, ih, runOps_smul, hstep, Gr_gw]
      have : cv (fun k => -gw (fun k => g ((t k).eval x))
          (φ + 2 * j * gθ (fun k => g ((t k).eval x)) + 2 * gθ (fun k => g ((t k).eval x))) k) =
          (-1 : ℂ) • cv (gw (fun k => g ((t k).eval x))
            (φ + 2 * ((j + 1 : ℕ) : ℝ) * gθ (fun k => g ((t k).eval x)))) := by
        funext k
        simp only [cv, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring_nf
      rw [this, lift_smul, smul_smul, pow_succ]
  refine ⟨iterOps st j, lift i0 (cv unif), fun z => z.2.1, OkOps_iterOps hst j,
    by rw [nq_iterOps, hnst], by rw [sumsq_lift, sumsq_unif], fun x k => ?_⟩
  rw [← unif_eq (fun k => g ((t k).eval x)), hiter, pr_smul, norm_pow, norm_neg, norm_one,
    one_pow, one_pow, one_mul, pr_lift]
  simp only [cv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  congr 2
  ring

/-- **Grover sampler**: a random number of iterations below `⌊√|K|⌋ + 1`, then a classical
check. Conditioned on a hit, the output is uniform over the marked indices, and the hit
probability is at least `1/4` whenever some index is marked. -/
theorem grover_sampler (i0 : ι) (t : K → DecisionTree ι Bool α) (d : ℕ)
    (ht : ∀ k x, (t k).queries x ≤ d) (g : α → Bool) :
    ∃ μ : (ι → Bool) → Option K → ℝ,
      Achievable ((Nat.sqrt (Fintype.card K) + 1) * (2 * d) + d) μ ∧
      ∃ ρ : (ι → Bool) → ℝ, (∀ x, (∃ k, g ((t k).eval x) = true) → 1 / 4 ≤ ρ x) ∧
        ∀ x k, μ x (some k) =
          if g ((t k).eval x) then ρ x / cnt (fun k => g ((t k).eval x)) else 0 := by
  set M := Nat.sqrt (Fintype.card K) + 1 with hMdef
  have hM : 0 < M := Nat.succ_pos _
  set mk := fun x k => g ((t k).eval x) with hmk
  -- stage 1: mixture over the iteration count
  have h1 : ∀ j : Fin M, Achievable (M * (2 * d))
      (fun x k => gw (mk x) ((2 * (j : ℕ) + 1) * gθ (mk x)) k ^ 2) := fun j =>
    (grover_real i0 t d ht g j).achievable.mono
      (Nat.mul_le_mul_right _ (Nat.le_of_lt j.isLt))
  have hπ1 : ∑ _j : Fin M, (1 / (M : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hmix := Achievable.mix (fun _ : Fin M => 1 / (M : ℝ)) (fun _ => by positivity) hπ1 h1
  -- stage 2: classical check
  let chk : K → DecisionTree ι Bool (Option K) :=
    fun k => tmap (fun v => if g v then some k else none) (t k)
  have h2 : ∀ k, Achievable d (fun x o => if o = (chk k).eval x then (1 : ℝ) else 0) := fun k =>
    Achievable.tree i0 (chk k) d fun x => by rw [queries_tmap]; exact ht k x
  refine ⟨_, hmix.bind h2, fun x => (1 / (M : ℝ)) *
    ∑ j ∈ Finset.range M, Real.sin ((2 * j + 1) * gθ (mk x)) ^ 2, ?_, fun x k => ?_⟩
  · -- the BBHT bound
    rintro x ⟨k0, hk0⟩
    have hm := card_pos' (K := K)
    have hc1 : 1 ≤ cnt (mk x) := by
      unfold cnt
      exact_mod_cast Finset.card_pos.2 ⟨k0, by simp [hmk, hk0]⟩
    set p := cnt (mk x) / Fintype.card K with hpdef
    have hp1 : 0 < p := div_pos (by linarith) hm
    have hp2 : p ≤ 1 := (div_le_one hm).2 (cnt_le _)
    have hs : Real.sin (gθ (mk x)) ^ 2 = p := by
      rw [sin_gθ, div_pow, Real.sq_sqrt (cnt_nonneg _), Real.sq_sqrt hm.le]
    have hc : Real.cos (gθ (mk x)) ^ 2 = 1 - p := by
      rw [cos_gθ, div_pow, Real.sq_sqrt (by linarith [cnt_le (mk x)]), Real.sq_sqrt hm.le,
        hpdef]
      field_simp
    have hMsq : (Fintype.card K : ℝ) ≤ (M : ℝ) ^ 2 := by
      have h := Nat.lt_succ_sqrt (Fintype.card K)
      have : Fintype.card K ≤ M ^ 2 := by rw [hMdef, sq]; exact h.le
      exact_mod_cast this
    have hcond : p = 1 ∨ 1 ≤ 4 * (M : ℝ) ^ 2 * p * (1 - p) := by
      by_cases hall : cnt (mk x) = Fintype.card K
      · left; rw [hpdef, hall]; field_simp
      · right
        have hlt : cnt (mk x) + 1 ≤ Fintype.card K := by
          have h := lt_of_le_of_ne (cnt_le (mk x)) hall
          have : ((Finset.univ.filter fun k => mk x k = true).card : ℝ) + 1 ≤
              (Fintype.card K : ℝ) := by
            unfold cnt at h
            exact_mod_cast (show (Finset.univ.filter fun k => mk x k = true).card + 1 ≤
              Fintype.card K by exact_mod_cast h)
          exact this
        have key : (Fintype.card K : ℝ) ^ 2 ≤
            4 * (M : ℝ) ^ 2 * cnt (mk x) * (Fintype.card K - cnt (mk x)) := by
          nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hlt)]
        have : 4 * (M : ℝ) ^ 2 * p * (1 - p) =
            4 * (M : ℝ) ^ 2 * cnt (mk x) * (Fintype.card K - cnt (mk x)) /
              (Fintype.card K) ^ 2 := by
          rw [hpdef]; field_simp
        rw [this, le_div_iff₀ (by positivity)]
        linarith
    have hb := bbht (gθ (mk x)) p hp1 hp2 hs hc
      (by rw [sin_gθ]; positivity) (by rw [cos_gθ]; positivity) M hcond
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    show (1 : ℝ) / 4 ≤ 1 / (M : ℝ) *
      ∑ j ∈ Finset.range M, Real.sin ((2 * j + 1) * gθ (mk x)) ^ 2
    rw [show (1 : ℝ) / 4 = (1 / M) * (M / 4) by field_simp]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  · -- the output distribution
    simp only
    rw [Finset.sum_eq_single k]
    · simp only [chk, eval_tmap]
      by_cases hk : g ((t k).eval x) = true
      · simp only [hk, if_true, mul_one]
        rw [Fin.sum_univ_eq_sum_range (fun j => 1 / (M : ℝ) *
          gw (mk x) ((2 * (j : ℝ) + 1) * gθ (mk x)) k ^ 2) M]
        rw [← Finset.mul_sum, mul_div_assoc, Finset.sum_div]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [gw, hmk, hk, if_true, div_pow, Real.sq_sqrt (cnt_nonneg _)]
      · simp [hk]
    · intro k' _ hk'
      simp only [chk, eval_tmap]
      split_ifs with h1 h2 <;> simp_all
    · simp
end Grover

end QComp

end File_Grover

section File_Iter

open QAlgorithms

set_option linter.unusedSectionVars false

namespace QComp

section Iter

variable {α : Type} [Fintype α]

/-- `K` steps of a Markov kernel. -/
noncomputable def iterD (μ0 : α → ℝ) (κ : α → α → ℝ) : ℕ → α → ℝ
  | 0 => μ0
  | k + 1 => fun b => ∑ a, iterD μ0 κ k a * κ a b

theorem iterD_nonneg {μ0 : α → ℝ} {κ : α → α → ℝ} (hμ0 : ∀ a, 0 ≤ μ0 a)
    (hκ : ∀ a b, 0 ≤ κ a b) : ∀ k a, 0 ≤ iterD μ0 κ k a
  | 0, a => hμ0 a
  | k + 1, b => Finset.sum_nonneg fun a _ => mul_nonneg (iterD_nonneg hμ0 hκ k a) (hκ a b)

/-- Expected potential after `K` steps, with a step invariant. -/
theorem iterD_potential (μ0 : α → ℝ) (κ : α → α → ℝ) (hμ0 : ∀ a, 0 ≤ μ0 a)
    (hκ : ∀ a b, 0 ≤ κ a b) (Ψ : α → ℝ) (c : ℝ) (hc : 0 ≤ c) (I : ℕ → α → Prop) (K : ℕ)
    (hI0 : ∀ a, μ0 a ≠ 0 → I 0 a)
    (hstep : ∀ k < K, ∀ a, I k a → ∑ b, κ a b * Ψ b ≤ c * Ψ a)
    (hpres : ∀ k < K, ∀ a b, I k a → κ a b ≠ 0 → I (k + 1) b) :
    (∀ a, iterD μ0 κ K a ≠ 0 → I K a) ∧
      ∑ b, iterD μ0 κ K b * Ψ b ≤ c ^ K * ∑ a, μ0 a * Ψ a := by
  induction K with
  | zero => exact ⟨hI0, by simp [iterD]⟩
  | succ K ih =>
    obtain ⟨hsupp, hsum⟩ := ih (fun k hk => hstep k (by omega)) (fun k hk => hpres k (by omega))
    have hD := iterD_nonneg hμ0 hκ K
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
      have h1 : iterD μ0 κ K a ≠ 0 := fun h => ha (by rw [h, zero_mul])
      have h2 : κ a b ≠ 0 := fun h => ha (by rw [h, mul_zero])
      exact hpres K (by omega) a b (hsupp a h1) h2
    · have hswap : ∑ b, iterD μ0 κ (K + 1) b * Ψ b =
          ∑ a, iterD μ0 κ K a * ∑ b, κ a b * Ψ b := by
        simp only [iterD, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [hswap]
      calc ∑ a, iterD μ0 κ K a * ∑ b, κ a b * Ψ b
          ≤ ∑ a, iterD μ0 κ K a * (c * Ψ a) := by
            refine Finset.sum_le_sum fun a _ => ?_
            by_cases h0 : iterD μ0 κ K a = 0
            · rw [h0, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left (hstep K (by omega) a (hsupp a h0)) (hD a)
        _ = c * ∑ a, iterD μ0 κ K a * Ψ a := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
        _ ≤ c * (c ^ K * ∑ a, μ0 a * Ψ a) := mul_le_mul_of_nonneg_left hsum hc
        _ = c ^ (K + 1) * ∑ a, μ0 a * Ψ a := by ring

variable {ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

theorem Achievable.iter {T0 T : ℕ} {μ0 : (ι → Bool) → α → ℝ} {κ : (ι → Bool) → α → α → ℝ}
    (h0 : Achievable T0 μ0) (hk : ∀ a, Achievable T (fun x b => κ x a b)) :
    ∀ K, Achievable (T0 + K * T) (fun x => iterD (μ0 x) (κ x) K)
  | 0 => by rw [Nat.zero_mul, Nat.add_zero]; exact h0
  | K + 1 => by
    have h := (Achievable.iter h0 hk K).bind hk
    rw [show T0 + (K + 1) * T = T0 + K * T + T by ring]
    exact h

end Iter

end QComp

end File_Iter

section File_Sol_RvsCert_lemma_3

open RvsCert QAlgorithms

namespace RvsCertL3

/-! ### Generic decision-tree combinators -/

section Generic

variable {ι : Type}

def bindT {α β : Type} : DecisionTree ι Bool α → (α → DecisionTree ι Bool β) → DecisionTree ι Bool β
  | .leaf a, k => k a
  | .node i next, k => .node i (fun b => bindT (next b) k)

theorem eval_bindT {α β : Type} (t : DecisionTree ι Bool α) (k : α → DecisionTree ι Bool β)
    (x : ι → Bool) : (bindT t k).eval x = (k (t.eval x)).eval x := by
  induction t with
  | leaf a => rfl
  | node i next ih => exact ih (x i)

theorem queries_bindT {α β : Type} (t : DecisionTree ι Bool α) (k : α → DecisionTree ι Bool β)
    (x : ι → Bool) : (bindT t k).queries x = t.queries x + (k (t.eval x)).queries x := by
  induction t with
  | leaf a => simp [bindT, DecisionTree.queries, DecisionTree.eval]
  | node i next ih =>
    simp only [bindT, DecisionTree.queries, DecisionTree.eval]
    rw [ih]
    omega

/-- Run `g c` for each `c` of a list, collecting the results. -/
def seqList {γ δ : Type} (g : γ → DecisionTree ι Bool δ) : List γ → DecisionTree ι Bool (List δ)
  | [] => .leaf []
  | c :: l => bindT (g c) fun d => bindT (seqList g l) fun ds => .leaf (d :: ds)

theorem eval_seqList {γ δ : Type} (g : γ → DecisionTree ι Bool δ) (l : List γ) (x : ι → Bool) :
    (seqList g l).eval x = l.map fun c => (g c).eval x := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [seqList, eval_bindT, DecisionTree.eval, ih, List.map_cons]

theorem queries_seqList {γ δ : Type} (g : γ → DecisionTree ι Bool δ) (l : List γ) (x : ι → Bool) :
    (seqList g l).queries x = (l.map fun c => (g c).queries x).sum := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [seqList, queries_bindT, eval_bindT, DecisionTree.queries, ih, List.map_cons,
      List.sum_cons, DecisionTree.eval]
    omega

theorem queries_seqList_le {γ δ : Type} (g : γ → DecisionTree ι Bool δ) (l : List γ)
    (x : ι → Bool) (K : ℕ) (h : ∀ c ∈ l, (g c).queries x ≤ K) :
    (seqList g l).queries x ≤ l.length * K := by
  rw [queries_seqList]
  have := List.sum_le_card_nsmul (l.map fun c => (g c).queries x) K
    (fun y hy => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      exact h c hc)
  simpa using this

/-- Read the bits at positions `f 0, …, f (w-1)` and return their binary value. -/
def readNum {w : ℕ} (f : Fin w → ι) : DecisionTree ι Bool ℕ :=
  bindT (seqList (fun i => .node i fun b => .leaf b) (List.ofFn f))
    fun bs => .leaf (bitsVal fun t : Fin w => bs.getD t false)

theorem eval_readNum {w : ℕ} (f : Fin w → ι) (x : ι → Bool) :
    (readNum f).eval x = bitsVal fun t => x (f t) := by
  simp only [readNum, eval_bindT, eval_seqList, DecisionTree.eval]
  congr 1
  funext t
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem queries_readNum {w : ℕ} (f : Fin w → ι) (x : ι → Bool) :
    (readNum f).queries x = w := by
  simp only [readNum, queries_bindT, queries_seqList, DecisionTree.queries]
  simp [List.sum_ofFn]

end Generic

/-! ### Probability of a uniformly seeded algorithm -/

theorem successProb_uniform {ι σ : Type} [Fintype σ] [Nonempty σ]
    (tree : σ → DecisionTree ι Bool Bool) (x : ι → Bool) (b : Bool) :
    successProb ((PMF.uniformOfFintype σ).map tree) x b =
      ((Finset.univ.filter fun s => (tree s).eval x = b).card : ℝ) / Fintype.card σ := by
  classical
  unfold successProb
  rw [PMF.map_comp, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Function.comp_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [div_eq_mul_inv]
  congr 3
  ext s
  simp [eq_comm]


/-! ### Encoding helpers -/

abbrev Ath (n : ℕ) := Fin (2 * n) × Fin n

theorem raceOf_val {n : ℕ} (c : Fin (2 * n)) (j : Fin (2 * n - 1)) :
    (raceOf c j).1 = if (j : ℕ) < c then (opponent c j, c) else (c, opponent c j) := by
  unfold raceOf
  split_ifs <;> rfl

theorem common_race_lt {n : ℕ} (c c' : Fin (2 * n)) (h : c < c') :
    ∃ j j' : Fin (2 * n - 1), raceOf c j = raceOf c' j' := by
  have h1 : (c' : ℕ) < 2 * n := c'.isLt
  have h2 : (c : ℕ) < c' := h
  refine ⟨⟨c' - 1, by omega⟩, ⟨c, by omega⟩, ?_⟩
  have hA : ¬ ((c' : ℕ) - 1 < c) := by omega
  apply Subtype.ext
  simp only [raceOf, opponent, hA, h2, dif_neg, dif_pos, if_neg, if_pos, not_false_eq_true]
  ext
  · simp
  · simp; omega

theorem common_race {n : ℕ} (hn : 0 < n) (c c' : Fin (2 * n)) :
    ∃ j j' : Fin (2 * n - 1), raceOf c j = raceOf c' j' := by
  rcases lt_trichotomy c c' with h | h | h
  · exact common_race_lt c c' h
  · subst h
    exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩
  · obtain ⟨j, j', hj⟩ := common_race_lt c' c h
    exact ⟨j', j, hj.symm⟩

theorem athleteCode_injective (n : ℕ) (a a' : Ath n)
    (h : athleteCode n a = athleteCode n a') : a = a' := by
  unfold athleteCode at h
  have hb : (a.2 : ℕ) < n := a.2.isLt
  have hb' : (a'.2 : ℕ) < n := a'.2.isLt
  have h' : (a.1 : ℕ) * n + a.2 = (a'.1 : ℕ) * n + a'.2 := by omega
  have hc : (a.1 : ℕ) = a'.1 := by
    have e1 : ((a.1 : ℕ) * n + a.2) / n = a.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
    have e2 : ((a'.1 : ℕ) * n + a'.2) / n = a'.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb', zero_add]
    rw [← e1, ← e2, h']
  have hb2 : (a.2 : ℕ) = a'.2 := by rw [hc] at h'; omega
  exact Prod.ext (Fin.ext hc) (Fin.ext hb2)

theorem athleteCode_pos (n : ℕ) (a : Ath n) : 0 < athleteCode n a := by
  unfold athleteCode; omega

def decode (n : ℕ) (v : ℕ) : Option (Ath n) :=
  if h : 1 ≤ v ∧ v ≤ 2 * n ^ 2 ∧ 0 < n then
    some (⟨(v - 1) / n, by
      rw [Nat.div_lt_iff_lt_mul h.2.2]
      have h1 := h.1; have h2 := h.2.1
      have h3 : 2 * n ^ 2 = 2 * n * n := by ring
      omega⟩, ⟨(v - 1) % n, Nat.mod_lt _ h.2.2⟩)
  else none

theorem decode_code {n : ℕ} (hn : 0 < n) (a : Ath n) : decode n (athleteCode n a) = some a := by
  have hb : (a.2 : ℕ) < n := a.2.isLt
  have hc : (a.1 : ℕ) < 2 * n := a.1.isLt
  have hle : athleteCode n a ≤ 2 * n ^ 2 := by unfold athleteCode; nlinarith
  unfold decode
  rw [dif_pos ⟨athleteCode_pos n a, hle, hn⟩]
  congr 1
  have hv : athleteCode n a - 1 = (a.1 : ℕ) * n + a.2 := by unfold athleteCode; omega
  apply Prod.ext
  · apply Fin.ext
    simp only [hv]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  · apply Fin.ext
    simp only [hv]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-! ### Reading entries -/

section Reads

variable (n : ℕ)

def readRace (r : Race n) (p : Fin n) : DecisionTree (Idx n) Bool ℕ :=
  readNum fun t : Fin (wX n) => (Sum.inl (r, p, t) : Idx n)

theorem eval_readRace (r : Race n) (p : Fin n) (x : Idx n → Bool) :
    (readRace n r p).eval x = raceEntry n x r p := by
  simp [readRace, eval_readNum, raceEntry]

theorem queries_readRace (r : Race n) (p : Fin n) (x : Idx n → Bool) :
    (readRace n r p).queries x = wX n := queries_readNum _ x

def readCard (a : Ath n) (j : Fin (2 * n - 1)) : DecisionTree (Idx n) Bool ℕ :=
  readNum fun t : Fin (wY n) => (Sum.inr (a, j, t) : Idx n)

theorem eval_readCard (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readCard n a j).eval x = cardEntry n x a j := by
  simp [readCard, eval_readNum, cardEntry]

theorem queries_readCard (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readCard n a j).queries x = wY n := queries_readNum _ x

def entryIf (x : Idx n → Bool) (r : Race n) (p : ℕ) : ℕ :=
  if h : p < n then raceEntry n x r ⟨p, h⟩ else 0

def readEntryIf (r : Race n) (p : ℕ) : DecisionTree (Idx n) Bool ℕ :=
  if h : p < n then readRace n r ⟨p, h⟩ else .leaf 0

theorem eval_readEntryIf (r : Race n) (p : ℕ) (x : Idx n → Bool) :
    (readEntryIf n r p).eval x = entryIf n x r p := by
  unfold readEntryIf entryIf
  split_ifs
  · exact eval_readRace n r _ x
  · rfl

theorem queries_readEntryIf (r : Race n) (p : ℕ) (x : Idx n → Bool) :
    (readEntryIf n r p).queries x ≤ wX n := by
  unfold readEntryIf
  split_ifs
  · exact (queries_readRace n r _ x).le
  · exact Nat.zero_le _

def readClaim (a : Ath n) (j : Fin (2 * n - 1)) : DecisionTree (Idx n) Bool ℕ :=
  bindT (readCard n a j) fun y1 =>
    if h : (j : ℕ) = 0 then .leaf (y1 - 0) else
      bindT (readCard n a ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩) fun y0 => .leaf (y1 - y0)

theorem eval_readClaim (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readClaim n a j).eval x = claimedPos n x a j := by
  unfold readClaim claimedPos
  rw [eval_bindT, eval_readCard]
  split_ifs with h
  · rfl
  · rw [eval_bindT, eval_readCard]; rfl

theorem queries_readClaim (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readClaim n a j).queries x ≤ 2 * wY n := by
  unfold readClaim
  rw [queries_bindT, queries_readCard]
  split_ifs with h
  · simp [DecisionTree.queries]; omega
  · rw [queries_bindT, queries_readCard]; simp [DecisionTree.queries]; omega

end Reads


/-! ### Comparing two potential champions -/

section Compare

variable (n : ℕ) (hn : 0 < n)

/-- Indices `(j, j')` of a common race: `raceOf p.1 j = raceOf q.1 j'`. -/
noncomputable def J (p q : Ath n) : Fin (2 * n - 1) × Fin (2 * n - 1) :=
  ((common_race hn p.1 q.1).choose, (common_race hn p.1 q.1).choose_spec.choose)

theorem J_spec (p q : Ath n) : raceOf p.1 (J n hn p q).1 = raceOf q.1 (J n hn p q).2 :=
  (common_race hn p.1 q.1).choose_spec.choose_spec

def winner (p q : Ath n) (pp pq ep eq : ℕ) : Ath n :=
  if pp < n ∧ ep = athleteCode n p then
    (if pq < n ∧ eq = athleteCode n q then (if pp ≤ pq then p else q) else p)
  else (if pq < n ∧ eq = athleteCode n q then q else p)

noncomputable def cmp (p q : Ath n) : DecisionTree (Idx n) Bool (Ath n) :=
  if p = q then .leaf p else
  bindT (readClaim n p (J n hn p q).1) fun pp =>
  bindT (readClaim n q (J n hn p q).2) fun pq =>
  bindT (readEntryIf n (raceOf p.1 (J n hn p q).1) pp) fun ep =>
  bindT (readEntryIf n (raceOf p.1 (J n hn p q).1) pq) fun eq =>
  .leaf (winner n p q pp pq ep eq)

theorem queries_cmp (p q : Ath n) (x : Idx n → Bool) :
    (cmp n hn p q).queries x ≤ 4 * wY n + 2 * wX n := by
  unfold cmp
  split_ifs
  · simp [DecisionTree.queries]
  · simp only [queries_bindT, eval_bindT, DecisionTree.queries]
    have := queries_readClaim n p (J n hn p q).1 x
    have := queries_readClaim n q (J n hn p q).2 x
    have := queries_readEntryIf n (raceOf p.1 (J n hn p q).1) ((readClaim n p (J n hn p q).1).eval x) x
    have := queries_readEntryIf n (raceOf p.1 (J n hn p q).1)
      ((readClaim n q (J n hn p q).2).eval x) x
    omega

theorem eval_cmp (p q : Ath n) (x : Idx n → Bool) (hpq : p ≠ q) :
    (cmp n hn p q).eval x =
      winner n p q (claimedPos n x p (J n hn p q).1) (claimedPos n x q (J n hn p q).2)
        (entryIf n x (raceOf p.1 (J n hn p q).1) (claimedPos n x p (J n hn p q).1))
        (entryIf n x (raceOf p.1 (J n hn p q).1) (claimedPos n x q (J n hn p q).2)) := by
  unfold cmp
  rw [if_neg hpq]
  simp only [eval_bindT, eval_readClaim, eval_readEntryIf, DecisionTree.eval]

/-- Facts about a champion's claim in its `j`-th race. -/
theorem champ_claim {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (j : Fin (2 * n - 1)) :
    claimedPos n x a j < n ∧
      entryIf n x (raceOf a.1 j) (claimedPos n x a j) = athleteCode n a ∧
      ∀ m < claimedPos n x a j, entryIf n x (raceOf a.1 j) m = 0 := by
  obtain ⟨hlt, hq⟩ := ha.2.2 j
  refine ⟨hlt, ?_, fun m hm => ?_⟩
  · unfold entryIf; rw [dif_pos hlt]; exact (hq ⟨_, hlt⟩).2 rfl
  · unfold entryIf; rw [dif_pos (by omega)]; exact (hq ⟨m, by omega⟩).1 hm

theorem entryIf_lt {x : Idx n → Bool} {r : Race n} {m : ℕ} (h : entryIf n x r m ≠ 0) : m < n := by
  unfold entryIf at h; split_ifs at h with hm; exact hm; exact absurd rfl h

theorem cmp_left {x : Idx n → Bool} {p : Ath n} (hp : IsChampion n x p) (q : Ath n) :
    (cmp n hn p q).eval x = p := by
  by_cases hpq : p = q
  · unfold cmp; rw [if_pos hpq]; rfl
  rw [eval_cmp n hn p q x hpq]
  obtain ⟨hlt, hcode, hzero⟩ := champ_claim n hp (J n hn p q).1
  unfold winner
  rw [if_pos ⟨hlt, hcode⟩]
  split_ifs with hq hle
  · rfl
  · exfalso
    have := hzero (claimedPos n x q (J n hn p q).2) (by omega)
    rw [hq.2] at this
    exact absurd this (athleteCode_pos n q).ne'
  · rfl

theorem cmp_right {x : Idx n → Bool} {q : Ath n} (hq : IsChampion n x q) (p : Ath n) :
    (cmp n hn p q).eval x = q := by
  by_cases hpq : p = q
  · unfold cmp; rw [if_pos hpq]; exact hpq
  rw [eval_cmp n hn p q x hpq]
  obtain ⟨hlt, hcode, hzero⟩ := champ_claim n hq (J n hn p q).2
  rw [← J_spec n hn p q] at hcode hzero
  unfold winner
  split_ifs with hp hq' hle hq''
  · exfalso
    rcases Nat.lt_or_ge (claimedPos n x p (J n hn p q).1) (claimedPos n x q (J n hn p q).2)
      with hlt' | hge
    · have := hzero _ hlt'
      rw [hp.2] at this
      exact absurd this (athleteCode_pos n p).ne'
    · have heq : claimedPos n x p (J n hn p q).1 = claimedPos n x q (J n hn p q).2 := by omega
      have h2 := hp.2
      rw [heq, hcode] at h2
      exact hpq (athleteCode_injective n p q h2.symm)
  · rfl
  · exact absurd ⟨hlt, hcode⟩ hq'
  · rfl
  · exact absurd ⟨hlt, hcode⟩ hq''

end Compare

/-! ### Knockout over the candidate list -/

section Knock

variable (n : ℕ) (hn : 0 < n)

noncomputable def step (cur : Option (Ath n)) (v : ℕ) : DecisionTree (Idx n) Bool (Option (Ath n)) :=
  match decode n v, cur with
  | none, _ => .leaf cur
  | some q, none => .leaf (some q)
  | some q, some p => bindT (cmp n hn p q) fun w => .leaf (some w)

noncomputable def knock : Option (Ath n) → List ℕ → DecisionTree (Idx n) Bool (Option (Ath n))
  | cur, [] => .leaf cur
  | cur, v :: l => bindT (step n hn cur v) fun c' => knock c' l

theorem queries_step (cur : Option (Ath n)) (v : ℕ) (x : Idx n → Bool) :
    (step n hn cur v).queries x ≤ 4 * wY n + 2 * wX n := by
  unfold step
  rcases decode n v with _ | q <;> rcases cur with _ | p <;>
    simp only [DecisionTree.queries, Nat.zero_le]
  rw [queries_bindT]
  simp only [DecisionTree.queries, add_zero]
  exact queries_cmp n hn p q x

theorem queries_knock (l : List ℕ) (x : Idx n → Bool) :
    ∀ cur, (knock n hn cur l).queries x ≤ l.length * (4 * wY n + 2 * wX n) := by
  induction l with
  | nil => intro cur; simp [knock, DecisionTree.queries]
  | cons v l ih =>
    intro cur
    simp only [knock, queries_bindT, List.length_cons]
    have := queries_step n hn cur v x
    have := ih ((step n hn cur v).eval x)
    nlinarith

theorem step_keep {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (v : ℕ) :
    (step n hn (some a) v).eval x = some a := by
  unfold step
  rcases decode n v with _ | q
  · rfl
  · simp only [eval_bindT, DecisionTree.eval, cmp_left n hn ha q]

theorem step_hit {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (cur : Option (Ath n))
    (v : ℕ) (hv : decode n v = some a) : (step n hn cur v).eval x = some a := by
  unfold step
  rw [hv]
  rcases cur with _ | p
  · rfl
  · simp only [eval_bindT, DecisionTree.eval, cmp_right n hn ha p]

theorem knock_champ {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (l : List ℕ) :
    ∀ cur, (cur = some a ∨ ∃ v ∈ l, decode n v = some a) → (knock n hn cur l).eval x = some a := by
  induction l with
  | nil =>
    intro cur h
    rcases h with h | ⟨v, hv, -⟩
    · exact h
    · simp at hv
  | cons v l ih =>
    intro cur h
    simp only [knock, eval_bindT]
    apply ih
    rcases h with h | ⟨w, hw, hdec⟩
    · left; rw [h]; exact step_keep n hn ha v
    · rcases List.mem_cons.1 hw with rfl | hw'
      · left; exact step_hit n hn ha cur w hdec
      · by_cases hd : decode n v = some a
        · left; exact step_hit n hn ha cur v hd
        · right; exact ⟨w, hw', hdec⟩

end Knock


/-! ### Verifying a candidate -/

section Verify

variable (n : ℕ)

def posOf (Y : Fin (2 * n - 1) → ℕ) (j : Fin (2 * n - 1)) : ℕ :=
  Y j - (if h : (j : ℕ) = 0 then 0 else Y ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)

theorem sum_posOf_lt (hn : 0 < n) (Y : Fin (2 * n - 1) → ℕ)
    (hmono : ∀ j j' : Fin (2 * n - 1), j ≤ j' → Y j ≤ Y j')
    (hlast : ∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → Y j < n) :
    ∑ j, posOf n Y j < n := by
  let F : ℕ → ℕ := fun k =>
    if k = 0 then 0 else Y ⟨min (k - 1) (2 * n - 2), by omega⟩
  have hFmono : Monotone F := by
    intro k k' hk
    simp only [F]
    split_ifs with h1 h2
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact hmono _ _ (by simp only [Fin.le_def]; omega)
  have hpos : ∀ j : Fin (2 * n - 1), posOf n Y j = F (j + 1) - F j := by
    intro j
    have hj := j.isLt
    simp only [posOf, F]
    congr 1
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
      congr 1
      ext
      simp only
      omega
    · by_cases h0 : (j : ℕ) = 0
      · simp [h0]
      · rw [dif_neg h0, if_neg h0]
        congr 1
        ext
        simp only
        omega
  have hsum : ∑ j, posOf n Y j = F (2 * n - 1) - F 0 := by
    simp only [hpos]
    rw [Fin.sum_univ_eq_sum_range (fun i => F (i + 1) - F i)]
    exact Finset.sum_range_tsub hFmono _
  rw [hsum]
  have hlastj := hlast ⟨2 * n - 2, by omega⟩ (by simp only; omega)
  have hF : F (2 * n - 1) = Y ⟨2 * n - 2, by omega⟩ := by
    simp only [F]
    rw [if_neg (by omega)]
    congr 1
    ext
    simp only
    omega
  rw [hF]
  simp only [F, if_pos]
  omega

def checkRace (a : Ath n) (j : Fin (2 * n - 1)) (p : ℕ) : DecisionTree (Idx n) Bool Bool :=
  if p < n then
    bindT (seqList (fun m => bindT (readEntryIf n (raceOf a.1 j) m) fun e =>
        DecisionTree.leaf (decide (e = if m < p then 0 else athleteCode n a)))
      (List.range (p + 1))) fun bs => .leaf (bs.all id)
  else .leaf false

theorem eval_checkRace (a : Ath n) (j : Fin (2 * n - 1)) (p : ℕ) (x : Idx n → Bool) :
    (checkRace n a j p).eval x = decide (p < n ∧ ∀ m < p + 1,
      entryIf n x (raceOf a.1 j) m = if m < p then 0 else athleteCode n a) := by
  unfold checkRace
  split_ifs with h
  · simp only [eval_bindT, eval_seqList, DecisionTree.eval, eval_readEntryIf]
    simp only [h, true_and]
    rw [Bool.eq_iff_iff, List.all_eq_true]
    simp [Nat.lt_succ_iff]
  · simp [DecisionTree.eval, h]

theorem queries_checkRace (a : Ath n) (j : Fin (2 * n - 1)) (p : ℕ) (x : Idx n → Bool) :
    (checkRace n a j p).queries x ≤ (p + 1) * wX n := by
  unfold checkRace
  split_ifs with h
  · rw [queries_bindT]
    simp only [DecisionTree.queries, add_zero]
    have := queries_seqList_le (fun m => bindT (readEntryIf n (raceOf a.1 j) m) fun e =>
        (DecisionTree.leaf (decide (e = if m < p then 0 else athleteCode n a)) :
          DecisionTree (Idx n) Bool Bool)) (List.range (p + 1)) x (wX n) (fun m _ => by
        rw [queries_bindT]
        simp only [DecisionTree.queries, add_zero]
        exact queries_readEntryIf n _ m x)
    simpa using this
  · simp [DecisionTree.queries]

def validCard (Ys : List ℕ) : Prop :=
  (∀ j j' : Fin (2 * n - 1), j ≤ j' → Ys.getD j 0 ≤ Ys.getD j' 0) ∧
    (∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → Ys.getD j 0 < n)

instance (Ys : List ℕ) : Decidable (validCard n Ys) := by unfold validCard; infer_instance

def verify (a : Ath n) : DecisionTree (Idx n) Bool Bool :=
  bindT (seqList (readCard n a) (List.finRange (2 * n - 1))) fun Ys =>
    if validCard n Ys then
      bindT (seqList (fun j => checkRace n a j (posOf n (fun j => Ys.getD j 0) j))
        (List.finRange (2 * n - 1))) fun bs => .leaf (bs.all id)
    else .leaf false

theorem getD_map_finRange {k : ℕ} (g : Fin k → ℕ) (j : Fin k) :
    ((List.finRange k).map g).getD j 0 = g j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem eval_verify (a : Ath n) (x : Idx n → Bool) :
    (verify n a).eval x = decide (IsChampion n x a) := by
  unfold verify
  rw [eval_bindT, eval_seqList]
  simp only [eval_readCard]
  have hY : ∀ j : Fin (2 * n - 1),
      ((List.finRange (2 * n - 1)).map fun j => cardEntry n x a j).getD j 0 = cardEntry n x a j :=
    getD_map_finRange _
  have hYf : (fun j : Fin (2 * n - 1) =>
      ((List.finRange (2 * n - 1)).map fun j => cardEntry n x a j).getD j 0) =
      fun j => cardEntry n x a j := funext hY
  have hvalid : validCard n ((List.finRange (2 * n - 1)).map fun j => cardEntry n x a j) ↔
      (∀ j j' : Fin (2 * n - 1), j ≤ j' → cardEntry n x a j ≤ cardEntry n x a j') ∧
        (∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → cardEntry n x a j < n) := by
    unfold validCard
    simp only [hY]
  split_ifs with hv
  · rw [eval_bindT, eval_seqList]
    simp only [DecisionTree.eval, hYf, eval_checkRace]
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_map, List.mem_finRange, true_and, id_eq,
      forall_exists_index, forall_apply_eq_imp_iff, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨(hvalid.1 hv).1, (hvalid.1 hv).2, fun j => ?_⟩
      obtain ⟨hlt, hall⟩ := h j
      have hcp : claimedPos n x a j = posOf n (fun j => cardEntry n x a j) j := rfl
      refine ⟨by rw [hcp]; exact hlt, fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
      · have := hall q (by rw [hcp] at hq; omega)
        rw [if_pos (by rw [hcp] at hq; exact hq)] at this
        unfold entryIf at this
        rwa [dif_pos q.isLt] at this
      · have := hall q (by rw [hcp] at hq; omega)
        rw [if_neg (by rw [hcp] at hq; omega)] at this
        unfold entryIf at this
        rwa [dif_pos q.isLt] at this
    · intro hc j
      obtain ⟨hlt, hq⟩ := hc.2.2 j
      have hcp : claimedPos n x a j = posOf n (fun j => cardEntry n x a j) j := rfl
      rw [← hcp]
      refine ⟨hlt, fun m hm => ?_⟩
      unfold entryIf
      rw [dif_pos (by omega)]
      split_ifs with hmp
      · exact (hq ⟨m, by omega⟩).1 hmp
      · exact (hq ⟨m, by omega⟩).2 (by simp only; omega)
  · simp only [DecisionTree.eval]
    symm
    rw [decide_eq_false_iff_not]
    intro hc
    exact hv (hvalid.2 ⟨hc.1, hc.2.1⟩)

theorem queries_verify (hn : 0 < n) (a : Ath n) (x : Idx n → Bool) :
    (verify n a).queries x ≤ (2 * n - 1) * wY n + 3 * n * wX n := by
  unfold verify
  rw [queries_bindT]
  have h1 : (seqList (readCard n a) (List.finRange (2 * n - 1))).queries x ≤
      (2 * n - 1) * wY n := by
    have := queries_seqList_le (readCard n a) (List.finRange (2 * n - 1)) x (wY n)
      (fun j _ => (queries_readCard n a j x).le)
    simpa using this
  split_ifs with hv
  · rw [queries_bindT]
    simp only [DecisionTree.queries, add_zero]
    set Ys := (seqList (readCard n a) (List.finRange (2 * n - 1))).eval x
    have hsum := sum_posOf_lt n hn (fun j => Ys.getD j 0) hv.1 hv.2
    have h2 : (seqList (fun j => checkRace n a j (posOf n (fun j => Ys.getD j 0) j))
        (List.finRange (2 * n - 1))).queries x ≤ 3 * n * wX n := by
      rw [queries_seqList, ← Fin.sum_univ_def]
      calc ∑ j, (checkRace n a j (posOf n (fun j => Ys.getD j 0) j)).queries x
          ≤ ∑ j, (posOf n (fun j => Ys.getD j 0) j + 1) * wX n :=
            Finset.sum_le_sum fun j _ => queries_checkRace n a j _ x
        _ = (∑ j, posOf n (fun j => Ys.getD j 0) j + (2 * n - 1)) * wX n := by
            rw [← Finset.sum_mul, Finset.sum_add_distrib]
            simp
        _ ≤ 3 * n * wX n := by
            apply Nat.mul_le_mul_right
            omega
    omega
  · simp only [DecisionTree.queries, add_zero]
    exact h1.trans (Nat.le_add_right _ _)

end Verify


/-! ### The full algorithm -/

section Main

variable (n : ℕ) (hn : 0 < n)

def pairs : List (Fin (2 * n) × Fin 2) :=
  (List.finRange (2 * n)).flatMap fun c => (List.finRange 2).map fun i => (c, i)

theorem mem_pairs (c : Fin (2 * n)) (i : Fin 2) : (c, i) ∈ pairs n := by
  simp [pairs]

theorem length_pairs : (pairs n).length = 4 * n := by
  simp [pairs, List.length_flatMap]
  ring

def cands (s : Fin 2 → Fin (2 * n - 1)) : DecisionTree (Idx n) Bool (List ℕ) :=
  seqList (fun ci : Fin (2 * n) × Fin 2 => readRace n (raceOf ci.1 (s ci.2)) ⟨0, hn⟩) (pairs n)

noncomputable def alg (s : Fin 2 → Fin (2 * n - 1)) : DecisionTree (Idx n) Bool Bool :=
  bindT (cands n hn s) fun cl => bindT (knock n hn none cl) fun o =>
    match o with
    | none => .leaf false
    | some a => verify n a

def Tbound : ℕ :=
  4 * n * wX n + 4 * n * (4 * wY n + 2 * wX n) + ((2 * n - 1) * wY n + 3 * n * wX n)

theorem queries_alg (s : Fin 2 → Fin (2 * n - 1)) (x : Idx n → Bool) :
    (alg n hn s).queries x ≤ Tbound n := by
  unfold alg Tbound
  rw [queries_bindT, queries_bindT]
  have h1 : (cands n hn s).queries x ≤ 4 * n * wX n := by
    have := queries_seqList_le (fun ci : Fin (2 * n) × Fin 2 =>
      readRace n (raceOf ci.1 (s ci.2)) ⟨0, hn⟩) (pairs n) x (wX n)
      (fun ci _ => (queries_readRace n _ _ x).le)
    rwa [length_pairs] at this
  have hlen : ((cands n hn s).eval x).length = 4 * n := by
    unfold cands; rw [eval_seqList, List.length_map, length_pairs]
  have h2 := queries_knock n hn ((cands n hn s).eval x) x none
  rw [hlen] at h2
  have h3 : (match (knock n hn none ((cands n hn s).eval x)).eval x with
      | none => (DecisionTree.leaf false : DecisionTree (Idx n) Bool Bool)
      | some a => verify n a).queries x ≤ (2 * n - 1) * wY n + 3 * n * wX n := by
    rcases (knock n hn none ((cands n hn s).eval x)).eval x with _ | a
    · simp [DecisionTree.queries]
    · exact queries_verify n hn a x
  omega

theorem alg_noChamp (x : Idx n → Bool) (h : ¬ ∃ a, IsChampion n x a)
    (s : Fin 2 → Fin (2 * n - 1)) : (alg n hn s).eval x = false := by
  unfold alg
  rw [eval_bindT, eval_bindT]
  rcases (knock n hn none ((cands n hn s).eval x)).eval x with _ | a
  · rfl
  · show (verify n a).eval x = false
    rw [eval_verify, decide_eq_false_iff_not]
    exact fun ha => h ⟨a, ha⟩

theorem alg_champ (x : Idx n → Bool) (a : Ath n) (ha : IsChampion n x a)
    (s : Fin 2 → Fin (2 * n - 1))
    (hs : ∃ i, raceEntry n x (raceOf a.1 (s i)) ⟨0, hn⟩ = athleteCode n a) :
    (alg n hn s).eval x = true := by
  obtain ⟨i, hi⟩ := hs
  unfold alg
  rw [eval_bindT, eval_bindT]
  have hk : (knock n hn none ((cands n hn s).eval x)).eval x = some a := by
    apply knock_champ n hn ha
    right
    refine ⟨athleteCode n a, ?_, decode_code hn a⟩
    unfold cands
    rw [eval_seqList]
    exact List.mem_map.2 ⟨(a.1, i), mem_pairs n a.1 i, by rw [eval_readRace]; exact hi⟩
  rw [hk]
  show (verify n a).eval x = true
  rw [eval_verify]
  exact decide_eq_true ha

end Main

end RvsCertL3


end File_Sol_RvsCert_lemma_3

section File_Verify

open RvsCert QAlgorithms RvsCertL3

set_option linter.unusedSectionVars false

namespace L5

variable (n : ℕ)

/-! ### `G i = Y_{i-1}` (with `G 0 = 0`): start of race `i` in the running totals -/

def Gv (x : Idx n → Bool) (p : Ath n) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if h : i - 1 < 2 * n - 1 then cardEntry n x p ⟨i - 1, h⟩ else 0

def readG (p : Ath n) (i : ℕ) : DecisionTree (Idx n) Bool ℕ :=
  if i = 0 then .leaf 0 else if h : i - 1 < 2 * n - 1 then readCard n p ⟨i - 1, h⟩ else .leaf 0

theorem eval_readG (p : Ath n) (i : ℕ) (x : Idx n → Bool) :
    (readG n p i).eval x = Gv n x p i := by
  unfold readG Gv
  split_ifs
  · rfl
  · exact eval_readCard n p _ x
  · rfl

theorem queries_readG (p : Ath n) (i : ℕ) (x : Idx n → Bool) :
    (readG n p i).queries x ≤ wY n := by
  unfold readG
  split_ifs
  · exact Nat.zero_le _
  · exact (queries_readCard n p _ x).le
  · exact Nat.zero_le _

/-! ### Binary search for the race containing a global position -/

def bsT (p : Ath n) (u : ℕ) : ℕ → ℕ → ℕ → DecisionTree (Idx n) Bool ℕ
  | 0, lo, _ => .leaf lo
  | f + 1, lo, hi =>
    if hi ≤ lo + 1 then .leaf lo else
      bindT (readG n p ((lo + hi) / 2)) fun gm =>
        if gm ≤ u then bsT p u f ((lo + hi) / 2) hi else bsT p u f lo ((lo + hi) / 2)

theorem queries_bsT (p : Ath n) (u : ℕ) (x : Idx n → Bool) :
    ∀ f lo hi, (bsT n p u f lo hi).queries x ≤ f * wY n
  | 0, lo, hi => by simp [bsT, DecisionTree.queries]
  | f + 1, lo, hi => by
    unfold bsT
    split_ifs
    · simp [DecisionTree.queries]
    · rw [queries_bindT, eval_readG]
      have h1 := queries_readG n p ((lo + hi) / 2) x
      split_ifs
      · have := queries_bsT p u x f ((lo + hi) / 2) hi
        rw [Nat.succ_mul]; omega
      · have := queries_bsT p u x f lo ((lo + hi) / 2)
        rw [Nat.succ_mul]; omega

theorem bsT_spec (p : Ath n) (u : ℕ) (x : Idx n → Bool) :
    ∀ f lo hi, lo < hi → hi - lo ≤ 2 ^ f → Gv n x p lo ≤ u → u < Gv n x p hi →
      lo ≤ (bsT n p u f lo hi).eval x ∧ (bsT n p u f lo hi).eval x < hi ∧
        Gv n x p ((bsT n p u f lo hi).eval x) ≤ u ∧ u < Gv n x p ((bsT n p u f lo hi).eval x + 1)
  | 0, lo, hi, h1, h2, h3, h4 => by
    have : hi = lo + 1 := by simp at h2; omega
    subst this
    exact ⟨le_rfl, by simp [bsT, DecisionTree.eval], h3, h4⟩
  | f + 1, lo, hi, h1, h2, h3, h4 => by
    unfold bsT
    split_ifs with hh
    · have : hi = lo + 1 := by omega
      subst this
      exact ⟨le_rfl, by simp [DecisionTree.eval], h3, h4⟩
    · rw [eval_bindT, eval_readG]
      have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
      split_ifs with hm
      · have := bsT_spec p u x f ((lo + hi) / 2) hi (by omega) (by omega) hm h4
        exact ⟨by omega, this.2.1, this.2.2⟩
      · have := bsT_spec p u x f lo ((lo + hi) / 2) (by omega) (by omega) h3 (by omega)
        exact ⟨this.1, by omega, this.2.2⟩

/-! ### The certificate constraints of a potential champion -/

abbrev CI := Fin (2 * n - 1) ⊕ Fin (2 * n - 1) ⊕ Fin n ⊕ Unit

def fuel : ℕ := Nat.log 2 (2 * n - 1) + 1

/-- Tree `c` outputs `true` iff constraint `c` of "`p` is the champion" is violated. -/
noncomputable def conT (p : Ath n) : CI n → DecisionTree (Idx n) Bool Bool
  | .inl j =>
    if h : (j : ℕ) + 1 < 2 * n - 1 then
      bindT (readCard n p j) fun y1 => bindT (readCard n p ⟨j + 1, h⟩) fun y2 =>
        .leaf (decide (y2 < y1))
    else .leaf false
  | .inr (.inl j) =>
    bindT (readClaim n p j) fun cp => bindT (readEntryIf n (raceOf p.1 j) cp) fun e =>
      .leaf (decide ¬(cp < n ∧ e = athleteCode n p))
  | .inr (.inr (.inl u)) =>
    bindT (bsT n p u (fuel n) 0 (2 * n - 1)) fun j =>
      if hj : j < 2 * n - 1 then
        bindT (readG n p j) fun g0 => bindT (readG n p (j + 1)) fun g1 =>
          if g0 ≤ u ∧ u < g1 then
            bindT (readEntryIf n (raceOf p.1 ⟨j, hj⟩) (u - g0)) fun e => .leaf (decide (e ≠ 0))
          else .leaf false
      else .leaf false
  | .inr (.inr (.inr _)) =>
    if h : 2 * n - 2 < 2 * n - 1 then
      bindT (readCard n p ⟨2 * n - 2, h⟩) fun y => .leaf (decide (n ≤ y))
    else .leaf false

def dc : ℕ := (fuel n + 2) * wY n + wX n

theorem queries_conT (p : Ath n) (c : CI n) (x : Idx n → Bool) :
    (conT n p c).queries x ≤ dc n := by
  unfold dc
  rcases c with j | j | u | ⟨⟩
  · simp only [conT]
    split_ifs
    · simp only [queries_bindT, eval_bindT, queries_readCard, DecisionTree.queries]
      nlinarith
    · exact Nat.zero_le _
  · simp only [conT, queries_bindT, eval_bindT, DecisionTree.queries]
    have := queries_readClaim n p j x
    have := queries_readEntryIf n (raceOf p.1 j) ((readClaim n p j).eval x) x
    nlinarith
  · simp only [conT, queries_bindT]
    have hb := queries_bsT n p u x (fuel n) 0 (2 * n - 1)
    set j := (bsT n p u (fuel n) 0 (2 * n - 1)).eval x
    split_ifs with hj
    · simp only [queries_bindT, eval_bindT]
      have := queries_readG n p j x
      have := queries_readG n p (j + 1) x
      split_ifs
      · simp only [queries_bindT, DecisionTree.queries]
        have := queries_readEntryIf n (raceOf p.1 ⟨j, hj⟩) (u - (readG n p j).eval x) x
        nlinarith
      · simp only [DecisionTree.queries]; nlinarith
    · simp only [DecisionTree.queries]; nlinarith
  · simp only [conT]
    split_ifs
    · simp only [queries_bindT, queries_readCard, DecisionTree.queries]; nlinarith
    · exact Nat.zero_le _

theorem claimedPos_G (x : Idx n → Bool) (p : Ath n) (j : Fin (2 * n - 1)) :
    claimedPos n x p j = Gv n x p (j + 1) - Gv n x p j := by
  have hj := j.isLt
  have h1 : Gv n x p (j + 1) = cardEntry n x p j := by
    unfold Gv; rw [if_neg (by omega), dif_pos (by omega)]; rfl
  have h2 : Gv n x p j = if h : (j : ℕ) = 0 then 0 else
      cardEntry n x p ⟨(j : ℕ) - 1, by omega⟩ := by
    unfold Gv
    by_cases h0 : (j : ℕ) = 0
    · rw [if_pos h0, dif_pos h0]
    · rw [if_neg h0, dif_neg h0, dif_pos (by omega)]
  unfold claimedPos
  rw [h1, h2]

theorem Gv_mono (x : Idx n → Bool) (p : Ath n)
    (hmono : ∀ j j' : Fin (2 * n - 1), j ≤ j' → cardEntry n x p j ≤ cardEntry n x p j')
    (i i' : ℕ) (hii : i ≤ i') (hi' : i' ≤ 2 * n - 1) : Gv n x p i ≤ Gv n x p i' := by
  unfold Gv
  by_cases h0 : i = 0
  · rw [if_pos h0]; exact Nat.zero_le _
  · rw [if_neg h0, if_neg (by omega), dif_pos (by omega), dif_pos (by omega)]
    exact hmono _ _ (by simp only [Fin.le_def]; omega)

theorem conT_iff (hn : 0 < n) (x : Idx n → Bool) (p : Ath n) :
    IsChampion n x p ↔ ∀ c, (conT n p c).eval x = false := by
  constructor
  · intro ha c
    rcases c with j | j | u | ⟨⟩
    · simp only [conT]
      split_ifs with h
      · simp only [eval_bindT, eval_readCard, DecisionTree.eval, decide_eq_false_iff_not, not_lt]
        exact ha.1 _ _ (by simp only [Fin.le_def]; omega)
      · rfl
    · simp only [conT, eval_bindT, eval_readClaim, eval_readEntryIf, DecisionTree.eval,
        decide_eq_false_iff_not, not_not]
      obtain ⟨h1, h2, -⟩ := champ_claim n ha j
      exact ⟨h1, h2⟩
    · simp only [conT, eval_bindT]
      set j := (bsT n p u (fuel n) 0 (2 * n - 1)).eval x
      split_ifs with hj
      · simp only [eval_bindT, eval_readG]
        split_ifs with hu
        · simp only [eval_bindT, eval_readEntryIf, DecisionTree.eval, decide_eq_false_iff_not,
            not_not]
          obtain ⟨-, -, hz⟩ := champ_claim n ha ⟨j, hj⟩
          apply hz
          rw [claimedPos_G]
          simp only
          omega
        · rfl
      · rfl
    · simp only [conT]
      split_ifs with h
      · simp only [eval_bindT, eval_readCard, DecisionTree.eval, decide_eq_false_iff_not, not_le]
        exact ha.2.1 _ (by simp only; omega)
      · rfl
  · intro hc
    have hN : 0 < 2 * n - 1 := by omega
    -- adjacent monotonicity, then full monotonicity
    have hadj : ∀ j : ℕ, (hj : j + 1 < 2 * n - 1) →
        cardEntry n x p ⟨j, by omega⟩ ≤ cardEntry n x p ⟨j + 1, hj⟩ := by
      intro j hj
      have := hc (.inl ⟨j, by omega⟩)
      simp only [conT, dif_pos hj, eval_bindT, eval_readCard, DecisionTree.eval,
        decide_eq_false_iff_not, not_lt] at this
      exact this
    have hmono : ∀ j j' : Fin (2 * n - 1), j ≤ j' → cardEntry n x p j ≤ cardEntry n x p j' := by
      let F : ℕ → ℕ := fun k => cardEntry n x p ⟨min k (2 * n - 2), by omega⟩
      have hF : Monotone F := by
        apply monotone_nat_of_le_succ
        intro k
        simp only [F]
        by_cases hk : k + 1 ≤ 2 * n - 2
        · have := hadj k (by omega)
          have e1 : min k (2 * n - 2) = k := by omega
          have e2 : min (k + 1) (2 * n - 2) = k + 1 := by omega
          simp only [e1, e2]
          exact this
        · have e1 : min k (2 * n - 2) = 2 * n - 2 := by omega
          have e2 : min (k + 1) (2 * n - 2) = 2 * n - 2 := by omega
          simp only [e1, e2, le_refl]
      intro j j' hjj
      have := hF (show (j : ℕ) ≤ j' from hjj)
      simp only [F] at this
      have e1 : min (j : ℕ) (2 * n - 2) = j := by have := j.isLt; omega
      have e2 : min (j' : ℕ) (2 * n - 2) = j' := by have := j'.isLt; omega
      simp only [e1, e2] at this
      exact this
    have hlast : ∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → cardEntry n x p j < n := by
      intro j hj
      have := hc (.inr (.inr (.inr ())))
      simp only [conT, dif_pos (show 2 * n - 2 < 2 * n - 1 by omega), eval_bindT, eval_readCard,
        DecisionTree.eval, decide_eq_false_iff_not, not_le] at this
      have e : j = ⟨2 * n - 2, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e]; exact this
    refine ⟨hmono, hlast, fun j => ?_⟩
    have hC := hc (.inr (.inl j))
    simp only [conT, eval_bindT, eval_readClaim, eval_readEntryIf, DecisionTree.eval,
      decide_eq_false_iff_not, not_not] at hC
    obtain ⟨hlt, hcode⟩ := hC
    refine ⟨hlt, fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
    · -- a position before the claimed one: found by the binary search
      have hj := j.isLt
      have hG1 : Gv n x p (j + 1) = cardEntry n x p j := by
        unfold Gv; rw [if_neg (by omega), dif_pos (by omega)]; rfl
      have hcpG := claimedPos_G n x p j
      set u := Gv n x p j + q with hu
      have hu1 : u < Gv n x p (j + 1) := by omega
      have hYl : cardEntry n x p j < n := by
        have := hmono j ⟨2 * n - 2, by omega⟩ (by simp only [Fin.le_def]; omega)
        have := hlast ⟨2 * n - 2, by omega⟩ (by simp only; omega)
        omega
      have hun : u < n := by omega
      have hD := hc (.inr (.inr (.inl ⟨u, hun⟩)))
      have hGN : Gv n x p (2 * n - 1) ≥ Gv n x p (j + 1) :=
        Gv_mono n x p hmono _ _ (by omega) le_rfl
      have hspec := bsT_spec n p u x (fuel n) 0 (2 * n - 1) hN
        (by have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2 * n - 1)
            unfold fuel; omega)
        (by unfold Gv; simp) (by omega)
      set j' := (bsT n p u (fuel n) 0 (2 * n - 1)).eval x with hj'
      obtain ⟨-, hj'N, hg0, hg1⟩ := hspec
      have hjj : j' = j := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := Gv_mono n x p hmono (j' + 1) j (by omega) (by omega)
          omega
        · have := Gv_mono n x p hmono (j + 1) j' (by omega) (by omega)
          omega
      simp only [conT, eval_bindT] at hD
      rw [← hj', dif_pos hj'N] at hD
      simp only [eval_bindT, eval_readG] at hD
      rw [if_pos ⟨hg0, hg1⟩] at hD
      simp only [eval_bindT, eval_readEntryIf, DecisionTree.eval, decide_eq_false_iff_not,
        not_not] at hD
      have hfin : (⟨j', hj'N⟩ : Fin (2 * n - 1)) = j := Fin.ext hjj
      rw [hfin, hjj] at hD
      have hq' : u - Gv n x p j = q := by omega
      rw [hq'] at hD
      unfold entryIf at hD
      rwa [dif_pos q.isLt] at hD
    · have : (q : ℕ) = claimedPos n x p j := hq
      unfold entryIf at hcode
      rw [dif_pos hlt] at hcode
      have e : q = ⟨claimedPos n x p j, hlt⟩ := Fin.ext this
      rw [e]; exact hcode

end L5

end File_Verify

section File_Pivot

open RvsCert QAlgorithms RvsCertL3 QComp

set_option linter.unusedSectionVars false

namespace L5

variable (n : ℕ) (hn : 0 < n)

abbrev Slot := Fin (2 * n) × Fin 2
abbrev Seed := Fin 2 → Fin (2 * n - 1)
abbrev St := Finset (Ath n) × Option (Ath n)

def slotT (s : Seed n) (k : Slot n) : DecisionTree (Idx n) Bool ℕ :=
  readRace n (raceOf k.1 (s k.2)) ⟨0, hn⟩

def athS (x : Idx n → Bool) (s : Seed n) (k : Slot n) : Option (Ath n) :=
  decode n (raceEntry n x (raceOf k.1 (s k.2)) ⟨0, hn⟩)

/-- `q` survives `p`: it wins the comparison in both orders. -/
abbrev Surv (x : Idx n → Bool) (q p : Ath n) : Prop :=
  (cmp n hn p q).eval x = q ∧ (cmp n hn q p).eval x = q

noncomputable def survT (p q : Ath n) : DecisionTree (Idx n) Bool Bool :=
  bindT (cmp n hn p q) fun w1 => bindT (cmp n hn q p) fun w2 => .leaf (decide (w1 = q ∧ w2 = q))

theorem eval_survT (p q : Ath n) (x : Idx n → Bool) :
    (survT n hn p q).eval x = decide (Surv n hn x q p) := by
  simp [survT, eval_bindT, DecisionTree.eval]

def cc : ℕ := 4 * wY n + 2 * wX n

theorem queries_survT (p q : Ath n) (x : Idx n → Bool) :
    (survT n hn p q).queries x ≤ 2 * cc n := by
  simp only [survT, queries_bindT, eval_bindT, DecisionTree.queries]
  have := queries_cmp n hn p q x
  have := queries_cmp n hn q ((cmp n hn p q).eval x) x
  have := queries_cmp n hn q p x
  unfold cc; omega

theorem surv_asymm {x : Idx n → Bool} {q q' : Ath n} (hne : q ≠ q') (h : Surv n hn x q q') :
    ¬ Surv n hn x q' q := by
  intro h'
  exact hne (h.2.symm.trans h'.1)

theorem surv_champ {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (p : Ath n) :
    Surv n hn x a p := ⟨cmp_right n hn ha p, cmp_left n hn ha p⟩

theorem not_surv_champ {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) {q : Ath n}
    (hq : q ≠ a) : ¬ Surv n hn x q a := fun h => hq (h.1.symm.trans (cmp_left n hn ha q))

noncomputable def markQ (Kc : ℕ) (P : Finset (Ath n)) (q : Ath n) :
    DecisionTree (Idx n) Bool (Option (Ath n)) :=
  if q ∈ P ∨ Kc < P.card then .leaf none else
    bindT (seqList (fun p => survT n hn p q) P.toList) fun bs =>
      .leaf (if bs.all id then some q else none)

noncomputable def markT (Kc : ℕ) (s : Seed n) (P : Finset (Ath n)) (k : Slot n) :
    DecisionTree (Idx n) Bool (Option (Ath n)) :=
  bindT (slotT n hn s k) fun v => (decode n v).elim (.leaf none) (markQ n hn Kc P)

/-- The athlete at slot `k` if it is a live candidate (not a pivot, survives every pivot). -/
noncomputable def mval (x : Idx n → Bool) (s : Seed n) (P : Finset (Ath n)) (k : Slot n) : Option (Ath n) :=
  (athS n hn x s k).bind fun q => if q ∉ P ∧ ∀ p ∈ P, Surv n hn x q p then some q else none

theorem eval_markT (Kc : ℕ) (s : Seed n) (P : Finset (Ath n)) (hP : P.card ≤ Kc) (k : Slot n)
    (x : Idx n → Bool) : (markT n hn Kc s P k).eval x = mval n hn x s P k := by
  unfold markT mval athS
  rw [eval_bindT]
  simp only [slotT, eval_readRace]
  cases decode n (raceEntry n x (raceOf k.1 (s k.2)) ⟨0, hn⟩) with
  | none => rfl
  | some q =>
    simp only [Option.elim, Option.bind]
    unfold markQ
    by_cases hq : q ∈ P
    · rw [if_pos (Or.inl hq)]; simp [DecisionTree.eval, hq]
    · rw [if_neg (by rintro (h | h); exact hq h; omega)]
      simp only [eval_bindT, eval_seqList, DecisionTree.eval, eval_survT]
      have : ((P.toList.map fun p => decide (Surv n hn x q p)).all id = true) ↔
          ∀ p ∈ P, Surv n hn x q p := by
        simp [List.all_eq_true]
      by_cases hall : ∀ p ∈ P, Surv n hn x q p
      · rw [if_pos (this.2 hall), if_pos ⟨hq, hall⟩]
      · rw [if_neg (fun h => hall (this.1 h)), if_neg (fun h => hall h.2)]

def dP (Kc : ℕ) : ℕ := wX n + Kc * (2 * cc n)

theorem queries_markT (Kc : ℕ) (s : Seed n) (P : Finset (Ath n)) (k : Slot n)
    (x : Idx n → Bool) : (markT n hn Kc s P k).queries x ≤ dP n Kc := by
  unfold markT dP
  rw [queries_bindT]
  have h1 : (slotT n hn s k).queries x = wX n := queries_readRace n _ _ x
  rw [h1]
  cases decode n ((slotT n hn s k).eval x) with
  | none => simp [Option.elim, DecisionTree.queries]
  | some q =>
    simp only [Option.elim]
    unfold markQ
    split_ifs with h
    · simp [DecisionTree.queries]
    · push Not at h
      rw [queries_bindT]
      simp only [DecisionTree.queries, add_zero]
      have := queries_seqList_le (fun p => survT n hn p q) P.toList x (2 * cc n)
        (fun p _ => queries_survT n hn p q x)
      rw [Finset.length_toList] at this
      have : P.card * (2 * cc n) ≤ Kc * (2 * cc n) := Nat.mul_le_mul_right _ h.2
      omega

def updR (st : St n) : Option (Ath n) → St n
  | none => st
  | some q => (insert q st.1, some q)

noncomputable def updT (Kc : ℕ) (s : Seed n) (st : St n) :
    Option (Slot n) → DecisionTree (Idx n) Bool (St n)
  | none => .leaf st
  | some k => tmap (updR n st) (markT n hn Kc s st.1 k)

noncomputable def updV (x : Idx n → Bool) (s : Seed n) (st : St n) (o : Option (Slot n)) : St n :=
  updR n st (o.bind (mval n hn x s st.1))

theorem eval_updT (Kc : ℕ) (s : Seed n) (st : St n) (hP : st.1.card ≤ Kc)
    (o : Option (Slot n)) (x : Idx n → Bool) :
    (updT n hn Kc s st o).eval x = updV n hn x s st o := by
  cases o with
  | none => rfl
  | some k => simp only [updT, updV, eval_tmap, eval_markT n hn Kc s st.1 hP, Option.bind]

theorem queries_updT (Kc : ℕ) (s : Seed n) (st : St n) (o : Option (Slot n))
    (x : Idx n → Bool) : (updT n hn Kc s st o).queries x ≤ dP n Kc := by
  cases o with
  | none => simp [updT, DecisionTree.queries]
  | some k => simp only [updT, queries_tmap]; exact queries_markT n hn Kc s st.1 k x

/-! ### The potential and its halving -/

/-- Live non-champion slots, plus one if the champion is not yet a pivot. -/
noncomputable def Ψ (x : Idx n → Bool) (s : Seed n) (a : Ath n) (st : St n) : ℝ :=
  ((Finset.univ.filter fun k => (mval n hn x s st.1 k).isSome = true ∧
      athS n hn x s k ≠ some a).card : ℝ) + if a ∈ st.1 then 0 else 1

theorem Ψ_nonneg (x : Idx n → Bool) (s : Seed n) (a : Ath n) (st : St n) :
    0 ≤ Ψ n hn x s a st := by
  unfold Ψ; split_ifs <;> positivity

theorem mval_none_of_champ {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (s : Seed n)
    {P : Finset (Ath n)} (haP : a ∈ P) (k : Slot n) : mval n hn x s P k = none := by
  unfold mval
  cases athS n hn x s k with
  | none => rfl
  | some q =>
    simp only [Option.bind]
    rw [if_neg]
    rintro ⟨hq, hall⟩
    have hqa : q ≠ a := fun h => hq (h ▸ haP)
    exact not_surv_champ n hn ha hqa (hall a haP)

theorem mval_isSome {x : Idx n → Bool} {s : Seed n} {P : Finset (Ath n)} {k : Slot n} :
    (mval n hn x s P k).isSome = true ↔
      ∃ q, athS n hn x s k = some q ∧ q ∉ P ∧ ∀ p ∈ P, Surv n hn x q p := by
  unfold mval
  cases athS n hn x s k with
  | none => simp
  | some q =>
    simp only [Option.bind]
    split_ifs with h
    · simp only [Option.isSome_some, true_iff]; exact ⟨q, rfl, h.1, h.2⟩
    · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨q', hq', h1, h2⟩
      cases hq'
      exact h ⟨h1, h2⟩

theorem mval_eq_some {x : Idx n → Bool} {s : Seed n} {P : Finset (Ath n)} {k : Slot n} {q : Ath n}
    (h : mval n hn x s P k = some q) : athS n hn x s k = some q := by
  unfold mval at h
  cases hk : athS n hn x s k with
  | none => rw [hk] at h; simp at h
  | some q' =>
    rw [hk] at h
    simp only [Option.bind] at h
    split_ifs at h
    cases h; rfl

/-- Counting ordered pairs of an asymmetric relation. -/
theorem card_asymm {β : Type} [DecidableEq β] (S : Finset β) (Q : β → β → Prop)
    [DecidableRel Q] (hirr : ∀ k, ¬ Q k k) (hasym : ∀ k j, Q k j → ¬ Q j k) :
    2 * ((S ×ˢ S).filter fun p => Q p.1 p.2).card ≤ S.card * S.card - S.card := by
  set A := (S ×ˢ S).filter fun p => Q p.1 p.2
  have hA : A ⊆ S.offDiag := by
    intro p hp
    simp only [A, Finset.mem_filter, Finset.mem_product] at hp
    rw [Finset.mem_offDiag]
    exact ⟨hp.1.1, hp.1.2, fun h => hirr p.1 (by rw [h] at hp ⊢; exact hp.2)⟩
  have hB : A.image Prod.swap ⊆ S.offDiag := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hp
    have := hA hp'
    rw [Finset.mem_offDiag] at this ⊢
    exact ⟨this.2.1, this.1, fun h => this.2.2 h.symm⟩
  have hdisj : Disjoint A (A.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hp hp2
    obtain ⟨p', hp', he⟩ := Finset.mem_image.1 hp2
    simp only [A, Finset.mem_filter] at hp hp'
    rw [← he] at hp
    exact hasym _ _ hp'.2 hp.2
  have hcard : (A.image Prod.swap).card = A.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have := Finset.card_le_card (Finset.union_subset hA hB)
  rw [Finset.card_union_of_disjoint hdisj, hcard, Finset.offDiag_card] at this
  omega

theorem card_filter_product {β : Type} [DecidableEq β] (S : Finset β) (Q : β → β → Prop)
    [DecidableRel Q] :
    ∑ k ∈ S, ((S.filter fun j => Q k j).card : ℝ) =
      (((S ×ˢ S).filter fun p => Q p.1 p.2).card : ℝ) := by
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.card_filter]
  push_cast
  rfl

/-- **One pivot round** shrinks the expected potential by `7/8`. -/
theorem pivot_step {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (s : Seed n)
    (hk0 : ∃ k0, athS n hn x s k0 = some a) (st : St n) (σ : Option (Slot n) → ℝ) (ρ : ℝ)
    (hσ1 : ∑ o, σ o = 1)
    (hρ : (∃ k, (mval n hn x s st.1 k).isSome = true) → 1 / 4 ≤ ρ)
    (hform : ∀ k, σ (some k) = if (mval n hn x s st.1 k).isSome = true then
      ρ / cnt (fun k => (mval n hn x s st.1 k).isSome) else 0) :
    ∑ o, σ o * Ψ n hn x s a (updV n hn x s st o) ≤ 7 / 8 * Ψ n hn x s a st := by
  obtain ⟨P, l⟩ := st
  simp only at hρ hform ⊢
  rw [Fintype.sum_option] at hσ1 ⊢
  have hnone : updV n hn x s (P, l) none = (P, l) := rfl
  rw [hnone]
  by_cases haP : a ∈ P
  · -- the champion is already a pivot: nothing is live
    have hm : ∀ k, mval n hn x s P k = none := mval_none_of_champ n hn ha s haP
    have hσk : ∀ k, σ (some k) = 0 := fun k => by rw [hform, hm k]; simp
    have hΨ : Ψ n hn x s a (P, l) = 0 := by
      unfold Ψ
      simp [hm, haP]
    simp [hσk, hΨ]
  · obtain ⟨k0, hk0⟩ := hk0
    have hlive0 : mval n hn x s P k0 = some a := by
      unfold mval; rw [hk0]; simp only [Option.bind]
      rw [if_pos ⟨haP, fun p _ => surv_champ n hn ha p⟩]
    set mk := fun k => (mval n hn x s P k).isSome with hmk
    set S := Finset.univ.filter fun k => mk k = true with hS
    have ht : cnt mk = S.card := rfl
    have hk0S : k0 ∈ S := by simp [hS, hmk, hlive0]
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 ⟨k0, hk0S⟩
    have hρ' : 1 / 4 ≤ ρ := hρ ⟨k0, by rw [hlive0]; rfl⟩
    -- athletes of live slots
    let f : Slot n → Ath n := fun k => (athS n hn x s k).getD a
    have hf : ∀ k ∈ S, mval n hn x s P k = some (f k) := by
      intro k hk
      simp only [hS, hmk, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hk
      have := mval_eq_some n hn hq
      simp only [f, this, Option.getD_some]
      exact hq
    have hfS : ∀ k ∈ S, f k ∉ P ∧ ∀ p ∈ P, Surv n hn x (f k) p := by
      intro k hk
      obtain ⟨q, hq1, hq2, hq3⟩ := (mval_isSome n hn).1 (by rw [hf k hk]; rfl)
      have : f k = q := by simp only [f, hq1, Option.getD_some]
      rw [this]; exact ⟨hq2, hq3⟩
    have hathS : ∀ k ∈ S, athS n hn x s k = some (f k) := fun k hk => mval_eq_some n hn (hf k hk)
    set S' := S.filter fun k => f k ≠ a with hS'
    have hΨst : Ψ n hn x s a (P, l) = S'.card + 1 := by
      have hset : (Finset.univ.filter fun k => (mval n hn x s (P, l).1 k).isSome = true ∧
          athS n hn x s k ≠ some a) = S' := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS', hS, hmk]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun h => h2 ?_⟩
          rw [hathS k (by simp [hS, hmk, h1]), h]
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun h => h2 ?_⟩
          rw [hathS k (by simp [hS, hmk, h1])] at h
          exact Option.some_injective _ h
      unfold Ψ
      rw [if_neg haP, hset]
    -- the potential after picking a live slot
    let Q : Slot n → Slot n → Prop := fun k j => f j ≠ f k ∧ Surv n hn x (f j) (f k)
    have hnext : ∀ k ∈ S, Ψ n hn x s a (updV n hn x s (P, l) (some k)) =
        if f k = a then 0 else ((S'.filter fun j => Q k j).card : ℝ) + 1 := by
      intro k hk
      simp only [updV, Option.bind, hf k hk, updR]
      by_cases hka : f k = a
      · rw [if_pos hka]
        have haP' : a ∈ insert (f k) P := by rw [hka]; exact Finset.mem_insert_self _ _
        unfold Ψ
        simp [mval_none_of_champ n hn ha s haP', haP']
      · rw [if_neg hka]
        unfold Ψ
        have haP' : a ∉ insert (f k) P := by
          rw [Finset.mem_insert, not_or]; exact ⟨fun h => hka h.symm, haP⟩
        rw [if_neg haP']
        congr 2
        apply congrArg Finset.card
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS', hS, hmk, Q]
        rw [mval_isSome n hn]
        constructor
        · rintro ⟨⟨q, hq1, hq2, hq3⟩, hja⟩
          have hjS : (mval n hn x s P j).isSome = true :=
            (mval_isSome n hn).2 ⟨q, hq1, fun h => hq2 (Finset.mem_insert_of_mem h),
              fun p hp => hq3 p (Finset.mem_insert_of_mem hp)⟩
          have hfj : f j = q := by simp only [f, hq1, Option.getD_some]
          refine ⟨⟨hjS, ?_⟩, ?_, ?_⟩
          · rw [hfj]; intro h; exact hja (by rw [hq1, h])
          · rw [hfj]; intro h; exact hq2 (by rw [h]; exact Finset.mem_insert_self _ _)
          · rw [hfj]; exact hq3 _ (Finset.mem_insert_self _ _)
        · rintro ⟨⟨hjS, hja⟩, hne, hsv⟩
          have hjS' : j ∈ S := by simp [hS, hmk, hjS]
          refine ⟨⟨f j, hathS j hjS', ?_, ?_⟩, ?_⟩
          · rw [Finset.mem_insert, not_or]; exact ⟨hne, (hfS j hjS').1⟩
          · intro p hp
            rcases Finset.mem_insert.1 hp with rfl | hp
            · exact hsv
            · exact (hfS j hjS').2 p hp
          · rw [hathS j hjS']; intro h; exact hja (Option.some_injective _ h)
    -- sum of the next potentials over live slots
    have hsumS : 2 * ∑ k ∈ S, Ψ n hn x s a (updV n hn x s (P, l) (some k)) ≤
        S.card * (S'.card + 1) := by
      rw [Finset.sum_congr rfl hnext]
      have hsplit : ∑ k ∈ S, (if f k = a then (0 : ℝ) else
          ((S'.filter fun j => Q k j).card : ℝ) + 1) =
          ∑ k ∈ S', (((S'.filter fun j => Q k j).card : ℝ) + 1) := by
        rw [hS', Finset.sum_filter (s := S) (p := fun k => f k ≠ a)]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases h : f k = a <;> simp [h]
      rw [hsplit, Finset.sum_add_distrib, card_filter_product, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      have hasy := card_asymm S' Q (fun k h => h.1 rfl)
        (fun k j h h' => surv_asymm n hn h'.1 h'.2 h.2)
      have hS'S : S'.card + 1 ≤ S.card := by
        have : S' ⊂ S := by
          refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨k0, hk0S, ?_⟩
          simp only [hS', Finset.mem_filter, not_and, not_not]
          intro _
          have := hathS k0 hk0S
          rw [hk0] at this
          exact (Option.some_injective _ this).symm
        exact Finset.card_lt_card this
      have h1 : (2 : ℝ) * ((S' ×ˢ S').filter fun p => Q p.1 p.2).card ≤
          (S'.card : ℝ) * S'.card - S'.card := by
        have h' : 2 * ((S' ×ˢ S').filter fun p => Q p.1 p.2).card + S'.card ≤
            S'.card * S'.card := by
          have := Nat.le_mul_self S'.card
          omega
        have : ((2 * ((S' ×ˢ S').filter fun p => Q p.1 p.2).card + S'.card : ℕ) : ℝ) ≤
            ((S'.card * S'.card : ℕ) : ℝ) := by exact_mod_cast h'
        push_cast at this
        linarith
      have h2 : ((S'.card : ℝ) + 1) ≤ S.card := by exact_mod_cast hS'S
      nlinarith [Nat.cast_nonneg (α := ℝ) S'.card]
    -- assemble
    have hσk : ∀ k, σ (some k) = if mk k = true then ρ / S.card else 0 := by
      intro k; rw [hform]; rfl
    have hσsum : ∑ k, σ (some k) = ρ := by
      rw [Finset.sum_congr rfl fun k _ => hσk k]
      rw [sum_mk mk (ρ / S.card) 0, ht, mul_zero, add_zero, mul_comm]
      exact div_mul_cancel₀ ρ hSpos.ne'
    have hσnone : σ none = 1 - ρ := by linarith
    have hterm : ∑ k, σ (some k) * Ψ n hn x s a (updV n hn x s (P, l) (some k)) =
        ρ / S.card * ∑ k ∈ S, Ψ n hn x s a (updV n hn x s (P, l) (some k)) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => by
        rw [hσk]
        have : ¬ mk k = true := by simpa [hS] using hk
        simp [this])]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hσk]
      have : mk k = true := by simpa [hS] using hk
      simp [this]
    rw [hσnone, hterm]
    have hΨ0 := Ψ_nonneg n hn x s a (P, l)
    have hbound : ρ / S.card * ∑ k ∈ S, Ψ n hn x s a (updV n hn x s (P, l) (some k)) ≤
        ρ / 2 * Ψ n hn x s a (P, l) := by
      rw [hΨst]
      rw [div_mul_eq_mul_div, div_le_iff₀ hSpos]
      have hρ0 : 0 ≤ ρ := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hsumS hρ0]
    nlinarith

end L5

end File_Pivot

section File_Main

open RvsCert QAlgorithms RvsCertL3 QComp

set_option linter.unusedSectionVars false

namespace L5

variable (n : ℕ)

def Kp : ℕ := 6 * (Nat.log 2 n + 7)

def i0 (hn : 0 < n) : Idx n :=
  Sum.inr ((⟨0, by omega⟩, ⟨0, hn⟩), ⟨0, by omega⟩, ⟨0, by unfold wY; omega⟩)

theorem kernel_swap {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] (σ : γ → ℝ)
    (e : γ → β) (Ψ : β → ℝ) :
    ∑ b, (∑ o, σ o * (if b = e o then 1 else 0)) * Ψ b = ∑ o, σ o * Ψ (e o) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [ite_mul]

theorem kernel_supp {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] (σ : γ → ℝ)
    (e : γ → β) (b : β) (h : ∑ o, σ o * (if b = e o then 1 else 0) ≠ 0) :
    ∃ o, σ o ≠ 0 ∧ b = e o := by
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨o, fun h0 => ho (by rw [h0, zero_mul]), ?_⟩
  by_contra hne
  exact ho (by rw [if_neg hne, mul_zero])

theorem sum_samp {K : Type} [Fintype K] [DecidableEq K] (mk : K → Bool) (ρ : ℝ) (h : ∃ k, mk k = true) :
    ∑ k, (if mk k = true then ρ / cnt mk else 0) = ρ := by
  obtain ⟨k0, hk0⟩ := h
  have hpos : 0 < cnt mk := cnt_pos hk0
  rw [sum_mk mk (ρ / cnt mk) 0, mul_zero, add_zero, mul_comm]
  exact div_mul_cancel₀ ρ hpos.ne'

theorem pow_bound : ((7 : ℝ) / 8) ^ Kp n * (4 * n + 1) ≤ 1 / 12 := by
  have h6 : ((7 : ℝ) / 8) ^ 6 ≤ 1 / 2 := by norm_num
  set M := Nat.log 2 n + 7
  have hK : ((7 : ℝ) / 8) ^ Kp n ≤ (1 / 2) ^ M := by
    unfold Kp
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) h6 M
  have h2 : 48 * n + 12 ≤ 2 ^ M := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    have e : 2 ^ M = 128 * 2 ^ Nat.log 2 n := by simp only [M]; ring
    rw [e]
    rw [pow_succ] at this
    omega
  have h2' : (48 * n + 12 : ℝ) ≤ 2 ^ M := by exact_mod_cast h2
  have hpos : (0 : ℝ) < 2 ^ M := by positivity
  calc ((7 : ℝ) / 8) ^ Kp n * (4 * n + 1) ≤ (1 / 2) ^ M * (4 * n + 1) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (4 * n + 1) / 2 ^ M := by rw [one_div_pow]; ring
    _ ≤ 1 / 12 := by
        rw [div_le_iff₀ hpos]
        linarith

/-- **Lemma 5, quantitative form.** -/
theorem lemma5_main (hn : 0 < n) :
    ∃ T : ℕ, quantQC (champion n) ≤ T ∧
      T = 0 + Kp n * ((Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) + dP n (Kp n) +
        dP n (Kp n)) + (0 + 4 * ((Nat.sqrt (Fintype.card (CI n)) + 1) * (2 * dc n) + dc n)) := by
  have : Nonempty (Idx n) := ⟨i0 n hn⟩
  have : Nonempty (Slot n) := ⟨(⟨0, by omega⟩, 0)⟩
  have : Nonempty (CI n) := ⟨.inr (.inr (.inr ()))⟩
  have : Nonempty (Fin (2 * n - 1)) := ⟨⟨0, by omega⟩⟩
  -- pivot rounds
  have hs := fun (s : Seed n) (st : St n) => grover_sampler (i0 n hn)
    (markT n hn (Kp n) s st.1) (dP n (Kp n)) (fun k x => queries_markT n hn (Kp n) s st.1 k x)
    Option.isSome
  choose σ hσA ρ hρ hσf using hs
  set Tsamp := (Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) + dP n (Kp n)
    with hTsamp
  let κ : Seed n → (Idx n → Bool) → St n → St n → ℝ := fun s x st st' =>
    ∑ o, σ s st x o * (if st' = (updT n hn (Kp n) s st o).eval x then 1 else 0)
  have hround : ∀ s st, Achievable (Tsamp + dP n (Kp n)) (fun x st' => κ s x st st') :=
    fun s st => (hσA s st).bind (fun o => Achievable.tree (i0 n hn) (updT n hn (Kp n) s st o)
      (dP n (Kp n)) (fun x => queries_updT n hn (Kp n) s st o x))
  let μ0 : St n → ℝ := fun st => if st = (∅, none) then 1 else 0
  have h0 : Achievable 0 (fun (_ : Idx n → Bool) st => μ0 st) :=
    Achievable.const 0 ((∅, none) : St n)
  have hpiv : ∀ s, Achievable (0 + Kp n * (Tsamp + dP n (Kp n)))
      (fun x => iterD μ0 (κ s x) (Kp n)) := fun s => Achievable.iter h0 (hround s) (Kp n)
  -- verification rounds
  have hv := fun (p : Ath n) => grover_sampler (i0 n hn) (conT n p) (dc n)
    (fun c x => queries_conT n p c x) id
  choose σv hσvA ρv hρv hσvf using hv
  set Tvs := (Nat.sqrt (Fintype.card (CI n)) + 1) * (2 * dc n) + dc n with hTvs
  let κv : Ath n → (Idx n → Bool) → Bool → Bool → ℝ := fun p x f f' =>
    if f then (if f' = true then 1 else 0) else ∑ o, if o.isSome = f' then σv p x o else 0
  have hvr : ∀ p f, Achievable Tvs (fun x f' => κv p x f f') := by
    intro p f
    cases f
    · exact ((hσvA p).map Option.isSome).congr fun x b => by simp [κv]
    · exact (Achievable.const Tvs true).congr fun x b => by simp [κv]
  let μv0 : Bool → ℝ := fun f => if f = false then 1 else 0
  have hv0 : Achievable 0 (fun (_ : Idx n → Bool) f => μv0 f) := Achievable.const 0 false
  have hver : ∀ p, Achievable (0 + 4 * Tvs) (fun x => iterD μv0 (κv p x) 4) :=
    fun p => Achievable.iter hv0 (hvr p) 4
  let Vd : (Idx n → Bool) → St n → Bool → ℝ := fun x st b =>
    match st.2 with
    | none => if b = false then 1 else 0
    | some p => ∑ f, if (!f) = b then iterD μv0 (κv p x) 4 f else 0
  have hV : ∀ st, Achievable (0 + 4 * Tvs) (fun x b => Vd x st b) := by
    intro st
    rcases st with ⟨P, _ | p⟩
    · exact Achievable.const _ false
    · exact (hver p).map (fun f => !f)
  have hfull : ∀ s, Achievable (0 + Kp n * (Tsamp + dP n (Kp n)) + (0 + 4 * Tvs))
      (fun x b => ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st b) := fun s => (hpiv s).bind hV
  set Ns := (Fintype.card (Seed n) : ℝ) with hNs
  have hNpos : 0 < Ns := by rw [hNs]; exact_mod_cast Fintype.card_pos
  have hπ1 : ∑ _s : Seed n, 1 / Ns = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNs]; field_simp
  have hmix := Achievable.mix (fun _ : Seed n => 1 / Ns) (fun _ => by positivity) hπ1 hfull
  -- basic facts
  have hκnn : ∀ s x st st', 0 ≤ κ s x st st' := fun s x st st' => (hround s st).nonneg x st'
  have hμ0nn : ∀ st, 0 ≤ μ0 st := fun st => by simp only [μ0]; split_ifs <;> norm_num
  have hκvnn : ∀ p x f f', 0 ≤ κv p x f f' := fun p x f f' => (hvr p f).nonneg x f'
  have hμv0nn : ∀ f, 0 ≤ μv0 f := fun f => by simp only [μv0]; split_ifs <;> norm_num
  have hVnn : ∀ x st b, 0 ≤ Vd x st b := fun x st b => (hV st).nonneg x b
  have hpivsum : ∀ s x, ∑ st, iterD μ0 (κ s x) (Kp n) st = 1 := fun s x => (hpiv s).sum_one x
  have hpivnn : ∀ s x st, 0 ≤ iterD μ0 (κ s x) (Kp n) st := fun s x st => (hpiv s).nonneg x st
  have hversum : ∀ p x, ∑ f, iterD μv0 (κv p x) 4 f = 1 := fun p x => (hver p).sum_one x
  have hvernn : ∀ p x f, 0 ≤ iterD μv0 (κv p x) 4 f := fun p x f => (hver p).nonneg x f
  -- (V1) the champion is never rejected
  have hV1 : ∀ x p, IsChampion n x p → iterD μv0 (κv p x) 4 true = 0 := by
    intro x p hp
    have hall := (conT_iff n hn x p).1 hp
    have hpot := iterD_potential μv0 (κv p x) hμv0nn (hκvnn p x) (fun f => if f then 1 else 0) 1
      (by norm_num) (fun _ _ => True) 4 (fun _ _ => trivial) (fun k _ f _ => by
        rw [Fintype.sum_bool]
        cases f
        · simp only [κv, Bool.false_eq_true, if_false, if_true, mul_one, mul_zero, add_zero,
            one_mul]
          rw [Fintype.sum_option]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false, Option.isSome_some,
            if_true, zero_add]
          apply le_of_eq
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [hσvf p x k, hall k]
          simp
        · simp [κv])
      (fun _ _ _ _ _ _ => trivial)
    have h := hpot.2
    rw [Fintype.sum_bool, Fintype.sum_bool] at h
    simp only [μv0, if_true, if_false, mul_one, mul_zero, Bool.false_eq_true, one_pow,
      zero_add, add_zero] at h
    have := hvernn p x true
    simp at h
    linarith
  -- (V2) a non-champion is accepted with probability at most `(3/4)^4`
  have hV2 : ∀ x p, ¬ IsChampion n x p → iterD μv0 (κv p x) 4 false ≤ (3 / 4) ^ 4 := by
    intro x p hp
    have hviol : ∃ c, (conT n p c).eval x = true := by
      by_contra hcon
      push Not at hcon
      exact hp ((conT_iff n hn x p).2 fun c => by simpa using hcon c)
    have hρ1 := hρv p x hviol
    have hs1 := (hσvA p).sum_one x
    rw [Fintype.sum_option] at hs1
    have hsome : ∑ k, σv p x (some k) = ρv p x := by
      rw [Finset.sum_congr rfl fun k _ => hσvf p x k]
      exact sum_samp _ _ (by obtain ⟨c, hc⟩ := hviol; exact ⟨c, by simpa using hc⟩)
    have hpot := iterD_potential μv0 (κv p x) hμv0nn (hκvnn p x)
      (fun f => if f then 0 else 1) (3 / 4) (by norm_num) (fun _ _ => True) 4
      (fun _ _ => trivial) (fun k _ f _ => by
        rw [Fintype.sum_bool]
        cases f
        · simp only [κv, Bool.false_eq_true, if_false, if_true, mul_one, mul_zero, zero_add]
          rw [Fintype.sum_option]
          simp only [Option.isSome_none, if_true, Option.isSome_some, Bool.true_eq_false,
            if_false, Finset.sum_const_zero, add_zero]
          linarith
        · simp [κv])
      (fun _ _ _ _ _ _ => trivial)
    have h := hpot.2
    rw [Fintype.sum_bool, Fintype.sum_bool] at h
    simp only [μv0, if_true, if_false, mul_one, mul_zero, Bool.false_eq_true, zero_add,
      add_zero] at h
    simpa using h
  -- (P) the pivot loop ends at the champion
  have hP : ∀ x s a, IsChampion n x a → (∃ k0, athS n hn x s k0 = some a) →
      1 - 1 / 12 ≤ ∑ st, iterD μ0 (κ s x) (Kp n) st * (if st.2 = some a then 1 else 0) := by
    intro x s a ha hk0
    let I : ℕ → St n → Prop := fun k st => st.1.card ≤ k ∧ (a ∈ st.1 → st.2 = some a)
    have hpot := iterD_potential μ0 (κ s x) hμ0nn (hκnn s x) (Ψ n hn x s a) (7 / 8)
      (by norm_num) I (Kp n)
      (fun st h => by
        simp only [μ0] at h
        split_ifs at h with he
        · subst he; exact ⟨by simp, by simp⟩
        · exact absurd rfl h)
      (fun k hk st hst => by
        have hc : st.1.card ≤ Kp n := by have := hst.1; omega
        simp only [κ]
        rw [kernel_swap]
        simp only [eval_updT n hn (Kp n) s st hc]
        apply pivot_step n hn ha s hk0 st (σ s st x) (ρ s st x)
        · exact (hσA s st).sum_one x
        · intro h
          apply hρ s st x
          simpa [eval_markT n hn (Kp n) s st.1 hc] using h
        · intro k
          rw [hσf s st x k]
          simp only [eval_markT n hn (Kp n) s st.1 hc])
      (fun k hk st b hst hb => by
        have hc : st.1.card ≤ Kp n := by have := hst.1; omega
        obtain ⟨o, ho, rfl⟩ := kernel_supp _ _ _ hb
        rw [eval_updT n hn (Kp n) s st hc]
        cases o with
        | none => exact ⟨by have := hst.1; simp only [updV, Option.bind, updR]; omega, hst.2⟩
        | some k' =>
          have hlive : (mval n hn x s st.1 k').isSome = true := by
            by_contra hcon
            apply ho
            rw [hσf s st x k']
            simp only [eval_markT n hn (Kp n) s st.1 hc]
            simp [hcon]
          obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hlive
          simp only [updV, Option.bind, hq, updR]
          refine ⟨(Finset.card_insert_le _ _).trans (by have := hst.1; omega), fun h => ?_⟩
          rcases Finset.mem_insert.1 h with h | h
          · rw [h]
          · exfalso
            rw [mval_none_of_champ n hn ha s h] at hq
            simp at hq)
    obtain ⟨hsupp, hsum⟩ := hpot
    have hΨ0 : ∑ st, μ0 st * Ψ n hn x s a st ≤ 4 * n + 1 := by
      simp only [μ0, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      unfold Ψ
      simp only [Finset.notMem_empty, if_false]
      have hc : ∀ F : Finset (Slot n), (F.card : ℝ) ≤ 4 * n := by
        intro F
        have : F.card ≤ 4 * n := (Finset.card_le_univ F).trans (by simp; omega)
        exact_mod_cast this
      linarith [hc (Finset.univ.filter fun k => (mval n hn x s ∅ k).isSome = true ∧
          athS n hn x s k ≠ some a)]
    have hbad : ∑ st, iterD μ0 (κ s x) (Kp n) st * (if st.2 = some a then 0 else 1) ≤
        ∑ st, iterD μ0 (κ s x) (Kp n) st * Ψ n hn x s a st := by
      refine Finset.sum_le_sum fun st _ => ?_
      by_cases h0 : iterD μ0 (κ s x) (Kp n) st = 0
      · rw [h0, zero_mul, zero_mul]
      · apply mul_le_mul_of_nonneg_left _ (hpivnn s x st)
        split_ifs with h2
        · exact Ψ_nonneg n hn x s a st
        · have haP : a ∉ st.1 := fun h => h2 ((hsupp st h0).2 h)
          unfold Ψ
          rw [if_neg haP]
          have : (0 : ℝ) ≤ _ := Nat.cast_nonneg ((Finset.univ.filter fun k =>
            (mval n hn x s st.1 k).isSome = true ∧ athS n hn x s k ≠ some a).card)
          linarith
    have hsplit : ∑ st, iterD μ0 (κ s x) (Kp n) st * (if st.2 = some a then 1 else 0) =
        1 - ∑ st, iterD μ0 (κ s x) (Kp n) st * (if st.2 = some a then 0 else 1) := by
      have e : ∀ st, iterD μ0 (κ s x) (Kp n) st * (if st.2 = some a then 1 else 0) =
          iterD μ0 (κ s x) (Kp n) st -
            iterD μ0 (κ s x) (Kp n) st * (if st.2 = some a then 0 else 1) := by
        intro st; split_ifs <;> ring
      rw [Finset.sum_congr rfl fun st _ => e st, Finset.sum_sub_distrib, hpivsum s x]
    rw [hsplit]
    have hpb := pow_bound n
    have : ((7 : ℝ) / 8) ^ Kp n * ∑ st, μ0 st * Ψ n hn x s a st ≤ 1 / 12 :=
      (mul_le_mul_of_nonneg_left hΨ0 (by positivity)).trans hpb
    linarith
  -- the success probability
  obtain ⟨w, A, out, hA⟩ := hmix
  refine ⟨_, ?_, rfl⟩
  unfold quantQC
  refine iInf₂_le _ ⟨w, A, out, fun x _ => ?_⟩
  unfold QueryAlg.outputProb
  rw [hA x]
  by_cases hc : ∃ a, IsChampion n x a
  · obtain ⟨a, ha⟩ := hc
    have hfx : champion n x = true := decide_eq_true ⟨a, ha⟩
    rw [hfx]
    -- good seeds
    set W := Finset.univ.filter fun j : Fin (2 * n - 1) =>
      raceEntry n x (raceOf a.1 j) ⟨0, hn⟩ = athleteCode n a with hW
    have hWcard : 2 * W.card ≥ 2 * n - 1 := lemma_3_first_stage n hn x a ha
    set G := Finset.univ.filter fun s : Seed n => ∃ i, s i ∈ W with hG
    have hgood : ∀ s ∈ G, ∃ k0, athS n hn x s k0 = some a := by
      intro s hs
      simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      obtain ⟨i, hi⟩ := hs
      refine ⟨(a.1, i), ?_⟩
      simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      unfold athS
      rw [hi, decode_code hn a]
    have hbadc : (Finset.univ.filter fun s : Seed n => ¬ ∃ i, s i ∈ W).card =
        (2 * n - 1 - W.card) ^ 2 := by
      have : (Finset.univ.filter fun s : Seed n => ¬ ∃ i, s i ∈ W) =
          Fintype.piFinset fun _ => Wᶜ := by
        ext s; simp [Fintype.mem_piFinset]
      rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_compl]
      simp
    have htot : G.card + (Finset.univ.filter fun s : Seed n => ¬ ∃ i, s i ∈ W).card =
        (2 * n - 1) ^ 2 := by
      rw [hG, Finset.card_filter_add_card_filter_not]
      simp
    have hWle : W.card ≤ 2 * n - 1 := by
      calc W.card ≤ (Finset.univ : Finset (Fin (2 * n - 1))).card := Finset.card_le_univ _
        _ = 2 * n - 1 := by simp
    have h4 : 4 * (2 * n - 1 - W.card) ^ 2 ≤ (2 * n - 1) ^ 2 := by
      have : 2 * (2 * n - 1 - W.card) ≤ 2 * n - 1 := by omega
      calc 4 * (2 * n - 1 - W.card) ^ 2 = (2 * (2 * n - 1 - W.card)) ^ 2 := by ring
        _ ≤ (2 * n - 1) ^ 2 := Nat.pow_le_pow_left this 2
    have hNs' : Ns = ((2 * n - 1) ^ 2 : ℕ) := by rw [hNs]; simp
    have hGc : (3 : ℝ) * Ns ≤ 4 * G.card := by
      rw [hNs']
      have : 3 * (2 * n - 1) ^ 2 ≤ 4 * G.card := by omega
      exact_mod_cast this
    -- each good seed succeeds with probability ≥ 11/12
    have hseed : ∀ s ∈ G, 1 - 1 / 12 ≤
        ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true := by
      intro s hs
      refine (hP x s a ha (hgood s hs)).trans (Finset.sum_le_sum fun st _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (hpivnn s x st)
      split_ifs with h2
      · obtain ⟨P, l⟩ := st
        change l = some a at h2
        subst h2
        simp only [Vd]
        rw [Fintype.sum_bool]
        simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false, if_true,
          zero_add]
        have h1 := hversum a x
        rw [Fintype.sum_bool, hV1 x a ha] at h1
        linarith
      · exact hVnn x st true
    show (1 : ℝ) - 1 / 3 ≤
      ∑ s : Seed n, 1 / Ns * ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true
    calc (1 : ℝ) - 1 / 3 ≤ 1 / Ns * (G.card * (1 - 1 / 12)) := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hNpos]
          nlinarith
      _ = ∑ s ∈ G, 1 / Ns * (1 - 1 / 12) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ s ∈ G, 1 / Ns * ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true :=
          Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hseed s hs) (by positivity)
      _ ≤ ∑ s, 1 / Ns * ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun s _ _ =>
            mul_nonneg (by positivity) (Finset.sum_nonneg fun st _ =>
              mul_nonneg (hpivnn s x st) (hVnn x st true))
  · have hfx : champion n x = false := decide_eq_false hc
    rw [hfx]
    push Not at hc
    -- every seed accepts with probability ≤ (3/4)^4
    have hacc : ∀ s, ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true ≤ (3 / 4) ^ 4 := by
      intro s
      calc ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true
          ≤ ∑ st, iterD μ0 (κ s x) (Kp n) st * (3 / 4) ^ 4 := by
            refine Finset.sum_le_sum fun st _ => mul_le_mul_of_nonneg_left ?_ (hpivnn s x st)
            obtain ⟨P, _ | p⟩ := st
            · show (if true = false then (1 : ℝ) else 0) ≤ _
              norm_num
            · simp only [Vd]
              rw [Fintype.sum_bool]
              simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false, if_true,
                zero_add]
              exact hV2 x p (hc p)
        _ = (3 / 4) ^ 4 := by rw [← Finset.sum_mul, hpivsum s x, one_mul]
    have hsum := (Achievable.mix (fun _ : Seed n => 1 / Ns) (fun _ => by positivity) hπ1
      hfull).sum_one x
    rw [Fintype.sum_bool] at hsum
    have htrue : ∑ s, 1 / Ns * ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true ≤ (3 / 4) ^ 4 := by
      calc ∑ s, 1 / Ns * ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st true
          ≤ ∑ s : Seed n, 1 / Ns * (3 / 4) ^ 4 :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hacc s) (by positivity)
        _ = (3 / 4) ^ 4 := by rw [← Finset.sum_mul, hπ1, one_mul]
    have : (2 : ℝ) / 3 ≤ 1 - (3 / 4) ^ 4 := by norm_num
    show ∑ s, 1 / Ns * ∑ st, iterD μ0 (κ s x) (Kp n) st * Vd x st false ≥ 1 - 1 / 3
    linarith

end L5

end File_Main

section File_Bound

open RvsCert QAlgorithms RvsCertL3 QComp

namespace L5

variable (n : ℕ)

theorem T_bound (hn : 0 < n) :
    ((0 + Kp n * ((Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) + dP n (Kp n) +
        dP n (Kp n)) + (0 + 4 * ((Nat.sqrt (Fintype.card (CI n)) + 1) * (2 * dc n) + dc n)) : ℕ)
        : ℝ) ≤ 425264 * Real.sqrt n * (Real.logb 2 n + 1) ^ 3 := by
  set L := Nat.log 2 n + 1 with hL
  set S := Nat.sqrt n + 1 with hS
  have hL1 : 1 ≤ L := by omega
  have hS1 : 1 ≤ S := by omega
  have hY : wY n = L := rfl
  have hX : wX n ≤ 3 * L := by
    have : wX n ≤ 2 * wY n + 1 := by
      apply Nat.clog_le_of_le_pow
      have h1 : n + 1 ≤ 2 ^ wY n := by
        unfold wY; exact Nat.lt_pow_succ_log_self (by norm_num) n
      have : 2 ^ (2 * wY n + 1) = 2 * (2 ^ wY n) ^ 2 := by ring
      rw [this]
      nlinarith
    omega
  have hLL : L ≤ L * L := Nat.le_mul_self L
  have hcc : cc n ≤ 10 * L := by unfold cc; omega
  have hK : Kp n ≤ 42 * L := by unfold Kp; omega
  have hdP : dP n (Kp n) ≤ 843 * (L * L) := by
    unfold dP
    have : Kp n * (2 * cc n) ≤ 42 * L * (2 * (10 * L)) := Nat.mul_le_mul hK (by omega)
    have e : 42 * L * (2 * (10 * L)) = 840 * (L * L) := by ring
    omega
  have hsq1 : Nat.sqrt (Fintype.card (Slot n)) + 1 ≤ 2 * S := by
    have hc : Fintype.card (Slot n) = 4 * n := by simp; ring
    rw [hc]
    have : Nat.sqrt (4 * n) < 2 * S := by
      rw [Nat.sqrt_lt']
      have := Nat.lt_succ_sqrt' n
      rw [Nat.succ_eq_add_one] at this
      nlinarith
    omega
  have hfuel : fuel n ≤ L + 1 := by
    unfold fuel
    have : Nat.log 2 (2 * n - 1) ≤ Nat.log 2 (n * 2) := Nat.log_mono_right (by omega)
    rw [Nat.log_mul_base (by norm_num) (by omega)] at this
    omega
  have hdc : dc n ≤ 7 * (L * L) := by
    unfold dc
    rw [hY]
    have : (fuel n + 2) * L ≤ (L + 3) * L := Nat.mul_le_mul_right _ (by omega)
    have e : (L + 3) * L = L * L + 3 * L := by ring
    omega
  have hsq2 : Nat.sqrt (Fintype.card (CI n)) + 1 ≤ 3 * S := by
    have hc : Fintype.card (CI n) ≤ 5 * n := by simp; omega
    have : Nat.sqrt (Fintype.card (CI n)) < 3 * S := by
      rw [Nat.sqrt_lt']
      have := Nat.lt_succ_sqrt' n
      rw [Nat.succ_eq_add_one] at this
      nlinarith
    omega
  -- the pivot loop
  have hTr : (Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) + dP n (Kp n) +
      dP n (Kp n) ≤ 6 * S * (843 * (L * L)) := by
    have h1 : (Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) ≤
        2 * S * (2 * (843 * (L * L))) := Nat.mul_le_mul hsq1 (by omega)
    have h2 : 843 * (L * L) ≤ S * (843 * (L * L)) := Nat.le_mul_of_pos_left _ (by omega)
    have e : 2 * S * (2 * (843 * (L * L))) = 4 * (S * (843 * (L * L))) := by ring
    have e2 : 6 * S * (843 * (L * L)) = 6 * (S * (843 * (L * L))) := by ring
    omega
  have hpiv : Kp n * ((Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) +
      dP n (Kp n) + dP n (Kp n)) ≤ 212436 * (S * (L * L * L)) := by
    have := Nat.mul_le_mul hK hTr
    have e : 42 * L * (6 * S * (843 * (L * L))) = 212436 * (S * (L * L * L)) := by ring
    omega
  -- the verification
  have hver : 4 * ((Nat.sqrt (Fintype.card (CI n)) + 1) * (2 * dc n) + dc n) ≤
      196 * (S * (L * L * L)) := by
    have h1 : (Nat.sqrt (Fintype.card (CI n)) + 1) * (2 * dc n) ≤
        3 * S * (2 * (7 * (L * L))) := Nat.mul_le_mul hsq2 (by omega)
    have h2 : 7 * (L * L) ≤ S * (7 * (L * L)) := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : S * (L * L) ≤ S * (L * L * L) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    have e : 3 * S * (2 * (7 * (L * L))) = 42 * (S * (L * L)) := by ring
    have e2 : S * (7 * (L * L)) = 7 * (S * (L * L)) := by ring
    omega
  have htot : 0 + Kp n * ((Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) +
      dP n (Kp n) + dP n (Kp n)) + (0 + 4 * ((Nat.sqrt (Fintype.card (CI n)) + 1) *
      (2 * dc n) + dc n)) ≤ 212632 * (S * (L * L * L)) := by omega
  -- to the reals
  have hR : ((0 + Kp n * ((Nat.sqrt (Fintype.card (Slot n)) + 1) * (2 * dP n (Kp n)) +
      dP n (Kp n) + dP n (Kp n)) + (0 + 4 * ((Nat.sqrt (Fintype.card (CI n)) + 1) *
      (2 * dc n) + dc n)) : ℕ) : ℝ) ≤ 212632 * ((S : ℝ) * ((L : ℝ) * L * L)) := by
    exact_mod_cast htot
  have hSr : (S : ℝ) ≤ 2 * Real.sqrt n := by
    have h1 : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
    have h2 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    simp only [hS]; push_cast; linarith
  have hLr : (L : ℝ) ≤ Real.logb 2 n + 1 := by
    have := Real.natLog_le_logb n 2
    simp only [hL]; push_cast
    push_cast at this
    linarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hL3 : (L : ℝ) * L * L ≤ (Real.logb 2 n + 1) ^ 3 := by
    have := pow_le_pow_left₀ hL0 hLr 3
    calc (L : ℝ) * L * L = (L : ℝ) ^ 3 := by ring
      _ ≤ _ := this
  calc _ ≤ 212632 * ((S : ℝ) * ((L : ℝ) * L * L)) := hR
    _ ≤ 212632 * ((2 * Real.sqrt n) * (Real.logb 2 n + 1) ^ 3) := by
        gcongr
    _ = 425264 * Real.sqrt n * (Real.logb 2 n + 1) ^ 3 := by ring

end L5

open L5 in
theorem solution_L5_inner :
    ∃ (A : ℝ) (k : ℕ), ∀ n : ℕ, 0 < n → ∃ T : ℕ, quantQC (champion n) ≤ T ∧
      (T : ℝ) ≤ A * Real.sqrt n * (Real.logb 2 n + 1) ^ k := by
  refine ⟨425264, 3, fun n hn => ?_⟩
  obtain ⟨T, hT, hTeq⟩ := lemma5_main n hn
  exact ⟨T, hT, hTeq ▸ T_bound n hn⟩

end File_Bound

theorem solution :
    ∃ (A : ℝ) (k : ℕ), ∀ n : ℕ, 0 < n → ∃ T : ℕ, RvsCert.quantQC (RvsCert.champion n) ≤ T ∧
      (T : ℝ) ≤ A * Real.sqrt n * (Real.logb 2 n + 1) ^ k :=
  solution_L5_inner

