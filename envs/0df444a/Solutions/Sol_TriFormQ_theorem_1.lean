-- Prove2me | solution 1 for TriFormQ.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:40:14.238832+00:00
-- url     : https://prove2.me/submissions/8fee8442-3f71-4121-9e48-28d69a4e62e2

import Definitions.Def_TriFormQ_TriForm
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_TriForm_eval
import Definitions.Def_TriFormQ_AR
import Definitions.Def_TriFormQ_sliceU
import Definitions.Def_TriFormQ_fiber
import Definitions.Def_TriFormQ_lam

-- ===== Definitions/Def_TriFormQ_CAlg.lean
section

namespace TriFormQ

/-- A classical randomized query algorithm with queries in `Q`, answers in `R` and outputs in
`α`: it halts with an output, flips a biased coin with natural weights `w` on `Fin k` (positive
total weight) and continues with `next j`, or asks a query `q` and continues with the answer. -/
inductive CAlg (Q R α : Type) : Type where
  | ret (a : α)
  | coin (k : ℕ) (w : Fin k → ℕ) (hw : 0 < ∑ j, w j) (next : Fin k → CAlg Q R α)
  | query (q : Q) (next : R → CAlg Q R α)

namespace CAlg

variable {Q R α : Type}

/-- Expected value of `g` on the output when queries are answered by `ans`. -/
noncomputable def expect (ans : Q → R) : CAlg Q R α → (α → ℝ) → ℝ
  | ret a, g => g a
  | coin _ w _ next, g => ∑ j, ((w j : ℝ) / ∑ i, (w i : ℝ)) * expect ans (next j) g
  | query q next, g => expect ans (next (ans q)) g

/-- Worst-case number of queries over the runs of positive probability when queries are
answered by `ans`. -/
noncomputable def cost (ans : Q → R) : CAlg Q R α → ℕ
  | ret _ => 0
  | coin _ w _ next => (Finset.univ.filter fun j => 0 < w j).sup fun j => cost ans (next j)
  | query q next => cost ans (next (ans q)) + 1

end CAlg

/-- Contraction queries to a trilinear form on `𝔽ⁿ`: fix two of the three arguments. -/
inductive CQ (F : Type) (n : ℕ) : Type where
  | xy (x y : Vec F n)
  | xz (x z : Vec F n)
  | yz (y z : Vec F n)

/-- The answer to a contraction query: the coefficient vector of the remaining linear form. -/
def CQ.ans {F : Type} [Field F] {n : ℕ} (θ : TriForm F n) : CQ F n → Vec F n
  | .xy x y => fun k => ∑ i, ∑ j, θ i j k * x i * y j
  | .xz x z => fun j => ∑ i, ∑ k, θ i j k * x i * z k
  | .yz y z => fun i => ∑ j, ∑ k, θ i j k * y j * z k

end TriFormQ

end


-- ===== Definitions/Def_TriFormQ_CAlgLib.lean
section

/-! Combinators for classical randomized query algorithms (`CAlg`) and their basic laws. -/

namespace TriFormQ

namespace CAlg

variable {Q R Q' R' α β γ : Type}

/-! ### Basic laws of `expect` and `cost` -/

/-- Every output reachable with positive probability satisfies `P`. -/
def AllOut (ans : Q → R) : CAlg Q R α → (α → Prop) → Prop
  | ret a, P => P a
  | coin _ w _ next, P => ∀ j, 0 < w j → AllOut ans (next j) P
  | query q next, P => AllOut ans (next (ans q)) P

lemma coin_weight_sum {k : ℕ} (w : Fin k → ℕ) (hw : 0 < ∑ j, w j) :
    ∑ j, ((w j : ℝ) / ∑ i, (w i : ℝ)) = 1 := by
  rw [← Finset.sum_div, div_self]
  exact_mod_cast hw.ne'

lemma coin_weight_nonneg {k : ℕ} (w : Fin k → ℕ) (j : Fin k) :
    0 ≤ (w j : ℝ) / ∑ i, (w i : ℝ) := by positivity

theorem expect_mono_allOut (ans : Q → R) (A : CAlg Q R α) {g g' : α → ℝ}
    (h : A.AllOut ans (fun a => g a ≤ g' a)) : A.expect ans g ≤ A.expect ans g' := by
  induction A with
  | ret a => exact h
  | coin k w hw next ih =>
    simp only [expect]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : 0 < w j
    · exact mul_le_mul_of_nonneg_left (ih j (h j hj)) (coin_weight_nonneg w j)
    · have : w j = 0 := by omega
      simp [this]
  | query q next ih => exact ih _ h

theorem allOut_of_forall (ans : Q → R) (A : CAlg Q R α) {P : α → Prop} (h : ∀ a, P a) :
    A.AllOut ans P := by
  induction A with
  | ret a => exact h a
  | coin k w hw next ih => exact fun j _ => ih j
  | query q next ih => exact ih _

theorem expect_mono (ans : Q → R) (A : CAlg Q R α) {g g' : α → ℝ} (h : ∀ a, g a ≤ g' a) :
    A.expect ans g ≤ A.expect ans g' :=
  expect_mono_allOut ans A (allOut_of_forall ans A h)

theorem expect_const (ans : Q → R) (A : CAlg Q R α) (c : ℝ) : A.expect ans (fun _ => c) = c := by
  induction A with
  | ret a => rfl
  | coin k w hw next ih =>
    simp only [expect, ih, ← Finset.sum_mul, coin_weight_sum w hw, one_mul]
  | query q next ih => exact ih _

theorem expect_add (ans : Q → R) (A : CAlg Q R α) (g g' : α → ℝ) :
    A.expect ans (fun a => g a + g' a) = A.expect ans g + A.expect ans g' := by
  induction A with
  | ret a => rfl
  | coin k w hw next ih =>
    simp only [expect, ih, mul_add, Finset.sum_add_distrib]
  | query q next ih => exact ih _

theorem expect_smul (ans : Q → R) (A : CAlg Q R α) (c : ℝ) (g : α → ℝ) :
    A.expect ans (fun a => c * g a) = c * A.expect ans g := by
  induction A with
  | ret a => rfl
  | coin k w hw next ih =>
    simp only [expect, ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  | query q next ih => exact ih _

theorem expect_sub (ans : Q → R) (A : CAlg Q R α) (g g' : α → ℝ) :
    A.expect ans (fun a => g a - g' a) = A.expect ans g - A.expect ans g' := by
  have h := expect_add ans A g (fun a => -g' a)
  have h2 := expect_smul ans A (-1) g'
  simp only [neg_one_mul] at h2
  simp only [sub_eq_add_neg, h, h2]

theorem expect_nonneg (ans : Q → R) (A : CAlg Q R α) {g : α → ℝ} (h : ∀ a, 0 ≤ g a) :
    0 ≤ A.expect ans g := by
  have := expect_mono ans A (g := fun _ => 0) h
  rwa [expect_const] at this

theorem expect_congr_allOut (ans : Q → R) (A : CAlg Q R α) {g g' : α → ℝ}
    (h : A.AllOut ans (fun a => g a = g' a)) : A.expect ans g = A.expect ans g' := by
  induction A with
  | ret a => exact h
  | coin k w hw next ih =>
    simp only [expect]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : 0 < w j
    · rw [ih j (h j hj)]
    · have : w j = 0 := by omega
      simp [this]
  | query q next ih => exact ih _ h

theorem allOut_mono (ans : Q → R) (A : CAlg Q R α) {P P' : α → Prop} (h : ∀ a, P a → P' a)
    (hA : A.AllOut ans P) : A.AllOut ans P' := by
  induction A with
  | ret a => exact h a hA
  | coin k w hw next ih => exact fun j hj => ih j (hA j hj)
  | query q next ih => exact ih _ hA

theorem allOut_and (ans : Q → R) (A : CAlg Q R α) {P P' : α → Prop}
    (h : A.AllOut ans P) (h' : A.AllOut ans P') : A.AllOut ans (fun a => P a ∧ P' a) := by
  induction A with
  | ret a => exact ⟨h, h'⟩
  | coin k w hw next ih => exact fun j hj => ih j (h j hj) (h' j hj)
  | query q next ih => exact ih _ h h'

/-! ### Probabilities -/

open Classical in
/-- Probability that the output satisfies `P`. -/
noncomputable def prob (ans : Q → R) (A : CAlg Q R α) (P : α → Prop) : ℝ :=
  A.expect ans (fun a => if P a then 1 else 0)

open Classical in
theorem prob_nonneg (ans : Q → R) (A : CAlg Q R α) (P : α → Prop) : 0 ≤ A.prob ans P :=
  expect_nonneg ans A (fun a => by split_ifs <;> norm_num)

open Classical in
theorem prob_le_one (ans : Q → R) (A : CAlg Q R α) (P : α → Prop) : A.prob ans P ≤ 1 := by
  have := expect_mono ans A (g := fun a => if P a then (1 : ℝ) else 0) (g' := fun _ => 1)
    (fun a => by split_ifs <;> norm_num)
  rwa [expect_const] at this

open Classical in
theorem prob_mono (ans : Q → R) (A : CAlg Q R α) {P P' : α → Prop} (h : ∀ a, P a → P' a) :
    A.prob ans P ≤ A.prob ans P' := by
  unfold prob
  refine expect_mono ans A fun a => ?_
  by_cases hp : P a
  · simp [hp, h a hp]
  · simp only [hp, if_false]; split_ifs <;> norm_num

open Classical in
theorem prob_mono_allOut (ans : Q → R) (A : CAlg Q R α) {P P' : α → Prop}
    (h : A.AllOut ans (fun a => P a → P' a)) : A.prob ans P ≤ A.prob ans P' := by
  unfold prob
  refine expect_mono_allOut ans A (allOut_mono ans A (fun a ha => ?_) h)
  by_cases hp : P a
  · simp [hp, ha hp]
  · simp only [hp, if_false]; split_ifs <;> norm_num

open Classical in
theorem prob_compl (ans : Q → R) (A : CAlg Q R α) (P : α → Prop) :
    A.prob ans P = 1 - A.prob ans (fun a => ¬ P a) := by
  have h := expect_add ans A (fun a => if P a then (1 : ℝ) else 0)
    (fun a => if ¬ P a then (1 : ℝ) else 0)
  have h1 : (fun a => (if P a then (1 : ℝ) else 0) + if ¬ P a then (1 : ℝ) else 0) =
      fun _ => 1 := by
    funext a; by_cases hp : P a <;> simp [hp]
  rw [h1, expect_const] at h
  unfold prob
  have e : (A.expect ans fun a => if ¬P a then (1 : ℝ) else 0) =
      A.expect ans (fun a => @ite ℝ (¬ P a) (Classical.propDecidable _) 1 0) := by
    congr 1; funext a; congr 1
  linarith

open Classical in
theorem prob_or_le (ans : Q → R) (A : CAlg Q R α) (P P' : α → Prop) :
    A.prob ans (fun a => P a ∨ P' a) ≤ A.prob ans P + A.prob ans P' := by
  unfold prob
  rw [← expect_add]
  refine expect_mono ans A fun a => ?_
  by_cases h1 : P a <;> by_cases h2 : P' a <;> simp [h1, h2]

open Classical in
theorem prob_of_allOut (ans : Q → R) (A : CAlg Q R α) {P : α → Prop} (h : A.AllOut ans P) :
    A.prob ans P = 1 := by
  unfold prob
  rw [expect_congr_allOut ans A (g' := fun _ => 1) (allOut_mono ans A (fun a ha => by simp [ha]) h)]
  exact expect_const ans A 1

/-- Lower bound from a failure bound. -/
theorem prob_ge_of_fail (ans : Q → R) (A : CAlg Q R α) {P : α → Prop} {ε : ℝ}
    (h : A.prob ans (fun a => ¬ P a) ≤ ε) : 1 - ε ≤ A.prob ans P := by
  rw [prob_compl]; linarith

/-! ### Bind -/

/-- Sequential composition. -/
def bind : CAlg Q R α → (α → CAlg Q R β) → CAlg Q R β
  | ret a, k => k a
  | coin m w hw next, k => coin m w hw (fun j => bind (next j) k)
  | query q next, k => query q (fun r => bind (next r) k)

theorem expect_bind (ans : Q → R) (A : CAlg Q R α) (k : α → CAlg Q R β) (g : β → ℝ) :
    (A.bind k).expect ans g = A.expect ans (fun a => (k a).expect ans g) := by
  induction A with
  | ret a => rfl
  | coin m w hw next ih => simp only [bind, expect, ih]
  | query q next ih => simp only [bind, expect, ih]

theorem prob_bind (ans : Q → R) (A : CAlg Q R α) (k : α → CAlg Q R β) (P : β → Prop) :
    (A.bind k).prob ans P = A.expect ans (fun a => (k a).prob ans P) :=
  expect_bind ans A k _

theorem allOut_bind (ans : Q → R) (A : CAlg Q R α) (k : α → CAlg Q R β) {P : α → Prop}
    {P' : β → Prop} (hA : A.AllOut ans P) (hk : ∀ a, P a → (k a).AllOut ans P') :
    (A.bind k).AllOut ans P' := by
  induction A with
  | ret a => exact hk a hA
  | coin m w hw next ih => exact fun j hj => ih j (hA j hj)
  | query q next ih => exact ih _ hA

theorem cost_bind_le (ans : Q → R) (A : CAlg Q R α) (k : α → CAlg Q R β) (c : ℕ)
    (hk : A.AllOut ans (fun a => (k a).cost ans ≤ c)) :
    (A.bind k).cost ans ≤ A.cost ans + c := by
  induction A with
  | ret a => simp only [bind, cost, zero_add]; exact hk
  | coin m w hw next ih =>
    simp only [bind, cost]
    refine Finset.sup_le fun j hj => ?_
    have hj' : 0 < w j := (Finset.mem_filter.1 hj).2
    refine (ih j (hk j hj')).trans ?_
    have : (next j).cost ans ≤ (Finset.univ.filter fun j => 0 < w j).sup
        fun j => (next j).cost ans := Finset.le_sup (f := fun j => (next j).cost ans) hj
    omega
  | query q next ih =>
    simp only [bind, cost]
    have := ih _ hk
    omega

/-- Composition lemma: success of the first stage and conditional success of the second. -/
theorem prob_bind_ge (ans : Q → R) (A : CAlg Q R α) (k : α → CAlg Q R β) (P : α → Prop)
    (P' : β → Prop) (ε₁ ε₂ : ℝ) (h₁ : 1 - ε₁ ≤ A.prob ans P)
    (h₂ : ∀ a, P a → 1 - ε₂ ≤ (k a).prob ans P') (hε₂ : 0 ≤ ε₂) (hε₂' : ε₂ ≤ 1) :
    1 - ε₁ - ε₂ ≤ (A.bind k).prob ans P' := by
  classical
  rw [prob_bind]
  have hmono : A.expect ans (fun a => (1 - ε₂) * (if P a then 1 else 0)) ≤
      A.expect ans (fun a => (k a).prob ans P') := by
    refine expect_mono ans A fun a => ?_
    by_cases hp : P a
    · simpa [hp] using h₂ a hp
    · simp only [hp, if_false, mul_zero]; exact prob_nonneg ans _ _
  rw [expect_smul] at hmono
  have hE : A.expect ans (fun a => if P a then 1 else 0) = A.prob ans P := by
    unfold prob; congr
  rw [hE] at hmono
  have hp1 := prob_le_one ans A P
  have hε1 : 0 ≤ ε₁ := by linarith
  have : (1 - ε₂) * (1 - ε₁) ≤ (1 - ε₂) * A.prob ans P :=
    mul_le_mul_of_nonneg_left h₁ (by linarith)
  nlinarith [mul_nonneg hε1 hε₂]

/-- Output map. -/
def map (f : α → β) (A : CAlg Q R α) : CAlg Q R β := A.bind (fun a => ret (f a))

theorem expect_map (ans : Q → R) (f : α → β) (A : CAlg Q R α) (g : β → ℝ) :
    (A.map f).expect ans g = A.expect ans (g ∘ f) := by
  simp [map, expect_bind, expect, Function.comp_def]

theorem prob_map (ans : Q → R) (f : α → β) (A : CAlg Q R α) (P : β → Prop) :
    (A.map f).prob ans P = A.prob ans (fun a => P (f a)) := by
  unfold prob; rw [expect_map]; rfl

theorem cost_map (ans : Q → R) (f : α → β) (A : CAlg Q R α) : (A.map f).cost ans = A.cost ans := by
  induction A with
  | ret a => rfl
  | coin m w hw next ih => simp only [map, bind, cost] at ih ⊢; simp only [ih]
  | query q next ih => simp only [map, bind, cost] at ih ⊢; simp only [ih]

/-! ### Sampling -/

/-- Sample `b` from a finite type with natural weights `wt` (positive total). -/
noncomputable def wsample {β : Type} [Fintype β] (wt : β → ℕ) (h : 0 < ∑ b, wt b)
    (k : β → CAlg Q R α) : CAlg Q R α :=
  coin (Fintype.card β) (fun j => wt ((Fintype.equivFin β).symm j))
    (by rwa [Equiv.sum_comp (Fintype.equivFin β).symm (fun b => wt b)])
    (fun j => k ((Fintype.equivFin β).symm j))

theorem expect_wsample {β : Type} [Fintype β] (ans : Q → R) (wt : β → ℕ) (h : 0 < ∑ b, wt b)
    (k : β → CAlg Q R α) (g : α → ℝ) :
    (wsample wt h k).expect ans g =
      ∑ b, ((wt b : ℝ) / ∑ b', (wt b' : ℝ)) * (k b).expect ans g := by
  simp only [wsample, expect]
  rw [Equiv.sum_comp (Fintype.equivFin β).symm
    (fun b => ((wt b : ℝ) / ∑ i : Fin (Fintype.card β), (wt ((Fintype.equivFin β).symm i) : ℝ))
      * (k b).expect ans g)]
  rw [Equiv.sum_comp (Fintype.equivFin β).symm (fun b => (wt b : ℝ))]

theorem allOut_wsample {β : Type} [Fintype β] (ans : Q → R) (wt : β → ℕ) (h : 0 < ∑ b, wt b)
    (k : β → CAlg Q R α) {P : α → Prop} (hk : ∀ b, 0 < wt b → (k b).AllOut ans P) :
    (wsample wt h k).AllOut ans P := fun j hj => hk _ hj

theorem cost_wsample_le {β : Type} [Fintype β] (ans : Q → R) (wt : β → ℕ) (h : 0 < ∑ b, wt b)
    (k : β → CAlg Q R α) (c : ℕ) (hk : ∀ b, 0 < wt b → (k b).cost ans ≤ c) :
    (wsample wt h k).cost ans ≤ c := by
  simp only [wsample, cost]
  exact Finset.sup_le fun j hj => hk _ (Finset.mem_filter.1 hj).2

/-- Uniform sample from a nonempty finite type. -/
noncomputable def unif {β : Type} [Fintype β] [Nonempty β] (k : β → CAlg Q R α) : CAlg Q R α :=
  wsample (fun _ => 1) (by simp [Fintype.card_pos]) k

theorem expect_unif {β : Type} [Fintype β] [Nonempty β] (ans : Q → R) (k : β → CAlg Q R α)
    (g : α → ℝ) : (unif k).expect ans g = (∑ b, (k b).expect ans g) / Fintype.card β := by
  rw [unif, expect_wsample]
  simp only [Nat.cast_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => by ring

theorem allOut_unif {β : Type} [Fintype β] [Nonempty β] (ans : Q → R) (k : β → CAlg Q R α)
    {P : α → Prop} (hk : ∀ b, (k b).AllOut ans P) : (unif k).AllOut ans P :=
  allOut_wsample ans _ _ k fun b _ => hk b

theorem cost_unif_le {β : Type} [Fintype β] [Nonempty β] (ans : Q → R) (k : β → CAlg Q R α)
    (c : ℕ) (hk : ∀ b, (k b).cost ans ≤ c) : (unif k).cost ans ≤ c :=
  cost_wsample_le ans _ _ k c fun b _ => hk b

/-! ### Batches of queries -/

/-- Ask the queries `qs 0, …, qs (m-1)` and continue with all answers. -/
def queryN : (m : ℕ) → (Fin m → Q) → ((Fin m → R) → CAlg Q R α) → CAlg Q R α
  | 0, _, k => k Fin.elim0
  | m + 1, qs, k => query (qs 0) (fun r => queryN m (fun i => qs i.succ) (fun rs => k (Fin.cons r rs)))

theorem expect_queryN (ans : Q → R) :
    ∀ (m : ℕ) (qs : Fin m → Q) (k : (Fin m → R) → CAlg Q R α) (g : α → ℝ),
      (queryN m qs k).expect ans g = (k (fun i => ans (qs i))).expect ans g
  | 0, qs, k, g => by
    simp only [queryN]; congr; funext i; exact i.elim0
  | m + 1, qs, k, g => by
    simp only [queryN, expect]
    rw [expect_queryN ans m]
    congr 2; funext i
    refine Fin.cases rfl (fun j => rfl) i

theorem allOut_queryN (ans : Q → R) :
    ∀ (m : ℕ) (qs : Fin m → Q) (k : (Fin m → R) → CAlg Q R α) {P : α → Prop},
      (k (fun i => ans (qs i))).AllOut ans P → (queryN m qs k).AllOut ans P
  | 0, qs, k, P, h => by
    simp only [queryN]
    have : (Fin.elim0 : Fin 0 → R) = (fun i => ans (qs i)) := funext fun i => i.elim0
    rw [this]; exact h
  | m + 1, qs, k, P, h => by
    simp only [queryN, AllOut]
    refine allOut_queryN ans m _ _ ?_
    have : (Fin.cons (ans (qs 0)) (fun i : Fin m => ans (qs i.succ)) : Fin (m + 1) → R) =
        fun i => ans (qs i) := by
      funext i; refine Fin.cases rfl (fun j => rfl) i
    rw [this]; exact h

theorem cost_queryN (ans : Q → R) :
    ∀ (m : ℕ) (qs : Fin m → Q) (k : (Fin m → R) → CAlg Q R α),
      (queryN m qs k).cost ans = (k (fun i => ans (qs i))).cost ans + m
  | 0, qs, k => by
    simp only [queryN, add_zero]
    have : (Fin.elim0 : Fin 0 → R) = (fun i => ans (qs i)) := funext fun i => i.elim0
    rw [this]
  | m + 1, qs, k => by
    simp only [queryN, cost]
    rw [cost_queryN ans m]
    have : (Fin.cons (ans (qs 0)) (fun i : Fin m => ans (qs i.succ)) : Fin (m + 1) → R) =
        fun i => ans (qs i) := by
      funext i; refine Fin.cases rfl (fun j => rfl) i
    rw [this]; omega


/-- Ask the queries `qs x` for all `x` of a finite type and continue with all answers. -/
noncomputable def queryF {ι : Type} [Fintype ι] (qs : ι → Q) (k : (ι → R) → CAlg Q R α) :
    CAlg Q R α :=
  queryN (Fintype.card ι) (fun i => qs ((Fintype.equivFin ι).symm i))
    fun rs => k (fun x => rs (Fintype.equivFin ι x))

theorem expect_queryF {ι : Type} [Fintype ι] (ans : Q → R) (qs : ι → Q)
    (k : (ι → R) → CAlg Q R α) (g : α → ℝ) :
    (queryF qs k).expect ans g = (k (fun x => ans (qs x))).expect ans g := by
  simp [queryF, expect_queryN]

theorem cost_queryF {ι : Type} [Fintype ι] (ans : Q → R) (qs : ι → Q)
    (k : (ι → R) → CAlg Q R α) :
    (queryF qs k).cost ans = (k (fun x => ans (qs x))).cost ans + Fintype.card ι := by
  simp [queryF, cost_queryN]

theorem allOut_queryF {ι : Type} [Fintype ι] (ans : Q → R) (qs : ι → Q)
    (k : (ι → R) → CAlg Q R α) {P : α → Prop} (h : (k (fun x => ans (qs x))).AllOut ans P) :
    (queryF qs k).AllOut ans P := by
  unfold queryF
  refine allOut_queryN ans _ _ _ ?_
  simpa using h

theorem prob_queryF {ι : Type} [Fintype ι] (ans : Q → R) (qs : ι → Q)
    (k : (ι → R) → CAlg Q R α) (P : α → Prop) :
    (queryF qs k).prob ans P = (k (fun x => ans (qs x))).prob ans P :=
  expect_queryF ans qs k _

/-! ### Simulation of one query interface by another -/

/-- Replace each `Q'`-query by the `Q`-query `φ q'` and post-process the answer with `ψ q'`. -/
def mapQ (φ : Q' → Q) (ψ : Q' → R → R') : CAlg Q' R' α → CAlg Q R α
  | ret a => ret a
  | coin m w hw next => coin m w hw (fun j => mapQ φ ψ (next j))
  | query q next => query (φ q) (fun r => mapQ φ ψ (next (ψ q r)))

theorem expect_mapQ (ans : Q → R) (φ : Q' → Q) (ψ : Q' → R → R') (A : CAlg Q' R' α)
    (g : α → ℝ) : (mapQ φ ψ A).expect ans g = A.expect (fun q => ψ q (ans (φ q))) g := by
  induction A with
  | ret a => rfl
  | coin m w hw next ih => simp only [mapQ, expect, ih]
  | query q next ih => simp only [mapQ, expect, ih]

theorem cost_mapQ (ans : Q → R) (φ : Q' → Q) (ψ : Q' → R → R') (A : CAlg Q' R' α) :
    (mapQ φ ψ A).cost ans = A.cost (fun q => ψ q (ans (φ q))) := by
  induction A with
  | ret a => rfl
  | coin m w hw next ih => simp only [mapQ, cost, ih]
  | query q next ih => simp only [mapQ, cost, ih]

theorem allOut_mapQ (ans : Q → R) (φ : Q' → Q) (ψ : Q' → R → R') (A : CAlg Q' R' α)
    {P : α → Prop} (h : A.AllOut (fun q => ψ q (ans (φ q))) P) :
    (mapQ φ ψ A).AllOut ans P := by
  induction A with
  | ret a => exact h
  | coin m w hw next ih => exact fun j hj => ih j (h j hj)
  | query q next ih => exact ih _ h

theorem prob_mapQ (ans : Q → R) (φ : Q' → Q) (ψ : Q' → R → R') (A : CAlg Q' R' α)
    (P : α → Prop) : (mapQ φ ψ A).prob ans P = A.prob (fun q => ψ q (ans (φ q))) P :=
  expect_mapQ ans φ ψ A _

end CAlg

end TriFormQ

end


-- ===== Solutions/W_BV.lean
section

open QAlgorithms Matrix

set_option linter.unusedSectionVars false

namespace TriFormQ.BVW

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

lemma exists_psi : ∃ ψ : AddChar F ℂ, ψ 1 ≠ 1 :=
  (AddChar.exists_apply_ne_zero (a := (1 : F))).2 one_ne_zero

lemma psi_conj (ψ : AddChar F ℂ) (t : F) : (starRingEnd ℂ) (ψ t) = ψ (-t) := by
  have h := AddChar.starComp_apply (R := F)
    (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)) (φ := ψ) t
  rw [h, AddChar.inv_apply', AddChar.map_neg_eq_inv]

/-- The character `z ↦ ψ (c ⬝ᵥ z)` sums to `q^n` or `0`. -/
lemma sum_psi_dot {n : ℕ} (ψ : AddChar F ℂ) (hψ : ψ 1 ≠ 1) (c : Fin n → F) :
    ∑ z : Fin n → F, ψ (c ⬝ᵥ z) = if c = 0 then (Fintype.card (Fin n → F) : ℂ) else 0 := by
  split_ifs with hc
  · subst hc; simp
  · let f : (Fin n → F) →+ F :=
      { toFun := fun z => c ⬝ᵥ z, map_zero' := dotProduct_zero c,
        map_add' := fun x y => dotProduct_add c x y }
    let χ : AddChar (Fin n → F) ℂ := ψ.compAddMonoidHom f
    have hχ : χ ≠ 1 := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h; push Not at h; exact hc (funext h)
      intro h1
      have : χ (Pi.single i (c i)⁻¹) = 1 := by rw [h1]; rfl
      simp only [χ, AddChar.compAddMonoidHom_apply, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        dotProduct_single, mul_inv_cancel₀ hi] at this
      exact hψ this
    have := AddChar.sum_eq_zero_of_ne_one hχ
    simpa [χ, f] using this

/-- Sum over `ι` of a product of two extensions by zero along an injection. -/
lemma sum_extend_mul {ι Z : Type} [Fintype ι] [Fintype Z] [DecidableEq ι] (emb : Z → ι)
    (hemb : Function.Injective emb) (f g : Z → ℂ) :
    ∑ i, (starRingEnd ℂ) (Function.extend emb f 0 i) * Function.extend emb g 0 i =
      ∑ z, (starRingEnd ℂ) (f z) * g z := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb))]
  · rw [Finset.sum_image (fun x _ y _ h => hemb h)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hemb.extend_apply, hemb.extend_apply]
  · intro i _ hi
    have : ¬ ∃ z, emb z = i := by
      rintro ⟨z, rfl⟩; exact hi (Finset.mem_image_of_mem _ (Finset.mem_univ z))
    rw [Function.extend_apply' _ _ _ this]; simp

/-- Action of the standard oracle tensored with the identity on the workspace. -/
lemma act_xor_apply {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (g : ι → F) (s : EuclideanSpace ℂ ((ι × F) × W)) (i : ι) (b : F) (w : W) :
    act (Matrix.kronecker (xorOracle g) (1 : Matrix W W ℂ)) s ((i, b), w) =
      s ((i, b - g i), w) := by
  simp only [act, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    xorOracle, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((i, b - g i), w)]
  · simp
  · rintro ⟨⟨i', b'⟩, w'⟩ _ hne
    by_cases h1 : i = i'
    · subst h1
      by_cases h2 : b = b' + g i
      · by_cases h3 : w = w'
        · subst h3; exfalso; apply hne; simp [h2]
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp

/-- Generic one-query Bernstein–Vazirani over a finite field: if the oracle restricted to an
injectively embedded copy of `𝔽ⁿ` is the linear function `z ↦ a ⬝ᵥ z`, one query yields `a`
exactly (the final state is a basis vector decoding to `a`). -/
theorem bv_generic {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (emb : (Fin n → F) → ι)
    (hemb : Function.Injective emb) :
    ∃ (A : QueryAlg ι F (Fin 1) 1) (dec : (ι × F) × Fin 1 → (Fin n → F)),
      ∀ (g : ι → F) (a : Fin n → F), (∀ z, g (emb z) = a ⬝ᵥ z) →
        ∃ z0, A.finalState (xorOracle g) = ket z0 ∧ dec z0 = a := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_psi (F := F)
  set N : ℕ := Fintype.card (Fin n → F) * Fintype.card F with hN
  have hNpos : (0 : ℝ) < N := by
    have h1 : 0 < Fintype.card (Fin n → F) := Fintype.card_pos
    have h2 : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast Nat.mul_pos h1 h2
  set c0 : ℂ := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) with hc0
  have hc0sq : (starRingEnd ℂ) c0 * c0 = ((N : ℝ)⁻¹ : ℝ) := by
    rw [hc0, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hNpos.le]
  let ι' := (ι × F) × Fin 1
  let φ : (Fin n → F) → EuclideanSpace ℂ ι' := fun a => WithLp.toLp 2 fun p =>
    Function.extend emb (fun z => c0 * ψ (a ⬝ᵥ z - p.1.2)) 0 p.1.1
  have hφ : Orthonormal ℂ φ := by
    rw [orthonormal_iff_ite]
    intro a a'
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, φ]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_unique]
    rw [Finset.sum_comm]
    have key : ∀ b : F, ∑ i : ι, (starRingEnd ℂ) (Function.extend emb
        (fun z => c0 * ψ (a ⬝ᵥ z - b)) 0 i) * Function.extend emb
        (fun z => c0 * ψ (a' ⬝ᵥ z - b)) 0 i = ((N : ℝ)⁻¹ : ℝ) * ∑ z, ψ ((a' - a) ⬝ᵥ z) := by
      intro b
      -- note: inner is conj(first) * second; here written as second * conj(first)
      rw [sum_extend_mul emb hemb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [map_mul, psi_conj, mul_mul_mul_comm, hc0sq, ← AddChar.map_add_eq_mul]
      congr 2; simp [sub_dotProduct]
    have key' : ∀ b : F, ∑ i : ι, Function.extend emb
        (fun z => c0 * ψ (a' ⬝ᵥ z - b)) 0 i * (starRingEnd ℂ) (Function.extend emb
        (fun z => c0 * ψ (a ⬝ᵥ z - b)) 0 i) = ((N : ℝ)⁻¹ : ℝ) * ∑ z, ψ ((a' - a) ⬝ᵥ z) := by
      intro b; rw [← key b]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp_rw [key']
    rw [Finset.sum_const, Finset.card_univ, sum_psi_dot ψ hψ]
    by_cases h : a = a'
    · subst h
      simp only [sub_self, if_true]
      rw [nsmul_eq_mul]
      have : (N : ℂ) = (Fintype.card F : ℂ) * (Fintype.card (Fin n → F) : ℂ) := by
        rw [hN]; push_cast; ring
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
      rw [Complex.ofReal_inv, Complex.ofReal_natCast]
      field_simp
      rw [this]
    · have : a' - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      simp [h, this]
  -- the embedding of `𝔽ⁿ` into the basis of the register
  let τ : (Fin n → F) → ι' := fun a => ((emb a, 0), 0)
  have hτ : Function.Injective τ := fun a a' h => hemb (by simpa [τ] using congrArg (·.1.1) h)
  let v : ι' → EuclideanSpace ℂ ι' := Function.extend τ φ 0
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ ι') = Fintype.card ι' := finrank_euclideanSpace
  have hv : Orthonormal ℂ ((Set.range τ).domRestrict v) := by
    let e := Equiv.ofInjective τ hτ
    have : (Set.range τ).domRestrict v = φ ∘ e.symm := by
      funext x
      simp only [Set.domRestrict, Function.comp_apply, v]
      have hx : (x : ι') = τ (e.symm x) := (Equiv.apply_ofInjective_symm hτ x).symm
      rw [hx, hτ.extend_apply]
    rw [this]
    exact hφ.comp _ e.symm.injective
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have hbτ : ∀ a, b (τ a) = φ a := by
    intro a
    rw [hb (τ a) ⟨a, rfl⟩]
    simp only [v, hτ.extend_apply]
  let U1 : Matrix ι' ι' ℂ := b.toBasis.toMatrix (EuclideanSpace.basisFun ι' ℂ).toBasis
  have hU1 : U1 ∈ Matrix.unitaryGroup ι' ℂ :=
    b.toMatrix_orthonormalBasis_mem_unitary (EuclideanSpace.basisFun ι' ℂ)
  have hU1act : ∀ x : EuclideanSpace ℂ ι', act U1 x = b.repr x := by
    intro x
    have h := Module.Basis.toMatrix_mulVec_repr (b' := b.toBasis) (b := (EuclideanSpace.basisFun ι' ℂ).toBasis) x
    simp only [act, U1]
    have e1 : (⇑((EuclideanSpace.basisFun ι' ℂ).toBasis.repr x) : ι' → ℂ) = WithLp.ofLp x := by
      funext i; simp
    rw [e1] at h
    rw [h]
    ext i
    simp
  let A : QueryAlg ι F (Fin 1) 1 :=
    { start := φ 0
      start_unit := hφ.1 0
      U := fun k => if k = 0 then 1 else ⟨U1, hU1⟩ }
  let dec : ι' → (Fin n → F) := fun p => Function.invFun emb p.1.1
  refine ⟨A, dec, fun g a hga => ⟨τ a, ?_, ?_⟩⟩
  · have hfin : A.finalState (xorOracle g) = act (A.U 1 : Matrix _ _ ℂ)
        (act (Matrix.kronecker (xorOracle g) (1 : Matrix (Fin 1) (Fin 1) ℂ))
          (act (A.U 0 : Matrix _ _ ℂ) A.start)) := rfl
    rw [hfin]
    have hU0 : (A.U 0 : Matrix ι' ι' ℂ) = 1 := by simp [A]
    have hU1' : (A.U 1 : Matrix ι' ι' ℂ) = U1 := by simp [A]
    rw [hU0, hU1']
    have hstep : act (Matrix.kronecker (xorOracle g) (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (act 1 A.start) = φ a := by
      ext ⟨⟨i, b'⟩, w⟩
      rw [act_xor_apply]
      simp only [act, Matrix.one_mulVec, A, φ]
      by_cases hi : ∃ z, emb z = i
      · obtain ⟨z, rfl⟩ := hi
        rw [hemb.extend_apply, hemb.extend_apply, hga z]
        congr 2; simp
      · rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    rw [hstep, hU1act, ← hbτ, OrthonormalBasis.repr_self]
    rfl
  · simp only [dec, τ]
    exact Function.leftInverse_invFun hemb a

end TriFormQ.BVW

end


-- ===== Solutions/W_Compile.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.CompileW
open QAlgorithms Matrix

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

abbrev Idx (F : Type) (n : ℕ) := Vec F n × Vec F n × Vec F n

def qemb : CQ F n → (Vec F n → Idx F n)
  | .xy x y => fun z => (x, y, z)
  | .xz x z => fun y => (x, y, z)
  | .yz y z => fun x => (x, y, z)

lemma qemb_inj (q : CQ F n) : Function.Injective (qemb q) := by
  cases q <;> intro a b h <;> simp_all [qemb]

lemma oracle_qemb (θ : TriForm F n) (q : CQ F n) (z : Vec F n) :
    oracle θ (qemb q z) = CQ.ans θ q ⬝ᵥ z := by
  cases q with
  | xy x y =>
    simp only [oracle, qemb, TriForm.eval, CQ.ans, dotProduct, Finset.sum_mul]
    rw [show (∑ i, ∑ j, ∑ k, θ i j k * x i * y j * z k) =
        ∑ i, ∑ k, ∑ j, θ i j k * x i * y j * z k from
      Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    exact Finset.sum_comm
  | xz x z =>
    simp only [oracle, qemb, TriForm.eval, CQ.ans, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  | yz y z =>
    simp only [oracle, qemb, TriForm.eval, CQ.ans, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem bv_q (q : CQ F n) : ∃ (A : QueryAlg (Idx F n) F (Fin 1) 1)
    (dec : ((Idx F n) × F) × Fin 1 → Vec F n), ∀ θ : TriForm F n,
      ∃ z0, A.finalState (xorOracle (oracle θ)) = ket z0 ∧ dec z0 = CQ.ans θ q := by
  obtain ⟨A, dec, h⟩ := BVW.bv_generic (F := F) (qemb q) (qemb_inj q)
  exact ⟨A, dec, fun θ => h (oracle θ) (CQ.ans θ q) (oracle_qemb θ q)⟩

noncomputable def bvA (q : CQ F n) : QueryAlg (Idx F n) F (Fin 1) 1 := Classical.choose (bv_q q)
noncomputable def bvDec (q : CQ F n) : ((Idx F n) × F) × Fin 1 → Vec F n :=
  Classical.choose (Classical.choose_spec (bv_q q))
lemma bv_spec (q : CQ F n) (θ : TriForm F n) :
    ∃ z0, (bvA q).finalState (xorOracle (oracle θ)) = ket z0 ∧ bvDec q z0 = CQ.ans θ q :=
  Classical.choose_spec (Classical.choose_spec (bv_q q)) θ

noncomputable def coinStart (k : ℕ) (w : Fin k → ℕ) :
    EuclideanSpace ℂ ((Idx F n × F) × Fin k) :=
  WithLp.toLp 2 fun p => if p.1 = (0, 0) then
    ((Real.sqrt ((w p.2 : ℝ) / ∑ i, (w i : ℝ)) : ℝ) : ℂ) else 0

lemma coinStart_norm_sq (k : ℕ) (w : Fin k → ℕ) (hw : 0 < ∑ j, w j) (p : (Idx F n × F) × Fin k) :
    ‖(coinStart (F := F) (n := n) k w) p‖ ^ 2 =
      if p.1 = (0, 0) then (w p.2 : ℝ) / ∑ i, (w i : ℝ) else 0 := by
  unfold coinStart
  split_ifs
  · simp only [PiLp.toLp_apply]
    rw [if_pos (by assumption), Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt]
    positivity
  · simp only [PiLp.toLp_apply]; rw [if_neg (by assumption)]; simp

lemma coinStart_unit (k : ℕ) (w : Fin k → ℕ) (hw : 0 < ∑ j, w j) :
    ‖(coinStart (F := F) (n := n) k w)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp_rw [coinStart_norm_sq k w hw]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (((0 : Vec F n), (0 : Vec F n), (0 : Vec F n)), (0 : F))]
  · have hW : (∑ i, (w i : ℝ)) ≠ 0 := by exact_mod_cast hw.ne'
    simp [← Finset.sum_div, hW]
  · intro p _ hp
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · exact absurd h hp
    · rfl
  · simp

noncomputable def coinAlg (k : ℕ) (w : Fin k → ℕ) (hw : 0 < ∑ j, w j) :
    QueryAlg (Idx F n) F (Fin k) 0 where
  start := coinStart k w
  start_unit := coinStart_unit k w hw
  U := fun _ => 1

lemma prob_coin (k : ℕ) (w : Fin k → ℕ) (hw : 0 < ∑ j, w j) (O : Matrix _ _ ℂ)
    (z : (Idx F n × F) × Fin k) :
    prob ((coinAlg (F := F) (n := n) k w hw).finalState O) z =
      if z.1 = (0, 0) then (w z.2 : ℝ) / ∑ i, (w i : ℝ) else 0 := by
  have : (coinAlg (F := F) (n := n) k w hw).finalState O = coinStart k w := by
    simp [QueryAlg.finalState, QueryAlg.stateAt, coinAlg, act]
  rw [this, prob]
  rw [show inner ℂ (ket z) (coinStart (F := F) (n := n) k w) = (coinStart k w) z by
    simp [ket, EuclideanSpace.inner_single_left]]
  exact coinStart_norm_sq k w hw z

lemma prob_ket {ι : Type} [Fintype ι] [DecidableEq ι] (z0 z : ι) :
    prob (ket z0) z = if z = z0 then 1 else 0 := by
  by_cases h : z = z0 <;> simp [prob, ket, h, EuclideanSpace.inner_single_left, Pi.single_apply]

noncomputable def compile {α : Type} : CAlg (CQ F n) (Vec F n) α → AdaptiveAlg (Idx F n) F α
  | .ret a => .halt a
  | .coin k w hw next => .round 0 k (coinAlg k w hw) (fun z => compile (next z.2))
  | .query q next => .round 1 1 (bvA q) (fun z => compile (next (bvDec q z)))

theorem outProb_compile {α : Type} (θ : TriForm F n) (P : α → Prop) [DecidablePred P] :
    ∀ A : CAlg (CQ F n) (Vec F n) α,
      (compile A).outProb (oracle θ) P = A.expect (CQ.ans θ) (fun a => if P a then 1 else 0) := by
  intro A
  induction A with
  | ret a => rfl
  | coin k w hw next ih =>
    simp only [compile, AdaptiveAlg.outProb, CAlg.expect]
    simp_rw [prob_coin, ih]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single ((0 : Idx F n), (0 : F))]
    · simp
    · intro p _ hp; simp [hp]
    · simp
  | query q next ih =>
    simp only [compile, AdaptiveAlg.outProb, CAlg.expect]
    obtain ⟨z0, hz0, hd⟩ := bv_spec q θ
    rw [hz0]
    simp_rw [prob_ket]
    rw [Finset.sum_eq_single z0]
    · simp [ih, hd]
    · intro z _ hz; simp [hz]
    · simp

theorem maxQueries_compile {α : Type} (θ : TriForm F n) :
    ∀ A : CAlg (CQ F n) (Vec F n) α,
      (compile A).maxQueries (oracle θ) = A.cost (CQ.ans θ) := by
  intro A
  induction A with
  | ret a => rfl
  | coin k w hw next ih =>
    classical
    simp only [compile, AdaptiveAlg.maxQueries, CAlg.cost, zero_add]
    have hset : (Finset.univ.filter fun z : (Idx F n × F) × Fin k =>
        0 < prob ((coinAlg (F := F) (n := n) k w hw).finalState (xorOracle (oracle θ))) z) =
        (Finset.univ.filter fun j => 0 < w j).image (fun j => (((0 : Idx F n), (0 : F)), j)) := by
      ext ⟨p, j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, prob_coin]
      have hW : (0 : ℝ) < ∑ i, (w i : ℝ) := by exact_mod_cast hw
      constructor
      · intro h
        split_ifs at h with hp
        · refine ⟨j, ?_, by simp [← hp]⟩
          have : (0 : ℝ) < w j := by
            by_contra hc; push Not at hc
            have : (w j : ℝ) / ∑ i, (w i : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hW.le
            linarith
          exact_mod_cast this
        · exact absurd h (lt_irrefl 0)
      · rintro ⟨j', hj', hpj⟩
        simp only [Prod.mk.injEq] at hpj
        obtain ⟨rfl, rfl⟩ := hpj
        simp only [if_true]
        exact div_pos (by exact_mod_cast hj') hW
    convert congrArg (fun s => s.sup fun z => (compile (next z.2)).maxQueries (oracle θ)) hset
      using 1
    rw [Finset.sup_image]
    simp only [Function.comp_def, ih]
  | query q next ih =>
    classical
    simp only [compile, AdaptiveAlg.maxQueries, CAlg.cost]
    obtain ⟨z0, hz0, hd⟩ := bv_spec q θ
    have hset : (Finset.univ.filter fun z : (Idx F n × F) × Fin 1 =>
        0 < prob ((bvA q).finalState (xorOracle (oracle θ))) z) = {z0} := by
      ext z; rw [hz0]; simp only [Finset.mem_filter, Finset.mem_univ, true_and, prob_ket,
        Finset.mem_singleton]
      split_ifs <;> simp_all
    rw [add_comm]
    congr 1
    convert congrArg (fun s => s.sup fun z => (compile (next (bvDec q z))).maxQueries (oracle θ))
      hset using 1
    simp [hd, ih]

/-- Every classical contraction-query algorithm is realised by an adaptive quantum query
algorithm with the same output law and the same worst-case query count. -/
theorem compile_spec {α : Type} (A : CAlg (CQ F n) (Vec F n) α) :
    ∃ B : AdaptiveAlg (Vec F n × Vec F n × Vec F n) F α, ∀ θ : TriForm F n,
      (∀ (P : α → Prop) [DecidablePred P],
        B.outProb (oracle θ) P = A.expect (CQ.ans θ) (fun a => if P a then 1 else 0)) ∧
      B.maxQueries (oracle θ) = A.cost (CQ.ans θ) :=
  ⟨compile A, fun θ => ⟨fun P _ => outProb_compile θ P A, maxQueries_compile θ A⟩⟩

end TriFormQ.CompileW

end


-- ===== Solutions/W_Tri.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TriFormQ.W

open Matrix

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Contraction answers -/

lemma eval_xy (θ : TriForm F n) (x y z : Vec F n) :
    TriForm.eval θ x y z = CQ.ans θ (.xy x y) ⬝ᵥ z := by
  simp only [TriForm.eval, CQ.ans, dotProduct, Finset.sum_mul]
  rw [show (∑ i, ∑ j, ∑ k, θ i j k * x i * y j * z k) =
      ∑ i, ∑ k, ∑ j, θ i j k * x i * y j * z k from
    Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma eval_xz (θ : TriForm F n) (x y z : Vec F n) :
    TriForm.eval θ x y z = CQ.ans θ (.xz x z) ⬝ᵥ y := by
  simp only [TriForm.eval, CQ.ans, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma eval_yz (θ : TriForm F n) (x y z : Vec F n) :
    TriForm.eval θ x y z = CQ.ans θ (.yz y z) ⬝ᵥ x := by
  simp only [TriForm.eval, CQ.ans, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma vec_eq_zero_of_dot (a : Vec F n) (h : ∀ z, a ⬝ᵥ z = 0) : a = 0 := by
  funext k
  have := h (Pi.single k 1)
  simpa [dotProduct_single] using this

lemma ans_xy_eq_zero_iff (θ : TriForm F n) (x y : Vec F n) :
    CQ.ans θ (.xy x y) = 0 ↔ ∀ z, TriForm.eval θ x y z = 0 := by
  constructor
  · intro h z; rw [eval_xy, h, zero_dotProduct]
  · intro h; exact vec_eq_zero_of_dot _ fun z => by rw [← eval_xy]; exact h z

lemma ans_sub (θ θ' : TriForm F n) (q : CQ F n) :
    CQ.ans (θ - θ') q = CQ.ans θ q - CQ.ans θ' q := by
  cases q <;> funext k <;> simp [CQ.ans, sub_mul, Finset.sum_sub_distrib]

lemma ans_add (θ θ' : TriForm F n) (q : CQ F n) :
    CQ.ans (θ + θ') q = CQ.ans θ q + CQ.ans θ' q := by
  cases q <;> funext k <;> simp [CQ.ans, add_mul, Finset.sum_add_distrib]

lemma eval_sub (θ θ' : TriForm F n) (x y z : Vec F n) :
    TriForm.eval (θ - θ') x y z = TriForm.eval θ x y z - TriForm.eval θ' x y z := by
  simp [TriForm.eval, sub_mul, Finset.sum_sub_distrib]

lemma eval_add (θ θ' : TriForm F n) (x y z : Vec F n) :
    TriForm.eval (θ + θ') x y z = TriForm.eval θ x y z + TriForm.eval θ' x y z := by
  simp [TriForm.eval, add_mul, Finset.sum_add_distrib]

/-- Linearity of `yz`-contractions in the first fixed argument. -/
lemma ans_yz_lin (θ : TriForm F n) (y y' z : Vec F n) (a : F) :
    CQ.ans θ (.yz (a • y + y') z) = a • CQ.ans θ (.yz y z) + CQ.ans θ (.yz y' z) := by
  funext i
  simp only [CQ.ans, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma ans_yz_sum (θ : TriForm F n) {d : ℕ} (v0 : Vec F n) (h : Fin d → Vec F n) (c : Fin d → F)
    (z : Vec F n) :
    CQ.ans θ (.yz (v0 + ∑ k, c k • h k) z) =
      CQ.ans θ (.yz v0 z) + ∑ k, c k • CQ.ans θ (.yz (h k) z) := by
  funext i
  have e1 : ∀ j, (v0 + ∑ k, c k • h k) j = v0 j + ∑ k, c k * h k j := by
    intro j; simp [Finset.sum_apply]
  have e2 : (∑ k, c k • CQ.ans θ (.yz (h k) z)) i = ∑ k, c k * CQ.ans θ (.yz (h k) z) i := by
    simp [Finset.sum_apply]
  rw [Pi.add_apply, e2]
  simp only [CQ.ans, e1, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [show (∑ j, ∑ k, ∑ l, θ i j k * (c l * h l j) * z k) =
      ∑ j, ∑ l, ∑ k, θ i j k * (c l * h l j) * z k from
    Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by ring

/-! ### Slices -/

lemma eval_sliceU (θ : TriForm F n) (u y z : Vec F n) :
    TriForm.eval θ u y z = y ⬝ᵥ (sliceU θ u *ᵥ z) := by
  simp only [TriForm.eval, sliceU, dotProduct, mulVec, of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

lemma sliceU_add (θ : TriForm F n) (u u' : Vec F n) :
    sliceU θ (u + u') = sliceU θ u + sliceU θ u' := by
  ext j k; simp [sliceU, mul_add, Finset.sum_add_distrib]

lemma sliceU_sub (θ : TriForm F n) (u u' : Vec F n) :
    sliceU θ (u - u') = sliceU θ u - sliceU θ u' := by
  ext j k; simp [sliceU, mul_sub, Finset.sum_sub_distrib]

lemma sliceU_smul (θ : TriForm F n) (a : F) (u : Vec F n) :
    sliceU θ (a • u) = a • sliceU θ u := by
  ext j k; simp [sliceU, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring

/-! ### Cardinalities of subspaces -/

lemma card_submodule_toFinset (P : Submodule F (Vec F n)) [DecidablePred (· ∈ P)] :
    (Finset.univ.filter (· ∈ P)).card = Fintype.card F ^ Module.finrank F P := by
  classical
  have h := Module.card_eq_pow_finrank (K := F) (V := P)
  rw [← h]
  convert (Fintype.card_subtype (· ∈ P)).symm

lemma card_vec : Fintype.card (Vec F n) = Fintype.card F ^ n := by
  simp [Fintype.card_fun]

lemma q_ge_two : 2 ≤ Fintype.card F := by
  have := Fintype.one_lt_card (α := F); omega

/-- A proper subspace has at most `q^(n-1)` elements (as a filtered set). -/
lemma card_proper_le (P : Submodule F (Vec F n)) (hP : P ≠ ⊤) [DecidablePred (· ∈ P)] :
    (Finset.univ.filter (· ∈ P)).card * Fintype.card F ≤ Fintype.card F ^ n := by
  rw [card_submodule_toFinset]
  have hlt : Module.finrank F P < n := by
    have h := Submodule.finrank_lt hP
    simpa using h
  have : Module.finrank F P + 1 ≤ n := hlt
  calc Fintype.card F ^ Module.finrank F P * Fintype.card F
      = Fintype.card F ^ (Module.finrank F P + 1) := by ring
    _ ≤ Fintype.card F ^ n := Nat.pow_le_pow_right Fintype.card_pos this

/-! ### Zero locus -/

lemma mem_zeroLocus (θ : TriForm F n) (u v : Vec F n) :
    (u, v) ∈ zeroLocus θ ↔ ∀ w, TriForm.eval θ u v w = 0 := by
  simp [zeroLocus]

lemma zeroLocus_card_pos (θ : TriForm F n) : 0 < (zeroLocus θ).card := by
  refine Finset.card_pos.2 ⟨(0, 0), ?_⟩
  rw [mem_zeroLocus]; intro w; simp [TriForm.eval]

/-- The analytic rank in count form: `AR ≤ ρ` iff `q^(2n) ≤ q^ρ |Z|`. -/
lemma AR_le_iff (θ : TriForm F n) (ρ : ℝ) :
    AR θ ≤ ρ ↔ (Fintype.card F : ℝ) ^ (2 * n) ≤ (Fintype.card F : ℝ) ^ ρ * (zeroLocus θ).card := by
  have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast (q_ge_two (F := F))
  have hZ : (0 : ℝ) < (zeroLocus θ).card := by exact_mod_cast zeroLocus_card_pos θ
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (2 * n) / (zeroLocus θ).card := by positivity
  unfold AR
  rw [Real.logb_le_iff_le_rpow hq hpos, div_le_iff₀ hZ]

/-- A nonzero trilinear form has `|Z| ≤ (3/4) q^(2n)`. -/
lemma zeroLocus_card_le_of_ne_zero (θ : TriForm F n) (hθ : θ ≠ 0) :
    4 * (zeroLocus θ).card ≤ 3 * Fintype.card F ^ (2 * n) := by
  classical
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := q_ge_two
  -- the linear map `u ↦ sliceU θ u` is nonzero
  let Lu : Vec F n →ₗ[F] Matrix (Fin n) (Fin n) F :=
    { toFun := sliceU θ, map_add' := sliceU_add θ, map_smul' := fun a u => sliceU_smul θ a u }
  have hLu : LinearMap.ker Lu ≠ ⊤ := by
    intro htop
    apply hθ
    funext i j k
    have h0 : sliceU θ (Pi.single i 1) = 0 := by
      have : Pi.single i 1 ∈ LinearMap.ker Lu := htop ▸ Submodule.mem_top
      simpa [Lu] using this
    have := congrFun (congrFun h0 j) k
    simpa [sliceU, Pi.single_apply] using this
  -- fibers
  have hfib : ∀ u : Vec F n, (Finset.univ.filter fun v : Vec F n =>
      ∀ w, TriForm.eval θ u v w = 0).card * (if sliceU θ u = 0 then 1 else q) ≤ q ^ n := by
    intro u
    split_ifs with hs
    · simpa [card_vec] using Finset.card_le_univ (Finset.univ.filter fun v : Vec F n =>
        ∀ w, TriForm.eval θ u v w = 0)
    · let P : Submodule F (Vec F n) := LinearMap.ker (vecMulLinear (sliceU θ u))
      have hP : P ≠ ⊤ := by
        intro htop; apply hs
        ext j k
        have : Pi.single j 1 ∈ P := htop ▸ Submodule.mem_top
        have h2 := congrFun (show Pi.single j (1 : F) ᵥ* sliceU θ u = 0 from this) k
        simpa [vecMul, dotProduct, Pi.single_apply] using h2
      have hset : (Finset.univ.filter fun v : Vec F n => ∀ w, TriForm.eval θ u v w = 0) =
          Finset.univ.filter (· ∈ P) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, LinearMap.mem_ker,
          vecMulLinear_apply]
        constructor
        · intro h; funext k
          have := h (Pi.single k 1)
          rw [eval_sliceU, dotProduct_mulVec] at this
          simpa [dotProduct_single] using this
        · intro h w; rw [eval_sliceU, dotProduct_mulVec, h, zero_dotProduct]
      rw [hset]; exact card_proper_le P hP
  -- count
  have hZ : (zeroLocus θ).card = ∑ u : Vec F n, (Finset.univ.filter fun v : Vec F n =>
      ∀ w, TriForm.eval θ u v w = 0).card := by
    rw [zeroLocus, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.card_filter]
  have hK := card_proper_le (LinearMap.ker Lu) hLu
  rw [← hq] at hK
  set K := (Finset.univ.filter (· ∈ LinearMap.ker Lu)).card with hKdef
  -- split the sum over u ∈ K and u ∉ K
  have hsplit : ∀ u : Vec F n, q * (Finset.univ.filter fun v : Vec F n =>
      ∀ w, TriForm.eval θ u v w = 0).card ≤ q ^ n + (if u ∈ LinearMap.ker Lu then
        (q - 1) * q ^ n else 0) := by
    intro u
    have h := hfib u
    by_cases hu : u ∈ LinearMap.ker Lu
    · have : sliceU θ u = 0 := by simpa [Lu] using hu
      rw [if_pos this] at h
      rw [if_pos hu]
      have : q * q ^ n = q ^ n + (q - 1) * q ^ n := by
        have : 1 ≤ q := by omega
        zify [this]; ring
      nlinarith
    · have : sliceU θ u ≠ 0 := by simpa [Lu] using hu
      rw [if_neg this] at h
      rw [if_neg hu]; linarith [mul_comm q ((Finset.univ.filter fun v : Vec F n =>
        ∀ w, TriForm.eval θ u v w = 0).card)]
  have hsum : q * (zeroLocus θ).card ≤ q ^ n * q ^ n + K * ((q - 1) * q ^ n) := by
    rw [hZ, Finset.mul_sum]
    calc ∑ u : Vec F n, q * (Finset.univ.filter fun v : Vec F n =>
          ∀ w, TriForm.eval θ u v w = 0).card
        ≤ ∑ u : Vec F n, (q ^ n + (if u ∈ LinearMap.ker Lu then (q - 1) * q ^ n else 0)) :=
          Finset.sum_le_sum fun u _ => hsplit u
      _ = q ^ n * q ^ n + K * ((q - 1) * q ^ n) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_vec, ← hq,
            Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
            smul_eq_mul, hKdef]
  -- combine: q |Z| ≤ q^(2n) + K (q-1) q^n with K q ≤ q^n
  have h2n : q ^ (2 * n) = q ^ n * q ^ n := by ring
  rw [h2n]
  have hq1 : 1 ≤ q := by omega
  -- multiply by q: q^2 |Z| ≤ q^(2n+1) + (q-1) q^n (K q) ≤ q^(2n) (2q - 1)
  have h3 : q * (q * (zeroLocus θ).card) ≤ q ^ n * q ^ n * (2 * q - 1) := by
    calc q * (q * (zeroLocus θ).card) ≤ q * (q ^ n * q ^ n + K * ((q - 1) * q ^ n)) :=
          Nat.mul_le_mul_left q hsum
      _ = q * (q ^ n * q ^ n) + (K * q) * ((q - 1) * q ^ n) := by ring
      _ ≤ q * (q ^ n * q ^ n) + q ^ n * ((q - 1) * q ^ n) := by
          have := Nat.mul_le_mul_right ((q - 1) * q ^ n) hK
          omega
      _ = q ^ n * q ^ n * (2 * q - 1) := by
          zify [hq1, (by omega : 1 ≤ 2 * q)]; ring
  -- (2q-1)*4 ≤ 3 q^2
  have h4 : 4 * (2 * q - 1) ≤ 3 * (q * q) := by
    zify [(by omega : 1 ≤ 2 * q)]; nlinarith
  have hqq : 0 < q * q := by positivity
  have : q * q * (4 * (zeroLocus θ).card) ≤ q * q * (3 * (q ^ n * q ^ n)) := by
    calc q * q * (4 * (zeroLocus θ).card) = 4 * (q * (q * (zeroLocus θ).card)) := by ring
      _ ≤ 4 * (q ^ n * q ^ n * (2 * q - 1)) := Nat.mul_le_mul_left 4 h3
      _ = q ^ n * q ^ n * (4 * (2 * q - 1)) := by ring
      _ ≤ q ^ n * q ^ n * (3 * (q * q)) := Nat.mul_le_mul_left _ h4
      _ = q * q * (3 * (q ^ n * q ^ n)) := by ring
  exact Nat.le_of_mul_le_mul_left this hqq

end TriFormQ.W

end


-- ===== Solutions/W_Prefilter.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TriFormQ.W

open CAlg

variable {Q R : Type} [DecidableEq R]

/-- Generic prefilter: `k` independent uniform query points; keep the candidates whose
answers agree with the oracle on all of them. -/
noncomputable def prefilter {Ω0 ι : Type} [Fintype Ω0] [Nonempty Ω0] (k : ℕ) (qf : Ω0 → Q)
    (cand : ι → Q → R) (C : Finset ι) : CAlg Q R (Finset ι) :=
  unif (β := Fin k → Ω0) fun ωs => queryN k (fun t => qf (ωs t)) fun rs =>
    ret (C.filter fun j => ∀ t, cand j (qf (ωs t)) = rs t)

variable {Ω0 ι : Type} [Fintype Ω0] [Nonempty Ω0]

/-- The survivors of the prefilter on query points `ωs`. -/
def survivors (qf : Ω0 → Q) (cand : ι → Q → R) (C : Finset ι) (ans : Q → R) {k : ℕ}
    (ωs : Fin k → Ω0) : Finset ι :=
  C.filter fun j => ∀ t, cand j (qf (ωs t)) = ans (qf (ωs t))

theorem expect_prefilter (ans : Q → R) (k : ℕ) (qf : Ω0 → Q) (cand : ι → Q → R) (C : Finset ι)
    (g : Finset ι → ℝ) :
    (prefilter k qf cand C).expect ans g =
      (∑ ωs : Fin k → Ω0, g (survivors qf cand C ans ωs)) / (Fintype.card Ω0 : ℝ) ^ k := by
  rw [prefilter, expect_unif]
  simp only [expect_queryN, expect]
  congr 1
  simp [Fintype.card_fun]

theorem cost_prefilter (ans : Q → R) (k : ℕ) (qf : Ω0 → Q) (cand : ι → Q → R) (C : Finset ι) :
    (prefilter k qf cand C).cost ans ≤ k := by
  refine cost_unif_le ans _ k fun ωs => ?_
  rw [cost_queryN]; simp [cost]

theorem allOut_prefilter (ans : Q → R) (k : ℕ) (qf : Ω0 → Q) (cand : ι → Q → R) (C : Finset ι) :
    (prefilter k qf cand C).AllOut ans fun S =>
      S ⊆ C ∧ ∀ j ∈ C, (∀ ω, cand j (qf ω) = ans (qf ω)) → j ∈ S := by
  refine allOut_unif ans _ fun ωs => allOut_queryN ans k _ _ ?_
  refine ⟨Finset.filter_subset _ _, fun j hj hagree => ?_⟩
  exact Finset.mem_filter.2 ⟨hj, fun t => hagree _⟩

/-- Agreement probability of candidate `j` at one uniform query point. -/
noncomputable def agreeProb (qf : Ω0 → Q) (cand : ι → Q → R) (ans : Q → R) (j : ι) : ℝ :=
  ((Finset.univ.filter fun ω => cand j (qf ω) = ans (qf ω)).card : ℝ) / Fintype.card Ω0

lemma card_all_mem {k : ℕ} (A : Finset Ω0)
    [DecidablePred fun ωs : Fin k → Ω0 => ∀ t, ωs t ∈ A] :
    (Finset.univ.filter fun ωs : Fin k → Ω0 => ∀ t, ωs t ∈ A).card = A.card ^ k := by
  classical
  have : (Finset.univ.filter fun ωs : Fin k → Ω0 => ∀ t, ωs t ∈ A) =
      Fintype.piFinset fun _ => A := by
    ext ωs; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp

/-- Union bound for the prefilter: a set `B` of bad candidates all survive with probability at
most `Σ_{j ∈ B} p_j^k`. -/
theorem prob_prefilter_bad (ans : Q → R) (k : ℕ) (qf : Ω0 → Q) (cand : ι → Q → R)
    (C : Finset ι) (bad : ι → Prop) [DecidablePred bad] :
    (prefilter k qf cand C).prob ans (fun S => ∃ j ∈ S, bad j) ≤
      ∑ j ∈ C.filter bad, agreeProb qf cand ans j ^ k := by
  classical
  unfold prob
  rw [expect_prefilter]
  have key : ∀ S : Finset ι, @ite ℝ (∃ j ∈ S, bad j) (Classical.propDecidable _) 1 0 =
      if ∃ j ∈ S, bad j then 1 else 0 := by
    intro S; by_cases h : ∃ j ∈ S, bad j <;> simp [h]
  simp only [key]
  have hΩ : (0 : ℝ) < (Fintype.card Ω0 : ℝ) ^ k := by
    have : 0 < Fintype.card Ω0 := Fintype.card_pos
    positivity
  rw [div_le_iff₀ hΩ]
  -- pointwise bound
  have hpt : ∀ ωs : Fin k → Ω0, (if ∃ j ∈ survivors qf cand C ans ωs, bad j then (1 : ℝ) else 0)
      ≤ ∑ j ∈ C.filter bad,
        (if ∀ t, cand j (qf (ωs t)) = ans (qf (ωs t)) then (1 : ℝ) else 0) := by
    intro ωs
    split_ifs with h
    · obtain ⟨j, hj, hb⟩ := h
      rw [survivors, Finset.mem_filter] at hj
      have : (if ∀ t, cand j (qf (ωs t)) = ans (qf (ωs t)) then (1 : ℝ) else 0) = 1 :=
        if_pos hj.2
      calc (1 : ℝ) = (if ∀ t, cand j (qf (ωs t)) = ans (qf (ωs t)) then (1 : ℝ) else 0) :=
            this.symm
        _ ≤ _ := Finset.single_le_sum (f := fun j => (if ∀ t, cand j (qf (ωs t)) =
              ans (qf (ωs t)) then (1 : ℝ) else 0)) (fun i _ => by split_ifs <;> norm_num)
              (Finset.mem_filter.2 ⟨hj.1, hb⟩)
    · exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  calc ∑ ωs : Fin k → Ω0, (if ∃ j ∈ survivors qf cand C ans ωs, bad j then (1 : ℝ) else 0)
      ≤ ∑ ωs : Fin k → Ω0, ∑ j ∈ C.filter bad,
        (if ∀ t, cand j (qf (ωs t)) = ans (qf (ωs t)) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun ωs _ => hpt ωs
    _ = ∑ j ∈ C.filter bad, ∑ ωs : Fin k → Ω0,
        (if ∀ t, cand j (qf (ωs t)) = ans (qf (ωs t)) then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ j ∈ C.filter bad, agreeProb qf cand ans j ^ k * (Fintype.card Ω0 : ℝ) ^ k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_boole]
        have := card_all_mem (k := k) (Finset.univ.filter fun ω => cand j (qf ω) = ans (qf ω))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        rw [this, agreeProb, div_pow, div_mul_cancel₀ _ hΩ.ne']
        push_cast; ring
    _ = (∑ j ∈ C.filter bad, agreeProb qf cand ans j ^ k) * (Fintype.card Ω0 : ℝ) ^ k := by
        rw [Finset.sum_mul]

theorem prob_prefilter_bad' (ans : Q → R) (k : ℕ) (qf : Ω0 → Q) (cand : ι → Q → R)
    (C : Finset ι) (bad : ι → Prop) [DecidablePred bad] (τ : ℝ) (hτ : 0 ≤ τ)
    (hbad : ∀ j ∈ C, bad j → agreeProb qf cand ans j ≤ τ) :
    (prefilter k qf cand C).prob ans (fun S => ∃ j ∈ S, bad j) ≤ C.card * τ ^ k := by
  refine (prob_prefilter_bad ans k qf cand C bad).trans ?_
  calc ∑ j ∈ C.filter bad, agreeProb qf cand ans j ^ k ≤ ∑ j ∈ C.filter bad, τ ^ k := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_filter.1 hj
        have h0 : 0 ≤ agreeProb qf cand ans j := by unfold agreeProb; positivity
        exact pow_le_pow_left₀ h0 (hbad j hj'.1 hj'.2) k
    _ = (C.filter bad).card * τ ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C.card * τ ^ k := by
        have : ((C.filter bad).card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_filter_le _ _
        exact mul_le_mul_of_nonneg_right this (by positivity)

/-! ### Trilinear instance: contraction queries `xy` at uniform `(u, v)` -/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

lemma agreeProb_tri (T : ι → TriForm F n) (θ : TriForm F n) (j : ι) :
    agreeProb (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2) (fun j => CQ.ans (T j)) (CQ.ans θ) j =
      ((zeroLocus (T j - θ)).card : ℝ) / (Fintype.card F : ℝ) ^ (2 * n) := by
  unfold agreeProb
  congr 2
  · congr 1
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_zeroLocus, eval_sub]
    rw [← sub_eq_zero, ← ans_sub, ans_xy_eq_zero_iff]
    simp [eval_sub]
  · simp [Fintype.card_prod, card_vec]; ring

end TriFormQ.W

end


-- ===== Solutions/W_LinAlg.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TriFormQ.W

open Matrix Module

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Ranks -/

lemma finrank_vec : finrank F (Vec F n) = n := by simp

lemma rank_add_le' (A B : Matrix (Fin n) (Fin n) F) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have h : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_sub_le' (A B : Matrix (Fin n) (Fin n) F) : (A - B).rank ≤ A.rank + B.rank := by
  have hneg : (-B).rank = B.rank := by
    rw [show -B = (-1 : F) • B by simp]
    exact Matrix.rank_smul_of_mem_nonZeroDivisors B (by simp)
  rw [sub_eq_add_neg]
  exact (rank_add_le' A (-B)).trans (by rw [hneg])

lemma finrank_ker_mulVecLin (A : Matrix (Fin n) (Fin n) F) :
    finrank F (LinearMap.ker A.mulVecLin) = n - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [finrank_vec] at h
  unfold Matrix.rank; omega

lemma card_ker_mulVec (A : Matrix (Fin n) (Fin n) F) :
    (Finset.univ.filter fun z : Vec F n => A *ᵥ z = 0).card = Fintype.card F ^ (n - A.rank) := by
  classical
  rw [← finrank_ker_mulVecLin, ← card_submodule_toFinset]
  congr 1; ext z; simp

lemma card_ker_vecMul (A : Matrix (Fin n) (Fin n) F) :
    (Finset.univ.filter fun y : Vec F n => y ᵥ* A = 0).card = Fintype.card F ^ (n - A.rank) := by
  have h := card_ker_mulVec Aᵀ
  rw [Matrix.rank_transpose] at h
  rw [← h]
  congr 1; ext y; simp [Matrix.mulVec_transpose]

/-! ### The random-probe lemma -/

open Classical in
/-- For a subspace `X` of dimension `r`, the number of `m`-tuples of vectors that are all
orthogonal to some nonzero `x ∈ X` is at most `q^r · (q^(n-1))^m`. -/
theorem probe_count (X : Submodule F (Vec F n)) (m : ℕ) :
    ((Finset.univ.filter fun zs : Fin m → Vec F n =>
        ∃ x ∈ X, x ≠ 0 ∧ ∀ l, zs l ⬝ᵥ x = 0).card : ℝ) * (Fintype.card F : ℝ) ^ m ≤
      (Fintype.card F : ℝ) ^ finrank F X * ((Fintype.card F : ℝ) ^ n) ^ m := by
  classical
  set q := Fintype.card F
  have hq : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  -- union bound over x ∈ X \ {0}
  let SX := (Finset.univ.filter (· ∈ X)).erase 0
  have hsub : (Finset.univ.filter fun zs : Fin m → Vec F n =>
      ∃ x ∈ X, x ≠ 0 ∧ ∀ l, zs l ⬝ᵥ x = 0) ⊆
      SX.biUnion fun x => Fintype.piFinset fun _ => Finset.univ.filter fun z => z ⬝ᵥ x = 0 := by
    intro zs hzs
    obtain ⟨x, hx, hx0, hxz⟩ := (Finset.mem_filter.1 hzs).2
    refine Finset.mem_biUnion.2 ⟨x, ?_, ?_⟩
    · exact Finset.mem_erase.2 ⟨hx0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩
    · exact Fintype.mem_piFinset.2 fun l => Finset.mem_filter.2 ⟨Finset.mem_univ _, hxz l⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  -- each kernel has at most q^(n-1) elements
  have hker : ∀ x ∈ SX, ((Finset.univ.filter fun z : Vec F n => z ⬝ᵥ x = 0).card : ℝ) * q ≤
      (q : ℝ) ^ n := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.1 hx).1
    let f : Vec F n →ₗ[F] F :=
      { toFun := fun z => z ⬝ᵥ x, map_add' := fun a b => add_dotProduct a b x,
        map_smul' := fun c a => smul_dotProduct c a x }
    have hP : LinearMap.ker f ≠ ⊤ := by
      intro htop
      apply hx0
      apply vec_eq_zero_of_dot
      intro z
      have : z ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
      simpa [f, dotProduct_comm] using this
    have := card_proper_le (LinearMap.ker f) hP
    have e : (Finset.univ.filter fun z : Vec F n => z ⬝ᵥ x = 0) =
        Finset.univ.filter (· ∈ LinearMap.ker f) := by
      ext z; simp [f]
    rw [e]; exact_mod_cast this
  have hSX : (SX.card : ℝ) ≤ (q : ℝ) ^ finrank F X := by
    have : SX.card ≤ (Finset.univ.filter (· ∈ X)).card := Finset.card_erase_le
    rw [card_submodule_toFinset] at this
    exact_mod_cast this
  calc ((Finset.univ.filter fun zs : Fin m → Vec F n =>
        ∃ x ∈ X, x ≠ 0 ∧ ∀ l, zs l ⬝ᵥ x = 0).card : ℝ) * (q : ℝ) ^ m
      ≤ (∑ x ∈ SX, ((Fintype.piFinset fun _ : Fin m =>
          Finset.univ.filter fun z : Vec F n => z ⬝ᵥ x = 0).card : ℝ)) * (q : ℝ) ^ m := by
        gcongr; exact_mod_cast hcard
    _ = ∑ x ∈ SX, ((Finset.univ.filter fun z : Vec F n => z ⬝ᵥ x = 0).card * q : ℝ) ^ m := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.card_piFinset]; push_cast
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    _ ≤ ∑ x ∈ SX, ((q : ℝ) ^ n) ^ m := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact pow_le_pow_left₀ (by positivity) (hker x hx) m
    _ = SX.card * ((q : ℝ) ^ n) ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) ^ finrank F X * ((q : ℝ) ^ n) ^ m := by gcongr

open Classical in
/-- Probability form of the probe lemma. -/
theorem probe_prob (X : Submodule F (Vec F n)) (m : ℕ) :
    ((Finset.univ.filter fun zs : Fin m → Vec F n =>
        ∃ x ∈ X, x ≠ 0 ∧ ∀ l, zs l ⬝ᵥ x = 0).card : ℝ) / ((Fintype.card F : ℝ) ^ n) ^ m ≤
      (Fintype.card F : ℝ) ^ finrank F X / (Fintype.card F : ℝ) ^ m := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := probe_count X m
  linarith

/-! ### Spans of random images -/

/-- If no nonzero vector of the row space of `Δ` is orthogonal to all probes `ys`, the images
`Δ ys_i` span the column space of `Δ`. -/
theorem span_images_eq (Δ : Matrix (Fin n) (Fin n) F) {m : ℕ} (ys : Fin m → Vec F n)
    (h : ¬ ∃ x ∈ LinearMap.range (Matrix.vecMulLinear Δ), x ≠ 0 ∧ ∀ i, ys i ⬝ᵥ x = 0) :
    Submodule.span F (Set.range fun i => Δ *ᵥ ys i) = LinearMap.range Δ.mulVecLin := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨ys i, rfl⟩
  · by_contra hne
    rw [SetLike.not_le_iff_exists] at hne
    obtain ⟨v, hv, hvs⟩ := hne
    obtain ⟨f, hfv, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvs inferInstance
    let lam : Vec F n := fun k => f (Pi.single k 1)
    have hf : ∀ w : Vec F n, f w = lam ⬝ᵥ w := by
      intro w
      conv_lhs => rw [show w = ∑ k, w k • Pi.single k (1 : F) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, lam, dotProduct, mul_comm]
    apply h
    refine ⟨lam ᵥ* Δ, ⟨lam, rfl⟩, ?_, ?_⟩
    · obtain ⟨w0, rfl⟩ := hv
      intro h0
      apply hfv
      rw [hf]
      show lam ⬝ᵥ (Δ *ᵥ w0) = 0
      rw [dotProduct_mulVec, h0, zero_dotProduct]
    · intro i
      have hmem : Δ *ᵥ ys i ∈ Submodule.span F (Set.range fun i => Δ *ᵥ ys i) :=
        Submodule.subset_span ⟨i, rfl⟩
      have : f (Δ *ᵥ ys i) = 0 := by
        have h2 : f (Δ *ᵥ ys i) ∈ (Submodule.span F (Set.range fun i => Δ *ᵥ ys i)).map f :=
          ⟨_, hmem, rfl⟩
        rw [hfS] at h2; simpa using h2
      rw [hf] at this
      rw [dotProduct_comm, ← dotProduct_mulVec]; exact this

/-! ### Lemma 11 (rank inequality) -/

section Tri

variable {V1 V2 W1 W2 : Type} [AddCommGroup V1] [Module F V1] [FiniteDimensional F V1]
  [AddCommGroup V2] [Module F V2] [FiniteDimensional F V2]
  [AddCommGroup W1] [Module F W1] [AddCommGroup W2] [Module F W2]

/-- A block lower-triangular map has rank at least the sum of the ranks of its diagonal
blocks. -/
lemma finrank_range_tri (f : V1 →ₗ[F] W1) (g : V1 →ₗ[F] W2) (h : V2 →ₗ[F] W2) :
    finrank F (LinearMap.range f) + finrank F (LinearMap.range h) ≤
      finrank F (LinearMap.range ((f ∘ₗ LinearMap.fst F V1 V2).prod
        (g ∘ₗ LinearMap.fst F V1 V2 + h ∘ₗ LinearMap.snd F V1 V2))) := by
  set T := (f ∘ₗ LinearMap.fst F V1 V2).prod (g ∘ₗ LinearMap.fst F V1 V2 + h ∘ₗ LinearMap.snd F V1 V2)
  have hT := LinearMap.finrank_range_add_finrank_ker T
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hh := LinearMap.finrank_range_add_finrank_ker h
  rw [Module.finrank_prod] at hT
  -- bound the kernel of T
  let ψ : LinearMap.ker T →ₗ[F] V1 := (LinearMap.fst F V1 V2) ∘ₗ (LinearMap.ker T).subtype
  have hψr : LinearMap.range ψ ≤ LinearMap.ker f := by
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    have := congrArg Prod.fst (LinearMap.mem_ker.1 hp)
    simpa [T, ψ] using this
  have hψ := LinearMap.finrank_range_add_finrank_ker ψ
  let χ : LinearMap.ker ψ →ₗ[F] V2 :=
    (LinearMap.snd F V1 V2) ∘ₗ (LinearMap.ker T).subtype ∘ₗ (LinearMap.ker ψ).subtype
  have hχinj : Function.Injective χ := by
    intro a b hab
    have ha := LinearMap.mem_ker.1 a.2
    have hb := LinearMap.mem_ker.1 b.2
    apply Subtype.ext; apply Subtype.ext
    simp only [χ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.snd_apply] at hab
    simp only [ψ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.fst_apply] at ha hb
    exact Prod.ext (ha.trans hb.symm) hab
  have hχr : LinearMap.range χ ≤ LinearMap.ker h := by
    rintro _ ⟨⟨⟨p, hp⟩, hp2⟩, rfl⟩
    have h1 := LinearMap.mem_ker.1 hp2
    simp only [ψ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.fst_apply] at h1
    have h2 : g p.1 + h p.2 = 0 := by
      have := congrArg Prod.snd (LinearMap.mem_ker.1 hp)
      simpa [T] using this
    rw [h1, map_zero, zero_add] at h2
    simpa [χ] using h2
  have hχ := LinearMap.finrank_range_of_inj hχinj
  have e1 := Submodule.finrank_mono hψr
  have e2 := Submodule.finrank_mono hχr
  omega

end Tri

lemma rank_eq_finrank (A : Matrix (Fin n) (Fin n) F) :
    A.rank = finrank F (LinearMap.range A.mulVecLin) := rfl

lemma rank_mul_le_left' (A B : Matrix (Fin n) (Fin n) F) : (A * B).rank ≤ A.rank :=
  Matrix.rank_mul_le_left A B

lemma rank_mul_le_right' (A B : Matrix (Fin n) (Fin n) F) : (A * B).rank ≤ B.rank :=
  Matrix.rank_mul_le_right A B

/-- Lemma 11 of the paper in the form used by the pivot: if `X A = 0` and `A Y = 0` (the
columns of `Xᵀ` lie in the left kernel and those of `Y` in the right kernel of `A`), then
`2 rk(X B Y) + rk A ≤ rk B + rk(A + B)`. -/
theorem lemma11_matrix (A B X Y : Matrix (Fin n) (Fin n) F) (hXA : X * A = 0)
    (hAY : A * Y = 0) : 2 * (X * B * Y).rank + A.rank ≤ B.rank + (A + B).rank := by
  let a := A.mulVecLin
  let b := B.mulVecLin
  let x := X.mulVecLin
  let y := Y.mulVecLin
  -- M (p1, p2) = ((A+B) p1 + A p2, B p2)
  let Mm : (Vec F n) × (Vec F n) →ₗ[F] (Vec F n) × (Vec F n) :=
    ((a + b) ∘ₗ LinearMap.fst F (Vec F n) (Vec F n) + a ∘ₗ LinearMap.snd F (Vec F n) (Vec F n)).prod (b ∘ₗ LinearMap.snd F (Vec F n) (Vec F n))
  have hM : finrank F (LinearMap.range Mm) ≤ (A + B).rank + B.rank := by
    -- Mm = inl ∘ (a+b) ∘ (fst + snd) + (inr - inl) ∘ b ∘ snd
    let G1 : (Vec F n) × (Vec F n) →ₗ[F] (Vec F n) × (Vec F n) := LinearMap.inl F (Vec F n) (Vec F n) ∘ₗ (a + b) ∘ₗ
      (LinearMap.fst F (Vec F n) (Vec F n) + LinearMap.snd F (Vec F n) (Vec F n))
    let G2 : (Vec F n) × (Vec F n) →ₗ[F] (Vec F n) × (Vec F n) := (LinearMap.inr F (Vec F n) (Vec F n) - LinearMap.inl F (Vec F n) (Vec F n)) ∘ₗ b ∘ₗ
      LinearMap.snd F (Vec F n) (Vec F n)
    have hMG : Mm = G1 + G2 := by
      apply LinearMap.ext; rintro ⟨p1, p2⟩
      simp only [Mm, G1, G2, a, b, LinearMap.prod_apply, LinearMap.add_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.sub_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_add,
        Prod.mk_add_mk, Prod.mk_sub_mk, Matrix.mulVec_add, Matrix.add_mulVec]
      ext i <;> simp [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVecLin_apply,
        Pi.neg_apply, LinearMap.neg_apply] <;> ring
    have h1 : finrank F (LinearMap.range G1) ≤ (A + B).rank := by
      have : LinearMap.range G1 ≤ (LinearMap.range (a + b)).map (LinearMap.inl F (Vec F n) (Vec F n)) := by
        rintro _ ⟨p, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩
      refine (Submodule.finrank_mono this).trans ((Submodule.finrank_map_le _ _).trans ?_)
      rw [rank_eq_finrank, Matrix.mulVecLin_add]
    have h2 : finrank F (LinearMap.range G2) ≤ B.rank := by
      have : LinearMap.range G2 ≤ (LinearMap.range b).map
          (LinearMap.inr F (Vec F n) (Vec F n) - LinearMap.inl F (Vec F n) (Vec F n)) := by
        rintro _ ⟨p, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩
      exact (Submodule.finrank_mono this).trans (Submodule.finrank_map_le _ _)
    have h3 : LinearMap.range Mm ≤ LinearMap.range G1 ⊔ LinearMap.range G2 := by
      rw [hMG]; rintro _ ⟨p, rfl⟩
      exact Submodule.add_mem_sup ⟨p, rfl⟩ ⟨p, rfl⟩
    have := (Submodule.finrank_mono h3).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
    omega
  -- R (y1, (y2, y3)) = (Y y1, y2 + Y y3), L (z1, z2) = (X z1, (z1, X z2))
  let Rm : (Vec F n) × ((Vec F n) × (Vec F n)) →ₗ[F] (Vec F n) × (Vec F n) :=
    (y ∘ₗ LinearMap.fst F (Vec F n) ((Vec F n) × (Vec F n))).prod
      (LinearMap.fst F (Vec F n) (Vec F n) ∘ₗ LinearMap.snd F (Vec F n) ((Vec F n) × (Vec F n)) +
        y ∘ₗ LinearMap.snd F (Vec F n) (Vec F n) ∘ₗ LinearMap.snd F (Vec F n) ((Vec F n) × (Vec F n)))
  let Lm : (Vec F n) × (Vec F n) →ₗ[F] (Vec F n) × ((Vec F n) × (Vec F n)) :=
    (x ∘ₗ LinearMap.fst F (Vec F n) (Vec F n)).prod ((LinearMap.fst F (Vec F n) (Vec F n)).prod (x ∘ₗ LinearMap.snd F (Vec F n) (Vec F n)))
  let P := (X * B * Y).mulVecLin
  -- the triangular form
  let h' : (Vec F n) × (Vec F n) →ₗ[F] (Vec F n) × (Vec F n) := (a ∘ₗ LinearMap.fst F (Vec F n) (Vec F n)).prod
    ((X * B).mulVecLin ∘ₗ LinearMap.fst F (Vec F n) (Vec F n) + P ∘ₗ LinearMap.snd F (Vec F n) (Vec F n))
  let g' : (Vec F n) →ₗ[F] (Vec F n) × (Vec F n) := LinearMap.inl F (Vec F n) (Vec F n) ∘ₗ (B * Y).mulVecLin
  let N : (Vec F n) × ((Vec F n) × (Vec F n)) →ₗ[F] (Vec F n) × ((Vec F n) × (Vec F n)) := (P ∘ₗ LinearMap.fst F (Vec F n) ((Vec F n) × (Vec F n))).prod
    (g' ∘ₗ LinearMap.fst F (Vec F n) ((Vec F n) × (Vec F n)) + h' ∘ₗ LinearMap.snd F (Vec F n) ((Vec F n) × (Vec F n)))
  have hN : Lm ∘ₗ Mm ∘ₗ Rm = N := by
    apply LinearMap.ext; rintro ⟨y1, y2, y3⟩
    have eXA : ∀ v, X *ᵥ (A *ᵥ v) = 0 := fun v => by rw [Matrix.mulVec_mulVec, hXA]; simp
    have eAY : ∀ v, A *ᵥ (Y *ᵥ v) = 0 := fun v => by rw [Matrix.mulVec_mulVec, hAY]; simp
    simp only [Lm, Mm, Rm, N, h', g', P, a, b, x, y, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.prod_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.inl_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_add, Function.prod_apply,
      Matrix.add_mulVec, Matrix.mulVec_add, ← Matrix.mulVec_mulVec, eXA, eAY]
    simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_zero, add_zero, zero_add, Prod.mk_add_mk, eAY]
  have hlow1 : finrank F (LinearMap.range P) + finrank F (LinearMap.range h') ≤
      finrank F (LinearMap.range N) := finrank_range_tri (F := F) P g' h'
  have hlow2 : finrank F (LinearMap.range a) + finrank F (LinearMap.range P) ≤
      finrank F (LinearMap.range h') := finrank_range_tri (F := F) a ((X * B).mulVecLin) P
  have hup : finrank F (LinearMap.range N) ≤ finrank F (LinearMap.range Mm) := by
    rw [← hN, LinearMap.range_comp]
    refine (Submodule.finrank_map_le _ _).trans ?_
    rw [LinearMap.range_comp]
    exact Submodule.finrank_mono (LinearMap.map_le_range)
  have hPr : (X * B * Y).rank = finrank F (LinearMap.range P) := rfl
  have hAr : A.rank = finrank F (LinearMap.range a) := rfl
  omega

end TriFormQ.W

end


-- ===== Solutions/W_MatId.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Matrix–vector queries to an unknown matrix. -/
inductive MQ (F : Type) (n : ℕ) : Type where
  | right (y : Vec F n)
  | left (x : Vec F n)

def MQ.ans (M : Matrix (Fin n) (Fin n) F) : MQ F n → Vec F n
  | .right y => M *ᵥ y
  | .left x => x ᵥ* M

/-! ### Numeric helpers -/

lemma two_pow_ceil_logb (x : ℝ) (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := by
  calc x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := Real.rpow_natCast 2 _

lemma q_pow_ge_two_pow (k : ℕ) : (2 : ℝ) ^ k ≤ (Fintype.card F : ℝ) ^ k := by
  have : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast q_ge_two (F := F)
  exact pow_le_pow_left₀ (by norm_num) this k

/-- `q^r / q^m ≤ 2^(r-m)`-type bound in the form we use: if `r + c ≤ m` then `q^r/q^m ≤ 1/2^c`. -/
lemma q_ratio_le {r m c : ℕ} (h : r + c ≤ m) :
    (Fintype.card F : ℝ) ^ r / (Fintype.card F : ℝ) ^ m ≤ 1 / (2 : ℝ) ^ c := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc (Fintype.card F : ℝ) ^ r * 2 ^ c ≤ (Fintype.card F : ℝ) ^ r * (Fintype.card F : ℝ) ^ c :=
        mul_le_mul_of_nonneg_left (q_pow_ge_two_pow c) (by positivity)
    _ = (Fintype.card F : ℝ) ^ (r + c) := by ring
    _ ≤ (Fintype.card F : ℝ) ^ m := pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos) h

/-! ### Decoding lemma -/

lemma vecMul_apply_eq_dot (v : Vec F n) (G : Matrix (Fin n) (Fin n) F) (k : Fin n) :
    (v ᵥ* G) k = v ⬝ᵥ (G *ᵥ Pi.single k 1) := by
  rw [dotProduct_mulVec, dotProduct_single, mul_one]

/-- If the probes `ys` reveal the column space of `Δ` and the probes `zs` are injective on it,
then `Δ` is the only matrix whose columns lie in the observed span and which has the observed
left products. -/
theorem decode_unique (Δ G : Matrix (Fin n) (Fin n) F) {m m' : ℕ} (ys : Fin m → Vec F n)
    (zs : Fin m' → Vec F n)
    (hY : Submodule.span F (Set.range fun i => Δ *ᵥ ys i) = LinearMap.range Δ.mulVecLin)
    (hZ : ¬ ∃ y ∈ LinearMap.range Δ.mulVecLin, y ≠ 0 ∧ ∀ i, zs i ⬝ᵥ y = 0) :
    ((∀ k, G *ᵥ Pi.single k 1 ∈ Submodule.span F (Set.range fun i => Δ *ᵥ ys i)) ∧
      ∀ i, zs i ᵥ* G = zs i ᵥ* Δ) ↔ G = Δ := by
  constructor
  · rintro ⟨hcol, hrow⟩
    have hcolk : ∀ k, G *ᵥ Pi.single k 1 = Δ *ᵥ Pi.single k 1 := by
      intro k
      by_contra hne
      apply hZ
      refine ⟨G *ᵥ Pi.single k 1 - Δ *ᵥ Pi.single k 1, ?_, sub_ne_zero.2 hne, ?_⟩
      · refine Submodule.sub_mem _ ?_ ⟨Pi.single k 1, rfl⟩
        rw [← hY]; exact hcol k
      · intro i
        rw [dotProduct_sub, ← vecMul_apply_eq_dot, ← vecMul_apply_eq_dot, hrow i, sub_self]
    ext j k
    have := congrFun (hcolk k) j
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  · rintro rfl
    refine ⟨fun k => ?_, fun i => rfl⟩
    rw [hY]; exact ⟨Pi.single k 1, rfl⟩

lemma finrank_range_vecMulLinear (Δ : Matrix (Fin n) (Fin n) F) :
    finrank F (LinearMap.range (Matrix.vecMulLinear Δ)) = Δ.rank := by
  have e : Matrix.vecMulLinear Δ = Δᵀ.mulVecLin := by
    rw [← Matrix.vecMulLinear_transpose, Matrix.transpose_transpose]
  rw [e, ← Matrix.rank_transpose Δ]; rfl

/-! ### The algorithm -/

/-- Parameters of the list-identification algorithm. -/
noncomputable def mR (K : ℕ) : ℕ := ⌈Real.sqrt (Real.logb 2 K)⌉₊
noncomputable def mk1 (K : ℕ) (ε : ℝ) : ℕ := ⌈(Real.logb 2 K + Real.logb 2 (4 / ε)) / (mR K + 1)⌉₊
noncomputable def mm1 (K : ℕ) (ε : ℝ) : ℕ := mR K + ⌈Real.logb 2 (8 / ε)⌉₊
noncomputable def mm3 (ε : ℝ) : ℕ := ⌈Real.logb 2 (4 / ε)⌉₊

open Classical in
/-- Identify the oracle matrix among `Ns`, or reject. -/
noncomputable def matId {K : ℕ} (Ns : Fin K → Matrix (Fin n) (Fin n) F) (ε : ℝ) :
    CAlg (MQ F n) (Vec F n) (Option (Fin K)) :=
  (prefilter (mk1 K ε) (fun y : Vec F n => MQ.right y) (fun l => MQ.ans (Ns l)) Finset.univ).bind
    fun S =>
      if hS : S.Nonempty then
        unif (β := Fin (mm1 K ε) → Vec F n) fun ys =>
          queryN (mm1 K ε) (fun i => MQ.right (ys i)) fun rs =>
            unif (β := Fin (mm1 K ε) → Vec F n) fun zs =>
              queryN (mm1 K ε) (fun i => MQ.left (zs i)) fun ls =>
                let s := S.min' hS
                let Y := Submodule.span F (Set.range fun i => rs i - Ns s *ᵥ ys i)
                let C := Finset.univ.filter fun l : Fin K =>
                  (∀ k, (Ns l - Ns s) *ᵥ Pi.single k 1 ∈ Y) ∧
                    ∀ i, zs i ᵥ* (Ns l - Ns s) = ls i - zs i ᵥ* Ns s
                if hC : C.Nonempty then
                  unif (β := Fin (mm3 ε) → Vec F n) fun vs =>
                    queryN (mm3 ε) (fun i => MQ.right (vs i)) fun ts =>
                      ret (if ∀ i, Ns (C.min' hC) *ᵥ vs i = ts i then some (C.min' hC) else none)
                else ret none
      else ret none

/-! ### Cost -/

theorem cost_matId {K : ℕ} (Ns : Fin K → Matrix (Fin n) (Fin n) F) (ε : ℝ)
    (ans' : MQ F n → Vec F n) :
    (matId Ns ε).cost ans' ≤ mk1 K ε + 2 * mm1 K ε + mm3 ε := by
  unfold matId
  refine (cost_bind_le _ _ _ (2 * mm1 K ε + mm3 ε) (allOut_of_forall _ _ fun S => ?_)).trans ?_
  · split_ifs with hS
    · refine cost_unif_le _ _ _ fun ys => ?_
      rw [cost_queryN]
      refine Nat.add_le_of_le_sub (by omega) ?_
      refine (cost_unif_le _ _ (mm1 K ε + mm3 ε) fun zs => ?_).trans (by omega)
      rw [cost_queryN]
      refine Nat.add_le_of_le_sub (by omega) ?_
      simp only [Nat.add_sub_cancel]
      split_ifs with hC
      · refine cost_unif_le _ _ _ fun vs => ?_
        rw [cost_queryN]; simp [cost]
      · simp [cost]
    · simp [cost]
  · have := cost_prefilter ans' (mk1 K ε) (fun y : Vec F n => MQ.right y)
      (fun l => MQ.ans (Ns l)) Finset.univ
    omega

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Generic probability helpers -/

section helpers
variable {Q R α : Type}

theorem prob_unif_le {β : Type} [Fintype β] [Nonempty β] (ans : Q → R) (k : β → CAlg Q R α)
    (P : α → Prop) (c : ℝ) (h : ∀ b, (k b).prob ans P ≤ c) : (unif k).prob ans P ≤ c := by
  unfold prob; rw [expect_unif]
  have hc : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc]
  calc ∑ b, (k b).expect ans _ ≤ ∑ _b : β, c := Finset.sum_le_sum fun b _ => h b
    _ = c * Fintype.card β := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

theorem prob_queryN (ans : Q → R) (m : ℕ) (qs : Fin m → Q) (k : (Fin m → R) → CAlg Q R α)
    (P : α → Prop) : (queryN m qs k).prob ans P = (k (fun i => ans (qs i))).prob ans P :=
  expect_queryN ans m qs k _

theorem prob_unif {β : Type} [Fintype β] [Nonempty β] (ans : Q → R) (k : β → CAlg Q R α)
    (P : α → Prop) : (unif k).prob ans P = (∑ b, (k b).prob ans P) / Fintype.card β :=
  expect_unif ans k _

theorem prob_ret (ans : Q → R) (a : α) (P : α → Prop) [Decidable (P a)] :
    (ret a : CAlg Q R α).prob ans P = if P a then 1 else 0 := by
  unfold prob; simp only [expect]; congr 1

end helpers

/-- Fraction of tuples satisfying a predicate. -/
lemma avg_indicator_le {β : Type} [Fintype β] [Nonempty β] (B : β → Prop) [DecidablePred B]
    (c : ℝ) (h : ((Finset.univ.filter B).card : ℝ) / Fintype.card β ≤ c) :
    (∑ b, (if B b then (1 : ℝ) else 0)) / Fintype.card β ≤ c := by
  rwa [Finset.sum_boole]

/-! ### Rejection -/

theorem matId_reject {K : ℕ} (Ns : Fin K → Matrix (Fin n) (Fin n) F) (ε : ℝ) (hε : 0 < ε)
    (M : Matrix (Fin n) (Fin n) F) (hM : ∀ l, Ns l ≠ M) :
    (matId Ns ε).prob (MQ.ans M) (fun o => o ≠ none) ≤ ε / 4 := by
  classical
  unfold matId
  rw [prob_bind]
  have hc : ∀ S : Finset (Fin K), (if hS : S.Nonempty then
        unif (β := Fin (mm1 K ε) → Vec F n) fun ys =>
          queryN (mm1 K ε) (fun i => MQ.right (ys i)) fun rs =>
            unif (β := Fin (mm1 K ε) → Vec F n) fun zs =>
              queryN (mm1 K ε) (fun i => MQ.left (zs i)) fun ls =>
                let s := S.min' hS
                let Y := Submodule.span F (Set.range fun i => rs i - Ns s *ᵥ ys i)
                let C := Finset.univ.filter fun l : Fin K =>
                  (∀ k, (Ns l - Ns s) *ᵥ Pi.single k 1 ∈ Y) ∧
                    ∀ i, zs i ᵥ* (Ns l - Ns s) = ls i - zs i ᵥ* Ns s
                if hC : C.Nonempty then
                  unif (β := Fin (mm3 ε) → Vec F n) fun vs =>
                    queryN (mm3 ε) (fun i => MQ.right (vs i)) fun ts =>
                      ret (if ∀ i, Ns (C.min' hC) *ᵥ vs i = ts i then some (C.min' hC) else none)
                else ret none
      else ret none).prob (MQ.ans M) (fun o => o ≠ none) ≤ ε / 4 := by
    intro S
    split_ifs with hS
    · refine prob_unif_le _ _ _ _ fun ys => ?_
      rw [prob_queryN]
      refine prob_unif_le _ _ _ _ fun zs => ?_
      rw [prob_queryN]
      simp only
      split_ifs with hC
      · set l := (Finset.univ.filter _).min' hC
        rw [prob_unif]
        simp only [prob_queryN, MQ.ans]
        simp_rw [prob_ret]
        have hne : Ns l - M ≠ 0 := sub_ne_zero.2 (hM l)
        -- count the passing tuples
        have hcount : ((Finset.univ.filter fun vs : Fin (mm3 ε) → Vec F n =>
            ∀ i, Ns l *ᵥ vs i = M *ᵥ vs i).card : ℝ) / Fintype.card (Fin (mm3 ε) → Vec F n)
            ≤ ε / 4 := by
          have e : (Finset.univ.filter fun vs : Fin (mm3 ε) → Vec F n =>
              ∀ i, Ns l *ᵥ vs i = M *ᵥ vs i) = Finset.univ.filter fun vs =>
              ∀ i, vs i ∈ Finset.univ.filter fun v : Vec F n => (Ns l - M) *ᵥ v = 0 := by
            ext vs; simp [Matrix.sub_mulVec, sub_eq_zero]
          rw [e, card_all_mem, card_ker_mulVec]
          have hr : 1 ≤ (Ns l - M).rank := by
            by_contra h0; push Not at h0
            have h00 : (Ns l - M).rank = 0 := by omega
            apply hne
            have := LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 h00)
            ext i j
            have h2 := congrArg (fun f => f (Pi.single j 1) i) this
            simpa [Matrix.mulVecLin_apply, mulVec, dotProduct, Pi.single_apply] using h2
          have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
          rw [Fintype.card_fun, Fintype.card_fin, card_vec]
          push_cast
          have hn : (n - (Ns l - M).rank) + 1 ≤ n := by
            have := Matrix.rank_le_width (Ns l - M); omega
          calc ((Fintype.card F : ℝ) ^ (n - (Ns l - M).rank)) ^ mm3 ε /
                ((Fintype.card F : ℝ) ^ n) ^ mm3 ε
              = ((Fintype.card F : ℝ) ^ (n - (Ns l - M).rank) / (Fintype.card F : ℝ) ^ n)
                  ^ mm3 ε := by rw [div_pow]
            _ ≤ (1 / 2) ^ mm3 ε := by
                refine pow_le_pow_left₀ (by positivity) ?_ _
                have := q_ratio_le (F := F) (r := n - (Ns l - M).rank) (m := n) (c := 1)
                  (by omega)
                simpa using this
            _ = 1 / (2 : ℝ) ^ mm3 ε := by rw [div_pow, one_pow]
            _ ≤ ε / 4 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul]
                have := two_pow_ceil_logb (4 / ε) (by positivity)
                unfold mm3
                rw [div_le_iff₀ hε] at this
                linarith
        convert hcount using 2
        rw [Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun vs _ => ?_
        by_cases h : ∀ i, Ns l *ᵥ vs i = M *ᵥ vs i
        · simp [h]
        · simp [h]
      · rw [prob_ret]; simp; positivity
    · rw [prob_ret]; simp; positivity
  calc _ ≤ (prefilter (mk1 K ε) (fun y : Vec F n => MQ.right y) (fun l => MQ.ans (Ns l))
        Finset.univ).expect (MQ.ans M) (fun _ => ε / 4) := expect_mono _ _ hc
    _ = ε / 4 := expect_const _ _ _

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

lemma avg2_ge {β γ : Type} [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (f : β → γ → ℝ) (a : β → ℝ) (b : γ → ℝ) (h : ∀ x y, 1 - a x - b y ≤ f x y) :
    1 - (∑ x, a x) / Fintype.card β - (∑ y, b y) / Fintype.card γ ≤
      (∑ x, (∑ y, f x y) / Fintype.card γ) / Fintype.card β := by
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hγ : (0 : ℝ) < Fintype.card γ := by exact_mod_cast Fintype.card_pos
  have h1 : ∀ x, 1 - a x - (∑ y, b y) / Fintype.card γ ≤ (∑ y, f x y) / Fintype.card γ := by
    intro x
    rw [le_div_iff₀ hγ]
    calc (1 - a x - (∑ y, b y) / Fintype.card γ) * Fintype.card γ
        = ∑ y : γ, (1 - a x - b y) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
      _ ≤ ∑ y, f x y := Finset.sum_le_sum fun y _ => h x y
  rw [le_div_iff₀ hβ]
  calc (1 - (∑ x, a x) / Fintype.card β - (∑ y, b y) / Fintype.card γ) * Fintype.card β
      = ∑ x : β, (1 - a x - (∑ y, b y) / Fintype.card γ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    _ ≤ _ := Finset.sum_le_sum fun x _ => h1 x

open Classical in
/-- The probe failure fraction for a matrix of rank at most `r` with `r + c` probes. -/
lemma probe_frac_le (X : Submodule F (Vec F n)) {r c : ℕ} (hX : finrank F X ≤ r) :
    (∑ zs : Fin (r + c) → Vec F n, (if ∃ x ∈ X, x ≠ 0 ∧ ∀ l, zs l ⬝ᵥ x = 0 then (1 : ℝ) else 0))
      / Fintype.card (Fin (r + c) → Vec F n) ≤ 1 / 2 ^ c := by
  classical
  rw [Finset.sum_boole, Fintype.card_fun, Fintype.card_fin, card_vec]
  push_cast
  refine le_trans ?_ ((q_ratio_le (F := F) (r := finrank F X) (m := r + c) (c := c)
    (by omega)))
  convert probe_prob X (r + c) using 3

lemma one_div_two_pow_ceil_le (x : ℝ) (hx : 0 < x) :
    1 / (2 : ℝ) ^ ⌈Real.logb 2 (1 / x)⌉₊ ≤ x := by
  have := two_pow_ceil_logb (1 / x) (by positivity)
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hx] at this
  linarith

theorem matId_found {K : ℕ} (Ns : Fin K → Matrix (Fin n) (Fin n) F) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (M : Matrix (Fin n) (Fin n) F) (l0 : Fin K) (hl0 : Ns l0 = M) :
    1 - ε / 2 ≤ (matId Ns ε).prob (MQ.ans M) (fun o => ∃ j, o = some j ∧ Ns j = M) := by
  classical
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact l0.elim0)
  set R := mR K
  unfold matId
  refine le_trans (by linarith : 1 - ε / 2 ≤ 1 - ε / 4 - ε / 4) (prob_bind_ge (MQ.ans M) _ _
    (fun S => l0 ∈ S ∧ ∀ l ∈ S, (Ns l - M).rank ≤ R)
    (fun o => ∃ j, o = some j ∧ Ns j = M) (ε / 4) (ε / 4) ?_ ?_ (by positivity) (by linarith))
  · -- the prefilter keeps `l0` and removes every candidate far in rank
    refine prob_ge_of_fail _ _ ?_
    have hall := allOut_prefilter (MQ.ans M) (mk1 K ε) (fun y : Vec F n => MQ.right y)
      (fun l => MQ.ans (Ns l)) Finset.univ
    refine (prob_mono_allOut _ _ (P' := fun S => ∃ l ∈ S, R < (Ns l - M).rank)
      (allOut_mono _ _ (fun S hS hn => ?_) hall)).trans ?_
    · have hl0S : l0 ∈ S := hS.2 l0 (Finset.mem_univ _) (fun y => by simp [MQ.ans, hl0])
      by_contra hc; push Not at hc
      exact hn ⟨hl0S, fun l hl => hc l hl⟩
    · refine (prob_prefilter_bad' (MQ.ans M) (mk1 K ε) (fun y : Vec F n => MQ.right y)
        (fun l => MQ.ans (Ns l)) Finset.univ (fun l => R < (Ns l - M).rank)
        (1 / 2 ^ (R + 1)) (by positivity) ?_).trans ?_
      · intro l _ hl
        unfold agreeProb
        have e : (Finset.univ.filter fun y : Vec F n => MQ.ans (Ns l) (MQ.right y) =
            MQ.ans M (MQ.right y)) = Finset.univ.filter fun y => (Ns l - M) *ᵥ y = 0 := by
          refine Finset.filter_congr fun y _ => ?_
          simp only [MQ.ans, Matrix.sub_mulVec, sub_eq_zero]
        rw [e, card_ker_mulVec, card_vec]
        push_cast
        have := Matrix.rank_le_width (Ns l - M)
        exact q_ratio_le (by omega)
      · -- K (1/2^(R+1))^k1 ≤ ε/4
        rw [Finset.card_univ, Fintype.card_fin, ← _root_.one_div_pow, ← pow_mul]
        rw [_root_.one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        have hk1 : Real.logb 2 K + Real.logb 2 (4 / ε) ≤ ((R + 1) * mk1 K ε : ℕ) := by
          push_cast
          have h := Nat.le_ceil ((Real.logb 2 K + Real.logb 2 (4 / ε)) / (R + 1))
          unfold mk1 at *
          rw [div_le_iff₀ (by positivity)] at h
          linarith
        have h2 : (4 * K / ε : ℝ) ≤ 2 ^ ((R + 1) * mk1 K ε) := by
          have hpos : (0 : ℝ) < 4 * K / ε := by
            have : (0 : ℝ) < K := by exact_mod_cast hK
            positivity
          calc (4 * K / ε : ℝ) = 2 ^ Real.logb 2 (4 * K / ε) :=
                (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
            _ ≤ 2 ^ (((R + 1) * mk1 K ε : ℕ) : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                rw [show (4 * K / ε : ℝ) = K * (4 / ε) by ring,
                  Real.logb_mul (by exact_mod_cast (show K ≠ 0 by omega)) (by positivity)]
                exact hk1
            _ = _ := Real.rpow_natCast _ _
        rw [div_le_iff₀ hε] at h2
        linarith
  · -- second stage
    rintro S ⟨hl0S, hrank⟩
    have hS : S.Nonempty := ⟨l0, hl0S⟩
    rw [dif_pos hS, prob_unif]
    set s := S.min' hS
    have hs : (M - Ns s).rank ≤ R := by
      have := hrank s (S.min'_mem hS)
      rw [← Matrix.rank_transpose] at this ⊢
      have e : (M - Ns s)ᵀ = (-1 : F) • (Ns s - M)ᵀ := by
        ext i j; simp
      rw [e, Matrix.rank_smul_of_mem_nonZeroDivisors _ (by simp)]; exact this
    set Δ := M - Ns s
    simp only [prob_queryN, prob_unif]
    refine le_trans ?_ (avg2_ge _
      (fun ys : Fin (mm1 K ε) → Vec F n =>
        if ∃ x ∈ LinearMap.range (Matrix.vecMulLinear Δ), x ≠ 0 ∧ ∀ i, ys i ⬝ᵥ x = 0
          then (1 : ℝ) else 0)
      (fun zs : Fin (mm1 K ε) → Vec F n =>
        if ∃ y ∈ LinearMap.range Δ.mulVecLin, y ≠ 0 ∧ ∀ i, zs i ⬝ᵥ y = 0
          then (1 : ℝ) else 0) ?_)
    rotate_left
    · intro ys zs
      by_cases hE2 : ∃ x ∈ LinearMap.range (Matrix.vecMulLinear Δ), x ≠ 0 ∧ ∀ i, ys i ⬝ᵥ x = 0
      · rw [if_pos hE2]
        refine le_trans ?_ (prob_nonneg _ _ _)
        split_ifs <;> norm_num
      by_cases hE3 : ∃ y ∈ LinearMap.range Δ.mulVecLin, y ≠ 0 ∧ ∀ i, zs i ⬝ᵥ y = 0
      · rw [if_pos hE3]
        refine le_trans ?_ (prob_nonneg _ _ _)
        split_ifs <;> norm_num
      rw [if_neg hE2, if_neg hE3]
      have hY := span_images_eq Δ ys hE2
      have hYeq : Submodule.span F (Set.range fun i => M *ᵥ ys i - Ns s *ᵥ ys i) =
          Submodule.span F (Set.range fun i => Δ *ᵥ ys i) := by
        congr 2; funext i; simp [Δ, Matrix.sub_mulVec]
      have hmemC : ∀ l, ((∀ k, (Ns l - Ns s) *ᵥ Pi.single k 1 ∈ Submodule.span F
          (Set.range fun i => (fun i => MQ.ans M (MQ.right (ys i))) i - Ns s *ᵥ ys i)) ∧
          ∀ i, zs i ᵥ* (Ns l - Ns s) = (fun i => MQ.ans M (MQ.left (zs i))) i - zs i ᵥ* Ns s)
          ↔ Ns l = M := by
        intro l
        simp only [MQ.ans]
        rw [hYeq]
        have hd := decode_unique Δ (Ns l - Ns s) ys zs hY hE3
        have e2 : ∀ i, zs i ᵥ* M - zs i ᵥ* Ns s = zs i ᵥ* Δ := fun i => by
          simp [Δ, Matrix.vecMul_sub]
        simp only [e2, hd, Δ, sub_left_inj]
      try dsimp only
      split_ifs with hC
      · have hl := Finset.min'_mem _ hC
        rw [Finset.mem_filter, hmemC] at hl
        rw [prob_of_allOut]
        · norm_num
        refine allOut_unif _ _ fun vs => allOut_queryN _ _ _ _ ?_
        have hpass : ∀ i, Ns (Finset.min' _ hC) *ᵥ vs i = MQ.ans M (MQ.right (vs i)) :=
          fun i => by rw [hl.2]; rfl
        simp only [AllOut, if_pos hpass]
        exact ⟨_, rfl, hl.2⟩
      · exfalso; apply hC
        exact ⟨l0, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmemC l0).2 hl0⟩⟩
    have h2 : (∑ ys : Fin (mm1 K ε) → Vec F n, (if ∃ x ∈ LinearMap.range (Matrix.vecMulLinear Δ),
        x ≠ 0 ∧ ∀ i, ys i ⬝ᵥ x = 0 then (1 : ℝ) else 0)) /
        Fintype.card (Fin (mm1 K ε) → Vec F n) ≤ ε / 8 := by
      have := probe_frac_le (F := F) (n := n) (LinearMap.range (Matrix.vecMulLinear Δ))
        (r := R) (c := ⌈Real.logb 2 (8 / ε)⌉₊) (by rw [finrank_range_vecMulLinear]; exact hs)
      refine le_trans ?_ (this.trans ?_)
      · rfl
      · have := one_div_two_pow_ceil_le (ε / 8) (by positivity)
        rwa [show 1 / (ε / 8) = 8 / ε by field_simp] at this
    have h3 : (∑ zs : Fin (mm1 K ε) → Vec F n, (if ∃ y ∈ LinearMap.range Δ.mulVecLin,
        y ≠ 0 ∧ ∀ i, zs i ⬝ᵥ y = 0 then (1 : ℝ) else 0)) /
        Fintype.card (Fin (mm1 K ε) → Vec F n) ≤ ε / 8 := by
      have := probe_frac_le (F := F) (n := n) (LinearMap.range Δ.mulVecLin)
        (r := R) (c := ⌈Real.logb 2 (8 / ε)⌉₊) hs
      refine le_trans ?_ (this.trans ?_)
      · rfl
      · have := one_div_two_pow_ceil_le (ε / 8) (by positivity)
        rwa [show 1 / (ε / 8) = 8 / ε by field_simp] at this
    linarith

end TriFormQ.W

end


-- ===== Solutions/W_Bands.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Numeric cost bound of `matId` -/

lemma logb_two_nat_nonneg (K : ℕ) : 0 ≤ Real.logb 2 K := by
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

lemma logb_mul_inv (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    Real.logb 2 (c / ε) = Real.logb 2 c + Real.logb 2 (1 / ε) := by
  rw [show c / ε = c * (1 / ε) by ring, Real.logb_mul hc.ne' (by positivity)]

lemma logb_inv_nonneg (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ Real.logb 2 (1 / ε) :=
  Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hε]; linarith)

theorem matId_cost_real (K : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((mk1 K ε + 2 * mm1 K ε + mm3 ε : ℕ) : ℝ) ≤
      3 * Real.sqrt (Real.logb 2 K) + 4 * Real.logb 2 (1 / ε) + 20 := by
  set x := Real.logb 2 K with hx
  set L := Real.logb 2 (1 / ε) with hL
  have hx0 : 0 ≤ x := logb_two_nat_nonneg K
  have hL0 : 0 ≤ L := logb_inv_nonneg ε hε hε1
  have l4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  have l8 : Real.logb 2 8 = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  have h4 : Real.logb 2 (4 / ε) = 2 + L := by
    rw [logb_mul_inv 4 ε (by norm_num) hε, l4]
  have h8 : Real.logb 2 (8 / ε) = 3 + L := by
    rw [logb_mul_inv 8 ε (by norm_num) hε, l8]
  set s := Real.sqrt x
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hR1 : (mR K : ℝ) ≤ s + 1 := (Nat.ceil_lt_add_one hs0).le
  have hR2 : s ≤ (mR K : ℝ) := Nat.le_ceil _
  have hk1 : (mk1 K ε : ℝ) ≤ s + (2 + L) + 1 := by
    unfold mk1
    rw [h4]
    refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
    have hpos : (0 : ℝ) < (mR K : ℝ) + 1 := by positivity
    have : (x + (2 + L)) / ((mR K : ℝ) + 1) ≤ s + (2 + L) := by
      rw [div_le_iff₀ hpos]
      have hxs : x = s * s := (Real.mul_self_sqrt hx0).symm
      nlinarith
    linarith
  have hm1 : (mm1 K ε : ℝ) ≤ s + 1 + (3 + L) + 1 := by
    unfold mm1; push_cast
    have := (Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (8 / ε) by rw [h8]; linarith)).le
    rw [h8] at this ⊢
    linarith
  have hm3 : (mm3 ε : ℝ) ≤ (2 + L) + 1 := by
    unfold mm3
    have := (Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (4 / ε) by rw [h4]; linarith)).le
    rw [h4] at this ⊢; exact this
  push_cast
  linarith

/-! ### Bands -/

section Bands

variable {ι : Type} [DecidableEq ι] {Mat : Type} [DecidableEq Mat]

/-- Number of candidates in `C` whose value is `V`. -/
def cntV (val : ι → Mat) (C : Finset ι) (V : Mat) : ℕ := (C.filter fun j => val j = V).card

/-- Band `k`: values whose weight `cnt / |C|` lies in `(2^{-2^k}, 2^{-2^{k-1}}]` (band 0: `> 1/2`). -/
def band (val : ι → Mat) (C : Finset ι) (k : ℕ) : Finset Mat :=
  (C.image val).filter fun V => C.card < cntV val C V * 2 ^ (2 ^ k) ∧
    (k = 0 ∨ cntV val C V * 2 ^ (2 ^ (k - 1)) ≤ C.card)

lemma cntV_pos {val : ι → Mat} {C : Finset ι} {V : Mat} (hV : V ∈ C.image val) :
    0 < cntV val C V := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hV
  exact Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨hj, rfl⟩⟩

lemma two_pow_two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ (2 ^ a) ≤ 2 ^ (2 ^ b) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

/-- Every value of a candidate lies in a band of index at most `kmax` if `|C| < 2^(2^kmax)`. -/
lemma exists_band {val : ι → Mat} {C : Finset ι} {V : Mat} (hV : V ∈ C.image val) {kmax : ℕ}
    (hk : C.card < 2 ^ (2 ^ kmax)) : ∃ k ≤ kmax, V ∈ band val C k := by
  classical
  have hc := cntV_pos hV
  have hex : ∃ k, C.card < cntV val C V * 2 ^ (2 ^ k) :=
    ⟨kmax, lt_of_lt_of_le hk (Nat.le_mul_of_pos_left _ hc)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (lt_of_lt_of_le hk (Nat.le_mul_of_pos_left _ hc)), ?_⟩
  refine Finset.mem_filter.2 ⟨hV, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · exact Or.inl h0
  · right
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this; exact this

lemma band_disjoint {val : ι → Mat} {C : Finset ι} {V : Mat} {k k' : ℕ} (h : k < k')
    (hk : V ∈ band val C k) (hk' : V ∈ band val C k') : False := by
  have h1 := (Finset.mem_filter.1 hk).2.1
  have h2 := (Finset.mem_filter.1 hk').2.2
  rcases h2 with h2 | h2
  · omega
  · have := two_pow_two_pow_mono (show k ≤ k' - 1 by omega)
    have := Nat.mul_le_mul_left (cntV val C V) this
    omega

lemma sum_cntV (val : ι → Mat) (C : Finset ι) :
    ∑ V ∈ C.image val, cntV val C V = C.card := by
  unfold cntV
  exact (Finset.card_eq_sum_card_image val C).symm

lemma band_card_lt {val : ι → Mat} {C : Finset ι} (k : ℕ) (hne : (band val C k).Nonempty) :
    (band val C k).card < 2 ^ (2 ^ k) := by
  have hsub : band val C k ⊆ C.image val := Finset.filter_subset _ _
  have hsum : ∑ V ∈ band val C k, cntV val C V ≤ C.card := by
    rw [← sum_cntV val C]
    exact Finset.sum_le_sum_of_subset hsub
  have hC : 0 < C.card := by
    obtain ⟨V, hV⟩ := hne
    obtain ⟨j, hj, _⟩ := Finset.mem_image.1 (hsub hV)
    exact Finset.card_pos.2 ⟨j, hj⟩
  have hlt : (band val C k).card * C.card < (band val C k).card * C.card + 1 := by omega
  by_contra hcon
  push Not at hcon
  have : (band val C k).card * C.card < ∑ V ∈ band val C k, cntV val C V * 2 ^ (2 ^ k) := by
    calc (band val C k).card * C.card = ∑ _V ∈ band val C k, C.card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ < ∑ V ∈ band val C k, cntV val C V * 2 ^ (2 ^ k) :=
          Finset.sum_lt_sum_of_nonempty hne fun V hV => (Finset.mem_filter.1 hV).2.1
  rw [← Finset.sum_mul] at this
  have := Nat.mul_le_mul_right C.card hcon
  have h3 := Nat.mul_le_mul_right (2 ^ (2 ^ k)) hsum
  nlinarith

end Bands

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

set_option synthInstance.maxSize 1000

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

section Seq

variable {Q R : Type} {ι : Type} [LinearOrder ι]

/-- A slice: how matrix queries to the slice are answered by base queries, and the slice
values of the candidates. -/
structure SliceData (Q R F : Type) (n : ℕ) (ι : Type) where
  φ : MQ F n → Q
  ψ : MQ F n → R → Vec F n
  val : ι → Matrix (Fin n) (Fin n) F

/-- The values of band `k`, listed. -/
noncomputable def bandList (d : SliceData Q R F n ι) (C : Finset ι) (k : ℕ) :
    Fin (band d.val C k).card → Matrix (Fin n) (Fin n) F :=
  fun i => ((band d.val C k).equivFin.symm i : Matrix (Fin n) (Fin n) F)

lemma bandList_mem (d : SliceData Q R F n ι) (C : Finset ι) (k : ℕ) (i) :
    bandList d C k i ∈ band d.val C k := ((band d.val C k).equivFin.symm i).2

lemma exists_bandList (d : SliceData Q R F n ι) (C : Finset ι) (k : ℕ) {V}
    (hV : V ∈ band d.val C k) : ∃ i, bandList d C k i = V :=
  ⟨(band d.val C k).equivFin ⟨V, hV⟩, by simp [bandList]⟩

/-- Try the bands `k, k+1, …` (with `fuel` levels left). -/
noncomputable def bandLoop (ε' : ℝ) (d : SliceData Q R F n ι) (C : Finset ι) :
    ℕ → ℕ → CAlg Q R (Option (Matrix (Fin n) (Fin n) F))
  | _, 0 => ret none
  | k, fuel + 1 => (mapQ d.φ d.ψ (matId (bandList d C k) ε')).bind fun o =>
      match o with
      | some idx => ret (some (bandList d C k idx))
      | none => bandLoop ε' d C (k + 1) fuel

/-- Sequential identification of the slices. -/
noncomputable def seqId (ε' : ℝ) (kmax : ℕ) :
    List (SliceData Q R F n ι) → Finset ι → CAlg Q R (Option ι)
  | [], C => ret (if h : C.Nonempty then some (C.min' h) else none)
  | d :: rest, C => (bandLoop ε' d C 0 (kmax + 1)).bind fun o =>
      match o with
      | none => ret none
      | some V => seqId ε' kmax rest (C.filter fun j => d.val j = V)

theorem bandLoop_correct (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (ans : Q → R)
    (d : SliceData Q R F n ι) (C : Finset ι) (V : Matrix (Fin n) (Fin n) F)
    (hans : ∀ mq, d.ψ mq (ans (d.φ mq)) = MQ.ans V mq) (kst : ℕ) (hkst : V ∈ band d.val C kst) :
    ∀ fuel k, k ≤ kst → kst < k + fuel →
      1 - ((kst + 1 - k : ℕ) : ℝ) * ε' ≤ (bandLoop ε' d C k fuel).prob ans (fun o => o = some V) := by
  have hans' : (fun q => d.ψ q (ans (d.φ q))) = MQ.ans V := funext hans
  intro fuel
  induction fuel with
  | zero => intro k _ h; omega
  | succ fuel ih =>
    intro k hk hlt
    simp only [bandLoop]
    rcases Nat.lt_or_ge k kst with hk' | hk'
    · -- the true value is not in band k: reject, then continue
      have hnot : ∀ idx, bandList d C k idx ≠ V := by
        intro idx h
        exact band_disjoint hk' (h ▸ bandList_mem d C k idx) hkst
      have h1 : 1 - ε' / 4 ≤ (mapQ d.φ d.ψ (matId (bandList d C k) ε')).prob ans
          (fun o => o = none) := by
        rw [prob_mapQ, hans']
        have := matId_reject (bandList d C k) ε' hε' V hnot
        rw [prob_compl] at this
        have e : (fun o : Option (Fin (band d.val C k).card) => ¬ (o ≠ none)) =
            fun o => o = none := by funext o; simp
        rw [e] at this
        linarith
      have h2 := ih (k + 1) (by omega) (by omega)
      have e : ((kst + 1 - k : ℕ) : ℝ) = ((kst + 1 - (k + 1) : ℕ) : ℝ) + 1 := by
        rw [show kst + 1 - k = (kst + 1 - (k + 1)) + 1 by omega]; push_cast; ring
      by_cases hbig : 1 ≤ ((kst + 1 - k : ℕ) : ℝ) * ε'
      · exact le_trans (by linarith) (prob_nonneg _ _ _)
      push Not at hbig
      have := prob_bind_ge ans _ (fun o => match o with
          | some idx => ret (some (bandList d C k idx))
          | none => bandLoop ε' d C (k + 1) fuel) (fun o => o = none) (fun o => o = some V)
        (ε' / 4) ((kst + 1 - (k + 1) : ℕ) * ε') h1 (fun o ho => by subst ho; exact h2)
        (by positivity) (by rw [e] at hbig; nlinarith)
      refine le_trans ?_ this
      rw [e]; nlinarith
    · have hkk : k = kst := le_antisymm hk hk'
      subst hkk
      obtain ⟨idx, hidx⟩ := exists_bandList d C k hkst
      have h1 : 1 - ε' / 2 ≤ (mapQ d.φ d.ψ (matId (bandList d C k) ε')).prob ans
          (fun o => ∃ j, o = some j ∧ bandList d C k j = V) := by
        rw [prob_mapQ, hans']
        exact matId_found (bandList d C k) ε' hε' hε1 V idx hidx
      have := prob_bind_ge ans _ (fun o => match o with
          | some idx => ret (some (bandList d C k idx))
          | none => bandLoop ε' d C (k + 1) fuel)
        (fun o => ∃ j, o = some j ∧ bandList d C k j = V)
        (fun o => o = some V) (ε' / 2) 0 h1 (fun o ho => by
          obtain ⟨j, rfl, hj⟩ := ho
          rw [prob_of_allOut]
          · norm_num
          · show some (bandList d C k j) = some V; rw [hj]) (le_refl 0) (by norm_num)
      refine le_trans ?_ this
      have e : ((k + 1 - k : ℕ) : ℝ) = 1 := by rw [show k + 1 - k = 1 by omega]; norm_num
      rw [e]; linarith

theorem seqId_correct (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (kmax : ℕ) (ans : Q → R) (i : ι) :
    ∀ (ds : List (SliceData Q R F n ι)) (C : Finset ι), i ∈ C → C.card < 2 ^ (2 ^ kmax) →
      (∀ d ∈ ds, ∀ mq, d.ψ mq (ans (d.φ mq)) = MQ.ans (d.val i) mq) →
      1 - ((ds.length * (kmax + 1) : ℕ) : ℝ) * ε' ≤ (seqId ε' kmax ds C).prob ans
        (fun o => ∃ j, o = some j ∧ j ∈ C ∧ ∀ d ∈ ds, d.val j = d.val i) := by
  intro ds
  induction ds with
  | nil =>
    intro C hi _ _
    have hne : C.Nonempty := ⟨i, hi⟩
    simp only [seqId, List.length_nil, zero_mul, Nat.cast_zero, zero_mul, sub_zero]
    rw [prob_of_allOut]
    show ∃ j, (if h : C.Nonempty then some (C.min' h) else none) = some j ∧ j ∈ C ∧ _
    rw [dif_pos hne]
    exact ⟨_, rfl, C.min'_mem hne, fun d hd => by simp at hd⟩
  | cons d rest ih =>
    intro C hi hcard hans
    have hV : d.val i ∈ C.image d.val := Finset.mem_image_of_mem _ hi
    obtain ⟨kst, hkst, hband⟩ := exists_band hV hcard
    have h1 := bandLoop_correct ε' hε' hε1 ans d C (d.val i) (hans d (List.mem_cons_self))
      kst hband (kmax + 1) 0 (Nat.zero_le _) (by omega)
    have h1' : 1 - ((kmax + 1 : ℕ) : ℝ) * ε' ≤ (bandLoop ε' d C 0 (kmax + 1)).prob ans
        (fun o => o = some (d.val i)) := by
      refine le_trans ?_ h1
      have : ((kst + 1 - 0 : ℕ) : ℝ) ≤ ((kmax + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show kst + 1 - 0 ≤ kmax + 1 by omega)
      nlinarith
    set C' := C.filter fun j => d.val j = d.val i
    have hi' : i ∈ C' := Finset.mem_filter.2 ⟨hi, rfl⟩
    have hcard' : C'.card < 2 ^ (2 ^ kmax) := lt_of_le_of_lt (Finset.card_filter_le _ _) hcard
    have h2 := ih C' hi' hcard' (fun d' hd' => hans d' (List.mem_cons_of_mem _ hd'))
    by_cases hbig : 1 ≤ (((d :: rest).length * (kmax + 1) : ℕ) : ℝ) * ε'
    · exact le_trans (by linarith) (prob_nonneg _ _ _)
    push Not at hbig
    have elen : (((d :: rest).length * (kmax + 1) : ℕ) : ℝ) =
        ((kmax + 1 : ℕ) : ℝ) + ((rest.length * (kmax + 1) : ℕ) : ℝ) := by
      simp only [List.length_cons]; push_cast; ring
    have := prob_bind_ge ans _ (fun o => match o with
        | none => ret none
        | some V => seqId ε' kmax rest (C.filter fun j => d.val j = V))
      (fun o => o = some (d.val i))
      (fun o => ∃ j, o = some j ∧ j ∈ C ∧ ∀ d' ∈ d :: rest, d'.val j = d'.val i)
      (((kmax + 1 : ℕ) : ℝ) * ε') (((rest.length * (kmax + 1) : ℕ) : ℝ) * ε') h1'
      (fun o ho => by
        subst ho
        refine le_trans h2 (prob_mono _ _ fun o' ho' => ?_)
        obtain ⟨j, hj, hjC, hjd⟩ := ho'
        have hjC' := Finset.mem_filter.1 hjC
        refine ⟨j, hj, hjC'.1, fun d' hd' => ?_⟩
        rcases List.mem_cons.1 hd' with h | h
        · subst h; exact hjC'.2
        · exact hjd d' h)
      (by positivity) (by rw [elen] at hbig; nlinarith)
    refine le_trans ?_ this
    rw [elen]; linarith


/-! ### Cost of the sequential identification -/

section generic
variable {α β γ : Type}

theorem bind_assoc' (A : CAlg Q R α) (f : α → CAlg Q R β) (g : β → CAlg Q R γ) :
    (A.bind f).bind g = A.bind (fun a => (f a).bind g) := by
  induction A with
  | ret a => rfl
  | coin m w hw next ih => simp only [CAlg.bind, ih]
  | query q next ih => simp only [CAlg.bind, ih]

theorem cost_bind_le_real (ans : Q → R) (A : CAlg Q R α) (k : α → CAlg Q R β) (c : ℝ)
    (hc : 0 ≤ c) (hk : ∀ a, ((k a).cost ans : ℝ) ≤ c) :
    ((A.bind k).cost ans : ℝ) ≤ A.cost ans + c := by
  have h := cost_bind_le ans A k ⌊c⌋₊ (allOut_of_forall _ _ fun a =>
    Nat.le_floor (hk a))
  have := Nat.floor_le hc
  have h' : ((A.bind k).cost ans : ℝ) ≤ ((A.cost ans + ⌊c⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'; linarith

end generic

lemma sqrt_add_sqrt_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt a + Real.sqrt (c * b) ≤ Real.sqrt ((c + 1) * (a + b)) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt (mul_nonneg hc hb)
  have h3 : Real.sqrt a * Real.sqrt (c * b) = Real.sqrt (c * a) * Real.sqrt b := by
    rw [← Real.sqrt_mul ha, ← Real.sqrt_mul (mul_nonneg hc ha)]; ring_nf
  have h4 := Real.sq_sqrt (mul_nonneg hc ha)
  have h5 := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt (c * a) - Real.sqrt b)]

lemma sum_sqrt_two_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), Real.sqrt (2 ^ j) ≤ 4 * Real.sqrt (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e : Real.sqrt (2 ^ (k + 1)) = Real.sqrt 2 * Real.sqrt (2 ^ k) := by
      rw [pow_succ, Real.sqrt_mul (by positivity), mul_comm]
    have hs2 : (4 : ℝ) ≤ 3 * Real.sqrt 2 := by
      rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      rw [show (3 : ℝ) * Real.sqrt 2 = Real.sqrt 18 by
        rw [show (18 : ℝ) = 3 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [e]
    have := Real.sqrt_nonneg (2 ^ k)
    nlinarith

/-- Per-level additive constant. -/
noncomputable def cK1 (ε' : ℝ) : ℝ := 4 * Real.logb 2 (1 / ε') + 20
/-- Cost spent on levels `0, …, k-1`. -/
noncomputable def cS (ε' : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (3 * Real.sqrt (2 ^ j) + cK1 ε')
/-- Potential bound. -/
noncomputable def cPhi (ε' : ℝ) (kmax m N : ℕ) : ℝ :=
  17 * Real.sqrt (m * Real.logb 2 N) + m * (12 + (kmax + 1) * cK1 ε') + cS ε' (kmax + 1)

lemma cK1_nonneg (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) : 0 ≤ cK1 ε' := by
  unfold cK1; have := logb_inv_nonneg ε' hε' hε1; linarith

lemma cS_nonneg (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (k : ℕ) : 0 ≤ cS ε' k :=
  Finset.sum_nonneg fun j _ => by have := cK1_nonneg ε' hε' hε1; positivity

lemma cS_succ_le (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (k : ℕ) :
    cS ε' (k + 1) ≤ 12 * Real.sqrt (2 ^ k) + (k + 1) * cK1 ε' := by
  unfold cS
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have := sum_sqrt_two_pow k
  push_cast; linarith

lemma level_cost (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (ans : Q → R)
    (d : SliceData Q R F n ι) (C : Finset ι) (k : ℕ) :
    ((mapQ d.φ d.ψ (matId (bandList d C k) ε')).cost ans : ℝ) ≤
      3 * Real.sqrt (2 ^ k) + cK1 ε' := by
  rw [cost_mapQ]
  have h1 := cost_matId (bandList d C k) ε' (fun q => d.ψ q (ans (d.φ q)))
  have h2 := matId_cost_real (band d.val C k).card ε' hε' hε1
  have h3 : Real.logb 2 (band d.val C k).card ≤ 2 ^ k := by
    rcases Finset.eq_empty_or_nonempty (band d.val C k) with h | h
    · rw [h]; simp
    · have hlt := band_card_lt k h
      have hpos : (0 : ℝ) < (band d.val C k).card := by exact_mod_cast h.card_pos
      rw [Real.logb_le_iff_le_rpow (by norm_num) hpos]
      have : ((band d.val C k).card : ℝ) ≤ (2 : ℝ) ^ (2 ^ k : ℕ) := by exact_mod_cast hlt.le
      calc ((band d.val C k).card : ℝ) ≤ (2 : ℝ) ^ (2 ^ k : ℕ) := this
        _ = (2 : ℝ) ^ ((2 : ℝ) ^ k) := by rw [← Real.rpow_natCast]; push_cast; ring_nf
  have h4 : Real.sqrt (Real.logb 2 (band d.val C k).card) ≤ Real.sqrt (2 ^ k) :=
    Real.sqrt_le_sqrt h3
  have : ((matId (bandList d C k) ε').cost (fun q => d.ψ q (ans (d.φ q))) : ℝ) ≤
      ((mk1 (band d.val C k).card ε' + 2 * mm1 (band d.val C k).card ε' + mm3 ε' : ℕ) : ℝ) := by
    exact_mod_cast h1
  unfold cK1; linarith

/-- The band inequality: what is spent on the levels up to `k` plus the remaining potential
fits in the potential. -/
lemma band_step (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (kmax m : ℕ)
    (d : SliceData Q R F n ι) (C : Finset ι) (k : ℕ) (hk : k ≤ kmax)
    (V : Matrix (Fin n) (Fin n) F) (hV : V ∈ band d.val C k) :
    cS ε' (k + 1) + cPhi ε' kmax m (cntV d.val C V) ≤ cPhi ε' kmax (m + 1) C.card := by
  have hVi := (Finset.mem_filter.1 hV)
  have hc := cntV_pos hVi.1
  have hcN : cntV d.val C V ≤ C.card := Finset.card_filter_le _ _
  set N := C.card
  set c := cntV d.val C V
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  set b := Real.logb 2 c
  set a := Real.logb 2 N - b
  have hb0 : 0 ≤ b := Real.logb_nonneg (by norm_num) hc1
  have ha0 : 0 ≤ a := by
    have : Real.logb 2 c ≤ Real.logb 2 N :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by exact_mod_cast hcN)
    simp only [a, b]; linarith
  have hK1 := cK1_nonneg ε' hε' hε1
  -- 12 √(2^k) ≤ 17 √a + 12
  have hsq : 12 * Real.sqrt (2 ^ k) ≤ 17 * Real.sqrt a + 12 := by
    rcases Nat.eq_zero_or_pos k with h0 | hkpos
    · subst h0
      simp only [pow_zero, Real.sqrt_one]
      have := Real.sqrt_nonneg a; linarith
    · have hband := hVi.2.2
      rcases hband with h | h
      · omega
      have h' : (c : ℝ) * 2 ^ (2 ^ (k - 1) : ℕ) ≤ N := by exact_mod_cast h
      have hlog : (2 : ℝ) ^ (k - 1) ≤ a := by
        have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h'
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)] at this
        simp only [a, b]; push_cast at this; linarith
      have h2k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      have : Real.sqrt (2 ^ k) ≤ Real.sqrt 2 * Real.sqrt a := by
        rw [← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by rw [h2k]; linarith)
      have hs2 : 12 * Real.sqrt 2 ≤ 17 := by
        rw [show (17 : ℝ) = Real.sqrt (17 ^ 2) by rw [Real.sqrt_sq (by norm_num)],
          show (12 : ℝ) * Real.sqrt 2 = Real.sqrt (12 ^ 2 * 2) by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have := Real.sqrt_nonneg a
      nlinarith
  have hS := cS_succ_le ε' hε' hε1 k
  have hkk : ((k : ℝ) + 1) * cK1 ε' ≤ ((kmax : ℝ) + 1) * cK1 ε' := by
    have : (k : ℝ) ≤ kmax := by exact_mod_cast hk
    nlinarith
  have hsqrt := sqrt_add_sqrt_le a b m ha0 hb0 (by positivity)
  unfold cPhi
  have e : Real.logb 2 N = a + b := by simp only [a]; ring
  rw [e]
  push_cast
  have : ((m : ℝ) + 1) * (a + b) = ((m : ℝ) + 1) * (a + b) := rfl
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg (m * b)]

theorem seqId_cost (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (kmax : ℕ) (ans : Q → R) :
    ∀ (ds : List (SliceData Q R F n ι)) (C : Finset ι),
      ((seqId ε' kmax ds C).cost ans : ℝ) ≤ cPhi ε' kmax ds.length C.card := by
  have hK1 := cK1_nonneg ε' hε' hε1
  intro ds
  induction ds with
  | nil =>
    intro C
    simp only [seqId, cost, Nat.cast_zero, List.length_nil]
    unfold cPhi
    have := cS_nonneg ε' hε' hε1 (kmax + 1)
    simp
    linarith
  | cons d rest ih =>
    intro C
    simp only [seqId, List.length_cons]
    set cont : Option (Matrix (Fin n) (Fin n) F) → CAlg Q R (Option ι) := fun o => match o with
      | none => ret none
      | some V => seqId ε' kmax rest (C.filter fun j => d.val j = V)
    have main : ∀ fuel k, k + fuel = kmax + 1 →
        cS ε' k + ((bandLoop ε' d C k fuel).bind cont).cost ans ≤
          cPhi ε' kmax (rest.length + 1) C.card := by
      intro fuel
      induction fuel with
      | zero =>
        intro k hk
        simp only [bandLoop, CAlg.bind, cont, CAlg.cost, Nat.cast_zero, add_zero]
        rw [show k = kmax + 1 by omega]
        unfold cPhi
        push_cast
        have := Real.sqrt_nonneg (((rest.length : ℝ) + 1) * Real.logb 2 C.card)
        have h1 : 0 ≤ ((rest.length : ℝ) + 1) * (12 + ((kmax : ℝ) + 1) * cK1 ε') := by positivity
        linarith
      | succ fuel ihf =>
        intro k hk
        have hk' : k ≤ kmax := by omega
        simp only [bandLoop]
        rw [bind_assoc']
        have hnone := ihf (k + 1) (by omega)
        have hcostnn : (0 : ℝ) ≤ (((bandLoop ε' d C (k + 1) fuel).bind cont).cost ans : ℝ) :=
          Nat.cast_nonneg _
        have hSk : cS ε' (k + 1) = cS ε' k + (3 * Real.sqrt (2 ^ k) + cK1 ε') := by
          unfold cS; rw [Finset.sum_range_succ]
        have hlev := level_cost ε' hε' hε1 ans d C k
        set c0 := cPhi ε' kmax (rest.length + 1) C.card - cS ε' (k + 1)
        have hc0 : 0 ≤ c0 := by simp only [c0]; linarith
        have hb := cost_bind_le_real ans (mapQ d.φ d.ψ (matId (bandList d C k) ε'))
          (fun o => (match o with
            | some idx => ret (some (bandList d C k idx))
            | none => bandLoop ε' d C (k + 1) fuel).bind cont) c0 hc0 (fun o => ?_)
        · linarith
        · rcases o with _ | idx
          · show (((bandLoop ε' d C (k + 1) fuel).bind cont).cost ans : ℝ) ≤ c0
            simp only [c0]; linarith
          · show ((seqId ε' kmax rest (C.filter fun j => d.val j = bandList d C k idx)).cost ans
              : ℝ) ≤ c0
            have h1 := ih (C.filter fun j => d.val j = bandList d C k idx)
            have h2 := band_step ε' hε' hε1 kmax rest.length d C k hk' (bandList d C k idx)
              (bandList_mem d C k idx)
            simp only [c0]
            unfold cntV at h2
            linarith
    have := main (kmax + 1) 0 (by omega)
    have h0 : cS ε' 0 = 0 := by simp [cS]
    rw [h0, zero_add] at this
    exact this

end Seq

end TriFormQ.W

end


-- ===== Solutions/W_Base.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Uniformity of random affine combinations -/

/-- The point `v₀ + Σ c_k h_k`. -/
def phiA {d : ℕ} (v0 : Vec F n) (h : Fin d → Vec F n) (c : Fin d → F) : Vec F n :=
  v0 + ∑ k, c k • h k

lemma sum_translate (f : Vec F n → ℝ) (w : Vec F n) :
    ∑ v0 : Vec F n, f (v0 + w) = ∑ v, f v :=
  Fintype.sum_equiv (Equiv.addRight w) _ _ (fun _ => rfl)

/-- A single random affine combination is uniform. -/
lemma single_sum {d : ℕ} (c : Fin d → F) (f : Vec F n → ℝ) :
    ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n, f (phiA v0 h c) =
      (Fintype.card F : ℝ) ^ (n * d) * ∑ v, f v := by
  rw [Finset.sum_comm]
  simp only [phiA, sum_translate]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Fintype.card_fun, Fintype.card_fin, card_vec]; push_cast; ring

/-- A 2×2 change of variables `(v₀, x) ↦ (v₀ + α x + R, v₀ + β x + R')` with `α ≠ β`. -/
def affPairEquiv (α β : F) (hαβ : α ≠ β) (R R' : Vec F n) : Vec F n × Vec F n ≃ Vec F n × Vec F n
    where
  toFun p := (p.1 + α • p.2 + R, p.1 + β • p.2 + R')
  invFun q := (q.1 - R - α • ((β - α)⁻¹ • ((q.2 - R') - (q.1 - R))),
    (β - α)⁻¹ • ((q.2 - R') - (q.1 - R)))
  left_inv p := by
    have h : β - α ≠ 0 := sub_ne_zero.2 (Ne.symm hαβ)
    ext i <;> simp <;> field_simp <;> ring
  right_inv q := by
    have h : β - α ≠ 0 := sub_ne_zero.2 (Ne.symm hαβ)
    ext i <;> simp <;> field_simp <;> ring

lemma sum_split_at {d : ℕ} (c : Fin d → F) (k0 : Fin d) (x : Vec F n)
    (r : {j // j ≠ k0} → Vec F n) :
    ∑ k, c k • (Equiv.funSplitAt k0 (Vec F n)).symm (x, r) k =
      c k0 • x + ∑ j : {j // j ≠ k0}, c j • r j := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ k0]
  congr 1
  · simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]

/-- Two distinct random affine combinations are independent and uniform. -/
lemma pair_sum {d : ℕ} (c c' : Fin d → F) (hcc : c ≠ c') (G : Vec F n → Vec F n → ℝ) :
    ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n, G (phiA v0 h c) (phiA v0 h c') =
      (Fintype.card F : ℝ) ^ (n * (d - 1)) * ∑ a, ∑ b, G a b := by
  obtain ⟨k0, hk0⟩ : ∃ k0, c k0 ≠ c' k0 := Function.ne_iff.1 hcc
  rw [Finset.sum_comm]
  rw [← (Equiv.funSplitAt k0 (Vec F n)).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have key : ∀ r : {j // j ≠ k0} → Vec F n,
      ∑ x : Vec F n, ∑ v0 : Vec F n,
        G (phiA v0 ((Equiv.funSplitAt k0 (Vec F n)).symm (x, r)) c)
          (phiA v0 ((Equiv.funSplitAt k0 (Vec F n)).symm (x, r)) c') = ∑ a, ∑ b, G a b := by
    intro r
    simp only [phiA, sum_split_at]
    rw [Finset.sum_comm, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (affPairEquiv (c k0) (c' k0) hk0
      (∑ j : {j // j ≠ k0}, c j • r j) (∑ j : {j // j ≠ k0}, c' j • r j)) _ _ (fun p => ?_)
    simp only [affPairEquiv, Equiv.coe_fn_mk]
    congr 1 <;> abel
  simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Fintype.card_fun, card_vec]
  simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  push_cast
  rw [← pow_mul]

/-! ### Fibers -/

/-- The probe kernel `K(v, ws) = {u : f(u, v, w_i) = 0 ∀ i}`. -/
def Kset (D : TriForm F n) (v : Vec F n) {e : ℕ} (ws : Fin e → Vec F n) : Finset (Vec F n) :=
  Finset.univ.filter fun u => ∀ i, TriForm.eval D u v (ws i) = 0

lemma fiber_subset_Kset (D : TriForm F n) (v : Vec F n) {e : ℕ} (ws : Fin e → Vec F n) :
    fiber D v ⊆ Kset D v ws := by
  intro u hu
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => hu _⟩

lemma card_Kset_le (D : TriForm F n) (v : Vec F n) {e : ℕ} (ws : Fin e → Vec F n) :
    (Kset D v ws).card ≤ Fintype.card F ^ n := by
  rw [← card_vec]; exact Finset.card_le_univ _

lemma zeroLocus_card_eq_sum (D : TriForm F n) :
    (zeroLocus D).card = ∑ v, (fiber D v).card := by
  rw [zeroLocus, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [fiber, Finset.card_filter]

/-- Number of `w` with `f(u, v, w) = 0`. -/
lemma card_w_zero (D : TriForm F n) (u v : Vec F n) :
    ((Finset.univ.filter fun w : Vec F n => TriForm.eval D u v w = 0).card : ℝ) ≤
      if u ∈ fiber D v then (Fintype.card F : ℝ) ^ n else (Fintype.card F : ℝ) ^ n /
        Fintype.card F := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  split_ifs with hu
  · have := Finset.card_le_univ (Finset.univ.filter fun w : Vec F n => TriForm.eval D u v w = 0)
    rw [card_vec] at this; exact_mod_cast this
  · rw [le_div_iff₀ hq]
    have hne : CQ.ans D (.xy u v) ≠ 0 := by
      intro h; apply hu
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (ans_xy_eq_zero_iff D u v).1 h
    let f : Vec F n →ₗ[F] F :=
      { toFun := fun w => CQ.ans D (.xy u v) ⬝ᵥ w, map_add' := fun a b => dotProduct_add _ a b,
        map_smul' := fun c a => dotProduct_smul c _ a }
    have hP : LinearMap.ker f ≠ ⊤ := by
      intro htop; apply hne
      exact vec_eq_zero_of_dot _ fun z => by
        have : z ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
        simpa [f] using this
    have := card_proper_le (LinearMap.ker f) hP
    have e : (Finset.univ.filter fun w : Vec F n => TriForm.eval D u v w = 0) =
        Finset.univ.filter (· ∈ LinearMap.ker f) := by
      ext w; simp [f, eval_xy]
    rw [e]; exact_mod_cast this

/-- Average size of the probe kernel. -/
lemma sum_Kset_le (D : TriForm F n) (e : ℕ) :
    ∑ ws : Fin e → Vec F n, ∑ a : Vec F n, ((Kset D a ws).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (n * e) * (zeroLocus D).card +
        (Fintype.card F : ℝ) ^ (2 * n) * ((Fintype.card F : ℝ) ^ n / Fintype.card F) ^ e := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_comm]
  -- Σ_a Σ_ws |K| = Σ_a Σ_u #{w : f(u,a,w)=0}^e
  have h1 : ∀ a : Vec F n, ∑ ws : Fin e → Vec F n, ((Kset D a ws).card : ℝ) =
      ∑ u : Vec F n, ((Finset.univ.filter fun w : Vec F n => TriForm.eval D u a w = 0).card
        : ℝ) ^ e := by
    intro a
    simp only [Kset, Finset.card_filter]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    have := card_all_mem (k := e) (Finset.univ.filter fun w : Vec F n => TriForm.eval D u a w = 0)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    rw [Finset.sum_boole, Finset.sum_boole]
    exact_mod_cast this
  simp only [h1]
  have h2 : ∀ a u : Vec F n, ((Finset.univ.filter fun w : Vec F n => TriForm.eval D u a w = 0).card
      : ℝ) ^ e ≤ (if u ∈ fiber D a then (Fintype.card F : ℝ) ^ (n * e) else 0) +
        ((Fintype.card F : ℝ) ^ n / Fintype.card F) ^ e := by
    intro a u
    have h := card_w_zero D u a
    split_ifs at h ⊢ with hu
    · rw [pow_mul]
      have : ((Finset.univ.filter fun w : Vec F n => TriForm.eval D u a w = 0).card : ℝ) ^ e ≤
          ((Fintype.card F : ℝ) ^ n) ^ e := pow_le_pow_left₀ (by positivity) h e
      have : (0 : ℝ) ≤ ((Fintype.card F : ℝ) ^ n / Fintype.card F) ^ e := by positivity
      linarith
    · simp only [zero_add]; exact pow_le_pow_left₀ (by positivity) h e
  calc ∑ a : Vec F n, ∑ u : Vec F n,
        ((Finset.univ.filter fun w : Vec F n => TriForm.eval D u a w = 0).card : ℝ) ^ e
      ≤ ∑ a : Vec F n, ∑ u : Vec F n, ((if u ∈ fiber D a then (Fintype.card F : ℝ) ^ (n * e)
          else 0) + ((Fintype.card F : ℝ) ^ n / Fintype.card F) ^ e) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun u _ => h2 a u
    _ = (Fintype.card F : ℝ) ^ (n * e) * (zeroLocus D).card +
        (Fintype.card F : ℝ) ^ (2 * n) * ((Fintype.card F : ℝ) ^ n / Fintype.card F) ^ e := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, zeroLocus_card_eq_sum]
        rw [card_vec, ← Finset.sum_mul]
        push_cast
        ring

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Good base points (Definition 2, with an upper bound `ρ` in place of `AR`) -/

/-- Good set: large fiber and small average `q^{rk f[u]}` on the fiber. -/
noncomputable def goodS (D : TriForm F n) (ρ : ℝ) : Finset (Vec F n) :=
  Finset.univ.filter fun v =>
    (Fintype.card F : ℝ) ^ n ≤ 8 * (Fintype.card F : ℝ) ^ ρ * (fiber D v).card ∧
    ∑ u ∈ fiber D v, (Fintype.card F : ℝ) ^ (sliceU D u).rank ≤
      8 * (Fintype.card F : ℝ) ^ ρ * (fiber D v).card

lemma eval_sub_left (D : TriForm F n) (u a v w : Vec F n) :
    TriForm.eval D (u - a) v w = TriForm.eval D u v w - TriForm.eval D a v w := by
  simp [TriForm.eval, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma mem_fiber (D : TriForm F n) (u v : Vec F n) :
    u ∈ fiber D v ↔ ∀ w, TriForm.eval D u v w = 0 := by simp [fiber]

lemma card_v_fiber (D : TriForm F n) (u : Vec F n) :
    (Finset.univ.filter fun v : Vec F n => u ∈ fiber D v).card =
      Fintype.card F ^ (n - (sliceU D u).rank) := by
  rw [← card_ker_vecMul]
  congr 1; ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_fiber]
  constructor
  · intro h; apply vec_eq_zero_of_dot; intro w
    have := h w; rw [eval_sliceU, dotProduct_mulVec] at this; exact this
  · intro h w; rw [eval_sliceU, dotProduct_mulVec, h, zero_dotProduct]

lemma sum_fiber_qrank (D : TriForm F n) :
    ∑ v : Vec F n, ∑ u ∈ fiber D v, (Fintype.card F : ℝ) ^ (sliceU D u).rank =
      (Fintype.card F : ℝ) ^ (2 * n) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [show (∑ v : Vec F n, ∑ u ∈ fiber D v, (Fintype.card F : ℝ) ^ (sliceU D u).rank) =
      ∑ v : Vec F n, ∑ u : Vec F n, if u ∈ fiber D v then
        (Fintype.card F : ℝ) ^ (sliceU D u).rank else 0 by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter]]
  rw [Finset.sum_comm]
  have : ∀ u : Vec F n, ∑ v : Vec F n, (if u ∈ fiber D v then
      (Fintype.card F : ℝ) ^ (sliceU D u).rank else 0) = (Fintype.card F : ℝ) ^ n := by
    intro u
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_v_fiber]
    push_cast
    rw [← pow_add]
    have := Matrix.rank_le_width (sliceU D u)
    congr 1; omega
  simp only [this, Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul]
  push_cast; ring

/-- Fact 1 (counting form): good base points carry at least `3/4` of the fiber mass. -/
theorem fact1' (D : TriForm F n) (ρ : ℝ)
    (hAR : (Fintype.card F : ℝ) ^ (2 * n) ≤ (Fintype.card F : ℝ) ^ ρ * (zeroLocus D).card) :
    (3 / 4 : ℝ) * (zeroLocus D).card ≤ ∑ v ∈ goodS D ρ, ((fiber D v).card : ℝ) := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  set Q := (Fintype.card F : ℝ) ^ ρ with hQ
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hq ρ
  have hpt : ∀ v : Vec F n, ((fiber D v).card : ℝ) ≤
      (if v ∈ goodS D ρ then ((fiber D v).card : ℝ) else 0) +
        (Fintype.card F : ℝ) ^ n / (8 * Q) +
        (∑ u ∈ fiber D v, (Fintype.card F : ℝ) ^ (sliceU D u).rank) / (8 * Q) := by
    intro v
    have h1 : 0 ≤ (Fintype.card F : ℝ) ^ n / (8 * Q) := by positivity
    have h2 : 0 ≤ (∑ u ∈ fiber D v, (Fintype.card F : ℝ) ^ (sliceU D u).rank) / (8 * Q) :=
      by positivity
    by_cases hg : v ∈ goodS D ρ
    · rw [if_pos hg]; linarith
    · rw [if_neg hg]
      simp only [goodS, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_le] at hg
      rcases hg with hg | hg
      · have h3 : ((fiber D v).card : ℝ) * (8 * Q) ≤ (Fintype.card F : ℝ) ^ n := by
          rw [hQ]; linarith
        have := (le_div_iff₀ (by positivity : (0:ℝ) < 8 * Q)).2 h3
        linarith
      · have : ((fiber D v).card : ℝ) * (8 * Q) ≤
            ∑ u ∈ fiber D v, (Fintype.card F : ℝ) ^ (sliceU D u).rank := by rw [hQ]; linarith
        have := (le_div_iff₀ (by positivity : (0:ℝ) < 8 * Q)).2 this
        linarith
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ (Finset.univ : Finset (Vec F n))) => hpt v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
    sum_fiber_qrank, Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul,
    ← Finset.sum_filter] at hsum
  have hZ : ((zeroLocus D).card : ℝ) = ∑ v : Vec F n, ((fiber D v).card : ℝ) := by
    rw [zeroLocus_card_eq_sum]; push_cast; rfl
  have hfilt : (Finset.univ.filter fun v => v ∈ goodS D ρ) = goodS D ρ := by
    ext v; simp
  rw [hfilt] at hsum
  have e1 : ((Fintype.card F ^ n : ℕ) : ℝ) * (Fintype.card F : ℝ) ^ n / (8 * Q) =
      (Fintype.card F : ℝ) ^ (2 * n) / (8 * Q) := by
    push_cast; rw [two_mul, pow_add]
  rw [e1] at hsum
  have e2 : (Fintype.card F : ℝ) ^ (2 * n) / (8 * Q) ≤ (zeroLocus D).card / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  rw [← hZ] at hsum
  linarith

/-- Fact 2 (with `t = ⌈ρ⌉ + 5`): on a good fiber every slice has rank at most `2t`. -/
theorem fact2' (D : TriForm F n) (ρ : ℝ) (v : Vec F n) (hv : v ∈ goodS D ρ) (u : Vec F n)
    (hu : u ∈ fiber D v) : (sliceU D u).rank ≤ 2 * (⌈ρ⌉₊ + 5) := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq2 : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast q_ge_two (F := F)
  set t := ⌈ρ⌉₊ + 5
  set Z := fiber D v
  set A := Z.filter fun a => (sliceU D a).rank ≤ t
  have hv2 := (Finset.mem_filter.1 hv).2.2
  -- |Z \ A| q^(t+1) ≤ 8 q^ρ |Z|
  have hbad : ((Z \ A).card : ℝ) * (Fintype.card F : ℝ) ^ (t + 1) ≤
      8 * (Fintype.card F : ℝ) ^ ρ * Z.card := by
    refine le_trans ?_ hv2
    calc ((Z \ A).card : ℝ) * (Fintype.card F : ℝ) ^ (t + 1)
        = ∑ _u ∈ Z \ A, (Fintype.card F : ℝ) ^ (t + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ Z \ A, (Fintype.card F : ℝ) ^ (sliceU D u).rank := by
          refine Finset.sum_le_sum fun a ha => ?_
          have : ¬ (sliceU D a).rank ≤ t := by
            intro h; exact (Finset.mem_sdiff.1 ha).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 ha).1, h⟩)
          exact pow_le_pow_right₀ (by linarith) (by omega)
      _ ≤ ∑ u ∈ Z, (Fintype.card F : ℝ) ^ (sliceU D u).rank :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => by positivity)
  have hqt : 64 * (Fintype.card F : ℝ) ^ ρ ≤ (Fintype.card F : ℝ) ^ (t + 1) := by
    have h6 : (64 : ℝ) ≤ (Fintype.card F : ℝ) ^ (6 : ℕ) := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hq2 6
    have hρ : (Fintype.card F : ℝ) ^ ρ ≤ (Fintype.card F : ℝ) ^ (⌈ρ⌉₊ : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil ρ)
    calc 64 * (Fintype.card F : ℝ) ^ ρ ≤ (Fintype.card F : ℝ) ^ 6 *
          (Fintype.card F : ℝ) ^ (⌈ρ⌉₊ : ℕ) := by
          have := Real.rpow_pos_of_pos hq ρ
          nlinarith
      _ = (Fintype.card F : ℝ) ^ (t + 1) := by rw [← pow_add]; congr 1; omega
  have hZpos : (0 : ℝ) < Z.card := by
    have : (0 : Vec F n) ∈ Z := by rw [mem_fiber]; intro w; simp [TriForm.eval]
    exact_mod_cast Finset.card_pos.2 ⟨0, this⟩
  have hA : Z.card < 2 * A.card := by
    have h1 : ((Z \ A).card : ℝ) * 64 * (Fintype.card F : ℝ) ^ ρ ≤ 8 * (Fintype.card F : ℝ) ^ ρ *
        Z.card := by
      have := Real.rpow_pos_of_pos hq ρ
      nlinarith
    have hρpos := Real.rpow_pos_of_pos hq ρ
    have h2 : ((Z \ A).card : ℝ) * 8 ≤ Z.card := by
      have : ((Z \ A).card : ℝ) * 8 * (8 * (Fintype.card F : ℝ) ^ ρ) ≤
          Z.card * (8 * (Fintype.card F : ℝ) ^ ρ) := by nlinarith
      exact le_of_mul_le_mul_right this (by positivity)
    have h3 : (Z \ A).card + A.card = Z.card := Finset.card_sdiff_add_card_eq_card
      (Finset.filter_subset _ _)
    have h4 : ((Z \ A).card : ℝ) + A.card = Z.card := by exact_mod_cast h3
    have : (Z.card : ℝ) < 2 * A.card := by linarith
    exact_mod_cast this
  -- the translate `u - A` also lies in `Z`
  set B := A.image fun a => u - a
  have hBsub : B ⊆ Z := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    have haZ := (Finset.mem_filter.1 ha).1
    rw [mem_fiber] at hu haZ ⊢
    intro w; rw [eval_sub_left, hu w, haZ w, sub_zero]
  have hBcard : B.card = A.card := Finset.card_image_of_injective _ (sub_right_injective)
  have hinter : (A ∩ B).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have := Finset.card_union_add_card_inter A B
    rw [hne, Finset.card_empty, add_zero] at this
    have hsub : A ∪ B ⊆ Z := Finset.union_subset (Finset.filter_subset _ _) hBsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨a, ha⟩ := hinter
  obtain ⟨haA, haB⟩ := Finset.mem_inter.1 ha
  obtain ⟨a', ha'A, ha'⟩ := Finset.mem_image.1 haB
  have hu' : sliceU D u = sliceU D a + sliceU D a' := by
    rw [← sliceU_add]; congr 1; rw [← ha']; abel
  rw [hu']
  have h1 := (Finset.mem_filter.1 haA).2
  have h2 := (Finset.mem_filter.1 ha'A).2
  have := rank_add_le' (sliceU D a) (sliceU D a')
  omega

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### The base-point ratio estimate -/

/-- Cauchy–Schwarz in the form `(Σ Y)² ≤ (Σ Y/X)(Σ X Y)`. -/
lemma cs_ratio {β : Type} [Fintype β] (X Y : β → ℝ) (hX : ∀ b, 0 < X b) (hY : ∀ b, 0 ≤ Y b) :
    (∑ b, Y b) ^ 2 ≤ (∑ b, Y b / X b) * ∑ b, X b * Y b := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => Real.sqrt (Y b / X b))
    (fun b => Real.sqrt (X b * Y b))
  have e1 : ∀ b, Real.sqrt (Y b / X b) * Real.sqrt (X b * Y b) = Y b := by
    intro b
    rw [← Real.sqrt_mul (div_nonneg (hY b) (hX b).le)]
    rw [show Y b / X b * (X b * Y b) = Y b * Y b by field_simp [(hX b).ne']]
    exact Real.sqrt_mul_self (hY b)
  have e2 : ∀ b, Real.sqrt (Y b / X b) ^ 2 = Y b / X b :=
    fun b => Real.sq_sqrt (div_nonneg (hY b) (hX b).le)
  have e3 : ∀ b, Real.sqrt (X b * Y b) ^ 2 = X b * Y b :=
    fun b => Real.sq_sqrt (mul_nonneg (hX b).le (hY b))
  simp only [e1, e2, e3] at h
  exact h

/-- The fiber mass at good points. -/
noncomputable def gW (D : TriForm F n) (ρ : ℝ) (v : Vec F n) : ℝ :=
  if v ∈ goodS D ρ then ((fiber D v).card : ℝ) else 0

lemma gW_nonneg (D : TriForm F n) (ρ : ℝ) (v : Vec F n) : 0 ≤ gW D ρ v := by
  unfold gW; split_ifs <;> positivity

lemma gW_le (D : TriForm F n) (ρ : ℝ) (v : Vec F n) : gW D ρ v ≤ (Fintype.card F : ℝ) ^ n := by
  unfold gW; split_ifs
  · have := Finset.card_le_univ (fiber D v); rw [card_vec] at this; exact_mod_cast this
  · positivity

lemma sum_gW (D : TriForm F n) (ρ : ℝ) :
    ∑ v, gW D ρ v = ∑ v ∈ goodS D ρ, ((fiber D v).card : ℝ) := by
  unfold gW; rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma base_arith (t1 Rq Zc Sg A E : ℝ) (hRq : 0 < Rq) (hZc : 0 ≤ Zc) (hA : 0 < A) (hE : 0 < E)
    (h1 : t1 ≤ Rq * Zc) (hA16 : 16 * Rq ≤ A) (hE16 : 16 * Rq ≤ E) (hSg : 3 / 4 * Zc ≤ Sg) :
    2 / 3 * (t1 + A * Zc + A * t1 / E) ≤ A * Sg := by
  have h2 : t1 ≤ A * Zc / 16 := by
    rw [le_div_iff₀ (by norm_num)]
    calc t1 * 16 ≤ Rq * Zc * 16 := by linarith
      _ = (16 * Rq) * Zc := by ring
      _ ≤ A * Zc := mul_le_mul_of_nonneg_right hA16 hZc
  have h3 : A * t1 / E ≤ A * Zc / 16 := by
    rw [div_le_div_iff₀ hE (by norm_num)]
    have : t1 * 16 ≤ Zc * E := by
      calc t1 * 16 ≤ Rq * Zc * 16 := by linarith
        _ = (16 * Rq) * Zc := by ring
        _ ≤ E * Zc := mul_le_mul_of_nonneg_right hE16 hZc
        _ = Zc * E := by ring
    calc A * t1 * 16 = A * (t1 * 16) := by ring
      _ ≤ A * (Zc * E) := mul_le_mul_of_nonneg_left this hA.le
      _ = A * Zc * E := by ring
  have h4 : A * (3 / 4 * Zc) ≤ A * Sg := mul_le_mul_of_nonneg_left hSg hA.le
  linarith

lemma base_ident (q P Sg Zc : ℝ) (n d e : ℕ) (hd1 : 1 ≤ d) (hq : 0 < q)
    (hP : P = q ^ (n * d) * q ^ (n * e)) :
    q ^ n * P * (q ^ d * (q ^ n * q ^ (n * e) * q ^ (n * d) * Sg) +
      q ^ d * q ^ d * (q ^ (n * (d - 1)) * (q ^ (n * e) * Zc + q ^ (2 * n) * (q ^ n / q) ^ e)
        * Sg)) =
      q ^ d * P ^ 2 * Sg * (q ^ (2 * n) + q ^ d * Zc + q ^ d * q ^ (2 * n) / q ^ e) := by
  have e1 : q ^ (n * d) = q ^ n * q ^ (n * (d - 1)) := by
    rw [← pow_add]; congr 1
    rw [Nat.mul_sub, mul_one]; have : n ≤ n * d := Nat.le_mul_of_pos_right n hd1; omega
  have e2 : (q ^ n / q) ^ e = q ^ (n * e) / q ^ e := by rw [div_pow, ← pow_mul]
  have e3 : q ^ (2 * n) = q ^ n * q ^ n := by rw [two_mul, pow_add]
  subst hP
  rw [e2, e3, e1]
  have : q ^ e ≠ 0 := by positivity
  field_simp
  ring

theorem base_ratio (D : TriForm F n) (ρ : ℝ)
    (hAR : (Fintype.card F : ℝ) ^ (2 * n) ≤ (Fintype.card F : ℝ) ^ ρ * (zeroLocus D).card)
    (d e : ℕ) (hd : ρ + 4 ≤ d) (he : ρ + 4 ≤ e) :
    (2 / 3 : ℝ) * Fintype.card (Vec F n × (Fin d → Vec F n) × (Fin e → Vec F n)) ≤
      ∑ ω : Vec F n × (Fin d → Vec F n) × (Fin e → Vec F n),
        (∑ c : Fin d → F, ((Kset D (phiA ω.1 ω.2.1 c) ω.2.2).card : ℝ) *
            (if phiA ω.1 ω.2.1 c ∈ goodS D ρ then 1 else 0)) /
          (∑ c : Fin d → F, ((Kset D (phiA ω.1 ω.2.1 c) ω.2.2).card : ℝ)) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq : (0 : ℝ) < q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
  have hq2 : (2 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast q_ge_two (F := F)
  set Ω := Vec F n × (Fin d → Vec F n) × (Fin e → Vec F n)
  let X : Ω → ℝ := fun ω => ∑ c : Fin d → F, ((Kset D (phiA ω.1 ω.2.1 c) ω.2.2).card : ℝ)
  let Y : Ω → ℝ := fun ω => ∑ c : Fin d → F, gW D ρ (phiA ω.1 ω.2.1 c)
  have hX : ∀ ω, 0 < X ω := by
    intro ω
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun c => ((Kset D (phiA ω.1 ω.2.1 c)
      ω.2.2).card : ℝ)) (fun _ _ => by positivity) (Finset.mem_univ 0))
    have : (0 : Vec F n) ∈ Kset D (phiA ω.1 ω.2.1 0) ω.2.2 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => by simp [TriForm.eval]⟩
    exact_mod_cast Finset.card_pos.2 ⟨0, this⟩
  have hY : ∀ ω, 0 ≤ Y ω := fun ω => Finset.sum_nonneg fun c _ => gW_nonneg D ρ _
  -- Ỹ ≥ Y
  have hYt : ∀ ω : Ω, Y ω / X ω ≤
      (∑ c : Fin d → F, ((Kset D (phiA ω.1 ω.2.1 c) ω.2.2).card : ℝ) *
        (if phiA ω.1 ω.2.1 c ∈ goodS D ρ then 1 else 0)) / X ω := by
    intro ω
    refine div_le_div_of_nonneg_right ?_ (hX ω).le
    refine Finset.sum_le_sum fun c _ => ?_
    unfold gW
    split_ifs
    · rw [mul_one]; exact_mod_cast Finset.card_le_card (fiber_subset_Kset D _ _)
    · simp
  -- sums over Ω
  have hsumΩ : ∀ H : Vec F n → (Fin d → Vec F n) → (Fin e → Vec F n) → ℝ,
      ∑ ω : Ω, H ω.1 ω.2.1 ω.2.2 = ∑ v0, ∑ h, ∑ ws, H v0 h ws := by
    intro H; rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type]
  set P : ℝ := q ^ (n * d) * q ^ (n * e)
  set Sg : ℝ := ∑ v, gW D ρ v
  set Zc : ℝ := ((zeroLocus D).card : ℝ)
  have hZc : 1 ≤ Zc := by
    have h := zeroLocus_card_pos D
    have : (1 : ℝ) ≤ ((zeroLocus D).card : ℝ) := by exact_mod_cast h
    exact this
  have hSg : (3 / 4 : ℝ) * Zc ≤ Sg := by
    have := fact1' D ρ hAR; rw [← sum_gW] at this; exact this
  have hcardΩ : (Fintype.card Ω : ℝ) = q ^ n * P := by
    simp only [Ω, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, card_vec, P]
    push_cast; rw [← pow_mul, ← pow_mul]
  have hcardc : (Fintype.card (Fin d → F) : ℝ) = q ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin]; push_cast; rfl
  have hcardws : (Fintype.card (Fin e → Vec F n) : ℝ) = q ^ (n * e) := by
    rw [Fintype.card_fun, Fintype.card_fin, card_vec]; push_cast; rw [← pow_mul]
  -- Σ Y
  have hswap : ∀ f : Vec F n → (Fin d → Vec F n) → (Fin d → F) → ℝ,
      ∑ v0, ∑ h, ∑ c, f v0 h c = ∑ c, ∑ v0, ∑ h, f v0 h c := by
    intro f
    rw [Finset.sum_congr rfl fun v0 _ => Finset.sum_comm]
    exact Finset.sum_comm
  have hSY : ∑ ω : Ω, Y ω = q ^ d * P * Sg := by
    rw [hsumΩ (fun v0 h ws => ∑ c : Fin d → F, gW D ρ (phiA v0 h c))]
    have h1 : ∀ v0 (h : Fin d → Vec F n), ∑ _ws : Fin e → Vec F n, ∑ c : Fin d → F,
        gW D ρ (phiA v0 h c) = q ^ (n * e) * ∑ c, gW D ρ (phiA v0 h c) := by
      intro v0 h; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardws]
    simp only [h1, ← Finset.mul_sum]
    rw [hswap (fun v0 h c => gW D ρ (phiA v0 h c))]
    simp only [single_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardc]
    simp only [P, Sg]; ring
  -- Σ X Y
  set SKb : ℝ := q ^ (n * e) * Zc + q ^ (2 * n) * (q ^ n / q) ^ e
  have hSK : ∑ ws : Fin e → Vec F n, ∑ a : Vec F n, ((Kset D a ws).card : ℝ) ≤ SKb :=
    sum_Kset_le D e
  have hT : ∀ c c' : Fin d → F,
      ∑ ws : Fin e → Vec F n, ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n,
        ((Kset D (phiA v0 h c) ws).card : ℝ) * gW D ρ (phiA v0 h c') ≤
      (if c = c' then q ^ n * q ^ (n * e) * q ^ (n * d) * Sg else 0) +
        q ^ (n * (d - 1)) * SKb * Sg := by
    intro c c'
    have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun v _ => gW_nonneg D ρ v
    by_cases hcc : c = c'
    · subst hcc
      rw [if_pos rfl]
      have hle : ∑ ws : Fin e → Vec F n, ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n,
          ((Kset D (phiA v0 h c) ws).card : ℝ) * gW D ρ (phiA v0 h c) ≤
          ∑ _ws : Fin e → Vec F n, ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n,
            q ^ n * gW D ρ (phiA v0 h c) := by
        refine Finset.sum_le_sum fun ws _ => Finset.sum_le_sum fun v0 _ =>
          Finset.sum_le_sum fun h _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (gW_nonneg D ρ _)
        have := card_Kset_le D (phiA v0 h c) ws
        rw [hqdef]; exact_mod_cast this
      have heq : ∑ _ws : Fin e → Vec F n, ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n,
            q ^ n * gW D ρ (phiA v0 h c) = q ^ n * q ^ (n * e) * q ^ (n * d) * Sg := by
        simp only [← Finset.mul_sum, single_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcardws]
        ring
      have : 0 ≤ q ^ (n * (d - 1)) * SKb * Sg := by
        have : 0 ≤ SKb := by simp only [SKb]; positivity
        positivity
      linarith
    · rw [if_neg hcc, zero_add]
      have hp : ∀ ws : Fin e → Vec F n, ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n,
          ((Kset D (phiA v0 h c) ws).card : ℝ) * gW D ρ (phiA v0 h c') =
          q ^ (n * (d - 1)) * ((∑ a, ((Kset D a ws).card : ℝ)) * Sg) := by
        intro ws
        rw [pair_sum c c' hcc (fun a b => ((Kset D a ws).card : ℝ) * gW D ρ b)]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        rfl
      simp only [hp, ← Finset.mul_sum, ← Finset.sum_mul]
      have := mul_le_mul_of_nonneg_right hSK hSg0
      have hq0 : 0 ≤ q ^ (n * (d - 1)) := by positivity
      nlinarith
  have hSXY : ∑ ω : Ω, X ω * Y ω ≤
      q ^ d * (q ^ n * q ^ (n * e) * q ^ (n * d) * Sg) +
        q ^ d * q ^ d * (q ^ (n * (d - 1)) * SKb * Sg) := by
    have e1 : ∑ ω : Ω, X ω * Y ω = ∑ c : Fin d → F, ∑ c' : Fin d → F,
        ∑ ws : Fin e → Vec F n, ∑ v0 : Vec F n, ∑ h : Fin d → Vec F n,
          ((Kset D (phiA v0 h c) ws).card : ℝ) * gW D ρ (phiA v0 h c') := by
      rw [hsumΩ (fun v0 h ws => (∑ c : Fin d → F, ((Kset D (phiA v0 h c) ws).card : ℝ)) *
        ∑ c' : Fin d → F, gW D ρ (phiA v0 h c'))]
      simp only [Finset.sum_mul_sum]
      have sw3 : ∀ {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → ℝ),
          ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
        intro A B C _ _ _ f
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
        exact Finset.sum_comm
      have sw4 : ∀ {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E]
          (f : A → B → C → E → ℝ),
          ∑ a, ∑ b, ∑ c, ∑ x, f a b c x = ∑ x, ∑ a, ∑ b, ∑ c, f a b c x := by
        intro A B C E _ _ _ _ f
        rw [Finset.sum_congr rfl fun a _ => sw3 (fun b c x => f a b c x)]
        exact Finset.sum_comm
      rw [sw4 (fun v0 h ws c => ∑ c' : Fin d → F,
        ((Kset D (phiA v0 h c) ws).card : ℝ) * gW D ρ (phiA v0 h c'))]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [sw4 (fun v0 h ws c' => ((Kset D (phiA v0 h c) ws).card : ℝ) * gW D ρ (phiA v0 h c'))]
      refine Finset.sum_congr rfl fun c' _ => ?_
      exact sw3 (fun v0 h ws => ((Kset D (phiA v0 h c) ws).card : ℝ) * gW D ρ (phiA v0 h c'))
    rw [e1]
    calc _ ≤ ∑ c : Fin d → F, ∑ c' : Fin d → F,
          ((if c = c' then q ^ n * q ^ (n * e) * q ^ (n * d) * Sg else 0) +
            q ^ (n * (d - 1)) * SKb * Sg) :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => hT c c'
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardc]
          ring
  -- the final arithmetic
  have hρ0 : 0 ≤ ρ := by
    have hZq : Zc ≤ q ^ (2 * n) := by
      have := Finset.card_le_univ (zeroLocus D)
      simp only [Fintype.card_prod, card_vec] at this
      simp only [Zc, hqdef]; rw [two_mul, pow_add]; exact_mod_cast this
    by_contra hneg; push Not at hneg
    have : q ^ ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hneg
    have h2n : 0 < q ^ (2 * n) := by positivity
    nlinarith
  have hd1 : 1 ≤ d := by
    have : (1 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  set Rq := q ^ ρ with hRq
  have hRq0 : 0 < Rq := Real.rpow_pos_of_pos hq ρ
  have hqd : 16 * Rq ≤ q ^ d := by
    have h4 : (16 : ℝ) ≤ q ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := pow_le_pow_left₀ (by norm_num) hq2 4
    calc 16 * Rq ≤ q ^ (4 : ℝ) * q ^ ρ := by nlinarith
      _ = q ^ (ρ + 4) := by rw [Real.rpow_add hq]; ring
      _ ≤ q ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hd
      _ = q ^ d := Real.rpow_natCast q d
  have hqe : 16 * Rq ≤ q ^ e := by
    have h4 : (16 : ℝ) ≤ q ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := pow_le_pow_left₀ (by norm_num) hq2 4
    calc 16 * Rq ≤ q ^ (4 : ℝ) * q ^ ρ := by nlinarith
      _ = q ^ (ρ + 4) := by rw [Real.rpow_add hq]; ring
      _ ≤ q ^ (e : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ = q ^ e := Real.rpow_natCast q e
  have hSg0 : 0 < Sg := by linarith
  have hqd0 : 0 < q ^ d := by positivity
  have hqe0 : 0 < q ^ e := by positivity
  have hP0 : 0 < P := by positivity
  have hkey : (2 / 3 : ℝ) * (q ^ (2 * n) + q ^ d * Zc + q ^ d * q ^ (2 * n) / q ^ e) ≤
      q ^ d * Sg :=
    base_arith _ Rq Zc Sg _ _ hRq0 (by linarith) hqd0 hqe0 hAR hqd hqe hSg
  have hident := base_ident q P Sg Zc n d e hd1 hq rfl
  -- conclude
  have hXY1 : ∑ ω : Ω, Y ω ≤ ∑ ω : Ω, X ω * Y ω := by
    refine Finset.sum_le_sum fun ω _ => ?_
    have hX1 : 1 ≤ X ω := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun c => ((Kset D (phiA ω.1 ω.2.1 c)
        ω.2.2).card : ℝ)) (fun _ _ => by positivity) (Finset.mem_univ 0))
      have : (0 : Vec F n) ∈ Kset D (phiA ω.1 ω.2.1 0) ω.2.2 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => by simp [TriForm.eval]⟩
      exact_mod_cast Finset.card_pos.2 ⟨0, this⟩
    have := mul_le_mul_of_nonneg_right hX1 (hY ω)
    linarith
  have hSYpos : 0 < ∑ ω : Ω, Y ω := by rw [hSY]; positivity
  have hSXYpos : 0 < ∑ ω : Ω, X ω * Y ω := lt_of_lt_of_le hSYpos hXY1
  have hcs := cs_ratio X Y hX hY
  have hmain : (2 / 3 : ℝ) * (Fintype.card Ω) * ∑ ω : Ω, X ω * Y ω ≤ (∑ ω : Ω, Y ω) ^ 2 := by
    rw [hcardΩ, hSY]
    calc (2 / 3 : ℝ) * (q ^ n * P) * ∑ ω : Ω, X ω * Y ω
        ≤ (2 / 3 : ℝ) * (q ^ n * P) * (q ^ d * (q ^ n * q ^ (n * e) * q ^ (n * d) * Sg) +
            q ^ d * q ^ d * (q ^ (n * (d - 1)) * SKb * Sg)) := by
          gcongr
      _ = (2 / 3 : ℝ) * (q ^ d * P ^ 2 * Sg * (q ^ (2 * n) + q ^ d * Zc +
            q ^ d * q ^ (2 * n) / q ^ e)) := by rw [← hident]; ring
      _ ≤ q ^ d * P ^ 2 * Sg * (q ^ d * Sg) := by
          have : 0 < q ^ d * P ^ 2 * Sg := by positivity
          have := mul_le_mul_of_nonneg_left hkey this.le
          linarith
      _ = (q ^ d * P * Sg) ^ 2 := by ring
  have hratio : (2 / 3 : ℝ) * Fintype.card Ω ≤ ∑ ω : Ω, Y ω / X ω := by
    have : (2 / 3 : ℝ) * Fintype.card Ω * ∑ ω : Ω, X ω * Y ω ≤
        (∑ ω : Ω, Y ω / X ω) * ∑ ω : Ω, X ω * Y ω := le_trans hmain hcs
    exact le_of_mul_le_mul_right this hSXYpos
  exact le_trans hratio (Finset.sum_le_sum fun ω _ => hYt ω)

end TriFormQ.W

end


-- ===== Solutions/W_Struct.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Stage 2a: the base-point algorithm -/

lemma basePoint_pos {d e : ℕ} (A : Option (Fin d) × Fin e → Vec F n) :
    0 < ∑ c : Fin d → F, (Finset.univ.filter fun u : Vec F n =>
      ∀ i, (A (none, i) + ∑ k, c k • A (some k, i)) ⬝ᵥ u = 0).card := by
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
  exact Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => by simp⟩⟩

/-- Stage 2a: a random affine map `c ↦ v₀ + Σ c_k h_k`, `e` probes, `(d+1) e` queries, and a
sample of `c` with weight `|{u : f(u, φ(c), w_i) = 0 ∀ i}|`. -/
noncomputable def basePoint (d e : ℕ) : CAlg (CQ F n) (Vec F n) (Vec F n) :=
  unif (β := Vec F n × (Fin d → Vec F n) × (Fin e → Vec F n)) fun ω =>
    queryF (ι := Option (Fin d) × Fin e)
      (fun p => CQ.yz (Option.elim p.1 ω.1 ω.2.1) (ω.2.2 p.2)) fun A =>
      wsample (fun c : Fin d → F => (Finset.univ.filter fun u : Vec F n =>
          ∀ i, (A (none, i) + ∑ k, c k • A (some k, i)) ⬝ᵥ u = 0).card) (basePoint_pos A)
        fun c => ret (phiA ω.1 ω.2.1 c)

theorem cost_basePoint (d e : ℕ) (ans : CQ F n → Vec F n) :
    (basePoint d e).cost ans ≤ (d + 1) * e := by
  refine cost_unif_le _ _ _ fun ω => ?_
  rw [cost_queryF]
  refine le_trans (Nat.add_le_add_right (cost_wsample_le ans _ _ _ 0 fun c _ => le_refl 0) _) ?_
  simp [Fintype.card_prod, Fintype.card_option]

lemma Kset_eq_filter (D : TriForm F n) {d e : ℕ} (v0 : Vec F n) (h : Fin d → Vec F n)
    (ws : Fin e → Vec F n) (c : Fin d → F) :
    (Finset.univ.filter fun u : Vec F n =>
      ∀ i, (CQ.ans D (CQ.yz v0 (ws i)) + ∑ k, c k • CQ.ans D (CQ.yz (h k) (ws i))) ⬝ᵥ u = 0) =
      Kset D (phiA v0 h c) ws := by
  ext u
  simp only [Kset, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall_congr' fun i => ?_
  rw [← ans_yz_sum, ← eval_yz]; rfl

lemma Kset_eq_filter' (D : TriForm F n) {d e : ℕ}
    (ω : Vec F n × (Fin d → Vec F n) × (Fin e → Vec F n)) (c : Fin d → F) :
    (Finset.univ.filter fun u : Vec F n =>
      ∀ i, (CQ.ans D (CQ.yz (Option.elim (none : Option (Fin d)) ω.1 ω.2.1) (ω.2.2 i)) +
        ∑ k, c k • CQ.ans D (CQ.yz (Option.elim (some k) ω.1 ω.2.1) (ω.2.2 i))) ⬝ᵥ u = 0) =
      Kset D (phiA ω.1 ω.2.1 c) ω.2.2 := by
  rw [← Kset_eq_filter]
  exact Finset.filter_congr fun u _ => Iff.rfl

theorem basePoint_good (D : TriForm F n) (ρ : ℝ)
    (hAR : (Fintype.card F : ℝ) ^ (2 * n) ≤ (Fintype.card F : ℝ) ^ ρ * (zeroLocus D).card)
    (d e : ℕ) (hd : ρ + 4 ≤ d) (he : ρ + 4 ≤ e) :
    2 / 3 ≤ (basePoint d e).prob (CQ.ans D) (fun v => v ∈ goodS D ρ) := by
  classical
  unfold basePoint
  rw [prob_unif]
  simp only [prob_queryF]
  have hcard : (0 : ℝ) < Fintype.card (Vec F n × (Fin d → Vec F n) × (Fin e → Vec F n)) := by
    exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hcard]
  have hb := base_ratio D ρ hAR d e hd he
  refine le_trans hb (le_of_eq (Finset.sum_congr rfl fun ω _ => ?_))
  unfold prob
  rw [expect_wsample]
  simp only [expect]
  simp_rw [Kset_eq_filter']
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  split_ifs <;> ring

/-! ### Stage 2b: the fiber probe -/

/-- The subspace `{u : a_i ⬝ u = 0 ∀ i}`. -/
def kerDots {m : ℕ} (a : Fin m → Vec F n) : Submodule F (Vec F n) :=
  LinearMap.ker (Matrix.of a).mulVecLin

lemma mem_kerDots {m : ℕ} (a : Fin m → Vec F n) (u : Vec F n) :
    u ∈ kerDots a ↔ ∀ i, a i ⬝ᵥ u = 0 := by
  simp only [kerDots, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h i; have := congrFun h i; simpa [mulVec] using this
  · intro h; funext i; simpa [mulVec] using h i

/-- Stage 2b: `m` probes recover the fiber `Z_v` as a subspace. -/
noncomputable def fiberProbe (v : Vec F n) (m : ℕ) :
    CAlg (CQ F n) (Vec F n) (Submodule F (Vec F n)) :=
  unif (β := Fin m → Vec F n) fun ws =>
    queryN m (fun i => CQ.yz v (ws i)) fun A => ret (kerDots A)

theorem cost_fiberProbe (v : Vec F n) (m : ℕ) (ans : CQ F n → Vec F n) :
    (fiberProbe v m).cost ans ≤ m := by
  refine cost_unif_le _ _ _ fun ws => ?_
  rw [cost_queryN]; simp [cost]

/-- The fiber as a subspace (the kernel of `u ↦ f(u, v, ·)`). -/
def fiberLin (D : TriForm F n) (v : Vec F n) : Vec F n →ₗ[F] Vec F n where
  toFun u := CQ.ans D (.xy u v)
  map_add' a b := by funext k; simp [CQ.ans, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext k
    simp only [CQ.ans, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma mem_ker_fiberLin (D : TriForm F n) (v u : Vec F n) :
    u ∈ LinearMap.ker (fiberLin D v) ↔ u ∈ fiber D v := by
  rw [LinearMap.mem_ker, mem_fiber]
  exact ans_xy_eq_zero_iff D u v

theorem fiberProbe_exact (D : TriForm F n) (v : Vec F n) (r c : ℕ)
    (hr : n - finrank F (LinearMap.ker (fiberLin D v)) ≤ r) :
    1 - 1 / 2 ^ c ≤ (fiberProbe v (r + c)).prob (CQ.ans D)
      (fun S => ∀ u, u ∈ S ↔ u ∈ fiber D v) := by
  classical
  unfold fiberProbe
  rw [prob_unif]
  simp only [prob_queryN, prob_ret]
  have hX : finrank F (LinearMap.range (fiberLin D v)) ≤ r := by
    have := LinearMap.finrank_range_add_finrank_ker (fiberLin D v)
    rw [finrank_vec] at this; omega
  have hfrac := probe_frac_le (F := F) (n := n) (LinearMap.range (fiberLin D v)) (c := c) hX
  have hpt : ∀ ws : Fin (r + c) → Vec F n,
      1 - (if ∃ x ∈ LinearMap.range (fiberLin D v), x ≠ 0 ∧ ∀ l, ws l ⬝ᵥ x = 0 then (1 : ℝ)
        else 0) ≤ (if ∀ u, u ∈ kerDots (fun i => CQ.ans D (CQ.yz v (ws i))) ↔ u ∈ fiber D v
          then 1 else 0) := by
    intro ws
    by_cases hb : ∃ x ∈ LinearMap.range (fiberLin D v), x ≠ 0 ∧ ∀ l, ws l ⬝ᵥ x = 0
    · rw [if_pos hb]; split_ifs <;> norm_num
    · rw [if_neg hb, if_pos]; · norm_num
      intro u
      rw [mem_kerDots]
      constructor
      · intro h
        by_contra hu
        apply hb
        refine ⟨fiberLin D v u, ⟨u, rfl⟩, ?_, fun l => ?_⟩
        · intro h0; exact hu ((mem_ker_fiberLin D v u).1 (LinearMap.mem_ker.2 h0))
        · have := h l
          rw [← eval_yz, eval_xy] at this
          rw [dotProduct_comm]; exact this
      · intro hu i
        rw [← eval_yz]
        exact (mem_fiber D u v).1 hu _
  have hcard : (0 : ℝ) < Fintype.card (Fin (r + c) → Vec F n) := by
    exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hcard]
  calc (1 - 1 / 2 ^ c) * (Fintype.card (Fin (r + c) → Vec F n) : ℝ)
      ≤ (1 - (∑ ws : Fin (r + c) → Vec F n, (if ∃ x ∈ LinearMap.range (fiberLin D v), x ≠ 0 ∧
          ∀ l, ws l ⬝ᵥ x = 0 then (1 : ℝ) else 0)) / Fintype.card (Fin (r + c) → Vec F n)) *
          Fintype.card (Fin (r + c) → Vec F n) := by
        gcongr
    _ = ∑ ws : Fin (r + c) → Vec F n, (1 - (if ∃ x ∈ LinearMap.range (fiberLin D v), x ≠ 0 ∧
          ∀ l, ws l ⬝ᵥ x = 0 then (1 : ℝ) else 0)) := by
        rw [Finset.sum_sub_distrib, sub_mul, div_mul_cancel₀ _ hcard.ne']
        simp
    _ ≤ _ := Finset.sum_le_sum fun ws _ => hpt ws

end TriFormQ.W

end


-- ===== Solutions/W_Pivot.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Matrices with prescribed range -/

/-- A matrix whose column space is `S` (a projection onto `S`). -/
noncomputable def projMat (S : Submodule F (Vec F n)) : Matrix (Fin n) (Fin n) F :=
  LinearMap.toMatrix' (S.projection (Classical.choose (Submodule.exists_isCompl S))
    (Classical.choose_spec (Submodule.exists_isCompl S)))

lemma range_projMat (S : Submodule F (Vec F n)) :
    LinearMap.range (projMat S).mulVecLin = S := by
  unfold projMat
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix', Submodule.range_projection]

lemma projMat_mem (S : Submodule F (Vec F n)) (v : Vec F n) : projMat S *ᵥ v ∈ S := by
  have h : projMat S *ᵥ v ∈ LinearMap.range (projMat S).mulVecLin := ⟨v, rfl⟩
  rwa [range_projMat] at h

lemma rank_projMat (S : Submodule F (Vec F n)) : (projMat S).rank = finrank F S := by
  rw [rank_eq_finrank, range_projMat]

/-- Sylvester-type bound: `rk(P Q) + (n - rk Q) ≥ rk P`... in the form `rk P ≤ rk(P Q) + (n - rk Q)`. -/
lemma rank_mul_ge (P Q : Matrix (Fin n) (Fin n) F) : P.rank ≤ (P * Q).rank + (n - Q.rank) := by
  -- rk(PQ) = dim P(range Q) ≥ dim range Q - dim ker P
  have hrange : LinearMap.range (P * Q).mulVecLin = (LinearMap.range Q.mulVecLin).map P.mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  let f := P.mulVecLin.domRestrict (LinearMap.range Q.mulVecLin)
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have hf : LinearMap.range f = (LinearMap.range Q.mulVecLin).map P.mulVecLin :=
    LinearMap.range_domRestrict _ _
  -- the kernel of `f` embeds into the kernel of `P`
  let g : LinearMap.ker f →ₗ[F] Vec F n := (LinearMap.range Q.mulVecLin).subtype ∘ₗ
    (LinearMap.ker f).subtype
  have hg : Function.Injective g := by
    intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  have hgr : LinearMap.range g ≤ LinearMap.ker P.mulVecLin := by
    rintro _ ⟨⟨⟨v, hv⟩, hk⟩, rfl⟩
    have := LinearMap.mem_ker.1 hk
    simp only [f, LinearMap.domRestrict_apply] at this
    simpa [g] using this
  have h2 := LinearMap.finrank_range_of_inj hg
  have h3 := Submodule.finrank_mono hgr
  have h4 := finrank_ker_mulVecLin P
  have h5 : (P * Q).rank = finrank F (LinearMap.range f) := by
    rw [rank_eq_finrank, hrange, hf]
  have h6 : Q.rank = finrank F (LinearMap.range Q.mulVecLin) := rfl
  have h7 := Matrix.rank_le_width P
  have h8 := Matrix.rank_le_width Q
  have k1 : finrank F (LinearMap.ker f) ≤ finrank F (LinearMap.ker P.mulVecLin) := h2 ▸ h3
  have k2 : (P * Q).rank + finrank F (LinearMap.ker f) = Q.rank := by rw [h5, h6]; exact h1
  clear_value f
  omega

/-! ### The pivot step -/

/-- The current space of matrices: `x ↦ P_Vᵀ f[P_U x] P_W`. -/
def mView (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) (x : Vec F n) :
    Matrix (Fin n) (Fin n) F :=
  PVᵀ * sliceU D (PU *ᵥ x) * PW

lemma mView_add (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) (x x' : Vec F n) :
    mView D PU PV PW (x + x') = mView D PU PV PW x + mView D PU PV PW x' := by
  simp [mView, Matrix.mulVec_add, sliceU_add, Matrix.mul_add, Matrix.add_mul]

lemma mView_sub (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) (x x' : Vec F n) :
    mView D PU PV PW (x - x') = mView D PU PV PW x - mView D PU PV PW x' := by
  simp [mView, Matrix.mulVec_sub, sliceU_sub, Matrix.mul_sub, Matrix.sub_mul]

lemma eval_mView (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) (x y z : Vec F n) :
    TriForm.eval D (PU *ᵥ x) (PV *ᵥ y) (PW *ᵥ z) = y ⬝ᵥ (mView D PU PV PW x *ᵥ z) := by
  rw [eval_sliceU, mView, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec y PVᵀ, Matrix.vecMul_transpose]

lemma ans_xy_vecMul (D : TriForm F n) (u y : Vec F n) :
    CQ.ans D (.xy u y) = y ᵥ* sliceU D u := by
  funext k
  simp only [CQ.ans, vecMul, dotProduct, sliceU, of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma ans_xz_mulVec (D : TriForm F n) (u z : Vec F n) :
    CQ.ans D (.xz u z) = sliceU D u *ᵥ z := by
  funext j
  simp only [CQ.ans, mulVec, dotProduct, sliceU, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  try exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- The output of a pivot step from the observed left-probe rows and right-probe columns. -/
noncomputable def pivotOut (PV PW : Matrix (Fin n) (Fin n) F) {J m : ℕ}
    (rows cols : Fin (J + 1) → Fin m → Vec F n) :
    Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F :=
  (PV * projMat (kerDots (cols (Classical.choose (Finset.exists_max_image Finset.univ
      (fun j => n - finrank F (kerDots (rows j))) Finset.univ_nonempty)))),
    PW * projMat (kerDots (rows (Classical.choose (Finset.exists_max_image Finset.univ
      (fun j => n - finrank F (kerDots (rows j))) Finset.univ_nonempty)))))

/-- One pivot step with `J+1` candidate slices and `m` probes per side. -/
noncomputable def pivotStep (PU PV PW : Matrix (Fin n) (Fin n) F) (J m : ℕ) :
    CAlg (CQ F n) (Vec F n) (Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F) :=
  unif (β := (Fin (J + 1) → Vec F n) × (Fin (J + 1) → Fin m → Vec F n) ×
      (Fin (J + 1) → Fin m → Vec F n)) fun ω =>
    queryF (ι := Fin (J + 1) × Fin m × Bool)
      (fun p => if p.2.2 then CQ.xy (PU *ᵥ ω.1 p.1) (PV *ᵥ ω.2.1 p.1 p.2.1)
        else CQ.xz (PU *ᵥ ω.1 p.1) (PW *ᵥ ω.2.2 p.1 p.2.1)) fun A =>
      ret (pivotOut PV PW (fun j i => A (j, i, true) ᵥ* PW) (fun j i => PVᵀ *ᵥ A (j, i, false)))

theorem cost_pivotStep (PU PV PW : Matrix (Fin n) (Fin n) F) (J m : ℕ) (ans : CQ F n → Vec F n) :
    (pivotStep PU PV PW J m).cost ans ≤ (J + 1) * m * 2 := by
  refine cost_unif_le _ _ _ fun ω => ?_
  rw [cost_queryF]
  simp only [cost, zero_add, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  try exact le_of_eq (by ring)

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

lemma sum_fun_single {T : Type} [Fintype T] [DecidableEq T] {K : ℕ} (j : Fin K) (g : T → ℝ) :
    ∑ f : Fin K → T, g (f j) = (Fintype.card T : ℝ) ^ (K - 1) * ∑ t, g t := by
  rw [← (Equiv.funSplitAt j T).symm.sum_comp, Fintype.sum_prod_type]
  have key : ∀ t rest, (Equiv.funSplitAt j T).symm (t, rest) j = t := by
    intro t rest; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hc : Fintype.card {i : Fin K // i ≠ j} = K - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]; simp
  rw [Fintype.card_fun, hc]
  push_cast; ring

lemma finrank_ker_vecMulLinear (A : Matrix (Fin n) (Fin n) F) :
    finrank F (LinearMap.ker (Matrix.vecMulLinear A)) = n - A.rank := by
  have e : Matrix.vecMulLinear A = Aᵀ.mulVecLin := by
    rw [← Matrix.vecMulLinear_transpose, Matrix.transpose_transpose]
  rw [e, finrank_ker_mulVecLin, Matrix.rank_transpose]

/-- Half of the space has a slice of rank at least half the maximum. -/
lemma bad_half (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) :
    2 * (Finset.univ.filter fun x : Vec F n => 2 * (mView D PU PV PW x).rank <
      Finset.univ.sup fun x => (mView D PU PV PW x).rank).card ≤ Fintype.card F ^ n := by
  classical
  set M := mView D PU PV PW
  set rmax := Finset.univ.sup fun x => (M x).rank
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ (fun x => (M x).rank)
    Finset.univ_nonempty
  have hx0' : (M x0).rank = rmax := le_antisymm (Finset.le_sup (f := fun x => (M x).rank)
    (Finset.mem_univ x0)) (Finset.sup_le fun x _ => hx0 x (Finset.mem_univ x))
  set Bad := Finset.univ.filter fun x : Vec F n => 2 * (M x).rank < rmax
  -- the involution x ↦ x0 - x maps Bad into its complement
  have himg : Bad.image (fun x => x0 - x) ⊆ Badᶜ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_compl]
    intro hy'
    have h1 := (Finset.mem_filter.1 hx).2
    have h2 := (Finset.mem_filter.1 hy').2
    have hsum : (M x0).rank ≤ (M x).rank + (M (x0 - x)).rank := by
      have : M x0 = M x + M (x0 - x) := by rw [← mView_add]; congr 1; abel
      rw [this]; exact rank_add_le' _ _
    omega
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ (sub_right_injective), Finset.card_compl] at hcard
  rw [card_vec] at hcard
  have := Finset.card_le_univ Bad
  rw [card_vec] at this
  omega

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

lemma rows_true (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) (x y : Vec F n) :
    CQ.ans D (.xy (PU *ᵥ x) (PV *ᵥ y)) ᵥ* PW = y ᵥ* mView D PU PV PW x := by
  rw [ans_xy_vecMul, mView, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    Matrix.vecMul_transpose]

lemma cols_true (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) (x z : Vec F n) :
    PVᵀ *ᵥ CQ.ans D (.xz (PU *ᵥ x) (PW *ᵥ z)) = mView D PU PV PW x *ᵥ z := by
  rw [ans_xz_mulVec, mView, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- The deterministic heart of the pivot step. -/
theorem pivot_det (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) (r c : ℕ)
    (hinv : ∀ x, (mView D PU PV PW x).rank ≤ r) (hcV : n - PV.rank ≤ c) (hcW : n - PW.rank ≤ c)
    {J m : ℕ} (xs : Fin (J + 1) → Vec F n) (yss zss : Fin (J + 1) → Fin m → Vec F n)
    (hrank : ∃ j, (Finset.univ.sup fun x => (mView D PU PV PW x).rank) ≤
      2 * (mView D PU PV PW (xs j)).rank)
    (hY : ∀ j, ¬ ∃ v ∈ LinearMap.range (mView D PU PV PW (xs j)).mulVecLin, v ≠ 0 ∧
      ∀ i, yss j i ⬝ᵥ v = 0)
    (hZ : ∀ j, ¬ ∃ v ∈ LinearMap.range (Matrix.vecMulLinear (mView D PU PV PW (xs j))), v ≠ 0 ∧
      ∀ i, zss j i ⬝ᵥ v = 0) :
    let st := pivotOut PV PW (fun j i => yss j i ᵥ* mView D PU PV PW (xs j))
      (fun j i => mView D PU PV PW (xs j) *ᵥ zss j i)
    (∀ x, (mView D PU st.1 st.2 x).rank ≤ 3 * r / 4) ∧ n - st.1.rank ≤ c + r ∧
      n - st.2.rank ≤ c + r := by
  intro st
  set M := mView D PU PV PW
  set rmax := Finset.univ.sup fun x => (M x).rank
  have hrmax : rmax ≤ r := Finset.sup_le fun x _ => hinv x
  have hle : ∀ x, (M x).rank ≤ rmax := fun x =>
    Finset.le_sup (f := fun x => (M x).rank) (Finset.mem_univ x)
  set R : Fin (J + 1) → Submodule F (Vec F n) := fun j => kerDots fun i => yss j i ᵥ* M (xs j)
  set L : Fin (J + 1) → Submodule F (Vec F n) := fun j => kerDots fun i => M (xs j) *ᵥ zss j i
  have hR : ∀ j, R j = LinearMap.ker (M (xs j)).mulVecLin := by
    intro j; ext z
    simp only [R, mem_kerDots, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro h; by_contra hne
      exact hY j ⟨M (xs j) *ᵥ z, ⟨z, rfl⟩, hne, fun i => by rw [dotProduct_mulVec]; exact h i⟩
    · intro h i; rw [← dotProduct_mulVec, h, dotProduct_zero]
  have hL : ∀ j, L j = LinearMap.ker (Matrix.vecMulLinear (M (xs j))) := by
    intro j; ext y
    simp only [L, mem_kerDots, LinearMap.mem_ker, Matrix.vecMulLinear_apply]
    constructor
    · intro h; by_contra hne
      exact hZ j ⟨y ᵥ* M (xs j), ⟨y, rfl⟩, hne, fun i => by
        rw [dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]; exact h i⟩
    · intro h i; rw [dotProduct_comm, dotProduct_mulVec, h, zero_dotProduct]
  have hRf : ∀ j, finrank F (R j) = n - (M (xs j)).rank := fun j => by
    rw [hR, finrank_ker_mulVecLin]
  have hLf : ∀ j, finrank F (L j) = n - (M (xs j)).rank := fun j => by
    rw [hL, finrank_ker_vecMulLinear]
  -- the chosen index
  set js := Classical.choose (Finset.exists_max_image Finset.univ
      (fun j => n - finrank F (R j)) Finset.univ_nonempty)
  have hjs := Classical.choose_spec (Finset.exists_max_image Finset.univ
      (fun j => n - finrank F (R j)) Finset.univ_nonempty)
  have hst : st = (PV * projMat (L js), PW * projMat (R js)) := rfl
  set A := M (xs js) with hAdef
  have hAle : ∀ j, (M (xs j)).rank ≤ A.rank := by
    intro j
    have h0 : n - finrank F (R j) ≤ n - finrank F (R js) := hjs.2 j (Finset.mem_univ j)
    rw [hRf, hRf, ← hAdef] at h0
    have h1 := Matrix.rank_le_width (M (xs j))
    have h2 := Matrix.rank_le_width A
    omega
  obtain ⟨j0, hj0⟩ := hrank
  have hA2 : rmax ≤ 2 * A.rank := le_trans hj0 (by have := hAle j0; omega)
  have hAr : A.rank ≤ rmax := hle _
  -- X A = 0 and A Y = 0
  set X := (projMat (L js))ᵀ
  set Y := projMat (R js)
  have hXA : X * A = 0 := by
    ext a b
    have hmem : projMat (L js) *ᵥ Pi.single a 1 ∈ LinearMap.ker (Matrix.vecMulLinear A) := by
      rw [hAdef, ← hL]; exact projMat_mem _ _
    rw [LinearMap.mem_ker, Matrix.vecMulLinear_apply] at hmem
    have := congrFun hmem b
    simp only [Pi.zero_apply] at this
    rw [Matrix.zero_apply, ← this]
    simp [X, Matrix.mul_apply, vecMul, dotProduct, mulVec, Pi.single_apply]
  have hAY : A * Y = 0 := by
    ext a b
    have hmem : projMat (R js) *ᵥ Pi.single b 1 ∈ LinearMap.ker A.mulVecLin := by
      rw [hAdef, ← hR]; exact projMat_mem _ _
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at hmem
    have := congrFun hmem a
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [hst]
    have hview : mView D PU (PV * projMat (L js)) (PW * projMat (R js)) x = X * M x * Y := by
      simp only [mView, M, X, Y, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hview]
    have h11 := lemma11_matrix A (M x) X Y hXA hAY
    have hsum : (A + M x).rank ≤ rmax := by
      rw [show A + M x = M (xs js + x) from (mView_add D PU PV PW (xs js) x).symm]; exact hle _
    have hMx := hle x
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  · rw [hst]
    show n - (PV * projMat (L js)).rank ≤ c + r
    have h1 := rank_mul_ge PV (projMat (L js))
    rw [rank_projMat, hLf, ← hAdef] at h1
    have h2 := Matrix.rank_le_width A
    omega
  · rw [hst]
    show n - (PW * projMat (R js)).rank ≤ c + r
    have h1 := rank_mul_ge PW (projMat (R js))
    rw [rank_projMat, hRf, ← hAdef] at h1
    have h2 := Matrix.rank_le_width A
    omega

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Invariant of the pivot loop. -/
def PivInv (D : TriForm F n) (PU : Matrix (Fin n) (Fin n) F) (r c : ℕ)
    (st : Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ x, (mView D PU st.1 st.2 x).rank ≤ r) ∧ n - st.1.rank ≤ c ∧ n - st.2.rank ≤ c

theorem pivotStep_good (D : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F)
    (r r' c s J : ℕ) (hrr : r ≤ r') (hinv : PivInv D PU r c (PV, PW)) :
    1 - (1 / 2 ^ (J + 1) + 2 * (J + 1) / 2 ^ s) ≤
      (pivotStep PU PV PW J (r' + s)).prob (CQ.ans D) (PivInv D PU (3 * r / 4) (c + r)) := by
  classical
  obtain ⟨hinvr, hcV, hcW⟩ := hinv
  simp only at hinvr hcV hcW
  set m := r' + s
  set M := mView D PU PV PW
  set rmax := Finset.univ.sup fun x => (M x).rank
  set T := Fin m → Vec F n
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  unfold pivotStep
  rw [prob_unif]
  simp only [prob_queryF, prob_ret]
  simp only [Bool.false_eq_true, if_false, if_true, rows_true, cols_true]
  -- bad events
  let BR : (Fin (J + 1) → Vec F n) → ℝ := fun xs =>
    if ∀ j, 2 * (M (xs j)).rank < rmax then 1 else 0
  let BY : Fin (J + 1) → Vec F n → T → ℝ := fun j x ys =>
    if ∃ v ∈ LinearMap.range (M x).mulVecLin, v ≠ 0 ∧ ∀ i, ys i ⬝ᵥ v = 0 then 1 else 0
  let BZ : Fin (J + 1) → Vec F n → T → ℝ := fun j x zs =>
    if ∃ v ∈ LinearMap.range (Matrix.vecMulLinear (M x)), v ≠ 0 ∧ ∀ i, zs i ⬝ᵥ v = 0 then 1
      else 0
  have hpt : ∀ (xs : Fin (J + 1) → Vec F n) (yss zss : Fin (J + 1) → T),
      1 - BR xs - ∑ j, BY j (xs j) (yss j) - ∑ j, BZ j (xs j) (zss j) ≤
        (if PivInv D PU (3 * r / 4) (c + r) (pivotOut PV PW (fun j i => yss j i ᵥ* M (xs j))
          (fun j i => M (xs j) *ᵥ zss j i)) then 1 else 0) := by
    intro xs yss zss
    have hBY : ∀ j, 0 ≤ BY j (xs j) (yss j) := fun j => by simp only [BY]; split_ifs <;> norm_num
    have hBZ : ∀ j, 0 ≤ BZ j (xs j) (zss j) := fun j => by simp only [BZ]; split_ifs <;> norm_num
    have sBY := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hBY j
    have sBZ := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hBZ j
    by_cases hR : ∀ j, 2 * (M (xs j)).rank < rmax
    · have : BR xs = 1 := if_pos hR
      rw [this]; split_ifs <;> linarith
    have hR' : BR xs = 0 := if_neg hR
    by_cases hY : ∃ j, ∃ v ∈ LinearMap.range (M (xs j)).mulVecLin, v ≠ 0 ∧ ∀ i, yss j i ⬝ᵥ v = 0
    · obtain ⟨j, hj⟩ := hY
      have : BY j (xs j) (yss j) = 1 := if_pos hj
      have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hBY j) (Finset.mem_univ j)
      split_ifs <;> linarith
    by_cases hZ : ∃ j, ∃ v ∈ LinearMap.range (Matrix.vecMulLinear (M (xs j))), v ≠ 0 ∧
        ∀ i, zss j i ⬝ᵥ v = 0
    · obtain ⟨j, hj⟩ := hZ
      have : BZ j (xs j) (zss j) = 1 := if_pos hj
      have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hBZ j) (Finset.mem_univ j)
      split_ifs <;> linarith
    push Not at hR hY hZ
    have hdet := pivot_det D PU PV PW r c hinvr hcV hcW xs yss zss
      (by obtain ⟨j, hj⟩ := hR; exact ⟨j, hj⟩)
      (fun j ⟨v, hv, hv0, hvy⟩ => by obtain ⟨i, hi⟩ := hY j v hv hv0; exact hi (hvy i))
      (fun j ⟨v, hv, hv0, hvz⟩ => by obtain ⟨i, hi⟩ := hZ j v hv hv0; exact hi (hvz i))
    have hdet' : PivInv D PU (3 * r / 4) (c + r) (pivotOut PV PW (fun j i => yss j i ᵥ* M (xs j))
        (fun j i => M (xs j) *ᵥ zss j i)) := hdet
    rw [if_pos hdet']
    linarith
  -- counting
  set NT : ℝ := (Fintype.card T : ℝ)
  set NX : ℝ := (Fintype.card (Fin (J + 1) → Vec F n) : ℝ)
  have hNT : 0 < NT := by simp only [NT]; exact_mod_cast Fintype.card_pos
  have hNX : 0 < NX := by simp only [NX]; exact_mod_cast Fintype.card_pos
  have hNYc : (Fintype.card (Fin (J + 1) → T) : ℝ) = NT ^ (J + 1) := by
    simp only [NT, Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  have hΩ : (Fintype.card ((Fin (J + 1) → Vec F n) × (Fin (J + 1) → T) × (Fin (J + 1) → T)) : ℝ)
      = NX * NT ^ (J + 1) * NT ^ (J + 1) := by
    rw [Fintype.card_prod, Fintype.card_prod]; push_cast; rw [hNYc]; ring
  rw [hΩ, le_div_iff₀ (by positivity)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  -- (a)
  have hBadR : ∑ xs : Fin (J + 1) → Vec F n, BR xs ≤ NX / 2 ^ (J + 1) := by
    have hb := bad_half D PU PV PW
    simp only [BR]
    rw [Finset.sum_boole]
    have e := card_all_mem (k := J + 1) (Finset.univ.filter fun x : Vec F n =>
      2 * (M x).rank < rmax)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at e
    rw [e]
    simp only [NX, Fintype.card_fun, Fintype.card_fin, card_vec]
    push_cast
    rw [le_div_iff₀ (by positivity), ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have hb2 : (Finset.univ.filter fun x : Vec F n => 2 * (M x).rank < rmax).card * 2 ≤
        Fintype.card F ^ n := by
      rw [mul_comm]; exact hb
    exact_mod_cast hb2
  -- (b), (c)
  have hBadY : ∀ j, ∀ x : Vec F n, ∑ ys : T, BY j x ys ≤ NT / 2 ^ s := by
    intro j x
    have hf := probe_frac_le (F := F) (n := n) (LinearMap.range (M x).mulVecLin) (r := r') (c := s)
      (by rw [← rank_eq_finrank]; exact (hinvr x).trans hrr)
    rw [div_le_iff₀ hNT] at hf
    simp only [BY]
    calc _ ≤ 1 / 2 ^ s * NT := hf
      _ = NT / 2 ^ s := by ring
  have hBadZ : ∀ j, ∀ x : Vec F n, ∑ zs : T, BZ j x zs ≤ NT / 2 ^ s := by
    intro j x
    have hf := probe_frac_le (F := F) (n := n) (LinearMap.range (Matrix.vecMulLinear (M x)))
      (r := r') (c := s) (by rw [finrank_range_vecMulLinear]; exact (hinvr x).trans hrr)
    rw [div_le_iff₀ hNT] at hf
    simp only [BZ]
    calc _ ≤ 1 / 2 ^ s * NT := hf
      _ = NT / 2 ^ s := by ring
  have hSY : ∀ (xs : Fin (J + 1) → Vec F n) j,
      ∑ yss : Fin (J + 1) → T, BY j (xs j) (yss j) ≤ NT ^ (J + 1) / 2 ^ s := by
    intro xs j
    rw [sum_fun_single j (fun ys => BY j (xs j) ys)]
    calc NT ^ (J + 1 - 1) * ∑ t, BY j (xs j) t ≤ NT ^ (J + 1 - 1) * (NT / 2 ^ s) :=
          mul_le_mul_of_nonneg_left (hBadY j _) (by positivity)
      _ = NT ^ (J + 1) / 2 ^ s := by rw [Nat.add_sub_cancel, pow_succ]; ring
  have hSZ : ∀ (xs : Fin (J + 1) → Vec F n) j,
      ∑ zss : Fin (J + 1) → T, BZ j (xs j) (zss j) ≤ NT ^ (J + 1) / 2 ^ s := by
    intro xs j
    rw [sum_fun_single j (fun zs => BZ j (xs j) zs)]
    calc NT ^ (J + 1 - 1) * ∑ t, BZ j (xs j) t ≤ NT ^ (J + 1 - 1) * (NT / 2 ^ s) :=
          mul_le_mul_of_nonneg_left (hBadZ j _) (by positivity)
      _ = NT ^ (J + 1) / 2 ^ s := by rw [Nat.add_sub_cancel, pow_succ]; ring
  -- sum of the pointwise bound
  set NY : ℝ := NT ^ (J + 1)
  have hNY : 0 < NY := by positivity
  have hSYx : ∀ xs : Fin (J + 1) → Vec F n,
      ∑ yss : Fin (J + 1) → T, ∑ j, BY j (xs j) (yss j) ≤ (J + 1) * (NY / 2 ^ s) := by
    intro xs
    rw [Finset.sum_comm]
    calc ∑ j, ∑ yss : Fin (J + 1) → T, BY j (xs j) (yss j) ≤ ∑ _j : Fin (J + 1), NY / 2 ^ s :=
          Finset.sum_le_sum fun j _ => hSY xs j
      _ = (J + 1) * (NY / 2 ^ s) := by simp
  have hSZx : ∀ xs : Fin (J + 1) → Vec F n,
      ∑ zss : Fin (J + 1) → T, ∑ j, BZ j (xs j) (zss j) ≤ (J + 1) * (NY / 2 ^ s) := by
    intro xs
    rw [Finset.sum_comm]
    calc ∑ j, ∑ zss : Fin (J + 1) → T, BZ j (xs j) (zss j) ≤ ∑ _j : Fin (J + 1), NY / 2 ^ s :=
          Finset.sum_le_sum fun j _ => hSZ xs j
      _ = (J + 1) * (NY / 2 ^ s) := by simp
  have hcY : (Fintype.card (Fin (J + 1) → T) : ℝ) = NY := hNYc
  have hcX : (Fintype.card (Fin (J + 1) → Vec F n) : ℝ) = NX := rfl
  -- per-xs lower bound
  have hx : ∀ xs : Fin (J + 1) → Vec F n,
      NY * NY - NY * NY * BR xs - NY * ((J + 1) * (NY / 2 ^ s)) -
        NY * ((J + 1) * (NY / 2 ^ s)) ≤
      ∑ yss : Fin (J + 1) → T, ∑ zss : Fin (J + 1) → T,
        (1 - BR xs - ∑ j, BY j (xs j) (yss j) - ∑ j, BZ j (xs j) (zss j)) := by
    intro xs
    have e : ∑ yss : Fin (J + 1) → T, ∑ zss : Fin (J + 1) → T,
        (1 - BR xs - ∑ j, BY j (xs j) (yss j) - ∑ j, BZ j (xs j) (zss j)) =
        NY * NY - NY * NY * BR xs - NY * ∑ yss : Fin (J + 1) → T, ∑ j, BY j (xs j) (yss j) -
          NY * ∑ zss : Fin (J + 1) → T, ∑ j, BZ j (xs j) (zss j) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcY,
        Finset.mul_sum]
      ring_nf
    rw [e]
    have h1 := hSYx xs
    have h2 := hSZx xs
    nlinarith
  have hstep1 : ∑ xs : Fin (J + 1) → Vec F n, ∑ yss : Fin (J + 1) → T, ∑ zss : Fin (J + 1) → T,
      (1 - BR xs - ∑ j, BY j (xs j) (yss j) - ∑ j, BZ j (xs j) (zss j)) ≤
      ∑ xs : Fin (J + 1) → Vec F n, ∑ yss : Fin (J + 1) → T, ∑ zss : Fin (J + 1) → T,
        (if PivInv D PU (3 * r / 4) (c + r) (pivotOut PV PW (fun j i => yss j i ᵥ* M (xs j))
          (fun j i => M (xs j) *ᵥ zss j i)) then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun xs _ => Finset.sum_le_sum fun yss _ => Finset.sum_le_sum fun zss _ =>
      hpt xs yss zss
  have hstep2 : ∑ xs : Fin (J + 1) → Vec F n,
      (NY * NY - NY * NY * BR xs - NY * ((J + 1) * (NY / 2 ^ s)) -
        NY * ((J + 1) * (NY / 2 ^ s))) ≤
      ∑ xs : Fin (J + 1) → Vec F n, ∑ yss : Fin (J + 1) → T, ∑ zss : Fin (J + 1) → T,
        (1 - BR xs - ∑ j, BY j (xs j) (yss j) - ∑ j, BZ j (xs j) (zss j)) :=
    Finset.sum_le_sum fun xs _ => hx xs
  have hstep3 : ∑ xs : Fin (J + 1) → Vec F n,
      (NY * NY - NY * NY * BR xs - NY * ((J + 1) * (NY / 2 ^ s)) -
        NY * ((J + 1) * (NY / 2 ^ s))) =
      NX * (NY * NY) - NY * NY * (∑ xs, BR xs) - 2 * NX * (NY * ((J + 1) * (NY / 2 ^ s))) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcX,
      ← Finset.mul_sum]
    ring
  rw [hstep3] at hstep2
  have hBR := mul_le_mul_of_nonneg_left hBadR (by positivity : (0 : ℝ) ≤ NY * NY)
  have hfinal : (1 - (1 / 2 ^ (J + 1) + 2 * (J + 1) / 2 ^ s)) * (NX * NY * NY) =
      NX * (NY * NY) - NY * NY * (NX / 2 ^ (J + 1)) -
        2 * NX * (NY * ((J + 1) * (NY / 2 ^ s))) := by
    field_simp; ring
  push_cast at hfinal ⊢
  linarith

end TriFormQ.W

end


-- ===== Solutions/W_Loop.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- `I` pivot steps. -/
noncomputable def pivotLoop (PU : Matrix (Fin n) (Fin n) F) (J m : ℕ) :
    ℕ → Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F →
      CAlg (CQ F n) (Vec F n) (Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F)
  | 0, st => ret st
  | I + 1, st => (pivotStep PU st.1 st.2 J m).bind (pivotLoop PU J m I)

def rIter : ℕ → ℕ → ℕ
  | r, 0 => r
  | r, I + 1 => rIter (3 * r / 4) I

def cIter : ℕ → ℕ → ℕ
  | _, 0 => 0
  | r, I + 1 => r + cIter (3 * r / 4) I

lemma cIter_le : ∀ I r, cIter r I ≤ 4 * r
  | 0, r => by simp [cIter]
  | I + 1, r => by
    simp only [cIter]
    have := cIter_le I (3 * r / 4)
    have h : 4 * (3 * r / 4) ≤ 3 * r := Nat.mul_div_le (3 * r) 4
    omega

lemma rIter_mul : ∀ I r, rIter r I * 4 ^ I ≤ r * 3 ^ I
  | 0, r => by simp [rIter]
  | I + 1, r => by
    simp only [rIter]
    have := rIter_mul I (3 * r / 4)
    have h : 4 * (3 * r / 4) ≤ 3 * r := Nat.mul_div_le (3 * r) 4
    calc rIter (3 * r / 4) I * 4 ^ (I + 1) = rIter (3 * r / 4) I * 4 ^ I * 4 := by ring
      _ ≤ 3 * r / 4 * 3 ^ I * 4 := Nat.mul_le_mul_right 4 this
      _ = 4 * (3 * r / 4) * 3 ^ I := by ring
      _ ≤ 3 * r * 3 ^ I := Nat.mul_le_mul_right _ h
      _ = r * 3 ^ (I + 1) := by ring

lemma rIter_zero (r ℓ : ℕ) (hℓ : r < 2 ^ ℓ) : rIter r (4 * ℓ) = 0 := by
  have h := rIter_mul (4 * ℓ) r
  have e1 : (4 : ℕ) ^ (4 * ℓ) = 256 ^ ℓ := by rw [pow_mul]; norm_num
  have e2 : (3 : ℕ) ^ (4 * ℓ) = 81 ^ ℓ := by rw [pow_mul]; norm_num
  rw [e1, e2] at h
  have h3 : 2 ^ ℓ * 81 ^ ℓ ≤ 256 ^ ℓ := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) ℓ
  by_contra hne
  have h4 : 1 ≤ rIter r (4 * ℓ) := Nat.one_le_iff_ne_zero.2 hne
  have h5 : 256 ^ ℓ ≤ r * 81 ^ ℓ := le_trans (Nat.le_mul_of_pos_left _ h4) h
  have h6 : r * 81 ^ ℓ < 2 ^ ℓ * 81 ^ ℓ := Nat.mul_lt_mul_of_pos_right hℓ (by positivity)
  omega

theorem cost_pivotLoop (PU : Matrix (Fin n) (Fin n) F) (J m : ℕ) (ans : CQ F n → Vec F n) :
    ∀ I st, (pivotLoop PU J m I st).cost ans ≤ I * ((J + 1) * m * 2)
  | 0, st => by simp [pivotLoop, cost]
  | I + 1, st => by
    simp only [pivotLoop]
    refine (cost_bind_le _ _ _ (I * ((J + 1) * m * 2)) (allOut_of_forall _ _ fun st' =>
      cost_pivotLoop PU J m ans I st')).trans ?_
    have := cost_pivotStep PU st.1 st.2 J m ans
    nlinarith

theorem pivotLoop_good (D : TriForm F n) (PU : Matrix (Fin n) (Fin n) F) (r0 s J : ℕ) :
    ∀ I r c st, r ≤ r0 → PivInv D PU r c st →
      1 - I * (1 / 2 ^ (J + 1) + 2 * (J + 1) / 2 ^ s) ≤
        (pivotLoop PU J (r0 + s) I st).prob (CQ.ans D)
          (PivInv D PU (rIter r I) (c + cIter r I))
  | 0, r, c, st, _, h => by
    simp only [pivotLoop, rIter, cIter, add_zero, Nat.cast_zero, zero_mul, sub_zero]
    rw [prob_of_allOut]; exact h
  | I + 1, r, c, st, hr, h => by
    simp only [pivotLoop]
    set η : ℝ := 1 / 2 ^ (J + 1) + 2 * (J + 1) / 2 ^ s
    have hη : 0 ≤ η := by positivity
    by_cases hbig : 1 ≤ ((I : ℝ) + 1) * η
    · refine le_trans ?_ (prob_nonneg _ _ _)
      push_cast; linarith
    push Not at hbig
    have h1 := pivotStep_good D PU st.1 st.2 r r0 c s J hr h
    have := prob_bind_ge (CQ.ans D) _ (pivotLoop PU J (r0 + s) I)
      (PivInv D PU (3 * r / 4) (c + r))
      (PivInv D PU (rIter r (I + 1)) (c + cIter r (I + 1))) η (I * η) h1
      (fun st' hst' => by
        have := pivotLoop_good D PU r0 s J I (3 * r / 4) (c + r) st'
          (by omega) hst'
        simp only [rIter, cIter] at this ⊢
        rw [show c + (r + cIter (3 * r / 4) I) = c + r + cIter (3 * r / 4) I by ring]
        exact this)
      (by positivity) (by nlinarith)
    push_cast
    linarith

end TriFormQ.W

end


-- ===== Solutions/W_StructAll.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Parameters of the structure stage, from `t = ⌈ρ⌉`. -/
def sR0 (t : ℕ) : ℕ := 2 * (t + 5)
def sL (t : ℕ) : ℕ := Nat.log 2 (sR0 t) + 1
def sI (t : ℕ) : ℕ := 4 * sL t
def sJ (t : ℕ) : ℕ := 4 * sL t + 5
def sS (t : ℕ) : ℕ := 4 * sL t + 8

/-- Stages 2a–2c: a good base point, its fiber `S_U`, and the pivot loop for `S_V, S_W`. -/
noncomputable def structAlg (t : ℕ) :
    CAlg (CQ F n) (Vec F n)
      (Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F) :=
  (basePoint (t + 4) (t + 4)).bind fun v =>
    (fiberProbe v (t + 3 + 4)).bind fun SU =>
      (pivotLoop (projMat SU) (sJ t) (sR0 t + sS t) (sI t) (1, 1)).map
        fun st => (projMat SU, st.1, st.2)

/-- Success of the structure stage. -/
def StructOK (D : TriForm F n) (t : ℕ)
    (P : Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F) :
    Prop :=
  (∀ x y z, TriForm.eval D (P.1 *ᵥ x) (P.2.1 *ᵥ y) (P.2.2 *ᵥ z) = 0) ∧
    n - P.1.rank ≤ t + 3 ∧ n - P.2.1.rank ≤ 4 * sR0 t ∧ n - P.2.2.rank ≤ 4 * sR0 t

theorem cost_structAlg (t : ℕ) (ans : CQ F n → Vec F n) :
    (structAlg (F := F) (n := n) t).cost ans ≤
      (t + 4 + 1) * (t + 4) + (t + 3 + 4) + sI t * ((sJ t + 1) * (sR0 t + sS t) * 2) := by
  unfold structAlg
  have hpiv : ∀ SU : Submodule F (Vec F n),
      ((pivotLoop (projMat SU) (sJ t) (sR0 t + sS t) (sI t) (1, 1)).map
        fun st => (projMat SU, st.1, st.2)).cost ans ≤
        sI t * ((sJ t + 1) * (sR0 t + sS t) * 2) := fun SU => by
    rw [cost_map]; exact cost_pivotLoop _ _ _ ans _ _
  have hfib : ∀ v : Vec F n, ((fiberProbe v (t + 3 + 4)).bind fun SU =>
      (pivotLoop (projMat SU) (sJ t) (sR0 t + sS t) (sI t) (1, 1)).map
        fun st => (projMat SU, st.1, st.2)).cost ans ≤
        (t + 3 + 4) + sI t * ((sJ t + 1) * (sR0 t + sS t) * 2) := fun v =>
    (cost_bind_le _ _ _ _ (allOut_of_forall _ _ hpiv)).trans
      (Nat.add_le_add_right (cost_fiberProbe _ _ ans) _)
  refine (cost_bind_le _ _ _ _ (allOut_of_forall _ _ hfib)).trans ?_
  have := cost_basePoint (F := F) (n := n) (t + 4) (t + 4) ans
  omega

lemma sixteen_sq_le (ℓ : ℕ) (h : 1 ≤ ℓ) : 16 * ℓ ^ 2 ≤ 16 ^ ℓ := by
  induction ℓ with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · have := ih hk
      have h3 : 16 ≤ 16 ^ k := by
        calc 16 = 16 ^ 1 := by norm_num
          _ ≤ 16 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have h2 : 16 * k ≤ 16 ^ k := by nlinarith
      rw [show (16 : ℕ) ^ (k + 1) = 16 ^ k * 16 from pow_succ 16 k]; nlinarith

lemma pivot_fail_le (t : ℕ) :
    (sI t : ℝ) * (1 / 2 ^ (sJ t + 1) + 2 * (sJ t + 1) / 2 ^ sS t) ≤ 1 / 20 := by
  set ℓ := sL t
  have hℓ : 1 ≤ ℓ := by simp [ℓ, sL]
  have h16 := sixteen_sq_le ℓ hℓ
  have h16r : (16 : ℝ) * (ℓ : ℝ) ^ 2 ≤ (16 : ℝ) ^ ℓ := by exact_mod_cast h16
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have e1 : (2 : ℝ) ^ (sJ t + 1) = 64 * 16 ^ ℓ := by
    simp only [sJ, ℓ]; rw [show 4 * sL t + 5 + 1 = 4 * sL t + 6 by ring, pow_add, pow_mul]; norm_num
    ring
  have e2 : (2 : ℝ) ^ sS t = 256 * 16 ^ ℓ := by
    simp only [sS, ℓ]; rw [pow_add, pow_mul]; norm_num; ring
  have hI : (sI t : ℝ) = 4 * ℓ := by simp [sI, ℓ]
  have hJ : ((sJ t : ℕ) : ℝ) + 1 = 4 * ℓ + 6 := by simp [sJ, ℓ]; ring
  rw [e1, e2, hI, hJ]
  set X : ℝ := (16 : ℝ) ^ ℓ
  have hpos : (0 : ℝ) < X := by positivity
  have key : 4 * (ℓ : ℝ) * (1 / (64 * X) + 2 * (4 * ℓ + 6) / (256 * X)) =
      (32 * (ℓ : ℝ) ^ 2 + 64 * ℓ) / (256 * X) := by
    field_simp; ring
  rw [key, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The structure stage succeeds with probability at least `2/3 - 1/16 - 1/20`. -/
theorem structAlg_good (D : TriForm F n) (ρ : ℝ)
    (hAR : (Fintype.card F : ℝ) ^ (2 * n) ≤ (Fintype.card F : ℝ) ^ ρ * (zeroLocus D).card) :
    2 / 3 - 1 / 16 - 1 / 20 ≤ (structAlg (F := F) (n := n) ⌈ρ⌉₊).prob (CQ.ans D)
      (StructOK D ⌈ρ⌉₊) := by
  classical
  set t := ⌈ρ⌉₊
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq2 : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast q_ge_two (F := F)
  have hd : ρ + 4 ≤ ((t + 4 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil ρ]
  unfold structAlg
  have h := prob_bind_ge (CQ.ans D) (basePoint (t + 4) (t + 4)) (fun v =>
    (fiberProbe v (t + 3 + 4)).bind fun SU =>
      (pivotLoop (projMat SU) (sJ t) (sR0 t + sS t) (sI t) (1, 1)).map
        fun st => (projMat SU, st.1, st.2)) (fun v => v ∈ goodS D ρ)
    (StructOK D t) (1 / 3) (1 / 16 + 1 / 20) (by linarith [basePoint_good D ρ hAR _ _ hd hd])
    ?_ (by norm_num) (by norm_num)
  · linarith
  intro v hv
  -- the fiber has codimension at most `t + 3`
  have hcodim : n - finrank F (LinearMap.ker (fiberLin D v)) ≤ t + 3 := by
    have hv1 := (Finset.mem_filter.1 hv).2.1
    have hcard : ((fiber D v).card : ℝ) = (Fintype.card F : ℝ) ^
        finrank F (LinearMap.ker (fiberLin D v)) := by
      have : fiber D v = Finset.univ.filter (· ∈ LinearMap.ker (fiberLin D v)) := by
        ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_ker_fiberLin]
      rw [this, card_submodule_toFinset]; push_cast; rfl
    rw [hcard] at hv1
    by_contra hcon
    push Not at hcon
    set k := finrank F (LinearMap.ker (fiberLin D v))
    have hk : k ≤ n := by
      have := Submodule.finrank_le (LinearMap.ker (fiberLin D v)); simpa using this
    have hρ : (Fintype.card F : ℝ) ^ ρ ≤ (Fintype.card F : ℝ) ^ t := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil ρ)
    have h1 : (Fintype.card F : ℝ) ^ n = (Fintype.card F : ℝ) ^ k *
        (Fintype.card F : ℝ) ^ (n - k) := by rw [← pow_add]; congr 1; omega
    have h2 : (Fintype.card F : ℝ) ^ (t + 4) ≤ (Fintype.card F : ℝ) ^ (n - k) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h3 : (16 : ℝ) * (Fintype.card F : ℝ) ^ t ≤ (Fintype.card F : ℝ) ^ (t + 4) := by
      rw [pow_add]
      have : (16 : ℝ) ≤ (Fintype.card F : ℝ) ^ 4 := by
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ _ := pow_le_pow_left₀ (by norm_num) hq2 4
      nlinarith [pow_pos hq t]
    have hpk : (0 : ℝ) < (Fintype.card F : ℝ) ^ k := by positivity
    have hpρ : (0 : ℝ) < (Fintype.card F : ℝ) ^ ρ := Real.rpow_pos_of_pos hq ρ
    nlinarith
  have h2 := prob_bind_ge (CQ.ans D) (fiberProbe v (t + 3 + 4)) (fun SU =>
      (pivotLoop (projMat SU) (sJ t) (sR0 t + sS t) (sI t) (1, 1)).map
        fun st => (projMat SU, st.1, st.2))
    (fun SU => ∀ u, u ∈ SU ↔ u ∈ fiber D v) (StructOK D t) (1 / 16) (1 / 20)
    (by have := fiberProbe_exact D v (t + 3) 4 hcodim; norm_num at this ⊢; linarith) ?_
    (by norm_num) (by norm_num)
  · linarith
  intro SU hSU
  set PU := projMat SU
  -- initial invariant
  have hinit : PivInv D PU (sR0 t) 0 (1, 1) := by
    refine ⟨fun x => ?_, by simp [Matrix.rank_one], by simp [Matrix.rank_one]⟩
    have : mView D PU (1, 1).1 (1, 1).2 x = sliceU D (PU *ᵥ x) := by simp [mView]
    rw [this]
    exact fact2' D ρ v hv _ ((hSU _).1 (projMat_mem SU x))
  have hloop := pivotLoop_good D PU (sR0 t) (sS t) (sJ t) (sI t) (sR0 t) 0 (1, 1) le_rfl hinit
  have hzero : rIter (sR0 t) (sI t) = 0 := by
    apply rIter_zero
    simp only [sL]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  rw [prob_map]
  refine le_trans ?_ (le_trans hloop (prob_mono _ _ fun st hst => ?_))
  · have := pivot_fail_le t
    linarith
  · obtain ⟨hst1, hst2, hst3⟩ := hst
    rw [hzero] at hst1
    have hc := cIter_le (sI t) (sR0 t)
    refine ⟨fun x y z => ?_, ?_, by simp only at hst2 ⊢; omega, by simp only at hst3 ⊢; omega⟩
    · rw [eval_mView]
      have : mView D PU st.1 st.2 x = 0 := by
        have h0 := hst1 x
        have h00 := Nat.le_zero.1 h0
        have hr := LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 h00)
        ext i j
        have h2 := congrArg (fun f => f (Pi.single j 1) i) hr
        simpa [Matrix.mulVecLin_apply, mulVec, dotProduct, Pi.single_apply] using h2
      rw [this, Matrix.zero_mulVec, dotProduct_zero]
    · show n - (projMat SU).rank ≤ t + 3
      rw [rank_projMat]
      have : SU = LinearMap.ker (fiberLin D v) := by
        ext u; rw [hSU, mem_ker_fiberLin]
      rw [this]; exact hcodim

end TriFormQ.W

end


-- ===== Solutions/W_Slices.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Multilinearity of `TriForm.eval` -/

lemma eval_add1 (θ : TriForm F n) (a b v w : Vec F n) :
    TriForm.eval θ (a + b) v w = TriForm.eval θ a v w + TriForm.eval θ b v w := by
  simp [TriForm.eval, mul_add, add_mul, Finset.sum_add_distrib]
lemma eval_add2 (θ : TriForm F n) (u a b w : Vec F n) :
    TriForm.eval θ u (a + b) w = TriForm.eval θ u a w + TriForm.eval θ u b w := by
  simp [TriForm.eval, mul_add, add_mul, Finset.sum_add_distrib]
lemma eval_add3 (θ : TriForm F n) (u v a b : Vec F n) :
    TriForm.eval θ u v (a + b) = TriForm.eval θ u v a + TriForm.eval θ u v b := by
  simp [TriForm.eval, mul_add, add_mul, Finset.sum_add_distrib]

lemma sum_smul_apply' {k : ℕ} (α : Fin k → F) (a : Fin k → Vec F n) (j : Fin n) :
    (∑ i, α i • a i) j = ∑ i, α i * a i j := by simp [Finset.sum_apply]

lemma sw3' {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → F) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma sw4' {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E]
    (f : A → B → C → E → F) :
    ∑ a, ∑ b, ∑ c, ∑ x, f a b c x = ∑ x, ∑ a, ∑ b, ∑ c, f a b c x := by
  rw [Finset.sum_congr rfl fun a _ => sw3' (fun b c x => f a b c x)]
  exact Finset.sum_comm

lemma eval_sum1 (θ : TriForm F n) {k : ℕ} (α : Fin k → F) (a : Fin k → Vec F n) (v w : Vec F n) :
    TriForm.eval θ (∑ i, α i • a i) v w = ∑ i, α i * TriForm.eval θ (a i) v w := by
  simp only [TriForm.eval, sum_smul_apply', Finset.mul_sum, Finset.sum_mul]
  rw [sw4']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

lemma eval_sum2 (θ : TriForm F n) {k : ℕ} (u : Vec F n) (α : Fin k → F) (a : Fin k → Vec F n)
    (w : Vec F n) :
    TriForm.eval θ u (∑ i, α i • a i) w = ∑ i, α i * TriForm.eval θ u (a i) w := by
  simp only [TriForm.eval, sum_smul_apply', Finset.mul_sum, Finset.sum_mul]
  rw [sw4']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

lemma eval_sum3 (θ : TriForm F n) {k : ℕ} (u v : Vec F n) (α : Fin k → F) (a : Fin k → Vec F n) :
    TriForm.eval θ u v (∑ i, α i • a i) = ∑ i, α i * TriForm.eval θ u v (a i) := by
  simp only [TriForm.eval, sum_smul_apply', Finset.mul_sum, Finset.sum_mul]
  rw [sw4']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

lemma triForm_eq_zero_of_eval (E : TriForm F n) (h : ∀ u v w, TriForm.eval E u v w = 0) :
    E = 0 := by
  funext i j k
  have := h (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)
  simpa [TriForm.eval, Pi.single_apply] using this

/-! ### Slice matrices -/

/-- `f⟨v⟩` as a matrix on `U × W`. -/
def sliceVm (θ : TriForm F n) (v : Vec F n) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i k => ∑ j, θ i j k * v j

/-- `f(·, ·, w)` as a matrix on `U × V`. -/
def sliceWm (θ : TriForm F n) (w : Vec F n) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => ∑ k, θ i j k * w k

lemma sliceVm_mulVec (θ : TriForm F n) (v z : Vec F n) :
    sliceVm θ v *ᵥ z = CQ.ans θ (.yz v z) := by
  funext i
  simp only [sliceVm, mulVec, dotProduct, of_apply, CQ.ans, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma vecMul_sliceVm (θ : TriForm F n) (u v : Vec F n) :
    u ᵥ* sliceVm θ v = CQ.ans θ (.xy u v) := by
  funext k
  simp only [sliceVm, vecMul, dotProduct, of_apply, CQ.ans, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma sliceWm_mulVec (θ : TriForm F n) (w y : Vec F n) :
    sliceWm θ w *ᵥ y = CQ.ans θ (.yz y w) := by
  funext i
  simp only [sliceWm, mulVec, dotProduct, of_apply, CQ.ans, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma vecMul_sliceWm (θ : TriForm F n) (u w : Vec F n) :
    u ᵥ* sliceWm θ w = CQ.ans θ (.xz u w) := by
  funext j
  simp only [sliceWm, vecMul, dotProduct, of_apply, CQ.ans, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma eval_sliceVm (θ : TriForm F n) (u v z : Vec F n) :
    TriForm.eval θ u v z = u ⬝ᵥ (sliceVm θ v *ᵥ z) := by
  rw [sliceVm_mulVec, eval_yz, dotProduct_comm]

lemma eval_sliceWm (θ : TriForm F n) (u y w : Vec F n) :
    TriForm.eval θ u y w = u ⬝ᵥ (sliceWm θ w *ᵥ y) := by
  rw [sliceWm_mulVec, eval_yz, dotProduct_comm]

lemma sliceU_sub' (θ θ' : TriForm F n) (u : Vec F n) :
    sliceU (θ - θ') u = sliceU θ u - sliceU θ' u := by
  ext j k; simp [sliceU, sub_mul, Finset.sum_sub_distrib]
lemma sliceVm_sub (θ θ' : TriForm F n) (v : Vec F n) :
    sliceVm (θ - θ') v = sliceVm θ v - sliceVm θ' v := by
  ext j k; simp [sliceVm, sub_mul, Finset.sum_sub_distrib]
lemma sliceWm_sub (θ θ' : TriForm F n) (w : Vec F n) :
    sliceWm (θ - θ') w = sliceWm θ w - sliceWm θ' w := by
  ext j k; simp [sliceWm, sub_mul, Finset.sum_sub_distrib]

/-! ### Slice data -/

section SD
variable {ι : Type}

/-- Slice `A_i = f(u, ·, ·)`. -/
def sdA (T : ι → TriForm F n) (u : Vec F n) : SliceData (CQ F n) (Vec F n) F n ι where
  φ := fun mq => match mq with
    | .right z => .xz u z
    | .left y => .xy u y
  ψ := fun _ r => r
  val := fun j => sliceU (T j) u

/-- Slice `B_j = f(P_U ·, v, ·)`. -/
def sdB (T : ι → TriForm F n) (PU : Matrix (Fin n) (Fin n) F) (v : Vec F n) :
    SliceData (CQ F n) (Vec F n) F n ι where
  φ := fun mq => match mq with
    | .right z => .yz v z
    | .left x => .xy (PU *ᵥ x) v
  ψ := fun mq r => match mq with
    | .right _ => PUᵀ *ᵥ r
    | .left _ => r
  val := fun j => PUᵀ * sliceVm (T j) v

/-- Slice `C_k = f(P_U ·, P_V ·, w)`. -/
def sdC (T : ι → TriForm F n) (PU PV : Matrix (Fin n) (Fin n) F) (w : Vec F n) :
    SliceData (CQ F n) (Vec F n) F n ι where
  φ := fun mq => match mq with
    | .right y => .yz (PV *ᵥ y) w
    | .left x => .xz (PU *ᵥ x) w
  ψ := fun mq r => match mq with
    | .right _ => PUᵀ *ᵥ r
    | .left _ => r ᵥ* PV
  val := fun j => PUᵀ * sliceWm (T j) w * PV

lemma sdA_sim (T : ι → TriForm F n) (u : Vec F n) (θ : TriForm F n) (mq : MQ F n) :
    (sdA T u).ψ mq (CQ.ans θ ((sdA T u).φ mq)) = MQ.ans (sliceU θ u) mq := by
  cases mq with
  | right z => simp [sdA, MQ.ans, ans_xz_mulVec]
  | left y => simp [sdA, MQ.ans, ans_xy_vecMul]

lemma sdB_sim (T : ι → TriForm F n) (PU : Matrix (Fin n) (Fin n) F) (v : Vec F n)
    (θ : TriForm F n) (mq : MQ F n) :
    (sdB T PU v).ψ mq (CQ.ans θ ((sdB T PU v).φ mq)) = MQ.ans (PUᵀ * sliceVm θ v) mq := by
  cases mq with
  | right z => simp [sdB, MQ.ans, ← Matrix.mulVec_mulVec, sliceVm_mulVec]
  | left x =>
    simp only [sdB, MQ.ans, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, vecMul_sliceVm]

lemma sdC_sim (T : ι → TriForm F n) (PU PV : Matrix (Fin n) (Fin n) F) (w : Vec F n)
    (θ : TriForm F n) (mq : MQ F n) :
    (sdC T PU PV w).ψ mq (CQ.ans θ ((sdC T PU PV w).φ mq)) =
      MQ.ans (PUᵀ * sliceWm θ w * PV) mq := by
  cases mq with
  | right y => simp [sdC, MQ.ans, ← Matrix.mulVec_mulVec, sliceWm_mulVec]
  | left x =>
    simp only [sdC, MQ.ans, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, vecMul_sliceWm]

end SD

/-! ### Complements -/

/-- A complement of `S`. -/
noncomputable def compL (S : Submodule F (Vec F n)) : Submodule F (Vec F n) :=
  Classical.choose (Submodule.exists_isCompl S)

lemma compL_isCompl (S : Submodule F (Vec F n)) : IsCompl S (compL S) :=
  Classical.choose_spec (Submodule.exists_isCompl S)

lemma finrank_compL (S : Submodule F (Vec F n)) : finrank F (compL S) = n - finrank F S := by
  have h := Submodule.finrank_add_eq_of_isCompl (compL_isCompl S)
  rw [finrank_vec] at h; omega

/-- A basis of the complement, indexed by `Fin (n - dim S)`. -/
noncomputable def compBasis (S : Submodule F (Vec F n)) :
    Module.Basis (Fin (n - finrank F S)) F (compL S) :=
  Module.finBasisOfFinrankEq F (compL S) (finrank_compL S)

noncomputable def compVecs (S : Submodule F (Vec F n)) : Fin (n - finrank F S) → Vec F n :=
  fun i => (compBasis S i : Vec F n)

lemma compVecs_span (S : Submodule F (Vec F n)) (u : Vec F n) :
    ∃ s ∈ S, ∃ α : Fin (n - finrank F S) → F, u = s + ∑ i, α i • compVecs S i := by
  have hsup : S ⊔ compL S = ⊤ := (compL_isCompl S).sup_eq_top
  have hu : u ∈ S ⊔ compL S := hsup ▸ Submodule.mem_top
  obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hu
  refine ⟨s, hs, fun i => (compBasis S).repr ⟨l, hl⟩ i, ?_⟩
  congr 1
  have := (compBasis S).sum_repr ⟨l, hl⟩
  have h2 := congrArg (fun x : compL S => (x : Vec F n)) this
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  exact h2.symm

lemma range_mem_iff (P : Matrix (Fin n) (Fin n) F) (u : Vec F n) :
    u ∈ LinearMap.range P.mulVecLin ↔ ∃ x, u = P *ᵥ x := by
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩

/-- Equations (32)–(33) in the form used: a form vanishing on `range P_U × range P_V × range P_W`
whose `A`-, `B`- and `C`-slices vanish is zero. -/
theorem eq33' (E : TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F)
    (h0 : ∀ x y z, TriForm.eval E (PU *ᵥ x) (PV *ᵥ y) (PW *ᵥ z) = 0)
    (hA : ∀ i, sliceU E (compVecs (LinearMap.range PU.mulVecLin) i) = 0)
    (hB : ∀ j, PUᵀ * sliceVm E (compVecs (LinearMap.range PV.mulVecLin) j) = 0)
    (hC : ∀ k, PUᵀ * sliceWm E (compVecs (LinearMap.range PW.mulVecLin) k) * PV = 0) :
    E = 0 := by
  apply triForm_eq_zero_of_eval
  intro u v w
  obtain ⟨su, hsu, α, rfl⟩ := compVecs_span (LinearMap.range PU.mulVecLin) u
  obtain ⟨x, rfl⟩ := (range_mem_iff PU su).1 hsu
  obtain ⟨sv, hsv, β, rfl⟩ := compVecs_span (LinearMap.range PV.mulVecLin) v
  obtain ⟨y, rfl⟩ := (range_mem_iff PV sv).1 hsv
  obtain ⟨sw, hsw, γ, rfl⟩ := compVecs_span (LinearMap.range PW.mulVecLin) w
  obtain ⟨z, rfl⟩ := (range_mem_iff PW sw).1 hsw
  rw [eval_add1, eval_sum1]
  have hAterm : ∀ i, TriForm.eval E (compVecs (LinearMap.range PU.mulVecLin) i)
      (PV *ᵥ y + ∑ j, β j • compVecs (LinearMap.range PV.mulVecLin) j)
      (PW *ᵥ z + ∑ k, γ k • compVecs (LinearMap.range PW.mulVecLin) k) = 0 := by
    intro i; rw [eval_sliceU, hA i, Matrix.zero_mulVec, dotProduct_zero]
  simp only [hAterm, mul_zero, Finset.sum_const_zero, add_zero]
  rw [eval_add2, eval_sum2]
  have hBterm : ∀ j, TriForm.eval E (PU *ᵥ x) (compVecs (LinearMap.range PV.mulVecLin) j)
      (PW *ᵥ z + ∑ k, γ k • compVecs (LinearMap.range PW.mulVecLin) k) = 0 := by
    intro j
    rw [eval_sliceVm, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hB j,
      Matrix.zero_mulVec, dotProduct_zero]
  simp only [hBterm, mul_zero, Finset.sum_const_zero, add_zero]
  rw [eval_add3, eval_sum3, h0]
  have hCterm : ∀ k, TriForm.eval E (PU *ᵥ x) (PV *ᵥ y)
      (compVecs (LinearMap.range PW.mulVecLin) k) = 0 := by
    intro k
    rw [eval_sliceWm, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hC k, Matrix.zero_mulVec, dotProduct_zero]
  simp only [hCterm, mul_zero, Finset.sum_const_zero, zero_add]

end TriFormQ.W

end


-- ===== Solutions/W_Attempt.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The slices determined by the structure `(P_U, P_V, P_W)`. -/
noncomputable def sliceList {L : ℕ} (T : Fin L → TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) :
    List (SliceData (CQ F n) (Vec F n) F n (Fin L)) :=
  (List.ofFn fun i => sdA T (compVecs (LinearMap.range PU.mulVecLin) i)) ++
    (List.ofFn fun j => sdB T PU (compVecs (LinearMap.range PV.mulVecLin) j)) ++
    (List.ofFn fun k => sdC T PU PV (compVecs (LinearMap.range PW.mulVecLin) k))

lemma sliceList_length {L : ℕ} (T : Fin L → TriForm F n) (PU PV PW : Matrix (Fin n) (Fin n) F) :
    (sliceList T PU PV PW).length = (n - PU.rank) + (n - PV.rank) + (n - PW.rank) := by
  simp only [sliceList, List.length_append, List.length_ofFn, rank_eq_finrank]

/-- One attempt of the identification algorithm. -/
noncomputable def attempt {L : ℕ} (T : Fin L → TriForm F n) (t k1 kmax : ℕ) (ε' : ℝ) :
    CAlg (CQ F n) (Vec F n) (Option (Fin L)) :=
  (prefilter k1 (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2) (fun j => CQ.ans (T j))
    Finset.univ).bind fun S =>
    if hS : S.Nonempty then
      (mapQ id (fun q r => r - CQ.ans (T (S.min' hS)) q) (structAlg t)).bind fun P =>
        if n - P.1.rank ≤ t + 3 ∧ n - P.2.1.rank ≤ 4 * sR0 t ∧ n - P.2.2.rank ≤ 4 * sR0 t then
          seqId ε' kmax (sliceList T P.1 P.2.1 P.2.2)
            (S.filter fun j => ∀ x y z,
              TriForm.eval (T j - T (S.min' hS)) (P.1 *ᵥ x) (P.2.1 *ᵥ y) (P.2.2 *ᵥ z) = 0)
        else ret none
    else ret none

lemma zeroLocus_sub_comm (θ θ' : TriForm F n) : zeroLocus (θ - θ') = zeroLocus (θ' - θ) := by
  ext p
  simp only [zeroLocus, Finset.mem_filter, Finset.mem_univ, true_and, eval_sub]
  constructor <;> intro h z <;> have := h z <;> linear_combination -this

lemma AR_sub_comm (θ θ' : TriForm F n) : AR (θ - θ') = AR (θ' - θ) := by
  unfold AR; rw [zeroLocus_sub_comm]

/-- Number of slices allowed by the caps. -/
def mBound (t : ℕ) : ℕ := (t + 3) + 2 * (4 * sR0 t)

theorem attempt_good {L : ℕ} (T : Fin L → TriForm F n) (i : Fin L) (ρ : ℝ) (k1 kmax : ℕ)
    (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1)
    (hk1 : (L : ℝ) * ((Fintype.card F : ℝ) ^ ρ)⁻¹ ^ k1 ≤ 1 / 32)
    (hkmax : L < 2 ^ (2 ^ kmax))
    (hεsmall : ((mBound ⌈ρ⌉₊ * (kmax + 1) : ℕ) : ℝ) * ε' ≤ 1 / 20) :
    2 / 5 ≤ (attempt T ⌈ρ⌉₊ k1 kmax ε').prob (CQ.ans (T i)) (fun o => ∃ j, o = some j ∧ T j = T i) := by
  classical
  set t := ⌈ρ⌉₊
  set θ := T i
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  unfold attempt
  refine le_trans (by norm_num : (2 : ℝ) / 5 ≤ 1 - 1 / 32 - ((1 / 3 + 1 / 16 + 1 / 20) + 1 / 20))
    (prob_bind_ge (CQ.ans θ) _ _ (fun S => i ∈ S ∧ ∀ j ∈ S, AR (T j - θ) ≤ ρ) _ (1 / 32)
      ((1 / 3 + 1 / 16 + 1 / 20) + 1 / 20) ?_ ?_ (by norm_num) (by norm_num))
  · -- prefilter
    refine prob_ge_of_fail _ _ ?_
    have hall := allOut_prefilter (CQ.ans θ) k1 (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2)
      (fun j => CQ.ans (T j)) Finset.univ
    refine (prob_mono_allOut _ _ (P' := fun S => ∃ j ∈ S, ρ < AR (T j - θ))
      (allOut_mono _ _ (fun S hS hn => ?_) hall)).trans ?_
    · have hiS : i ∈ S := hS.2 i (Finset.mem_univ _) (fun ω => rfl)
      by_contra hc; push Not at hc
      exact hn ⟨hiS, fun j hj => hc j hj⟩
    · refine (prob_prefilter_bad' (CQ.ans θ) k1 (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2)
        (fun j => CQ.ans (T j)) Finset.univ (fun j => ρ < AR (T j - θ))
        ((Fintype.card F : ℝ) ^ ρ)⁻¹ (by positivity) ?_).trans ?_
      · intro j _ hj
        rw [agreeProb_tri]
        have h := (AR_le_iff (T j - θ) ρ).not.1 (not_le.2 hj)
        push Not at h
        have hZ : (0 : ℝ) < (zeroLocus (T j - θ)).card := by
          exact_mod_cast zeroLocus_card_pos _
        rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
        linarith
      · simpa [Finset.card_univ, Fintype.card_fin] using hk1
  · -- the rest
    rintro S ⟨hiS, hAR⟩
    have hS : S.Nonempty := ⟨i, hiS⟩
    rw [dif_pos hS]
    set s := S.min' hS
    set D := θ - T s
    have hDAR : (Fintype.card F : ℝ) ^ (2 * n) ≤ (Fintype.card F : ℝ) ^ ρ * (zeroLocus D).card := by
      rw [← AR_le_iff, AR_sub_comm]; exact hAR s (S.min'_mem hS)
    have hsim : (fun q => (fun q r => r - CQ.ans (T s) q) q (CQ.ans θ (id q))) = CQ.ans D := by
      funext q; simp [D, ans_sub]
    refine le_trans (by norm_num) (prob_bind_ge (CQ.ans θ) _ _ (StructOK D t) _
      (1 / 3 + 1 / 16 + 1 / 20) (1 / 20) ?_ ?_ (by norm_num) (by norm_num))
    · rw [prob_mapQ, hsim]
      have := structAlg_good D ρ hDAR
      linarith
    · intro P hP
      obtain ⟨h0, hcU, hcV, hcW⟩ := hP
      rw [if_pos ⟨hcU, hcV, hcW⟩]
      set C := S.filter fun j => ∀ x y z,
        TriForm.eval (T j - T s) (P.1 *ᵥ x) (P.2.1 *ᵥ y) (P.2.2 *ᵥ z) = 0
      have hiC : i ∈ C := Finset.mem_filter.2 ⟨hiS, h0⟩
      have hCcard : C.card < 2 ^ (2 ^ kmax) := lt_of_le_of_lt (by
        have := Finset.card_le_univ C; simpa using this) hkmax
      have hsimd : ∀ d ∈ sliceList T P.1 P.2.1 P.2.2, ∀ mq,
          d.ψ mq (CQ.ans θ (d.φ mq)) = MQ.ans (d.val i) mq := by
        intro d hd mq
        simp only [sliceList, List.mem_append, List.mem_ofFn] at hd
        rcases hd with (⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
        · exact sdA_sim T _ θ mq
        · exact sdB_sim T _ _ θ mq
        · exact sdC_sim T _ _ _ θ mq
      have hseq := seqId_correct ε' hε' hε1 kmax (CQ.ans θ) i (sliceList T P.1 P.2.1 P.2.2) C
        hiC hCcard hsimd
      have hlen : ((sliceList T P.1 P.2.1 P.2.2).length * (kmax + 1) : ℕ) ≤
          mBound t * (kmax + 1) := by
        rw [sliceList_length]
        apply Nat.mul_le_mul_right
        simp only [mBound]; omega
      have hlenr : (((sliceList T P.1 P.2.1 P.2.2).length * (kmax + 1) : ℕ) : ℝ) * ε' ≤ 1 / 20 :=
        le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hε'.le) hεsmall
      refine le_trans (by linarith) (le_trans hseq (prob_mono _ _ fun o ho => ?_))
      obtain ⟨j, rfl, hjC, hjd⟩ := ho
      refine ⟨j, rfl, ?_⟩
      have hjC' := (Finset.mem_filter.1 hjC).2
      have hE := eq33' (T j - θ) P.1 P.2.1 P.2.2
        (fun x y z => by
          have h1 := hjC' x y z
          have h2 := h0 x y z
          simp only [D, eval_sub] at h1 h2 ⊢
          linear_combination h1 - h2)
        (fun k => by
          have := hjd _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
            (List.mem_ofFn.2 ⟨k, rfl⟩)))))
          simp only [sdA] at this
          rw [sliceU_sub', this, sub_self])
        (fun k => by
          have := hjd _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
            (List.mem_ofFn.2 ⟨k, rfl⟩)))))
          simp only [sdB] at this
          rw [sliceVm_sub, Matrix.mul_sub, this, sub_self])
        (fun k => by
          have := hjd _ (List.mem_append.2 (Or.inr (List.mem_ofFn.2 ⟨k, rfl⟩)))
          simp only [sdC] at this
          rw [sliceWm_sub, Matrix.mul_sub, Matrix.sub_mul, this, sub_self])
      exact sub_eq_zero.1 hE

end TriFormQ.W

end


-- ===== Solutions/W_Amp.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

section Amp
variable {Q R : Type} {L : ℕ}

/-- Run `N` independent copies of `A` and collect their outputs. -/
noncomputable def collect (A : CAlg Q R (Option (Fin L))) : ℕ → CAlg Q R (Finset (Fin L))
  | 0 => ret ∅
  | N + 1 => A.bind fun o => (collect A N).map fun S => match o with
      | some j => insert j S
      | none => S

theorem collect_good (A : CAlg Q R (Option (Fin L))) (ans : Q → R) (good : Fin L → Prop)
    (p : ℝ) (hp : 0 ≤ p) (hA : A.prob ans (fun o => ¬ ∃ j, o = some j ∧ good j) ≤ p) :
    ∀ N, (collect A N).prob ans (fun S => ¬ ∃ j ∈ S, good j) ≤ p ^ N
  | 0 => by
    simp only [collect, pow_zero]; exact prob_le_one _ _ _
  | N + 1 => by
    classical
    simp only [collect]
    rw [prob_bind]
    have hN := collect_good A ans good p hp hA N
    refine le_trans (expect_mono _ _ (g' := fun o =>
      p ^ N * (if ¬ ∃ j, o = some j ∧ good j then 1 else 0)) (fun o => ?_)) ?_
    · rw [prob_map]
      rcases o with _ | j
      · have hno : ¬ ∃ j, (none : Option (Fin L)) = some j ∧ good j := by simp
        rw [if_pos hno, mul_one]
        exact hN
      · by_cases hj : good j
        · have hno : ∃ j', (some j : Option (Fin L)) = some j' ∧ good j' := ⟨j, rfl, hj⟩
          rw [if_neg (not_not.2 hno), mul_zero]
          have h := prob_of_allOut ans (collect A N) (P := fun S => ∃ j' ∈ insert j S, good j')
            (allOut_of_forall _ _ fun S => ⟨j, Finset.mem_insert_self _ _, hj⟩)
          have h2 := prob_compl ans (collect A N) (fun S => ∃ j' ∈ insert j S, good j')
          have : (collect A N).prob ans (fun S => ¬ ∃ j' ∈ insert j S, good j') = 0 := by
            linarith
          exact this.le
        · have hno : ¬ ∃ j', (some j : Option (Fin L)) = some j' ∧ good j' := by
            rintro ⟨j', hj', hg⟩; cases hj'; exact hj hg
          rw [if_pos hno, mul_one]
          refine le_trans (prob_mono _ _ fun S hS => ?_) hN
          rintro ⟨j', hj'S, hj'⟩
          exact hS ⟨j', Finset.mem_insert_of_mem hj'S, hj'⟩
    · rw [expect_smul]
      have e : A.expect ans (fun o => if ¬ ∃ j, o = some j ∧ good j then (1 : ℝ) else 0) =
          A.prob ans (fun o => ¬ ∃ j, o = some j ∧ good j) := by
        unfold prob; congr 1; funext o
        by_cases h : ∃ j, o = some j ∧ good j <;> simp [h]
      rw [e]
      calc p ^ N * A.prob ans (fun o => ¬ ∃ j, o = some j ∧ good j) ≤ p ^ N * p :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = p ^ (N + 1) := by ring

theorem cost_collect (A : CAlg Q R (Option (Fin L))) (ans : Q → R) (c : ℕ)
    (hc : A.cost ans ≤ c) : ∀ N, (collect A N).cost ans ≤ N * c
  | 0 => by simp [collect, cost]
  | N + 1 => by
    simp only [collect]
    refine (cost_bind_le _ _ _ (N * c) (allOut_of_forall _ _ fun o => ?_)).trans ?_
    · rw [cost_map]; exact cost_collect A ans c hc N
    · nlinarith

end Amp

/-- Final selection among collected candidates with a prefilter. -/
noncomputable def finalSel {L : ℕ} (T : Fin L → TriForm F n) (j0 : Fin L) (k2 : ℕ)
    (C : Finset (Fin L)) : CAlg (CQ F n) (Vec F n) (Fin L) :=
  (prefilter k2 (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2) (fun j => CQ.ans (T j)) C).map
    fun S => if h : S.Nonempty then S.min' h else j0

theorem cost_finalSel {L : ℕ} (T : Fin L → TriForm F n) (j0 : Fin L) (k2 : ℕ)
    (C : Finset (Fin L)) (ans : CQ F n → Vec F n) : (finalSel T j0 k2 C).cost ans ≤ k2 := by
  unfold finalSel; rw [cost_map]; exact cost_prefilter _ _ _ _ _

/-- A nonzero difference agrees with the oracle at a uniform `(u, v)` with probability `≤ 3/4`. -/
lemma agreeProb_ne {L : ℕ} (T : Fin L → TriForm F n) (θ : TriForm F n) (j : Fin L)
    (hj : T j ≠ θ) :
    agreeProb (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2) (fun j => CQ.ans (T j)) (CQ.ans θ) j
      ≤ 3 / 4 := by
  rw [agreeProb_tri]
  have h := zeroLocus_card_le_of_ne_zero (T j - θ) (sub_ne_zero.2 hj)
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ (2 * n) := by positivity
  rw [div_le_iff₀ hq]
  have : (4 : ℝ) * (zeroLocus (T j - θ)).card ≤ 3 * (Fintype.card F : ℝ) ^ (2 * n) := by
    exact_mod_cast h
  linarith

theorem finalSel_good {L : ℕ} (T : Fin L → TriForm F n) (j0 : Fin L) (k2 : ℕ)
    (C : Finset (Fin L)) (i : Fin L) (hC : ∃ j ∈ C, T j = T i) :
    1 - C.card * (3 / 4 : ℝ) ^ k2 ≤ (finalSel T j0 k2 C).prob (CQ.ans (T i))
      (fun j => T j = T i) := by
  classical
  unfold finalSel
  rw [prob_map]
  obtain ⟨j1, hj1C, hj1⟩ := hC
  have hall := allOut_prefilter (CQ.ans (T i)) k2 (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2)
    (fun j => CQ.ans (T j)) C
  refine prob_ge_of_fail _ _ ?_
  refine (prob_mono_allOut _ _ (P' := fun S => ∃ j ∈ S, T j ≠ T i)
    (allOut_mono _ _ (fun S hS hn => ?_) hall)).trans ?_
  · have hj1S : j1 ∈ S := hS.2 j1 hj1C (fun ω => by simp [hj1])
    have hne : S.Nonempty := ⟨j1, hj1S⟩
    rw [dif_pos hne] at hn
    exact ⟨S.min' hne, S.min'_mem hne, hn⟩
  · exact prob_prefilter_bad' _ _ _ _ C (fun j => T j ≠ T i) (3 / 4) (by norm_num)
      (fun j _ hj => agreeProb_ne T (T i) j hj)

end TriFormQ.W

end


-- ===== Solutions/W_Cost.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

lemma cPhi_mono (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (kmax m m' N N' : ℕ) (hm : m ≤ m')
    (hN : N ≤ N') (hN' : 1 ≤ N') : cPhi ε' kmax m N ≤ cPhi ε' kmax m' N' := by
  unfold cPhi
  have hK1 := cK1_nonneg ε' hε' hε1
  have hlog : Real.logb 2 N ≤ Real.logb 2 N' := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp only [Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hN')
    · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) (by exact_mod_cast hN)
  have hlog0 : 0 ≤ Real.logb 2 N := logb_two_nat_nonneg N
  have hmr : (m : ℝ) ≤ m' := by exact_mod_cast hm
  have h1 : Real.sqrt (m * Real.logb 2 N) ≤ Real.sqrt (m' * Real.logb 2 N') :=
    Real.sqrt_le_sqrt (mul_le_mul hmr hlog hlog0 (by positivity))
  have h2 : (m : ℝ) * (12 + (kmax + 1) * cK1 ε') ≤ m' * (12 + (kmax + 1) * cK1 ε') :=
    mul_le_mul_of_nonneg_right hmr (by positivity)
  linarith

/-- Worst-case query count of the structure stage. -/
def structCost (t : ℕ) : ℕ :=
  (t + 4 + 1) * (t + 4) + (t + 3 + 4) + sI t * ((sJ t + 1) * (sR0 t + sS t) * 2)

theorem cost_attempt {L : ℕ} (hL : 1 ≤ L) (T : Fin L → TriForm F n) (t k1 kmax : ℕ) (ε' : ℝ)
    (hε' : 0 < ε') (hε1 : ε' ≤ 1) (ans : CQ F n → Vec F n) :
    ((attempt T t k1 kmax ε').cost ans : ℝ) ≤
      k1 + structCost t + cPhi ε' kmax (mBound t) L := by
  have hΦ0 : 0 ≤ cPhi ε' kmax (mBound t) L := by
    unfold cPhi
    have := cK1_nonneg ε' hε' hε1
    have := cS_nonneg ε' hε' hε1 (kmax + 1)
    positivity
  unfold attempt
  have hcont : ∀ S : Finset (Fin L), ((if hS : S.Nonempty then
      (mapQ id (fun q r => r - CQ.ans (T (S.min' hS)) q) (structAlg t)).bind fun P =>
        if n - P.1.rank ≤ t + 3 ∧ n - P.2.1.rank ≤ 4 * sR0 t ∧ n - P.2.2.rank ≤ 4 * sR0 t then
          seqId ε' kmax (sliceList T P.1 P.2.1 P.2.2)
            (S.filter fun j => ∀ x y z,
              TriForm.eval (T j - T (S.min' hS)) (P.1 *ᵥ x) (P.2.1 *ᵥ y) (P.2.2 *ᵥ z) = 0)
        else ret none
    else ret none).cost ans : ℝ) ≤ structCost t + cPhi ε' kmax (mBound t) L := by
    intro S
    split_ifs with hS
    · refine le_trans (cost_bind_le_real ans _ _ (cPhi ε' kmax (mBound t) L) hΦ0 fun P => ?_) ?_
      · split_ifs with hcap
        · refine le_trans (seqId_cost ε' hε' hε1 kmax ans _ _) (cPhi_mono ε' hε' hε1 kmax _ _ _ _
            ?_ ?_ hL)
          · rw [sliceList_length]; simp only [mBound]; omega
          · exact (Finset.card_le_univ _).trans (by simp)
        · simp [cost]; exact hΦ0
      · rw [cost_mapQ]
        have := cost_structAlg (F := F) (n := n) t (fun q => (fun q r => r - CQ.ans (T (S.min' hS)) q)
          q (ans (id q)))
        have h : ((structAlg (F := F) (n := n) t).cost (fun q => (fun q r =>
            r - CQ.ans (T (S.min' hS)) q) q (ans (id q))) : ℝ) ≤ structCost t := by
          exact_mod_cast this
        linarith
    · simp only [cost, Nat.cast_zero]
      have : (0 : ℝ) ≤ structCost t := by positivity
      linarith
  refine le_trans (cost_bind_le_real ans _ _ _ (by positivity) hcont) ?_
  have := cost_prefilter ans k1 (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2)
    (fun j => CQ.ans (T j)) Finset.univ
  have : ((prefilter k1 (fun p : Vec F n × Vec F n => CQ.xy p.1 p.2)
    (fun j => CQ.ans (T j)) Finset.univ).cost ans : ℝ) ≤ k1 := by exact_mod_cast this
  linarith

end TriFormQ.W

namespace TriFormQ.W

open Matrix Module CAlg

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

theorem allOut_collect_card {Q R : Type} {L : ℕ} (A : CAlg Q R (Option (Fin L))) (ans : Q → R) :
    ∀ N, (collect A N).AllOut ans (fun C => C.card ≤ N)
  | 0 => by simp [collect, AllOut]
  | N + 1 => by
    simp only [collect]
    refine allOut_bind _ _ _ (P := fun _ => True) (allOut_of_forall _ _ fun _ => trivial)
      fun o _ => ?_
    unfold CAlg.map
    refine allOut_bind _ _ _ (allOut_collect_card A ans N) fun C hC => ?_
    rcases o with _ | j
    · show C.card ≤ N + 1
      omega
    · show (insert j C).card ≤ N + 1
      exact (Finset.card_insert_le _ _).trans (by omega)

/-- The full algorithm: `N` attempts, then a final prefilter among their outputs. -/
noncomputable def fullAlg {L : ℕ} (T : Fin L → TriForm F n) (j0 : Fin L) (t k1 kmax : ℕ)
    (ε' : ℝ) (N k2 : ℕ) : CAlg (CQ F n) (Vec F n) (Fin L) :=
  (collect (attempt T t k1 kmax ε') N).bind fun C => finalSel T j0 k2 C

theorem fullAlg_good {L : ℕ} (T : Fin L → TriForm F n) (j0 i : Fin L) (ρ : ℝ) (k1 kmax : ℕ)
    (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1)
    (hk1 : (L : ℝ) * ((Fintype.card F : ℝ) ^ ρ)⁻¹ ^ k1 ≤ 1 / 32)
    (hkmax : L < 2 ^ (2 ^ kmax))
    (hεsmall : ((mBound ⌈ρ⌉₊ * (kmax + 1) : ℕ) : ℝ) * ε' ≤ 1 / 20) (N k2 : ℕ) :
    1 - (3 / 5 : ℝ) ^ N - N * (3 / 4 : ℝ) ^ k2 ≤
      (fullAlg T j0 ⌈ρ⌉₊ k1 kmax ε' N k2).prob (CQ.ans (T i)) (fun j => T j = T i) := by
  classical
  have hatt := attempt_good T i ρ k1 kmax ε' hε' hε1 hk1 hkmax hεsmall
  have hfail : (attempt T ⌈ρ⌉₊ k1 kmax ε').prob (CQ.ans (T i))
      (fun o => ¬ ∃ j, o = some j ∧ T j = T i) ≤ 3 / 5 := by
    have := prob_compl (CQ.ans (T i)) (attempt T ⌈ρ⌉₊ k1 kmax ε')
      (fun o => ∃ j, o = some j ∧ T j = T i)
    linarith
  have hcol := collect_good (attempt T ⌈ρ⌉₊ k1 kmax ε') (CQ.ans (T i)) (fun j => T j = T i)
    (3 / 5) (by norm_num) hfail N
  have hcard := allOut_collect_card (attempt T ⌈ρ⌉₊ k1 kmax ε') (CQ.ans (T i)) N
  by_cases hbig : 1 ≤ (N : ℝ) * (3 / 4 : ℝ) ^ k2
  · refine le_trans ?_ (prob_nonneg _ _ _)
    have : (0 : ℝ) ≤ (3 / 5 : ℝ) ^ N := by positivity
    linarith
  push Not at hbig
  unfold fullAlg
  refine prob_bind_ge (CQ.ans (T i)) _ _ (fun C => (∃ j ∈ C, T j = T i) ∧ C.card ≤ N) _
    ((3 / 5 : ℝ) ^ N) (N * (3 / 4 : ℝ) ^ k2) ?_ ?_ (by positivity) hbig.le
  · refine prob_ge_of_fail _ _ ?_
    refine le_trans (prob_mono_allOut _ _ (P' := fun C => ¬ ∃ j ∈ C, T j = T i)
      (allOut_mono _ _ (fun C hC hn => ?_) hcard)) hcol
    intro h; exact hn ⟨h, hC⟩
  · rintro C ⟨hC, hCN⟩
    refine le_trans ?_ (finalSel_good T j0 k2 C i hC)
    have : (C.card : ℝ) ≤ N := by exact_mod_cast hCN
    have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k2 := by positivity
    nlinarith

theorem cost_fullAlg {L : ℕ} (hL : 1 ≤ L) (T : Fin L → TriForm F n) (j0 : Fin L) (t k1 kmax : ℕ)
    (ε' : ℝ) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (N k2 : ℕ) (ans : CQ F n → Vec F n) :
    ((fullAlg T j0 t k1 kmax ε' N k2).cost ans : ℝ) ≤
      N * (k1 + structCost t + cPhi ε' kmax (mBound t) L) + k2 := by
  set X : ℝ := k1 + structCost t + cPhi ε' kmax (mBound t) L
  have hX0 : 0 ≤ X := by
    have := cost_attempt hL T t k1 kmax ε' hε' hε1 ans; simp only [X]
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((attempt T t k1 kmax ε').cost ans : ℝ))]
  have hatt : (attempt T t k1 kmax ε').cost ans ≤ ⌊X⌋₊ :=
    Nat.le_floor (cost_attempt hL T t k1 kmax ε' hε' hε1 ans)
  have hcol := cost_collect (attempt T t k1 kmax ε') ans ⌊X⌋₊ hatt N
  unfold fullAlg
  have h := cost_bind_le ans (collect (attempt T t k1 kmax ε') N) (fun C => finalSel T j0 k2 C)
    k2 (allOut_of_forall _ _ fun C => cost_finalSel T j0 k2 C ans)
  have h2 : ((collect (attempt T t k1 kmax ε') N).bind fun C => finalSel T j0 k2 C).cost ans ≤
      N * ⌊X⌋₊ + k2 := h.trans (Nat.add_le_add_right hcol _)
  have h3 : (((collect (attempt T t k1 kmax ε') N).bind fun C => finalSel T j0 k2 C).cost ans : ℝ)
      ≤ (N * ⌊X⌋₊ + k2 : ℕ) := by exact_mod_cast h2
  push_cast at h3
  have h4 : (N : ℝ) * (⌊X⌋₊ : ℝ) ≤ N * X :=
    mul_le_mul_of_nonneg_left (Nat.floor_le hX0) (by positivity)
  linarith

end TriFormQ.W

end


-- ===== Solutions/W_Num.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TriFormQ.W

/-! ### Numeric lemmas -/

lemma logb_le_three_sqrt (x : ℝ) (hx : 1 ≤ x) : Real.logb 2 x ≤ 3 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (by linarith)]
  have h2 := Real.log_le_sub_one_of_pos hs
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

lemma nat_log_sq_le (r : ℕ) (hr : 1 ≤ r) : (Nat.log 2 r + 1) ^ 2 ≤ 3 * r := by
  have hk : ∀ k : ℕ, (k + 1) ^ 2 ≤ 3 * 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rcases Nat.lt_or_ge k 3 with h | h
      · interval_cases k <;> norm_num
      · have : 2 * k + 3 ≤ 3 * 2 ^ k := by
          have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
          nlinarith
        rw [show (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]; nlinarith
  have h1 := hk (Nat.log 2 r)
  have h2 : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 (by omega)
  omega

lemma structCost_le (t : ℕ) : structCost t ≤ 400000 * (t + 1) ^ 2 := by
  have hr : 1 ≤ sR0 t := by simp only [sR0]; omega
  have hl := nat_log_sq_le (sR0 t) hr
  set r := sR0 t with hrdef
  set ℓ := sL t with hℓ
  have hℓdef : ℓ = Nat.log 2 r + 1 := rfl
  rw [← hℓdef] at hl
  have hℓr : ℓ ≤ 3 * r := by nlinarith
  have hr10 : 10 ≤ r := by simp only [r, sR0]; omega
  have hrt : r = 2 * t + 10 := rfl
  simp only [structCost, sI, sJ, sS, ← hℓ, ← hrdef]
  have h1 : 4 * ℓ * (4 * ℓ + 5 + 1) ≤ 120 * r := by nlinarith
  have h2 : r + (4 * ℓ + 8) ≤ 14 * r := by omega
  have h3 : 4 * ℓ * ((4 * ℓ + 5 + 1) * (r + (4 * ℓ + 8)) * 2) ≤ 3360 * r ^ 2 := by
    calc 4 * ℓ * ((4 * ℓ + 5 + 1) * (r + (4 * ℓ + 8)) * 2)
        = (4 * ℓ * (4 * ℓ + 5 + 1)) * (r + (4 * ℓ + 8)) * 2 := by ring
      _ ≤ (120 * r) * (14 * r) * 2 := by gcongr
      _ = 3360 * r ^ 2 := by ring
  have h4 : r ^ 2 ≤ 100 * (t + 1) ^ 2 := by rw [hrt]; nlinarith
  nlinarith

end TriFormQ.W

namespace TriFormQ.W

lemma sqrt_le_self' (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

lemma one_le_sqrt' (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx

/-- The attempt's worst-case query count is `O(ρ²)` with `ρ = (log₂ L)^{1/3}`. -/
theorem attCost_bound (B ρ : ℝ) (hB : 1 ≤ B) (hρ1 : 1 ≤ ρ) (hρ3 : ρ ^ 3 = B) (L : ℕ)
    (hLB : Real.logb 2 L = B) :
    ((⌈(B + 5) / ρ⌉₊ : ℕ) : ℝ) + structCost ⌈ρ⌉₊ +
      cPhi (1 / (((mBound ⌈ρ⌉₊ * (⌈Real.logb 2 (B + 1)⌉₊ + 1 + 1) : ℕ) : ℝ) * 20))
        (⌈Real.logb 2 (B + 1)⌉₊ + 1) (mBound ⌈ρ⌉₊) L ≤ 4000000 * ρ ^ 2 := by
  set t := ⌈ρ⌉₊ with htdef
  set kmax := ⌈Real.logb 2 (B + 1)⌉₊ + 1 with hkdef
  set mB := mBound t with hmB
  set X : ℝ := ((mB * (kmax + 1) : ℕ) : ℝ) * 20 with hX
  have ht1 : (t : ℝ) ≤ ρ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hs1 := one_le_sqrt' ρ hρ1
  have hsρ : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (by linarith)
  -- k1
  have hk1 : ((⌈(B + 5) / ρ⌉₊ : ℕ) : ℝ) ≤ 7 * ρ ^ 2 := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ (B + 5) / ρ by positivity)).le
    have h2 : (B + 5) / ρ ≤ ρ ^ 2 + 5 := by
      rw [div_le_iff₀ (by linarith), ← hρ3]; nlinarith
    nlinarith
  -- structCost
  have hsc : (structCost t : ℝ) ≤ 3600000 * ρ ^ 2 := by
    have h := structCost_le t
    have h' : ((structCost t : ℕ) : ℝ) ≤ ((400000 * (t + 1) ^ 2 : ℕ) : ℝ) := Nat.cast_le.2 h
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h'
    have h1 : (t : ℝ) + 1 ≤ 3 * ρ := by linarith
    have h0 : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
    have h2 : ((t : ℝ) + 1) ^ 2 ≤ 9 * ρ ^ 2 := by
      calc ((t : ℝ) + 1) ^ 2 ≤ (3 * ρ) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = 9 * ρ ^ 2 := by ring
    have h400 : ((400000 : ℕ) : ℝ) = 400000 := by norm_num
    rw [h400] at h'
    have h3 : (400000 : ℝ) * ((t : ℝ) + 1) ^ 2 ≤ 400000 * (9 * ρ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  -- mB
  have hmBr : (mB : ℝ) ≤ 117 * ρ := by
    have : (mB : ℝ) = 17 * t + 83 := by simp only [mB, mBound, sR0]; push_cast; ring
    rw [this]; nlinarith
  have hmB1 : (1 : ℝ) ≤ mB := by
    have : 1 ≤ mB := by simp only [mB, mBound]; omega
    exact_mod_cast this
  -- kmax
  have hlogB1 : Real.logb 2 (B + 1) ≤ 1 + 9 * Real.sqrt ρ := by
    have h1 : Real.logb 2 (B + 1) ≤ Real.logb 2 (2 * B) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have h2 : Real.logb 2 (2 * B) = 1 + 3 * Real.logb 2 ρ := by
      rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num), ← hρ3,
        Real.logb_pow]; push_cast; ring
    have h3 := logb_le_three_sqrt ρ hρ1
    linarith
  have hkm : (kmax : ℝ) + 1 ≤ 13 * Real.sqrt ρ := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (B + 1) from
      Real.logb_nonneg (by norm_num) (by linarith))).le
    simp only [kmax]; push_cast
    linarith
  have hkm0 : (0 : ℝ) ≤ kmax := by positivity
  -- ε' and K1
  have hprod : 1 ≤ mB * (kmax + 1) := by
    have : 1 ≤ mB := by simp only [mB, mBound]; omega
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hX1 : 20 ≤ X := by
    simp only [X]
    have : (1 : ℝ) ≤ ((mB * (kmax + 1) : ℕ) : ℝ) := by exact_mod_cast hprod
    linarith
  have hXpos : 0 < X := by linarith
  have hε1 : 1 / X ≤ 1 := by rw [div_le_one hXpos]; linarith
  have hε0 : 0 < 1 / X := by positivity
  have hXle : X ≤ 30420 * ρ ^ 2 := by
    simp only [X]; push_cast
    have h1 : (mB : ℝ) * ((kmax : ℝ) + 1) ≤ 117 * ρ * (13 * Real.sqrt ρ) :=
      mul_le_mul hmBr hkm (by positivity) (by positivity)
    have h2 : Real.sqrt ρ ≤ ρ := sqrt_le_self' ρ hρ1
    have h3 : 117 * ρ * (13 * Real.sqrt ρ) ≤ 117 * ρ * (13 * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : 117 * ρ * (13 * ρ) * 20 = 30420 * ρ ^ 2 := by ring
    linarith
  have hK1 : cK1 (1 / X) ≤ 104 * Real.sqrt ρ := by
    unfold cK1
    rw [one_div_one_div]
    have h1 : Real.logb 2 X ≤ Real.logb 2 (30420 * ρ ^ 2) :=
      Real.logb_le_logb_of_le (by norm_num) hXpos hXle
    have h2 : Real.logb 2 (30420 * ρ ^ 2) = Real.logb 2 30420 + 2 * Real.logb 2 ρ := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]; push_cast; ring
    have h3 : Real.logb 2 30420 ≤ 15 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
    have h4 := logb_le_three_sqrt ρ hρ1
    linarith
  have hK10 : 0 ≤ cK1 (1 / X) := cK1_nonneg _ hε0 hε1
  have hkK : ((kmax : ℝ) + 1) * cK1 (1 / X) ≤ 1352 * ρ := by
    have := mul_le_mul hkm hK1 hK10 (by positivity)
    have e : 13 * Real.sqrt ρ * (104 * Real.sqrt ρ) = 1352 * (Real.sqrt ρ * Real.sqrt ρ) := by ring
    rw [e, hsρ] at this; exact this
  -- cPhi
  have hsqrt : Real.sqrt (mB * Real.logb 2 L) ≤ 11 * ρ ^ 2 := by
    rw [hLB, ← hρ3]
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : (mB : ℝ) * ρ ^ 3 ≤ 117 * ρ * ρ ^ 3 :=
      mul_le_mul_of_nonneg_right hmBr (by positivity)
    have h2 : 117 * ρ * ρ ^ 3 ≤ (11 * ρ ^ 2) ^ 2 := by
      have : (0 : ℝ) ≤ ρ ^ 4 := by positivity
      nlinarith
    linarith
  have hpow : (2 : ℝ) ^ kmax ≤ 8 * ρ ^ 3 := by
    have h1 : (2 : ℝ) ^ kmax = 2 * 2 ^ (⌈Real.logb 2 (B + 1)⌉₊ : ℕ) := by
      simp only [kmax]; rw [pow_succ]; ring
    have h2 : (2 : ℝ) ^ (⌈Real.logb 2 (B + 1)⌉₊ : ℕ) ≤ 2 * (B + 1) := by
      rw [← Real.rpow_natCast]
      calc (2 : ℝ) ^ ((⌈Real.logb 2 (B + 1)⌉₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (B + 1) + 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.ceil_lt_add_one
              (Real.logb_nonneg (by norm_num) (by linarith))).le
        _ = 2 * (B + 1) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
              (by linarith), Real.rpow_one]; ring
    rw [h1]
    have : B + 1 ≤ 2 * ρ ^ 3 := by rw [hρ3]; linarith
    linarith
  have hcS : cS (1 / X) (kmax + 1) ≤ 1388 * ρ ^ 2 := by
    have h := cS_succ_le (1 / X) hε0 hε1 kmax
    have hs : Real.sqrt ((2 : ℝ) ^ kmax) ≤ 3 * ρ ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      have : ρ ^ 3 ≤ ρ ^ 4 := pow_le_pow_right₀ hρ1 (by norm_num)
      have e : (3 * ρ ^ 2) ^ 2 = 9 * ρ ^ 4 := by ring
      have : (0 : ℝ) ≤ ρ ^ 4 := by positivity
      rw [e]; linarith
    push_cast at h
    have hρρ : ρ ≤ ρ ^ 2 := le_self_pow₀ hρ1 (by norm_num)
    linarith
  have hΦ : cPhi (1 / X) kmax mB L ≤ 161200 * ρ ^ 2 := by
    unfold cPhi
    have h1 : (mB : ℝ) * (12 + ((kmax : ℝ) + 1) * cK1 (1 / X)) ≤ 117 * ρ * (12 + 1352 * ρ) :=
      mul_le_mul hmBr (by linarith) (by positivity) (by positivity)
    have hρρ : ρ ≤ ρ ^ 2 := le_self_pow₀ hρ1 (by norm_num)
    have e : 117 * ρ * (12 + 1352 * ρ) = 1404 * ρ + 158184 * ρ ^ 2 := by ring
    push_cast
    linarith
  linarith

end TriFormQ.W

end


-- ===== Solutions/W_Final.lean
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 1000

namespace TriFormQ.W

open CAlg

lemma rpow_third_cube (B : ℝ) (hB : 0 ≤ B) : (B ^ ((1 : ℝ) / 3)) ^ 3 = B := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hB]; norm_num

lemma rpow_third_sq (B : ℝ) (hB : 0 ≤ B) : (B ^ ((1 : ℝ) / 3)) ^ 2 = B ^ ((2 : ℝ) / 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hB]; norm_num

lemma delta_bounds (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let c := ⌈Real.logb 2 (2 / δ)⌉₊
    (3 / 5 : ℝ) ^ (2 * c) + ((2 * c : ℕ) : ℝ) * (3 / 4 : ℝ) ^ (3 * (2 * c + 1)) ≤ δ ∧
      ((c : ℕ) : ℝ) ≤ 3 * lam δ := by
  intro c
  have hc2 : 2 / δ ≤ (2 : ℝ) ^ c := two_pow_ceil_logb (2 / δ) (by positivity)
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have hcle : ((c : ℕ) : ℝ) ≤ 2 ^ c := by exact_mod_cast (Nat.lt_two_pow_self (n := c)).le
  have hδc : 1 / (2 : ℝ) ^ c ≤ δ / 2 := by
    rw [div_le_div_iff₀ h2c (by norm_num)]
    rw [div_le_iff₀ hδ] at hc2; linarith
  refine ⟨?_, ?_⟩
  · have h1 : (3 / 5 : ℝ) ^ (2 * c) ≤ 1 / 2 ^ c := by
      rw [pow_mul, one_div, ← inv_pow]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) c
    have h2 : (3 / 4 : ℝ) ^ (3 * (2 * c + 1)) ≤ (1 / 2) ^ (2 * c + 1) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h3 : ((2 * c : ℕ) : ℝ) * (1 / 2) ^ (2 * c + 1) ≤ δ / 2 := by
      have hA : ((c : ℕ) : ℝ) * (1 / 2) ^ c ≤ 1 := by
        rw [one_div_pow, mul_one_div, div_le_one h2c]; exact hcle
      have hB : ((2 * c : ℕ) : ℝ) * (1 / 2) ^ (2 * c + 1) =
          (((c : ℕ) : ℝ) * (1 / 2) ^ c) * (1 / 2) ^ c := by push_cast; ring
      rw [hB]
      have hC : (((c : ℕ) : ℝ) * (1 / 2) ^ c) * (1 / 2) ^ c ≤ 1 * (1 / 2) ^ c :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      have hδc' : (1 / 2 : ℝ) ^ c ≤ δ / 2 := by rw [one_div_pow]; exact hδc
      linarith
    have h4 : ((2 * c : ℕ) : ℝ) * (3 / 4 : ℝ) ^ (3 * (2 * c + 1)) ≤
        ((2 * c : ℕ) : ℝ) * (1 / 2) ^ (2 * c + 1) := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · have h := (Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (2 / δ) by
      apply Real.logb_nonneg (by norm_num); rw [le_div_iff₀ hδ]; linarith)).le
    have e : Real.logb 2 (2 / δ) = 1 + Real.logb 2 (1 / δ) := by
      rw [logb_mul_inv 2 δ (by norm_num) hδ, Real.logb_self_eq_one (by norm_num)]
    have hl1 : 1 ≤ lam δ := le_max_left _ _
    have hl2 : Real.logb 2 (1 / δ) ≤ lam δ := le_max_right _ _
    simp only [c] at h ⊢
    linarith

/-- The classical core: identification with contraction queries. -/
theorem classical_core (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ n L : ℕ, 0 < n → 0 < L → ∀ (T : Fin L → TriForm F n) (δ : ℝ), 0 < δ → δ < 1 →
      ∃ A : CAlg (CQ F n) (Vec F n) (Fin L), ∀ i : Fin L,
        (A.cost (CQ.ans (T i)) : ℝ) ≤ C * (Real.logb 2 L) ^ ((2 : ℝ) / 3) * lam δ ∧
        1 - δ ≤ A.expect (CQ.ans (T i)) (fun j => if T j = T i then 1 else 0) := by
  classical
  refine ⟨24000021, fun n L hn hL T δ hδ hδ1 => ?_⟩
  have hlam1 : 1 ≤ lam δ := le_max_left _ _
  rcases Nat.lt_or_ge L 2 with hL1 | hL2
  · -- a single candidate
    have hL1' : L = 1 := by omega
    subst hL1'
    refine ⟨ret 0, fun i => ⟨?_, ?_⟩⟩
    · simp only [cost, Nat.cast_zero]
      have : (0 : ℝ) ≤ (Real.logb 2 ((1 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) := by
        simp
      positivity
    · simp only [expect]
      rw [if_pos (by rw [Subsingleton.elim (0 : Fin 1) i])]
      linarith
  · set B := Real.logb 2 L with hBdef
    have hB : 1 ≤ B := by
      rw [hBdef, Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
      simp only [Real.rpow_one]; exact_mod_cast hL2
    set ρ := B ^ ((1 : ℝ) / 3) with hρdef
    have hρ1 : 1 ≤ ρ := Real.one_le_rpow hB (by norm_num)
    have hρ3 : ρ ^ 3 = B := rpow_third_cube B (by linarith)
    have hρ2 : ρ ^ 2 = B ^ ((2 : ℝ) / 3) := rpow_third_sq B (by linarith)
    set k1 := ⌈(B + 5) / ρ⌉₊
    set kmax := ⌈Real.logb 2 (B + 1)⌉₊ + 1
    set ε' : ℝ := 1 / (((mBound ⌈ρ⌉₊ * (kmax + 1) : ℕ) : ℝ) * 20)
    obtain ⟨hdelta, hcl⟩ := delta_bounds δ hδ hδ1
    set c := ⌈Real.logb 2 (2 / δ)⌉₊
    have hprod : (1 : ℝ) ≤ ((mBound ⌈ρ⌉₊ * (kmax + 1) : ℕ) : ℝ) := by
      have : 1 ≤ mBound ⌈ρ⌉₊ * (kmax + 1) := by
        have : 1 ≤ mBound ⌈ρ⌉₊ := by simp only [mBound]; omega
        exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      exact_mod_cast this
    have hε0 : 0 < ε' := by positivity
    have hε1 : ε' ≤ 1 := by
      simp only [ε']; rw [div_le_one (by positivity)]; linarith
    have hεsmall : ((mBound ⌈ρ⌉₊ * (kmax + 1) : ℕ) : ℝ) * ε' ≤ 1 / 20 := by
      simp only [ε']; field_simp; norm_num
    have hLB : (2 : ℝ) ^ B = L := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    have hk1 : (L : ℝ) * ((Fintype.card F : ℝ) ^ ρ)⁻¹ ^ k1 ≤ 1 / 32 := by
      have hq2 : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast q_ge_two (F := F)
      have hk1ρ : B + 5 ≤ ρ * k1 := by
        have := Nat.le_ceil ((B + 5) / ρ)
        rw [div_le_iff₀ (by linarith)] at this; linarith
      have h1 : (2 : ℝ) ^ (B + 5) ≤ ((Fintype.card F : ℝ) ^ ρ) ^ k1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        calc (2 : ℝ) ^ (B + 5) ≤ (2 : ℝ) ^ (ρ * k1) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hk1ρ
          _ ≤ (Fintype.card F : ℝ) ^ (ρ * k1) :=
              Real.rpow_le_rpow (by norm_num) hq2 (by positivity)
      have h2 : (2 : ℝ) ^ (B + 5) = 32 * L := by
        rw [Real.rpow_add (by norm_num), hLB]; norm_num; ring
      rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hkmax : L < 2 ^ (2 ^ kmax) := by
      have h1 : B + 1 ≤ (2 : ℝ) ^ (⌈Real.logb 2 (B + 1)⌉₊ : ℕ) := by
        have := two_pow_ceil_logb (B + 1) (by linarith); exact this
      have h2 : B < ((2 ^ kmax : ℕ) : ℝ) := by
        simp only [kmax]; push_cast; rw [pow_succ]; linarith
      have h3 : (L : ℝ) < ((2 ^ (2 ^ kmax) : ℕ) : ℝ) := by
        rw [← hLB]; push_cast
        rw [← Real.rpow_natCast]
        exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by exact_mod_cast h2)
      exact_mod_cast h3
    refine ⟨fullAlg T ⟨0, hL⟩ ⌈ρ⌉₊ k1 kmax ε' (2 * c) (3 * (2 * c + 1)), fun i => ⟨?_, ?_⟩⟩
    · have h := cost_fullAlg (by omega) T ⟨0, hL⟩ ⌈ρ⌉₊ k1 kmax ε' hε0 hε1 (2 * c) (3 * (2 * c + 1))
        (CQ.ans (T i))
      have hX := attCost_bound B ρ hB hρ1 hρ3 L hBdef.symm
      set X := (k1 : ℝ) + structCost ⌈ρ⌉₊ + cPhi ε' kmax (mBound ⌈ρ⌉₊) L
      have hX0 : 0 ≤ X := by
        have := cost_attempt (F := F) (by omega) T ⌈ρ⌉₊ k1 kmax ε' hε0 hε1 (CQ.ans (T i))
        linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((attempt T ⌈ρ⌉₊ k1 kmax ε').cost
          (CQ.ans (T i)) : ℝ))]
      have hN : (((2 * c : ℕ)) : ℝ) ≤ 6 * lam δ := by push_cast; linarith
      have hk2 : (((3 * (2 * c + 1) : ℕ)) : ℝ) ≤ 21 * lam δ := by push_cast; linarith
      have hρ2' : 1 ≤ ρ ^ 2 := by nlinarith
      rw [← hρ2]
      have e1 : (((2 * c : ℕ)) : ℝ) * X ≤ 6 * lam δ * (4000000 * ρ ^ 2) :=
        mul_le_mul hN hX hX0 (by positivity)
      have e2 : 21 * lam δ ≤ 21 * ρ ^ 2 * lam δ := by nlinarith
      push_cast at h e1 ⊢
      nlinarith
    · have h := fullAlg_good T ⟨0, hL⟩ i ρ k1 kmax ε' hε0 hε1 hk1 hkmax hεsmall (2 * c)
        (3 * (2 * c + 1))
      have e : (fullAlg T ⟨0, hL⟩ ⌈ρ⌉₊ k1 kmax ε' (2 * c) (3 * (2 * c + 1))).prob
          (CQ.ans (T i)) (fun j => T j = T i) =
          (fullAlg T ⟨0, hL⟩ ⌈ρ⌉₊ k1 kmax ε' (2 * c) (3 * (2 * c + 1))).expect (CQ.ans (T i))
            (fun j => if T j = T i then 1 else 0) := by
        unfold prob; congr 1; funext j; by_cases hj : T j = T i <;> simp [hj]
      rw [← e]
      push_cast at h hdelta
      linarith

end TriFormQ.W

/-- The main theorem. -/
theorem TriFormQ.W.main_theorem :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], ∃ C : ℝ, ∀ n L : ℕ, 0 < n → 0 < L →
      ∀ (T : Fin L → TriFormQ.TriForm F n) (δ : ℝ), 0 < δ → δ < 1 →
        ∃ A : TriFormQ.AdaptiveAlg (TriFormQ.Vec F n × TriFormQ.Vec F n × TriFormQ.Vec F n) F
          (Fin L), ∀ i : Fin L,
          (A.maxQueries (TriFormQ.oracle (T i)) : ℝ) ≤
            C * (Real.logb 2 L) ^ ((2 : ℝ) / 3) * TriFormQ.lam δ ∧
          1 - δ ≤ A.outProb (TriFormQ.oracle (T i)) (fun j => T j = T i) := by
  intro F _ _ _
  obtain ⟨C, hC⟩ := TriFormQ.W.classical_core F
  refine ⟨C, fun n L hn hL T δ hδ hδ1 => ?_⟩
  obtain ⟨A, hA⟩ := hC n L hn hL T δ hδ hδ1
  obtain ⟨B, hB⟩ := TriFormQ.CompileW.compile_spec A
  refine ⟨B, fun i => ⟨?_, ?_⟩⟩
  · rw [(hB (T i)).2]; exact (hA i).1
  · rw [(hB (T i)).1]; exact (hA i).2

end


/-- Grigorescu–Juba–Wimmer–Xie, Theorem 1 (Main), as stated on the platform. -/
theorem solution :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], ∃ C : ℝ, ∀ n L : ℕ, 0 < n → 0 < L →
      ∀ (T : Fin L → TriFormQ.TriForm F n) (δ : ℝ), 0 < δ → δ < 1 →
        ∃ A : TriFormQ.AdaptiveAlg (TriFormQ.Vec F n × TriFormQ.Vec F n × TriFormQ.Vec F n) F
          (Fin L), ∀ i : Fin L,
          (A.maxQueries (TriFormQ.oracle (T i)) : ℝ) ≤
            C * (Real.logb 2 L) ^ ((2 : ℝ) / 3) * TriFormQ.lam δ ∧
          1 - δ ≤ A.outProb (TriFormQ.oracle (T i)) (fun j => T j = T i) :=
  TriFormQ.W.main_theorem
